//! EIP-8288 mixed recursive proof profile.

use super::*;

/// A canonical big-endian scheme word, data hash and verification-key hash.
pub type Dependency = [u8; 96];

pub const MAX_DEPENDENCIES: usize = 256;
pub const MAX_GENERIC_DEPENDENCIES: usize = 16;
pub const MAX_GENERIC_BYTECODE_LOG: usize = 11;
pub const MAX_GENERIC_COMMITTED_LOG: usize = 22;
pub const MAX_GENERIC_BUS_LOG: usize = 22;
pub const MAX_MIXED_COMMITTED_LOG: usize = 27;
pub const MAX_MIXED_BUS_LOG: usize = 26;
pub const LOG_INV_RATE: usize = 1;

/// A generic CPU proof and the program/public input it claims to execute.
pub struct GenericInput<'a> {
    pub program: &'a Program,
    pub proof: &'a lean_vm::cpu::Proof,
    pub data: [u8; 32],
}

#[derive(Debug)]
pub enum MixedError {
    Dependencies,
    Program,
    Encoding,
    Capacity,
    Proof(AggregateVerifyError),
    Witness(AggregationError),
    Prover(ProveError),
}

impl std::fmt::Display for MixedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dependencies => f.write_str("noncanonical mixed dependency set"),
            Self::Program => f.write_str("unsupported generic program encoding"),
            Self::Encoding => f.write_str("malformed mixed proof encoding"),
            Self::Capacity => f.write_str("mixed proof exceeds profile capacity"),
            Self::Proof(error) => write!(f, "mixed proof verification failed: {error}"),
            Self::Witness(error) => write!(f, "mixed proof witness failed: {error}"),
            Self::Prover(error) => write!(f, "mixed prover failed: {error}"),
        }
    }
}
impl std::error::Error for MixedError {}

fn check_dependencies(deps: &[Dependency]) -> Result<(), MixedError> {
    if deps.len() > MAX_DEPENDENCIES
        || deps.iter().filter(|dep| dep[31] == 0x11).count() > MAX_GENERIC_DEPENDENCIES
        || deps
            .iter()
            .any(|dep| dep[..31] != [0; 31] || !matches!(dep[31], 0x10 | 0x11))
        || !deps.windows(2).all(|pair| pair[0] < pair[1])
    {
        return Err(MixedError::Dependencies);
    }
    Ok(())
}

/// The 32-byte domain block closing a digest that covers generic dependencies.
pub const LEANSTARK_DEPS_DOMAIN: [u8; 32] = *b"eip8288/leanstark-deps\0\0\0\0\0\0\0\0\0\0";

/// EIP-8288 `get_deps_hash` of a canonical dependency list.
///
/// Without generic (`0x11`) dependencies this is the EIP's BLAKE2s over the 64-byte
/// `data_hash || verification_key_hash` entries. The EIP leaves `0x11` undefined; here a list
/// with generic entries hashes `get_deps_hash(sphincs) || get_deps_hash(generic) ||
/// LEANSTARK_DEPS_DOMAIN`, a 96-byte preimage that no all-SPHINCS list shares.
pub fn deps_hash(deps: &[Dependency]) -> [u8; 32] {
    let split = deps.partition_point(|dep| dep[31] == 0x10);
    let list = |deps: &[Dependency]| {
        primitives::hash::hash(
            &deps
                .iter()
                .flat_map(|dep| dep[32..].iter().copied())
                .collect::<Vec<_>>(),
        )
    };
    let sphincs = list(&deps[..split]);
    if split == deps.len() {
        return sphincs;
    }
    primitives::hash::hash(&[sphincs, list(&deps[split..]), LEANSTARK_DEPS_DOMAIN].concat())
}

/// EIP-8288 leanSPHINCS `verification_key_hash`: the key itself, root then public parameter.
pub fn sphincs_verification_key(pk: &SphincsPublicKey) -> [u8; 32] {
    pk.flatten()
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_KEYS: usize = 16;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn unhex(text: &str) -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
            .collect()
    }

    /// Write the test leanSPHINCS keys (`keys.bin`, 32 bytes each) and a
    /// genuine root proof for every requested dependency set, one hex line of
    /// 96-byte dependencies each, as `<deps_hash>.bin`: `EXPORT_DIR=...
    /// [EXPORT_REQUESTS=...] cargo test --release --features eip8288-mixed
    /// export_eip8288_test_proofs -- --ignored`.
    #[test]
    #[ignore]
    fn export_eip8288_test_proofs() {
        let directory = std::env::var("EXPORT_DIR").expect("EXPORT_DIR");
        let keys: Vec<_> = (0..TEST_KEYS)
            .map(|i| sphincs::key_gen_from_seed([i as u8 + 1; 32]))
            .collect();
        let verification_keys: Vec<[u8; 32]> =
            keys.iter().map(|(_, pk)| sphincs_verification_key(pk)).collect();
        std::fs::write(format!("{directory}/keys.bin"), verification_keys.concat()).unwrap();
        let Ok(requests) = std::env::var("EXPORT_REQUESTS") else {
            return;
        };
        let mut lines = Vec::new();
        for entry in std::fs::read_dir(requests).unwrap() {
            lines.extend(std::fs::read_to_string(entry.unwrap().path()).unwrap().lines().map(str::to_owned));
        }
        for line in &lines {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let bytes = unhex(line);
            let mut deps: Vec<Dependency> =
                bytes.chunks(96).map(|chunk| chunk.try_into().unwrap()).collect();
            deps.sort();
            deps.dedup();
            let hash = deps_hash(&deps);
            let path = format!("{directory}/{}.bin", hex(&hash));
            if std::path::Path::new(&path).exists() {
                continue;
            }
            let raws: Vec<_> = deps
                .iter()
                .map(|dependency| {
                    assert_eq!(dependency[31], 0x10, "only leanSPHINCS claims");
                    let index = verification_keys
                        .iter()
                        .position(|key| key[..] == dependency[64..96])
                        .expect("claim under a test key");
                    let message: [u8; 32] = dependency[32..64].try_into().unwrap();
                    let (secret, key) = &keys[index];
                    (*key, message, sphincs::sign(secret, &message))
                })
                .collect();
            let started = std::time::Instant::now();
            let mut level: Vec<MixedProof> = raws
                .chunks(4)
                .map(|chunk| {
                    let selected: Vec<Dependency> =
                        chunk.iter().map(|(key, message, _)| sph_dep(key, *message)).collect();
                    aggregate_mixed(&[], chunk, &[], &selected, 1).unwrap()
                })
                .collect();
            while level.len() > 1 {
                level = level
                    .chunks(2)
                    .map(|pair| {
                        if pair.len() == 1 {
                            return pair[0].clone();
                        }
                        let mut union = pair[0].dependencies().to_vec();
                        union.extend_from_slice(pair[1].dependencies());
                        union.sort();
                        union.dedup();
                        aggregate_mixed(pair, &[], &[], &union, 1).unwrap()
                    })
                    .collect();
            }
            let root = level.pop().unwrap();
            assert_eq!(root.dependencies(), &deps[..]);
            let payload = root.to_bytes_without_deps();
            verify_mixed_deps(&hash, &payload).unwrap();
            std::fs::write(&path, &payload).unwrap();
            eprintln!("{} deps -> {} bytes in {:.2?}", deps.len(), payload.len(), started.elapsed());
        }
    }

    /// Export a genuine one-claim root and every intermediate the Python
    /// verifier port checks against: `EXPORT_DIR=... cargo test --release
    /// --features eip8288-mixed export_python_vectors -- --ignored`.
    #[test]
    #[ignore]
    fn export_python_vectors() {
        let directory = std::env::var("EXPORT_DIR").expect("EXPORT_DIR");
        let write = |name: &str, bytes: &[u8]| std::fs::write(format!("{directory}/{name}"), bytes).unwrap();
        let (secret, key) = sphincs::key_gen_from_seed([19; 32]);
        let message = [23; 32];
        let signature = sphincs::sign(&secret, &message);
        let sph = sph_dep(&key, message);
        let started = std::time::Instant::now();
        let leaf = aggregate_mixed(&[], &[(key, message, signature.clone())], &[], &[sph], 1).unwrap();
        eprintln!("proved in {:.2?}", started.elapsed());
        let payload = leaf.to_bytes_without_deps();
        let hash = deps_hash(&[sph]);
        verify_mixed_deps(&hash, &payload).unwrap();
        let (deferred, proof) = decode_payload(&payload).unwrap();
        let pi = mixed_statement(hash, &deferred);
        assert!(pi.iter().all(|value| value.c2 == 0));
        let raw = verify(unified_guest(), &pi, &proof).unwrap().raw;
        write("dependency.bin", &sph);
        write("deps_hash.bin", &hash);
        write("payload.bin", &payload);
        write("guest_key.bin", &mixed_guest_key());
        write("message.bin", &message);
        write("sphincs_public_key.bin", &key.flatten());
        write("sphincs_signature.bin", &signature.to_bytes());
        let table: Vec<u8> = mixed_table().iter().flat_map(|w| w.0.to_le_bytes()).collect();
        write("bytecode.bin", &table);
        let pi_bytes: Vec<u8> = pi.iter().flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes()].concat()).collect();
        write("public_input.bin", &pi_bytes);
        let cells: Vec<u8> = deferred
            .cells()
            .iter()
            .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes(), v.c2.to_le_bytes()].concat())
            .collect();
        write("cells.bin", &cells);
        let mut stream = Vec::new();
        for scalar in &raw.stream {
            for limb in [scalar.c0, scalar.c1, scalar.c2] {
                stream.extend(limb.to_le_bytes());
            }
        }
        let mut openings = Vec::new();
        for opening in &raw.merkle {
            for word in &opening.leaf_data {
                openings.extend(word.0.to_le_bytes());
            }
            for digest in &opening.path {
                openings.extend(digest);
            }
        }
        write("stream.bin", &stream);
        write("merkle_openings.bin", &openings);
        let seed = lean_vm::cpu::fs_seed(unified_guest());
        let seed_bytes: Vec<u8> = seed
            .iter()
            .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes(), v.c2.to_le_bytes()].concat())
            .collect();
        write("fs_seed.bin", &seed_bytes);
        eprintln!(
            "program={} payload={} table_words={} stream={} openings={} key={:02x?}",
            unified_guest().prog.len(),
            payload.len(),
            mixed_table().len(),
            raw.stream.len(),
            raw.merkle.len(),
            mixed_guest_key()
        );
    }

    #[test]
    #[ignore]
    fn mixed_leaf_and_same_key_depth_two_bind_programs_and_discards() {
        let data = [7; 32];
        let pi = pack_hash_state(&data);
        let mut program = compile(
            &lean_compiler::parse(&format!(
                "def main():\n    p = 1\n    p[1] = {}\n    p[GEN] = {}\n    return\n",
                f192_literal(pi[0]),
                f192_literal(pi[1])
            ))
            .unwrap(),
        );
        let (inner, _) = prove(&program, pi, 1).unwrap();
        assert!(generic_recursion_supported(&program, &inner));
        let generic_dep = dep(0x11, data, generic_verification_key(&program).unwrap());
        let generic_input = GenericInput {
            program: &program,
            proof: &inner,
            data,
        };
        for name in [
            "code_header",
            "code_instruction",
            "cell_bytes",
            "cell_index",
            "operand_index",
            "counter_index",
            "generic_data",
            "dependency_split",
            "bytecode_val",
            "leaf_defer",
            "matpart",
            "fs_seed",
        ] {
            let (guest, _, honest_pi) = prepare_mixed_with_hints(
                &[],
                &[],
                &[GenericInput {
                    program: &program,
                    proof: &inner,
                    data,
                }],
                &[generic_dep],
                1,
                |hints| {
                    let entry = &mut hints.entries(name)[0];
                    if name == "generic_data" {
                        entry[0] += F192::new(0, 1, 0);
                    } else {
                        entry[0] += F192::ONE;
                    }
                },
            )
            .unwrap();
            assert!(
                std::panic::catch_unwind(|| guest.execute(honest_pi)).is_err(),
                "accepted malicious {name}"
            );
        }
        let (mut missing, deferred, _) = prepare_mixed(
            &[],
            &[],
            &[GenericInput {
                program: &program,
                proof: &inner,
                data,
            }],
            &[generic_dep],
            1,
        )
        .unwrap();
        let mut unsupported = generic_dep;
        unsupported[95] ^= 1;
        let mut false_deps = vec![generic_dep, unsupported];
        false_deps.sort();
        missing.set_witness("mixed_meta", vec![vec![gcount(2), gcount(0), gcount(1), gcount(0)]]);
        missing.set_witness("dependency", false_deps.iter().map(cells).collect());
        let mut false_digest_hints = Hints::default();
        push_dependency_digest(&mut false_digest_hints, &false_deps);
        push_block_counters(&mut false_digest_hints, 2 * program.prog.len());
        for (name, entries) in false_digest_hints.0 {
            missing.set_witness(&name, entries);
        }
        missing.set_witness(
            "selection",
            vec![vec![F192::ONE, gcount(false_deps.binary_search(&generic_dep).unwrap())]],
        );
        assert!(
            std::panic::catch_unwind(|| missing.execute(mixed_statement(deps_hash(&false_deps), &deferred))).is_err()
        );
        eprintln!("proving genuine generic leaf");
        let generic = aggregate_mixed(&[], &[], &[generic_input], &[generic_dep], 1).unwrap();
        generic.verify().unwrap();
        let (secret, key) = sphincs::key_gen_from_seed([19; 32]);
        let message = [23; 32];
        let signature = sphincs::sign(&secret, &message);
        let sph = sph_dep(&key, message);
        let mut union = vec![sph, generic_dep];
        union.sort();
        eprintln!("proving genuine SPH leaf");
        let sph_leaf = aggregate_mixed(&[], &[(key, message, signature)], &[], &[sph], 1).unwrap();
        sph_leaf.verify().unwrap();
        eprintln!("proving same-key mixed parent");
        let parent = aggregate_mixed(&[generic.clone(), sph_leaf], &[], &[], &union, 1).unwrap();
        parent.verify().unwrap();
        for name in ["child_carried", "bytecode_val", "matpart", "fs_seed"] {
            let (forged, _, honest_pi) =
                prepare_mixed_with_hints(std::slice::from_ref(&parent), &[], &[], &[generic_dep], 1, |hints| {
                    hints.entries(name)[0][0] += F192::ONE;
                })
                .unwrap();
            assert!(
                std::panic::catch_unwind(|| forged.execute(honest_pi)).is_err(),
                "accepted malicious child {name}"
            );
        }
        eprintln!("proving depth-two overlapping discard root");
        let root = aggregate_mixed(&[parent, generic], &[], &[], &[generic_dep], 1).unwrap();
        root.verify().unwrap();
        let payload = root.to_bytes_without_deps();
        verify_mixed_deps(&deps_hash(&[generic_dep]), &payload).unwrap();
        assert!(verify_mixed_deps(&deps_hash(&union), &payload).is_err());
        let mut forged = generic_dep;
        forged[32] ^= 1;
        assert!(
            MixedProof::from_bytes_without_deps(&[forged], &payload)
                .unwrap()
                .verify()
                .is_err()
        );
        program.prog[0] = lean_vm::cpu::Op::Xor { a: 0, b: 0, c: 0 };
        assert!(
            aggregate_mixed(
                &[],
                &[],
                &[GenericInput {
                    program: &program,
                    proof: &inner,
                    data
                }],
                &[generic_dep],
                1
            )
            .is_err()
        );
        eprintln!("mixed root bytes={} key={:02x?}", payload.len(), mixed_guest_key());
    }

    fn vector_dependencies() -> [Dependency; 5] {
        let key = |start: u8| std::array::from_fn(|i| start + i as u8);
        [
            dep(0x10, [0x07; 32], key(0)),
            dep(0x10, [0x07; 32], key(1)),
            dep(0x10, [0x01; 32], [0xff; 32]),
            dep(0x11, [0x07; 32], key(0)),
            dep(0x11, [0xa5; 32], [0x5a; 32]),
        ]
    }

    /// Expected digests computed in Python from the EIP-8288 `get_deps_hash` pseudocode.
    #[test]
    fn deps_hash_matches_eip_pseudocode_vectors() {
        let [a, b, c, g1, g2] = vector_dependencies();
        let canonical = |deps: &[Dependency]| {
            deps.iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        };
        for (deps, expected) in [
            (
                vec![],
                "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9",
            ),
            (
                vec![a],
                "6921fc8275ae947e76ab603255f550b615341fb880a8635996d30b55201d28f6",
            ),
            (
                vec![b, a, c, a],
                "27ad454def73a88020d3f7a6428cd790cf354b531b0447013027e7fa277b9e13",
            ),
            (
                vec![g1],
                "3ae64e624f1d16e19a7699b95f501134828652df566420f26a4f298b5bb54b9a",
            ),
            (
                vec![g2, a, g1, c],
                "ba1180b0f634d713dbf9b5b87e68a36786f550676d2b05d4f49f699eeb42e90f",
            ),
        ] {
            let digest: String = deps_hash(&canonical(&deps))
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect();
            assert_eq!(digest, expected);
        }
    }

    #[test]
    fn guest_dependency_digest_matches_deps_hash() {
        let helpers = runtime_guest_source(19);
        let helpers = format!(
            "{}{}",
            &helpers[..helpers.find("\ndef main():").unwrap()],
            program_seed_source()
        );
        let source = format!(
            "{helpers}\ndef main():\n    powers = HeapBuf(768)\n    for i in unroll(0, 256):\n        powers[GEN ** i] = i\n        powers[GEN ** (256 + i)] = GEN ** i\n        powers[GEN ** (512 + i)] = GEN ** (256 * i)\n    n = hint_witness(\"count\")\n    entries, h0, h1 = mixed_dependencies(n, powers)\n    p = 1\n    assert p[1] == h0\n    assert p[GEN] == h1\n    return\n"
        );
        let guest = compile(&lean_compiler::parse(&source).unwrap());
        let configure = |deps: &[Dependency], split: Option<[usize; 2]>| {
            let mut hints = Hints::default();
            hints.push("count", vec![gcount(deps.len())]);
            for dependency in deps {
                hints.push("dependency", cells(dependency));
            }
            push_dependency_digest(&mut hints, deps);
            if let Some(split) = split {
                hints.0.retain(|(name, _)| name != "dependency_split");
                hints.push("dependency_split", split.map(gcount).to_vec());
            }
            let mut configured = guest.clone();
            hints.install(&mut configured);
            configured
        };
        let [a, b, c, g1, g2] = vector_dependencies();
        for deps in [vec![], vec![a], vec![c, a, b], vec![g1], vec![c, a, g1, g2]] {
            let pi = pack_hash_state(&deps_hash(&deps));
            assert!(configure(&deps, None).execute(pi).unconstrained_reads.is_empty());
            assert!(std::panic::catch_unwind(|| configure(&deps, None).execute([pi[0] + F192::ONE, pi[1]])).is_err());
        }
        // A generic dependency cannot be hashed as a SPHINCS one, nor the reverse.
        let mixed = [c, a, g1, g2];
        for split in [[3, 1], [1, 3]] {
            let pi = pack_hash_state(&deps_hash(&mixed));
            assert!(std::panic::catch_unwind(|| configure(&mixed, Some(split)).execute(pi)).is_err());
        }
    }

    #[test]
    fn coverage_count_rejects_missing_duplicate_and_unbounded_writers() {
        let helpers = include_str!("../guests/eip8288_mixed.py");
        let cover = &helpers[helpers.find("def mixed_cover(").unwrap()..helpers.find("def mixed_leaf(").unwrap()];
        let source = format!(
            "{cover}\ndef main():\n    selected = HeapBuf(12)\n    hint_witness(selected[0:12], \"selected\")\n    covered = HeapBuf(2)\n    marks = HeapBuf(3)\n    marks[1] = 1\n    for row in mul_range(1, GEN ** 2):\n        claim = HeapBuf(6)\n        hint_witness(claim[0:6], \"claim\")\n        marks[row * GEN] = mixed_cover(claim, selected, GEN ** 2, covered, marks[row])\n    assert marks[GEN ** 2] == GEN ** 2\n    p = 1\n    p[1] = 7\n    p[GEN] = 9\n    return\n"
        );
        let mut guest = compile(&lean_compiler::parse(&source).unwrap());
        let a = vec![integer(3); 6];
        let b = vec![integer(5); 6];
        guest.set_witness("selected", vec![[a.clone(), b.clone()].concat()]);
        guest.set_witness("claim", vec![a.clone(), b]);
        guest.set_witness(
            "selection",
            vec![vec![F192::ONE, gcount(0)], vec![F192::ONE, gcount(1)]],
        );
        let pi = [integer(7), integer(9)];
        let (proof, _) = prove(&guest, pi, 1).unwrap();
        verify(&guest, &pi, &proof).unwrap();
        for selection in [
            vec![vec![F192::ONE, gcount(0)], vec![F192::ZERO, gcount(1)]],
            vec![vec![F192::ONE, gcount(0)], vec![F192::ONE, gcount(2)]],
            vec![vec![F192::ONE, gcount(1)], vec![F192::ONE, gcount(0)]],
            vec![vec![integer(2), gcount(0)], vec![F192::ONE, gcount(1)]],
        ] {
            let mut forged = guest.clone();
            forged.set_witness("selection", selection);
            assert!(std::panic::catch_unwind(|| forged.execute(pi)).is_err());
        }
        let mut duplicate = guest.clone();
        duplicate.set_witness("claim", vec![a.clone(), a]);
        duplicate.set_witness("selection", vec![vec![F192::ONE, gcount(0)]; 2]);
        assert!(std::panic::catch_unwind(|| duplicate.execute(pi)).is_err());
    }

    #[test]
    #[ignore]
    fn executed_hash_opcodes_recurse_with_full_public_input() {
        let data = [0xa7; 32];
        let pi = pack_hash_state(&data);
        let blake = lean_vm::vmhash::compress([F64(5), F64(0), F64(7), F64(0)], [F64(5), F64(0), F64(7), F64(0)]);
        let blake_cells = [
            F192::new(blake[0].0, blake[1].0, 0),
            F192::new(blake[2].0, blake[3].0, 0),
        ];
        let mut bytes = vec![0u8; 32];
        bytes[0] = 5;
        bytes[16] = 7;
        let keccak = pack_hash_state(&primitives::keccak::keccak256(&bytes));
        let source = format!(
            "def main():\n    a = StackBuf(2)\n    a[0] = 5\n    a[1] = 7\n    b = StackBuf(2)\n    blake2s(a, a, b)\n    k = StackBuf(2)\n    keccak([a[0], a[1]], k)\n    assert b[0] == {}\n    assert b[1] == {}\n    assert k[0] == {}\n    assert k[1] == {}\n    p = 1\n    if a[0] != 0:\n        p[1] = {}\n        p[GEN] = {}\n    return\n",
            f192_literal(blake_cells[0]),
            f192_literal(blake_cells[1]),
            f192_literal(keccak[0]),
            f192_literal(keccak[1]),
            f192_literal(pi[0]),
            f192_literal(pi[1])
        );
        let program = compile(&lean_compiler::parse(&source).unwrap());
        eprintln!("executed BLAKE2s/SHA3 program class={}", program.prog.len());
        let (proof, _) = prove(&program, pi, 1).unwrap();
        let native_layout = lean_vm::cpu::layout(
            &program.prog,
            proof.stream[0].c0 as usize,
            std::array::from_fn(|i| proof.stream[i + 1].c0 as usize),
            pi,
        );
        eprintln!(
            "inner_mu={} bus_mu={} stream={}",
            native_layout.shape.mu,
            lean_vm::leaf::layout(&native_layout.push).mu,
            proof.stream.len()
        );
        let dependency = dep(0x11, data, generic_verification_key(&program).unwrap());
        let mixed = aggregate_mixed(
            &[],
            &[],
            &[GenericInput {
                program: &program,
                proof: &proof,
                data,
            }],
            &[dependency],
            1,
        )
        .unwrap();
        mixed.verify().unwrap();
    }

    #[test]
    #[ignore]
    fn active_rate_rejects_an_otherwise_valid_cpu_proof() {
        let pi = pack_hash_state(&[0x97; 32]);
        let program = compile(
            &lean_compiler::parse(&format!(
                "def main():\n    p = 1\n    p[1] = {}\n    p[GEN] = {}\n    return\n",
                f192_literal(pi[0]),
                f192_literal(pi[1])
            ))
            .unwrap(),
        );
        let (proof, _) = prove(&program, pi, 2).unwrap();
        verify(&program, &pi, &proof).unwrap();
        assert!(!generic_recursion_supported(&program, &proof));
        let helpers = runtime_guest_source(19);
        let helpers = format!(
            "{}{}",
            &helpers[..helpers.find("\ndef main():").unwrap()],
            program_seed_source()
        );
        let source = format!(
            "{helpers}\ndef main():\n    logs, squares = exponent_tables()\n    seed = StackBuf(2)\n    hint_witness(seed, \"seed\")\n    fresh = HeapBuf(DEFER_SIZE)\n    p = 1\n    verify_sub(p[1], p[GEN], seed[0], seed[1], logs, squares, fresh, GEN ** {}, GEN ** GENERIC_COMMITTED_LOG, GEN ** GENERIC_BUS_LOG)\n    return\n",
            program.prog.len().trailing_zeros()
        );
        for permitted in [false, true] {
            let source = if permitted {
                source.replace("    assert log_inv_rate == 1\n", "")
            } else {
                source.clone()
            };
            let mut guest = compile(&lean_compiler::parse(&source).unwrap());
            let summary = verify(&program, &pi, &proof).unwrap();
            let (hints, _) = gen_verify_with_min(&program, pi, summary, lean_vm::pcs::MIN_MU).unwrap();
            let mut streams = Hints::default();
            for (name, entry) in hints {
                streams.push(name, entry);
            }
            streams.install(&mut guest);
            guest.set_witness("seed", vec![lean_vm::cpu::fs_seed(&program).to_vec()]);
            let execution = std::panic::catch_unwind(|| guest.execute(pi));
            assert_eq!(execution.is_ok(), permitted);
            if let Ok(execution) = execution {
                assert!(execution.unconstrained_reads.is_empty());
            }
        }
    }

    #[test]
    #[ignore]
    fn generic_geometry_cap_rejects_a_native_valid_large_proof() {
        let data = [0x97; 32];
        let pi = pack_hash_state(&data);
        let source = format!(
            "def main():\n    h = HeapBuf(262144)\n    for i in mul_range(1, GEN ** 262144):\n        h[i] = i\n    p = 1\n    p[1] = {}\n    p[GEN] = {}\n    return\n",
            f192_literal(pi[0]),
            f192_literal(pi[1])
        );
        let program = compile(&lean_compiler::parse(&source).unwrap());
        assert!(program.prog.len() <= 1 << MAX_GENERIC_BYTECODE_LOG);
        let (proof, _) = prove(&program, pi, 1).unwrap();
        let summary = verify(&program, &pi, &proof).unwrap();
        let layout = lean_vm::cpu::layout(
            &program.prog,
            proof.stream[0].c0 as usize,
            std::array::from_fn(|i| proof.stream[i + 1].c0 as usize),
            pi,
        );
        eprintln!(
            "native_valid_unrecursible_mu={} stream={}",
            layout.shape.mu,
            proof.stream.len()
        );
        assert!(layout.shape.mu > MAX_GENERIC_COMMITTED_LOG);
        assert!(!generic_recursion_supported(&program, &proof));
        let helpers = runtime_guest_source(19);
        let helpers = format!(
            "{}{}",
            &helpers[..helpers.find("\ndef main():").unwrap()],
            program_seed_source()
        );
        let verifier = format!(
            "{helpers}\ndef main():\n    logs, squares = exponent_tables()\n    seed = StackBuf(2)\n    hint_witness(seed, \"seed\")\n    fresh = HeapBuf(DEFER_SIZE)\n    p = 1\n    verify_sub(p[1], p[GEN], seed[0], seed[1], logs, squares, fresh, GEN ** {}, GEN ** GENERIC_COMMITTED_LOG, GEN ** GENERIC_BUS_LOG)\n    return\n",
            program.prog.len().trailing_zeros()
        );
        let mut guest = compile(&lean_compiler::parse(&verifier).unwrap());
        let (hints, _) = gen_verify_with_min(&program, pi, summary, lean_vm::pcs::MIN_MU).unwrap();
        let mut streams = Hints::default();
        for (name, entry) in hints {
            streams.push(name, entry);
        }
        streams.install(&mut guest);
        guest.set_witness("seed", vec![lean_vm::cpu::fs_seed(&program).to_vec()]);
        assert!(std::panic::catch_unwind(|| guest.execute(pi)).is_err());
        let permissive = verifier
            .replace("GEN ** GENERIC_COMMITTED_LOG", "GEN ** 30")
            .replace("GEN ** GENERIC_BUS_LOG", "GEN ** 40");
        let mut permitted = compile(&lean_compiler::parse(&permissive).unwrap());
        let summary = verify(&program, &pi, &proof).unwrap();
        let (hints, _) = gen_verify_with_min(&program, pi, summary, lean_vm::pcs::MIN_MU).unwrap();
        let mut streams = Hints::default();
        for (name, entry) in hints {
            streams.push(name, entry);
        }
        streams.install(&mut permitted);
        permitted.set_witness("seed", vec![lean_vm::cpu::fs_seed(&program).to_vec()]);
        let execution = permitted.execute(pi);
        assert!(execution.unconstrained_reads.is_empty());
    }

    #[test]
    #[ignore]
    fn coverage_capacity_resource_probe() {
        let start = std::time::Instant::now();
        let mut layer = Vec::new();
        for offset in (0..MAX_DEPENDENCIES).step_by(4) {
            let claims: Vec<_> = (offset..offset + 4)
                .map(|index| {
                    let mut seed = [0; 32];
                    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
                    let (secret, key) = sphincs::key_gen_from_seed(seed);
                    let message = primitives::keccak::keccak256(&seed);
                    (key, message, sphincs::sign(&secret, &message))
                })
                .collect();
            let mut selected: Vec<_> = claims.iter().map(|(key, message, _)| sph_dep(key, *message)).collect();
            selected.sort();
            let proof = aggregate_mixed(&[], &claims, &[], &selected, 1).unwrap();
            proof.verify().unwrap();
            layer.push(proof);
            eprintln!("capacity_leaves={}/{}", offset + 4, MAX_DEPENDENCIES);
        }
        while layer.len() > 1 {
            let mut next = Vec::new();
            for pair in layer.chunks(2) {
                let mut selected: Vec<_> = pair.iter().flat_map(|child| child.deps.iter().copied()).collect();
                selected.sort();
                selected.dedup();
                let proof = aggregate_mixed(pair, &[], &[], &selected, 1).unwrap();
                proof.verify().unwrap();
                next.push(proof);
            }
            eprintln!("capacity_layer={} claims={}", next.len(), next[0].deps.len());
            layer = next;
        }
        let root = layer.pop().unwrap();
        assert_eq!(root.deps.len(), MAX_DEPENDENCIES);
        let children = [root.clone(), root];
        let selected = children[0].deps.clone();
        let (guest, deferred, pi) = prepare_mixed(&children, &[], &[], &selected, 1).unwrap();
        let (proof, stats) = prove(&guest, pi, 1).unwrap();
        assert!(recursion_supported(unified_guest(), &proof));
        let result = MixedProof {
            deps: selected,
            deferred,
            proof,
        };
        result.verify().unwrap();
        eprintln!(
            "capacity_deps={} child_rows={} proof_bytes={} cycles={} committed={} wall_seconds={:.3}",
            result.deps.len(),
            children.iter().map(|child| child.deps.len()).sum::<usize>(),
            result.to_bytes_without_deps().len(),
            stats.cycles,
            stats.committed,
            start.elapsed().as_secs_f64()
        );
    }

    #[test]
    #[ignore]
    fn node_resource_probe() {
        let case = std::env::var("MIXED_PROBE_CASE").unwrap();
        let directory = std::env::var("MIXED_PROBE_DIR").unwrap();
        let init = std::time::Instant::now();
        unified_guest();
        let compile_ms = init.elapsed().as_secs_f64() * 1000.0;
        let data = [7; 32];
        let pi = pack_hash_state(&data);
        let heap: usize = std::env::var("MIXED_PROBE_HEAP")
            .unwrap_or_else(|_| "0".into())
            .parse()
            .unwrap();
        assert!(heap <= 262144);
        let work = if heap == 0 {
            String::new()
        } else {
            format!("    h = HeapBuf({heap})\n    for i in mul_range(1, GEN ** {heap}):\n        h[i] = i\n")
        };
        let program = compile(
            &lean_compiler::parse(&format!(
                "def main():\n{work}    p = 1\n    p[1] = {}\n    p[GEN] = {}\n    return\n",
                f192_literal(pi[0]),
                f192_literal(pi[1])
            ))
            .unwrap(),
        );
        let program = if std::env::var_os("MIXED_PROBE_DENSE").is_some() {
            assert_eq!(heap, 0);
            use lean_vm::cpu::{Op, filler};
            let execution = program.execute(pi);
            let main_end = program.filler.iter().map(|block| block.pc as usize).min().unwrap();
            let mut protected = vec![false; program.prog.len()];
            protected[..main_end].fill(true);
            for (pc, size, _) in filler::cycles(&program.filler, execution.base_counts, filler::NO_FLOORS) {
                protected[pc as usize..pc as usize + size as usize + 1].fill(true);
            }
            let mut ops = program.prog.clone();
            let mut replacements = 0;
            for (index, op) in ops.iter_mut().enumerate() {
                if !protected[index] {
                    *op = Op::Set {
                        o: (index as u32 % 65535) + 1,
                        k: F192::new(u64::MAX, u64::MAX, u64::MAX),
                    };
                    replacements += 1;
                }
            }
            let mut dense = Program::assemble(ops, std::collections::HashMap::new(), 4096);
            dense.filler = program.filler.clone();
            eprintln!("dense_code replaced={replacements} total={}", dense.prog.len());
            drop(execution);
            dense
        } else {
            program
        };
        let (inner, _) = prove(&program, pi, 1).unwrap();
        let native_layout = lean_vm::cpu::layout(
            &program.prog,
            inner.stream[0].c0 as usize,
            std::array::from_fn(|i| inner.stream[i + 1].c0 as usize),
            pi,
        );
        eprintln!(
            "inner_mu={} bus_mu={} stream={}",
            native_layout.shape.mu,
            lean_vm::leaf::layout(&native_layout.push).mu,
            inner.stream.len()
        );
        let generic_dep = dep(0x11, data, generic_verification_key(&program).unwrap());
        let (secret, key) = sphincs::key_gen_from_seed([19; 32]);
        let message = [23; 32];
        let signature = sphincs::sign(&secret, &message);
        let read = |name: &str| {
            let (deps, payload): (Vec<Vec<u8>>, Vec<u8>) =
                bincode::deserialize(&std::fs::read(format!("{directory}/{name}.bin")).unwrap()).unwrap();
            MixedProof::from_bytes_without_deps(
                &deps
                    .into_iter()
                    .map(|entry| entry.try_into().unwrap())
                    .collect::<Vec<Dependency>>(),
                &payload,
            )
            .unwrap()
        };
        let children = match case.as_str() {
            "one-child" => vec![read("mixed")],
            "mixed" | "two-child" => vec![read("generic"), read("sph")],
            _ => vec![],
        };
        let raw_sph = if matches!(case.as_str(), "sph") {
            let count: usize = std::env::var("MIXED_PROBE_SPH")
                .unwrap_or_else(|_| "1".into())
                .parse()
                .unwrap();
            assert!((1..=4).contains(&count));
            let mut claims = vec![(key, message, signature)];
            for index in 1..count {
                let (secret, key) = sphincs::key_gen_from_seed([19 + index as u8; 32]);
                let message = [23 + index as u8; 32];
                claims.push((key, message, sphincs::sign(&secret, &message)));
            }
            claims
        } else {
            vec![]
        };
        let raw_generic = if matches!(case.as_str(), "generic") {
            vec![GenericInput {
                program: &program,
                proof: &inner,
                data,
            }]
        } else {
            vec![]
        };
        let mut deps = match case.as_str() {
            "generic" | "one-child" => vec![generic_dep],
            "sph" => raw_sph.iter().map(|(key, message, _)| sph_dep(key, *message)).collect(),
            "mixed" | "two-child" => children.iter().flat_map(|child| child.deps.iter().copied()).collect(),
            _ => panic!("unknown probe case"),
        };
        deps.sort();
        deps.dedup();
        let prepare_start = std::time::Instant::now();
        let (guest, deferred, outer_pi) = prepare_mixed(&children, &raw_sph, &raw_generic, &deps, 1).unwrap();
        let prepare_ms = prepare_start.elapsed().as_secs_f64() * 1000.0;
        let start = std::time::Instant::now();
        let (proof, stats) = prove(&guest, outer_pi, 1).unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
        assert!(recursion_supported(unified_guest(), &proof));
        let result = MixedProof { deps, deferred, proof };
        let start = std::time::Instant::now();
        result.verify().unwrap();
        let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
        let payload = result.to_bytes_without_deps();
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            format!("{directory}/{case}.bin"),
            bincode::serialize(&(
                result.deps.iter().map(|entry| entry.to_vec()).collect::<Vec<_>>(),
                payload.clone(),
            ))
            .unwrap(),
        )
        .unwrap();
        eprintln!(
            "case={case} workers=1 class={} guest_ops={} compile_ms={compile_ms:.3} prepare_ms={prepare_ms:.3} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3} proof_bytes={} log_mem={} mem_used={} cycles={} base_counts={:?} committed={}",
            program.prog.len(),
            guest.prog.len(),
            payload.len(),
            stats.log_mem,
            stats.mem_used,
            stats.cycles,
            stats.base_counts,
            stats.committed
        );
        let layout = lean_vm::cpu::layout(
            &guest.prog,
            result.proof.stream[0].c0 as usize,
            std::array::from_fn(|i| result.proof.stream[i + 1].c0 as usize),
            outer_pi,
        );
        eprintln!(
            "outer_mu={} bus_mu={} stream={}",
            layout.shape.mu,
            lean_vm::leaf::layout(&layout.push).mu,
            result.proof.stream.len()
        );
    }

    #[test]
    #[ignore]
    fn runtime_class_resource_probe() {
        let size: usize = std::env::var("MIXED_PROBE_SIZE")
            .unwrap_or_else(|_| "2048".into())
            .parse()
            .unwrap();
        assert!(size.is_power_of_two() && size <= 1 << MAX_GENERIC_BYTECODE_LOG);
        let data = [0x97; 32];
        let pi = pack_hash_state(&data);
        let program = sized_program(size, pi);
        let start = std::time::Instant::now();
        let (inner, _) = prove(&program, pi, 1).unwrap();
        let inner_ms = start.elapsed().as_secs_f64() * 1000.0;
        let init = std::time::Instant::now();
        unified_guest();
        let compile_ms = init.elapsed().as_secs_f64() * 1000.0;
        let prepare_start = std::time::Instant::now();
        let dependency = dep(0x11, data, generic_verification_key(&program).unwrap());
        let (guest, deferred, outer_pi) = prepare_mixed(
            &[],
            &[],
            &[GenericInput {
                program: &program,
                proof: &inner,
                data,
            }],
            &[dependency],
            1,
        )
        .unwrap();
        let prepare_ms = prepare_start.elapsed().as_secs_f64() * 1000.0;
        let start = std::time::Instant::now();
        let (proof, stats) = prove(&guest, outer_pi, 1).unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
        assert!(recursion_supported(unified_guest(), &proof));
        let result = MixedProof {
            deps: vec![dependency],
            deferred,
            proof,
        };
        let verify_start = std::time::Instant::now();
        result.verify().unwrap();
        let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;
        eprintln!(
            "class={size} guest_ops={} execution_steps={} mem_used={} table_rows={:?} inner_bytes={} inner_ms={inner_ms:.3} compile_ms={compile_ms:.3} prepare_ms={prepare_ms:.3}",
            guest.prog.len(),
            stats.cycles,
            stats.mem_used,
            stats.base_counts,
            bincode::serialize(&inner).unwrap().len()
        );
        eprintln!(
            "class={size} outer_bytes={} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3} total_prove_verify_ms={:.3}",
            result.to_bytes_without_deps().len(),
            start.elapsed().as_secs_f64() * 1000.0
        );
    }

    fn sized_program(size: usize, pi: [F192; 2]) -> Program {
        for padding in 0..size {
            let padding_source = if padding == 0 {
                String::new()
            } else {
                format!("    h = StackBuf({padding})\n    for i in unroll(0, {padding}):\n        h[i] = i + 1\n")
            };
            let source = format!(
                "def main():\n{padding_source}    p = 1\n    p[1] = {}\n    p[GEN] = {}\n    return\n",
                f192_literal(pi[0]),
                f192_literal(pi[1])
            );
            let program = compile(&lean_compiler::parse(&source).unwrap());
            if program.prog.len() == size {
                return program;
            }
            assert!(
                program.prog.len() < size,
                "target class smaller than minimal compiled program"
            );
        }
        panic!("cannot build class {size}");
    }

    #[test]
    #[ignore]
    fn mixed_guest_compiles_to_its_own_geometry() {
        let guest = unified_guest();
        assert!(guest.prog.len().is_power_of_two());
        assert!(mixed_vars() <= 32);
        eprintln!(
            "mixed guest instructions={} key={:02x?}",
            guest.prog.len(),
            mixed_guest_key()
        );
    }

    #[test]
    fn initialized_byte_table_membership_binds_the_full_value_and_index() {
        let source = include_str!("../guests/eip8288_mixed.py");
        let checker = &source[..source.find("def word(").unwrap()];
        let source = format!(
            "{checker}\ndef main():\n    table = HeapBuf(256)\n    for i in unroll(0, 256):\n        table[GEN ** i] = i\n    x = hint_witness(\"value\")\n    checked_byte(x, table)\n    p = 1\n    p[1] = x\n    p[GEN] = 0\n    return\n"
        );
        let guest = compile(&lean_compiler::parse(&source).unwrap());
        for value in [0usize, 255] {
            let mut valid = guest.clone();
            valid.set_witness("value", vec![vec![integer(value)]]);
            valid.set_witness("byte_index", vec![vec![gcount(value)]]);
            let pi = [integer(value), F192::ZERO];
            let (proof, _) = prove(&valid, pi, 1).unwrap();
            verify(&valid, &pi, &proof).unwrap();
        }
        for (value, index) in [
            (integer(256), gcount(0)),
            (F192::new(0, 1, 0), gcount(0)),
            (F192::new(0, 0, 1), gcount(0)),
            (integer(255), gcount(256)),
            (integer(255), gcount(7)),
        ] {
            let mut forged = guest.clone();
            forged.set_witness("value", vec![vec![value]]);
            forged.set_witness("byte_index", vec![vec![index]]);
            assert!(std::panic::catch_unwind(|| forged.execute([value, F192::ZERO])).is_err());
        }
    }

    #[test]
    fn initialized_operand_powers_bind_bytes_and_upper_padding() {
        let source = include_str!("../guests/eip8288_mixed.py");
        let helpers = &source[source.find("def operand_power(").unwrap()..source.find("def columns(").unwrap()];
        let source = format!(
            "{helpers}\ndef main():\n    powers = HeapBuf(768)\n    for i in unroll(0, 256):\n        powers[GEN ** i] = i\n        powers[GEN ** (256 + i)] = GEN ** i\n        powers[GEN ** (512 + i)] = GEN ** (256 * i)\n    raw = HeapBuf(8)\n    hint_witness(raw[0:8], \"bytes\")\n    value = operand_power(raw, 0, 8, powers)\n    expected = hint_witness(\"expected\")\n    assert value == expected\n    p = 1\n    p[1] = 0\n    p[GEN] = 0\n    return\n"
        );
        let guest = compile(&lean_compiler::parse(&source).unwrap());
        let configure = |bytes: Vec<F192>, indexes: [usize; 2], expected: usize| {
            let mut configured = guest.clone();
            configured.set_witness("bytes", vec![bytes]);
            configured.set_witness("operand_index", indexes.map(|i| vec![gcount(i)]).to_vec());
            configured.set_witness("expected", vec![vec![gcount(expected)]]);
            configured
        };
        for value in [0usize, 255, 256, 65535] {
            let bytes = (0..8).map(|i| integer((value >> (8 * i)) & 255)).collect();
            let valid = configure(bytes, [value & 255, value >> 8], value);
            let (proof, _) = prove(&valid, [F192::ZERO; 2], 1).unwrap();
            verify(&valid, &[F192::ZERO; 2], &proof).unwrap();
        }
        for (offset, byte, indexes) in [
            (2, integer(1), [0, 0]),
            (7, integer(1), [0, 0]),
            (0, integer(1), [0, 0]),
            (0, integer(1), [256, 0]),
            (0, F192::new(0, 1, 0), [0, 0]),
            (1, F192::new(0, 0, 1), [0, 0]),
        ] {
            let mut bytes = vec![F192::ZERO; 8];
            bytes[offset] = byte;
            let forged = configure(bytes, indexes, 0);
            assert!(std::panic::catch_unwind(|| forged.execute([F192::ZERO; 2])).is_err());
        }
    }

    #[test]
    fn table_counter_binds_exact_exponent_and_numeric_counter() {
        let helpers = runtime_guest_source(19);
        let helpers = format!(
            "{}{}",
            &helpers[..helpers.find("\ndef main():").unwrap()],
            program_seed_source()
        );
        let source = format!(
            "{helpers}\ndef main():\n    powers = HeapBuf(768)\n    for i in unroll(0, 256):\n        powers[GEN ** i] = i\n        powers[GEN ** (256 + i)] = GEN ** i\n        powers[GEN ** (512 + i)] = GEN ** (256 * i)\n    exponent = hint_witness(\"exponent\")\n    counter = table_counter(exponent, powers)\n    p = 1\n    assert p[1] == counter\n    assert p[GEN] == 0\n    return\n"
        );
        let guest = compile(&lean_compiler::parse(&source).unwrap());
        let configure = |exponent: usize, low: usize, high: usize| {
            let mut result = guest.clone();
            result.set_witness("exponent", vec![vec![gcount(exponent)]]);
            result.set_witness("counter_index", vec![vec![gcount(low)], vec![gcount(high)]]);
            result
        };
        for value in [0usize, 255, 256, 32768, 65535] {
            let pi = [integer(value * 64), F192::ZERO];
            let valid = configure(value, value & 255, value >> 8);
            let (proof, _) = prove(&valid, pi, 1).unwrap();
            verify(&valid, &pi, &proof).unwrap();
            let wrong_pi = [integer(value * 64) + F192::ONE, F192::ZERO];
            assert!(std::panic::catch_unwind(|| valid.execute(wrong_pi)).is_err());
        }
        for (exponent, low, high) in [(0, 1, 0), (256, 0, 0), (0, 256, 0)] {
            let invalid = configure(exponent, low, high);
            let forged_counter = match low {
                256 => 64,
                _ => (low + 256 * high) * 64,
            };
            assert!(std::panic::catch_unwind(|| invalid.execute([integer(forged_counter), F192::ZERO])).is_err());
        }
    }

    #[test]
    fn canonical_cell_byte_membership_reconstructs_all_limbs() {
        let helpers = runtime_guest_source(19);
        let helpers = format!(
            "{}{}",
            &helpers[..helpers.find("\ndef main():").unwrap()],
            program_seed_source()
        );
        let source = format!(
            "{helpers}\ndef main():\n    table = HeapBuf(256)\n    for i in unroll(0, 256):\n        table[GEN ** i] = i\n    raw = HeapBuf(16)\n    p = 1\n    mixed_cell_bytes(p[1], raw, table)\n    assert p[GEN] == 0\n    return\n"
        );
        let guest = compile(&lean_compiler::parse(&source).unwrap());
        let configure = |bytes: Vec<F192>, indices: Vec<Vec<F192>>| {
            let mut result = guest.clone();
            result.set_witness("cell_bytes", vec![bytes]);
            result.set_witness("cell_index", indices);
            result
        };
        for value in [F192::ZERO, F192::new(u64::MAX, u64::MAX, 0)] {
            let bytes: Vec<_> = [value.c0.to_le_bytes(), value.c1.to_le_bytes()].concat();
            let scalar_bytes = bytes.iter().map(|&b| integer(b as usize)).collect();
            let indices = bytes.iter().map(|&b| vec![gcount(b as usize)]).collect();
            let valid = configure(scalar_bytes, indices);
            let pi = [value, F192::ZERO];
            let (proof, _) = prove(&valid, pi, 1).unwrap();
            verify(&valid, &pi, &proof).unwrap();
        }
        for (first, second) in [
            (integer(256), F192::ONE),
            (F192::new(0, 1, 0), F192::ONE),
            (F192::new(0, 0, 1), F192::new(0, 1, 0)),
        ] {
            let mut bytes = vec![F192::ZERO; 16];
            bytes[0] = first;
            let second_slot = if first == integer(256) { 1 } else { 8 };
            bytes[second_slot] = second;
            let invalid = configure(bytes, vec![vec![gcount(0)]; 16]);
            assert!(std::panic::catch_unwind(|| invalid.execute([F192::ZERO; 2])).is_err());
        }
        let invalid = configure(vec![F192::ZERO; 16], vec![vec![gcount(1)]; 16]);
        assert!(std::panic::catch_unwind(|| invalid.execute([F192::ZERO; 2])).is_err());
        let invalid = configure(vec![F192::ZERO; 16], vec![vec![gcount(0)]; 16]);
        assert!(std::panic::catch_unwind(|| invalid.execute([F192::new(0, 0, 1), F192::ZERO])).is_err());
    }

    #[test]
    fn payload_count_preflight_rejects_lengths_before_allocation() {
        assert!(preflight_payload(&u64::MAX.to_le_bytes()).is_err());
        for prefix_vectors in 0..=3 {
            let mut payload = vec![0; prefix_vectors * 8];
            payload.extend_from_slice(&u64::MAX.to_le_bytes());
            assert!(preflight_payload(&payload).is_err());
        }
        let mut dimensions = 33u64.to_le_bytes().to_vec();
        dimensions.resize(8 + 33 * 24, 0);
        assert!(preflight_payload(&dimensions).is_err());
        let mut stream = vec![0; 24];
        stream.extend_from_slice(&((STREAM_CAP + 1) as u64).to_le_bytes());
        stream.resize(32 + (STREAM_CAP + 1) * 24, 0);
        assert!(preflight_payload(&stream).is_err());
    }

    #[test]
    fn streaming_keccak_matches_native_padding_and_rejects_forged_geometry() {
        let all_helpers = include_str!("../guests/eip8288_mixed.py");
        let helpers = "def pack64x2(lo, hi):\n    assert_in_k(lo, hi)\n    return lo + hi * f192(0, 1, 0)\n\n"
            .to_owned()
            + &all_helpers[..all_helpers.find("def word(").unwrap()]
            + &all_helpers
                [all_helpers.find("def mixed_keccak(").unwrap()..all_helpers.find("def dynamic_eqtree(").unwrap()];
        for length in [0usize, 1, 135, 136, 137, 1184, 4096] {
            let mut source = format!("{helpers}\ndef main():\n    raw = HeapBuf({})\n", length + 136);
            if length != 0 {
                source += &format!("    hint_witness(raw[0:{length}], \"bytes\")\n");
            }
            source += &format!(
                "    digest = mixed_keccak(raw, GEN ** {length}, 0)\n    p = 1\n    p[1] = digest[0]\n    p[GEN] = digest[1]\n    return\n"
            );
            let mut guest = compile(&lean_compiler::parse(&source).unwrap());
            let bytes: Vec<u8> = (0..length).map(|i| (i * 193 + 17) as u8).collect();
            if length != 0 {
                guest.set_witness("bytes", vec![bytes.iter().map(|&x| integer(x as usize)).collect()]);
            }
            guest.set_witness(
                "keccak_split",
                vec![vec![F192::from(g_pow(length / 136)), F192::from(g_pow(length % 136))]],
            );
            guest.set_witness("byte_index", byte_indices(&bytes));
            let pi = pack_hash_state(&primitives::keccak::keccak256(&bytes));
            assert!(guest.execute(pi).unconstrained_reads.is_empty());
            if length == 137 {
                let (proof, _) = prove(&guest, pi, 1).unwrap();
                verify(&guest, &pi, &proof).unwrap();
                let mut forged = guest.clone();
                forged.set_witness("keccak_split", vec![vec![F192::from(g_pow(1)), F192::from(g_pow(2))]]);
                assert!(std::panic::catch_unwind(|| forged.execute(pi)).is_err());
                let mut nonbyte = guest.clone();
                let mut witness: Vec<F192> = bytes.iter().map(|&x| integer(x as usize)).collect();
                witness[0] = integer(256);
                nonbyte.set_witness("bytes", vec![witness]);
                assert!(std::panic::catch_unwind(|| nonbyte.execute(pi)).is_err());
                assert!(std::panic::catch_unwind(|| guest.execute([pi[0] + F192::ONE, pi[1]])).is_err());
            }
        }
    }

    #[test]
    fn runtime_program_geometry_has_only_explicit_length_dependent_fields() {
        let base = placeholder_map(1);
        let length_fields = [
            "BLOCK_KAPPA_ADJ_PLACEHOLDER",
            "COL_KAPPA_ADJ_PLACEHOLDER",
            "COORD_CONST_PLACEHOLDER",
            "BYTECODE_LOG_PLACEHOLDER",
            "BYTECODE_VARS_PLACEHOLDER",
            "DEFER_SIZE_PLACEHOLDER",
            "DEFER_STMT_CELLS_PLACEHOLDER",
            "DEFER_STMT_PADDED_CELLS_PLACEHOLDER",
            "STMT_ODD_PLACEHOLDER",
            "STMT_BLOCKS_PLACEHOLDER",
            "STMT_PAIRS_PLACEHOLDER",
            "STMT_PAD_CELLS_PLACEHOLDER",
        ];
        for log in 0..=MAX_GENERIC_BYTECODE_LOG {
            let map = placeholder_map(log);
            for (name, value) in &base {
                if !length_fields.contains(&name.as_str()) {
                    assert_eq!(
                        map.get(name),
                        Some(value),
                        "unexpected geometry change {name} at class {log}"
                    );
                }
            }
        }
    }
}

fn list_values(map: &BTreeMap<String, String>, key: &str) -> Vec<u128> {
    map[&format!("{key}_PLACEHOLDER")]
        .trim_matches(['[', ']'])
        .split(',')
        .map(|value| value.trim().parse().expect("integer geometry descriptor"))
        .collect()
}

fn runtime_guest_source(kbc: usize) -> String {
    let one = placeholder_map(1);
    let two = placeholder_map(2);
    let mut source = include_str!("../guests/lean_ethereum.py").to_owned();
    let main = source.find("\ndef main():").expect("aggregation entry point");
    let aggregate = source.find("\ndef aggregate_claims(").expect("aggregation sumchecks");
    source.replace_range(main..aggregate, "\n");
    let mut declarations = format!(
        "N_COORDS = {}\nMAX_MIXED_DEPENDENCIES = {MAX_DEPENDENCIES}\nMAX_MIXED_GENERIC = {MAX_GENERIC_DEPENDENCIES}\nMAX_GENERIC_CODE_LOG = {MAX_GENERIC_BYTECODE_LOG}\nGENERIC_COMMITTED_LOG = {MAX_GENERIC_COMMITTED_LOG}\nGENERIC_BUS_LOG = {MAX_GENERIC_BUS_LOG}\nMIXED_COMMITTED_LOG = {MAX_MIXED_COMMITTED_LOG}\nMIXED_BUS_LOG = {MAX_MIXED_BUS_LOG}\n",
        list_values(&one, "COORD_CONST").len()
    );
    for key in ["BLOCK_KAPPA_ADJ", "COL_KAPPA_ADJ", "COORD_CONST"] {
        let values = list_values(&one, key);
        let other = list_values(&two, key);
        let mask: Vec<_> = values.iter().zip(other).map(|(a, b)| usize::from(*a != b)).collect();
        declarations += &format!("{key}_DYNAMIC = {}\n", literals(mask));
    }
    source = source.replace(
        "def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out):",
        "def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out, code_log_g, max_mu_g, max_bus_g):",
    );
    source = source.replace("        block_kappa[GEN ** b] = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]",
        "        if BLOCK_KAPPA_ADJ_DYNAMIC[b] == 1:\n            block_kappa[GEN ** b] = code_log_g\n        else:\n            block_kappa[GEN ** b] = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]");
    source = source.replace(
        "def certify_placement(kappa_base, g_squares):",
        "def certify_placement(kappa_base, g_squares, code_log_g):",
    );
    source = source.replace("        col_kappa_g[GEN ** c] = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]",
        "        if COL_KAPPA_ADJ_DYNAMIC[c] == 1:\n            col_kappa_g[GEN ** c] = code_log_g\n        else:\n            col_kappa_g[GEN ** c] = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]");
    source = source.replace(
        "certify_placement(kappa_base, g_squares)",
        "certify_placement(kappa_base, g_squares, code_log_g)",
    );
    source = source.replace(
        "claim_push, claim_pull, claim_count):",
        "claim_push, claim_pull, claim_count, code_log_g):",
    );
    source = source.replace(
        "claim_push, claim_pull, claim_count)\n    fs =",
        "claim_push, claim_pull, claim_count, code_log_g)\n    fs =",
    );
    source = source.replace("    # ---- 3x leaf decomposition", "    coord_constants = HeapBuf(N_COORDS)\n    for ci in unroll(0, N_COORDS):\n        if COORD_CONST_DYNAMIC[ci] == 1:\n            coord_constants[GEN ** ci] = g_squares[code_log_g] / GEN\n        else:\n            coord_constants[GEN ** ci] = COORD_CONST[ci]\n\n    # ---- 3x leaf decomposition");
    source = source.replace("coord_val = COORD_CONST[ci]", "coord_val = coord_constants[GEN ** ci]");
    source = source.replace(
        "coord_val = COORD_CONST[ci] * rawv",
        "coord_val = coord_constants[GEN ** ci] * rawv",
    );
    source = source.replace("    for k in unroll(0, BYTECODE_LOG):\n        defer_out[GEN ** k] = zeta[GEN ** k]",
        "    for k in mul_range(1, code_log_g):\n        defer_out[k] = zeta[k]\n    padded_rows_g = GEN ** BYTECODE_LOG / code_log_g\n    for k in mul_range(1, padded_rows_g):\n        defer_out[code_log_g * k] = 0");
    source = source.replace(
        "    zeta = HeapBuf(g_bus_mu)",
        "    assert log(g_bus_mu) < log(max_bus_g * GEN)\n    zeta = HeapBuf(g_bus_mu)",
    );
    source = source.replace(
        "    size_sel = gmv * LIG_MIN_SHIFT_INV",
        "    assert log(gmv) < log(max_mu_g * GEN)\n    size_sel = gmv * LIG_MIN_SHIFT_INV",
    );
    source = source.replace(
        "    rate_sel = g_power_of_word(log_inv_rate, g_squares, LOG_WORD_BITS) / GEN",
        "    assert log_inv_rate == 1\n    rate_sel = g_power_of_word(log_inv_rate, g_squares, LOG_WORD_BITS) / GEN",
    );
    let map = placeholder_map_with_min(kbc, lean_vm::pcs::MIN_MU);
    let mut replacements: Vec<_> = map.iter().collect();
    replacements.sort_by_key(|(key, _)| std::cmp::Reverse(key.len()));
    for (key, value) in replacements {
        source = source.replace(key, value);
    }
    declarations += &format!("OPCODES = {}\n", literals((0..7).map(|i| g_pow(i).0)));
    for (i, value) in lean_vm::hash_flock::IV_CELLS.iter().enumerate() {
        declarations += &format!("MIXED_BLAKE_IV_{i} = {}\n", f192_literal(*value));
    }
    for (i, cell) in LEANSTARK_DEPS_DOMAIN.as_chunks::<16>().0.iter().enumerate() {
        declarations += &format!("LEANSTARK_DEPS_DOMAIN_{i} = {}\n", f192_literal(pack_16_bytes(cell)));
    }
    let extension = include_str!("../guests/eip8288_mixed.py");
    declarations + &source + extension + &program_seed_source()
}

fn recursion_supported(program: &Program, proof: &lean_vm::cpu::Proof) -> bool {
    recursion_supported_with_bounds(program, proof, MAX_MIXED_COMMITTED_LOG, MAX_MIXED_BUS_LOG)
}
fn recursion_supported_with_bounds(
    program: &Program,
    proof: &lean_vm::cpu::Proof,
    max_mu: usize,
    max_bus: usize,
) -> bool {
    use lean_vm::tables::N_TABLES;
    if proof.stream.len() > STREAM_CAP
        || proof.stream.len() < N_TABLES + 2
        || proof.stream[..N_TABLES + 1]
            .iter()
            .any(|value| value.c1 != 0 || value.c2 != 0 || value.c0 > 32)
        || proof.stream[N_TABLES + 1].c1 != 0
        || proof.stream[N_TABLES + 1].c2 != 0
        || proof.stream[N_TABLES + 1].c0 as usize != LOG_INV_RATE
    {
        return false;
    }
    let layout = lean_vm::cpu::layout(
        &program.prog,
        proof.stream[0].c0 as usize,
        std::array::from_fn(|i| proof.stream[i + 1].c0 as usize),
        [F192::ZERO; 2],
    );
    (lean_vm::pcs::MIN_MU..=max_mu).contains(&layout.shape.mu)
        && [&layout.push, &layout.pull, &layout.count]
            .iter()
            .all(|side| lean_vm::leaf::layout(side).mu <= max_bus)
}

/// Whether a generic proof fits this recursive profile's checked transport and layout bounds.
pub fn generic_recursion_supported(program: &Program, proof: &lean_vm::cpu::Proof) -> bool {
    encode_program(program).is_ok()
        && recursion_supported_with_bounds(program, proof, MAX_GENERIC_COMMITTED_LOG, MAX_GENERIC_BUS_LOG)
}

/// The canonical code preimage used by the EIP-8288 generic verification-key hash.
pub fn generic_verification_key(program: &Program) -> Result<[u8; 32], MixedError> {
    Ok(primitives::keccak::keccak256(&encode_program(program)?))
}

fn encode_program(program: &Program) -> Result<Vec<u8>, MixedError> {
    use lean_vm::cpu::{DerefMode, Op};
    let n = program.prog.len();
    if !n.is_power_of_two() || n > 1 << MAX_GENERIC_BYTECODE_LOG {
        return Err(MixedError::Program);
    }
    let mut bytes = Vec::with_capacity(4 + 45 * n);
    bytes.extend_from_slice(&(n as u32).to_le_bytes());
    for op in &program.prog {
        let (tag, args, limbs, md) = match *op {
            Op::Xor { a, b, c } => (0, [a, b, c, 0], [0; 3], 0),
            Op::Mul { a, b, c } => (1, [a, b, c, 0], [0; 3], 0),
            Op::Set { o, k } => (2, [o, 0, 0, 0], [k.c0, k.c1, k.c2], 0),
            Op::Deref { o1, o2, o3, mode } => (
                3,
                [
                    o1,
                    o2,
                    o3,
                    match mode {
                        DerefMode::Cell => 0,
                        DerefMode::Pc => 1,
                        DerefMode::Fp => 2,
                    },
                ],
                [0; 3],
                0,
            ),
            Op::Jump { oc, od, of } => (4, [oc, od, of, 0], [0; 3], 0),
            Op::Blake2s { ins, cv, out, md } if cv <= 65535 && out <= 65535 => (5, ins, [cv as u64, out as u64, 0], md),
            Op::Sha3 { m, cap, out, digest }
                if m.iter().all(|&value| value <= 65535) && cap <= 65531 && out <= 65523 =>
            {
                (
                    6,
                    m[..4].try_into().expect("four operands"),
                    [
                        m[4] as u64 | ((m[5] as u64) << 32),
                        m[6] as u64 | ((m[7] as u64) << 32),
                        cap as u64 | ((out as u64) << 32),
                    ],
                    u32::from(digest),
                )
            }
            _ => return Err(MixedError::Program),
        };
        if args.iter().any(|&value| value > 65535) || md > 65535 {
            return Err(MixedError::Program);
        }
        bytes.push(tag);
        for value in args {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        for value in limbs {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes.extend_from_slice(&md.to_le_bytes());
    }
    Ok(bytes)
}

const MAX_PAYLOAD_BYTES: usize = 8 * 1024 * 1024;
type MixedWire = (Vec<F192>, [Vec<F192>; 2], lean_vm::cpu::Proof);

/// A proof of the exact selected dependency set under one self-recursive guest.
#[derive(Clone)]
pub struct MixedProof {
    deps: Vec<Dependency>,
    deferred: DeferredClaim,
    proof: lean_vm::cpu::Proof,
}

impl MixedProof {
    pub fn dependencies(&self) -> &[Dependency] {
        &self.deps
    }

    pub fn from_bytes_without_deps(deps: &[Dependency], payload: &[u8]) -> Result<Self, MixedError> {
        check_dependencies(deps)?;
        let (deferred, proof) = decode_payload(payload)?;
        Ok(Self {
            deps: deps.to_vec(),
            deferred,
            proof,
        })
    }

    pub fn to_bytes_without_deps(&self) -> Vec<u8> {
        wire()
            .serialize(&(
                self.deferred.bytecode_point.as_slice(),
                self.deferred.matrix_points(),
                &self.proof,
            ))
            .expect("mixed proof encoding")
    }

    pub fn verify(&self) -> Result<(), MixedError> {
        check_dependencies(&self.deps)?;
        if !recursion_supported(unified_guest(), &self.proof) {
            return Err(MixedError::Capacity);
        }
        let pi = mixed_statement(deps_hash(&self.deps), &self.deferred);
        verify(unified_guest(), &pi, &self.proof)
            .map_err(|error| MixedError::Proof(AggregateVerifyError::Snark(error)))?;
        Ok(())
    }
}

fn mixed_table() -> &'static [F64] {
    static TABLE: std::sync::OnceLock<Vec<F64>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| lean_vm::cpu::layout::bytecode_table(&unified_guest().prog))
}

fn mixed_vars() -> usize {
    unified_guest().prog.len().trailing_zeros() as usize + lean_vm::leaf::N_BYTECODE_SELECTORS
}

fn mixed_deferred(points: Vec<F192>, matrices: [Vec<F192>; 2]) -> Result<DeferredClaim, MixedError> {
    if points.len() != mixed_vars()
        || Circuit::BOTH
            .iter()
            .zip(&matrices)
            .any(|(circuit, point)| point.len() != 2 * circuit.k_log())
    {
        return Err(MixedError::Encoding);
    }
    let bytecode_value = if points.iter().all(|&x| x == F192::ZERO) {
        F192::from(mixed_table()[0])
    } else {
        mle_eval_par(mixed_table(), &points)
    };
    let [blake, keccak] = matrices;
    Ok(DeferredClaim {
        bytecode_point: points,
        bytecode_value,
        matrices: [
            MatrixClaim::at(Circuit::Blake2s, blake).map_err(MixedError::Proof)?,
            MatrixClaim::at(Circuit::Keccak, keccak).map_err(MixedError::Proof)?,
        ],
    })
}

fn decode_payload(payload: &[u8]) -> Result<(DeferredClaim, lean_vm::cpu::Proof), MixedError> {
    if payload.len() > MAX_PAYLOAD_BYTES {
        return Err(MixedError::Capacity);
    }
    preflight_payload(payload)?;
    let (points, matrices, proof): MixedWire = wire()
        .with_limit(MAX_PAYLOAD_BYTES as u64)
        .deserialize(payload)
        .map_err(|_| MixedError::Encoding)?;
    if !recursion_supported(unified_guest(), &proof) {
        return Err(MixedError::Capacity);
    }
    Ok((mixed_deferred(points, matrices)?, proof))
}

fn mixed_statement(hash: [u8; 32], deferred: &DeferredClaim) -> [F192; 2] {
    let seed = lean_vm::cpu::fs_seed(unified_guest());
    let digest = pack_hash_state(&hash);
    let header = [seed[0], seed[1], digest[0], digest[1], F192::ZERO, F192::ZERO];
    let mut cells = deferred.cells();
    if !cells.len().is_multiple_of(2) {
        cells.push(F192::ZERO);
    }
    lane_hash(
        header
            .iter()
            .flat_map(|value| [value.c0, value.c1])
            .chain(cells.iter().flat_map(|value| [value.c0, value.c1, value.c2])),
    )
}

/// Verify the complete recursive statement without transmitting application witnesses.
pub fn verify_mixed_deps(hash: &[u8; 32], payload: &[u8]) -> Result<(), MixedError> {
    let (deferred, proof) = decode_payload(payload)?;
    let pi = mixed_statement(*hash, &deferred);
    verify(unified_guest(), &pi, &proof).map_err(|error| MixedError::Proof(AggregateVerifyError::Snark(error)))?;
    Ok(())
}

/// The pinned mixed guest's two canonical Fiat-Shamir seed halves.
pub fn mixed_guest_key() -> [u8; 32] {
    let seed = lean_vm::cpu::fs_seed(unified_guest());
    let mut key = [0; 32];
    for (i, value) in seed.iter().enumerate() {
        key[16 * i..16 * i + 8].copy_from_slice(&value.c0.to_le_bytes());
        key[16 * i + 8..16 * i + 16].copy_from_slice(&value.c1.to_le_bytes());
    }
    key
}

/// The common guest for raw leaves and every recursive level.
pub fn unified_guest() -> &'static Program {
    static GUEST: std::sync::OnceLock<Program> = std::sync::OnceLock::new();
    GUEST.get_or_init(|| {
        let mut log = 19;
        for _ in 0..8 {
            let source = runtime_guest_source(log);
            if let Ok(path) = std::env::var("DBG_MIXED_SOURCE") {
                std::fs::write(path, &source).expect("mixed source dump");
            }
            let program = compile(&lean_compiler::parse(&source).expect("mixed recursion guest parses"));
            let actual = program.prog.len().trailing_zeros() as usize;
            if log == actual {
                return program;
            }
            log = actual;
        }
        panic!("mixed recursive guest fixed point did not converge")
    })
}

fn cells(dependency: &Dependency) -> Vec<F192> {
    dependency
        .as_chunks::<16>()
        .0
        .iter()
        .map(|cell| pack_16_bytes(cell))
        .collect()
}
fn gcount(n: usize) -> F192 {
    F192::from(g_pow(n))
}
fn byte_indices(bytes: &[u8]) -> Vec<Vec<F192>> {
    let mut padded = bytes.to_vec();
    padded.push(1);
    padded.resize(padded.len().div_ceil(136) * 136, 0);
    *padded.last_mut().expect("padded hash block") ^= 128;
    padded
        .into_iter()
        .filter(|&byte| byte != 0)
        .map(|byte| vec![gcount(byte as usize)])
        .collect()
}
fn push_cell_bytes(hints: &mut Hints, bytes: &[u8]) {
    assert!(bytes.len().is_multiple_of(16));
    for cell in bytes.as_chunks::<16>().0 {
        hints.push("cell_bytes", cell.iter().map(|&byte| integer(byte as usize)).collect());
        for &byte in cell {
            hints.push("cell_index", vec![gcount(byte as usize)]);
        }
    }
}
fn push_dependency_digest(hints: &mut Hints, deps: &[Dependency]) {
    let split = deps.partition_point(|dep| dep[31] == 0x10);
    hints.push("dependency_split", vec![gcount(split), gcount(deps.len() - split)]);
    for count in [split, deps.len() - split] {
        push_block_counters(hints, count);
    }
}
fn push_block_counters(hints: &mut Hints, blocks: usize) {
    for block in 1..=blocks {
        hints.push("counter_index", vec![gcount(block & 255)]);
        hints.push("counter_index", vec![gcount(block >> 8)]);
    }
}
fn program_digest(program: &Program) -> [u8; 32] {
    let table = lean_vm::cpu::layout::bytecode_table(&program.prog);
    let bytes: Vec<_> = table.iter().flat_map(|word| word.0.to_le_bytes()).collect();
    primitives::hash::Hasher::new().update(&bytes).finalize()
}
fn push_hash_split(hints: &mut Hints, bytes: &[u8]) {
    hints.push(
        "keccak_split",
        vec![gcount(bytes.len() / 136), gcount(bytes.len() % 136)],
    );
    for entry in byte_indices(bytes) {
        hints.push("byte_index", entry);
    }
}
fn dep(scheme: u8, data: [u8; 32], key: [u8; 32]) -> Dependency {
    let mut out = [0; 96];
    out[31] = scheme;
    out[32..64].copy_from_slice(&data);
    out[64..].copy_from_slice(&key);
    out
}
fn sph_dep(pk: &SphincsPublicKey, data: [u8; 32]) -> Dependency {
    dep(0x10, data, sphincs_verification_key(pk))
}
fn push_selection(
    hints: &mut Hints,
    selected: &[Dependency],
    seen: &mut BTreeSet<Dependency>,
    dependency: &Dependency,
) {
    let index = selected
        .binary_search(dependency)
        .ok()
        .filter(|_| seen.insert(*dependency));
    hints.push(
        "selection",
        vec![integer(usize::from(index.is_some())), gcount(index.unwrap_or(0))],
    );
}

/// Verify all inputs in the guest and publish a covered canonical subset.
pub fn aggregate_mixed(
    children: &[MixedProof],
    raw_sph: &[(SphincsPublicKey, [u8; 32], SphincsSignature)],
    raw_generic: &[GenericInput<'_>],
    selected: &[Dependency],
    rate: usize,
) -> Result<MixedProof, MixedError> {
    let (guest, deferred, pi) = prepare_mixed(children, raw_sph, raw_generic, selected, rate)?;
    let (proof, _) = prove(&guest, pi, rate).map_err(MixedError::Prover)?;
    if !recursion_supported(unified_guest(), &proof) {
        return Err(MixedError::Capacity);
    }
    let result = MixedProof {
        deps: selected.to_vec(),
        deferred,
        proof,
    };
    if result.to_bytes_without_deps().len() > MAX_PAYLOAD_BYTES {
        return Err(MixedError::Capacity);
    }
    Ok(result)
}

fn prepare_mixed(
    children: &[MixedProof],
    raw_sph: &[(SphincsPublicKey, [u8; 32], SphincsSignature)],
    raw_generic: &[GenericInput<'_>],
    selected: &[Dependency],
    rate: usize,
) -> Result<(Program, DeferredClaim, [F192; 2]), MixedError> {
    prepare_mixed_with_hints(children, raw_sph, raw_generic, selected, rate, |_| {})
}

fn prepare_mixed_with_hints(
    children: &[MixedProof],
    raw_sph: &[(SphincsPublicKey, [u8; 32], SphincsSignature)],
    raw_generic: &[GenericInput<'_>],
    selected: &[Dependency],
    rate: usize,
    mutate: impl FnOnce(&mut Hints),
) -> Result<(Program, DeferredClaim, [F192; 2]), MixedError> {
    check_dependencies(selected)?;
    if children.len() > 2
        || raw_sph.len() > 4
        || raw_generic.len() > 1
        || usize::from(!children.is_empty()) + usize::from(!raw_sph.is_empty()) + usize::from(!raw_generic.is_empty())
            > 1
        || rate != LOG_INV_RATE
    {
        return Err(MixedError::Capacity);
    }
    let mut available = BTreeSet::new();
    for child in children {
        check_dependencies(&child.deps)?;
        available.extend(child.deps.iter().copied());
    }
    available.extend(raw_sph.iter().map(|(pk, data, _)| sph_dep(pk, *data)));
    for input in raw_generic {
        available.insert(dep(0x11, input.data, generic_verification_key(input.program)?));
    }
    if selected.iter().any(|dependency| !available.contains(dependency)) {
        return Err(MixedError::Dependencies);
    }
    let leaf = mixed_deferred(
        vec![F192::ZERO; mixed_vars()],
        Circuit::BOTH.map(|circuit| vec![F192::ZERO; 2 * circuit.k_log()]),
    )?;
    let mut hints = Hints::default();
    let mut seen = BTreeSet::new();
    hints.push(
        "mixed_meta",
        vec![
            gcount(selected.len()),
            gcount(raw_sph.len()),
            gcount(raw_generic.len()),
            gcount(children.len()),
        ],
    );
    let seed = lean_vm::cpu::fs_seed(unified_guest());
    hints.push("fs_seed", seed.to_vec());
    for dependency in selected {
        hints.push("dependency", cells(dependency));
    }
    push_dependency_digest(&mut hints, selected);
    hints.push(
        "leaf_defer",
        vec![
            leaf.bytecode_value,
            leaf.matrices[0].a_value,
            leaf.matrices[0].b_value,
            leaf.matrices[1].a_value,
            leaf.matrices[1].b_value,
        ],
    );
    for (pk, data, signature) in raw_sph {
        hints.push("raw_sph_claim", sphincs_signer_cells(&(*data, *pk)).to_vec());
        push_sphincs_hints(&mut hints, &(*data, *pk), signature).map_err(MixedError::Witness)?;
        push_selection(&mut hints, selected, &mut seen, &sph_dep(pk, *data));
    }
    let mut fresh = Vec::new();
    let mut carried = Vec::new();
    for input in raw_generic {
        if !generic_recursion_supported(input.program, input.proof) {
            return Err(MixedError::Capacity);
        }
        let pi = pack_hash_state(&input.data);
        let summary = verify(input.program, &pi, input.proof)
            .map_err(|error| MixedError::Proof(AggregateVerifyError::Snark(error)))?;
        hints.push(
            "program_log",
            vec![integer(input.program.prog.len().trailing_zeros() as usize)],
        );
        let code = encode_program(input.program)?;
        hints.push("code_header", code[..4].iter().map(|&x| integer(x as usize)).collect());
        for instruction in code[4..].as_chunks::<45>().0 {
            hints.push(
                "code_instruction",
                instruction.iter().map(|&x| integer(x as usize)).collect(),
            );
            let offsets: &[usize] = match instruction[0] {
                0 | 1 | 3 | 4 => &[1, 5, 9],
                2 => &[1],
                5 => &[1, 5, 9, 13, 17, 25, 41],
                6 => &[1, 5, 9, 13, 17, 21, 25, 29, 33, 37],
                _ => return Err(MixedError::Capacity),
            };
            for &offset in offsets {
                for &byte in &instruction[offset..offset + 2] {
                    hints.push("operand_index", vec![gcount(byte as usize)]);
                }
            }
        }
        push_hash_split(&mut hints, &code);
        push_block_counters(&mut hints, 2 * input.program.prog.len());
        push_cell_bytes(&mut hints, &program_digest(input.program));
        hints.push("generic_data", pi.to_vec());
        let (sub_hints, mut sub) =
            gen_verify_with_min(input.program, pi, summary, lean_vm::pcs::MIN_MU).map_err(MixedError::Witness)?;
        for (name, entry) in sub_hints {
            hints.push(name, entry);
        }
        sub.bytecode_row_point = vec![F192::ZERO; mixed_vars() - 4];
        sub.bytecode_selector_point = vec![F192::ZERO; 4];
        sub.bytecode_value = F192::ZERO;
        push_selection(
            &mut hints,
            selected,
            &mut seen,
            &dep(0x11, input.data, generic_verification_key(input.program)?),
        );
        fresh.push(sub);
        carried.push(leaf.clone());
    }
    for child in children {
        if !recursion_supported(unified_guest(), &child.proof) {
            return Err(MixedError::Capacity);
        }
        hints.push("child_count", vec![gcount(child.deps.len())]);
        for dependency in &child.deps {
            hints.push("dependency", cells(dependency));
            push_selection(&mut hints, selected, &mut seen, dependency);
        }
        push_dependency_digest(&mut hints, &child.deps);
        hints.push("child_carried", child.deferred.cells());
        let pi = mixed_statement(deps_hash(&child.deps), &child.deferred);
        let summary = verify(unified_guest(), &pi, &child.proof)
            .map_err(|error| MixedError::Proof(AggregateVerifyError::Snark(error)))?;
        let (sub_hints, sub) =
            gen_verify_with_min(unified_guest(), pi, summary, lean_vm::pcs::MIN_MU).map_err(MixedError::Witness)?;
        for (name, entry) in sub_hints {
            hints.push(name, entry);
        }
        fresh.push(sub);
        carried.push(child.deferred.clone());
    }
    let deferred = if fresh.is_empty() {
        leaf
    } else {
        let carried_refs: Vec<_> = carried.iter().collect();
        let (sub_hints, claim) =
            aggregate_deferred_claims_for_program(&fresh, &carried_refs, mixed_table(), mixed_vars());
        for (name, entry) in sub_hints {
            hints.push(name, entry);
        }
        claim
    };
    let pi = mixed_statement(deps_hash(selected), &deferred);
    mutate(&mut hints);
    let mut guest = unified_guest().clone();
    hints.install(&mut guest);
    Ok((guest, deferred, pi))
}

fn integer(n: usize) -> F192 {
    F192::new(n as u64, 0, 0)
}

fn program_seed_source() -> String {
    let mut prefix = Vec::from(*b"leanvm");
    for digest in [flock::hash::R1CS_DIGEST, flock::keccak::R1CS_DIGEST] {
        prefix.extend_from_slice(&(digest.len() as u64).to_le_bytes());
        prefix.extend_from_slice(&digest);
    }
    let mut source = String::from(
        "\ndef mixed_program_seed(table_digest):\n    byte_table = HeapBuf(256)\n    for i in unroll(0, 256):\n        byte_table[GEN ** i] = i\n    data = HeapBuf(32)\n    mixed_cell_bytes(table_digest[1], data, byte_table)\n    mixed_cell_bytes(table_digest[GEN], data * GEN ** 16, byte_table)\n",
    );
    let mut bytes: Vec<String> = prefix.iter().map(u8::to_string).collect();
    bytes.extend((0..32).map(|i| format!("data[GEN ** {i}]")));
    let length = bytes.len();
    bytes.resize(length.next_multiple_of(64), "0".to_owned());
    let packed = |slice: &[String]| {
        slice
            .iter()
            .enumerate()
            .map(|(i, value)| {
                let scale = F192::new(
                    if i < 8 { 1 << (8 * i) } else { 0 },
                    if i >= 8 { 1 << (8 * (i - 8)) } else { 0 },
                    0,
                );
                format!("({value}) * {}", f192_literal(scale))
            })
            .collect::<Vec<_>>()
            .join(" + ")
    };
    for (i, block) in bytes.as_chunks::<64>().0.iter().enumerate() {
        let halves: Vec<_> = block.as_chunks::<16>().0.iter().map(|cell| packed(cell)).collect();
        source += &format!(
            "    h{i} = StackBuf(2)\n    blake2s([{}, {}], [{}, {}], h{i}{}, counter={}, final={})\n",
            halves[0],
            halves[1],
            halves[2],
            halves[3],
            if i == 0 {
                String::new()
            } else {
                format!(", cv=h{}", i - 1)
            },
            ((i + 1) * 64).min(length),
            usize::from((i + 1) * 64 >= length)
        );
    }
    source
        + &format!(
            "    return h{}[0], h{}[1]\n",
            bytes.len() / 64 - 1,
            bytes.len() / 64 - 1
        )
}

fn preflight_payload(mut bytes: &[u8]) -> Result<(), MixedError> {
    fn take(bytes: &mut &[u8], n: usize) -> Result<(), MixedError> {
        if n > bytes.len() {
            return Err(MixedError::Encoding);
        }
        *bytes = &bytes[n..];
        Ok(())
    }
    fn length(bytes: &mut &[u8], max: usize, width: usize) -> Result<usize, MixedError> {
        let prefix = bytes.get(..8).ok_or(MixedError::Encoding)?;
        let count = usize::try_from(u64::from_le_bytes(prefix.try_into().expect("eight bytes")))
            .map_err(|_| MixedError::Encoding)?;
        take(bytes, 8)?;
        if count > max || count > bytes.len() / width {
            return Err(MixedError::Encoding);
        }
        Ok(count)
    }
    fn vector(bytes: &mut &[u8], max: usize, width: usize) -> Result<(), MixedError> {
        let count = length(bytes, max, width)?;
        take(bytes, count * width)
    }
    for _ in 0..3 {
        vector(&mut bytes, 32, 24)?;
    }
    vector(&mut bytes, STREAM_CAP, 24)?;
    let phases = length(&mut bytes, 128, 16)?;
    let mut allocation = 0usize;
    for _ in 0..phases {
        let rows = length(&mut bytes, 4096, 8)?;
        allocation += rows * 24;
        if allocation > 32 * 1024 * 1024 {
            return Err(MixedError::Encoding);
        }
        for _ in 0..rows {
            vector(&mut bytes, MAX_PAYLOAD_BYTES / 8, 8)?;
        }
        vector(&mut bytes, MAX_PAYLOAD_BYTES / 32, 32)?;
    }
    if !bytes.is_empty() {
        return Err(MixedError::Encoding);
    }
    Ok(())
}
