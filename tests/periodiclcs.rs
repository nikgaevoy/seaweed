use futures::executor::block_on;
use futures::future::join_all;
use num::bigint::BigInt;
use num::One;
use seaweed::{build_affine_permutation, AffinePermutation};
use std::fs::File;
use std::io::Read;

use zip::ZipArchive;

async fn periodic_lcs(a: String, n: usize, b: String, m: i128) -> i128 {
    let braid: AffinePermutation<i128> = build_affine_permutation(
        &a.chars().collect::<Vec<_>>(),
        &b.chars().collect::<Vec<_>>(),
    );

    let repeated_braid = &braid * n;

    let ans = repeated_braid.lcs_repeat(&m);

    assert_eq!(
        ans,
        repeated_braid.lcs_len(m * repeated_braid.len() as i128)
    );

    ans
}

#[test]
fn tests_from_archive() -> std::io::Result<()> {
    let file = File::open("tests.zip")?;
    let mut zip = ZipArchive::new(file)?;

    let mut names: Vec<_> = zip
        .file_names()
        .filter(|s| !s.ends_with('/'))
        .map(|s| s.to_string())
        .collect();
    names.sort_unstable();
    let names = names;

    let mut futures = Vec::with_capacity(names.len() / 2);
    let mut answers = Vec::with_capacity(names.len() / 2);

    for pair in names.chunks(2) {
        let [test, ans] = pair else {
            panic!("Odd number of files in the archive")
        };

        assert_eq!(
            ans.rsplit_once('.'),
            Some((test.as_str(), "a")),
            "{} is not the answer to {}",
            ans,
            test
        );

        let mut unzip = |s| -> std::io::Result<String> {
            let mut res = String::new();

            zip.by_name(s)?.read_to_string(&mut res)?;

            Ok(res)
        };

        let test = unzip(test)?;
        let ans = unzip(ans)?;

        let tokens: [&str; 4] = test
            .split_whitespace()
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let [n, m, a, b] = tokens;
        let n: usize = n.parse().unwrap();
        let m = m.parse().unwrap();

        futures.push(periodic_lcs(a.to_string(), n, b.to_string(), m));
        answers.push(ans.trim().parse().unwrap());
    }

    assert_eq!(
        block_on(join_all(futures.into_iter().map(async_std::task::spawn))),
        answers
    );

    Ok(())
}

#[test]
fn test_period() {
    assert_eq!(AffinePermutation::<isize>::id(10).period(), 1);
    assert_eq!(
        build_affine_permutation::<i128, _>(b"A", b"ABABAB").period(),
        2
    );
}

#[test]
fn test_bigint() {
    let braid: AffinePermutation<BigInt> = build_affine_permutation(b"ABC", b"ABABAB");

    assert_eq!((&braid * 2u8).lcs_repeat(&BigInt::one()), 4.into());
}
