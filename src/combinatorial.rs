#![cfg_attr(feature = "const_fn", feature(rank_lookup))]
use std::convert::TryFrom;

#[cfg(feature = "rank_lookup")]
const MARKER_TABLE_SIZE: usize = 200000;
#[cfg(feature = "rank_lookup")]
static mut MARKER_TABLE: [u128; MARKER_TABLE_SIZE] = [0; MARKER_TABLE_SIZE];
#[cfg(feature = "rank_lookup")]
static mut MARKER_BITS: u8 = 0;

#[cfg(feature = "rank_lookup")]
pub fn rank(value: usize, k: u8) -> u128 {
    // note that you can only test this feature with
    // `RUST_TEST_THREADS=1 cargo test` or else you'll get tons of
    // errors because of data races between threads with different k's

    unsafe {
        // clear out the lookup table if we have a new k and fill
        // it with values for the new k
        if MARKER_BITS != k {
            let mut table_size = MARKER_TABLE_SIZE;
            if k == 1 {
                table_size = 128;
            } else if k == 2 {
                table_size = 8128;
            }
            MARKER_TABLE = [0; MARKER_TABLE_SIZE];
            MARKER_TABLE[0] = (1 << k) - 1;
            for i in 1..table_size {
                MARKER_TABLE[i] = next_rank(MARKER_TABLE[i - 1]);
            }
            MARKER_BITS = k;
        }
        // it's possible this may overflow if value > (128 choose k) or return
        // a bad value (0) if value > (128 choose k) and k == 1 or 2
        if value as usize >= MARKER_TABLE_SIZE {
            let mut marker = MARKER_TABLE[MARKER_TABLE_SIZE - 1];
            for _ in 0..(value as usize - MARKER_TABLE_SIZE) {
                marker = next_rank(marker);
            }
            marker
        } else {
            MARKER_TABLE[value as usize]
        }
    }
}

#[cfg(not(feature = "rank_lookup"))]
pub fn rank(value: usize, k: u8) -> u128 {
    // set the appropriate number of bits in the marker
    let mut marker = (1 << k) - 1 as u128;
    // just step through `value` times until we find the marker we want
    // (this could be speed up *a lot* with some kind of lookup table)
    for _ in 0..value {
        marker = next_rank(marker)
    }
    marker
    // note that we could potentially calculate this much faster for larger ranks
    // by analytically solving for the bit positions (see following for an example)
    //
    // this requires solving the equation `choose(x, n_bits) == rank` to find the
    // first bit position (x) and then updating rank and n_bits and solving again

    // from scipy.special import comb
    //
    // def rank(rank: int, bits: int) -> int:
    //     cur_rank = rank
    //     marker = 0
    //     for i in range(bits, 0, -1):
    //         # there's probably a better way to do this by skipping more values?
    //         # maybe something with b < log_i(factorial(i) * cur_rank) + i + 1 ?
    //         # (i think i inverted the binomial properly, but please check)
    //
    //         # (right now we use the fact that bit n has to be in at least the nth position)
    //         b = bits
    //         while comb(b, i) <= cur_rank:
    //             b += 1
    //         b -= 1
    //         marker += 2**b
    //         cur_rank -= comb(b, bits)
    //     return marker
    //
    // assert rank(70, 2) == 4112  # 1000000010000
    // assert rank(70, 3) == 304   # 100110000
}

#[test]
fn test_rank() {
    assert_eq!(rank(0, 3), 7);
    assert_eq!(rank(2, 3), 13);
    assert_eq!(rank(0, 3).count_ones(), 3);
    assert_eq!(rank(2, 3).count_ones(), 3);
    assert_eq!(rank(35001, 4).count_ones(), 4);

    // Maximum value of 64 choose 3
    assert_eq!(rank(41663, 3).count_ones(), 3);
}

pub fn unrank(marker: u128) -> usize {
    // val = choose(rank(0), 1) + choose(rank(1), 2) + choose(rank(2), 3) + ...
    let mut working_marker = marker;
    let mut value = 0u64;
    let mut idx = 0;
    while working_marker != 0 {
        let rank = u64::from(working_marker.trailing_zeros());
        working_marker -= 1 << rank;
        idx += 1;
        value += choose(rank, idx);
    }
    value as usize
}

#[test]
fn test_unrank() {
    // 3 bit markers
    assert_eq!(unrank(7), 0);
    assert_eq!(unrank(13), 2);
}

#[test]
fn test_rank_and_unrank() {
    for k in 1..4u8 {
        for value in [1 as usize, 23, 45].iter() {
            assert_eq!(unrank(rank(*value, k)), *value);
        }
    }
}

/// (Hopefully) fast implementation of a binomial
///
/// This uses a preset group of equations for k < 8 and then falls back to a
/// multiplicative implementation that tries to prevent overflows while
/// maintaining all results as exact integers.
#[inline]
pub fn choose(n: u64, k: u8) -> u64 {
    // (extra border condition for speed-up?)
    // if n == u64::from(k) {
    //     return 1;
    // }
    match k {
        0 => 1,
        1 => n,
        2 => n * (n - 1) / 2,
        3 => n * (n - 1) * (n - 2) / 6,
        4 => n * (n - 1) * (n - 2) * (n - 3) / 24,
        5 => n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120,
        6 => n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 720,
        7 => n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 5040,
        _ => {
            let mut num: u128 = 1;
            let mut denom: u128 = 1;
            for i in 1..=u128::from(k) {
                num *= u128::from(n) + 1 - i;
                if num % i == 0 {
                    num /= i;
                    continue;
                }
                denom *= i;
                if num % denom == 0 {
                    num /= denom;
                    denom = 1;
                }
            }
            TryFrom::try_from(num / denom)
                .unwrap_or_else(|_| panic!("{} choose {} is greater than 2**64", n, k))
            // (or recursively) choose(n - 1, k - 1) + choose(n-1, k)
            // for floats, this should work since they handle fractions:
            // (1..u64::from(k)).map(|i| (n + 1 - i) / i).product(),
        }
    }
}

#[test]
fn test_choose() {
    assert_eq!(choose(1, 1), 1);
    assert_eq!(choose(10, 1), 10);

    assert_eq!(choose(5, 2), 10);

    assert_eq!(choose(5, 3), 10);

    assert_eq!(choose(5, 4), 5);

    assert_eq!(choose(5, 5), 1);
    assert_eq!(choose(20, 5), 15504);

    assert_eq!(choose(20, 6), 38760);

    assert_eq!(choose(20, 7), 77520);
    assert_eq!(choose(23, 7), 245157);

    // test the last branch
    assert_eq!(choose(8, 8), 1);
    assert_eq!(choose(9, 8), 9);

    // every value of 64 choose n should work
    assert_eq!(choose(64, 0), 1);
    assert_eq!(choose(64, 1), 64);
    assert_eq!(choose(64, 16), 488526937079580);
    assert_eq!(choose(64, 32), 1832624140942590534);
    assert_eq!(choose(64, 48), 488526937079580);
    assert_eq!(choose(64, 63), 64);
    assert_eq!(choose(64, 64), 1);

    // super high values can overflow; these are approaching the limit
    assert_eq!(choose(128, 11), 2433440563030400);
    assert_eq!(choose(128, 13), 211709328983644800);
    assert_eq!(choose(256, 9), 11288510714272000);
}

#[test]
#[should_panic(expected = "256 choose 20 is greater than 2**64")]
fn test_choose_overflow() {
    assert_eq!(choose(256, 20), 11288510714272000);
}

#[inline]
fn next_rank(marker: u128) -> u128 {
    let t = marker | (marker - 1);
    (t + 1) | (((!t & (t + 1)) - 1) >> (marker.trailing_zeros() + 1))
}

#[test]
fn test_next_rank() {
    assert_eq!(next_rank(0b1), 0b10);
    assert_eq!(next_rank(0b100), 0b1000);

    assert_eq!(next_rank(0b111), 0b1011);
    assert_eq!(next_rank(0b1000101), 0b1000110);
}
