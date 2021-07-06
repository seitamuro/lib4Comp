#![allow(dead_code, non_snake_case)]

use std::cmp::Ordering;

fn y() {
    println!("yes");
}

fn Y() {
    println!("Yes");
}

fn n() {
    println!("no");
}

fn N() {
    println!("No");
}

#[macro_export]
macro_rules! ans {
    ($i:item) => (println!("{}", stringify!($i)))
}

/// get_divisors function returns the list of divisors of n.
fn get_divisors(n: usize) -> Vec<usize> {
    // https://algo-logic.info/divisor/
    let nsq = (n as f32).sqrt() as usize;
    let mut ans1 = Vec::new();
    let mut ans2 = Vec::new();

    for i in 1..nsq {
        if n % i == 0 {
            ans1.push(i);
            ans2.insert(0, n / i);
        }
    }

    if n % nsq == 0 {
        ans1.push(nsq);

        if n / nsq != nsq {
            ans1.push(n / nsq);
        }
    }

    ans1.append(&mut ans2);
    ans1
}

/// gcd function returns the greatest common factor of a and b.
/// For example, gcd(12, 7) returns 1.
fn gcd(a: usize, b: usize) -> usize {
    let a = a % b;

    if a == 0 {
        return b;
    }

    let greater = a.max(b);
    let smaller = a.min(b);

    gcd(greater, smaller)
}

/// lcm function returns the least common multiple of a and b.
/// For exmaple, gcd(4, 6) returns 24.
fn lcm(a: usize, b: usize) -> usize {
    a * b / gcd(a, b)
}

fn search<T: Ord>(key: T, elems: &[T]) -> Option<usize> {
    let mut low = 0;
    let mut high = elems.len();

    while low != high {
        let m = (high - low) / 2 + low;

        match elems[m].cmp(&key) {
            Ordering::Equal => return Some(m),
            Ordering::Less => {
                if m == elems.len() - 1 {
                    return None;
                }

                low = m + 1;
            }
            Ordering::Greater => {
                if m == 0 {
                    return None;
                }

                high = m - 1;
            }
        }
    }

    if elems[low] == key {
        Some(low)
    } else {
        None
    }
}

/// 幅優先探索
/// startからの各ノードへの最短距離を返す
/// path[i]はnode[i]が移動可能なノードを表す｡
fn bfs(start: usize, node: &[usize], path: &[Vec<usize>]) -> Vec<Option<usize>> {
    let mut ans = vec![None; node.len()];
    let mut todo = Vec::<usize>::new();

    ans[start] = Some(0);
    for &i in path[start].iter() {
        if ans[i] == None {
            let x = ans[start].unwrap();
            todo.push(i);
            ans[i] = Some(x + 1);
        }
    }

    while !todo.is_empty() {
        let i = todo.remove(0);

        for &node in path[i].iter() {
            if ans[node] == None {
                let x = ans[i].unwrap();
                todo.push(node);
                ans[node] = Some(x + 1);
            }
        }
    }

    ans
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd() {
        assert_eq!(gcd(2, 2), 2);
        assert_eq!(gcd(2, 6), 2);
        assert_eq!(gcd(12, 16), 4);
        assert_eq!(gcd(16, 12), 4);
        assert_eq!(gcd(123, 456), 3);
    }

    #[test]
    fn test_lcm() {
        assert_eq!(lcm(2, 2), 2);
        assert_eq!(lcm(2, 4), 4);
        assert_eq!(lcm(12, 10), 60);
        assert_eq!(lcm(6, 7), 42);
        assert_eq!(lcm(123, 456), 18696);
    }

    #[test]
    fn test_search() {
        let a = [1, 3, 6, 8, 12, 20];
        for i in 0..a.len() {
            assert_eq!(search(a[i], &a), Some(i));
        }

        assert_eq!(search(0, &a), None);
        assert_eq!(search(21, &a), None);
        assert_eq!(search(2, &a), None);
        assert_eq!(search(9, &a), None);

        let a = [1, 3, 6, 8, 12];
        for i in 0..a.len() {
            assert_eq!(search(a[i], &a), Some(i));
        }

        assert_eq!(search(0, &a), None);
        assert_eq!(search(21, &a), None);
        assert_eq!(search(2, &a), None);
        assert_eq!(search(9, &a), None);
    }

    #[test]
    fn test_bfs() {
        let a = vec![0, 1, 2, 3];
        let path = vec![vec![1, 2], vec![0, 3], vec![0, 3], vec![1, 2]];

        assert_eq!(bfs(0, &a, &path), vec![Some(0), Some(1), Some(1), Some(2)]);
    }

    #[test]
    fn test_get_divisors() {
        assert_eq!(get_divisors(36), vec![1, 2, 3, 4, 6, 9, 12, 18, 36]);
        assert_eq!(get_divisors(24), vec![1, 2, 3, 4, 6, 8, 12, 24]);
        assert_eq!(get_divisors(1), vec![1]);
    }
}
