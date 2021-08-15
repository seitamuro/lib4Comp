#![allow(dead_code, non_snake_case)]
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};

struct CountQ {
    q: VecDeque<usize>,
    maxlen: usize,
    memo: HashMap<usize, usize>,
    count: usize,
}

impl CountQ {
    fn new(maxlen: usize) -> Self {
        Self {
            q: VecDeque::new(),
            maxlen: maxlen,
            memo: HashMap::new(),
            count: 0,
        }
    }

    fn push(&mut self, v: usize) {
        self.q.push_back(v);
        self.count += if *self.memo.get(&v).unwrap_or(&0) == 0 {1} else {0};
        self.memo.insert(v, *self.memo.get(&v).unwrap_or(&0) + 1);

        if self.q.len() > self.maxlen {
            let k = self.q.pop_front().unwrap();
            self.memo.insert(k, *self.memo.get(&k).unwrap() - 1);
            self.count -= if *self.memo.get(&k).unwrap_or(&0) == 0 {1} else {0};
        }
    }

    fn ok(&self) -> bool {
        self.q.len() == self.maxlen
    }

    fn cnt(&self) -> usize {
        self.count
    }
}

fn lower_bound<T: Ord>(list: &[T], value: T) -> Option<usize> {
    let mut lower = -1i32;
    let mut higher = list.len() as i32;
    let h = list.len() as i32 - 1;

    fn w(v: i32, low: i32, high: i32) -> usize {
        if v < low {
            return low as usize;
        } else if v > high {
            return high as usize;
        }
        v as usize
    }

    while lower != higher && higher - lower > 1 {
        let m = (higher - lower) / 2 + lower;
        if list[w(m, 0, h)] < value {
            lower = m;
        } else if list[w(m, 0, h)] >= value {
            higher = m;
        }
    }

    if higher >= list.len() as i32 {
        None
    } else {
        Some(higher as usize)
    }
}

fn higher_bound<T: Ord>(list: &[T], value: T) -> Option<usize> {
    let mut lower = -1i32;
    let mut higher = list.len() as i32;
    let h = list.len() as i32 - 1;

    fn w(v: i32, low: i32, high: i32) -> usize {
        if v < low {
            return low as usize;
        } else if v > high {
            return high as usize;
        }
        v as usize
    }

    while lower != higher && (higher - lower) > 1 {
        let m = (higher - lower) / 2 + lower;
        if list[w(m, 0, h)] <= value {
            lower = m as i32;
        } else if list[w(m, 0, h)] > value {
            higher = m as i32;
        }
    }

    if lower < 0 {
        None
    } else {
        Some(lower as usize)
    }
}

/// path: path to the other nodes
/// cost: weight of the path corresponding to each path
/// https://qiita.com/okaryo/items/8e6cd73f8a676b7a5d75
fn warshall_floyd(path: Vec<Vec<usize>>, cost: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let mut table = vec![vec![usize::MAX; path.len()]; path.len()];

    for i in 0..path.len() {
        table[i][i] = 0;
        for (j, c) in path[i].iter().zip(cost[i].iter()) {
            table[i][*j] = *c;
        }
    }

    for k in 0..path.len() {
        for i in 0..path.len() {
            for j in 0..path.len() {
                println!("{} -> {} | {} | {} {}", i, j, table[i][j], table[i][k], table[k][j]);
                table[i][j] = table[i][j].min(table[i][k].saturating_add(table[k][j]));
            }
        }
    }

    table
}

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
    ($i:item) => {
        println!("{}", stringify!($i))
    };
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

// path: Vec<(to, cost)>
#[allow(unused_assignments)]
fn dijkstra(path: &[Vec<(usize, usize)>], start: usize) -> Vec<usize> {
    let mut costs = vec![std::usize::MAX; path.len()];
    let mut todo = VecDeque::new();
    todo.push_back(start);
    costs[start] = 0;

    while !todo.is_empty() {
        let from = todo.remove(0).unwrap();
        for &(to, c) in path[from].iter() {
            let mut min = usize::MAX;
            let mut min_to = None;
            if costs[from] + c < costs[to] {
                costs[to] = costs[from] + c;
                if costs[to] < min {
                    min = costs[to];
                    min_to = Some(to);
                }
            }

            if min_to.is_some() {
                todo.push_back(min_to.unwrap());
            }
        }
    }

    costs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dijkstra() {
        let path = vec![
            vec![(3, 2), (1, 1)],
            vec![(0, 1), (4, 1)],
            vec![(0, 100), (4, 4)],
            vec![(0, 2)],
            vec![(1, 1), (2, 4)],
        ];

        assert_eq!(dijkstra(&path, 0), vec![0, 1, 6, 2, 2]);
    }

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

    #[test]
    fn test_warshall_floyd() {
        let path = vec![vec![1, 2, 3], vec![0, 3], vec![0, 3], vec![0, 1, 2]];

        let cost = vec![vec![5, 3, 8], vec![5, 2], vec![3, 20], vec![8, 2, 20]];

        let ans = vec![
            vec![0, 5, 3, 7],
            vec![5, 0, 8, 2],
            vec![3, 8, 0, 10],
            vec![7, 2, 10, 0],
        ];

        let ret = warshall_floyd(path, cost);

        assert_eq!(ret, ans);
    }

    #[test]
    fn test_lower_bound() {
        let a = vec![1, 2, 3, 4, 5, 6];
        assert_eq!(Some(2), lower_bound(&a, 3));
        assert_eq!(Some(0), lower_bound(&a, 0));
        assert_eq!(Some(0), lower_bound(&a, 1));
        assert_eq!(None, lower_bound(&a, 7));
        assert_eq!(Some(5), lower_bound(&a, 6));

        let a = vec![1, 2, 3, 4, 4, 4];
        assert_eq!(Some(2), lower_bound(&a, 3));
        assert_eq!(Some(0), lower_bound(&a, 0));
        assert_eq!(Some(0), lower_bound(&a, 1));
        assert_eq!(None, lower_bound(&a, 7));
        assert_eq!(None, lower_bound(&a, 6));
        assert_eq!(Some(3), lower_bound(&a, 4));

        let a = vec![1, 4, 4, 4, 4, 4];
        assert_eq!(Some(1), lower_bound(&a, 3));
        assert_eq!(Some(0), lower_bound(&a, 0));
        assert_eq!(Some(0), lower_bound(&a, 1));
        assert_eq!(None, lower_bound(&a, 7));
        assert_eq!(None, lower_bound(&a, 6));
        assert_eq!(Some(1), lower_bound(&a, 4));

        let a = vec![1, 1, 4, 4, 6, 6];
        assert_eq!(Some(0), lower_bound(&a, 1));
        assert_eq!(Some(2), lower_bound(&a, 4));
        assert_eq!(Some(4), lower_bound(&a, 6));
    }

    #[test]
    fn test_higher_bound() {
        let a = vec![1, 2, 3, 4, 5, 6];
        assert_eq!(Some(2), higher_bound(&a, 3));
        assert_eq!(None, higher_bound(&a, 0));
        assert_eq!(Some(0), higher_bound(&a, 1));
        assert_eq!(Some(5), higher_bound(&a, 7));
        assert_eq!(Some(5), higher_bound(&a, 6));

        let a = vec![1, 2, 3, 4, 4, 4];
        assert_eq!(Some(2), higher_bound(&a, 3));
        assert_eq!(None, higher_bound(&a, 0));
        assert_eq!(Some(0), higher_bound(&a, 1));
        assert_eq!(Some(5), higher_bound(&a, 7));
        assert_eq!(Some(5), higher_bound(&a, 6));
        assert_eq!(Some(5), higher_bound(&a, 4));

        let a = vec![1, 4, 4, 4, 4, 4];
        assert_eq!(Some(0), higher_bound(&a, 3));
        assert_eq!(None, higher_bound(&a, 0));
        assert_eq!(Some(0), higher_bound(&a, 1));
        assert_eq!(Some(5), higher_bound(&a, 7));
        assert_eq!(Some(5), higher_bound(&a, 6));
        assert_eq!(Some(5), higher_bound(&a, 4));

        let a = vec![1, 3, 3, 3, 4];
        assert_eq!(Some(4), higher_bound(&a, 4));
        assert_eq!(Some(3), higher_bound(&a, 3));
        assert_eq!(Some(0), higher_bound(&a, 1));

        let a = vec![1, 1, 3, 3, 4];
        assert_eq!(Some(1), higher_bound(&a, 1));
    }

    #[test]
    fn test_CountQ() {
        let mut q = CountQ::new(2);
        let a = [1, 1, 1, 3, 4, 5, 6];
        let mut ret = Vec::new();

        for i in a.iter() {
            let i = *i;
            q.push(i);
            if q.ok() {
                ret.push(q.cnt());
            }
        }

        assert_eq!(ret, [1, 1, 2, 2, 2, 2]);
    }
}