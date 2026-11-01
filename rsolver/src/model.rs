//! The game model: a direct port of theories/Model.v (pre-Foundations
//! damage rules only). Move lists come out in the same order as the
//! extracted OCaml, which the differential tests rely on. Natural-number
//! subtraction saturates at zero, as in Rocq.

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Player {
    A,
    B,
}

impl Player {
    pub fn opp(self) -> Player {
        match self {
            Player::A => Player::B,
            Player::B => Player::A,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Card {
    Walker,
    Elixir,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Walker {
    pub counters: u32,
    pub tapped: bool,
    pub sick: bool,
}

/// A list of at most N elements stored inline (a player has at most two
/// Walkers on the battlefield and two cards in the library).
#[derive(Clone, Copy)]
pub struct SVec<T: Copy + Default, const N: usize> {
    len: u8,
    a: [T; N],
}

impl<T: Copy + Default, const N: usize> SVec<T, N> {
    pub fn new() -> Self {
        SVec { len: 0, a: [T::default(); N] }
    }
    pub fn push(&mut self, x: T) {
        assert!((self.len as usize) < N, "SVec capacity");
        self.a[self.len as usize] = x;
        self.len += 1;
    }
    pub fn clear(&mut self) {
        self.len = 0;
    }
    pub fn remove(&mut self, i: usize) -> T {
        let x = self.a[i];
        self.a.copy_within(i + 1..self.len as usize, i);
        self.len -= 1;
        x
    }
    pub fn retain(&mut self, mut f: impl FnMut(&T) -> bool) {
        let mut k = 0;
        for i in 0..self.len as usize {
            if f(&self.a[i]) {
                self.a[k] = self.a[i];
                k += 1;
            }
        }
        self.len = k as u8;
    }
    pub fn from_slice(l: &[T]) -> Self {
        let mut v = Self::new();
        for &x in l {
            v.push(x);
        }
        v
    }
}

impl<T: Copy + Default, const N: usize> std::ops::Deref for SVec<T, N> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.a[..self.len as usize]
    }
}
impl<T: Copy + Default, const N: usize> std::ops::DerefMut for SVec<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.a[..self.len as usize]
    }
}
impl<'a, T: Copy + Default, const N: usize> IntoIterator for &'a SVec<T, N> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T: Copy + Default + PartialEq, const N: usize> PartialEq for SVec<T, N> {
    fn eq(&self, o: &Self) -> bool {
        **self == **o
    }
}
impl<T: Copy + Default + Eq, const N: usize> Eq for SVec<T, N> {}
impl<T: Copy + Default + std::hash::Hash, const N: usize> std::hash::Hash for SVec<T, N> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}
impl<T: Copy + Default + std::fmt::Debug, const N: usize> std::fmt::Debug for SVec<T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

impl Default for Walker {
    fn default() -> Self {
        Walker { counters: 0, tapped: false, sick: false }
    }
}
impl Default for Card {
    fn default() -> Self {
        Card::Walker
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Side {
    pub life: u32,
    pub city: bool,
    pub pool: u32,
    pub hand_w: u32,
    pub hand_e: bool,
    pub bf: SVec<Walker, 2>,
    pub elixir_bf: bool,
    pub thop_u: u32,
    pub thop_t: u32,
    pub library: SVec<Card, 2>,
    pub gy_w: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Step {
    Upkeep,
    DrawStep,
    Main1,
    BeginCombat,
    DeclAtk,
    DeclBlk,
    DamageStep,
    EndCombat,
    Main2,
    EndStep,
}

fn is_main(st: Step) -> bool {
    matches!(st, Step::Main1 | Step::Main2)
}

/// Declared with BT first so that the derived order matches OCaml's
/// `compare` (constant constructors before non-constant ones).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Blocker {
    BT,
    BW(u32),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Combat {
    pub atk: Vec<u32>,
    pub atk_thop: u32,
    pub blk: Vec<Vec<Blocker>>,
    pub trades: u32,
}

impl Combat {
    pub fn is_empty(&self) -> bool {
        self.atk.is_empty() && self.atk_thop == 0 && self.blk.is_empty() && self.trades == 0
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pending {
    Window(Step, Player, bool),
    ChooseAttack,
    ChooseBlock,
    ChooseOrder,
    ChooseDamage,
    ChooseShuffle(Step, Player, Vec<Card>),
    Over(Player),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct State {
    pub active: Player,
    pub first_turn: bool,
    pub side_a: Side,
    pub side_b: Side,
    pub cmb: Combat,
    pub pend: Pending,
}

/// Declared in the OCaml constructor order: constant constructors (Pass,
/// ActElixir, CastElixir) compare before the others there, which matters
/// only where moves are sorted, and those sorts only see one constructor.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Move {
    Pass,
    Pump(u32),
    ActElixir,
    CastWalker(u32),
    CastElixir,
    Attack(Vec<u32>, u32),
    Block(Vec<Option<u32>>, Vec<u32>, u32),
    Order(Vec<Vec<Blocker>>),
    Assign(Vec<u32>),
    Arrange(Vec<Card>),
}

impl State {
    pub fn side(&self, p: Player) -> &Side {
        match p {
            Player::A => &self.side_a,
            Player::B => &self.side_b,
        }
    }
    pub fn side_mut(&mut self, p: Player) -> &mut Side {
        match p {
            Player::A => &mut self.side_a,
            Player::B => &mut self.side_b,
        }
    }
}

pub fn to_move(s: &State) -> Player {
    match &s.pend {
        Pending::Window(_, p, _) => *p,
        Pending::ChooseAttack | Pending::ChooseOrder | Pending::ChooseDamage => s.active,
        Pending::ChooseBlock => s.active.opp(),
        Pending::ChooseShuffle(_, p, _) => p.opp(),
        Pending::Over(w) => *w,
    }
}

pub fn winner(s: &State) -> Option<Player> {
    match &s.pend {
        Pending::Over(w) => Some(*w),
        _ => None,
    }
}

fn start_side(walkers: u32, elixir: bool) -> Side {
    Side {
        life: 20,
        city: false,
        pool: 0,
        hand_w: walkers,
        hand_e: elixir,
        bf: SVec::new(),
        elixir_bf: false,
        thop_u: 0,
        thop_t: 0,
        library: SVec::new(),
        gy_w: 0,
    }
}

pub fn init(starter: Player) -> State {
    let mut s = State {
        active: starter,
        first_turn: true,
        side_a: start_side(2, false),
        side_b: start_side(1, true),
        cmb: Combat::default(),
        pend: Pending::Window(Step::Upkeep, starter, false),
    };
    s.side_mut(starter).city = true;
    s
}

// ---- helpers ----

fn subsets(l: &[u32]) -> Vec<Vec<u32>> {
    match l.split_first() {
        None => vec![vec![]],
        Some((&x, r)) => {
            let rs = subsets(r);
            let mut out = rs.clone();
            for v in rs {
                let mut w = vec![x];
                w.extend(v);
                out.push(w);
            }
            out
        }
    }
}

/// All lists of `len` naturals whose sum is at most `total`.
fn bounded_vectors(len: u32, total: u32) -> Vec<Vec<u32>> {
    if len == 0 {
        return vec![vec![]];
    }
    let mut out = vec![];
    for k in 0..=total {
        for v in bounded_vectors(len - 1, total - k) {
            let mut w = vec![k];
            w.extend(v);
            out.push(w);
        }
    }
    out
}

fn product<T: Clone>(choices: &[Vec<T>]) -> Vec<Vec<T>> {
    match choices.split_first() {
        None => vec![vec![]],
        Some((c, cs)) => {
            let rs = product(cs);
            let mut out = vec![];
            for x in c {
                for r in &rs {
                    let mut w = vec![x.clone()];
                    w.extend(r.iter().cloned());
                    out.push(w);
                }
            }
            out
        }
    }
}

fn cons<T: Clone>(x: &T, l: Vec<T>) -> Vec<T> {
    let mut w = Vec::with_capacity(l.len() + 1);
    w.push(x.clone());
    w.extend(l);
    w
}

/// The distinct orders of `l`'s elements (Model.orders): each distinct
/// element in the order of its last occurrence (`nodup`), first, followed
/// by the orders of the rest with its first occurrence removed.
fn orders<T: Clone + PartialEq>(l: &[T]) -> Vec<Vec<T>> {
    if l.is_empty() {
        return vec![vec![]];
    }
    let mut out = vec![];
    for (i, x) in l.iter().enumerate() {
        if l[i + 1..].contains(x) {
            continue;
        }
        let mut rest = l.to_vec();
        rest.remove(l.iter().position(|y| y == x).unwrap());
        out.extend(orders(&rest).into_iter().map(|o| cons(x, o)));
    }
    out
}

// ---- mana ----

/// Pay `n` generic mana, tapping City for {C}{C} only if the pool is short.
fn pay(n: u32, s: &Side) -> Option<Side> {
    if n <= s.pool {
        let mut s = s.clone();
        s.pool -= n;
        Some(s)
    } else if s.city && n <= s.pool + 2 {
        let mut s = s.clone();
        s.pool = s.pool + 2 - n;
        s.city = false;
        Some(s)
    } else {
        None
    }
}

fn can_pay(n: u32, s: &Side) -> bool {
    n <= s.pool || (s.city && n <= s.pool + 2)
}

fn can_pump(w: &Walker) -> bool {
    !w.tapped && !w.sick
}

fn window_moves(st: Step, p: Player, s: &State) -> Vec<Move> {
    let sd = s.side(p);
    let mut out = vec![Move::Pass];
    if can_pay(1, sd) {
        for (i, w) in sd.bf.iter().enumerate() {
            if can_pump(w) {
                out.push(Move::Pump(i as u32));
            }
        }
    }
    if sd.elixir_bf && can_pay(2, sd) {
        out.push(Move::ActElixir);
    }
    if p == s.active && is_main(st) {
        if sd.hand_w > 0 {
            out.push(Move::CastWalker(0));
            if can_pay(2, sd) {
                out.push(Move::CastWalker(1));
            }
        }
        if sd.hand_e && can_pay(1, sd) {
            out.push(Move::CastElixir);
        }
    }
    out
}

fn attack_moves(s: &State) -> Vec<Move> {
    let sd = s.side(s.active);
    let ready: Vec<u32> = sd.bf.iter().enumerate().filter(|(_, w)| can_pump(w)).map(|(i, _)| i as u32).collect();
    let mut out = vec![];
    for ws in subsets(&ready) {
        for k in 0..=sd.thop_u {
            out.push(Move::Attack(ws.clone(), k));
        }
    }
    out
}

fn block_moves(s: &State) -> Vec<Move> {
    let d = s.side(s.active.opp());
    let n = s.cmb.atk.len() as u32;
    let wchoices: Vec<Vec<Option<u32>>> = d
        .bf
        .iter()
        .map(|w| {
            if w.tapped {
                vec![None]
            } else {
                let mut c = vec![None];
                c.extend((0..n).map(Some));
                c
            }
        })
        .collect();
    let mut out = vec![];
    for wb in product(&wchoices) {
        for tb in bounded_vectors(n, d.thop_u) {
            let left = d.thop_u - tb.iter().sum::<u32>();
            for tr in 0..=left.min(s.cmb.atk_thop) {
                out.push(Move::Block(wb.clone(), tb.clone(), tr));
            }
        }
    }
    out
}

fn order_moves(s: &State) -> Vec<Move> {
    let choices: Vec<Vec<Vec<Blocker>>> = s.cmb.blk.iter().map(|b| orders(b)).collect();
    product(&choices).into_iter().map(Move::Order).collect()
}

pub fn walker_power(sd: &Side, i: u32) -> u32 {
    sd.bf.get(i as usize).map_or(0, |w| w.counters)
}

pub fn blocker_toughness(d: &Side, b: Blocker) -> u32 {
    match b {
        Blocker::BW(i) => walker_power(d, i),
        Blocker::BT => 1,
    }
}

/// Largest j such that the first j toughnesses sum to at most p.
fn max_prefix(mut p: u32, ts: &[u32]) -> u32 {
    let mut j = 0;
    for &t in ts {
        if t <= p {
            p -= t;
            j += 1;
        } else {
            break;
        }
    }
    j
}

fn kill_choices(p: u32, ts: &[u32]) -> Vec<u32> {
    match ts.first() {
        None => vec![0],
        Some(&t) => {
            if p < t {
                vec![0]
            } else {
                (1..=max_prefix(p, ts)).collect()
            }
        }
    }
}

fn damage_moves(s: &State) -> Vec<Move> {
    let a = s.side(s.active);
    let d = s.side(s.active.opp());
    let choices: Vec<Vec<u32>> = s
        .cmb
        .atk
        .iter()
        .zip(s.cmb.blk.iter())
        .map(|(&i, bs)| {
            let ts: Vec<u32> = bs.iter().map(|&b| blocker_toughness(d, b)).collect();
            kill_choices(walker_power(a, i), &ts)
        })
        .collect();
    product(&choices).into_iter().map(Move::Assign).collect()
}

pub fn moves(s: &State) -> Vec<Move> {
    match &s.pend {
        Pending::Window(st, p, _) => window_moves(*st, *p, s),
        Pending::ChooseAttack => attack_moves(s),
        Pending::ChooseBlock => block_moves(s),
        Pending::ChooseOrder => order_moves(s),
        Pending::ChooseDamage => damage_moves(s),
        Pending::ChooseShuffle(_, _, cards) => orders(cards).into_iter().map(Move::Arrange).collect(),
        Pending::Over(_) => vec![],
    }
}

// ---- turn structure ----

fn draw(sd: &mut Side) {
    if sd.library.is_empty() {
        return;
    }
    match sd.library.remove(0) {
        Card::Walker => sd.hand_w += 1,
        Card::Elixir => sd.hand_e = true,
    }
}

fn untap_side(sd: &mut Side) {
    sd.city = true;
    for w in sd.bf.iter_mut() {
        w.tapped = false;
        w.sick = false;
    }
    sd.thop_u += sd.thop_t;
    sd.thop_t = 0;
}

fn next_turn(mut s: State) -> State {
    let p = s.active.opp();
    untap_side(s.side_mut(p));
    s.active = p;
    s.first_turn = false;
    s.cmb = Combat::default();
    s.pend = Pending::Window(Step::Upkeep, p, false);
    s
}

fn end_step(st: Step, mut s: State) -> State {
    s.side_a.pool = 0;
    s.side_b.pool = 0;
    let ap = s.active;
    match st {
        Step::Upkeep => {
            if !s.first_turn {
                draw(s.side_mut(ap));
            }
            s.pend = Pending::Window(Step::DrawStep, ap, false);
            s
        }
        Step::DrawStep => {
            s.pend = Pending::Window(Step::Main1, ap, false);
            s
        }
        Step::Main1 => {
            s.pend = Pending::Window(Step::BeginCombat, ap, false);
            s
        }
        Step::BeginCombat => {
            s.pend = Pending::ChooseAttack;
            s
        }
        Step::DeclAtk => {
            s.pend = if s.cmb.atk.is_empty() && s.cmb.atk_thop == 0 {
                Pending::Window(Step::EndCombat, ap, false)
            } else {
                Pending::ChooseBlock
            };
            s
        }
        Step::DeclBlk => {
            s.pend = Pending::ChooseDamage;
            s
        }
        Step::DamageStep => {
            s.pend = Pending::Window(Step::EndCombat, ap, false);
            s
        }
        Step::EndCombat => {
            s.cmb = Combat::default();
            s.pend = Pending::Window(Step::Main2, ap, false);
            s
        }
        Step::Main2 => {
            s.pend = Pending::Window(Step::EndStep, ap, false);
            s
        }
        Step::EndStep => next_turn(s),
    }
}

// ---- effects ----

fn with_payment(n: u32, p: Player, s: State, k: impl FnOnce(State) -> State) -> State {
    match pay(n, s.side(p)) {
        Some(sd) => {
            let mut s = s;
            *s.side_mut(p) = sd;
            k(s)
        }
        None => s,
    }
}

fn do_pump(st: Step, p: Player, i: u32, s: State) -> State {
    with_payment(1, p, s, |mut s| {
        if let Some(w) = s.side_mut(p).bf.get_mut(i as usize) {
            w.counters += 1;
            w.tapped = true;
        }
        s.pend = Pending::Window(st, p, false);
        s
    })
}

fn do_elixir(st: Step, p: Player, s: State) -> State {
    with_payment(2, p, s, |mut s| {
        let sd = s.side_mut(p);
        let mut cards = sd.library.to_vec();
        cards.push(Card::Elixir);
        cards.extend(std::iter::repeat(Card::Walker).take(sd.gy_w as usize));
        sd.life += 5;
        sd.elixir_bf = false;
        sd.library.clear();
        sd.gy_w = 0;
        s.pend = Pending::ChooseShuffle(st, p, cards);
        s
    })
}

fn do_cast_walker(st: Step, p: Player, x: u32, s: State) -> State {
    with_payment(2 * x, p, s, |mut s| {
        let sd = s.side_mut(p);
        sd.hand_w = sd.hand_w.saturating_sub(1);
        if x == 0 {
            sd.gy_w += 1;
        } else {
            sd.bf.push(Walker { counters: x, tapped: false, sick: true });
        }
        s.pend = Pending::Window(st, p, false);
        s
    })
}

fn do_cast_elixir(st: Step, p: Player, s: State) -> State {
    with_payment(1, p, s, |mut s| {
        let sd = s.side_mut(p);
        sd.hand_e = false;
        sd.elixir_bf = true;
        s.pend = Pending::Window(st, p, false);
        s
    })
}

fn do_attack(ws: &[u32], k: u32, mut s: State) -> State {
    let ap = s.active;
    let sd = s.side_mut(ap);
    for &i in ws {
        if let Some(w) = sd.bf.get_mut(i as usize) {
            w.tapped = true;
        }
    }
    sd.thop_u = sd.thop_u.saturating_sub(k);
    sd.thop_t += k;
    s.cmb = Combat { atk: ws.to_vec(), atk_thop: k, blk: vec![vec![]; ws.len()], trades: 0 };
    s.pend = Pending::Window(Step::DeclAtk, ap, false);
    s
}

fn do_block(wb: &[Option<u32>], tb: &[u32], tr: u32, mut s: State) -> State {
    let n = s.cmb.atk.len();
    let blks: Vec<Vec<Blocker>> = (0..n)
        .zip(tb.iter())
        .map(|(a, &k)| {
            let mut bs: Vec<Blocker> = wb
                .iter()
                .enumerate()
                .filter(|(_, o)| **o == Some(a as u32))
                .map(|(i, _)| Blocker::BW(i as u32))
                .collect();
            bs.extend(std::iter::repeat(Blocker::BT).take(k as usize));
            bs
        })
        .collect();
    let multi = blks.iter().any(|bs| bs.len() >= 2);
    s.cmb.blk = blks;
    s.cmb.trades = tr;
    s.pend = if multi { Pending::ChooseOrder } else { Pending::Window(Step::DeclBlk, s.active, false) };
    s
}

fn do_order(os: &[Vec<Blocker>], mut s: State) -> State {
    s.cmb.blk = os.to_vec();
    s.pend = Pending::Window(Step::DeclBlk, s.active, false);
    s
}

/// Dead Walkers go to the graveyard; their controller gets one untapped
/// Thopter per counter.
fn bury(dead: &[u32], sd: &mut Side) {
    let gone: u32 = dead.iter().map(|&i| walker_power(sd, i)).sum();
    sd.gy_w += dead.len() as u32;
    sd.thop_u += gone;
    let mut i = 0;
    sd.bf.retain(|_| {
        let keep = !dead.contains(&i);
        i += 1;
        keep
    });
}

fn do_damage(js: &[u32], s: State) -> State {
    let ap = s.active;
    let dp = ap.opp();
    let a = s.side(ap);
    let d = s.side(dp);
    let c = &s.cmb;
    let mut unblocked = 0u32;
    let mut a_dead = vec![];
    let mut killed: Vec<Blocker> = vec![];
    for ((&i, bs), &j) in c.atk.iter().zip(c.blk.iter()).zip(js.iter()) {
        if bs.is_empty() {
            unblocked += walker_power(a, i);
        } else if walker_power(a, i) <= bs.iter().map(|&b| blocker_toughness(d, b)).sum::<u32>() {
            a_dead.push(i);
        }
        killed.extend(bs.iter().take(j as usize).copied());
    }
    unblocked += c.atk_thop.saturating_sub(c.trades);
    let d_dead: Vec<u32> = killed.iter().filter_map(|b| if let Blocker::BW(i) = b { Some(*i) } else { None }).collect();
    let d_thop_dead = killed.iter().filter(|b| matches!(b, Blocker::BT)).count() as u32 + c.trades;
    let trades = c.trades;
    let mut s = s;
    {
        let a = s.side_mut(ap);
        a.thop_t = a.thop_t.saturating_sub(trades);
        bury(&a_dead, a);
    }
    {
        let d = s.side_mut(dp);
        d.thop_u = d.thop_u.saturating_sub(d_thop_dead);
        bury(&d_dead, d);
    }
    s.cmb = Combat::default();
    if s.side(dp).life <= unblocked {
        s.pend = Pending::Over(ap);
    } else {
        s.side_mut(dp).life -= unblocked;
        s.pend = Pending::Window(Step::DamageStep, ap, false);
    }
    s
}

/// The transition function; only meaningful for legal moves.
pub fn step(s: &State, m: &Move) -> State {
    let s = s.clone();
    match (&s.pend, m) {
        (Pending::Window(st, p, passed), Move::Pass) => {
            let (st, p, passed) = (*st, *p, *passed);
            if passed {
                end_step(st, s)
            } else {
                let mut s = s;
                s.pend = Pending::Window(st, p.opp(), true);
                s
            }
        }
        (Pending::Window(st, p, _), Move::Pump(i)) => {
            let (st, p) = (*st, *p);
            do_pump(st, p, *i, s)
        }
        (Pending::Window(st, p, _), Move::ActElixir) => {
            let (st, p) = (*st, *p);
            do_elixir(st, p, s)
        }
        (Pending::Window(st, p, _), Move::CastWalker(x)) => {
            let (st, p) = (*st, *p);
            do_cast_walker(st, p, *x, s)
        }
        (Pending::Window(st, p, _), Move::CastElixir) => {
            let (st, p) = (*st, *p);
            do_cast_elixir(st, p, s)
        }
        (Pending::ChooseAttack, Move::Attack(ws, k)) => do_attack(ws, *k, s),
        (Pending::ChooseBlock, Move::Block(wb, tb, tr)) => do_block(wb, tb, *tr, s),
        (Pending::ChooseOrder, Move::Order(os)) => do_order(os, s),
        (Pending::ChooseDamage, Move::Assign(js)) => do_damage(js, s),
        (Pending::ChooseShuffle(st, p, _), Move::Arrange(lib)) => {
            let (st, p) = (*st, *p);
            let mut s = s;
            s.side_mut(p).library = SVec::from_slice(lib);
            s.pend = Pending::Window(st, p, false);
            s
        }
        _ => s,
    }
}

pub fn is_turn_start(s: &State) -> bool {
    matches!(s.pend, Pending::Window(Step::Upkeep, _, false))
}

/// Canonical form outside combat: Walkers sorted (as Explore.canon).
pub fn canon(s: &mut State) {
    if s.cmb.atk.is_empty() && s.cmb.atk_thop == 0 {
        s.side_a.bf.sort();
        s.side_b.bf.sort();
    }
}
