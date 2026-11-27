/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.PfaffianMatching
public import ExactMatching.Proofs.PfaffianPairingHelpers
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section

/-!
# Unconditional Mahajan–Subramanya–Vinay (`[MSV04]`) Pfaffian Clow-Sequence Algebra

Proves unconditionally (from Lean's three standard axioms alone) that for every `k ≥ 1` and every
skew-symmetric `(2k) × (2k)` matrix `A` over a commutative ring `R`, the 3-index dynamic program
`dpAns A` equals `pfaffian A`:

1. `dpAns A = ∑ W : ClowSeq k, clowSeqWeight A W` via `PartialClowSeq k t c u` induction on `t`.
2. Non-diagonal-free clow sequences have `clowSeqWeight A W = 0`.
3. Non-simple, diagonal-free clow sequences cancel via an explicit fixed-point-free, sign-reversing
   3-case involution (reverse-between-mates / split-at-same-vertex / merge-from-later-clow).
4. Simple clow sequences biject with `OrderedPairing k` with identical signed weight.
-/

namespace ExactMatching.Proofs.PfaffianClow

open scoped BigOperators

/-! ### 1. Vertex-pair primitives on `Fin (2 * k)` and skew-symmetric matrices -/

/-- Skew-symmetry of a matrix `A` over a commutative ring `R`. -/
def IsSkewSymm {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ u, A u u = 0) ∧ (∀ u v, A v u = -A u v)

/-- Pair index `⌊v / 2⌋ ∈ Fin k` of a vertex `v ∈ Fin (2 * k)`. -/
def pairOf {k : ℕ} (v : Fin (2 * k)) : Fin k :=
  ⟨v.val / 2, by omega⟩

/-- Even vertex `2 * c` of pair `c`. -/
def evenV {k : ℕ} (c : Fin k) : Fin (2 * k) :=
  ⟨2 * c.val, by omega⟩

/-- Odd vertex `2 * c + 1` of pair `c`. -/
def oddV {k : ℕ} (c : Fin k) : Fin (2 * k) :=
  ⟨2 * c.val + 1, by omega⟩

/-- Mate `v ⊕ 1` of `v` inside its pair `{2c, 2c+1}`. -/
def mate {k : ℕ} (v : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if v.val % 2 = 0 then v.val + 1 else v.val - 1, by split_ifs <;> omega⟩

/-- Sign `jSign v = +1` if `v` is even, `-1` if `v` is odd. -/
def jSign {k : ℕ} (v : Fin (2 * k)) : ℤ :=
  if v.val % 2 = 0 then 1 else -1

@[simp] lemma mate_mate {k : ℕ} (v : Fin (2 * k)) : mate (mate v) = v := by
  ext; dsimp [mate]; split_ifs <;> omega

lemma mate_ne_self {k : ℕ} (v : Fin (2 * k)) : mate v ≠ v := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [mate] at hv
  split_ifs at hv <;> omega

lemma mate_injective {k : ℕ} : Function.Injective (mate (k := k)) :=
  Function.LeftInverse.injective mate_mate

@[simp] lemma pairOf_mate {k : ℕ} (v : Fin (2 * k)) : pairOf (mate v) = pairOf v := by
  ext; dsimp [pairOf, mate]; split_ifs <;> omega

@[simp] lemma pairOf_evenV {k : ℕ} (c : Fin k) : pairOf (evenV c) = c := by
  ext; dsimp [pairOf, evenV]; omega

@[simp] lemma pairOf_oddV {k : ℕ} (c : Fin k) : pairOf (oddV c) = c := by
  ext; dsimp [pairOf, oddV]; omega

@[simp] lemma mate_evenV {k : ℕ} (c : Fin k) : mate (evenV c) = oddV c := by
  ext; dsimp [mate, evenV, oddV]
  have h : 2 * c.val % 2 = 0 := by omega
  simp [h]

@[simp] lemma mate_oddV {k : ℕ} (c : Fin k) : mate (oddV c) = evenV c := by
  ext; dsimp [mate, evenV, oddV]
  have h : (2 * c.val + 1) % 2 ≠ 0 := by omega
  simp [h]

lemma evenV_ne_oddV {k : ℕ} (c : Fin k) : evenV c ≠ oddV c := by
  intro h; have := congrArg Fin.val h; dsimp [evenV, oddV] at this; omega

lemma evenV_injective {k : ℕ} : Function.Injective (evenV (k := k)) := by
  intro a b h; have := congrArg Fin.val h; dsimp [evenV] at this; ext; omega

lemma oddV_injective {k : ℕ} : Function.Injective (oddV (k := k)) := by
  intro a b h; have := congrArg Fin.val h; dsimp [oddV] at this; ext; omega

lemma evenV_ne_oddV_any {k : ℕ} (a b : Fin k) : evenV a ≠ oddV b := by
  intro h; have := congrArg Fin.val h; dsimp [evenV, oddV] at this; omega

@[simp] lemma jSign_evenV {k : ℕ} (c : Fin k) : jSign (evenV c) = 1 := by
  dsimp [jSign, evenV]; split_ifs <;> omega

@[simp] lemma jSign_oddV {k : ℕ} (c : Fin k) : jSign (oddV c) = -1 := by
  dsimp [jSign, oddV]; split_ifs <;> omega

@[simp] lemma jSign_mate {k : ℕ} (v : Fin (2 * k)) : jSign (mate v) = -jSign v := by
  dsimp [jSign, mate]; split_ifs <;> omega

lemma jSign_mul_self {k : ℕ} {R : Type*} [CommRing R] (v : Fin (2 * k)) :
    (jSign v : R) * (jSign v : R) = 1 := by
  dsimp [jSign]; split_ifs <;> norm_num

lemma eq_evenV_or_oddV {k : ℕ} (v : Fin (2 * k)) :
    v = evenV (pairOf v) ∨ v = oddV (pairOf v) := by
  by_cases h : v.val % 2 = 0
  · left; ext; dsimp [evenV, pairOf]; omega
  · right; ext; dsimp [oddV, pairOf]; omega

lemma pairOf_eq_iff {k : ℕ} {u v : Fin (2 * k)} :
    pairOf u = pairOf v ↔ u = v ∨ u = mate v := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    dsimp [pairOf] at hv
    by_cases heq : u.val = v.val
    · left; exact Fin.ext heq
    · right; ext; dsimp [mate]; split_ifs <;> omega
  · rintro (rfl | rfl)
    · rfl
    · exact pairOf_mate v

/-- Universal skew-symmetric `(2k) × (2k)` matrix over `ℤ[y_0, ..., y_{m-1}]`. -/
noncomputable def univSkewMat (k : ℕ) :
    Matrix (Fin (2 * k)) (Fin (2 * k))
      (MvPolynomial (Fin (Fintype.card (UpperPair (2 * k)))) ℤ) :=
  fun u v =>
    if hlt : u < v then
      MvPolynomial.X (upperPairEquiv (2 * k) ⟨(u, v), hlt⟩)
    else if hgt : v < u then
      -MvPolynomial.X (upperPairEquiv (2 * k) ⟨(v, u), hgt⟩)
    else 0

lemma univSkewMat_isSkewSymm (k : ℕ) : IsSkewSymm (univSkewMat k) := by
  refine ⟨fun u => ?_, fun u v => ?_⟩
  · simp [univSkewMat]
  · unfold univSkewMat
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · have hnot : ¬ (v < u) := lt_asymm hlt
      simp [hlt, hnot]
    · simp
    · have hnot : ¬ (u < v) := lt_asymm hgt
      simp [hgt, hnot]

lemma pfaffian_univSkewMat (k : ℕ) :
    pfaffian (univSkewMat k) =
      MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k) := by
  unfold pfaffian universalPfaffian
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPolynomial.rename_C, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MvPolynomial.rename_X]
  unfold univSkewMat
  have hlt := m.pair_lt i
  simp [hlt]

/-! ### 2. Alternating walk & cyclic walk weights (`pathWeight`, `cycWeight`) -/

/-- Mate-reversal of a vertex list: `revMate [w_0, ..., w_{m-1}] = [mate w_{m-1}, ..., mate w_0]`. -/
def revMate {k : ℕ} (ws : List (Fin (2 * k))) : List (Fin (2 * k)) :=
  (ws.map mate).reverse

@[simp] lemma revMate_nil {k : ℕ} : revMate ([] : List (Fin (2 * k))) = [] := rfl

@[simp] lemma revMate_singleton {k : ℕ} (v : Fin (2 * k)) : revMate [v] = [mate v] := rfl

lemma revMate_append {k : ℕ} (a b : List (Fin (2 * k))) :
    revMate (a ++ b) = revMate b ++ revMate a := by
  simp [revMate, List.map_append, List.reverse_append]

@[simp] lemma revMate_revMate {k : ℕ} (ws : List (Fin (2 * k))) :
    revMate (revMate ws) = ws := by
  simp [revMate, List.map_reverse, List.map_map, Function.comp_def]

@[simp] lemma revMate_length {k : ℕ} (ws : List (Fin (2 * k))) :
    (revMate ws).length = ws.length := by
  simp [revMate]

lemma mem_revMate_iff {k : ℕ} {v : Fin (2 * k)} {ws : List (Fin (2 * k))} :
    v ∈ revMate ws ↔ mate v ∈ ws := by
  simp only [revMate, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨mate v, h, mate_mate v⟩

lemma map_pairOf_revMate {k : ℕ} (ws : List (Fin (2 * k))) :
    (revMate ws).map pairOf = (ws.map pairOf).reverse := by
  simp [revMate, List.map_reverse, List.map_map, Function.comp_def]

/-- Alternating walk weight starting from `u` along vertex list `ws`. -/
def pathWeight {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) :
    Fin (2 * k) → List (Fin (2 * k)) → R
  | _, [] => 1
  | u, w :: ws => A u w * (jSign w : R) * pathWeight A (mate w) ws

@[simp] lemma pathWeight_nil {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (u : Fin (2 * k)) :
    pathWeight A u [] = 1 := rfl

@[simp] lemma pathWeight_cons {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (u w : Fin (2 * k)) (ws : List (Fin (2 * k))) :
    pathWeight A u (w :: ws) = A u w * (jSign w : R) * pathWeight A (mate w) ws := rfl

lemma pathWeight_append {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R)
    (u : Fin (2 * k)) (a b : List (Fin (2 * k))) :
    pathWeight A u (a ++ b) =
      pathWeight A u a *
        pathWeight A (match a.getLast? with | none => u | some x => mate x) b := by
  induction a generalizing u with
  | nil => simp [pathWeight]
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp [pathWeight, mul_assoc]
    | cons w2 ws2 =>
      rw [List.cons_append, pathWeight_cons, ih (mate w), List.getLast?_cons_cons]
      have hne : (w2 :: ws2).getLast? ≠ none := by simp
      cases hl : (w2 :: ws2).getLast? with
      | none => exact absurd hl hne
      | some x => simp only [pathWeight_cons, mul_assoc]

/-- Cyclic alternating walk weight of `ws`. -/
def cycWeight {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (ws : List (Fin (2 * k))) : R :=
  match ws.getLast? with
  | none => 1
  | some last => pathWeight A (mate last) ws

/-- Identity 1 (Rotation invariance): `cycWeight A (a ++ b) = cycWeight A (b ++ a)`. -/
lemma cycWeight_append_comm {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (a b : List (Fin (2 * k))) :
    cycWeight A (a ++ b) = cycWeight A (b ++ a) := by
  cases ha : a.getLast? with
  | none =>
    have ha0 : a = [] := List.getLast?_eq_none_iff.mp ha
    subst ha0; simp
  | some la =>
    cases hb : b.getLast? with
    | none =>
      have hb0 : b = [] := List.getLast?_eq_none_iff.mp hb
      subst hb0; simp
    | some lb =>
      have hne_a : a ≠ [] := fun h => by simp [h] at ha
      have hne_b : b ≠ [] := fun h => by simp [h] at hb
      unfold cycWeight
      rw [List.getLast?_append_of_ne_nil a hne_b, hb,
          List.getLast?_append_of_ne_nil b hne_a, ha]
      dsimp only
      rw [pathWeight_append, pathWeight_append, ha, hb]
      exact mul_comm _ _

/-- Identity 3 (Split/merge at same vertex `v`):
`cycWeight A ((a ++ [v]) ++ (b ++ [v])) = cycWeight A (a ++ [v]) * cycWeight A (b ++ [v])`. -/
lemma cycWeight_split_same {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R)
    (a b : List (Fin (2 * k))) (v : Fin (2 * k)) :
    cycWeight A ((a ++ [v]) ++ (b ++ [v])) =
      cycWeight A (a ++ [v]) * cycWeight A (b ++ [v]) := by
  unfold cycWeight
  have h1 : (a ++ [v]).getLast? = some v := by simp
  have h2 : (b ++ [v]).getLast? = some v := by simp
  have h3 : ((a ++ [v]) ++ (b ++ [v])).getLast? = some v := by
    rw [List.getLast?_append_of_ne_nil _ (by simp), h2]
  rw [h1, h2, h3]
  dsimp only
  rw [pathWeight_append, h1]

/-- Key path-reversal sign identity for skew-symmetric `A`. -/
lemma jSign_mul_pathWeight_revMate {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (u v : Fin (2 * k)) (b : List (Fin (2 * k))) :
    (jSign v : R) * pathWeight A v (revMate b ++ [u]) =
      -((jSign u : R) * pathWeight A u (b ++ [v])) := by
  induction b generalizing u with
  | nil =>
    simp only [revMate_nil, List.nil_append, pathWeight_cons, pathWeight_nil, mul_one]
    rw [hA.2 u v]
    ring
  | cons x bs ih =>
    have hrev : revMate (x :: bs) ++ [u] = (revMate bs ++ [mate x]) ++ [u] := by
      change revMate ([x] ++ bs) ++ [u] = _
      rw [revMate_append, revMate_singleton, List.append_assoc]
    rw [hrev, pathWeight_append]
    have hlast : (revMate bs ++ [mate x]).getLast? = some (mate x) := by simp
    rw [hlast]; dsimp only; rw [mate_mate]
    simp only [List.cons_append, pathWeight_cons, pathWeight_nil, mul_one]
    have hih := ih (mate x)
    have hjm : ((jSign (mate x) : ℤ) : R) = -((jSign x : ℤ) : R) := by
      rw [jSign_mate]; push_cast; rfl
    rw [hjm] at hih
    calc
      (jSign v : R) * (pathWeight A v (revMate bs ++ [mate x]) * (A x u * (jSign u : R)))
          = ((jSign v : R) * pathWeight A v (revMate bs ++ [mate x])) * (A x u * (jSign u : R)) := by ring
      _ = (-(-(jSign x : R) * pathWeight A (mate x) (bs ++ [v]))) * (A x u * (jSign u : R)) := by
            rw [hih]
      _ = ((jSign x : R) * pathWeight A (mate x) (bs ++ [v])) * ((-A u x) * (jSign u : R)) := by
            rw [hA.2 u x]; ring
      _ = -((jSign u : R) * (A u x * (jSign x : R) * pathWeight A (mate x) (bs ++ [v]))) := by ring

/-- Identity 2 (Mate-reversal invariance of `cycWeight`):
`cycWeight A (revMate ws) = cycWeight A ws`. -/
lemma cycWeight_revMate {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (ws : List (Fin (2 * k))) :
    cycWeight A (revMate ws) = cycWeight A ws := by
  cases h : ws.reverse with
  | nil =>
    have h0 : ws = [] := List.reverse_eq_nil_iff.mp h
    subst h0; rfl
  | cons x xr =>
    have hws : ws = xr.reverse ++ [x] := by
      have := congrArg List.reverse h
      simpa using this
    rw [hws]
    have h1 : revMate (xr.reverse ++ [x]) = [mate x] ++ revMate xr.reverse := by
      rw [revMate_append, revMate_singleton]
    rw [h1, cycWeight_append_comm]
    unfold cycWeight
    have hl1 : (revMate xr.reverse ++ [mate x]).getLast? = some (mate x) := by simp
    have hl2 : (xr.reverse ++ [x]).getLast? = some x := by simp
    rw [hl1, hl2]; dsimp only; rw [mate_mate]
    have hkey := jSign_mul_pathWeight_revMate hA (mate x) x xr.reverse
    have hjm : ((jSign (mate x) : ℤ) : R) = -((jSign x : ℤ) : R) := by
      rw [jSign_mate]; push_cast; rfl
    rw [hjm] at hkey
    have hstep : (jSign x : R) * ((jSign x : R) * pathWeight A x (revMate xr.reverse ++ [mate x])) =
        (jSign x : R) * ((jSign x : R) * pathWeight A (mate x) (xr.reverse ++ [x])) := by
      rw [hkey]; ring
    rw [← mul_assoc, ← mul_assoc, jSign_mul_self, one_mul, one_mul] at hstep
    exact hstep

/-- Identity 4 (Reverse-between-mates sign flip):
`cycWeight A ((a ++ [v]) ++ (revMate b ++ [mate v])) = -cycWeight A ((a ++ [v]) ++ (b ++ [mate v]))`. -/
lemma cycWeight_reverse_between_mates {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (a b : List (Fin (2 * k))) (v : Fin (2 * k)) :
    cycWeight A ((a ++ [v]) ++ (revMate b ++ [mate v])) =
      -cycWeight A ((a ++ [v]) ++ (b ++ [mate v])) := by
  unfold cycWeight
  have h1 : ((a ++ [v]) ++ (revMate b ++ [mate v])).getLast? = some (mate v) := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
  have h2 : ((a ++ [v]) ++ (b ++ [mate v])).getLast? = some (mate v) := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
  have h3 : (a ++ [v]).getLast? = some v := by simp
  rw [h1, h2]; dsimp only; rw [mate_mate]
  conv_lhs => rw [pathWeight_append, h3]
  conv_rhs => rw [pathWeight_append, h3]
  dsimp only
  have hkey := jSign_mul_pathWeight_revMate hA (mate v) (mate v) b
  have hneg : pathWeight A (mate v) (revMate b ++ [mate v]) =
      -pathWeight A (mate v) (b ++ [mate v]) := by
    have hstep :
        (jSign (mate v) : R) * ((jSign (mate v) : R) * pathWeight A (mate v) (revMate b ++ [mate v])) =
        (jSign (mate v) : R) * (-((jSign (mate v) : R) * pathWeight A (mate v) (b ++ [mate v]))) := by
      rw [hkey]
    have hmul : (jSign (mate v) : R) * (jSign (mate v) : R) = 1 := jSign_mul_self (mate v)
    calc
      pathWeight A (mate v) (revMate b ++ [mate v])
          = ((jSign (mate v) : R) * (jSign (mate v) : R)) *
              pathWeight A (mate v) (revMate b ++ [mate v]) := by rw [hmul, one_mul]
      _ = (jSign (mate v) : R) * ((jSign (mate v) : R) *
              pathWeight A (mate v) (revMate b ++ [mate v])) := by ring
      _ = (jSign (mate v) : R) * (-((jSign (mate v) : R) *
              pathWeight A (mate v) (b ++ [mate v]))) := hstep
      _ = -(((jSign (mate v) : R) * (jSign (mate v) : R)) *
              pathWeight A (mate v) (b ++ [mate v])) := by ring
      _ = -pathWeight A (mate v) (b ++ [mate v]) := by rw [hmul, one_mul]
  rw [hneg]; ring

/-- If `ws` contains two consecutive vertices `x, mate x`, then `pathWeight A u ws = 0`. -/
lemma pathWeight_eq_zero_of_adj_mate {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (u x : Fin (2 * k)) (a b : List (Fin (2 * k))) :
    pathWeight A u (a ++ [x, mate x] ++ b) = 0 := by
  have h1 : a ++ [x, mate x] ++ b = (a ++ [x]) ++ (mate x :: b) := by simp
  rw [h1, pathWeight_append]
  have hl : (a ++ [x]).getLast? = some x := by simp
  rw [hl, pathWeight_cons, hA.1 (mate x)]
  simp

/-! ### 3. Clows, Clow Sequences, Partial Clow Sequences, and the 3-Index DP -/

/-- A single clow of head `c : Fin k`: intermediate vertices `mid` all have `pairOf v > c`,
and the closing vertex is `oddV c`. -/
structure Clow (k : ℕ) where
  head : Fin k
  mid : List (Fin (2 * k))
  mid_gt : ∀ v ∈ mid, head < pairOf v

instance instDecidableEqClow (k : ℕ) : DecidableEq (Clow k) := fun a b =>
  if h1 : a.head = b.head then
    if h2 : a.mid = b.mid then
      isTrue (by cases a; cases b; cases h1; cases h2; rfl)
    else
      isFalse (fun h => h2 (by cases h; rfl))
  else
    isFalse (fun h => h1 (by cases h; rfl))

/-- Full vertex list `mid ++ [oddV head]` of a clow (nonempty, length `mid.length + 1`). -/
def Clow.verts {k : ℕ} (C : Clow k) : List (Fin (2 * k)) :=
  C.mid ++ [oddV C.head]

/-- Length `|mid| + 1 ≥ 1` of a clow. -/
def Clow.len {k : ℕ} (C : Clow k) : ℕ :=
  C.mid.length + 1

lemma Clow.verts_length {k : ℕ} (C : Clow k) : C.verts.length = C.len := by
  simp [Clow.verts, Clow.len]

lemma Clow.verts_ne_nil {k : ℕ} (C : Clow k) : C.verts ≠ [] := by
  simp [Clow.verts]

lemma Clow.verts_getLast? {k : ℕ} (C : Clow k) : C.verts.getLast? = some (oddV C.head) := by
  simp [Clow.verts]

lemma Clow.head_le_pairOf_verts {k : ℕ} (C : Clow k) {v : Fin (2 * k)} (hv : v ∈ C.verts) :
    C.head ≤ pairOf v := by
  simp only [Clow.verts, List.mem_append, List.mem_singleton] at hv
  rcases hv with hm | rfl
  · exact le_of_lt (C.mid_gt v hm)
  · simp

lemma Clow.head_not_mem_mid_pairs {k : ℕ} (C : Clow k) :
    C.head ∉ C.mid.map pairOf := by
  intro h
  rcases List.mem_map.mp h with ⟨v, hv, heq⟩
  have hlt := C.mid_gt v hv
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- Weight of a single clow: `-cycWeight A C.verts`
(`= pathWeight A (evenV C.head) C.mid * A (last_u) (oddV C.head)`). -/
def clowWeight {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (C : Clow k) : R :=
  -cycWeight A C.verts

/-- Equivalent explicit product form of `clowWeight`: avoids the trailing `jSign (oddV c) = -1`. -/
lemma clowWeight_eq_path {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (C : Clow k) :
    clowWeight A C =
      pathWeight A (evenV C.head) C.mid *
        A (match C.mid.getLast? with | none => evenV C.head | some v => mate v) (oddV C.head) := by
  unfold clowWeight cycWeight
  rw [C.verts_getLast?]; dsimp only; rw [mate_oddV]
  unfold Clow.verts
  rw [pathWeight_append]
  simp only [pathWeight_cons, pathWeight_nil, jSign_oddV, Int.cast_neg, Int.cast_one, mul_one]
  ring

/-- A clow is diagonal-free iff no two consecutive elements of `mid` satisfy `w_{i+1} = mate w_i`. -/
def IsDiagFreeList {k : ℕ} : List (Fin (2 * k)) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y ≠ mate x ∧ IsDiagFreeList (y :: rest)

instance instDecidableIsDiagFreeList {k : ℕ} : ∀ l : List (Fin (2 * k)), Decidable (IsDiagFreeList l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | x :: y :: rest =>
    haveI := instDecidableIsDiagFreeList (y :: rest)
    inferInstanceAs (Decidable (y ≠ mate x ∧ IsDiagFreeList (y :: rest)))

lemma isDiagFreeList_iff_not_exists_adj {k : ℕ} (l : List (Fin (2 * k))) :
    ¬ IsDiagFreeList l ↔ ∃ a b x, l = a ++ [x, mate x] ++ b := by
  induction l with
  | nil =>
    simp [IsDiagFreeList]
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [IsDiagFreeList, not_true_eq_false, false_iff, not_exists]
      intro a b z h
      have hlen := congrArg List.length h
      simp at hlen
      omega
    | cons y rest' =>
      simp only [IsDiagFreeList, not_and_or, not_ne_iff]
      rw [ih]
      constructor
      · rintro (rfl | ⟨a, b, z, h⟩)
        · exact ⟨[], rest', x, rfl⟩
        · exact ⟨x :: a, b, z, by simp [h]⟩
      · rintro ⟨a, b, z, h⟩
        cases a with
        | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          rcases h with ⟨rfl, rfl, _⟩
          left; rfl
        | cons a0 a' =>
          simp only [List.cons_append, List.cons.injEq] at h
          rcases h with ⟨_, htail⟩
          right; exact ⟨a', b, z, htail⟩

lemma isDiagFreeList_append_iff {k : ℕ} (a b : List (Fin (2 * k))) :
    IsDiagFreeList (a ++ b) ↔
      IsDiagFreeList a ∧ IsDiagFreeList b ∧
        ∀ x y, a.getLast? = some x → b.head? = some y → y ≠ mate x := by
  induction a with
  | nil => simp [IsDiagFreeList]
  | cons u us ih =>
    cases us with
    | nil =>
      cases b with
      | nil => simp [IsDiagFreeList]
      | cons v vs => simp [IsDiagFreeList, and_comm]
    | cons u2 us2 =>
      simp only [List.cons_append, IsDiagFreeList, ih, List.getLast?_cons_cons]
      tauto

lemma isDiagFreeList_revMate {k : ℕ} (l : List (Fin (2 * k))) :
    IsDiagFreeList (revMate l) ↔ IsDiagFreeList l := by
  suffices ∀ m : List (Fin (2 * k)), IsDiagFreeList m → IsDiagFreeList (revMate m) by
    exact ⟨fun h => by simpa [revMate_revMate] using this (revMate l) h, this l⟩
  intro m hm
  by_contra hnot
  rw [isDiagFreeList_iff_not_exists_adj] at hnot
  rcases hnot with ⟨a, b, x, heq⟩
  have hrev := congrArg revMate heq
  rw [revMate_revMate, revMate_append, revMate_append] at hrev
  have hpair : revMate [x, mate x] = [x, mate x] := by
    simp [revMate, mate_mate]
  rw [hpair] at hrev
  have hbad : ¬ IsDiagFreeList m := (isDiagFreeList_iff_not_exists_adj m).mpr
    ⟨revMate b, revMate a, x, by simpa [List.append_assoc] using hrev⟩
  exact hbad hm

lemma isDiagFreeList_of_pairOf_nodup {k : ℕ} (l : List (Fin (2 * k)))
    (h : (l.map pairOf).Nodup) : IsDiagFreeList l := by
  induction l with
  | nil => trivial
  | cons x rest ih =>
    cases rest with
    | nil => trivial
    | cons y rest' =>
      rw [List.map_cons, List.nodup_cons] at h
      refine ⟨?_, ih h.2⟩
      intro hy
      have hp : pairOf x = pairOf y := by rw [hy, pairOf_mate]
      exact h.1 (by simp [hp])

lemma clowWeight_eq_zero_of_not_diagFree {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (C : Clow k) (h : ¬ IsDiagFreeList C.mid) :
    clowWeight A C = 0 := by
  rw [isDiagFreeList_iff_not_exists_adj] at h
  rcases h with ⟨a, b, x, hmid⟩
  rw [clowWeight_eq_path, hmid, pathWeight_eq_zero_of_adj_mate hA, zero_mul]

/-- A clow sequence of total length `k` with strictly increasing heads. -/
structure ClowSeq (k : ℕ) where
  clows : List (Clow k)
  heads_strict : (clows.map Clow.head).Pairwise (· < ·)
  total_len : (clows.map Clow.len).sum = k

instance instDecidableEqClowSeq (k : ℕ) : DecidableEq (ClowSeq k) := fun a b =>
  if h : a.clows = b.clows then
    isTrue (by cases a; cases b; cases h; rfl)
  else
    isFalse (fun hab => h (by cases hab; rfl))

/-- Weight of a clow sequence: product of weights of its clows. -/
def clowSeqWeight {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (W : ClowSeq k) : R :=
  (W.clows.map (clowWeight A)).prod

/-- Encode a list of clows as tagged steps `(head, vertex)`. -/
def clowsToSteps {k : ℕ} (cs : List (Clow k)) : List (Fin k × Fin (2 * k)) :=
  cs.flatMap (fun C => C.verts.map (fun v => (C.head, v)))

lemma clowsToSteps_length {k : ℕ} (cs : List (Clow k)) :
    (clowsToSteps cs).length = (cs.map Clow.len).sum := by
  induction cs with
  | nil => rfl
  | cons C rest ih =>
    simp [clowsToSteps, List.flatMap_cons, Clow.verts_length, ih]

lemma clowsToSteps_injective {k : ℕ} {cs₁ cs₂ : List (Clow k)}
    (h₁ : (cs₁.map Clow.head).Pairwise (· < ·))
    (h₂ : (cs₂.map Clow.head).Pairwise (· < ·))
    (heq : clowsToSteps cs₁ = clowsToSteps cs₂) : cs₁ = cs₂ := by
  induction cs₁ generalizing cs₂ with
  | nil =>
    cases cs₂ with
    | nil => rfl
    | cons C₂ r₂ =>
      have hlen := congrArg List.length heq
      simp [clowsToSteps_length, Clow.len] at hlen; omega
  | cons C₁ r₁ ih =>
    cases cs₂ with
    | nil =>
      have hlen := congrArg List.length heq
      simp [clowsToSteps_length, Clow.len] at hlen
    | cons C₂ r₂ =>
      simp only [List.map_cons, List.pairwise_cons] at h₁ h₂
      have hfirst : (C₁.head, (C₁.verts.head C₁.verts_ne_nil)) =
          (C₂.head, (C₂.verts.head C₂.verts_ne_nil)) := by
        have h1 : (clowsToSteps (C₁ :: r₁)).head? =
            some (C₁.head, C₁.verts.head C₁.verts_ne_nil) := by
          have hcons : clowsToSteps (C₁ :: r₁) =
              C₁.verts.map (fun v => (C₁.head, v)) ++ clowsToSteps r₁ := rfl
          rw [hcons, List.head?_append_of_ne_nil _ (by simp [C₁.verts_ne_nil]),
              List.head?_map, List.head?_eq_some_head C₁.verts_ne_nil]
          rfl
        have h2 : (clowsToSteps (C₂ :: r₂)).head? =
            some (C₂.head, C₂.verts.head C₂.verts_ne_nil) := by
          have hcons : clowsToSteps (C₂ :: r₂) =
              C₂.verts.map (fun v => (C₂.head, v)) ++ clowsToSteps r₂ := rfl
          rw [hcons, List.head?_append_of_ne_nil _ (by simp [C₂.verts_ne_nil]),
              List.head?_map, List.head?_eq_some_head C₂.verts_ne_nil]
          rfl
        rw [heq] at h1
        exact Option.some.inj (h1.symm.trans h2)
      have hhead : C₁.head = C₂.head := congrArg Prod.fst hfirst
      -- All elements of r₁ have head > C₁.head, and similarly for r₂
      have htake1 : (clowsToSteps (C₁ :: r₁)).takeWhile (fun p => decide (p.1 = C₁.head)) =
          C₁.verts.map (fun v => (C₁.head, v)) := by
        have hcons : clowsToSteps (C₁ :: r₁) =
            C₁.verts.map (fun v => (C₁.head, v)) ++ clowsToSteps r₁ := rfl
        rw [hcons, List.takeWhile_append_of_pos]
        · have hrest : (clowsToSteps r₁).takeWhile (fun p => decide (p.1 = C₁.head)) = [] := by
            cases hr : clowsToSteps r₁ with
            | nil => rfl
            | cons p ps =>
              have hmem : p ∈ clowsToSteps r₁ := by rw [hr]; exact List.mem_cons_self
              rcases List.mem_flatMap.mp hmem with ⟨D, hD, hp⟩
              rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
              have hlt := h₁.1 D.head (List.mem_map_of_mem hD)
              simp [List.takeWhile_cons, ne_of_gt hlt]
          rw [hrest, List.append_nil]
        · intro p hp
          rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
          simp
      have htake2 : (clowsToSteps (C₂ :: r₂)).takeWhile (fun p => decide (p.1 = C₁.head)) =
          C₂.verts.map (fun v => (C₂.head, v)) := by
        have hcons : clowsToSteps (C₂ :: r₂) =
            C₂.verts.map (fun v => (C₂.head, v)) ++ clowsToSteps r₂ := rfl
        rw [hcons, List.takeWhile_append_of_pos]
        · have hrest : (clowsToSteps r₂).takeWhile (fun p => decide (p.1 = C₁.head)) = [] := by
            cases hr : clowsToSteps r₂ with
            | nil => rfl
            | cons p ps =>
              have hmem : p ∈ clowsToSteps r₂ := by rw [hr]; exact List.mem_cons_self
              rcases List.mem_flatMap.mp hmem with ⟨D, hD, hp⟩
              rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
              have hlt := h₂.1 D.head (List.mem_map_of_mem hD)
              rw [← hhead] at hlt
              simp [List.takeWhile_cons, ne_of_gt hlt]
          rw [hrest, List.append_nil]
        · intro p hp
          rcases List.mem_map.mp hp with ⟨_, _, rfl⟩
          simp [hhead]
      have hverts_map : C₁.verts.map (fun v => (C₁.head, v)) =
          C₂.verts.map (fun v => (C₂.head, v)) := by
        rw [← htake1, ← htake2, heq]
      have hverts : C₁.verts = C₂.verts := by
        have := congrArg (List.map Prod.snd) hverts_map
        simpa [List.map_map, Function.comp_def] using this
      have hmid : C₁.mid = C₂.mid := by
        have := congrArg List.dropLast hverts
        simpa [Clow.verts] using this
      have hC : C₁ = C₂ := by
        cases C₁; cases C₂; simp only [Clow.mk.injEq]; exact ⟨hhead, hmid⟩
      subst hC
      have htail : clowsToSteps r₁ = clowsToSteps r₂ := by
        unfold clowsToSteps at heq
        simp only [List.flatMap_cons] at heq
        exact List.append_cancel_left heq
      rw [ih h₁.2 h₂.2 htail]

/-- Inject `ClowSeq k` into `Fin k → Fin k × Fin (2 * k)` to obtain `Fintype (ClowSeq k)`. -/
def ClowSeq.toFun {k : ℕ} (W : ClowSeq k) : Fin k → Fin k × Fin (2 * k) :=
  fun i => (clowsToSteps W.clows)[i.val]'(by rw [clowsToSteps_length, W.total_len]; exact i.isLt)

lemma ClowSeq.toFun_injective (k : ℕ) : Function.Injective (ClowSeq.toFun (k := k)) := by
  intro W₁ W₂ h
  have hsteps : clowsToSteps W₁.clows = clowsToSteps W₂.clows := by
    refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
    · rw [clowsToSteps_length, clowsToSteps_length, W₁.total_len, W₂.total_len]
    · have hik : i < k := by rw [clowsToSteps_length, W₁.total_len] at hi1; exact hi1
      exact congrFun h ⟨i, hik⟩
  have hclows := clowsToSteps_injective W₁.heads_strict W₂.heads_strict hsteps
  cases W₁; cases W₂; cases hclows; rfl

noncomputable instance instFintypeClowSeq (k : ℕ) : Fintype (ClowSeq k) :=
  Fintype.ofInjective (ClowSeq.toFun (k := k)) (ClowSeq.toFun_injective k)

/-! #### Partial clow sequences and the 3-index DP -/

/-- A partial clow sequence of `t` completed edges currently in active clow `c` at vertex `u`. -/
structure PartialClowSeq (k t : ℕ) (c : Fin k) (u : Fin (2 * k)) where
  closed : List (Clow k)
  heads_strict : (closed.map Clow.head).Pairwise (· < ·)
  heads_lt : ∀ C ∈ closed, C.head < c
  curMid : List (Fin (2 * k))
  curMid_gt : ∀ v ∈ curMid, c < pairOf v
  total_steps : (closed.map Clow.len).sum + curMid.length = t
  cur_u : (match curMid.getLast? with | none => evenV c | some v => mate v) = u

instance instDecidableEqPartialClowSeq (k t : ℕ) (c : Fin k) (u : Fin (2 * k)) :
    DecidableEq (PartialClowSeq k t c u) := fun a b =>
  if h1 : a.closed = b.closed then
    if h2 : a.curMid = b.curMid then
      isTrue (by cases a; cases b; cases h1; cases h2; rfl)
    else
      isFalse (fun h => h2 (by cases h; rfl))
  else
    isFalse (fun h => h1 (by cases h; rfl))

def PartialClowSeq.toSteps {k t : ℕ} {c : Fin k} {u : Fin (2 * k)}
    (P : PartialClowSeq k t c u) : List (Fin k × Fin (2 * k)) :=
  clowsToSteps P.closed ++ P.curMid.map (fun v => (c, v))

lemma PartialClowSeq.toSteps_length {k t : ℕ} {c : Fin k} {u : Fin (2 * k)}
    (P : PartialClowSeq k t c u) : P.toSteps.length = t := by
  simp [PartialClowSeq.toSteps, clowsToSteps_length, P.total_steps]

def PartialClowSeq.toFun {k t : ℕ} {c : Fin k} {u : Fin (2 * k)}
    (P : PartialClowSeq k t c u) : Fin t → Fin k × Fin (2 * k) :=
  fun i => P.toSteps[i.val]'(by rw [P.toSteps_length]; exact i.isLt)

lemma PartialClowSeq.toFun_injective (k t : ℕ) (c : Fin k) (u : Fin (2 * k)) :
    Function.Injective (PartialClowSeq.toFun (k := k) (t := t) (c := c) (u := u)) := by
  intro P₁ P₂ h
  have hsteps : P₁.toSteps = P₂.toSteps := by
    refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
    · rw [P₁.toSteps_length, P₂.toSteps_length]
    · have hit : i < t := by rw [P₁.toSteps_length] at hi1; exact hi1
      exact congrFun h ⟨i, hit⟩
  have htake : ∀ P : PartialClowSeq k t c u,
      P.toSteps.takeWhile (fun p => decide (p.1 < c)) = clowsToSteps P.closed := by
    intro P
    unfold PartialClowSeq.toSteps
    rw [List.takeWhile_append_of_pos]
    · cases hm : P.curMid with
      | nil => simp
      | cons v vs => simp [List.takeWhile_cons]
    · intro p hp
      rcases List.mem_flatMap.mp hp with ⟨D, hD, hpd⟩
      rcases List.mem_map.mp hpd with ⟨_, _, rfl⟩
      simp [P.heads_lt D hD]
  have hcl_steps : clowsToSteps P₁.closed = clowsToSteps P₂.closed := by
    rw [← htake P₁, ← htake P₂, hsteps]
  have hcl : P₁.closed = P₂.closed :=
    clowsToSteps_injective P₁.heads_strict P₂.heads_strict hcl_steps
  have hcur_map : P₁.curMid.map (fun v => (c, v)) = P₂.curMid.map (fun v => (c, v)) := by
    unfold PartialClowSeq.toSteps at hsteps
    rw [hcl] at hsteps
    exact List.append_cancel_left hsteps
  have hcur : P₁.curMid = P₂.curMid := by
    have := congrArg (List.map Prod.snd) hcur_map
    simpa [List.map_map, Function.comp_def] using this
  cases P₁; cases P₂; cases hcl; cases hcur; rfl

noncomputable instance instFintypePartialClowSeq (k t : ℕ) (c : Fin k) (u : Fin (2 * k)) :
    Fintype (PartialClowSeq k t c u) :=
  Fintype.ofInjective (PartialClowSeq.toFun) (PartialClowSeq.toFun_injective k t c u)

/-- Weight of a partial clow sequence. -/
def partialWeight {k t : ℕ} {c : Fin k} {u : Fin (2 * k)} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (P : PartialClowSeq k t c u) : R :=
  (P.closed.map (clowWeight A)).prod * pathWeight A (evenV c) P.curMid

/-- The 3-index Mahajan–Subramanya–Vinay DP table `dpVal A t c u`. -/
def dpVal {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) : ℕ → Fin k → Fin (2 * k) → R
  | 0, c, u => if u = evenV c then 1 else 0
  | t + 1, c, u =>
    if c < pairOf u then
      ∑ uPrev : Fin (2 * k), dpVal A t c uPrev * (A uPrev (mate u) * (jSign (mate u) : R))
    else if u = evenV c then
      ∑ cPrev : Fin k,
        if cPrev < c then
          ∑ uPrev : Fin (2 * k), dpVal A t cPrev uPrev * A uPrev (oddV cPrev)
        else 0
    else 0

/-- Closing-clow table `closeVal A t c = ∑ uPrev, dpVal A t c uPrev * A uPrev (oddV c)`. -/
def closeVal {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (t : ℕ) (c : Fin k) : R :=
  ∑ uPrev : Fin (2 * k), dpVal A t c uPrev * A uPrev (oddV c)

/-- Final DP output for `k ≥ 1`: `∑ c, closeVal A (k - 1) c`. -/
def dpAns {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) : R :=
  ∑ c : Fin k, closeVal A (k - 1) c

lemma dpVal_succ_eq_closeVal {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (t : ℕ) (c : Fin k) (u : Fin (2 * k)) :
    dpVal A (t + 1) c u =
      if c < pairOf u then
        ∑ uPrev : Fin (2 * k), dpVal A t c uPrev * (A uPrev (mate u) * (jSign (mate u) : R))
      else if u = evenV c then
        ∑ cPrev : Fin k, if cPrev < c then closeVal A t cPrev else 0
      else 0 := rfl

/-- Exact DP invariant: `dpVal A t c u = ∑ P : PartialClowSeq k t c u, partialWeight A P`. -/
theorem dpVal_eq_sum_partial {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (t : ℕ) (c : Fin k) (u : Fin (2 * k)) :
    dpVal A t c u = ∑ P : PartialClowSeq k t c u, partialWeight A P := by
  induction t generalizing c u with
  | zero =>
    unfold dpVal
    split_ifs with hu
    · subst hu
      let P0 : PartialClowSeq k 0 c (evenV c) := {
        closed := []
        heads_strict := List.Pairwise.nil
        heads_lt := fun _ h => nomatch h
        curMid := []
        curMid_gt := fun _ h => nomatch h
        total_steps := rfl
        cur_u := rfl
      }
      have huniq : ∀ P : PartialClowSeq k 0 c (evenV c), P = P0 := by
        intro P
        have hcl : P.closed = [] := by
          cases hc : P.closed with
          | nil => rfl
          | cons D ds =>
            have htot := P.total_steps
            rw [hc] at htot
            simp [Clow.len] at htot
        have hcm : P.curMid = [] := by
          have htot := P.total_steps
          rw [hcl] at htot
          simp at htot
          exact htot
        rcases P with ⟨cl, hs, hlt, cm, cmgt, tot, hcu⟩
        dsimp only at hcl hcm
        subst hcl; subst hcm; rfl
      rw [Fintype.sum_eq_single P0 (fun P hne => absurd (huniq P) hne)]
      simp [partialWeight, P0]
    · have hempty : IsEmpty (PartialClowSeq k 0 c u) := ⟨fun P => by
        have hcl : P.closed = [] := by
          cases hc : P.closed with
          | nil => rfl
          | cons D ds =>
            have htot := P.total_steps; rw [hc] at htot; simp [Clow.len] at htot
        have hcm : P.curMid = [] := by
          have htot := P.total_steps; rw [hcl] at htot; simp at htot; exact htot
        have hcu := P.cur_u
        rw [hcm] at hcu
        exact hu hcu.symm⟩
      simp
  | succ t ih =>
    unfold dpVal
    split_ifs with hgt heven
    · -- Case 1: c < pairOf u, continue current clow with mate u
      simp_rw [ih, Finset.sum_mul]
      rw [← Fintype.sum_sigma']
      let toSig : PartialClowSeq k (t + 1) c u →
          Σ uPrev : Fin (2 * k), PartialClowSeq k t c uPrev := fun P =>
        let mid' := P.curMid.dropLast
        let uPrev := match mid'.getLast? with | none => evenV c | some v => mate v
        have hne : P.curMid ≠ [] := by
          intro hempty
          have hcu := P.cur_u
          rw [hempty] at hcu; simp only [List.getLast?_nil] at hcu
          rw [← hcu, pairOf_evenV] at hgt
          exact lt_irrefl _ hgt
        ⟨uPrev, {
          closed := P.closed
          heads_strict := P.heads_strict
          heads_lt := P.heads_lt
          curMid := mid'
          curMid_gt := fun v hv => P.curMid_gt v (List.dropLast_subset _ hv)
          total_steps := by
            have hlen : mid'.length + 1 = P.curMid.length := by
              dsimp [mid']; rw [List.length_dropLast]; have := List.length_pos_of_ne_nil hne; omega
            have := P.total_steps; omega
          cur_u := rfl
        }⟩
      let ofSig : (Σ uPrev : Fin (2 * k), PartialClowSeq k t c uPrev) →
          PartialClowSeq k (t + 1) c u := fun ⟨uPrev, Q⟩ => {
        closed := Q.closed
        heads_strict := Q.heads_strict
        heads_lt := Q.heads_lt
        curMid := Q.curMid ++ [mate u]
        curMid_gt := by
          intro v hv
          simp only [List.mem_append, List.mem_singleton] at hv
          rcases hv with hq | rfl
          · exact Q.curMid_gt v hq
          · rwa [pairOf_mate]
        total_steps := by
          simp only [List.length_append, List.length_singleton]
          have := Q.total_steps; omega
        cur_u := by simp
      }
      let e : (Σ uPrev : Fin (2 * k), PartialClowSeq k t c uPrev) ≃
          PartialClowSeq k (t + 1) c u := {
        toFun := ofSig
        invFun := toSig
        left_inv := fun ⟨uPrev, Q⟩ => by
          rcases Q with ⟨closed, hs, hlt, curMid, cmgt, tot, hcu⟩
          subst hcu
          have haux : ∀ (cm1 cm2 : List (Fin (2 * k))) (heq : cm1 = cm2)
              (hgt1 : ∀ v ∈ cm1, c < pairOf v) (hgt2 : ∀ v ∈ cm2, c < pairOf v)
              (ht1 : (closed.map Clow.len).sum + cm1.length = t)
              (ht2 : (closed.map Clow.len).sum + cm2.length = t),
              (⟨match cm1.getLast? with | none => evenV c | some v => mate v,
                ⟨closed, hs, hlt, cm1, hgt1, ht1, rfl⟩⟩ :
                  Σ uP : Fin (2 * k), PartialClowSeq k t c uP) =
              ⟨match cm2.getLast? with | none => evenV c | some v => mate v,
                ⟨closed, hs, hlt, cm2, hgt2, ht2, rfl⟩⟩ := by
            rintro cm1 _ rfl _ _ _ _; rfl
          dsimp only [toSig, ofSig]
          exact haux _ curMid (by simp) _ _ _ _
        right_inv := fun P => by
          have hne : P.curMid ≠ [] := by
            intro hempty
            have hcu := P.cur_u; rw [hempty] at hcu; simp only [List.getLast?_nil] at hcu
            rw [← hcu, pairOf_evenV] at hgt; exact lt_irrefl _ hgt
          have hlast : P.curMid.getLast? = some (mate u) := by
            cases hl : P.curMid.getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
            | some v =>
              have hcu := P.cur_u; rw [hl] at hcu
              simp only [Option.some.injEq]
              rw [← hcu, mate_mate]
          have hrecons : P.curMid.dropLast ++ [mate u] = P.curMid := by
            have := List.dropLast_append_getLast hne
            have hgl : P.curMid.getLast hne = mate u := by
              rw [List.getLast?_eq_some_getLast hne] at hlast
              exact Option.some.inj hlast
            rwa [hgl] at this
          cases P
          simp only [toSig, ofSig, PartialClowSeq.mk.injEq, true_and]
          exact hrecons
      }
      refine Fintype.sum_equiv e _ _ fun ⟨uPrev, Q⟩ => ?_
      change partialWeight A Q * (A uPrev (mate u) * (jSign (mate u) : R)) =
        partialWeight A (ofSig ⟨uPrev, Q⟩)
      unfold partialWeight ofSig
      dsimp only
      rw [pathWeight_append, Q.cur_u]
      simp only [pathWeight_cons, pathWeight_nil, mul_one]
      ring
    · -- Case 2: u = evenV c, close an earlier clow cPrev < c
      subst heven
      simp_rw [ih]
      have hlhs :
          (∑ cPrev : Fin k, if cPrev < c then
              ∑ uPrev : Fin (2 * k),
                (∑ P : PartialClowSeq k t cPrev uPrev, partialWeight A P) * A uPrev (oddV cPrev)
            else 0) =
          ∑ x : Σ (cPrev : { d : Fin k // d < c }) (uPrev : Fin (2 * k)),
              PartialClowSeq k t cPrev.1 uPrev,
            partialWeight A x.2.2 * A x.2.1 (oddV x.1.1) := by
        rw [← Finset.sum_filter]
        have hsub :
            (∑ cPrev ∈ Finset.univ.filter (fun d : Fin k => d < c),
              ∑ uPrev : Fin (2 * k),
                (∑ P : PartialClowSeq k t cPrev uPrev, partialWeight A P) * A uPrev (oddV cPrev)) =
            ∑ cPrev : { d : Fin k // d < c },
              ∑ uPrev : Fin (2 * k),
                (∑ P : PartialClowSeq k t cPrev.1 uPrev, partialWeight A P) * A uPrev (oddV cPrev.1) := by
          refine Finset.sum_bij (fun (d : Fin k) (hd : d ∈ Finset.univ.filter (fun d : Fin k => d < c)) =>
              (⟨d, (Finset.mem_filter.mp hd).2⟩ : { d : Fin k // d < c }))
            (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => congrArg Subtype.val h)
            (fun x _ => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩, rfl⟩)
            (fun _ _ => rfl)
        rw [hsub]
        simp_rw [Finset.sum_mul, ← Fintype.sum_sigma']
      rw [hlhs]
      let ofSig : (Σ (cPrev : { d : Fin k // d < c }) (uPrev : Fin (2 * k)),
            PartialClowSeq k t cPrev.1 uPrev) → PartialClowSeq k (t + 1) c (evenV c) :=
        fun ⟨⟨cPrev, hlt⟩, uPrev, Q⟩ =>
          let Cnew : Clow k := ⟨cPrev, Q.curMid, Q.curMid_gt⟩
          {
            closed := Q.closed ++ [Cnew]
            heads_strict := by
              rw [List.map_append, List.map_singleton, List.pairwise_append]
              refine ⟨Q.heads_strict, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
              simp only [List.mem_singleton] at hb; subst hb
              rcases List.mem_map.mp ha with ⟨D, hD, rfl⟩
              exact Q.heads_lt D hD
            heads_lt := by
              intro D hD
              simp only [List.mem_append, List.mem_singleton] at hD
              rcases hD with hq | rfl
              · exact lt_trans (Q.heads_lt D hq) hlt
              · exact hlt
            curMid := []
            curMid_gt := fun _ h => nomatch h
            total_steps := by
              simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
                List.length_nil, add_zero, Clow.len, Cnew]
              have := Q.total_steps; omega
            cur_u := rfl
          }
      let toSig : PartialClowSeq k (t + 1) c (evenV c) →
          Σ (cPrev : { d : Fin k // d < c }) (uPrev : Fin (2 * k)),
            PartialClowSeq k t cPrev.1 uPrev := fun P =>
        have hcm : P.curMid = [] := by
          cases hl : P.curMid.getLast? with
          | none => exact List.getLast?_eq_none_iff.mp hl
          | some v =>
            have hmem : v ∈ P.curMid := List.mem_of_getLast? hl
            have hcu := P.cur_u; rw [hl] at hcu; dsimp only at hcu
            have hp := P.curMid_gt v hmem
            rw [← pairOf_mate v, hcu, pairOf_evenV] at hp
            exact absurd hp (lt_irrefl _)
        have hne : P.closed ≠ [] := by
          intro h0
          have htot := P.total_steps
          rw [h0, hcm] at htot
          simp at htot
        let Clast := P.closed.getLast hne
        let rest := P.closed.dropLast
        have hrecons : rest ++ [Clast] = P.closed := List.dropLast_append_getLast hne
        have hlt : Clast.head < c := P.heads_lt Clast (List.getLast_mem hne)
        have hpw : ((rest ++ [Clast]).map Clow.head).Pairwise (· < ·) := by
          rw [hrecons]; exact P.heads_strict
        let uPrev := match Clast.mid.getLast? with | none => evenV Clast.head | some v => mate v
        ⟨⟨Clast.head, hlt⟩, uPrev, {
          closed := rest
          heads_strict := by
            rw [List.map_append, List.pairwise_append] at hpw
            exact hpw.1
          heads_lt := by
            intro D hD
            rw [List.map_append, List.map_singleton, List.pairwise_append] at hpw
            exact hpw.2.2 D.head (List.mem_map_of_mem hD) Clast.head (List.mem_singleton_self _)
          curMid := Clast.mid
          curMid_gt := Clast.mid_gt
          total_steps := by
            have htot := P.total_steps
            rw [← hrecons, hcm] at htot
            simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
              List.length_nil, add_zero, Clow.len] at htot
            omega
          cur_u := rfl
        }⟩
      let e : (Σ (cPrev : { d : Fin k // d < c }) (uPrev : Fin (2 * k)),
            PartialClowSeq k t cPrev.1 uPrev) ≃ PartialClowSeq k (t + 1) c (evenV c) := {
        toFun := ofSig
        invFun := toSig
        left_inv := fun ⟨⟨cPrev, hlt⟩, uPrev, Q⟩ => by
          rcases Q with ⟨closed, hs, hltq, curMid, cmgt, tot, hcu⟩
          subst hcu
          have haux : ∀ (cl1 cl2 : List (Clow k)) (C1 C2 : Clow k) (hcl : cl1 = cl2) (hC : C1 = C2)
              (h1 : C1.head < c) (h2 : C2.head < c)
              (hs1 : (cl1.map Clow.head).Pairwise (· < ·)) (hs2 : (cl2.map Clow.head).Pairwise (· < ·))
              (hl1 : ∀ D ∈ cl1, D.head < C1.head) (hl2 : ∀ D ∈ cl2, D.head < C2.head)
              (ht1 : (cl1.map Clow.len).sum + C1.mid.length = t)
              (ht2 : (cl2.map Clow.len).sum + C2.mid.length = t),
              (⟨⟨C1.head, h1⟩, match C1.mid.getLast? with | none => evenV C1.head | some v => mate v,
                ⟨cl1, hs1, hl1, C1.mid, C1.mid_gt, ht1, rfl⟩⟩ :
                  Σ (cP : { d : Fin k // d < c }) (uP : Fin (2 * k)), PartialClowSeq k t cP.1 uP) =
              ⟨⟨C2.head, h2⟩, match C2.mid.getLast? with | none => evenV C2.head | some v => mate v,
                ⟨cl2, hs2, hl2, C2.mid, C2.mid_gt, ht2, rfl⟩⟩ := by
            rintro cl1 _ C1 _ rfl rfl _ _ _ _ _ _ _ _; rfl
          dsimp only [toSig, ofSig]
          exact haux _ closed _ ⟨cPrev, curMid, cmgt⟩ (by simp) (by simp) _ _ _ _ _ _ _ _
        right_inv := fun P => by
          have hcm : P.curMid = [] := by
            cases hl : P.curMid.getLast? with
            | none => exact List.getLast?_eq_none_iff.mp hl
            | some v =>
              have hmem : v ∈ P.curMid := List.mem_of_getLast? hl
              have hcu := P.cur_u; rw [hl] at hcu; dsimp only at hcu
              have hp := P.curMid_gt v hmem
              rw [← pairOf_mate v, hcu, pairOf_evenV] at hp
              exact absurd hp (lt_irrefl _)
          have hne : P.closed ≠ [] := by
            intro h0; have htot := P.total_steps; rw [h0, hcm] at htot; simp at htot
          have hrecons := List.dropLast_append_getLast hne
          rcases P with ⟨closed, hs, hlt, curMid, cmgt, tot, hcu⟩
          dsimp only at hcm hne hrecons
          subst hcm
          dsimp only [toSig, ofSig]
          congr 1
      }
      refine Fintype.sum_equiv e _ _ fun ⟨⟨cPrev, hlt⟩, uPrev, Q⟩ => ?_
      change partialWeight A Q * A uPrev (oddV cPrev) = partialWeight A (ofSig ⟨⟨cPrev, hlt⟩, uPrev, Q⟩)
      unfold partialWeight ofSig
      dsimp only
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        pathWeight_nil, mul_one]
      rw [clowWeight_eq_path]
      dsimp only
      rw [Q.cur_u]
      ring
    · -- Case 3: pairOf u ≤ c and u ≠ evenV c -> PartialClowSeq is empty
      have hempty : IsEmpty (PartialClowSeq k (t + 1) c u) := ⟨fun P => by
        cases hl : P.curMid.getLast? with
        | none =>
          have hcu := P.cur_u; rw [hl] at hcu
          exact heven hcu.symm
        | some v =>
          have hmem : v ∈ P.curMid := List.mem_of_getLast? hl
          have hcu := P.cur_u; rw [hl] at hcu; dsimp only at hcu
          have hp := P.curMid_gt v hmem
          rw [← pairOf_mate v, hcu] at hp
          exact hgt hp⟩
      simp

/-- Closing the DP at step `k - 1` yields the sum of weights of all `ClowSeq k` (`k ≥ 1`). -/
theorem dpAns_eq_sum_clowSeq {k : ℕ} (hk : 1 ≤ k) {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) :
    dpAns A = ∑ W : ClowSeq k, clowSeqWeight A W := by
  unfold dpAns closeVal
  simp_rw [dpVal_eq_sum_partial, Finset.sum_mul, ← Fintype.sum_sigma']
  let ofSig : (Σ (c : Fin k) (uPrev : Fin (2 * k)), PartialClowSeq k (k - 1) c uPrev) →
      ClowSeq k := fun ⟨c, uPrev, Q⟩ =>
    let Cnew : Clow k := ⟨c, Q.curMid, Q.curMid_gt⟩
    {
      clows := Q.closed ++ [Cnew]
      heads_strict := by
        rw [List.map_append, List.map_singleton, List.pairwise_append]
        refine ⟨Q.heads_strict, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb; subst hb
        rcases List.mem_map.mp ha with ⟨D, hD, rfl⟩
        exact Q.heads_lt D hD
      total_len := by
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
          Clow.len, Cnew]
        have := Q.total_steps; omega
    }
  let toSig : ClowSeq k →
      Σ (c : Fin k) (uPrev : Fin (2 * k)), PartialClowSeq k (k - 1) c uPrev := fun W =>
    have hne : W.clows ≠ [] := by
      intro h0; have htot := W.total_len; rw [h0] at htot; simp at htot; omega
    let Clast := W.clows.getLast hne
    let rest := W.clows.dropLast
    have hrecons : rest ++ [Clast] = W.clows := List.dropLast_append_getLast hne
    have hpw : ((rest ++ [Clast]).map Clow.head).Pairwise (· < ·) := by
      rw [hrecons]; exact W.heads_strict
    let uPrev := match Clast.mid.getLast? with | none => evenV Clast.head | some v => mate v
    ⟨Clast.head, uPrev, {
      closed := rest
      heads_strict := by
        rw [List.map_append, List.pairwise_append] at hpw; exact hpw.1
      heads_lt := by
        intro D hD
        rw [List.map_append, List.map_singleton, List.pairwise_append] at hpw
        exact hpw.2.2 D.head (List.mem_map_of_mem hD) Clast.head (List.mem_singleton_self _)
      curMid := Clast.mid
      curMid_gt := Clast.mid_gt
      total_steps := by
        have htot := W.total_len
        rw [← hrecons] at htot
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
          Clow.len] at htot
        omega
      cur_u := rfl
    }⟩
  let e : (Σ (c : Fin k) (uPrev : Fin (2 * k)), PartialClowSeq k (k - 1) c uPrev) ≃
      ClowSeq k := {
    toFun := ofSig
    invFun := toSig
    left_inv := fun ⟨c, uPrev, Q⟩ => by
      rcases Q with ⟨closed, hs, hltq, curMid, cmgt, tot, hcu⟩
      subst hcu
      have haux : ∀ (cl1 cl2 : List (Clow k)) (C1 C2 : Clow k) (hcl : cl1 = cl2) (hC : C1 = C2)
          (hs1 : (cl1.map Clow.head).Pairwise (· < ·)) (hs2 : (cl2.map Clow.head).Pairwise (· < ·))
          (hl1 : ∀ D ∈ cl1, D.head < C1.head) (hl2 : ∀ D ∈ cl2, D.head < C2.head)
          (ht1 : (cl1.map Clow.len).sum + C1.mid.length = k - 1)
          (ht2 : (cl2.map Clow.len).sum + C2.mid.length = k - 1),
          (⟨C1.head, match C1.mid.getLast? with | none => evenV C1.head | some v => mate v,
            ⟨cl1, hs1, hl1, C1.mid, C1.mid_gt, ht1, rfl⟩⟩ :
              Σ (cP : Fin k) (uP : Fin (2 * k)), PartialClowSeq k (k - 1) cP uP) =
          ⟨C2.head, match C2.mid.getLast? with | none => evenV C2.head | some v => mate v,
            ⟨cl2, hs2, hl2, C2.mid, C2.mid_gt, ht2, rfl⟩⟩ := by
        rintro cl1 _ C1 _ rfl rfl _ _ _ _ _ _; rfl
      dsimp only [toSig, ofSig]
      exact haux _ closed _ ⟨c, curMid, cmgt⟩ (by simp) (by simp) _ _ _ _ _ _
    right_inv := fun W => by
      have hne : W.clows ≠ [] := by
        intro h0; have htot := W.total_len; rw [h0] at htot; simp at htot; omega
      have hrecons := List.dropLast_append_getLast hne
      cases W
      simp only [toSig, ofSig, ClowSeq.mk.injEq]
      simpa using hrecons
  }
  refine Fintype.sum_equiv e _ _ fun ⟨c, uPrev, Q⟩ => ?_
  change partialWeight A Q * A uPrev (oddV c) = clowSeqWeight A (ofSig ⟨c, uPrev, Q⟩)
  unfold partialWeight clowSeqWeight ofSig
  dsimp only
  simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  rw [clowWeight_eq_path]
  dsimp only
  rw [Q.cur_u]
  ring

/-! ### 4. Dihedral Cycle Orientation & 3-Case Sign-Reversing Involution -/

/-- Rotation equivalence on lists: `xs = a ++ b` and `ys = b ++ a`. -/
def IsRot {α : Type*} (xs ys : List α) : Prop :=
  ∃ a b, xs = a ++ b ∧ ys = b ++ a

lemma isRot_refl {α : Type*} (xs : List α) : IsRot xs xs :=
  ⟨[], xs, rfl, by simp⟩

lemma isRot_symm {α : Type*} {xs ys : List α} (h : IsRot xs ys) : IsRot ys xs := by
  rcases h with ⟨a, b, rfl, rfl⟩
  exact ⟨b, a, rfl, rfl⟩

lemma isRot_trans {α : Type*} {xs ys zs : List α} (h1 : IsRot xs ys) (h2 : IsRot ys zs) :
    IsRot xs zs := by
  rcases h1 with ⟨a, b, rfl, hba⟩
  rcases h2 with ⟨c, d, hcd, rfl⟩
  have heq : b ++ a = c ++ d := hba.symm.trans hcd
  rcases List.append_eq_append_iff.mp heq with ⟨m, hc, ha⟩ | ⟨m, hb, hd⟩
  · exact ⟨m, d ++ b, by rw [ha]; simp [List.append_assoc], by rw [hc]; simp [List.append_assoc]⟩
  · exact ⟨a ++ c, m, by rw [hb]; simp [List.append_assoc], by rw [hd]; simp [List.append_assoc]⟩

lemma isRot_perm {α : Type*} {xs ys : List α} (h : IsRot xs ys) : xs.Perm ys := by
  rcases h with ⟨a, b, rfl, rfl⟩
  exact List.perm_append_comm

lemma isRot_revMate {k : ℕ} {xs ys : List (Fin (2 * k))} (h : IsRot xs ys) :
    IsRot (revMate xs) (revMate ys) := by
  rcases h with ⟨a, b, rfl, rfl⟩
  exact ⟨revMate b, revMate a, revMate_append a b, revMate_append b a⟩

lemma cycWeight_of_isRot {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) {xs ys : List (Fin (2 * k))} (h : IsRot xs ys) :
    cycWeight A xs = cycWeight A ys := by
  rcases h with ⟨a, b, rfl, rfl⟩
  exact cycWeight_append_comm A a b

/-- Dihedral (rotation + mate-reversal) equivalence on vertex lists. -/
def InDihedral {k : ℕ} (xs ys : List (Fin (2 * k))) : Prop :=
  IsRot xs ys ∨ IsRot (revMate xs) ys

lemma inDihedral_refl {k : ℕ} (xs : List (Fin (2 * k))) : InDihedral xs xs :=
  Or.inl (isRot_refl xs)

lemma inDihedral_symm {k : ℕ} {xs ys : List (Fin (2 * k))} (h : InDihedral xs ys) :
    InDihedral ys xs := by
  rcases h with h | h
  · exact Or.inl (isRot_symm h)
  · right
    have h' := isRot_revMate (isRot_symm h)
    rwa [revMate_revMate] at h'

lemma inDihedral_trans {k : ℕ} {xs ys zs : List (Fin (2 * k))}
    (h1 : InDihedral xs ys) (h2 : InDihedral ys zs) : InDihedral xs zs := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (isRot_trans h1 h2)
  · exact Or.inr (isRot_trans (isRot_revMate h1) h2)
  · exact Or.inr (isRot_trans h1 h2)
  · left
    have h1' := isRot_revMate h1
    rw [revMate_revMate] at h1'
    exact isRot_trans h1' h2

lemma inDihedral_perm_pairOf {k : ℕ} {xs ys : List (Fin (2 * k))} (h : InDihedral xs ys) :
    (xs.map pairOf).Perm (ys.map pairOf) := by
  rcases h with h | h
  · exact (isRot_perm h).map pairOf
  · have hp := (isRot_perm h).map pairOf
    rw [map_pairOf_revMate] at hp
    exact (List.reverse_perm _).symm.trans hp

lemma cycWeight_of_inDihedral {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    {xs ys : List (Fin (2 * k))} (h : InDihedral xs ys) :
    cycWeight A xs = cycWeight A ys := by
  rcases h with h | h
  · exact cycWeight_of_isRot A h
  · rw [← cycWeight_revMate hA xs]
    exact cycWeight_of_isRot A h

/-- Dihedral Orbit Uniqueness: if `(xs.map pairOf).Nodup`, two elements of its dihedral orbit
with the same last vertex are identical. -/
lemma eq_of_inDihedral_of_getLast?_eq {k : ℕ} {xs ys : List (Fin (2 * k))}
    (hnodup : (xs.map pairOf).Nodup) (h : InDihedral xs ys)
    {v : Fin (2 * k)} (hx : xs.getLast? = some v) (hy : ys.getLast? = some v) :
    xs = ys := by
  rcases h with ⟨a, b, rfl, rfl⟩ | hrev
  · cases a with
    | nil => simp
    | cons a0 as =>
      cases b with
      | nil => simp
      | cons b0 bs =>
        have hvb : v ∈ b0 :: bs := by
          rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hx
          exact List.mem_of_getLast? hx
        have hva : v ∈ a0 :: as := by
          rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hy
          exact List.mem_of_getLast? hy
        rw [List.map_append, List.nodup_append] at hnodup
        exact False.elim (hnodup.2.2 (pairOf v) (List.mem_map_of_mem hva) (pairOf v) (List.mem_map_of_mem hvb) rfl)
  · exfalso
    have hv_xs : v ∈ xs := List.mem_of_getLast? hx
    have hv_ys : v ∈ ys := List.mem_of_getLast? hy
    have hv_rev : v ∈ revMate xs := (isRot_perm hrev).mem_iff.mpr hv_ys
    have hmv_xs : mate v ∈ xs := mem_revMate_iff.mp hv_rev
    -- xs contains both v and mate v with v ≠ mate v and pairOf v = pairOf (mate v)
    rcases List.append_of_mem hv_xs with ⟨l1, l2, rfl⟩
    rw [List.mem_append, List.mem_cons] at hmv_xs
    rw [List.map_append, List.map_cons, List.nodup_append] at hnodup
    rcases hmv_xs with hm1 | hmeq | hm2
    · have h1 := hnodup.2.2 (pairOf (mate v)) (List.mem_map_of_mem hm1) (pairOf v) List.mem_cons_self
      rw [pairOf_mate] at h1
      exact h1 rfl
    · exact mate_ne_self v hmeq
    · have hnd := (List.nodup_cons.mp hnodup.2.1).1
      have hmem : pairOf v ∈ l2.map pairOf := by
        rw [← pairOf_mate v]; exact List.mem_map_of_mem hm2
      exact hnd hmem

/-- Split `l` at the first element `w` with `pairOf w = p`. -/
def splitAtPair {k : ℕ} (p : Fin k) :
    List (Fin (2 * k)) → Option (List (Fin (2 * k)) × Fin (2 * k) × List (Fin (2 * k)))
  | [] => none
  | w :: ws =>
    if pairOf w = p then some ([], w, ws)
    else (splitAtPair p ws).map fun ⟨a, x, b⟩ => (w :: a, x, b)

lemma splitAtPair_spec {k : ℕ} (p : Fin k) (l : List (Fin (2 * k))) :
    match splitAtPair p l with
    | none => p ∉ l.map pairOf
    | some (a, w, b) => l = a ++ [w] ++ b ∧ pairOf w = p ∧ p ∉ a.map pairOf := by
  induction l with
  | nil => simp [splitAtPair]
  | cons w ws ih =>
    unfold splitAtPair
    split_ifs with h
    · simp [h]
    · cases hs : splitAtPair p ws with
      | none =>
        rw [hs] at ih
        simp [Option.map, Ne.symm h, ih]
      | some res =>
        rcases res with ⟨a, x, b⟩
        rw [hs] at ih
        rcases ih with ⟨rfl, hx, hna⟩
        simp [Option.map, Ne.symm h, hx, hna]

/-- Orient a cycle `xs` (containing pair `pairOf v`) inside its dihedral orbit so it ends at `v`. -/
def orientTo {k : ℕ} (xs : List (Fin (2 * k))) (v : Fin (2 * k)) : List (Fin (2 * k)) :=
  match splitAtPair (pairOf v) xs with
  | none => xs
  | some (a, w, b) =>
    if w = v then b ++ a ++ [v]
    else revMate (b ++ a) ++ [v]

lemma orientTo_spec {k : ℕ} (xs : List (Fin (2 * k))) (v : Fin (2 * k))
    (hmem : pairOf v ∈ xs.map pairOf) :
    InDihedral xs (orientTo xs v) ∧ (orientTo xs v).getLast? = some v := by
  have hsp := splitAtPair_spec (pairOf v) xs
  unfold orientTo
  cases hs : splitAtPair (pairOf v) xs with
  | none =>
    rw [hs] at hsp; exact absurd hmem hsp
  | some res =>
    rcases res with ⟨a, w, b⟩
    rw [hs] at hsp
    rcases hsp with ⟨hxs, hw, _⟩
    dsimp only
    split_ifs with heq
    · subst heq
      refine ⟨Or.inl ⟨a ++ [w], b, by simpa [List.append_assoc] using hxs,
        by simp [List.append_assoc]⟩, by simp⟩
    · have hwm : w = mate v := by
        rcases pairOf_eq_iff.mp hw with h1 | h2
        · exact absurd h1 heq
        · exact h2
      subst hwm
      have hrot1 : IsRot xs (b ++ a ++ [mate v]) :=
        ⟨a ++ [mate v], b, by simpa [List.append_assoc] using hxs, by simp [List.append_assoc]⟩
      have hrev : revMate (b ++ a ++ [mate v]) = [v] ++ revMate (b ++ a) := by
        rw [revMate_append, revMate_singleton, mate_mate]
      have hrot2 : IsRot (revMate (b ++ a ++ [mate v])) (revMate (b ++ a) ++ [v]) := by
        rw [hrev]; exact ⟨[v], revMate (b ++ a), rfl, rfl⟩
      refine ⟨Or.inr (isRot_trans (isRot_revMate hrot1) hrot2), by simp⟩

lemma orientTo_orientTo {k : ℕ} {xs : List (Fin (2 * k))}
    (hnodup : (xs.map pairOf).Nodup) {v w : Fin (2 * k)}
    (hv : pairOf v ∈ xs.map pairOf) (hw : pairOf w ∈ xs.map pairOf) :
    orientTo (orientTo xs v) w = orientTo xs w := by
  have ⟨hd1, _⟩ := orientTo_spec xs v hv
  have hperm1 := inDihedral_perm_pairOf hd1
  have hw1 : pairOf w ∈ (orientTo xs v).map pairOf := hperm1.mem_iff.mp hw
  have ⟨hd2, hlast2⟩ := orientTo_spec (orientTo xs v) w hw1
  have ⟨hd3, hlast3⟩ := orientTo_spec xs w hw
  exact eq_of_inDihedral_of_getLast?_eq
    ((inDihedral_perm_pairOf hd2).nodup_iff.mp (hperm1.nodup_iff.mp hnodup))
    (inDihedral_trans (inDihedral_symm hd2) (inDihedral_trans (inDihedral_symm hd1) hd3))
    hlast2 hlast3

lemma orientTo_self {k : ℕ} {xs : List (Fin (2 * k))}
    (hnodup : (xs.map pairOf).Nodup) {v : Fin (2 * k)} (hlast : xs.getLast? = some v) :
    orientTo xs v = xs := by
  have hv : pairOf v ∈ xs.map pairOf := List.mem_map_of_mem (List.mem_of_getLast? hlast)
  have ⟨hd, hlast'⟩ := orientTo_spec xs v hv
  exact (eq_of_inDihedral_of_getLast?_eq hnodup hd hlast hlast').symm

/-- Minimum `pairOf` of a nonempty vertex list. -/
def minPair {k : ℕ} : (xs : List (Fin (2 * k))) → xs ≠ [] → Fin k
  | [v], _ => pairOf v
  | v :: w :: rest, _ => min (pairOf v) (minPair (w :: rest) (List.cons_ne_nil _ _))

lemma minPair_mem {k : ℕ} : ∀ (xs : List (Fin (2 * k))) (hne : xs ≠ []),
    minPair xs hne ∈ xs.map pairOf
  | [v], _ => by simp [minPair]
  | v :: w :: rest, _ => by
    simp only [minPair, List.map_cons]
    rcases min_cases (pairOf v) (minPair (w :: rest) (List.cons_ne_nil _ _)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact List.mem_cons_self
    · rw [h]; exact List.mem_cons_of_mem _ (minPair_mem (w :: rest) (List.cons_ne_nil _ _))

lemma minPair_le {k : ℕ} : ∀ (xs : List (Fin (2 * k))) (hne : xs ≠ []) {v : Fin (2 * k)},
    v ∈ xs → minPair xs hne ≤ pairOf v
  | [u], _, v, hv => by
    simp only [List.mem_singleton] at hv; subst hv; exact le_rfl
  | u :: w :: rest, _, v, hv => by
    simp only [minPair]
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hrest
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _)
        (minPair_le (w :: rest) (List.cons_ne_nil _ _) (List.mem_cons.mpr hrest))

lemma minPair_eq_of_perm {k : ℕ} {xs ys : List (Fin (2 * k))}
    (hx : xs ≠ []) (hy : ys ≠ []) (hperm : (xs.map pairOf).Perm (ys.map pairOf)) :
    minPair xs hx = minPair ys hy := by
  apply le_antisymm
  · have hmem : minPair ys hy ∈ xs.map pairOf := hperm.mem_iff.mpr (minPair_mem ys hy)
    rcases List.mem_map.mp hmem with ⟨v, hv, heq⟩
    rw [← heq]; exact minPair_le xs hx hv
  · have hmem : minPair xs hx ∈ ys.map pairOf := hperm.mem_iff.mp (minPair_mem xs hx)
    rcases List.mem_map.mp hmem with ⟨v, hv, heq⟩
    rw [← heq]; exact minPair_le ys hy hv

/-- Convert a nonempty pair-distinct list `cyc` into its canonical `Clow k`. -/
def mkClowFromCycle {k : ℕ} (cyc : List (Fin (2 * k))) (hne : cyc ≠ [])
    (hnodup : (cyc.map pairOf).Nodup) : Clow k :=
  let c := minPair cyc hne
  let verts := orientTo cyc (oddV c)
  have hmem : pairOf (oddV c) ∈ cyc.map pairOf := by
    rw [pairOf_oddV]; exact minPair_mem cyc hne
  have ⟨hd, hlast⟩ := orientTo_spec cyc (oddV c) hmem
  have hperm := inDihedral_perm_pairOf hd
  have hnodup' : (verts.map pairOf).Nodup := hperm.nodup_iff.mp hnodup
  have hverts_ne : verts ≠ [] := fun h0 => by
    change orientTo cyc (oddV c) = [] at h0
    rw [h0] at hlast; simp at hlast
  have hrecons : verts.dropLast ++ [oddV c] = verts := by
    have hgl : verts.getLast hverts_ne = oddV c := by
      rw [List.getLast?_eq_some_getLast hverts_ne] at hlast
      exact Option.some.inj hlast
    simpa [hgl] using List.dropLast_append_getLast hverts_ne
  {
    head := c
    mid := verts.dropLast
    mid_gt := by
      intro w hw
      have hw_v : w ∈ verts := by rw [← hrecons]; exact List.mem_append_left _ hw
      have hpw_mem : pairOf w ∈ cyc.map pairOf := hperm.mem_iff.mpr (List.mem_map_of_mem hw_v)
      rcases List.mem_map.mp hpw_mem with ⟨u, hu, heq⟩
      have hle : c ≤ pairOf w := by rw [← heq]; exact minPair_le cyc hne hu
      have hne_c : pairOf w ≠ c := by
        intro heqc
        rw [← hrecons, List.map_append, List.map_singleton, List.nodup_append] at hnodup'
        have hbad := hnodup'.2.2 (pairOf w) (List.mem_map_of_mem hw) (pairOf (oddV c)) (List.mem_singleton_self _)
        rw [heqc, pairOf_oddV] at hbad
        exact hbad rfl
      exact lt_of_le_of_ne hle hne_c.symm
  }

lemma mkClowFromCycle_verts {k : ℕ} (cyc : List (Fin (2 * k))) (hne : cyc ≠ [])
    (hnodup : (cyc.map pairOf).Nodup) :
    (mkClowFromCycle cyc hne hnodup).verts = orientTo cyc (oddV (minPair cyc hne)) := by
  unfold mkClowFromCycle Clow.verts
  dsimp only
  have hmem : pairOf (oddV (minPair cyc hne)) ∈ cyc.map pairOf := by
    rw [pairOf_oddV]; exact minPair_mem cyc hne
  have ⟨_, hlast⟩ := orientTo_spec cyc (oddV (minPair cyc hne)) hmem
  have hverts_ne : orientTo cyc (oddV (minPair cyc hne)) ≠ [] := fun h0 => by simp [h0] at hlast
  have hgl : (orientTo cyc (oddV (minPair cyc hne))).getLast hverts_ne = oddV (minPair cyc hne) := by
    rw [List.getLast?_eq_some_getLast hverts_ne] at hlast
    exact Option.some.inj hlast
  simpa [hgl] using List.dropLast_append_getLast hverts_ne

lemma mkClowFromCycle_self {k : ℕ} (C : Clow k) (hnodup : (C.verts.map pairOf).Nodup) :
    mkClowFromCycle C.verts C.verts_ne_nil hnodup = C := by
  have hmin : minPair C.verts C.verts_ne_nil = C.head := by
    apply le_antisymm
    · have := minPair_le C.verts C.verts_ne_nil (v := oddV C.head) (by simp [Clow.verts])
      simpa using this
    · have hmem := minPair_mem C.verts C.verts_ne_nil
      rcases List.mem_map.mp hmem with ⟨v, hv, heq⟩
      rw [← heq]; exact C.head_le_pairOf_verts hv
  have hv : (mkClowFromCycle C.verts C.verts_ne_nil hnodup).verts = C.verts := by
    rw [mkClowFromCycle_verts, hmin]
    exact orientTo_self hnodup C.verts_getLast?
  have hmid : (mkClowFromCycle C.verts C.verts_ne_nil hnodup).mid = C.mid := by
    have := congrArg List.dropLast hv
    simpa [Clow.verts] using this
  cases C
  simp only [mkClowFromCycle, Clow.mk.injEq] at hmid ⊢
  exact ⟨hmin, hmid⟩

/-! #### Tail-clean decomposition, scanning, sorted insertion, and the 3-case involution -/

/-- All pairs appearing in a list of clows. -/
def clowsPairs {k : ℕ} (cs : List (Clow k)) : List (Fin k) :=
  (cs.flatMap Clow.verts).map pairOf

/-- A list of clows is tail-clean iff all its pairs are distinct. -/
def TailClean {k : ℕ} (cs : List (Clow k)) : Prop :=
  (clowsPairs cs).Nodup

instance instDecidableTailClean {k : ℕ} (cs : List (Clow k)) : Decidable (TailClean cs) :=
  inferInstanceAs (Decidable ((clowsPairs cs).Nodup))

/-- A clow sequence is diagonal-free iff every clow's `mid` is diagonal-free. -/
def IsDiagFreeSeq {k : ℕ} (W : ClowSeq k) : Prop :=
  ∀ C ∈ W.clows, IsDiagFreeList C.mid

instance instDecidableIsDiagFreeSeq {k : ℕ} (W : ClowSeq k) : Decidable (IsDiagFreeSeq W) :=
  inferInstanceAs (Decidable (∀ C ∈ W.clows, IsDiagFreeList C.mid))

/-- A clow sequence is simple iff all `k` pairs in `W.clows` are distinct. -/
def IsSimpleSeq {k : ℕ} (W : ClowSeq k) : Prop :=
  TailClean W.clows

instance instDecidableIsSimpleSeq {k : ℕ} (W : ClowSeq k) : Decidable (IsSimpleSeq W) :=
  inferInstanceAs (Decidable (TailClean W.clows))

lemma isDiagFreeSeq_of_isSimpleSeq {k : ℕ} {W : ClowSeq k} (h : IsSimpleSeq W) :
    IsDiagFreeSeq W := by
  intro C hC
  rcases List.append_of_mem hC with ⟨l1, l2, heq⟩
  have hnd : (clowsPairs W.clows).Nodup := h
  rw [heq] at hnd
  unfold clowsPairs at hnd
  simp only [List.flatMap_append, List.flatMap_cons, List.map_append, List.nodup_append] at hnd
  have hCnd : (C.verts.map pairOf).Nodup := hnd.2.1.1
  unfold Clow.verts at hCnd
  rw [List.map_append, List.nodup_append] at hCnd
  exact isDiagFreeList_of_pairOf_nodup C.mid hCnd.1

lemma clowSeqWeight_eq_zero_of_not_diagFree {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (W : ClowSeq k) (h : ¬ IsDiagFreeSeq W) :
    clowSeqWeight A W = 0 := by
  unfold IsDiagFreeSeq at h
  push_neg at h
  rcases h with ⟨C, hC, hbad⟩
  unfold clowSeqWeight
  exact List.prod_eq_zero (List.mem_map.mpr ⟨C, hC, clowWeight_eq_zero_of_not_diagFree hA C hbad⟩)

/-- Right-to-left split finding the rightmost bad clow: `cs = pref ++ [C] ++ suff`
with `TailClean suff` and `¬ TailClean (C :: suff)`. -/
def splitBad {k : ℕ} : List (Clow k) → Option (List (Clow k) × Clow k × List (Clow k))
  | [] => none
  | C :: rest =>
    match splitBad rest with
    | some (p, D, s) => some (C :: p, D, s)
    | none => if TailClean (C :: rest) then none else some ([], C, rest)

lemma splitBad_none_iff {k : ℕ} (cs : List (Clow k)) :
    splitBad cs = none ↔ TailClean cs := by
  induction cs with
  | nil => simp [splitBad, TailClean, clowsPairs]
  | cons C rest ih =>
    unfold splitBad
    cases hs : splitBad rest with
    | some res =>
      rcases res with ⟨p, D, s⟩
      simp only [reduceCtorEq, false_iff]
      intro htc
      have hrest : TailClean rest := by
        unfold TailClean clowsPairs at htc ⊢
        rw [List.flatMap_cons, List.map_append, List.nodup_append] at htc
        exact htc.2.1
      rw [ih.mpr hrest] at hs
      cases hs
    | none =>
      split_ifs with htc
      · simp [htc]
      · simp [htc]

lemma splitBad_some_spec {k : ℕ} {cs pref suff : List (Clow k)} {C : Clow k}
    (h : splitBad cs = some (pref, C, suff)) :
    cs = pref ++ [C] ++ suff ∧ TailClean suff ∧ ¬ TailClean (C :: suff) := by
  induction cs generalizing pref with
  | nil => simp [splitBad] at h
  | cons X rest ih =>
    unfold splitBad at h
    cases hs : splitBad rest with
    | some res =>
      rcases res with ⟨p, D, s⟩
      rw [hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rcases ih hs with ⟨rfl, hts, hnb⟩
      exact ⟨rfl, hts, hnb⟩
    | none =>
      rw [hs] at h
      split_ifs at h with htc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, (splitBad_none_iff rest).mp hs, htc⟩

lemma splitBad_unique {k : ℕ} {pref suff : List (Clow k)} {C : Clow k}
    (hts : TailClean suff) (hnb : ¬ TailClean (C :: suff)) :
    splitBad (pref ++ [C] ++ suff) = some (pref, C, suff) := by
  induction pref with
  | nil =>
    simp only [List.nil_append, List.cons_append]
    unfold splitBad
    rw [(splitBad_none_iff suff).mpr hts]
    simp [hnb]
  | cons X ps ih =>
    simp only [List.cons_append]
    unfold splitBad
    rw [ih]

/-- Clean-prefix invariant for scanning `C.mid` against `tailPairs`. -/
def CleanPrefix {k : ℕ} (seen : List (Fin (2 * k))) (tailPairs : List (Fin k)) : Prop :=
  (seen.map pairOf).Nodup ∧ ∀ v ∈ seen, pairOf v ∉ tailPairs

/-- Outcome of scanning `C.mid` for the first pair collision. -/
inductive ScanRes (k : ℕ) where
  | selfOpp (p1 : List (Fin (2 * k))) (v0 : Fin (2 * k)) (seg : List (Fin (2 * k)))
      (v : Fin (2 * k)) (rest : List (Fin (2 * k)))
  | selfSame (p1 : List (Fin (2 * k))) (seg : List (Fin (2 * k)))
      (v : Fin (2 * k)) (rest : List (Fin (2 * k)))
  | hitLater (seen : List (Fin (2 * k))) (v : Fin (2 * k)) (rest : List (Fin (2 * k)))
  | none

def scanMidAux {k : ℕ} (tailPairs : List (Fin k)) :
    List (Fin (2 * k)) → List (Fin (2 * k)) → ScanRes k
  | _, [] => .none
  | seen, v :: rest =>
    match splitAtPair (pairOf v) seen with
    | some (p1, v0, seg) =>
      if v0 = v then .selfSame p1 seg v rest
      else .selfOpp p1 v0 seg v rest
    | none =>
      if pairOf v ∈ tailPairs then .hitLater seen v rest
      else scanMidAux tailPairs (seen ++ [v]) rest

def scanMid {k : ℕ} (tailPairs mid : List (Fin k)) : ScanRes k := .none -- unused placeholder
-- Actual scanMid:
def scanMidList {k : ℕ} (tailPairs : List (Fin k)) (mid : List (Fin (2 * k))) : ScanRes k :=
  scanMidAux tailPairs [] mid

lemma scanMidAux_spec {k : ℕ} (tailPairs : List (Fin k))
    (seen rem : List (Fin (2 * k))) (hclean : CleanPrefix seen tailPairs) :
    match scanMidAux tailPairs seen rem with
    | .selfOpp p1 v0 seg v rest =>
        seen ++ rem = p1 ++ [v0] ++ seg ++ [v] ++ rest ∧
        CleanPrefix (p1 ++ [v0] ++ seg) tailPairs ∧ v0 = mate v
    | .selfSame p1 seg v rest =>
        seen ++ rem = p1 ++ [v] ++ seg ++ [v] ++ rest ∧
        CleanPrefix (p1 ++ [v] ++ seg) tailPairs
    | .hitLater s v rest =>
        seen ++ rem = s ++ [v] ++ rest ∧
        CleanPrefix s tailPairs ∧ pairOf v ∈ tailPairs
    | .none =>
        CleanPrefix (seen ++ rem) tailPairs := by
  induction rem generalizing seen with
  | nil =>
    simpa [scanMidAux] using hclean
  | cons v rest ih =>
    unfold scanMidAux
    have hsp := splitAtPair_spec (pairOf v) seen
    cases hs : splitAtPair (pairOf v) seen with
    | some res =>
      rcases res with ⟨p1, v0, seg⟩
      rw [hs] at hsp
      rcases hsp with ⟨hseen, hv0, _⟩
      dsimp only
      split_ifs with heq
      · subst heq
        exact ⟨by simp [hseen, List.append_assoc], by rwa [← hseen]⟩
      · have hmv : v0 = mate v := by
          rcases pairOf_eq_iff.mp hv0 with h1 | h2
          · exact absurd h1 heq
          · exact h2
        exact ⟨by simp [hseen, List.append_assoc], by rwa [← hseen], hmv⟩
    | none =>
      rw [hs] at hsp
      dsimp only
      split_ifs with hmem
      · exact ⟨by simp, hclean, hmem⟩
      · have hclean' : CleanPrefix (seen ++ [v]) tailPairs := by
          refine ⟨?_, ?_⟩
          · rw [List.map_append, List.map_singleton, List.nodup_append]
            refine ⟨hclean.1, List.nodup_singleton _, fun a ha b hb => ?_⟩
            simp only [List.mem_singleton] at hb; subst hb
            intro heq; subst heq; exact hsp ha
          · intro w hw
            simp only [List.mem_append, List.mem_singleton] at hw
            rcases hw with hw | rfl
            · exact hclean.2 w hw
            · exact hmem
        have hres := ih (seen ++ [v]) hclean'
        simpa [List.append_assoc] using hres

lemma scanMidList_spec {k : ℕ} (tailPairs : List (Fin k)) (mid : List (Fin (2 * k))) :
    match scanMidList tailPairs mid with
    | .selfOpp p1 v0 seg v rest =>
        mid = p1 ++ [v0] ++ seg ++ [v] ++ rest ∧
        CleanPrefix (p1 ++ [v0] ++ seg) tailPairs ∧ v0 = mate v
    | .selfSame p1 seg v rest =>
        mid = p1 ++ [v] ++ seg ++ [v] ++ rest ∧
        CleanPrefix (p1 ++ [v] ++ seg) tailPairs
    | .hitLater s v rest =>
        mid = s ++ [v] ++ rest ∧
        CleanPrefix s tailPairs ∧ pairOf v ∈ tailPairs
    | .none =>
        CleanPrefix mid tailPairs := by
  simpa [scanMidList] using
    scanMidAux_spec tailPairs [] mid ⟨List.nodup_nil, fun _ h => nomatch h⟩

lemma scanMidAux_unique_prefix {k : ℕ} (tailPairs : List (Fin k))
    (seen pref rem : List (Fin (2 * k))) (hclean : CleanPrefix (seen ++ pref) tailPairs) :
    scanMidAux tailPairs seen (pref ++ rem) = scanMidAux tailPairs (seen ++ pref) rem := by
  induction pref generalizing seen with
  | nil => simp
  | cons u us ih =>
    simp only [List.cons_append]
    conv_lhs => unfold scanMidAux
    have hclean_u : CleanPrefix (seen ++ [u]) tailPairs := by
      refine ⟨?_, ?_⟩
      · have hnd := hclean.1
        have h1 : (seen ++ u :: us) = (seen ++ [u]) ++ us := by simp
        rw [h1, List.map_append, List.nodup_append] at hnd
        exact hnd.1
      · intro w hw
        apply hclean.2 w
        have h1 : (seen ++ u :: us) = (seen ++ [u]) ++ us := by simp
        rw [h1]; exact List.mem_append_left _ hw
    have hnot_seen : pairOf u ∉ seen.map pairOf := by
      have hnd := hclean_u.1
      rw [List.map_append, List.map_singleton, List.nodup_append] at hnd
      intro hm
      exact hnd.2.2 (pairOf u) hm (pairOf u) (List.mem_singleton_self _) rfl
    have hsp := splitAtPair_spec (pairOf u) seen
    cases hs : splitAtPair (pairOf u) seen with
    | some res =>
      rcases res with ⟨p1, v0, seg⟩
      rw [hs] at hsp
      rcases hsp with ⟨hseen, hv0, _⟩
      exfalso; apply hnot_seen
      rw [hseen, ← hv0]; exact List.mem_map_of_mem (by simp)
    | none =>
      have hnot_tail : pairOf u ∉ tailPairs := hclean_u.2 u (by simp)
      simp only [hnot_tail, ↓reduceIte]
      have h1 : seen ++ u :: us = (seen ++ [u]) ++ us := by simp
      rw [h1] at hclean ⊢
      exact ih (seen ++ [u]) hclean

lemma splitAtPair_eq_of_clean {k : ℕ} {p1 seg : List (Fin (2 * k))} {v0 : Fin (2 * k)}
    (hnd : ((p1 ++ [v0] ++ seg).map pairOf).Nodup) :
    splitAtPair (pairOf v0) (p1 ++ [v0] ++ seg) = some (p1, v0, seg) := by
  have hnot : pairOf v0 ∉ p1.map pairOf := by
    rw [List.map_append, List.map_append, List.map_singleton, List.nodup_append] at hnd
    have h1 := hnd.1
    rw [List.nodup_append] at h1
    intro hm
    exact h1.2.2 (pairOf v0) hm (pairOf v0) (List.mem_singleton_self _) rfl
  clear hnd
  induction p1 with
  | nil => simp [splitAtPair]
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.cons_append, splitAtPair, Ne.symm hnot.1, ↓reduceIte]
    rw [ih hnot.2]
    rfl

lemma scanMidList_unique_selfOpp {k : ℕ} {tailPairs : List (Fin k)}
    {p1 seg rest : List (Fin (2 * k))} {v0 v : Fin (2 * k)}
    (hclean : CleanPrefix (p1 ++ [v0] ++ seg) tailPairs) (hmv : v0 = mate v) :
    scanMidList tailPairs (p1 ++ [v0] ++ seg ++ [v] ++ rest) =
      .selfOpp p1 v0 seg v rest := by
  unfold scanMidList
  have h1 : p1 ++ [v0] ++ seg ++ [v] ++ rest = (p1 ++ [v0] ++ seg) ++ (v :: rest) := by simp
  rw [h1, scanMidAux_unique_prefix tailPairs [] (p1 ++ [v0] ++ seg) (v :: rest) (by simpa using hclean)]
  simp only [List.nil_append]
  unfold scanMidAux
  have hp : pairOf v = pairOf v0 := by rw [hmv, pairOf_mate]
  rw [hp, splitAtPair_eq_of_clean hclean.1]
  have hne : v0 ≠ v := by rw [hmv]; exact mate_ne_self v
  simp [hne]

lemma scanMidList_unique_selfSame {k : ℕ} {tailPairs : List (Fin k)}
    {p1 seg rest : List (Fin (2 * k))} {v : Fin (2 * k)}
    (hclean : CleanPrefix (p1 ++ [v] ++ seg) tailPairs) :
    scanMidList tailPairs (p1 ++ [v] ++ seg ++ [v] ++ rest) =
      .selfSame p1 seg v rest := by
  unfold scanMidList
  have h1 : p1 ++ [v] ++ seg ++ [v] ++ rest = (p1 ++ [v] ++ seg) ++ (v :: rest) := by simp
  rw [h1, scanMidAux_unique_prefix tailPairs [] (p1 ++ [v] ++ seg) (v :: rest) (by simpa using hclean)]
  simp only [List.nil_append]
  unfold scanMidAux
  rw [splitAtPair_eq_of_clean hclean.1]
  simp

lemma scanMidList_unique_hitLater {k : ℕ} {tailPairs : List (Fin k)}
    {seen rest : List (Fin (2 * k))} {v : Fin (2 * k)}
    (hclean : CleanPrefix seen tailPairs) (hmem : pairOf v ∈ tailPairs) :
    scanMidList tailPairs (seen ++ [v] ++ rest) = .hitLater seen v rest := by
  unfold scanMidList
  have h1 : seen ++ [v] ++ rest = seen ++ (v :: rest) := by simp
  rw [h1, scanMidAux_unique_prefix tailPairs [] seen (v :: rest) (by simpa using hclean)]
  simp only [List.nil_append]
  unfold scanMidAux
  have hnot : pairOf v ∉ seen.map pairOf := by
    intro hm
    rcases List.mem_map.mp hm with ⟨w, hw, heq⟩
    exact hclean.2 w hw (by rwa [heq])
  have hsp := splitAtPair_spec (pairOf v) seen
  cases hs : splitAtPair (pairOf v) seen with
  | some res =>
    rcases res with ⟨p1, v0, seg⟩
    rw [hs] at hsp
    rcases hsp with ⟨hseen, hv0, _⟩
    exfalso; apply hnot
    rw [hseen, ← hv0]; exact List.mem_map_of_mem (by simp)
  | none =>
    simp [hmem]

/-- Insert a clow into a strictly head-sorted list of clows. -/
def insertClow {k : ℕ} (Cnew : Clow k) : List (Clow k) → List (Clow k)
  | [] => [Cnew]
  | D :: ds => if Cnew.head < D.head then Cnew :: D :: ds else D :: insertClow Cnew ds

lemma insertClow_perm {k : ℕ} (Cnew : Clow k) (ds : List (Clow k)) :
    (insertClow Cnew ds).Perm (Cnew :: ds) := by
  induction ds with
  | nil => exact List.Perm.refl _
  | cons D ds ih =>
    unfold insertClow
    split_ifs
    · exact List.Perm.refl _
    · exact (ih.cons D).trans (List.Perm.swap Cnew D ds)

lemma insertClow_heads_strict {k : ℕ} (Cnew : Clow k) (ds : List (Clow k))
    (hds : (ds.map Clow.head).Pairwise (· < ·)) (hne : ∀ D ∈ ds, Cnew.head ≠ D.head) :
    ((insertClow Cnew ds).map Clow.head).Pairwise (· < ·) := by
  induction ds with
  | nil => simp [insertClow]
  | cons D ds ih =>
    simp only [List.map_cons, List.pairwise_cons] at hds
    unfold insertClow
    split_ifs with hlt
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, hds.1, hds.2⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hlt
      · exact lt_trans hlt (hds.1 x hx)
    · have hgt : D.head < Cnew.head := lt_of_le_of_ne (not_lt.mp hlt) (hne D List.mem_cons_self).symm
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih hds.2 (fun E hE => hne E (List.mem_cons_of_mem _ hE))⟩
      intro x hx
      have hperm := (insertClow_perm Cnew ds).map Clow.head
      rw [hperm.mem_iff] at hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hgt
      · exact hds.1 x hx

lemma insertClow_split {k : ℕ} (Cnew : Clow k) (ds : List (Clow k)) :
    ∃ s1 s2, insertClow Cnew ds = s1 ++ [Cnew] ++ s2 ∧ s1 ++ s2 = ds := by
  induction ds with
  | nil => exact ⟨[], [], rfl, rfl⟩
  | cons D ds ih =>
    unfold insertClow
    split_ifs
    · exact ⟨[], D :: ds, rfl, rfl⟩
    · rcases ih with ⟨s1, s2, h1, h2⟩
      exact ⟨D :: s1, s2, by simp [h1], by simp [h2]⟩

lemma insertClow_eq_of_sorted {k : ℕ} {s1 s2 : List (Clow k)} {D : Clow k}
    (hpw : ((s1 ++ [D] ++ s2).map Clow.head).Pairwise (· < ·)) :
    insertClow D (s1 ++ s2) = s1 ++ [D] ++ s2 := by
  induction s1 with
  | nil =>
    cases s2 with
    | nil => rfl
    | cons E es =>
      simp only [List.nil_append, List.cons_append, List.map_cons, List.pairwise_cons] at hpw
      have hlt : D.head < E.head := hpw.1 E.head List.mem_cons_self
      simp [insertClow, hlt]
  | cons X xs ih =>
    simp only [List.cons_append, List.map_cons, List.pairwise_cons] at hpw
    have hlt : X.head < D.head := hpw.1 D.head (by simp)
    have hnot : ¬ (D.head < X.head) := lt_asymm hlt
    simp only [List.cons_append, insertClow, hnot, ↓reduceIte]
    rw [ih hpw.2]

/-- Find the first clow in `suff` containing pair `p`, splitting `suff = s1 ++ [D] ++ s2`. -/
def findClowWithPair {k : ℕ} (p : Fin k) :
    List (Clow k) → Option (List (Clow k) × Clow k × List (Clow k))
  | [] => none
  | D :: ds =>
    if p ∈ D.verts.map pairOf then some ([], D, ds)
    else (findClowWithPair p ds).map fun ⟨s1, E, s2⟩ => (D :: s1, E, s2)

lemma findClowWithPair_spec {k : ℕ} (p : Fin k) (ds : List (Clow k)) :
    match findClowWithPair p ds with
    | none => p ∉ clowsPairs ds
    | some (s1, D, s2) =>
        ds = s1 ++ [D] ++ s2 ∧ p ∈ D.verts.map pairOf ∧ p ∉ clowsPairs s1 := by
  induction ds with
  | nil => simp [findClowWithPair, clowsPairs]
  | cons D ds ih =>
    unfold findClowWithPair
    split_ifs with h
    · simp [h, clowsPairs]
    · cases hf : findClowWithPair p ds with
      | none =>
        rw [hf] at ih
        simp only [Option.map]
        unfold clowsPairs at ih ⊢
        simp [List.flatMap_cons, h, ih]
      | some res =>
        rcases res with ⟨s1, E, s2⟩
        rw [hf] at ih
        rcases ih with ⟨rfl, hE, hns1⟩
        refine ⟨rfl, hE, ?_⟩
        unfold clowsPairs at hns1 ⊢
        simp [List.flatMap_cons, h, hns1]

lemma findClowWithPair_unique {k : ℕ} {p : Fin k} {s1 s2 : List (Clow k)} {D : Clow k}
    (htc : TailClean (s1 ++ [D] ++ s2)) (hmem : p ∈ D.verts.map pairOf) :
    findClowWithPair p (s1 ++ [D] ++ s2) = some (s1, D, s2) := by
  have hnot : p ∉ clowsPairs s1 := by
    unfold TailClean clowsPairs at htc
    unfold clowsPairs
    have hsplit : s1 ++ [D] ++ s2 = s1 ++ (D :: s2) := by simp
    rw [hsplit, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
        List.nodup_append] at htc
    intro hm
    exact htc.2.2 p hm p (List.mem_append_left _ hmem) rfl
  clear htc
  induction s1 with
  | nil => simp [findClowWithPair, hmem]
  | cons X xs ih =>
    unfold clowsPairs at hnot
    simp only [List.flatMap_cons, List.map_append, List.mem_append, not_or] at hnot
    simp only [List.cons_append, findClowWithPair, hnot.1, ↓reduceIte]
    rw [ih hnot.2]
    rfl

lemma clowsPairs_perm_of_perm {k : ℕ} {cs₁ cs₂ : List (Clow k)} (h : cs₁.Perm cs₂) :
    (clowsPairs cs₁).Perm (clowsPairs cs₂) := by
  unfold clowsPairs
  refine List.Perm.map pairOf ?_
  induction h with
  | nil => exact List.Perm.nil
  | cons C _ ih => exact ih.append_left C.verts
  | swap C₁ C₂ rest =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma clows_prod_perm {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) {cs₁ cs₂ : List (Clow k)} (h : cs₁.Perm cs₂) :
    (cs₁.map (clowWeight A)).prod = (cs₂.map (clowWeight A)).prod :=
  (h.map (clowWeight A)).prod_eq

lemma clows_len_sum_perm {k : ℕ} {cs₁ cs₂ : List (Clow k)} (h : cs₁.Perm cs₂) :
    (cs₁.map Clow.len).sum = (cs₂.map Clow.len).sum :=
  (h.map Clow.len).sum_eq

/-- Helper: if `W.heads_strict` and `W.clows = pref ++ [C] ++ suff` with `TailClean suff`
and `¬ TailClean (C :: suff)`, then `scanMidList (clowsPairs suff) C.mid` cannot be `.none`. -/
lemma scanMidList_ne_none_of_bad {k : ℕ} {C : Clow k} {suff : List (Clow k)}
    (hhead_lt : ∀ D ∈ suff, C.head < D.head)
    (hts : TailClean suff) (hnb : ¬ TailClean (C :: suff)) :
    scanMidList (clowsPairs suff) C.mid ≠ .none := by
  intro hnone
  have hsp := scanMidList_spec (clowsPairs suff) C.mid
  rw [hnone] at hsp
  apply hnb
  unfold TailClean clowsPairs at hts ⊢
  rw [List.flatMap_cons, List.map_append, List.nodup_append]
  refine ⟨?_, hts, ?_⟩
  · unfold Clow.verts
    rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hsp.1, List.nodup_singleton _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    intro heq; rw [heq, pairOf_oddV] at ha
    exact C.head_not_mem_mid_pairs ha
  · intro p hp q hqt heq
    subst heq
    unfold Clow.verts at hp
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hp
    rcases hp with hmid | rfl
    · rcases List.mem_map.mp hmid with ⟨v, hv, rfl⟩
      exact hsp.2 v hv hqt
    · rcases List.mem_map.mp hqt with ⟨w, hw, hpw⟩
      rcases List.mem_flatMap.mp hw with ⟨D, hD, hDw⟩
      have h1 : C.head < D.head := hhead_lt D hD
      have h2 : D.head ≤ pairOf w := D.head_le_pairOf_verts hDw
      rw [hpw, pairOf_oddV] at h2
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

/-- Helper for Case 3 of `clowInv`. -/
def clowInvStep3 {k : ℕ} (W : ClowSeq k) (pref : List (Clow k)) (C : Clow k) (suff : List (Clow k))
    (hclows_eq : W.clows = pref ++ [C] ++ suff)
    (hpw_all : ((pref ++ [C] ++ suff).map Clow.head).Pairwise (· < ·))
    (hhead_lt_suff : ∀ D ∈ suff, C.head < D.head)
    (seen : List (Fin (2 * k))) (v : Fin (2 * k)) (rest : List (Fin (2 * k)))
    (hmid_eq : C.mid = seen ++ [v] ++ rest)
    (fc : Option (List (Clow k) × Clow k × List (Clow k)))
    (hfc : findClowWithPair (pairOf v) suff = fc) : ClowSeq k :=
  match fc, hfc with
  | none, _ => W
  | some (s1, D, s2), hfc =>
    have hfc_spec := findClowWithPair_spec (pairOf v) suff
    have hfc' : suff = s1 ++ [D] ++ s2 ∧ pairOf v ∈ D.verts.map pairOf := by
      rw [hfc] at hfc_spec; exact ⟨hfc_spec.1, hfc_spec.2.1⟩
    let cyc := orientTo D.verts v
    have hcyc_spec := orientTo_spec D.verts v hfc'.2
    have hcyc_perm := inDihedral_perm_pairOf hcyc_spec.1
    let C' : Clow k := {
      head := C.head
      mid := seen ++ [v] ++ cyc ++ rest
      mid_gt := by
        intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with ((hs | rfl) | hcyc) | hr
        · exact C.mid_gt w (by rw [hmid_eq]; simp [hs])
        · exact C.mid_gt w (by rw [hmid_eq]; simp)
        · have hpw : pairOf w ∈ D.verts.map pairOf :=
            hcyc_perm.mem_iff.mpr (List.mem_map_of_mem hcyc)
          rcases List.mem_map.mp hpw with ⟨u, hu, heq⟩
          rw [← heq]
          exact lt_of_lt_of_le (hhead_lt_suff D (by rw [hfc'.1]; simp))
            (D.head_le_pairOf_verts hu)
        · exact C.mid_gt w (by rw [hmid_eq]; simp [hr])
    }
    {
      clows := pref ++ [C'] ++ (s1 ++ s2)
      heads_strict := by
        have hsub : List.Sublist ((pref ++ [C'] ++ (s1 ++ s2)).map Clow.head)
            ((pref ++ [C] ++ (s1 ++ [D] ++ s2)).map Clow.head) := by
          simp only [List.map_append, List.map_singleton, C', List.append_assoc]
          refine List.Sublist.append (List.Sublist.refl _) ?_
          refine List.Sublist.append (List.Sublist.refl _) ?_
          refine List.Sublist.append (List.Sublist.refl _) ?_
          exact List.sublist_append_right [D.head] (s2.map Clow.head)
        have hpw' : ((pref ++ [C] ++ (s1 ++ [D] ++ s2)).map Clow.head).Pairwise (· < ·) := by
          rwa [← hfc'.1]
        exact hpw'.sublist hsub
      total_len := by
        have htot := W.total_len
        rw [hclows_eq, hfc'.1] at htot
        have hcyc_len : cyc.length = D.len := by
          rw [← Clow.verts_length]
          have := hcyc_perm.length_eq
          simp only [List.length_map] at this
          exact this.symm
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
          Clow.len, C', List.length_append, List.length_singleton, hcyc_len] at htot ⊢
        rw [hmid_eq] at htot
        simp only [List.length_append, List.length_singleton] at htot
        omega
    }

/-- Helper dispatching Cases 1, 2, 3 of `clowInv`. -/
def clowInvStep2 {k : ℕ} (W : ClowSeq k) (pref : List (Clow k)) (C : Clow k) (suff : List (Clow k))
    (hclows_eq : W.clows = pref ++ [C] ++ suff)
    (hpw_all : ((pref ++ [C] ++ suff).map Clow.head).Pairwise (· < ·))
    (hhead_lt_suff : ∀ D ∈ suff, C.head < D.head)
    (hhead_gt_pref : ∀ P ∈ pref, P.head < C.head)
    (hpw_pref : (pref.map Clow.head).Pairwise (· < ·))
    (hpw_suff : (suff.map Clow.head).Pairwise (· < ·))
    (sc : ScanRes k) (hsc : scanMidList (clowsPairs suff) C.mid = sc) : ClowSeq k :=
  match sc, hsc with
  | .none, _ => W
  | .selfOpp p1 v0 seg v rest, hsc =>
    have hscan_spec := scanMidList_spec (clowsPairs suff) C.mid
    have hmid_eq : C.mid = p1 ++ [v0] ++ seg ++ [v] ++ rest := by
      rw [hsc] at hscan_spec; exact hscan_spec.1
    let C' : Clow k := {
      head := C.head
      mid := p1 ++ [v0] ++ revMate seg ++ [v] ++ rest
      mid_gt := by
        intro w hw
        have hw' : pairOf w ∈ C.mid.map pairOf := by
          rw [hmid_eq]
          simp only [List.mem_append, List.mem_singleton] at hw
          simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
          rcases hw with (((hp | rfl) | hrm) | rfl) | hr
          · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem hp))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
          · have hmw := mem_revMate_iff.mp hrm
            exact Or.inl (Or.inl (Or.inr (by rw [← pairOf_mate w]; exact List.mem_map_of_mem hmw)))
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (List.mem_map_of_mem hr)
        rcases List.mem_map.mp hw' with ⟨u, hu, heq⟩
        rw [← heq]; exact C.mid_gt u hu
    }
    {
      clows := pref ++ [C'] ++ suff
      heads_strict := by simpa [C'] using hpw_all
      total_len := by
        have htot := W.total_len
        rw [hclows_eq] at htot
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
          Clow.len, C', List.length_append, List.length_singleton, revMate_length] at htot ⊢
        rw [hmid_eq] at htot
        simp only [List.length_append, List.length_singleton] at htot
        exact htot
    }
  | .selfSame p1 seg v rest, hsc =>
    have hscan_spec := scanMidList_spec (clowsPairs suff) C.mid
    have hsc_pair : C.mid = p1 ++ [v] ++ seg ++ [v] ++ rest ∧
        CleanPrefix (p1 ++ [v] ++ seg) (clowsPairs suff) := by
      rw [hsc] at hscan_spec; exact hscan_spec
    let cyc := seg ++ [v]
    have hcyc_ne : cyc ≠ [] := by simp [cyc]
    have hcyc_nodup : (cyc.map pairOf).Nodup := by
      have hnd := hsc_pair.2.1
      have hperm : ((p1 ++ [v] ++ seg).map pairOf).Perm (p1.map pairOf ++ cyc.map pairOf) := by
        dsimp [cyc]
        simp only [List.map_append, List.map_singleton, List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
      have hnd' := hperm.nodup_iff.mp hnd
      exact (List.nodup_append.mp hnd').2.1
    let Cnew := mkClowFromCycle cyc hcyc_ne hcyc_nodup
    let C' : Clow k := {
      head := C.head
      mid := p1 ++ [v] ++ rest
      mid_gt := by
        intro w hw
        apply C.mid_gt w
        rw [hsc_pair.1]
        simp only [List.mem_append, List.mem_singleton] at hw ⊢
        tauto
    }
    have hCnew_gt_C : C.head < Cnew.head := by
      have hmem : Cnew.head ∈ cyc.map pairOf := minPair_mem cyc hcyc_ne
      rcases List.mem_map.mp hmem with ⟨u, hu, heq⟩
      rw [← heq]; apply C.mid_gt u
      rw [hsc_pair.1]
      simp only [cyc, List.mem_append, List.mem_singleton] at hu
      simp only [List.mem_append, List.mem_singleton]
      tauto
    have hCnew_not_suff : ∀ D ∈ suff, Cnew.head ≠ D.head := by
      intro D hD heq
      have hmem : Cnew.head ∈ cyc.map pairOf := minPair_mem cyc hcyc_ne
      rcases List.mem_map.mp hmem with ⟨u, hu, hpu⟩
      have hu_in : u ∈ p1 ++ [v] ++ seg := by
        simp only [cyc, List.mem_append, List.mem_singleton] at hu ⊢
        tauto
      have hnot := hsc_pair.2.2 u hu_in
      apply hnot
      rw [hpu, heq]
      unfold clowsPairs
      exact List.mem_map.mpr ⟨oddV D.head, List.mem_flatMap.mpr ⟨D, hD, by simp [Clow.verts]⟩,
        by simp⟩
    {
      clows := pref ++ [C'] ++ insertClow Cnew suff
      heads_strict := by
        rw [List.map_append, List.map_append, List.map_singleton, List.pairwise_append]
        refine ⟨?_, insertClow_heads_strict Cnew suff hpw_suff hCnew_not_suff, ?_⟩
        · rw [List.pairwise_append]
          refine ⟨hpw_pref, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb; subst hb
          rcases List.mem_map.mp ha with ⟨P, hP, rfl⟩
          exact hhead_gt_pref P hP
        · intro a ha b hb
          have hb' : b ∈ (Cnew :: suff).map Clow.head :=
            ((insertClow_perm Cnew suff).map Clow.head).mem_iff.mp hb
          simp only [List.map_cons, List.mem_cons] at hb'
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · rcases List.mem_map.mp ha with ⟨P, hP, rfl⟩
            have hPC := hhead_gt_pref P hP
            rcases hb' with rfl | hbd
            · exact lt_trans hPC hCnew_gt_C
            · rcases List.mem_map.mp hbd with ⟨D, hD, rfl⟩
              exact lt_trans hPC (hhead_lt_suff D hD)
          · rcases hb' with rfl | hbd
            · exact hCnew_gt_C
            · rcases List.mem_map.mp hbd with ⟨D, hD, rfl⟩
              exact hhead_lt_suff D hD
      total_len := by
        have htot := W.total_len
        rw [hclows_eq] at htot
        have hCnew_len : Cnew.len = cyc.length := by
          rw [← Clow.verts_length, mkClowFromCycle_verts]
          have hmem : pairOf (oddV (minPair cyc hcyc_ne)) ∈ cyc.map pairOf := by
            rw [pairOf_oddV]; exact minPair_mem cyc hcyc_ne
          have ⟨hd, _⟩ := orientTo_spec cyc (oddV (minPair cyc hcyc_ne)) hmem
          have hperm := inDihedral_perm_pairOf hd
          have := hperm.length_eq
          simp only [List.length_map] at this
          exact this.symm
        rw [List.map_append, List.map_append, List.map_singleton,
            List.sum_append, List.sum_append, List.sum_singleton,
            clows_len_sum_perm (insertClow_perm Cnew suff),
            List.map_cons, List.sum_cons, hCnew_len]
        rw [List.map_append, List.map_append, List.map_singleton,
            List.sum_append, List.sum_append, List.sum_singleton] at htot
        simp only [Clow.len, C', cyc, List.length_append, List.length_singleton] at htot ⊢
        rw [hsc_pair.1] at htot
        simp only [List.length_append, List.length_singleton] at htot
        omega
    }
  | .hitLater seen v rest, hsc =>
    have hscan_spec := scanMidList_spec (clowsPairs suff) C.mid
    have hmid_eq : C.mid = seen ++ [v] ++ rest := by
      rw [hsc] at hscan_spec; exact hscan_spec.1
    clowInvStep3 W pref C suff hclows_eq hpw_all hhead_lt_suff seen v rest hmid_eq _ rfl

/-- Helper dispatching `splitBad` for `clowInv`. -/
def clowInvStep1 {k : ℕ} (W : ClowSeq k)
    (sb : Option (List (Clow k) × Clow k × List (Clow k)))
    (hsb : splitBad W.clows = sb) : ClowSeq k :=
  match sb, hsb with
  | none, _ => W
  | some (pref, C, suff), hsb =>
    have hsb_spec := splitBad_some_spec hsb
    have hclows_eq : W.clows = pref ++ [C] ++ suff := hsb_spec.1
    have hpw_all : ((pref ++ [C] ++ suff).map Clow.head).Pairwise (· < ·) := by
      rw [← hclows_eq]; exact W.heads_strict
    have hhead_lt_suff : ∀ D ∈ suff, C.head < D.head := by
      intro D hD
      rw [List.map_append, List.map_append, List.map_singleton, List.pairwise_append] at hpw_all
      exact hpw_all.2.2 C.head (by simp) D.head (List.mem_map_of_mem hD)
    have hhead_gt_pref : ∀ P ∈ pref, P.head < C.head := by
      intro P hP
      rw [List.map_append, List.map_append, List.map_singleton, List.pairwise_append] at hpw_all
      have h1 := hpw_all.1
      rw [List.pairwise_append] at h1
      exact h1.2.2 P.head (List.mem_map_of_mem hP) C.head (List.mem_singleton_self _)
    have hpw_pref : (pref.map Clow.head).Pairwise (· < ·) := by
      rw [List.map_append, List.map_append, List.pairwise_append] at hpw_all
      exact (List.pairwise_append.mp hpw_all.1).1
    have hpw_suff : (suff.map Clow.head).Pairwise (· < ·) := by
      rw [List.map_append, List.pairwise_append] at hpw_all
      exact hpw_all.2.1
    clowInvStep2 W pref C suff hclows_eq hpw_all hhead_lt_suff hhead_gt_pref hpw_pref hpw_suff _ rfl

/-- The 3-case sign-reversing, fixed-point-free involution on non-simple diagonal-free `ClowSeq k`.
Outside `{W | IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W}`, returns `W`. -/
def clowInv {k : ℕ} (W : ClowSeq k) : ClowSeq k :=
  if _ : IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W then clowInvStep1 W _ rfl else W

private lemma clowInvStep1_eq {k : ℕ} (W : ClowSeq k) (sb : Option (List (Clow k) × Clow k × List (Clow k)))
    (hsb : splitBad W.clows = sb) : clowInvStep1 W (splitBad W.clows) rfl = clowInvStep1 W sb hsb := by
  cases hsb; rfl

private lemma clowInvStep2_eq {k : ℕ} (W : ClowSeq k) (pref : List (Clow k)) (C : Clow k)
    (suff : List (Clow k)) (hclows_eq hpw_all hhead_lt_suff hhead_gt_pref hpw_pref hpw_suff)
    (sc : ScanRes k) (hsc : scanMidList (clowsPairs suff) C.mid = sc) :
    clowInvStep2 W pref C suff hclows_eq hpw_all hhead_lt_suff hhead_gt_pref hpw_pref hpw_suff
      (scanMidList (clowsPairs suff) C.mid) rfl =
    clowInvStep2 W pref C suff hclows_eq hpw_all hhead_lt_suff hhead_gt_pref hpw_pref hpw_suff sc hsc := by
  cases hsc; rfl

private lemma clowInvStep3_eq {k : ℕ} (W : ClowSeq k) (pref : List (Clow k)) (C : Clow k)
    (suff : List (Clow k)) (hclows_eq hpw_all hhead_lt_suff seen v rest hmid_eq)
    (fc : Option (List (Clow k) × Clow k × List (Clow k)))
    (hfc : findClowWithPair (pairOf v) suff = fc) :
    clowInvStep3 W pref C suff hclows_eq hpw_all hhead_lt_suff seen v rest hmid_eq
      (findClowWithPair (pairOf v) suff) rfl =
    clowInvStep3 W pref C suff hclows_eq hpw_all hhead_lt_suff seen v rest hmid_eq fc hfc := by
  cases hfc; rfl

private lemma clowInv_clows_selfOpp {k : ℕ} (W : ClowSeq k) (hW : IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W)
    {pref suff : List (Clow k)} {C : Clow k}
    (hsb : splitBad W.clows = some (pref, C, suff))
    {p1 seg rest : List (Fin (2 * k))} {v0 v : Fin (2 * k)}
    (hsc : scanMidList (clowsPairs suff) C.mid = .selfOpp p1 v0 seg v rest)
    (hgt : ∀ w ∈ p1 ++ [v0] ++ revMate seg ++ [v] ++ rest, C.head < pairOf w) :
    (clowInv W).clows = pref ++ [⟨C.head, p1 ++ [v0] ++ revMate seg ++ [v] ++ rest, hgt⟩] ++ suff := by
  unfold clowInv
  rw [dif_pos hW, clowInvStep1_eq W (some (pref, C, suff)) hsb]
  dsimp only [clowInvStep1]
  rw [clowInvStep2_eq (hsc := hsc)]
  rfl

private lemma clowInv_clows_selfSame {k : ℕ} (W : ClowSeq k) (hW : IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W)
    {pref suff : List (Clow k)} {C : Clow k}
    (hsb : splitBad W.clows = some (pref, C, suff))
    {p1 seg rest : List (Fin (2 * k))} {v : Fin (2 * k)}
    (hsc : scanMidList (clowsPairs suff) C.mid = .selfSame p1 seg v rest)
    (hgt : ∀ w ∈ p1 ++ [v] ++ rest, C.head < pairOf w)
    (hnd : ((seg ++ [v]).map pairOf).Nodup) :
    (clowInv W).clows =
      pref ++ [⟨C.head, p1 ++ [v] ++ rest, hgt⟩] ++
        insertClow (mkClowFromCycle (seg ++ [v]) (by simp) hnd) suff := by
  unfold clowInv
  rw [dif_pos hW, clowInvStep1_eq W (some (pref, C, suff)) hsb]
  dsimp only [clowInvStep1]
  rw [clowInvStep2_eq (hsc := hsc)]
  rfl

private lemma clowInv_clows_hitLater {k : ℕ} (W : ClowSeq k) (hW : IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W)
    {pref suff s1 s2 : List (Clow k)} {C D : Clow k}
    (hsb : splitBad W.clows = some (pref, C, suff))
    {seen rest : List (Fin (2 * k))} {v : Fin (2 * k)}
    (hsc : scanMidList (clowsPairs suff) C.mid = .hitLater seen v rest)
    (hfc : findClowWithPair (pairOf v) suff = some (s1, D, s2))
    (hgt : ∀ w ∈ seen ++ [v] ++ orientTo D.verts v ++ rest, C.head < pairOf w) :
    (clowInv W).clows =
      pref ++ [⟨C.head, seen ++ [v] ++ orientTo D.verts v ++ rest, hgt⟩] ++ (s1 ++ s2) := by
  unfold clowInv
  rw [dif_pos hW, clowInvStep1_eq W (some (pref, C, suff)) hsb]
  dsimp only [clowInvStep1]
  rw [clowInvStep2_eq (hsc := hsc)]
  dsimp only [clowInvStep2]
  rw [clowInvStep3_eq (hfc := hfc)]
  rfl

@[ext] lemma Clow.ext {k : ℕ} {a b : Clow k} (h1 : a.head = b.head) (h2 : a.mid = b.mid) :
    a = b := by
  cases a; cases b; cases h1; cases h2; rfl

@[ext] lemma ClowSeq.ext {k : ℕ} {a b : ClowSeq k} (h : a.clows = b.clows) : a = b := by
  cases a; cases b; cases h; rfl

/-- Helper: if `W` is diagonal-free and non-simple, and `splitBad W.clows = some (pref, C, suff)`,
then `clowInv W` unfolds cleanly in each of the 3 cases. -/
private lemma cleanPrefix_revMate_mid {k : ℕ} {tailPairs : List (Fin k)}
    {p1 seg : List (Fin (2 * k))} {v0 : Fin (2 * k)}
    (hclean : CleanPrefix (p1 ++ [v0] ++ seg) tailPairs) :
    CleanPrefix (p1 ++ [v0] ++ revMate seg) tailPairs := by
  have hperm : ((p1 ++ [v0] ++ revMate seg).map pairOf).Perm
      ((p1 ++ [v0] ++ seg).map pairOf) := by
    simp only [List.map_append, List.map_singleton, map_pairOf_revMate]
    exact List.Perm.append_left _ (List.reverse_perm _)
  refine ⟨hperm.nodup_iff.mpr hclean.1, fun w hw => ?_⟩
  have hpw : pairOf w ∈ ((p1 ++ [v0] ++ seg).map pairOf) :=
    hperm.mem_iff.mp (List.mem_map_of_mem hw)
  rcases List.mem_map.mp hpw with ⟨u, hu, heq⟩
  rw [← heq]; exact hclean.2 u hu

private lemma revMate_ne_self_of_pairOf_nodup {k : ℕ} {seg : List (Fin (2 * k))}
    (hne : seg ≠ []) (hnd : (seg.map pairOf).Nodup) : revMate seg ≠ seg := by
  intro heq
  cases hlen : seg with
  | nil => exact hne hlen
  | cons x xs =>
    cases hxs : xs.reverse with
    | nil =>
      have hx0 : xs = [] := List.reverse_eq_nil_iff.mp hxs
      subst hx0
      rw [hlen] at heq
      simp only [revMate_singleton, List.cons.injEq] at heq
      exact mate_ne_self x heq.1
    | cons y ys =>
      have hseg_eq : seg = x :: ys.reverse ++ [y] := by
        rw [hlen]
        have := congrArg List.reverse hxs
        simp at this
        simp [this]
      have hhead_eq : (revMate seg).head? = seg.head? := congrArg List.head? heq
      rw [hseg_eq] at hhead_eq hnd
      have hr : revMate (x :: ys.reverse ++ [y]) = mate y :: revMate (x :: ys.reverse) := by
        change revMate ((x :: ys.reverse) ++ [y]) = _
        rw [revMate_append, revMate_singleton]; rfl
      rw [hr] at hhead_eq
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead_eq
      have hp : pairOf x = pairOf y := by rw [← hhead_eq, pairOf_mate]
      simp only [List.cons_append, List.map_cons, List.map_append, List.map_singleton,
        List.nodup_cons, List.mem_append, List.mem_singleton] at hnd
      exact hnd.1 (Or.inr (by simp [hp]))

/-- Main theorem of Section 4: `clowInv` is a fixed-point-free, sign-reversing involution
on `{W : ClowSeq k // IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W}`. -/
theorem clowInv_properties {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (W : ClowSeq k) (hW : IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W) :
    (IsDiagFreeSeq (clowInv W) ∧ ¬ IsSimpleSeq (clowInv W)) ∧
    clowInv (clowInv W) = W ∧
    clowInv W ≠ W ∧
    clowSeqWeight A (clowInv W) = -clowSeqWeight A W := by
  have hsb_ne : splitBad W.clows ≠ none := by
    intro h0; exact hW.2 ((splitBad_none_iff W.clows).mp h0)
  cases hsb : splitBad W.clows with
  | none => exact absurd hsb hsb_ne
  | some res =>
    rcases res with ⟨pref, C, suff⟩
    have hsb_spec := splitBad_some_spec hsb
    have hclows_eq : W.clows = pref ++ [C] ++ suff := hsb_spec.1
    have hts : TailClean suff := hsb_spec.2.1
    have hnb : ¬ TailClean (C :: suff) := hsb_spec.2.2
    have hpw_all : ((pref ++ [C] ++ suff).map Clow.head).Pairwise (· < ·) := by
      rw [← hclows_eq]; exact W.heads_strict
    have hhead_lt_suff : ∀ D ∈ suff, C.head < D.head := by
      intro D hD
      rw [List.map_append, List.map_append, List.map_singleton, List.pairwise_append] at hpw_all
      exact hpw_all.2.2 C.head (by simp) D.head (List.mem_map_of_mem hD)
    have hC_df : IsDiagFreeList C.mid := hW.1 C (by rw [hclows_eq]; simp)
    have hscan_ne : scanMidList (clowsPairs suff) C.mid ≠ .none :=
      scanMidList_ne_none_of_bad hhead_lt_suff hts hnb
    have hscan_spec := scanMidList_spec (clowsPairs suff) C.mid
    cases hsc : scanMidList (clowsPairs suff) C.mid with
    | none => exact absurd hsc hscan_ne
    | selfOpp p1 v0 seg v rest =>
      -- CASE 1: Self-opposite
      rw [hsc] at hscan_spec
      rcases hscan_spec with ⟨hmid_eq, hclean, hmv⟩
      have hv_eq : v = mate v0 := by rw [hmv, mate_mate]
      have hseg_ne : seg ≠ [] := by
        intro h0; subst h0
        rw [hmid_eq, hv_eq] at hC_df
        have hbad : ¬ IsDiagFreeList (p1 ++ [v0, mate v0] ++ rest) :=
          (isDiagFreeList_iff_not_exists_adj _).mpr ⟨p1, rest, v0, rfl⟩
        exact hbad (by simpa [List.append_assoc] using hC_df)
      have hseg_nd : (seg.map pairOf).Nodup := by
        have hnd := hclean.1
        rw [List.map_append, List.nodup_append] at hnd
        exact hnd.2.1
      have hC'_mid_gt : ∀ w ∈ p1 ++ [v0] ++ revMate seg ++ [v] ++ rest, C.head < pairOf w := by
        intro w hw
        have hw' : pairOf w ∈ C.mid.map pairOf := by
          rw [hmid_eq]
          simp only [List.mem_append, List.mem_singleton] at hw
          simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
          rcases hw with (((hp | rfl) | hrm) | rfl) | hr
          · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem hp))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
          · have hmw := mem_revMate_iff.mp hrm
            exact Or.inl (Or.inl (Or.inr (by rw [← pairOf_mate w]; exact List.mem_map_of_mem hmw)))
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (List.mem_map_of_mem hr)
        rcases List.mem_map.mp hw' with ⟨u, hu, heq⟩
        rw [← heq]; exact C.mid_gt u hu
      let C' : Clow k := ⟨C.head, p1 ++ [v0] ++ revMate seg ++ [v] ++ rest, hC'_mid_gt⟩
      have hinv_eq : (clowInv W).clows = pref ++ [C'] ++ suff :=
        clowInv_clows_selfOpp W hW hsb hsc hC'_mid_gt
      have hC'_df : IsDiagFreeList C'.mid := by
        dsimp [C']
        rw [hmid_eq] at hC_df
        have h1 : p1 ++ [v0] ++ seg ++ [v] ++ rest = (p1 ++ [v0]) ++ (seg ++ ([v] ++ rest)) := by
          simp [List.append_assoc]
        rw [h1, isDiagFreeList_append_iff] at hC_df
        have hdf_p1v0 : IsDiagFreeList (p1 ++ [v0]) := hC_df.1
        have hC_df2 : IsDiagFreeList (seg ++ ([v] ++ rest)) := hC_df.2.1
        rw [isDiagFreeList_append_iff] at hC_df2
        have hdf_seg : IsDiagFreeList seg := hC_df2.1
        have hdf_vrest : IsDiagFreeList ([v] ++ rest) := hC_df2.2.1
        have h2 : p1 ++ [v0] ++ revMate seg ++ [v] ++ rest =
            (p1 ++ [v0]) ++ (revMate seg ++ ([v] ++ rest)) := by simp [List.append_assoc]
        rw [h2, isDiagFreeList_append_iff]
        refine ⟨hdf_p1v0, ?_, ?_⟩
        · rw [isDiagFreeList_append_iff]
          refine ⟨(isDiagFreeList_revMate seg).mpr hdf_seg, hdf_vrest, ?_⟩
          intro x y hx hy
          have hy0 : y = v := by
            have : ([v] ++ rest).head? = some v := rfl
            rw [this] at hy; exact Option.some.inj hy.symm
          subst y
          have hx_mem : x ∈ revMate seg := List.mem_of_getLast? hx
          have hmx_seg : mate x ∈ seg := mem_revMate_iff.mp hx_mem
          intro hvmx
          have hpx : pairOf (mate x) = pairOf v0 := by rw [← hvmx, hmv, pairOf_mate]
          have hnd := hclean.1
          rw [List.map_append, List.map_append, List.map_singleton, List.nodup_append] at hnd
          exact hnd.2.2 (pairOf v0) (by simp) (pairOf (mate x)) (List.mem_map_of_mem hmx_seg) hpx.symm
        · intro x y hx hy
          have hx0 : x = v0 := by
            have : (p1 ++ [v0]).getLast? = some v0 := by simp
            rw [this] at hx; exact Option.some.inj hx.symm
          subst x
          have hrm_ne : revMate seg ≠ [] := by simp [revMate, hseg_ne]
          rw [List.head?_append_of_ne_nil _ hrm_ne] at hy
          have hy_mem : y ∈ revMate seg := List.mem_of_head? hy
          have hmy_seg : mate y ∈ seg := mem_revMate_iff.mp hy_mem
          intro hymv0
          have hpy : pairOf (mate y) = pairOf v0 := by rw [hymv0, mate_mate]
          have hnd := hclean.1
          rw [List.map_append, List.map_append, List.map_singleton, List.nodup_append] at hnd
          exact hnd.2.2 (pairOf v0) (by simp) (pairOf (mate y)) (List.mem_map_of_mem hmy_seg) hpy.symm
      have hW'_df : IsDiagFreeSeq (clowInv W) := by
        intro D hD
        rw [hinv_eq] at hD
        simp only [List.mem_append, List.mem_singleton] at hD
        rcases hD with (hp | rfl) | hs
        · exact hW.1 D (by rw [hclows_eq]; simp [hp])
        · exact hC'_df
        · exact hW.1 D (by rw [hclows_eq]; simp [hs])
      have hnb' : ¬ TailClean (C' :: suff) := by
        intro htc
        unfold TailClean clowsPairs at htc
        rw [List.flatMap_cons, List.map_append, List.nodup_append] at htc
        have hC'nd : (C'.verts.map pairOf).Nodup := htc.1
        unfold Clow.verts at hC'nd
        rw [List.map_append, List.nodup_append] at hC'nd
        have hmid_nd : (C'.mid.map pairOf).Nodup := hC'nd.1
        dsimp [C'] at hmid_nd
        have hsplit : p1 ++ [v0] ++ revMate seg ++ [v] ++ rest =
            (p1 ++ [v0] ++ revMate seg) ++ ([v] ++ rest) := by simp [List.append_assoc]
        rw [hsplit, List.map_append, List.nodup_append] at hmid_nd
        have hpair : pairOf v0 = pairOf v := by rw [hmv, pairOf_mate]
        exact hmid_nd.2.2 (pairOf v0) (by simp) (pairOf v) (by simp) hpair
      have hW'_ns : ¬ IsSimpleSeq (clowInv W) := by
        intro hs
        apply hnb'
        unfold IsSimpleSeq at hs
        unfold TailClean clowsPairs at hs ⊢
        rw [hinv_eq] at hs
        have h1 : pref ++ [C'] ++ suff = pref ++ (C' :: suff) := by simp
        rw [h1, List.flatMap_append, List.map_append, List.nodup_append] at hs
        exact hs.2.1
      have hsb' : splitBad (clowInv W).clows = some (pref, C', suff) := by
        rw [hinv_eq]; exact splitBad_unique hts hnb'
      have hclean' : CleanPrefix (p1 ++ [v0] ++ revMate seg) (clowsPairs suff) :=
        cleanPrefix_revMate_mid hclean
      have hsc' : scanMidList (clowsPairs suff) C'.mid =
          .selfOpp p1 v0 (revMate seg) v rest :=
        scanMidList_unique_selfOpp hclean' hmv
      have hinv_inv : clowInv (clowInv W) = W := by
        apply ClowSeq.ext
        rw [clowInv_clows_selfOpp (clowInv W) ⟨hW'_df, hW'_ns⟩ hsb' hsc' (by
              intro w hw; rw [revMate_revMate] at hw; exact C.mid_gt w (by rw [hmid_eq]; exact hw)),
            hclows_eq]
        congr 2; congr 1
        apply Clow.ext
        · rfl
        · simp [hmid_eq]
      have hne : clowInv W ≠ W := by
        intro heq
        have hcl := congrArg ClowSeq.clows heq
        rw [hinv_eq, hclows_eq] at hcl
        have h1 : [C'] ++ suff = [C] ++ suff :=
          List.append_cancel_left (as := pref) (by simpa [List.append_assoc] using hcl)
        have hCeq : C' = C := by simpa using h1
        have hmeq : C'.mid = C.mid := congrArg Clow.mid hCeq
        dsimp [C'] at hmeq
        rw [hmid_eq] at hmeq
        have h2 : revMate seg ++ ([v] ++ rest) = seg ++ ([v] ++ rest) :=
          List.append_cancel_left (as := p1 ++ [v0]) (by simpa [List.append_assoc] using hmeq)
        have h3 : revMate seg = seg := List.append_cancel_right h2
        exact revMate_ne_self_of_pairOf_nodup hseg_ne hseg_nd h3
      have hwt : clowSeqWeight A (clowInv W) = -clowSeqWeight A W := by
        unfold clowSeqWeight
        rw [hinv_eq, hclows_eq]
        simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
        suffices hcw : clowWeight A C' = -clowWeight A C by rw [hcw]; ring
        unfold clowWeight Clow.verts
        dsimp [C']
        rw [hmid_eq, hv_eq]
        have hrot1 : IsRot ((p1 ++ [v0] ++ revMate seg ++ [mate v0] ++ rest) ++ [oddV C.head])
            (((rest ++ [oddV C.head]) ++ p1 ++ [v0]) ++ (revMate seg ++ [mate v0])) :=
          ⟨p1 ++ [v0] ++ revMate seg ++ [mate v0], rest ++ [oddV C.head],
            by simp [List.append_assoc], by simp [List.append_assoc]⟩
        have hrot2 : IsRot ((p1 ++ [v0] ++ seg ++ [mate v0] ++ rest) ++ [oddV C.head])
            (((rest ++ [oddV C.head]) ++ p1 ++ [v0]) ++ (seg ++ [mate v0])) :=
          ⟨p1 ++ [v0] ++ seg ++ [mate v0], rest ++ [oddV C.head],
            by simp [List.append_assoc], by simp [List.append_assoc]⟩
        rw [cycWeight_of_isRot A hrot1, cycWeight_of_isRot A hrot2]
        have hneg := cycWeight_reverse_between_mates hA ((rest ++ [oddV C.head]) ++ p1) seg v0
        simp only [List.append_assoc] at hneg ⊢
        rw [hneg]
      exact ⟨⟨hW'_df, hW'_ns⟩, hinv_inv, hne, hwt⟩
    | selfSame p1 seg v rest =>
      -- CASE 2: Self-same -> Case 3 (hitLater)
      rw [hsc] at hscan_spec
      rcases hscan_spec with ⟨hmid_eq, hclean⟩
      let cyc := seg ++ [v]
      have hcyc_ne : cyc ≠ [] := by simp [cyc]
      have hcyc_nodup : (cyc.map pairOf).Nodup := by
        have hnd := hclean.1
        have hperm : ((p1 ++ [v] ++ seg).map pairOf).Perm (p1.map pairOf ++ cyc.map pairOf) := by
          dsimp [cyc]; simp only [List.map_append, List.map_singleton, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        exact (List.nodup_append.mp (hperm.nodup_iff.mp hnd)).2.1
      let Cnew := mkClowFromCycle cyc hcyc_ne hcyc_nodup
      have hCnew_verts : Cnew.verts = orientTo cyc (oddV (minPair cyc hcyc_ne)) :=
        mkClowFromCycle_verts cyc hcyc_ne hcyc_nodup
      have hCnew_hd : InDihedral cyc Cnew.verts := by
        rw [hCnew_verts]
        exact (orientTo_spec cyc (oddV (minPair cyc hcyc_ne))
          (by rw [pairOf_oddV]; exact minPair_mem cyc hcyc_ne)).1
      have hCnew_perm : (cyc.map pairOf).Perm (Cnew.verts.map pairOf) :=
        inDihedral_perm_pairOf hCnew_hd
      have hC'_mid_gt : ∀ w ∈ p1 ++ [v] ++ rest, C.head < pairOf w := by
        intro w hw; apply C.mid_gt w; rw [hmid_eq]
        simp only [List.mem_append, List.mem_singleton] at hw ⊢; tauto
      let C' : Clow k := ⟨C.head, p1 ++ [v] ++ rest, hC'_mid_gt⟩
      have hinv_eq : (clowInv W).clows = pref ++ [C'] ++ insertClow Cnew suff :=
        clowInv_clows_selfSame W hW hsb hsc hC'_mid_gt hcyc_nodup
      have hC'_df : IsDiagFreeList C'.mid := by
        dsimp [C']
        rw [hmid_eq] at hC_df
        have h1 : p1 ++ [v] ++ seg ++ [v] ++ rest = (p1 ++ [v]) ++ (seg ++ ([v] ++ rest)) := by
          simp [List.append_assoc]
        rw [h1, isDiagFreeList_append_iff] at hC_df
        have hdf_p1v : IsDiagFreeList (p1 ++ [v]) := hC_df.1
        have hC_df2 : IsDiagFreeList (seg ++ ([v] ++ rest)) := hC_df.2.1
        rw [isDiagFreeList_append_iff] at hC_df2
        have hdf_vrest : IsDiagFreeList ([v] ++ rest) := hC_df2.2.1
        have h2 : p1 ++ [v] ++ rest = (p1 ++ [v]) ++ rest := by simp [List.append_assoc]
        rw [h2, isDiagFreeList_append_iff]
        refine ⟨hdf_p1v, ?_, ?_⟩
        · cases rest with
          | nil => trivial
          | cons r rs => exact hdf_vrest.2
        · intro x y hx hy
          have hx0 : x = v := by
            have : (p1 ++ [v]).getLast? = some v := by simp
            rw [this] at hx; exact Option.some.inj hx.symm
          subst x
          cases rest with
          | nil => simp at hy
          | cons r rs =>
            simp only [List.head?_cons, Option.some.injEq] at hy; subst y
            exact hdf_vrest.1
      have hCnew_df : IsDiagFreeList Cnew.mid := by
        have hnd : (Cnew.verts.map pairOf).Nodup := hCnew_perm.nodup_iff.mp hcyc_nodup
        unfold Clow.verts at hnd
        rw [List.map_append, List.nodup_append] at hnd
        exact isDiagFreeList_of_pairOf_nodup Cnew.mid hnd.1
      have hW'_df : IsDiagFreeSeq (clowInv W) := by
        intro D hD
        rw [hinv_eq] at hD
        simp only [List.mem_append, List.mem_singleton] at hD
        rcases hD with (hp | rfl) | hs
        · exact hW.1 D (by rw [hclows_eq]; simp [hp])
        · exact hC'_df
        · have hs' : D ∈ Cnew :: suff := (insertClow_perm Cnew suff).mem_iff.mp hs
          simp only [List.mem_cons] at hs'
          rcases hs' with rfl | hs''
          · exact hCnew_df
          · exact hW.1 D (by rw [hclows_eq]; simp [hs''])
      have hts' : TailClean (insertClow Cnew suff) := by
        unfold TailClean
        rw [(clowsPairs_perm_of_perm (insertClow_perm Cnew suff)).nodup_iff]
        unfold clowsPairs
        rw [List.flatMap_cons, List.map_append, List.nodup_append]
        refine ⟨hCnew_perm.nodup_iff.mp hcyc_nodup, hts, ?_⟩
        intro p hp q hq heq
        subst heq
        have hp_cyc : p ∈ cyc.map pairOf := hCnew_perm.mem_iff.mpr hp
        rcases List.mem_map.mp hp_cyc with ⟨u, hu, rfl⟩
        have hu_in : u ∈ p1 ++ [v] ++ seg := by
          simp only [cyc, List.mem_append, List.mem_singleton] at hu ⊢; tauto
        exact hclean.2 u hu_in hq
      have hv_in_Cnew : pairOf v ∈ Cnew.verts.map pairOf :=
        hCnew_perm.mem_iff.mp (List.mem_map_of_mem (by simp [cyc]))
      have hv_in_suff' : pairOf v ∈ clowsPairs (insertClow Cnew suff) := by
        rw [(clowsPairs_perm_of_perm (insertClow_perm Cnew suff)).mem_iff]
        unfold clowsPairs
        rw [List.flatMap_cons, List.map_append]
        exact List.mem_append_left _ hv_in_Cnew
      have hnb' : ¬ TailClean (C' :: insertClow Cnew suff) := by
        intro htc
        unfold TailClean clowsPairs at htc
        rw [List.flatMap_cons, List.map_append, List.nodup_append] at htc
        have hv_in_C' : pairOf v ∈ C'.verts.map pairOf :=
          List.mem_map_of_mem (by simp [C', Clow.verts])
        exact htc.2.2 (pairOf v) hv_in_C' (pairOf v) hv_in_suff' rfl
      have hW'_ns : ¬ IsSimpleSeq (clowInv W) := by
        intro hs; apply hnb'
        unfold IsSimpleSeq at hs
        unfold TailClean clowsPairs at hs ⊢
        rw [hinv_eq] at hs
        have h1 : pref ++ [C'] ++ insertClow Cnew suff = pref ++ (C' :: insertClow Cnew suff) := by simp
        rw [h1, List.flatMap_append, List.map_append, List.nodup_append] at hs
        exact hs.2.1
      have hsb' : splitBad (clowInv W).clows = some (pref, C', insertClow Cnew suff) := by
        rw [hinv_eq]; exact splitBad_unique hts' hnb'
      have hclean_p1 : CleanPrefix p1 (clowsPairs (insertClow Cnew suff)) := by
        have hnd_all := hclean.1
        have hperm : ((p1 ++ [v] ++ seg).map pairOf).Perm (p1.map pairOf ++ cyc.map pairOf) := by
          dsimp [cyc]; simp only [List.map_append, List.map_singleton, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        have hnd_sp := List.nodup_append.mp (hperm.nodup_iff.mp hnd_all)
        refine ⟨hnd_sp.1, fun w hw hm => ?_⟩
        rw [(clowsPairs_perm_of_perm (insertClow_perm Cnew suff)).mem_iff] at hm
        unfold clowsPairs at hm
        rw [List.flatMap_cons, List.map_append, List.mem_append] at hm
        rcases hm with hmc | hms
        · exact hnd_sp.2.2 (pairOf w) (List.mem_map_of_mem hw) (pairOf w)
            (hCnew_perm.mem_iff.mpr hmc) rfl
        · exact hclean.2 w (by simp [hw]) hms
      have hsc' : scanMidList (clowsPairs (insertClow Cnew suff)) C'.mid =
          .hitLater p1 v rest :=
        scanMidList_unique_hitLater hclean_p1 hv_in_suff'
      rcases insertClow_split Cnew suff with ⟨s1, s2, hins_eq, hs12⟩
      have hfc' : findClowWithPair (pairOf v) (insertClow Cnew suff) = some (s1, Cnew, s2) := by
        rw [hins_eq]
        exact findClowWithPair_unique (by rwa [← hins_eq]) hv_in_Cnew
      have horient_back : orientTo Cnew.verts v = cyc := by
        rw [hCnew_verts, orientTo_orientTo hcyc_nodup
          (by rw [pairOf_oddV]; exact minPair_mem cyc hcyc_ne)
          (List.mem_map_of_mem (by simp [cyc]))]
        exact orientTo_self hcyc_nodup (by simp [cyc])
      have hinv_inv : clowInv (clowInv W) = W := by
        apply ClowSeq.ext
        rw [clowInv_clows_hitLater (clowInv W) ⟨hW'_df, hW'_ns⟩ hsb' hsc' hfc' (by
              intro w hw; rw [horient_back] at hw
              exact C.mid_gt w (by rw [hmid_eq]; simpa [cyc, List.append_assoc] using hw)),
            hs12, hclows_eq]
        congr 2; congr 1
        apply Clow.ext
        · rfl
        · simp [horient_back, cyc, hmid_eq, List.append_assoc]
      have hne : clowInv W ≠ W := by
        intro heq
        have hlen := congrArg (fun X : ClowSeq k => X.clows.length) heq
        rw [hinv_eq, hclows_eq] at hlen
        simp only [List.length_append, List.length_singleton,
          (insertClow_perm Cnew suff).length_eq, List.length_cons] at hlen
        omega
      have hwt : clowSeqWeight A (clowInv W) = -clowSeqWeight A W := by
        unfold clowSeqWeight
        rw [hinv_eq, hclows_eq]
        simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
          clows_prod_perm A (insertClow_perm Cnew suff), List.map_cons, List.prod_cons,
          List.map_nil, List.prod_nil, mul_one]
        have hcw : clowWeight A C' * clowWeight A Cnew = -clowWeight A C := by
          unfold clowWeight
          rw [← cycWeight_of_inDihedral hA hCnew_hd]
          unfold Clow.verts
          dsimp [C', cyc]
          rw [hmid_eq]
          have hrot_C : IsRot ((p1 ++ [v] ++ seg ++ [v] ++ rest) ++ [oddV C.head])
              ((((rest ++ [oddV C.head]) ++ p1) ++ [v]) ++ (seg ++ [v])) :=
            ⟨p1 ++ [v] ++ seg ++ [v], rest ++ [oddV C.head],
              by simp [List.append_assoc], by simp [List.append_assoc]⟩
          have hrot_C' : IsRot ((p1 ++ [v] ++ rest) ++ [oddV C.head])
              (((rest ++ [oddV C.head]) ++ p1) ++ [v]) :=
            ⟨p1 ++ [v], rest ++ [oddV C.head],
              by simp [List.append_assoc], by simp [List.append_assoc]⟩
          rw [cycWeight_of_isRot A hrot_C, cycWeight_of_isRot A hrot_C', cycWeight_split_same]
          ring
        have hre : (pref.map (clowWeight A)).prod * clowWeight A C' *
            (clowWeight A Cnew * (suff.map (clowWeight A)).prod) =
            (pref.map (clowWeight A)).prod * (clowWeight A C' * clowWeight A Cnew) *
              (suff.map (clowWeight A)).prod := by ring
        rw [hre, hcw]; ring
      exact ⟨⟨hW'_df, hW'_ns⟩, hinv_inv, hne, hwt⟩
    | hitLater seen v rest =>
      -- CASE 3: Hit later clow -> Case 2 (selfSame)
      rw [hsc] at hscan_spec
      rcases hscan_spec with ⟨hmid_eq, hclean, hv_tail⟩
      have hfc_spec := findClowWithPair_spec (pairOf v) suff
      cases hfc : findClowWithPair (pairOf v) suff with
      | none =>
        rw [hfc] at hfc_spec; exact absurd hv_tail hfc_spec
      | some fres =>
        rcases fres with ⟨s1, D, s2⟩
        rw [hfc] at hfc_spec
        rcases hfc_spec with ⟨hsuff_eq, hv_D, _⟩
        have hD_nodup : (D.verts.map pairOf).Nodup := by
          have hts' := hts
          rw [hsuff_eq] at hts'
          unfold TailClean clowsPairs at hts'
          have hsplit : s1 ++ [D] ++ s2 = s1 ++ (D :: s2) := by simp
          rw [hsplit, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
              List.nodup_append] at hts'
          exact (List.nodup_append.mp hts'.2.1).1
        let cyc := orientTo D.verts v
        have hcyc_spec := orientTo_spec D.verts v hv_D
        have hcyc_hd : InDihedral D.verts cyc := hcyc_spec.1
        have hcyc_last : cyc.getLast? = some v := hcyc_spec.2
        have hcyc_perm : (D.verts.map pairOf).Perm (cyc.map pairOf) :=
          inDihedral_perm_pairOf hcyc_hd
        have hcyc_ne : cyc ≠ [] := fun h0 => by rw [h0] at hcyc_last; simp at hcyc_last
        have hcyc_nodup : (cyc.map pairOf).Nodup := hcyc_perm.nodup_iff.mp hD_nodup
        let seg := cyc.dropLast
        have hcyc_eq : seg ++ [v] = cyc := by
          have hgl : cyc.getLast hcyc_ne = v := by
            rw [List.getLast?_eq_some_getLast hcyc_ne] at hcyc_last
            exact Option.some.inj hcyc_last
          simpa [seg, hgl] using List.dropLast_append_getLast hcyc_ne
        have hC'_mid_gt : ∀ w ∈ seen ++ [v] ++ cyc ++ rest, C.head < pairOf w := by
          intro w hw
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with ((hs | rfl) | hcyc) | hr
          · exact C.mid_gt w (by rw [hmid_eq]; simp [hs])
          · exact C.mid_gt w (by rw [hmid_eq]; simp)
          · have hpw : pairOf w ∈ D.verts.map pairOf :=
              hcyc_perm.mem_iff.mpr (List.mem_map_of_mem hcyc)
            rcases List.mem_map.mp hpw with ⟨u, hu, heq⟩
            rw [← heq]
            exact lt_of_lt_of_le (hhead_lt_suff D (by rw [hsuff_eq]; simp))
              (D.head_le_pairOf_verts hu)
          · exact C.mid_gt w (by rw [hmid_eq]; simp [hr])
        let C' : Clow k := ⟨C.head, seen ++ [v] ++ cyc ++ rest, hC'_mid_gt⟩
        have hinv_eq : (clowInv W).clows = pref ++ [C'] ++ (s1 ++ s2) :=
          clowInv_clows_hitLater W hW hsb hsc hfc hC'_mid_gt
        have hC'_df : IsDiagFreeList C'.mid := by
          dsimp [C']
          rw [hmid_eq] at hC_df
          have h1 : seen ++ [v] ++ rest = (seen ++ [v]) ++ rest := by simp [List.append_assoc]
          rw [h1, isDiagFreeList_append_iff] at hC_df
          have hdf_sv : IsDiagFreeList (seen ++ [v]) := hC_df.1
          have hdf_rest : IsDiagFreeList rest := hC_df.2.1
          have hadj_vr : ∀ y, rest.head? = some y → y ≠ mate v := fun y hy =>
            hC_df.2.2 v y (by simp) hy
          have h2 : seen ++ [v] ++ cyc ++ rest = (seen ++ [v]) ++ (cyc ++ rest) := by
            simp [List.append_assoc]
          rw [h2, isDiagFreeList_append_iff]
          refine ⟨hdf_sv, ?_, ?_⟩
          · rw [isDiagFreeList_append_iff]
            refine ⟨isDiagFreeList_of_pairOf_nodup cyc hcyc_nodup, hdf_rest, ?_⟩
            intro x y hx hy
            rw [hcyc_last] at hx
            have hx0 : x = v := Option.some.inj hx.symm
            subst x
            exact hadj_vr y hy
          · intro x y hx hy
            have hx0 : x = v := by
              have : (seen ++ [v]).getLast? = some v := by simp
              rw [this] at hx; exact Option.some.inj hx.symm
            subst x
            rw [List.head?_append_of_ne_nil _ hcyc_ne] at hy
            cases hseg : seg with
            | nil =>
              have hcyc1 : cyc = [v] := by rw [← hcyc_eq, hseg]; rfl
              rw [hcyc1] at hy
              simp only [List.head?_cons, Option.some.injEq] at hy; subst y
              exact (mate_ne_self v).symm
            | cons s0 ss =>
              have hcyc1 : cyc = s0 :: (ss ++ [v]) := by rw [← hcyc_eq, hseg]; rfl
              rw [hcyc1] at hy hcyc_nodup
              simp only [List.head?_cons, Option.some.injEq] at hy; subst y
              intro hsm
              simp only [List.map_cons, List.map_append, List.map_singleton, List.nodup_cons,
                List.mem_append, List.mem_singleton] at hcyc_nodup
              exact hcyc_nodup.1 (Or.inr (by rw [hsm, pairOf_mate]; exact List.mem_singleton_self _))
        have hW'_df : IsDiagFreeSeq (clowInv W) := by
          intro E hE
          rw [hinv_eq] at hE
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with (hp | rfl) | hs
          · exact hW.1 E (by rw [hclows_eq]; simp [hp])
          · exact hC'_df
          · exact hW.1 E (by rw [hclows_eq, hsuff_eq]; simp only [List.mem_append] at hs ⊢; tauto)
        have hts' : TailClean (s1 ++ s2) := by
          have hts0 := hts
          rw [hsuff_eq] at hts0
          have hperm : (s1 ++ [D] ++ s2).Perm (D :: (s1 ++ s2)) := by
            have h1 : s1 ++ [D] ++ s2 = s1 ++ (D :: s2) := by simp
            rw [h1]; exact List.perm_middle
          unfold TailClean at hts0 ⊢
          rw [(clowsPairs_perm_of_perm hperm).nodup_iff] at hts0
          unfold clowsPairs at hts0 ⊢
          rw [List.flatMap_cons, List.map_append, List.nodup_append] at hts0
          exact hts0.2.1
        have hnb' : ¬ TailClean (C' :: (s1 ++ s2)) := by
          intro htc
          unfold TailClean clowsPairs at htc
          rw [List.flatMap_cons, List.map_append, List.nodup_append] at htc
          have hC'nd : (C'.verts.map pairOf).Nodup := htc.1
          unfold Clow.verts at hC'nd
          rw [List.map_append, List.nodup_append] at hC'nd
          have hmid_nd : (C'.mid.map pairOf).Nodup := hC'nd.1
          dsimp [C'] at hmid_nd
          rw [← hcyc_eq] at hmid_nd
          have hsplit : seen ++ [v] ++ (seg ++ [v]) ++ rest =
              (seen ++ [v] ++ seg) ++ ([v] ++ rest) := by simp [List.append_assoc]
          rw [hsplit, List.map_append, List.nodup_append] at hmid_nd
          exact hmid_nd.2.2 (pairOf v) (by simp) (pairOf v) (by simp) rfl
        have hW'_ns : ¬ IsSimpleSeq (clowInv W) := by
          intro hs; apply hnb'
          unfold IsSimpleSeq at hs
          unfold TailClean clowsPairs at hs ⊢
          rw [hinv_eq] at hs
          have h1 : pref ++ [C'] ++ (s1 ++ s2) = pref ++ (C' :: (s1 ++ s2)) := by simp
          rw [h1, List.flatMap_append, List.map_append, List.nodup_append] at hs
          exact hs.2.1
        have hsb' : splitBad (clowInv W).clows = some (pref, C', s1 ++ s2) := by
          rw [hinv_eq]; exact splitBad_unique hts' hnb'
        -- CleanPrefix (seen ++ [v] ++ seg) (clowsPairs (s1 ++ s2))
        have hclean' : CleanPrefix (seen ++ [v] ++ seg) (clowsPairs (s1 ++ s2)) := by
          have hdisj_D_rest : ∀ p ∈ D.verts.map pairOf, p ∉ clowsPairs (s1 ++ s2) := by
            have hts0 := hts
            rw [hsuff_eq] at hts0
            have hperm : (s1 ++ [D] ++ s2).Perm (D :: (s1 ++ s2)) := by
              have h1 : s1 ++ [D] ++ s2 = s1 ++ (D :: s2) := by simp
              rw [h1]; exact List.perm_middle
            unfold TailClean at hts0
            rw [(clowsPairs_perm_of_perm hperm).nodup_iff] at hts0
            unfold clowsPairs at hts0
            rw [List.flatMap_cons, List.map_append, List.nodup_append] at hts0
            intro p hp hm
            exact hts0.2.2 p hp p hm rfl
          have hcyc_disj_seen : ∀ p ∈ seen.map pairOf, p ∉ cyc.map pairOf := by
            intro p hp hm
            rcases List.mem_map.mp hp with ⟨w, hw, rfl⟩
            have hD : pairOf w ∈ D.verts.map pairOf := hcyc_perm.mem_iff.mpr hm
            apply hclean.2 w hw
            rw [hsuff_eq]; unfold clowsPairs
            simp only [List.flatMap_append, List.flatMap_cons, List.map_append, List.mem_append]
            exact Or.inl (Or.inr (Or.inl hD))
          refine ⟨?_, ?_⟩
          · have hperm : ((seen ++ [v] ++ seg).map pairOf).Perm
                (seen.map pairOf ++ cyc.map pairOf) := by
              rw [← hcyc_eq]
              simp only [List.map_append, List.map_singleton, List.append_assoc]
              exact List.Perm.append_left _ List.perm_append_comm
            rw [hperm.nodup_iff, List.nodup_append]
            refine ⟨hclean.1, hcyc_nodup, fun a ha b hb heq => ?_⟩
            subst heq; exact hcyc_disj_seen a ha hb
          · intro w hw hm
            simp only [List.mem_append, List.mem_singleton] at hw
            rcases hw with (hw_s | rfl) | hw_seg
            · apply hclean.2 w hw_s
              rw [hsuff_eq]; unfold clowsPairs at hm ⊢
              simp only [List.flatMap_append, List.flatMap_cons, List.map_append,
                List.mem_append] at hm ⊢
              tauto
            · exact hdisj_D_rest (pairOf w) hv_D hm
            · have hpw : pairOf w ∈ D.verts.map pairOf :=
                hcyc_perm.mem_iff.mpr (List.mem_map_of_mem (by rw [← hcyc_eq]; simp [hw_seg]))
              exact hdisj_D_rest (pairOf w) hpw hm
        have hC'_mid_eq : C'.mid = seen ++ [v] ++ seg ++ [v] ++ rest := by
          dsimp [C']; rw [← hcyc_eq]; simp [List.append_assoc]
        have hsc' : scanMidList (clowsPairs (s1 ++ s2)) C'.mid =
            .selfSame seen seg v rest := by
          rw [hC'_mid_eq]; exact scanMidList_unique_selfSame hclean'
        have hmk_back : mkClowFromCycle (seg ++ [v]) (by simp) (by rwa [hcyc_eq]) = D := by
          have hmin : minPair (seg ++ [v]) (by simp) = minPair D.verts D.verts_ne_nil := by
            apply minPair_eq_of_perm
            rw [hcyc_eq]; exact hcyc_perm.symm
          have hminD : minPair D.verts D.verts_ne_nil = D.head := by
            apply le_antisymm
            · have := minPair_le D.verts D.verts_ne_nil (v := oddV D.head) (by simp [Clow.verts])
              simpa using this
            · rcases List.mem_map.mp (minPair_mem D.verts D.verts_ne_nil) with ⟨u, hu, heq⟩
              rw [← heq]; exact D.head_le_pairOf_verts hu
          have hverts_eq : (mkClowFromCycle (seg ++ [v]) (by simp) (by rwa [hcyc_eq])).verts =
              D.verts := by
            rw [mkClowFromCycle_verts, hmin, hminD]
            simp only [hcyc_eq, cyc]
            have hoddD : pairOf (oddV D.head) ∈ D.verts.map pairOf :=
              List.mem_map_of_mem (by simp [Clow.verts])
            rw [orientTo_orientTo hD_nodup hv_D hoddD]
            exact orientTo_self hD_nodup D.verts_getLast?
          apply Clow.ext
          · change minPair (seg ++ [v]) (by simp) = D.head
            rw [hmin, hminD]
          · have := congrArg List.dropLast hverts_eq
            simpa [Clow.verts] using this
        have hins_back : insertClow D (s1 ++ s2) = suff := by
          rw [hsuff_eq]
          have hpw_suff : ((s1 ++ [D] ++ s2).map Clow.head).Pairwise (· < ·) := by
            rw [← hsuff_eq]
            rw [List.map_append, List.pairwise_append] at hpw_all
            exact hpw_all.2.1
          exact insertClow_eq_of_sorted hpw_suff
        have hinv_inv : clowInv (clowInv W) = W := by
          apply ClowSeq.ext
          rw [clowInv_clows_selfSame (clowInv W) ⟨hW'_df, hW'_ns⟩ hsb' hsc'
                (by intro w hw; exact C.mid_gt w (by rw [hmid_eq]; exact hw))
                (by rwa [hcyc_eq]),
              hmk_back, hins_back, hclows_eq]
          congr 2; congr 1
          apply Clow.ext
          · rfl
          · exact hmid_eq.symm
        have hne : clowInv W ≠ W := by
          intro heq
          have hlen := congrArg (fun X : ClowSeq k => X.clows.length) heq
          rw [hinv_eq, hclows_eq, hsuff_eq] at hlen
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        have hwt : clowSeqWeight A (clowInv W) = -clowSeqWeight A W := by
          unfold clowSeqWeight
          rw [hinv_eq, hclows_eq, hsuff_eq]
          simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
          suffices hcw : clowWeight A C' = -(clowWeight A C * clowWeight A D) by
            rw [hcw]; ring
          unfold clowWeight
          rw [cycWeight_of_inDihedral hA hcyc_hd]
          unfold Clow.verts
          dsimp [C']
          rw [hmid_eq, ← hcyc_eq]
          have hrot_C' : IsRot ((seen ++ [v] ++ (seg ++ [v]) ++ rest) ++ [oddV C.head])
              ((((rest ++ [oddV C.head]) ++ seen) ++ [v]) ++ (seg ++ [v])) :=
            ⟨seen ++ [v] ++ (seg ++ [v]), rest ++ [oddV C.head],
              by simp [List.append_assoc], by simp [List.append_assoc]⟩
          have hrot_C : IsRot ((seen ++ [v] ++ rest) ++ [oddV C.head])
              (((rest ++ [oddV C.head]) ++ seen) ++ [v]) :=
            ⟨seen ++ [v], rest ++ [oddV C.head],
              by simp [List.append_assoc], by simp [List.append_assoc]⟩
          rw [cycWeight_of_isRot A hrot_C', cycWeight_of_isRot A hrot_C, cycWeight_split_same]
          ring
        exact ⟨⟨hW'_df, hW'_ns⟩, hinv_inv, hne, hwt⟩

/-- Sum of `clowSeqWeight A W` over all non-simple `W : ClowSeq k` is `0`. -/
theorem sum_not_simple_eq_zero {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A) :
    ∑ W ∈ Finset.univ.filter (fun W : ClowSeq k => ¬ IsSimpleSeq W), clowSeqWeight A W = 0 := by
  have hsplit :
      Finset.univ.filter (fun W : ClowSeq k => ¬ IsSimpleSeq W) =
      Finset.univ.filter (fun W : ClowSeq k => IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W) ∪
      Finset.univ.filter (fun W : ClowSeq k => ¬ IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W) := by
    ext W; simp; tauto
  have hdisj : Disjoint
      (Finset.univ.filter (fun W : ClowSeq k => IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W))
      (Finset.univ.filter (fun W : ClowSeq k => ¬ IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W)) := by
    rw [Finset.disjoint_filter]
    intro W _ h1 h2; exact h2.1 h1.1
  rw [hsplit, Finset.sum_union hdisj]
  have hzero2 : ∑ W ∈ Finset.univ.filter (fun W : ClowSeq k => ¬ IsDiagFreeSeq W ∧ ¬ IsSimpleSeq W),
      clowSeqWeight A W = 0 :=
    Finset.sum_eq_zero fun W hW =>
      clowSeqWeight_eq_zero_of_not_diagFree hA W (Finset.mem_filter.mp hW).2.1
  rw [hzero2, add_zero]
  refine Finset.sum_involution (fun W _ => clowInv W) ?_ ?_ ?_ ?_
  · intro W hW
    have hprop := clowInv_properties hA W (Finset.mem_filter.mp hW).2
    rw [hprop.2.2.2]; exact add_neg_cancel _
  · intro W hW _
    have hprop := clowInv_properties hA W (Finset.mem_filter.mp hW).2
    exact hprop.2.2.1
  · intro W hW
    have hprop := clowInv_properties hA W (Finset.mem_filter.mp hW).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprop.1⟩
  · intro W hW
    have hprop := clowInv_properties hA W (Finset.mem_filter.mp hW).2
    exact hprop.2.1

/-! ### 5. Bijection between Simple Clow Sequences and `OrderedPairing k` + Sign Identity -/

/-- Lift a permutation `τ : Equiv.Perm (Fin k)` to `Equiv.Perm (Fin (2 * k))` acting on pairs. -/
def liftPairPerm {k : ℕ} (τ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (2 * k)) where
  toFun x := if x.val % 2 = 0 then evenV (τ (pairOf x)) else oddV (τ (pairOf x))
  invFun x := if x.val % 2 = 0 then evenV (τ.symm (pairOf x)) else oddV (τ.symm (pairOf x))
  left_inv x := by
    by_cases h : x.val % 2 = 0
    · simp only [h, ↓reduceIte]
      have hev : (evenV (τ (pairOf x))).val % 2 = 0 := by dsimp [evenV]; omega
      simp only [hev, ↓reduceIte, pairOf_evenV, Equiv.symm_apply_apply]
      ext; dsimp [evenV, pairOf]; omega
    · simp only [h, ↓reduceIte]
      have hod : ¬ ((oddV (τ (pairOf x))).val % 2 = 0) := by dsimp [oddV]; omega
      simp only [hod, ↓reduceIte, pairOf_oddV, Equiv.symm_apply_apply]
      ext; dsimp [oddV, pairOf]; omega
  right_inv x := by
    by_cases h : x.val % 2 = 0
    · simp only [h, ↓reduceIte]
      have hev : (evenV (τ.symm (pairOf x))).val % 2 = 0 := by dsimp [evenV]; omega
      simp only [hev, ↓reduceIte, pairOf_evenV, Equiv.apply_symm_apply]
      ext; dsimp [evenV, pairOf]; omega
    · simp only [h, ↓reduceIte]
      have hod : ¬ ((oddV (τ.symm (pairOf x))).val % 2 = 0) := by dsimp [oddV]; omega
      simp only [hod, ↓reduceIte, pairOf_oddV, Equiv.apply_symm_apply]
      ext; dsimp [oddV, pairOf]; omega

@[simp] lemma liftPairPerm_evenV {k : ℕ} (τ : Equiv.Perm (Fin k)) (i : Fin k) :
    liftPairPerm τ (evenV i) = evenV (τ i) := by
  dsimp [liftPairPerm]
  have h : (evenV i).val % 2 = 0 := by dsimp [evenV]; omega
  simp [h]

@[simp] lemma liftPairPerm_oddV {k : ℕ} (τ : Equiv.Perm (Fin k)) (i : Fin k) :
    liftPairPerm τ (oddV i) = oddV (τ i) := by
  dsimp [liftPairPerm]
  have h : ¬ ((oddV i).val % 2 = 0) := by dsimp [oddV]; omega
  simp [h]

lemma liftPairPerm_mul {k : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin k)) :
    liftPairPerm (τ₁ * τ₂) = liftPairPerm τ₁ * liftPairPerm τ₂ := by
  ext x
  rcases eq_evenV_or_oddV x with h | h <;> rw [h] <;> simp [Equiv.Perm.mul_apply]

lemma liftPairPerm_one {k : ℕ} : liftPairPerm (1 : Equiv.Perm (Fin k)) = 1 := by
  ext x
  rcases eq_evenV_or_oddV x with h | h <;> rw [h] <;> simp

lemma liftPairPerm_swap {k : ℕ} (a b : Fin k) :
    liftPairPerm (Equiv.swap a b) =
      Equiv.swap (evenV a) (evenV b) * Equiv.swap (oddV a) (oddV b) := by
  ext x
  rcases eq_evenV_or_oddV x with h | h
  · rw [h, liftPairPerm_evenV, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (evenV_ne_oddV_any _ _) (evenV_ne_oddV_any _ _)]
    by_cases ha : pairOf x = a
    · rw [ha, Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hb : pairOf x = b
      · rw [hb, Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb,
            Equiv.swap_apply_of_ne_of_ne (fun he => ha (evenV_injective he))
              (fun he => hb (evenV_injective he))]
  · rw [h, liftPairPerm_oddV, Equiv.Perm.mul_apply]
    by_cases ha : pairOf x = a
    · rw [ha, Equiv.swap_apply_left, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (evenV_ne_oddV_any _ _).symm (evenV_ne_oddV_any _ _).symm]
    · by_cases hb : pairOf x = b
      · rw [hb, Equiv.swap_apply_right, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne (evenV_ne_oddV_any _ _).symm (evenV_ne_oddV_any _ _).symm]
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb,
            Equiv.swap_apply_of_ne_of_ne (fun he => ha (oddV_injective he))
              (fun he => hb (oddV_injective he)),
            Equiv.swap_apply_of_ne_of_ne (evenV_ne_oddV_any _ _).symm (evenV_ne_oddV_any _ _).symm]

/-- Every pair-preserving permutation `liftPairPerm τ` is even (`sign = 1`). -/
lemma sign_liftPairPerm {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (liftPairPerm τ) = 1 := by
  induction τ using Equiv.Perm.swap_induction_on with
  | one => rw [liftPairPerm_one, map_one]
  | swap_mul f a b hab ih =>
    rw [liftPairPerm_mul, map_mul, ih, mul_one, liftPairPerm_swap, map_mul,
        Equiv.Perm.sign_swap (fun h => hab (evenV_injective h)),
        Equiv.Perm.sign_swap (fun h => hab (oddV_injective h))]
    rfl

/-- Flip pairs `(evenV i, oddV i)` for all `i ∈ S`. -/
def flipPairs {k : ℕ} (S : Finset (Fin k)) : Equiv.Perm (Fin (2 * k)) where
  toFun x := if pairOf x ∈ S then mate x else x
  invFun x := if pairOf x ∈ S then mate x else x
  left_inv x := by
    by_cases h : pairOf x ∈ S <;> simp [h]
  right_inv x := by
    by_cases h : pairOf x ∈ S <;> simp [h]

lemma flipPairs_empty {k : ℕ} : flipPairs (∅ : Finset (Fin k)) = 1 := by
  ext x; simp [flipPairs]

lemma flipPairs_insert {k : ℕ} {a : Fin k} {S : Finset (Fin k)} (ha : a ∉ S) :
    flipPairs (insert a S) = Equiv.swap (evenV a) (oddV a) * flipPairs S := by
  ext x
  simp only [flipPairs, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, Finset.mem_insert]
  by_cases hxa : pairOf x = a
  · have hnot : pairOf x ∉ S := by rwa [hxa]
    simp only [hxa, true_or, ↓reduceIte, hnot]
    rcases eq_evenV_or_oddV x with hx | hx
    · rw [hx, hxa]; simp [ha]
    · rw [hx, hxa]; simp [ha]
  · simp only [hxa, false_or]
    split_ifs with hS
    · have hne1 : mate x ≠ evenV a := fun h => hxa (by rw [← pairOf_mate x, h, pairOf_evenV])
      have hne2 : mate x ≠ oddV a := fun h => hxa (by rw [← pairOf_mate x, h, pairOf_oddV])
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    · have hne1 : x ≠ evenV a := fun h => hxa (by rw [h, pairOf_evenV])
      have hne2 : x ≠ oddV a := fun h => hxa (by rw [h, pairOf_oddV])
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

lemma sign_flipPairs {k : ℕ} (S : Finset (Fin k)) :
    Equiv.Perm.sign (flipPairs S) = (-1 : ℤˣ) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [flipPairs_empty]
  | insert a S ha ih =>
    rw [flipPairs_insert ha, map_mul, Equiv.Perm.sign_swap (evenV_ne_oddV a), ih,
        Finset.card_insert_of_notMem ha, pow_succ']

/-- Pfaffian term invariance: any permutation `π` whose pairs `{π(2i), π(2i+1)}` are the edges
of `m : OrderedPairing k` gives the exact same signed product as `m`. -/
lemma perm_pfaffian_term_eq {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A)
    (m : OrderedPairing k) (π : Equiv.Perm (Fin (2 * k)))
    (hpair : ∀ i : Fin k, s(π (evenV i), π (oddV i)) ∈ m.edgeFinset) :
    (Equiv.Perm.sign π : R) * ∏ i : Fin k, A (π (evenV i)) (π (oddV i)) =
      (m.sign : R) * ∏ i : Fin k, A (m.fst i) (m.snd i) := by
  classical
  let S : Finset (Fin k) := Finset.univ.filter (fun i => π (oddV i) < π (evenV i))
  let π₁ : Equiv.Perm (Fin (2 * k)) := π * flipPairs S
  have hlt : ∀ i : Fin k, π₁ (evenV i) < π₁ (oddV i) := by
    intro i
    have hne : π (evenV i) ≠ π (oddV i) := fun h => evenV_ne_oddV i (π.injective h)
    dsimp [π₁, flipPairs]
    by_cases hi : i ∈ S
    · have hgt : π (oddV i) < π (evenV i) := (Finset.mem_filter.mp hi).2
      simpa [hi] using hgt
    · have hle : π (evenV i) ≤ π (oddV i) := not_lt.mp (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      simpa [hi] using lt_of_le_of_ne hle hne
  have hprod_flip :
      (Equiv.Perm.sign (flipPairs S) : R) * ∏ i : Fin k, A (π₁ (evenV i)) (π₁ (oddV i)) =
        ∏ i : Fin k, A (π (evenV i)) (π (oddV i)) := by
    have hsign : ((Equiv.Perm.sign (flipPairs S) : ℤ) : R) =
        ∏ i : Fin k, if i ∈ S then (-1 : R) else 1 := by
      rw [sign_flipPairs]
      simp [Finset.prod_ite, Finset.filter_mem_eq_inter]
    rw [hsign, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp [π₁, flipPairs]
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte, pairOf_evenV, mate_evenV, pairOf_oddV, mate_oddV]
      rw [hA.2]
      ring
    · simp [hi]
  have hmatch : ∀ i : Fin k, ∃ j : Fin k, π₁ (evenV i) = m.fst j ∧ π₁ (oddV i) = m.snd j := by
    intro i
    have hmem : s(π₁ (evenV i), π₁ (oddV i)) ∈ m.edgeFinset := by
      have h1 := hpair i
      dsimp [π₁, flipPairs]
      by_cases hi : i ∈ S
      · simpa [hi, Sym2.eq_swap] using h1
      · simpa [hi] using h1
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    rcases Sym2.eq_iff.mp hj.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨j, h1, h2⟩
    · exfalso
      have hlt1 := hlt i
      have hlt2 := m.fst_lt_snd j
      rw [h1, h2] at hlt1
      exact lt_asymm hlt1 hlt2
  let f : Fin k → Fin k := fun i => Classical.choose (hmatch i)
  have hf_spec : ∀ i, π₁ (evenV i) = m.fst (f i) ∧ π₁ (oddV i) = m.snd (f i) :=
    fun i => Classical.choose_spec (hmatch i)
  have hf_inj : Function.Injective f := by
    intro i₁ i₂ heq
    have h1 : π₁ (evenV i₁) = π₁ (evenV i₂) := by
      rw [(hf_spec i₁).1, (hf_spec i₂).1, heq]
    exact evenV_injective (π₁.injective h1)
  let τ : Equiv.Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hπ₁_eq : π₁ = m.perm * liftPairPerm τ := by
    refine Equiv.ext fun x => ?_
    rcases eq_evenV_or_oddV x with hx | hx
    · rw [hx]
      conv_rhs => rw [Equiv.Perm.mul_apply, liftPairPerm_evenV]
      exact (hf_spec (pairOf x)).1
    · rw [hx]
      conv_rhs => rw [Equiv.Perm.mul_apply, liftPairPerm_oddV]
      exact (hf_spec (pairOf x)).2
  have hsign_π₁ : Equiv.Perm.sign π₁ = Equiv.Perm.sign m.perm := by
    rw [hπ₁_eq, map_mul, sign_liftPairPerm, mul_one]
  have hsign_π : Equiv.Perm.sign π = Equiv.Perm.sign m.perm * Equiv.Perm.sign (flipPairs S) := by
    have : π = π₁ * (flipPairs S)⁻¹ := by simp [π₁]
    rw [this, map_mul, hsign_π₁, map_inv]
    -- sign is in ℤˣ, so u⁻¹ = u
    have hinv : (Equiv.Perm.sign (flipPairs S))⁻¹ = Equiv.Perm.sign (flipPairs S) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (flipPairs S)) with h | h <;> rw [h] <;> rfl
    rw [hinv]
  have hsign_sq : ((Equiv.Perm.sign (flipPairs S) : ℤ) : R) *
      ((Equiv.Perm.sign (flipPairs S) : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (flipPairs S)) with h | h <;> rw [h] <;> norm_num
  have hprod_m : ∏ i : Fin k, A (π₁ (evenV i)) (π₁ (oddV i)) =
      ∏ j : Fin k, A (m.fst j) (m.snd j) := by
    refine Fintype.prod_equiv τ _ _ fun i => ?_
    change A (π₁ (evenV i)) (π₁ (oddV i)) = A (m.fst (f i)) (m.snd (f i))
    rw [(hf_spec i).1, (hf_spec i).2]
  calc
    ((Equiv.Perm.sign π : ℤ) : R) * ∏ i : Fin k, A (π (evenV i)) (π (oddV i))
        = ((Equiv.Perm.sign m.perm : ℤ) : R) * ((Equiv.Perm.sign (flipPairs S) : ℤ) : R) *
            (((Equiv.Perm.sign (flipPairs S) : ℤ) : R) *
              ∏ i : Fin k, A (π₁ (evenV i)) (π₁ (oddV i))) := by
          rw [hsign_π, ← hprod_flip]; push_cast; rfl
    _ = ((Equiv.Perm.sign m.perm : ℤ) : R) *
          (((Equiv.Perm.sign (flipPairs S) : ℤ) : R) *
            ((Equiv.Perm.sign (flipPairs S) : ℤ) : R)) *
          ∏ i : Fin k, A (π₁ (evenV i)) (π₁ (oddV i)) := by ring
    _ = (m.sign : R) * ∏ j : Fin k, A (m.fst j) (m.snd j) := by
          rw [hsign_sq, mul_one, hprod_m]; rfl

/-- Cyclic shift on the `L` even indices `evenV a, ..., evenV (a + L - 1)` sending
`evenV a ↦ evenV (a + L - 1)` and `evenV (a + r + 1) ↦ evenV (a + r)` (`L ≥ 1`). -/
def shiftBlock {k : ℕ} (a L : ℕ) (hL : 1 ≤ L) (hbound : a + L ≤ k) : Equiv.Perm (Fin (2 * k)) where
  toFun x :=
    if h : x.val % 2 = 0 ∧ a ≤ x.val / 2 ∧ x.val / 2 < a + L then
      evenV ⟨if x.val / 2 = a then a + L - 1 else x.val / 2 - 1, by split_ifs <;> omega⟩
    else x
  invFun x :=
    if h : x.val % 2 = 0 ∧ a ≤ x.val / 2 ∧ x.val / 2 < a + L then
      evenV ⟨if x.val / 2 = a + L - 1 then a else x.val / 2 + 1, by split_ifs <;> omega⟩
    else x
  left_inv x := by
    by_cases h : x.val % 2 = 0 ∧ a ≤ x.val / 2 ∧ x.val / 2 < a + L
    · rcases h with ⟨heven, hlo, hhi⟩
      simp only [heven, hlo, hhi, and_self, ↓reduceDIte]
      by_cases h1 : x.val / 2 = a
      · simp only [h1, ↓reduceIte]
        have hin : (evenV ⟨a + L - 1, by omega⟩ : Fin (2 * k)).val % 2 = 0 ∧
            a ≤ (evenV ⟨a + L - 1, by omega⟩ : Fin (2 * k)).val / 2 ∧
            (evenV ⟨a + L - 1, by omega⟩ : Fin (2 * k)).val / 2 < a + L := by
          dsimp [evenV]; omega
        rw [dif_pos hin]
        ext; dsimp [evenV]
        have h2 : 2 * (a + L - 1) / 2 = a + L - 1 := by omega
        simp [h2]; omega
      · simp only [h1, ↓reduceIte]
        have hin : (evenV ⟨x.val / 2 - 1, by omega⟩ : Fin (2 * k)).val % 2 = 0 ∧
            a ≤ (evenV ⟨x.val / 2 - 1, by omega⟩ : Fin (2 * k)).val / 2 ∧
            (evenV ⟨x.val / 2 - 1, by omega⟩ : Fin (2 * k)).val / 2 < a + L := by
          dsimp [evenV]; omega
        rw [dif_pos hin]
        apply Fin.ext; dsimp only [evenV]
        have hdiv : 2 * (x.val / 2 - 1) / 2 = x.val / 2 - 1 := by omega
        simp only [hdiv]
        split_ifs <;> omega
    · simp [h]
  right_inv x := by
    by_cases h : x.val % 2 = 0 ∧ a ≤ x.val / 2 ∧ x.val / 2 < a + L
    · rcases h with ⟨heven, hlo, hhi⟩
      simp only [heven, hlo, hhi, and_self, ↓reduceDIte]
      by_cases h1 : x.val / 2 = a + L - 1
      · simp only [h1, ↓reduceIte]
        have hin : (evenV ⟨a, by omega⟩ : Fin (2 * k)).val % 2 = 0 ∧
            a ≤ (evenV ⟨a, by omega⟩ : Fin (2 * k)).val / 2 ∧
            (evenV ⟨a, by omega⟩ : Fin (2 * k)).val / 2 < a + L := by
          dsimp [evenV]; omega
        rw [dif_pos hin]
        apply Fin.ext; dsimp only [evenV]
        have hdiv : 2 * a / 2 = a := by omega
        simp only [hdiv]
        split_ifs <;> omega
      · simp only [h1, ↓reduceIte]
        have hin : (evenV ⟨x.val / 2 + 1, by omega⟩ : Fin (2 * k)).val % 2 = 0 ∧
            a ≤ (evenV ⟨x.val / 2 + 1, by omega⟩ : Fin (2 * k)).val / 2 ∧
            (evenV ⟨x.val / 2 + 1, by omega⟩ : Fin (2 * k)).val / 2 < a + L := by
          dsimp [evenV]; omega
        rw [dif_pos hin]
        apply Fin.ext; dsimp only [evenV]
        have hdiv : 2 * (x.val / 2 + 1) / 2 = x.val / 2 + 1 := by omega
        simp only [hdiv]
        split_ifs <;> omega
    · simp [h]

lemma shiftBlock_oddV {k : ℕ} (a L : ℕ) (hL : 1 ≤ L) (hbound : a + L ≤ k) (i : Fin k) :
    shiftBlock a L hL hbound (oddV i) = oddV i := by
  simp only [shiftBlock, Equiv.coe_fn_mk]
  rw [dif_neg]
  intro h; dsimp [oddV] at h; omega

lemma shiftBlock_evenV_outside {k : ℕ} (a L : ℕ) (hL : 1 ≤ L) (hbound : a + L ≤ k)
    (i : Fin k) (hout : i.val < a ∨ a + L ≤ i.val) :
    shiftBlock a L hL hbound (evenV i) = evenV i := by
  simp only [shiftBlock, Equiv.coe_fn_mk]
  rw [dif_neg]
  intro h; dsimp [evenV] at h; omega

lemma shiftBlock_evenV_inside {k : ℕ} (a L : ℕ) (hL : 1 ≤ L) (hbound : a + L ≤ k)
    (r : ℕ) (hr : r < L) :
    shiftBlock a L hL hbound (evenV ⟨a + r, by omega⟩) =
      evenV ⟨if r = 0 then a + L - 1 else a + r - 1, by split_ifs <;> omega⟩ := by
  simp only [shiftBlock, Equiv.coe_fn_mk]
  have hin : (evenV ⟨a + r, by omega⟩ : Fin (2 * k)).val % 2 = 0 ∧
      a ≤ (evenV ⟨a + r, by omega⟩ : Fin (2 * k)).val / 2 ∧
      (evenV ⟨a + r, by omega⟩ : Fin (2 * k)).val / 2 < a + L := by
    dsimp [evenV]; omega
  rw [dif_pos hin]
  apply Fin.ext
  dsimp only [evenV]
  have hdiv : 2 * (a + r) / 2 = a + r := by omega
  simp only [hdiv]
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hne : a + r ≠ a := by omega
    simp [hr0, hne]

lemma sign_shiftBlock {k : ℕ} (a L : ℕ) (hL : 1 ≤ L) (hbound : a + L ≤ k) :
    Equiv.Perm.sign (shiftBlock a L hL hbound) = (-1 : ℤˣ) ^ (L - 1) := by
  induction L with
  | zero => omega
  | succ L' ih =>
    by_cases hL' : L' = 0
    · subst hL'
      have h1 : shiftBlock a 1 hL hbound = 1 := by
        ext x; dsimp [shiftBlock]
        split_ifs with h <;> dsimp [evenV] at * <;> omega
      rw [h1, map_one]; rfl
    · have hge : 1 ≤ L' := Nat.pos_of_ne_zero hL'
      have hstep : shiftBlock a (L' + 1) hL hbound =
          Equiv.swap (evenV ⟨a + L' - 1, by omega⟩) (evenV ⟨a + L', by omega⟩) *
            shiftBlock a L' hge (by omega) := by
        ext x
        rcases eq_evenV_or_oddV x with hx | hx
        · rw [hx, Equiv.Perm.mul_apply]
          set i := pairOf x
          by_cases hlow : i.val < a
          · rw [shiftBlock_evenV_outside _ _ _ _ i (Or.inl hlow),
                shiftBlock_evenV_outside _ _ _ _ i (Or.inl hlow),
                Equiv.swap_apply_of_ne_of_ne]
            · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
            · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
          · by_cases hhi : a + L' + 1 ≤ i.val
            · rw [shiftBlock_evenV_outside _ _ _ _ i (Or.inr (by omega)),
                  shiftBlock_evenV_outside _ _ _ _ i (Or.inr (by omega)),
                  Equiv.swap_apply_of_ne_of_ne]
              · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
              · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
            · by_cases htop : i.val = a + L'
              · have hi_eq : i = ⟨a + L', by omega⟩ := Fin.ext htop
                rw [hi_eq, shiftBlock_evenV_inside a (L' + 1) hL hbound L' (by omega),
                    shiftBlock_evenV_outside a L' hge (by omega) ⟨a + L', by omega⟩ (Or.inr (by omega)),
                    Equiv.swap_apply_right]
                simp [hL']
              · set r := i.val - a
                have hi_eq : i = ⟨a + r, by dsimp [r]; omega⟩ := Fin.ext (by dsimp [r]; omega)
                rw [hi_eq, shiftBlock_evenV_inside a (L' + 1) hL hbound r (by dsimp [r]; omega),
                    shiftBlock_evenV_inside a L' hge (by omega) r (by dsimp [r]; omega)]
                by_cases hr0 : r = 0
                · simp only [hr0, ↓reduceIte]
                  rw [Equiv.swap_apply_left]
                  congr 1
                · simp only [hr0, ↓reduceIte]
                  rw [Equiv.swap_apply_of_ne_of_ne]
                  · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
                  · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega
        · rw [hx, Equiv.Perm.mul_apply, shiftBlock_oddV, shiftBlock_oddV,
              Equiv.swap_apply_of_ne_of_ne (evenV_ne_oddV_any _ _).symm (evenV_ne_oddV_any _ _).symm]
      rw [hstep, map_mul, Equiv.Perm.sign_swap, ih hge (by omega)]
      · have : L' + 1 - 1 = (L' - 1) + 1 := by omega
        rw [this, pow_succ']
      · intro he; have := congrArg Fin.val he; dsimp [evenV] at this; omega

/-- Product of `shiftBlock` over a list of clows starting at offset `a`. -/
def shiftClows {k : ℕ} : (a : ℕ) → (cs : List (Clow k)) →
    a + (cs.map Clow.len).sum ≤ k → Equiv.Perm (Fin (2 * k))
  | _, [], _ => 1
  | a, C :: cs, h =>
    have hL : 1 ≤ C.len := by unfold Clow.len; omega
    have h1 : a + C.len ≤ k := by simp at h; omega
    have h2 : (a + C.len) + (cs.map Clow.len).sum ≤ k := by simp at h; omega
    shiftBlock a C.len hL h1 * shiftClows (a + C.len) cs h2

lemma shiftClows_oddV {k : ℕ} (a : ℕ) (cs : List (Clow k)) (h : a + (cs.map Clow.len).sum ≤ k)
    (i : Fin k) : shiftClows a cs h (oddV i) = oddV i := by
  induction cs generalizing a with
  | nil => rfl
  | cons C cs ih =>
    simp only [shiftClows, Equiv.Perm.mul_apply, ih, shiftBlock_oddV]

lemma shiftClows_evenV_outside {k : ℕ} (a : ℕ) (cs : List (Clow k))
    (h : a + (cs.map Clow.len).sum ≤ k) (i : Fin k)
    (hout : i.val < a ∨ a + (cs.map Clow.len).sum ≤ i.val) :
    shiftClows a cs h (evenV i) = evenV i := by
  induction cs generalizing a with
  | nil => rfl
  | cons C cs ih =>
    simp only [shiftClows, Equiv.Perm.mul_apply]
    have hcs : i.val < a + C.len ∨ a + C.len + (cs.map Clow.len).sum ≤ i.val := by
      simp only [List.map_cons, List.sum_cons] at hout; omega
    have h1 : shiftClows (a + C.len) cs (by simp at h; omega) (evenV i) = evenV i := ih _ _ hcs
    rw [h1]
    have hblk : i.val < a ∨ a + C.len ≤ i.val := by
      simp only [List.map_cons, List.sum_cons] at hout; omega
    exact shiftBlock_evenV_outside _ _ _ _ i hblk

lemma sign_shiftClows {k : ℕ} (a : ℕ) (cs : List (Clow k)) (h : a + (cs.map Clow.len).sum ≤ k) :
    ((Equiv.Perm.sign (shiftClows a cs h) : ℤ) : ℤ) =
      (cs.map (fun C => (-1 : ℤ) ^ (C.len - 1))).prod := by
  induction cs generalizing a with
  | nil => simp [shiftClows]
  | cons C cs ih =>
    simp only [shiftClows, map_mul, Units.val_mul, sign_shiftBlock, ih, List.map_cons,
      List.prod_cons]
    simp

/-- Helper: product of `A (mate prev) w * jSign w` along a clow block equals `cycWeight`. -/
lemma pathWeight_eq_fin_prod {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (ws : List (Fin (2 * k))) (u : Fin (2 * k)) :
    pathWeight A u ws =
      ∏ r : Fin ws.length,
        A (if hr : r.val = 0 then u else mate (ws[r.val - 1]'(by omega))) ws[r.val] *
          (jSign ws[r.val] : R) := by
  induction ws generalizing u with
  | nil => simp [pathWeight]
  | cons w ws ih =>
    rw [pathWeight_cons, ih (mate w)]
    simp only [List.length_cons]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, ↓reduceDIte, List.getElem_cons_zero]
    congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    rcases r with ⟨rv, hrv⟩
    simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
      List.getElem_cons_succ]
    cases rv with
    | zero => simp
    | succ m => simp

lemma cycWeight_eq_fin_prod {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (C : Clow k) :
    cycWeight A C.verts =
      ∏ r : Fin C.len,
        A (mate (C.verts[if r.val = 0 then C.len - 1 else r.val - 1]'(by
            rw [C.verts_length]; unfold Clow.len; split_ifs <;> omega)))
          (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt)) *
          (jSign (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt)) : R) := by
  unfold cycWeight
  rw [C.verts_getLast?]; dsimp only; rw [pathWeight_eq_fin_prod]
  let e : Fin C.verts.length ≃ Fin C.len := finCongr C.verts_length
  rw [← Fintype.prod_equiv e]
  intro r
  have hev : (e r).val = r.val := rfl
  by_cases hr : r.val = 0
  · simp only [hev, hr, ↓reduceDIte, ↓reduceIte]
    have hlast : C.verts[C.len - 1]'(by rw [C.verts_length]; unfold Clow.len; omega) = oddV C.head := by
      unfold Clow.verts Clow.len
      simp
    rw [hlast]
  · simp only [hev, hr, ↓reduceDIte, ↓reduceIte]

/-- Construct the explicit permutation `clowPerm W hSimple : Equiv.Perm (Fin (2 * k))`
whose `k` pairs `(π(2t), π(2t+1))` are the `k` edges of `W`. -/
noncomputable def clowPerm {k : ℕ} (W : ClowSeq k) (hSimple : IsSimpleSeq W) :
    Equiv.Perm (Fin (2 * k)) :=
  let verts := W.clows.flatMap Clow.verts
  have hlen : verts.length = k := by
    have : (clowsToSteps W.clows).length = verts.length := by
      unfold clowsToSteps verts
      clear hSimple
      induction W.clows with
      | nil => rfl
      | cons C cs ih => simp [List.flatMap_cons, ih]
    rw [← this, clowsToSteps_length, W.total_len]
  let ws : Fin k → Fin (2 * k) := fun t => verts[t.val]'(by rw [hlen]; exact t.isLt)
  have hpair_inj : Function.Injective (fun t : Fin k => pairOf (ws t)) := by
    intro t₁ t₂ heq
    have hnd : (verts.map pairOf).Nodup := hSimple
    have h1 : (verts.map pairOf)[t₁.val]'(by simp [hlen]) =
        (verts.map pairOf)[t₂.val]'(by simp [hlen]) := by
      simpa [ws] using heq
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  let τ : Equiv.Perm (Fin k) :=
    Equiv.ofBijective (fun t => pairOf (ws t)) (Finite.injective_iff_bijective.mp hpair_inj)
  let S : Finset (Fin k) := Finset.univ.filter (fun t => (ws t).val % 2 = 0)
  let σ : Equiv.Perm (Fin (2 * k)) := liftPairPerm τ * flipPairs S
  let shiftAll : Equiv.Perm (Fin (2 * k)) :=
    shiftClows 0 W.clows (by rw [zero_add, W.total_len])
  σ * shiftAll

/-- Direct evaluation of `(sign (clowPerm W)) * ∏ A(π(2t), π(2t+1)) = clowSeqWeight A W`. -/
lemma clowPerm_weight_eq {k : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) R) (W : ClowSeq k) (hSimple : IsSimpleSeq W) :
    (Equiv.Perm.sign (clowPerm W hSimple) : R) *
        ∏ t : Fin k, A (clowPerm W hSimple (evenV t)) (clowPerm W hSimple (oddV t)) =
      clowSeqWeight A W := by
  classical
  -- Unfold clowPerm pieces
  set verts := W.clows.flatMap Clow.verts
  have hlen : verts.length = k := by
    have : (clowsToSteps W.clows).length = verts.length := by
      unfold clowsToSteps verts
      induction W.clows with
      | nil => rfl
      | cons C cs ih => simp [List.flatMap_cons, ih]
    rw [← this, clowsToSteps_length, W.total_len]
  let ws : Fin k → Fin (2 * k) := fun t => verts[t.val]'(by rw [hlen]; exact t.isLt)
  have hpair_inj : Function.Injective (fun t : Fin k => pairOf (ws t)) := by
    intro t₁ t₂ heq
    have hnd : (verts.map pairOf).Nodup := hSimple
    have h1 : (verts.map pairOf)[t₁.val]'(by simp [hlen]) =
        (verts.map pairOf)[t₂.val]'(by simp [hlen]) := by simpa [ws] using heq
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  let τ : Equiv.Perm (Fin k) :=
    Equiv.ofBijective (fun t => pairOf (ws t)) (Finite.injective_iff_bijective.mp hpair_inj)
  let S : Finset (Fin k) := Finset.univ.filter (fun t => (ws t).val % 2 = 0)
  let σ : Equiv.Perm (Fin (2 * k)) := liftPairPerm τ * flipPairs S
  let shiftAll : Equiv.Perm (Fin (2 * k)) :=
    shiftClows 0 W.clows (by rw [zero_add, W.total_len])
  have hperm_eq : clowPerm W hSimple = σ * shiftAll := rfl
  -- Check σ action on evenV t and oddV t
  have hσ_even : ∀ t : Fin k, σ (evenV t) = mate (ws t) := by
    intro t
    dsimp [σ, flipPairs, S]
    by_cases he : (ws t).val % 2 = 0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
        mate_evenV, liftPairPerm_oddV]
      change oddV (pairOf (ws t)) = mate (ws t)
      ext; dsimp [oddV, mate, pairOf]; split_ifs <;> omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
        liftPairPerm_evenV]
      change evenV (pairOf (ws t)) = mate (ws t)
      ext; dsimp [evenV, mate, pairOf]; split_ifs <;> omega
  have hσ_odd : ∀ t : Fin k, σ (oddV t) = ws t := by
    intro t
    dsimp [σ, flipPairs, S]
    by_cases he : (ws t).val % 2 = 0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
        mate_oddV, liftPairPerm_evenV]
      change evenV (pairOf (ws t)) = ws t
      ext; dsimp [evenV, pairOf]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
        liftPairPerm_oddV]
      change oddV (pairOf (ws t)) = ws t
      ext; dsimp [oddV, pairOf]; omega
  -- Compute sign of clowPerm
  have hsign_σ : ((Equiv.Perm.sign σ : ℤ) : R) = ∏ t : Fin k, (-(jSign (ws t) : R)) := by
    dsimp [σ]
    rw [map_mul, sign_liftPairPerm, one_mul, sign_flipPairs, Units.val_pow_eq_pow_val]
    have hcard : ((-1 : ℤ) ^ S.card : ℤ) = ∏ t : Fin k, if (ws t).val % 2 = 0 then (-1 : ℤ) else 1 := by
      simp [S, Finset.prod_ite]
    change (((-1 : ℤ) ^ S.card : ℤ) : R) = _
    rw [hcard]
    push_cast
    refine Finset.prod_congr rfl fun t _ => ?_
    unfold jSign; split_ifs <;> norm_num
  have hsign_shift : ((Equiv.Perm.sign shiftAll : ℤ) : R) =
      (W.clows.map (fun C => (-1 : R) ^ (C.len - 1))).prod := by
    have h1 := sign_shiftClows 0 W.clows (by rw [zero_add, W.total_len])
    have hcast := congrArg (Int.cast (R := R)) h1
    simpa [shiftAll, List.map_map, Function.comp_def] using hcast
  have hflat_len : ∀ (ds : List (Clow k)), (ds.flatMap Clow.verts).length = (ds.map Clow.len).sum := by
    intro ds
    induction ds with
    | nil => rfl
    | cons C cs' ih => simp [List.flatMap_cons, Clow.verts_length, ih]
  -- Now prove the block product identity by induction on a suffix `cs` of `W.clows`
  have hblock_ind :
      ∀ (a : ℕ) (cs : List (Clow k)) (hbound : a + (cs.map Clow.len).sum ≤ k)
        (hslice : ∀ (j : ℕ) (hj : j < (cs.flatMap Clow.verts).length),
          ws ⟨a + j, by have := hflat_len cs; omega⟩ = (cs.flatMap Clow.verts)[j]),
      (cs.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
        ∏ t ∈ Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val < a + (cs.map Clow.len).sum),
          (-(jSign (ws t) : R) * A (σ (shiftClows a cs hbound (evenV t))) (ws t)) =
      (cs.map (clowWeight A)).prod := by
    intro a cs
    induction cs generalizing a with
    | nil =>
      intro hbound _
      have hemp : Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val < a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro t _; omega
      simp [hemp]
    | cons C cs ih =>
      intro hbound hslice
      have hlen_cs : (cs.flatMap Clow.verts).length = (cs.map Clow.len).sum := by
        clear hslice hbound ih
        induction cs with
        | nil => rfl
        | cons D ds ih2 => simp [List.flatMap_cons, Clow.verts_length, ih2]
      have hL : 1 ≤ C.len := by unfold Clow.len; omega
      have h1 : a + C.len ≤ k := by simp at hbound; omega
      have h2 : a + C.len + (cs.map Clow.len).sum ≤ k := by simp at hbound; omega
      -- Split the Finset into [a, a + C.len) and [a + C.len, a + C.len + sum cs)
      let F1 := Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val < a + C.len)
      let F2 := Finset.univ.filter (fun t : Fin k => a + C.len ≤ t.val ∧ t.val < a + C.len + (cs.map Clow.len).sum)
      have hunion : Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val < a + ((C :: cs).map Clow.len).sum) =
          F1 ∪ F2 := by
        ext t; simp only [F1, F2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
          List.map_cons, List.sum_cons]
        omega
      have hdisj : Disjoint F1 F2 := by
        rw [Finset.disjoint_filter]; intro t _ ht1 ht2; omega
      rw [hunion, Finset.prod_union hdisj, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      -- Simplify F2 using IH
      have hF2_congr : ∏ t ∈ F2, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t)) =
          ∏ t ∈ F2, (-(jSign (ws t) : R) * A (σ (shiftClows (a + C.len) cs h2 (evenV t))) (ws t)) := by
        refine Finset.prod_congr rfl fun t ht => ?_
        have htr := (Finset.mem_filter.mp ht).2
        simp only [shiftClows, Equiv.Perm.mul_apply]
        -- shiftClows (a + C.len) cs maps evenV t to evenV t' with t' ≥ a + C.len
        have hge_after : ∃ t' : Fin k, shiftClows (a + C.len) cs h2 (evenV t) = evenV t' ∧ a + C.len ≤ t'.val := by
          -- Even simpler: shiftBlock a C.len fixes everything outside [a, a + C.len), and shiftClows (a + C.len) preserves {evenV i | a + C.len ≤ i}
          suffices hpres : ∀ (b : ℕ) (ds : List (Clow k)) (hb : b + (ds.map Clow.len).sum ≤ k)
              (x : Fin k), b ≤ x.val → ∃ y : Fin k, shiftClows b ds hb (evenV x) = evenV y ∧ b ≤ y.val from
            hpres (a + C.len) cs h2 t htr.1
          intro b ds
          induction ds generalizing b with
          | nil => intro _ x hx; exact ⟨x, rfl, hx⟩
          | cons D ds ihd =>
            intro hb x hx
            simp only [shiftClows, Equiv.Perm.mul_apply]
            by_cases hxD : x.val < b + D.len
            · have hb' : b + D.len + (ds.map Clow.len).sum ≤ k := by
                simp only [List.map_cons, List.sum_cons] at hb; omega
              have hfix := shiftClows_evenV_outside (b + D.len) ds hb' x (Or.inl hxD)
              rw [hfix]
              have hDlen : 1 ≤ D.len := by unfold Clow.len; omega
              have hxe : x = ⟨b + (x.val - b), by have := x.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hxe, shiftBlock_evenV_inside b D.len hDlen (by omega) (x.val - b) (by omega)]
              refine ⟨_, rfl, ?_⟩
              dsimp only; split_ifs <;> omega
            · have hb' : b + D.len + (ds.map Clow.len).sum ≤ k := by
                simp only [List.map_cons, List.sum_cons] at hb; omega
              rcases ihd (b + D.len) hb' x (by omega) with ⟨y, hy, hyge⟩
              rw [hy, shiftBlock_evenV_outside b D.len (by unfold Clow.len; omega) (by omega) y (Or.inr hyge)]
              exact ⟨y, rfl, by omega⟩
        rcases hge_after with ⟨t', ht', ht'ge⟩
        rw [ht', shiftBlock_evenV_outside a C.len hL h1 t' (Or.inr ht'ge)]
      have hslice_cs : ∀ (j : ℕ) (hj : j < (cs.flatMap Clow.verts).length),
          ws ⟨a + C.len + j, by omega⟩ = (cs.flatMap Clow.verts)[j] := by
        intro j hj
        have htot : C.len + j < ((C :: cs).flatMap Clow.verts).length := by
          rw [List.flatMap_cons, List.length_append, C.verts_length]; omega
        have h0 := hslice (C.len + j) htot
        have hidx : (⟨a + C.len + j, by omega⟩ : Fin k) = ⟨a + (C.len + j), by
            have := hflat_len (C :: cs); omega⟩ := Fin.ext (by dsimp only; omega)
        rw [hidx, h0]
        simp only [List.flatMap_cons]
        rw [List.getElem_append_right (by rw [C.verts_length]; omega)]
        simp [C.verts_length]
      have hIH := ih (a + C.len) h2 hslice_cs
      -- Simplify F1
      have hF1 : ((-1 : R) ^ (C.len - 1)) *
          ∏ t ∈ F1, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t)) =
          clowWeight A C := by
        have hbi : ∏ t ∈ F1, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t)) =
            ∏ r : Fin C.len,
              (-(jSign (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt)) : R) *
                A (mate (C.verts[if r.val = 0 then C.len - 1 else r.val - 1]'(by
                    rw [C.verts_length]; unfold Clow.len; split_ifs <;> omega)))
                  (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt))) := by
          refine Finset.prod_bij (fun (t : Fin k) (ht : t ∈ F1) =>
              (⟨t.val - a, by have := (Finset.mem_filter.mp ht).2; omega⟩ : Fin C.len))
            (fun _ _ => Finset.mem_univ _)
            (fun t₁ ht₁ t₂ ht₂ heq => by
              have h1 := (Finset.mem_filter.mp ht₁).2
              have h2 := (Finset.mem_filter.mp ht₂).2
              have hv := congrArg Fin.val heq
              dsimp at hv; exact Fin.ext (by omega))
            (fun r _ => ⟨⟨a + r.val, by have := r.isLt; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by have := r.isLt; dsimp; omega⟩,
              Fin.ext (by dsimp; omega)⟩)
            (fun t ht => ?_)
          have htr := (Finset.mem_filter.mp ht).2
          have hws_t : ∀ (r : ℕ) (hr : r < C.len),
              ws ⟨a + r, by omega⟩ = C.verts[r]'(by rw [C.verts_length]; exact hr) := by
            intro r hr
            have htot : r < ((C :: cs).flatMap Clow.verts).length := by
              rw [List.flatMap_cons, List.length_append, C.verts_length]; omega
            have h0 := hslice r htot
            have hidx : (⟨a + r, by omega⟩ : Fin k) = ⟨a + r, by
                have := hflat_len (C :: cs); omega⟩ := rfl
            rw [hidx, h0]
            simp only [List.flatMap_cons]
            rw [List.getElem_append_left (by rw [C.verts_length]; exact hr)]
          have ht_eq : t = ⟨a + (t.val - a), by have := t.isLt; omega⟩ := Fin.ext (by dsimp only; omega)
          simp only [shiftClows, Equiv.Perm.mul_apply]
          rw [shiftClows_evenV_outside (a + C.len) cs h2 t (Or.inl htr.2)]
          conv_lhs => rw [ht_eq]
          rw [shiftBlock_evenV_inside a C.len hL h1 (t.val - a) (by omega), hσ_even,
              hws_t (t.val - a) (by omega)]
          have hprev : (⟨if t.val - a = 0 then a + C.len - 1 else a + (t.val - a) - 1, by split_ifs <;> omega⟩ : Fin k) =
              ⟨a + (if t.val - a = 0 then C.len - 1 else (t.val - a) - 1), by split_ifs <;> omega⟩ := by
            apply Fin.ext; dsimp only; split_ifs <;> omega
          rw [hprev, hws_t (if t.val - a = 0 then C.len - 1 else (t.val - a) - 1) (by split_ifs <;> omega)]
        rw [hbi]
        have hfact :
            (∏ r : Fin C.len,
              (-(jSign (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt)) : R) *
                A (mate (C.verts[if r.val = 0 then C.len - 1 else r.val - 1]'(by
                    rw [C.verts_length]; unfold Clow.len; split_ifs <;> omega)))
                  (C.verts[r.val]'(by rw [C.verts_length]; exact r.isLt)))) =
            ((-1 : R) ^ C.len) * cycWeight A C.verts := by
          rw [cycWeight_eq_fin_prod]
          have h1 : ((-1 : R) ^ C.len) = ∏ _r : Fin C.len, (-1 : R) := by simp
          rw [h1, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun r _ => ?_
          ring
        rw [hfact]
        unfold clowWeight
        have hpow : (-1 : R) ^ (C.len - 1) * (-1 : R) ^ C.len = -1 := by
          rw [← pow_add]
          have hodd : C.len - 1 + C.len = 2 * (C.len - 1) + 1 := by omega
          rw [hodd, pow_succ, pow_mul]
          norm_num
        calc
          (-1 : R) ^ (C.len - 1) * ((-1 : R) ^ C.len * cycWeight A C.verts)
              = ((-1 : R) ^ (C.len - 1) * (-1 : R) ^ C.len) * cycWeight A C.verts := by ring
          _ = -cycWeight A C.verts := by rw [hpow]; ring
      calc
        (-1 : R) ^ (C.len - 1) * (cs.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
            ((∏ t ∈ F1, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t))) *
             (∏ t ∈ F2, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t))))
            = ((-1 : R) ^ (C.len - 1) *
                ∏ t ∈ F1, (-(jSign (ws t) : R) * A (σ (shiftClows a (C :: cs) hbound (evenV t))) (ws t))) *
              ((cs.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
                ∏ t ∈ F2, (-(jSign (ws t) : R) * A (σ (shiftClows (a + C.len) cs h2 (evenV t))) (ws t))) := by
              rw [hF2_congr]; ring
        _ = clowWeight A C * (cs.map (clowWeight A)).prod := by rw [hF1, hIH]
  -- Apply hblock_ind at a = 0, cs = W.clows
  have hmain := hblock_ind 0 W.clows (by rw [zero_add, W.total_len])
    (fun j hj => by simp only [ws, verts, zero_add])
  have hfilt : Finset.univ.filter (fun t : Fin k => 0 ≤ t.val ∧ t.val < 0 + (W.clows.map Clow.len).sum) =
      Finset.univ := by
    ext t; simp [W.total_len, t.isLt]
  rw [hfilt] at hmain
  rw [hperm_eq, map_mul, Units.val_mul, Int.cast_mul, hsign_σ, hsign_shift]
  have hprod_eq :
      (∏ t : Fin k, (-(jSign (ws t) : R))) *
        ∏ t : Fin k, A ((σ * shiftAll) (evenV t)) ((σ * shiftAll) (oddV t)) =
      ∏ t : Fin k, (-(jSign (ws t) : R) * A (σ (shiftAll (evenV t))) (ws t)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [Equiv.Perm.mul_apply, shiftAll, shiftClows_oddV, hσ_odd]
  calc
    (∏ t : Fin k, -(jSign (ws t) : R)) * (W.clows.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
        ∏ t : Fin k, A ((σ * shiftAll) (evenV t)) ((σ * shiftAll) (oddV t))
        = (W.clows.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
            ((∏ t : Fin k, -(jSign (ws t) : R)) *
              ∏ t : Fin k, A ((σ * shiftAll) (evenV t)) ((σ * shiftAll) (oddV t))) := by ring
    _ = (W.clows.map (fun C => (-1 : R) ^ (C.len - 1))).prod *
          ∏ t : Fin k, (-(jSign (ws t) : R) * A (σ (shiftAll (evenV t))) (ws t)) := by
          rw [hprod_eq]
    _ = clowSeqWeight A W := hmain

/-- Edge finset of a permutation `π : Equiv.Perm (Fin (2 * k))`. -/
def permEdgeFinset {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) : Finset (Sym2 (Fin (2 * k))) :=
  Finset.univ.image (fun t : Fin k => s(π (evenV t), π (oddV t)))

lemma permEdgeFinset_isPerfectMatching {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) :
    IsPerfectMatching (⊤ : SimpleGraph (Fin (2 * k))) (permEdgeFinset π) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨t, _, rfl⟩
    exact fun h => evenV_ne_oddV t (π.injective h)
  · intro v
    let idx := π.symm v
    let t0 : Fin k := pairOf idx
    have hv_in : s(π (evenV t0), π (oddV t0)) ∈
        (permEdgeFinset π).filter (fun e => v ∈ e) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t0), ?_⟩
      rw [Sym2.mem_iff]
      rcases eq_evenV_or_oddV idx with h | h
      · left; change v = π (evenV (pairOf (π.symm v))); rw [← h, Equiv.apply_symm_apply]
      · right; change v = π (oddV (pairOf (π.symm v))); rw [← h, Equiv.apply_symm_apply]
    refine Finset.card_eq_one.mpr ⟨s(π (evenV t0), π (oddV t0)),
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hv_in, ?_⟩⟩
    intro e he
    rcases Finset.mem_filter.mp he with ⟨himg, hve⟩
    rcases Finset.mem_image.mp himg with ⟨t, _, rfl⟩
    rw [Sym2.mem_iff] at hve
    have ht_eq : t = t0 := by
      rcases hve with h1 | h2
      · have : idx = evenV t := by rw [← π.symm_apply_apply (evenV t), ← h1]
        dsimp [t0]; rw [this, pairOf_evenV]
      · have : idx = oddV t := by rw [← π.symm_apply_apply (oddV t), ← h2]
        dsimp [t0]; rw [this, pairOf_oddV]
    rw [ht_eq]

/-- Map a simple clow sequence to its unique `OrderedPairing k`. -/
noncomputable def simpleToPairing {k : ℕ} (W : {W : ClowSeq k // IsSimpleSeq W}) :
    OrderedPairing k :=
  Classical.choose (exists_orderedPairing_of_isPerfectMatching
    (⊤ : SimpleGraph (Fin (2 * k))) (permEdgeFinset (clowPerm W.1 W.2))
    (permEdgeFinset_isPerfectMatching (clowPerm W.1 W.2)))

lemma simpleToPairing_edgeFinset {k : ℕ} (W : {W : ClowSeq k // IsSimpleSeq W}) :
    (simpleToPairing W).edgeFinset = permEdgeFinset (clowPerm W.1 W.2) :=
  Classical.choose_spec (exists_orderedPairing_of_isPerfectMatching
    (⊤ : SimpleGraph (Fin (2 * k))) (permEdgeFinset (clowPerm W.1 W.2))
    (permEdgeFinset_isPerfectMatching (clowPerm W.1 W.2)))

/-! #### Alternating step permutation `step m` for an `OrderedPairing k` -/

/-- The `mate` involution as an `Equiv.Perm (Fin (2 * k))`. -/
def mateEquiv (k : ℕ) : Equiv.Perm (Fin (2 * k)) where
  toFun := mate
  invFun := mate
  left_inv := mate_mate
  right_inv := mate_mate

/-- Matching mate of `v` under `m : OrderedPairing k`. -/
def matchMateEquiv {k : ℕ} (m : OrderedPairing k) : Equiv.Perm (Fin (2 * k)) :=
  (m.perm.symm.trans (mateEquiv k)).trans m.perm

lemma matchMateEquiv_involutive {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) :
    matchMateEquiv m (matchMateEquiv m v) = v := by
  simp [matchMateEquiv, mateEquiv]

lemma matchMateEquiv_ne_self {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) :
    matchMateEquiv m v ≠ v := by
  intro h
  simp only [matchMateEquiv, Equiv.trans_apply, mateEquiv, Equiv.coe_fn_mk] at h
  have := m.perm.injective (h.trans (m.perm.apply_symm_apply v).symm)
  exact mate_ne_self (m.perm.symm v) this

lemma matchMateEquiv_eq_iff_mem_edgeFinset {k : ℕ} (m : OrderedPairing k) (u v : Fin (2 * k)) :
    matchMateEquiv m u = v ↔ s(u, v) ∈ m.edgeFinset := by
  constructor
  · intro h
    let idx := m.perm.symm u
    let i : Fin k := pairOf idx
    have hu : u = m.perm idx := (m.perm.apply_symm_apply u).symm
    have hv : v = m.perm (mate idx) := h.symm
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rcases eq_evenV_or_oddV idx with hidx | hidx
    · change s(m.perm (evenV i), m.perm (oddV i)) = s(u, v)
      rw [hu, hv, hidx]; simp [i]
    · change s(m.perm (evenV i), m.perm (oddV i)) = s(u, v)
      rw [hu, hv, hidx, Sym2.eq_swap]; simp [i]
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    change s(m.perm (evenV i), m.perm (oddV i)) = s(u, v) at hi
    rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      simp [matchMateEquiv, mateEquiv]
    · rw [← h1, ← h2]
      simp [matchMateEquiv, mateEquiv]

/-- Alternating cycle step `stepPerm m v = matchMateEquiv m (mate v)`. -/
def stepPerm {k : ℕ} (m : OrderedPairing k) : Equiv.Perm (Fin (2 * k)) :=
  (mateEquiv k).trans (matchMateEquiv m)

lemma stepPerm_apply {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) :
    stepPerm m v = matchMateEquiv m (mate v) := rfl

lemma stepPerm_symm_apply {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) :
    (stepPerm m)⁻¹ v = mate (matchMateEquiv m v) := by
  change (stepPerm m).symm v = _
  simp [stepPerm, Equiv.symm_trans_apply, mateEquiv, matchMateEquiv]

lemma mate_stepPerm_pow {k : ℕ} (m : OrderedPairing k) (r : ℕ) (v : Fin (2 * k)) :
    mate (((stepPerm m) ^ r) v) = (((stepPerm m)⁻¹) ^ r) (mate v) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, stepPerm_apply,
        pow_succ', Equiv.Perm.mul_apply, stepPerm_symm_apply, ← ih]

/-- Key 5-line theorem: no power of `stepPerm m` maps `v` to `mate v`! -/
lemma stepPerm_pow_ne_mate {k : ℕ} (m : OrderedPairing k) (r : ℕ) (v : Fin (2 * k)) :
    ((stepPerm m) ^ r) v ≠ mate v := by
  intro h
  rcases Nat.even_or_odd r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · -- r = t + t
    rw [pow_add, Equiv.Perm.mul_apply] at h
    have h1 : ((stepPerm m) ^ t) v = (((stepPerm m)⁻¹) ^ t) (mate v) := by
      have := congrArg (((stepPerm m)⁻¹) ^ t) h
      rw [← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply] at this
      exact this
    rw [← mate_stepPerm_pow] at h1
    exact mate_ne_self _ h1.symm
  · -- r = 2 * t + 1
    have h2 : (stepPerm m) (((stepPerm m) ^ t) v) = (((stepPerm m)⁻¹) ^ t) (mate v) := by
      have hsplit : 2 * t + 1 = t + (1 + t) := by omega
      rw [hsplit, pow_add, pow_add, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h
      have := congrArg (((stepPerm m)⁻¹) ^ t) h
      rw [← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply] at this
      exact this
    rw [← mate_stepPerm_pow, stepPerm_apply] at h2
    exact matchMateEquiv_ne_self m _ h2

/-- The alternating step relation holds on every clow of a simple clow sequence `W`. -/
lemma clow_verts_stepPerm {k : ℕ} (W : {W : ClowSeq k // IsSimpleSeq W}) :
    let m := simpleToPairing W
    ∀ C ∈ W.1.clows,
      (∀ (r : ℕ) (hr : r < C.len),
        stepPerm m (C.verts[if r = 0 then C.len - 1 else r - 1]'(by
            rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)) =
          C.verts[r]'(by rw [C.verts_length]; exact hr)) := by
  intro m C hC r hr
  -- Every edge (mate prev, cur) of C is an edge of clowPerm W, hence in m.edgeFinset
  rw [stepPerm_apply, matchMateEquiv_eq_iff_mem_edgeFinset, simpleToPairing_edgeFinset]
  -- Locate C inside W.1.clows = l1 ++ [C] ++ l2
  rcases List.append_of_mem hC with ⟨l1, l2, hcl⟩
  let a := (l1.map Clow.len).sum
  have ha_le : a + C.len ≤ k := by
    have htot := W.1.total_len
    rw [hcl] at htot
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htot
    dsimp [a]; omega
  let t : Fin k := ⟨a + r, by omega⟩
  refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
  -- Compute clowPerm W (evenV t) and clowPerm W (oddV t)
  set verts := W.1.clows.flatMap Clow.verts
  have hlen_l1 : (l1.flatMap Clow.verts).length = a := by
    dsimp [a]
    suffices ∀ ds : List (Clow k), (ds.flatMap Clow.verts).length = (ds.map Clow.len).sum from this l1
    intro ds; induction ds with
    | nil => rfl
    | cons X xs ih => simp [List.flatMap_cons, Clow.verts_length, ih]
  have hlen_all : verts.length = k := by
    have : (clowsToSteps W.1.clows).length = verts.length := by
      unfold clowsToSteps verts
      induction W.1.clows with
      | nil => rfl
      | cons X xs ih => simp [List.flatMap_cons, ih]
    rw [← this, clowsToSteps_length, W.1.total_len]
  have hverts_get : ∀ (j : ℕ) (hj : j < C.len),
      verts[a + j]'(by rw [hlen_all]; omega) = C.verts[j]'(by rw [C.verts_length]; exact hj) := by
    intro j hj
    have hv_eq : verts = l1.flatMap Clow.verts ++ (C.verts ++ l2.flatMap Clow.verts) := by
      dsimp [verts]; rw [hcl]; simp [List.flatMap_append, List.flatMap_cons]
    have hget : ∀ (xs : List (Fin (2 * k))) (h : xs = l1.flatMap Clow.verts ++ (C.verts ++ l2.flatMap Clow.verts))
        (h1 : a + j < xs.length),
        xs[a + j]'h1 = C.verts[j]'(by rw [C.verts_length]; exact hj) := by
      intro xs h h1; subst h
      rw [List.getElem_append_right (by omega)]
      simp only [hlen_l1, Nat.add_sub_cancel_left]
      rw [List.getElem_append_left (by rw [C.verts_length]; exact hj)]
    exact hget verts hv_eq _
  -- Evaluate shiftClows 0 W.1.clows at evenV t and oddV t
  have hshift_split : ∀ (b : ℕ) (xs ys : List (Clow k)) (hb : b + ((xs ++ ys).map Clow.len).sum ≤ k),
      shiftClows b (xs ++ ys) hb =
        shiftClows b xs (by simp at hb; omega) *
          shiftClows (b + (xs.map Clow.len).sum) ys (by simp at hb; omega) := by
    intro b xs ys
    induction xs generalizing b with
    | nil => intro hb; simp [shiftClows]
    | cons X xs ih =>
      intro hb
      simp only [List.cons_append, shiftClows, mul_assoc]
      congr 1
      have hsum : b + X.len + (xs.map Clow.len).sum = b + ((X :: xs).map Clow.len).sum := by
        simp [Nat.add_assoc]
      have hb' : b + X.len + ((xs ++ ys).map Clow.len).sum ≤ k := by
        simp only [List.cons_append, List.map_cons, List.sum_cons] at hb; omega
      have hrec := ih (b + X.len) hb'
      rw [hrec]
      congr 1
      have hcongr : ∀ (n₁ n₂ : ℕ) (he : n₁ = n₂)
          (h1 : n₁ + (ys.map Clow.len).sum ≤ k) (h2 : n₂ + (ys.map Clow.len).sum ≤ k),
          shiftClows n₁ ys h1 = shiftClows n₂ ys h2 := by
        rintro n₁ _ rfl _ _; rfl
      exact hcongr _ _ hsum _ _
  have hshift_t : shiftClows 0 W.1.clows (by rw [zero_add, W.1.total_len]) (evenV t) =
      evenV ⟨a + (if r = 0 then C.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
    have h0 : ∀ (cs : List (Clow k)) (hcs : cs = l1 ++ (C :: l2))
        (hb : 0 + (cs.map Clow.len).sum ≤ k),
        shiftClows 0 cs hb (evenV t) =
          evenV ⟨a + (if r = 0 then C.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
      intro cs hcs hb; subst hcs
      rw [hshift_split 0 l1 (C :: l2) hb, Equiv.Perm.mul_apply]
      have hba : a + ((C :: l2).map Clow.len).sum ≤ k := by
        simp only [List.map_append, List.sum_append, zero_add] at hb; dsimp [a]; omega
      have hstep : shiftClows a (C :: l2) hba (evenV t) =
          evenV ⟨a + (if r = 0 then C.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
        simp only [shiftClows, Equiv.Perm.mul_apply]
        have hba2 : a + C.len + (l2.map Clow.len).sum ≤ k := by
          simp only [List.map_cons, List.sum_cons] at hba; omega
        rw [shiftClows_evenV_outside (a + C.len) l2 hba2 t (Or.inl (by dsimp [t]; omega))]
        rw [shiftBlock_evenV_inside a C.len (by unfold Clow.len; omega) ha_le r hr]
        congr 1; apply Fin.ext; dsimp only; split_ifs <;> omega
      have heq_shift : shiftClows (0 + (l1.map Clow.len).sum) (C :: l2) (by simp at hb; omega) =
          shiftClows a (C :: l2) hba := by
        congr 1; simp [a]
      rw [heq_shift, hstep]
      exact shiftClows_evenV_outside 0 l1 (by simp at hb; omega) _
        (Or.inr (by dsimp [a]; split_ifs <;> omega))
    exact h0 W.1.clows hcl (by rw [zero_add, W.1.total_len])
  -- Now evaluate clowPerm W (evenV t) and clowPerm W (oddV t)
  have hclow_even : clowPerm W.1 W.2 (evenV t) =
      mate (C.verts[if r = 0 then C.len - 1 else r - 1]'(by
        rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)) := by
    unfold clowPerm
    simp only [Equiv.Perm.mul_apply]
    rw [hshift_t]
    set s : Fin k := ⟨a + (if r = 0 then C.len - 1 else r - 1), by split_ifs <;> omega⟩
    have hws_s : verts[s.val]'(by rw [hlen_all]; exact s.isLt) =
        C.verts[if r = 0 then C.len - 1 else r - 1]'(by
          rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega) :=
      hverts_get _ (by unfold Clow.len at hr ⊢; split_ifs <;> omega)
    dsimp [flipPairs]
    by_cases he : ((W.1.clows.flatMap Clow.verts)[s.val]'(by rw [hlen_all]; exact s.isLt)).val % 2 = 0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
        mate_evenV, liftPairPerm_oddV]
      change oddV (pairOf (verts[s.val]'_)) = _
      have he' : (C.verts[if r = 0 then C.len - 1 else r - 1]'(by
          rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)).val % 2 = 0 := by
        rw [← hws_s]; exact he
      rw [hws_s]
      ext; dsimp [oddV, mate, pairOf]; simp [he']; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
        liftPairPerm_evenV]
      change evenV (pairOf (verts[s.val]'_)) = _
      have he' : (C.verts[if r = 0 then C.len - 1 else r - 1]'(by
          rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)).val % 2 ≠ 0 := by
        rw [← hws_s]; exact he
      rw [hws_s]
      ext; dsimp [evenV, mate, pairOf]; simp [he']; omega
  have hclow_odd : clowPerm W.1 W.2 (oddV t) =
      C.verts[r]'(by rw [C.verts_length]; exact hr) := by
    unfold clowPerm
    simp only [Equiv.Perm.mul_apply, shiftClows_oddV]
    have hws_t : verts[t.val]'(by rw [hlen_all]; exact t.isLt) =
        C.verts[r]'(by rw [C.verts_length]; exact hr) := hverts_get r hr
    dsimp [flipPairs]
    by_cases he : ((W.1.clows.flatMap Clow.verts)[t.val]'(by rw [hlen_all]; exact t.isLt)).val % 2 = 0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
        mate_oddV, liftPairPerm_evenV]
      change evenV (pairOf (verts[t.val]'_)) = _
      have he' : (C.verts[r]'(by rw [C.verts_length]; exact hr)).val % 2 = 0 := by
        rw [← hws_t]; exact he
      rw [hws_t]
      ext; dsimp [evenV, pairOf]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
        liftPairPerm_oddV]
      change oddV (pairOf (verts[t.val]'_)) = _
      have he' : (C.verts[r]'(by rw [C.verts_length]; exact hr)).val % 2 ≠ 0 := by
        rw [← hws_t]; exact he
      rw [hws_t]
      ext; dsimp [oddV, pairOf]; omega
  rw [hclow_even, hclow_odd]

/-- For a clow `C` obeying `stepPerm m`, `C.verts[r] = (stepPerm m)^(r + 1) (oddV C.head)`
and `C.len` is the smallest `L ≥ 1` with `(stepPerm m)^L (oddV C.head) = oddV C.head`. -/
lemma clow_verts_eq_stepPerm_pow {k : ℕ} (m : OrderedPairing k) (C : Clow k)
    (hstep : ∀ (r : ℕ) (hr : r < C.len),
      stepPerm m (C.verts[if r = 0 then C.len - 1 else r - 1]'(by
          rw [C.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)) =
        C.verts[r]'(by rw [C.verts_length]; exact hr)) :
    ∀ (r : ℕ) (hr : r < C.len),
      C.verts[r]'(by rw [C.verts_length]; exact hr) =
        ((stepPerm m) ^ (r + 1)) (oddV C.head) := by
  intro r
  induction r with
  | zero =>
    intro hr
    have h0 := hstep 0 hr
    simp only [↓reduceIte] at h0
    have hlast : C.verts[C.len - 1]'(by rw [C.verts_length]; unfold Clow.len; omega) = oddV C.head := by
      unfold Clow.verts Clow.len; simp
    rw [hlast] at h0
    simpa [pow_one] using h0.symm
  | succ r ih =>
    intro hr
    have h1 := hstep (r + 1) hr
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h1
    rw [← h1, ih (by omega), ← Equiv.Perm.mul_apply, ← pow_succ']

/-- Every element of a finite permutation returns to itself in `L ≥ 1` steps. -/
lemma orbitLen_exists {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) :
    ∃ L : ℕ, 1 ≤ L ∧ (f ^ L) v = v := by
  have hfin : ∃ a b : ℕ, a < b ∧ (f ^ a) v = (f ^ b) v := by
    by_contra h
    push_neg at h
    have hinj : Function.Injective (fun n : ℕ => (f ^ n) v) := by
      intro a b hab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact absurd hab (h a b hlt)
      · rfl
      · exact absurd hab.symm (h b a hgt)
    haveI : Finite ℕ := Finite.of_injective (fun n : ℕ => (f ^ n) v) hinj
    exact not_finite ℕ
  rcases hfin with ⟨a, b, hab, heq⟩
  refine ⟨b - a, by omega, ?_⟩
  have h1 : (f ^ a) (((f ^ (b - a)) v)) = (f ^ a) v := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (le_of_lt hab), ← heq]
  exact (f ^ a).injective h1

/-- Minimum return time `≥ 1` of `v` under a permutation `f : Equiv.Perm (Fin (2 * k))`. -/
noncomputable def orbitLen {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) : ℕ :=
  Nat.find (orbitLen_exists f v)

lemma orbitLen_pos {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) :
    1 ≤ orbitLen f v := (Nat.find_spec (orbitLen_exists f v)).1

lemma orbitLen_pow {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) :
    (f ^ (orbitLen f v)) v = v := (Nat.find_spec (orbitLen_exists f v)).2

lemma orbitLen_min {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k))
    {L : ℕ} (hL1 : 1 ≤ L) (hL2 : L < orbitLen f v) :
    (f ^ L) v ≠ v := by
  intro h
  exact absurd (Nat.find_min' (orbitLen_exists f v) ⟨hL1, h⟩) (not_le_of_gt hL2)

lemma orbit_pow_inj {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k))
    {a b : ℕ} (ha : a < orbitLen f v) (hb : b < orbitLen f v)
    (heq : (f ^ a) v = (f ^ b) v) : a = b := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exfalso
    have h1 : (f ^ a) ((f ^ (b - a)) v) = (f ^ a) v := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt), ← heq]
    exact orbitLen_min f v (by omega) (by omega) ((f ^ a).injective h1)
  · rfl
  · exfalso
    have h1 : (f ^ b) ((f ^ (a - b)) v) = (f ^ b) v := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (le_of_lt hgt), heq]
    exact orbitLen_min f v (by omega) (by omega) ((f ^ b).injective h1)

lemma orbit_mem_iff_lt_orbitLen {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v w : Fin (2 * k)) :
    (∃ n : ℕ, (f ^ n) v = w) ↔ ∃ r : ℕ, r < orbitLen f v ∧ (f ^ r) v = w := by
  constructor
  · rintro ⟨n, rfl⟩
    let L := orbitLen f v
    have hL : 0 < L := orbitLen_pos f v
    refine ⟨n % L, Nat.mod_lt n hL, ?_⟩
    have hmod : ∀ q : ℕ, (f ^ (L * q + n % L)) v = (f ^ (n % L)) v := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        have : L * (q + 1) + n % L = L * q + n % L + L := by ring
        rw [this, pow_add, Equiv.Perm.mul_apply, orbitLen_pow, ih]
    rw [← hmod (n / L), Nat.div_add_mod]
  · rintro ⟨r, _, h⟩; exact ⟨r, h⟩

/-- Orbit list `[(f^1) v, (f^2) v, ..., (f^L) v]` of `v` under `f` (ends at `v`). -/
noncomputable def orbitList {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) :
    List (Fin (2 * k)) :=
  (List.range (orbitLen f v)).map (fun r => (f ^ (r + 1)) v)

lemma orbitList_length {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v : Fin (2 * k)) :
    (orbitList f v).length = orbitLen f v := by
  simp [orbitList]

lemma orbitList_mem_iff {k : ℕ} (f : Equiv.Perm (Fin (2 * k))) (v w : Fin (2 * k)) :
    w ∈ orbitList f v ↔ ∃ n : ℕ, (f ^ n) v = w := by
  rw [orbit_mem_iff_lt_orbitLen]
  simp only [orbitList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases hlast : r + 1 = orbitLen f v
    · exact ⟨0, orbitLen_pos f v, by rw [hlast, orbitLen_pow]; rfl⟩
    · exact ⟨r + 1, by omega, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    by_cases hr0 : r = 0
    · subst hr0
      exact ⟨orbitLen f v - 1, by have := orbitLen_pos f v; omega, by
        have := orbitLen_pos f v
        rw [Nat.sub_add_cancel this, orbitLen_pow]; rfl⟩
    · exact ⟨r - 1, by omega, by rw [Nat.sub_add_cancel (by omega)]⟩

/-- Orbit of `stepPerm m` has distinct `pairOf` values (from `stepPerm_pow_ne_mate`). -/
lemma orbitList_stepPerm_pairOf_nodup {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) :
    ((orbitList (stepPerm m) v).map pairOf).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  apply Fin.ext
  dsimp only at hi hj heq ⊢
  simp only [orbitList, List.map_map, List.length_map, List.length_range] at hi hj
  simp only [orbitList, List.map_map, List.getElem_map, List.getElem_range, Function.comp_def] at heq
  rcases pairOf_eq_iff.mp heq with h1 | h2
  · rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      have hsub : ((stepPerm m) ^ (i + 1)) (((stepPerm m) ^ (j - i)) v) =
          ((stepPerm m) ^ (i + 1)) v := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show i + 1 + (j - i) = j + 1 by omega, ← h1]
      exact orbitLen_min (stepPerm m) v (by omega) (by omega) (((stepPerm m) ^ (i + 1)).injective hsub)
    · rfl
    · exfalso
      have hsub : ((stepPerm m) ^ (j + 1)) (((stepPerm m) ^ (i - j)) v) =
          ((stepPerm m) ^ (j + 1)) v := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show j + 1 + (i - j) = i + 1 by omega, h1]
      exact orbitLen_min (stepPerm m) v (by omega) (by omega) (((stepPerm m) ^ (j + 1)).injective hsub)
  · exfalso
    rcases le_total i j with hle | hle
    · have hsub : ((stepPerm m) ^ (j - i)) (((stepPerm m) ^ (i + 1)) v) =
          mate (((stepPerm m) ^ (i + 1)) v) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show j - i + (i + 1) = j + 1 by omega]
        rw [h2, mate_mate]
      exact stepPerm_pow_ne_mate m (j - i) _ hsub
    · have hsub : ((stepPerm m) ^ (i - j)) (((stepPerm m) ^ (j + 1)) v) =
          mate (((stepPerm m) ^ (j + 1)) v) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show i - j + (j + 1) = i + 1 by omega, h2]
      exact stepPerm_pow_ne_mate m (i - j) _ hsub

private lemma pairwise_lt_eq_of_mem_iff {α : Type*} [LinearOrder α] :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: bs, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: as, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: as, b :: bs, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have ha : a = b := by
      have ha_in : a ∈ b :: bs := (h a).mp List.mem_cons_self
      have hb_in : b ∈ a :: as := (h b).mpr List.mem_cons_self
      simp only [List.mem_cons] at ha_in hb_in
      rcases ha_in with rfl | ha_bs
      · rfl
      · rcases hb_in with rfl | hb_as
        · rfl
        · exact absurd (lt_trans (h2.1 a ha_bs) (h1.1 b hb_as)) (lt_irrefl _)
    subst ha
    congr 1
    apply pairwise_lt_eq_of_mem_iff h1.2 h2.2
    intro x
    have hx := h x
    simp only [List.mem_cons] at hx
    constructor
    · intro hxa
      have hne : x ≠ a := ne_of_gt (h1.1 x hxa)
      exact (hx.mp (Or.inr hxa)).resolve_left hne
    · intro hxb
      have hne : x ≠ a := ne_of_gt (h2.1 x hxb)
      exact (hx.mpr (Or.inr hxb)).resolve_left hne

/-- `simpleToPairing` is bijective! -/
theorem simpleToPairing_bijective (k : ℕ) :
    Function.Bijective (simpleToPairing (k := k)) := by
  classical
  -- Predicate: `c` is the canonical head of its `stepPerm m` orbit (contains `oddV c`, all pairs ≥ c)
  let IsHead (m : OrderedPairing k) (c : Fin k) : Prop :=
    ∀ w ∈ orbitList (stepPerm m) (oddV c), c ≤ pairOf w
  -- Helper: any clow C of a simple W satisfies C.verts = orbitList (stepPerm m) (oddV C.head) and IsHead m C.head
  have hclow_eq_orbit : ∀ (W : {W : ClowSeq k // IsSimpleSeq W}) (C : Clow k),
      C ∈ W.1.clows →
      C.verts = orbitList (stepPerm (simpleToPairing W)) (oddV C.head) ∧
      IsHead (simpleToPairing W) C.head := by
    intro W C hC
    set m := simpleToPairing W
    have hstep := clow_verts_stepPerm W C hC
    have hpow := clow_verts_eq_stepPerm_pow m C hstep
    have hlen_eq : C.len = orbitLen (stepPerm m) (oddV C.head) := by
      have hret : ((stepPerm m) ^ C.len) (oddV C.head) = oddV C.head := by
        have h1 := hpow (C.len - 1) (by unfold Clow.len; omega)
        have hlast : C.verts[C.len - 1]'(by rw [C.verts_length]; unfold Clow.len; omega) = oddV C.head := by
          unfold Clow.verts Clow.len; simp
        rw [hlast, Nat.sub_add_cancel (by unfold Clow.len; omega)] at h1
        exact h1.symm
      have hge : orbitLen (stepPerm m) (oddV C.head) ≤ C.len :=
        Nat.find_min' (orbitLen_exists (stepPerm m) (oddV C.head)) ⟨by unfold Clow.len; omega, hret⟩
      by_contra hne
      have hlt : orbitLen (stepPerm m) (oddV C.head) < C.len := lt_of_le_of_ne hge (Ne.symm hne)
      have hLpos := orbitLen_pos (stepPerm m) (oddV C.head)
      have hmid_val := hpow (orbitLen (stepPerm m) (oddV C.head) - 1) (by omega)
      rw [Nat.sub_add_cancel hLpos, orbitLen_pow] at hmid_val
      have hmem_mid : oddV C.head ∈ C.mid := by
        have hget : C.verts[orbitLen (stepPerm m) (oddV C.head) - 1]'(by rw [C.verts_length]; omega) =
            C.mid[orbitLen (stepPerm m) (oddV C.head) - 1]'(by unfold Clow.len at hlt; omega) := by
          unfold Clow.verts; rw [List.getElem_append_left (by unfold Clow.len at hlt; omega)]
        rw [← hmid_val, hget]; exact List.getElem_mem _
      have hgt := C.mid_gt (oddV C.head) hmem_mid
      simp at hgt
    have hverts_eq : C.verts = orbitList (stepPerm m) (oddV C.head) := by
      refine List.ext_getElem (by rw [C.verts_length, orbitList_length, hlen_eq]) fun i hi1 hi2 => ?_
      rw [C.verts_length] at hi1
      simp only [orbitList, List.getElem_map, List.getElem_range]
      exact hpow i hi1
    refine ⟨hverts_eq, fun w hw => ?_⟩
    rw [← hverts_eq] at hw
    exact C.head_le_pairOf_verts hw
  -- Helper: two vertices in the same orbit have the same orbitList (up to mem)
  have horbit_same : ∀ (m : OrderedPairing k) (u v : Fin (2 * k)),
      v ∈ orbitList (stepPerm m) u →
      ∀ w, w ∈ orbitList (stepPerm m) v ↔ w ∈ orbitList (stepPerm m) u := by
    intro m u v hv w
    rw [orbitList_mem_iff] at hv ⊢
    rw [orbitList_mem_iff]
    rcases hv with ⟨a, rfl⟩
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b + a, by rw [pow_add, Equiv.Perm.mul_apply]⟩
    · rintro ⟨c, rfl⟩
      let L := orbitLen (stepPerm m) u
      have hL : 0 < L := orbitLen_pos _ _
      -- Choose b ≡ c - a (mod L)
      let b := (L - a % L + c)
      refine ⟨b, ?_⟩
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      have hmod_eq : (b + a) % L = c % L := by
        have hlt : a % L < L := Nat.mod_lt a hL
        have h2 : b + a = L * (a / L + 1) + c := by
          dsimp [b]
          calc
            L - a % L + c + a = (L - a % L) + (L * (a / L) + a % L) + c := by
              rw [Nat.div_add_mod]; ring
            _ = L * (a / L) + L + c := by omega
            _ = L * (a / L + 1) + c := by ring
        rw [h2, Nat.mul_add_mod]
      have hpow_mod : ∀ n : ℕ, ((stepPerm m) ^ n) u = ((stepPerm m) ^ (n % L)) u := by
        intro n
        have hloop : ∀ q : ℕ, ((stepPerm m) ^ (L * q + n % L)) u = ((stepPerm m) ^ (n % L)) u := by
          intro q
          induction q with
          | zero => simp
          | succ q ih =>
            have : L * (q + 1) + n % L = L * q + n % L + L := by ring
            rw [this, pow_add, Equiv.Perm.mul_apply, orbitLen_pow, ih]
        rw [← hloop (n / L), Nat.div_add_mod]
      rw [hpow_mod (b + a), hpow_mod c, hmod_eq]
  -- Helper: mate conjugates orbit of u to orbit of mate u
  have horbit_mate : ∀ (m : OrderedPairing k) (u w : Fin (2 * k)),
      w ∈ orbitList (stepPerm m) (mate u) ↔ mate w ∈ orbitList (stepPerm m) u := by
    intro m u w
    rw [orbitList_mem_iff, orbitList_mem_iff]
    constructor
    · rintro ⟨n, rfl⟩
      -- (step^n) (mate u) = mate ((step⁻¹)^n u)
      let L := orbitLen (stepPerm m) u
      have hL : 0 < L := orbitLen_pos _ _
      refine ⟨(L - n % L) % L, ?_⟩
      have hstep : mate (((stepPerm m) ^ n) (mate u)) = (((stepPerm m)⁻¹) ^ n) u := by
        rw [mate_stepPerm_pow, mate_mate]
      rw [hstep]
      have hinv : (((stepPerm m) ^ (L * (n / L + 1))) u) = u := by
        have hloop : ∀ q : ℕ, ((stepPerm m) ^ (L * q)) u = u := by
          intro q; induction q with
          | zero => simp
          | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, orbitLen_pow, ih]
        exact hloop _
      have hmul : ((stepPerm m) ^ n) (((stepPerm m) ^ (L - n % L)) u) = u := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        have hlt : n % L < L := Nat.mod_lt n hL
        have hsum : n + (L - n % L) = L * (n / L + 1) := by
          calc
            n + (L - n % L) = (L * (n / L) + n % L) + (L - n % L) := by rw [Nat.div_add_mod]
            _ = L * (n / L) + L := by omega
            _ = L * (n / L + 1) := by ring
        rw [hsum, hinv]
      have hpow_mod : ∀ x : ℕ, ((stepPerm m) ^ (x % L)) u = ((stepPerm m) ^ x) u := by
        intro x
        have hloop : ∀ q : ℕ, ((stepPerm m) ^ (L * q + x % L)) u = ((stepPerm m) ^ (x % L)) u := by
          intro q; induction q with
          | zero => simp
          | succ q ih =>
            have : L * (q + 1) + x % L = L * q + x % L + L := by ring
            rw [this, pow_add, Equiv.Perm.mul_apply, orbitLen_pow, ih]
        rw [← hloop (x / L), Nat.div_add_mod]
      rw [hpow_mod]
      have := congrArg (((stepPerm m)⁻¹) ^ n) hmul
      rw [← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply] at this
      exact this
    · rintro ⟨n, h⟩
      have h1 : mate w = ((stepPerm m) ^ n) u := h.symm
      have h2 : w = (((stepPerm m)⁻¹) ^ n) (mate u) := by
        rw [← mate_stepPerm_pow, ← h1, mate_mate]
      let L := orbitLen (stepPerm m) (mate u)
      have hL : 0 < L := orbitLen_pos _ _
      refine ⟨L - n % L, ?_⟩
      have hloop : ∀ q : ℕ, ((stepPerm m) ^ (L * q)) (mate u) = mate u := by
        intro q; induction q with
        | zero => simp
        | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, orbitLen_pow, ih]
      have hmul : ((stepPerm m) ^ n) (((stepPerm m) ^ (L - n % L)) (mate u)) = mate u := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        have hlt : n % L < L := Nat.mod_lt n hL
        have hsum : n + (L - n % L) = L * (n / L + 1) := by
          calc
            n + (L - n % L) = (L * (n / L) + n % L) + (L - n % L) := by rw [Nat.div_add_mod]
            _ = L * (n / L) + L := by omega
            _ = L * (n / L + 1) := by ring
        rw [hsum, hloop]
      rw [h2]
      have := congrArg (((stepPerm m)⁻¹) ^ n) hmul
      rw [← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply] at this
      exact this
  -- Injectivity of simpleToPairing
  constructor
  · intro W₁ W₂ heq
    have hheads : W₁.1.clows.map Clow.head = W₂.1.clows.map Clow.head := by
      -- Both lists are strictly increasing and equal as sets to {c | IsHead (simpleToPairing W₁) c}
      have hset : ∀ (W : {W : ClowSeq k // IsSimpleSeq W}) (c : Fin k),
          c ∈ W.1.clows.map Clow.head ↔ IsHead (simpleToPairing W) c := by
        intro W c
        constructor
        · intro hc
          rcases List.mem_map.mp hc with ⟨C, hC, rfl⟩
          exact (hclow_eq_orbit W C hC).2
        · intro hhead
          -- Since W is simple of total length k, pair c appears in some clow C of W
          have hcard : (clowsPairs W.1.clows).length = k := by
            unfold clowsPairs
            have : (clowsToSteps W.1.clows).length = (W.1.clows.flatMap Clow.verts).length := by
              unfold clowsToSteps
              induction W.1.clows with
              | nil => rfl
              | cons X xs ih => simp [List.flatMap_cons, ih]
            rw [List.length_map, ← this, clowsToSteps_length, W.1.total_len]
          have hmem_c : c ∈ clowsPairs W.1.clows := by
            have hto : (clowsPairs W.1.clows).toFinset = Finset.univ := by
              apply Finset.eq_univ_of_card
              rw [List.toFinset_card_of_nodup W.2, hcard, Fintype.card_fin]
            have : c ∈ (clowsPairs W.1.clows).toFinset := by rw [hto]; exact Finset.mem_univ c
            exact List.mem_toFinset.mp this
          rcases List.mem_map.mp hmem_c with ⟨v, hv, hpc⟩
          rcases List.mem_flatMap.mp hv with ⟨C, hC, hvC⟩
          have hC_orb := (hclow_eq_orbit W C hC).1
          rw [hC_orb] at hvC
          have hle1 : C.head ≤ c := by rw [← hpc]; exact C.head_le_pairOf_verts (by rwa [hC_orb])
          -- v is either oddV c or evenV c = mate (oddV c)
          rcases eq_evenV_or_oddV v with hve | hvo
          · rw [hpc] at hve; subst hve
            -- evenV c ∈ orbit of oddV C.head => oddV c ∈ orbit of evenV C.head => evenV C.head ∈ orbit of oddV c
            have h1 : mate (evenV c) ∈ orbitList (stepPerm (simpleToPairing W)) (mate (oddV C.head)) :=
              (horbit_mate _ _ _).mpr (by simpa using hvC)
            rw [mate_evenV, mate_oddV] at h1
            have h2 : evenV C.head ∈ orbitList (stepPerm (simpleToPairing W)) (oddV c) :=
              (horbit_same _ _ _ h1 (evenV C.head)).mpr (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩)
            have hle2 : c ≤ C.head := by simpa using hhead (evenV C.head) h2
            have heqc : C.head = c := le_antisymm hle1 hle2
            rw [← heqc]; exact List.mem_map_of_mem hC
          · rw [hpc] at hvo; subst hvo
            have h2 : oddV C.head ∈ orbitList (stepPerm (simpleToPairing W)) (oddV c) :=
              (horbit_same _ _ _ hvC (oddV C.head)).mpr (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩)
            have hle2 : c ≤ C.head := by simpa using hhead (oddV C.head) h2
            have heqc : C.head = c := le_antisymm hle1 hle2
            rw [← heqc]; exact List.mem_map_of_mem hC
      -- Two strictly increasing lists with the same membership are equal
      have hmem_eq : ∀ c, c ∈ W₁.1.clows.map Clow.head ↔ c ∈ W₂.1.clows.map Clow.head := by
        intro c; rw [hset W₁ c, hset W₂ c, heq]
      exact pairwise_lt_eq_of_mem_iff W₁.1.heads_strict W₂.1.heads_strict hmem_eq
    -- Now reconstruct each clow from its head via hclow_eq_orbit
    apply Subtype.ext
    apply ClowSeq.ext
    refine List.ext_getElem (by have := congrArg List.length hheads; simpa using this) fun i hi1 hi2 => ?_
    have hhi : W₁.1.clows[i].head = W₂.1.clows[i].head := by
      have := congrArg (fun l => l[i]?) hheads
      simpa [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using this
    have hv1 := (hclow_eq_orbit W₁ W₁.1.clows[i] (List.getElem_mem hi1)).1
    have hv2 := (hclow_eq_orbit W₂ W₂.1.clows[i] (List.getElem_mem hi2)).1
    rw [← heq, ← hhi] at hv2
    have hveq : W₁.1.clows[i].verts = W₂.1.clows[i].verts := hv1.trans hv2.symm
    apply Clow.ext hhi
    have := congrArg List.dropLast hveq
    simpa [Clow.verts] using this
  -- Surjectivity of simpleToPairing
  · intro m
    -- Collect all canonical heads c ∈ Fin k with IsHead m c in increasing order
    let heads : List (Fin k) := (List.finRange k).filter (fun c => decide (IsHead m c))
    have hheads_strict : heads.Pairwise (· < ·) := by
      have hfr : (List.finRange k).Pairwise (· < ·) :=
        List.pairwise_lt_finRange k
      exact hfr.filter _
    have horb_ne_fn : ∀ c : Fin k, orbitList (stepPerm m) (oddV c) ≠ [] := by
      intro c h0
      have hlen := congrArg List.length h0
      rw [orbitList_length, List.length_nil] at hlen
      have := orbitLen_pos (stepPerm m) (oddV c); omega
    have horb_last_fn : ∀ c : Fin k,
        (orbitList (stepPerm m) (oddV c)).getLast (horb_ne_fn c) = oddV c := by
      intro c
      rw [List.getLast_eq_getElem]
      have hlen : (orbitList (stepPerm m) (oddV c)).length = orbitLen (stepPerm m) (oddV c) :=
        orbitList_length _ _
      simp only [orbitList, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      rw [Nat.sub_add_cancel (orbitLen_pos _ _), orbitLen_pow]
    let mkClow (c : Fin k) (hc : IsHead m c) : Clow k :=
      let orb := orbitList (stepPerm m) (oddV c)
      have hrecons : orb.dropLast ++ [oddV c] = orb := by
        simpa [horb_last_fn c] using List.dropLast_append_getLast (horb_ne_fn c)
      have hnd : (orb.map pairOf).Nodup := orbitList_stepPerm_pairOf_nodup m (oddV c)
      {
        head := c
        mid := orb.dropLast
        mid_gt := by
          intro w hw
          have hw_orb : w ∈ orb := by rw [← hrecons]; exact List.mem_append_left _ hw
          have hle : c ≤ pairOf w := hc w hw_orb
          have hne : pairOf w ≠ c := by
            intro heq
            rw [← hrecons, List.map_append, List.map_singleton, List.nodup_append] at hnd
            exact hnd.2.2 (pairOf w) (List.mem_map_of_mem hw) (pairOf (oddV c))
              (List.mem_singleton_self _) (by rw [heq, pairOf_oddV])
          exact lt_of_le_of_ne hle hne.symm
      }
    have hmkClow_verts : ∀ c hc, (mkClow c hc).verts = orbitList (stepPerm m) (oddV c) := by
      intro c hc
      unfold mkClow Clow.verts; dsimp only
      simpa [horb_last_fn c] using List.dropLast_append_getLast (horb_ne_fn c)
    let cs : List (Clow k) :=
      heads.pmap (fun c (hc : IsHead m c) => mkClow c hc)
        (fun c hc => of_decide_eq_true (List.mem_filter.mp hc).2)
    have hcs_heads : cs.map Clow.head = heads := by
      simp [cs, List.map_pmap, mkClow]
    -- Show clowsPairs cs is Nodup and covers every p : Fin k
    have hcs_pairs_nodup : TailClean cs := by
      unfold TailClean clowsPairs
      -- Pairwise disjoint orbits for distinct heads
      have hdisj : ∀ c₁ c₂, IsHead m c₁ → IsHead m c₂ → c₁ ≠ c₂ →
          ∀ p, p ∈ (orbitList (stepPerm m) (oddV c₁)).map pairOf →
               p ∉ (orbitList (stepPerm m) (oddV c₂)).map pairOf := by
        intro c₁ c₂ h1 h2 hne p hp1 hp2
        rcases List.mem_map.mp hp1 with ⟨v₁, hv1, rfl⟩
        rcases List.mem_map.mp hp2 with ⟨v₂, hv2, hpeq⟩
        rcases pairOf_eq_iff.mp hpeq with hveq | hveq
        · subst hveq
          have h12 : oddV c₁ ∈ orbitList (stepPerm m) (oddV c₂) :=
            (horbit_same _ _ _ hv2 _).mp ((horbit_same _ _ _ hv1 _).mpr (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩))
          have h21 : oddV c₂ ∈ orbitList (stepPerm m) (oddV c₁) :=
            (horbit_same _ _ _ hv1 _).mp ((horbit_same _ _ _ hv2 _).mpr (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩))
          have hle1 : c₂ ≤ c₁ := by simpa using h2 (oddV c₁) h12
          have hle2 : c₁ ≤ c₂ := by simpa using h1 (oddV c₂) h21
          exact hne (le_antisymm hle2 hle1)
        · have hv2m : v₂ ∈ orbitList (stepPerm m) (mate (oddV c₁)) := by
            rw [horbit_mate, hveq, mate_mate]; exact hv1
          have h12 : evenV c₁ ∈ orbitList (stepPerm m) (oddV c₂) :=
            (horbit_same _ _ _ hv2 _).mp ((horbit_same _ _ _ hv2m _).mpr
              (by rw [mate_oddV, orbitList_mem_iff]; exact ⟨0, rfl⟩))
          have h21 : evenV c₂ ∈ orbitList (stepPerm m) (oddV c₁) := by
            have hm1 : mate (oddV c₂) ∈ orbitList (stepPerm m) (mate (mate (oddV c₁))) :=
              (horbit_mate _ _ _).mpr ((horbit_same _ _ _ hv2m _).mp ((horbit_same _ _ _ hv2 _).mpr
                (by rw [orbitList_mem_iff]; exact ⟨0, by simp⟩)))
            simpa using hm1
          have hle1 : c₂ ≤ c₁ := by simpa using h2 (evenV c₁) h12
          have hle2 : c₁ ≤ c₂ := by simpa using h1 (evenV c₂) h21
          exact hne (le_antisymm hle2 hle1)
      -- Prove nodup by induction on a nodup sublist of heads
      suffices ∀ (hs : List (Fin k)) (hnd : hs.Nodup) (hh : ∀ c ∈ hs, IsHead m c),
          ((hs.pmap (fun c (hc : IsHead m c) => mkClow c hc) hh).flatMap Clow.verts |>.map pairOf).Nodup from
        this heads (hheads_strict.imp ne_of_lt) (fun c hc => of_decide_eq_true (List.mem_filter.mp hc).2)
      intro hs
      induction hs with
      | nil => intro _ _; simp
      | cons c rest ih =>
        intro hnd hh
        rw [List.nodup_cons] at hnd
        simp only [List.pmap, List.flatMap_cons, List.map_append, List.nodup_append, hmkClow_verts]
        refine ⟨orbitList_stepPerm_pairOf_nodup m (oddV c),
          ih hnd.2 (fun d hd => hh d (List.mem_cons_of_mem _ hd)), ?_⟩
        intro p hp1 q hq2 heq
        subst heq
        rcases List.mem_map.mp hq2 with ⟨w, hw, rfl⟩
        rcases List.mem_flatMap.mp hw with ⟨D, hD, hwD⟩
        rcases List.mem_pmap.mp hD with ⟨d, hd, rfl⟩
        have hhd : IsHead m d := hh d (List.mem_cons_of_mem _ hd)
        rw [hmkClow_verts d hhd] at hwD
        exact hdisj c d (hh c List.mem_cons_self) hhd
          (fun he => hnd.1 (he ▸ hd)) (pairOf w) hp1 (List.mem_map_of_mem hwD)
    have hcs_pairs_cover : ∀ p : Fin k, p ∈ clowsPairs cs := by
      intro p
      -- Consider orbit of oddV p; take its minimum pair c
      set orb := orbitList (stepPerm m) (oddV p)
      have horb_ne : orb ≠ [] := horb_ne_fn p
      let c := minPair orb horb_ne
      rcases List.mem_map.mp (minPair_mem orb horb_ne) with ⟨v, hv, hvc⟩
      rcases eq_evenV_or_oddV v with hve | hvo
      · rw [hvc] at hve; subst hve
        -- evenV c ∈ orbit of oddV p => oddV c ∈ orbit of evenV p, and IsHead m c!
        have hhead_c : IsHead m c := by
          intro w hw
          have hmw : mate w ∈ orb := by
            have h1 : w ∈ orbitList (stepPerm m) (mate (evenV c)) := by simpa using hw
            have h2 := (horbit_mate m (evenV c) w).mp h1
            exact (horbit_same m (oddV p) (evenV c) hv (mate w)).mp h2
          simpa using minPair_le orb horb_ne hmw
        have hc_mem : c ∈ heads := List.mem_filter.mpr ⟨List.mem_finRange c, decide_eq_true hhead_c⟩
        have hD_mem : mkClow c hhead_c ∈ cs :=
          List.mem_pmap.mpr ⟨c, hc_mem, rfl⟩
        have hp_in_c : evenV p ∈ orbitList (stepPerm m) (oddV c) := by
          have h1 : evenV p = mate (oddV p) := (mate_oddV p).symm
          rw [h1, ← mate_evenV c]
          rw [horbit_mate, mate_mate]
          exact (horbit_same m (oddV p) (evenV c) hv (oddV p)).mpr
            (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩)
        unfold clowsPairs
        refine List.mem_map.mpr ⟨evenV p, List.mem_flatMap.mpr ⟨mkClow c hhead_c, hD_mem, ?_⟩, by simp⟩
        rwa [hmkClow_verts]
      · rw [hvc] at hvo; subst hvo
        have hhead_c : IsHead m c := by
          intro w hw
          have hw' : w ∈ orb := (horbit_same m (oddV p) (oddV c) hv w).mp hw
          exact minPair_le orb horb_ne hw'
        have hc_mem : c ∈ heads := List.mem_filter.mpr ⟨List.mem_finRange c, decide_eq_true hhead_c⟩
        have hD_mem : mkClow c hhead_c ∈ cs :=
          List.mem_pmap.mpr ⟨c, hc_mem, rfl⟩
        have hp_in_c : oddV p ∈ orbitList (stepPerm m) (oddV c) :=
          (horbit_same m (oddV p) (oddV c) hv (oddV p)).mpr
            (by rw [orbitList_mem_iff]; exact ⟨0, rfl⟩)
        unfold clowsPairs
        refine List.mem_map.mpr ⟨oddV p, List.mem_flatMap.mpr ⟨mkClow c hhead_c, hD_mem, ?_⟩, by simp⟩
        rwa [hmkClow_verts]
    have hcs_len : (cs.map Clow.len).sum = k := by
      have hcard : (clowsPairs cs).length = k := by
        have hto : (clowsPairs cs).toFinset = Finset.univ := by
          ext p; simp [hcs_pairs_cover p]
        have := congrArg Finset.card hto
        rw [List.toFinset_card_of_nodup hcs_pairs_nodup, Finset.card_univ, Fintype.card_fin] at this
        exact this
      have hflat : (cs.flatMap Clow.verts).length = (cs.map Clow.len).sum := by
        suffices ∀ ds : List (Clow k), (ds.flatMap Clow.verts).length = (ds.map Clow.len).sum from this cs
        intro ds; induction ds with
        | nil => rfl
        | cons X xs ih => simp [List.flatMap_cons, Clow.verts_length, ih]
      rw [← hflat]
      simpa [clowsPairs] using hcard
    let W : ClowSeq k := {
      clows := cs
      heads_strict := by rw [hcs_heads]; exact hheads_strict
      total_len := hcs_len
    }
    refine ⟨⟨W, hcs_pairs_nodup⟩, ?_⟩
    -- Prove simpleToPairing ⟨W, hcs_pairs_nodup⟩ = m via edgeFinset_injective!
    apply OrderedPairing.edgeFinset_injective
    rw [simpleToPairing_edgeFinset]
    -- Show permEdgeFinset (clowPerm W) = m.edgeFinset (same card k, show subset!)
    have hsub : permEdgeFinset (clowPerm W hcs_pairs_nodup) ⊆ m.edgeFinset := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨t, _, rfl⟩
      -- Find which clow C in W.clows contains index t
      have hfind : ∃ (l1 l2 : List (Clow k)) (C : Clow k) (r : ℕ),
          W.clows = l1 ++ (C :: l2) ∧ r < C.len ∧ t.val = (l1.map Clow.len).sum + r := by
        have ht : t.val < (W.clows.map Clow.len).sum := by rw [W.total_len]; exact t.isLt
        suffices ∀ (ds : List (Clow k)) (n : ℕ), n < (ds.map Clow.len).sum →
            ∃ (l1 l2 : List (Clow k)) (C : Clow k) (r : ℕ),
              ds = l1 ++ (C :: l2) ∧ r < C.len ∧ n = (l1.map Clow.len).sum + r from
          this W.clows t.val ht
        intro ds
        induction ds with
        | nil => intro n hn; simp at hn
        | cons C ds ih =>
          intro n hn
          simp only [List.map_cons, List.sum_cons] at hn
          by_cases htr : n < C.len
          · exact ⟨[], ds, C, n, rfl, htr, by simp⟩
          · rcases ih (n - C.len) (by omega) with ⟨l1, l2, D, r, hds, hr, hval⟩
            exact ⟨C :: l1, l2, D, r, by simp [hds], hr, by
              simp only [List.map_cons, List.sum_cons]; omega⟩
      rcases hfind with ⟨l1, l2, C, r, hcl, hr, htval⟩
      -- Since C ∈ cs, C.verts = orbitList (stepPerm m) (oddV C.head)
      have hC_mem : C ∈ cs := by change C ∈ W.clows; rw [hcl]; simp
      rcases List.mem_pmap.mp hC_mem with ⟨c, hc, rfl⟩
      set C0 := mkClow c (of_decide_eq_true (List.mem_filter.mp hc).2)
      have hcur_eq_step :
          stepPerm m (C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
              rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)) =
            C0.verts[r]'(by rw [C0.verts_length]; exact hr) := by
        have hv0 := hmkClow_verts c (of_decide_eq_true (List.mem_filter.mp hc).2)
        have hlen0 : C0.len = orbitLen (stepPerm m) (oddV c) := by
          rw [← C0.verts_length, hv0, orbitList_length]
        have hget : ∀ (j : ℕ) (hj : j < C0.len),
            C0.verts[j]'(by rw [C0.verts_length]; exact hj) =
              ((stepPerm m) ^ (j + 1)) (oddV c) := by
          intro j hj
          have : ∀ (xs : List (Fin (2 * k))) (h : xs = orbitList (stepPerm m) (oddV c)) (h1 : j < xs.length),
              xs[j]'h1 = ((stepPerm m) ^ (j + 1)) (oddV c) := by
            intro xs h h1; subst h; simp [orbitList]
          exact this C0.verts hv0 _
        rw [hget _ (by unfold Clow.len at hr ⊢; split_ifs <;> omega), hget r hr]
        by_cases hr0 : r = 0
        · simp only [hr0, ↓reduceIte]
          rw [Nat.sub_add_cancel (by unfold Clow.len; omega), hlen0, orbitLen_pow, pow_one]
        · simp only [hr0, ↓reduceIte]
          rw [Nat.sub_add_cancel (by omega), ← Equiv.Perm.mul_apply, ← pow_succ']
      -- Match clowPerm edge with s(mate prev, cur)
      have hedge_eq :
          s(clowPerm W hcs_pairs_nodup (evenV t), clowPerm W hcs_pairs_nodup (oddV t)) =
            s(mate (C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
                rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)),
              C0.verts[r]'(by rw [C0.verts_length]; exact hr)) := by
        set a := (l1.map Clow.len).sum
        have ha_le : a + C0.len ≤ k := by
          have htot := W.total_len; rw [hcl] at htot
          simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htot
          dsimp [a]; omega
        set verts := W.clows.flatMap Clow.verts
        have hlen_l1 : (l1.flatMap Clow.verts).length = a := by
          dsimp [a]
          suffices ∀ ds : List (Clow k), (ds.flatMap Clow.verts).length = (ds.map Clow.len).sum from this l1
          intro ds; induction ds with
          | nil => rfl
          | cons X xs ih => simp [List.flatMap_cons, Clow.verts_length, ih]
        have hlen_all : verts.length = k := by
          have : (clowsToSteps W.clows).length = verts.length := by
            unfold clowsToSteps verts
            induction W.clows with
            | nil => rfl
            | cons X xs ih => simp [List.flatMap_cons, ih]
          rw [← this, clowsToSteps_length, W.total_len]
        have hverts_get : ∀ (j : ℕ) (hj : j < C0.len),
            verts[a + j]'(by rw [hlen_all]; omega) = C0.verts[j]'(by rw [C0.verts_length]; exact hj) := by
          intro j hj
          have hv_eq : verts = l1.flatMap Clow.verts ++ (C0.verts ++ l2.flatMap Clow.verts) := by
            dsimp [verts]; rw [hcl]; simp [List.flatMap_append, List.flatMap_cons]
          have hget : ∀ (xs : List (Fin (2 * k))) (h : xs = l1.flatMap Clow.verts ++ (C0.verts ++ l2.flatMap Clow.verts))
              (h1 : a + j < xs.length),
              xs[a + j]'h1 = C0.verts[j]'(by rw [C0.verts_length]; exact hj) := by
            intro xs h h1; subst h
            rw [List.getElem_append_right (by omega)]
            simp only [hlen_l1, Nat.add_sub_cancel_left]
            rw [List.getElem_append_left (by rw [C0.verts_length]; exact hj)]
          exact hget verts hv_eq _
        have hshift_split : ∀ (b : ℕ) (xs ys : List (Clow k)) (hb : b + ((xs ++ ys).map Clow.len).sum ≤ k),
            shiftClows b (xs ++ ys) hb =
              shiftClows b xs (by simp at hb; omega) *
                shiftClows (b + (xs.map Clow.len).sum) ys (by simp at hb; omega) := by
          intro b xs ys
          induction xs generalizing b with
          | nil => intro hb; simp [shiftClows]
          | cons X xs ih =>
            intro hb
            simp only [List.cons_append, shiftClows, mul_assoc]
            congr 1
            have hsum : b + X.len + (xs.map Clow.len).sum = b + ((X :: xs).map Clow.len).sum := by
              simp [Nat.add_assoc]
            have hb' : b + X.len + ((xs ++ ys).map Clow.len).sum ≤ k := by
              simp only [List.cons_append, List.map_cons, List.sum_cons] at hb; omega
            rw [ih (b + X.len) hb']
            congr 1
            have hcongr : ∀ (n₁ n₂ : ℕ) (he : n₁ = n₂)
                (h1 : n₁ + (ys.map Clow.len).sum ≤ k) (h2 : n₂ + (ys.map Clow.len).sum ≤ k),
                shiftClows n₁ ys h1 = shiftClows n₂ ys h2 := by
              rintro n₁ _ rfl _ _; rfl
            exact hcongr _ _ hsum _ _
        have ht_eq : t = ⟨a + r, by omega⟩ := Fin.ext htval
        have hshift_t : shiftClows 0 W.clows (by rw [zero_add, W.total_len]) (evenV t) =
            evenV ⟨a + (if r = 0 then C0.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
          have h0 : ∀ (ds : List (Clow k)) (hds : ds = l1 ++ (C0 :: l2))
              (hb : 0 + (ds.map Clow.len).sum ≤ k),
              shiftClows 0 ds hb (evenV t) =
                evenV ⟨a + (if r = 0 then C0.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
            intro ds hds hb; subst hds
            rw [hshift_split 0 l1 (C0 :: l2) hb, Equiv.Perm.mul_apply]
            have hba : a + ((C0 :: l2).map Clow.len).sum ≤ k := by
              simp only [List.map_append, List.sum_append, zero_add] at hb; dsimp [a]; omega
            have hstep : shiftClows a (C0 :: l2) hba (evenV t) =
                evenV ⟨a + (if r = 0 then C0.len - 1 else r - 1), by split_ifs <;> omega⟩ := by
              simp only [shiftClows, Equiv.Perm.mul_apply]
              have hba2 : a + C0.len + (l2.map Clow.len).sum ≤ k := by
                simp only [List.map_cons, List.sum_cons] at hba; omega
              rw [shiftClows_evenV_outside (a + C0.len) l2 hba2 t (Or.inl (by rw [htval]; omega))]
              conv_lhs => arg 2; rw [ht_eq]
              rw [shiftBlock_evenV_inside a C0.len (by unfold Clow.len; omega) ha_le r hr]
              congr 1; apply Fin.ext; dsimp only; split_ifs <;> omega
            have heq_shift : shiftClows (0 + (l1.map Clow.len).sum) (C0 :: l2) (by simp at hb; omega) =
                shiftClows a (C0 :: l2) hba := by
              congr 1; simp [a]
            rw [heq_shift, hstep]
            exact shiftClows_evenV_outside 0 l1 (by simp at hb; omega) _
              (Or.inr (by dsimp [a]; split_ifs <;> omega))
          exact h0 W.clows hcl (by rw [zero_add, W.total_len])
        have hclow_even : clowPerm W hcs_pairs_nodup (evenV t) =
            mate (C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
              rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)) := by
          unfold clowPerm
          simp only [Equiv.Perm.mul_apply]
          rw [hshift_t]
          set s : Fin k := ⟨a + (if r = 0 then C0.len - 1 else r - 1), by split_ifs <;> omega⟩
          have hws_s : verts[s.val]'(by rw [hlen_all]; exact s.isLt) =
              C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
                rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega) :=
            hverts_get _ (by unfold Clow.len at hr ⊢; split_ifs <;> omega)
          dsimp [flipPairs]
          by_cases he : ((W.clows.flatMap Clow.verts)[s.val]'(by rw [hlen_all]; exact s.isLt)).val % 2 = 0
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
              mate_evenV, liftPairPerm_oddV]
            change oddV (pairOf (verts[s.val]'_)) = _
            have he' : (C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
                rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)).val % 2 = 0 := by
              rw [← hws_s]; exact he
            rw [hws_s]; ext; dsimp [oddV, mate, pairOf]; simp [he']; omega
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_evenV, he, ↓reduceIte,
              liftPairPerm_evenV]
            change evenV (pairOf (verts[s.val]'_)) = _
            have he' : (C0.verts[if r = 0 then C0.len - 1 else r - 1]'(by
                rw [C0.verts_length]; unfold Clow.len at hr ⊢; split_ifs <;> omega)).val % 2 ≠ 0 := by
              rw [← hws_s]; exact he
            rw [hws_s]; ext; dsimp [evenV, mate, pairOf]; simp [he']; omega
        have hclow_odd : clowPerm W hcs_pairs_nodup (oddV t) =
            C0.verts[r]'(by rw [C0.verts_length]; exact hr) := by
          unfold clowPerm
          simp only [Equiv.Perm.mul_apply, shiftClows_oddV]
          have hws_t : verts[t.val]'(by rw [hlen_all]; exact t.isLt) =
              C0.verts[r]'(by rw [C0.verts_length]; exact hr) := by
            rw [ht_eq]; exact hverts_get r hr
          dsimp [flipPairs]
          by_cases he : ((W.clows.flatMap Clow.verts)[t.val]'(by rw [hlen_all]; exact t.isLt)).val % 2 = 0
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
              mate_oddV, liftPairPerm_evenV]
            change evenV (pairOf (verts[t.val]'_)) = _
            have he' : (C0.verts[r]'(by rw [C0.verts_length]; exact hr)).val % 2 = 0 := by
              rw [← hws_t]; exact he
            rw [hws_t]; ext; dsimp [evenV, pairOf]; omega
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairOf_oddV, he, ↓reduceIte,
              liftPairPerm_oddV]
            change oddV (pairOf (verts[t.val]'_)) = _
            have he' : (C0.verts[r]'(by rw [C0.verts_length]; exact hr)).val % 2 ≠ 0 := by
              rw [← hws_t]; exact he
            rw [hws_t]; ext; dsimp [oddV, pairOf]; omega
        rw [hclow_even, hclow_odd]
      rw [hedge_eq, ← matchMateEquiv_eq_iff_mem_edgeFinset]
      exact hcur_eq_step
    -- Both finsets have card k, so subset implies equality!
    apply Finset.eq_of_subset_of_card_le hsub
    have hcard_m : m.edgeFinset.card = k := by
      rw [OrderedPairing.edgeFinset_eq, Finset.card_image_of_injective _ m.edge_injective,
          Finset.card_fin]
    have hcard_p : (permEdgeFinset (clowPerm W hcs_pairs_nodup)).card = k := by
      unfold permEdgeFinset
      rw [Finset.card_image_of_injective, Finset.card_fin]
      intro t₁ t₂ heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact evenV_injective ((clowPerm W hcs_pairs_nodup).injective h1)
      · exact absurd ((clowPerm W hcs_pairs_nodup).injective h1) (evenV_ne_oddV_any _ _)
    omega

/-- Sum of `clowSeqWeight A W` over all simple `W : ClowSeq k` equals `pfaffian A`. -/
theorem sum_simple_eq_pfaffian {k : ℕ} {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A) :
    ∑ W ∈ Finset.univ.filter (fun W : ClowSeq k => IsSimpleSeq W), clowSeqWeight A W =
      pfaffian A := by
  have hsub :
      ∑ W ∈ Finset.univ.filter (fun W : ClowSeq k => IsSimpleSeq W), clowSeqWeight A W =
        ∑ W : {W : ClowSeq k // IsSimpleSeq W}, clowSeqWeight A W.1 := by
    refine Finset.sum_bij (fun W hW => ⟨W, (Finset.mem_filter.mp hW).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun W _ => ⟨W.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, W.2⟩, rfl⟩)
      (fun _ _ => rfl)
  rw [hsub]
  let e : {W : ClowSeq k // IsSimpleSeq W} ≃ OrderedPairing k :=
    Equiv.ofBijective (simpleToPairing (k := k)) (simpleToPairing_bijective k)
  unfold pfaffian
  refine Fintype.sum_equiv e _ _ fun W => ?_
  change clowSeqWeight A W.1 =
    ((simpleToPairing W).sign : R) *
      ∏ i : Fin k, A ((simpleToPairing W).fst i) ((simpleToPairing W).snd i)
  rw [← clowPerm_weight_eq A W.1 W.2]
  refine perm_pfaffian_term_eq hA (simpleToPairing W) (clowPerm W.1 W.2) fun i => ?_
  rw [simpleToPairing_edgeFinset]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- **Main Algebraic Theorem (`[MSV04]`):** for every `k ≥ 1` and every skew-symmetric `(2k)×(2k)`
matrix `A` over a commutative ring `R`, the 3-index DP output `dpAns A` equals `pfaffian A`. -/
theorem dpAns_eq_pfaffian {k : ℕ} (hk : 1 ≤ k) {R : Type*} [CommRing R]
    {A : Matrix (Fin (2 * k)) (Fin (2 * k)) R} (hA : IsSkewSymm A) :
    dpAns A = pfaffian A := by
  rw [dpAns_eq_sum_clowSeq hk A]
  have hpart : (Finset.univ : Finset (ClowSeq k)) =
      Finset.univ.filter (fun W : ClowSeq k => IsSimpleSeq W) ∪
      Finset.univ.filter (fun W : ClowSeq k => ¬ IsSimpleSeq W) := by
    ext W; simp [em]
  have hdisj : Disjoint
      (Finset.univ.filter (fun W : ClowSeq k => IsSimpleSeq W))
      (Finset.univ.filter (fun W : ClowSeq k => ¬ IsSimpleSeq W)) := by
    rw [Finset.disjoint_filter]; intro W _ h1 h2; exact h2 h1
  rw [hpart, Finset.sum_union hdisj, sum_simple_eq_pfaffian hA, sum_not_simple_eq_zero hA, add_zero]

end ExactMatching.Proofs.PfaffianClow
