/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.CitedHypotheses
public import ExactMatching.Defs.Design
public import ExactMatching.Proofs.Design
public import ExactMatching.Proofs.CircuitsTransfer
public import ExactMatching.Proofs.PitBounds
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

/-!
# Proof of Lemma 2.2 (Reconstruction from NW-design vanishing via `KI04_Cor_7_4`)

Proves `lem_2_2_reconstruction_proved`: given `KI04_Cor_7_4`, a nonzero integer circuit `C_f`
and multilinear polynomial `p` whose Nisan–Wigderson composition vanishes on a grid `S^l`
with `|S| > d_f * d_p` yield a `[A26]` `ℚ`-circuit (`Computes`) for `p` of size at most `s^κ`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: Basic `Computes` and polynomial degree / L1-norm lemmas -/

theorem computes_mono {R : Type*} {V : Type} [CommSemiring R] {f : MvPolynomial V R}
    {r r' : ℕ} (h : Computes f r) (hle : r ≤ r') : Computes f r' := by
  rcases h with ⟨l, hstep, k₀, hk₀, hlk₀⟩
  refine ⟨fun k => if k < r then l k else MvPolynomial.C 0, ?_, k₀, lt_of_lt_of_le hk₀ hle, ?_⟩
  · intro k _
    by_cases hkr : k < r
    · simp only [hkr, ite_true]
      rcases hstep k hkr with h1 | h2 | ⟨i, hi, j, hj, hij⟩ | ⟨i, hi, j, hj, hij⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by
          simp only [lt_trans hi hkr, lt_trans hj hkr, ite_true]; exact hij⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by
          simp only [lt_trans hi hkr, lt_trans hj hkr, ite_true]; exact hij⟩))
    · simp only [hkr, ite_false]
      exact Or.inr (Or.inl ⟨0, rfl⟩)
  · simp only [hk₀, ite_true]; exact hlk₀

theorem computes_rename {R : Type*} {V W : Type} [CommSemiring R] (σ : V → W)
    {f : MvPolynomial V R} {r : ℕ} (h : Computes f r) :
    Computes (MvPolynomial.rename σ f) r := by
  rcases h with ⟨l, hstep, k₀, hk₀, hlk₀⟩
  refine ⟨fun k => MvPolynomial.rename σ (l k), ?_, k₀, hk₀, by dsimp only; rw [hlk₀]⟩
  intro k hk
  dsimp only
  rcases hstep k hk with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, j, hj, hij⟩ | ⟨i, hi, j, hj, hij⟩
  · exact Or.inl ⟨σ v, by rw [hv, MvPolynomial.rename_X]⟩
  · exact Or.inr (Or.inl ⟨a, by rw [ha, MvPolynomial.rename_C]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [hij, map_add]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [hij, map_mul]⟩))

private theorem totalDegree_map_le {V R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (p : MvPolynomial V R) :
    (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro d hd
  exact Finset.le_sup (f := fun d : V →₀ ℕ => d.sum fun _ e => e)
    (MvPolynomial.support_map_subset φ p hd)

private theorem eval₂_bind₁_eq {V W R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (g : V → MvPolynomial W R) (x : W → S) (f : MvPolynomial V R) :
    MvPolynomial.eval₂ φ x (MvPolynomial.bind₁ g f) =
      MvPolynomial.eval₂ φ (fun v => MvPolynomial.eval₂ φ x (g v)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.bind₁_C_right]
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ih => simp [map_mul, ih, MvPolynomial.bind₁_X_right]

private theorem bind₁_X_comp_eq_rename {V W R : Type*} [CommSemiring R]
    (σ : V → W) (f : MvPolynomial V R) :
    MvPolynomial.bind₁ (fun v => MvPolynomial.X (σ v)) f = MvPolynomial.rename σ f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.bind₁_C_right, MvPolynomial.rename_C]
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ih => simp [map_mul, ih, MvPolynomial.bind₁_X_right, MvPolynomial.rename_X]

private theorem bind₁_eq_sum {V W R : Type*} [CommSemiring R]
    (g : V → MvPolynomial W R) (f : MvPolynomial V R) :
    MvPolynomial.bind₁ g f =
      ∑ d ∈ f.support, MvPolynomial.C (f.coeff d) * ∏ v ∈ d.support, g v ^ d v := by
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rfl

theorem totalDegree_bind₁_le {V W : Type*} {R : Type*} [CommSemiring R]
    (g : V → MvPolynomial W R) (f : MvPolynomial V R) (D : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ D) :
    (MvPolynomial.bind₁ g f).totalDegree ≤ f.totalDegree * D := by
  rw [bind₁_eq_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_le_iff]
  intro d hd
  have h1 : (MvPolynomial.C (f.coeff d) * ∏ v ∈ d.support, g v ^ d v).totalDegree ≤
      (∏ v ∈ d.support, g v ^ d v).totalDegree := by
    have := MvPolynomial.totalDegree_mul (MvPolynomial.C (f.coeff d)) (∏ v ∈ d.support, g v ^ d v)
    rw [MvPolynomial.totalDegree_C, zero_add] at this
    exact this
  have h2 : (∏ v ∈ d.support, g v ^ d v).totalDegree ≤ ∑ v ∈ d.support, (g v ^ d v).totalDegree :=
    MvPolynomial.totalDegree_finsetProd _ _
  have h3 : ∑ v ∈ d.support, (g v ^ d v).totalDegree ≤ ∑ v ∈ d.support, d v * D := by
    refine Finset.sum_le_sum fun v _ => ?_
    exact le_trans (MvPolynomial.totalDegree_pow _ _) (Nat.mul_le_mul_left _ (hg v))
  have h4 : ∑ v ∈ d.support, d v * D = (d.sum fun _ e => e) * D := by
    rw [← Finset.sum_mul]; rfl
  have h5 : (d.sum fun _ e => e) ≤ f.totalDegree :=
    Finset.le_sup (f := fun d => d.sum fun _ e => e) hd
  exact le_trans h1 (le_trans h2 (le_trans h3 (by rw [h4]; exact Nat.mul_le_mul_right D h5)))

private noncomputable def polyL1 {V : Type*} (h : MvPolynomial V ℤ) : ℕ :=
  ∑ d ∈ h.support, (h.coeff d).natAbs

private theorem coeff_natAbs_le_polyL1 {V : Type*} (h : MvPolynomial V ℤ) (d : V →₀ ℕ) :
    (h.coeff d).natAbs ≤ polyL1 h := by
  unfold polyL1
  by_cases hd : d ∈ h.support
  · exact Finset.single_le_sum (f := fun e => (h.coeff e).natAbs) (fun _ _ => Nat.zero_le _) hd
  · rw [MvPolynomial.notMem_support_iff.mp hd]; simp

private theorem polyL1_zero {V : Type*} : polyL1 (0 : MvPolynomial V ℤ) = 0 := by
  simp [polyL1]

private theorem polyL1_monomial {V : Type*} (d : V →₀ ℕ) (a : ℤ) :
    polyL1 (MvPolynomial.monomial d a) = a.natAbs := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [polyL1]
  · rw [polyL1, MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton,
        MvPolynomial.coeff_monomial, if_pos rfl]

private theorem polyL1_C {V : Type*} (a : ℤ) : polyL1 (MvPolynomial.C a : MvPolynomial V ℤ) = a.natAbs := by
  rw [← MvPolynomial.monomial_zero']; exact polyL1_monomial 0 a

private theorem polyL1_X {V : Type*} (v : V) : polyL1 (MvPolynomial.X v : MvPolynomial V ℤ) = 1 := by
  rw [MvPolynomial.X]; simpa using polyL1_monomial (Finsupp.single v 1) 1

private theorem polyL1_add_le {V : Type*} (h₁ h₂ : MvPolynomial V ℤ) :
    polyL1 (h₁ + h₂) ≤ polyL1 h₁ + polyL1 h₂ := by
  classical
  unfold polyL1
  have hsub : (h₁ + h₂).support ⊆ h₁.support ∪ h₂.support := MvPolynomial.support_add
  calc
    ∑ d ∈ (h₁ + h₂).support, ((h₁ + h₂).coeff d).natAbs
        ≤ ∑ d ∈ h₁.support ∪ h₂.support, ((h₁ + h₂).coeff d).natAbs :=
          Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ d ∈ h₁.support ∪ h₂.support, ((h₁.coeff d).natAbs + (h₂.coeff d).natAbs) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [MvPolynomial.coeff_add]
          exact Int.natAbs_add_le _ _
    _ = (∑ d ∈ h₁.support ∪ h₂.support, (h₁.coeff d).natAbs) +
        (∑ d ∈ h₁.support ∪ h₂.support, (h₂.coeff d).natAbs) := Finset.sum_add_distrib
    _ = (∑ d ∈ h₁.support, (h₁.coeff d).natAbs) + (∑ d ∈ h₂.support, (h₂.coeff d).natAbs) := by
          congr 1
          · symm
            exact Finset.sum_subset Finset.subset_union_left fun d _ hd => by
              rw [MvPolynomial.notMem_support_iff.mp hd]; rfl
          · symm
            exact Finset.sum_subset Finset.subset_union_right fun d _ hd => by
              rw [MvPolynomial.notMem_support_iff.mp hd]; rfl

private theorem polyL1_finset_sum_le {ι V : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → MvPolynomial V ℤ) :
    polyL1 (∑ i ∈ s, g i) ≤ ∑ i ∈ s, polyL1 (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [polyL1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (polyL1_add_le _ _) (Nat.add_le_add_left ih _)

private theorem polyL1_mul_le {V : Type*} (h₁ h₂ : MvPolynomial V ℤ) :
    polyL1 (h₁ * h₂) ≤ polyL1 h₁ * polyL1 h₂ := by
  classical
  have hmul : h₁ * h₂ =
      ∑ d₁ ∈ h₁.support, ∑ d₂ ∈ h₂.support,
        MvPolynomial.monomial (d₁ + d₂) (h₁.coeff d₁ * h₂.coeff d₂) := by
    conv_lhs => rw [h₁.as_sum, h₂.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [MvPolynomial.monomial_mul_monomial]
  rw [hmul]
  calc
    polyL1 (∑ d₁ ∈ h₁.support, ∑ d₂ ∈ h₂.support,
        MvPolynomial.monomial (d₁ + d₂) (h₁.coeff d₁ * h₂.coeff d₂))
        ≤ ∑ d₁ ∈ h₁.support, polyL1 (∑ d₂ ∈ h₂.support,
            MvPolynomial.monomial (d₁ + d₂) (h₁.coeff d₁ * h₂.coeff d₂)) :=
          polyL1_finset_sum_le _ _
    _ ≤ ∑ d₁ ∈ h₁.support, ∑ d₂ ∈ h₂.support,
            polyL1 (MvPolynomial.monomial (d₁ + d₂) (h₁.coeff d₁ * h₂.coeff d₂)) :=
          Finset.sum_le_sum fun d₁ _ => polyL1_finset_sum_le _ _
    _ = ∑ d₁ ∈ h₁.support, ∑ d₂ ∈ h₂.support, (h₁.coeff d₁).natAbs * (h₂.coeff d₂).natAbs := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
          rw [polyL1_monomial, Int.natAbs_mul]
    _ = polyL1 h₁ * polyL1 h₂ := by
          unfold polyL1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          rw [Finset.mul_sum]

private theorem polyL1_pow_le {V : Type*} (h : MvPolynomial V ℤ) (k : ℕ) :
    polyL1 (h ^ k) ≤ polyL1 h ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    have h1 : (1 : MvPolynomial V ℤ) = MvPolynomial.C 1 := rfl
    rw [h1, polyL1_C]; decide
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (polyL1_mul_le _ _) (Nat.mul_le_mul_right _ ih)

private theorem polyL1_finset_prod_le {ι V : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → MvPolynomial V ℤ) :
    polyL1 (∏ i ∈ s, g i) ≤ ∏ i ∈ s, polyL1 (g i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    have h1 : (1 : MvPolynomial V ℤ) = MvPolynomial.C 1 := rfl
    rw [h1, polyL1_C]; decide
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (polyL1_mul_le _ _) (Nat.mul_le_mul_left _ ih)

private theorem polyL1_bind₁_le {V W : Type*} (g : V → MvPolynomial W ℤ)
    (f : MvPolynomial V ℤ) (K B df M : ℕ) (hM : 1 ≤ M)
    (hK : f.support.card ≤ K) (hB : ∀ d, (f.coeff d).natAbs ≤ B)
    (hdf : f.totalDegree ≤ df) (hg : ∀ v, polyL1 (g v) ≤ M) :
    polyL1 (MvPolynomial.bind₁ g f) ≤ K * B * M ^ df := by
  classical
  rw [bind₁_eq_sum]
  calc
    polyL1 (∑ d ∈ f.support, MvPolynomial.C (f.coeff d) * ∏ v ∈ d.support, g v ^ d v)
        ≤ ∑ d ∈ f.support, polyL1 (MvPolynomial.C (f.coeff d) * ∏ v ∈ d.support, g v ^ d v) :=
          polyL1_finset_sum_le _ _
    _ ≤ ∑ _d ∈ f.support, B * M ^ df := by
          refine Finset.sum_le_sum fun d hd => ?_
          refine le_trans (polyL1_mul_le _ _) ?_
          rw [polyL1_C]
          refine Nat.mul_le_mul (hB d) ?_
          calc
            polyL1 (∏ v ∈ d.support, g v ^ d v)
                ≤ ∏ v ∈ d.support, polyL1 (g v ^ d v) := polyL1_finset_prod_le _ _
            _ ≤ ∏ v ∈ d.support, polyL1 (g v) ^ d v :=
                Finset.prod_le_prod' fun v _ => polyL1_pow_le _ _
            _ ≤ ∏ v ∈ d.support, M ^ d v :=
                Finset.prod_le_prod' fun v _ => Nat.pow_le_pow_left (hg v) _
            _ = M ^ (∑ v ∈ d.support, d v) := Finset.prod_pow_eq_pow_sum _ _ _
            _ ≤ M ^ df := by
                apply Nat.pow_le_pow_right hM
                exact le_trans (Finset.le_sup (f := fun d => d.sum fun _ e => e) hd) hdf
    _ = f.support.card * (B * M ^ df) := by simp
    _ ≤ K * (B * M ^ df) := Nat.mul_le_mul_right _ hK
    _ = K * B * M ^ df := by ring

private theorem multilinear_support_card_le {m : ℕ} (p : MvPolynomial (Fin m) ℤ)
    (hp : IsMultilinear p) : p.support.card ≤ 2 ^ m := by
  have hinj : Set.InjOn (fun d : Fin m →₀ ℕ => d.support) (p.support : Set (Fin m →₀ ℕ)) := by
    intro d₁ hd₁ d₂ hd₂ heq
    dsimp only at heq
    ext v
    have h1 := hp d₁ hd₁ v
    have h2 := hp d₂ hd₂ v
    have hiff : v ∈ d₁.support ↔ v ∈ d₂.support := by rw [heq]
    simp only [Finsupp.mem_support_iff] at hiff
    omega
  have hcard : p.support.card = (p.support.image (fun d => d.support)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  calc
    (p.support.image (fun d => d.support)).card
        ≤ (Finset.univ : Finset (Finset (Fin m))).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ m := by simp

/-! ### Part 2: `IntCircuit` combinators and encoding-length bound -/

private theorem intCircuit_size_le_encodingLength {n : ℕ} (C : IntCircuit n) :
    C.size ≤ C.encodingLength := by
  unfold IntCircuit.encodingLength
  have h1 : ∀ k : Fin C.size, 1 ≤ (C.gate k).bitCost := by
    intro k
    cases C.gate k <;> simp [IntGate.bitCost, intBitLen]
  calc
    C.size = ∑ _k : Fin C.size, 1 := by simp
    _ ≤ ∑ k : Fin C.size, (C.gate k).bitCost := Finset.sum_le_sum fun k _ => h1 k

private theorem intCircuit_constBitLen_le_encodingLength {n : ℕ} (C : IntCircuit n)
    (k : Fin C.size) (a : ℤ) (hk : C.gate k = .const a) :
    intBitLen a ≤ C.encodingLength := by
  have hle : (C.gate k).bitCost ≤ C.encodingLength := by
    unfold IntCircuit.encodingLength
    exact Finset.single_le_sum (f := fun j => (C.gate j).bitCost) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  rw [hk] at hle
  simp only [IntGate.bitCost] at hle
  omega

private theorem intCircuit_encodingLength_le {n : ℕ} (C : IntCircuit n) (M : ℕ)
    (hconst : ∀ k : Fin C.size, ∀ a : ℤ, C.gate k = .const a → intBitLen a ≤ M) :
    C.encodingLength ≤ C.size * (2 * Nat.clog 2 (C.size + n + 2) + M + 2) := by
  unfold IntCircuit.encodingLength
  calc
    ∑ k : Fin C.size, (C.gate k).bitCost
        ≤ ∑ _k : Fin C.size, (2 * Nat.clog 2 (C.size + n + 2) + M + 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hwf := C.wf k
          cases hg : C.gate k with
          | var v =>
            simp only [IntGate.bitCost]
            have hc := Nat.clog_mono_right 2 (show v.val + 2 ≤ C.size + n + 2 by have := v.isLt; omega)
            omega
          | const a =>
            simp only [IntGate.bitCost]
            have ha := hconst k a hg
            omega
          | add i j =>
            rw [hg] at hwf; simp only [IntGate.bitCost]
            have hci := Nat.clog_mono_right 2 (show i + 2 ≤ C.size + n + 2 by have := hwf.1; omega)
            have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ C.size + n + 2 by have := hwf.2; omega)
            omega
          | sub i j =>
            rw [hg] at hwf; simp only [IntGate.bitCost]
            have hci := Nat.clog_mono_right 2 (show i + 2 ≤ C.size + n + 2 by have := hwf.1; omega)
            have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ C.size + n + 2 by have := hwf.2; omega)
            omega
          | mul i j =>
            rw [hg] at hwf; simp only [IntGate.bitCost]
            have hci := Nat.clog_mono_right 2 (show i + 2 ≤ C.size + n + 2 by have := hwf.1; omega)
            have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ C.size + n + 2 by have := hwf.2; omega)
            omega
    _ = C.size * (2 * Nat.clog 2 (C.size + n + 2) + M + 2) := by simp

private def shiftIntGate {n : ℕ} (off : ℕ) : IntGate n → IntGate n
  | .var v => .var v
  | .const a => .const a
  | .add i j => .add (off + i) (off + j)
  | .sub i j => .sub (off + i) (off + j)
  | .mul i j => .mul (off + i) (off + j)

private theorem shiftIntGate_wf {n : ℕ} (off k : ℕ) (g : IntGate n) (h : g.WF k) :
    (shiftIntGate off g).WF (off + k) := by
  cases g with
  | var _ => trivial
  | const _ => trivial
  | add i j => dsimp only [shiftIntGate, IntGate.WF] at h ⊢; exact ⟨by omega, by omega⟩
  | sub i j => dsimp only [shiftIntGate, IntGate.WF] at h ⊢; exact ⟨by omega, by omega⟩
  | mul i j => dsimp only [shiftIntGate, IntGate.WF] at h ⊢; exact ⟨by omega, by omega⟩

private def constCircuit (n : ℕ) (a : ℤ) : IntCircuit n where
  size := 1
  size_pos := Nat.one_pos
  gate _ := .const a
  wf _ := trivial
  out := ⟨0, Nat.one_pos⟩

private theorem constCircuit_evalPoly (n : ℕ) (a : ℤ) :
    (constCircuit n a).evalPoly = MvPolynomial.C a := by
  change (constCircuit n a).evalGateAt MvPolynomial.X ⟨0, Nat.one_pos⟩ = _
  rw [evalGateAt_const _ _ _ a rfl]
  rfl

private def varCircuit (n : ℕ) (v : Fin n) : IntCircuit n where
  size := 1
  size_pos := Nat.one_pos
  gate _ := .var v
  wf _ := trivial
  out := ⟨0, Nat.one_pos⟩

private theorem varCircuit_evalPoly (n : ℕ) (v : Fin n) :
    (varCircuit n v).evalPoly = MvPolynomial.X v := by
  change (varCircuit n v).evalGateAt MvPolynomial.X ⟨0, Nat.one_pos⟩ = _
  exact evalGateAt_var _ _ _ v rfl

private def binCircuit {n : ℕ} (isMul : Bool) (C₁ C₂ : IntCircuit n) : IntCircuit n where
  size := C₁.size + C₂.size + 1
  size_pos := by omega
  gate k :=
    if h1 : k.val < C₁.size then C₁.gate ⟨k.val, h1⟩
    else if h2 : k.val < C₁.size + C₂.size then
      shiftIntGate C₁.size (C₂.gate ⟨k.val - C₁.size, by omega⟩)
    else if isMul then .mul C₁.out.val (C₁.size + C₂.out.val)
    else .add C₁.out.val (C₁.size + C₂.out.val)
  wf k := by
    split_ifs with h1 h2 hm
    · exact C₁.wf ⟨k.val, h1⟩
    · have hwf := shiftIntGate_wf C₁.size (k.val - C₁.size) _ (C₂.wf ⟨k.val - C₁.size, by omega⟩)
      have heq : C₁.size + (k.val - C₁.size) = k.val := by omega
      rwa [heq] at hwf
    · exact ⟨by have := C₁.out.isLt; omega, by have := C₂.out.isLt; omega⟩
    · exact ⟨by have := C₁.out.isLt; omega, by have := C₂.out.isLt; omega⟩
  out := ⟨C₁.size + C₂.size, by omega⟩

private theorem binCircuit_evalGate_left {n : ℕ} (isMul : Bool) (C₁ C₂ : IntCircuit n) :
    ∀ (k : ℕ) (hk : k < C₁.size),
      (binCircuit isMul C₁ C₂).evalGateAt
        (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) ⟨k, by dsimp [binCircuit]; omega⟩ =
        C₁.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) ⟨k, hk⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hgate : (binCircuit isMul C₁ C₂).gate ⟨k, by dsimp [binCircuit]; omega⟩ = C₁.gate ⟨k, hk⟩ := by
      simp [binCircuit, hk]
    have hwf := C₁.wf ⟨k, hk⟩
    cases hg : C₁.gate ⟨k, hk⟩ with
    | var v =>
      rw [hg] at hgate
      rw [evalGateAt_var _ _ _ v hgate, evalGateAt_var _ _ _ v hg]
    | const a =>
      rw [hg] at hgate
      rw [evalGateAt_const _ _ _ a hgate, evalGateAt_const _ _ _ a hg]
    | add i j =>
      rw [hg] at hgate hwf; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_add _ _ _ i j hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_add _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]
    | sub i j =>
      rw [hg] at hgate hwf; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_sub _ _ _ i j hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_sub _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]
    | mul i j =>
      rw [hg] at hgate hwf; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_mul _ _ _ i j hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_mul _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]

private theorem binCircuit_evalGate_right {n : ℕ} (isMul : Bool) (C₁ C₂ : IntCircuit n) :
    ∀ (k : ℕ) (hk : k < C₂.size),
      (binCircuit isMul C₁ C₂).evalGateAt
        (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) ⟨C₁.size + k, by dsimp [binCircuit]; omega⟩ =
        C₂.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) ⟨k, hk⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hgate : (binCircuit isMul C₁ C₂).gate ⟨C₁.size + k, by dsimp [binCircuit]; omega⟩ =
        shiftIntGate C₁.size (C₂.gate ⟨k, hk⟩) := by
      have h1 : ¬ (C₁.size + k < C₁.size) := by omega
      have h2 : C₁.size + k < C₁.size + C₂.size := by omega
      dsimp only [binCircuit]
      rw [dif_neg h1, dif_pos h2]
      congr 2
      ext; simp
    have hwf := C₂.wf ⟨k, hk⟩
    cases hg : C₂.gate ⟨k, hk⟩ with
    | var v =>
      rw [hg] at hgate; dsimp only [shiftIntGate] at hgate
      rw [evalGateAt_var _ _ _ v hgate, evalGateAt_var _ _ _ v hg]
    | const a =>
      rw [hg] at hgate; dsimp only [shiftIntGate] at hgate
      rw [evalGateAt_const _ _ _ a hgate, evalGateAt_const _ _ _ a hg]
    | add i j =>
      rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_add _ _ _ _ _ hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_add _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]
    | sub i j =>
      rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_sub _ _ _ _ _ hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_sub _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]
    | mul i j =>
      rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
      rw [evalGateAt_mul _ _ _ _ _ hgate (by dsimp [binCircuit]; omega) (by dsimp [binCircuit]; omega),
          evalGateAt_mul _ _ _ i j hg (lt_trans hwf.1 hk) (lt_trans hwf.2 hk),
          ih i hwf.1 (lt_trans hwf.1 hk), ih j hwf.2 (lt_trans hwf.2 hk)]

private theorem binCircuit_evalPoly {n : ℕ} (isMul : Bool) (C₁ C₂ : IntCircuit n) :
    (binCircuit isMul C₁ C₂).evalPoly =
      if isMul then C₁.evalPoly * C₂.evalPoly else C₁.evalPoly + C₂.evalPoly := by
  change (binCircuit isMul C₁ C₂).evalGateAt MvPolynomial.X ⟨C₁.size + C₂.size, _⟩ = _
  cases isMul with
  | false =>
    have hg : (binCircuit false C₁ C₂).gate ⟨C₁.size + C₂.size, by dsimp [binCircuit]; omega⟩ =
        .add C₁.out.val (C₁.size + C₂.out.val) := by
      dsimp only [binCircuit]
      rw [dif_neg (by omega), dif_neg (by omega)]; rfl
    rw [evalGateAt_add _ _ _ _ _ hg (by dsimp [binCircuit]; have := C₁.out.isLt; omega)
          (by dsimp [binCircuit]; have := C₂.out.isLt; omega),
        binCircuit_evalGate_left false C₁ C₂ C₁.out.val C₁.out.isLt,
        binCircuit_evalGate_right false C₁ C₂ C₂.out.val C₂.out.isLt]
    rfl
  | true =>
    have hg : (binCircuit true C₁ C₂).gate ⟨C₁.size + C₂.size, by dsimp [binCircuit]; omega⟩ =
        .mul C₁.out.val (C₁.size + C₂.out.val) := by
      dsimp only [binCircuit]
      rw [dif_neg (by omega), dif_neg (by omega)]; rfl
    rw [evalGateAt_mul _ _ _ _ _ hg (by dsimp [binCircuit]; have := C₁.out.isLt; omega)
          (by dsimp [binCircuit]; have := C₂.out.isLt; omega),
        binCircuit_evalGate_left true C₁ C₂ C₁.out.val C₁.out.isLt,
        binCircuit_evalGate_right true C₁ C₂ C₂.out.val C₂.out.isLt]
    rfl

private theorem binCircuit_constBound {n : ℕ} (isMul : Bool) (C₁ C₂ : IntCircuit n) (M : ℕ)
    (h₁ : ∀ k a, C₁.gate k = .const a → intBitLen a ≤ M)
    (h₂ : ∀ k a, C₂.gate k = .const a → intBitLen a ≤ M) :
    ∀ k a, (binCircuit isMul C₁ C₂).gate k = .const a → intBitLen a ≤ M := by
  intro k a hga
  dsimp only [binCircuit] at hga
  split_ifs at hga with hk1 hk2 hm
  · exact h₁ ⟨k.val, hk1⟩ a hga
  · cases hg2 : C₂.gate ⟨k.val - C₁.size, by omega⟩ <;> rw [hg2] at hga <;>
      dsimp only [shiftIntGate] at hga <;> cases hga
    exact h₂ _ a hg2
  all_goals cases hga

private theorem exists_monomial_circuit {n : ℕ} (a : ℤ) (L : List (Fin n)) (M : ℕ)
    (ha : intBitLen a ≤ M) :
    ∃ C : IntCircuit n,
      C.size = 1 + 2 * L.length ∧
      (∀ k c, C.gate k = .const c → intBitLen c ≤ M) ∧
      C.evalPoly = MvPolynomial.C a * (L.map MvPolynomial.X).prod := by
  induction L with
  | nil =>
    refine ⟨constCircuit n a, rfl, ?_, ?_⟩
    · intro k c hkc; dsimp [constCircuit] at hkc; cases hkc; exact ha
    · rw [constCircuit_evalPoly]; simp
  | cons v vs ih =>
    rcases ih with ⟨C, hsz, hcb, hev⟩
    let C' := binCircuit true (varCircuit n v) C
    refine ⟨C', ?_, ?_, ?_⟩
    · dsimp [C', binCircuit, varCircuit]; omega
    · refine binCircuit_constBound true (varCircuit n v) C M ?_ hcb
      intro k c hkc; dsimp [varCircuit] at hkc; cases hkc
    · simp only [C', binCircuit_evalPoly, ite_true, varCircuit_evalPoly, hev, List.map_cons,
        List.prod_cons]
      ring

private theorem exists_multilinear_circuit {n : ℕ} (q : MvPolynomial (Fin n) ℤ)
    (hq_ml : IsMultilinear q) (K D M : ℕ)
    (hK : q.support.card ≤ K) (hD : q.totalDegree ≤ D)
    (hM : ∀ d, intBitLen (q.coeff d) ≤ M) (hM2 : 2 ≤ M) :
    ∃ C : IntCircuit n,
      C.size ≤ 1 + K * (2 * D + 2) ∧
      (∀ k c, C.gate k = .const c → intBitLen c ≤ M) ∧
      C.evalPoly = q := by
  classical
  have haux : ∀ (S : Finset (Fin n →₀ ℕ)), S ⊆ q.support →
      ∃ C : IntCircuit n,
        C.size ≤ 1 + S.card * (2 * D + 2) ∧
        (∀ k c, C.gate k = .const c → intBitLen c ≤ M) ∧
        C.evalPoly = ∑ d ∈ S, MvPolynomial.monomial d (q.coeff d) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨constCircuit n 0, by dsimp [constCircuit]; omega, ?_, ?_⟩
      · intro k c hkc
        dsimp [constCircuit] at hkc; cases hkc
        have h0 : intBitLen 0 = 1 := by decide
        omega
      · rw [constCircuit_evalPoly]; simp
    | insert d S hd ih =>
      intro hsub
      rcases ih (Finset.Subset.trans (Finset.subset_insert d S) hsub) with ⟨Cacc, hsz, hcb, hev⟩
      have hd_mem : d ∈ q.support := hsub (Finset.mem_insert_self d S)
      let L : List (Fin n) := d.support.toList
      have hL_len : L.length ≤ D := by
        have h1 : L.length = d.support.card := Finset.length_toList _
        rw [h1]
        have h2 : d.support.card ≤ ∑ v ∈ d.support, d v := by
          calc
            d.support.card = ∑ _v ∈ d.support, 1 := by simp
            _ ≤ ∑ v ∈ d.support, d v := by
              refine Finset.sum_le_sum fun v hv => ?_
              have := Finsupp.mem_support_iff.mp hv
              omega
        have h3 : (d.sum fun _ e => e) ≤ q.totalDegree :=
          Finset.le_sup (f := fun d => d.sum fun _ e => e) hd_mem
        exact le_trans h2 (le_trans h3 hD)
      rcases exists_monomial_circuit (q.coeff d) L M (hM d) with ⟨Cmon, hmsz, hmcb, hmev⟩
      have hmon_eq : MvPolynomial.C (q.coeff d) * (L.map MvPolynomial.X).prod =
          MvPolynomial.monomial d (q.coeff d) := by
        have hprod : (L.map MvPolynomial.X).prod =
            ∏ v ∈ d.support, (MvPolynomial.X v : MvPolynomial (Fin n) ℤ) := by
          rw [← Multiset.prod_coe, ← Multiset.map_coe]
          dsimp only [L]
          rw [Finset.coe_toList]
          rfl
        rw [hprod]
        have hpow : ∏ v ∈ d.support, (MvPolynomial.X v : MvPolynomial (Fin n) ℤ) =
            ∏ v ∈ d.support, (MvPolynomial.X v : MvPolynomial (Fin n) ℤ) ^ d v := by
          refine Finset.prod_congr rfl fun v hv => ?_
          have hv1 : d v ≤ 1 := hq_ml d hd_mem v
          have hv0 : d v ≠ 0 := Finsupp.mem_support_iff.mp hv
          have hveq : d v = 1 := by omega
          rw [hveq, pow_one]
        rw [hpow, MvPolynomial.monomial_eq]
        rfl
      let C' := binCircuit false Cmon Cacc
      refine ⟨C', ?_, binCircuit_constBound false Cmon Cacc M hmcb hcb, ?_⟩
      · have hcard : (insert d S).card = S.card + 1 := Finset.card_insert_of_notMem hd
        dsimp [C', binCircuit]
        rw [hcard, hmsz]
        nlinarith
      · simp only [C', binCircuit_evalPoly, Bool.false_eq_true, ite_false, hmev, hmon_eq, hev,
          Finset.sum_insert hd]
  rcases haux q.support (Finset.Subset.refl _) with ⟨C, hsz, hcb, hev⟩
  refine ⟨C, le_trans hsz (by nlinarith), hcb, ?_⟩
  rw [hev, ← q.as_sum]

private def composeWidth {n m : ℕ} (sub : Fin n → IntCircuit m) : ℕ :=
  max 1 (Finset.univ.sup fun r : Fin n => (sub r).size)

private def composeCircuits {n m : ℕ} (C : IntCircuit n) (sub : Fin n → IntCircuit m) :
    IntCircuit m :=
  let W : ℕ := composeWidth sub
  { size := 1 + n * W + C.size
    size_pos := by omega
    gate := fun slot =>
      if h0 : slot.val = 0 then .const 0
      else if h1 : slot.val < 1 + n * W then
        let r := (slot.val - 1) / W
        let t := (slot.val - 1) % W
        if hr : r < n then
          if ht : t < (sub ⟨r, hr⟩).size then
            shiftIntGate (1 + r * W) ((sub ⟨r, hr⟩).gate ⟨t, ht⟩)
          else .const 0
        else .const 0
      else
        let k := slot.val - (1 + n * W)
        if hk : k < C.size then
          match C.gate ⟨k, hk⟩ with
          | .var r => .add (1 + r.val * W + (sub r).out.val) 0
          | .const a => .const a
          | .add i j => .add (1 + n * W + i) (1 + n * W + j)
          | .sub i j => .sub (1 + n * W + i) (1 + n * W + j)
          | .mul i j => .mul (1 + n * W + i) (1 + n * W + j)
        else .const 0
    wf := fun slot => by
      dsimp only
      have hWpos : 0 < W := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      split_ifs with h0 h1 hr ht hk
      · trivial
      · have hwf := shiftIntGate_wf (1 + ((slot.val - 1) / W) * W) ((slot.val - 1) % W) _
          ((sub ⟨_, hr⟩).wf ⟨_, ht⟩)
        have heq : 1 + ((slot.val - 1) / W) * W + (slot.val - 1) % W = slot.val := by
          have hdm := Nat.div_add_mod (slot.val - 1) W
          rw [Nat.mul_comm] at hdm
          omega
        rwa [heq] at hwf
      · trivial
      · trivial
      · have hCwf := C.wf ⟨slot.val - (1 + n * W), hk⟩
        cases hg : C.gate ⟨slot.val - (1 + n * W), hk⟩ with
        | var r =>
          have hsubW : (sub r).size ≤ W :=
            le_trans (Finset.le_sup (f := fun r : Fin n => (sub r).size) (Finset.mem_univ r))
              (le_max_right _ _)
          have hlt1 : 1 + r.val * W + (sub r).out.val < 1 + n * W := by
            have hrm : (r.val + 1) * W ≤ n * W := Nat.mul_le_mul_right W r.isLt
            have hout := (sub r).out.isLt
            nlinarith
          exact ⟨by omega, by omega⟩
        | const _ => trivial
        | add i j =>
          rw [hg] at hCwf; dsimp only [IntGate.WF] at hCwf ⊢
          exact ⟨by omega, by omega⟩
        | sub i j =>
          rw [hg] at hCwf; dsimp only [IntGate.WF] at hCwf ⊢
          exact ⟨by omega, by omega⟩
        | mul i j =>
          rw [hg] at hCwf; dsimp only [IntGate.WF] at hCwf ⊢
          exact ⟨by omega, by omega⟩
      · trivial
    out := ⟨1 + n * W + C.out.val, by have := C.out.isLt; omega⟩ }

private theorem composeCircuits_size_le {n m : ℕ} (C : IntCircuit n) (sub : Fin n → IntCircuit m)
    (W₀ : ℕ) (hW₀ : 1 ≤ W₀) (hsub : ∀ r, (sub r).size ≤ W₀) :
    (composeCircuits C sub).size ≤ 1 + n * W₀ + C.size := by
  dsimp only [composeCircuits, composeWidth]
  have hsup : max 1 (Finset.univ.sup fun r : Fin n => (sub r).size) ≤ W₀ :=
    max_le hW₀ (Finset.sup_le fun r _ => hsub r)
  nlinarith

private theorem composeCircuits_constBound {n m : ℕ} (C : IntCircuit n) (sub : Fin n → IntCircuit m)
    (M : ℕ) (hM2 : 2 ≤ M)
    (hC : ∀ k a, C.gate k = .const a → intBitLen a ≤ M)
    (hsub : ∀ r k a, (sub r).gate k = .const a → intBitLen a ≤ M) :
    ∀ slot a, (composeCircuits C sub).gate slot = .const a → intBitLen a ≤ M := by
  intro slot a hga
  dsimp only [composeCircuits] at hga
  have h0bit : intBitLen 0 = 1 := by decide
  split_ifs at hga with h0 h1 hr ht hk
  · cases hga; omega
  · cases hg : (sub ⟨_, hr⟩).gate ⟨_, ht⟩ <;> rw [hg] at hga <;>
      dsimp only [shiftIntGate] at hga <;> cases hga
    exact hsub _ _ a hg
  · cases hga; omega
  · cases hga; omega
  · cases hg : C.gate ⟨_, hk⟩ <;> rw [hg] at hga <;> cases hga
    exact hC _ a hg
  · cases hga; omega

private theorem gate_eq_of_idx_eq {n m : ℕ} (sub : Fin n → IntCircuit m)
    (r₁ r₂ : Fin n) (hr : r₁ = r₂) (t : ℕ) (ht₁ : t < (sub r₁).size) (ht₂ : t < (sub r₂).size) :
    (sub r₁).gate ⟨t, ht₁⟩ = (sub r₂).gate ⟨t, ht₂⟩ := by
  subst hr; rfl

private theorem composeCircuits_evalPoly {n m : ℕ} (C : IntCircuit n) (sub : Fin n → IntCircuit m) :
    (composeCircuits C sub).evalPoly = MvPolynomial.bind₁ (fun r => (sub r).evalPoly) C.evalPoly := by
  let W : ℕ := composeWidth sub
  have hWpos : 0 < W := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  let CC := composeCircuits C sub
  have hCC_sz : CC.size = 1 + n * W + C.size := rfl
  have hsubW : ∀ r : Fin n, (sub r).size ≤ W := fun r =>
    le_trans (Finset.le_sup (f := fun r : Fin n => (sub r).size) (Finset.mem_univ r))
      (le_max_right _ _)
  have hgate0 : CC.evalGateAt (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℤ) ⟨0, CC.size_pos⟩ = 0 := by
    have hg0 : CC.gate ⟨0, CC.size_pos⟩ = .const 0 := by simp [CC, composeCircuits]
    simpa using evalGateAt_const CC
      (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℤ) ⟨0, CC.size_pos⟩ 0 hg0
  have hslot_lt : ∀ (r : Fin n) (t : ℕ), t < (sub r).size → 1 + r.val * W + t < 1 + n * W := by
    intro r t ht
    have hrm : (r.val + 1) * W ≤ n * W := Nat.mul_le_mul_right W r.isLt
    have htW : t < W := lt_of_lt_of_le ht (hsubW r)
    nlinarith
  have hsub_eval : ∀ (r : Fin n) (t : ℕ) (ht : t < (sub r).size),
      CC.evalGateAt (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℤ)
        ⟨1 + r.val * W + t, by have := hslot_lt r t ht; omega⟩ =
        (sub r).evalGateAt (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℤ) ⟨t, ht⟩ := by
    intro r t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      have htW : t < W := lt_of_lt_of_le ht (hsubW r)
      have hdiv : (1 + r.val * W + t - 1) / W = r.val := by
        have h1 : 1 + r.val * W + t - 1 = r.val * W + t := by omega
        rw [h1, Nat.mul_comm r.val W, Nat.mul_add_div hWpos, Nat.div_eq_of_lt htW, Nat.add_zero]
      have hmod : (1 + r.val * W + t - 1) % W = t := by
        have h1 : 1 + r.val * W + t - 1 = r.val * W + t := by omega
        rw [h1, Nat.mul_comm r.val W, Nat.mul_add_mod, Nat.mod_eq_of_lt htW]
      have hgate : CC.gate ⟨1 + r.val * W + t, by have := hslot_lt r t ht; omega⟩ =
          shiftIntGate (1 + r.val * W) ((sub r).gate ⟨t, ht⟩) := by
        have hne0 : 1 + r.val * W + t ≠ 0 := by omega
        have hlt1 : 1 + r.val * W + t < 1 + n * W := hslot_lt r t ht
        dsimp only [CC, composeCircuits]
        dsimp only [W] at hne0 hlt1 hdiv hmod ⊢
        rw [dif_neg hne0, dif_pos hlt1]
        simp only [hdiv, hmod, dif_pos r.isLt, dif_pos ht]
        exact congrArg (shiftIntGate _) (gate_eq_of_idx_eq sub _ r (Fin.ext hdiv) t _ ht)
      have hwf := (sub r).wf ⟨t, ht⟩
      cases hg : (sub r).gate ⟨t, ht⟩ with
      | var v =>
        rw [hg] at hgate; dsimp only [shiftIntGate] at hgate
        rw [evalGateAt_var _ _ _ v hgate, evalGateAt_var _ _ _ v hg]
      | const a =>
        rw [hg] at hgate; dsimp only [shiftIntGate] at hgate
        rw [evalGateAt_const _ _ _ a hgate, evalGateAt_const _ _ _ a hg]
      | add i j =>
        rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 ht; have hj := lt_trans hwf.2 ht
        rw [evalGateAt_add _ _ _ _ _ hgate (by have := hslot_lt r i hi; omega)
              (by have := hslot_lt r j hj; omega),
            evalGateAt_add _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
      | sub i j =>
        rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 ht; have hj := lt_trans hwf.2 ht
        rw [evalGateAt_sub _ _ _ _ _ hgate (by have := hslot_lt r i hi; omega)
              (by have := hslot_lt r j hj; omega),
            evalGateAt_sub _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
      | mul i j =>
        rw [hg] at hgate hwf; dsimp only [shiftIntGate] at hgate; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 ht; have hj := lt_trans hwf.2 ht
        rw [evalGateAt_mul _ _ _ _ _ hgate (by have := hslot_lt r i hi; omega)
              (by have := hslot_lt r j hj; omega),
            evalGateAt_mul _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
  have htop_eval : ∀ (k : ℕ) (hk : k < C.size),
      CC.evalGateAt (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℤ) ⟨1 + n * W + k, by omega⟩ =
        C.evalGateAt (fun r => (sub r).evalPoly) ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hne0 : 1 + n * W + k ≠ 0 := by omega
      have hnot1 : ¬ (1 + n * W + k < 1 + n * W) := by omega
      have hsubk : 1 + n * W + k - (1 + n * W) = k := by omega
      have hgate_top : CC.gate ⟨1 + n * W + k, by omega⟩ =
          match C.gate ⟨k, hk⟩ with
          | .var r => .add (1 + r.val * W + (sub r).out.val) 0
          | .const a => .const a
          | .add i j => .add (1 + n * W + i) (1 + n * W + j)
          | .sub i j => .sub (1 + n * W + i) (1 + n * W + j)
          | .mul i j => .mul (1 + n * W + i) (1 + n * W + j) := by
        dsimp only [CC, composeCircuits]
        dsimp only [W] at hne0 hnot1 hsubk ⊢
        rw [dif_neg hne0, dif_neg hnot1]
        simp only [hsubk, dif_pos hk]
      have hwf := C.wf ⟨k, hk⟩
      cases hg : C.gate ⟨k, hk⟩ with
      | var r =>
        rw [hg] at hgate_top
        rw [evalGateAt_add _ _ _ _ _ hgate_top
              (by have := hslot_lt r (sub r).out.val (sub r).out.isLt; omega)
              CC.size_pos,
            hgate0, add_zero, hsub_eval r (sub r).out.val (sub r).out.isLt,
            evalGateAt_var _ _ _ r hg]
        rfl
      | const a =>
        rw [hg] at hgate_top
        rw [evalGateAt_const _ _ _ a hgate_top, evalGateAt_const _ _ _ a hg]
      | add i j =>
        rw [hg] at hwf hgate_top; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        rw [evalGateAt_add _ _ _ _ _ hgate_top (by omega) (by omega),
            evalGateAt_add _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
      | sub i j =>
        rw [hg] at hwf hgate_top; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        rw [evalGateAt_sub _ _ _ _ _ hgate_top (by omega) (by omega),
            evalGateAt_sub _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
      | mul i j =>
        rw [hg] at hwf hgate_top; dsimp only [IntGate.WF] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        rw [evalGateAt_mul _ _ _ _ _ hgate_top (by omega) (by omega),
            evalGateAt_mul _ _ _ i j hg hi hj, ih i hwf.1 hi, ih j hwf.2 hj]
  change CC.evalGateAt MvPolynomial.X ⟨1 + n * W + C.out.val, _⟩ = _
  rw [htop_eval C.out.val C.out.isLt]
  change C.evalAt (MvPolynomial (Fin m) ℤ) (fun r => (sub r).evalPoly) = _
  rw [intCircuit_evalAt_eq_aeval]
  rfl

/-! ### Part 3: Hybrid nonvanishing witness on bounded integers -/

private theorem exists_bounded_nat_subst_ne_zero {l n : ℕ}
    (H : MvPolynomial (Fin l ⊕ Fin n) ℤ) (hH : H ≠ 0) (D : ℕ) (hdeg : H.totalDegree ≤ D)
    {m : ℕ} (embStar : Fin m ↪o Fin l) (iStar : Fin n) :
    ∃ (βL : Fin l → ℕ) (βR : Fin n → ℕ),
      (∀ u, βL u ≤ D) ∧ (∀ r, βR r ≤ D) ∧
      MvPolynomial.bind₁
        (Sum.elim
          (fun u => if h : ∃ j : Fin m, embStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
                    else MvPolynomial.C (βL u : ℤ))
          (fun r => if r = iStar then MvPolynomial.X (Fin.last m)
                    else MvPolynomial.C (βR r : ℤ)))
        H ≠ 0 := by
  classical
  let e := finSumFinEquiv (m := l) (n := n)
  let Hq : MvPolynomial (Fin (l + n)) ℚ :=
    MvPolynomial.rename e (MvPolynomial.map (Int.castRingHom ℚ) H)
  have hHq_ne : Hq ≠ 0 := by
    intro h0
    apply hH
    have h1 : MvPolynomial.map (Int.castRingHom ℚ) H = 0 :=
      (MvPolynomial.rename_injective e e.injective) (by rw [map_zero]; exact h0)
    exact (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) (by rw [map_zero]; exact h1)
  have hHq_deg : Hq.totalDegree ≤ D := by
    refine le_trans (MvPolynomial.totalDegree_rename_le e _) ?_
    exact le_trans (totalDegree_map_le _ _) hdeg
  let S : Finset ℚ := (Finset.range (D + 1)).image (fun k : ℕ => (k : ℚ))
  have hScard : Hq.totalDegree < S.card := by
    have hinj : Function.Injective (fun k : ℕ => (k : ℚ)) := Nat.cast_injective
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega
  obtain ⟨x, hxS, hx_ne⟩ := step_2_2_nonvanishing_proved Hq hHq_ne S hScard
  have hx_nat : ∀ t : Fin (l + n), ∃ k : ℕ, k ≤ D ∧ (k : ℚ) = x t := by
    intro t
    rcases Finset.mem_image.mp (hxS t) with ⟨k, hk, hkx⟩
    exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), hkx⟩
  let βL : Fin l → ℕ := fun u => (hx_nat (e (Sum.inl u))).choose
  let βR : Fin n → ℕ := fun r => (hx_nat (e (Sum.inr r))).choose
  have hβL_le : ∀ u, βL u ≤ D := fun u => (hx_nat (e (Sum.inl u))).choose_spec.1
  have hβR_le : ∀ r, βR r ≤ D := fun r => (hx_nat (e (Sum.inr r))).choose_spec.1
  have hβL_eq : ∀ u, (βL u : ℚ) = x (e (Sum.inl u)) := fun u => (hx_nat (e (Sum.inl u))).choose_spec.2
  have hβR_eq : ∀ r, (βR r : ℚ) = x (e (Sum.inr r)) := fun r => (hx_nat (e (Sum.inr r))).choose_spec.2
  refine ⟨βL, βR, hβL_le, hβR_le, ?_⟩
  intro hzero
  apply hx_ne
  let y : Fin (m + 1) → ℚ :=
    Fin.lastCases (x (e (Sum.inr iStar))) (fun j => x (e (Sum.inl (embStar j))))
  have heval_eq :
      MvPolynomial.eval y
        (MvPolynomial.map (Int.castRingHom ℚ)
          (MvPolynomial.bind₁
            (Sum.elim
              (fun u => if h : ∃ j : Fin m, embStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
                        else MvPolynomial.C (βL u : ℤ))
              (fun r => if r = iStar then MvPolynomial.X (Fin.last m)
                        else MvPolynomial.C (βR r : ℤ)))
            H)) = MvPolynomial.eval x Hq := by
    rw [MvPolynomial.eval_map, eval₂_bind₁_eq]
    dsimp only [Hq]
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_map]
    refine congrArg (fun fn => MvPolynomial.eval₂ (Int.castRingHom ℚ) fn H) ?_
    ext v
    cases v with
    | inl u =>
      dsimp only [Sum.elim]
      split_ifs with h
      · rw [MvPolynomial.eval₂_X]
        dsimp only [y]
        rw [Fin.lastCases_castSucc, h.choose_spec]
        rfl
      · rw [MvPolynomial.eval₂_C]
        simpa [Int.castRingHom] using hβL_eq u
    | inr r =>
      dsimp only [Sum.elim]
      split_ifs with h
      · subst h
        rw [MvPolynomial.eval₂_X]
        dsimp only [y]
        rw [Fin.lastCases_last]
        rfl
      · rw [MvPolynomial.eval₂_C]
        simpa [Int.castRingHom] using hβR_eq r
  rw [← heval_eq, hzero, map_zero, map_zero]

/-! ### Part 4: Restricted polynomial properties and hybrid witness -/

private theorem two_pow_lt_of_lt_logb {k n : ℕ} (hn : 2 ≤ n) (hk : (k : ℝ) < Real.logb 2 n) :
    2 ^ k ≤ n := by
  have h1 : ((2 ^ k : ℕ) : ℝ) < (n : ℝ) := by
    calc
      ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ < (2 : ℝ) ^ (Real.logb 2 (n : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hk
      _ = (n : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  exact le_of_lt (by exact_mod_cast h1)

private theorem prod_monomial_single {ι V : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → V) :
    (∏ j ∈ S, MvPolynomial.monomial (Finsupp.single (f j) 1) (1 : ℤ)) =
      MvPolynomial.monomial (∑ j ∈ S, Finsupp.single (f j) 1) 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.monomial_mul_monomial, one_mul]

private theorem restricted_poly_props {m n l : ℕ} (hn : 2 ≤ n)
    (S : Fin n → Finset (Fin l)) (hcard : ∀ i, (S i).card = m)
    (hinter : ∀ i j : Fin n, i ≠ j → ((S i ∩ S j).card : ℝ) < Real.logb 2 n)
    (p : MvPolynomial (Fin m) ℤ) (hp_ml : IsMultilinear p)
    (r iStar : Fin n) (hne : r ≠ iStar) (βL : Fin l → ℕ) :
    let emb (i : Fin n) : Fin m ↪o Fin l := (S i).orderEmbOfFin (hcard i)
    let substL (u : Fin l) : MvPolynomial (Fin (m + 1)) ℤ :=
      if h : ∃ j : Fin m, emb iStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
      else MvPolynomial.C (βL u : ℤ)
    let q : MvPolynomial (Fin (m + 1)) ℤ := MvPolynomial.bind₁ (fun j => substL (emb r j)) p
    IsMultilinear q ∧ q.support.card ≤ n := by
  classical
  intro emb substL q
  let hit : Finset (Fin m) := Finset.univ.filter fun j' : Fin m => emb iStar j' ∈ S r
  have hhit_card : hit.card ≤ (S r ∩ S iStar).card := by
    have hinj : Set.InjOn (fun j' : Fin m => emb iStar j') (hit : Set (Fin m)) :=
      fun a _ b _ h => (emb iStar).injective h
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card fun u hu => ?_
    rcases Finset.mem_image.mp hu with ⟨j', hj', rfl⟩
    refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hj').2, ?_⟩
    exact (S iStar).orderEmbOfFin_mem (hcard iStar) j'
  have hterm : ∀ d ∈ p.support,
      ∃ (e : Fin (m + 1) →₀ ℕ) (c : ℤ),
        (∀ v, e v ≤ 1) ∧
        (∀ v ∈ e.support, ∃ j' ∈ hit, v = Fin.castSucc j') ∧
        MvPolynomial.C (p.coeff d) * ∏ j ∈ d.support, substL (emb r j) ^ d j =
          MvPolynomial.monomial e c := by
    intro d hd
    let dVar : Finset (Fin m) := d.support.filter fun j => ∃ j' : Fin m, emb iStar j' = emb r j
    let dConst : Finset (Fin m) := d.support.filter fun j => ¬ ∃ j' : Fin m, emb iStar j' = emb r j
    have hsplit : d.support = dVar ∪ dConst := by
      ext j; simp [dVar, dConst]; tauto
    have hdisj : Disjoint dVar dConst := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      exact (Finset.mem_filter.mp hj2).2 (Finset.mem_filter.mp hj1).2
    let fVar : Fin m → Fin (m + 1) := fun j =>
      if h : ∃ j' : Fin m, emb iStar j' = emb r j then Fin.castSucc h.choose else Fin.last m
    have hfVar_inj : Set.InjOn fVar (dVar : Set (Fin m)) := by
      intro j₁ hj₁ j₂ hj₂ heq
      have h1 := (Finset.mem_filter.mp hj₁).2
      have h2 := (Finset.mem_filter.mp hj₂).2
      simp only [fVar, dif_pos h1, dif_pos h2] at heq
      have hch : h1.choose = h2.choose := Fin.castSucc_injective _ heq
      have hemb : emb r j₁ = emb r j₂ := by rw [← h1.choose_spec, hch, h2.choose_spec]
      exact (emb r).injective hemb
    let e : Fin (m + 1) →₀ ℕ := ∑ j ∈ dVar, Finsupp.single (fVar j) 1
    let c : ℤ := p.coeff d * ∏ j ∈ dConst, (βL (emb r j) : ℤ) ^ d j
    have he_val : ∀ v : Fin (m + 1), e v = if v ∈ dVar.image fVar then 1 else 0 := by
      intro v
      dsimp only [e]
      rw [Finsupp.finsetSum_apply]
      by_cases hv : v ∈ dVar.image fVar
      · rcases Finset.mem_image.mp hv with ⟨j₀, hj₀, rfl⟩
        rw [if_pos hv, Finset.sum_eq_single j₀]
        · simp
        · intro j hj hne
          rw [Finsupp.single_apply, if_neg]
          intro heq
          exact hne (hfVar_inj hj hj₀ heq)
        · intro hnot; exact absurd hj₀ hnot
      · rw [if_neg hv, Finset.sum_eq_zero]
        intro j hj
        rw [Finsupp.single_apply, if_neg]
        intro heq
        exact hv (Finset.mem_image.mpr ⟨j, hj, heq⟩)
    refine ⟨e, c, ?_, ?_, ?_⟩
    · intro v; rw [he_val v]; split_ifs <;> omega
    · intro v hv
      have hv_im : v ∈ dVar.image fVar := by
        have hne0 := Finsupp.mem_support_iff.mp hv
        rw [he_val v] at hne0
        by_contra hnot; simp [hnot] at hne0
      rcases Finset.mem_image.mp hv_im with ⟨j, hj, rfl⟩
      have hj_ex := (Finset.mem_filter.mp hj).2
      refine ⟨hj_ex.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp [fVar, dif_pos hj_ex]⟩
      rw [hj_ex.choose_spec]
      exact (S r).orderEmbOfFin_mem (hcard r) j
    · rw [hsplit, Finset.prod_union hdisj]
      have hprodC : ∏ j ∈ dConst, substL (emb r j) ^ d j =
          MvPolynomial.C (∏ j ∈ dConst, (βL (emb r j) : ℤ) ^ d j) := by
        rw [map_prod]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hnot := (Finset.mem_filter.mp hj).2
        simp [substL, dif_neg hnot, map_pow]
      have hprodV : ∏ j ∈ dVar, substL (emb r j) ^ d j = MvPolynomial.monomial e 1 := by
        have hstep : ∏ j ∈ dVar, substL (emb r j) ^ d j =
            ∏ j ∈ dVar, MvPolynomial.monomial (Finsupp.single (fVar j) 1) (1 : ℤ) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hmem : j ∈ d.support := (Finset.mem_filter.mp hj).1
          have hex := (Finset.mem_filter.mp hj).2
          have hdj1 : d j = 1 := by
            have hle := hp_ml d hd j
            have hne0 := Finsupp.mem_support_iff.mp hmem
            omega
          rw [hdj1, pow_one]
          simp [substL, fVar, dif_pos hex, MvPolynomial.X]
        rw [hstep, prod_monomial_single]
      rw [hprodC, hprodV, mul_comm (MvPolynomial.monomial e 1), ← mul_assoc, ← map_mul,
          MvPolynomial.C_mul_monomial, mul_one]
  have hq_supp : ∀ e ∈ q.support,
      (∀ v, e v ≤ 1) ∧ (∀ v ∈ e.support, ∃ j' ∈ hit, v = Fin.castSucc j') := by
    intro e he
    have hq_eq : q = ∑ d ∈ p.support, MvPolynomial.C (p.coeff d) * ∏ j ∈ d.support, substL (emb r j) ^ d j := by
      dsimp only [q]; exact bind₁_eq_sum _ p
    rw [hq_eq] at he
    have hmem : ∃ d ∈ p.support,
        e ∈ (MvPolynomial.C (p.coeff d) * ∏ j ∈ d.support, substL (emb r j) ^ d j).support := by
      by_contra hall
      push Not at hall
      have h0 : (∑ d ∈ p.support, MvPolynomial.C (p.coeff d) * ∏ j ∈ d.support, substL (emb r j) ^ d j).coeff e = 0 := by
        rw [MvPolynomial.coeff_sum]
        refine Finset.sum_eq_zero fun d hd => MvPolynomial.notMem_support_iff.mp (hall d hd)
      exact MvPolynomial.mem_support_iff.mp he h0
    rcases hmem with ⟨d, hd, hde⟩
    rcases hterm d hd with ⟨e', c', hml', hsupp', heq'⟩
    rw [heq'] at hde
    have hee' : e = e' := by
      have hsub := MvPolynomial.support_monomial_subset (s := e') (a := c')
      exact Finset.mem_singleton.mp (hsub hde)
    subst hee'
    exact ⟨hml', hsupp'⟩
  constructor
  · intro e he; exact (hq_supp e he).1
  · let hitImg : Finset (Fin (m + 1)) := hit.image Fin.castSucc
    have hinj : Set.InjOn (fun e : Fin (m + 1) →₀ ℕ => e.support) (q.support : Set (Fin (m + 1) →₀ ℕ)) := by
      intro e₁ he₁ e₂ he₂ heq
      dsimp only at heq
      ext v
      have h1 := (hq_supp e₁ he₁).1 v
      have h2 := (hq_supp e₂ he₂).1 v
      have hiff : v ∈ e₁.support ↔ v ∈ e₂.support := by rw [heq]
      simp only [Finsupp.mem_support_iff] at hiff
      omega
    have hcard_le : q.support.card ≤ 2 ^ hit.card := by
      rw [← Finset.card_image_of_injOn hinj]
      calc
        (q.support.image (fun e => e.support)).card
            ≤ hitImg.powerset.card := by
              refine Finset.card_le_card fun T hT => ?_
              rcases Finset.mem_image.mp hT with ⟨e, he, rfl⟩
              refine Finset.mem_powerset.mpr fun v hv => ?_
              rcases (hq_supp e he).2 v hv with ⟨j', hj', rfl⟩
              exact Finset.mem_image.mpr ⟨j', hj', rfl⟩
        _ = 2 ^ hitImg.card := Finset.card_powerset _
        _ = 2 ^ hit.card := by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
    have hpow_le : 2 ^ (S r ∩ S iStar).card ≤ n :=
      two_pow_lt_of_lt_logb hn (hinter r iStar hne)
    exact le_trans hcard_le (le_trans (Nat.pow_le_pow_right (by decide) hhit_card) hpow_le)

private theorem intBitLen_le_of_natAbs_le_two_pow (a : ℤ) (k : ℕ) (h : a.natAbs ≤ 2 ^ k) :
    intBitLen a ≤ k + 2 := by
  unfold intBitLen
  have h1 : a.natAbs + 1 ≤ 2 ^ (k + 1) := by
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    rw [pow_succ]
    omega
  have h2 : Nat.clog 2 (a.natAbs + 1) ≤ k + 1 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h1
  omega

/-- Steps 1–4 of Lemma 2.2: extract the hybrid index `k₀ < n` and bounded integer
substitutions `(βL, βR)` yielding a nonzero `g` with `g(x, p(x)) = 0`. -/
private theorem hybrid_witness_exists {m n l d_f d_p : ℕ}
    (S : Fin n → Finset (Fin l)) (hcard : ∀ i, (S i).card = m)
    (f : MvPolynomial (Fin n) ℤ) (hf_nz : f ≠ 0) (hf_deg : f.totalDegree ≤ d_f)
    (p : MvPolynomial (Fin m) ℤ) (hp_deg : p.totalDegree ≤ d_p)
    (S_grid : Finset ℚ) (hS_card : d_f * d_p < S_grid.card)
    (hvanish : ∀ a : Fin l → ℚ, (∀ j, a j ∈ S_grid) →
      MvPolynomial.eval
        (nwMap S hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a)
        (MvPolynomial.map (Int.castRingHom ℚ) f) = 0) :
    let emb (r : Fin n) : Fin m ↪o Fin l := (S r).orderEmbOfFin (hcard r)
    ∃ (k₀ : ℕ) (hk₀ : k₀ < n) (βL : Fin l → ℕ) (βR : Fin n → ℕ),
      (∀ u, βL u ≤ d_f * (d_p + 1)) ∧
      (∀ r, βR r ≤ d_f * (d_p + 1)) ∧
      let iStar : Fin n := ⟨k₀, hk₀⟩
      let substL (u : Fin l) : MvPolynomial (Fin (m + 1)) ℤ :=
        if h : ∃ j : Fin m, emb iStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
        else MvPolynomial.C (βL u : ℤ)
      let substR (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
        if r = iStar then MvPolynomial.X (Fin.last m) else MvPolynomial.C (βR r : ℤ)
      let inp (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
        if r.val < k₀ then MvPolynomial.bind₁ (fun j => substL (emb r j)) p else substR r
      let g : MvPolynomial (Fin (m + 1)) ℤ := MvPolynomial.bind₁ inp f
      g ≠ 0 ∧ MvPolynomial.bind₁ (Fin.lastCases p (fun j => MvPolynomial.X j)) g = 0 := by
  classical
  intro emb
  let pr (r : Fin n) : MvPolynomial (Fin l) ℤ := MvPolynomial.rename (emb r) p
  let F : MvPolynomial (Fin l) ℤ := MvPolynomial.bind₁ pr f
  have hF_zero : F = 0 := by
    have hFq_zero : MvPolynomial.map (Int.castRingHom ℚ) F = 0 := by
      by_contra hne
      have hdegF : (MvPolynomial.map (Int.castRingHom ℚ) F).totalDegree ≤ d_f * d_p := by
        refine le_trans (totalDegree_map_le _ _) ?_
        have h1 := totalDegree_bind₁_le pr f d_p (fun r =>
          le_trans (MvPolynomial.totalDegree_rename_le _ _) hp_deg)
        exact le_trans h1 (Nat.mul_le_mul_right d_p hf_deg)
      obtain ⟨a, haS, ha_ne⟩ := step_2_2_nonvanishing_proved _ hne S_grid (lt_of_le_of_lt hdegF hS_card)
      apply ha_ne
      have heval : MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom ℚ) F) =
          MvPolynomial.eval
            (nwMap S hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a)
            (MvPolynomial.map (Int.castRingHom ℚ) f) := by
        dsimp only [F]
        rw [MvPolynomial.eval_map, eval₂_bind₁_eq, MvPolynomial.eval_map]
        refine congrArg (fun fn => MvPolynomial.eval₂ (Int.castRingHom ℚ) fn f) ?_
        ext r
        dsimp only [pr, nwMap, emb]
        rw [MvPolynomial.eval₂_rename, MvPolynomial.eval_map]
        rfl
      rw [heval]
      exact hvanish a haS
    exact (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) (by rw [map_zero]; exact hFq_zero)
  let H (k : ℕ) : MvPolynomial (Fin l ⊕ Fin n) ℤ :=
    MvPolynomial.bind₁
      (fun r : Fin n => if r.val < k then MvPolynomial.rename Sum.inl (pr r) else MvPolynomial.X (Sum.inr r))
      f
  have hH0 : H 0 ≠ 0 := by
    have heq : H 0 = MvPolynomial.rename Sum.inr f := by
      dsimp only [H]
      simp only [Nat.not_lt_zero, ite_false]
      exact bind₁_X_comp_eq_rename Sum.inr f
    rw [heq]
    intro h0
    exact hf_nz ((MvPolynomial.rename_injective Sum.inr Sum.inr_injective) (by rw [map_zero]; exact h0))
  have hHn : H n = 0 := by
    have heq : H n = MvPolynomial.rename Sum.inl F := by
      dsimp only [H, F]
      have hcond : (fun r : Fin n => if r.val < n then MvPolynomial.rename Sum.inl (pr r)
          else MvPolynomial.X (Sum.inr r)) = fun r => MvPolynomial.rename Sum.inl (pr r) := by
        ext r; simp [r.isLt]
      rw [hcond]
      symm
      rw [MvPolynomial.rename_bind₁]
    rw [heq, hF_zero, map_zero]
  have hex_hybrid : ∃ k₀ < n, H k₀ ≠ 0 ∧ H (k₀ + 1) = 0 := by
    by_contra hall
    push Not at hall
    have hne_all : ∀ k ≤ n, H k ≠ 0 := by
      intro k
      induction k with
      | zero => intro _; exact hH0
      | succ k ih => intro hk; exact hall k (by omega) (ih (by omega))
    exact hne_all n le_rfl hHn
  rcases hex_hybrid with ⟨k₀, hk₀, hHk₀_ne, hHk₀1_zero⟩
  let iStar : Fin n := ⟨k₀, hk₀⟩
  let D : ℕ := d_f * (d_p + 1)
  have hHk₀_deg : (H k₀).totalDegree ≤ D := by
    have h1 := totalDegree_bind₁_le
      (fun r : Fin n => if r.val < k₀ then MvPolynomial.rename Sum.inl (pr r) else MvPolynomial.X (Sum.inr r))
      f (d_p + 1)
      (fun r => by
        by_cases hlt : r.val < k₀
        · simp only [if_pos hlt]
          have h1 := MvPolynomial.totalDegree_rename_le (Sum.inl : Fin l → Fin l ⊕ Fin n) (pr r)
          have h2 := MvPolynomial.totalDegree_rename_le (emb r) p
          dsimp only [pr] at h1 ⊢
          omega
        · simp only [if_neg hlt]
          have h1 := MvPolynomial.totalDegree_X (R := ℤ) (Sum.inr r : Fin l ⊕ Fin n)
          omega)
    exact le_trans h1 (Nat.mul_le_mul_right _ hf_deg)
  obtain ⟨βL, βR, hβL_le, hβR_le, hg_ne⟩ :=
    exists_bounded_nat_subst_ne_zero (H k₀) hHk₀_ne D hHk₀_deg (emb iStar) iStar
  refine ⟨k₀, hk₀, βL, βR, hβL_le, hβR_le, ?_⟩
  dsimp only
  let substL (u : Fin l) : MvPolynomial (Fin (m + 1)) ℤ :=
    if h : ∃ j : Fin m, emb iStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
    else MvPolynomial.C (βL u : ℤ)
  let substR (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
    if r = iStar then MvPolynomial.X (Fin.last m) else MvPolynomial.C (βR r : ℤ)
  let inp (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
    if r.val < k₀ then MvPolynomial.bind₁ (fun j => substL (emb r j)) p else substR r
  have hg_eq : MvPolynomial.bind₁ inp f = MvPolynomial.bind₁ (Sum.elim substL substR) (H k₀) := by
    dsimp only [H]
    rw [MvPolynomial.bind₁_bind₁]
    refine congrArg (fun fn => MvPolynomial.bind₁ fn f) ?_
    ext r
    dsimp only [Function.comp_def, inp]
    split_ifs with hlt
    · dsimp only [pr]
      rw [MvPolynomial.bind₁_rename, MvPolynomial.bind₁_rename]
      rfl
    · rw [MvPolynomial.bind₁_X_right]; rfl
  refine ⟨by rw [hg_eq]; exact hg_ne, ?_⟩
  rw [hg_eq]
  let φ : Fin l ⊕ Fin n → MvPolynomial (Fin m) ℤ :=
    Sum.elim
      (fun u => if h : ∃ j : Fin m, emb iStar j = u then MvPolynomial.X h.choose
                else MvPolynomial.C (βL u : ℤ))
      (fun r => MvPolynomial.C (βR r : ℤ))
  have hcomp :
      MvPolynomial.bind₁ (Fin.lastCases p fun j => MvPolynomial.X j)
        (MvPolynomial.bind₁ (Sum.elim substL substR) (H k₀)) =
      MvPolynomial.bind₁ φ (H (k₀ + 1)) := by
    rw [MvPolynomial.bind₁_bind₁]
    dsimp only [H]
    rw [MvPolynomial.bind₁_bind₁, MvPolynomial.bind₁_bind₁]
    refine congrArg (fun fn => MvPolynomial.bind₁ fn f) ?_
    funext r
    by_cases hr_lt : r.val < k₀
    · have hr_lt1 : r.val < k₀ + 1 := by omega
      simp only [if_pos hr_lt, if_pos hr_lt1]
      dsimp only [pr]
      rw [MvPolynomial.bind₁_rename, MvPolynomial.bind₁_rename, MvPolynomial.bind₁_rename,
          MvPolynomial.bind₁_rename]
      refine congrArg (fun fn => MvPolynomial.bind₁ fn p) ?_
      funext j
      dsimp only [Function.comp_def, Sum.elim, substL, φ]
      split_ifs with h
      · rw [MvPolynomial.bind₁_X_right, Fin.lastCases_castSucc]
      · rw [MvPolynomial.bind₁_C_right]
    · by_cases hr_eq : r.val = k₀
      · have hr_is : r = iStar := Fin.ext hr_eq
        have hr_lt1 : r.val < k₀ + 1 := by omega
        simp only [if_neg hr_lt, if_pos hr_lt1]
        rw [MvPolynomial.bind₁_X_right]
        dsimp only [Sum.elim, substR]
        rw [if_pos hr_is, MvPolynomial.bind₁_X_right, Fin.lastCases_last]
        dsimp only [pr]
        rw [MvPolynomial.bind₁_rename, MvPolynomial.bind₁_rename]
        subst hr_is
        have hid : (φ ∘ Sum.inl) ∘ ⇑(emb iStar) = MvPolynomial.X := by
          funext j
          have hex : ∃ j' : Fin m, emb iStar j' = emb iStar j := ⟨j, rfl⟩
          dsimp only [Function.comp_def, φ, Sum.elim]
          rw [dif_pos hex]
          have hch : hex.choose = j := (emb iStar).injective hex.choose_spec
          rw [hch]
        rw [hid, MvPolynomial.bind₁_X_left]; rfl
      · have hr_nlt1 : ¬ (r.val < k₀ + 1) := by omega
        have hr_ne : r ≠ iStar := fun h => hr_eq (congrArg Fin.val h)
        simp only [if_neg hr_lt, if_neg hr_nlt1]
        rw [MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right]
        dsimp only [Sum.elim, substR, φ]
        rw [if_neg hr_ne, MvPolynomial.bind₁_C_right]
  rw [hcomp, hHk₀1_zero, map_zero]

/-- Step 5 of Lemma 2.2: build `g_circ : IntCircuit (m + 1)` computing `g` with
polynomial encoding length `≤ 100 * s^5`, degree `≤ s^2`, and `CoeffBitBound g (8 * s^3)`. -/
private theorem build_hybrid_circuit {s m n l d_f d_p b : ℕ}
    (hs : 2 ≤ s) (hn : 2 ≤ n)
    (hmax : m ≤ s ∧ n ≤ s ∧ d_f ≤ s ∧ d_p ≤ s ∧ b ≤ s)
    (S : Fin n → Finset (Fin l)) (hcard : ∀ i, (S i).card = m)
    (hinter : ∀ i j : Fin n, i ≠ j → ((S i ∩ S j).card : ℝ) < Real.logb 2 n)
    (C_f : IntCircuit n) (hC_len : C_f.encodingLength ≤ s)
    (hf_deg : C_f.evalPoly.totalDegree ≤ d_f) (hf_bit : CoeffBitBound C_f.evalPoly b)
    (p : MvPolynomial (Fin m) ℤ) (hp_ml : IsMultilinear p)
    (hp_deg : p.totalDegree ≤ d_p) (hp_bit : CoeffBitBound p b)
    (k₀ : ℕ) (hk₀ : k₀ < n) (βL : Fin l → ℕ) (βR : Fin n → ℕ)
    (hβL_le : ∀ u, βL u ≤ d_f * (d_p + 1)) (hβR_le : ∀ r, βR r ≤ d_f * (d_p + 1)) :
    let emb (r : Fin n) : Fin m ↪o Fin l := (S r).orderEmbOfFin (hcard r)
    let iStar : Fin n := ⟨k₀, hk₀⟩
    let substL (u : Fin l) : MvPolynomial (Fin (m + 1)) ℤ :=
      if h : ∃ j : Fin m, emb iStar j = u then MvPolynomial.X (Fin.castSucc h.choose)
      else MvPolynomial.C (βL u : ℤ)
    let substR (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
      if r = iStar then MvPolynomial.X (Fin.last m) else MvPolynomial.C (βR r : ℤ)
    let inp (r : Fin n) : MvPolynomial (Fin (m + 1)) ℤ :=
      if r.val < k₀ then MvPolynomial.bind₁ (fun j => substL (emb r j)) p else substR r
    let g : MvPolynomial (Fin (m + 1)) ℤ := MvPolynomial.bind₁ inp C_f.evalPoly
    ∃ g_circ : IntCircuit (m + 1),
      g_circ.evalPoly = g ∧
      g_circ.encodingLength ≤ 100 * s ^ 5 ∧
      g.totalDegree ≤ s ^ 2 ∧
      CoeffBitBound g (8 * s ^ 3) := by
  classical
  rcases hmax with ⟨hms, hns, hds, hdps, hbs⟩
  intro emb iStar substL substR inp g
  let D : ℕ := d_f * (d_p + 1)
  have hD_le : D ≤ 2 * s ^ 2 := by dsimp [D]; nlinarith
  have hs_pow : s ≤ 2 ^ s := le_of_lt Nat.lt_two_pow_self
  have h2s2_pow : 2 * s ^ 2 ≤ 2 ^ (2 * s + 1) := by
    calc
      2 * s ^ 2 ≤ 2 * (2 ^ s) ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hs_pow 2)
      _ = 2 ^ (2 * s + 1) := by rw [← pow_mul, mul_comm s 2, ← pow_succ']
  have hsub_L1 : ∀ r : Fin n, polyL1 (inp r) ≤ 2 ^ (5 * s ^ 2) := by
    intro r
    dsimp only [inp]
    split_ifs with hr
    · have h1 := polyL1_bind₁_le (fun j => substL (emb r j)) p (2 ^ m) (2 ^ b) d_p (2 * s ^ 2)
        (by nlinarith) (multilinear_support_card_le p hp_ml) hp_bit hp_deg
        (fun j => by
          dsimp only [substL]
          split_ifs
          · rw [polyL1_X]; nlinarith
          · rw [polyL1_C]; simpa using le_trans (hβL_le _) hD_le)
      calc
        polyL1 (MvPolynomial.bind₁ (fun j => substL (emb r j)) p)
            ≤ 2 ^ m * 2 ^ b * (2 * s ^ 2) ^ d_p := h1
        _ ≤ 2 ^ s * 2 ^ s * (2 ^ (2 * s + 1)) ^ s := by
            refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hms)
              (Nat.pow_le_pow_right (by decide) hbs)) ?_
            exact le_trans (Nat.pow_le_pow_left h2s2_pow d_p)
              (Nat.pow_le_pow_right (Nat.pow_pos (by decide)) hdps)
        _ = 2 ^ (s + s + (2 * s + 1) * s) := by rw [← pow_mul, ← pow_add, ← pow_add]
        _ ≤ 2 ^ (5 * s ^ 2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
    · dsimp only [substR]
      split_ifs
      · rw [polyL1_X]; exact Nat.one_le_pow _ _ (by decide)
      · rw [polyL1_C]
        calc
          (βR r : ℤ).natAbs = βR r := Int.natAbs_natCast _
          _ ≤ 2 * s ^ 2 := le_trans (hβR_le r) hD_le
          _ ≤ 2 ^ (2 * s + 1) := h2s2_pow
          _ ≤ 2 ^ (5 * s ^ 2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  let Mbit : ℕ := 5 * s ^ 2 + 2
  have hsub_circ : ∀ r : Fin n, ∃ C_r : IntCircuit (m + 1),
      C_r.size ≤ 1 + s * (2 * s + 2) ∧
      (∀ k c, C_r.gate k = .const c → intBitLen c ≤ Mbit) ∧
      C_r.evalPoly = inp r := by
    intro r
    by_cases hr : r.val < k₀
    · have hne : r ≠ iStar := fun h => by have := congrArg Fin.val h; dsimp only [iStar] at this; omega
      have hprops := restricted_poly_props hn S hcard hinter p hp_ml r iStar hne βL
      have hdeg_q : (inp r).totalDegree ≤ s := by
        dsimp only [inp]; rw [if_pos hr]
        have h1 := totalDegree_bind₁_le (fun j => substL (emb r j)) p 1 (fun j => by
          dsimp only [substL]
          split_ifs
          · exact le_of_eq (MvPolynomial.totalDegree_X _)
          · rw [MvPolynomial.totalDegree_C]; omega)
        exact le_trans h1 (by simpa using le_trans hp_deg hdps)
      have hml_q : IsMultilinear (inp r) := by dsimp only [inp]; rw [if_pos hr]; exact hprops.1
      have hcard_q : (inp r).support.card ≤ s := by
        dsimp only [inp]; rw [if_pos hr]; exact le_trans hprops.2 hns
      have hbit_q : ∀ d, intBitLen ((inp r).coeff d) ≤ Mbit := fun d =>
        intBitLen_le_of_natAbs_le_two_pow _ _ (le_trans (coeff_natAbs_le_polyL1 _ d) (hsub_L1 r))
      exact exists_multilinear_circuit (inp r) hml_q s s Mbit hcard_q hdeg_q hbit_q (by dsimp [Mbit]; omega)
    · dsimp only [inp]; rw [if_neg hr]
      dsimp only [substR]
      by_cases heq : r = iStar
      · rw [if_pos heq]
        refine ⟨varCircuit (m + 1) (Fin.last m), by dsimp [varCircuit]; omega, ?_, varCircuit_evalPoly _ _⟩
        intro k c hkc; dsimp [varCircuit] at hkc; cases hkc
      · rw [if_neg heq]
        refine ⟨constCircuit (m + 1) (βR r : ℤ), by dsimp [constCircuit]; omega, ?_, constCircuit_evalPoly _ _⟩
        intro k c hkc; dsimp [constCircuit] at hkc; cases hkc
        have hle : ((βR r : ℤ)).natAbs ≤ 2 ^ (5 * s ^ 2) := by
          rw [Int.natAbs_natCast]
          exact le_trans (le_trans (hβR_le r) hD_le)
            (le_trans h2s2_pow (Nat.pow_le_pow_right (by decide) (by nlinarith)))
        exact intBitLen_le_of_natAbs_le_two_pow _ _ hle
  let sub : Fin n → IntCircuit (m + 1) := fun r => (hsub_circ r).choose
  let g_circ : IntCircuit (m + 1) := composeCircuits C_f sub
  have hg_circ_eval : g_circ.evalPoly = g := by
    dsimp only [g_circ, g]
    rw [composeCircuits_evalPoly]
    exact congrArg (fun fn => MvPolynomial.bind₁ fn C_f.evalPoly)
      (funext fun r => (hsub_circ r).choose_spec.2.2)
  have hCf_sz : C_f.size ≤ s := le_trans (intCircuit_size_le_encodingLength C_f) hC_len
  have hg_circ_sz : g_circ.size ≤ 5 * s ^ 3 := by
    have h1 := composeCircuits_size_le C_f sub (1 + s * (2 * s + 2)) (by omega)
      (fun r => (hsub_circ r).choose_spec.1)
    nlinarith
  have hg_circ_const : ∀ k a, g_circ.gate k = .const a → intBitLen a ≤ Mbit :=
    composeCircuits_constBound C_f sub Mbit (by dsimp [Mbit]; omega)
      (fun k a hka => le_trans (le_trans (intCircuit_constBitLen_le_encodingLength C_f k a hka) hC_len)
        (by dsimp [Mbit]; nlinarith))
      (fun r => (hsub_circ r).choose_spec.2.1)
  have hg_circ_len : g_circ.encodingLength ≤ 100 * s ^ 5 := by
    have h1 := intCircuit_encodingLength_le g_circ Mbit hg_circ_const
    have hclog : Nat.clog 2 (g_circ.size + (m + 1) + 2) ≤ 4 * s ^ 2 := by
      have harg : g_circ.size + (m + 1) + 2 ≤ 2 ^ (4 * s ^ 2) := by
        have h2 : g_circ.size + (m + 1) + 2 ≤ 8 * s ^ 3 := by nlinarith
        have h3 : 8 * s ^ 3 ≤ 2 ^ (3 + 3 * s) := by
          calc
            8 * s ^ 3 ≤ 2 ^ 3 * (2 ^ s) ^ 3 :=
              Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hs_pow 3)
            _ = 2 ^ (3 + 3 * s) := by rw [← pow_mul, mul_comm s 3, ← pow_add]
        exact le_trans h2 (le_trans h3 (Nat.pow_le_pow_right (by decide) (by nlinarith)))
      exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr harg
    have hfac : 2 * Nat.clog 2 (g_circ.size + (m + 1) + 2) + Mbit + 2 ≤ 20 * s ^ 2 := by
      dsimp [Mbit]; nlinarith
    calc
      g_circ.encodingLength ≤ g_circ.size * (2 * Nat.clog 2 (g_circ.size + (m + 1) + 2) + Mbit + 2) := h1
      _ ≤ (5 * s ^ 3) * (20 * s ^ 2) := Nat.mul_le_mul hg_circ_sz hfac
      _ = 100 * s ^ 5 := by ring
  have hg_deg : g.totalDegree ≤ s ^ 2 := by
    have h1 := totalDegree_bind₁_le inp C_f.evalPoly s (fun r => by
      dsimp only [inp]
      split_ifs
      · have h2 := totalDegree_bind₁_le (fun j => substL (emb r j)) p 1 (fun j => by
          dsimp only [substL]; split_ifs
          · exact le_of_eq (MvPolynomial.totalDegree_X _)
          · rw [MvPolynomial.totalDegree_C]; omega)
        exact le_trans h2 (by simpa using le_trans hp_deg hdps)
      · dsimp only [substR]; split_ifs
        · rw [MvPolynomial.totalDegree_X]; omega
        · rw [MvPolynomial.totalDegree_C]; omega)
    have h2 : C_f.evalPoly.totalDegree * s ≤ s * s := Nat.mul_le_mul_right s (le_trans hf_deg hds)
    simpa [sq] using le_trans h1 h2
  have hg_bit : CoeffBitBound g (8 * s ^ 3) := by
    intro d
    have hf_supp : C_f.evalPoly.support.card ≤ 2 ^ (2 * s) := by
      let pad : Fin n → Fin s := fun r => ⟨r.val, lt_of_lt_of_le r.isLt hns⟩
      have hpad_inj : Function.Injective pad := fun a b h =>
        Fin.ext (by simpa [pad] using congrArg Fin.val h)
      let fpad : MvPolynomial (Fin s) ℤ := MvPolynomial.rename pad C_f.evalPoly
      have hdeg_pad : fpad.totalDegree ≤ s :=
        le_trans (MvPolynomial.totalDegree_rename_le _ _) (le_trans hf_deg hds)
      have hcard_le : C_f.evalPoly.support.card ≤ fpad.support.card := by
        have hinj : Function.Injective (Finsupp.mapDomain (M := ℕ) pad) :=
          Finsupp.mapDomain_injective hpad_inj
        rw [← Finset.card_image_of_injective C_f.evalPoly.support hinj]
        refine Finset.card_le_card fun e he => ?_
        rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
        rw [MvPolynomial.mem_support_iff] at hx ⊢
        dsimp only [fpad]
        rwa [MvPolynomial.coeff_rename_mapDomain _ hpad_inj]
      exact le_trans hcard_le (support_card_le_pow_two_mul fpad hdeg_pad)
    have hL1 := polyL1_bind₁_le inp C_f.evalPoly (2 ^ (2 * s)) (2 ^ b) s (2 ^ (5 * s ^ 2))
      (Nat.one_le_pow _ _ (by decide)) hf_supp hf_bit (le_trans hf_deg hds) hsub_L1
    have hexp_le : 2 * s + s + 5 * s ^ 2 * s ≤ 8 * s ^ 3 := by
      have hs1 : s ≤ s ^ 3 := le_self_pow₀ (by omega) (by decide)
      have hs3 : 5 * s ^ 2 * s = 5 * s ^ 3 := by ring
      omega
    calc
      (g.coeff d).natAbs ≤ polyL1 g := coeff_natAbs_le_polyL1 g d
      _ ≤ 2 ^ (2 * s) * 2 ^ b * (2 ^ (5 * s ^ 2)) ^ s := hL1
      _ ≤ 2 ^ (2 * s) * 2 ^ s * (2 ^ (5 * s ^ 2)) ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hbs))
      _ = 2 ^ (2 * s + s + 5 * s ^ 2 * s) := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ (8 * s ^ 3) := Nat.pow_le_pow_right (by decide) hexp_le
  exact ⟨g_circ, hg_circ_eval, hg_circ_len, hg_deg, hg_bit⟩

/-- Lemma 2.2 (full reconstruction theorem from `KI04_Cor_7_4`). -/
theorem lem_2_2_reconstruction_proved (hKI : KI04_Cor_7_4) :
    ∃ κ : ℕ, 1 ≤ κ ∧
      ∀ (s m n d_f d_p b : ℕ) (hs : 2 ≤ s) (hn : 2 ≤ n)
        (hm_gt : Real.logb 2 n < (m : ℝ)) (hmn : m ≤ n)
        (hmax : m ≤ s ∧ n ≤ s ∧ d_f ≤ s ∧ d_p ≤ s ∧ b ≤ s)
        (C_f : IntCircuit n) (hC_len : C_f.encodingLength ≤ s)
        (hf_nz : C_f.evalPoly ≠ 0) (hf_deg : C_f.evalPoly.totalDegree ≤ d_f)
        (hf_bit : CoeffBitBound C_f.evalPoly b)
        (p : MvPolynomial (Fin m) ℤ) (hp_nz : p ≠ 0) (hp_ml : IsMultilinear p)
        (hp_deg : p.totalDegree ≤ d_p) (hp_bit : CoeffBitBound p b)
        (S_grid : Finset ℚ) (hS_card : d_f * d_p < S_grid.card),
        have hm2 : 2 ≤ m := by
          have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
            rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
            exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
          exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast lt_of_le_of_lt h1 hm_gt)
        ∀ (hcard : ∀ i : Fin n, (designSets m n hm2 i).card = m),
        (∀ a : Fin (designL m) → ℚ, (∀ j, a j ∈ S_grid) →
          MvPolynomial.eval
            (nwMap (designSets m n hm2) hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a)
            (MvPolynomial.map (Int.castRingHom ℚ) C_f.evalPoly) = 0) →
        Computes (MvPolynomial.map (Int.castRingHom ℚ) p) (s ^ κ) := by
  rcases hKI with ⟨c_ki, e_ki, hc_ki, he_ki, hKI_body⟩
  let C_poly : ℕ := 200
  let κ : ℕ := 6 * e_ki + Nat.clog 2 (3 * c_ki * C_poly ^ e_ki) + 1
  refine ⟨κ, by omega, ?_⟩
  intro s m n d_f d_p b hs hn hm_gt hmn hmax C_f hC_len hf_nz hf_deg hf_bit
    p _hp_nz hp_ml hp_deg hp_bit S_grid hS_card hm2 hcard hvanish
  have hdesign := lem_2_1_design_proved m n hn hm_gt hmn
  have hinter := hdesign.2.2
  obtain ⟨k₀, hk₀, βL, βR, hβL, hβR, hg_nz, hg_root⟩ :=
    hybrid_witness_exists (designSets m n hm2) hcard C_f.evalPoly hf_nz hf_deg p hp_deg
      S_grid hS_card hvanish
  obtain ⟨g_circ, hg_eval, hg_len, hg_deg, hg_bit⟩ :=
    build_hybrid_circuit hs hn hmax (designSets m n hm2) hcard hinter C_f hC_len hf_deg hf_bit
      p hp_ml hp_deg hp_bit k₀ hk₀ βL βR hβL hβR
  obtain ⟨C_p, hCp_sz, hCp_eval⟩ := hKI_body m g_circ (s ^ 2) (8 * s ^ 3) p
    (by rw [hg_eval]; exact hg_nz)
    (by rw [hg_eval]; exact hg_deg)
    (by rw [hg_eval]; exact hg_bit)
    (by rw [hg_eval]; exact hg_root)
  have htr := step_2_2_model_transfer_proved C_p
  have hCp_eq : C_p.evalPoly = MvPolynomial.map (Int.castRingHom ℚ) p :=
    htr.2 (MvPolynomial.map (Int.castRingHom ℚ) p) hCp_eval
  have hcomp_p : Computes (MvPolynomial.map (Int.castRingHom ℚ) p) (3 * C_p.size) := by
    rw [← hCp_eq]; exact htr.1
  have hsz_le : 3 * C_p.size ≤ s ^ κ := by
    have hbase : g_circ.encodingLength + s ^ 2 + 8 * s ^ 3 + 2 ≤ C_poly * s ^ 5 := by
      have hs2_5 : s ^ 2 ≤ s ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
      have hs3_5 : s ^ 3 ≤ s ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
      have h1_5 : 1 ≤ s ^ 5 := Nat.one_le_pow 5 s (by omega)
      dsimp [C_poly]; omega
    have hmul : 3 * C_p.size ≤ (3 * c_ki * C_poly ^ e_ki) * s ^ (5 * e_ki) := by
      calc
        3 * C_p.size ≤ 3 * (c_ki * (g_circ.encodingLength + s ^ 2 + 8 * s ^ 3 + 2) ^ e_ki) :=
            Nat.mul_le_mul_left 3 hCp_sz
        _ ≤ 3 * (c_ki * (C_poly * s ^ 5) ^ e_ki) :=
            Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left c_ki (Nat.pow_le_pow_left hbase e_ki))
        _ = (3 * c_ki * C_poly ^ e_ki) * s ^ (5 * e_ki) := by
            rw [mul_pow, ← pow_mul]; ring
    have hclog_le : 3 * c_ki * C_poly ^ e_ki ≤ s ^ Nat.clog 2 (3 * c_ki * C_poly ^ e_ki) :=
      le_trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)
        (Nat.pow_le_pow_left hs _)
    calc
      3 * C_p.size ≤ (3 * c_ki * C_poly ^ e_ki) * s ^ (5 * e_ki) := hmul
      _ ≤ s ^ Nat.clog 2 (3 * c_ki * C_poly ^ e_ki) * s ^ (5 * e_ki) :=
          Nat.mul_le_mul_right _ hclog_le
      _ = s ^ (Nat.clog 2 (3 * c_ki * C_poly ^ e_ki) + 5 * e_ki) := (pow_add _ _ _).symm
      _ ≤ s ^ κ := Nat.pow_le_pow_right (by omega) (by dsimp [κ]; omega)
  exact computes_mono hcomp_p hsz_le

end ExactMatching.Proofs
