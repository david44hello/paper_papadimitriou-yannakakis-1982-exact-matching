/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.Circuits
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Strassen (1973) homogenization and degree-`≤ d` truncation for `RatCircuit`

Standalone module exporting:
- `ZeroMod`: every monomial in the support of `f` has total degree at least `N`.
- `ZeroMod` closure lemmas (`zero`, `mono`, `neg`, `add`, `sub`, `C_mul`, `mul`).
- `sum_homogeneousComponent_eq_of_zeroMod`: if `Y - p` is `ZeroMod (d + 1)` and
  `p.totalDegree ≤ d`, then `∑ r ∈ Finset.range (d + 1), homogeneousComponent r Y = p`.
- `ratCircuit_homog_trunc`: uniform `2 * (d + 1)^2` wire-expansion converting any
  `C : RatCircuit m` into a strictly division-free `RatCircuit m` of size
  `≤ (2 * (d + 1)^2 + 2 * (d + 1) + 4) * C.size + (d + 2)` computing
  `∑ r ∈ Finset.range (d + 1), homogeneousComponent r C.evalPoly`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: `ZeroMod` predicate, algebra helpers, and truncation recovery -/

/-- Every monomial in the support of `f` has total degree at least `N`. -/
def ZeroMod {m : ℕ} (N : ℕ) (f : MvPolynomial (Fin m) ℚ) : Prop :=
  ∀ e ∈ f.support, N ≤ e.sum (fun _ v => v)

theorem zeroMod_zero {m : ℕ} (N : ℕ) : ZeroMod (m := m) N 0 := by
  intro e he; simp at he

theorem zeroMod_mono {m N₁ N₂ : ℕ} {f : MvPolynomial (Fin m) ℚ}
    (hle : N₁ ≤ N₂) (h : ZeroMod N₂ f) : ZeroMod N₁ f :=
  fun e he => le_trans hle (h e he)

theorem zeroMod_neg {m N : ℕ} {f : MvPolynomial (Fin m) ℚ}
    (h : ZeroMod N f) : ZeroMod N (-f) := by
  intro e he
  apply h e
  rw [MvPolynomial.mem_support_iff] at he ⊢
  have hneg : (-f).coeff e = -(f.coeff e) := by simp
  rw [hneg] at he
  exact neg_ne_zero.mp he

theorem zeroMod_add {m N : ℕ} {f g : MvPolynomial (Fin m) ℚ}
    (hf : ZeroMod N f) (hg : ZeroMod N g) : ZeroMod N (f + g) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h1 | h2
  · exact hf e h1
  · exact hg e h2

theorem zeroMod_sub {m N : ℕ} {f g : MvPolynomial (Fin m) ℚ}
    (hf : ZeroMod N f) (hg : ZeroMod N g) : ZeroMod N (f - g) := by
  rw [sub_eq_add_neg]
  exact zeroMod_add hf (zeroMod_neg hg)

theorem zeroMod_C_mul {m N : ℕ} (a : ℚ) {f : MvPolynomial (Fin m) ℚ}
    (hf : ZeroMod N f) : ZeroMod N (MvPolynomial.C a * f) := by
  intro e he
  apply hf e
  rw [MvPolynomial.mem_support_iff] at he ⊢
  rw [MvPolynomial.coeff_C_mul] at he
  exact right_ne_zero_of_mul he

theorem zeroMod_mul {m N₁ N₂ : ℕ} {f g : MvPolynomial (Fin m) ℚ}
    (hf : ZeroMod N₁ f) (hg : ZeroMod N₂ g) : ZeroMod (N₁ + N₂) (f * g) := by
  classical
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at he
  have hex : ∃ x ∈ Finset.antidiagonal e, f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he (Finset.sum_eq_zero hall)
  rcases hex with ⟨x, hx, hne⟩
  have h1 : N₁ ≤ x.1.sum (fun _ v => v) :=
    hf x.1 (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne))
  have h2 : N₂ ≤ x.2.sum (fun _ v => v) :=
    hg x.2 (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne))
  have hadd : x.1 + x.2 = e := Finset.mem_antidiagonal.mp hx
  have hdeg : e.sum (fun _ v => v) = x.1.sum (fun _ v => v) + x.2.sum (fun _ v => v) := by
    rw [← hadd]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  omega

/-- If `Y - p` has no monomials of degree `≤ d` and `p.totalDegree ≤ d`, then the sum of
the homogeneous components of `Y` of degrees `0..d` equals `p`. -/
theorem sum_homogeneousComponent_eq_of_zeroMod {m d : ℕ}
    (Y p : MvPolynomial (Fin m) ℚ)
    (hp : p.totalDegree ≤ d)
    (hmod : ZeroMod (d + 1) (Y - p)) :
    (∑ r ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent r Y) = p := by
  ext e
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hle : e.degree ≤ d
  · have hmem : e.degree ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single e.degree]
    · rw [if_pos rfl]
      by_contra hne
      have hsub_ne : (Y - p).coeff e ≠ 0 := by
        have hsub : (Y - p).coeff e = Y.coeff e - p.coeff e := by simp
        rw [hsub]
        exact sub_ne_zero.mpr hne
      have hge := hmod e (MvPolynomial.mem_support_iff.mpr hsub_ne)
      change d + 1 ≤ e.degree at hge
      omega
    · intro r _ hne
      exact if_neg (Ne.symm hne)
    · intro hnot; exact absurd hmem hnot
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      have hmem : e ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
      have hdeg_le : e.degree ≤ p.totalDegree :=
        Finset.le_sup (f := fun e : Fin m →₀ ℕ => e.sum fun _ v => v) hmem
      omega
    · intro r hr
      have hr_le : r ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      exact if_neg (by omega)

/-! ### Part 2: Homogeneous-component identities and `RatCircuit` gate evaluation helpers -/

private theorem degree_add_eq {σ : Type*} (x y : σ →₀ ℕ) :
    (x + y).degree = x.degree + y.degree := by
  change (x + y).sum (fun _ v => v) = x.sum (fun _ v => v) + y.sum (fun _ v => v)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private theorem homogeneousComponent_X_eq {m : ℕ} (r : ℕ) (v : Fin m) :
    MvPolynomial.homogeneousComponent r (MvPolynomial.X v : MvPolynomial (Fin m) ℚ) =
      if r = 1 then MvPolynomial.X v else 0 := by
  ext e
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases he : e = Finsupp.single v 1
  · subst he
    have hdeg : (Finsupp.single v (1 : ℕ)).degree = 1 := by
      change (Finsupp.single v (1 : ℕ)).sum (fun _ k => k) = 1
      simp
    rw [hdeg]
    by_cases hr : r = 1
    · subst hr; simp
    · simp [hr, Ne.symm hr]
  · have hX0 : (MvPolynomial.X v : MvPolynomial (Fin m) ℚ).coeff e = 0 := by
      rw [MvPolynomial.coeff_X']
      exact if_neg (Ne.symm he)
    split_ifs <;> simp [hX0]

private theorem homogeneousComponent_C_eq {m : ℕ} (r : ℕ) (a : ℚ) :
    MvPolynomial.homogeneousComponent r (MvPolynomial.C a : MvPolynomial (Fin m) ℚ) =
      if r = 0 then MvPolynomial.C a else 0 := by
  ext e
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases he : e = 0
  · subst he
    have hdeg : (0 : Fin m →₀ ℕ).degree = 0 := by
      change (0 : Fin m →₀ ℕ).sum (fun _ k => k) = 0
      simp
    rw [hdeg]
    by_cases hr : r = 0
    · subst hr; simp
    · simp [hr, Ne.symm hr]
  · have hC0 : (MvPolynomial.C a : MvPolynomial (Fin m) ℚ).coeff e = 0 := by
      rw [MvPolynomial.coeff_C]
      exact if_neg (Ne.symm he)
    split_ifs <;> simp [hC0]

private theorem homogeneousComponent_mul_range {m : ℕ} (r : ℕ)
    (P Q : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.homogeneousComponent r (P * Q) =
      ∑ a ∈ Finset.range (r + 1),
        MvPolynomial.homogeneousComponent a P * MvPolynomial.homogeneousComponent (r - a) Q := by
  classical
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_homogeneousComponent]
  rw [Finset.sum_comm]
  by_cases hd : d.degree = r
  · rw [if_pos hd]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxsum : x.1.degree + x.2.degree = r := by
      have h1 : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
      rw [← h1, degree_add_eq] at hd
      exact hd
    have hlt : x.1.degree ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single x.1.degree]
    · have h2 : x.2.degree = r - x.1.degree := by omega
      simp [h2]
    · intro a _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro hnot; exact absurd hlt hnot
  · rw [if_neg hd, Finset.sum_eq_zero]
    intro x hx
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha_le : a ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    by_cases h1 : x.1.degree = a
    · have h2 : x.2.degree ≠ r - a := by
        intro heq
        apply hd
        have hadd : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
        rw [← hadd, degree_add_eq, h1, heq]
        omega
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem ratEvalGate_var {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (v : Fin m)
    (h : C.gate k = .var v) : C.evalGatePoly k = MvPolynomial.X v := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all

private theorem ratEvalGate_const {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (a : ℚ)
    (h : C.gate k = .const a) : C.evalGatePoly k = MvPolynomial.C a := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all

private theorem ratEvalGate_add {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .add i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ + C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem ratEvalGate_sub {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .sub i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ - C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem ratEvalGate_mul {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .mul i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ * C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem ratEvalGate_smul {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (a : ℚ) (i : ℕ)
    (h : C.gate k = .smul a i) (hi : i < C.size) :
    C.evalGatePoly k = MvPolynomial.C a * C.evalGatePoly ⟨i, hi⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; exact Or.inl rfl

/-! ### Part 3: Uniform `2 * (d + 1)^2` homogenization wire-expansion (`ratCircuit_homog_trunc`) -/

private def hProdSlot (D idx a b : ℕ) : ℕ :=
  1 + idx * (2 * D ^ 2) + (a * D + b)

private def hSumSlot (D idx r t : ℕ) : ℕ :=
  1 + idx * (2 * D ^ 2) + D ^ 2 + (r * D + t)

private def hWireIdx (d idx r : ℕ) : ℕ :=
  hSumSlot (d + 1) idx r d

private def expandHomogGate {m : ℕ} (d idx off : ℕ) (gt : RatGate m) : RatGate m :=
  let D := d + 1
  match gt with
  | .var v =>
    if D ^ 2 ≤ off ∧ (off - D ^ 2) % D = d then
      if (off - D ^ 2) / D = 1 then .var v else .const 0
    else .const 0
  | .const a =>
    if D ^ 2 ≤ off ∧ (off - D ^ 2) % D = d then
      if (off - D ^ 2) / D = 0 then .const a else .const 0
    else .const 0
  | .add i j =>
    if D ^ 2 ≤ off ∧ (off - D ^ 2) % D = d then
      .add (hWireIdx d i ((off - D ^ 2) / D)) (hWireIdx d j ((off - D ^ 2) / D))
    else .const 0
  | .sub i j =>
    if D ^ 2 ≤ off ∧ (off - D ^ 2) % D = d then
      .sub (hWireIdx d i ((off - D ^ 2) / D)) (hWireIdx d j ((off - D ^ 2) / D))
    else .const 0
  | .smul a i =>
    if D ^ 2 ≤ off ∧ (off - D ^ 2) % D = d then
      .smul a (hWireIdx d i ((off - D ^ 2) / D))
    else .const 0
  | .mul i j =>
    if off < D ^ 2 then
      .mul (hWireIdx d i (off / D)) (hWireIdx d j (off % D))
    else
      let rel := off - D ^ 2
      let r := rel / D
      let t := rel % D
      if t = 0 then
        .add (hProdSlot D idx 0 r) 0
      else if t ≤ r then
        .add (hSumSlot D idx r (t - 1)) (hProdSlot D idx t (r - t))
      else
        .add (hSumSlot D idx r (t - 1)) 0

private theorem expandHomogGate_wf {m : ℕ} (d idx off : ℕ)
    (hoff : off < 2 * (d + 1) ^ 2) (gt : RatGate m) (hwf : gt.WF idx) :
    (expandHomogGate d idx off gt).WF (1 + idx * (2 * (d + 1) ^ 2) + off) := by
  let D := d + 1
  have hDpos : 0 < D := Nat.succ_pos d
  have hwire_lt : ∀ i r : ℕ, i < idx → r < D →
      hWireIdx d i r < 1 + idx * (2 * D ^ 2) + off := by
    intro i r hi hr
    dsimp only [hWireIdx, hSumSlot, D]
    have h1 : (i + 1) * (2 * (d + 1) ^ 2) ≤ idx * (2 * (d + 1) ^ 2) :=
      Nat.mul_le_mul_right _ hi
    have h2 : (r + 1) * (d + 1) ≤ (d + 1) * (d + 1) := Nat.mul_le_mul_right _ hr
    nlinarith
  cases gt with
  | var v => unfold expandHomogGate; dsimp only; split_ifs <;> trivial
  | const a => unfold expandHomogGate; dsimp only; split_ifs <;> trivial
  | add i j =>
    unfold expandHomogGate; dsimp only
    split_ifs with h
    · have hr : (off - D ^ 2) / D < D := by
        have hsub : off - D ^ 2 < D * D := by dsimp only [D]; rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      exact ⟨hwire_lt i _ hwf.1 hr, hwire_lt j _ hwf.2 hr⟩
    · trivial
  | sub i j =>
    unfold expandHomogGate; dsimp only
    split_ifs with h
    · have hr : (off - D ^ 2) / D < D := by
        have hsub : off - D ^ 2 < D * D := by dsimp only [D]; rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      exact ⟨hwire_lt i _ hwf.1 hr, hwire_lt j _ hwf.2 hr⟩
    · trivial
  | smul a i =>
    unfold expandHomogGate; dsimp only
    split_ifs with h
    · have hr : (off - D ^ 2) / D < D := by
        have hsub : off - D ^ 2 < D * D := by dsimp only [D]; rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      exact hwire_lt i _ hwf hr
    · trivial
  | mul i j =>
    unfold expandHomogGate; dsimp only
    split_ifs with hp ht0 htr
    · have ha : off / D < D := Nat.div_lt_of_lt_mul (by dsimp only [D] at *; simpa [sq] using hp)
      have hb : off % D < D := Nat.mod_lt _ hDpos
      exact ⟨hwire_lt i _ hwf.1 ha, hwire_lt j _ hwf.2 hb⟩
    · dsimp only [RatGate.WF, hProdSlot]
      have hr : (off - (d + 1) ^ 2) / (d + 1) < d + 1 := by
        have hsub : off - (d + 1) ^ 2 < (d + 1) * (d + 1) := by rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      have hlt : 0 * (d + 1) + (off - (d + 1) ^ 2) / (d + 1) < (d + 1) ^ 2 := by nlinarith
      exact ⟨by omega, by omega⟩
    · dsimp only [RatGate.WF, hSumSlot, hProdSlot]
      have hdiv : ((off - (d + 1) ^ 2) / (d + 1)) * (d + 1) + (off - (d + 1) ^ 2) % (d + 1) =
          off - (d + 1) ^ 2 := by
        have h1 := Nat.div_add_mod (off - (d + 1) ^ 2) (d + 1)
        rw [Nat.mul_comm] at h1; exact h1
      have ht : (off - (d + 1) ^ 2) % (d + 1) < d + 1 := Nat.mod_lt _ hDpos
      have hr : (off - (d + 1) ^ 2) / (d + 1) < d + 1 := by
        have hsub : off - (d + 1) ^ 2 < (d + 1) * (d + 1) := by rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      have hprod : ((off - (d + 1) ^ 2) % (d + 1)) * (d + 1) +
          ((off - (d + 1) ^ 2) / (d + 1) - (off - (d + 1) ^ 2) % (d + 1)) < (d + 1) ^ 2 := by
        have h1 : ((off - (d + 1) ^ 2) % (d + 1) + 1) * (d + 1) ≤ (d + 1) * (d + 1) :=
          Nat.mul_le_mul_right (d + 1) ht
        have h2 : (off - (d + 1) ^ 2) / (d + 1) - (off - (d + 1) ^ 2) % (d + 1) < d + 1 := by omega
        nlinarith
      exact ⟨by omega, by omega⟩
    · dsimp only [RatGate.WF, hSumSlot]
      have hdiv : ((off - (d + 1) ^ 2) / (d + 1)) * (d + 1) + (off - (d + 1) ^ 2) % (d + 1) =
          off - (d + 1) ^ 2 := by
        have h1 := Nat.div_add_mod (off - (d + 1) ^ 2) (d + 1)
        rw [Nat.mul_comm] at h1; exact h1
      exact ⟨by omega, by omega⟩

/-- Strassen homogenization: given any `C : RatCircuit m` and degree bound `d`, constructs a
`RatCircuit m` computing `∑ r ∈ Finset.range (d + 1), homogeneousComponent r C.evalPoly`
of size `≤ (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) * C.size + (d + 2)`. -/
theorem ratCircuit_homog_trunc {m : ℕ} (C : RatCircuit m) (d : ℕ) :
    ∃ C_h : RatCircuit m,
      C_h.size ≤ (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) * C.size + (d + 2) ∧
      C_h.evalPoly = ∑ r ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent r C.evalPoly := by
  set D := d + 1 with hD_def
  have hDpos : 0 < D := Nat.succ_pos d
  set B := 2 * D ^ 2 with hB_def
  have hBpos : 0 < B := by dsimp [B, D]; nlinarith
  set base := 1 + C.size * B with hbase_def
  set N_out := base + D with hN_def
  have hN_le : N_out ≤ (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) * C.size + (d + 2) := by
    have h1 : N_out = 2 * (d + 1) ^ 2 * C.size + (d + 2) := by
      dsimp only [N_out, base, B, D]; ring
    rw [h1]
    nlinarith
  have hsum_lt_base : ∀ (idx : ℕ), idx < C.size → ∀ r t : ℕ, r < D → t < D →
      hSumSlot D idx r t < base := by
    intro idx hidx r t hr ht
    dsimp only [hSumSlot, base, B]
    have h1 : (idx + 1) * (2 * D ^ 2) ≤ C.size * (2 * D ^ 2) := Nat.mul_le_mul_right _ hidx
    have h2 : (r + 1) * D ≤ D * D := Nat.mul_le_mul_right D hr
    nlinarith
  have hprod_lt_base : ∀ (idx : ℕ), idx < C.size → ∀ a b : ℕ, a < D → b < D →
      hProdSlot D idx a b < base := by
    intro idx hidx a b ha hb
    dsimp only [hProdSlot, base, B]
    have h1 : (idx + 1) * (2 * D ^ 2) ≤ C.size * (2 * D ^ 2) := Nat.mul_le_mul_right _ hidx
    have h2 : (a + 1) * D ≤ D * D := Nat.mul_le_mul_right D ha
    nlinarith
  have hwire_lt_base : ∀ (idx : ℕ), idx < C.size → ∀ r : ℕ, r < D →
      hWireIdx d idx r < base :=
    fun idx hidx r hr => hsum_lt_base idx hidx r d hr (by dsimp [D]; omega)
  let gateFn : Fin N_out → RatGate m := fun slot =>
    if _h0 : slot.val = 0 then .const 0
    else if _hb : slot.val < base then
      let idx := (slot.val - 1) / B
      let off := (slot.val - 1) % B
      if hidx : idx < C.size then
        expandHomogGate d idx off (C.gate ⟨idx, hidx⟩)
      else .const 0
    else
      let r := slot.val - base
      if r = 0 then .add (hWireIdx d C.out.val 0) 0
      else .add (base + (r - 1)) (hWireIdx d C.out.val r)
  have hwf : ∀ slot : Fin N_out, (gateFn slot).WF slot.val := by
    intro slot
    dsimp only [gateFn]
    split_ifs with h0 hb hidx hr0
    · trivial
    · have hslot_eq :
          1 + ((slot.val - 1) / B) * (2 * (d + 1) ^ 2) + (slot.val - 1) % B = slot.val := by
        have h1 := Nat.div_add_mod (slot.val - 1) B
        rw [Nat.mul_comm] at h1
        change 1 + ((slot.val - 1) / B) * B + (slot.val - 1) % B = slot.val
        omega
      have hwf' := expandHomogGate_wf d ((slot.val - 1) / B) ((slot.val - 1) % B)
        (Nat.mod_lt _ hBpos) (C.gate ⟨_, hidx⟩) (C.wf ⟨_, hidx⟩)
      rwa [hslot_eq] at hwf'
    · trivial
    · have hlt := hwire_lt_base C.out.val C.out.isLt 0 hDpos
      exact ⟨by omega, by omega⟩
    · have hr_lt : slot.val - base < D := by omega
      have hlt := hwire_lt_base C.out.val C.out.isLt (slot.val - base) hr_lt
      exact ⟨by omega, by omega⟩
  let C_h : RatCircuit m :=
    { size := N_out
      size_pos := by dsimp [N_out, base]; omega
      gate := gateFn
      wf := hwf
      out := ⟨base + d, by dsimp [N_out, D]; omega⟩ }
  have hCh_sz : C_h.size = base + D := rfl
  have hgate0 : C_h.evalGatePoly ⟨0, C_h.size_pos⟩ = 0 := by
    have h0 : C_h.gate ⟨0, C_h.size_pos⟩ = .const 0 := by simp [C_h, gateFn]
    simpa using ratEvalGate_const C_h ⟨0, C_h.size_pos⟩ 0 h0
  have hgate_at_sum : ∀ (idx : ℕ) (hidx : idx < C.size) (r t : ℕ) (hr : r < D) (ht : t < D),
      C_h.gate ⟨hSumSlot D idx r t, lt_trans (hsum_lt_base idx hidx r t hr ht) (by omega)⟩ =
        expandHomogGate d idx (D ^ 2 + (r * D + t)) (C.gate ⟨idx, hidx⟩) := by
    intro idx hidx r t hr ht
    have hltB : D ^ 2 + (r * D + t) < B := by
      have h1 : (r + 1) * D ≤ D * D := Nat.mul_le_mul_right D hr
      dsimp [B]; nlinarith
    have hne0 : hSumSlot D idx r t ≠ 0 := by dsimp [hSumSlot]; omega
    have hltb : hSumSlot D idx r t < base := hsum_lt_base idx hidx r t hr ht
    have heq : hSumSlot D idx r t - 1 = idx * B + (D ^ 2 + (r * D + t)) := by
      dsimp [hSumSlot, B]; omega
    have hdiv : (hSumSlot D idx r t - 1) / B = idx := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hltB, Nat.add_zero]
    have hmod : (hSumSlot D idx r t - 1) % B = D ^ 2 + (r * D + t) := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_mod, Nat.mod_eq_of_lt hltB]
    dsimp only [C_h, gateFn]
    rw [dif_neg hne0, dif_pos hltb, hdiv, hmod, dif_pos hidx]
  have hgate_at_prod : ∀ (idx : ℕ) (hidx : idx < C.size) (a b : ℕ) (ha : a < D) (hb : b < D),
      C_h.gate ⟨hProdSlot D idx a b, lt_trans (hprod_lt_base idx hidx a b ha hb) (by omega)⟩ =
        expandHomogGate d idx (a * D + b) (C.gate ⟨idx, hidx⟩) := by
    intro idx hidx a b ha hb
    have hltB : a * D + b < B := by
      have h1 : (a + 1) * D ≤ D * D := Nat.mul_le_mul_right D ha
      dsimp [B]; nlinarith
    have hne0 : hProdSlot D idx a b ≠ 0 := by dsimp [hProdSlot]; omega
    have hltb : hProdSlot D idx a b < base := hprod_lt_base idx hidx a b ha hb
    have heq : hProdSlot D idx a b - 1 = idx * B + (a * D + b) := by dsimp [hProdSlot, B]; omega
    have hdiv : (hProdSlot D idx a b - 1) / B = idx := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hltB, Nat.add_zero]
    have hmod : (hProdSlot D idx a b - 1) % B = a * D + b := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_mod, Nat.mod_eq_of_lt hltB]
    dsimp only [C_h, gateFn]
    rw [dif_neg hne0, dif_pos hltb, hdiv, hmod, dif_pos hidx]
  have hwire_eval : ∀ (idx : ℕ) (hidx : idx < C.size) (r : ℕ) (hr : r < D),
      C_h.evalGatePoly ⟨hWireIdx d idx r, lt_trans (hwire_lt_base idx hidx r hr) (by omega)⟩ =
        MvPolynomial.homogeneousComponent r (C.evalGatePoly ⟨idx, hidx⟩) := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | h idx ih =>
      intro hidx r hr
      let wSlot : Fin N_out := ⟨hWireIdx d idx r, lt_trans (hwire_lt_base idx hidx r hr) (by omega)⟩
      have hgw_base : C_h.gate wSlot =
          expandHomogGate d idx (D ^ 2 + (r * D + d)) (C.gate ⟨idx, hidx⟩) :=
        hgate_at_sum idx hidx r d hr (by dsimp [D]; omega)
      have hsub_D2 : D ^ 2 + (r * D + d) - D ^ 2 = r * D + d := Nat.add_sub_cancel_left _ _
      have hdiv_r : (r * D + d) / D = r := by
        rw [Nat.mul_comm r D, Nat.mul_add_div hDpos, Nat.div_eq_of_lt (by dsimp [D]; omega), Nat.add_zero]
      have hmod_d : (r * D + d) % D = d := by
        rw [Nat.mul_comm r D, Nat.mul_add_mod, Nat.mod_eq_of_lt (by dsimp [D]; omega)]
      have hcond : D ^ 2 ≤ D ^ 2 + (r * D + d) ∧ (D ^ 2 + (r * D + d) - D ^ 2) % D = d :=
        ⟨Nat.le_add_right _ _, by rw [hsub_D2, hmod_d]⟩
      have hgate_wf := C.wf ⟨idx, hidx⟩
      cases hgp : C.gate ⟨idx, hidx⟩ with
      | var v =>
        rw [ratEvalGate_var C ⟨idx, hidx⟩ v hgp, homogeneousComponent_X_eq]
        rw [hgp] at hgw_base; unfold expandHomogGate at hgw_base; dsimp only at hgw_base
        simp only [← hD_def] at hgw_base
        rw [if_pos hcond, hsub_D2, hdiv_r] at hgw_base
        by_cases hr1 : r = 1
        · rw [if_pos hr1] at hgw_base ⊢
          exact ratEvalGate_var C_h wSlot v hgw_base
        · rw [if_neg hr1] at hgw_base ⊢
          simpa using ratEvalGate_const C_h wSlot 0 hgw_base
      | const a =>
        rw [ratEvalGate_const C ⟨idx, hidx⟩ a hgp, homogeneousComponent_C_eq]
        rw [hgp] at hgw_base; unfold expandHomogGate at hgw_base; dsimp only at hgw_base
        simp only [← hD_def] at hgw_base
        rw [if_pos hcond, hsub_D2, hdiv_r] at hgw_base
        by_cases hr0 : r = 0
        · rw [if_pos hr0] at hgw_base ⊢
          exact ratEvalGate_const C_h wSlot a hgw_base
        · rw [if_neg hr0] at hgw_base ⊢
          simpa using ratEvalGate_const C_h wSlot 0 hgw_base
      | add i j =>
        rw [hgp] at hgate_wf hgw_base
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [ratEvalGate_add C ⟨idx, hidx⟩ i j hgp (lt_trans hi hidx) (lt_trans hj hidx),
          map_add, ← ih i hi (lt_trans hi hidx) r hr, ← ih j hj (lt_trans hj hidx) r hr]
        unfold expandHomogGate at hgw_base; dsimp only at hgw_base
        simp only [← hD_def] at hgw_base
        rw [if_pos hcond, hsub_D2, hdiv_r] at hgw_base
        exact ratEvalGate_add C_h wSlot _ _ hgw_base
          (lt_trans (hwire_lt_base i (lt_trans hi hidx) r hr) (by omega))
          (lt_trans (hwire_lt_base j (lt_trans hj hidx) r hr) (by omega))
      | sub i j =>
        rw [hgp] at hgate_wf hgw_base
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [ratEvalGate_sub C ⟨idx, hidx⟩ i j hgp (lt_trans hi hidx) (lt_trans hj hidx),
          map_sub, ← ih i hi (lt_trans hi hidx) r hr, ← ih j hj (lt_trans hj hidx) r hr]
        unfold expandHomogGate at hgw_base; dsimp only at hgw_base
        simp only [← hD_def] at hgw_base
        rw [if_pos hcond, hsub_D2, hdiv_r] at hgw_base
        exact ratEvalGate_sub C_h wSlot _ _ hgw_base
          (lt_trans (hwire_lt_base i (lt_trans hi hidx) r hr) (by omega))
          (lt_trans (hwire_lt_base j (lt_trans hj hidx) r hr) (by omega))
      | smul a i =>
        rw [hgp] at hgate_wf hgw_base
        have hi : i < idx := hgate_wf
        rw [ratEvalGate_smul C ⟨idx, hidx⟩ a i hgp (lt_trans hi hidx),
          MvPolynomial.homogeneousComponent_C_mul, ← ih i hi (lt_trans hi hidx) r hr]
        unfold expandHomogGate at hgw_base; dsimp only at hgw_base
        simp only [← hD_def] at hgw_base
        rw [if_pos hcond, hsub_D2, hdiv_r] at hgw_base
        exact ratEvalGate_smul C_h wSlot a _ hgw_base
          (lt_trans (hwire_lt_base i (lt_trans hi hidx) r hr) (by omega))
      | mul i j =>
        rw [hgp] at hgate_wf
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [ratEvalGate_mul C ⟨idx, hidx⟩ i j hgp (lt_trans hi hidx) (lt_trans hj hidx),
          homogeneousComponent_mul_range]
        have hprod_eval : ∀ (a b : ℕ) (ha : a < D) (hb : b < D),
            C_h.evalGatePoly ⟨hProdSlot D idx a b, lt_trans (hprod_lt_base idx hidx a b ha hb) (by omega)⟩ =
              MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
              MvPolynomial.homogeneousComponent b (C.evalGatePoly ⟨j, lt_trans hj hidx⟩) := by
          intro a b ha hb
          have hgp_slot := hgate_at_prod idx hidx a b ha hb
          rw [hgp] at hgp_slot; unfold expandHomogGate at hgp_slot; dsimp only at hgp_slot
          simp only [← hD_def] at hgp_slot
          have hab_lt : a * D + b < D ^ 2 := by
            have h1 : (a + 1) * D ≤ D * D := Nat.mul_le_mul_right D ha; nlinarith
          have hda : (a * D + b) / D = a := by
            rw [Nat.mul_comm a D, Nat.mul_add_div hDpos, Nat.div_eq_of_lt hb, Nat.add_zero]
          have hdb : (a * D + b) % D = b := by
            rw [Nat.mul_comm a D, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
          rw [if_pos hab_lt, hda, hdb] at hgp_slot
          rw [← ih i hi (lt_trans hi hidx) a ha, ← ih j hj (lt_trans hj hidx) b hb]
          exact ratEvalGate_mul C_h _ _ _ hgp_slot
            (lt_trans (hwire_lt_base i (lt_trans hi hidx) a ha) (by omega))
            (lt_trans (hwire_lt_base j (lt_trans hj hidx) b hb) (by omega))
        have hsum_eval : ∀ (t : ℕ) (ht : t < D),
            C_h.evalGatePoly ⟨hSumSlot D idx r t, lt_trans (hsum_lt_base idx hidx r t hr ht) (by omega)⟩ =
              ∑ a ∈ Finset.range (t + 1),
                if a ≤ r then
                  MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
                  MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩)
                else 0 := by
          intro t
          induction t with
          | zero =>
            intro ht
            have hgs := hgate_at_sum idx hidx r 0 hr ht
            rw [hgp] at hgs; unfold expandHomogGate at hgs; dsimp only at hgs
            simp only [← hD_def] at hgs
            have hnotp : ¬ (D ^ 2 + (r * D + 0) < D ^ 2) := by omega
            have hsub : D ^ 2 + (r * D + 0) - D ^ 2 = r * D + 0 := Nat.add_sub_cancel_left _ _
            have hd0 : (r * D + 0) / D = r := by
              rw [Nat.mul_comm r D, Nat.mul_add_div hDpos, Nat.div_eq_of_lt ht, Nat.add_zero]
            have hm0 : (r * D + 0) % D = 0 := by
              rw [Nat.mul_comm r D, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
            simp only [if_neg hnotp, hsub, hd0, hm0, ite_true] at hgs
            rw [ratEvalGate_add C_h _ _ _ hgs
              (lt_trans (hprod_lt_base idx hidx 0 r ht hr) (by omega)) C_h.size_pos,
              hgate0, add_zero, hprod_eval 0 r ht hr]
            simp
          | succ t iht =>
            intro ht
            have hgs := hgate_at_sum idx hidx r (t + 1) hr ht
            rw [hgp] at hgs; unfold expandHomogGate at hgs; dsimp only at hgs
            simp only [← hD_def] at hgs
            have hnotp : ¬ (D ^ 2 + (r * D + (t + 1)) < D ^ 2) := by omega
            have hsub : D ^ 2 + (r * D + (t + 1)) - D ^ 2 = r * D + (t + 1) := Nat.add_sub_cancel_left _ _
            have hd1 : (r * D + (t + 1)) / D = r := by
              rw [Nat.mul_comm r D, Nat.mul_add_div hDpos, Nat.div_eq_of_lt ht, Nat.add_zero]
            have hm1 : (r * D + (t + 1)) % D = t + 1 := by
              rw [Nat.mul_comm r D, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
            simp only [if_neg hnotp, hsub, hd1, hm1, Nat.succ_ne_zero, ite_false] at hgs
            by_cases hle : t + 1 ≤ r
            · rw [if_pos hle] at hgs
              have hsubt : t + 1 - 1 = t := Nat.add_sub_cancel t 1
              rw [hsubt] at hgs
              rw [ratEvalGate_add C_h _ _ _ hgs
                (lt_trans (hsum_lt_base idx hidx r t hr (by omega)) (by omega))
                (lt_trans (hprod_lt_base idx hidx (t + 1) (r - (t + 1)) ht (by omega)) (by omega)),
                iht (by omega), hprod_eval (t + 1) (r - (t + 1)) ht (by omega),
                Finset.sum_range_succ _ (t + 1), if_pos hle]
            · rw [if_neg hle] at hgs
              have hsubt : t + 1 - 1 = t := Nat.add_sub_cancel t 1
              rw [hsubt] at hgs
              rw [ratEvalGate_add C_h _ _ _ hgs
                (lt_trans (hsum_lt_base idx hidx r t hr (by omega)) (by omega)) C_h.size_pos,
                iht (by omega), hgate0, Finset.sum_range_succ _ (t + 1), if_neg hle]
        have hlast := hsum_eval d (by dsimp [D]; omega)
        change C_h.evalGatePoly ⟨hSumSlot D idx r d, _⟩ = _
        rw [hlast]
        have hsum_eq :
            (∑ a ∈ Finset.range (d + 1),
              if a ≤ r then
                MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
                MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩)
              else 0) =
            ∑ a ∈ Finset.range (r + 1),
              MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
              MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩) := by
          calc
            (∑ a ∈ Finset.range (d + 1),
              if a ≤ r then
                MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
                MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩)
              else 0)
                = ∑ a ∈ Finset.range (r + 1),
                    if a ≤ r then
                      MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
                      MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩)
                    else 0 := by
                  symm
                  refine Finset.sum_subset (Finset.range_mono (by dsimp [D] at hr; omega)) ?_
                  intro a _ hnot
                  have hgt : ¬ (a ≤ r) := by rw [Finset.mem_range] at hnot; omega
                  exact if_neg hgt
            _ = ∑ a ∈ Finset.range (r + 1),
                  MvPolynomial.homogeneousComponent a (C.evalGatePoly ⟨i, lt_trans hi hidx⟩) *
                  MvPolynomial.homogeneousComponent (r - a) (C.evalGatePoly ⟨j, lt_trans hj hidx⟩) := by
                  refine Finset.sum_congr rfl fun a ha => ?_
                  exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp ha))
        exact hsum_eq
  have hfinal_eval : ∀ (t : ℕ) (ht : t < D),
      C_h.evalGatePoly ⟨base + t, by omega⟩ =
        ∑ r ∈ Finset.range (t + 1), MvPolynomial.homogeneousComponent r C.evalPoly := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hne0 : base + 0 ≠ 0 := by dsimp [base]; omega
      have hnotb : ¬ (base + 0 < base) := by omega
      have hsub0 : base + 0 - base = 0 := by omega
      have hg0 : C_h.gate ⟨base + 0, by omega⟩ = .add (hWireIdx d C.out.val 0) 0 := by
        dsimp only [C_h, gateFn]
        rw [dif_neg hne0, dif_neg hnotb, hsub0, if_pos rfl]
      rw [ratEvalGate_add C_h _ _ _ hg0
        (lt_trans (hwire_lt_base C.out.val C.out.isLt 0 ht) (by omega)) C_h.size_pos,
        hgate0, add_zero, hwire_eval C.out.val C.out.isLt 0 ht]
      simp [RatCircuit.evalPoly]
    | succ t iht =>
      intro ht
      have hne0 : base + (t + 1) ≠ 0 := by dsimp [base]; omega
      have hnotb : ¬ (base + (t + 1) < base) := by omega
      have hsub1 : base + (t + 1) - base = t + 1 := by omega
      have hg1 : C_h.gate ⟨base + (t + 1), by omega⟩ =
          .add (base + t) (hWireIdx d C.out.val (t + 1)) := by
        dsimp only [C_h, gateFn]
        rw [dif_neg hne0, dif_neg hnotb, hsub1, if_neg (Nat.succ_ne_zero t)]
        simp
      rw [ratEvalGate_add C_h _ _ _ hg1 (by omega)
        (lt_trans (hwire_lt_base C.out.val C.out.isLt (t + 1) ht) (by omega)),
        iht (by omega), hwire_eval C.out.val C.out.isLt (t + 1) ht,
        Finset.sum_range_succ _ (t + 1)]
      rfl
  refine ⟨C_h, hN_le, ?_⟩
  exact hfinal_eval d (by dsimp [D]; omega)

end ExactMatching.Proofs
