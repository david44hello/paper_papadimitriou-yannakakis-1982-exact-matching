/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.Design
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Proofs for Lemma 2.1 (Explicit polynomial-graph design)

Proves:
- `lem_2_1_irred_exists_proved`: existence of a monic irreducible polynomial of degree
  `designR m` over `ZMod 2` for every `m ≥ 2`.
- `lem_2_1_design_proved`: `designL m < 2 * m^2`, `|S_i| = m`, and `|S_i ∩ S_j| < log₂ n`
  for all `i ≠ j`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-- Lemma 2.1 (field existence): for every `m ≥ 2`, there exists a monic irreducible
polynomial of degree `r = designR m` over `ZMod 2`. -/
theorem lem_2_1_irred_exists_proved (m : ℕ) (hm : 2 ≤ m) :
    ∃ f : Polynomial (ZMod 2), f.Monic ∧ Irreducible f ∧ f.natDegree = designR m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let r := designR m
  have hr : r ≠ 0 := Nat.ne_of_gt (Nat.clog_pos (by decide) (by omega))
  let K := GaloisField 2 r
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  let α : K := (u : K)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  have hadj : IntermediateField.adjoin (ZMod 2) ({α} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · subst hx
      exact zero_mem _
    · have hux : IsUnit x := isUnit_iff_ne_zero.mpr hx
      obtain ⟨k, hk⟩ := hu hux.unit
      have hxk : (u : K) ^ k = x := by
        have h1 := congrArg (fun z : Kˣ => (z : K)) hk
        simpa [Units.val_zpow_eq_zpow_val] using h1
      rw [← hxk]
      exact zpow_mem (IntermediateField.subset_adjoin (ZMod 2) {α} (Set.mem_singleton α)) k
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  have hdeg : (minpoly (ZMod 2) α).natDegree =
      Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) ({α} : Set K)) :=
    (IntermediateField.adjoin.finrank hint).symm
  rw [hdeg, hadj, IntermediateField.finrank_top']
  exact GaloisField.finrank 2 hr

private theorem polyOfCoeffs_coeff {m t : ℕ} (c : Fin t → DesignField m) (k : ℕ) :
    (polyOfCoeffs c).coeff k = if hk : k < t then c ⟨k, hk⟩ else 0 := by
  unfold polyOfCoeffs
  rw [Polynomial.finset_sum_coeff]
  by_cases hk : k < t
  · rw [dif_pos hk, Finset.sum_eq_single ⟨k, hk⟩]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro j _ hj
      have hne : j.val ≠ k := fun h => hj (Fin.ext h)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne.symm]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [dif_neg hk, Finset.sum_eq_zero]
    intro j _
    have hne : k ≠ j.val := fun h => hk (h ▸ j.isLt)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]

private theorem polyOfCoeffs_injective {m t : ℕ} :
    Function.Injective (polyOfCoeffs (m := m) (t := t)) := by
  intro c₁ c₂ h
  ext j
  have h1 := congrArg (fun p : Polynomial (DesignField m) => p.coeff j.val) h
  simpa [polyOfCoeffs_coeff, j.isLt] using h1

private theorem polyOfCoeffs_sub_natDegree_le {m t : ℕ} (ht : 1 ≤ t)
    (c₁ c₂ : Fin t → DesignField m) :
    (polyOfCoeffs c₁ - polyOfCoeffs c₂).natDegree ≤ t - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hkt : ¬ k < t := by omega
  rw [Polynomial.coeff_sub, polyOfCoeffs_coeff, polyOfCoeffs_coeff, dif_neg hkt, dif_neg hkt,
    sub_self]

private theorem polyGraphSet_card {m t : ℕ} (hm : 2 ≤ m) (c : Fin t → DesignField m) :
    (polyGraphSet hm c).card = m := by
  unfold polyGraphSet
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro u₁ u₂ h
  have hq : 0 < designQ m := Nat.lt_of_lt_of_le (by omega)
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)
  have hval : u₁.val * designQ m + (designFieldEquiv hm ((polyOfCoeffs c).eval _)).val =
      u₂.val * designQ m + (designFieldEquiv hm ((polyOfCoeffs c).eval _)).val :=
    congrArg Fin.val h
  have hdiv := congrArg (fun x => x / designQ m) hval
  rw [Nat.mul_comm u₁.val (designQ m), Nat.mul_add_div hq,
    Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero,
    Nat.mul_comm u₂.val (designQ m), Nat.mul_add_div hq,
    Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero] at hdiv
  exact Fin.ext hdiv

private theorem polyGraphSet_inter_card_le {m t : ℕ} (hm : 2 ≤ m) (ht : 1 ≤ t)
    (c₁ c₂ : Fin t → DesignField m) (hne : c₁ ≠ c₂) :
    (polyGraphSet hm c₁ ∩ polyGraphSet hm c₂).card ≤ t - 1 := by
  classical
  have hq : 0 < designQ m := Nat.lt_of_lt_of_le (by omega)
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)
  have hle : m ≤ designQ m := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
  let p := polyOfCoeffs c₁ - polyOfCoeffs c₂
  have hp_ne : p ≠ 0 := sub_ne_zero.mpr (fun h => hne (polyOfCoeffs_injective h))
  let e := designFieldEquiv hm
  let proj : Fin (designL m) → DesignField m := fun z =>
    if hz : z.val / designQ m < m then
      e.symm ⟨z.val / designQ m, Nat.lt_of_lt_of_le hz hle⟩
    else 0
  have hmaps : Set.MapsTo proj (polyGraphSet hm c₁ ∩ polyGraphSet hm c₂ : Finset (Fin (designL m)))
      (p.roots.toFinset : Finset (DesignField m)) := by
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_inter, polyGraphSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hz
    obtain ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ := hz
    have hu1_div : z.val / designQ m = u₁.val := by
      rw [← hu₁]
      simp only
      rw [Nat.mul_comm u₁.val (designQ m), Nat.mul_add_div hq,
        Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero]
    have hu2_div : z.val / designQ m = u₂.val := by
      rw [← hu₂]
      simp only
      rw [Nat.mul_comm u₂.val (designQ m), Nat.mul_add_div hq,
        Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero]
    have hu_eq : u₁ = u₂ := Fin.ext (hu1_div.symm.trans hu2_div)
    subst hu_eq
    have hy1_mod : z.val % designQ m =
        (e ((polyOfCoeffs c₁).eval (e.symm ⟨u₁.val, Nat.lt_of_lt_of_le u₁.isLt hle⟩))).val := by
      rw [← hu₁]
      simp only
      rw [Nat.mul_comm u₁.val (designQ m), Nat.mul_add_mod, Nat.mod_eq_of_lt (Fin.isLt _)]
    have hy2_mod : z.val % designQ m =
        (e ((polyOfCoeffs c₂).eval (e.symm ⟨u₁.val, Nat.lt_of_lt_of_le u₁.isLt hle⟩))).val := by
      rw [← hu₂]
      simp only
      rw [Nat.mul_comm u₁.val (designQ m), Nat.mul_add_mod, Nat.mod_eq_of_lt (Fin.isLt _)]
    have heval : (polyOfCoeffs c₁).eval (e.symm ⟨u₁.val, Nat.lt_of_lt_of_le u₁.isLt hle⟩) =
        (polyOfCoeffs c₂).eval (e.symm ⟨u₁.val, Nat.lt_of_lt_of_le u₁.isLt hle⟩) :=
      e.injective (Fin.ext (hy1_mod.symm.trans hy2_mod))
    have hproj : proj z = e.symm ⟨u₁.val, Nat.lt_of_lt_of_le u₁.isLt hle⟩ := by
      simp only [proj, hu1_div, u₁.isLt, dite_true]
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot,
      hproj]
    simp [p, heval]
  have hinj : Set.InjOn proj (polyGraphSet hm c₁ ∩ polyGraphSet hm c₂ : Finset (Fin (designL m))) := by
    intro z₁ hz₁ z₂ hz₂ hEq
    simp only [Finset.mem_coe, Finset.mem_inter, polyGraphSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hz₁ hz₂
    obtain ⟨⟨u₁, hu₁⟩, _⟩ := hz₁
    obtain ⟨⟨u₂, hu₂⟩, _⟩ := hz₂
    have h1 : z₁.val / designQ m = u₁.val := by
      rw [← hu₁]; simp only
      rw [Nat.mul_comm u₁.val (designQ m), Nat.mul_add_div hq,
        Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero]
    have h2 : z₂.val / designQ m = u₂.val := by
      rw [← hu₂]; simp only
      rw [Nat.mul_comm u₂.val (designQ m), Nat.mul_add_div hq,
        Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero]
    simp only [proj, h1, h2, u₁.isLt, u₂.isLt, dite_true] at hEq
    have hu : u₁ = u₂ :=
      Fin.ext (congrArg (Fin.val : Fin (designQ m) → ℕ) (e.symm.injective hEq))
    subst hu
    rw [← hu₁, ← hu₂]
  calc
    (polyGraphSet hm c₁ ∩ polyGraphSet hm c₂).card
        ≤ p.roots.toFinset.card := Finset.card_le_card_of_injOn proj hmaps hinj
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ t - 1 := polyOfCoeffs_sub_natDegree_le ht c₁ c₂

/-- Lemma 2.1 (combinatorial & explicit design bounds). -/
theorem lem_2_1_design_proved (m n : ℕ) (hn : 2 ≤ n) (hm_gt : Real.logb 2 n < (m : ℝ))
    (hmn : m ≤ n) :
    have hm2 : 2 ≤ m := by
      have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
      have h2 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt h1 hm_gt
      exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h2)
    designL m < 2 * m ^ 2 ∧
    (∀ i : Fin n, (designSets m n hm2 i).card = m) ∧
    (∀ i j : Fin n, i ≠ j →
      ((designSets m n hm2 i ∩ designSets m n hm2 j).card : ℝ) < Real.logb 2 n) := by
  have hm2 : 2 ≤ m := by
    have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
      rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
    have h2 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt h1 hm_gt
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h2)
  refine ⟨?_, ?_, ?_⟩
  · -- `designL m < 2 * m ^ 2`
    have hr_pos : 1 ≤ designR m := Nat.clog_pos (by decide) (by omega)
    have hpow_lt : 2 ^ (designR m - 1) < m := by
      by_contra h
      push Not at h
      have hle : designR m ≤ designR m - 1 :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h
      omega
    have hq_lt : designQ m < 2 * m := by
      unfold designQ
      have hsplit : 2 ^ designR m = 2 * 2 ^ (designR m - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hr_pos, pow_succ, Nat.mul_comm]
      omega
    unfold designL
    calc
      m * designQ m < m * (2 * m) := Nat.mul_lt_mul_of_pos_left hq_lt (by omega)
      _ = 2 * m ^ 2 := by ring
  · -- `(designSets m n hm2 i).card = m`
    intro i
    exact polyGraphSet_card hm2 _
  · -- `|S_i ∩ S_j| < log₂ n`
    intro i j hij
    have hq2 : 2 ≤ designQ m := le_trans hm2 ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)
    have ht1 : 1 ≤ designT m n := Nat.clog_pos (by omega) (by omega)
    have hc_ne : (coeffVecEquiv hm2).symm
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt
            ((Nat.clog_le_iff_le_pow (by omega : 1 < designQ m)).mp le_rfl)⟩ ≠
        (coeffVecEquiv hm2).symm
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            ((Nat.clog_le_iff_le_pow (by omega : 1 < designQ m)).mp le_rfl)⟩ := by
      intro h
      have h1 := (coeffVecEquiv hm2).symm.injective h
      exact hij (Fin.ext (congrArg (Fin.val : Fin (designQ m ^ designT m n) → ℕ) h1))
    have hcard_le : (designSets m n hm2 i ∩ designSets m n hm2 j).card ≤ designT m n - 1 :=
      polyGraphSet_inter_card_le hm2 ht1 _ _ hc_ne
    have hpow_lt_n : designQ m ^ (designT m n - 1) < n := by
      by_contra h
      push Not at h
      have hle : designT m n ≤ designT m n - 1 :=
        (Nat.clog_le_iff_le_pow (by omega : 1 < designQ m)).mpr h
      omega
    have h2pow_lt_n : 2 ^ (designT m n - 1) < n :=
      lt_of_le_of_lt (Nat.pow_le_pow_left hq2 _) hpow_lt_n
    have hlt_log : ((designT m n - 1 : ℕ) : ℝ) < Real.logb 2 n := by
      have h2r : ((2 : ℝ) ^ (designT m n - 1 : ℕ)) < (n : ℝ) := by exact_mod_cast h2pow_lt_n
      have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h2r
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
    exact lt_of_le_of_lt (by exact_mod_cast hcard_le) hlt_log

end ExactMatching.Proofs
