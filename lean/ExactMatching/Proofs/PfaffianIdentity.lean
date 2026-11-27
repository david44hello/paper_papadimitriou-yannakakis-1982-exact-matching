/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.PfaffianMatching
public import ExactMatching.Proofs.MatchingReductions
public import ExactMatching.Proofs.PitBounds
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Proofs for Proposition 3.1 (Cyclic rank bound & Group-ring Pfaffian identity) and Remark 2

Proves:
- `prop_3_1_cyclic_rank_bound_proved`: `r ≤ max 1 (log₂ |Γ|)`.
- `prop_3_1_pfaffian_identity_proved`: Tutte-Pfaffian identity over `ℤ[Γ][x]`, coefficients in
  `{-1, 0, 1}`, degree `≤ k` (homogeneous `k`), and `P_{γ*} ≠ 0 ↔ ∃ M, w(M) = γ*`.
- `rem_2_interpolation_proved`: graph-independent integer Lagrange multipliers of magnitude
  `≤ (2N + 2)^N` recovering `N! * weightFiberPoly G w' k'`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: Cyclic rank bound -/

/-- Proposition 3.1: `r ≤ max(1, log₂ |Γ|)`. -/
theorem prop_3_1_cyclic_rank_bound_proved (r : ℕ) (q : Fin r → ℕ)
    (hq : (∀ i, 2 ≤ q i) ∨ (∃ hr : r = 1, q ⟨0, by omega⟩ = 1)) :
    (r : ℝ) ≤ max (1 : ℝ) (Real.logb 2 ((∏ i : Fin r, q i : ℕ) : ℝ)) := by
  rcases hq with hall | ⟨rfl, _⟩
  · by_cases hr0 : r = 0
    · subst hr0
      exact le_trans (by norm_num) (le_max_left _ _)
    · have hpow : 2 ^ r ≤ ∏ i : Fin r, q i := by
        calc
          2 ^ r = ∏ _i : Fin r, (2 : ℕ) := by simp
          _ ≤ ∏ i : Fin r, q i := Finset.prod_le_prod (fun i _ => hall i)
      have hpowR : ((2 : ℝ) ^ (r : ℕ)) ≤ ((∏ i : Fin r, q i : ℕ) : ℝ) := by exact_mod_cast hpow
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hpowR
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
      exact le_trans hlog (le_max_right _ _)
  · simpa using le_max_left (1 : ℝ) (Real.logb 2 ((∏ i : Fin 1, q i : ℕ) : ℝ))

/-! ### Part 2: Algebraic Pfaffian identity over `ℤ[Γ][x]` -/

private theorem orderedPairing_edge_inj {k : ℕ} (m : OrderedPairing k) :
    Function.Injective (fun i : Fin k =>
      s(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩)) := by
  intro i j hEq
  have hi : m.perm ⟨2 * i.val, by omega⟩ < m.perm ⟨2 * i.val + 1, by omega⟩ := m.pair_lt i
  have hj : m.perm ⟨2 * j.val, by omega⟩ < m.perm ⟨2 * j.val + 1, by omega⟩ := m.pair_lt j
  rw [Sym2.eq_iff] at hEq
  rcases hEq with ⟨ha, _⟩ | ⟨ha, hb⟩
  · have hidx := m.perm.injective ha
    have hval : 2 * i.val = 2 * j.val := congrArg Fin.val hidx
    exact Fin.ext (by omega)
  · exfalso
    rw [ha, hb] at hi
    exact lt_asymm hi hj

private theorem orderedPairing_edgeFinset_inj {k : ℕ} :
    Function.Injective (OrderedPairing.edgeFinset (k := k)) := by
  intro m₁ m₂ hEq
  have hmem_iff : ∀ (m : OrderedPairing k) (u v : Fin (2 * k)), u < v →
      (s(u, v) ∈ m.edgeFinset ↔ ∃ i : Fin k, m.perm ⟨2 * i.val, by omega⟩ = u ∧
        m.perm ⟨2 * i.val + 1, by omega⟩ = v) := by
    intro m u v huv
    simp only [OrderedPairing.edgeFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      rw [Sym2.eq_iff] at hi
      rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨i, ha, hb⟩
      · exfalso
        have hlt := m.pair_lt i
        rw [ha, hb] at hlt
        exact lt_asymm hlt huv
    · rintro ⟨i, ha, hb⟩
      exact ⟨i, by rw [ha, hb]⟩
  let f₁ : Fin k → Fin (2 * k) := fun i => m₁.perm ⟨2 * i.val, by omega⟩
  let f₂ : Fin k → Fin (2 * k) := fun i => m₂.perm ⟨2 * i.val, by omega⟩
  have hf₁_mono : StrictMono f₁ := fun i j hij => m₁.fst_mono i j hij
  have hf₂_mono : StrictMono f₂ := fun i j hij => m₂.fst_mono i j hij
  have himg_eq : Finset.univ.image f₁ = Finset.univ.image f₂ := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      have hmem : s(m₁.perm ⟨2 * i.val, by omega⟩, m₁.perm ⟨2 * i.val + 1, by omega⟩) ∈
          m₂.edgeFinset := by
        rw [← hEq]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      obtain ⟨j, hj1, _⟩ := (hmem_iff m₂ _ _ (m₁.pair_lt i)).mp hmem
      exact ⟨j, hj1⟩
    · rintro ⟨j, rfl⟩
      have hmem : s(m₂.perm ⟨2 * j.val, by omega⟩, m₂.perm ⟨2 * j.val + 1, by omega⟩) ∈
          m₁.edgeFinset := by
        rw [hEq]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
      obtain ⟨i, hi1, _⟩ := (hmem_iff m₁ _ _ (m₂.pair_lt j)).mp hmem
      exact ⟨i, hi1⟩
  have hf_eq : ∀ i : Fin k, f₁ i = f₂ i := by
    have h := strictMono_eq_of_image_eq hf₁_mono hf₂_mono himg_eq
    intro i
    exact congrFun h i
  have hperm_eq : m₁.perm = m₂.perm := by
    ext x
    by_cases heven : x.val % 2 = 0
    · let i : Fin k := ⟨x.val / 2, by omega⟩
      have hx : x = ⟨2 * i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      rw [hx]
      exact congrArg Fin.val (hf_eq i)
    · let i : Fin k := ⟨x.val / 2, by omega⟩
      have hx : x = ⟨2 * i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      rw [hx]
      have hmem : s(m₁.perm ⟨2 * i.val, by omega⟩, m₁.perm ⟨2 * i.val + 1, by omega⟩) ∈
          m₂.edgeFinset := by
        rw [← hEq]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      obtain ⟨j, hj1, hj2⟩ := (hmem_iff m₂ _ _ (m₁.pair_lt i)).mp hmem
      have hij : i = j := by
        have h1 : f₂ j = f₂ i := hj1.trans (hf_eq i)
        exact (hf₂_mono.injective h1).symm
      subst hij
      exact congrArg Fin.val hj2.symm
  cases m₁; cases m₂; cases hperm_eq; rfl

private theorem orderedPairing_isPerfectMatching {k : ℕ}
    (G : SimpleGraph (Fin (2 * k))) (m : OrderedPairing k)
    (hsub : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)) :
    IsPerfectMatching G m.edgeFinset := by
  constructor
  · intro e he
    rw [OrderedPairing.edgeFinset, Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    exact hsub i
  · intro v
    let x := m.perm.symm v
    let i : Fin k := ⟨x.val / 2, by omega⟩
    let e₀ := s(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩)
    have hset : m.edgeFinset.filter (fun e => v ∈ e) = {e₀} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_singleton, OrderedPairing.edgeFinset,
        Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, rfl⟩, hv⟩
        rw [Sym2.mem_iff] at hv
        rcases hv with h1 | h2
        · have hx1 : x = ⟨2 * j.val, by omega⟩ := m.perm.injective (by simp [x, h1])
          have hij : j = i := Fin.ext (by
            have : x.val = 2 * j.val := congrArg Fin.val hx1
            dsimp [i]; omega)
          rw [hij]
        · have hx2 : x = ⟨2 * j.val + 1, by omega⟩ := m.perm.injective (by simp [x, h2])
          have hij : j = i := Fin.ext (by
            have : x.val = 2 * j.val + 1 := congrArg Fin.val hx2
            dsimp [i]; omega)
          rw [hij]
      · rintro rfl
        refine ⟨⟨i, rfl⟩, ?_⟩
        rw [Sym2.mem_iff]
        by_cases hev : x.val % 2 = 0
        · left
          have hx : (⟨2 * i.val, by omega⟩ : Fin (2 * k)) = x := Fin.ext (by dsimp [i]; omega)
          rw [hx]; simp [x]
        · right
          have hx : (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k)) = x := Fin.ext (by dsimp [i]; omega)
          rw [hx]; simp [x]
    rw [hset, Finset.card_singleton]

/-- Every perfect matching `M` of `G` on `Fin (2k)` arises from a unique `OrderedPairing k`. -/
private theorem exists_orderedPairing_of_isPerfectMatching {k : ℕ}
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (M : Finset (Sym2 (Fin (2 * k)))) (hM : IsPerfectMatching G M) :
    ∃ m : OrderedPairing k,
      (∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)) ∧
      m.edgeFinset = M := by
  have hMcard : M.card = k := by
    have h2 := perfectMatching_two_mul_card hM
    omega
  let edgesOrd : Finset (Fin (2 * k) × Fin (2 * k)) :=
    Finset.univ.filter fun p => p.1 < p.2 ∧ s(p.1, p.2) ∈ M
  have hcard_ord_M : edgesOrd.card = M.card := by
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp; exact (Finset.mem_filter.mp hp).2.2
    · intro p₁ hp₁ p₂ hp₂ hEq
      have h1 := (Finset.mem_filter.mp hp₁).2.1
      have h2 := (Finset.mem_filter.mp hp₂).2.1
      rw [Sym2.eq_iff] at hEq
      rcases hEq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Prod.ext ha hb
      · exfalso; rw [ha, hb] at h1; exact lt_asymm h1 h2
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : G.Adj u v := hM.1 s(u, v) he
        have hne : u ≠ v := G.ne_of_adj hadj
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, he⟩, rfl⟩
        · exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, by rwa [Sym2.eq_swap]⟩, Sym2.eq_swap⟩
  have hcard_ord : edgesOrd.card = k := hcard_ord_M.trans hMcard
  have hdisj : ∀ p₁ ∈ edgesOrd, ∀ p₂ ∈ edgesOrd, p₁ ≠ p₂ →
      p₁.1 ≠ p₂.1 ∧ p₁.1 ≠ p₂.2 ∧ p₁.2 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2 := by
    intro p₁ hp₁ p₂ hp₂ hne
    have hm1 := (Finset.mem_filter.mp hp₁).2
    have hm2 := (Finset.mem_filter.mp hp₂).2
    have hsym_ne : s(p₁.1, p₁.2) ≠ s(p₂.1, p₂.2) := by
      intro hEq
      rw [Sym2.eq_iff] at hEq
      rcases hEq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hne (Prod.ext ha hb)
      · rw [ha, hb] at hm1; exact lt_asymm hm1.1 hm2.1
    have hno_share : ∀ v : Fin (2 * k), ¬ (v ∈ s(p₁.1, p₁.2) ∧ v ∈ s(p₂.1, p₂.2)) := by
      intro v ⟨hv1, hv2⟩
      have h1 : s(p₁.1, p₁.2) ∈ M.filter (fun e => v ∈ e) := Finset.mem_filter.mpr ⟨hm1.2, hv1⟩
      have h2 : s(p₂.1, p₂.2) ∈ M.filter (fun e => v ∈ e) := Finset.mem_filter.mpr ⟨hm2.2, hv2⟩
      have hcard1 := hM.2 v
      exact hsym_ne (Finset.card_le_one_iff.mp hcard1.le h1 h2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; exact hno_share p₁.1 ⟨by simp, by simp [h]⟩
    · intro h; exact hno_share p₁.1 ⟨by simp, by simp [h]⟩
    · intro h; exact hno_share p₁.2 ⟨by simp, by simp [h]⟩
    · intro h; exact hno_share p₁.2 ⟨by simp, by simp [h]⟩
  let pairs : Fin k ↪o Fin (2 * k) ×ₗ Fin (2 * k) :=
    (edgesOrd.map ⟨toLex, toLex.injective⟩).orderEmbOfFin (by simp [hcard_ord])
  let pairFn : Fin k → Fin (2 * k) × Fin (2 * k) := fun i => ofLex (pairs i)
  have hpair_mem : ∀ i : Fin k, pairFn i ∈ edgesOrd := by
    intro i
    have hmem := Finset.orderEmbOfFin_mem (edgesOrd.map ⟨toLex, toLex.injective⟩)
      (by simp [hcard_ord]) i
    rw [Finset.mem_map] at hmem
    obtain ⟨p, hp, hpeq⟩ := hmem
    have : pairFn i = p := by
      dsimp only [pairFn, pairs]
      rw [← hpeq]
      rfl
    rwa [this]
  have hpair_inj : Function.Injective pairFn := fun i j h =>
    pairs.injective (ofLex.injective h)
  have hfst_mono : ∀ i j : Fin k, i < j → (pairFn i).1 < (pairFn j).1 := by
    intro i j hij
    have hlex : pairs i < pairs j := pairs.strictMono hij
    rw [Prod.Lex.lt_iff] at hlex
    rcases hlex with h1 | ⟨heq1, _⟩
    · exact h1
    · exfalso
      exact (hdisj _ (hpair_mem i) _ (hpair_mem j) (fun h => ne_of_lt hij (hpair_inj h))).1 heq1
  let f : Fin (2 * k) → Fin (2 * k) := fun x =>
    if x.val % 2 = 0 then (pairFn ⟨x.val / 2, by omega⟩).1
    else (pairFn ⟨x.val / 2, by omega⟩).2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    let ix : Fin k := ⟨x.val / 2, by omega⟩
    let iy : Fin k := ⟨y.val / 2, by omega⟩
    by_cases hixy : ix = iy
    · have hdiv : x.val / 2 = y.val / 2 := congrArg Fin.val hixy
      by_cases hx : x.val % 2 = 0 <;> by_cases hy : y.val % 2 = 0
      · exact Fin.ext (by omega)
      · exfalso
        simp only [f, hx, hy, ite_true, ite_false] at hxy
        have hlt := (Finset.mem_filter.mp (hpair_mem ix)).2.1
        have hEq_idx : (⟨y.val / 2, by omega⟩ : Fin k) = ix := hixy.symm
        change (pairFn ix).1 = (pairFn ⟨y.val / 2, by omega⟩).2 at hxy
        rw [hEq_idx] at hxy
        exact ne_of_lt hlt hxy
      · exfalso
        simp only [f, hx, hy, ite_true, ite_false] at hxy
        have hlt := (Finset.mem_filter.mp (hpair_mem ix)).2.1
        have hEq_idx : (⟨y.val / 2, by omega⟩ : Fin k) = ix := hixy.symm
        change (pairFn ix).2 = (pairFn ⟨y.val / 2, by omega⟩).1 at hxy
        rw [hEq_idx] at hxy
        exact ne_of_lt hlt hxy.symm
      · exact Fin.ext (by omega)
    · exfalso
      have hne_pair : pairFn ix ≠ pairFn iy := fun h => hixy (hpair_inj h)
      have hd := hdisj _ (hpair_mem ix) _ (hpair_mem iy) hne_pair
      by_cases hx : x.val % 2 = 0 <;> by_cases hy : y.val % 2 = 0 <;>
        simp only [f, hx, hy, ite_true, ite_false] at hxy
      · exact hd.1 hxy
      · exact hd.2.1 hxy
      · exact hd.2.2.1 hxy
      · exact hd.2.2.2 hxy
  let perm : Equiv.Perm (Fin (2 * k)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hperm_even : ∀ i : Fin k, perm ⟨2 * i.val, by omega⟩ = (pairFn i).1 := by
    intro i
    change f ⟨2 * i.val, by omega⟩ = (pairFn i).1
    have hmod : (2 * i.val) % 2 = 0 := by omega
    have hdiv : (2 * i.val) / 2 = i.val := by omega
    simp [f, hmod, hdiv]
  have hperm_odd : ∀ i : Fin k, perm ⟨2 * i.val + 1, by omega⟩ = (pairFn i).2 := by
    intro i
    change f ⟨2 * i.val + 1, by omega⟩ = (pairFn i).2
    have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
    simp [f, hmod, hdiv]
  let m : OrderedPairing k :=
    { perm := perm
      pair_lt := fun i => by
        rw [hperm_even i, hperm_odd i]
        exact (Finset.mem_filter.mp (hpair_mem i)).2.1
      fst_mono := fun i j hij => by
        rw [hperm_even i, hperm_even j]
        exact hfst_mono i j hij }
  refine ⟨m, ?_, ?_⟩
  · intro i
    change G.Adj (perm ⟨2 * i.val, by omega⟩) (perm ⟨2 * i.val + 1, by omega⟩)
    rw [hperm_even i, hperm_odd i]
    exact hM.1 _ (Finset.mem_filter.mp (hpair_mem i)).2.2
  · apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [OrderedPairing.edgeFinset, Finset.mem_image] at he
      obtain ⟨i, _, rfl⟩ := he
      change s(perm ⟨2 * i.val, by omega⟩, perm ⟨2 * i.val + 1, by omega⟩) ∈ M
      rw [hperm_even i, hperm_odd i]
      exact (Finset.mem_filter.mp (hpair_mem i)).2.2
    · rw [hMcard, OrderedPairing.edgeFinset, Finset.card_image_of_injective _ (orderedPairing_edge_inj m)]
      simp

theorem extractGroupCoeff_coeff {E Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (γ : Γ) (F : MvPolynomial E (AddMonoidAlgebra ℤ Γ)) (d : E →₀ ℕ) :
    (extractGroupCoeff γ F).coeff d = (AddMonoidAlgebra.coeffAddEquiv (F.coeff d)) γ := by
  classical
  unfold extractGroupCoeff
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ F.support
  · rw [Finset.sum_eq_single d]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro d' _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro h; exact (h hd).elim
  · have hzero : F.coeff d = 0 := by simpa [MvPolynomial.mem_support_iff] using hd
    rw [hzero, map_zero, Finsupp.zero_apply]
    apply Finset.sum_eq_zero
    intro d' hd'
    have hne : d' ≠ d := fun h => hd (h ▸ hd')
    rw [MvPolynomial.coeff_monomial, if_neg hne]

theorem extractGroupCoeff_add {E Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (γ : Γ) (F₁ F₂ : MvPolynomial E (AddMonoidAlgebra ℤ Γ)) :
    extractGroupCoeff γ (F₁ + F₂) = extractGroupCoeff γ F₁ + extractGroupCoeff γ F₂ := by
  ext d
  simp [extractGroupCoeff_coeff]

theorem extractGroupCoeff_sub {E Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (γ : Γ) (F₁ F₂ : MvPolynomial E (AddMonoidAlgebra ℤ Γ)) :
    extractGroupCoeff γ (F₁ - F₂) = extractGroupCoeff γ F₁ - extractGroupCoeff γ F₂ := by
  ext d
  simp [extractGroupCoeff_coeff]

theorem coeffAddEquiv_single {Γ : Type*} [DecidableEq Γ] (g γ : Γ) (r : ℤ) :
    (AddMonoidAlgebra.coeffAddEquiv (AddMonoidAlgebra.single g r)) γ =
      if g = γ then r else 0 := by
  change (Finsupp.single g r) γ = if g = γ then r else 0
  exact Finsupp.single_apply

theorem extractGroupCoeff_mul {E Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (γ : Γ) (F₁ F₂ : MvPolynomial E (AddMonoidAlgebra ℤ Γ)) :
    extractGroupCoeff γ (F₁ * F₂) =
      ∑ α : Γ, extractGroupCoeff α F₁ * extractGroupCoeff (γ - α) F₂ := by
  classical
  ext d
  rw [extractGroupCoeff_coeff, MvPolynomial.coeff_mul, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_mul, extractGroupCoeff_coeff]
  rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hconv : ∀ (a b : AddMonoidAlgebra ℤ Γ),
      (AddMonoidAlgebra.coeffAddEquiv (a * b)) γ =
      ∑ α : Γ, (AddMonoidAlgebra.coeffAddEquiv a) α * (AddMonoidAlgebra.coeffAddEquiv b) (γ - α) := by
    intro a b
    induction a using AddMonoidAlgebra.induction_on with
    | of g =>
      induction b using AddMonoidAlgebra.induction_on with
      | of h =>
        change (AddMonoidAlgebra.coeffAddEquiv
            (AddMonoidAlgebra.single g (1 : ℤ) * AddMonoidAlgebra.single h (1 : ℤ))) γ =
          ∑ α : Γ,
            (AddMonoidAlgebra.coeffAddEquiv (AddMonoidAlgebra.single g (1 : ℤ))) α *
            (AddMonoidAlgebra.coeffAddEquiv (AddMonoidAlgebra.single h (1 : ℤ))) (γ - α)
        rw [AddMonoidAlgebra.single_mul_single, one_mul, coeffAddEquiv_single]
        simp_rw [coeffAddEquiv_single]
        rw [Finset.sum_eq_single g]
        · by_cases hgh : g + h = γ
          · have hh : h = γ - g := by rw [← hgh]; abel
            simp [hgh, hh]
          · have hh : h ≠ γ - g := fun h1 => hgh (by rw [h1]; abel)
            simp [hgh, hh]
        · intro α _ hα
          simp [Ne.symm hα]
        · intro h; exact (h (Finset.mem_univ g)).elim
      | add b₁ b₂ ih₁ ih₂ =>
        rw [mul_add, map_add, Finsupp.add_apply, ih₁, ih₂, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp [mul_add]
      | smul r b ih =>
        rw [mul_smul_comm, map_zsmul, Finsupp.smul_apply, ih, zsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
        ring
    | add a₁ a₂ ih₁ ih₂ =>
      rw [add_mul, map_add, Finsupp.add_apply, ih₁, ih₂, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp [add_mul]
    | smul r a ih =>
      rw [smul_mul_assoc, map_zsmul, Finsupp.smul_apply, ih, zsmul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
      ring
  exact hconv _ _

/-- Degree monomial `∏_{i : Fin k} X_{e_i}` for an `OrderedPairing k` contained in `G`. -/
private noncomputable def pairingMonomial {k : ℕ} (G : SimpleGraph (Fin (2 * k)))
    (m : OrderedPairing k)
    (hsub : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)) :
    UpperEdge G →₀ ℕ :=
  ∑ i : Fin k,
    Finsupp.single
      ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩, hsub i⟩ 1

private theorem pairingMonomial_sum {k : ℕ} (G : SimpleGraph (Fin (2 * k)))
    (m : OrderedPairing k)
    (hsub : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)) :
    (pairingMonomial G m hsub).sum (fun _ e => e) = k := by
  unfold pairingMonomial
  have hgen : ∀ (S : Finset (Fin k)) (f : Fin k → UpperEdge G),
      (∑ i ∈ S, Finsupp.single (f i) (1 : ℕ)).sum (fun _ e => e) = S.card := by
    intro S f
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, ih, Finset.card_insert_of_notMem ha, Nat.add_comm]
  simpa using hgen Finset.univ _

private theorem pairingMonomial_eq_iff {k : ℕ} (G : SimpleGraph (Fin (2 * k)))
    (m₁ m₂ : OrderedPairing k)
    (h₁ : ∀ i : Fin k, G.Adj (m₁.perm ⟨2 * i.val, by omega⟩) (m₁.perm ⟨2 * i.val + 1, by omega⟩))
    (h₂ : ∀ i : Fin k, G.Adj (m₂.perm ⟨2 * i.val, by omega⟩) (m₂.perm ⟨2 * i.val + 1, by omega⟩)) :
    pairingMonomial G m₁ h₁ = pairingMonomial G m₂ h₂ ↔ m₁ = m₂ := by
  constructor
  · intro hEq
    apply orderedPairing_edgeFinset_inj
    ext e
    simp only [OrderedPairing.edgeFinset, Finset.mem_image, Finset.mem_univ, true_and]
    have hsupp : ∀ (m : OrderedPairing k)
        (h : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩))
        (ed : UpperEdge G),
        0 < pairingMonomial G m h ed ↔
          ∃ i : Fin k,
            m.perm ⟨2 * i.val, by omega⟩ = ed.val.val.1 ∧
            m.perm ⟨2 * i.val + 1, by omega⟩ = ed.val.val.2 := by
      intro m h ed
      unfold pairingMonomial
      rw [Finsupp.finset_sum_apply]
      constructor
      · intro hpos
        obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
        rw [Finsupp.single_apply] at hi
        split_ifs at hi with heq
        · exact ⟨i, congrArg (fun x : UpperEdge G => x.val.val.1) heq,
            congrArg (fun x : UpperEdge G => x.val.val.2) heq⟩
        · exact (hi rfl).elim
      · rintro ⟨i, h1, h2⟩
        have heq : (⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
            m.pair_lt i⟩, h i⟩ : UpperEdge G) = ed :=
          Subtype.ext (Subtype.ext (Prod.ext h1 h2))
        have hle : (Finsupp.single
            (⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
              m.pair_lt i⟩, h i⟩ : UpperEdge G) 1) ed ≤
            ∑ j : Fin k, (Finsupp.single
              (⟨⟨(m.perm ⟨2 * j.val, by omega⟩, m.perm ⟨2 * j.val + 1, by omega⟩),
                m.pair_lt j⟩, h j⟩ : UpperEdge G) 1) ed :=
          Finset.single_le_sum (f := fun j : Fin k => (Finsupp.single
            (⟨⟨(m.perm ⟨2 * j.val, by omega⟩, m.perm ⟨2 * j.val + 1, by omega⟩),
              m.pair_lt j⟩, h j⟩ : UpperEdge G) 1) ed) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [heq] at hle
        have h1 : (Finsupp.single ed 1) ed = 1 := Finsupp.single_eq_same
        omega
    constructor
    · rintro ⟨i, rfl⟩
      let ed : UpperEdge G :=
        ⟨⟨(m₁.perm ⟨2 * i.val, by omega⟩, m₁.perm ⟨2 * i.val + 1, by omega⟩), m₁.pair_lt i⟩, h₁ i⟩
      have hpos1 : 0 < pairingMonomial G m₁ h₁ ed := (hsupp m₁ h₁ ed).mpr ⟨i, rfl, rfl⟩
      have hpos2 : 0 < pairingMonomial G m₂ h₂ ed := hEq ▸ hpos1
      obtain ⟨j, hj1, hj2⟩ := (hsupp m₂ h₂ ed).mp hpos2
      exact ⟨j, by rw [hj1, hj2]⟩
    · rintro ⟨j, rfl⟩
      let ed : UpperEdge G :=
        ⟨⟨(m₂.perm ⟨2 * j.val, by omega⟩, m₂.perm ⟨2 * j.val + 1, by omega⟩), m₂.pair_lt j⟩, h₂ j⟩
      have hpos2 : 0 < pairingMonomial G m₂ h₂ ed := (hsupp m₂ h₂ ed).mpr ⟨j, rfl, rfl⟩
      have hpos1 : 0 < pairingMonomial G m₁ h₁ ed := hEq.symm ▸ hpos2
      obtain ⟨i, hi1, hi2⟩ := (hsupp m₁ h₁ ed).mp hpos1
      exact ⟨i, by rw [hi1, hi2]⟩
  · rintro rfl; rfl

/-- Exact expansion of `pfaffian (tutteMatrix G w)` as a sum of distinct monomials. -/
private theorem pfaffian_tutteMatrix_eq {k : ℕ} {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) :
    pfaffian (tutteMatrix G w) =
      ∑ m : OrderedPairing k,
        if hsub : ∀ i : Fin k,
            G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
        then
          MvPolynomial.monomial (pairingMonomial G m hsub)
            (AddMonoidAlgebra.single
              (∑ i : Fin k,
                w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                  m.pair_lt i⟩, hsub i⟩)
              m.sign)
        else 0 := by
  unfold pfaffian
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hsub : ∀ i : Fin k,
      G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
  · rw [dif_pos hsub]
    have hterm : ∀ i : Fin k,
        tutteMatrix G w (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩) =
        MvPolynomial.monomial
          (Finsupp.single
            ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
              hsub i⟩ 1)
          (AddMonoidAlgebra.single
            (w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
              hsub i⟩) 1) := by
      intro i
      unfold tutteMatrix
      rw [dif_pos (m.pair_lt i), dif_pos (hsub i), MvPolynomial.C_mul_X_eq_monomial]
    simp_rw [hterm]
    have hprod_mon : ∀ (S : Finset (Fin k))
        (f : Fin k → UpperEdge G) (g : Fin k → Γ),
        (∏ i ∈ S, MvPolynomial.monomial (Finsupp.single (f i) 1) (AddMonoidAlgebra.single (g i) (1 : ℤ))) =
        MvPolynomial.monomial (∑ i ∈ S, Finsupp.single (f i) 1)
          (AddMonoidAlgebra.single (∑ i ∈ S, g i) (1 : ℤ)) := by
      intro S f g
      induction S using Finset.induction_on with
      | empty =>
        simp [MvPolynomial.monomial_zero']
        rfl
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, ih, MvPolynomial.monomial_mul,
          AddMonoidAlgebra.single_mul_single, one_mul, Finset.sum_insert ha, Finset.sum_insert ha]
    rw [hprod_mon Finset.univ]
    have hcast_sign : (m.sign : MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) =
        MvPolynomial.C (AddMonoidAlgebra.single (0 : Γ) m.sign) := by
      have h1 : (m.sign : AddMonoidAlgebra ℤ Γ) = AddMonoidAlgebra.single (0 : Γ) m.sign := by
        rw [← map_intCast (AddMonoidAlgebra.singleZeroRingHom : ℤ →+* AddMonoidAlgebra ℤ Γ)]
        rfl
      rw [← h1, map_intCast]
    rw [hcast_sign, MvPolynomial.C_mul_monomial, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rfl
  · rw [dif_neg hsub]
    push Not at hsub
    obtain ⟨i₀, hi₀⟩ := hsub
    have hzero : tutteMatrix G w (m.perm ⟨2 * i₀.val, by omega⟩) (m.perm ⟨2 * i₀.val + 1, by omega⟩) = 0 := by
      unfold tutteMatrix
      rw [dif_pos (m.pair_lt i₀), dif_neg hi₀]
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, mul_zero]

/-- Proposition 3.1 (algebraic Pfaffian identity over `ℤ[Γ][x]`). -/
theorem prop_3_1_pfaffian_identity_proved {k : ℕ} (hk : 1 ≤ k)
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (γstar : Γ) :
    let P := groupRingPoly G w γstar
    (∀ d, P.coeff d = -1 ∨ P.coeff d = 0 ∨ P.coeff d = 1) ∧
    P.totalDegree ≤ k ∧
    (∀ d ∈ P.support, d.sum (fun _ e => e) = k) ∧
    (P ≠ 0 ↔ ∃ M : Finset (Sym2 (Fin (2 * k))),
      IsPerfectMatching G M ∧ matchingLabelSum G w M = γstar) := by
  dsimp only
  set P := groupRingPoly G w γstar
  have hP_coeff : ∀ d : UpperEdge G →₀ ℕ,
      P.coeff d =
        ∑ m : OrderedPairing k,
          if hsub : ∀ i : Fin k,
              G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
          then
            if pairingMonomial G m hsub = d ∧
                (∑ i : Fin k,
                  w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                    m.pair_lt i⟩, hsub i⟩) = γstar
            then m.sign
            else 0
          else 0 := by
    intro d
    dsimp only [P, groupRingPoly]
    rw [extractGroupCoeff_coeff, pfaffian_tutteMatrix_eq, MvPolynomial.coeff_sum, map_sum,
      Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hsub : ∀ i : Fin k,
        G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
    · rw [dif_pos hsub, dif_pos hsub, MvPolynomial.coeff_monomial]
      by_cases hd : pairingMonomial G m hsub = d
      · rw [if_pos hd, coeffAddEquiv_single]
        simp only [hd, true_and]
      · rw [if_neg hd]
        simp [hd]
    · rw [dif_neg hsub, dif_neg hsub]
      simp
  have hP_val : ∀ d : UpperEdge G →₀ ℕ,
      (∃ m : OrderedPairing k, ∃ hsub : ∀ i : Fin k,
          G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩),
          pairingMonomial G m hsub = d ∧
          (∑ i : Fin k,
            w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
              m.pair_lt i⟩, hsub i⟩) = γstar ∧
          P.coeff d = m.sign) ∨
      P.coeff d = 0 := by
    intro d
    by_cases hex : ∃ m : OrderedPairing k, ∃ hsub : ∀ i : Fin k,
        G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩),
        pairingMonomial G m hsub = d ∧
        (∑ i : Fin k,
          w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
            m.pair_lt i⟩, hsub i⟩) = γstar
    · left
      obtain ⟨m₀, hsub₀, hd₀, hw₀⟩ := hex
      refine ⟨m₀, hsub₀, hd₀, hw₀, ?_⟩
      rw [hP_coeff d, Finset.sum_eq_single m₀]
      · simp [hsub₀, hd₀, hw₀]
      · intro m' _ hne
        by_cases hsub' : ∀ i : Fin k,
            G.Adj (m'.perm ⟨2 * i.val, by omega⟩) (m'.perm ⟨2 * i.val + 1, by omega⟩)
        · simp only [hsub', dite_true]
          have hnot : ¬ (pairingMonomial G m' hsub' = d ∧
              (∑ i : Fin k,
                w ⟨⟨(m'.perm ⟨2 * i.val, by omega⟩, m'.perm ⟨2 * i.val + 1, by omega⟩),
                  m'.pair_lt i⟩, hsub' i⟩) = γstar) := by
            intro ⟨hd', _⟩
            exact hne ((pairingMonomial_eq_iff G m' m₀ hsub' hsub₀).mp (hd'.trans hd₀.symm))
          simp [hnot]
        · simp [hsub']
      · intro h; exact (h (Finset.mem_univ m₀)).elim
    · right
      rw [hP_coeff d]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hsub : ∀ i : Fin k,
          G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
      · simp only [hsub, dite_true]
        have hnot : ¬ (pairingMonomial G m hsub = d ∧
            (∑ i : Fin k,
              w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                m.pair_lt i⟩, hsub i⟩) = γstar) := fun ⟨hd, hw⟩ => hex ⟨m, hsub, hd, hw⟩
        simp [hnot]
      · simp [hsub]
  have hsign_pm : ∀ m : OrderedPairing k, m.sign = -1 ∨ m.sign = 1 := by
    intro m
    unfold OrderedPairing.sign
    rcases Int.units_eq_one_or (Equiv.Perm.sign m.perm) with h1 | h2
    · right; rw [h1]; rfl
    · left; rw [h2]; rfl
  have hsign_ne0 : ∀ m : OrderedPairing k, m.sign ≠ 0 := by
    intro m; rcases hsign_pm m with h | h <;> omega
  have hlabel_eq : ∀ (m : OrderedPairing k)
      (hsub : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)),
      matchingLabelSum G w m.edgeFinset =
        ∑ i : Fin k,
          w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
            hsub i⟩ := by
    intro m hsub
    unfold matchingLabelSum
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun (i : Fin k) _ =>
      (⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
        hsub i⟩ : UpperEdge G)) ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · intro i _ j _ hEq
      have h1 : m.perm ⟨2 * i.val, by omega⟩ = m.perm ⟨2 * j.val, by omega⟩ :=
        congrArg (fun x : UpperEdge G => x.val.val.1) hEq
      have hidx : (⟨2 * i.val, by omega⟩ : Fin (2 * k)) = ⟨2 * j.val, by omega⟩ :=
        m.perm.injective h1
      have hval : 2 * i.val = 2 * j.val := congrArg Fin.val hidx
      exact Fin.ext (by omega)
    · intro e he
      have hmem := (Finset.mem_filter.mp he).2
      rw [OrderedPairing.edgeFinset, Finset.mem_image] at hmem
      obtain ⟨i, _, hi⟩ := hmem
      rw [Sym2.eq_iff] at hi
      rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨i, Finset.mem_univ i, Subtype.ext (Subtype.ext (Prod.ext ha hb))⟩
      · exfalso
        have h1 := m.pair_lt i
        have h2 := e.val.property
        rw [ha, hb] at h1
        exact lt_asymm h1 h2
    · intro _ _; rfl
  have hdeg_supp : ∀ d ∈ P.support, d.sum (fun _ e => e) = k := by
    intro d hd
    have hne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    rcases hP_val d with ⟨m, hsub, rfl, _, _⟩ | h0
    · exact pairingMonomial_sum G m hsub
    · exact (hne h0).elim
  refine ⟨?_, ?_, hdeg_supp, ?_⟩
  · intro d
    rcases hP_val d with ⟨m, _, _, _, hc⟩ | h0
    · rw [hc]
      rcases hsign_pm m with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h0)
  · rw [MvPolynomial.totalDegree]
    exact Finset.sup_le fun d hd => (hdeg_supp d hd).le
  · constructor
    · intro hne
      have hsupp_ne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hne
      obtain ⟨d, hd⟩ := hsupp_ne
      have hc_ne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      rcases hP_val d with ⟨m, hsub, _, hw, _⟩ | h0
      · exact ⟨m.edgeFinset, orderedPairing_isPerfectMatching G m hsub, by rw [hlabel_eq m hsub]; exact hw⟩
      · exact (hc_ne h0).elim
    · rintro ⟨M, hM, hsum⟩
      obtain ⟨m, hsub, rfl⟩ := exists_orderedPairing_of_isPerfectMatching G M hM
      have hw : (∑ i : Fin k,
          w ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
            hsub i⟩) = γstar := by
        rw [← hlabel_eq m hsub]; exact hsum
      intro h0
      have hc : P.coeff (pairingMonomial G m hsub) = m.sign := by
        rw [hP_coeff, Finset.sum_eq_single m]
        · simp [hsub, hw]
        · intro m' _ hne
          by_cases hsub' : ∀ i : Fin k,
              G.Adj (m'.perm ⟨2 * i.val, by omega⟩) (m'.perm ⟨2 * i.val + 1, by omega⟩)
          · simp only [hsub', dite_true]
            have hnot : ¬ (pairingMonomial G m' hsub' = pairingMonomial G m hsub ∧
                (∑ i : Fin k,
                  w ⟨⟨(m'.perm ⟨2 * i.val, by omega⟩, m'.perm ⟨2 * i.val + 1, by omega⟩),
                    m'.pair_lt i⟩, hsub' i⟩) = γstar) := by
              intro ⟨hd', _⟩
              exact hne ((pairingMonomial_eq_iff G m' m hsub' hsub).mp hd')
            simp [hnot]
          · simp [hsub']
        · intro h; exact (h (Finset.mem_univ m)).elim
      have hc0 : P.coeff (pairingMonomial G m hsub) = 0 := by simp [h0]
      exact hsign_ne0 m (hc.symm.trans hc0)

/-! ### Part 3: Remark 2 (Alternative Lagrange interpolation identity) -/

/-- Coefficient magnitude bound for `∏ i ∈ S, (X - C (i : ℤ))` when every `i ∈ S` is `≤ N`. -/
private theorem prod_X_sub_C_coeff_natAbs_le (N : ℕ) :
    ∀ (S : Finset ℕ), (∀ i ∈ S, i ≤ N) →
      ∀ d : ℕ, ((∏ i ∈ S, (Polynomial.X - Polynomial.C (i : ℤ))).coeff d).natAbs ≤
        (N + 1) ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ d
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
    split_ifs <;> decide
  | @insert a s ha ih =>
    intro hle d
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
    have ha_le : a ≤ N := hle a (Finset.mem_insert_self a s)
    have hs_le : ∀ i ∈ s, i ≤ N := fun i hi => hle i (Finset.mem_insert_of_mem hi)
    set Q : Polynomial ℤ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (i : ℤ))
    have hcoeff : ((Polynomial.X - Polynomial.C (a : ℤ)) * Q).coeff d =
        (if d = 0 then 0 else Q.coeff (d - 1)) - (a : ℤ) * Q.coeff d := by
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      cases d with
      | zero => simp
      | succ d => simp [Polynomial.coeff_X_mul]
    rw [hcoeff]
    have h1 : (if d = 0 then (0 : ℤ) else Q.coeff (d - 1)).natAbs ≤ (N + 1) ^ s.card := by
      split_ifs
      · simp
      · exact ih hs_le (d - 1)
    have h2 : ((a : ℤ) * Q.coeff d).natAbs ≤ N * (N + 1) ^ s.card := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul ha_le (ih hs_le d)
    calc
      ((if d = 0 then (0 : ℤ) else Q.coeff (d - 1)) - (a : ℤ) * Q.coeff d).natAbs
          ≤ (if d = 0 then (0 : ℤ) else Q.coeff (d - 1)).natAbs + ((a : ℤ) * Q.coeff d).natAbs :=
            Int.natAbs_sub_le _ _
      _ ≤ (N + 1) ^ s.card + N * (N + 1) ^ s.card := Nat.add_le_add h1 h2
      _ = (N + 1) ^ s.card * (N + 1) := by ring

/-- Exact evaluation of `∏ i ≠ j, (j - i) = (-1)^(N - j) * j! * (N - j)!`. -/
private theorem prod_sub_erase_eq (N : ℕ) (j : Fin (N + 1)) :
    (∏ i ∈ Finset.univ.erase j, ((j.val : ℤ) - (i.val : ℤ))) =
      (-1 : ℤ) ^ (N - j.val) * (j.val.factorial : ℤ) * ((N - j.val).factorial : ℤ) := by
  have hj_le : j.val ≤ N := Nat.le_of_lt_succ j.isLt
  let S_lt := (Finset.univ.erase j).filter (fun i : Fin (N + 1) => i.val < j.val)
  let S_gt := (Finset.univ.erase j).filter (fun i : Fin (N + 1) => j.val < i.val)
  have hsplit : Finset.univ.erase j = S_lt ∪ S_gt := by
    ext i
    simp only [S_lt, S_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true]
    constructor
    · intro hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact Or.inl ⟨hne, h⟩
      · exact Or.inr ⟨hne, h⟩
    · rintro (⟨hne, _⟩ | ⟨hne, _⟩) <;> exact hne
  have hdisj : Disjoint S_lt S_gt := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hlt_prod : ∏ i ∈ S_lt, ((j.val : ℤ) - (i.val : ℤ)) = (j.val.factorial : ℤ) := by
    have hbij : ∏ i ∈ S_lt, ((j.val : ℤ) - (i.val : ℤ)) =
        ∏ r ∈ Finset.range j.val, ((r + 1 : ℕ) : ℤ) := by
      refine Finset.prod_bij (fun i _ => j.val - i.val - 1) ?_ ?_ ?_ ?_
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr (by omega)
      · intro i₁ hi₁ i₂ hi₂ hEq
        have h1 := (Finset.mem_filter.mp hi₁).2
        have h2 := (Finset.mem_filter.mp hi₂).2
        exact Fin.ext (by omega)
      · intro r hr
        have hr' := Finset.mem_range.mp hr
        refine ⟨⟨j.val - 1 - r, by omega⟩, ?_, ?_⟩
        · simp only [S_lt, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          refine ⟨fun h => ?_, by omega⟩
          have hv : j.val - 1 - r = j.val := congrArg Fin.val h
          omega
        · simp only
          omega
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        omega
    rw [hbij, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hgt_prod : ∏ i ∈ S_gt, ((j.val : ℤ) - (i.val : ℤ)) =
      (-1 : ℤ) ^ (N - j.val) * ((N - j.val).factorial : ℤ) := by
    have hbij : ∏ i ∈ S_gt, ((j.val : ℤ) - (i.val : ℤ)) =
        ∏ r ∈ Finset.range (N - j.val), (-((r + 1 : ℕ) : ℤ)) := by
      refine Finset.prod_bij (fun i _ => i.val - j.val - 1) ?_ ?_ ?_ ?_
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        have := i.isLt
        exact Finset.mem_range.mpr (by omega)
      · intro i₁ hi₁ i₂ hi₂ hEq
        have h1 := (Finset.mem_filter.mp hi₁).2
        have h2 := (Finset.mem_filter.mp hi₂).2
        exact Fin.ext (by omega)
      · intro r hr
        have hr' := Finset.mem_range.mp hr
        refine ⟨⟨j.val + 1 + r, by omega⟩, ?_, ?_⟩
        · simp only [S_gt, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          refine ⟨fun h => ?_, by omega⟩
          have hv : j.val + 1 + r = j.val := congrArg Fin.val h
          omega
        · simp only
          omega
      · intro i hi
        have := (Finset.mem_filter.mp hi).2
        omega
    rw [hbij]
    have hpull : (∏ r ∈ Finset.range (N - j.val), (-((r + 1 : ℕ) : ℤ))) =
        (-1 : ℤ) ^ (N - j.val) * ∏ r ∈ Finset.range (N - j.val), ((r + 1 : ℕ) : ℤ) := by
      calc
        ∏ r ∈ Finset.range (N - j.val), (-((r + 1 : ℕ) : ℤ))
            = ∏ r ∈ Finset.range (N - j.val), ((-1 : ℤ) * ((r + 1 : ℕ) : ℤ)) := by
              refine Finset.prod_congr rfl fun _ _ => by ring
        _ = (∏ _r ∈ Finset.range (N - j.val), (-1 : ℤ)) *
              ∏ r ∈ Finset.range (N - j.val), ((r + 1 : ℕ) : ℤ) := Finset.prod_mul_distrib
        _ = (-1 : ℤ) ^ (N - j.val) * ∏ r ∈ Finset.range (N - j.val), ((r + 1 : ℕ) : ℤ) := by simp
    rw [hpull, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  rw [hlt_prod, hgt_prod]
  ring

/-- Remark 2: graph-independent integer Lagrange multipliers of magnitude `≤ (2N + 2)^N`
recovering `N! * weightFiberPoly G w' k'`. -/
theorem rem_2_interpolation_proved {k : ℕ} (hk : 1 ≤ k) (W : ℕ)
    (k' : ℕ) (hk' : k' ≤ 2 * k * W) :
    ∃ coeff : Fin (2 * k * W + 1) → ℤ,
      (∀ j, (coeff j).natAbs ≤ (2 * (2 * k * W) + 2) ^ (2 * k * W)) ∧
      ∀ (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w' : UpperEdge G → ℕ), (∀ e, w' e ≤ 2 * W) →
        ∑ j : Fin (2 * k * W + 1),
          MvPolynomial.C (coeff j) * pfaffian (interpMatrix G w' (j.val : ℤ)) =
        MvPolynomial.C (((2 * k * W).factorial : ℤ)) * weightFiberPoly G w' k' := by
  set N := 2 * k * W
  let Lnum : Fin (N + 1) → Polynomial ℤ := fun j =>
    ∏ i ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (i.val : ℤ))
  let scale : Fin (N + 1) → ℤ := fun j =>
    (-1 : ℤ) ^ (N - j.val) * (Nat.choose N j.val : ℤ)
  let coeff : Fin (N + 1) → ℤ := fun j => scale j * (Lnum j).coeff k'
  have hpoly_id : ∀ d : ℕ, d ≤ N →
      (∑ j : Fin (N + 1), Polynomial.C (scale j * (j.val : ℤ) ^ d) * Lnum j) =
        Polynomial.C (N.factorial : ℤ) * Polynomial.X ^ d := by
    intro d hd
    let P_lhs : Polynomial ℤ := ∑ j : Fin (N + 1), Polynomial.C (scale j * (j.val : ℤ) ^ d) * Lnum j
    let P_rhs : Polynomial ℤ := Polynomial.C (N.factorial : ℤ) * Polynomial.X ^ d
    have heval : ∀ r : Fin (N + 1), P_lhs.eval (r.val : ℤ) = P_rhs.eval (r.val : ℤ) := by
      intro r
      dsimp only [P_lhs, P_rhs]
      rw [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [Finset.sum_eq_single r]
      · rw [Polynomial.eval_mul, Polynomial.eval_C]
        have hLval : (Lnum r).eval (r.val : ℤ) =
            (-1 : ℤ) ^ (N - r.val) * (r.val.factorial : ℤ) * ((N - r.val).factorial : ℤ) := by
          dsimp only [Lnum]
          rw [Polynomial.eval_prod]
          simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          exact prod_sub_erase_eq N r
        rw [hLval]
        dsimp only [scale]
        have hchoose : (Nat.choose N r.val : ℤ) * (r.val.factorial : ℤ) * ((N - r.val).factorial : ℤ) =
            (N.factorial : ℤ) := by
          have hnat : Nat.choose N r.val * r.val.factorial * (N - r.val).factorial = N.factorial := by
            have := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ r.isLt)
            linarith
          exact_mod_cast hnat
        have hneg : (-1 : ℤ) ^ (N - r.val) * (-1 : ℤ) ^ (N - r.val) = 1 := by
          rw [← mul_pow]; simp
        calc
          (-1 : ℤ) ^ (N - r.val) * ↑(N.choose ↑r) * (↑r : ℤ) ^ d *
              ((-1 : ℤ) ^ (N - ↑r) * ↑(↑r : ℕ).factorial * ↑(N - ↑r).factorial)
              = ((-1 : ℤ) ^ (N - ↑r) * (-1 : ℤ) ^ (N - ↑r)) *
                (↑(N.choose ↑r) * ↑(↑r : ℕ).factorial * ↑(N - ↑r).factorial) * (↑r : ℤ) ^ d := by ring
          _ = 1 * (N.factorial : ℤ) * (r.val : ℤ) ^ d := by rw [hneg, hchoose]
          _ = (N.factorial : ℤ) * (r.val : ℤ) ^ d := by rw [one_mul]
      · intro j _ hjr
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        have hzero : (Lnum j).eval (r.val : ℤ) = 0 := by
          dsimp only [Lnum]
          rw [Polynomial.eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjr.symm, Finset.mem_univ r⟩) ?_
          simp
        rw [hzero, mul_zero]
      · intro h; exact (h (Finset.mem_univ r)).elim
    have hdeg_lhs : P_lhs.natDegree ≤ N := by
      refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le fun j _ => ?_)
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      let degF : Fin (N + 1) → ℕ := fun i => (Polynomial.X - Polynomial.C (i.val : ℤ)).natDegree
      have hprod_le : (Lnum j).natDegree ≤ ∑ i ∈ Finset.univ.erase j, degF i :=
        Polynomial.natDegree_prod_le (Finset.univ.erase j)
          (fun i : Fin (N + 1) => Polynomial.X - Polynomial.C (i.val : ℤ))
      have hlin : ∀ i ∈ Finset.univ.erase j, degF i ≤ 1 := by
        intro i _
        exact le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
      have hsum_le : ∑ i ∈ Finset.univ.erase j, degF i ≤ ∑ _i ∈ Finset.univ.erase j, (1 : ℕ) :=
        Finset.sum_le_sum (f := degF) (g := fun _ => 1) hlin
      calc
        (Lnum j).natDegree ≤ ∑ i ∈ Finset.univ.erase j, degF i := hprod_le
        _ ≤ ∑ _i ∈ Finset.univ.erase j, (1 : ℕ) := hsum_le
        _ = (Finset.univ.erase j).card := by simp
        _ = N := by simp
    have hdeg_rhs : P_rhs.natDegree ≤ N := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      simpa using hd
    by_contra hne
    have hdiff_ne : P_lhs - P_rhs ≠ 0 := sub_ne_zero.mpr hne
    have hdiff_deg : (P_lhs - P_rhs).natDegree ≤ N :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le hdeg_lhs hdeg_rhs)
    let Rset : Finset ℤ := Finset.univ.image (fun r : Fin (N + 1) => (r.val : ℤ))
    have hRsub : Rset ⊆ (P_lhs - P_rhs).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨r, _, rfl⟩ := hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hdiff_ne, Polynomial.IsRoot,
        Polynomial.eval_sub, heval r, sub_self]
    have hRcard : Rset.card = N + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by exact_mod_cast h))]
      simp
    have hcard_le : N + 1 ≤ N := by
      calc
        N + 1 = Rset.card := hRcard.symm
        _ ≤ (P_lhs - P_rhs).roots.toFinset.card := Finset.card_le_card hRsub
        _ ≤ (P_lhs - P_rhs).roots.card := Multiset.toFinset_card_le _
        _ ≤ (P_lhs - P_rhs).natDegree := Polynomial.card_roots' _
        _ ≤ N := hdiff_deg
    omega
  have hortho : ∀ d : ℕ, d ≤ N →
      (∑ j : Fin (N + 1), coeff j * (j.val : ℤ) ^ d) = if d = k' then (N.factorial : ℤ) else 0 := by
    intro d hd
    have h1 := congrArg (fun P : Polynomial ℤ => P.coeff k') (hpoly_id d hd)
    rw [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h1
    have hlhs : (∑ j : Fin (N + 1), (Polynomial.C (scale j * (j.val : ℤ) ^ d) * Lnum j).coeff k') =
        ∑ j : Fin (N + 1), coeff j * (j.val : ℤ) ^ d := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coeff_C_mul]
      dsimp only [coeff]
      ring
    rw [hlhs] at h1
    rw [h1]
    by_cases hdk : d = k'
    · subst hdk; simp
    · have hk'd : k' ≠ d := fun h => hdk h.symm
      simp [hdk, hk'd]
  refine ⟨coeff, ?_, ?_⟩
  · intro j
    dsimp only [coeff, scale]
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
    simp only [Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast]
    have hch : Nat.choose N j.val ≤ 2 ^ N := by
      calc Nat.choose N j.val ≤ ∑ r ∈ Finset.range (N + 1), Nat.choose N r :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr j.isLt)
      _ = 2 ^ N := Nat.sum_range_choose N
    have hL : ((Lnum j).coeff k').natAbs ≤ (N + 1) ^ N := by
      let S : Finset ℕ := (Finset.univ.erase j).image Fin.val
      have hScard : S.card = N := by
        rw [Finset.card_image_of_injective _ Fin.val_injective]
        simp
      have hLeq : Lnum j = ∏ i ∈ S, (Polynomial.X - Polynomial.C (i : ℤ)) := by
        dsimp only [Lnum, S]
        rw [Finset.prod_image (fun a _ b _ h => Fin.val_injective h)]
      rw [hLeq]
      have hbound := prod_X_sub_C_coeff_natAbs_le N S (fun i hi => by
        rw [Finset.mem_image] at hi
        obtain ⟨x, _, rfl⟩ := hi
        exact Nat.le_of_lt_succ x.isLt) k'
      rwa [hScard] at hbound
    calc
      Nat.choose N j.val * ((Lnum j).coeff k').natAbs
          ≤ 2 ^ N * (N + 1) ^ N := Nat.mul_le_mul hch hL
      _ = (2 * (N + 1)) ^ N := (Nat.mul_pow 2 (N + 1) N).symm
      _ = (2 * N + 2) ^ N := by ring
  · intro G _ w' hw'
    have hpf_expand : ∀ j : Fin (N + 1),
        pfaffian (interpMatrix G w' (j.val : ℤ)) =
          ∑ m : OrderedPairing k,
            if hsub : ∀ i : Fin k,
                G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
            then
              let wt : ℕ :=
                ∑ i : Fin k,
                  w' ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                    m.pair_lt i⟩, hsub i⟩
              MvPolynomial.C ((j.val : ℤ) ^ wt) *
                (MvPolynomial.C m.sign *
                  ∏ i : Fin k,
                    MvPolynomial.X
                      ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                        m.pair_lt i⟩, hsub i⟩)
            else 0 := by
      intro j
      unfold pfaffian
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hsub : ∀ i : Fin k,
          G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
      · rw [dif_pos hsub]
        have hterm : ∀ i : Fin k,
            interpMatrix G w' (j.val : ℤ)
              (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩) =
            MvPolynomial.C ((j.val : ℤ) ^
              w' ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                m.pair_lt i⟩, hsub i⟩) *
              MvPolynomial.X
                ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                  m.pair_lt i⟩, hsub i⟩ := by
          intro i; unfold interpMatrix; rw [dif_pos (m.pair_lt i), dif_pos (hsub i)]
        simp_rw [hterm, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
        have hsignC : (m.sign : MvPolynomial (UpperEdge G) ℤ) = MvPolynomial.C m.sign := by simp
        rw [hsignC]
        ring
      · rw [dif_neg hsub]
        push Not at hsub
        obtain ⟨i₀, hi₀⟩ := hsub
        have hzero : interpMatrix G w' (j.val : ℤ)
            (m.perm ⟨2 * i₀.val, by omega⟩) (m.perm ⟨2 * i₀.val + 1, by omega⟩) = 0 := by
          unfold interpMatrix; rw [dif_pos (m.pair_lt i₀), dif_neg hi₀]
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, mul_zero]
    simp_rw [hpf_expand, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold weightFiberPoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hsub : ∀ i : Fin k,
        G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
    · rw [dif_pos hsub]
      simp_rw [dif_pos hsub]
      set wt : ℕ :=
        ∑ i : Fin k,
          w' ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
            m.pair_lt i⟩, hsub i⟩
      have hwt_le : wt ≤ N := by
        calc
          wt ≤ ∑ _i : Fin k, 2 * W := Finset.sum_le_sum fun i _ => hw' _
          _ = k * (2 * W) := by simp
          _ = N := by dsimp [N]; ring
      set monP : MvPolynomial (UpperEdge G) ℤ :=
        MvPolynomial.C m.sign *
          ∏ i : Fin k,
            MvPolynomial.X
              ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
                m.pair_lt i⟩, hsub i⟩
      have hfactor :
          (∑ j : Fin (N + 1), MvPolynomial.C (coeff j) * (MvPolynomial.C ((j.val : ℤ) ^ wt) * monP)) =
          MvPolynomial.C (∑ j : Fin (N + 1), coeff j * (j.val : ℤ) ^ wt) * monP := by
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, ← map_mul]
      rw [hfactor, hortho wt hwt_le]
      split_ifs <;> simp
    · simp [hsub]

end ExactMatching.Proofs
