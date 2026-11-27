/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.CitedHypotheses
public import ExactMatching.Defs.PitAlgorithm
public import ExactMatching.Proofs.CircuitsTransfer
public import ExactMatching.Proofs.PitBounds
public import ExactMatching.Proofs.Reconstruction

@[expose] public section

/-!
# Proofs of Theorem 1 (core PIT correctness) and Corollary 1 (`[A26]` instantiation)

Proves:
- `paperPerm_properties` and `nwPermModTest_implies_computes_paperPerm` (shared engine for
  both Theorem 1 and Remark 1)
- `thm_1_test_correct_proved`
- `cor_1_a26_implies_H_proved`
- `cor_1_implication_proved`
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: Combinatorial properties of `paperPerm ℤ μ` and Ryser/NW bridge -/

private noncomputable def permMonomial {μ : ℕ} (σ : Equiv.Perm (Fin μ)) : (Fin μ × Fin μ) →₀ ℕ :=
  ∑ i : Fin μ, Finsupp.single (i, σ i) 1

private theorem permMonomial_apply {μ : ℕ} (σ : Equiv.Perm (Fin μ)) (p : Fin μ × Fin μ) :
    permMonomial σ p = if σ p.1 = p.2 then 1 else 0 := by
  dsimp only [permMonomial]
  rw [Finsupp.finsetSum_apply]
  by_cases h : σ p.1 = p.2
  · rw [if_pos h, Finset.sum_eq_single p.1]
    · have hp : (p.1, σ p.1) = p := Prod.ext rfl h
      rw [Finsupp.single_apply, if_pos hp]
    · intro i _ hne
      rw [Finsupp.single_apply, if_neg (fun heq => hne (congrArg Prod.fst heq))]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg h, Finset.sum_eq_zero]
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro heq
    have h1 : i = p.1 := congrArg Prod.fst heq
    have h2 : σ i = p.2 := congrArg Prod.snd heq
    exact h (h1 ▸ h2)

private theorem permMonomial_inj {μ : ℕ} : Function.Injective (@permMonomial μ) := by
  intro σ₁ σ₂ heq
  refine Equiv.ext fun i => ?_
  have h := congrFun (congrArg DFunLike.coe heq) (i, σ₁ i)
  rw [permMonomial_apply, if_pos rfl, permMonomial_apply] at h
  by_contra hne
  have hne' : σ₂ i ≠ σ₁ i := fun h1 => hne h1.symm
  rw [if_neg hne'] at h
  omega

private theorem paperPerm_term_eq (μ : ℕ) (σ : Equiv.Perm (Fin μ)) :
    (∏ i : Fin μ, (MvPolynomial.X (i, σ i) : MvPolynomial (Fin μ × Fin μ) ℤ)) =
      MvPolynomial.monomial (permMonomial σ) 1 := by
  have haux : ∀ (S : Finset (Fin μ)),
      (∏ i ∈ S, (MvPolynomial.X (i, σ i) : MvPolynomial (Fin μ × Fin μ) ℤ)) =
        MvPolynomial.monomial (∑ i ∈ S, Finsupp.single (i, σ i) 1) 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.X, MvPolynomial.monomial_mul,
        one_mul]
  exact haux Finset.univ

private theorem paperPerm_coeff (μ : ℕ) (d : (Fin μ × Fin μ) →₀ ℕ) :
    (paperPerm ℤ μ).coeff d = if ∃ σ : Equiv.Perm (Fin μ), permMonomial σ = d then 1 else 0 := by
  classical
  unfold paperPerm
  rw [MvPolynomial.coeff_sum]
  have hterm : ∀ σ : Equiv.Perm (Fin μ),
      (∏ i : Fin μ, (MvPolynomial.X (i, σ i) : MvPolynomial (Fin μ × Fin μ) ℤ)).coeff d =
        if permMonomial σ = d then 1 else 0 := by
    intro σ
    rw [paperPerm_term_eq, MvPolynomial.coeff_monomial]
  simp_rw [hterm]
  split_ifs with hex
  · rcases hex with ⟨σ₀, hσ₀⟩
    rw [Finset.sum_eq_single σ₀]
    · rw [if_pos hσ₀]
    · intro σ _ hne
      rw [if_neg (fun heq => hne (permMonomial_inj (heq.trans hσ₀.symm)))]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg (fun heq => hex ⟨σ, heq⟩)]

theorem paperPerm_ne_zero (μ : ℕ) : paperPerm ℤ μ ≠ 0 := by
  intro h0
  have h : (paperPerm ℤ μ).coeff (permMonomial (1 : Equiv.Perm (Fin μ))) = 0 := by
    rw [h0]; simp
  rw [paperPerm_coeff, if_pos ⟨1, rfl⟩] at h
  norm_num at h

theorem paperPerm_isMultilinear (μ : ℕ) : IsMultilinear (paperPerm ℤ μ) := by
  intro d hd p
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [paperPerm_coeff] at hne
  have hex : ∃ σ : Equiv.Perm (Fin μ), permMonomial σ = d := by
    by_contra hnot; rw [if_neg hnot] at hne; exact hne rfl
  rcases hex with ⟨σ, rfl⟩
  rw [permMonomial_apply]
  split_ifs <;> omega

theorem paperPerm_totalDegree_le (μ : ℕ) : (paperPerm ℤ μ).totalDegree ≤ μ := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro d hd
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [paperPerm_coeff] at hne
  have hex : ∃ σ : Equiv.Perm (Fin μ), permMonomial σ = d := by
    by_contra hnot; rw [if_neg hnot] at hne; exact hne rfl
  rcases hex with ⟨σ, rfl⟩
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  have hsum : ∑ p : Fin μ × Fin μ, permMonomial σ p = μ := by
    simp_rw [permMonomial_apply]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ i : Fin μ, ∑ j : Fin μ, (if σ i = j then (1 : ℕ) else 0) = 1 := by
      intro i
      rw [Finset.sum_eq_single (σ i)]
      · simp
      · intro j _ hne; exact if_neg (Ne.symm hne)
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    simp [hrow]
  exact le_of_eq hsum

theorem paperPerm_coeff_bitBound (μ b : ℕ) : CoeffBitBound (paperPerm ℤ μ) b := by
  intro d
  rw [paperPerm_coeff]
  split_ifs
  · exact Nat.one_le_pow _ _ (by decide)
  · exact Nat.zero_le _

theorem eval_rename_paperPerm_eq_ryser {μ : ℕ} (v : Fin (μ ^ 2) → ℤ) :
    MvPolynomial.eval (fun j => (v j : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ)
        (MvPolynomial.rename (finPairEquivSq μ) (paperPerm ℤ μ))) =
      ((ryserPerm (R := ℤ) (matrixOfVec v) : ℤ) : ℚ) := by
  rw [step_thm1_ryser_proved, paperPerm_eq_perm_proved ℤ μ]
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_rename]
  unfold perm Matrix.permanent
  rw [MvPolynomial.eval₂_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MvPolynomial.eval₂_prod, Int.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval₂_X]
  rfl

/-- Shared NW-permanent contradiction engine: if a nonzero `C : IntCircuit s` passes
`nwPermModTest μ B s hm hcard C` (with `B = 3s + s*μ*clog 2 (s*μ²) + 2`, `log₂ s < μ² < s`),
then `paperPerm ℚ μ` is computable in `Computes` with at most `s ^ κ` gates. -/
theorem nwPermModTest_implies_computes_paperPerm (hKI : KI04_Cor_7_4) :
    ∃ κ : ℕ, 1 ≤ κ ∧
      ∀ (μ s : ℕ) (hs : 2 ≤ s) (hμ1 : 1 ≤ μ) (hm_gt : Real.logb 2 s < ((μ ^ 2 : ℕ) : ℝ))
        (hm_lt : μ ^ 2 < s) (hm : 2 ≤ μ ^ 2)
        (hcard : ∀ i : Fin s, (designSets (μ ^ 2) s hm i).card = μ ^ 2)
        (C : IntCircuit s) (hC_len : C.encodingLength ≤ s)
        (hdeg : C.evalPoly.totalDegree ≤ s) (hcoeff : CoeffBitBound C.evalPoly s),
        let B := 3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) + 2
        nwPermModTest μ B s hm hcard C →
        C.evalPoly ≠ 0 →
        Computes (paperPerm ℚ μ) (s ^ κ) := by
  obtain ⟨κ, hκ, hRec⟩ := lem_2_2_reconstruction_proved hKI
  refine ⟨κ, hκ, ?_⟩
  intro μ s hs hμ1 hm_gt hm_lt hm hcard C hC_len hdeg hcoeff B htest hnz
  let p : MvPolynomial (Fin (μ ^ 2)) ℤ := MvPolynomial.rename (finPairEquivSq μ) (paperPerm ℤ μ)
  have hp_nz : p ≠ 0 := by
    intro h0
    exact paperPerm_ne_zero μ ((MvPolynomial.rename_injective _ (finPairEquivSq μ).injective)
      (by simpa [p] using h0))
  have hp_ml : IsMultilinear p := by
    intro d hd j
    have hne := MvPolynomial.mem_support_iff.mp hd
    dsimp only [p] at hne
    have hco : (MvPolynomial.rename (finPairEquivSq μ) (paperPerm ℤ μ)).coeff d =
        (paperPerm ℤ μ).coeff (Finsupp.mapDomain (finPairEquivSq μ).symm d) := by
      have heq : d = Finsupp.mapDomain (finPairEquivSq μ) (Finsupp.mapDomain (finPairEquivSq μ).symm d) := by
        rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
      conv_lhs => rw [heq]
      exact MvPolynomial.coeff_rename_mapDomain _ (finPairEquivSq μ).injective _ _
    rw [hco] at hne
    have hmem : Finsupp.mapDomain (finPairEquivSq μ).symm d ∈ (paperPerm ℤ μ).support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hml := paperPerm_isMultilinear μ _ hmem ((finPairEquivSq μ).symm j)
    simpa [Finsupp.mapDomain_equiv_apply] using hml
  have hp_deg : p.totalDegree ≤ μ :=
    le_trans (MvPolynomial.totalDegree_rename_le _ _) (paperPerm_totalDegree_le μ)
  have hp_bit : CoeffBitBound p s := by
    intro d
    dsimp only [p]
    have heq : d = Finsupp.mapDomain (finPairEquivSq μ) (Finsupp.mapDomain (finPairEquivSq μ).symm d) := by
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
    conv_lhs => rw [heq]
    rw [MvPolynomial.coeff_rename_mapDomain _ (finPairEquivSq μ).injective]
    exact paperPerm_coeff_bitBound μ s _
  have hμ_le_s : μ ≤ s := by
    have h1 : μ ≤ μ ^ 2 := by simpa [sq] using Nat.le_mul_self μ
    omega
  let S_grid : Finset ℚ := (Finset.range (s * μ + 1)).image (fun k : ℕ => (k : ℚ))
  have hS_card : s * μ < S_grid.card := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    omega
  have hvanish : ∀ a : Fin (designL (μ ^ 2)) → ℚ, (∀ j, a j ∈ S_grid) →
      MvPolynomial.eval
        (nwMap (designSets (μ ^ 2) s hm) hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a)
        (MvPolynomial.map (Int.castRingHom ℚ) C.evalPoly) = 0 := by
    intro a haS
    have ha_nat : ∀ j : Fin (designL (μ ^ 2)), ∃ k : Fin (s * μ + 1), (k.val : ℚ) = a j := by
      intro j
      rcases Finset.mem_image.mp (haS j) with ⟨k, hk, hka⟩
      exact ⟨⟨k, Finset.mem_range.mp hk⟩, hka⟩
    let aFin : Fin (designL (μ ^ 2)) → Fin (s * μ + 1) := fun j => (ha_nat j).choose
    have haFin_eq : ∀ j, ((aFin j).val : ℚ) = a j := fun j => (ha_nat j).choose_spec
    have hmod := nwPermModTest_modulus_exact μ s hs hμ1 hm hcard C hdeg hcoeff aFin
    have hzero_int : MvPolynomial.eval
        (fun i => ryserPerm (R := ℤ) (matrixOfVec fun j : Fin (μ ^ 2) =>
          ((aFin ((designSets (μ ^ 2) s hm i).orderEmbOfFin (hcard i) j)).val : ℤ)))
        C.evalPoly = 0 :=
      hmod.2.2.mp (htest aFin)
    have hvec : nwMap (designSets (μ ^ 2) s hm) hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a =
        fun i => ((ryserPerm (R := ℤ) (matrixOfVec fun j : Fin (μ ^ 2) =>
          ((aFin ((designSets (μ ^ 2) s hm i).orderEmbOfFin (hcard i) j)).val : ℤ)) : ℤ) : ℚ) := by
      ext i
      dsimp only [nwMap]
      have harg : (fun j : Fin (μ ^ 2) => a ((designSets (μ ^ 2) s hm i).orderEmbOfFin (hcard i) j)) =
          fun j => (((aFin ((designSets (μ ^ 2) s hm i).orderEmbOfFin (hcard i) j)).val : ℤ) : ℚ) := by
        ext j
        rw [Int.cast_natCast, haFin_eq]
      rw [harg]
      exact eval_rename_paperPerm_eq_ryser _
    rw [hvec, MvPolynomial.eval_map]
    have heq := aeval_intCast_eq_intCast_eval (R := ℚ) C.evalPoly
      (fun i => ryserPerm (R := ℤ) (matrixOfVec fun j : Fin (μ ^ 2) =>
        ((aFin ((designSets (μ ^ 2) s hm i).orderEmbOfFin (hcard i) j)).val : ℤ)))
    rw [MvPolynomial.aeval_def] at heq
    change MvPolynomial.eval₂ (algebraMap ℤ ℚ) _ C.evalPoly = 0
    rw [heq, hzero_int, Int.cast_zero]
  have hcomp_p : Computes (MvPolynomial.map (Int.castRingHom ℚ) p) (s ^ κ) :=
    hRec s (μ ^ 2) s s μ s hs hs hm_gt (le_of_lt hm_lt)
      ⟨le_of_lt hm_lt, le_rfl, le_rfl, hμ_le_s, le_rfl⟩
      C hC_len hnz hdeg hcoeff p hp_nz hp_ml hp_deg hp_bit S_grid hS_card hcard hvanish
  have hcomp_unren := computes_rename (finPairEquivSq μ).symm hcomp_p
  have heq_perm : MvPolynomial.rename (finPairEquivSq μ).symm (MvPolynomial.map (Int.castRingHom ℚ) p) =
      paperPerm ℚ μ := by
    dsimp only [p]
    rw [← MvPolynomial.map_rename, MvPolynomial.rename_rename, Equiv.symm_comp_self,
      MvPolynomial.rename_id, AlgHom.id_apply]
    unfold paperPerm
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPolynomial.map_X]
  rwa [heq_perm] at hcomp_unren

/-! ### Part 2: Theorem 1 (`thm_1_test_correct_proved`) -/

/-- Theorem 1 core: PIT test correctness and evaluation-point bound under `HypothesisH c μ₀`
and `KI04_Cor_7_4`. -/
theorem thm_1_test_correct_proved (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ : ℕ) (K : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 0 < K ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s),
        C.encodingLength ≤ s →
        C.evalPoly.totalDegree ≤ s →
        CoeffBitBound C.evalPoly s →
        (s < s₀ → (pitSmallTest s C ↔ C.evalPoly = 0)) ∧
        (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
           (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
           pitLargeTest A μ₀ s hm hcard C ↔ C.evalPoly = 0)) ∧
      (∀ s ≥ 2,
        (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
          expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ)))) := by
  rcases hH with ⟨hc, hμ₀, hLB⟩
  obtain ⟨κ, hκ, hEngine⟩ := nwPermModTest_implies_computes_paperPerm hKI
  let A : ℕ := Nat.ceil ((κ : ℝ) / c)
  have hA : 1 ≤ A := by
    have hpos : (0 : ℝ) < (κ : ℝ) / c := div_pos (by exact_mod_cast hκ) hc
    exact Nat.ceil_pos.mpr hpos
  obtain ⟨s₀, hs₀, hthr⟩ := step_thm1_threshold_proved A μ₀ hA hμ₀
  obtain ⟨K, hK, hExp⟩ := step_thm1_exponent_bound_proved A μ₀ s₀ 4 hA hμ₀ hs₀
  have hthr4 : ∀ s ≥ s₀,
      Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
      pitM A μ₀ s < s ∧
      2 ≤ pitM A μ₀ s ∧
      s * pitMu A μ₀ s + 1 ≤ s ^ 2 := by
    intro s hs
    rcases hthr s hs with ⟨h1, h2, h3⟩
    have hm2 : 2 ≤ pitM A μ₀ s := by
      have hlog1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one (by omega)
      have hgt1 : (1 : ℝ) < (pitM A μ₀ s : ℝ) := lt_of_le_of_lt hlog1 h1
      exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hgt1)
    exact ⟨h1, h2, hm2, h3⟩
  refine ⟨A, s₀, K, hA, hs₀, hK, hthr4, ?_, hExp⟩
  intro s hs C hC_len hdeg hcoeff
  constructor
  · intro _
    exact step_thm1_small_inputs_proved s hs C hdeg hcoeff
  · intro hge hm hcard
    constructor
    · intro htest
      by_contra hnz
      have hμ1 : 1 ≤ pitMu A μ₀ s := by
        have h1 : 1 ≤ pitT A s := (Nat.find_spec (pitT_exists A s)).1
        have h2 : 2 ≤ 2 ^ pitT A s := le_trans (by decide : 2 ≤ 2 ^ 1)
          (Nat.pow_le_pow_right (by decide) h1)
        exact le_trans (by decide) (le_trans h2 (le_max_right μ₀ _))
      have hts := hthr4 s hge
      have hcomp : Computes (paperPerm ℚ (pitMu A μ₀ s)) (s ^ κ) :=
        hEngine (pitMu A μ₀ s) s hs hμ1 hts.1 hts.2.1 hm hcard C hC_len hdeg hcoeff htest hnz
      have heq1 := step_thm1_eq1_proved c hc κ μ₀ s hκ hs
      have hbey : Beyond c (pitMu A μ₀ s) (s ^ κ) := hLB (pitMu A μ₀ s) heq1.1 (s ^ κ) hcomp
      unfold Beyond at hbey
      have hcast : ((s ^ κ : ℕ) : ℝ) = (s : ℝ) ^ κ := by push_cast; rfl
      rw [hcast] at hbey
      linarith [heq1.2.2]
    · intro h0 a
      rw [intCircuit_evalAt_eq_aeval, h0, map_zero]

/-! ### Part 3: Corollary 1 (`cor_1_a26_implies_H_proved`, `cor_1_implication_proved`) -/

/-- Corollary 1 (unconditional implication): `[A26]` `MainTheorem` over `ℚ` implies `HypothesisH c μ₀`. -/
theorem cor_1_a26_implies_H_proved (hA26 : A26_MainTheorem.{0}) :
    ∃ (c : ℝ) (μ₀ : ℕ), HypothesisH c μ₀ := by
  rcases hA26 with ⟨c, hc, hAll⟩
  obtain ⟨m₀, hm₀⟩ := hAll 0
  refine ⟨c, max 1 m₀, hc, le_max_left 1 m₀, ?_⟩
  intro μ hμ s hcomp
  have hcomp' : Computes (perm ℚ μ) s := by rwa [← paperPerm_eq_perm_proved ℚ μ]
  exact (hm₀ ℚ μ (le_trans (le_max_right 1 m₀) hμ) s).2 (by decide) hcomp'

/-- Corollary 1 core: conditional on `A26_MainTheorem` (**UNREFEREED**) and `KI04_Cor_7_4`. -/
theorem cor_1_implication_proved (hA26 : A26_MainTheorem.{0}) (hKI : KI04_Cor_7_4) :
    ∃ (c : ℝ) (μ₀ : ℕ), HypothesisH c μ₀ ∧
      ∃ (A s₀ : ℕ) (K : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 0 < K ∧
        (∀ s ≥ s₀,
          Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
          pitM A μ₀ s < s ∧
          2 ≤ pitM A μ₀ s ∧
          s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
        (∀ (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s),
          C.encodingLength ≤ s →
          C.evalPoly.totalDegree ≤ s →
          CoeffBitBound C.evalPoly s →
          (s < s₀ → (pitSmallTest s C ↔ C.evalPoly = 0)) ∧
          (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
             (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
             pitLargeTest A μ₀ s hm hcard C ↔ C.evalPoly = 0)) ∧
        (∀ s ≥ 2,
          (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ)))) := by
  obtain ⟨c, μ₀, hH⟩ := cor_1_a26_implies_H_proved hA26
  exact ⟨c, μ₀, hH, thm_1_test_correct_proved hKI c μ₀ hH⟩

end ExactMatching.Proofs
