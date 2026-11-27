/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.CitedHypotheses
public import ExactMatching.Defs.PfaffianMatching
public import ExactMatching.Defs.PitAlgorithm
public import ExactMatching.Proofs.PitBounds
public import ExactMatching.Proofs.PitMain
public import ExactMatching.Proofs.MatchingReductions
public import ExactMatching.Proofs.PfaffianIdentity
public import ExactMatching.Proofs.WireExpansion

@[expose] public section

/-!
# Proofs of Proposition 3.1 (combined circuit core) and Theorem 2(a)–(c) decision-witness cores

Parameterized cleanly by the single internal statement `PfaffianClowCircuitExists` so that
Proposition 3.1's combined circuit theorem and all three Theorem 2(a)–(c) decision-witness
theorems close immediately in parallel with the unconditional alternating-clow-sequence DP.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-- Internal statement matching `Paper.pfaffian_clow_circuit_exists`. -/
def PfaffianClowCircuitExists : Prop :=
  ∃ C_const : ℕ, 1 ≤ C_const ∧ ∀ (k : ℕ), 1 ≤ k →
    ∃ C_pf : IntCircuit (Fintype.card (UpperPair (2 * k))),
      C_pf.UsesOnlyUnitConstants ∧
      C_pf.size ≤ C_const * k ^ 4 ∧
      C_pf.evalPoly = MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k)

/-! ### Part 1: Proposition 3.1 combined circuit core -/

/-- Proposition 3.1 (combined algebraic + circuit construction core, from `PfaffianClowCircuitExists`). -/
theorem prop_3_1_pfaffian_circuit_from_clow (hclow : PfaffianClowCircuitExists) :
    ∃ C_0 : ℕ, 1 ≤ C_0 ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k)
        (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : UpperEdge G → Γ) (γstar : Γ),
        let P := groupRingPoly G w γstar
        ∃ C_out : IntCircuit (Fintype.card (UpperEdge G)),
          C_out.UsesOnlyUnitConstants ∧
          C_out.encodingLength ≤ C_0 * (2 * k + Fintype.card Γ) ^ 8 ∧
          C_out.evalPoly = MvPolynomial.rename (Fintype.equivFin (UpperEdge G)) P ∧
          (∀ d, P.coeff d = -1 ∨ P.coeff d = 0 ∨ P.coeff d = 1) ∧
          P.totalDegree ≤ k ∧
          (∀ d ∈ P.support, d.sum (fun _ e => e) = k) ∧
          (P ≠ 0 ↔ ∃ M : Finset (Sym2 (Fin (2 * k))),
            IsPerfectMatching G M ∧ matchingLabelSum G w M = γstar) := by
  rcases hclow with ⟨C_const, hCc, hpf_ex⟩
  let C_0 : ℕ := 3 * C_const * (2 * (Nat.clog 2 (5 * C_const) + 6) + 4)
  have hC_0 : 1 ≤ C_0 := by dsimp [C_0]; nlinarith
  refine ⟨C_0, hC_0, ?_⟩
  intro k hk Γ _ _ _ G _ w γstar
  dsimp only
  obtain ⟨C_pf, hunit, hsz, hpf_eval⟩ := hpf_ex k hk
  obtain ⟨C_out, hOut_unit, hOut_sz, hOut_enc, hOut_eval⟩ :=
    prop_3_1_wire_expansion_proved hk G w γstar C_pf hunit hpf_eval
  have hid := prop_3_1_pfaffian_identity_proved hk G w γstar
  set g := Fintype.card Γ
  have hg : 1 ≤ g := Fintype.card_pos
  set N := 2 * k + g
  have hN3 : 3 ≤ N := by omega
  set M := 2 * g ^ 2 * C_pf.size + g
  have hM_le : M ≤ 3 * C_const * N ^ 6 := by
    have hk_le : k ≤ N := by omega
    have hg_le : g ≤ N := by omega
    have h1 : g ^ 2 * k ^ 4 ≤ N ^ 6 := by
      calc
        g ^ 2 * k ^ 4 ≤ N ^ 2 * N ^ 4 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hg_le 2) (Nat.pow_le_pow_left hk_le 4)
        _ = N ^ 6 := by ring
    have h2 : 2 * g ^ 2 * C_pf.size ≤ 2 * C_const * N ^ 6 := by
      calc
        2 * g ^ 2 * C_pf.size ≤ 2 * g ^ 2 * (C_const * k ^ 4) :=
          Nat.mul_le_mul_left _ hsz
        _ = 2 * C_const * (g ^ 2 * k ^ 4) := by ring
        _ ≤ 2 * C_const * N ^ 6 := Nat.mul_le_mul_left _ h1
    have h3 : g ≤ C_const * N ^ 6 := by
      have hgN6 : g ≤ N ^ 6 := le_trans hg_le (le_self_pow₀ (by omega) (by decide))
      nlinarith
    dsimp only [M]
    linarith
  have hclog_le : Nat.clog 2 (M + (2 * k) ^ 2 + 2) ≤ (Nat.clog 2 (5 * C_const) + 6) * N ^ 2 := by
    have harg : M + (2 * k) ^ 2 + 2 ≤ 5 * C_const * N ^ 6 := by
      have h2k : (2 * k) ^ 2 ≤ N ^ 6 := by
        have h1 : (2 * k) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h2 : N ^ 2 ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
        exact le_trans h1 h2
      have h2c : 2 ≤ C_const * N ^ 6 := by
        have : 2 ≤ N ^ 6 := le_trans (by omega : 2 ≤ N) (le_self_pow₀ (by omega) (by decide))
        nlinarith
      nlinarith
    have hpow_le : 5 * C_const * N ^ 6 ≤ 2 ^ (Nat.clog 2 (5 * C_const) + 6 * N) := by
      have h1 : 5 * C_const ≤ 2 ^ Nat.clog 2 (5 * C_const) :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
      have h2 : N ≤ 2 ^ N := le_of_lt Nat.lt_two_pow_self
      calc
        5 * C_const * N ^ 6 ≤ 2 ^ Nat.clog 2 (5 * C_const) * (2 ^ N) ^ 6 :=
          Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 6)
        _ = 2 ^ (Nat.clog 2 (5 * C_const) + 6 * N) := by rw [← pow_mul, mul_comm N 6, ← pow_add]
    have hcl1 : Nat.clog 2 (M + (2 * k) ^ 2 + 2) ≤ Nat.clog 2 (5 * C_const) + 6 * N :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (le_trans harg hpow_le)
    have hN_le_N2 : N ≤ N ^ 2 := by simpa [sq] using Nat.le_mul_self N
    have h1_le_N2 : 1 ≤ N ^ 2 := by nlinarith
    nlinarith
  have henc_le : C_out.encodingLength ≤ C_0 * N ^ 8 := by
    have hfac : 2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4 ≤
        (2 * (Nat.clog 2 (5 * C_const) + 6) + 4) * N ^ 2 := by
      have h1 : 1 ≤ N ^ 2 := by nlinarith
      nlinarith
    calc
      C_out.encodingLength ≤ M * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) := hOut_enc
      _ ≤ (3 * C_const * N ^ 6) * ((2 * (Nat.clog 2 (5 * C_const) + 6) + 4) * N ^ 2) :=
          Nat.mul_le_mul hM_le hfac
      _ = C_0 * N ^ 8 := by dsimp [C_0]; ring
  exact ⟨C_out, hOut_unit, henc_le, hOut_eval, hid.1, hid.2.1, hid.2.2.1, hid.2.2.2⟩

/-! ### Part 2: Variable padding for `IntCircuit` and edge-sum bridge -/

private def padGate {n s : ℕ} (hle : n ≤ s) : IntGate n → IntGate s
  | .var v => .var ⟨v.val, lt_of_lt_of_le v.isLt hle⟩
  | .const a => .const a
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

private theorem padGate_wf {n s : ℕ} (hle : n ≤ s) (k : ℕ) (g : IntGate n) (h : g.WF k) :
    (padGate hle g).WF k := by
  cases g <;> exact h

private theorem padGate_bitCost {n s : ℕ} (hle : n ≤ s) (g : IntGate n) :
    (padGate hle g).bitCost = g.bitCost := by
  cases g <;> rfl

private def padIntCircuit {n s : ℕ} (hle : n ≤ s) (C : IntCircuit n) : IntCircuit s where
  size := C.size
  size_pos := C.size_pos
  gate k := padGate hle (C.gate k)
  wf k := padGate_wf hle k.val (C.gate k) (C.wf k)
  out := C.out

private theorem padIntCircuit_unit {n s : ℕ} (hle : n ≤ s) (C : IntCircuit n)
    (h : C.UsesOnlyUnitConstants) : (padIntCircuit hle C).UsesOnlyUnitConstants := by
  intro k a hga
  dsimp only [padIntCircuit] at hga
  cases hg : C.gate k <;> rw [hg] at hga <;> dsimp only [padGate] at hga <;> cases hga
  exact h k a hg

private theorem padIntCircuit_encodingLength {n s : ℕ} (hle : n ≤ s) (C : IntCircuit n) :
    (padIntCircuit hle C).encodingLength = C.encodingLength := by
  unfold IntCircuit.encodingLength
  refine Finset.sum_congr rfl fun k _ => padGate_bitCost hle (C.gate k)

private theorem padIntCircuit_evalPoly {n s : ℕ} (hle : n ≤ s) (C : IntCircuit n) :
    (padIntCircuit hle C).evalPoly =
      MvPolynomial.rename (fun v : Fin n => (⟨v.val, lt_of_lt_of_le v.isLt hle⟩ : Fin s)) C.evalPoly := by
  let f : Fin n → Fin s := fun v => ⟨v.val, lt_of_lt_of_le v.isLt hle⟩
  have hgate : ∀ (k : ℕ) (hk : k < C.size),
      (padIntCircuit hle C).evalGateAt (MvPolynomial.X : Fin s → MvPolynomial (Fin s) ℤ) ⟨k, hk⟩ =
        MvPolynomial.rename f (C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) ⟨k, hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hwf := C.wf ⟨k, hk⟩
      cases hg : C.gate ⟨k, hk⟩ with
      | var v =>
        have hgp : (padIntCircuit hle C).gate ⟨k, hk⟩ = .var (f v) := by
          dsimp [padIntCircuit, padGate, f]; rw [hg]
        rw [evalGateAt_var _ _ _ (f v) hgp, evalGateAt_var _ _ _ v hg, MvPolynomial.rename_X]
      | const a =>
        have hgp : (padIntCircuit hle C).gate ⟨k, hk⟩ = .const a := by
          dsimp [padIntCircuit, padGate]; rw [hg]
        rw [evalGateAt_const _ _ _ a hgp, evalGateAt_const _ _ _ a hg, map_intCast]
      | add i j =>
        rw [hg] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        have hgp : (padIntCircuit hle C).gate ⟨k, hk⟩ = .add i j := by
          dsimp [padIntCircuit, padGate]; rw [hg]
        rw [evalGateAt_add _ _ _ i j hgp hi hj, evalGateAt_add _ _ _ i j hg hi hj, map_add,
            ih i hwf.1 hi, ih j hwf.2 hj]
      | sub i j =>
        rw [hg] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        have hgp : (padIntCircuit hle C).gate ⟨k, hk⟩ = .sub i j := by
          dsimp [padIntCircuit, padGate]; rw [hg]
        rw [evalGateAt_sub _ _ _ i j hgp hi hj, evalGateAt_sub _ _ _ i j hg hi hj, map_sub,
            ih i hwf.1 hi, ih j hwf.2 hj]
      | mul i j =>
        rw [hg] at hwf
        have hi := lt_trans hwf.1 hk; have hj := lt_trans hwf.2 hk
        have hgp : (padIntCircuit hle C).gate ⟨k, hk⟩ = .mul i j := by
          dsimp [padIntCircuit, padGate]; rw [hg]
        rw [evalGateAt_mul _ _ _ i j hgp hi hj, evalGateAt_mul _ _ _ i j hg hi hj, map_mul,
            ih i hwf.1 hi, ih j hwf.2 hj]
  exact hgate C.out.val C.out.isLt

private theorem upperEdgeEmbed_injective {n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hle : Fintype.card (UpperEdge H) ≤ s) :
    Function.Injective (upperEdgeEmbed H hle) := by
  intro a b hab
  have hval : (Fintype.equivFin (UpperEdge H) a).val = (Fintype.equivFin (UpperEdge H) b).val := by
    simpa [upperEdgeEmbed] using congrArg Fin.val hab
  exact (Fintype.equivFin (UpperEdge H)).injective (Fin.ext hval)

private theorem card_upperEdge_le_sq {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Fintype.card (UpperEdge H) ≤ n ^ 2 := by
  have hinj : Function.Injective (fun e : UpperEdge H => e.val.val) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have hle := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_prod, Fintype.card_fin, sq] using hle

private theorem matchingLabelSum_restrictEdgeWeight {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (w : Sym2 (Fin n) → Γ)
    (M : Finset (Sym2 (Fin n))) (hM : IsPerfectMatching H M) :
    matchingLabelSum H (restrictEdgeWeight H w) M = ∑ e ∈ M, w e := by
  classical
  unfold matchingLabelSum restrictEdgeWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun e _ => s(e.val.val.1, e.val.val.2))
    (fun e he => (Finset.mem_filter.mp he).2)
    (fun e₁ _ e₂ _ heq => by
      have hsym := Sym2.eq_iff.mp heq
      rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
      · have hlt1 : e₁.val.val.1 < e₁.val.val.2 := e₁.val.property
        have hlt2 : e₂.val.val.1 < e₂.val.val.2 := e₂.val.property
        rw [h1, h2] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _))
    (fun e he => by
      have hedg : e ∈ H.edgeSet := hM.1 e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : H.Adj u v := hedg
        have hne : u ≠ v := H.ne_of_adj hadj
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨⟨⟨(u, v), hlt⟩, hadj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
        · exact ⟨⟨⟨(v, u), hgt⟩, (H.adj_comm u v).mp hadj⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Sym2.eq_swap]⟩, Sym2.eq_swap⟩)
    (fun _ _ => rfl)

private theorem rename_coeffBitBound_of_unit {V W : Type*} (f : V → W) (hf : Function.Injective f)
    (P : MvPolynomial V ℤ) (hunit : ∀ d, P.coeff d = -1 ∨ P.coeff d = 0 ∨ P.coeff d = 1) (s : ℕ) :
    CoeffBitBound (MvPolynomial.rename f P) s := by
  classical
  intro d
  by_cases hex : ∃ e : V →₀ ℕ, Finsupp.mapDomain f e = d
  · rcases hex with ⟨e, rfl⟩
    rw [MvPolynomial.coeff_rename_mapDomain _ hf]
    rcases hunit e with h | h | h <;> rw [h]
    · exact Nat.one_le_pow _ _ (by decide)
    · exact Nat.zero_le _
    · exact Nat.one_le_pow _ _ (by decide)
  · have h0 : (MvPolynomial.rename f P).coeff d = 0 := by
      rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
        MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hterm : MvPolynomial.C (P.coeff e) *
          e.prod (fun v k => (MvPolynomial.X (f v) : MvPolynomial W ℤ) ^ k) =
          MvPolynomial.monomial (Finsupp.mapDomain f e) (P.coeff e) := by
        rw [MvPolynomial.monomial_eq]
        congr 1
        rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      change (MvPolynomial.C (P.coeff e) *
        e.prod (fun v k => (MvPolynomial.X (f v) : MvPolynomial W ℤ) ^ k)).coeff d = 0
      rw [hterm, MvPolynomial.coeff_monomial, if_neg (fun h => hex ⟨e, h⟩)]
    rw [h0]; exact Nat.zero_le _

/-! ### Part 3: Theorem 2(c), 2(a), 2(b) decision-witness cores -/

private theorem pit_eval_poly_scale {A μ₀ s₀ : ℕ} (K5 : ℝ) (hK5 : 0 < K5)
    (hExp5 : ∀ s ≥ 2,
      (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 5) ≤
        expTwo (expTwo (K5 * (Real.logb 2 s) ^ (3 / 4 : ℝ))))
    (C_0 : ℕ) (hC_0 : 1 ≤ C_0) :
    let K' := K5 * (Real.logb 2 (C_0 : ℝ) + 8) ^ (3 / 4 : ℝ)
    0 < K' ∧ ∀ (k g : ℕ), 1 ≤ k → 1 ≤ g →
      let s := max (2 * k) (C_0 * (2 * k + g) ^ 8)
      ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
        ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
          expTwo (expTwo (K' * (Real.logb 2 ((2 * k + g : ℕ) : ℝ)) ^ (3 / 4 : ℝ))) := by
  have hlogC0_nn : 0 ≤ Real.logb 2 (C_0 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hC_0)
  have hfac_pos : 0 < Real.logb 2 (C_0 : ℝ) + 8 := by linarith
  refine ⟨mul_pos hK5 (Real.rpow_pos_of_pos hfac_pos _), fun k g hk hg => ?_⟩
  dsimp only
  set N := 2 * k + g
  have hN3 : 3 ≤ N := by omega
  set s := max (2 * k) (C_0 * N ^ 8)
  have h2k_sq_le_s : (2 * k) ^ 2 ≤ s := by
    have h1 : (2 * k) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : N ^ 2 ≤ N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    have h3 : 1 * N ^ 8 ≤ C_0 * N ^ 8 := Nat.mul_le_mul_right _ hC_0
    exact le_trans h1 (le_trans h2 (le_trans (by simpa using h3) (le_max_right _ _)))
  have hs2 : 2 ≤ s := le_trans (by omega : 2 ≤ 2 * k) (le_max_left _ _)
  have hseq : s = C_0 * N ^ 8 := by
    apply max_eq_right
    have h1 : 2 * k ≤ N ^ 8 := le_trans (by omega : 2 * k ≤ N) (le_self_pow₀ (by omega) (by decide))
    nlinarith
  have hmul_le : ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
      ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
      (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 5) := by
    have h1 : (2 * k : ℝ) ^ 2 ≤ (s : ℝ) := by exact_mod_cast h2k_sq_le_s
    have h2 : (2 * k : ℝ) ^ 2 * (s : ℝ) ^ 4 ≤ (s : ℝ) ^ 5 := by
      calc
        (2 * k : ℝ) ^ 2 * (s : ℝ) ^ 4 ≤ (s : ℝ) * (s : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (s : ℝ) ^ 5 := by ring
    have h3 := mul_le_mul_of_nonneg_left h2
      (show 0 ≤ (pitEvalPointCount A μ₀ s₀ s : ℝ) * (2 : ℝ) ^ pitMu A μ₀ s by positivity)
    linarith
  have hlogs_le : Real.logb 2 s ≤ (Real.logb 2 (C_0 : ℝ) + 8) * Real.logb 2 (N : ℝ) := by
    have hsR : (s : ℝ) = (C_0 : ℝ) * (N : ℝ) ^ (8 : ℕ) := by rw [hseq]; push_cast; rfl
    rw [hsR, Real.logb_mul (by exact_mod_cast (show C_0 ≠ 0 by omega)) (by positivity),
      Real.logb_pow]
    have hlogN1 : (1 : ℝ) ≤ Real.logb 2 (N : ℝ) := logb_two_ge_one (by omega)
    push_cast
    nlinarith
  have hinner : K5 * (Real.logb 2 s) ^ (3 / 4 : ℝ) ≤
      (K5 * (Real.logb 2 (C_0 : ℝ) + 8) ^ (3 / 4 : ℝ)) * (Real.logb 2 (N : ℝ)) ^ (3 / 4 : ℝ) := by
    have h1 : (Real.logb 2 s) ^ (3 / 4 : ℝ) ≤
        ((Real.logb 2 (C_0 : ℝ) + 8) * Real.logb 2 (N : ℝ)) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith [logb_two_ge_one hs2]) hlogs_le (by norm_num)
    rw [Real.mul_rpow hfac_pos.le (by linarith [logb_two_ge_one (show 2 ≤ N by omega)])] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hK5.le
    linarith
  exact le_trans hmul_le (le_trans (hExp5 s hs2)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner)))

/-- Theorem 2(c) decision-witness core (from `PfaffianClowCircuitExists`). -/
theorem thm_2c_decision_witness_from_clow (hclow : PfaffianClowCircuitExists)
    (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (k : ℕ) (_hk : 1 ≤ k)
        (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : Sym2 (Fin (2 * k)) → Γ) (γstar : Γ),
        let s := max (2 * k) (C_0 * (2 * k + Fintype.card Γ) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (restrictEdgeWeight H w) γstar) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ ∑ e ∈ M, w e = γstar),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            ∑ e ∈ M, w e = γstar ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k + Fintype.card Γ : ℕ) : ℝ)) ^ (3 / 4 : ℝ))))) ∧
      (∀ (C : ℝ), 0 < C → ∃ K'_C : ℝ, 0 < K'_C ∧
        ∀ (k : ℕ) (_hk : 1 ≤ k) (gCard : ℕ), 1 ≤ gCard →
          (gCard : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ C →
          let s := max (2 * k) (C_0 * (2 * k + gCard) ^ 8)
          ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'_C * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  obtain ⟨A, s₀, _, hA, hs₀, _, hthr, hpit, _⟩ := thm_1_test_correct_proved hKI c μ₀ hH
  obtain ⟨C_0, hC_0, hprop31⟩ := prop_3_1_pfaffian_circuit_from_clow hclow
  obtain ⟨K5, hK5, hExp5⟩ := step_thm1_exponent_bound_proved A μ₀ s₀ 5 hA hH.2.1 hs₀
  have hscale := pit_eval_poly_scale K5 hK5 hExp5 C_0 hC_0
  set K' := K5 * (Real.logb 2 (C_0 : ℝ) + 8) ^ (3 / 4 : ℝ)
  refine ⟨A, s₀, C_0, K', hA, hs₀, hC_0, hscale.1, hthr, ?_, ?_⟩
  · intro k hk Γ _ _ _ G _ w γstar
    dsimp only
    set s := max (2 * k) (C_0 * (2 * k + Fintype.card Γ) ^ 8)
    have hs2 : 2 ≤ s := le_trans (by omega) (le_max_left _ _)
    refine ⟨?_, ?_, hscale.2 k (Fintype.card Γ) hk Fintype.card_pos⟩
    · intro H _
      obtain ⟨C_out, hOut_unit, hOut_enc, hOut_eval, hP_unit, hP_deg, _, hP_iff⟩ :=
        hprop31 k hk Γ H (restrictEdgeWeight H w) γstar
      have hle : Fintype.card (UpperEdge H) ≤ s := by
        have h1 : Fintype.card (UpperEdge H) ≤ (2 * k) ^ 2 := card_upperEdge_le_sq H
        have h2 : (2 * k) ^ 2 ≤ (2 * k + Fintype.card Γ) ^ 8 := by
          have ha : (2 * k) ^ 2 ≤ (2 * k + Fintype.card Γ) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have hb : (2 * k + Fintype.card Γ) ^ 2 ≤ (2 * k + Fintype.card Γ) ^ 8 :=
            Nat.pow_le_pow_right (by omega) (by decide)
          exact le_trans ha hb
        have h3 : 1 * (2 * k + Fintype.card Γ) ^ 8 ≤ C_0 * (2 * k + Fintype.card Γ) ^ 8 :=
          Nat.mul_le_mul_right _ hC_0
        exact le_trans h1 (le_trans h2 (le_trans (by simpa using h3) (le_max_right _ _)))
      let C_H : IntCircuit s := padIntCircuit hle C_out
      have hCH_unit : C_H.UsesOnlyUnitConstants := padIntCircuit_unit hle C_out hOut_unit
      have hCH_enc : C_H.encodingLength ≤ s := by
        rw [padIntCircuit_encodingLength]
        exact le_trans hOut_enc (le_max_right _ _)
      have hCH_eval : C_H.evalPoly =
          MvPolynomial.rename (upperEdgeEmbed H hle)
            (groupRingPoly H (restrictEdgeWeight H w) γstar) := by
        dsimp only [C_H]
        rw [padIntCircuit_evalPoly, hOut_eval, MvPolynomial.rename_rename]
        rfl
      have hCH_deg : C_H.evalPoly.totalDegree ≤ s := by
        rw [hCH_eval]
        exact le_trans (MvPolynomial.totalDegree_rename_le _ _)
          (le_trans hP_deg (le_trans (by omega : k ≤ 2 * k) (le_max_left _ _)))
      have hCH_bit : CoeffBitBound C_H.evalPoly s := by
        rw [hCH_eval]
        exact rename_coeffBitBound_of_unit _ (upperEdgeEmbed_injective H hle) _ hP_unit s
      have hCH_ne_iff : C_H.evalPoly ≠ 0 ↔
          ∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar := by
        have h1 : C_H.evalPoly ≠ 0 ↔ groupRingPoly H (restrictEdgeWeight H w) γstar ≠ 0 := by
          rw [hCH_eval]
          constructor
          · intro hne h0; exact hne (by rw [h0, map_zero])
          · intro hne h0
            exact hne ((MvPolynomial.rename_injective _ (upperEdgeEmbed_injective H hle))
              (by simpa using h0))
        rw [h1, hP_iff]
        constructor <;> rintro ⟨M, hM, hsum⟩
        · exact ⟨M, hM, by rwa [← matchingLabelSum_restrictEdgeWeight H w M hM]⟩
        · exact ⟨M, hM, by rwa [matchingLabelSum_restrictEdgeWeight H w M hM]⟩
      have hpitH := hpit s hs2 C_H hCH_enc hCH_deg hCH_bit
      refine ⟨hle, C_H, hCH_unit, hCH_enc, hCH_eval, hCH_deg, hCH_bit, ?_, ?_⟩
      · intro hlt
        rw [(hpitH.1 hlt).not]
        exact hCH_ne_iff
      · intro hge hm hcard
        rw [(hpitH.2 hge hm hcard).not]
        exact hCH_ne_iff
    · intro oracle horacle edges hedges hnodup hex
      exact step_thm2c_self_reduction_proved (by omega : 2 ≤ 2 * k) G w γstar oracle horacle
        edges hedges hnodup hex
  · intro C hC
    let Cmax : ℝ := max 1 C
    let K'_C : ℝ := K' * (1 + Cmax) ^ (3 / 4 : ℝ)
    have h1C_pos : 0 < 1 + Cmax := by
      have : 1 ≤ Cmax := le_max_left _ _
      linarith
    refine ⟨K'_C, mul_pos hscale.1 (Real.rpow_pos_of_pos h1C_pos _), fun k hk gCard hg hgC => ?_⟩
    dsimp only
    have hbase := hscale.2 k gCard hk hg
    have h2k1 : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
    have hlog2k1 : (1 : ℝ) ≤ Real.logb 2 ((2 * k : ℕ) : ℝ) := logb_two_ge_one (by omega)
    have hsum_le : ((2 * k + gCard : ℕ) : ℝ) ≤ 2 * ((2 * k : ℕ) : ℝ) ^ Cmax := by
      rw [Nat.cast_add]
      have h1 : ((2 * k : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ Cmax := by
        have := Real.rpow_le_rpow_of_exponent_le h2k1 (le_max_left 1 C)
        simpa using this
      have h2 : (gCard : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ Cmax :=
        le_trans hgC (Real.rpow_le_rpow_of_exponent_le h2k1 (le_max_right 1 C))
      linarith
    have hlog_le : Real.logb 2 ((2 * k + gCard : ℕ) : ℝ) ≤
        (1 + Cmax) * Real.logb 2 ((2 * k : ℕ) : ℝ) := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hsum_le
      rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos (by positivity) _).ne',
        Real.logb_self_eq_one (by norm_num),
        Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at h1
      nlinarith
    have hinner : K' * (Real.logb 2 ((2 * k + gCard : ℕ) : ℝ)) ^ (3 / 4 : ℝ) ≤
        K'_C * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by linarith [logb_two_ge_one (show 2 ≤ 2 * k + gCard by omega)])
        hlog_le (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rw [Real.mul_rpow h1C_pos.le (by linarith)] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hscale.1.le
      dsimp only [K'_C]
      linarith
    exact le_trans hbase (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner))

/-- Theorem 2(a) decision-witness core (Exact Matching via `ZMod (k + 1)`). -/
theorem thm_2a_decision_witness_from_clow (hclow : PfaffianClowCircuitExists)
    (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k)
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (R : Finset (Sym2 (Fin (2 * k)))) (target : ℕ) (htarget : target ≤ k),
        let s := max (2 * k) (C_0 * (2 * k + (k + 1)) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (exactMatchingLabel H R) (target : ZMod (k + 1))) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ (M ∩ R).card = target)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ (M ∩ R).card = target))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ (M ∩ R).card = target)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ (M ∩ R).card = target),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            (M ∩ R).card = target ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  obtain ⟨A, s₀, C_0, _, hA, hs₀, hC_0, _, hthr, h2c, h2c_C⟩ :=
    thm_2c_decision_witness_from_clow hclow hKI c μ₀ hH
  obtain ⟨K'1, hK'1, hbound1⟩ := h2c_C 1 zero_lt_one
  refine ⟨A, s₀, C_0, K'1, hA, hs₀, hC_0, hK'1, hthr, ?_⟩
  intro k hk G _ R target htarget
  dsimp only
  let w : Sym2 (Fin (2 * k)) → ZMod (k + 1) := fun e => if e ∈ R then 1 else 0
  have hcardZ : Fintype.card (ZMod (k + 1)) = k + 1 := ZMod.card (k + 1)
  have hspec := h2c k hk (ZMod (k + 1)) G w (target : ZMod (k + 1))
  rw [hcardZ] at hspec
  have hiff_M : ∀ (H : SimpleGraph (Fin (2 * k))) [DecidableRel H.Adj],
      (∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = (target : ZMod (k + 1))) ↔
      (∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧ (M ∩ R).card = target) := by
    intro H _
    have hemb := (step_thm2a_embedding_proved hk H R target htarget).1
    constructor <;> rintro ⟨M, hM, hprop⟩
    · refine ⟨M, hM, (hemb M hM).mpr ?_⟩
      change matchingLabelSum H (restrictEdgeWeight H w) M = _
      rwa [matchingLabelSum_restrictEdgeWeight H w M hM]
    · refine ⟨M, hM, ?_⟩
      rw [← matchingLabelSum_restrictEdgeWeight H w M hM]
      exact (hemb M hM).mp hprop
  refine ⟨?_, ?_, ?_⟩
  · intro H _
    obtain ⟨hle, C_H, hunit, henc, heval, hdeg, hbit, hsm, hlg⟩ := hspec.1 H
    have hw_eq : restrictEdgeWeight H w = exactMatchingLabel H R := rfl
    rw [hw_eq] at heval
    refine ⟨hle, C_H, hunit, henc, heval, hdeg, hbit, ?_, ?_⟩
    · intro hlt; rw [hsm hlt, hiff_M H]
    · intro hge hm hcard; rw [hlg hge hm hcard, hiff_M H]
  · intro oracle horacle edges hedges hnodup hex
    have horacle' : ∀ H, oracle H = true ↔
        ∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = (target : ZMod (k + 1)) := by
      intro H
      classical
      rw [horacle H, ← hiff_M H]
    have hex' : ∃ M : Finset (Sym2 (Fin (2 * k))),
        IsPerfectMatching G M ∧ ∑ e ∈ M, w e = (target : ZMod (k + 1)) := (hiff_M G).mpr hex
    obtain ⟨M, hHM, hMG, hsum, hlen⟩ := hspec.2.1 oracle horacle' edges hedges hnodup hex'
    have hemb := (step_thm2a_embedding_proved hk G R target htarget).1 M hMG
    refine ⟨M, hHM, hMG, hemb.mpr ?_, hlen⟩
    change matchingLabelSum G (restrictEdgeWeight G w) M = _
    rwa [matchingLabelSum_restrictEdgeWeight G w M hMG]
  · have hle1 : ((k + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]; exact_mod_cast (show k + 1 ≤ 2 * k by omega)
    exact hbound1 k hk (k + 1) (by omega) hle1

/-- Theorem 2(b) decision-witness core (bounded integer weights via shifted `ZMod (2kW + 1)`). -/
theorem thm_2b_decision_witness_from_clow (hclow : PfaffianClowCircuitExists)
    (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (k : ℕ) (_hk : 1 ≤ k) (W : ℕ)
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : Sym2 (Fin (2 * k)) → ℤ) (hw : ∀ e, -(W : ℤ) ≤ w e ∧ w e ≤ (W : ℤ))
        (target : ℤ) (htarget : -(k * W : ℤ) ≤ target ∧ target ≤ (k * W : ℤ)),
        let s := max (2 * k) (C_0 * (2 * k + (2 * k * W + 1)) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (boundedWeightLabel W H (restrictEdgeWeight H w))
                  ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1))) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ ∑ e ∈ M, w e = target),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            ∑ e ∈ M, w e = target ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k + W : ℕ) : ℝ)) ^ (3 / 4 : ℝ))))) ∧
      (∀ (C : ℝ), 0 < C → ∃ K'_C : ℝ, 0 < K'_C ∧
        ∀ (k : ℕ) (_hk : 1 ≤ k) (W : ℕ),
          (W : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ C →
          let s := max (2 * k) (C_0 * (2 * k + (2 * k * W + 1)) ^ 8)
          ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'_C * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  obtain ⟨A, s₀, C_0, K'2c, hA, hs₀, hC_0, hK'2c, hthr, h2c, h2c_C⟩ :=
    thm_2c_decision_witness_from_clow hclow hKI c μ₀ hH
  let K' : ℝ := K'2c * (2 : ℝ) ^ (3 / 4 : ℝ)
  have hK' : 0 < K' := mul_pos hK'2c (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨A, s₀, C_0, K', hA, hs₀, hC_0, hK', hthr, ?_, ?_⟩
  · intro k hk W G _ w hw target htarget
    dsimp only
    let wShift : Sym2 (Fin (2 * k)) → ZMod (2 * k * W + 1) :=
      fun e => ((w e + (W : ℤ)) : ZMod (2 * k * W + 1))
    have hcardZ : Fintype.card (ZMod (2 * k * W + 1)) = 2 * k * W + 1 := ZMod.card _
    have hspec := h2c k hk (ZMod (2 * k * W + 1)) G wShift ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1))
    rw [hcardZ] at hspec
    have hsum_bridge : ∀ (H : SimpleGraph (Fin (2 * k))) [DecidableRel H.Adj]
        (M : Finset (Sym2 (Fin (2 * k)))), IsPerfectMatching H M →
        (∑ e : UpperEdge H, if s(e.val.val.1, e.val.val.2) ∈ M then restrictEdgeWeight H w e else 0) =
          ∑ e ∈ M, w e := fun H _ M hM => matchingLabelSum_restrictEdgeWeight H w M hM
    have hiff_M : ∀ (H : SimpleGraph (Fin (2 * k))) [DecidableRel H.Adj],
        (∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧
          ∑ e ∈ M, wShift e = ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1))) ↔
        (∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target) := by
      intro H _
      have hemb := (step_thm2b_embedding_proved hk W H (restrictEdgeWeight H w)
        (fun e => hw _) target htarget).1
      constructor <;> rintro ⟨M, hM, hprop⟩
      · refine ⟨M, hM, ?_⟩
        rw [← hsum_bridge H M hM]
        refine (hemb M hM).mpr ?_
        change matchingLabelSum H (restrictEdgeWeight H wShift) M = _
        rwa [matchingLabelSum_restrictEdgeWeight H wShift M hM]
      · refine ⟨M, hM, ?_⟩
        rw [← matchingLabelSum_restrictEdgeWeight H wShift M hM]
        refine (hemb M hM).mp ?_
        rwa [hsum_bridge H M hM]
    refine ⟨?_, ?_, ?_⟩
    · intro H _
      obtain ⟨hle, C_H, hunit, henc, heval, hdeg, hbit, hsm, hlg⟩ := hspec.1 H
      have hw_eq : restrictEdgeWeight H wShift = boundedWeightLabel W H (restrictEdgeWeight H w) := rfl
      rw [hw_eq] at heval
      refine ⟨hle, C_H, hunit, henc, heval, hdeg, hbit, ?_, ?_⟩
      · intro hlt; rw [hsm hlt, hiff_M H]
      · intro hge hm hcard; rw [hlg hge hm hcard, hiff_M H]
    · intro oracle horacle edges hedges hnodup hex
      have horacle' : ∀ H, oracle H = true ↔
          ∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching H M ∧
            ∑ e ∈ M, wShift e = ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)) := by
        intro H
        classical
        rw [horacle H, ← hiff_M H]
      have hex' : ∃ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching G M ∧
          ∑ e ∈ M, wShift e = ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)) := (hiff_M G).mpr hex
      obtain ⟨M, hHM, hMG, hsum, hlen⟩ := hspec.2.1 oracle horacle' edges hedges hnodup hex'
      have hemb := (step_thm2b_embedding_proved hk W G (restrictEdgeWeight G w)
        (fun e => hw _) target htarget).1 M hMG
      refine ⟨M, hHM, hMG, ?_, hlen⟩
      rw [← hsum_bridge G M hMG]
      refine hemb.mpr ?_
      change matchingLabelSum G (restrictEdgeWeight G wShift) M = _
      rwa [matchingLabelSum_restrictEdgeWeight G wShift M hMG]
    · have hbase := hspec.2.2
      have hsq : 2 * k + (2 * k * W + 1) ≤ (2 * k + W) ^ 2 :=
        (step_thm2b_embedding_proved hk W G (restrictEdgeWeight G w) (fun e => hw _) target htarget).2
      have hlog_le : Real.logb 2 ((2 * k + (2 * k * W + 1) : ℕ) : ℝ) ≤
          2 * Real.logb 2 ((2 * k + W : ℕ) : ℝ) := by
        have h1 : ((2 * k + (2 * k * W + 1) : ℕ) : ℝ) ≤ (((2 * k + W : ℕ) : ℝ) ^ (2 : ℕ)) := by
          exact_mod_cast hsq
        have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h1
        rw [Real.logb_pow] at h2
        simpa using h2
      have hinner : K'2c * (Real.logb 2 ((2 * k + (2 * k * W + 1) : ℕ) : ℝ)) ^ (3 / 4 : ℝ) ≤
          K' * (Real.logb 2 ((2 * k + W : ℕ) : ℝ)) ^ (3 / 4 : ℝ) := by
        have h1 := Real.rpow_le_rpow
          (by linarith [logb_two_ge_one (show 2 ≤ 2 * k + (2 * k * W + 1) by omega)])
          hlog_le (by norm_num : (0 : ℝ) ≤ 3 / 4)
        rw [Real.mul_rpow (by norm_num) (by linarith [logb_two_ge_one (show 2 ≤ 2 * k + W by omega)])] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 hK'2c.le
        dsimp only [K']
        linarith
      exact le_trans hbase (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner))
  · intro C hC
    obtain ⟨K'_C, hK'_C, hboundC⟩ := h2c_C (C + 2) (by linarith)
    refine ⟨K'_C, hK'_C, fun k hk W hWC => ?_⟩
    have hg_le : ((2 * k * W + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ (C + 2) := by
      have h2k_ge2 : (2 : ℝ) ≤ 2 * (k : ℝ) := by
        have : 2 ≤ 2 * k := by omega
        exact_mod_cast this
      have h2k_pow : ((2 * k : ℕ) : ℝ) ^ (C + 2) =
          ((2 * k : ℕ) : ℝ) ^ C * ((2 * k : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ) := by
        rw [Real.rpow_add (by positivity), Real.rpow_two]; ring
      rw [h2k_pow]
      push_cast
      have h1 : (2 * (k : ℝ)) * (W : ℝ) ≤ (2 * (k : ℝ)) * ((2 * (k : ℝ)) ^ C) :=
        mul_le_mul_of_nonneg_left (by simpa using hWC) (by positivity)
      have h2 : (1 : ℝ) ≤ (2 * (k : ℝ)) ^ C := Real.one_le_rpow (by linarith) hC.le
      have h3 : 2 * ((2 * (k : ℝ)) ^ C * (2 * (k : ℝ))) ≤
          (2 * (k : ℝ)) ^ C * (2 * (k : ℝ)) * (2 * (k : ℝ)) := by
        have hnn : 0 ≤ (2 * (k : ℝ)) ^ C * (2 * (k : ℝ)) := by positivity
        nlinarith
      have h4 : (1 : ℝ) ≤ (2 * (k : ℝ)) ^ C * (2 * (k : ℝ)) := by nlinarith
      linarith
    exact hboundC k hk (2 * k * W + 1) (by omega) hg_le

end ExactMatching.Proofs
