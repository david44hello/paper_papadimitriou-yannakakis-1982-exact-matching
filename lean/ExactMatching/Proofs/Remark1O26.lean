/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.CitedHypotheses
public import ExactMatching.Defs.PitAlgorithm
public import ExactMatching.Proofs.CircuitsTransfer
public import ExactMatching.Proofs.PitBounds
public import ExactMatching.Proofs.PitMain
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Proof of Remark 1 (`[O26]` stronger permanent lower bound tradeoff)

Proves `rem_1_tradeoff_proved`: conditional on `O26_Thm_1_1` (**UNREFEREED**) and
`KI04_Cor_7_4`, fixing `C₁ ≥ 4` and taking `μ = o26Mu C₁ N₀ s` gives explicit PIT
correctness and the sharpened `exp₂(exp₂(K'' (log₂ s)^(1/2) log₂ log₂(s + 2)))`
evaluation-point bounds (including `K'''` and `K'''_C` for polynomial matching sizes).
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: Elementary real-analytic inequalities for Remark 1 -/

private theorem logb_logb_add_two_ge_one {s : ℕ} (hs : 2 ≤ s) :
    (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
  have h4 : (4 : ℝ) ≤ ((s + 2 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ s + 2 by omega)
  have hlog4 : (2 : ℝ) ≤ Real.logb 2 ((s + 2 : ℕ) : ℝ) := by
    have h2 : Real.logb 2 4 = 2 := by
      have h4eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4eq, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]; norm_num
    calc
      (2 : ℝ) = Real.logb 2 4 := h2.symm
      _ ≤ Real.logb 2 ((s + 2 : ℕ) : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h4
  rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hlog4

private theorem logb_le_rpow_const {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 x ≤ (1 / (α * Real.log 2)) * x ^ α := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow_pos : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have h1 : Real.log (x ^ α) ≤ x ^ α := le_trans (Real.log_le_sub_one_of_pos hpow_pos) (by linarith)
  rw [Real.log_rpow hx0] at h1
  have h2 : Real.log x ≤ (1 / α) * x ^ α := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hα]
    linarith
  rw [Real.logb]
  calc
    Real.log x / Real.log 2 ≤ ((1 / α) * x ^ α) / Real.log 2 :=
      div_le_div_of_nonneg_right h2 hlog2.le
    _ = (1 / (α * Real.log 2)) * x ^ α := by ring

private theorem div_logb_mono {x y : ℝ} (hx : 4 ≤ x) (hxy : x ≤ y) :
    x / Real.logb 2 x ≤ y / Real.logb 2 y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1_lt_logx : 1 < Real.log x := by
    have he : Real.exp 1 < x := lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith)
    have hlog := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at hlog
  have hlogx_pos : 0 < Real.log x := by linarith
  have hlogy_pos : 0 < Real.log y := lt_of_lt_of_le hlogx_pos (Real.log_le_log hx0 hxy)
  have hlogbx_pos : 0 < Real.logb 2 x := div_pos hlogx_pos hlog2
  have hlogby_pos : 0 < Real.logb 2 y := div_pos hlogy_pos hlog2
  have hratio_pos : 0 < y / x := div_pos hy0 hx0
  have hratio_ge : 1 ≤ y / x := (one_le_div hx0).mpr hxy
  have hsub : Real.log y - Real.log x ≤ y / x - 1 := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    exact Real.log_le_sub_one_of_pos hratio_pos
  have hmul1 : y / x - 1 ≤ (y / x - 1) * Real.log x :=
    le_mul_of_one_le_right (by linarith) h1_lt_logx.le
  have hmul2 : x * (Real.log y - Real.log x) ≤ x * ((y / x - 1) * Real.log x) :=
    mul_le_mul_of_nonneg_left (le_trans hsub hmul1) hx0.le
  have hsimp : x * ((y / x - 1) * Real.log x) = (y - x) * Real.log x := by
    field_simp [hx0.ne']
  have hkey : x * Real.log y ≤ y * Real.log x := by linarith
  rw [div_le_div_iff₀ hlogbx_pos hlogby_pos]
  simp only [Real.logb]
  have hkey' : x * (Real.log y / Real.log 2) ≤ y * (Real.log x / Real.log 2) := by
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hkey hlog2.le
  exact hkey'

/-! ### Part 2: `o26T` upper/lower bounds and threshold `s₀` -/

private theorem o26T_ge_four (C₁ s : ℕ) (hC₁ : 4 ≤ C₁) (hs : 2 ≤ s) :
    4 ≤ o26T C₁ s := by
  have hspec := Nat.find_spec (o26T_exists C₁ s)
  have hL : 1 ≤ Nat.clog 2 s := Nat.clog_pos (by decide) (by omega)
  have hL2 : 2 ≤ Nat.clog 2 (s + 2) := by
    have h4 : 2 ^ 1 < s + 2 := by omega
    have hgt : 1 < Nat.clog 2 (s + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr h4
    omega
  have hLL : 1 ≤ Nat.clog 2 (Nat.clog 2 (s + 2)) := Nat.clog_pos (by decide) (by omega)
  have h16 : 16 ≤ (o26T C₁ s) ^ 2 := by
    calc
      16 = 4 ^ 2 * 1 * 1 ^ 2 := by norm_num
      _ ≤ C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 := by
          refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hC₁ 2) hL)
            (Nat.pow_le_pow_left hLL 2)
      _ ≤ (o26T C₁ s) ^ 2 := hspec.2
  nlinarith

private theorem o26T_le_bound (C₁ s : ℕ) (hC₁ : 4 ≤ C₁) (hs : 2 ≤ s) :
    (o26T C₁ s : ℝ) ≤
      ((6 * C₁ + 1 : ℕ) : ℝ) * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
        Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
  let L := Nat.clog 2 s
  let LL := Nat.clog 2 (Nat.clog 2 (s + 2))
  let t_up := Nat.ceil ((C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ))
  have hL1 : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hL2 : 2 ≤ Nat.clog 2 (s + 2) := by
    have h4 : 2 ^ 1 < s + 2 := by omega
    have hgt : 1 < Nat.clog 2 (s + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr h4
    omega
  have hLL1 : 1 ≤ LL := Nat.clog_pos (by decide) (by omega)
  have ht_up_pos : 1 ≤ t_up := by
    apply Nat.ceil_pos.mpr
    have h1 : (0 : ℝ) < (C₁ : ℝ) := by positivity
    have h2 : (0 : ℝ) < (L : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL1) _
    have h3 : (0 : ℝ) < (LL : ℝ) := by exact_mod_cast hLL1
    positivity
  have ht_up_sq : C₁ ^ 2 * L * LL ^ 2 ≤ t_up ^ 2 := by
    have hR : ((C₁ ^ 2 * L * LL ^ 2 : ℕ) : ℝ) ≤ ((t_up ^ 2 : ℕ) : ℝ) := by
      have hceil : (C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ) ≤ (t_up : ℝ) := Nat.le_ceil _
      have hsq : ((C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ)) ^ 2 ≤ (t_up : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hceil 2
      have hlhs : ((C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ)) ^ 2 = ((C₁ ^ 2 * L * LL ^ 2 : ℕ) : ℝ) := by
        have hsqrt : ((L : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (L : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
        calc
          ((C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ)) ^ 2
              = (C₁ : ℝ) ^ 2 * ((L : ℝ) ^ (1 / 2 : ℝ)) ^ 2 * (LL : ℝ) ^ 2 := by ring
          _ = (C₁ : ℝ) ^ 2 * (L : ℝ) * (LL : ℝ) ^ 2 := by rw [hsqrt]
          _ = ((C₁ ^ 2 * L * LL ^ 2 : ℕ) : ℝ) := by push_cast; ring
      rw [← hlhs]
      simpa using hsq
    exact_mod_cast hR
  have ht_le_nat : o26T C₁ s ≤ t_up := Nat.find_min' (o26T_exists C₁ s) ⟨ht_up_pos, ht_up_sq⟩
  have ht_le_R : (o26T C₁ s : ℝ) ≤ (C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ) + 1 := by
    have h1 : (o26T C₁ s : ℝ) ≤ (t_up : ℝ) := by exact_mod_cast ht_le_nat
    have h2 : (t_up : ℝ) < (C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs
  have hll_ge1 : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := logb_logb_add_two_ge_one hs
  have hL_le : (L : ℝ) ≤ 2 * Real.logb 2 s := by
    have h := clog_lt_logb_add_one s hs
    linarith
  have hL_rpow : (L : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * (Real.logb 2 s) ^ (1 / 2 : ℝ) := by
    have h1 : (L : ℝ) ^ (1 / 2 : ℝ) ≤ (2 * Real.logb 2 s) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hL_le (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa using this
    nlinarith [Real.rpow_nonneg (show 0 ≤ Real.logb 2 s by linarith) (1 / 2 : ℝ)]
  have hLL_le : (LL : ℝ) ≤ 3 * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
    have hlogs2_ge2 : (2 : ℝ) ≤ Real.logb 2 ((s + 2 : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) ≤ ((s + 2 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ s + 2 by omega)
      have h2 : Real.logb 2 4 = 2 := by
        have h4eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [h4eq, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]; norm_num
      calc
        (2 : ℝ) = Real.logb 2 4 := h2.symm
        _ ≤ Real.logb 2 ((s + 2 : ℕ) : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h4
    have hcl1 : (Nat.clog 2 (s + 2) : ℝ) ≤ 2 * Real.logb 2 ((s + 2 : ℕ) : ℝ) := by
      have h := clog_lt_logb_add_one (s + 2) (by omega)
      linarith
    have hcl2 : (LL : ℝ) < Real.logb 2 (Nat.clog 2 (s + 2) : ℝ) + 1 :=
      clog_lt_logb_add_one (Nat.clog 2 (s + 2)) hL2
    have hlog_cl1 : Real.logb 2 (Nat.clog 2 (s + 2) : ℝ) ≤
        Real.logb 2 (2 * Real.logb 2 ((s + 2 : ℕ) : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0 < Nat.clog 2 (s + 2) by omega)) hcl1
    rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at hlog_cl1
    linarith
  have hprod_ge1 : (1 : ℝ) ≤ (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (Real.logb 2 s) ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num) hlog_ge1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa using this
    nlinarith
  have hmain : (C₁ : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ) ≤
      (6 * (C₁ : ℝ)) * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
    have hstep1 : (L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ) ≤
        (2 * (Real.logb 2 s) ^ (1 / 2 : ℝ)) * (3 * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) :=
      mul_le_mul hL_rpow hLL_le (by positivity) (by positivity)
    have hstep2 : (C₁ : ℝ) * ((L : ℝ) ^ (1 / 2 : ℝ) * (LL : ℝ)) ≤
        (C₁ : ℝ) * ((2 * (Real.logb 2 s) ^ (1 / 2 : ℝ)) *
          (3 * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hstep1 (by positivity)
    linarith
  have hcastC : ((6 * C₁ + 1 : ℕ) : ℝ) = 6 * (C₁ : ℝ) + 1 := by push_cast; rfl
  rw [hcastC]
  linarith

private theorem o26_threshold (C₁ N₀ : ℕ) (hC₁ : 4 ≤ C₁) (hN₀ : 3 ≤ N₀) :
    ∃ s₀ : ℕ, 4 ≤ s₀ ∧ ∀ s ≥ s₀,
      Real.logb 2 s < (o26M C₁ N₀ s : ℝ) ∧
      o26M C₁ N₀ s < s ∧
      2 ≤ o26M C₁ N₀ s ∧
      s * o26Mu C₁ N₀ s + 1 ≤ s ^ 2 ∧
      o26T C₁ s ≤ Nat.clog 2 s := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C_log : ℝ := 1 / ((1 / 4 : ℝ) * Real.log 2)
  have hC_log : 0 < C_log := by dsimp [C_log]; positivity
  let C_tot : ℝ := 4 * ((6 * C₁ + 1 : ℕ) : ℝ) * (2 * C_log)
  have hC_tot : 0 < C_tot := by dsimp [C_tot]; positivity
  obtain ⟨U₀, hU₀1, hU₀⟩ := exists_rpow_lt_self C_tot (3 / 4 : ℝ) hC_tot (by norm_num) (by norm_num)
  let s₀ : ℕ := max 4 (max (N₀ ^ 2 + 1) (Nat.ceil ((2 : ℝ) ^ U₀) + 1))
  refine ⟨s₀, le_max_left _ _, fun s hs => ?_⟩
  have hs4 : 4 ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : 2 ≤ s := by omega
  have hsN : N₀ ^ 2 < s := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right 4 _)) hs
    omega
  have hsU : (2 : ℝ) ^ U₀ < (s : ℝ) := by
    have h1 : Nat.ceil ((2 : ℝ) ^ U₀) + 1 ≤ s :=
      le_trans (le_trans (le_max_right _ _) (le_max_right 4 _)) hs
    have h2 : (2 : ℝ) ^ U₀ ≤ (Nat.ceil ((2 : ℝ) ^ U₀) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil ((2 : ℝ) ^ U₀) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h1
    linarith
  have hlog_geU : U₀ ≤ Real.logb 2 s := by
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (Real.rpow_pos_of_pos (by norm_num) _) hsU
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    exact hlog.le
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs2
  have h2t_lt_log : 2 * (o26T C₁ s : ℝ) < Real.logb 2 s := by
    have ht_le := o26T_le_bound C₁ s hC₁ hs2
    have hs2_le : ((s + 2 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
      have : s + 2 ≤ 2 * s := by omega
      exact_mod_cast this
    have hlogs2_le : Real.logb 2 ((s + 2 : ℕ) : ℝ) ≤ 2 * Real.logb 2 s := by
      have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hs2_le
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)] at h1
      linarith
    have hll_le : Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
        (2 * C_log) * (Real.logb 2 s) ^ (1 / 4 : ℝ) := by
      have h1 : Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
          Real.logb 2 (2 * Real.logb 2 s) :=
        Real.logb_le_logb_of_le (by norm_num) (by
          have := logb_two_ge_one (show 2 ≤ s + 2 by omega); linarith) hlogs2_le
      have h2 : Real.logb 2 (2 * Real.logb 2 s) ≤ C_log * (2 * Real.logb 2 s) ^ (1 / 4 : ℝ) :=
        logb_le_rpow_const (by norm_num) (by linarith)
      rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
      have h2r : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1)
        simpa using this
      calc
        Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))
            ≤ C_log * ((2 : ℝ) ^ (1 / 4 : ℝ) * (Real.logb 2 s) ^ (1 / 4 : ℝ)) := le_trans h1 h2
        _ ≤ C_log * (2 * (Real.logb 2 s) ^ (1 / 4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hC_log.le
            exact mul_le_mul_of_nonneg_right h2r (Real.rpow_nonneg (by linarith) _)
        _ = (2 * C_log) * (Real.logb 2 s) ^ (1 / 4 : ℝ) := by ring
    have hrpow_mul : (Real.logb 2 s) ^ (1 / 2 : ℝ) * (Real.logb 2 s) ^ (1 / 4 : ℝ) =
        (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have hbound : 2 * (o26T C₁ s : ℝ) ≤ C_tot * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
      calc
        2 * (o26T C₁ s : ℝ)
            ≤ 2 * (((6 * C₁ + 1 : ℕ) : ℝ) * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
                Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by linarith
        _ ≤ 2 * (((6 * C₁ + 1 : ℕ) : ℝ) * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
                ((2 * C_log) * (Real.logb 2 s) ^ (1 / 4 : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hll_le (by positivity)
        _ = (2 * ((6 * C₁ + 1 : ℕ) : ℝ) * (2 * C_log)) *
              ((Real.logb 2 s) ^ (1 / 2 : ℝ) * (Real.logb 2 s) ^ (1 / 4 : ℝ)) := by ring
        _ = (2 * ((6 * C₁ + 1 : ℕ) : ℝ) * (2 * C_log)) * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
            rw [hrpow_mul]
        _ ≤ C_tot * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
            dsimp only [C_tot]
            have : 0 ≤ ((6 * C₁ + 1 : ℕ) : ℝ) * (2 * C_log) * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
              positivity
            linarith
    exact lt_of_le_of_lt hbound (hU₀ (Real.logb 2 s) hlog_geU)
  have ht_le_L : o26T C₁ s ≤ Nat.clog 2 s := by
    have h1 : (o26T C₁ s : ℝ) < Real.logb 2 s := by linarith
    have h2 : Real.logb 2 s ≤ (Nat.clog 2 s : ℝ) := logb_two_le_clog s (by omega)
    exact_mod_cast le_of_lt (lt_of_lt_of_le h1 h2)
  have hm_lt_s : o26M C₁ N₀ s < s := by
    have hpow : 2 ^ (2 * o26T C₁ s) < s := by
      have hR : ((2 ^ (2 * o26T C₁ s) : ℕ) : ℝ) < (s : ℝ) := by
        calc
          ((2 ^ (2 * o26T C₁ s) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (o26T C₁ s : ℝ)) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
          _ < (2 : ℝ) ^ (Real.logb 2 (s : ℝ)) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2t_lt_log
          _ = (s : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      exact_mod_cast hR
    unfold o26M o26Mu
    rcases le_total N₀ (2 ^ o26T C₁ s) with hle | hle
    · rw [max_eq_right hle, ← pow_mul, mul_comm (o26T C₁ s) 2]
      exact hpow
    · rw [max_eq_left hle]
      exact hsN
  have hlog_lt_m : Real.logb 2 s < (o26M C₁ N₀ s : ℝ) := by
    have hspec := Nat.find_spec (o26T_exists C₁ s)
    have hL1 : 1 ≤ Nat.clog 2 s := Nat.clog_pos (by decide) (by omega)
    have hL2 : 2 ≤ Nat.clog 2 (s + 2) := by
      have h4 : 2 ^ 1 < s + 2 := by omega
      have hgt : 1 < Nat.clog 2 (s + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr h4
      omega
    have hLL_le_t : Nat.clog 2 (Nat.clog 2 (s + 2)) ≤ o26T C₁ s := by
      have hsq : (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 ≤ (o26T C₁ s) ^ 2 := by
        calc
          (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2
              = 1 * 1 * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 := by ring
          _ ≤ C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul (by nlinarith) hL1)
          _ ≤ (o26T C₁ s) ^ 2 := hspec.2
      nlinarith
    have hcl_lt : Nat.clog 2 s < 2 ^ (2 * o26T C₁ s) := by
      have h1 : Nat.clog 2 s ≤ Nat.clog 2 (s + 2) := Nat.clog_mono_right 2 (by omega)
      have h2 : Nat.clog 2 (s + 2) ≤ 2 ^ Nat.clog 2 (Nat.clog 2 (s + 2)) :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
      have h3 : 2 ^ Nat.clog 2 (Nat.clog 2 (s + 2)) ≤ 2 ^ o26T C₁ s :=
        Nat.pow_le_pow_right (by decide) hLL_le_t
      have h4 : 2 ^ o26T C₁ s < 2 ^ (2 * o26T C₁ s) := by
        have ht4 := o26T_ge_four C₁ s hC₁ hs2
        exact Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    have hpow_le_m : 2 ^ (2 * o26T C₁ s) ≤ o26M C₁ N₀ s := by
      unfold o26M o26Mu
      have h := le_max_right N₀ (2 ^ o26T C₁ s)
      calc
        2 ^ (2 * o26T C₁ s) = (2 ^ o26T C₁ s) ^ 2 := by rw [← pow_mul, mul_comm]
        _ ≤ (max N₀ (2 ^ o26T C₁ s)) ^ 2 := Nat.pow_le_pow_left h 2
    have hlog_le : Real.logb 2 s ≤ (Nat.clog 2 s : ℝ) := logb_two_le_clog s (by omega)
    have hlt_R : (Nat.clog 2 s : ℝ) < (o26M C₁ N₀ s : ℝ) := by exact_mod_cast lt_of_lt_of_le hcl_lt hpow_le_m
    exact lt_of_le_of_lt hlog_le hlt_R
  have hm2 : 2 ≤ o26M C₁ N₀ s := by
    have hgt1 : (1 : ℝ) < (o26M C₁ N₀ s : ℝ) := lt_of_le_of_lt hlog_ge1 hlog_lt_m
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hgt1)
  have hsmu : s * o26Mu C₁ N₀ s + 1 ≤ s ^ 2 := by
    have hmu_le_m : o26Mu C₁ N₀ s ≤ o26M C₁ N₀ s := by
      unfold o26M; simpa [sq] using Nat.le_mul_self (o26Mu C₁ N₀ s)
    have hmu_lt_s : o26Mu C₁ N₀ s < s := lt_of_le_of_lt hmu_le_m hm_lt_s
    nlinarith
  exact ⟨hlog_lt_m, hm_lt_s, hm2, hsmu, ht_le_L⟩

/-! ### Part 3: Evaluation-point bounds (`K''`, `K'''`, `K'''_C`) -/

private theorem o26_eval_bound_pow (C₁ N₀ s₀ d : ℕ) (hC₁ : 4 ≤ C₁) (hN₀ : 3 ≤ N₀) (hs₀ : 4 ≤ s₀)
    (hthr : ∀ s ≥ s₀,
      Real.logb 2 s < (o26M C₁ N₀ s : ℝ) ∧
      o26M C₁ N₀ s < s ∧
      2 ≤ o26M C₁ N₀ s ∧
      s * o26Mu C₁ N₀ s + 1 ≤ s ^ 2 ∧
      o26T C₁ s ≤ Nat.clog 2 s) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 2,
      (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ d) ≤
        expTwo (expTwo (K * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)))) := by
  let Msmall : ℝ := ((s₀ + 1 : ℝ) ^ s₀) * ((2 : ℝ) ^ (max N₀ (2 ^ o26T C₁ s₀))) * ((s₀ : ℝ) ^ d) + 2
  have hMsmall_ge2 : 2 ≤ Msmall := by
    dsimp [Msmall]
    have hnn : 0 ≤ ((s₀ + 1 : ℝ) ^ s₀) * ((2 : ℝ) ^ (max N₀ (2 ^ o26T C₁ s₀))) * ((s₀ : ℝ) ^ d) := by
      positivity
    linarith
  let Ksmall : ℝ := max 1 (Real.logb 2 (Real.logb 2 Msmall + 1) + 1)
  let Klarge : ℝ := 4 * ((6 * C₁ + 1 : ℕ) : ℝ) + Real.logb 2 (10 * ((N₀ : ℝ) ^ 4) + 2) + (d : ℝ) + 10
  let K : ℝ := max Ksmall Klarge
  have hKpos : 0 < K := by
    have : 1 ≤ Ksmall := le_max_left _ _
    have : Ksmall ≤ K := le_max_left _ _
    linarith
  refine ⟨K, hKpos, fun s hs => ?_⟩
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs
  have hll_ge1 : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := logb_logb_add_two_ge_one hs
  have hsqrt_ge1 : (1 : ℝ) ≤ (Real.logb 2 s) ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow (by norm_num) hlog_ge1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using this
  have hprod_ge1 : (1 : ℝ) ≤ (Real.logb 2 s) ^ (1 / 2 : ℝ) *
      Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by nlinarith
  by_cases hlt : s < s₀
  · have ht_mono : o26T C₁ s ≤ o26T C₁ s₀ := by
      have hspec := Nat.find_spec (o26T_exists C₁ s₀)
      apply Nat.find_min' (o26T_exists C₁ s)
      refine ⟨hspec.1, le_trans ?_ hspec.2⟩
      have hL := Nat.clog_mono_right 2 (le_of_lt hlt)
      have hLL := Nat.clog_mono_right 2 (Nat.clog_mono_right 2 (show s + 2 ≤ s₀ + 2 by omega))
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) (Nat.pow_le_pow_left hLL 2)
    have hmu_le : o26Mu C₁ N₀ s ≤ max N₀ (2 ^ o26T C₁ s₀) :=
      max_le_max_left N₀ (Nat.pow_le_pow_right (by decide) ht_mono)
    have hlhs_le : (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ d) ≤ Msmall := by
      dsimp only [o26EvalPointCount, Msmall]
      rw [if_pos hlt]
      have h1 : (((s + 1 : ℕ) ^ s : ℕ) : ℝ) ≤ ((s₀ + 1 : ℝ) ^ s₀) := by
        push_cast
        calc
          ((s : ℝ) + 1) ^ s ≤ ((s₀ : ℝ) + 1) ^ s := by
            apply pow_le_pow_left₀ (by positivity)
            exact_mod_cast (show s + 1 ≤ s₀ + 1 by omega)
          _ ≤ ((s₀ : ℝ) + 1) ^ s₀ := pow_le_pow_right₀ (by linarith) (le_of_lt hlt)
      have h2 : (2 : ℝ) ^ o26Mu C₁ N₀ s ≤ (2 : ℝ) ^ (max N₀ (2 ^ o26T C₁ s₀)) :=
        pow_le_pow_right₀ (by norm_num) hmu_le
      have h3 : (s : ℝ) ^ d ≤ (s₀ : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast le_of_lt hlt) d
      have hmul : (((s + 1 : ℕ) ^ s : ℕ) : ℝ) * (2 : ℝ) ^ o26Mu C₁ N₀ s * (s : ℝ) ^ d ≤
          ((s₀ + 1 : ℝ) ^ s₀) * (2 : ℝ) ^ (max N₀ (2 ^ o26T C₁ s₀)) * (s₀ : ℝ) ^ d :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
      linarith
    have hK_ge : Real.logb 2 (Real.logb 2 Msmall + 1) ≤
        K * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
      have hKs : Real.logb 2 (Real.logb 2 Msmall + 1) ≤ Ksmall := by
        have := le_max_right (1 : ℝ) (Real.logb 2 (Real.logb 2 Msmall + 1) + 1); linarith
      have hKK : Ksmall ≤ K := le_max_left _ _
      have hK1 : 1 ≤ K := le_trans (le_max_left _ _) hKK
      nlinarith
    have hexp1 : Real.logb 2 Msmall + 1 ≤ expTwo (K * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
        Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
      have hpos : 0 < Real.logb 2 Msmall + 1 := by
        have h1 : (1 : ℝ) ≤ Real.logb 2 Msmall := by
          rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hMsmall_ge2
        linarith
      calc
        Real.logb 2 Msmall + 1 = (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 Msmall + 1)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
        _ ≤ expTwo (K * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
              Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hK_ge
    calc
      (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ d)
          ≤ Msmall := hlhs_le
      _ = (2 : ℝ) ^ (Real.logb 2 Msmall) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ expTwo (expTwo (K * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
            Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have hge : s₀ ≤ s := le_of_not_gt hlt
    have hts := hthr s hge
    set μ := o26Mu C₁ N₀ s
    set m := o26M C₁ N₀ s
    have hdesign := lem_2_1_design_proved m s hs hts.1 (le_of_lt hts.2.1)
    have hdl : designL m < 2 * m ^ 2 := hdesign.1
    have hbase : (s * μ + 1 : ℕ) ≤ s ^ 2 := hts.2.2.2.1
    have hpts_le : (o26EvalPointCount C₁ N₀ s₀ s : ℝ) ≤
        (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s) := by
      dsimp only [o26EvalPointCount]
      rw [if_neg hlt]
      have h1 : ((s * μ + 1 : ℕ) : ℝ) ^ designL m ≤ ((s ^ 2 : ℕ) : ℝ) ^ (2 * m ^ 2) := by
        calc
          ((s * μ + 1 : ℕ) : ℝ) ^ designL m
              ≤ ((s ^ 2 : ℕ) : ℝ) ^ designL m :=
                pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _
          _ ≤ ((s ^ 2 : ℕ) : ℝ) ^ (2 * m ^ 2) :=
                pow_le_pow_right₀ (by
                  have : 1 ≤ s ^ 2 := by nlinarith
                  exact_mod_cast this) (le_of_lt hdl)
      have h2 : ((s ^ 2 : ℕ) : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s) := by
        have hs2eq : (s : ℝ) = (2 : ℝ) ^ (Real.logb 2 (s : ℝ)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        calc
          ((s ^ 2 : ℕ) : ℝ) ^ (2 * m ^ 2) = (s : ℝ) ^ (4 * m ^ 2) := by
            push_cast; rw [← pow_mul]; congr 1; ring
          _ = ((2 : ℝ) ^ (Real.logb 2 (s : ℝ))) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, ← hs2eq]
          _ = (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s) := by
            rw [← Real.rpow_mul (by norm_num)]
            congr 1; push_cast; ring
      exact_mod_cast le_trans h1 (le_of_eq h2)
    have hsd_eq : (s : ℝ) ^ d = (2 : ℝ) ^ ((d : ℝ) * Real.logb 2 s) := by
      have hs2eq : (s : ℝ) = (2 : ℝ) ^ (Real.logb 2 (s : ℝ)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      calc
        (s : ℝ) ^ d = ((2 : ℝ) ^ (Real.logb 2 (s : ℝ))) ^ (d : ℝ) := by
          rw [Real.rpow_natCast, ← hs2eq]
        _ = (2 : ℝ) ^ ((d : ℝ) * Real.logb 2 s) := by
          rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    have hprod_le : (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ μ) * ((s : ℝ) ^ d) ≤
        (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s + (μ : ℝ) + (d : ℝ) * Real.logb 2 s) := by
      have h2mu : ((2 : ℝ) ^ μ) = (2 : ℝ) ^ (μ : ℝ) := (Real.rpow_natCast 2 μ).symm
      calc
        (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ μ) * ((s : ℝ) ^ d)
            ≤ (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s) * (2 : ℝ) ^ (μ : ℝ) *
                (2 : ℝ) ^ ((d : ℝ) * Real.logb 2 s) := by
              rw [h2mu, hsd_eq]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpts_le (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ (4 * (m : ℝ) ^ 2 * Real.logb 2 s + (μ : ℝ) + (d : ℝ) * Real.logb 2 s) := by
              rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    have hm_le_prod : (m : ℝ) ≤ ((N₀ : ℝ) ^ 2) * (2 : ℝ) ^ (2 * (o26T C₁ s : ℝ)) := by
      have hμ_le : (μ : ℝ) ≤ (N₀ : ℝ) * (2 : ℝ) ^ (o26T C₁ s : ℝ) := by
        dsimp only [μ, o26Mu]
        have h1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (show 1 ≤ N₀ by omega)
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (o26T C₁ s : ℝ) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        rw [Nat.cast_max, max_le_iff]
        constructor
        · nlinarith
        · have : ((2 ^ o26T C₁ s : ℕ) : ℝ) = (2 : ℝ) ^ (o26T C₁ s : ℝ) := by
            rw [Real.rpow_natCast]; push_cast; rfl
          rw [this]; nlinarith
      have hm_eq : (m : ℝ) = (μ : ℝ) ^ 2 := by dsimp [m, o26M]; push_cast; rfl
      rw [hm_eq]
      calc
        (μ : ℝ) ^ 2 ≤ ((N₀ : ℝ) * (2 : ℝ) ^ (o26T C₁ s : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hμ_le 2
        _ = (N₀ : ℝ) ^ 2 * ((2 : ℝ) ^ (o26T C₁ s : ℝ)) ^ 2 := by ring
        _ = (N₀ : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (o26T C₁ s : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (o26T C₁ s : ℝ)), ← Real.rpow_mul (by norm_num)]
          congr 2; push_cast; ring
    have hm2_le : (m : ℝ) ^ 2 ≤ ((N₀ : ℝ) ^ 4) * (2 : ℝ) ^ (4 * (o26T C₁ s : ℝ)) := by
      calc
        (m : ℝ) ^ 2 ≤ ((N₀ : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (o26T C₁ s : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hm_le_prod 2
        _ = (N₀ : ℝ) ^ 4 * ((2 : ℝ) ^ (2 * (o26T C₁ s : ℝ))) ^ 2 := by ring
        _ = (N₀ : ℝ) ^ 4 * (2 : ℝ) ^ (4 * (o26T C₁ s : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 * (o26T C₁ s : ℝ))), ← Real.rpow_mul (by norm_num)]
          congr 2; push_cast; ring
    have hμ_le_m2 : (μ : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h1 : μ ≤ m := by dsimp [m, o26M]; simpa [sq] using Nat.le_mul_self μ
      have h2 : m ≤ m ^ 2 := by simpa [sq] using Nat.le_mul_self m
      exact_mod_cast le_trans h1 h2
    have hm2_ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : 1 ≤ m ^ 2 := by have := hts.2.2.1; nlinarith
      exact_mod_cast this
    have hexp_inner : 4 * (m : ℝ) ^ 2 * Real.logb 2 s + (μ : ℝ) + (d : ℝ) * Real.logb 2 s ≤
        expTwo (K * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
      have hA : 4 * (m : ℝ) ^ 2 * Real.logb 2 s + (μ : ℝ) + (d : ℝ) * Real.logb 2 s ≤
          (5 + (d : ℝ)) * (m : ℝ) ^ 2 * Real.logb 2 s := by
        have h1 : (μ : ℝ) ≤ (m : ℝ) ^ 2 * Real.logb 2 s := by nlinarith
        have h2 : (d : ℝ) * Real.logb 2 s ≤ (d : ℝ) * ((m : ℝ) ^ 2 * Real.logb 2 s) := by
          have : 0 ≤ (d : ℝ) * Real.logb 2 s := by positivity
          nlinarith
        linarith
      have hB : (5 + (d : ℝ)) * (m : ℝ) ^ 2 * Real.logb 2 s ≤
          ((5 + (d : ℝ)) * (N₀ : ℝ) ^ 4) * (2 : ℝ) ^ (4 * (o26T C₁ s : ℝ)) * Real.logb 2 s := by
        have h1 := mul_le_mul_of_nonneg_left hm2_le (show 0 ≤ 5 + (d : ℝ) by positivity)
        have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ Real.logb 2 s by linarith)
        linarith
      have hd_le_pow : 5 + (d : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) + 4) := by
        have hnat : d + 5 ≤ 2 ^ (d + 4) := by
          have h := Nat.lt_two_pow_self (n := d + 4)
          omega
        have hR : ((d + 5 : ℕ) : ℝ) ≤ ((2 ^ (d + 4) : ℕ) : ℝ) := by exact_mod_cast hnat
        rw [Nat.cast_pow, ← Real.rpow_natCast] at hR
        push_cast at hR ⊢
        linarith
      have hN4_le : (N₀ : ℝ) ^ 4 ≤ (2 : ℝ) ^ (Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2)) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
        have : (0 : ℝ) ≤ (N₀ : ℝ) ^ 4 := by positivity
        linarith
      have hlogs_le : Real.logb 2 s ≤ (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by
          have := logb_two_ge_one (show 2 ≤ s + 2 by omega); linarith)]
        exact Real.logb_le_logb_of_le (by norm_num) (by positivity)
          (by exact_mod_cast (show s ≤ s + 2 by omega))
      have hC : ((5 + (d : ℝ)) * (N₀ : ℝ) ^ 4) * (2 : ℝ) ^ (4 * (o26T C₁ s : ℝ)) * Real.logb 2 s ≤
          (2 : ℝ) ^ (((d : ℝ) + 4) + Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2) +
            4 * (o26T C₁ s : ℝ) + Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
        have h1 : (5 + (d : ℝ)) * (N₀ : ℝ) ^ 4 ≤
            (2 : ℝ) ^ ((d : ℝ) + 4) * (2 : ℝ) ^ (Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2)) :=
          mul_le_mul hd_le_pow hN4_le (by positivity) (by positivity)
        have h2 := mul_le_mul_of_nonneg_right h1
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (4 * (o26T C₁ s : ℝ)))
        have h3 := mul_le_mul h2 hlogs_le (by linarith) (by positivity)
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)] at h3
        exact h3
      have ht_le := o26T_le_bound C₁ s hC₁ hs
      have hexp_le : ((d : ℝ) + 4) + Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2) +
          4 * (o26T C₁ s : ℝ) + Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
          K * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
        have hKL : Klarge ≤ K := le_max_right _ _
        have hNlog_nn : 0 ≤ Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2) := by
          apply Real.logb_nonneg (by norm_num)
          have h0 : 0 ≤ (N₀ : ℝ) ^ 4 := by positivity
          linarith
        have hll_le_prod : Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
            (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) := by
          exact le_mul_of_one_le_left (by linarith) hsqrt_ge1
        have hconst_le : ((d : ℝ) + 4) + Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2) ≤
            (((d : ℝ) + 4) + Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2)) *
              ((Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) :=
          le_mul_of_one_le_right (by positivity) hprod_ge1
        have hKmul : Klarge * ((Real.logb 2 s) ^ (1 / 2 : ℝ) *
            Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) ≤
            K * ((Real.logb 2 s) ^ (1 / 2 : ℝ) *
            Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hKL (by linarith)
        have hKlarge_exp : Klarge * ((Real.logb 2 s) ^ (1 / 2 : ℝ) *
            Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) =
            4 * ((6 * C₁ + 1 : ℕ) : ℝ) * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
              Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) +
            (((d : ℝ) + 4) + Real.logb 2 (10 * (N₀ : ℝ) ^ 4 + 2)) *
              ((Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) +
            6 * ((Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
          dsimp only [Klarge]; ring
        have hK_assoc : K * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) =
            K * ((Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ))) := by
          ring
        linarith
      exact le_trans hA (le_trans hB (le_trans hC (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)))
    exact le_trans hprod_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_inner)

private theorem o26_poly_scale (K : ℝ) (hK : 0 < K) (A₀ D₀ : ℝ) (hA₀ : 1 ≤ A₀) (hD₀ : 1 ≤ D₀) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ (N s : ℕ), 2 ≤ N → 2 ≤ s →
      (s : ℝ) ≤ A₀ * (N : ℝ) ^ D₀ →
      K * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
        K' * (Real.logb 2 N) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 ((N + 2 : ℕ) : ℝ)) := by
  let C_s : ℝ := Real.logb 2 A₀ + D₀
  have hC_s : 1 ≤ C_s := by
    have : 0 ≤ Real.logb 2 A₀ := Real.logb_nonneg (by norm_num) hA₀
    dsimp [C_s]; linarith
  let C_ll : ℝ := max 0 (Real.logb 2 (Real.logb 2 (2 * A₀) + D₀)) + 1
  have hC_ll : 1 ≤ C_ll := by dsimp [C_ll]; linarith [le_max_left (0 : ℝ) (Real.logb 2 (Real.logb 2 (2 * A₀) + D₀))]
  let K' : ℝ := K * C_s ^ (1 / 2 : ℝ) * C_ll
  have hK' : 0 < K' := by
    have : 0 < C_s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [K']; positivity
  refine ⟨K', hK', fun N s hN hs hs_le => ?_⟩
  have hlogN1 : (1 : ℝ) ≤ Real.logb 2 N := logb_two_ge_one hN
  have hllN1 : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((N + 2 : ℕ) : ℝ)) := logb_logb_add_two_ge_one hN
  have hlogN2_ge1 : (1 : ℝ) ≤ Real.logb 2 ((N + 2 : ℕ) : ℝ) := logb_two_ge_one (by omega)
  have hlogs_le : Real.logb 2 s ≤ C_s * Real.logb 2 N := by
    have h1 : Real.logb 2 s ≤ Real.logb 2 (A₀ * (N : ℝ) ^ D₀) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hs_le
    rw [Real.logb_mul (by linarith) (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at h1
    have hA_nn : 0 ≤ Real.logb 2 A₀ := Real.logb_nonneg (by norm_num) hA₀
    dsimp only [C_s]
    nlinarith
  have hsqrt_le : (Real.logb 2 s) ^ (1 / 2 : ℝ) ≤ C_s ^ (1 / 2 : ℝ) * (Real.logb 2 N) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by linarith [logb_two_ge_one hs]) hlogs_le (by norm_num)
  have hll_le : Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
      C_ll * Real.logb 2 (Real.logb 2 ((N + 2 : ℕ) : ℝ)) := by
    have hs2_le : ((s + 2 : ℕ) : ℝ) ≤ (2 * A₀) * (((N + 2 : ℕ) : ℝ) ^ D₀) := by
      have h1 : ((s + 2 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
        have : s + 2 ≤ 2 * s := by omega
        exact_mod_cast this
      have h2 : (N : ℝ) ^ D₀ ≤ ((N + 2 : ℕ) : ℝ) ^ D₀ :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show N ≤ N + 2 by omega)) (by linarith)
      calc
        ((s + 2 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := h1
        _ ≤ 2 * (A₀ * (N : ℝ) ^ D₀) := by linarith
        _ = (2 * A₀) * (N : ℝ) ^ D₀ := by ring
        _ ≤ (2 * A₀) * ((N + 2 : ℕ) : ℝ) ^ D₀ := by
          apply mul_le_mul_of_nonneg_left h2 (by linarith)
    have hlogs2_le : Real.logb 2 ((s + 2 : ℕ) : ℝ) ≤
        (Real.logb 2 (2 * A₀) + D₀) * Real.logb 2 ((N + 2 : ℕ) : ℝ) := by
      have h1 : Real.logb 2 ((s + 2 : ℕ) : ℝ) ≤
          Real.logb 2 ((2 * A₀) * ((N + 2 : ℕ) : ℝ) ^ D₀) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hs2_le
      rw [Real.logb_mul (by linarith) (Real.rpow_pos_of_pos (by positivity) _).ne',
        Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at h1
      have h2A_nn : 0 ≤ Real.logb 2 (2 * A₀) := Real.logb_nonneg (by norm_num) (by linarith)
      nlinarith
    have hpos_fac : 0 < Real.logb 2 (2 * A₀) + D₀ := by
      have : 0 ≤ Real.logb 2 (2 * A₀) := Real.logb_nonneg (by norm_num) (by linarith)
      linarith
    have hll1 : Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)) ≤
        Real.logb 2 ((Real.logb 2 (2 * A₀) + D₀) * Real.logb 2 ((N + 2 : ℕ) : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by
        have := logb_two_ge_one (show 2 ≤ s + 2 by omega); linarith) hlogs2_le
    rw [Real.logb_mul hpos_fac.ne' (by linarith)] at hll1
    have hmax : Real.logb 2 (Real.logb 2 (2 * A₀) + D₀) ≤
        max 0 (Real.logb 2 (Real.logb 2 (2 * A₀) + D₀)) := le_max_right _ _
    have hmax_nn : 0 ≤ max 0 (Real.logb 2 (Real.logb 2 (2 * A₀) + D₀)) := le_max_left _ _
    dsimp only [C_ll]
    nlinarith
  have hmul := mul_le_mul hsqrt_le hll_le (by linarith [logb_logb_add_two_ge_one hs]) (by positivity)
  have hmulK := mul_le_mul_of_nonneg_left hmul hK.le
  dsimp only [K']
  linarith

/-! ### Part 4: Main Theorem — Remark 1 (`rem_1_tradeoff_proved`) -/

/-- Remark 1 core: conditional on `O26_Thm_1_1` (**UNREFEREED**) and `KI04_Cor_7_4`. -/
theorem rem_1_tradeoff_proved (hO26 : O26_Thm_1_1) (hKI : KI04_Cor_7_4) :
    ∃ (C₁ N₀ s₀ : ℕ) (K'' : ℝ), 4 ≤ C₁ ∧ 3 ≤ N₀ ∧ 4 ≤ s₀ ∧ 0 < K'' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (o26M C₁ N₀ s : ℝ) ∧
        o26M C₁ N₀ s < s ∧
        2 ≤ o26M C₁ N₀ s ∧
        s * o26Mu C₁ N₀ s + 1 ≤ s ^ 2) ∧
      (∀ (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s),
        C.encodingLength ≤ s →
        C.evalPoly.totalDegree ≤ s →
        CoeffBitBound C.evalPoly s →
        (s < s₀ → (pitSmallTest s C ↔ C.evalPoly = 0)) ∧
        (∀ (hge : s₀ ≤ s) (hm : 2 ≤ o26M C₁ N₀ s)
           (hcard : ∀ i : Fin s, (designSets (o26M C₁ N₀ s) s hm i).card = o26M C₁ N₀ s),
           o26LargeTest C₁ N₀ s hm hcard C ↔ C.evalPoly = 0)) ∧
      (∀ s ≥ 2,
        (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
          expTwo (expTwo (K'' * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (s + 2))))) ∧
      (∀ (C_0 d_poly : ℕ), 1 ≤ C_0 → 1 ≤ d_poly → ∃ K''' : ℝ, 0 < K''' ∧
        ∀ (N : ℕ), 2 ≤ N →
          let s := max N (C_0 * N ^ d_poly)
          ((N : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K''' * (Real.logb 2 N) ^ (1 / 2 : ℝ) *
                Real.logb 2 (Real.logb 2 (N + 2))))) ∧
      (∀ (C_0 d_poly : ℕ) (C : ℝ), 1 ≤ C_0 → 1 ≤ d_poly → 0 < C → ∃ K'''_C : ℝ, 0 < K'''_C ∧
        ∀ (n M : ℕ), 2 ≤ n → (M : ℝ) ≤ (n : ℝ) ^ C →
          let s := max n (C_0 * (n + M) ^ d_poly)
          ((n : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'''_C * (Real.logb 2 n) ^ (1 / 2 : ℝ) *
                Real.logb 2 (Real.logb 2 (n + 2))))) := by
  rcases hO26 with ⟨c, hc, N₀, hN₀, hO26_LB⟩
  obtain ⟨κ, hκ, hEngine⟩ := nwPermModTest_implies_computes_paperPerm hKI
  let C₁ : ℕ := max 4 (Nat.ceil ((κ : ℝ) / c) + 1)
  have hC₁ : 4 ≤ C₁ := le_max_left _ _
  have hcC₁_gt : (κ : ℝ) < c * (C₁ : ℝ) ^ 2 := by
    have h1 : (κ : ℝ) / c < (C₁ : ℝ) := by
      have hceil : (κ : ℝ) / c ≤ (Nat.ceil ((κ : ℝ) / c) : ℝ) := Nat.le_ceil _
      have hle : (Nat.ceil ((κ : ℝ) / c) : ℝ) + 1 ≤ (C₁ : ℝ) := by
        exact_mod_cast le_max_right 4 (Nat.ceil ((κ : ℝ) / c) + 1)
      linarith
    have h2 : (κ : ℝ) < c * (C₁ : ℝ) := by
      have := (div_lt_iff₀ hc).mp h1
      linarith
    have h3 : (C₁ : ℝ) ≤ (C₁ : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast (show 1 ≤ C₁ by omega)
      nlinarith
    nlinarith
  obtain ⟨s₀, hs₀, hthr⟩ := o26_threshold C₁ N₀ hC₁ hN₀
  obtain ⟨K'', hK'', hExp4⟩ := o26_eval_bound_pow C₁ N₀ s₀ 4 hC₁ hN₀ hs₀ hthr
  obtain ⟨K6, hK6, hExp6⟩ := o26_eval_bound_pow C₁ N₀ s₀ 6 hC₁ hN₀ hs₀ hthr
  refine ⟨C₁, N₀, s₀, K'', hC₁, hN₀, hs₀, hK'',
    fun s hs => ⟨(hthr s hs).1, (hthr s hs).2.1, (hthr s hs).2.2.1, (hthr s hs).2.2.2.1⟩,
    ?_, ?_, ?_, ?_⟩
  · -- Test correctness
    intro s hs C hC_len hdeg hcoeff
    constructor
    · intro _; exact step_thm1_small_inputs_proved s hs C hdeg hcoeff
    · intro hge hm hcard
      constructor
      · intro htest
        by_contra hnz
        set μ := o26Mu C₁ N₀ s
        have hμ_ge_N₀ : N₀ ≤ μ := le_max_left _ _
        have hμ3 : 3 ≤ μ := le_trans hN₀ hμ_ge_N₀
        have hμ1 : 1 ≤ μ := by omega
        have hts := hthr s hge
        have hcomp : Computes (paperPerm ℚ μ) (s ^ κ) :=
          hEngine μ s hs hμ1 hts.1 hts.2.1 hm hcard C hC_len hdeg hcoeff htest hnz
        have hcomp' : Computes (perm ℚ μ) (s ^ κ) := by rwa [← paperPerm_eq_perm_proved ℚ μ]
        have ho26 : O26ExactComputes (perm ℚ μ) (s ^ κ) := step_rem1_computes_to_o26_proved _ _ hcomp'
        have hlb : Real.exp (c * (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2) ≤ ((s ^ κ : ℕ) : ℝ) :=
          hO26_LB μ hμ_ge_N₀ (s ^ κ) ho26
        -- Show Real.exp (...) > (s : ℝ) ^ κ
        set t := o26T C₁ s
        have ht4 : 4 ≤ t := o26T_ge_four C₁ s hC₁ hs
        have ht_le_L : t ≤ Nat.clog 2 s := hts.2.2.2.2
        have hpow_le_μ : 2 ^ t ≤ μ := le_max_right _ _
        have ht_le_logμ : (t : ℝ) ≤ Real.logb 2 μ := by
          have h1 : ((2 ^ t : ℕ) : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hpow_le_μ
          have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h1
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
          exact hlog
        have hmono : (t : ℝ) / Real.logb 2 t ≤ Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ) :=
          div_logb_mono (by exact_mod_cast ht4) ht_le_logμ
        have hlogt_pos : 0 < Real.logb 2 t := by
          have := logb_two_ge_one (show 2 ≤ t by omega); linarith
        have hlogt_le_LL : Real.logb 2 t ≤ (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) := by
          have h1 : Real.logb 2 t ≤ Real.logb 2 (Nat.clog 2 (s + 2) : ℝ) :=
            Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0 < t by omega))
              (by exact_mod_cast le_trans ht_le_L (Nat.clog_mono_right 2 (by omega)))
          have h2 : Real.logb 2 (Nat.clog 2 (s + 2) : ℝ) ≤ (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) :=
            logb_two_le_clog (Nat.clog 2 (s + 2)) (Nat.clog_pos (by decide) (by omega))
          exact le_trans h1 h2
        have hLL_pos : (0 : ℝ) < (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) := by
          have hL2 : 2 ≤ Nat.clog 2 (s + 2) := by
            have hgt : 1 < Nat.clog 2 (s + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
            omega
          exact_mod_cast Nat.clog_pos (by decide) (by omega : 1 < Nat.clog 2 (s + 2))
        have hspec := Nat.find_spec (o26T_exists C₁ s)
        have hratio_sq : (C₁ : ℝ) ^ 2 * Real.logb 2 s ≤
            (Real.logb 2 μ) ^ 2 / (Real.logb 2 (Real.logb 2 μ)) ^ 2 := by
          have h1 : (t : ℝ) / (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) ≤ (t : ℝ) / Real.logb 2 t :=
            div_le_div_of_nonneg_left (by positivity) hlogt_pos hlogt_le_LL
          have h2 : (t : ℝ) / (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) ≤
              Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ) := le_trans h1 hmono
          have hsq : ((t : ℝ) / (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ)) ^ 2 ≤
              (Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h2 2
          rw [div_pow, div_pow] at hsq
          have hnum : (C₁ : ℝ) ^ 2 * Real.logb 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) ^ 2 ≤
              (t : ℝ) ^ 2 := by
            have hL_ge : Real.logb 2 s ≤ (Nat.clog 2 s : ℝ) := logb_two_le_clog s (by omega)
            have hsp : ((C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 : ℕ) : ℝ) ≤
                ((t ^ 2 : ℕ) : ℝ) := by exact_mod_cast hspec.2
            push_cast at hsp
            have hmul := mul_le_mul_of_nonneg_left hL_ge (show 0 ≤ (C₁ : ℝ) ^ 2 by positivity)
            have hmul2 := mul_le_mul_of_nonneg_right hmul (show 0 ≤ (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) ^ 2 by positivity)
            exact le_trans hmul2 hsp
          have hdiv : (C₁ : ℝ) ^ 2 * Real.logb 2 s ≤
              (t : ℝ) ^ 2 / (Nat.clog 2 (Nat.clog 2 (s + 2)) : ℝ) ^ 2 :=
            (le_div_iff₀ (pow_pos hLL_pos 2)).mpr hnum
          exact le_trans hdiv hsq
        have hln_gt : (Real.logb 2 μ) ^ 2 / (Real.logb 2 (Real.logb 2 μ)) ^ 2 <
            (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2 := step_rem1_ln_vs_log2_proved μ hμ3
        have hexp_gt : (κ : ℝ) * Real.log s < c * (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2 := by
          have hlog2_lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
          have hlogs_lt : Real.log s < Real.logb 2 s := by
            have hlog_pos : 0 < Real.log s := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            rw [Real.logb, lt_div_iff₀ hlog2_pos]
            nlinarith
          have h1 : (κ : ℝ) * Real.log s < (κ : ℝ) * Real.logb 2 s :=
            mul_lt_mul_of_pos_left hlogs_lt (by exact_mod_cast hκ)
          have h2 : (κ : ℝ) * Real.logb 2 s < c * (C₁ : ℝ) ^ 2 * Real.logb 2 s :=
            mul_lt_mul_of_pos_right hcC₁_gt (by linarith [logb_two_ge_one hs])
          have h3 : c * (C₁ : ℝ) ^ 2 * Real.logb 2 s <
              c * ((Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2) := by
            have := mul_lt_mul_of_pos_left (lt_of_le_of_lt hratio_sq hln_gt) hc
            linarith
          rw [← mul_div_assoc] at h3
          linarith
        have hsk_lt : ((s ^ κ : ℕ) : ℝ) <
            Real.exp (c * (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2) := by
          have hs_eq : ((s ^ κ : ℕ) : ℝ) = Real.exp ((κ : ℝ) * Real.log s) := by
            rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
            congr 1; ring
          rw [hs_eq]
          exact Real.exp_lt_exp.mpr hexp_gt
        linarith
      · intro h0 a
        rw [intCircuit_evalAt_eq_aeval, h0, map_zero]
  · -- K'' bound (note: `(s : ℝ) + 2 = ((s + 2 : ℕ) : ℝ)`)
    intro s hs
    have h := hExp4 s hs
    simpa [Nat.cast_add, Nat.cast_ofNat] using h
  · -- K''' bound for `s = max N (C_0 * N ^ d_poly)`
    intro C_0 d_poly hC_0 hd_poly
    obtain ⟨K''', hK''', hscale⟩ := o26_poly_scale K6 hK6 (C_0 : ℝ) (d_poly : ℝ)
      (by exact_mod_cast hC_0) (by exact_mod_cast hd_poly)
    refine ⟨K''', hK''', fun N hN => ?_⟩
    dsimp only
    set s := max N (C_0 * N ^ d_poly)
    have hN_le_s : N ≤ s := le_max_left _ _
    have hs2 : 2 ≤ s := le_trans hN hN_le_s
    have hs_le : (s : ℝ) ≤ (C_0 : ℝ) * (N : ℝ) ^ (d_poly : ℝ) := by
      have hN_le_pow : N ≤ C_0 * N ^ d_poly := by
        have h1 : N ^ 1 ≤ N ^ d_poly := Nat.pow_le_pow_right (by omega) hd_poly
        rw [pow_one] at h1
        have h2 : 1 * N ≤ C_0 * N ^ d_poly := Nat.mul_le_mul hC_0 h1
        simpa using h2
      have hseq : s = C_0 * N ^ d_poly := max_eq_right hN_le_pow
      rw [hseq, Nat.cast_mul, Nat.cast_pow, Real.rpow_natCast]
    have hN2_le : ((N : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
        ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
        (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 6) := by
      have h1 : (N : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN_le_s) 2
      have h2 : ((N : ℝ) ^ 2) * ((s : ℝ) ^ 4) ≤ (s : ℝ) ^ 6 := by
        calc
          (N : ℝ) ^ 2 * (s : ℝ) ^ 4 ≤ (s : ℝ) ^ 2 * (s : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (s : ℝ) ^ 6 := by ring
      have h3 := mul_le_mul_of_nonneg_left h2
        (show 0 ≤ (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * (2 : ℝ) ^ o26Mu C₁ N₀ s by positivity)
      linarith
    have h6 := hExp6 s hs2
    have hsc := hscale N s hN hs2 hs_le
    have houter : expTwo (expTwo (K6 * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)))) ≤
        expTwo (expTwo (K''' * (Real.logb 2 N) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((N + 2 : ℕ) : ℝ)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsc)
    have hfin := le_trans hN2_le (le_trans h6 houter)
    simpa [Nat.cast_add, Nat.cast_ofNat] using hfin
  · -- K'''_C bound for `s = max n (C_0 * (n + M) ^ d_poly)` with `M ≤ n ^ C`
    intro C_0 d_poly C hC_0 hd_poly hC
    let Cmax : ℝ := max 1 C
    let A₀ : ℝ := (C_0 : ℝ) * (2 : ℝ) ^ d_poly
    let D₀ : ℝ := (d_poly : ℝ) * Cmax
    have hA₀ : 1 ≤ A₀ := by
      have h1 : (1 : ℝ) ≤ (C_0 : ℝ) := by exact_mod_cast hC_0
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ d_poly := one_le_pow₀ (by norm_num)
      dsimp [A₀]; nlinarith
    have hD₀ : 1 ≤ D₀ := by
      have h1 : (1 : ℝ) ≤ (d_poly : ℝ) := by exact_mod_cast hd_poly
      have h2 : (1 : ℝ) ≤ Cmax := le_max_left _ _
      dsimp [D₀]; nlinarith
    obtain ⟨K'''_C, hK'''_C, hscale⟩ := o26_poly_scale K6 hK6 A₀ D₀ hA₀ hD₀
    refine ⟨K'''_C, hK'''_C, fun n M hn hMC => ?_⟩
    dsimp only
    set s := max n (C_0 * (n + M) ^ d_poly)
    have hn_le_s : n ≤ s := le_max_left _ _
    have hs2 : 2 ≤ s := le_trans hn hn_le_s
    have hs_le : (s : ℝ) ≤ A₀ * (n : ℝ) ^ D₀ := by
      have hn_le_pow : n ≤ C_0 * (n + M) ^ d_poly := by
        have h1 : n ≤ (n + M) ^ 1 := by rw [pow_one]; omega
        have h2 : (n + M) ^ 1 ≤ (n + M) ^ d_poly := Nat.pow_le_pow_right (by omega) hd_poly
        have h3 : 1 * n ≤ C_0 * (n + M) ^ d_poly := Nat.mul_le_mul hC_0 (le_trans h1 h2)
        simpa using h3
      have hseq : s = C_0 * (n + M) ^ d_poly := max_eq_right hn_le_pow
      rw [hseq, Nat.cast_mul, Nat.cast_pow, Nat.cast_add]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hn_le_Cmax : (n : ℝ) ≤ (n : ℝ) ^ Cmax := by
        have := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left 1 C)
        simpa using this
      have hM_le_Cmax : (M : ℝ) ≤ (n : ℝ) ^ Cmax :=
        le_trans hMC (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right 1 C))
      have hsum_le : (n : ℝ) + (M : ℝ) ≤ 2 * (n : ℝ) ^ Cmax := by linarith
      calc
        (C_0 : ℝ) * ((n : ℝ) + (M : ℝ)) ^ d_poly
            ≤ (C_0 : ℝ) * (2 * (n : ℝ) ^ Cmax) ^ d_poly :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum_le _) (by positivity)
        _ = (C_0 : ℝ) * (2 : ℝ) ^ d_poly * ((n : ℝ) ^ Cmax) ^ d_poly := by rw [mul_pow]; ring
        _ = A₀ * (n : ℝ) ^ D₀ := by
            dsimp only [A₀, D₀]
            rw [← Real.rpow_natCast ((n : ℝ) ^ Cmax), ← Real.rpow_mul (by positivity)]
            congr 2; ring
    have hn2_le : ((n : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
        ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
        (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 6) := by
      have h1 : (n : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn_le_s) 2
      have h2 : ((n : ℝ) ^ 2) * ((s : ℝ) ^ 4) ≤ (s : ℝ) ^ 6 := by
        calc
          (n : ℝ) ^ 2 * (s : ℝ) ^ 4 ≤ (s : ℝ) ^ 2 * (s : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (s : ℝ) ^ 6 := by ring
      have h3 := mul_le_mul_of_nonneg_left h2
        (show 0 ≤ (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * (2 : ℝ) ^ o26Mu C₁ N₀ s by positivity)
      linarith
    have h6 := hExp6 s hs2
    have hsc := hscale n s hn hs2 hs_le
    have houter : expTwo (expTwo (K6 * (Real.logb 2 s) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((s + 2 : ℕ) : ℝ)))) ≤
        expTwo (expTwo (K'''_C * (Real.logb 2 n) ^ (1 / 2 : ℝ) *
          Real.logb 2 (Real.logb 2 ((n + 2 : ℕ) : ℝ)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsc)
    have hfin := le_trans hn2_le (le_trans h6 houter)
    simpa [Nat.cast_add, Nat.cast_ofNat] using hfin

end ExactMatching.Proofs
