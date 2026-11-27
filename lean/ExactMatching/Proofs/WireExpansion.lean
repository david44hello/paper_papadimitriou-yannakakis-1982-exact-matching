/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.PfaffianMatching
import ExactMatching.Proofs.PfaffianIdentity
import ExactMatching.Proofs.PitBounds

/-!
# Proof of Proposition 3.1 (Group-ring wire-expansion theorem)

Proves `prop_3_1_wire_expansion_proved` via a uniform `B = 2 * |Γ|²`-slot-per-gate layout:
gate `0` is `const 0`; each gate `idx` occupies `[1 + idx * B, 1 + (idx + 1) * B)` with
- offsets `0 .. g² - 1`: product slots `prodSlot g idx a b = 1 + idx * B + a * g + b`,
- offsets `g² .. 2 g² - 1`: partial-sum slots `sumSlot g idx c t = 1 + idx * B + g² + c * g + t`,
- output wires at `wireIdx g idx c = sumSlot g idx c (g - 1)`.
Works uniformly for every `g = |Γ| ≥ 1` with zero case splits on `g`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

private theorem aeval_universalPfaffian {k : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (2 * k)) (Fin (2 * k)) R) :
    MvPolynomial.aeval (fun p : UpperPair (2 * k) => M p.val.1 p.val.2) (universalPfaffian k) =
      pfaffian M := by
  unfold universalPfaffian pfaffian
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPolynomial.aeval_C, map_prod]
  simp

private def prodSlot (g idx a b : ℕ) : ℕ :=
  1 + idx * (2 * g ^ 2) + (a * g + b)

private def sumSlot (g idx c t : ℕ) : ℕ :=
  1 + idx * (2 * g ^ 2) + g ^ 2 + (c * g + t)

private def wireIdx (g idx c : ℕ) : ℕ :=
  sumSlot g idx c (g - 1)

private noncomputable def expandBlockGate {k : ℕ}
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ)
    (eΓ : Γ ≃ Fin (Fintype.card Γ))
    (eEdge : UpperEdge G ≃ Fin (Fintype.card (UpperEdge G)))
    (ePair : UpperPair (2 * k) ≃ Fin (Fintype.card (UpperPair (2 * k))))
    (idx off : ℕ) (gt : IntGate (Fintype.card (UpperPair (2 * k)))) :
    IntGate (Fintype.card (UpperEdge G)) :=
  let g := Fintype.card Γ
  match gt with
  | .var v =>
    if _ : g ^ 2 ≤ off ∧ (off - g ^ 2) % g = g - 1 then
      let c := (off - g ^ 2) / g
      if hc : c < g then
        let p := ePair.symm v
        if hadj : G.Adj p.val.1 p.val.2 then
          let ed : UpperEdge G := ⟨p, hadj⟩
          if eΓ (w ed) = ⟨c, hc⟩ then .var (eEdge ed) else .const 0
        else .const 0
      else .const 0
    else .const 0
  | .const a =>
    if _ : g ^ 2 ≤ off ∧ (off - g ^ 2) % g = g - 1 then
      let c := (off - g ^ 2) / g
      if hc : c < g then
        if eΓ (0 : Γ) = ⟨c, hc⟩ then .const a else .const 0
      else .const 0
    else .const 0
  | .add i j =>
    if _ : g ^ 2 ≤ off ∧ (off - g ^ 2) % g = g - 1 then
      .add (wireIdx g i ((off - g ^ 2) / g)) (wireIdx g j ((off - g ^ 2) / g))
    else .const 0
  | .sub i j =>
    if _ : g ^ 2 ≤ off ∧ (off - g ^ 2) % g = g - 1 then
      .sub (wireIdx g i ((off - g ^ 2) / g)) (wireIdx g j ((off - g ^ 2) / g))
    else .const 0
  | .mul i j =>
    if _ : off < g ^ 2 then
      .mul (wireIdx g i (off / g)) (wireIdx g j (off % g))
    else
      let rel := off - g ^ 2
      let c := rel / g
      let t := rel % g
      if hc : c < g then
        if ht : t < g then
          let b := (eΓ (eΓ.symm ⟨c, hc⟩ - eΓ.symm ⟨t, ht⟩)).val
          if t = 0 then .add (prodSlot g idx 0 b) 0
          else .add (sumSlot g idx c (t - 1)) (prodSlot g idx t b)
        else .const 0
      else .const 0

private theorem expandBlockGate_wf {k : ℕ}
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ)
    (eΓ : Γ ≃ Fin (Fintype.card Γ))
    (eEdge : UpperEdge G ≃ Fin (Fintype.card (UpperEdge G)))
    (ePair : UpperPair (2 * k) ≃ Fin (Fintype.card (UpperPair (2 * k))))
    (idx off : ℕ) (hoff : off < 2 * (Fintype.card Γ) ^ 2)
    (gt : IntGate (Fintype.card (UpperPair (2 * k)))) (hwf : gt.WF idx) :
    (expandBlockGate G w eΓ eEdge ePair idx off gt).WF
      (1 + idx * (2 * (Fintype.card Γ) ^ 2) + off) := by
  let g := Fintype.card Γ
  have hg : 1 ≤ g := Fintype.card_pos
  have hwire_lt_block : ∀ i c : ℕ, i < idx → c < g →
      wireIdx g i c < 1 + idx * (2 * g ^ 2) + off := by
    intro i c hi hc
    dsimp only [wireIdx, sumSlot]
    have h1 : (i + 1) * (2 * g ^ 2) ≤ idx * (2 * g ^ 2) := Nat.mul_le_mul_right _ hi
    have h2 : c * g + (g - 1) < g ^ 2 := by
      have h3 : (c + 1) * g ≤ g * g := Nat.mul_le_mul_right g hc
      have h4 : g - 1 < g := by omega
      nlinarith
    nlinarith
  cases gt with
  | var v => unfold expandBlockGate; dsimp only; split_ifs <;> trivial
  | const a => unfold expandBlockGate; dsimp only; split_ifs <;> trivial
  | add i j =>
    unfold expandBlockGate; dsimp only
    split_ifs with h
    · have hc : (off - g ^ 2) / g < g := by
        have hsub : off - g ^ 2 < g * g := by dsimp only [g] at *; rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      exact ⟨hwire_lt_block i _ hwf.1 hc, hwire_lt_block j _ hwf.2 hc⟩
    · trivial
  | sub i j =>
    unfold expandBlockGate; dsimp only
    split_ifs with h
    · have hc : (off - g ^ 2) / g < g := by
        have hsub : off - g ^ 2 < g * g := by dsimp only [g] at *; rw [← sq]; omega
        exact Nat.div_lt_of_lt_mul hsub
      exact ⟨hwire_lt_block i _ hwf.1 hc, hwire_lt_block j _ hwf.2 hc⟩
    · trivial
  | mul i j =>
    unfold expandBlockGate; dsimp only
    split_ifs with hp hc ht ht0
    · have ha : off / g < g := Nat.div_lt_of_lt_mul (by dsimp only [g] at *; simpa [sq] using hp)
      have hb : off % g < g := Nat.mod_lt _ hg
      exact ⟨hwire_lt_block i _ hwf.1 ha, hwire_lt_block j _ hwf.2 hb⟩
    · dsimp only [IntGate.WF, prodSlot]
      dsimp only [g] at hg hp hc ht ht0 ⊢
      have hblt :
          (eΓ (eΓ.symm ⟨(off - Fintype.card Γ ^ 2) / Fintype.card Γ, hc⟩ -
            eΓ.symm ⟨(off - Fintype.card Γ ^ 2) % Fintype.card Γ, ht⟩)).val < Fintype.card Γ :=
        Fin.isLt _
      have hlt :
          0 * Fintype.card Γ +
            (eΓ (eΓ.symm ⟨(off - Fintype.card Γ ^ 2) / Fintype.card Γ, hc⟩ -
              eΓ.symm ⟨(off - Fintype.card Γ ^ 2) % Fintype.card Γ, ht⟩)).val < Fintype.card Γ ^ 2 := by
        nlinarith
      exact ⟨by omega, by omega⟩
    · dsimp only [IntGate.WF, sumSlot, prodSlot]
      dsimp only [g] at hg hp hc ht ht0 ⊢
      have hdiv :
          ((off - Fintype.card Γ ^ 2) / Fintype.card Γ) * Fintype.card Γ +
            (off - Fintype.card Γ ^ 2) % Fintype.card Γ = off - Fintype.card Γ ^ 2 := by
        have h1 := Nat.div_add_mod (off - Fintype.card Γ ^ 2) (Fintype.card Γ)
        rw [Nat.mul_comm] at h1
        exact h1
      have hblt :
          (eΓ (eΓ.symm ⟨(off - Fintype.card Γ ^ 2) / Fintype.card Γ, hc⟩ -
            eΓ.symm ⟨(off - Fintype.card Γ ^ 2) % Fintype.card Γ, ht⟩)).val < Fintype.card Γ :=
        Fin.isLt _
      have hprod :
          ((off - Fintype.card Γ ^ 2) % Fintype.card Γ) * Fintype.card Γ +
            (eΓ (eΓ.symm ⟨(off - Fintype.card Γ ^ 2) / Fintype.card Γ, hc⟩ -
              eΓ.symm ⟨(off - Fintype.card Γ ^ 2) % Fintype.card Γ, ht⟩)).val < Fintype.card Γ ^ 2 := by
        have h1 : ((off - Fintype.card Γ ^ 2) % Fintype.card Γ + 1) * Fintype.card Γ ≤
            Fintype.card Γ * Fintype.card Γ := Nat.mul_le_mul_right (Fintype.card Γ) ht
        nlinarith
      exact ⟨by omega, by omega⟩
    · trivial
    · trivial

private theorem expandBlockGate_unit {k : ℕ}
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ)
    (eΓ : Γ ≃ Fin (Fintype.card Γ))
    (eEdge : UpperEdge G ≃ Fin (Fintype.card (UpperEdge G)))
    (ePair : UpperPair (2 * k) ≃ Fin (Fintype.card (UpperPair (2 * k))))
    (idx off : ℕ) (gt : IntGate (Fintype.card (UpperPair (2 * k))))
    (hgt : ∀ a : ℤ, gt = .const a → a = 0 ∨ a = 1 ∨ a = -1)
    (a : ℤ) (heq : expandBlockGate G w eΓ eEdge ePair idx off gt = .const a) :
    a = 0 ∨ a = 1 ∨ a = -1 := by
  cases gt with
  | var v =>
    unfold expandBlockGate at heq; dsimp only at heq
    split_ifs at heq <;> cases heq <;> exact Or.inl rfl
  | const a' =>
    unfold expandBlockGate at heq; dsimp only at heq
    split_ifs at heq
    · cases heq; exact hgt _ rfl
    · cases heq; exact Or.inl rfl
    · cases heq; exact Or.inl rfl
    · cases heq; exact Or.inl rfl
  | add i j =>
    unfold expandBlockGate at heq; dsimp only at heq
    split_ifs at heq <;> cases heq <;> exact Or.inl rfl
  | sub i j =>
    unfold expandBlockGate at heq; dsimp only at heq
    split_ifs at heq <;> cases heq <;> exact Or.inl rfl
  | mul i j =>
    unfold expandBlockGate at heq; dsimp only at heq
    split_ifs at heq <;> cases heq <;> exact Or.inl rfl

/-- Proposition 3.1 (wire-expansion theorem). -/
theorem prop_3_1_wire_expansion_proved {k : ℕ} (hk : 1 ≤ k)
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (γstar : Γ)
    (C_pf : IntCircuit (Fintype.card (UpperPair (2 * k))))
    (hunit : C_pf.UsesOnlyUnitConstants)
    (hpf : C_pf.evalPoly = MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k)) :
    let M := 2 * (Fintype.card Γ) ^ 2 * C_pf.size + Fintype.card Γ
    ∃ C_out : IntCircuit (Fintype.card (UpperEdge G)),
      C_out.UsesOnlyUnitConstants ∧
      C_out.size ≤ M ∧
      C_out.encodingLength ≤ M * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) ∧
      C_out.evalPoly = MvPolynomial.rename (Fintype.equivFin (UpperEdge G)) (groupRingPoly G w γstar) := by
  dsimp only
  set g := Fintype.card Γ with hg_def
  have hg : 1 ≤ g := Fintype.card_pos
  set B := 2 * g ^ 2
  have hBpos : 0 < B := by dsimp [B]; nlinarith
  set N_out := 1 + B * C_pf.size
  set M := 2 * g ^ 2 * C_pf.size + g
  have hN_le_M : N_out ≤ M := by dsimp [N_out, B, M]; omega
  let eΓ : Γ ≃ Fin g := Fintype.equivFin Γ
  let eEdge : UpperEdge G ≃ Fin (Fintype.card (UpperEdge G)) := Fintype.equivFin (UpperEdge G)
  let ePair : UpperPair (2 * k) ≃ Fin (Fintype.card (UpperPair (2 * k))) := upperPairEquiv (2 * k)
  let gateFn : Fin N_out → IntGate (Fintype.card (UpperEdge G)) := fun slot =>
    if _h0 : slot.val = 0 then .const 0
    else
      let idx := (slot.val - 1) / B
      let off := (slot.val - 1) % B
      if hidx : idx < C_pf.size then
        expandBlockGate G w eΓ eEdge ePair idx off (C_pf.gate ⟨idx, hidx⟩)
      else .const 0
  have hwf : ∀ slot : Fin N_out, (gateFn slot).WF slot.val := by
    intro slot
    dsimp only [gateFn]
    split_ifs with h0 hidx
    · trivial
    · have hslot_eq :
          1 + ((slot.val - 1) / B) * (2 * (Fintype.card Γ) ^ 2) + (slot.val - 1) % B = slot.val := by
        have h1 := Nat.div_add_mod (slot.val - 1) B
        rw [Nat.mul_comm] at h1
        change 1 + ((slot.val - 1) / B) * B + (slot.val - 1) % B = slot.val
        omega
      have hwf' := expandBlockGate_wf G w eΓ eEdge ePair ((slot.val - 1) / B) ((slot.val - 1) % B)
        (Nat.mod_lt _ hBpos) (C_pf.gate ⟨_, hidx⟩) (C_pf.wf ⟨_, hidx⟩)
      rwa [hslot_eq] at hwf'
    · trivial
  have hsum_lt : ∀ (idx : ℕ), idx < C_pf.size → ∀ c t : ℕ, c < g → t < g →
      sumSlot g idx c t < N_out := by
    intro idx hidx c t hc ht
    dsimp only [sumSlot, N_out, B]
    have h1 : (idx + 1) * (2 * g ^ 2) ≤ C_pf.size * (2 * g ^ 2) := Nat.mul_le_mul_right _ hidx
    have h2 : (c + 1) * g ≤ g * g := Nat.mul_le_mul_right g hc
    nlinarith
  have hprod_lt : ∀ (idx : ℕ), idx < C_pf.size → ∀ a b : ℕ, a < g → b < g →
      prodSlot g idx a b < N_out := by
    intro idx hidx a b ha hb
    dsimp only [prodSlot, N_out, B]
    have h1 : (idx + 1) * (2 * g ^ 2) ≤ C_pf.size * (2 * g ^ 2) := Nat.mul_le_mul_right _ hidx
    have h2 : (a + 1) * g ≤ g * g := Nat.mul_le_mul_right g ha
    nlinarith
  have hwire_lt : ∀ (idx : ℕ), idx < C_pf.size → ∀ γ : Γ, wireIdx g idx (eΓ γ).val < N_out :=
    fun idx hidx γ => hsum_lt idx hidx (eΓ γ).val (g - 1) (Fin.isLt _) (by omega)
  let C_out : IntCircuit (Fintype.card (UpperEdge G)) :=
    { size := N_out
      size_pos := by dsimp [N_out]; omega
      gate := gateFn
      wf := hwf
      out := ⟨wireIdx g C_pf.out.val (eΓ γstar).val, hwire_lt C_pf.out.val C_pf.out.isLt γstar⟩ }
  have hC_unit : C_out.UsesOnlyUnitConstants := by
    intro slot a hga
    dsimp only [C_out, gateFn] at hga
    split_ifs at hga with h0 hidx
    · cases hga; exact Or.inl rfl
    · exact expandBlockGate_unit G w eΓ eEdge ePair _ _ _ (hunit ⟨_, hidx⟩) a hga
    · cases hga; exact Or.inl rfl
  have hC_enc : C_out.encodingLength ≤ M * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) := by
    unfold IntCircuit.encodingLength
    have hUpper_le : Fintype.card (UpperEdge G) ≤ (2 * k) ^ 2 := by
      have hinj : Function.Injective (fun e : UpperEdge G => e.val.val) :=
        fun a b h => Subtype.ext (Subtype.ext h)
      have hle := Fintype.card_le_of_injective _ hinj
      simpa [Fintype.card_prod, Fintype.card_fin, sq] using hle
    have hgate_cost : ∀ slot : Fin C_out.size,
        (C_out.gate slot).bitCost ≤ 2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4 := by
      intro slot
      have hslot_wf := C_out.wf slot
      have hslot_lt : slot.val < M := Nat.lt_of_lt_of_le slot.isLt hN_le_M
      cases hg_eq : C_out.gate slot with
      | var v =>
        simp only [IntGate.bitCost]
        have hclog := Nat.clog_mono_right 2 (show v.val + 2 ≤ M + (2 * k) ^ 2 + 2 by have := v.isLt; omega)
        omega
      | const a =>
        simp only [IntGate.bitCost, intBitLen]
        rcases hC_unit slot a hg_eq with rfl | rfl | rfl
        · have h0 : Nat.clog 2 (Int.natAbs (0 : ℤ) + 1) = 0 := by decide
          omega
        · have h1 : Nat.clog 2 (Int.natAbs (1 : ℤ) + 1) = 1 := by decide
          omega
        · have h2 : Nat.clog 2 (Int.natAbs (-1 : ℤ) + 1) = 1 := by decide
          omega
      | add i j =>
        rw [hg_eq] at hslot_wf; simp only [IntGate.bitCost]
        have hci := Nat.clog_mono_right 2 (show i + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.1; omega)
        have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.2; omega)
        omega
      | sub i j =>
        rw [hg_eq] at hslot_wf; simp only [IntGate.bitCost]
        have hci := Nat.clog_mono_right 2 (show i + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.1; omega)
        have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.2; omega)
        omega
      | mul i j =>
        rw [hg_eq] at hslot_wf; simp only [IntGate.bitCost]
        have hci := Nat.clog_mono_right 2 (show i + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.1; omega)
        have hcj := Nat.clog_mono_right 2 (show j + 2 ≤ M + (2 * k) ^ 2 + 2 by have := hslot_wf.2; omega)
        omega
    calc
      ∑ slot : Fin C_out.size, (C_out.gate slot).bitCost
          ≤ ∑ _slot : Fin C_out.size, (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) :=
            Finset.sum_le_sum fun slot _ => hgate_cost slot
      _ = C_out.size * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) := by simp
      _ ≤ M * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) := Nat.mul_le_mul_right _ hN_le_M
  let tutVec : Fin (Fintype.card (UpperPair (2 * k))) → MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ) :=
    fun v => tutteMatrix G w (ePair.symm v).val.1 (ePair.symm v).val.2
  have hgate0 :
      C_out.evalGateAt
        (MvPolynomial.X : Fin (Fintype.card (UpperEdge G)) → MvPolynomial (Fin (Fintype.card (UpperEdge G))) ℤ)
        ⟨0, C_out.size_pos⟩ = 0 := by
    have h0 : C_out.gate ⟨0, C_out.size_pos⟩ = .const 0 := by simp [C_out, gateFn]
    simpa using evalGateAt_const C_out
      (MvPolynomial.X : Fin (Fintype.card (UpperEdge G)) → MvPolynomial (Fin (Fintype.card (UpperEdge G))) ℤ)
      ⟨0, C_out.size_pos⟩ 0 h0
  have hgate_at_sum : ∀ (idx : ℕ) (hidx : idx < C_pf.size) (c t : ℕ) (hc : c < g) (ht : t < g),
      C_out.gate ⟨sumSlot g idx c t, hsum_lt idx hidx c t hc ht⟩ =
        expandBlockGate G w eΓ eEdge ePair idx (g ^ 2 + (c * g + t)) (C_pf.gate ⟨idx, hidx⟩) := by
    intro idx hidx c t hc ht
    have hltB : g ^ 2 + (c * g + t) < B := by
      have h1 : (c + 1) * g ≤ g * g := Nat.mul_le_mul_right g hc
      dsimp [B]; nlinarith
    have hne0 : sumSlot g idx c t ≠ 0 := by dsimp [sumSlot]; omega
    have heq : sumSlot g idx c t - 1 = idx * B + (g ^ 2 + (c * g + t)) := by
      dsimp [sumSlot, B]; omega
    have hdiv : (sumSlot g idx c t - 1) / B = idx := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hltB, Nat.add_zero]
    have hmod : (sumSlot g idx c t - 1) % B = g ^ 2 + (c * g + t) := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_mod, Nat.mod_eq_of_lt hltB]
    dsimp only [C_out, gateFn]
    rw [dif_neg hne0, hdiv, hmod, dif_pos hidx]
  have hgate_at_prod : ∀ (idx : ℕ) (hidx : idx < C_pf.size) (a b : ℕ) (ha : a < g) (hb : b < g),
      C_out.gate ⟨prodSlot g idx a b, hprod_lt idx hidx a b ha hb⟩ =
        expandBlockGate G w eΓ eEdge ePair idx (a * g + b) (C_pf.gate ⟨idx, hidx⟩) := by
    intro idx hidx a b ha hb
    have hltB : a * g + b < B := by
      have h1 : (a + 1) * g ≤ g * g := Nat.mul_le_mul_right g ha
      dsimp [B]; nlinarith
    have hne0 : prodSlot g idx a b ≠ 0 := by dsimp [prodSlot]; omega
    have heq : prodSlot g idx a b - 1 = idx * B + (a * g + b) := by dsimp [prodSlot, B]; omega
    have hdiv : (prodSlot g idx a b - 1) / B = idx := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hltB, Nat.add_zero]
    have hmod : (prodSlot g idx a b - 1) % B = a * g + b := by
      rw [heq, Nat.mul_comm idx B, Nat.mul_add_mod, Nat.mod_eq_of_lt hltB]
    dsimp only [C_out, gateFn]
    rw [dif_neg hne0, hdiv, hmod, dif_pos hidx]
  have hwire_eval : ∀ (idx : ℕ) (hidx : idx < C_pf.size) (γ : Γ),
      C_out.evalGateAt MvPolynomial.X ⟨wireIdx g idx (eΓ γ).val, hwire_lt idx hidx γ⟩ =
        MvPolynomial.rename eEdge (extractGroupCoeff γ (C_pf.evalGateAt tutVec ⟨idx, hidx⟩)) := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | h idx ih =>
      intro hidx γ
      have hγlt : (eΓ γ).val < g := Fin.isLt _
      let wSlot : Fin N_out := ⟨wireIdx g idx (eΓ γ).val, hwire_lt idx hidx γ⟩
      have hgw_base : C_out.gate wSlot =
          expandBlockGate G w eΓ eEdge ePair idx (g ^ 2 + ((eΓ γ).val * g + (g - 1)))
            (C_pf.gate ⟨idx, hidx⟩) :=
        hgate_at_sum idx hidx (eΓ γ).val (g - 1) hγlt (by omega)
      have hsub_g2 : g ^ 2 + ((eΓ γ).val * g + (g - 1)) - g ^ 2 = (eΓ γ).val * g + (g - 1) :=
        Nat.add_sub_cancel_left _ _
      have hdiv_c : ((eΓ γ).val * g + (g - 1)) / g = (eΓ γ).val := by
        rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_div hg, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hmod_t : ((eΓ γ).val * g + (g - 1)) % g = g - 1 := by
        rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hcond : g ^ 2 ≤ g ^ 2 + ((eΓ γ).val * g + (g - 1)) ∧
          (g ^ 2 + ((eΓ γ).val * g + (g - 1)) - g ^ 2) % g = g - 1 :=
        ⟨Nat.le_add_right _ _, by rw [hsub_g2, hmod_t]⟩
      have hgate_wf := C_pf.wf ⟨idx, hidx⟩
      cases hgp : C_pf.gate ⟨idx, hidx⟩ with
      | var v =>
        rw [evalGateAt_var C_pf tutVec ⟨idx, hidx⟩ v hgp]
        dsimp only [tutVec, tutteMatrix]
        rw [dif_pos (ePair.symm v).property]
        rw [hgp] at hgw_base; unfold expandBlockGate at hgw_base; dsimp only at hgw_base; simp only [← hg_def] at hgw_base
        simp only [dif_pos hcond, hsub_g2, hdiv_c] at hgw_base
        by_cases hadj : G.Adj (ePair.symm v).val.1 (ePair.symm v).val.2
        · rw [dif_pos hadj]
          let ed : UpperEdge G := ⟨ePair.symm v, hadj⟩
          have hgw' : C_out.gate wSlot = if eΓ (w ed) = eΓ γ then .var (eEdge ed) else .const 0 := by
            simpa [hγlt, hadj, ed] using hgw_base
          have hextr : extractGroupCoeff γ
              (MvPolynomial.C (AddMonoidAlgebra.single (w ed) (1 : ℤ)) * MvPolynomial.X ed) =
              if w ed = γ then MvPolynomial.X ed else 0 := by
            rw [MvPolynomial.C_mul_X_eq_monomial]
            ext d
            rw [extractGroupCoeff_coeff, MvPolynomial.coeff_monomial]
            by_cases hd : Finsupp.single ed 1 = d
            · rw [if_pos hd, coeffAddEquiv_single]
              split_ifs with hwg
              · rw [← hd, MvPolynomial.coeff_X']; simp
              · simp
            · rw [if_neg hd, map_zero, Finsupp.zero_apply]
              split_ifs
              · rw [MvPolynomial.coeff_X']; simp [hd]
              · simp
          rw [hextr]
          by_cases hwg : w ed = γ
          · have hgw'' : C_out.gate wSlot = .var (eEdge ed) := by rw [hgw', if_pos (congrArg eΓ hwg)]
            rw [if_pos hwg, MvPolynomial.rename_X]
            exact evalGateAt_var C_out MvPolynomial.X wSlot (eEdge ed) hgw''
          · have hgw'' : C_out.gate wSlot = .const 0 := by
              rw [hgw', if_neg (fun h => hwg (eΓ.injective h))]
            rw [if_neg hwg, map_zero]
            simpa using evalGateAt_const C_out MvPolynomial.X wSlot 0 hgw''
        · rw [dif_neg hadj]
          have hgw' : C_out.gate wSlot = .const 0 := by simpa [hγlt, hadj] using hgw_base
          have hextr0 : extractGroupCoeff γ (0 : MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) = 0 := by
            ext d; simp [extractGroupCoeff_coeff]
          rw [hextr0, map_zero]
          simpa using evalGateAt_const C_out MvPolynomial.X wSlot 0 hgw'
      | const a =>
        rw [evalGateAt_const C_pf tutVec ⟨idx, hidx⟩ a hgp]
        rw [hgp] at hgw_base; unfold expandBlockGate at hgw_base; dsimp only at hgw_base; simp only [← hg_def] at hgw_base
        simp only [dif_pos hcond, hsub_g2, hdiv_c] at hgw_base
        have hgw' : C_out.gate wSlot = if eΓ (0 : Γ) = eΓ γ then .const a else .const 0 := by
          simpa [hγlt] using hgw_base
        have hextr : extractGroupCoeff γ (a : MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) =
            if (0 : Γ) = γ then MvPolynomial.C a else 0 := by
          have ha_eq : (a : MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) =
              MvPolynomial.C (AddMonoidAlgebra.single (0 : Γ) a) := by
            have h1 : (a : AddMonoidAlgebra ℤ Γ) = AddMonoidAlgebra.single (0 : Γ) a := by
              rw [← map_intCast (AddMonoidAlgebra.singleZeroRingHom : ℤ →+* AddMonoidAlgebra ℤ Γ)]
              rfl
            rw [← h1, map_intCast]
          rw [ha_eq]
          ext d
          rw [extractGroupCoeff_coeff, MvPolynomial.coeff_C]
          by_cases hd : 0 = d
          · rw [if_pos hd, coeffAddEquiv_single]
            split_ifs with h0g
            · rw [← hd, MvPolynomial.coeff_C]; simp
            · simp
          · rw [if_neg hd, map_zero, Finsupp.zero_apply]
            split_ifs
            · rw [MvPolynomial.coeff_C]; simp [hd]
            · simp
        rw [hextr]
        by_cases h0g : (0 : Γ) = γ
        · have hgw'' : C_out.gate wSlot = .const a := by rw [hgw', if_pos (congrArg eΓ h0g)]
          rw [if_pos h0g, MvPolynomial.rename_C]
          simpa using evalGateAt_const C_out MvPolynomial.X wSlot a hgw''
        · have hgw'' : C_out.gate wSlot = .const 0 := by
            rw [hgw', if_neg (fun h => h0g (eΓ.injective h))]
          rw [if_neg h0g, map_zero]
          simpa using evalGateAt_const C_out MvPolynomial.X wSlot 0 hgw''
      | add i j =>
        rw [hgp] at hgate_wf hgw_base
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [evalGateAt_add C_pf tutVec ⟨idx, hidx⟩ i j hgp (Nat.lt_trans hi hidx) (Nat.lt_trans hj hidx)]
        unfold expandBlockGate at hgw_base; dsimp only at hgw_base; simp only [← hg_def] at hgw_base
        rw [dif_pos hcond, hsub_g2, hdiv_c] at hgw_base
        rw [extractGroupCoeff_add, map_add, ← ih i hi _ γ, ← ih j hj _ γ]
        exact evalGateAt_add C_out MvPolynomial.X wSlot _ _ hgw_base
          (hwire_lt i (Nat.lt_trans hi hidx) γ) (hwire_lt j (Nat.lt_trans hj hidx) γ)
      | sub i j =>
        rw [hgp] at hgate_wf hgw_base
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [evalGateAt_sub C_pf tutVec ⟨idx, hidx⟩ i j hgp (Nat.lt_trans hi hidx) (Nat.lt_trans hj hidx)]
        unfold expandBlockGate at hgw_base; dsimp only at hgw_base; simp only [← hg_def] at hgw_base
        rw [dif_pos hcond, hsub_g2, hdiv_c] at hgw_base
        rw [extractGroupCoeff_sub, map_sub, ← ih i hi _ γ, ← ih j hj _ γ]
        exact evalGateAt_sub C_out MvPolynomial.X wSlot _ _ hgw_base
          (hwire_lt i (Nat.lt_trans hi hidx) γ) (hwire_lt j (Nat.lt_trans hj hidx) γ)
      | mul i j =>
        rw [hgp] at hgate_wf
        have hi : i < idx := hgate_wf.1; have hj : j < idx := hgate_wf.2
        rw [evalGateAt_mul C_pf tutVec ⟨idx, hidx⟩ i j hgp (Nat.lt_trans hi hidx) (Nat.lt_trans hj hidx),
          extractGroupCoeff_mul, map_sum]
        have hprod_eval : ∀ (a b : ℕ) (ha : a < g) (hb : b < g),
            C_out.evalGateAt MvPolynomial.X ⟨prodSlot g idx a b, hprod_lt idx hidx a b ha hb⟩ =
            MvPolynomial.rename eEdge
              (extractGroupCoeff (eΓ.symm ⟨a, ha⟩) (C_pf.evalGateAt tutVec ⟨i, Nat.lt_trans hi hidx⟩)) *
            MvPolynomial.rename eEdge
              (extractGroupCoeff (eΓ.symm ⟨b, hb⟩) (C_pf.evalGateAt tutVec ⟨j, Nat.lt_trans hj hidx⟩)) := by
          intro a b ha hb
          have hgp_slot := hgate_at_prod idx hidx a b ha hb
          rw [hgp] at hgp_slot; unfold expandBlockGate at hgp_slot; dsimp only at hgp_slot; simp only [← hg_def] at hgp_slot
          have hab_lt : a * g + b < g ^ 2 := by
            have h1 : (a + 1) * g ≤ g * g := Nat.mul_le_mul_right g ha; nlinarith
          rw [dif_pos hab_lt] at hgp_slot
          have hda : (a * g + b) / g = a := by
            rw [Nat.mul_comm a g, Nat.mul_add_div hg, Nat.div_eq_of_lt hb, Nat.add_zero]
          have hdb : (a * g + b) % g = b := by
            rw [Nat.mul_comm a g, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
          rw [hda, hdb] at hgp_slot
          have hgp_slot' : C_out.gate ⟨prodSlot g idx a b, hprod_lt idx hidx a b ha hb⟩ =
              .mul (wireIdx g i (eΓ (eΓ.symm ⟨a, ha⟩)).val) (wireIdx g j (eΓ (eΓ.symm ⟨b, hb⟩)).val) := by
            simpa using hgp_slot
          rw [← ih i hi _ (eΓ.symm ⟨a, ha⟩), ← ih j hj _ (eΓ.symm ⟨b, hb⟩)]
          exact evalGateAt_mul C_out MvPolynomial.X _ _ _ hgp_slot'
            (hwire_lt i (Nat.lt_trans hi hidx) _) (hwire_lt j (Nat.lt_trans hj hidx) _)
        have hsum_eval : ∀ (t : ℕ) (ht : t < g),
            C_out.evalGateAt MvPolynomial.X ⟨sumSlot g idx (eΓ γ).val t, hsum_lt idx hidx (eΓ γ).val t hγlt ht⟩ =
              ∑ a ∈ Finset.range (t + 1),
                if ha : a < g then
                  MvPolynomial.rename eEdge
                    (extractGroupCoeff (eΓ.symm ⟨a, ha⟩) (C_pf.evalGateAt tutVec ⟨i, Nat.lt_trans hi hidx⟩) *
                     extractGroupCoeff (γ - eΓ.symm ⟨a, ha⟩) (C_pf.evalGateAt tutVec ⟨j, Nat.lt_trans hj hidx⟩))
                else 0 := by
          intro t
          induction t with
          | zero =>
            intro ht
            have hgs := hgate_at_sum idx hidx (eΓ γ).val 0 hγlt ht
            rw [hgp] at hgs; unfold expandBlockGate at hgs; dsimp only at hgs; simp only [← hg_def] at hgs
            have hnotp : ¬ (g ^ 2 + ((eΓ γ).val * g + 0) < g ^ 2) := by omega
            have hsub : g ^ 2 + ((eΓ γ).val * g + 0) - g ^ 2 = (eΓ γ).val * g + 0 :=
              Nat.add_sub_cancel_left _ _
            have hd0 : ((eΓ γ).val * g + 0) / g = (eΓ γ).val := by
              rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_div hg, Nat.div_eq_of_lt ht, Nat.add_zero]
            have hm0 : ((eΓ γ).val * g + 0) % g = 0 := by
              rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
            simp only [dif_neg hnotp, hsub, hd0, hm0, dif_pos hγlt, dif_pos ht, if_pos rfl] at hgs
            have hgs' : C_out.gate ⟨sumSlot g idx (eΓ γ).val 0, hsum_lt idx hidx (eΓ γ).val 0 hγlt ht⟩ =
                .add (prodSlot g idx 0 (eΓ (γ - eΓ.symm ⟨0, ht⟩)).val) 0 := by
              simpa using hgs
            rw [evalGateAt_add C_out MvPolynomial.X _ _ _ hgs'
              (hprod_lt idx hidx 0 _ ht (Fin.isLt _)) C_out.size_pos,
              hgate0, add_zero, hprod_eval 0 _ ht (Fin.isLt _)]
            simp [Finset.sum_range_one, ht, map_mul]
          | succ t iht =>
            intro ht
            have hgs := hgate_at_sum idx hidx (eΓ γ).val (t + 1) hγlt ht
            rw [hgp] at hgs; unfold expandBlockGate at hgs; dsimp only at hgs; simp only [← hg_def] at hgs
            have hnotp : ¬ (g ^ 2 + ((eΓ γ).val * g + (t + 1)) < g ^ 2) := by omega
            have hsub : g ^ 2 + ((eΓ γ).val * g + (t + 1)) - g ^ 2 = (eΓ γ).val * g + (t + 1) :=
              Nat.add_sub_cancel_left _ _
            have hd1 : ((eΓ γ).val * g + (t + 1)) / g = (eΓ γ).val := by
              rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_div hg, Nat.div_eq_of_lt ht, Nat.add_zero]
            have hm1 : ((eΓ γ).val * g + (t + 1)) % g = t + 1 := by
              rw [Nat.mul_comm (eΓ γ).val g, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
            simp only [dif_neg hnotp, hsub, hd1, hm1, dif_pos hγlt, dif_pos ht, if_neg (Nat.succ_ne_zero t)] at hgs
            have hgs' : C_out.gate ⟨sumSlot g idx (eΓ γ).val (t + 1), hsum_lt idx hidx (eΓ γ).val (t + 1) hγlt ht⟩ =
                .add (sumSlot g idx (eΓ γ).val t) (prodSlot g idx (t + 1) (eΓ (γ - eΓ.symm ⟨t + 1, ht⟩)).val) := by
              simpa using hgs
            rw [evalGateAt_add C_out MvPolynomial.X _ _ _ hgs'
              (hsum_lt idx hidx (eΓ γ).val t hγlt (by omega))
              (hprod_lt idx hidx (t + 1) _ ht (Fin.isLt _)),
              iht (by omega), hprod_eval (t + 1) _ ht (Fin.isLt _),
              Finset.sum_range_succ _ (t + 1), dif_pos ht]
            simp [map_mul]
        have hsum_eq :
            (∑ a ∈ Finset.range g,
              if ha : a < g then
                MvPolynomial.rename eEdge
                  (extractGroupCoeff (eΓ.symm ⟨a, ha⟩) (C_pf.evalGateAt tutVec ⟨i, Nat.lt_trans hi hidx⟩) *
                   extractGroupCoeff (γ - eΓ.symm ⟨a, ha⟩) (C_pf.evalGateAt tutVec ⟨j, Nat.lt_trans hj hidx⟩))
              else 0) =
            ∑ α : Γ,
              MvPolynomial.rename eEdge
                (extractGroupCoeff α (C_pf.evalGateAt tutVec ⟨i, Nat.lt_trans hi hidx⟩) *
                 extractGroupCoeff (γ - α) (C_pf.evalGateAt tutVec ⟨j, Nat.lt_trans hj hidx⟩)) := by
          refine Finset.sum_bij (fun a ha => eΓ.symm ⟨a, Finset.mem_range.mp ha⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a₁ ha₁ a₂ ha₂ hEq
            exact congrArg Fin.val (eΓ.symm.injective hEq)
          · intro α _
            exact ⟨(eΓ α).val, Finset.mem_range.mpr (Fin.isLt _), by simp⟩
          · intro a ha
            simp [Finset.mem_range.mp ha]
        rw [← hsum_eq]
        have hlast := hsum_eval (g - 1) (by omega)
        rwa [Nat.sub_add_cancel hg] at hlast
  have hC_eval : C_out.evalPoly = MvPolynomial.rename eEdge (groupRingPoly G w γstar) := by
    change C_out.evalGateAt MvPolynomial.X ⟨wireIdx g C_pf.out.val (eΓ γstar).val, hwire_lt C_pf.out.val C_pf.out.isLt γstar⟩ = _
    rw [hwire_eval C_pf.out.val C_pf.out.isLt γstar]
    congr 1
    unfold groupRingPoly
    congr 1
    change C_pf.evalAt (MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) tutVec = _
    rw [intCircuit_evalAt_eq_aeval, hpf, MvPolynomial.aeval_rename]
    have hcomp : tutVec ∘ ePair = fun p : UpperPair (2 * k) => tutteMatrix G w p.val.1 p.val.2 := by
      ext p; simp [tutVec]
    rw [hcomp]
    exact aeval_universalPfaffian (tutteMatrix G w)
  exact ⟨C_out, hC_unit, hN_le_M, hC_enc, hC_eval⟩

end ExactMatching.Proofs
