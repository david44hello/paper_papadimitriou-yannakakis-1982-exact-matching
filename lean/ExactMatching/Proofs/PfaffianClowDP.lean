/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.PfaffianMatching
import ExactMatching.Proofs.PfaffianClowAlgebra

/-!
# Unconditional Mahajan–Subramanya–Vinay (`[MSV04]`) Pfaffian Arithmetic Circuit

Constructs an explicit fixed-slot division-free `{0, 1}`-constant `IntCircuit` `dpCircuit k` of
size `≤ 27 * k^4` computing `dpAns (univSkewMat k) = rename (upperPairEquiv (2 * k)) (universalPfaffian k)`,
proving `pfaffian_clow_circuit_exists` unconditionally.

Fixed-slot layout for `k ≥ 1` (`m := 2 * k`):
- Header (`H := 2 + 3 * m^2` slots):
  - `0`: `.const 0`, `1`: `.const 1`
  - `posVarSlot k u v = 2 + u * m + v`: `.var (upperPairEquiv m ⟨(u, v), hlt⟩)` if `u < v` else `.const 0`
  - `matSlot k u v = 2 + m^2 + u * m + v`: `univSkewMat k u v`
  - `negMatSlot k u v = 2 + 2 * m^2 + u * m + v`: `-univSkewMat k u v`
- Layers `t = 0 .. k - 1` (each layer has `L := 8 * k^3 + 4 * k^2` slots):
  - DP cells `(c, u)` (`c < k`, `u < 2*k`), `4 * k` slots each (`2*k` prod slots + `2*k` acc slots),
    ending at `dpSlot k t c u`.
  - Close cells `c` (`c < k`), `4 * k` slots each (`2*k` prod slots + `2*k` acc slots),
    ending at `closeSlot k t c`.
- Answer block (`k` slots): `ansSlot k r` (`r < k`) accumulates `∑ c, closeVal (k - 1) c`.
-/

namespace ExactMatching.Proofs.PfaffianClow

open scoped BigOperators

/-! ### Fixed-slot index formulas -/

def zeroSlot : ℕ := 0
def oneSlot : ℕ := 1

def headerSize (k : ℕ) : ℕ := 2 + 3 * (2 * k) ^ 2

def posVarSlot (k u v : ℕ) : ℕ := 2 + u * (2 * k) + v
def matSlot (k u v : ℕ) : ℕ := 2 + (2 * k) ^ 2 + u * (2 * k) + v
def negMatSlot (k u v : ℕ) : ℕ := 2 + 2 * (2 * k) ^ 2 + u * (2 * k) + v

def layerDpSize (k : ℕ) : ℕ := k * (2 * k) * (4 * k)
def layerCloseSize (k : ℕ) : ℕ := k * (4 * k)
def layerSize (k : ℕ) : ℕ := layerDpSize k + layerCloseSize k

def layerBase (k t : ℕ) : ℕ := headerSize k + t * layerSize k

def dpProdSlot (k t c u r : ℕ) : ℕ :=
  layerBase k t + (c * (2 * k) + u) * (4 * k) + r

def dpAccSlot (k t c u r : ℕ) : ℕ :=
  layerBase k t + (c * (2 * k) + u) * (4 * k) + 2 * k + r

def dpSlot (k t c u : ℕ) : ℕ :=
  dpAccSlot k t c u (2 * k - 1)

def closeProdSlot (k t c r : ℕ) : ℕ :=
  layerBase k t + layerDpSize k + c * (4 * k) + r

def closeAccSlot (k t c r : ℕ) : ℕ :=
  layerBase k t + layerDpSize k + c * (4 * k) + 2 * k + r

def closeSlot (k t c : ℕ) : ℕ :=
  closeAccSlot k t c (2 * k - 1)

def ansBase (k : ℕ) : ℕ := headerSize k + k * layerSize k
def ansSlot (k r : ℕ) : ℕ := ansBase k + r
def totalDpSize (k : ℕ) : ℕ := ansBase k + k

def signedEdgeSlot (k : ℕ) (u w : Fin (2 * k)) : ℕ :=
  if (mate w).val % 2 = 0 then matSlot k u.val (mate w).val else negMatSlot k u.val (mate w).val

/-- Gate function for the fixed-slot Pfaffian DP circuit. -/
noncomputable def dpGateFn (k : ℕ) (hk : 1 ≤ k) (idx : ℕ) :
    IntGate (Fintype.card (UpperPair (2 * k))) :=
  let m := 2 * k
  if idx = 0 then .const 0
  else if idx = 1 then .const 1
  else if idx < 2 + m ^ 2 then
    let off := idx - 2
    let u := off / m
    let v := off % m
    if h : u < m ∧ v < m ∧ u < v then
      .var (upperPairEquiv m ⟨(⟨u, h.1⟩, ⟨v, h.2.1⟩), h.2.2⟩)
    else .const 0
  else if idx < 2 + 2 * m ^ 2 then
    let off := idx - (2 + m ^ 2)
    let u := off / m
    let v := off % m
    if u < v then .add (posVarSlot k u v) zeroSlot
    else if v < u then .sub zeroSlot (posVarSlot k v u)
    else .const 0
  else if idx < headerSize k then
    let off := idx - (2 + 2 * m ^ 2)
    let u := off / m
    let v := off % m
    .sub zeroSlot (matSlot k u v)
  else if idx < ansBase k then
    let rel := idx - headerSize k
    let t := rel / layerSize k
    let inLayer := rel % layerSize k
    if inLayer < layerDpSize k then
      let cell := inLayer / (4 * k)
      let inCell := inLayer % (4 * k)
      let c := cell / m
      let u := cell % m
      if t = 0 then
        if inCell = 4 * k - 1 then
          if u = 2 * c then .const 1 else .const 0
        else .const 0
      else
        if hrm : inCell < m then
          let r := inCell
          if hcu : c < u / 2 ∧ u < m then
            .mul (dpSlot k (t - 1) c r)
              (signedEdgeSlot k ⟨r, hrm⟩ ⟨u, hcu.2⟩)
          else .const 0
        else
          let r := inCell - m
          if c < u / 2 then
            if r = 0 then .add zeroSlot (dpProdSlot k t c u 0)
            else .add (dpAccSlot k t c u (r - 1)) (dpProdSlot k t c u r)
          else if u = 2 * c then
            if r = 0 then
              if 0 < c then .add zeroSlot (closeSlot k (t - 1) 0) else .const 0
            else
              if r < c then .add (dpAccSlot k t c u (r - 1)) (closeSlot k (t - 1) r)
              else .add (dpAccSlot k t c u (r - 1)) zeroSlot
          else .const 0
    else
      let relC := inLayer - layerDpSize k
      let c := relC / (4 * k)
      let inCell := relC % (4 * k)
      if inCell < m then
        let r := inCell
        .mul (dpSlot k t c r) (matSlot k r (2 * c + 1))
      else
        let r := inCell - m
        if r = 0 then .add zeroSlot (closeProdSlot k t c 0)
        else .add (closeAccSlot k t c (r - 1)) (closeProdSlot k t c r)
  else
    let r := idx - ansBase k
    if r = 0 then .add zeroSlot (closeSlot k (k - 1) 0)
    else .add (ansSlot k (r - 1)) (closeSlot k (k - 1) r)

/-! ### Slot bounds and well-formedness -/

private lemma mul_add_div_eq (a b m : ℕ) (hb : b < m) : (a * m + b) / m = a := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, add_zero]

private lemma mul_add_mod_eq (a b m : ℕ) (hb : b < m) : (a * m + b) % m = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private lemma layerSize_pos (k : ℕ) (hk : 1 ≤ k) : 0 < layerSize k := by
  unfold layerSize layerDpSize layerCloseSize
  positivity

private lemma posVarSlot_lt_matSlot (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    posVarSlot k u v < 2 + (2 * k) ^ 2 := by
  unfold posVarSlot
  have : u * (2 * k) + v < (2 * k) * (2 * k) := by nlinarith
  nlinarith

private lemma matSlot_lt_header (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    matSlot k u v < 2 + 2 * (2 * k) ^ 2 := by
  unfold matSlot
  have : u * (2 * k) + v < (2 * k) * (2 * k) := by nlinarith
  nlinarith

private lemma negMatSlot_lt_header (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    negMatSlot k u v < headerSize k := by
  unfold negMatSlot headerSize
  have : u * (2 * k) + v < (2 * k) * (2 * k) := by nlinarith
  nlinarith

private lemma signedEdgeSlot_lt_header (k : ℕ) (u w : Fin (2 * k)) :
    signedEdgeSlot k u w < headerSize k := by
  unfold signedEdgeSlot
  split_ifs
  · exact lt_trans (matSlot_lt_header k u.val (mate w).val u.isLt (mate w).isLt) (by
      unfold headerSize; nlinarith [u.isLt])
  · exact negMatSlot_lt_header k u.val (mate w).val u.isLt (mate w).isLt

private lemma dpAccSlot_lt_layerDp (k t c u r : ℕ) (hc : c < k) (hu : u < 2 * k) (hr : r < 2 * k) :
    (c * (2 * k) + u) * (4 * k) + 2 * k + r < layerDpSize k := by
  unfold layerDpSize
  have h1 : c * (2 * k) + u + 1 ≤ k * (2 * k) := by nlinarith
  nlinarith

private lemma dpSlot_lt_layerBase_next (k t c u : ℕ) (hk : 1 ≤ k) (hc : c < k) (hu : u < 2 * k) :
    dpSlot k t c u < layerBase k t + layerDpSize k := by
  unfold dpSlot dpAccSlot
  have := dpAccSlot_lt_layerDp k t c u (2 * k - 1) hc hu (by omega)
  omega

private lemma closeSlot_lt_layerBase_next (k t c : ℕ) (hk : 1 ≤ k) (hc : c < k) :
    closeSlot k t c < layerBase k (t + 1) := by
  unfold closeSlot closeAccSlot layerBase layerSize layerCloseSize
  have hsub : 2 * k + (2 * k - 1) < 4 * k := by omega
  have h1 : c * (4 * k) + (2 * k + (2 * k - 1)) < k * (4 * k) := by nlinarith
  nlinarith

private lemma dpGateFn_wf (k : ℕ) (hk : 1 ≤ k) (idx : ℕ) (hidx : idx < totalDpSize k) :
    (dpGateFn k hk idx).WF idx := by
  unfold dpGateFn
  have hLs : 0 < layerSize k := layerSize_pos k hk
  dsimp only
  by_cases h0 : idx = 0
  · simp [h0, IntGate.WF]
  rw [if_neg h0]
  by_cases h1 : idx = 1
  · simp [h1, IntGate.WF]
  rw [if_neg h1]
  by_cases h2 : idx < 2 + (2 * k) ^ 2
  · rw [if_pos h2]
    split_ifs <;> exact trivial
  rw [if_neg h2]
  by_cases h3 : idx < 2 + 2 * (2 * k) ^ 2
  · rw [if_pos h3]
    have hsq : (2 * k) ^ 2 = (2 * k) * (2 * k) := sq (2 * k)
    have hdiff : idx - (2 + (2 * k) ^ 2) < (2 * k) * (2 * k) := by rw [← hsq]; omega
    have hu : (idx - (2 + (2 * k) ^ 2)) / (2 * k) < 2 * k := Nat.div_lt_of_lt_mul hdiff
    have hv : (idx - (2 + (2 * k) ^ 2)) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    split_ifs
    · exact ⟨lt_of_lt_of_le (posVarSlot_lt_matSlot k _ _ hu hv) (by omega), by unfold zeroSlot; omega⟩
    · exact ⟨by unfold zeroSlot; omega, lt_of_lt_of_le (posVarSlot_lt_matSlot k _ _ hv hu) (by omega)⟩
    · exact trivial
  rw [if_neg h3]
  by_cases h4 : idx < headerSize k
  · rw [if_pos h4]
    have hsq : (2 * k) ^ 2 = (2 * k) * (2 * k) := sq (2 * k)
    have hdiff : idx - (2 + 2 * (2 * k) ^ 2) < (2 * k) * (2 * k) := by
      unfold headerSize at h4; rw [← hsq]; omega
    have hu : (idx - (2 + 2 * (2 * k) ^ 2)) / (2 * k) < 2 * k := Nat.div_lt_of_lt_mul hdiff
    have hv : (idx - (2 + 2 * (2 * k) ^ 2)) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    exact ⟨by unfold zeroSlot; omega, lt_of_lt_of_le (matSlot_lt_header k _ _ hu hv) (by omega)⟩
  rw [if_neg h4]
  by_cases h5 : idx < ansBase k
  · rw [if_pos h5]
    set rel := idx - headerSize k
    set t := rel / layerSize k
    set inLayer := rel % layerSize k
    have hdiv1 : t * layerSize k + inLayer = rel := by
      have := Nat.div_add_mod rel (layerSize k); rw [Nat.mul_comm] at this; exact this
    have hidx_eq : idx = layerBase k t + inLayer := by unfold layerBase; omega
    by_cases h6 : inLayer < layerDpSize k
    · rw [if_pos h6]
      set cell := inLayer / (4 * k)
      set inCell := inLayer % (4 * k)
      set c := cell / (2 * k)
      set u := cell % (2 * k)
      have hdiv2 : cell * (4 * k) + inCell = inLayer := by
        have := Nat.div_add_mod inLayer (4 * k); rw [Nat.mul_comm] at this; exact this
      have hdiv3 : c * (2 * k) + u = cell := by
        have := Nat.div_add_mod cell (2 * k); rw [Nat.mul_comm] at this; exact this
      have hcell_lt : cell < k * (2 * k) := by
        unfold layerDpSize at h6; exact Nat.div_lt_of_lt_mul (by nlinarith)
      have hc_lt : c < k := Nat.div_lt_of_lt_mul (by nlinarith)
      by_cases ht0 : t = 0
      · rw [if_pos ht0]; split_ifs <;> exact trivial
      rw [if_neg ht0]
      have ht_pos : 1 ≤ t := Nat.pos_of_ne_zero ht0
      by_cases hrm : inCell < 2 * k
      · rw [dif_pos hrm]
        by_cases hcu : c < u / 2 ∧ u < 2 * k
        · rw [dif_pos hcu]
          unfold IntGate.WF
          have hdp_lt : dpSlot k (t - 1) c inCell < layerBase k t := by
            have hd := dpSlot_lt_layerBase_next k (t - 1) c inCell hk hc_lt hrm
            have hstep : (t - 1) * layerSize k + layerSize k = t * layerSize k := by
              rw [← Nat.succ_mul]; congr 1; omega
            have hle : layerDpSize k ≤ layerSize k := by unfold layerSize; omega
            have h2 : layerBase k (t - 1) + layerDpSize k ≤ layerBase k t := by
              unfold layerBase; omega
            omega
          have hed_lt := signedEdgeSlot_lt_header k ⟨inCell, hrm⟩ ⟨u, hcu.2⟩
          have hlb_ge : headerSize k ≤ layerBase k t := by unfold layerBase; omega
          have hlb_le : layerBase k t ≤ idx := by rw [hidx_eq]; exact Nat.le_add_right _ _
          exact ⟨lt_of_lt_of_le hdp_lt hlb_le, lt_of_lt_of_le hed_lt (le_trans hlb_ge hlb_le)⟩
        · rw [dif_neg hcu]; exact trivial
      rw [dif_neg hrm]
      have hmod_lt : inCell < 4 * k := Nat.mod_lt _ (by omega)
      by_cases hcu : c < u / 2
      · rw [if_pos hcu]
        by_cases hr0 : inCell - 2 * k = 0
        · rw [if_pos hr0]
          unfold IntGate.WF zeroSlot dpProdSlot
          rw [hdiv3]
          omega
        · rw [if_neg hr0]
          unfold IntGate.WF dpAccSlot dpProdSlot
          rw [hdiv3]
          omega
      rw [if_neg hcu]
      by_cases hev : u = 2 * c
      · rw [if_pos hev]
        by_cases hr0 : inCell - 2 * k = 0
        · rw [if_pos hr0]
          by_cases hc0 : 0 < c
          · rw [if_pos hc0]
            unfold IntGate.WF zeroSlot
            have hcl := closeSlot_lt_layerBase_next k (t - 1) 0 hk hk
            have hlb : layerBase k ((t - 1) + 1) = layerBase k t := by congr 1; omega
            omega
          · rw [if_neg hc0]; exact trivial
        rw [if_neg hr0]
        by_cases hrc : inCell - 2 * k < c
        · rw [if_pos hrc]
          unfold IntGate.WF dpAccSlot
          rw [hdiv3]
          have hcl := closeSlot_lt_layerBase_next k (t - 1) (inCell - 2 * k) hk (by omega)
          have hlb : layerBase k ((t - 1) + 1) = layerBase k t := by congr 1; omega
          omega
        · rw [if_neg hrc]
          unfold IntGate.WF dpAccSlot zeroSlot
          rw [hdiv3]
          omega
      · rw [if_neg hev]; exact trivial
    · rw [if_neg h6]
      set relC := inLayer - layerDpSize k
      set c := relC / (4 * k)
      set inCell := relC % (4 * k)
      have hdiv2 : c * (4 * k) + inCell = relC := by
        have := Nat.div_add_mod relC (4 * k); rw [Nat.mul_comm] at this; exact this
      have hinL_lt : inLayer < layerSize k := Nat.mod_lt _ hLs
      have hrelC_lt : relC < layerCloseSize k := by unfold layerSize at hinL_lt; omega
      have hc_lt : c < k := by unfold layerCloseSize at hrelC_lt; exact Nat.div_lt_of_lt_mul (by nlinarith)
      by_cases hrm : inCell < 2 * k
      · rw [if_pos hrm]
        unfold IntGate.WF
        have hdp := dpSlot_lt_layerBase_next k t c inCell hk hc_lt hrm
        have hmat := matSlot_lt_header k inCell (2 * c + 1) hrm (by omega)
        have hmat2 : matSlot k inCell (2 * c + 1) < headerSize k :=
          lt_trans hmat (by unfold headerSize; nlinarith [hk])
        have hlb_ge : headerSize k ≤ layerBase k t := by unfold layerBase; omega
        omega
      · rw [if_neg hrm]
        have hmod_lt : inCell < 4 * k := Nat.mod_lt _ (by omega)
        by_cases hr0 : inCell - 2 * k = 0
        · rw [if_pos hr0]
          unfold IntGate.WF zeroSlot closeProdSlot
          omega
        · rw [if_neg hr0]
          unfold IntGate.WF closeAccSlot closeProdSlot
          omega
  · rw [if_neg h5]
    by_cases hr0 : idx - ansBase k = 0
    · rw [if_pos hr0]
      unfold IntGate.WF zeroSlot
      have hcl := closeSlot_lt_layerBase_next k (k - 1) 0 hk hk
      have hlb : layerBase k ((k - 1) + 1) = ansBase k := by
        unfold layerBase ansBase; congr 2; omega
      omega
    · rw [if_neg hr0]
      unfold IntGate.WF ansSlot
      have hr_lt : idx - ansBase k < k := by unfold totalDpSize at hidx; omega
      have hcl := closeSlot_lt_layerBase_next k (k - 1) (idx - ansBase k) hk hr_lt
      have hlb : layerBase k ((k - 1) + 1) = ansBase k := by
        unfold layerBase ansBase; congr 2; omega
      omega

/-- The explicit `[MSV04]` Pfaffian DP circuit `dpCircuit k` for `k ≥ 1`. -/
noncomputable def dpCircuit (k : ℕ) (hk : 1 ≤ k) :
    IntCircuit (Fintype.card (UpperPair (2 * k))) where
  size := totalDpSize k
  size_pos := by unfold totalDpSize ansBase headerSize; omega
  gate idx := dpGateFn k hk idx.val
  wf idx := dpGateFn_wf k hk idx.val idx.isLt
  out := ⟨ansSlot k (k - 1), by unfold ansSlot totalDpSize; omega⟩

private def IsUnitConstGate {n : ℕ} : IntGate n → Prop
  | .const a => a = 0 ∨ a = 1 ∨ a = -1
  | _ => True

private lemma ite_prop {p : Prop} [Decidable p] {α : Type*} {P : α → Prop} {x y : α}
    (hx : P x) (hy : P y) : P (if p then x else y) := by
  by_cases hp : p <;> simp [hp, hx, hy]

private lemma dite_prop {p : Prop} [Decidable p] {α : Type*} {P : α → Prop}
    {x : p → α} {y : ¬ p → α} (hx : ∀ hp, P (x hp)) (hy : ∀ hnp, P (y hnp)) :
    P (if hp : p then x hp else y hp) := by
  by_cases hp : p <;> simp [hp, hx, hy]

private lemma dpGateFn_isUnitConst (k : ℕ) (hk : 1 ≤ k) (idx : ℕ) :
    IsUnitConstGate (dpGateFn k hk idx) := by
  unfold dpGateFn; dsimp only
  apply ite_prop; · exact Or.inl rfl
  apply ite_prop; · exact Or.inr (Or.inl rfl)
  apply ite_prop; · apply dite_prop <;> intro _ <;> simp [IsUnitConstGate]
  apply ite_prop; · apply ite_prop <;> [exact trivial; (apply ite_prop <;> [exact trivial; exact Or.inl rfl])]
  apply ite_prop; · exact trivial
  apply ite_prop
  · apply ite_prop
    · apply ite_prop
      · apply ite_prop
        · apply ite_prop <;> [exact Or.inr (Or.inl rfl); exact Or.inl rfl]
        · exact Or.inl rfl
      · apply dite_prop
        · intro _; apply dite_prop <;> intro _ <;> simp [IsUnitConstGate]
        · intro _
          apply ite_prop
          · apply ite_prop <;> exact trivial
          · apply ite_prop
            · apply ite_prop
              · apply ite_prop <;> [exact trivial; exact Or.inl rfl]
              · apply ite_prop <;> exact trivial
            · exact Or.inl rfl
    · apply ite_prop
      · exact trivial
      · apply ite_prop <;> exact trivial
  · apply ite_prop <;> exact trivial

lemma dpCircuit_usesOnlyUnitConstants (k : ℕ) (hk : 1 ≤ k) :
    (dpCircuit k hk).UsesOnlyUnitConstants := by
  intro idx a hgate
  have h := dpGateFn_isUnitConst k hk idx.val
  change IsUnitConstGate ((dpCircuit k hk).gate idx) at h
  rw [hgate] at h
  exact h

lemma dpCircuit_size_le (k : ℕ) (hk : 1 ≤ k) :
    (dpCircuit k hk).size ≤ 27 * k ^ 4 := by
  dsimp [dpCircuit, totalDpSize, ansBase, headerSize, layerSize, layerDpSize, layerCloseSize]
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have hk3 : 1 ≤ k ^ 3 := by nlinarith
  have hk4 : 1 ≤ k ^ 4 := by nlinarith
  have h1 : k ≤ k ^ 4 := by nlinarith
  have h2 : k ^ 2 ≤ k ^ 4 := by nlinarith
  have h3 : k ^ 3 ≤ k ^ 4 := by nlinarith
  nlinarith

/-! ### Exact evaluation of `dpCircuit k` -/

private lemma evalGateAt_var {n : ℕ} {R : Type*} [CommRing R]
    (C : IntCircuit n) (x : Fin n → R) (idx : Fin C.size) (v : Fin n)
    (h : C.gate idx = .var v) : C.evalGateAt x idx = x v := by
  unfold IntCircuit.evalGateAt
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGateAt_const {n : ℕ} {R : Type*} [CommRing R]
    (C : IntCircuit n) (x : Fin n → R) (idx : Fin C.size) (a : ℤ)
    (h : C.gate idx = .const a) : C.evalGateAt x idx = (a : R) := by
  unfold IntCircuit.evalGateAt
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGateAt_add {n : ℕ} {R : Type*} [CommRing R]
    (C : IntCircuit n) (x : Fin n → R) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .add i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x idx = C.evalGateAt x ⟨i, hi⟩ + C.evalGateAt x ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGateAt_sub {n : ℕ} {R : Type*} [CommRing R]
    (C : IntCircuit n) (x : Fin n → R) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .sub i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x idx = C.evalGateAt x ⟨i, hi⟩ - C.evalGateAt x ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGateAt_mul {n : ℕ} {R : Type*} [CommRing R]
    (C : IntCircuit n) (x : Fin n → R) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .mul i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x idx = C.evalGateAt x ⟨i, hi⟩ * C.evalGateAt x ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

/-- Slot bound helper: `dpSlot k t c u < totalDpSize k` for `t < k`, `c < k`, `u < 2*k`. -/
private lemma dpSlot_lt_total (k t c u : ℕ) (hk : 1 ≤ k) (ht : t < k) (hc : c < k) (hu : u < 2 * k) :
    dpSlot k t c u < totalDpSize k := by
  have h1 := dpSlot_lt_layerBase_next k t c u hk hc hu
  unfold totalDpSize ansBase; unfold layerBase at h1; unfold layerSize at h1 ⊢; nlinarith

/-- Slot bound helper: `closeSlot k t c < totalDpSize k` for `t < k`, `c < k`. -/
private lemma closeSlot_lt_total (k t c : ℕ) (hk : 1 ≤ k) (ht : t < k) (hc : c < k) :
    closeSlot k t c < totalDpSize k := by
  have h1 := closeSlot_lt_layerBase_next k t c hk hc
  unfold totalDpSize ansBase; unfold layerBase at h1; nlinarith

private lemma posVarSlot_lt_total (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    posVarSlot k u v < totalDpSize k := by
  have h1 := posVarSlot_lt_matSlot k u v hu hv
  unfold totalDpSize ansBase headerSize; nlinarith

private lemma matSlot_lt_total (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    matSlot k u v < totalDpSize k := by
  have h1 := matSlot_lt_header k u v hu hv
  unfold totalDpSize ansBase headerSize; nlinarith

private lemma negMatSlot_lt_total (k u v : ℕ) (hu : u < 2 * k) (hv : v < 2 * k) :
    negMatSlot k u v < totalDpSize k := by
  have h1 := negMatSlot_lt_header k u v hu hv
  unfold totalDpSize ansBase; omega

private lemma dpCircuit_gate_eq (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i < (dpCircuit k hk).size) :
    (dpCircuit k hk).gate ⟨i, hi⟩ = dpGateFn k hk i := rfl

private lemma dpCircuit_eval_zero (k : ℕ) (hk : 1 ≤ k) :
    (dpCircuit k hk).evalGateAt (MvPolynomial.X : Fin (Fintype.card (UpperPair (2 * k))) → MvPolynomial (Fin (Fintype.card (UpperPair (2 * k)))) ℤ)
      ⟨zeroSlot, (dpCircuit k hk).size_pos⟩ = 0 := by
  rw [evalGateAt_const _ _ _ 0 (by dsimp [dpCircuit, dpGateFn, zeroSlot])]
  simp

private lemma dpCircuit_eval_posVar (k : ℕ) (hk : 1 ≤ k) (u v : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt (MvPolynomial.X : Fin (Fintype.card (UpperPair (2 * k))) → MvPolynomial (Fin (Fintype.card (UpperPair (2 * k)))) ℤ)
      ⟨posVarSlot k u.val v.val, posVarSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
      if hlt : u < v then MvPolynomial.X (upperPairEquiv (2 * k) ⟨(u, v), hlt⟩) else 0 := by
  have hlt1 := posVarSlot_lt_matSlot k u.val v.val u.isLt v.isLt
  have hsub : posVarSlot k u.val v.val - 2 = u.val * (2 * k) + v.val := by unfold posVarSlot; omega
  have hdiv : (posVarSlot k u.val v.val - 2) / (2 * k) = u.val := by
    rw [hsub]; exact mul_add_div_eq u.val v.val (2 * k) v.isLt
  have hmod : (posVarSlot k u.val v.val - 2) % (2 * k) = v.val := by
    rw [hsub]; exact mul_add_mod_eq u.val v.val (2 * k) v.isLt
  have hge2 : 2 ≤ posVarSlot k u.val v.val := by unfold posVarSlot; omega
  have hn0 : posVarSlot k u.val v.val ≠ 0 := by omega
  have hn1 : posVarSlot k u.val v.val ≠ 1 := by omega
  by_cases hlt : u < v
  · have hltv : u.val < v.val := hlt
    have hgt : (dpCircuit k hk).gate ⟨posVarSlot k u.val v.val, posVarSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
        .var (upperPairEquiv (2 * k) ⟨(u, v), hlt⟩) := by
      dsimp [dpCircuit, dpGateFn]
      simp only [hn0, hn1, hlt1, ↓reduceIte, hdiv, hmod, u.isLt, v.isLt, hltv, true_and, ↓reduceDIte]
    rw [evalGateAt_var _ _ _ _ hgt]
    simp [hlt]
  · have hnot : ¬ (u.val < 2 * k ∧ v.val < 2 * k ∧ u.val < v.val) := fun h => hlt h.2.2
    have hgt : (dpCircuit k hk).gate ⟨posVarSlot k u.val v.val, posVarSlot_lt_total k u.val v.val u.isLt v.isLt⟩ = .const 0 := by
      dsimp [dpCircuit, dpGateFn]
      simp only [hn0, hn1, hlt1, ↓reduceIte, hdiv, hmod, hnot, ↓reduceDIte]
    rw [evalGateAt_const _ _ _ 0 hgt]
    simp [hlt]

private lemma dpCircuit_eval_mat (k : ℕ) (hk : 1 ≤ k) (u v : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨matSlot k u.val v.val, matSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
      univSkewMat k u v := by
  have hlt2 := matSlot_lt_header k u.val v.val u.isLt v.isLt
  have hge1 : 2 + (2 * k) ^ 2 ≤ matSlot k u.val v.val := by unfold matSlot; omega
  have hsub : matSlot k u.val v.val - (2 + (2 * k) ^ 2) = u.val * (2 * k) + v.val := by unfold matSlot; omega
  have hdiv : (matSlot k u.val v.val - (2 + (2 * k) ^ 2)) / (2 * k) = u.val := by
    rw [hsub]; exact mul_add_div_eq u.val v.val (2 * k) v.isLt
  have hmod : (matSlot k u.val v.val - (2 + (2 * k) ^ 2)) % (2 * k) = v.val := by
    rw [hsub]; exact mul_add_mod_eq u.val v.val (2 * k) v.isLt
  have hn0 : matSlot k u.val v.val ≠ 0 := by omega
  have hn1 : matSlot k u.val v.val ≠ 1 := by omega
  have hnot1 : ¬ (matSlot k u.val v.val < 2 + (2 * k) ^ 2) := by omega
  unfold univSkewMat
  by_cases hlt : u < v
  · have hgt : (dpCircuit k hk).gate ⟨matSlot k u.val v.val, matSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
        .add (posVarSlot k u.val v.val) zeroSlot := by
      dsimp [dpCircuit, dpGateFn]
      simp only [hn0, hn1, hnot1, hlt2, ↓reduceIte, hdiv, hmod]
      have : u.val < v.val := hlt; simp [this]
    rw [evalGateAt_add _ _ _ _ _ hgt (posVarSlot_lt_total k u.val v.val u.isLt v.isLt) (dpCircuit k hk).size_pos,
        dpCircuit_eval_posVar k hk u v, dpCircuit_eval_zero k hk]
    simp [hlt]
  · by_cases hgt' : v < u
    · have hgt : (dpCircuit k hk).gate ⟨matSlot k u.val v.val, matSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
          .sub zeroSlot (posVarSlot k v.val u.val) := by
        dsimp [dpCircuit, dpGateFn]
        simp only [hn0, hn1, hnot1, hlt2, ↓reduceIte, hdiv, hmod]
        have h1 : ¬ (u.val < v.val) := hlt
        have h2 : v.val < u.val := hgt'
        simp [h1, h2]
      rw [evalGateAt_sub _ _ _ _ _ hgt (dpCircuit k hk).size_pos (posVarSlot_lt_total k v.val u.val v.isLt u.isLt),
          dpCircuit_eval_zero k hk, dpCircuit_eval_posVar k hk v u]
      simp [hlt, hgt']
    · have hgt : (dpCircuit k hk).gate ⟨matSlot k u.val v.val, matSlot_lt_total k u.val v.val u.isLt v.isLt⟩ = .const 0 := by
        dsimp [dpCircuit, dpGateFn]
        simp only [hn0, hn1, hnot1, hlt2, ↓reduceIte, hdiv, hmod]
        have h1 : ¬ (u.val < v.val) := hlt
        have h2 : ¬ (v.val < u.val) := hgt'
        simp [h1, h2]
      rw [evalGateAt_const _ _ _ 0 hgt]
      simp [hlt, hgt']

private lemma dpCircuit_eval_negMat (k : ℕ) (hk : 1 ≤ k) (u v : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨negMatSlot k u.val v.val, negMatSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
      -univSkewMat k u v := by
  have hlt3 := negMatSlot_lt_header k u.val v.val u.isLt v.isLt
  have hge2 : 2 + 2 * (2 * k) ^ 2 ≤ negMatSlot k u.val v.val := by unfold negMatSlot; omega
  have hsub : negMatSlot k u.val v.val - (2 + 2 * (2 * k) ^ 2) = u.val * (2 * k) + v.val := by unfold negMatSlot; omega
  have hdiv : (negMatSlot k u.val v.val - (2 + 2 * (2 * k) ^ 2)) / (2 * k) = u.val := by
    rw [hsub]; exact mul_add_div_eq u.val v.val (2 * k) v.isLt
  have hmod : (negMatSlot k u.val v.val - (2 + 2 * (2 * k) ^ 2)) % (2 * k) = v.val := by
    rw [hsub]; exact mul_add_mod_eq u.val v.val (2 * k) v.isLt
  have hgt : (dpCircuit k hk).gate ⟨negMatSlot k u.val v.val, negMatSlot_lt_total k u.val v.val u.isLt v.isLt⟩ =
      .sub zeroSlot (matSlot k u.val v.val) := by
    dsimp [dpCircuit, dpGateFn]
    have hn0 : negMatSlot k u.val v.val ≠ 0 := by omega
    have hn1 : negMatSlot k u.val v.val ≠ 1 := by omega
    have hnot1 : ¬ (negMatSlot k u.val v.val < 2 + (2 * k) ^ 2) := by omega
    have hnot2 : ¬ (negMatSlot k u.val v.val < 2 + 2 * (2 * k) ^ 2) := by omega
    simp only [hn0, hn1, hnot1, hnot2, hlt3, ↓reduceIte, hdiv, hmod]
  rw [evalGateAt_sub _ _ _ _ _ hgt (dpCircuit k hk).size_pos (matSlot_lt_total k u.val v.val u.isLt v.isLt),
      dpCircuit_eval_zero k hk, dpCircuit_eval_mat k hk u v, zero_sub]

private lemma dpCircuit_eval_signedEdge (k : ℕ) (hk : 1 ≤ k) (u w : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X
      ⟨signedEdgeSlot k u w, lt_of_lt_of_le (signedEdgeSlot_lt_header k u w) (by dsimp only [dpCircuit]; unfold totalDpSize ansBase; omega)⟩ =
      univSkewMat k u (mate w) * (jSign (mate w) : MvPolynomial _ ℤ) := by
  unfold signedEdgeSlot jSign
  split_ifs with h
  · rw [dpCircuit_eval_mat k hk u (mate w)]; simp
  · rw [dpCircuit_eval_negMat k hk u (mate w)]; simp

/-- Uniform evaluation of `closeSlot k t c` given `dpSlot k t c u` for all `u`. -/
private lemma dpCircuit_eval_close (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : t < k) (c : Fin k)
    (hdp : ∀ u : Fin (2 * k),
      (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpSlot k t c.val u.val, dpSlot_lt_total k t c.val u.val hk ht c.isLt u.isLt⟩ =
        dpVal (univSkewMat k) t c u) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨closeSlot k t c.val, closeSlot_lt_total k t c.val hk ht c.isLt⟩ =
      closeVal (univSkewMat k) t c := by
  have hLs : 0 < layerSize k := layerSize_pos k hk
  have hA_le : ansBase k ≤ totalDpSize k := by unfold totalDpSize; omega
  have hdecodeC : ∀ (off : ℕ) (hoff : off < 4 * k),
      let idx := layerBase k t + layerDpSize k + c.val * (4 * k) + off
      (idx - headerSize k) / layerSize k = t ∧
      (idx - headerSize k) % layerSize k = layerDpSize k + c.val * (4 * k) + off ∧
      (c.val * (4 * k) + off) / (4 * k) = c.val ∧
      (c.val * (4 * k) + off) % (4 * k) = off ∧
      headerSize k ≤ idx ∧ idx < ansBase k := by
    intro off hoff
    have hrel : layerBase k t + layerDpSize k + c.val * (4 * k) + off - headerSize k =
        t * layerSize k + (layerDpSize k + c.val * (4 * k) + off) := by unfold layerBase; omega
    have hltL : layerDpSize k + c.val * (4 * k) + off < layerSize k := by
      unfold layerSize layerCloseSize; nlinarith [c.isLt]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrel]; exact mul_add_div_eq t _ (layerSize k) hltL
    · rw [hrel]; exact mul_add_mod_eq t _ (layerSize k) hltL
    · exact mul_add_div_eq c.val off (4 * k) hoff
    · exact mul_add_mod_eq c.val off (4 * k) hoff
    · unfold layerBase; omega
    · unfold ansBase layerBase; nlinarith
  have hprod : ∀ (j : ℕ) (hj : j < 2 * k),
      (dpCircuit k hk).evalGateAt MvPolynomial.X
        ⟨closeProdSlot k t c.val j, lt_of_lt_of_le (by have := (hdecodeC j (by omega)).2.2.2.2.2; unfold closeProdSlot; omega) hA_le⟩ =
        dpVal (univSkewMat k) t c ⟨j, hj⟩ * univSkewMat k ⟨j, hj⟩ (oddV c) := by
    intro j hj
    rcases hdecodeC j (by omega) with ⟨hdt, hdm, hdc, hdo, hgeH, hltA⟩
    have hgate : (dpCircuit k hk).gate ⟨closeProdSlot k t c.val j, lt_of_lt_of_le (by unfold closeProdSlot; omega) hA_le⟩ =
        .mul (dpSlot k t c.val j) (matSlot k j (2 * c.val + 1)) := by
      dsimp [dpCircuit, dpGateFn, closeProdSlot] at hdt hdm hgeH hltA ⊢
      have hn0 : layerBase k t + layerDpSize k + c.val * (4 * k) + j ≠ 0 := by unfold headerSize at hgeH; omega
      have hn1 : layerBase k t + layerDpSize k + c.val * (4 * k) + j ≠ 1 := by unfold headerSize at hgeH; omega
      have hnot1 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + j < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
      have hnot2 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + j < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
      have hnot3 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + j < headerSize k) := by omega
      have hnotdp : ¬ (layerDpSize k + c.val * (4 * k) + j < layerDpSize k) := by omega
      have hsub : layerDpSize k + c.val * (4 * k) + j - layerDpSize k = c.val * (4 * k) + j := by omega
      simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, hdt, hdm, hnotdp, hsub, hdc, hdo, hj]
    have hmat := dpCircuit_eval_mat k hk ⟨j, hj⟩ (oddV c)
    dsimp [oddV] at hmat
    rw [evalGateAt_mul _ _ _ _ _ hgate (dpSlot_lt_total k t c.val j hk ht c.isLt hj)
          (matSlot_lt_total k j (2 * c.val + 1) hj (by omega)),
        hdp ⟨j, hj⟩, hmat]
    rfl
  have hacc : ∀ (r : ℕ) (hr : r < 2 * k),
      (dpCircuit k hk).evalGateAt MvPolynomial.X
        ⟨closeAccSlot k t c.val r, lt_of_lt_of_le (by have := (hdecodeC (2 * k + r) (by omega)).2.2.2.2.2; unfold closeAccSlot; omega) hA_le⟩ =
        ∑ i ∈ Finset.range (r + 1),
          if hi : i < 2 * k then
            dpVal (univSkewMat k) t c ⟨i, hi⟩ * univSkewMat k ⟨i, hi⟩ (oddV c)
          else 0 := by
    intro r
    induction r with
    | zero =>
      intro hr
      rcases hdecodeC (2 * k + 0) (by omega) with ⟨hdt, hdm, hdc, hdo, hgeH, hltA⟩
      have heq_idx : closeAccSlot k t c.val 0 = layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) := by
        unfold closeAccSlot; omega
      have hgate : (dpCircuit k hk).gate ⟨closeAccSlot k t c.val 0, lt_of_lt_of_le (by omega) hA_le⟩ =
          .add zeroSlot (closeProdSlot k t c.val 0) := by
        rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
        have hn0 : layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) ≠ 0 := by unfold headerSize at hgeH; omega
        have hn1 : layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) ≠ 1 := by unfold headerSize at hgeH; omega
        have hnot1 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot2 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot3 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + 0) < headerSize k) := by omega
        have hnotdp : ¬ (layerDpSize k + c.val * (4 * k) + (2 * k + 0) < layerDpSize k) := by omega
        have hsub : layerDpSize k + c.val * (4 * k) + (2 * k + 0) - layerDpSize k = c.val * (4 * k) + (2 * k + 0) := by omega
        simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, hdt, hdm, hnotdp, hsub, hdc, hdo]
        simp
      rw [evalGateAt_add _ _ _ _ _ hgate (dpCircuit k hk).size_pos
            (lt_of_lt_of_le (by have := (hdecodeC 0 (by omega)).2.2.2.2.2; unfold closeProdSlot; omega) hA_le),
          dpCircuit_eval_zero k hk, hprod 0 hr, zero_add]
      simp [hr]
    | succ r ihr =>
      intro hr
      rcases hdecodeC (2 * k + (r + 1)) (by omega) with ⟨hdt, hdm, hdc, hdo, hgeH, hltA⟩
      have heq_idx : closeAccSlot k t c.val (r + 1) = layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) := by
        unfold closeAccSlot; omega
      have hgate : (dpCircuit k hk).gate ⟨closeAccSlot k t c.val (r + 1), lt_of_lt_of_le (by omega) hA_le⟩ =
          .add (closeAccSlot k t c.val r) (closeProdSlot k t c.val (r + 1)) := by
        rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
        have hn0 : layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) ≠ 0 := by unfold headerSize at hgeH; omega
        have hn1 : layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) ≠ 1 := by unfold headerSize at hgeH; omega
        have hnot1 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot2 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot3 : ¬ (layerBase k t + layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) < headerSize k) := by omega
        have hnotdp : ¬ (layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) < layerDpSize k) := by omega
        have hsub : layerDpSize k + c.val * (4 * k) + (2 * k + (r + 1)) - layerDpSize k = c.val * (4 * k) + (2 * k + (r + 1)) := by omega
        have hnotm : ¬ (2 * k + (r + 1) < 2 * k) := by omega
        have hsubm : 2 * k + (r + 1) - 2 * k = r + 1 := by omega
        simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, hdt, hdm, hnotdp, hsub,
          hdc, hdo, hnotm, hsubm, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [evalGateAt_add _ _ _ _ _ hgate
            (lt_of_lt_of_le (by have := (hdecodeC (2 * k + r) (by omega)).2.2.2.2.2; unfold closeAccSlot; omega) hA_le)
            (lt_of_lt_of_le (by have := (hdecodeC (r + 1) (by omega)).2.2.2.2.2; unfold closeProdSlot; omega) hA_le),
          ihr (by omega), hprod (r + 1) hr, Finset.sum_range_succ _ (r + 1), dif_pos hr]
  have hres := hacc (2 * k - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hres
  change (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨closeAccSlot k t c.val (2 * k - 1), _⟩ = _
  rw [hres, ← Fin.sum_univ_eq_sum_range]
  unfold closeVal
  refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]

private lemma dpCircuit_eval_dp_zero (k : ℕ) (hk : 1 ≤ k) (c : Fin k) (u : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpSlot k 0 c.val u.val, dpSlot_lt_total k 0 c.val u.val hk hk c.isLt u.isLt⟩ =
      dpVal (univSkewMat k) 0 c u := by
  have hlt_dp := dpAccSlot_lt_layerDp k 0 c.val u.val (2 * k - 1) c.isLt u.isLt (by omega)
  have hrel : dpSlot k 0 c.val u.val - headerSize k =
      (c.val * (2 * k) + u.val) * (4 * k) + (4 * k - 1) := by unfold dpSlot dpAccSlot layerBase; omega
  have hlt_L : dpSlot k 0 c.val u.val - headerSize k < layerSize k := by unfold layerSize; omega
  have hdiv_t : (dpSlot k 0 c.val u.val - headerSize k) / layerSize k = 0 := Nat.div_eq_of_lt hlt_L
  have hmod_L : (dpSlot k 0 c.val u.val - headerSize k) % layerSize k =
      (c.val * (2 * k) + u.val) * (4 * k) + (4 * k - 1) := by rw [Nat.mod_eq_of_lt hlt_L, hrel]
  have hdiv_cell : ((c.val * (2 * k) + u.val) * (4 * k) + (4 * k - 1)) / (4 * k) = c.val * (2 * k) + u.val :=
    mul_add_div_eq (c.val * (2 * k) + u.val) (4 * k - 1) (4 * k) (by omega)
  have hmod_cell : ((c.val * (2 * k) + u.val) * (4 * k) + (4 * k - 1)) % (4 * k) = 4 * k - 1 :=
    mul_add_mod_eq (c.val * (2 * k) + u.val) (4 * k - 1) (4 * k) (by omega)
  have hdiv_c : (c.val * (2 * k) + u.val) / (2 * k) = c.val := mul_add_div_eq c.val u.val (2 * k) u.isLt
  have hmod_u : (c.val * (2 * k) + u.val) % (2 * k) = u.val := mul_add_mod_eq c.val u.val (2 * k) u.isLt
  have hge_H : headerSize k ≤ dpSlot k 0 c.val u.val := by unfold dpSlot dpAccSlot layerBase; omega
  have hlt_A : dpSlot k 0 c.val u.val < ansBase k := by
    have h1 := dpSlot_lt_layerBase_next k 0 c.val u.val hk c.isLt u.isLt
    unfold ansBase; unfold layerBase at h1; unfold layerSize at h1 ⊢; nlinarith
  have hgate : (dpCircuit k hk).gate ⟨dpSlot k 0 c.val u.val, dpSlot_lt_total k 0 c.val u.val hk hk c.isLt u.isLt⟩ =
      if u.val = 2 * c.val then .const 1 else .const 0 := by
    dsimp [dpCircuit, dpGateFn]
    have hn0 : dpSlot k 0 c.val u.val ≠ 0 := by unfold headerSize at hge_H; omega
    have hn1 : dpSlot k 0 c.val u.val ≠ 1 := by unfold headerSize at hge_H; omega
    have hnot1 : ¬ (dpSlot k 0 c.val u.val < 2 + (2 * k) ^ 2) := by unfold headerSize at hge_H; nlinarith
    have hnot2 : ¬ (dpSlot k 0 c.val u.val < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hge_H; nlinarith
    have hnot3 : ¬ (dpSlot k 0 c.val u.val < headerSize k) := by omega
    simp only [hn0, hn1, hnot1, hnot2, hnot3, hlt_A, ↓reduceIte, hdiv_t, hmod_L,
      hdiv_cell, hmod_cell, hdiv_c, hmod_u]
    have hin : (c.val * (2 * k) + u.val) * (4 * k) + (4 * k - 1) < layerDpSize k := by omega
    simp [hin]
  unfold dpVal
  by_cases hu : u = evenV c
  · have huv : u.val = 2 * c.val := by rw [hu]; rfl
    rw [if_pos huv] at hgate
    rw [evalGateAt_const _ _ _ 1 hgate]; simp [hu]
  · have huv : u.val ≠ 2 * c.val := fun h => hu (Fin.ext h)
    rw [if_neg huv] at hgate
    rw [evalGateAt_const _ _ _ 0 hgate]; simp [hu]

set_option maxHeartbeats 800000 in
private lemma dpCircuit_eval_dp_succ (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : t + 1 < k)
    (hdp_prev : ∀ (c : Fin k) (u : Fin (2 * k)),
      (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpSlot k t c.val u.val, dpSlot_lt_total k t c.val u.val hk (by omega) c.isLt u.isLt⟩ =
        dpVal (univSkewMat k) t c u)
    (hclose_prev : ∀ (c : Fin k),
      (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨closeSlot k t c.val, closeSlot_lt_total k t c.val hk (by omega) c.isLt⟩ =
        closeVal (univSkewMat k) t c)
    (c : Fin k) (u : Fin (2 * k)) :
    (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpSlot k (t + 1) c.val u.val, dpSlot_lt_total k (t + 1) c.val u.val hk ht c.isLt u.isLt⟩ =
      dpVal (univSkewMat k) (t + 1) c u := by
  have hLs : 0 < layerSize k := layerSize_pos k hk
  have hA_le : ansBase k ≤ totalDpSize k := by unfold totalDpSize; omega
  have hrel_dp : ∀ (off : ℕ) (hoff : off < 4 * k),
      layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + off - headerSize k =
        (t + 1) * layerSize k + ((c.val * (2 * k) + u.val) * (4 * k) + off) := by
    intro off _; unfold layerBase; omega
  have hlt_cell : ∀ (off : ℕ) (hoff : off < 4 * k),
      (c.val * (2 * k) + u.val) * (4 * k) + off < layerDpSize k := by
    intro off hoff; unfold layerDpSize
    have : c.val * (2 * k) + u.val + 1 ≤ k * (2 * k) := by nlinarith [c.isLt, u.isLt]
    nlinarith
  have hdecode : ∀ (off : ℕ) (hoff : off < 4 * k),
      let idx := layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + off
      (idx - headerSize k) / layerSize k = t + 1 ∧
      (idx - headerSize k) % layerSize k = (c.val * (2 * k) + u.val) * (4 * k) + off ∧
      ((c.val * (2 * k) + u.val) * (4 * k) + off) / (4 * k) = c.val * (2 * k) + u.val ∧
      ((c.val * (2 * k) + u.val) * (4 * k) + off) % (4 * k) = off ∧
      (c.val * (2 * k) + u.val) / (2 * k) = c.val ∧
      (c.val * (2 * k) + u.val) % (2 * k) = u.val ∧
      headerSize k ≤ idx ∧ idx < ansBase k := by
    intro off hoff
    have h1 := hrel_dp off hoff
    have h2 := hlt_cell off hoff
    have h2L : (c.val * (2 * k) + u.val) * (4 * k) + off < layerSize k := by unfold layerSize; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]; exact mul_add_div_eq (t + 1) _ (layerSize k) h2L
    · rw [h1]; exact mul_add_mod_eq (t + 1) _ (layerSize k) h2L
    · exact mul_add_div_eq (c.val * (2 * k) + u.val) off (4 * k) hoff
    · exact mul_add_mod_eq (c.val * (2 * k) + u.val) off (4 * k) hoff
    · exact mul_add_div_eq c.val u.val (2 * k) u.isLt
    · exact mul_add_mod_eq c.val u.val (2 * k) u.isLt
    · unfold layerBase; omega
    · unfold ansBase layerBase; nlinarith
  rw [dpVal_succ_eq_closeVal]
  by_cases hgt : c < pairOf u
  · simp only [hgt, ↓reduceIte]
    have hgt_val : c.val < u.val / 2 := hgt
    have hprod : ∀ (j : ℕ) (hj : j < 2 * k),
        (dpCircuit k hk).evalGateAt MvPolynomial.X
          ⟨dpProdSlot k (t + 1) c.val u.val j, lt_of_lt_of_le (by have := (hdecode j (by omega)).2.2.2.2.2.2.2; unfold dpProdSlot; omega) hA_le⟩ =
          dpVal (univSkewMat k) t c ⟨j, hj⟩ *
            (univSkewMat k ⟨j, hj⟩ (mate u) * (jSign (mate u) : MvPolynomial _ ℤ)) := by
      intro j hj
      rcases hdecode j (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
      have hgate : (dpCircuit k hk).gate ⟨dpProdSlot k (t + 1) c.val u.val j, lt_of_lt_of_le (by unfold dpProdSlot; omega) hA_le⟩ =
          .mul (dpSlot k t c.val j) (signedEdgeSlot k ⟨j, hj⟩ u) := by
        dsimp [dpCircuit, dpGateFn, dpProdSlot] at hdt hdm hgeH hltA ⊢
        have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + j ≠ 0 := by unfold headerSize at hgeH; omega
        have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + j ≠ 1 := by unfold headerSize at hgeH; omega
        have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + j < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + j < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + j < headerSize k) := by omega
        have hin := hlt_cell j (by omega)
        simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, hdt, hdm, hin,
          hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hj, hgt_val, u.isLt, and_self, ↓reduceDIte,
          Nat.add_sub_cancel]
      rw [evalGateAt_mul _ _ _ _ _ hgate (dpSlot_lt_total k t c.val j hk (by omega) c.isLt hj)
            (lt_of_lt_of_le (signedEdgeSlot_lt_header k ⟨j, hj⟩ u) (by dsimp only [dpCircuit]; unfold totalDpSize ansBase; omega)),
          hdp_prev c ⟨j, hj⟩, dpCircuit_eval_signedEdge k hk ⟨j, hj⟩ u]
    have hacc : ∀ (r : ℕ) (hr : r < 2 * k),
        (dpCircuit k hk).evalGateAt MvPolynomial.X
          ⟨dpAccSlot k (t + 1) c.val u.val r, lt_of_lt_of_le (by have := (hdecode (2 * k + r) (by omega)).2.2.2.2.2.2.2; unfold dpAccSlot; omega) hA_le⟩ =
          ∑ i ∈ Finset.range (r + 1),
            if hi : i < 2 * k then
              dpVal (univSkewMat k) t c ⟨i, hi⟩ *
                (univSkewMat k ⟨i, hi⟩ (mate u) * (jSign (mate u) : MvPolynomial _ ℤ))
            else 0 := by
      intro r
      induction r with
      | zero =>
        intro hr
        rcases hdecode (2 * k + 0) (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
        have heq_idx : dpAccSlot k (t + 1) c.val u.val 0 =
            layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) := by unfold dpAccSlot; omega
        have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val 0, lt_of_lt_of_le (by omega) hA_le⟩ =
            .add zeroSlot (dpProdSlot k (t + 1) c.val u.val 0) := by
          rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
          have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 0 := by unfold headerSize at hgeH; omega
          have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 1 := by unfold headerSize at hgeH; omega
          have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
          have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
          have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < headerSize k) := by omega
          have hin := hlt_cell (2 * k + 0) (by omega)
          simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, hdt, hdm, hin,
            hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hgt_val]
          simp
        rw [evalGateAt_add _ _ _ _ _ hgate (dpCircuit k hk).size_pos
              (lt_of_lt_of_le (by have := (hdecode 0 (by omega)).2.2.2.2.2.2.2; unfold dpProdSlot; omega) hA_le),
            dpCircuit_eval_zero k hk, hprod 0 hr, zero_add]
        simp [hr]
      | succ r ihr =>
        intro hr
        rcases hdecode (2 * k + (r + 1)) (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
        have heq_idx : dpAccSlot k (t + 1) c.val u.val (r + 1) =
            layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) := by unfold dpAccSlot; omega
        have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val (r + 1), lt_of_lt_of_le (by omega) hA_le⟩ =
            .add (dpAccSlot k (t + 1) c.val u.val r) (dpProdSlot k (t + 1) c.val u.val (r + 1)) := by
          rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
          have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 0 := by unfold headerSize at hgeH; omega
          have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 1 := by unfold headerSize at hgeH; omega
          have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
          have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
          have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < headerSize k) := by omega
          have hin := hlt_cell (2 * k + (r + 1)) (by omega)
          have hnotm : ¬ (2 * k + (r + 1) < 2 * k) := by omega
          have hsubm : 2 * k + (r + 1) - 2 * k = r + 1 := by omega
          simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
            hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnotm, hsubm, hgt_val, Nat.add_sub_cancel]
        rw [evalGateAt_add _ _ _ _ _ hgate
              (lt_of_lt_of_le (by have := (hdecode (2 * k + r) (by omega)).2.2.2.2.2.2.2; unfold dpAccSlot; omega) hA_le)
              (lt_of_lt_of_le (by have := (hdecode (r + 1) (by omega)).2.2.2.2.2.2.2; unfold dpProdSlot; omega) hA_le),
            ihr (by omega), hprod (r + 1) hr, Finset.sum_range_succ _ (r + 1), dif_pos hr]
    have hres := hacc (2 * k - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hres
    change (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpAccSlot k (t + 1) c.val u.val (2 * k - 1), _⟩ = _
    rw [hres, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  · by_cases hev : u = evenV c
    · simp only [hgt, ↓reduceIte, if_pos hev]
      have hnot_gt : ¬ (c.val < u.val / 2) := hgt
      have huv : u.val = 2 * c.val := by rw [hev]; rfl
      have hacc : ∀ (r : ℕ) (hr : r < 2 * k),
          (dpCircuit k hk).evalGateAt MvPolynomial.X
            ⟨dpAccSlot k (t + 1) c.val u.val r, lt_of_lt_of_le (by have := (hdecode (2 * k + r) (by omega)).2.2.2.2.2.2.2; unfold dpAccSlot; omega) hA_le⟩ =
            ∑ i ∈ Finset.range (r + 1),
              if hi : i < c.val then closeVal (univSkewMat k) t ⟨i, lt_trans hi c.isLt⟩ else 0 := by
        intro r
        induction r with
        | zero =>
          intro hr
          rcases hdecode (2 * k + 0) (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
          have heq_idx : dpAccSlot k (t + 1) c.val u.val 0 =
              layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) := by unfold dpAccSlot; omega
          by_cases hc0 : 0 < c.val
          · have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val 0, lt_of_lt_of_le (by omega) hA_le⟩ =
                .add zeroSlot (closeSlot k t 0) := by
              rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
              have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 0 := by unfold headerSize at hgeH; omega
              have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 1 := by unfold headerSize at hgeH; omega
              have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < headerSize k) := by omega
              have hin := hlt_cell (2 * k + 0) (by omega)
              simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
                hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnot_gt, Nat.add_sub_cancel]
              simp [huv, hc0]
            rw [evalGateAt_add _ _ _ _ _ hgate (dpCircuit k hk).size_pos
                  (closeSlot_lt_total k t 0 hk (by omega) (lt_trans hc0 c.isLt)),
                dpCircuit_eval_zero k hk, hclose_prev ⟨0, lt_trans hc0 c.isLt⟩, zero_add]
            simp [hc0]
          · have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val 0, lt_of_lt_of_le (by omega) hA_le⟩ = .const 0 := by
              rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
              have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 0 := by unfold headerSize at hgeH; omega
              have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) ≠ 1 := by unfold headerSize at hgeH; omega
              have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + 0) < headerSize k) := by omega
              have hin := hlt_cell (2 * k + 0) (by omega)
              simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
                hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnot_gt]
              simp [huv, hc0]
            rw [evalGateAt_const _ _ _ 0 hgate]
            simp [hc0]
        | succ r ihr =>
          intro hr
          rcases hdecode (2 * k + (r + 1)) (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
          have heq_idx : dpAccSlot k (t + 1) c.val u.val (r + 1) =
              layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) := by unfold dpAccSlot; omega
          by_cases hrc : r + 1 < c.val
          · have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val (r + 1), lt_of_lt_of_le (by omega) hA_le⟩ =
                .add (dpAccSlot k (t + 1) c.val u.val r) (closeSlot k t (r + 1)) := by
              rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
              have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 0 := by unfold headerSize at hgeH; omega
              have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 1 := by unfold headerSize at hgeH; omega
              have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < headerSize k) := by omega
              have hin := hlt_cell (2 * k + (r + 1)) (by omega)
              have hnotm : ¬ (2 * k + (r + 1) < 2 * k) := by omega
              have hsubm : 2 * k + (r + 1) - 2 * k = r + 1 := by omega
              simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
                hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnotm, hsubm, hnot_gt, Nat.add_sub_cancel]
              simp [huv, hrc]
            rw [evalGateAt_add _ _ _ _ _ hgate
                  (lt_of_lt_of_le (by have := (hdecode (2 * k + r) (by omega)).2.2.2.2.2.2.2; unfold dpAccSlot; omega) hA_le)
                  (closeSlot_lt_total k t (r + 1) hk (by omega) (lt_trans hrc c.isLt)),
                ihr (by omega), hclose_prev ⟨r + 1, lt_trans hrc c.isLt⟩, Finset.sum_range_succ _ (r + 1), dif_pos hrc]
          · have hgate : (dpCircuit k hk).gate ⟨dpAccSlot k (t + 1) c.val u.val (r + 1), lt_of_lt_of_le (by omega) hA_le⟩ =
                .add (dpAccSlot k (t + 1) c.val u.val r) zeroSlot := by
              rw [dpCircuit_gate_eq, heq_idx]; dsimp only [dpGateFn]
              have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 0 := by unfold headerSize at hgeH; omega
              have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) ≠ 1 := by unfold headerSize at hgeH; omega
              have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
              have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (r + 1)) < headerSize k) := by omega
              have hin := hlt_cell (2 * k + (r + 1)) (by omega)
              have hnotm : ¬ (2 * k + (r + 1) < 2 * k) := by omega
              have hsubm : 2 * k + (r + 1) - 2 * k = r + 1 := by omega
              simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
                hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnotm, hsubm, hnot_gt, Nat.add_sub_cancel]
              simp [huv, hrc]
            rw [evalGateAt_add _ _ _ _ _ hgate
                  (lt_of_lt_of_le (by have := (hdecode (2 * k + r) (by omega)).2.2.2.2.2.2.2; unfold dpAccSlot; omega) hA_le)
                  (dpCircuit k hk).size_pos,
                ihr (by omega), dpCircuit_eval_zero k hk, Finset.sum_range_succ _ (r + 1), dif_neg hrc]
      have hres := hacc (2 * k - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hres
      change (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpAccSlot k (t + 1) c.val u.val (2 * k - 1), _⟩ = _
      rw [hres]
      have hsplit : Finset.range (2 * k) = Finset.range k ∪ (Finset.range (2 * k) \ Finset.range k) := by
        rw [Finset.union_sdiff_of_subset (Finset.range_mono (by omega))]
      rw [hsplit, Finset.sum_union Finset.disjoint_sdiff]
      have hzero : ∑ i ∈ Finset.range (2 * k) \ Finset.range k,
          (if hi : i < c.val then closeVal (univSkewMat k) t ⟨i, lt_trans hi c.isLt⟩ else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi_ge : k ≤ i := by
          have := (Finset.mem_sdiff.mp hi).2; rw [Finset.mem_range] at this; omega
        have hnot : ¬ (i < c.val) := by omega
        simp [hnot]
      rw [hzero, add_zero, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => by
        by_cases hlt : i < c
        · have hv : i.val < c.val := hlt; simp [hlt, hv]
        · have hv : ¬ (i.val < c.val) := hlt; simp [hlt, hv]
    · simp only [hgt, hev, ↓reduceIte]
      have hnot_gt : ¬ (c.val < u.val / 2) := hgt
      have hnot_ev : u.val ≠ 2 * c.val := fun h => hev (Fin.ext h)
      rcases hdecode (2 * k + (2 * k - 1)) (by omega) with ⟨hdt, hdm, hdc, hdo, hdcc, hdu, hgeH, hltA⟩
      have heq_idx : dpSlot k (t + 1) c.val u.val =
          layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) := by
        unfold dpSlot dpAccSlot; omega
      have hgate : (dpCircuit k hk).gate ⟨dpSlot k (t + 1) c.val u.val, dpSlot_lt_total k (t + 1) c.val u.val hk ht c.isLt u.isLt⟩ = .const 0 := by
        change dpGateFn k hk (dpSlot k (t + 1) c.val u.val) = .const 0
        rw [heq_idx]; dsimp only [dpGateFn]
        have hn0 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) ≠ 0 := by unfold headerSize at hgeH; omega
        have hn1 : layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) ≠ 1 := by unfold headerSize at hgeH; omega
        have hnot1 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) < 2 + (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot2 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hgeH; nlinarith
        have hnot3 : ¬ (layerBase k (t + 1) + (c.val * (2 * k) + u.val) * (4 * k) + (2 * k + (2 * k - 1)) < headerSize k) := by omega
        have hin := hlt_cell (2 * k + (2 * k - 1)) (by omega)
        have hnotm : ¬ (2 * k + (2 * k - 1) < 2 * k) := by omega
        simp only [hn0, hn1, hnot1, hnot2, hnot3, hltA, ↓reduceIte, ↓reduceDIte, hdt, hdm, hin,
          hdc, hdo, hdcc, hdu, Nat.succ_ne_zero, hnotm, hnot_gt, hnot_ev]
      rw [evalGateAt_const _ _ _ 0 hgate]; simp

/-- Exact polynomial evaluation of `dpCircuit k`: equals `dpAns (univSkewMat k)`. -/
theorem dpCircuit_evalPoly (k : ℕ) (hk : 1 ≤ k) :
    (dpCircuit k hk).evalPoly = dpAns (univSkewMat k) := by
  have hlayer : ∀ (t : ℕ) (ht : t < k),
      (∀ (c : Fin k) (u : Fin (2 * k)),
        (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨dpSlot k t c.val u.val, dpSlot_lt_total k t c.val u.val hk ht c.isLt u.isLt⟩ =
          dpVal (univSkewMat k) t c u) ∧
      (∀ (c : Fin k),
        (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨closeSlot k t c.val, closeSlot_lt_total k t c.val hk ht c.isLt⟩ =
          closeVal (univSkewMat k) t c) := by
    intro t
    induction t with
    | zero =>
      intro ht
      exact ⟨fun c u => dpCircuit_eval_dp_zero k hk c u,
        fun c => dpCircuit_eval_close k hk 0 ht c (fun u => dpCircuit_eval_dp_zero k hk c u)⟩
    | succ t iht =>
      intro ht
      rcases iht (by omega) with ⟨hdp_prev, hclose_prev⟩
      have hdp_cur := fun c u => dpCircuit_eval_dp_succ k hk t ht hdp_prev hclose_prev c u
      exact ⟨hdp_cur, fun c => dpCircuit_eval_close k hk (t + 1) ht c (hdp_cur c)⟩
  have hclose_last := (hlayer (k - 1) (by omega)).2
  have hans : ∀ (r : ℕ) (hr : r < k),
      (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨ansSlot k r, by dsimp only [dpCircuit]; unfold ansSlot totalDpSize; omega⟩ =
        ∑ i ∈ Finset.range (r + 1),
          if hi : i < k then closeVal (univSkewMat k) (k - 1) ⟨i, hi⟩ else 0 := by
    intro r
    induction r with
    | zero =>
      intro hr
      have hgate : (dpCircuit k hk).gate ⟨ansSlot k 0, by dsimp only [dpCircuit]; unfold ansSlot totalDpSize; omega⟩ =
          .add zeroSlot (closeSlot k (k - 1) 0) := by
        dsimp [dpCircuit, dpGateFn, ansSlot]
        have hge : headerSize k ≤ ansBase k := by unfold ansBase; omega
        have hn0 : ansBase k ≠ 0 := by unfold headerSize at hge; omega
        have hn1 : ansBase k ≠ 1 := by unfold headerSize at hge; omega
        have hnot1 : ¬ (ansBase k < 2 + (2 * k) ^ 2) := by unfold headerSize at hge; nlinarith
        have hnot2 : ¬ (ansBase k < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hge; nlinarith
        have hnot3 : ¬ (ansBase k < headerSize k) := by omega
        simp [hn0, hn1, hnot1, hnot2, hnot3]
      rw [evalGateAt_add _ _ _ _ _ hgate (dpCircuit k hk).size_pos (closeSlot_lt_total k (k - 1) 0 hk (by omega) hr),
          dpCircuit_eval_zero k hk, hclose_last ⟨0, hr⟩, zero_add]
      simp [hr]
    | succ r ihr =>
      intro hr
      have hgate : (dpCircuit k hk).gate ⟨ansSlot k (r + 1), by dsimp only [dpCircuit]; unfold ansSlot totalDpSize; omega⟩ =
          .add (ansSlot k r) (closeSlot k (k - 1) (r + 1)) := by
        dsimp [dpCircuit, dpGateFn, ansSlot]
        have hge : headerSize k ≤ ansBase k := by unfold ansBase; omega
        have hn1 : ansBase k + (r + 1) ≠ 1 := by unfold headerSize at hge; omega
        have hnot1 : ¬ (ansBase k + (r + 1) < 2 + (2 * k) ^ 2) := by unfold headerSize at hge; nlinarith
        have hnot2 : ¬ (ansBase k + (r + 1) < 2 + 2 * (2 * k) ^ 2) := by unfold headerSize at hge; nlinarith
        have hnot3 : ¬ (ansBase k + (r + 1) < headerSize k) := by omega
        have hnot4 : ¬ (ansBase k + (r + 1) < ansBase k) := by omega
        simp [hn1, hnot1, hnot2, hnot3, hnot4]
      rw [evalGateAt_add _ _ _ _ _ hgate (by dsimp only [dpCircuit]; unfold ansSlot totalDpSize; omega)
            (closeSlot_lt_total k (k - 1) (r + 1) hk (by omega) hr),
          ihr (by omega), hclose_last ⟨r + 1, hr⟩, Finset.sum_range_succ _ (r + 1), dif_pos hr]
  have hfinal := hans (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk] at hfinal
  change (dpCircuit k hk).evalGateAt MvPolynomial.X ⟨ansSlot k (k - 1), _⟩ = dpAns (univSkewMat k)
  rw [hfinal, ← Fin.sum_univ_eq_sum_range]
  unfold dpAns
  refine Finset.sum_congr rfl fun c _ => by simp [c.isLt]

/-- **Unconditional `[MSV04]` Theorem:** there exists `C_const ≥ 1` (`C_const = 27`) such that for
every `k ≥ 1`, there is an explicit division-free `{0, ±1}`-constant `IntCircuit` of size
`≤ C_const * k^4` computing `rename (upperPairEquiv (2 * k)) (universalPfaffian k)`. -/
theorem pfaffian_clow_circuit_exists :
    ∃ C_const : ℕ, 1 ≤ C_const ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k),
        ∃ C_pf : IntCircuit (Fintype.card (UpperPair (2 * k))),
          C_pf.UsesOnlyUnitConstants ∧
          C_pf.size ≤ C_const * k ^ 4 ∧
          C_pf.evalPoly = MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k) := by
  refine ⟨27, by omega, fun k hk => ⟨dpCircuit k hk, dpCircuit_usesOnlyUnitConstants k hk,
    dpCircuit_size_le k hk, ?_⟩⟩
  rw [dpCircuit_evalPoly k hk, dpAns_eq_pfaffian hk (univSkewMat_isSkewSymm k), pfaffian_univSkewMat]

end ExactMatching.Proofs.PfaffianClow
