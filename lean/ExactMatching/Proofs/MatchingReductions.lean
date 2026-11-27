/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.PfaffianMatching
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-!
# Proofs for Theorem 2 (Odd `n`, edge-deletion self-reduction, and cyclic-group embeddings)

Proves:
- `step_thm2_odd_n_proved`: odd-vertex graphs have no perfect matching.
- `step_thm2c_self_reduction_proved`: edge-deletion self-reduction recovers a valid
  `γ*`-matching in at most `|E(G)| + 1 ≤ n^2` oracle calls.
- `step_thm2a_embedding_proved`: Exact Matching embedding into `ZMod (k + 1)` (`n = 2k`).
- `step_thm2b_embedding_proved`: bounded integer-weight shifted embedding into
  `ZMod (2kW + 1)` (`n = 2k`).
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-- A non-diagonal unordered pair `s(u, v)` has exactly 2 incident vertices in `Fin n`. -/
private theorem sym2_mem_filter_card_eq_two {n : ℕ} {e : Sym2 (Fin n)} (hnd : ¬ e.IsDiag) :
    (Finset.univ.filter (fun v : Fin n => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := fun h => hnd (by subst h; exact Sym2.mk_isDiag_iff.mpr rfl)
    have hset : Finset.univ.filter (fun x : Fin n => x ∈ s(u, v)) = {u, v} := by
      ext x
      simp [Sym2.mem_iff]
    rw [hset, Finset.card_pair huv]

/-- Every perfect matching of a graph on `n` vertices satisfies `2 * M.card = n`. -/
theorem perfectMatching_two_mul_card {n : ℕ} {G : SimpleGraph (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching G M) :
    2 * M.card = n := by
  have hdouble :
      ∑ v : Fin n, (M.filter (fun e => v ∈ e)).card =
      ∑ e ∈ M, (Finset.univ.filter (fun v : Fin n => v ∈ e)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hlhs : ∑ v : Fin n, (M.filter (fun e => v ∈ e)).card = n := by
    simp [hM.2]
  have hrhs : ∑ e ∈ M, (Finset.univ.filter (fun v : Fin n => v ∈ e)).card = 2 * M.card := by
    have hall : ∀ e ∈ M, (Finset.univ.filter (fun v : Fin n => v ∈ e)).card = 2 := by
      intro e he
      exact sym2_mem_filter_card_eq_two (G.not_isDiag_of_mem_edgeSet (hM.1 e he))
    rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- Odd-vertex graphs have no perfect matching. -/
theorem step_thm2_odd_n_proved {n : ℕ} (hodd : Odd n) (G : SimpleGraph (Fin n))
    (M : Finset (Sym2 (Fin n))) : ¬ IsPerfectMatching G M := by
  intro hM
  have h2 := perfectMatching_two_mul_card hM
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem deleteEdge_le {n : ℕ} (H : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    deleteEdge H e ≤ H :=
  fun _ _ h => h.1

private theorem isPerfectMatching_mono {n : ℕ} {H₁ H₂ : SimpleGraph (Fin n)}
    (hle : H₁ ≤ H₂) {M : Finset (Sym2 (Fin n))} (hM : IsPerfectMatching H₁ M) :
    IsPerfectMatching H₂ M :=
  ⟨fun e he => SimpleGraph.edgeSet_mono hle (hM.1 e he), hM.2⟩

private theorem mem_edgeSet_deleteEdge {n : ℕ} (H : SimpleGraph (Fin n)) (e e' : Sym2 (Fin n)) :
    e' ∈ (deleteEdge H e).edgeSet ↔ e' ∈ H.edgeSet ∧ e' ≠ e := by
  induction e' using Sym2.ind with
  | _ u v =>
    simp [SimpleGraph.mem_edgeSet, deleteEdge]

private theorem selfReduce_invariant {n : ℕ}
    {Γ : Type*} [AddCommGroup Γ]
    (w : Sym2 (Fin n) → Γ) (γstar : Γ)
    (oracle : SimpleGraph (Fin n) → Bool)
    (horacle : ∀ H : SimpleGraph (Fin n),
      oracle H = true ↔
        ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar) :
    ∀ (edges : List (Sym2 (Fin n))) (H₀ : SimpleGraph (Fin n)),
      (∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H₀ M ∧ ∑ e ∈ M, w e = γstar) →
      let H := selfReduce oracle H₀ edges
      H ≤ H₀ ∧
      (∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar) ∧
      (∀ e ∈ edges, e ∈ H.edgeSet →
        ∀ M : Finset (Sym2 (Fin n)), IsPerfectMatching H M → ∑ x ∈ M, w x = γstar → e ∈ M)
  | [], H₀, hex => by
    exact ⟨le_rfl, hex, fun _ h => by simp at h⟩
  | e :: rest, H₀, hex => by
    dsimp only [selfReduce, List.foldl_cons]
    let H' := deleteEdge H₀ e
    let H₁ := if oracle H' then H' else H₀
    have hH₁_le : H₁ ≤ H₀ := by
      dsimp only [H₁]
      split_ifs
      · exact deleteEdge_le H₀ e
      · exact le_rfl
    have hH₁_ex : ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H₁ M ∧ ∑ x ∈ M, w x = γstar := by
      dsimp only [H₁]
      split_ifs with h
      · exact (horacle H').mp h
      · exact hex
    have ih := selfReduce_invariant w γstar oracle horacle rest H₁ hH₁_ex
    obtain ⟨hEnd_le_H₁, hEnd_ex, hEnd_rest⟩ := ih
    refine ⟨le_trans hEnd_le_H₁ hH₁_le, hEnd_ex, ?_⟩
    intro x hx hx_in M hM_end hM_sum
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx_rest
    · -- `x = e`: if `e ∉ M`, then `M` is a valid matching of `H' = deleteEdge H₀ e`, so `e` would have been deleted
      by_contra he_not_M
      have hor_false : oracle H' = false := by
        cases h : oracle H'
        · rfl
        · exfalso
          have hH₁_eq : H₁ = H' := by simp [H₁, h]
          have hle_H' : selfReduce oracle H₁ rest ≤ H' := hH₁_eq ▸ hEnd_le_H₁
          have hmem_H' : x ∈ H'.edgeSet := SimpleGraph.edgeSet_mono hle_H' hx_in
          exact ((mem_edgeSet_deleteEdge H₀ x x).mp hmem_H').2 rfl
      have hM_H' : IsPerfectMatching H' M := by
        refine ⟨?_, hM_end.2⟩
        intro y hy
        rw [mem_edgeSet_deleteEdge]
        refine ⟨SimpleGraph.edgeSet_mono (le_trans hEnd_le_H₁ hH₁_le) (hM_end.1 y hy), ?_⟩
        intro hye
        exact he_not_M (hye ▸ hy)
      have hor_true : oracle H' = true := (horacle H').mpr ⟨M, hM_H', hM_sum⟩
      rw [hor_false] at hor_true
      exact Bool.false_ne_true hor_true
    · exact hEnd_rest x hx_rest hx_in M hM_end hM_sum

/-- Theorem 2(c) edge-deletion self-reduction. -/
theorem step_thm2c_self_reduction_proved {n : ℕ} (hn : 2 ≤ n)
    {Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Γ) (γstar : Γ)
    (oracle : SimpleGraph (Fin n) → Bool)
    (horacle : ∀ H : SimpleGraph (Fin n),
      oracle H = true ↔
        ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)
    (edges : List (Sym2 (Fin n))) (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
    (hnodup : edges.Nodup)
    (hex : ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching G M ∧ ∑ e ∈ M, w e = γstar) :
    let H := selfReduce oracle G edges
    ∃ M : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
      IsPerfectMatching G M ∧
      ∑ e ∈ M, w e = γstar ∧
      edges.length + 1 ≤ n ^ 2 := by
  obtain ⟨hH_le, ⟨M, hM_H, hM_sum⟩, hH_ess⟩ :=
    selfReduce_invariant w γstar oracle horacle edges G hex
  refine ⟨M, ?_, isPerfectMatching_mono hH_le hM_H, hM_sum, ?_⟩
  · intro e
    constructor
    · intro he_H
      have he_G : e ∈ G.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hH_le he_H)
      exact hH_ess e ((hedges e).mpr he_G) he_H M hM_H hM_sum
    · intro he_M
      exact hM_H.1 e he_M
  · -- `edges.length + 1 ≤ n ^ 2`
    have hlen_eq : edges.length = G.edgeFinset.card := by
      have hset : edges.toFinset = G.edgeFinset := by
        ext e
        simp [hedges]
      rw [← hset, List.toFinset_card_of_nodup hnodup]
    rw [hlen_eq]
    -- Inject `G.edgeFinset` into off-diagonal pairs `(u, v) : Fin n × Fin n` (`u < v`)
    let offDiag : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
    have hcard_le : G.edgeFinset.card ≤ offDiag.card := by
      let f : Fin n × Fin n → Sym2 (Fin n) := fun p => s(p.1, p.2)
      have hsub : G.edgeFinset ⊆ offDiag.image f := by
        intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
          have hne : u ≠ v := G.ne_of_adj hadj
          rw [Finset.mem_image]
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
          · exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, Sym2.eq_swap⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hoff_lt : offDiag.card < n ^ 2 := by
      have hdiag : (⟨0, by omega⟩, ⟨0, by omega⟩) ∉ offDiag := by
        simp [offDiag]
      have hssub : offDiag ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h => hdiag (h ▸ Finset.mem_univ _)⟩
      have hlt := Finset.card_lt_card hssub
      simpa [Fintype.card_prod, Fintype.card_fin, sq] using hlt
    omega

/-- Bijection between `UpperEdge G` with `s(u, v) ∈ M` and `M`, rewriting `matchingLabelSum`
as a sum over `e ∈ M`. -/
private theorem sum_upperEdge_matching_eq {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Finset (Sym2 (Fin n))) (hM : ∀ e ∈ M, e ∈ G.edgeSet)
    (f : Sym2 (Fin n) → Γ) :
    (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then f s(e.val.val.1, e.val.val.2) else 0) =
      ∑ e ∈ M, f e := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun e _ => s(e.val.val.1, e.val.val.2)) ?_ ?_ ?_ ?_
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e₁ _ e₂ _ heq
    have h1 : e₁.val.val.1 < e₁.val.val.2 := e₁.val.property
    have h2 : e₂.val.val.1 < e₂.val.val.2 := e₂.val.property
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Subtype.ext (Subtype.ext (Prod.ext ha hb))
    · exfalso
      rw [ha, hb] at h1
      exact lt_asymm h1 h2
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := hM s(u, v) he
      have hne : u ≠ v := G.ne_of_adj hadj
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨⟨⟨(u, v), hlt⟩, hadj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
      · refine ⟨⟨⟨(v, u), hgt⟩, G.symm.symm _ _ hadj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Sym2.eq_swap⟩
        rwa [Sym2.eq_swap]
  · intro _ _; rfl

/-- Theorem 2(a) Exact Matching cyclic-group embedding into `ZMod (k + 1)` (`n = 2k ≥ 2`). -/
theorem step_thm2a_embedding_proved {k : ℕ} (hk : 1 ≤ k)
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (R : Finset (Sym2 (Fin (2 * k)))) (target : ℕ) (htarget : target ≤ k) :
    (∀ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching G M →
      ((M ∩ R).card = target ↔
        matchingLabelSum G (exactMatchingLabel G R) M = (target : ZMod (k + 1)))) ∧
    2 * k + (k + 1) ≤ (2 * k) ^ 2 := by
  constructor
  · intro M hM
    have hMcard : M.card = k := by
      have h2 := perfectMatching_two_mul_card hM
      omega
    have hsum : matchingLabelSum G (exactMatchingLabel G R) M = ((M ∩ R).card : ZMod (k + 1)) := by
      unfold matchingLabelSum exactMatchingLabel
      rw [sum_upperEdge_matching_eq G M hM.1 (fun e => if e ∈ R then (1 : ZMod (k + 1)) else 0)]
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum, ZMod.natCast_eq_natCast_iff']
    have hlt1 : (M ∩ R).card < k + 1 := by
      have hle : (M ∩ R).card ≤ M.card := Finset.card_le_card Finset.inter_subset_left
      omega
    have hlt2 : target < k + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  · nlinarith

/-- Theorem 2(b) bounded integer-weight shifted cyclic-group embedding into `ZMod (2kW + 1)`. -/
theorem step_thm2b_embedding_proved {k : ℕ} (hk : 1 ≤ k) (W : ℕ)
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → ℤ) (hw : ∀ e, -(W : ℤ) ≤ w e ∧ w e ≤ (W : ℤ))
    (target : ℤ) (htarget : -(k * W : ℤ) ≤ target ∧ target ≤ (k * W : ℤ)) :
    (∀ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching G M →
      ((∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e else 0) = target ↔
        matchingLabelSum G (boundedWeightLabel W G w) M =
          ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)))) ∧
    2 * k + (2 * k * W + 1) ≤ (2 * k + W) ^ 2 := by
  constructor
  · intro M hM
    have hMcard : M.card = k := by
      have h2 := perfectMatching_two_mul_card hM
      omega
    let S : ℤ := ∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e else 0
    have hcount_edges :
        (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (1 : ℤ) else 0) = (k : ℤ) := by
      rw [sum_upperEdge_matching_eq G M hM.1 (fun _ => (1 : ℤ))]
      simp [hMcard]
    have hS_shift :
        (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e + (W : ℤ) else 0) =
          S + (k * W : ℤ) := by
      have hsplit :
          (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e + (W : ℤ) else 0) =
          (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e else 0) +
          (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (W : ℤ) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> ring
      rw [hsplit]
      have hWsum :
          (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (W : ℤ) else 0) =
            (k * W : ℤ) := by
        have h1 : (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (W : ℤ) else 0) =
            (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (1 : ℤ) else 0) * (W : ℤ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          split_ifs <;> ring
        rw [h1, hcount_edges]
      rw [hWsum]
    have hsum_cast :
        matchingLabelSum G (boundedWeightLabel W G w) M =
          ((S + (k * W : ℤ)) : ZMod (2 * k * W + 1)) := by
      unfold matchingLabelSum boundedWeightLabel
      have hcast0 : ((S + (k * W : ℤ)) : ZMod (2 * k * W + 1)) =
          ((S + (k : ℤ) * (W : ℤ) : ℤ) : ZMod (2 * k * W + 1)) := by push_cast; rfl
      rw [hcast0, ← hS_shift, Int.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
    have hS_nonneg : 0 ≤ S + (k * W : ℤ) := by
      rw [← hS_shift]
      refine Finset.sum_nonneg fun e _ => ?_
      split_ifs
      · linarith [(hw e).1]
      · exact le_rfl
    have hS_le : S + (k * W : ℤ) ≤ (2 * k * W : ℤ) := by
      rw [← hS_shift]
      calc
        (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e + (W : ℤ) else 0)
            ≤ ∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (2 * W : ℤ) else 0 := by
              refine Finset.sum_le_sum fun e _ => ?_
              split_ifs
              · linarith [(hw e).2]
              · exact le_rfl
        _ = (∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then (1 : ℤ) else 0) * (2 * W : ℤ) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun e _ => ?_
              split_ifs <;> ring
        _ = (2 * k * W : ℤ) := by rw [hcount_edges]; ring
    rw [hsum_cast]
    have hiff : ((S + (k * W : ℤ)) : ZMod (2 * k * W + 1)) =
        ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)) ↔
        S + (k * W : ℤ) = target + (k * W : ℤ) := by
      have hcast1 : ((S + (k * W : ℤ)) : ZMod (2 * k * W + 1)) =
          ((S + (k : ℤ) * (W : ℤ) : ℤ) : ZMod (2 * k * W + 1)) := by push_cast; rfl
      have hcast2 : ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)) =
          ((target + (k : ℤ) * (W : ℤ) : ℤ) : ZMod (2 * k * W + 1)) := by push_cast; rfl
      rw [hcast1, hcast2, ZMod.intCast_eq_intCast_iff_dvd_sub]
      constructor
      · intro hdvd
        obtain ⟨q, hq⟩ := hdvd
        have hdiff_lt : |(target + (k * W : ℤ)) - (S + (k * W : ℤ))| < (2 * k * W + 1 : ℤ) := by
          rw [abs_lt]
          constructor <;> linarith [htarget.1, htarget.2, hS_nonneg, hS_le]
        have hq0 : q = 0 := by
          by_contra hqne
          have habs : 1 ≤ |q| := Int.one_le_abs hqne
          have hmul : ((2 * k * W + 1 : ℕ) : ℤ) ≤ |((2 * k * W + 1 : ℕ) : ℤ) * q| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            nlinarith
          rw [← hq] at hmul
          have : (2 * k * W + 1 : ℤ) ≤ |(target + (k * W : ℤ)) - (S + (k * W : ℤ))| := by
            exact_mod_cast hmul
          linarith
        subst hq0
        linarith
      · intro h; rw [h, sub_self]; exact dvd_zero _
    rw [hiff]
    constructor <;> intro h <;> linarith
  · nlinarith

end ExactMatching.Proofs
