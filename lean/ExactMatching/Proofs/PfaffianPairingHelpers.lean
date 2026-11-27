/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.PfaffianMatching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators

/-!
# Ordered pairing helpers for the Pfaffian clow-sequence proof

Basic properties of `OrderedPairing k` (`fst`, `snd`, `edge`, `edgeFinset_injective`) and
surjectivity onto perfect matchings (`exists_orderedPairing_of_isPerfectMatching`).
-/

namespace ExactMatching

open scoped BigOperators

/-- The `i`-th first endpoint `u_i = m.perm (2i)` of an ordered pairing. -/
def OrderedPairing.fst {k : ℕ} (m : OrderedPairing k) (i : Fin k) : Fin (2 * k) :=
  m.perm ⟨2 * i.val, by omega⟩

/-- The `i`-th second endpoint `v_i = m.perm (2i + 1)` of an ordered pairing. -/
def OrderedPairing.snd {k : ℕ} (m : OrderedPairing k) (i : Fin k) : Fin (2 * k) :=
  m.perm ⟨2 * i.val + 1, by omega⟩

/-- The `i`-th undirected edge `s(u_i, v_i)` of an ordered pairing. -/
def OrderedPairing.edge {k : ℕ} (m : OrderedPairing k) (i : Fin k) : Sym2 (Fin (2 * k)) :=
  s(m.fst i, m.snd i)

lemma OrderedPairing.edgeFinset_eq {k : ℕ} (m : OrderedPairing k) :
    m.edgeFinset = Finset.univ.image m.edge := rfl

lemma OrderedPairing.fst_lt_snd {k : ℕ} (m : OrderedPairing k) (i : Fin k) :
    m.fst i < m.snd i := m.pair_lt i

lemma OrderedPairing.fst_strictMono {k : ℕ} (m : OrderedPairing k) :
    StrictMono m.fst := fun i j hij => m.fst_mono i j hij

lemma OrderedPairing.edge_injective {k : ℕ} (m : OrderedPairing k) :
    Function.Injective m.edge := by
  intro i j hij
  have hmem : m.fst i ∈ s(m.fst j, m.snd j) := by
    change m.fst i ∈ m.edge j
    rw [← hij]; exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp hmem with h1 | h2
  · exact m.fst_strictMono.injective h1
  · have : (⟨2 * i.val, by omega⟩ : Fin (2 * k)) = ⟨2 * j.val + 1, by omega⟩ :=
      m.perm.injective h2
    have hval := congrArg Fin.val this
    dsimp at hval
    omega

lemma OrderedPairing.mem_edge_iff {k : ℕ} (m : OrderedPairing k) (v : Fin (2 * k)) (i : Fin k) :
    v ∈ m.edge i ↔ v = m.fst i ∨ v = m.snd i :=
  Sym2.mem_iff

lemma OrderedPairing.isPerfectMatching_iff {k : ℕ} (G : SimpleGraph (Fin (2 * k)))
    (m : OrderedPairing k) :
    IsPerfectMatching G m.edgeFinset ↔ ∀ i : Fin k, G.Adj (m.fst i) (m.snd i) := by
  constructor
  · intro ⟨hsub, _⟩ i
    have hmem : m.edge i ∈ m.edgeFinset := Finset.mem_image_of_mem m.edge (Finset.mem_univ i)
    exact hsub (m.edge i) hmem
  · intro hadj
    refine ⟨?_, ?_⟩
    · intro e he
      rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
      exact hadj i
    · intro v
      let idx : Fin (2 * k) := m.perm.symm v
      let i0 : Fin k := ⟨idx.val / 2, by omega⟩
      have hv_in : m.edge i0 ∈ m.edgeFinset.filter (fun e => v ∈ e) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem m.edge (Finset.mem_univ i0), ?_⟩
        rw [OrderedPairing.mem_edge_iff]
        have hperm : m.perm idx = v := m.perm.apply_symm_apply v
        by_cases heven : idx.val % 2 = 0
        · left
          unfold OrderedPairing.fst
          have : (⟨2 * i0.val, by omega⟩ : Fin (2 * k)) = idx := by
            ext; dsimp [i0]; omega
          rw [this, hperm]
        · right
          unfold OrderedPairing.snd
          have : (⟨2 * i0.val + 1, by omega⟩ : Fin (2 * k)) = idx := by
            ext; dsimp [i0]; omega
          rw [this, hperm]
      refine Finset.card_eq_one.mpr ⟨m.edge i0, Finset.eq_singleton_iff_unique_mem.mpr ⟨hv_in, ?_⟩⟩
      intro e he
      rcases Finset.mem_filter.mp he with ⟨he_img, hv_e⟩
      rcases Finset.mem_image.mp he_img with ⟨j, _, rfl⟩
      have hidx_eq : j = i0 := by
        change v ∈ m.edge j at hv_e
        rw [OrderedPairing.mem_edge_iff] at hv_e
        have hperm : m.perm idx = v := m.perm.apply_symm_apply v
        rcases hv_e with h1 | h2
        · have heq : idx = ⟨2 * j.val, by omega⟩ := m.perm.injective (hperm.trans h1)
          have hval : idx.val = 2 * j.val := congrArg Fin.val heq
          ext; dsimp [i0]; omega
        · have heq : idx = ⟨2 * j.val + 1, by omega⟩ := m.perm.injective (hperm.trans h2)
          have hval : idx.val = 2 * j.val + 1 := congrArg Fin.val heq
          ext; dsimp [i0]; omega
      exact congrArg m.edge hidx_eq

lemma OrderedPairing.edgeFinset_injective {k : ℕ} :
    Function.Injective (OrderedPairing.edgeFinset (k := k)) := by
  intro m₁ m₂ h
  have hpair_eq : ∀ i : Fin k, ∃ j : Fin k, m₁.fst i = m₂.fst j ∧ m₁.snd i = m₂.snd j := by
    intro i
    have hmem : m₁.edge i ∈ m₂.edgeFinset := by
      rw [← h]; exact Finset.mem_image_of_mem m₁.edge (Finset.mem_univ i)
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    change s(m₂.fst j, m₂.snd j) = s(m₁.fst i, m₁.snd i) at hj
    rcases Sym2.eq_iff.mp hj.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨j, h1, h2⟩
    · exfalso
      have hlt1 := m₁.fst_lt_snd i
      have hlt2 := m₂.fst_lt_snd j
      rw [h1, h2] at hlt1
      exact lt_asymm hlt1 hlt2
  have hfst_img : Finset.univ.image m₁.fst = Finset.univ.image m₂.fst := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      rcases hpair_eq i with ⟨j, hj, _⟩
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      have hmem : m₂.edge j ∈ m₁.edgeFinset := by
        rw [h]; exact Finset.mem_image_of_mem m₂.edge (Finset.mem_univ j)
      rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
      change s(m₁.fst i, m₁.snd i) = s(m₂.fst j, m₂.snd j) at hi
      rcases Sym2.eq_iff.mp hi with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact ⟨i, h1⟩
      · exfalso
        have hlt1 := m₁.fst_lt_snd i
        have hlt2 := m₂.fst_lt_snd j
        rw [h1, h2] at hlt1
        exact lt_asymm hlt1 hlt2
  have hfst_eq : m₁.fst = m₂.fst := by
    have hcard1 : (Finset.univ.image m₁.fst).card = k := by
      rw [Finset.card_image_of_injective _ m₁.fst_strictMono.injective, Finset.card_fin]
    have h1 : m₁.fst = (Finset.univ.image m₁.fst).orderEmbOfFin hcard1 :=
      Finset.orderEmbOfFin_unique hcard1
        (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) m₁.fst_strictMono
    have hcard2 : (Finset.univ.image m₂.fst).card = k := by
      rw [Finset.card_image_of_injective _ m₂.fst_strictMono.injective, Finset.card_fin]
    have h2 : m₂.fst = (Finset.univ.image m₂.fst).orderEmbOfFin hcard2 :=
      Finset.orderEmbOfFin_unique hcard2
        (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) m₂.fst_strictMono
    funext i
    rw [congrFun h1 i, congrFun h2 i]
    generalize hS1 : Finset.univ.image m₁.fst = S1 at hcard1 hfst_img ⊢
    subst hfst_img
    rfl
  have hsnd_eq : m₁.snd = m₂.snd := by
    funext i
    rcases hpair_eq i with ⟨j, hfj, hsj⟩
    rw [hfst_eq] at hfj
    have hij : i = j := m₂.fst_strictMono.injective hfj
    subst hij
    exact hsj
  have hperm_eq : m₁.perm = m₂.perm := by
    ext t
    by_cases heven : t.val % 2 = 0
    · let i : Fin k := ⟨t.val / 2, by omega⟩
      have ht : t = ⟨2 * i.val, by omega⟩ := by ext; dsimp [i]; omega
      rw [ht]
      exact congrArg Fin.val (congrFun hfst_eq i)
    · let i : Fin k := ⟨t.val / 2, by omega⟩
      have ht : t = ⟨2 * i.val + 1, by omega⟩ := by ext; dsimp [i]; omega
      rw [ht]
      exact congrArg Fin.val (congrFun hsnd_eq i)
  cases m₁; cases m₂; simp only [OrderedPairing.mk.injEq] at hperm_eq ⊢; exact hperm_eq

end ExactMatching


namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### 3. Surjectivity of `OrderedPairing.edgeFinset` onto perfect matchings of `G` -/

lemma exists_orderedPairing_of_isPerfectMatching {k : ℕ}
    (G : SimpleGraph (Fin (2 * k))) (M : Finset (Sym2 (Fin (2 * k))))
    (hM : IsPerfectMatching G M) :
    ∃ m : OrderedPairing k, m.edgeFinset = M := by
  classical
  have hne : ∀ e ∈ M, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hM.1 e he)
  let minEnd : Sym2 (Fin (2 * k)) → Fin (2 * k) :=
    Sym2.lift ⟨fun a b => min a b, fun a b => min_comm a b⟩
  let maxEnd : Sym2 (Fin (2 * k)) → Fin (2 * k) :=
    Sym2.lift ⟨fun a b => max a b, fun a b => max_comm a b⟩
  have hmk : ∀ e ∈ M, s(minEnd e, maxEnd e) = e ∧ minEnd e < maxEnd e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by
        intro h; subst h; exact hne s(a, a) he (Sym2.mk_isDiag_iff.mpr rfl)
      simp only [minEnd, maxEnd, Sym2.lift_mk]
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨by rw [min_eq_left hlt.le, max_eq_right hlt.le],
               by rwa [min_eq_left hlt.le, max_eq_right hlt.le]⟩
      · exact ⟨by rw [min_eq_right hgt.le, max_eq_left hgt.le, Sym2.eq_swap],
               by rwa [min_eq_right hgt.le, max_eq_left hgt.le]⟩
  have hcardM : M.card = k := by
    have hsum : ∑ v : Fin (2 * k), (M.filter (fun e => v ∈ e)).card = 2 * k := by
      simp [hM.2]
    have hdouble : ∑ v : Fin (2 * k), (M.filter (fun e => v ∈ e)).card = 2 * M.card := by
      calc
        ∑ v : Fin (2 * k), (M.filter (fun e => v ∈ e)).card
            = ∑ v : Fin (2 * k), ∑ e ∈ M, if v ∈ e then 1 else 0 := by
              congr 1; ext v; rw [Finset.card_filter]
        _ = ∑ e ∈ M, ∑ v : Fin (2 * k), if v ∈ e then 1 else 0 := Finset.sum_comm
        _ = ∑ e ∈ M, 2 := by
              refine Finset.sum_congr rfl (fun e he => ?_)
              rcases hmk e he with ⟨heq, hlt⟩
              rw [← heq]
              have hfilter : Finset.univ.filter (fun v : Fin (2 * k) => v ∈ s(minEnd e, maxEnd e)) =
                  {minEnd e, maxEnd e} := by
                ext v; simp [Sym2.mem_iff]
              rw [← Finset.card_filter, hfilter, Finset.card_pair hlt.ne]
        _ = 2 * M.card := by simp [mul_comm]
    omega
  have hdisj : ∀ e₁ ∈ M, ∀ e₂ ∈ M, ∀ v, v ∈ e₁ → v ∈ e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ v hv₁ hv₂
    rcases Finset.card_eq_one.mp (hM.2 v) with ⟨e0, he0⟩
    have h1 : e₁ ∈ ({e0} : Finset _) := by rw [← he0]; exact Finset.mem_filter.mpr ⟨he₁, hv₁⟩
    have h2 : e₂ ∈ ({e0} : Finset _) := by rw [← he0]; exact Finset.mem_filter.mpr ⟨he₂, hv₂⟩
    rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]
  have hmin_mem_edge : ∀ e ∈ M, minEnd e ∈ e := by
    intro e he
    have hmem : minEnd e ∈ s(minEnd e, maxEnd e) := Sym2.mem_mk_left _ _
    rwa [(hmk e he).1] at hmem
  have hmax_mem_edge : ∀ e ∈ M, maxEnd e ∈ e := by
    intro e he
    have hmem : maxEnd e ∈ s(minEnd e, maxEnd e) := Sym2.mem_mk_right _ _
    rwa [(hmk e he).1] at hmem
  have hmin_inj : Set.InjOn minEnd M := by
    intro e₁ he₁ e₂ he₂ hmin
    exact hdisj e₁ he₁ e₂ he₂ (minEnd e₁) (hmin_mem_edge e₁ he₁)
      (by rw [hmin]; exact hmin_mem_edge e₂ he₂)
  let S : Finset (Fin (2 * k)) := M.image minEnd
  have hcardS : S.card = k := by
    rw [Finset.card_image_of_injOn hmin_inj, hcardM]
  let ordS : Fin k ↪o Fin (2 * k) := S.orderEmbOfFin hcardS
  have hedge_ex : ∀ i : Fin k, ∃ e ∈ M, minEnd e = ordS i := by
    intro i
    exact Finset.mem_image.mp (S.orderEmbOfFin_mem hcardS i)
  let edgeOf : Fin k → Sym2 (Fin (2 * k)) := fun i => Classical.choose (hedge_ex i)
  have hedgeOf_mem : ∀ i, edgeOf i ∈ M := fun i => (Classical.choose_spec (hedge_ex i)).1
  have hedgeOf_min : ∀ i, minEnd (edgeOf i) = ordS i := fun i => (Classical.choose_spec (hedge_ex i)).2
  let f : Fin (2 * k) → Fin (2 * k) := fun t =>
    let i : Fin k := ⟨t.val / 2, by omega⟩
    if t.val % 2 = 0 then ordS i else maxEnd (edgeOf i)
  have hf_even : ∀ i : Fin k, f ⟨2 * i.val, by omega⟩ = ordS i := by
    intro i
    dsimp [f]
    have hmod : (2 * i.val) % 2 = 0 := by omega
    have hdiv : (2 * i.val) / 2 = i.val := by omega
    simp [hmod, hdiv]
  have hf_odd : ∀ i : Fin k, f ⟨2 * i.val + 1, by omega⟩ = maxEnd (edgeOf i) := by
    intro i
    dsimp [f]
    have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
    simp [hmod, hdiv]
  have hf_inj : Function.Injective f := by
    intro t₁ t₂ hft
    let i₁ : Fin k := ⟨t₁.val / 2, by omega⟩
    let i₂ : Fin k := ⟨t₂.val / 2, by omega⟩
    have hf1_mem : f t₁ ∈ edgeOf i₁ := by
      change (if t₁.val % 2 = 0 then ordS i₁ else maxEnd (edgeOf i₁)) ∈ edgeOf i₁
      split_ifs
      · rw [← hedgeOf_min i₁]; exact hmin_mem_edge _ (hedgeOf_mem i₁)
      · exact hmax_mem_edge _ (hedgeOf_mem i₁)
    have hf2_mem : f t₂ ∈ edgeOf i₂ := by
      change (if t₂.val % 2 = 0 then ordS i₂ else maxEnd (edgeOf i₂)) ∈ edgeOf i₂
      split_ifs
      · rw [← hedgeOf_min i₂]; exact hmin_mem_edge _ (hedgeOf_mem i₂)
      · exact hmax_mem_edge _ (hedgeOf_mem i₂)
    have hedge_eq : edgeOf i₁ = edgeOf i₂ :=
      hdisj _ (hedgeOf_mem i₁) _ (hedgeOf_mem i₂) (f t₁) hf1_mem (by rwa [hft])
    have hi_eq : i₁ = i₂ := by
      apply ordS.injective
      rw [← hedgeOf_min i₁, ← hedgeOf_min i₂, hedge_eq]
    have hlt := (hmk (edgeOf i₁) (hedgeOf_mem i₁)).2
    rw [hedgeOf_min i₁] at hlt
    change (if t₁.val % 2 = 0 then ordS i₁ else maxEnd (edgeOf i₁)) =
           (if t₂.val % 2 = 0 then ordS i₂ else maxEnd (edgeOf i₂)) at hft
    rw [← hi_eq] at hft
    have hpar : t₁.val % 2 = t₂.val % 2 := by
      by_cases h1 : t₁.val % 2 = 0 <;> by_cases h2 : t₂.val % 2 = 0
      · omega
      · simp only [h1, h2, ↓reduceIte] at hft
        exact absurd hft hlt.ne
      · simp only [h1, h2, ↓reduceIte] at hft
        exact absurd hft.symm hlt.ne
      · omega
    have hdiv_eq : t₁.val / 2 = t₂.val / 2 := congrArg Fin.val hi_eq
    ext; omega
  let perm : Equiv.Perm (Fin (2 * k)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  refine ⟨⟨perm, ?_, ?_⟩, ?_⟩
  · intro i
    change f ⟨2 * i.val, by omega⟩ < f ⟨2 * i.val + 1, by omega⟩
    rw [hf_even i, hf_odd i, ← hedgeOf_min i]
    exact (hmk (edgeOf i) (hedgeOf_mem i)).2
  · intro i j hij
    change f ⟨2 * i.val, by omega⟩ < f ⟨2 * j.val, by omega⟩
    rw [hf_even i, hf_even j]
    exact ordS.strictMono hij
  · ext e
    simp only [OrderedPairing.edgeFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      change s(f ⟨2 * i.val, by omega⟩, f ⟨2 * i.val + 1, by omega⟩) ∈ M
      rw [hf_even i, hf_odd i, ← hedgeOf_min i, (hmk (edgeOf i) (hedgeOf_mem i)).1]
      exact hedgeOf_mem i
    · intro he
      have hmin_mem : minEnd e ∈ (S : Set (Fin (2 * k))) := Finset.mem_image_of_mem _ he
      rw [← S.range_orderEmbOfFin hcardS] at hmin_mem
      rcases Set.mem_range.mp hmin_mem with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change s(f ⟨2 * i.val, by omega⟩, f ⟨2 * i.val + 1, by omega⟩) = e
      have he_eq : edgeOf i = e :=
        hmin_inj (hedgeOf_mem i) he (by rw [hedgeOf_min i]; exact hi)
      rw [hf_even i, hf_odd i, ← hedgeOf_min i, he_eq, (hmk e he).1]


end ExactMatching.Proofs
