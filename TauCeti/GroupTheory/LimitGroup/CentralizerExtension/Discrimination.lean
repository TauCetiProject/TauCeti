/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Extensions of centralizers are discriminated by their base group

Let `G` be a CSA group with the big powers property and let `u ≠ 1`. The retractions
`ξₖ : G(u, ℤ) →* G`, `t ↦ u ^ k`, of the extension of the centralizer of `u` discriminate it by
`G`: every nonidentity element of `G(u, ℤ)` survives under `ξₖ` for all sufficiently large `k`
(`CentralizerExt.eventually_retraction_ne_one`), so any finite family survives under a single
retraction (`CentralizerExt.isDiscriminatedBy`). Since fully residually free groups are CSA groups
with the big powers property, extending the centralizer of a nonidentity element of a fully
residually free group by `ℤ` gives a fully residually free group
(`isFullyResiduallyFree_centralizerExt`). This is the basic step in showing that iterated
extensions of centralizers of a free group are fully residually free.

Neither that `u` is not a proper power nor that `G` is nonabelian is assumed: an extension at a
proper power with the same centralizer as its root is an extension at that root
(`CentralizerExt.congr`), and for abelian `G` the extension is `G × ℤ`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.eventually_retraction_ne_one`: a nonidentity element of
  `G(u, ℤ)` survives under the retraction `t ↦ u ^ k` for all large `k`.
* `TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`: `G(u, ℤ)` is `G`-discriminated by `G`.
* `TauCeti.LimitGroup.isFullyResiduallyFree_centralizerExt`: extending the centralizer of a
  nonidentity element of a fully residually free group by `ℤ` gives a fully residually free group.

## Implementation notes

The normal form of the amalgam `G ∗_{C_G(u)} (C_G(u) × ℤ)` (`Monoid.PushoutI.NormalWord`) writes
every element as `g` or as `g * t ^ n₁ * b₁ * ⋯ * t ^ n_r * b_r` with `r ≥ 1`, every `nᵢ ≠ 0` and
`b₁, …, b_{r-1} ∉ C_G(u)`. Its image under `ξₖ` is `g * W k` with
`W k = u ^ (k * n₁) * b₁ * ⋯ * u ^ (k * n_r) * b_r`. In a CSA group `u` does not commute with
`b * u * b⁻¹` for `b ∉ C_G(u)`, so `W k * (W k')⁻¹` is a product of powers of conjugates of `u`
with noncommuting neighbours and exponents `k * n₁, …, (k - k') * n_r, …, -(k' * n₁)`. By the big
powers property `W k ≠ W k'` once `k` and `k' - k` are large, so `g * W k = 1` only for `k` in a
bounded set.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5: for a nonabelian CSA group with the big powers property the retractions
  `t ↦ u ^ k` discriminate `G(u, t)` by `G`.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II*,
  J. Algebra 200 (1998), §0, Lemma 2 and Theorem 1.
-/

public section

open Subgroup Filter Group

namespace TauCeti.LimitGroup

variable {G : Type*} [Group G] {u : G}

/-! ### Syllables over `G` -/

/-- The product `u ^ (k * n₁) * b₁ * ⋯ * u ^ (k * n_r) * b_r` of a list of syllables
`(nᵢ, bᵢ)`. -/
private def sylProd (u : G) (k : ℤ) (S : List (ℤ × G)) : G :=
  (S.map fun p => u ^ (k * p.1) * p.2).prod

/-- A syllable list is *reduced* when its exponents are nonzero and every letter except the last
lies outside `C_G(u)`. -/
private def IsReducedSyl (u : G) : List (ℤ × G) → Prop
  | [] => True
  | p :: S => p.1 ≠ 0 ∧ (S ≠ [] → p.2 ∉ centralizer {u}) ∧ IsReducedSyl u S

/-- The conjugates of `u` whose powers make up `sylProd u k S * (sylProd u k' S)⁻¹`. -/
private def dblBase (u : G) : List (ℤ × G) → List G
  | [] => []
  | [_] => [u]
  | p :: q :: S => u :: (((dblBase u (q :: S)).map fun v => p.2 * v * p.2⁻¹) ++ [u])

/-- The conjugates of `u` of `dblBase u S` with the exponents that make their powers multiply to
`sylProd u k S * (sylProd u k' S)⁻¹`. -/
private def dbl (u : G) (k k' : ℤ) : List (ℤ × G) → List (G × ℤ)
  | [] => []
  | [p] => [(u, (k - k') * p.1)]
  | p :: q :: S =>
    (u, k * p.1) :: (((dbl u k k' (q :: S)).map fun x => (p.2 * x.1 * p.2⁻¹, x.2)) ++
      [(u, -(k' * p.1))])

private theorem prod_dbl (u : G) (k k' : ℤ) (S : List (ℤ × G)) :
    sylProd u k S * (sylProd u k' S)⁻¹ = ((dbl u k k' S).map fun x => x.1 ^ x.2).prod := by
  induction S with
  | nil => simp [sylProd, dbl]
  | cons p S ih =>
    cases S with
    | nil =>
      simp only [sylProd, dbl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      group
    | cons q S =>
      -- Conjugating every entry by `p.2` conjugates the product.
      have hconj : (((dbl u k k' (q :: S)).map fun x => (p.2 * x.1 * p.2⁻¹, x.2)).map
          fun x => x.1 ^ x.2).prod = MulAut.conj p.2 ((dbl u k k' (q :: S)).map
            fun x => x.1 ^ x.2).prod := by
        simp [map_list_prod, Function.comp_def, conj_zpow]
      rw [dbl, List.map_cons, List.prod_cons, List.map_append, List.prod_append, hconj, ← ih,
        MulAut.conj_apply]
      simp only [sylProd, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil]
      group

private theorem map_fst_dbl (u : G) (k k' : ℤ) (S : List (ℤ × G)) :
    (dbl u k k' S).map Prod.fst = dblBase u S := by
  induction S with
  | nil => simp [dbl, dblBase]
  | cons p S ih =>
    cases S with
    | nil => simp [dbl, dblBase]
    | cons q S => simp [dbl, dblBase, ← ih, Function.comp_def]

private theorem head?_dblBase {S : List (ℤ × G)} (hS : S ≠ []) : (dblBase u S).head? = some u := by
  match S, hS with
  | [_], _ => simp [dblBase]
  | _ :: _ :: _, _ => simp [dblBase]

private theorem getLast?_dblBase {S : List (ℤ × G)} (hS : S ≠ []) :
    (dblBase u S).getLast? = some u := by
  match S, hS with
  | [_], _ => simp [dblBase]
  | _ :: _ :: _, _ => rw [dblBase, ← List.cons_append, List.getLast?_concat]

/-- Every exponent in `dbl u k k' S` is at least `N` in absolute value when `N ≤ k` and
`k + N ≤ k'`. -/
private theorem le_abs_of_mem_dbl {S : List (ℤ × G)} (hS : IsReducedSyl u S) {N k k' : ℤ}
    (hN : 0 ≤ N) (hk : N ≤ k) (hk' : k + N ≤ k') : ∀ x ∈ dbl u k k' S, N ≤ |x.2| := by
  induction S with
  | nil => simp [dbl]
  | cons p S ih =>
    obtain ⟨hp, -, hS⟩ := hS
    cases S with
    | nil =>
      simp only [dbl, List.mem_singleton, forall_eq]
      rw [abs_mul, abs_sub_comm]
      nlinarith [le_abs_self (k' - k), Int.one_le_abs hp, abs_nonneg (k' - k)]
    | cons q S =>
      simp only [dbl, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false]
      rintro x (rfl | ⟨y, hy, rfl⟩ | rfl)
      · rw [abs_mul]
        nlinarith [le_abs_self k, Int.one_le_abs hp, abs_nonneg k]
      · exact ih hS y hy
      · rw [abs_neg, abs_mul]
        nlinarith [le_abs_self k', Int.one_le_abs hp, abs_nonneg k']

/-- For a reduced syllable list, `dblBase u S` consists of nonidentity elements with
noncommuting neighbours. -/
private theorem dblBase_spec (hG : IsCSA G) (hu : u ≠ 1) {S : List (ℤ × G)}
    (hS : IsReducedSyl u S) :
    (∀ v ∈ dblBase u S, v ≠ 1) ∧ (dblBase u S).IsChain fun a b => ¬Commute a b := by
  induction S with
  | nil => simp [dblBase]
  | cons p S ih =>
    obtain ⟨-, hb, hS⟩ := hS
    cases S with
    | nil => simp [dblBase, hu]
    | cons q S =>
      obtain ⟨ih₁, ih₂⟩ := ih hS
      have hb := hb (List.cons_ne_nil q S)
      -- In a CSA group, `u` commutes with `p.2 * u * p.2⁻¹` only if `p.2 ∈ C_G(u)`.
      have hub : ¬Commute u (p.2 * u * p.2⁻¹) := fun h => hb (mem_centralizer_singleton_iff.2
        ((isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2 u p.2 hu h).eq.symm)
      have hconj : ∀ v w : G, ¬Commute v w → ¬Commute (p.2 * v * p.2⁻¹) (p.2 * w * p.2⁻¹) :=
        fun v w h hc => h (by simpa [mul_assoc] using hc.map (MulAut.conj p.2).symm.toMonoidHom)
      refine ⟨?_, ?_⟩
      · simp only [dblBase, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
          or_false]
        rintro v (rfl | ⟨w, hw, rfl⟩ | rfl)
        · exact hu
        · simpa using ih₁ w hw
        · exact hu
      · rw [dblBase, List.isChain_cons, List.isChain_append]
        refine ⟨?_, ⟨List.isChain_map_of_isChain _ hconj ih₂, List.isChain_singleton _, ?_⟩⟩
        · intro y hy
          rw [List.head?_append, List.head?_map, head?_dblBase (List.cons_ne_nil q S)] at hy
          simp only [Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq] at hy
          exact hy ▸ hub
        · intro x hx y hy
          rw [List.getLast?_map, getLast?_dblBase (List.cons_ne_nil q S)] at hx
          simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          exact hx ▸ hy ▸ fun h => hub h.symm

/-- For a nonempty reduced syllable list, `sylProd u k S ≠ sylProd u k' S` once `k` and `k' - k`
are large. -/
private theorem exists_sylProd_ne (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1)
    {S : List (ℤ × G)} (hS : IsReducedSyl u S) (hne : S ≠ []) :
    ∃ N : ℤ, ∀ k k', N ≤ k → k + N ≤ k' → sylProd u k S ≠ sylProd u k' S := by
  obtain ⟨h₁, h₂⟩ := dblBase_spec hG hu hS
  have hne' : dblBase u S ≠ [] := fun h => by simpa [h] using head?_dblBase (u := u) hne
  obtain ⟨N, hN⟩ := hBP.exists_list_prod_zpow_ne_one hne' h₁ h₂
  refine ⟨N, fun k k' hk hk' heq => ?_⟩
  refine hN (dbl u k k' S) (map_fst_dbl u k k' S)
    (le_abs_of_mem_dbl hS (Int.natCast_nonneg N) hk hk') ?_
  rw [← prod_dbl, heq, mul_inv_cancel]

/-- For a nonempty reduced syllable list and any `g : G`, `g * sylProd u k S ≠ 1` for all large
`k`. -/
private theorem eventually_mul_sylProd_ne_one (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1)
    {S : List (ℤ × G)} (hS : IsReducedSyl u S) (hne : S ≠ []) (g : G) :
    ∀ᶠ k : ℤ in atTop, g * sylProd u k S ≠ 1 := by
  obtain ⟨N, hN⟩ := exists_sylProd_ne hG hBP hu hS hne
  by_cases h : ∃ k₀, N ≤ k₀ ∧ g * sylProd u k₀ S = 1
  · obtain ⟨k₀, hk₀, h₀⟩ := h
    exact eventually_atTop.2 ⟨k₀ + N, fun k hk h₁ =>
      hN k₀ k hk₀ hk (mul_left_cancel (h₀.trans h₁.symm))⟩
  · simp only [not_exists, not_and] at h
    exact eventually_atTop.2 ⟨N, h⟩

/-! ### Syllables of the normal form -/

namespace CentralizerExt

/-- The element `t ^ n₁ * b₁ * ⋯ * t ^ n_r * b_r` of `G(u, ℤ)` given by a list of syllables. -/
private def sylElem (S : List (ℤ × G)) : CentralizerExt u 1 :=
  (S.map fun p => t 0 ^ p.1 * of p.2).prod

private theorem retraction_sylElem (k : ℤ) (S : List (ℤ × G)) :
    retraction (fun _ => k) (sylElem (u := u) S) = sylProd u k S := by
  simp [sylElem, sylProd, map_list_prod, Function.comp_def, zpow_mul]

/-- The syllables of a word in the factors of `G(u, ℤ)`: its product is
`of (toSyl l).1 * sylElem (toSyl l).2`. -/
private def toSyl : List (Σ b, CentralizerExtFactor u 1 b) → G × List (ℤ × G)
  | [] => (1, [])
  -- A letter of the first factor has type `CentralizerExtFactor u 1 false`, which is `G` only
  -- after reducing `cond`, so it is multiplied in `G` through `show`.
  | ⟨false, g⟩ :: l => ((show G from g) * (toSyl l).1, (toSyl l).2)
  | ⟨true, p⟩ :: l => ((p.1 : G), ((p.2 0).toAdd, (toSyl l).1) :: (toSyl l).2)

private theorem ofCoprodI_prod_eq (l : List (Σ b, CentralizerExtFactor u 1 b)) :
    Monoid.PushoutI.ofCoprodI (l.map fun x => Monoid.CoprodI.of x.2).prod =
      of (toSyl l).1 * sylElem (toSyl l).2 := by
  induction l with
  | nil => simp [toSyl, sylElem]
  | cons x l ih =>
    obtain ⟨_ | _, g⟩ := x
    · rw [List.map_cons, List.prod_cons, map_mul, ih, Monoid.PushoutI.ofCoprodI_of,
        pushoutI_of_false]
      simp only [toSyl, map_mul, mul_assoc]
    · obtain ⟨c, τ⟩ := g
      rw [List.map_cons, List.prod_cons, map_mul, ih, Monoid.PushoutI.ofCoprodI_of,
        pushoutI_of_true]
      simp only [toSyl, sylElem, List.map_cons, List.prod_cons, mul_assoc]

/-- A word whose letters avoid the amalgamated subgroup and whose neighbouring letters lie in
different factors has a reduced syllable list; its leading element lies in `C_G(u)` exactly when
the word does not start with a letter of `G`. -/
private theorem toSyl_spec {l : List (Σ b, CentralizerExtFactor u 1 b)}
    (hred : ∀ x ∈ l, x.2 ∉ (centralizerExtMap u 1 x.1).range)
    (hchain : l.IsChain fun x y => x.1 ≠ y.1) :
    IsReducedSyl u (toSyl l).2 ∧
      ((toSyl l).1 ∈ centralizer {u} ↔ l.head?.map Sigma.fst ≠ some false) := by
  induction l with
  | nil => simp [toSyl, IsReducedSyl, one_mem]
  | cons x l ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (fun y hy => hred y (List.mem_cons_of_mem _ hy)) hchain.tail
    have hx := hred x List.mem_cons_self
    have hhead : ∀ y ∈ l.head?, x.1 ≠ y.1 := List.isChain_cons.1 hchain |>.1
    obtain ⟨_ | _, g⟩ := x
    · -- A letter of `G` outside `C_G(u)`, followed by a letter of `C_G(u) × ℤ` or nothing.
      have hg : g ∉ centralizer {u} := fun hg => hx ⟨⟨g, hg⟩, by simp⟩
      have hl : (toSyl l).1 ∈ centralizer {u} := ih₂.2 fun h => by
        obtain ⟨y, hy, hy'⟩ := Option.map_eq_some_iff.1 h
        exact hhead y hy hy'.symm
      refine ⟨ih₁, ?_⟩
      simp only [toSyl, List.head?_cons, Option.map_some, ne_eq, not_true_eq_false, iff_false]
      exact fun h => hg (by simpa using mul_mem h (inv_mem hl))
    · -- A letter `(c, τ)` with `τ ≠ 1`, followed by a letter of `G` or nothing.
      obtain ⟨c, τ⟩ := g
      have hτ : (τ 0).toAdd ≠ 0 := fun h => hx ⟨c, by
        rw [centralizerExtMap_true, MonoidHom.inl_apply]
        congr 1
        funext i
        rw [Subsingleton.elim i 0]
        exact (toAdd_eq_zero.1 h).symm⟩
      refine ⟨⟨hτ, fun hne => ?_, ih₁⟩, by simp [toSyl, c.2]⟩
      -- The syllables after this letter are nonempty, so `l` starts with a letter of `G`.
      rw [ih₂, not_not]
      cases l with
      | nil => simp [toSyl] at hne
      | cons y l =>
        have := hhead y rfl
        simp only [List.head?_cons, Option.map_some, Option.some.injEq]
        revert this
        cases y.1 <;> simp

/-- **Big powers discrimination of an extension of a centralizer.** In a CSA group `G` with the
big powers property, for `u ≠ 1`, every nonidentity element of `G(u, ℤ)` survives under the
retraction `t ↦ u ^ k` onto `G` for all sufficiently large `k`. -/
theorem eventually_retraction_ne_one (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1)
    {x : CentralizerExt u 1} (hx : x ≠ 1) :
    ∀ᶠ k : ℤ in atTop, retraction (fun _ => k) x ≠ 1 := by
  classical
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty (centralizerExtMap u 1)
    (centralizerExtMap_injective u 1)
  -- Write `x` in normal form: a head in `C_G(u)` times a word whose letters avoid `C_G(u)`.
  let w : Monoid.PushoutI.NormalWord d := x • .empty
  have hw : w.prod = x := by simp [w, Monoid.PushoutI.NormalWord.prod_smul]
  have hred : ∀ y ∈ w.toList, y.2 ∉ (centralizerExtMap u 1 y.1).range := fun y hy hmem => by
    refine w.ne_one y hy ?_
    have h₁ := (d.compl y.1).equiv_fst_eq_self_of_mem_of_one_mem (d.one_mem y.1) hmem
    have h₂ := (d.compl y.1).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _)
      (w.normalized y.1 y.2 hy)
    exact congrArg Subtype.val (h₁.symm.trans h₂)
  have hS := (toSyl_spec hred w.chain_ne).1
  have hx' : x = of ((w.head : G) * (toSyl w.toList).1) * sylElem (toSyl w.toList).2 := by
    rw [← hw, Monoid.PushoutI.NormalWord.prod, Monoid.CoprodI.Word.prod, ofCoprodI_prod_eq,
      ← Monoid.PushoutI.of_apply_eq_base _ false, centralizerExtMap_false, coe_subtype,
      pushoutI_of_false, map_mul, mul_assoc]
  rcases eq_or_ne (toSyl w.toList).2 [] with hnil | hne
  · -- Without syllables, `x` lies in `G` and every retraction fixes it.
    rw [hnil, sylElem, List.map_nil, List.prod_nil, mul_one] at hx'
    refine Eventually.of_forall fun k => ?_
    have hk := retraction_of (u := u) (n := 1) (fun _ => k) ((w.head : G) * (toSyl w.toList).1)
    rw [← hx'] at hk
    rw [hk]
    exact fun h => hx (by rw [hx', h, map_one])
  · filter_upwards [eventually_mul_sylProd_ne_one hG hBP hu hS hne
      ((w.head : G) * (toSyl w.toList).1)] with k hk
    rwa [hx', map_mul, retraction_of, retraction_sylElem]

/-- In a CSA group `G` with the big powers property, for `u ≠ 1`, the extension `G(u, ℤ)` is
`G`-discriminated by `G`: any finite family of nonidentity elements survives under one retraction
`t ↦ u ^ k`. -/
theorem isDiscriminatedBy (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1) :
    GroupAlgGeom.IsDiscriminatedBy (of : G →* CentralizerExt u 1) (MonoidHom.id G) := by
  refine (GroupAlgGeom.isDiscriminatedBy_def _ _).2 fun s hs => ?_
  obtain ⟨k, hk⟩ := ((eventually_all_finset s).2 fun x hx =>
    eventually_retraction_ne_one hG hBP hu (hs x hx)).exists
  exact ⟨⟨retraction fun _ => k, fun g => retraction_of _ g⟩, hk⟩

end CentralizerExt

/-- Extending the centralizer of a nonidentity element of a fully residually free group by `ℤ`
gives a fully residually free group. -/
theorem isFullyResiduallyFree_centralizerExt (hG : IsFullyResiduallyFree G) (hu : u ≠ 1) :
    IsFullyResiduallyFree (CentralizerExt u 1) :=
  hG.of_isDiscriminatedBy (CentralizerExt.isDiscriminatedBy hG.isCSA hG.isBP hu)

end TauCeti.LimitGroup
