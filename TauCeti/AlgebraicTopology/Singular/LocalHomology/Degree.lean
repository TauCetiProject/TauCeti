/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# The degree of a proper map between oriented manifolds

Let `M` and `N` be topological manifolds of the same dimension `n`, oriented by `o` and `o'`
(`TauCeti.HomologicalOrientation`), and let `f : M → N` be continuous. For a compact subset
`K ⊆ N` whose preimage `A = f⁻¹(K)` is compact, `f` is a map of pairs
`(M, M ∖ A) → (N, N ∖ K)`, so it carries the fundamental class `[M]_A ∈ Hₙ(M, M ∖ A; ℤ)` along `A`
to a class `f_*[M]_A ∈ Hₙ(N, N ∖ K; ℤ)`. The source group need not be cyclic, and for `A = ∅` the
class `[M]_A` is zero.

At a point `y` the target group `Hₙ(N, N ∖ {y}; ℤ)` is free of rank one on the local orientation
`o' y`, so `f_*[M]_{f⁻¹(y)} = d • o' y` for a unique integer `d`, the **local degree**
`o.localDegree o' hE f y`. For a proper map the local degree is locally constant, because local
homology is constant along a small compact ball in a chart. On a connected target the local
degree is therefore a single integer, the **degree** `o.degree o' hE f`, and it computes the image
of every fundamental class along a compact set:

`f_*[M]_{f⁻¹(K)} = deg f • [N]_K` for every compact `K ⊆ N`.

For compact `M` and `N` the case `K = N` reads `f_*[M] = deg f • [N]` in `Hₙ(N; ℤ)`.

This is the classical homological definition of the degree of a proper map, which does not need
compactness of `M` or `N` nor any smoothness of `f`. The degree is `1` for the identity, changes
sign when either orientation is reversed, is multiplicative under composition, vanishes for maps
that are not surjective and is invariant under proper homotopies, that is homotopies
`F : [0, 1] × M → N` which are proper as maps on `[0, 1] × M`.

## Main definitions

* `TauCeti.HomologicalOrientation.localDegree o o' hE f y`: the integer `d` with
  `f_*[M]_{f⁻¹(y)} = d • o' y`, and `0` if the fibre `f⁻¹(y)` is not compact.
* `TauCeti.HomologicalOrientation.degree o o' hE f`: the local degree at an arbitrary point of
  `N`; it is the degree of `f` when `f` is proper and `N` is connected.

## Main results

* `TauCeti.HomologicalOrientation.localDegree_eq_iff`: the defining property of the local degree.
* `TauCeti.HomologicalOrientation.isLocallyConstant_localDegree`: the local degree of a proper
  map is locally constant, so it equals the degree on a preconnected target
  (`TauCeti.HomologicalOrientation.localDegree_eq_degree`).
* `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_preimage`:
  `f_*[M]_{f⁻¹(K)} = deg f • [N]_K` for every compact `K`, and its converse
  `TauCeti.HomologicalOrientation.degree_eq_iff` for nonempty `K`.
* `TauCeti.HomologicalOrientation.degree_id`, `TauCeti.HomologicalOrientation.degree_neg_left`,
  `TauCeti.HomologicalOrientation.degree_neg_right`, `TauCeti.HomologicalOrientation.degree_comp`:
  normalization, orientation reversal and multiplicativity.
* `TauCeti.HomologicalOrientation.surjective_of_degree_ne_zero`: a proper map of nonzero degree
  onto a preconnected manifold is surjective.
* `TauCeti.HomologicalOrientation.degree_eq_of_homotopy`: the degree is invariant under proper
  homotopies.
* `TauCeti.HomologicalOrientation.mapFundamentalClass_eq_degree_smul`: for compact `M` and `N`,
  `f_*[M] = deg f • [N]` in `Hₙ(N; ℤ)`, and more generally
  `TauCeti.HomologicalOrientation.mapFundamentalClass_comp_eq_degree_smul`:
  `(g ∘ f)_*[M] = deg f • g_*[N]` for every continuous `g : N → X`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable {M N P E F G : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [TopologicalSpace P] [T2Space P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G P]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)
  (o'' : HomologicalOrientation P G n) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
  (hG : finrank ℝ G = n)

open scoped Classical in
/-- The **local degree** of `f : M → N` at `y ∈ N`: the integer `d` with
`f_*[M]_{f⁻¹(y)} = d • o' y` in `Hₙ(N, N ∖ {y}; ℤ)`, where `[M]_{f⁻¹(y)}` is the fundamental class
of `M` along the fibre (`TauCeti.HomologicalOrientation.localDegree_eq_iff`). It is `0` when the
fibre is not compact; for a proper map every fibre is compact. -/
def localDegree (f : C(M, N)) (y : N) : ℤ :=
  if h : IsCompact (f ⁻¹' {y}) then
    ((isLocalOrientation_iff _ _ _).1 (o' y).property
      (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
        (o.fundamentalClassOn hE h))).choose
  else 0

/-- At a point with compact fibre, `f` carries the fundamental class along the fibre to the local
degree times the local orientation. -/
theorem localHomologyMap_fundamentalClassOn_preimage_singleton (f : C(M, N)) {y : N}
    (h : IsCompact (f ⁻¹' {y})) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
      (o.fundamentalClassOn hE h) = o.localDegree o' hE f y • (o' y).val := by
  rw [localDegree, dite_eq_left h]
  exact ((isLocalOrientation_iff _ _ _).1 (o' y).property _).choose_spec.symm

/-- The local degree vanishes at a point whose fibre is not compact. -/
@[simp]
theorem localDegree_of_not_isCompact (f : C(M, N)) {y : N} (h : ¬IsCompact (f ⁻¹' {y})) :
    o.localDegree o' hE f y = 0 := by
  rw [localDegree, dite_eq_right h]

include hF in
/-- **The defining property of the local degree**: at a point `y` with compact fibre, the local
degree is the integer `c` with `f_*[M]_{f⁻¹(y)} = c • o' y`. -/
theorem localDegree_eq_iff (f : C(M, N)) {y : N} (h : IsCompact (f ⁻¹' {y})) {c : ℤ} :
    o.localDegree o' hE f y = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
        (o.fundamentalClassOn hE h) = c • (o' y).val := by
  rw [localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f h]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ o'.zsmul_left_injective hF y h⟩

include hF in
/-- The local degree at a point outside the range of `f` vanishes: the fibre is empty, and the
fundamental class along the empty set is zero. -/
@[simp]
theorem localDegree_eq_zero_of_notMem_range (f : C(M, N)) {y : N} (hy : y ∉ range f) :
    o.localDegree o' hE f y = 0 := by
  have h : f ⁻¹' {y} = ∅ := eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩
  have hc : IsCompact (f ⁻¹' {y}) := h ▸ isCompact_empty
  rw [localDegree_eq_iff o o' hE hF f hc, zero_smul,
    eq_zero_of_forall_localHomologyRestriction_eq_zero _ hE hc (o.fundamentalClassOn hE hc)
      fun x hx ↦ (h.subset hx).elim, map_zero]

/-- Let `K ⊆ N` have compact preimage. Then the restriction of `f_*[M]_{f⁻¹(K)}` to a point
`y ∈ K` is the local degree at `y` times the local orientation. -/
theorem localHomologyRestriction_localHomologyMap_fundamentalClassOn (f : C(M, N)) {K : Set N}
    (hK : IsCompact (f ⁻¹' K)) {y : N} (hy : y ∈ K) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hy) n
      (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
        (o.fundamentalClassOn hE hK)) =
      o.localDegree o' hE f y • (o' y).val := by
  have hy' : IsCompact (f ⁻¹' {y}) :=
    hK.of_isClosed_subset (isClosed_singleton.preimage f.continuous)
      (preimage_mono (singleton_subset_iff.2 hy))
  rw [← localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f hy',
    ← o.localHomologyRestriction_fundamentalClassOn_of_subset hE hK hy'
      (preimage_mono (singleton_subset_iff.2 hy)),
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, localHomologyMap_comp_localHomologyRestriction,
    localHomologyRestriction_comp_localHomologyMap]

include hF in
/-- **The local degree of a proper map is locally constant.** -/
theorem isLocallyConstant_localDegree {f : C(M, N)} (hf : IsProperMap f) :
    IsLocallyConstant (o.localDegree o' hE f) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y ↦ ?_
  obtain ⟨B, hB, hBc, hiso⟩ := exists_isCompact_mem_nhds_isIso_localHomologyRestriction
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (E := F) y n
  have hyB := mem_of_mem_nhds hB
  have hinj (z : N) (hz : z ∈ B) : Function.Injective
      (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hz) n) :=
    have := hiso z hz
    (ConcreteCategory.bijective_of_isIso _).1
  -- On `B` the image of the fundamental class is `d • [N]_B`, with `d` the local degree at `y`.
  have key : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
      (o.fundamentalClassOn hE (hf.isCompact_preimage hBc)) =
      o.localDegree o' hE f y • o'.fundamentalClassOn hF hBc :=
    hinj y hyB (by
      rw [localHomologyRestriction_localHomologyMap_fundamentalClassOn o o' hE f _ hyB, map_zsmul,
        o'.localHomologyRestriction_fundamentalClassOn hF hBc hyB])
  filter_upwards [hB] with z hz
  have h := localHomologyRestriction_localHomologyMap_fundamentalClassOn o o' hE f
    (hf.isCompact_preimage hBc) hz
  rw [key, map_zsmul, o'.localHomologyRestriction_fundamentalClassOn hF hBc hz] at h
  exact o'.zsmul_left_injective hF z h.symm

open scoped Classical in
/-- The **degree** of `f : M → N`: its local degree at an arbitrary point of `N`, and `0` when `N`
is empty. For a proper map onto a preconnected manifold the local degree is the same at every
point (`TauCeti.HomologicalOrientation.localDegree_eq_degree`), and the degree is characterized by
`f_*[M]_{f⁻¹(K)} = deg f • [N]_K` for compact `K`
(`TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_preimage`). -/
def degree (f : C(M, N)) : ℤ :=
  if h : Nonempty N then o.localDegree o' hE f h.some else 0

/-- On a nonempty target, the degree is the local degree at the chosen point `h.some`. -/
theorem degree_eq_localDegree_some (f : C(M, N)) (h : Nonempty N) :
    o.degree o' hE f = o.localDegree o' hE f h.some := by
  rw [degree, dite_eq_left h]

/-- The degree of a map to an empty manifold vanishes. -/
@[simp]
theorem degree_of_isEmpty [IsEmpty N] (f : C(M, N)) : o.degree o' hE f = 0 := by
  rw [degree, dite_eq_right (not_nonempty_iff.2 ‹_›)]

include hF in
/-- The local degree of a proper map onto a preconnected manifold is its degree at every point. -/
theorem localDegree_eq_degree [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f) (y : N) :
    o.localDegree o' hE f y = o.degree o' hE f := by
  rw [degree_eq_localDegree_some o o' hE f ⟨y⟩]
  exact (o.isLocallyConstant_localDegree o' hE hF hf).apply_eq_of_preconnectedSpace _ _

/-- **The degree computes the image of every fundamental class**: for a proper map `f` onto a
preconnected manifold and every compact `K ⊆ N`, `f_*[M]_{f⁻¹(K)} = deg f • [N]_K`. In particular
the degree may be read off from any nonempty compact `K`
(`TauCeti.HomologicalOrientation.degree_eq_iff`). -/
theorem localHomologyMap_fundamentalClassOn_preimage [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) {K : Set N} (hK : IsCompact K) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
      (o.fundamentalClassOn hE (hf.isCompact_preimage hK)) =
      o.degree o' hE f • o'.fundamentalClassOn hF hK := by
  refine localHomology_ext_of_isCompact _ hF hK fun y hy ↦ ?_
  rw [localHomologyRestriction_localHomologyMap_fundamentalClassOn o o' hE f _ hy, map_zsmul,
    o'.localHomologyRestriction_fundamentalClassOn hF hK hy,
    o.localDegree_eq_degree o' hE hF hf]

/-- **The degree is determined by any nonempty compact set**: for a proper map `f` onto a
preconnected manifold and nonempty compact `K ⊆ N`, the degree is the integer `c` with
`f_*[M]_{f⁻¹(K)} = c • [N]_K`. -/
theorem degree_eq_iff [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f) {K : Set N}
    (hK : IsCompact K) (hK₀ : K.Nonempty) {c : ℤ} :
    o.degree o' hE f = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
        (o.fundamentalClassOn hE (hf.isCompact_preimage hK)) = c • o'.fundamentalClassOn hF hK := by
  rw [o.localHomologyMap_fundamentalClassOn_preimage o' hE hF hf hK]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := hK₀
  have h' := congrArg (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
    (singleton_subset_iff.2 hy) n) h
  rw [map_zsmul, map_zsmul, o'.localHomologyRestriction_fundamentalClassOn hF hK hy] at h'
  exact o'.zsmul_left_injective hF y h'

include hF in
/-- A proper map of nonzero degree onto a preconnected manifold is surjective. -/
theorem surjective_of_degree_ne_zero [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f)
    (h : o.degree o' hE f ≠ 0) : Function.Surjective f := by
  intro y
  by_contra hy
  exact h (o.localDegree_eq_degree o' hE hF hf y ▸
    o.localDegree_eq_zero_of_notMem_range o' hE hF f fun ⟨x, hx⟩ ↦ hy ⟨x, hx⟩)

/-- The identity has local degree `1` at every point. -/
@[simp]
theorem localDegree_id (y : M) : o.localDegree o hE (ContinuousMap.id M) y = 1 := by
  rw [localDegree_eq_iff o o hE hE _ isCompact_singleton, one_smul, localHomologyMap_id,
    localHomologyRestriction_refl]
  exact o.fundamentalClassOn_singleton hE y isCompact_singleton

/-- The identity of a nonempty manifold has degree `1`. -/
@[simp]
theorem degree_id [Nonempty M] : o.degree o hE (ContinuousMap.id M) = 1 := by
  rw [degree_eq_localDegree_some o o hE _ ‹_›, localDegree_id]

include hF in
/-- Reversing the orientation of the source negates the local degree. -/
@[simp]
theorem localDegree_neg_left (f : C(M, N)) (y : N) :
    (-o).localDegree o' hE f y = -o.localDegree o' hE f y := by
  by_cases h : IsCompact (f ⁻¹' {y})
  · rw [localDegree_eq_iff (-o) o' hE hF f h, fundamentalClassOn_neg, map_neg,
      localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f h, neg_zsmul]
  · rw [localDegree_of_not_isCompact _ _ hE f h, localDegree_of_not_isCompact o o' hE f h,
      neg_zero]

include hF in
/-- Reversing the orientation of the target negates the local degree. -/
@[simp]
theorem localDegree_neg_right (f : C(M, N)) (y : N) :
    o.localDegree (-o') hE f y = -o.localDegree o' hE f y := by
  by_cases h : IsCompact (f ⁻¹' {y})
  · rw [localDegree_eq_iff o (-o') hE hF f h, localHomologyMap_fundamentalClassOn_preimage_singleton
      o o' hE f h, neg_apply, LocalOrientation.coe_neg, neg_zsmul, zsmul_neg, neg_neg]
  · rw [localDegree_of_not_isCompact _ _ hE f h, localDegree_of_not_isCompact o o' hE f h,
      neg_zero]

include hF in
/-- Reversing the orientation of the source negates the degree. -/
@[simp]
theorem degree_neg_left (f : C(M, N)) : (-o).degree o' hE f = -o.degree o' hE f := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, neg_zero]
  · rw [degree_eq_localDegree_some _ _ hE f h, degree_eq_localDegree_some o o' hE f h,
      localDegree_neg_left o o' hE hF]

include hF in
/-- Reversing the orientation of the target negates the degree. -/
@[simp]
theorem degree_neg_right (f : C(M, N)) : o.degree (-o') hE f = -o.degree o' hE f := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, neg_zero]
  · rw [degree_eq_localDegree_some _ _ hE f h, degree_eq_localDegree_some o o' hE f h,
      localDegree_neg_right o o' hE hF]

include hG in
/-- **Local degrees multiply under composition**: for proper maps `f : M → N` and `g : N → P` with
`N` preconnected, the local degree of `g ∘ f` at `z` is `deg f` times the local degree of `g` at
`z`. -/
theorem localDegree_comp [PreconnectedSpace N] {g : C(N, P)} {f : C(M, N)} (hg : IsProperMap g)
    (hf : IsProperMap f) (z : P) :
    o.localDegree o'' hE (g.comp f) z = o.degree o' hE f * o'.localDegree o'' hF g z := by
  have hz : IsCompact (g ⁻¹' {z}) := hg.isCompact_preimage isCompact_singleton
  rw [localDegree_eq_iff o o'' hE hG _ (hf.isCompact_preimage hz), mul_zsmul,
    ← localHomologyMap_fundamentalClassOn_preimage_singleton o' o'' hF g hz, ← map_zsmul,
    ← o.localHomologyMap_fundamentalClassOn_preimage o' hE hF hf hz,
    ← ModuleCat.comp_apply, localHomologyMap_comp]

include hG in
/-- **The degree is multiplicative**: for proper maps `f : M → N` and `g : N → P` with `N`
preconnected, `deg (g ∘ f) = deg g * deg f`. -/
theorem degree_comp [PreconnectedSpace N] {g : C(N, P)} {f : C(M, N)}
    (hg : IsProperMap g) (hf : IsProperMap f) :
    o.degree o'' hE (g.comp f) = o'.degree o'' hF g * o.degree o' hE f := by
  rcases isEmpty_or_nonempty P with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, zero_mul]
  · rw [degree_eq_localDegree_some _ _ hE _ h, degree_eq_localDegree_some _ _ hF _ h,
      localDegree_comp o o' o'' hE hF hG hg hf, mul_comm]

include hF in
/-- **Invariance of the local degree under proper homotopies**: if `H` is a homotopy from `f₀`
to `f₁` which is proper as a map `[0, 1] × M → N`, then `f₀` and `f₁` have the same local degree at
every point. -/
theorem localDegree_eq_of_homotopy {f₀ f₁ : C(M, N)} (H : f₀.Homotopy f₁) (hH : IsProperMap H)
    (y : N) : o.localDegree o' hE f₀ y = o.localDegree o' hE f₁ y := by
  -- Both fibres over `y` lie in the compact projection `A` of `H⁻¹(y)` to `M`.
  set A : Set M := Prod.snd '' (H ⁻¹' {y})
  have hA : IsCompact A := (hH.isCompact_preimage isCompact_singleton).image continuous_snd
  have h₀ : f₀ ⁻¹' {y} ⊆ A := fun x hx ↦ ⟨(0, x), by simpa using hx, rfl⟩
  have h₁ : f₁ ⁻¹' {y} ⊆ A := fun x hx ↦ ⟨(1, x), by simpa using hx, rfl⟩
  -- A map whose fibre over `y` lies in `A` carries `[M]_A` to its local degree times `o' y`.
  have hdeg (g : C(M, N)) (hg : g ⁻¹' {y} ⊆ A) :
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) g hg n (o.fundamentalClassOn hE hA) =
        o.localDegree o' hE g y • (o' y).val := by
    have hc : IsCompact (g ⁻¹' {y}) :=
      hA.of_isClosed_subset (isClosed_singleton.preimage g.continuous) hg
    rw [← localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE g hc,
      ← o.localHomologyRestriction_fundamentalClassOn_of_subset hE hA hc hg,
      ← ModuleCat.comp_apply, localHomologyRestriction_comp_localHomologyMap]
  -- The homotopy keeps `M ∖ A` inside `N ∖ {y}`, so the two maps of pairs agree on homology.
  have hmap : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f₀ h₀ n =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f₁ h₁ n := by
    rw [localHomologyMap_def, localHomologyMap_def]
    exact (TopPair.ofSubsetHomotopy (X := TopCat.of M) (Y := TopCat.of N) (B := Aᶜ) (B' := {y}ᶜ)
      (g₀ := TopCat.ofHom f₀) (g₁ := TopCat.ofHom f₁) H
      fun t x hx hHx ↦ hx ⟨(t, x), hHx, rfl⟩).congr_singularHomologyMap _ n
  have h := hdeg f₀ h₀
  rw [hmap, hdeg f₁ h₁] at h
  exact o'.zsmul_left_injective hF y h.symm

include hF in
/-- **Invariance of the degree under proper homotopies**: maps joined by a homotopy which is
proper as a map `[0, 1] × M → N` have the same degree. -/
theorem degree_eq_of_homotopy {f₀ f₁ : C(M, N)} (H : f₀.Homotopy f₁) (hH : IsProperMap H) :
    o.degree o' hE f₀ = o.degree o' hE f₁ := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty]
  · rw [degree_eq_localDegree_some o o' hE f₀ h, degree_eq_localDegree_some o o' hE f₁ h,
      o.localDegree_eq_of_homotopy o' hE hF H hH]

section CompactSpace

variable [CompactSpace M] [CompactSpace N]

variable [PreconnectedSpace N]

include hF in
/-- **The degree computes the image of the fundamental class**: for a map `f : M → N` between
compact oriented `n`-manifolds with `N` preconnected, `f_*[M] = deg f • [N]` in `Hₙ(N; ℤ)`. -/
theorem mapFundamentalClass_eq_degree_smul (f : C(M, N)) :
    o.mapFundamentalClass hE f = o.degree o' hE f • o'.fundamentalClass hF := by
  have : IsEmpty (TopPair.ofSubset ((univ : Set (TopCat.of N))ᶜ)).snd := by
    simp only [compl_univ]
    exact inferInstanceAs (IsEmpty (∅ : Set N))
  have hπ : IsIso ((TopPair.ofSubset ((univ : Set (TopCat.of N))ᶜ)).singularHomologyπ
      (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n) := inferInstance
  refine ((ConcreteCategory.isIso_iff_bijective _).1 hπ).1 ?_
  have h := o.localHomologyMap_fundamentalClassOn_preimage o' hE hF f.continuous.isProperMap
    isCompact_univ
  rw [← o.localHomologyRestriction_fundamentalClassOn_of_subset hE isCompact_univ _
    (subset_univ _), ← ModuleCat.comp_apply, localHomologyRestriction_comp_localHomologyMap] at h
  -- Both sides are read in `Hₙ(N, N ∖ N; ℤ)`, where `[N]` maps to `[N]` along `N`.
  exact (o.singularHomologyπ_mapFundamentalClass hE f).trans (h.trans
    ((congrArg (o.degree o' hE f • ·) (o'.singularHomologyπ_fundamentalClass hF)).symm.trans
      (map_zsmul _ _ _).symm))

include hF in
/-- **The degree of a composite with a further map**: for `f : M → N` between compact oriented
`n`-manifolds with `N` preconnected and any continuous `g : N → X`,
`(g ∘ f)_*[M] = deg f • g_*[N]` in `Hₙ(X; ℤ)`. -/
theorem mapFundamentalClass_comp_eq_degree_smul {X : Type} [TopologicalSpace X] (g : C(N, X))
    (f : C(M, N)) :
    o.mapFundamentalClass hE (g.comp f) = o.degree o' hE f • o'.mapFundamentalClass hF g := by
  rw [mapFundamentalClass_comp, o.mapFundamentalClass_eq_degree_smul o' hE hF f,
    mapFundamentalClass_def o' hF g]
  exact map_zsmul (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom g)).hom _ _

end CompactSpace

end HomologicalOrientation

end TauCeti
