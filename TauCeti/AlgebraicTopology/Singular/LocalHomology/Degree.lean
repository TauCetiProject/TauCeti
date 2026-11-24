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
`F : [0, 1] × M → N` which are proper as maps on `[0, 1] × M`. The local degree at `y` is already
invariant under homotopies whose fibre over `y` is compact. It only depends on `f` near the fibre
over `y` (excision), and it is additive over open sets covering a compact fibre and meeting it in
disjoint parts: the fundamental class along the fibre is the sum of the images of the fundamental
classes along the parts.

## Main definitions

* `TauCeti.HomologicalOrientation.localDegree o o' hE f y`: the integer `d` with
  `f_*[M]_{f⁻¹(y)} = d • o' y`, and `0` if the fibre `f⁻¹(y)` is not compact.
* `TauCeti.HomologicalOrientation.degree o o' hE f`: the local degree at an arbitrary point of
  `N`; it is the degree of `f` when `f` is proper and `N` is connected.

## Main results

* `TauCeti.HomologicalOrientation.localDegree_eq_iff`: the defining property of the local degree.
* `TauCeti.HomologicalOrientation.singularHomologyToLocalHomology_mapFundamentalClass`: for compact
  `M`, the image of `f_*[M]` in the local homology at `y` is the local degree at `y` times the
  local orientation, with no connectedness of `N`.
* `TauCeti.HomologicalOrientation.localDegree_comap_comp`: excision, the local degree at `y` is
  unchanged on restricting to an open subset containing the fibre over `y`.
* `TauCeti.HomologicalOrientation.isLocallyConstant_localDegree`: the local degree of a proper
  map is locally constant, so it equals the degree on a preconnected target
  (`TauCeti.HomologicalOrientation.localDegree_eq_degree`).
* `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_preimage`:
  `f_*[M]_{f⁻¹(K)} = deg f • [N]_K` for every compact `K`, and its converse
  `TauCeti.HomologicalOrientation.degree_eq_iff` for nonempty `K`.
* `TauCeti.HomologicalOrientation.degree_id`, `TauCeti.HomologicalOrientation.degree_neg_left`,
  `TauCeti.HomologicalOrientation.degree_neg_right`, `TauCeti.HomologicalOrientation.degree_comp`:
  normalization, orientation reversal and multiplicativity. On a connected manifold the degree of
  a self-map, and the local degree of a map from an open subset, do not depend on the orientation
  (`TauCeti.HomologicalOrientation.degree_self_eq`,
  `TauCeti.HomologicalOrientation.localDegree_comap_self_eq`). Local degrees are multiplicative
  as well, `localDegree (g ∘ f) z = deg f * localDegree g z`, as soon as `f` is proper onto a
  preconnected `N` and the fibre of `g` over `z` is compact
  (`TauCeti.HomologicalOrientation.localDegree_comp`).
* `TauCeti.HomologicalOrientation.localDegree_comap`: the local degree is natural under open
  embeddings of the source whose range contains the fibre, and so only depends on the map near
  the fibre (`TauCeti.HomologicalOrientation.localDegree_congr`).
* `TauCeti.HomologicalOrientation.localDegree_eq_sum`: the local degree is additive over finitely
  many open sets covering a compact fibre and meeting it in pairwise disjoint parts.
* `TauCeti.HomologicalOrientation.localDegree_eq_add`: additivity of the local degree over two
  open embeddings whose images cover a compact fibre and meet it in disjoint parts.
* `TauCeti.HomologicalOrientation.surjective_of_degree_ne_zero`: a proper map of nonzero degree
  onto a preconnected manifold is surjective.
* `TauCeti.HomologicalOrientation.degree_eq_of_homotopy`: the degree is invariant under proper
  homotopies, and the local degree at `y` under homotopies whose fibre over `y` is compact
  (`TauCeti.HomologicalOrientation.localDegree_eq_of_homotopy_of_isCompact`).
* `TauCeti.HomologicalOrientation.mapFundamentalClass_eq_degree_smul`: for compact `M` and `N`,
  `f_*[M] = deg f • [N]` in `Hₙ(N; ℤ)`, and more generally
  `TauCeti.HomologicalOrientation.mapFundamentalClass_comp_eq_degree_smul`:
  `(g ∘ f)_*[M] = deg f • g_*[N]` for every continuous `g : N → X`.
* `TauCeti.HomologicalOrientation.singularHomologyMap_eq_degree_smul`: a self-map of a compact
  connected oriented manifold acts on top homology by multiplication by its degree.
* `TauCeti.HomologicalOrientation.bijective_singularHomologyMap_iff`: for compact connected `M`
  and `N`, `f_* : Hₙ(M; ℤ) → Hₙ(N; ℤ)` is bijective exactly when `deg f = ±1`; the same holds for
  the `ULift ℤ` coefficients of the fundamental classes
  (`TauCeti.HomologicalOrientation.bijective_singularHomologyFunctor_map_iff`).

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
  (o'' : HomologicalOrientation P G n) (hE : finrank ℝ E = n)

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

/-- **The defining property of the local degree**: at a point `y` with compact fibre, the local
degree is the integer `c` with `f_*[M]_{f⁻¹(y)} = c • o' y`. -/
theorem localDegree_eq_iff (hF : finrank ℝ F = n) (f : C(M, N)) {y : N}
    (h : IsCompact (f ⁻¹' {y})) {c : ℤ} :
    o.localDegree o' hE f y = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f (subset_refl _) n
        (o.fundamentalClassOn hE h) = c • (o' y).val := by
  rw [localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f h]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ o'.zsmul_left_injective hF y h⟩

/-- The local degree at a point outside the range of `f` vanishes: the fibre is empty, and the
fundamental class along the empty set is zero. -/
@[simp]
theorem localDegree_eq_zero_of_notMem_range (hF : finrank ℝ F = n) (f : C(M, N)) {y : N}
    (hy : y ∉ range f) :
    o.localDegree o' hE f y = 0 := by
  have h : f ⁻¹' {y} = ∅ := eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩
  have hc : IsCompact (f ⁻¹' {y}) := h ▸ isCompact_empty
  rw [localDegree_eq_iff o o' hE hF f hc, zero_smul,
    eq_zero_of_forall_localHomologyRestriction_eq_zero _ hE hc (o.fundamentalClassOn hE hc)
      fun x hx ↦ (h.subset hx).elim, map_zero]

/-- A point at which `f` has nonzero local degree lies in the range of `f`. -/
theorem mem_range_of_localDegree_ne_zero (hF : finrank ℝ F = n) {f : C(M, N)} {y : N}
    (h : o.localDegree o' hE f y ≠ 0) : y ∈ range f :=
  by_contra fun hy ↦ h (o.localDegree_eq_zero_of_notMem_range o' hE hF f hy)

/-- **Excision for the local degree**: if `j : M' → M` is an open embedding whose image contains
the fibre of `f : M → N` over `y`, then `f ∘ j` has the same local degree at `y` as `f`, for the
orientation `o` pulled back along `j`. -/
theorem localDegree_comap_comp (hF : finrank ℝ F = n) {M' : Type} [TopologicalSpace M']
    [T2Space M'] [ChartedSpace E M'] {j : C(M', M)} (hj : IsOpenEmbedding j) (f : C(M, N))
    {y : N} (hy : f ⁻¹' {y} ⊆ range j) :
    (o.comap hj).localDegree o' hE (f.comp j) y = o.localDegree o' hE f y := by
  have hc : IsCompact ((f.comp j) ⁻¹' {y}) ↔ IsCompact (f ⁻¹' {y}) :=
    hj.isInducing.isCompact_preimage_iff hy
  by_cases h : IsCompact (f ⁻¹' {y})
  · -- `j` carries the fundamental class along the fibre of `f ∘ j` to that along the fibre of `f`.
    have h' := hc.2 h
    have himage : j '' ((f.comp j) ⁻¹' {y}) = f ⁻¹' {y} := image_preimage_eq_of_subset hy
    rw [localDegree_eq_iff (o.comap hj) o' hE hF _ h',
      ← localHomologyMap_comp _ j f (hj.injective.preimage_image _).subset himage.symm.subset,
      ModuleCat.comp_apply, o.localHomologyMap_fundamentalClassOn_comap hE hj h',
      ← localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f h,
      ← o.localHomologyRestriction_fundamentalClassOn_of_subset hE _ h himage.symm.subset,
      ← ModuleCat.comp_apply, localHomologyRestriction_comp_localHomologyMap]
  · rw [localDegree_of_not_isCompact _ _ _ _ (mt hc.1 h), localDegree_of_not_isCompact _ _ _ _ h]

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

/-- **The local image of the image of the fundamental class.** For a compact oriented manifold `M`,
the image of `f_*[M]` in the local homology `Hₙ(N, N ∖ {y}; ℤ)` is the local degree of `f` at `y`
times the local orientation. No connectedness of `N` is needed. -/
theorem singularHomologyToLocalHomology_mapFundamentalClass [CompactSpace M] (f : C(M, N))
    (y : N) :
    singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) y n
        (o.mapFundamentalClass hE f) =
      o.localDegree o' hE f y • (o' y).val := by
  refine (singularHomologyToLocalHomology_apply _ y (o.mapFundamentalClass hE f)).trans ?_
  rw [o.singularHomologyπ_mapFundamentalClass]
  exact localHomologyRestriction_localHomologyMap_fundamentalClassOn o o' hE f (K := univ)
    (by simpa using isCompact_univ) (mem_univ y)

/-- **The local degree of a proper map is locally constant.** -/
theorem isLocallyConstant_localDegree (hF : finrank ℝ F = n) {f : C(M, N)} (hf : IsProperMap f) :
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

/-- The local degree of a proper map onto a preconnected manifold is its degree at every point. -/
theorem localDegree_eq_degree (hF : finrank ℝ F = n) [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) (y : N) :
    o.localDegree o' hE f y = o.degree o' hE f := by
  rw [degree_eq_localDegree_some o o' hE f ⟨y⟩]
  exact (o.isLocallyConstant_localDegree o' hE hF hf).apply_eq_of_preconnectedSpace _ _

/-- **The degree computes the image of every fundamental class**: for a proper map `f` onto a
preconnected manifold and every compact `K ⊆ N`, `f_*[M]_{f⁻¹(K)} = deg f • [N]_K`. In particular
the degree may be read off from any nonempty compact `K`
(`TauCeti.HomologicalOrientation.degree_eq_iff`). -/
theorem localHomologyMap_fundamentalClassOn_preimage (hF : finrank ℝ F = n) [PreconnectedSpace N]
    {f : C(M, N)} (hf : IsProperMap f) {K : Set N} (hK : IsCompact K) :
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
theorem degree_eq_iff (hF : finrank ℝ F = n) [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) {K : Set N} (hK : IsCompact K) (hK₀ : K.Nonempty) {c : ℤ} :
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

/-- A proper map of nonzero degree onto a preconnected manifold is surjective. -/
theorem surjective_of_degree_ne_zero (hF : finrank ℝ F = n) [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) (h : o.degree o' hE f ≠ 0) : Function.Surjective f := by
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

/-- Reversing the orientation of the source negates the local degree. -/
@[simp]
theorem localDegree_neg_left (hF : finrank ℝ F = n) (f : C(M, N)) (y : N) :
    (-o).localDegree o' hE f y = -o.localDegree o' hE f y := by
  by_cases h : IsCompact (f ⁻¹' {y})
  · rw [localDegree_eq_iff (-o) o' hE hF f h, fundamentalClassOn_neg, map_neg,
      localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f h, neg_zsmul]
  · rw [localDegree_of_not_isCompact _ _ hE f h, localDegree_of_not_isCompact o o' hE f h,
      neg_zero]

/-- Reversing the orientation of the target negates the local degree. -/
@[simp]
theorem localDegree_neg_right (hF : finrank ℝ F = n) (f : C(M, N)) (y : N) :
    o.localDegree (-o') hE f y = -o.localDegree o' hE f y := by
  by_cases h : IsCompact (f ⁻¹' {y})
  · rw [localDegree_eq_iff o (-o') hE hF f h, localHomologyMap_fundamentalClassOn_preimage_singleton
      o o' hE f h, neg_apply, LocalOrientation.coe_neg, neg_zsmul, zsmul_neg, neg_neg]
  · rw [localDegree_of_not_isCompact _ _ hE f h, localDegree_of_not_isCompact o o' hE f h,
      neg_zero]

/-- Reversing the orientation of the source negates the degree. -/
@[simp]
theorem degree_neg_left (hF : finrank ℝ F = n) (f : C(M, N)) :
    (-o).degree o' hE f = -o.degree o' hE f := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, neg_zero]
  · rw [degree_eq_localDegree_some _ _ hE f h, degree_eq_localDegree_some o o' hE f h,
      localDegree_neg_left o o' hE hF]

/-- Reversing the orientation of the target negates the degree. -/
@[simp]
theorem degree_neg_right (hF : finrank ℝ F = n) (f : C(M, N)) :
    o.degree (-o') hE f = -o.degree o' hE f := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, neg_zero]
  · rw [degree_eq_localDegree_some _ _ hE f h, degree_eq_localDegree_some o o' hE f h,
      localDegree_neg_right o o' hE hF]

/-- **The local degree on an open subset does not depend on the orientation.** On a connected
manifold `M`, the local degree of a map `f : U → M` from an open subset, for an orientation of `M`
restricted to `U` on the source and used on the target, is the same for every orientation of `M`:
reversing it reverses both. -/
theorem localDegree_comap_self_eq [ConnectedSpace M] (o₁ : HomologicalOrientation M E n) {U : Type}
    [TopologicalSpace U] [T2Space U] [ChartedSpace E U] {j : U → M} (hj : IsOpenEmbedding j)
    (f : C(U, M)) (y : M) :
    (o₁.comap hj).localDegree o₁ hE f y = (o.comap hj).localDegree o hE f y := by
  rcases eq_or_eq_neg hE o o₁ with rfl | rfl
  · rfl
  · rw [comap_neg, localDegree_neg_left _ _ _ hE, localDegree_neg_right _ _ _ hE, neg_neg]

/-- **The degree of a self-map does not depend on the orientation.** On a connected manifold, the
degree of a self-map for an orientation used on both sides is the same for every orientation:
reversing it reverses both. -/
theorem degree_self_eq [ConnectedSpace M] (o₁ : HomologicalOrientation M E n) (f : C(M, M)) :
    o₁.degree o₁ hE f = o.degree o hE f := by
  rcases eq_or_eq_neg hE o o₁ with rfl | rfl
  · rfl
  · rw [degree_neg_left _ _ _ hE, degree_neg_right _ _ _ hE, neg_neg]

/-- **Local degrees multiply under composition**: for a proper map `f : M → N` with `N`
preconnected and a map `g : N → P` whose fibre over `z` is compact, the local degree of `g ∘ f` at
`z` is `deg f` times the local degree of `g` at `z`. -/
theorem localDegree_comp (hF : finrank ℝ F = n) (hG : finrank ℝ G = n) [PreconnectedSpace N]
    {g : C(N, P)} {f : C(M, N)} {z : P} (hz : IsCompact (g ⁻¹' {z})) (hf : IsProperMap f) :
    o.localDegree o'' hE (g.comp f) z = o.degree o' hE f * o'.localDegree o'' hF g z := by
  rw [localDegree_eq_iff o o'' hE hG _ (hf.isCompact_preimage hz), mul_zsmul,
    ← localHomologyMap_fundamentalClassOn_preimage_singleton o' o'' hF g hz, ← map_zsmul,
    ← o.localHomologyMap_fundamentalClassOn_preimage o' hE hF hf hz,
    ← ModuleCat.comp_apply, localHomologyMap_comp]

/-- **The degree is multiplicative**: for proper maps `f : M → N` and `g : N → P` with `N`
preconnected, `deg (g ∘ f) = deg g * deg f`. -/
theorem degree_comp (hF : finrank ℝ F = n) (hG : finrank ℝ G = n) [PreconnectedSpace N]
    {g : C(N, P)} {f : C(M, N)} (hg : IsProperMap g) (hf : IsProperMap f) :
    o.degree o'' hE (g.comp f) = o'.degree o'' hF g * o.degree o' hE f := by
  rcases isEmpty_or_nonempty P with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty, zero_mul]
  · rw [degree_eq_localDegree_some _ _ hE _ h, degree_eq_localDegree_some _ _ hF _ h,
      localDegree_comp o o' o'' hE hF hG (hg.isCompact_preimage isCompact_singleton) hf, mul_comm]

/-- **The local degree is natural under open embeddings of the source.** Let `j : U → M` be an open
embedding, with `U` oriented by `o.comap hj`. If the fibre of `f` over `y` lies in the range of
`j`, then `f ∘ j` has the same local degree at `y` as `f`. -/
theorem localDegree_comap (hF : finrank ℝ F = n) {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] {j : C(U, M)} (hj : IsOpenEmbedding j) (f : C(M, N)) {y : N}
    (hyj : f ⁻¹' {y} ⊆ range j) :
    (o.comap hj).localDegree o' hE (f.comp j) y = o.localDegree o' hE f y := by
  -- `j` maps the fibre of `f ∘ j` onto the fibre of `f`, so both are compact or neither is.
  by_cases hy : IsCompact (f ⁻¹' {y})
  swap
  · rw [localDegree_of_not_isCompact o o' hE f hy, localDegree_of_not_isCompact _ o' hE _
      fun hK ↦ hy (image_preimage_eq_of_subset hyj ▸ hK.image j.continuous)]
  have hK : IsCompact ((f.comp j) ⁻¹' {y}) := hj.isInducing.isCompact_preimage' hy hyj
  -- `j` carries the fundamental class of `U` along the fibre of `f ∘ j` to that of `M` along the
  -- fibre of `f`.
  have hj' (T : Set M) (hT : j '' ((f.comp j) ⁻¹' {y}) = T) (hTc : IsCompact T)
      (h : j ⁻¹' T ⊆ (f.comp j) ⁻¹' {y}) :
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) j h n
        ((o.comap hj).fundamentalClassOn hE hK) = o.fundamentalClassOn hE hTc := by
    subst hT
    exact o.localHomologyMap_fundamentalClassOn_comap hE hj hK
  rw [localDegree_eq_iff (o.comap hj) o' hE hF _ hK, ← localHomologyMap_comp
    (ModuleCat.of ℤ (ULift.{0} ℤ)) j f (subset_refl (j ⁻¹' (f ⁻¹' {y}))) (subset_refl _),
    ModuleCat.comp_apply, hj' _ (image_preimage_eq_of_subset hyj) hy,
    localHomologyMap_fundamentalClassOn_preimage_singleton o o' hE f hy]

/-- **The local degree only depends on the map near the fibre**: if `g` agrees with `f` on a
neighbourhood of the fibre of `f` over `y` and has no further points over `y`, then `f` and `g`
have the same local degree at `y`. -/
theorem localDegree_congr (hF : finrank ℝ F = n) {f g : C(M, N)} {y : N}
    (hfg : f =ᶠ[𝓝ˢ (f ⁻¹' {y})] g) (hgf : g ⁻¹' {y} ⊆ f ⁻¹' {y}) :
    o.localDegree o' hE f y = o.localDegree o' hE g y := by
  obtain ⟨W, hWo, hAW, hW⟩ := eventually_nhdsSet_iff_exists.1 hfg
  have hfib : g ⁻¹' {y} = f ⁻¹' {y} :=
    hgf.antisymm fun x hx ↦ ((hW x (hAW hx)).symm.trans hx :)
  let V : TopologicalSpace.Opens M := ⟨W, hWo⟩
  have hrange (A : Set M) (hA : A ⊆ W) : A ⊆ range (Subtype.val : V → M) :=
    fun x hx ↦ ⟨⟨x, hA hx⟩, rfl⟩
  have hcomp : f.comp ⟨Subtype.val, continuous_subtypeVal⟩ =
      g.comp (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M)) :=
    ContinuousMap.ext fun x ↦ hW x x.property
  let j : C(V, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  rw [← o.localDegree_comap o' hE hF (j := j) V.isOpenEmbedding' f (hrange _ hAW), hcomp,
    o.localDegree_comap o' hE hF (j := j) V.isOpenEmbedding' g (hfib ▸ hrange _ hAW)]

/-- **The local degree is additive over open sets.** Let the fibre of `f` over `y` be compact and
covered by finitely many open sets `U i` meeting it in pairwise disjoint sets, oriented by
restricting `o`. Then the local degree of `f` at `y` is the sum of the local degrees at `y` of the
restrictions of `f` to the `U i`. For an empty family this says that a map with empty fibre has
local degree zero. -/
theorem localDegree_eq_sum (hF : finrank ℝ F = n) (f : C(M, N)) {y : N}
    (hy : IsCompact (f ⁻¹' {y})) {ι : Type*} [Fintype ι] {U : ι → TopologicalSpace.Opens M}
    (hU : Pairwise fun i k ↦ Disjoint (f ⁻¹' {y} ∩ U i) (f ⁻¹' {y} ∩ U k))
    (hyU : f ⁻¹' {y} ⊆ ⋃ i, (U i : Set M)) :
    o.localDegree o' hE f y = ∑ i, (o.comap (U i).isOpenEmbedding').localDegree o' hE
      (f.comp ⟨Subtype.val, continuous_subtypeVal⟩) y := by
  rw [localDegree_eq_iff o o' hE hF f hy, o.fundamentalClassOn_eq_sum_localHomologyMap hE hy hU hyU,
    map_sum]
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans
    (map_sum (zmultiplesHom _ (o' y).val) _ _).symm
  rw [← ModuleCat.comp_apply, localHomologyMap_comp]
  exact localHomologyMap_fundamentalClassOn_preimage_singleton (o.comap (U i).isOpenEmbedding') o'
    hE (f.comp ⟨Subtype.val, continuous_subtypeVal⟩) _

/-- **Additivity of the local degree.** Let `j₁ : M₁ → M` and `j₂ : M₂ → M` be open embeddings
whose images together contain the fibre `f⁻¹(y)` and meet it in disjoint sets, and suppose that
this fibre is compact. Then the local degree of `f` at `y` is the sum of the local degrees of
`f ∘ j₁` and `f ∘ j₂` at `y`, for the orientations pulled back along `j₁` and `j₂`. This is
`localDegree_eq_sum` for the two images, read through `j₁` and `j₂`. -/
theorem localDegree_eq_add (hF : finrank ℝ F = n) {M₁ M₂ : Type} [TopologicalSpace M₁]
    [T2Space M₁] [ChartedSpace E M₁] [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E M₂]
    {j₁ : C(M₁, M)} {j₂ : C(M₂, M)}
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (f : C(M, N)) {y : N}
    (hc : IsCompact (f ⁻¹' {y})) (hy : f ⁻¹' {y} ⊆ range j₁ ∪ range j₂)
    (hdisj : Disjoint (f ⁻¹' {y} ∩ range j₁) (f ⁻¹' {y} ∩ range j₂)) :
    o.localDegree o' hE f y =
      (o.comap hj₁).localDegree o' hE (f.comp j₁) y +
        (o.comap hj₂).localDegree o' hE (f.comp j₂) y := by
  -- Restricting `f` to the open range of an open embedding `j` gives the local degree of `f ∘ j`,
  -- since `j` is a homeomorphism onto its range.
  have hrange {M' : Type} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M'] {j : C(M', M)}
      (hj : IsOpenEmbedding j) :
      (o.comap (⟨range j, hj.isOpen_range⟩ : TopologicalSpace.Opens M).isOpenEmbedding').localDegree
        o' hE (f.comp ⟨Subtype.val, continuous_subtypeVal⟩) y =
        (o.comap hj).localDegree o' hE (f.comp j) y := by
    let k : C(M', (⟨range j, hj.isOpen_range⟩ : TopologicalSpace.Opens M)) :=
      ⟨fun x ↦ ⟨j x, mem_range_self x⟩, j.continuous.subtype_mk _⟩
    have hk : IsOpenEmbedding k :=
      (IsOpenEmbedding.of_comp_iff _ (TopologicalSpace.Opens.isOpenEmbedding' _)).1 hj
    have hkj : (⟨Subtype.val, continuous_subtypeVal⟩ : C(_, M)).comp k = j :=
      ContinuousMap.ext fun _ ↦ rfl
    rw [← (o.comap _).localDegree_comap o' hE hF hk _ fun z _ ↦
        (z.property.imp fun _ hx ↦ Subtype.ext hx),
      comap_comap_of_comp_eq _ _ hk hj rfl, ContinuousMap.comp_assoc, hkj]
  rw [o.localDegree_eq_sum o' hE hF f hc
      (U := fun b ↦ cond b ⟨range j₁, hj₁.isOpen_range⟩ ⟨range j₂, hj₂.isOpen_range⟩)
      (by rintro (_ | _) (_ | _) h <;> first | exact absurd rfl h | exact hdisj | exact hdisj.symm)
      fun x hx ↦ (hy hx).elim (fun h ↦ mem_iUnion.2 ⟨true, h⟩) fun h ↦ mem_iUnion.2 ⟨false, h⟩,
    Fintype.sum_bool]
  exact congrArg₂ (· + ·) (hrange hj₁) (hrange hj₂)

/-- **Invariance of the local degree under homotopies with compact fibre**: if `H` is a homotopy
from `f₀` to `f₁` whose fibre `H⁻¹(y) ⊆ [0, 1] × M` over `y` is compact, then `f₀` and `f₁` have
the same local degree at `y`. -/
theorem localDegree_eq_of_homotopy_of_isCompact (hF : finrank ℝ F = n) {f₀ f₁ : C(M, N)}
    (H : f₀.Homotopy f₁) {y : N} (hH : IsCompact (H ⁻¹' {y})) :
    o.localDegree o' hE f₀ y = o.localDegree o' hE f₁ y := by
  -- Both fibres over `y` lie in the compact projection `A` of `H⁻¹(y)` to `M`.
  set A : Set M := Prod.snd '' (H ⁻¹' {y})
  have hA : IsCompact A := hH.image continuous_snd
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

/-- **Invariance of the local degree under proper homotopies**: if `H` is a homotopy from `f₀`
to `f₁` which is proper as a map `[0, 1] × M → N`, then `f₀` and `f₁` have the same local degree at
every point. -/
theorem localDegree_eq_of_homotopy (hF : finrank ℝ F = n) {f₀ f₁ : C(M, N)} (H : f₀.Homotopy f₁)
    (hH : IsProperMap H) (y : N) : o.localDegree o' hE f₀ y = o.localDegree o' hE f₁ y :=
  o.localDegree_eq_of_homotopy_of_isCompact o' hE hF H (hH.isCompact_preimage isCompact_singleton)

/-- **Invariance of the degree under proper homotopies**: maps joined by a homotopy which is
proper as a map `[0, 1] × M → N` have the same degree. -/
theorem degree_eq_of_homotopy (hF : finrank ℝ F = n) {f₀ f₁ : C(M, N)} (H : f₀.Homotopy f₁)
    (hH : IsProperMap H) :
    o.degree o' hE f₀ = o.degree o' hE f₁ := by
  rcases isEmpty_or_nonempty N with h | h
  · rw [degree_of_isEmpty, degree_of_isEmpty]
  · rw [degree_eq_localDegree_some o o' hE f₀ h, degree_eq_localDegree_some o o' hE f₁ h,
      o.localDegree_eq_of_homotopy o' hE hF H hH]

section CompactSpace

variable (hF : finrank ℝ F = n) [CompactSpace M] [CompactSpace N] [PreconnectedSpace N]

/-- **The degree computes the image of the fundamental class**: for a map `f : M → N` between
compact oriented `n`-manifolds with `N` preconnected, `f_*[M] = deg f • [N]` in `Hₙ(N; ℤ)`. -/
theorem mapFundamentalClass_eq_degree_smul (f : C(M, N)) :
    o.mapFundamentalClass hE f = o.degree o' hE f • o'.fundamentalClass hF := by
  refine (singularHomologyπ_compl_univ_bijective N (ModuleCat.of ℤ (ULift.{0} ℤ)) n).1 ?_
  have h := o.localHomologyMap_fundamentalClassOn_preimage o' hE hF f.continuous.isProperMap
    isCompact_univ
  rw [← o.localHomologyRestriction_fundamentalClassOn_of_subset hE isCompact_univ _
    (subset_univ _), ← ModuleCat.comp_apply, localHomologyRestriction_comp_localHomologyMap] at h
  -- Both sides are read in `Hₙ(N, N ∖ N; ℤ)`, where `[N]` maps to `[N]` along `N`.
  exact (o.singularHomologyπ_mapFundamentalClass hE f).trans (h.trans
    ((congrArg (o.degree o' hE f • ·)
      (o'.singularHomologyπ_fundamentalClass hF isCompact_univ)).symm.trans
      (map_zsmul _ _ _).symm))

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

/-- **A self-map acts on top homology by its degree**: for a self-map `f` of a compact connected
oriented `n`-manifold, `f_*` is multiplication by the degree of `f` on `Hₙ(M; ℤ)`. -/
theorem singularHomologyMap_eq_degree_smul [ConnectedSpace M] (f : C(M, M))
    (γ : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom γ = o.degree o hE f • γ := by
  obtain ⟨d, rfl⟩ := o.exists_eq_zsmul_fundamentalClass hE γ
  have h := o.mapFundamentalClass_eq_degree_smul o hE hE f
  rw [mapFundamentalClass_def] at h
  exact (map_zsmul _ d _).trans ((congrArg (d • ·) h).trans (zsmul_comm _ _ _))

end CompactSpace

/-- **The degree detects isomorphisms on top homology.** For a map `f : M → N` between compact
connected oriented `n`-manifolds, `f_* : Hₙ(M; ℤ) → Hₙ(N; ℤ)` is bijective exactly when the degree
of `f` is `±1`: in the generators `[M]` and `[N]` of these infinite cyclic groups, `f_*` is
multiplication by the degree. -/
theorem bijective_singularHomologyFunctor_map_iff (hF : finrank ℝ F = n)
    [CompactSpace M] [CompactSpace N] [ConnectedSpace M] [ConnectedSpace N] (f : C(M, N)) :
    Function.Bijective (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom ↔
      o.degree o' hE f = 1 ∨ o.degree o' hE f = -1 := by
  -- `f_*`, typed on the homology groups in which the fundamental classes live.
  let φ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
        ModuleCat.{0} ℤ) :=
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom
  -- In the bases `[M]` and `[N]`, `f_*` is multiplication by the degree.
  have key : ⇑φ = o'.fundamentalClassEquiv hF ∘ (· * o.degree o' hE f) ∘
      (o.fundamentalClassEquiv hE).symm := by
    funext γ
    obtain ⟨c, rfl⟩ := (o.fundamentalClassEquiv hE).surjective γ
    have h := o.mapFundamentalClass_eq_degree_smul o' hE hF f
    rw [mapFundamentalClass_def] at h
    rw [Function.comp_apply, Function.comp_apply, LinearEquiv.symm_apply_apply,
      fundamentalClassEquiv_apply, fundamentalClassEquiv_apply, map_zsmul]
    exact (congrArg (c • ·) h).trans (smul_smul _ _ _)
  change Function.Bijective φ ↔ _
  rw [key, (o'.fundamentalClassEquiv hF).bijective.of_comp_iff',
    Function.Bijective.of_comp_iff _ (o.fundamentalClassEquiv hE).symm.bijective, ← Int.isUnit_iff]
  exact IsUnit.isUnit_iff_mulRight_bijective.symm

/-- **The degree detects isomorphisms on integral top homology.** For a map `f : M → N` between
compact connected oriented `n`-manifolds, `f_* : Hₙ(M; ℤ) → Hₙ(N; ℤ)` on singular homology with
coefficients in the ring `ℤ` is bijective exactly when the degree of `f` is `±1`. -/
theorem bijective_singularHomologyMap_iff (hF : finrank ℝ F = n)
    [CompactSpace M] [CompactSpace N] [ConnectedSpace M] [ConnectedSpace N] (f : C(M, N)) :
    Function.Bijective (ContinuousMap.singularHomologyMap ℤ n f) ↔
      o.degree o' hE f = 1 ∨ o.degree o' hE f = -1 := by
  -- The coefficient modules `ULift ℤ` and `ℤ` give naturally isomorphic homology functors.
  let α := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).mapIso
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  -- `ContinuousMap.singularHomologyMap ℤ n f` is by definition the map of the homology functor
  -- with coefficients `ℤ`, but its source and target are stated through `singularChains`.
  change Function.Bijective (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) ↔ _
  rw [← o.bijective_singularHomologyFunctor_map_iff o' hE hF f,
    ← ConcreteCategory.isIso_iff_bijective, ← ConcreteCategory.isIso_iff_bijective]
  exact (NatIso.isIso_map_iff α (TopCat.ofHom f)).symm

end HomologicalOrientation

end TauCeti
