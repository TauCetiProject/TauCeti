/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# Thom classes of oriented vector bundles

Let `E → B` be a real vector bundle with model fibre `F` of finite dimension `r`. A linear
trivialization `e` identifies the fibre pair `(E_b, E_b ∖ {0})` over a point `b` of its base set
with `(F, F ∖ {0})` (`ContinuousLinearEquiv.complZeroPairIso` of
`Bundle.Trivialization.continuousLinearEquivAt`), so it pulls a class `g ∈ Hⁿ(F, F ∖ {0})` back
to a class of the fibre pair. A second trivialization `e'` differs from `e` over `b` by the
coordinate change `F ≃ F`, which acts on `Hⁿ(F, F ∖ {0})` by the sign of its determinant, so the
two pull-backs of `g` agree up to that sign
(`Bundle.Trivialization.singularCohomologyMap_complZeroPairIso_hom_eq_sign_smul`, in
`TauCeti.Topology.VectorBundle.ThomClass`). Hence they are equal when the two trivializations read
an orientation of the fibre as the same orientation of `F`, and opposite when they read it as
opposite orientations.

An orientation `o` of the bundle (`TauCeti.VectorBundleOrientation`) is a continuous choice of
fibre orientations. Fix an orientation `ω` of `F` and a class `g ∈ Hʳ(F, F ∖ {0})`. Pulling back
`g` along a trivialization reading `o` as `ω`, or `-g` along one reading it as `-ω`, gives the same
class of each fibre pair
(`singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg`, in the namespace
`Bundle.Trivialization`).
So the local Thom classes over trivializing sets that pull back `g` where the trivialization reads
`o` as `ω`, and `-g` where it reads `o` as `-ω`, have the same restrictions to the fibres wherever
two of them meet. Over a compact base finitely many of them cover, and they glue by Mayer–Vietoris
(`TauCeti.exists_singularCohomology_thomPairOver_biUnion`) to a class `u ∈ Hʳ(E, E₀)`: for every
linear trivialization `e` and point `b` of its base set, the restriction of `u` to the fibre over
`b` is the pull-back of `g` along `e` if `e` reads `o b` as `ω`, and of `-g` if `e` reads it as
`-ω`. Since a class in the top degree over a compact base is determined on the fibres
(`TauCeti.singularCohomology_thomPair_ext_of_compactSpace`), this characterizes `u`
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`). It is
the **Thom class of the oriented bundle normalized by `(ω, g)`**,
`TauCeti.VectorBundleOrientation.thomClass o hι ω g`.

When `g` generates `Hʳ(F, F ∖ {0}; K) ≅ K`, this class is a Thom class with coefficients in the
commutative ring `K` (`TauCeti.VectorBundleOrientation.isThomClass_thomClass`), so every oriented
real vector bundle over a compact base has a Thom class with coefficients in any commutative ring
(`TauCeti.VectorBundleOrientation.exists_isThomClass_of_compactSpace`), in particular an integral
one. Its image under `TauCeti.eulerClass` is an Euler class of the oriented bundle. The Thom class
is determined by `o` only together with the normalization `(ω, g)`: the theorems here fix no
preferred orientation of `F` or generator `g`. Without an orientation,
`TauCeti.exists_isThomClass_of_compactSpace` matches the fibre generators over a ring whose only
unit is `1`, such as `ZMod 2`. Over a noncompact base the gluing needs infinitely many local
classes, and is not carried out here.

## Main results

* In the namespace `Bundle.Trivialization`:
  * `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq`,
    `singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg`: two
    trivializations reading a fibre orientation the same way pull back classes the same way, and
    two reading it oppositely pull them back to opposite classes.
  * `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg`: pulling back
    `g` where a trivialization reads a fibre orientation as `ω`, and `-g` where it reads it as
    `-ω`, does not depend on the trivialization.
* `TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`: over
  a compact base, an oriented bundle has a unique class of `Hʳ(E, E₀)` with the fibre restrictions
  prescribed by the orientation and a class of `Hʳ(F, F ∖ {0})`.
* `TauCeti.VectorBundleOrientation.thomClass`: this class, the Thom class of the oriented bundle
  normalized by `(ω, g)`. Its fibre restrictions are
  `singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq` and
  `singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg`, and
  `eq_thomClass_of_forall` characterizes it.
* `TauCeti.VectorBundleOrientation.isThomClass_thomClass`: normalized by a generator, it is a Thom
  class.
* `TauCeti.VectorBundleOrientation.exists_isThomClass_of_compactSpace`: an oriented real vector
  bundle over a compact base has a Thom class with coefficients in any commutative ring.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10, Theorem 10.4 and its proof (Lemmas 10.2 and 10.3).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

universe w

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B}
  (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
  {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K} [Module.Projective K R']

variable {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  {o : Orientation ℝ (E b) ι}

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as the same
orientation of the model fibre pull back every class of `Hⁿ(F, F ∖ {0})` to the same class of the
fibre pair. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq
    (h : e'.mapOrientation ι hb' o = e.mapOrientation ι hb o) {n : ℕ}
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_iff_det_pos _ _ hι] at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : 0 < (e.coordChangeL ℝ e' b : F →L[ℝ] F).det := h
  rw [e.singularCohomologyMap_complZeroPairIso_hom_eq_sign_smul e' hb hb', sign_pos hd,
    SignType.coe_one, one_smul]

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as opposite
orientations of the model fibre pull back every class of `Hⁿ(F, F ∖ {0})` to opposite classes of
the fibre pair. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg
    (h : e'.mapOrientation ι hb' o = -e.mapOrientation ι hb o) {n : ℕ}
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g =
      -TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_neg_iff_det_neg _ _ hι]
    at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : (e.coordChangeL ℝ e' b : F →L[ℝ] F).det < 0 := h
  rw [e.singularCohomologyMap_complZeroPairIso_hom_eq_sign_smul e' hb hb', sign_neg hd,
    SignType.coe_neg_one, neg_one_smul]

include hι in
/-- Pulling back `g` along a linear trivialization that reads an orientation of the fibre over `b`
as `ω`, or `-g` along one that reads it as `-ω`, gives a class of the fibre pair that does not
depend on the trivialization. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg
    {ω : Orientation ℝ F ι} {n : ℕ}
    {g g₁ g₂ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n}
    (h₁ : e.mapOrientation ι hb o = ω ∧ g₁ = g ∨ e.mapOrientation ι hb o = -ω ∧ g₁ = -g)
    (h₂ : e'.mapOrientation ι hb' o = ω ∧ g₂ = g ∨ e'.mapOrientation ι hb' o = -ω ∧ g₂ = -g) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g₂ =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g₁ := by
  rcases h₁ with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases h₂ with ⟨h₂, rfl⟩ | ⟨h₂, rfl⟩
  · exact e.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e' hb hb' hι
      (h₂.trans h₁.symm) _
  · rw [map_neg, e.singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e' hb
      hb' hι (by rw [h₁, h₂]), neg_neg]
  · rw [map_neg, e.singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e' hb
      hb' hι (by rw [h₁, h₂]; exact (neg_neg ω).symm)]
  · exact e.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e' hb hb' hι
      (h₂.trans h₁.symm) _

end Bundle.Trivialization

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι] [CompactSpace B]

/-- **The Thom class of an oriented vector bundle over a compact base.** Let `o` be an orientation
of the real vector bundle `E` of rank `r = card ι` over a compact base, `ω` an orientation of the
model fibre `F` and `g` a class of `Hʳ(F, F ∖ {0}; R, M)`, `R` projective. There is a unique class
`u ∈ Hʳ(E, E₀; R, M)` such that for every linear trivialization `e` and every point `b` of its base
set, the restriction of `u` to the fibre pair `(E_b, E_b ∖ {0})` is the pull-back of `g` along the
isomorphism `(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})` given by `e` if `e` reads `o b` as `ω`, and the
pull-back of `-g` if `e` reads `o b` as `-ω`. -/
theorem existsUnique_singularCohomology_thomPair_of_compactSpace
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
    [Module.Projective K R']
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) :
    ∃! u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F),
      ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        (e.mapOrientation ι hb (o b) = ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
        (e.mapOrientation ι hb (o b) = -ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            -TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) := by
  let e (c : B) := trivializationAt F E c
  -- For `p = (c, g')`, the open subset of the base set of `e c` where `e c` reads `o` as `ω` and
  -- `g' = g`, or as `-ω` and `g' = -g`.
  let W (p : B × (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) : Set B :=
    {b | ∃ hb : b ∈ (e p.1).baseSet, (e p.1).mapOrientation ι hb (o b) = ω ∧ p.2 = g ∨
      (e p.1).mapOrientation ι hb (o b) = -ω ∧ p.2 = -g}
  have hWe p : W p ⊆ (e p.1).baseSet := fun _ hb ↦ hb.1
  have hWo p : IsOpen (W p) := isOpen_iff_mem_nhds.2 fun b ⟨hb, hbo⟩ ↦ by
    filter_upwards [o.eventually_mapOrientation_eq hι (e p.1) hb,
      (e p.1).open_baseSet.mem_nhds hb] with x hx hxs
    exact ⟨hxs, by rwa [hx hxs]⟩
  -- Every point lies in one of these sets, so finitely many of them cover the compact base.
  have hcover (b : B) : ∃ g', b ∈ W (b, g') := by
    have hb := mem_baseSet_trivializationAt F E b
    rcases Orientation.eq_or_eq_neg ((e b).mapOrientation ι hb (o b)) ω hι with h | h
    exacts [⟨g, hb, .inl ⟨h, rfl⟩⟩, ⟨-g, hb, .inr ⟨h, rfl⟩⟩]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun b _ ↦
    mem_iUnion.2 ⟨_, (hcover b).choose_spec⟩
  -- The local classes over the sets `W p`, glued over the finite subcover.
  choose u hu using fun p ↦ (e p.1).exists_singularCohomology_thomPairOver_fiber ℝ (hWe p) p.2
  obtain ⟨x, hx⟩ := exists_singularCohomology_thomPairOver_biUnion t (fun p _ ↦ hWo p)
    (fun p _ ↦ ⟨e p.1, inferInstance, hWe p⟩) u fun p _ q _ b hp hq ↦ by
      rw [hu p b hp, hu q b hq]
      exact (e q.1).singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg
        (e p.1) (hWe q hq) (hWe p hp) hι hq.2 hp.2
  -- The restriction of the glued class to the fibre over `b` is that of a local class.
  have hfib (e' : Trivialization F (π F E)) [e'.IsLinear ℝ] (b : B) (hb' : b ∈ e'.baseSet)
      (g' : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
        (finrank ℝ F))
      (hg' : e'.mapOrientation ι hb' (o b) = ω ∧ g' = g ∨
        e'.mapOrientation ι hb' (o b) = -ω ∧ g' = -g) :
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) _
        (TopPair.singularCohomologyMap ((thomPairOverUnivIso F E).inv ≫ thomPairOverMap F E ht)
          _ x) =
        TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom _
          g' := by
    obtain ⟨p, hpt, hbp⟩ := mem_iUnion₂.1 (ht (mem_univ b))
    rw [← TopPair.singularCohomologyMap_comp_apply,
      fiberThomPairMap_comp_thomPairOverUnivIso_inv_comp_thomPairOverMap F E ht
        (Finset.subset_set_biUnion_of_mem (f := W) hpt) hbp,
      TopPair.singularCohomologyMap_comp_apply, hx p hpt, hu p b hbp]
    exact e'.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg (e p.1)
      hb' (hWe p hbp) hι hg' hbp.2
  refine ⟨TopPair.singularCohomologyMap ((thomPairOverUnivIso F E).inv ≫ thomPairOverMap F E ht)
    _ x, fun e' _ b hb' ↦ ⟨fun h ↦ hfib e' b hb' g (.inl ⟨h, rfl⟩), fun h ↦ ?_⟩, fun v hv ↦ ?_⟩
  · rw [hfib e' b hb' (-g) (.inr ⟨h, rfl⟩), map_neg]
  · -- Uniqueness: both classes have the same restriction to every fibre.
    refine singularCohomology_thomPair_ext_of_compactSpace fun b ↦ ?_
    have hb := mem_baseSet_trivializationAt F E b
    rcases Orientation.eq_or_eq_neg ((e b).mapOrientation ι hb (o b)) ω hι with h | h
    · rw [(hv (e b) b hb).1 h, hfib (e b) b hb g (.inl ⟨h, rfl⟩)]
    · rw [(hv (e b) b hb).2 h, hfib (e b) b hb (-g) (.inr ⟨h, rfl⟩), map_neg]

section ThomClass

variable (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι) {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
  [Module.Projective K R']
  (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
    (finrank ℝ F))

/-- **The Thom class of an oriented vector bundle over a compact base**, normalized by an
orientation `ω` of the model fibre `F` and a class `g ∈ Hʳ(F, F ∖ {0}; R, M)`: the unique class of
`Hʳ(E, E₀; R, M)` whose restriction to the fibre pair over a point `b` of the base set of a linear
trivialization `e` is the pull-back of `g` along `e` if `e` reads `o b` as `ω`, and of `-g` if `e`
reads `o b` as `-ω`
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`). When
`g` generates `Hʳ(F, F ∖ {0}; K, K) ≅ K` it is a Thom class
(`TauCeti.VectorBundleOrientation.isThomClass_thomClass`). -/
def thomClass : (thomPair F E).singularCohomology R' K M' (finrank ℝ F) :=
  (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose

variable {hι ω g}

/-- Over a point where a linear trivialization `e` reads the orientation as `ω`, the restriction
of the Thom class `thomClass o hι ω g` to the fibre pair is the pull-back of `g` along `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hι ω g) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  ((o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec
    e b hb).1 h

/-- Over a point where a linear trivialization `e` reads the orientation as `-ω`, the restriction
of the Thom class `thomClass o hι ω g` to the fibre pair is the pull-back of `-g` along `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = -ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hι ω g) =
      -TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  ((o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec
    e b hb).2 h

/-- A class of `Hʳ(E, E₀; R, M)` whose fibre restrictions are those prescribed by `o`, `ω` and `g`
is the Thom class `thomClass o hι ω g`. -/
theorem eq_thomClass_of_forall {u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)}
    (hu : ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
      (e.mapOrientation ι hb (o b) = ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
      (e.mapOrientation ι hb (o b) = -ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          -TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g)) :
    u = o.thomClass hι ω g :=
  (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).unique hu
    (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec

end ThomClass

/-- **The Thom class of an oriented bundle normalized by a generator is a Thom class**: if `g`
generates `Hʳ(F, F ∖ {0}; K, K) ≅ K`, then `thomClass o hι ω g` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K, K)` on every fibre. -/
theorem isThomClass_thomClass (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) : IsThomClass F E (o.thomClass hι ω g) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun b ↦ ?_⟩
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  -- The pull-back of `g` along the isomorphism of fibre pairs given by `e` generates.
  have hge : Submodule.span K
      {TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (finrank ℝ F) g} = ⊤ := by
    let L := ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)).mapIso (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.op).toLinearEquiv
    exact L.span_singleton_apply_eq_top_iff.2 hg
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι with h | h
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq e hb h]
    exact hge
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg e hb h,
      ← Set.neg_singleton, Submodule.span_neg]
    exact hge

/-- **An oriented real vector bundle over a compact base has a Thom class** with coefficients in
any commutative ring `K`, in particular an integral one: a class of `Hʳ(E, E₀; K, K)`,
`r = dim F`, restricting to a generator of `Hʳ(E_b, E_b ∖ {0}; K, K) ≅ K` on every fibre. It is
`thomClass o hι ω g` for an orientation `ω` of `F` and a generator `g` of
`Hʳ(F, F ∖ {0}; K, K)` (`TauCeti.VectorBundleOrientation.isThomClass_thomClass`). -/
theorem exists_isThomClass_of_compactSpace (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (K : Type w) [CommRing K] :
    ∃ u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      IsThomClass F E u := by
  classical
  -- A generator `g` of the local cohomology `Hʳ(F, F ∖ {0}; K) ≅ K` and an orientation of `F`.
  obtain ⟨g, hg⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)
  exact ⟨_, o.isThomClass_thomClass hι
    ((finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation hg⟩

end TauCeti.VectorBundleOrientation
