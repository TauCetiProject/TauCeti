/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Thom classes of trivial and trivializable bundles

The trivial bundle `B × F → B` with finite-dimensional real fibre `F` of rank `r` has Thom pair
`(B × F, B × (F ∖ {0}))`, and the projection to the fibre is a map of pairs
`(B × F, B × (F ∖ {0})) ⟶ (F, F ∖ {0})` (`TauCeti.trivialThomPairMap`). Restricted to the fibre over
any point, it is the identity of `(F, F ∖ {0})`. So the pull-back `p^* u` of a class
`u ∈ Hʳ(F, F ∖ {0})` restricts to `u` on every fibre, and it is a Thom class
(`TauCeti.IsThomClass`) exactly when `u` generates `Hʳ(F, F ∖ {0})`, provided the base is nonempty
(`TauCeti.isThomClass_singularCohomologyMap_trivialThomPairMap_iff`).

With coefficients in a commutative ring `k`, the local cohomology `Hʳ(F, F ∖ {0}; k, k)` is one
copy of `k` (`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`), so it has a generator,
and every trivial bundle has a Thom class (`TauCeti.exists_isThomClass_trivial`). This is the local
model of the Thom isomorphism: a vector bundle is locally trivial, and an orientation selects a
compatible family of these local Thom classes.

A trivialization `e` of a real vector bundle `E` over the whole base is linear on the fibres, so it
gives an isomorphism of Thom pairs `(E, E₀) ≅ (B × F, B × (F ∖ {0}))`
(`Bundle.Trivialization.thomPairIso`), restricting on each fibre to the linear isomorphism
`E_b ≅ F` (`Bundle.Trivialization.fiberThomPairMap_comp_thomPairIso_hom`). Pulling back along it
identifies the Thom classes of `E` with those of the trivial bundle
(`Bundle.Trivialization.isThomClass_singularCohomologyMap_thomPairIso_hom_iff`), so a bundle with
a global trivialization has a Thom class (`Bundle.Trivialization.exists_isThomClass`). Any
trivialization pulls back to a global trivialization of the restriction of `E` to its base set, so
these restrictions have Thom classes (`Bundle.Trivialization.exists_isThomClass_pullback_baseSet`):
these are the local Thom classes over trivializing open sets that the Mayer–Vietoris argument of
Milnor and Stasheff (§10) glues to a Thom class of a general oriented bundle. That gluing is not
formalized here.

## Main definitions and results

* `TauCeti.trivialThomPairMap`: the projection of the Thom pair of the trivial bundle onto the
  fibre pair `(F, F ∖ {0})`.
* `TauCeti.fiberThomPairMap_comp_trivialThomPairMap`: the projection restricts to the identity on
  every fibre.
* `TauCeti.isThomClass_singularCohomologyMap_trivialThomPairMap_iff`: the pull-back of a class of
  the fibre pair is a Thom class iff that class generates.
* `TauCeti.exists_isThomClass_trivial`: the trivial bundle has a Thom class with coefficients in
  any commutative ring.
* `Bundle.Trivialization.thomPairIso`: the isomorphism of Thom pairs given by a trivialization over
  the whole base.
* `Bundle.Trivialization.isThomClass_singularCohomologyMap_thomPairIso_hom_iff`: it identifies the
  Thom classes of the bundle with those of the trivial bundle.
* `Bundle.Trivialization.exists_isThomClass`: a bundle with a global trivialization has a Thom
  class.
* `Bundle.Trivialization.exists_isThomClass_pullback_baseSet`: the restriction of a bundle to the
  base set of any trivialization has a Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism, first for trivial bundles).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable (B : Type w) [TopologicalSpace B] (F : Type w) {C : Type u} [Category.{v} C]
  [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}

section Projection

variable [TopologicalSpace F] [Zero F]

/-- The projection `(B × F, B × (F ∖ {0})) ⟶ (F, F ∖ {0})` of the Thom pair of the trivial bundle
onto its fibre pair. -/
def trivialThomPairMap :
    thomPair F (Bundle.Trivial B F) ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetMap
    (TopCat.ofHom ⟨TotalSpace.trivialSnd B F,
      continuous_snd.comp (Bundle.Trivial.homeomorphProd B F).continuous⟩)
    fun _ hv ↦ mem_zeroSectionCompl.1 hv

@[simp]
theorem trivialThomPairMap_fst_apply (v : TotalSpace F (Bundle.Trivial B F)) :
    TopPair.Hom.fst (trivialThomPairMap B F) v = v.2 := by
  unfold trivialThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The projection of the Thom pair of the trivial bundle onto its fibre pair restricts to the
identity of `(F, F ∖ {0})` on the fibre over every point. -/
theorem fiberThomPairMap_comp_trivialThomPairMap (b : B) :
    fiberThomPairMap F (Bundle.Trivial B F) b ≫ trivialThomPairMap B F = 𝟙 _ := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (congrArg _ (fiberThomPairMap_fst_apply F _ b v)).trans (trivialThomPairMap_fst_apply B F _)

/-- The pull-back of a class `u ∈ Hⁿ(F, F ∖ {0})` along the projection of the Thom pair of the
trivial bundle restricts to `u` on the fibre over every point. -/
theorem singularCohomologyMap_fiberThomPairMap_trivialThomPairMap (b : B) {n : ℕ}
    (u : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (fiberThomPairMap F (Bundle.Trivial B F) b) n
        (TopPair.singularCohomologyMap (trivialThomPairMap B F) n u) = u := by
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
    fiberThomPairMap_comp_trivialThomPairMap, TopPair.singularCohomologyMap_id,
    ConcreteCategory.id_apply]

end Projection

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Thom classes of the trivial bundle**: over a nonempty base, the pull-back of a class
`u ∈ Hʳ(F, F ∖ {0})`, for `r = finrank ℝ F`, along the projection of the Thom pair onto the fibre
pair is a Thom class of the trivial bundle exactly when `u` generates `Hʳ(F, F ∖ {0})` and `F` is
finite-dimensional. -/
theorem isThomClass_singularCohomologyMap_trivialThomPairMap_iff [Nonempty B]
    (u : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R k M
      (finrank ℝ F)) :
    IsThomClass F (Bundle.Trivial B F)
        (TopPair.singularCohomologyMap (trivialThomPairMap B F) _ u) ↔
      FiniteDimensional ℝ F ∧ Submodule.span k {u} = ⊤ := by
  simp only [isThomClass_iff, singularCohomologyMap_fiberThomPairMap_trivialThomPairMap]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h (Classical.arbitrary B), fun h _ ↦ h⟩

/-- **The trivial bundle has a Thom class** with coefficients in any commutative ring `K`: the
pull-back of a generator of the local cohomology `Hʳ(F, F ∖ {0}; K, K) ≅ K` along the projection
onto the fibre pair. -/
theorem exists_isThomClass_trivial (K : Type w) [CommRing K] [FiniteDimensional ℝ F] :
    ∃ u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
        (ModuleCat.of K K) (finrank ℝ F), IsThomClass F (Bundle.Trivial B F) u := by
  obtain ⟨u, hu⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)
  exact ⟨TopPair.singularCohomologyMap (trivialThomPairMap B F) _ u,
    isThomClass_iff.2 ⟨inferInstance, fun b ↦ by
      rw [singularCohomologyMap_fiberThomPairMap_trivialThomPairMap B F b u]
      exact hu⟩⟩

end TauCeti

namespace Bundle.Trivialization

open TauCeti

section Geometry

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear 𝕜]

/-- A trivialization over the whole base, as an isomorphism `(E, E₀) ≅ (B × F, B × (F ∖ {0}))` of
the Thom pair of `E` with the Thom pair of the trivial bundle: it is linear on the fibres, so it
carries the nonzero vectors onto the nonzero vectors. -/
def thomPairIso (he : e.baseSet = Set.univ) :
    thomPair F E ≅ thomPair F (Bundle.Trivial B F) :=
  TopPair.ofSubsetIso (X := TopCat.of (TotalSpace F E))
    (Y := TopCat.of (TotalSpace F (Bundle.Trivial B F))) (e.homeomorphTrivial he) fun v ↦ by
      rw [mem_zeroSectionCompl, mem_zeroSectionCompl,
        homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜]
      exact (map_ne_zero_iff _ (ContinuousLinearEquiv.injective _)).symm

@[simp]
theorem thomPairIso_hom_fst_apply (he : e.baseSet = Set.univ) (v : TotalSpace F E) :
    TopPair.Hom.fst (e.thomPairIso 𝕜 he).hom v = e.homeomorphTrivial he v := by
  rw [thomPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

@[simp]
theorem thomPairIso_inv_fst_apply (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    TopPair.Hom.fst (e.thomPairIso 𝕜 he).inv w = (e.homeomorphTrivial he).symm w := by
  rw [thomPairIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The fibre of a trivialization over `b`, as an isomorphism of fibre pairs
`(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})`. -/
def fiberPairIso {b : B} (hb : b ∈ e.baseSet) :
    TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b)) ≅
      TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetIso (X := TopCat.of (E b)) (Y := TopCat.of F)
    (e.continuousLinearEquivAt 𝕜 b hb).toHomeomorph fun _ ↦ by
      rw [Set.mem_compl_singleton_iff, Set.mem_compl_singleton_iff]
      exact (map_ne_zero_iff (e.continuousLinearEquivAt 𝕜 b hb)
        (ContinuousLinearEquiv.injective _)).symm

@[simp]
theorem fiberPairIso_hom_fst_apply {b : B} (hb : b ∈ e.baseSet) (x : E b) :
    TopPair.Hom.fst (e.fiberPairIso 𝕜 hb).hom x = e.continuousLinearEquivAt 𝕜 b hb x := by
  rw [fiberPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

@[simp]
theorem fiberPairIso_inv_fst_apply {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TopPair.Hom.fst (e.fiberPairIso 𝕜 hb).inv y = (e.continuousLinearEquivAt 𝕜 b hb).symm y := by
  rw [fiberPairIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- On the fibre over `b`, the isomorphism of Thom pairs given by a trivialization over the whole
base is the isomorphism of fibre pairs given by the trivialization at `b`. -/
theorem fiberThomPairMap_comp_thomPairIso_hom (he : e.baseSet = Set.univ) (b : B) :
    fiberThomPairMap F E b ≫ (e.thomPairIso 𝕜 he).hom =
      (e.fiberPairIso 𝕜 (he ▸ Set.mem_univ b)).hom ≫ fiberThomPairMap F (Bundle.Trivial B F) b := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E b) ↦ ?_)
  -- Both sides send `x : E_b` to `(b, e x)`. The carriers of the pairs agree with `E_b`, `F` and
  -- the total spaces only up to unfolding, so first split each composite into its evaluations.
  change TopPair.Hom.fst (e.thomPairIso 𝕜 he).hom (TopPair.Hom.fst (fiberThomPairMap F E b) x) =
    TopPair.Hom.fst (fiberThomPairMap F (Bundle.Trivial B F) b)
      (TopPair.Hom.fst (e.fiberPairIso 𝕜 (he ▸ Set.mem_univ b)).hom x)
  simp only [fiberThomPairMap_fst_apply, thomPairIso_hom_fst_apply,
    homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜, fiberPairIso_hom_fst_apply]
  -- `TotalSpace.mk'` is `TotalSpace.mk` with the fibre made explicit.
  rfl

end Geometry

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k]
  [Linear k C] {M : C} {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]

/-- **Thom classes of a trivializable bundle.** For a trivialization of `E` over the whole base,
the pull-back of a class `u` of the Thom pair of the trivial bundle `B × F` along the isomorphism
of Thom pairs `(E, E₀) ≅ (B × F, B × (F ∖ {0}))` is a Thom class of `E` exactly when `u` is a Thom
class of the trivial bundle. -/
theorem isThomClass_singularCohomologyMap_thomPairIso_hom_iff (he : e.baseSet = Set.univ)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology R k M (finrank ℝ F)} :
    IsThomClass F E (TopPair.singularCohomologyMap (e.thomPairIso ℝ he).hom _ u) ↔
      IsThomClass F (Bundle.Trivial B F) u := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ hu.singularCohomologyMap _ id _
    (e.fiberThomPairMap_comp_thomPairIso_hom ℝ he)⟩
  -- Pull back along the inverse isomorphism, whose fibres are the inverse fibre isomorphisms.
  have h := hu.singularCohomologyMap (e.thomPairIso ℝ he).inv id
    (fun b ↦ (e.fiberPairIso ℝ (he ▸ Set.mem_univ b)).symm) fun b ↦ by
      rw [id_eq, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc,
        ← e.fiberThomPairMap_comp_thomPairIso_hom ℝ he, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  rwa [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, Iso.inv_hom_id,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply] at h

variable [FiniteDimensional ℝ F]

/-- **A trivializable bundle has a Thom class** with coefficients in any commutative ring `K`: the
pull-back of a Thom class of the trivial bundle along a trivialization over the whole base. -/
theorem exists_isThomClass (he : e.baseSet = Set.univ) (K : Type w) [CommRing K] :
    ∃ u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
        (finrank ℝ F), IsThomClass F E u := by
  obtain ⟨u, hu⟩ := exists_isThomClass_trivial B F K
  exact ⟨_, (e.isThomClass_singularCohomologyMap_thomPairIso_hom_iff he).2 hu⟩

/-- **Local Thom classes.** Over the base set `U` of any trivialization, the restriction
`E|_U`, the pullback of `E` along the inclusion `U → B`, has a Thom class with coefficients in any
commutative ring `K`. -/
theorem exists_isThomClass_pullback_baseSet (K : Type w) [CommRing K] :
    ∃ u : (thomPair F ((⇑(ContinuousMap.subtypeVal e.baseSet)) *ᵖ E)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      IsThomClass F ((⇑(ContinuousMap.subtypeVal e.baseSet)) *ᵖ E) u :=
  (e.pullback (ContinuousMap.subtypeVal e.baseSet)).exists_isThomClass
    (Set.eq_univ_of_forall fun b ↦ b.2) K

end Bundle.Trivialization
