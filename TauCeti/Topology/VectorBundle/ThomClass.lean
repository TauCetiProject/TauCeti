/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Linear
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
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
Milnor and Stasheff (§10) glues to a Thom class of a general oriented bundle. The gluing over
finite trivializing covers is in `TauCeti.Topology.VectorBundle.MayerVietoris.Basic`.

The gluing works with the Thom pair `(E|_W, E₀|_W)` of the restriction of `E` to a subset `W` of
the base (`TauCeti.thomPairOver`). When `W` lies in the base set of a linear trivialization `e`,
the trivialization identifies this pair with the Thom pair `(W × F, W × (F ∖ {0}))` of the product
bundle (`Bundle.Trivialization.thomPairOverIso`), which on the fibre over `b ∈ W` is the
isomorphism of fibre pairs given by `e` at `b`
(`Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom`). Pulling back a class of
`(F, F ∖ {0})` along it gives classes over `W` with prescribed restrictions to the fibres
(`Bundle.Trivialization.exists_singularCohomology_thomPairOver_fiber`), and a class over `W` in the
top degree is determined by those restrictions
(`Bundle.Trivialization.singularCohomology_thomPairOver_ext`).

The Thom pair of the trivial bundle is that of the product bundle `B × F`
(`TauCeti.trivialThomPairIso`), whose cohomology is computed up to the rank in
`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair`. With coefficients `Hom(C(-; R), M)` for
`k`-modules `R` and `M`, `R` projective, this gives the two facts about a trivializable bundle that
the gluing uses: `Hⁿ(E, E₀) = 0` for `n < r`
(`Bundle.Trivialization.isZero_singularCohomology_thomPair`), and a class of `Hʳ(E, E₀)`, for
instance a Thom class, is determined by its restrictions to the fibres
(`Bundle.Trivialization.singularCohomology_thomPair_ext`).

Two linear trivializations whose base sets contain `b` read a class of `(F, F ∖ {0})` as classes of
the fibre pair over `b` differing by the sign of the determinant of their coordinate change at `b`
(`Bundle.Trivialization.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`): an invertible
linear map acts on `Hⁿ(F, F ∖ {0})` by the sign of its determinant. This is the transition rule
for the fibre classes of an oriented bundle.

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
* `TauCeti.trivialThomPairIso`: the Thom pair of the trivial bundle is that of the product bundle.
* `Bundle.Trivialization.isZero_singularCohomology_thomPair`: the relative cohomology of the Thom
  pair of a trivializable bundle vanishes below the rank.
* `Bundle.Trivialization.singularCohomology_thomPair_ext`: a class of a trivializable bundle in
  degree the rank is determined by its restrictions to the fibres.
* `Bundle.Trivialization.thomPairOverIso`: over a subset of the base set of a linear
  trivialization, the Thom pair of the restriction is the Thom pair of a product bundle.
* `Bundle.Trivialization.exists_singularCohomology_thomPairOver_fiber`: local classes over a
  trivializing set with prescribed restrictions to the fibres.
* `Bundle.Trivialization.singularCohomology_thomPairOver_ext`: over a trivializing set, a class in
  the top degree is determined on the fibres.
* `Bundle.Trivialization.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`: fibre classes
  read in two trivializations differ by the sign of the coordinate change.

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

/-- The Thom pair of the trivial bundle `Bundle.Trivial B F` is the Thom pair
`(B × F, B × (F ∖ {0}))` of the product bundle, through `Bundle.Trivial.homeomorphProd`. -/
def trivialThomPairIso :
    thomPair F (Bundle.Trivial B F) ≅ prodThomPair B F :=
  TopPair.ofSubsetIso (X := TopCat.of (TotalSpace F (Bundle.Trivial B F)))
    (Y := TopCat.of (B × F)) (Bundle.Trivial.homeomorphProd B F) fun v ↦ by
      simp [mem_zeroSectionCompl]

omit [NormedSpace ℝ F] in
@[simp]
theorem trivialThomPairIso_hom_fst_apply
    (v : TotalSpace F (Bundle.Trivial B F)) :
    TopPair.Hom.fst (trivialThomPairIso B F).hom v = (v.1, v.2) := by
  rw [trivialThomPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

omit [NormedSpace ℝ F] in
@[simp]
theorem trivialThomPairIso_inv_fst_apply (p : B × F) :
    TopPair.Hom.fst (trivialThomPairIso B F).inv p = TotalSpace.mk' F p.1 p.2 := by
  rw [trivialThomPairIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

omit [NormedSpace ℝ F] in
/-- The identification of the Thom pair of the trivial bundle with that of the product bundle
carries the fibre over `b` to the fibre over `b`. -/
@[reassoc (attr := simp)]
theorem fiberThomPairMap_comp_trivialThomPairIso_hom (b : B) :
    fiberThomPairMap F (Bundle.Trivial B F) b ≫ (trivialThomPairIso B F).hom =
      prodThomPairFiberMap F b := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : F) ↦ ?_)
  exact (congrArg _ (fiberThomPairMap_fst_apply F _ b x)).trans
    ((trivialThomPairIso_hom_fst_apply B F _).trans (prodThomPairFiberMap_fst_apply F b x).symm)

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

/-- On the fibre over `b`, the isomorphism of Thom pairs given by a trivialization over the whole
base is the isomorphism of fibre pairs given by the trivialization at `b`. -/
theorem fiberThomPairMap_comp_thomPairIso_hom (he : e.baseSet = Set.univ) (b : B) :
    fiberThomPairMap F E b ≫ (e.thomPairIso 𝕜 he).hom =
      (e.continuousLinearEquivAt 𝕜 b (he ▸ Set.mem_univ b)).complZeroPairIso.hom ≫
        fiberThomPairMap F (Bundle.Trivial B F) b := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E b) ↦ ?_)
  -- Both sides send `x : E_b` to `(b, e x)`. The carriers of the pairs agree with `E_b`, `F` and
  -- the total spaces only up to unfolding, so first split each composite into its evaluations.
  change TopPair.Hom.fst (e.thomPairIso 𝕜 he).hom (TopPair.Hom.fst (fiberThomPairMap F E b) x) =
    TopPair.Hom.fst (fiberThomPairMap F (Bundle.Trivial B F) b)
      (TopPair.Hom.fst
        (e.continuousLinearEquivAt 𝕜 b (he ▸ Set.mem_univ b)).complZeroPairIso.hom x)
  simp only [fiberThomPairMap_fst_apply, thomPairIso_hom_fst_apply,
    homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜,
    ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply]
  -- `TotalSpace.mk'` is `TotalSpace.mk` with the fibre made explicit.
  rfl

end Geometry

section ThomPairOver

variable (R : Type*) [Semiring R] {B : Type w} [TopologicalSpace B] {F : Type w}
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  (e : Trivialization F (π F E)) [e.IsLinear R] {W : Set B} (hW : W ⊆ e.baseSet)

/-- The map of pairs `(E|_W, E₀|_W) ⟶ (W × F, W × (F ∖ {0}))` given by a linear trivialization
whose base set contains `W`. -/
private def thomPairOverHom : thomPairOver F E W ⟶ prodThomPair W F :=
  TopPair.ofHom (TopCat.isoOfHomeo (e.preimageHomeomorph hW)).hom
    (TopCat.ofHom ⟨fun v ↦ ⟨e.preimageHomeomorph hW ⟨v.1, v.2.1⟩, by
      simpa [preimageHomeomorph_apply] using
        (e.snd_apply_ne_zero_iff R (hW v.2.1)).2 (mem_zeroSectionCompl.1 v.2.2)⟩,
      by fun_prop⟩) (by ext; rfl)

/-- Over a subset `W` of the base set of a linear trivialization `e`, the trivialization identifies
the Thom pair `(E|_W, E₀|_W)` of the restriction with the Thom pair `(W × F, W × (F ∖ {0}))` of the
product bundle. -/
def thomPairOverIso : thomPairOver F E W ≅ prodThomPair W F :=
  have : IsIso (TopPair.Hom.fst (e.thomPairOverHom R hW)) := (TopCat.isoOfHomeo _).isIso_hom
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd (e.thomPairOverHom R hW) fun p ↦ by
    let v := (e.preimageHomeomorph hW).symm p.1
    have hv : e.preimageHomeomorph hW v = p.1 := Homeomorph.apply_symm_apply _ _
    refine ⟨⟨v.1, v.2, mem_zeroSectionCompl.2 ((e.snd_apply_ne_zero_iff R (hW v.2)).1 ?_)⟩,
      Subtype.ext hv⟩
    simpa [preimageHomeomorph_apply, ← hv] using p.2
  asIso (e.thomPairOverHom R hW)

@[simp]
theorem thomPairOverIso_hom_fst_apply (v : π F E ⁻¹' W) :
    TopPair.Hom.fst (e.thomPairOverIso R hW).hom v = (⟨v.1.proj, v.2⟩, (e v).2) :=
  e.preimageHomeomorph_apply hW v

@[simp]
theorem thomPairOverIso_hom_snd_apply (v : (thomPairOver F E W).snd) :
    (TopPair.Hom.snd (e.thomPairOverIso R hW).hom v).1 = (⟨v.1.proj, v.2.1⟩, (e v.1).2) :=
  e.preimageHomeomorph_apply hW ⟨v.1, v.2.1⟩

@[simp]
theorem thomPairOverIso_inv_fst_apply (p : W × F) :
    TopPair.Hom.fst (e.thomPairOverIso R hW).inv p = (e.preimageHomeomorph hW).symm p :=
  (e.preimageHomeomorph hW).eq_symm_apply.2
    ((TopPair.proj₁.mapIso (e.thomPairOverIso R hW)).inv_hom_id_apply p)

@[simp]
theorem thomPairOverIso_inv_snd_apply (p : (prodThomPair W F).snd) :
    (TopPair.Hom.snd (e.thomPairOverIso R hW).inv p).1 = (e.preimageHomeomorph hW).symm p.1 :=
  (congrArg Subtype.val ((TopPair.Hom.w_apply (e.thomPairOverIso R hW).inv p).trans
    (e.thomPairOverIso_inv_fst_apply R hW p.1)) :)

end ThomPairOver

section ThomPairOverFiber

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {W : Set B} (hW : W ⊆ e.baseSet)

/-- On the fibre over a point `b ∈ W`, the identification of `(E|_W, E₀|_W)` with the Thom pair of
the product bundle `W × F` is the isomorphism of fibre pairs `(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})`
given by the trivialization at `b`. -/
@[reassoc]
theorem fiberThomPairOverMap_comp_thomPairOverIso_hom {b : B} (hb : b ∈ W) :
    fiberThomPairOverMap F E hb ≫ (e.thomPairOverIso 𝕜 hW).hom =
      (e.continuousLinearEquivAt 𝕜 b (hW hb)).complZeroPairIso.hom ≫
        prodThomPairFiberMap F (⟨b, hb⟩ : W) := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E b) ↦ ?_)
  -- Both sides send `x : E_b` to `(b, e x)`. The carriers of the pairs agree with `E_b`, `F` and
  -- the subspaces of the total space only up to unfolding, so first split each composite into
  -- its evaluations.
  change TopPair.Hom.fst (e.thomPairOverIso 𝕜 hW).hom
      (TopPair.Hom.fst (fiberThomPairOverMap F E hb) x) =
    TopPair.Hom.fst (prodThomPairFiberMap F (⟨b, hb⟩ : W))
      (TopPair.Hom.fst (e.continuousLinearEquivAt 𝕜 b (hW hb)).complZeroPairIso.hom x)
  rw [fiberThomPairOverMap_fst_apply, thomPairOverIso_hom_fst_apply,
    ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply,
    prodThomPairFiberMap_fst_apply, continuousLinearEquivAt_apply]

include hW in
/-- **Local classes over a trivializing set.** For `W` contained in the base set of a linear
trivialization, every class `g ∈ Hⁿ(F, F ∖ {0})` pulls back, along the trivialization followed by
the projection to the fibre, to a class of `Hⁿ(E|_W, E₀|_W)` whose restriction to the fibre pair
over each `b ∈ W` is the image of `g` under the isomorphism of fibre pairs
`(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})` given by the trivialization. For `g` a generator in degree
`dim F` these are local Thom classes. -/
theorem exists_singularCohomology_thomPairOver_fiber {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}
    {n : ℕ} (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R k M n) :
    ∃ u : (thomPairOver F E W).singularCohomology R k M n, ∀ b (hb : b ∈ W),
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) n u =
        TopPair.singularCohomologyMap
          (e.continuousLinearEquivAt 𝕜 b (hW hb)).complZeroPairIso.hom n g := by
  -- The projection `(W × F, W × (F ∖ {0})) ⟶ (F, F ∖ {0})` onto the fibre pair.
  let proj : prodThomPair W F ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
    TopPair.ofSubsetMap (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) fun _ hp ↦ hp
  have hproj (w : W) : prodThomPairFiberMap F w ≫ proj = 𝟙 _ :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ by
      -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
      erw [CategoryTheory.comp_apply, prodThomPairFiberMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      rfl)
  refine ⟨TopPair.singularCohomologyMap ((e.thomPairOverIso 𝕜 hW).hom ≫ proj) n g, fun b hb ↦ ?_⟩
  rw [← TopPair.singularCohomologyMap_comp_apply,
    e.fiberThomPairOverMap_comp_thomPairOverIso_hom_assoc 𝕜 hW hb, hproj, Category.comp_id]

end ThomPairOverFiber

section ThomPairOverExt

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet)
  {K : Type*} [CommRing K] [Linear K (ModuleCat.{w} K)] {R' M' : ModuleCat.{w} K}
  [Module.Projective K R']

include hW in
/-- **Classes over a trivializing set in the top degree are determined on the fibres**: for `W`
contained in the base set of a linear trivialization, two classes of
`Hʳ(E|_W, E₀|_W; R, M)`, `r = dim F` and `R` projective, whose restrictions to the fibre pair
`(E_b, E_b ∖ {0})` over every point `b ∈ W` agree, are equal. -/
theorem singularCohomology_thomPairOver_ext
    {u v : (thomPairOver F E W).singularCohomology R' K M' (finrank ℝ F)}
    (h : ∀ b (hb : b ∈ W), TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ u =
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ v) : u = v := by
  let φ := e.thomPairOverIso ℝ hW
  have hφ (b : W) : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  -- Transport `u` and `v` to the product bundle and compare them there, fibre by fibre.
  have hφu (w : (thomPairOver F E W).singularCohomology R' K M' (finrank ℝ F)) :
      TopPair.singularCohomologyMap φ.hom _ (TopPair.singularCohomologyMap φ.inv _ w) = w := by
    simp [← TopPair.singularCohomologyMap_comp_apply]
  refine (hφu u).symm.trans ((congrArg _ (singularCohomology_prodThomPair_ext fun b ↦ ?_)).trans
    (hφu v))
  simp only [← TopPair.singularCohomologyMap_comp_apply, hφ]
  simp only [TopPair.singularCohomologyMap_comp_apply, h b b.2]

end ThomPairOverExt

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
    (fun b ↦ (e.continuousLinearEquivAt ℝ b (he ▸ Set.mem_univ b)).complZeroPairIso.symm)
    fun b ↦ by
      dsimp only [id_eq]
      rw [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc,
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

section ProdThomPair

variable {K : Type*} [CommRing K] [Linear K (ModuleCat.{w} K)] (R' M' : ModuleCat.{w} K)
  [Module.Projective K R']

/-- **The relative cohomology of the Thom pair of a trivializable bundle vanishes below the
rank**: for a trivialization of `E` over the whole base, `Hⁿ(E, E₀; R, M) = 0` for
`n < dim F`. -/
theorem isZero_singularCohomology_thomPair (he : e.baseSet = Set.univ) {n : ℕ}
    (hn : n < finrank ℝ F) : IsZero ((thomPair F E).singularCohomology R' K M' n) :=
  (isZero_singularCohomology_prodThomPair R' M' B F hn).of_iso
    ((TopPair.singularCohomologyFunctor R' K M' n).mapIso
      (e.thomPairIso ℝ he ≪≫ trivialThomPairIso B F).op).symm

variable {R' M'} in
/-- **Classes of a trivializable bundle in the top degree are determined on the fibres**: for a
trivialization of `E` over the whole base, two classes of `Hʳ(E, E₀; R, M)`, `r = dim F`, whose
restrictions to the fibre pair `(E_b, E_b ∖ {0})` over every point `b` agree, are equal. In
particular a Thom class of `E` is determined by its restrictions to the fibres. -/
theorem singularCohomology_thomPair_ext (he : e.baseSet = Set.univ)
    {u v : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)}
    (h : ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ v) : u = v := by
  let φ := e.thomPairIso ℝ he ≪≫ trivialThomPairIso B F
  have hφ (b : B) : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b (he ▸ Set.mem_univ b)).complZeroPairIso.inv ≫
        fiberThomPairMap F E b := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Iso.trans_hom, ← Category.assoc,
      e.fiberThomPairMap_comp_thomPairIso_hom ℝ he, Category.assoc,
      fiberThomPairMap_comp_trivialThomPairIso_hom]
  -- Transport `u` and `v` to the product bundle and compare them there, fibre by fibre.
  have hφu (w : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)) :
      TopPair.singularCohomologyMap φ.hom _ (TopPair.singularCohomologyMap φ.inv _ w) = w := by
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, Iso.hom_inv_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  refine (hφu u).symm.trans ((congrArg _ (singularCohomology_prodThomPair_ext fun b ↦ ?_)).trans
    (hφu v))
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularCohomologyMap_comp, hφ, TopPair.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h b]

end ProdThomPair

section CoordChange

variable (e' : Trivialization F (π F E)) [e'.IsLinear ℝ] {K : Type*} [CommRing K]
  {R' : ModuleCat.{w} K} {M' : ModuleCat.{w} K} [Module.Projective K R']

/-- **Fibre classes read in two trivializations differ by the sign of the coordinate change**: for
linear trivializations `e` and `e'` whose base sets contain `b`, pulling back a class
`g ∈ Hⁿ(F, F ∖ {0}; R, M)` to the fibre pair `(E_b, E_b ∖ {0})` along `e'` gives the pull-back
along `e` multiplied by the sign of the determinant of the coordinate change from `e` to `e'` at
`b`. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul {b : B} (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) {n : ℕ}
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g =
      (SignType.sign (e.coordChangeL ℝ e' b : F →L[ℝ] F).det : ℤ) •
        TopPair.singularCohomologyMap
          (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g := by
  have hf : Set.MapsTo (e.coordChangeL ℝ e' b : F →L[ℝ] F) ({0}ᶜ : Set F) {0}ᶜ :=
    (e.coordChangeL ℝ e' b).mapsTo_compl_zero
  -- The fibre of `e'` at `b` is the fibre of `e` followed by the coordinate change.
  have hcomp : (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom =
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom ≫
        TopPair.ofSubsetMap (TopCat.ofHom ((e.coordChangeL ℝ e' b : F →L[ℝ] F) : C(F, F))) hf := by
    have h := (e.continuousLinearEquivAt_trans_coordChangeL ℝ e' hb hb').symm
    rw [h, ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom]
    exact congrArg _ (ContinuousLinearEquiv.complZeroPairIso_hom _)
  rw [hcomp, TopPair.singularCohomologyMap_comp,
    singularCohomologyMap_continuousLinearMap_compl_zero, Preadditive.zsmul_comp, Category.id_comp]
  exact congr($(ModuleCat.hom_zsmul _ _) g)

end CoordChange

end Bundle.Trivialization
