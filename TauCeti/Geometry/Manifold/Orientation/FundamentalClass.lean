/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.ModelTransport.Interior
import TauCeti.Geometry.Manifold.ModelWithCorners.LinearEquiv
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# The integral fundamental class of a compact oriented smooth manifold

Let `(M, I)` be a compact boundaryless `C¹` manifold (`[BoundarylessManifold I M]`) of dimension
`n + 1`, with orientation `o : TauCeti.Manifold.Orientation I M (Fin (n + 1))`. While
`TauCeti.Manifold.Orientation.toHomologicalOrientation` requires a self-modelled real inner product
space `𝓘(ℝ, E)`, any boundaryless `C¹` manifold can be transported to its interior vector-space
model `TauCeti.BoundarylessModel.interiorDiffeomorph` and then recharted to a self-modelled
Euclidean copy via `ModelWithCorners.transContinuousLinearEquiv` and
`TauCeti.BoundarylessModel.diffeomorph`.

Because orientation-preserving open embeddings pull back `toHomologicalOrientation`
(`TauCeti.Manifold.Orientation.comap_toHomologicalOrientation`), the resulting class
`TauCeti.Manifold.Orientation.fundamentalClass o ∈ Hₙ₊₁(M; ℤ)` is independent of the chosen linear
equivalence with `EuclideanSpace ℝ (Fin (n + 1))`. It agrees with
`(o.toHomologicalOrientation hE).fundamentalClass hE` on every `(n + 1)`-dimensional real inner
product model `𝓘(ℝ, E)`
(`TauCeti.Manifold.Orientation.fundamentalClass_eq_toHomologicalOrientation`, specialized to
`𝓡 (n + 1)` in `TauCeti.Manifold.Orientation.fundamentalClass_euclideanSpace`), and is natural
under pointwise orientation-preserving homeomorphisms between arbitrary boundaryless `C¹` models
(`TauCeti.Manifold.Orientation.mapFundamentalClass_homeomorph`).

## Main definitions

* `TauCeti.Manifold.Orientation.fundamentalClass`: the integral fundamental class `[M] ∈ Hₙ₊₁(M; ℤ)`
  of a compact oriented boundaryless `C¹` manifold `(M, I)`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass`: the pushforward `f_*[M] ∈ Hₙ₊₁(X; ℤ)` along
  a continuous map `f : C(M, X)`.

## Main results

* `TauCeti.Manifold.Orientation.comap_toHomologicalOrientation`: an orientation-preserving open
  embedding between manifolds on a common real inner product model pulls back
  `toHomologicalOrientation`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_toHomologicalOrientation_homeomorph`: an
  orientation-preserving homeomorphism on a common real inner product model carries the homological
  fundamental class of the source to that of the target.
* `TauCeti.Manifold.Orientation.fundamentalClass_neg`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_id`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_comp`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_neg`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_of_homotopic`: basic functoriality, sign,
  and homotopy invariance of `fundamentalClass` and `mapFundamentalClass`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_homeomorph`: an orientation-preserving
  homeomorphism between compact boundaryless `C¹` manifolds carries the fundamental class of the
  source to that of the target.
* `TauCeti.Manifold.Orientation.fundamentalClass_eq_toHomologicalOrientation`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_toHomologicalOrientation`: agreement with
  `toHomologicalOrientation` on any `(n + 1)`-dimensional real inner product model `𝓘(ℝ, E)`.
* `TauCeti.Manifold.Orientation.fundamentalClass_euclideanSpace`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_euclideanSpace`: `@[simp]` specializations to
  `𝓡 (n + 1)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations and fundamental classes).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 15 and 17.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module Set Topology
open scoped ContDiff EuclideanSpace Manifold

universe w

namespace TauCeti

namespace Manifold.Orientation

section OpenEmbedding

variable {M N E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]
  {n : ℕ} (hE : finrank ℝ E = n + 1)
  (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, E) N (Fin (n + 1)))

/-- An orientation-preserving open embedding between boundaryless `C¹` manifolds modelled on `E`
pulls back the homological orientation of the target to that of the source. -/
theorem comap_toHomologicalOrientation {j : M → N} (hj : IsOpenEmbedding j)
    (hj' : ∀ x, IsOrientationPreservingAt o o' j x) :
    (o'.toHomologicalOrientation hE).comap hj = o.toHomologicalOrientation hE := by
  ext x : 1
  apply (hj.localOrientationEquiv x (n + 1)).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply]
  apply Subtype.ext
  rw [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
    toHomologicalOrientation_apply, toHomologicalOrientation_apply,
    localOrientationOfManifoldOrientation_eq, localOrientationOfManifoldOrientation_eq]
  set oM : _root_.Orientation ℝ E (Fin (n + 1)) := o.orientationAt x
  set oN : _root_.Orientation ℝ E (Fin (n + 1)) := o'.orientationAt (j x)
  obtain ⟨e, he, heo⟩ := (isOrientationPreservingAt_iff o o' j x).1 (hj' x)
  let e' : E ≃L[ℝ] E := e
  set f' : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j x
  have he' : (e' : E →L[ℝ] E) = f' := he
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ E := by simp [hE]
  have hfd : HasFDerivAt (chartAt E (j x) ∘ j ∘ (chartAt E x).symm) f' (chartAt E x x) := by
    have h :=
      (mdifferentiableAt_of_isInvertible_mfderiv (hj' x).isInvertible_mfderiv).hasMFDerivAt.2
    simp only [writtenInExtChartAt, hasFDerivWithinAt_univ, ModelWithCorners.range_eq_univ] at h
    exact h
  have hdet : f'.det ≠ 0 := by
    rw [← he']
    exact (LinearEquiv.isUnit_det' e'.toLinearEquiv).ne_zero
  let jC : C(M, N) := ⟨j, hj.continuous⟩
  have hU := (chartAt E x).localHomologyMap_restrict_localOrientationOfOrientedChart
    oM hE (chartAt E (j x)) jC (mem_chart_source E x) (mem_chart_source E (j x))
    isOpen_univ (mem_univ x) (fun _ _ hz ↦ hj.injective hz) hfd hdet
  have huniv := isOpen_univ.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm
    ⟨x, mem_univ x⟩ ((chartAt E x).localOrientationOfOrientedChart (mem_chart_source E x) oM hE)
    fun _ hz ↦ Subtype.ext hz
  have hmap : localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) jC
        (by rw [ContinuousMap.coe_mk, ← image_singleton, hj.injective.preimage_image]) (n + 1)
        ((chartAt E x).localOrientationOfOrientedChart (mem_chart_source E x) oM hE).val =
      (SignType.sign f'.det : ℤ) • ((chartAt E (j x)).localOrientationOfOrientedChart
        (mem_chart_source E (j x)) oM hE).val := by
    rw [← huniv, ← ConcreteCategory.comp_apply]
    exact (ConcreteCategory.congr_hom (localHomologyMap_comp _ _ jC _ _ (n + 1)) _).trans hU
  rw [hmap]
  rcases _root_.Orientation.eq_or_eq_neg oN oM (by simp [hE]) with ho | ho
  · have hpos : 0 < f'.det := by
      rw [← he']
      exact (_root_.Orientation.map_eq_iff_det_pos _ _ hcard).1 (heo.trans ho)
    rw [sign_pos hpos, SignType.coe_one, one_zsmul, ho]
  · have hneg : f'.det < 0 := by
      rw [← he']
      exact (_root_.Orientation.map_eq_neg_iff_det_neg _ _ hcard).1 (heo.trans ho)
    rw [sign_neg hneg, SignType.coe_neg_one, neg_one_zsmul, ho,
      OpenPartialHomeomorph.localOrientationOfOrientedChart_neg, LocalOrientation.coe_neg]

end OpenEmbedding

section SameModel

variable {M N E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N] [CompactSpace N]
  {n : ℕ} (hE : finrank ℝ E = n + 1)
  (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, E) N (Fin (n + 1)))

/-- An orientation-preserving homeomorphism between compact boundaryless `C¹` manifolds modelled on
`E` carries the fundamental class of the source to that of the target. -/
theorem mapFundamentalClass_toHomologicalOrientation_homeomorph
    (e : M ≃ₜ N) (he : ∀ x, IsOrientationPreservingAt o o' e x) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE (e : C(M, N)) =
      (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [← comap_toHomologicalOrientation hE o o' e.isOpenEmbedding he,
    HomologicalOrientation.mapFundamentalClass_comap]

end SameModel

section LinearIsometryComparison

variable {E F : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem mem_refl_source {X : Type*} [TopologicalSpace X] (p : X) :
    p ∈ (OpenPartialHomeomorph.refl X).source := by
  rw [OpenPartialHomeomorph.refl_source]
  exact mem_univ p

private theorem homeomorph_preimage_singleton_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    (e : C(X, Y)) ⁻¹' {e x} ⊆ {x} :=
  fun _ hz ↦ e.injective (by simpa using hz)

/-- On punctured spaces, a linear isometry intertwines the radial projections onto the unit
spheres. -/
private theorem snd_ofSubsetMap_linearIsometryEquiv_comp_complSingletonHomotopyEquivSphere
    (f : E ≃ₗᵢ[ℝ] F) (p : E) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of F)
        (TopCat.ofHom (f.toHomeomorph : C(E, F))) (B := {p}ᶜ) (B' := {f p}ᶜ)
        (fun _ hy h ↦ hy (f.injective h))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere (f p)).toFun =
    TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
      TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
        f.toLinearIsometry.continuous_unitSphereMap⟩ := by
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine ((coe_complSingletonHomotopyEquivSphere_apply (f p) _).trans ?_).trans
    ((LinearIsometry.coe_unitSphereMap_apply f.toLinearIsometry _).trans
      (congrArg (f : E → F) (coe_complSingletonHomotopyEquivSphere_apply p z))).symm
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_ofClass, LinearIsometryEquiv.coe_toHomeomorph,
    ← map_sub, f.norm_map, map_smul]

/-- A linear isometry `f : E ≃ₗᵢ[ℝ] F` intertwines the connecting morphism and radial projection
in the oriented local homology isomorphism of the identity charts. -/
@[reassoc]
private theorem localHomologyMap_linearIsometryEquiv_comp_singularHomologyComplSingletonIso_refl
    {n : ℕ} (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 1)
    (f : E ≃ₗᵢ[ℝ] F) (p : E) {q : F} (hq : q = f p)
    (oE : _root_.Orientation ℝ E (Fin (n + 1)))
    (h : (f.toHomeomorph : C(E, F)) ⁻¹' {q} ⊆ {p}) :
    let R := ModuleCat.of ℤ (ULift.{w} ℤ)
    localHomologyMap R (f.toHomeomorph : C(E, F)) h (n + 1) ≫
        (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl F)
          (mem_refl_source q)
          (_root_.Orientation.map (Fin (n + 1)) f.toLinearEquiv oE) hF).hom =
      (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E)
        (mem_refl_source p) oE hE).hom := by
  subst hq
  intro R
  rw [singularHomologyComplSingletonIsoOfOrientation_refl_hom,
    singularHomologyComplSingletonIsoOfOrientation_refl_hom,
    localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
  congr 1
  -- The composite is only type-correct after unfolding the subspace of the pair.
  erw [← Functor.map_comp_assoc,
    snd_ofSubsetMap_linearIsometryEquiv_comp_complSingletonHomotopyEquivSphere f p,
    Functor.map_comp_assoc]
  congr 1
  exact reducedSingularHomologySphereIsoOfOrientation_hom_naturality R oE _ f rfl hE

/-- Intertwining of chart local homology isomorphisms under a homeomorphism `e : M ≃ₜ M'` whose
charts satisfy `ψ (e z) = f (φ z)`. -/
private theorem localHomologyMap_comp_singularHomologyComplSingletonIsoOfChart_hom
    {M M' : Type w} [TopologicalSpace M] [T1Space M] [TopologicalSpace M'] [T1Space M']
    (f : E ≃ₗᵢ[ℝ] F) (e : M ≃ₜ M')
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph M' F)
    {x : M} (hx : x ∈ φ.source) (hx' : e x ∈ ψ.source)
    (hsrc : ψ.source = e.symm ⁻¹' φ.source) (hφψ : ∀ z, ψ (e z) = f (φ z)) (k : ℕ) :
    let R := ModuleCat.of ℤ (ULift.{w} ℤ)
    localHomologyMap R (e : C(M, M')) (homeomorph_preimage_singleton_subset e x) k ≫
        (singularHomologyComplSingletonIsoOfChart R ψ hx' k).hom =
      (singularHomologyComplSingletonIsoOfChart R φ hx k).hom ≫
        localHomologyMap R (f.toHomeomorph : C(E, F))
          (by rw [hφψ x]; exact homeomorph_preimage_singleton_subset f.toHomeomorph (φ x)) k := by
  intro R
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R (X := TopCat.of M)
    φ.open_source isClosed_singleton (singleton_subset_iff.2 hx) k
  rw [← cancel_epi (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := TopCat.of M) φ.source {x}ᶜ) R k)]
  rw [singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom_assoc]
  have heφ : ∀ z : φ.source, e z.1 ∈ ψ.source := fun z ↦ by
    rw [hsrc, mem_preimage, e.symm_apply_apply]
    exact z.2
  have hex : TopPair.excisionMap (X := TopCat.of M) φ.source {x}ᶜ ≫
        TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of M') (TopCat.ofHom (e : C(M, M')))
          (B := {x}ᶜ) (B' := {e x}ᶜ) (fun _ hz h ↦ hz (e.injective h)) =
      TopPair.ofSubsetMap (X := TopCat.of φ.source) (Y := TopCat.of ψ.source)
          (TopCat.ofHom ⟨fun z ↦ ⟨e z.1, heφ z⟩,
            (e.continuous.comp continuous_subtype_val).subtype_mk heφ⟩)
          (B := Subtype.val ⁻¹' {x}ᶜ) (B' := Subtype.val ⁻¹' {e x}ᶜ)
          (fun _ hz h ↦ hz (e.injective h)) ≫
        TopPair.excisionMap (X := TopCat.of M') ψ.source {e x}ᶜ := by
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk]
    rfl
  rw [localHomologyMap_def, localHomologyMap_def, ← TopPair.singularHomologyMap_comp_assoc,
    hex, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp]
  congr 1
  apply TopPair.hom_ext_of_fst
  ext z
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  erw [TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply,
    TopPair.ofSubsetIso_hom, TopPair.ofSubsetIso_hom,
    TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
  exact hφψ z.1

/-- For a homeomorphism `e : M ≃ₜ M'` and charts `φ`, `ψ` intertwined by a linear isometry `f`
(`ψ (e z) = f (φ z)`), `e` carries the oriented-chart local orientation of `φ` to that of `ψ`. -/
private theorem localHomologyMap_homeomorph_localOrientationOfOrientedChart_linearIsometryEquiv
    {M M' : Type w} [TopologicalSpace M] [T1Space M] [TopologicalSpace M'] [T1Space M']
    {n : ℕ} (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 1)
    (f : E ≃ₗᵢ[ℝ] F) (e : M ≃ₜ M')
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph M' F)
    {x : M} (hx : x ∈ φ.source) (hx' : e x ∈ ψ.source)
    (hsrc : ψ.source = e.symm ⁻¹' φ.source) (hφψ : ∀ z, ψ (e z) = f (φ z))
    (oE : _root_.Orientation ℝ E (Fin (n + 1))) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (e : C(M, M'))
        (homeomorph_preimage_singleton_subset e x) (n + 1)
        (φ.localOrientationOfOrientedChart hx oE hE).val =
      (ψ.localOrientationOfOrientedChart hx'
        (_root_.Orientation.map (Fin (n + 1)) f.toLinearEquiv oE) hF).val := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let isoM := singularHomologyComplSingletonIsoOfOrientation R φ hx oE hE
  let isoM' := singularHomologyComplSingletonIsoOfOrientation R ψ hx'
    (_root_.Orientation.map (Fin (n + 1)) f.toLinearEquiv oE) hF
  have hiso :
      localHomologyMap R (e : C(M, M')) (homeomorph_preimage_singleton_subset e x) (n + 1) ≫
          isoM'.hom = isoM.hom := by
    change localHomologyMap R (e : C(M, M')) _ (n + 1) ≫
        (singularHomologyComplSingletonIsoOfOrientation R ψ hx' _ hF).hom =
      (singularHomologyComplSingletonIsoOfOrientation R φ hx oE hE).hom
    rw [singularHomologyComplSingletonIsoOfOrientation_hom_eq R ψ hx' (mem_refl_source _),
      singularHomologyComplSingletonIsoOfOrientation_hom_eq R φ hx (mem_refl_source _),
      ← Category.assoc,
      localHomologyMap_comp_singularHomologyComplSingletonIsoOfChart_hom f e φ ψ hx hx' hsrc hφψ,
      Category.assoc]
    congr 1
    exact localHomologyMap_linearIsometryEquiv_comp_singularHomologyComplSingletonIso_refl
      hE hF f (φ x) (hφψ x) oE _
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso isoM'.hom).1
  rw [← ConcreteCategory.comp_apply, hiso]
  exact (isoM.inv_hom_id_apply 1).trans (isoM'.inv_hom_id_apply 1).symm

end LinearIsometryComparison

section SelfModel

variable {E : Type*} {M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {n : ℕ}

/-- A chosen continuous linear equivalence `E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))` from the
dimension equality carried by an orientation. -/
private def modelEquivEuclidean {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (o : Manifold.Orientation I X (Fin (n + 1))) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq
    (by rw [← o.card_eq, Fintype.card_fin, finrank_euclideanSpace_fin])

/-- Recharting a self-modelled manifold `(M, 𝓘(ℝ, E))` to a self-modelled Euclidean copy along
`e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))`. -/
private def euclideanDiffeomorph (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    M ≃ₘ^1⟮𝓘(ℝ, E), 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))⟯
      BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M :=
  (e.toTransContinuousLinearEquiv (n := 1) 𝓘(ℝ, E) M).trans
    (BoundarylessModel.diffeomorph (𝓘(ℝ, E).transContinuousLinearEquiv e) 1)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 1 M] in
private theorem coe_euclideanDiffeomorph (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ⇑(euclideanDiffeomorph M e) =
      BoundarylessModel.homeomorph (𝓘(ℝ, E).transContinuousLinearEquiv e) M := by
  rw [euclideanDiffeomorph, Diffeomorph.coe_trans, BoundarylessModel.coe_diffeomorph,
    ContinuousLinearEquiv.coe_toTransContinuousLinearEquiv, Function.comp_id]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 1 M] in
private theorem coe_euclideanDiffeomorph_symm (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ⇑(euclideanDiffeomorph M e).symm =
      (BoundarylessModel.homeomorph (𝓘(ℝ, E).transContinuousLinearEquiv e) M).symm := by
  rw [euclideanDiffeomorph, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    ContinuousLinearEquiv.coe_toTransContinuousLinearEquiv_symm,
    BoundarylessModel.coe_diffeomorph_symm, Function.id_comp]

/-- The orientation on the self-modelled Euclidean copy pulled back from `o` along the inverse
recharting diffeomorphism. -/
private def euclideanOrientation (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M) (Fin (n + 1)) :=
  o.pullback (euclideanDiffeomorph M e).symm.contMDiff
    (fun _ ↦ (euclideanDiffeomorph M e).symm.isInvertible_mfderiv one_ne_zero)
    (by simp)

private theorem isOrientationPreservingAt_euclideanDiffeomorph_symm
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (y : BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M) :
    IsOrientationPreservingAt (o.euclideanOrientation e) o
      (euclideanDiffeomorph M e).symm y :=
  isOrientationPreservingAt_pullback _ _ _ _ y

private theorem isOrientationPreservingAt_euclideanDiffeomorph
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (x : M) :
    IsOrientationPreservingAt o (o.euclideanOrientation e) (euclideanDiffeomorph M e) x := by
  refine (isOrientationPreservingAt_euclideanDiffeomorph_symm o e
    (euclideanDiffeomorph M e x)).of_comp ?_
      ((euclideanDiffeomorph M e).mdifferentiable one_ne_zero x)
  have hid : ⇑(euclideanDiffeomorph M e).symm ∘ ⇑(euclideanDiffeomorph M e) = id :=
    funext (euclideanDiffeomorph M e).symm_apply_apply
  rw [hid]
  exact isOrientationPreservingAt_id o x

variable [T2Space M] [CompactSpace M]

/-- The integral fundamental class of a compact oriented self-modelled `C¹` manifold
`(M, 𝓘(ℝ, E))`. -/
private def fundamentalClassSelf (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  ((o.euclideanOrientation o.modelEquivEuclidean).toHomologicalOrientation
    finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
    ((euclideanDiffeomorph M o.modelEquivEuclidean).symm.toHomeomorph :
      C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv o.modelEquivEuclidean) M, M))

/-- Any continuous linear equivalence `e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))` computes
`o.fundamentalClassSelf`. -/
private theorem fundamentalClassSelf_eq (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    o.fundamentalClassSelf =
      ((o.euclideanOrientation e).toHomologicalOrientation
        finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
        ((euclideanDiffeomorph M e).symm.toHomeomorph :
          C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M, M)) := by
  rw [fundamentalClassSelf]
  set e₀ := o.modelEquivEuclidean
  let Ψ :=
    (euclideanDiffeomorph M e₀).symm.toHomeomorph.trans (euclideanDiffeomorph M e).toHomeomorph
  have hΨ : ∀ z, IsOrientationPreservingAt (o.euclideanOrientation e₀)
      (o.euclideanOrientation e) Ψ z := by
    intro z
    have hcoe : (Ψ : _ → _) = ⇑(euclideanDiffeomorph M e) ∘ ⇑(euclideanDiffeomorph M e₀).symm := by
      ext y
      simp only [Ψ, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph, Function.comp_apply]
    rw [hcoe]
    exact (isOrientationPreservingAt_euclideanDiffeomorph o e _).comp
      (isOrientationPreservingAt_euclideanDiffeomorph_symm o e₀ z)
  have hcomp : ((euclideanDiffeomorph M e₀).symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e₀) M, M)) =
      ((euclideanDiffeomorph M e).symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M, M)).comp
        (Ψ : C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e₀) M,
          BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M)) := by
    ext z
    simp [Ψ, Diffeomorph.coe_toHomeomorph]
  rw [← comap_toHomologicalOrientation finrank_euclideanSpace_fin
    (o.euclideanOrientation e₀) (o.euclideanOrientation e) Ψ.isOpenEmbedding hΨ, hcomp,
    HomologicalOrientation.mapFundamentalClass_comap_comp]

private theorem fundamentalClassSelf_neg (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    (-o).fundamentalClassSelf = -o.fundamentalClassSelf := by
  rw [(-o).fundamentalClassSelf_eq o.modelEquivEuclidean, fundamentalClassSelf]
  have hneg : (-o).euclideanOrientation o.modelEquivEuclidean =
      -o.euclideanOrientation o.modelEquivEuclidean :=
    pullback_neg o _ _ _
  rw [hneg, toHomologicalOrientation_neg, HomologicalOrientation.mapFundamentalClass_neg]

private theorem map_fundamentalClassSelf_homeomorph
    {F : Type*} {N : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [T2Space N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) 1 N] [CompactSpace N]
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1)))
    (e : M ≃ₜ N) (he : ∀ x, IsOrientationPreservingAt o o' e x) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (e : C(M, N)))).hom
        o.fundamentalClassSelf = o'.fundamentalClassSelf := by
  set Φ := euclideanDiffeomorph M o.modelEquivEuclidean
  set Φ' := euclideanDiffeomorph N o'.modelEquivEuclidean
  let Θ := (Φ.symm.toHomeomorph.trans e).trans Φ'.toHomeomorph
  have hΘ : ∀ z, IsOrientationPreservingAt (o.euclideanOrientation o.modelEquivEuclidean)
      (o'.euclideanOrientation o'.modelEquivEuclidean) Θ z := by
    intro z
    have hcoe : (Θ : _ → _) = ⇑Φ' ∘ (⇑e ∘ ⇑Φ.symm) := by
      ext y
      simp only [Θ, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph, Function.comp_apply]
    rw [hcoe]
    exact (isOrientationPreservingAt_euclideanDiffeomorph o' _ _).comp
      ((he (Φ.symm z)).comp (isOrientationPreservingAt_euclideanDiffeomorph_symm o _ z))
  have hcomp : (e : C(M, N)).comp
      (Φ.symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv o.modelEquivEuclidean) M, M)) =
      (Φ'.symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, F).transContinuousLinearEquiv o'.modelEquivEuclidean) N, N)).comp
        (Θ : C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv o.modelEquivEuclidean) M,
          BoundarylessModel (𝓘(ℝ, F).transContinuousLinearEquiv o'.modelEquivEuclidean) N)) := by
    ext z
    simp [Θ, Diffeomorph.coe_toHomeomorph]
  rw [fundamentalClassSelf, ← HomologicalOrientation.mapFundamentalClass_comp, hcomp,
    ← comap_toHomologicalOrientation finrank_euclideanSpace_fin _ _ Θ.isOpenEmbedding hΘ,
    HomologicalOrientation.mapFundamentalClass_comap_comp, ← fundamentalClassSelf]

end SelfModel

section SelfModelInnerProduct

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {n : ℕ}

omit [T2Space M] [CompactSpace M] in
/-- For a linear isometry `f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))`, the tangent orientation
of `o.euclideanOrientation f.toContinuousLinearEquiv` at `Φ x` is the pushforward of
`o.orientationAt x` along `f`. -/
private theorem orientationAt_euclideanOrientation_linearIsometryEquiv
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (x : M) :
    _root_.Orientation.map (Fin (n + 1)) f.toLinearEquiv
        (o.orientationAt x : _root_.Orientation ℝ E (Fin (n + 1))) =
      ((o.euclideanOrientation f.toContinuousLinearEquiv).orientationAt
        (euclideanDiffeomorph M f.toContinuousLinearEquiv x) :
        _root_.Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) := by
  set I' := 𝓘(ℝ, E).transContinuousLinearEquiv f.toContinuousLinearEquiv
  have hmf : (f.toContinuousLinearEquiv : E →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (euclideanDiffeomorph M f.toContinuousLinearEquiv) x := by
    have hcoe : (euclideanDiffeomorph M f.toContinuousLinearEquiv : M → BoundarylessModel I' M) =
        BoundarylessModel.homeomorph I' M ∘ id := by
      rw [coe_euclideanDiffeomorph, Function.comp_id]
    rw [hcoe, BoundarylessModel.mfderiv_target I' 𝓘(ℝ, E) id x,
      ModelWithCorners.mfderiv_id_transContinuousLinearEquiv 𝓘(ℝ, E) f.toContinuousLinearEquiv x]
    ext v
    simp only [ContinuousLinearEquiv.coe_coe]
    -- `tangentSpaceCastModel` on `𝓘(ℝ, E)` and `𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))` is `id`.
    rfl
  exact (isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ f.toContinuousLinearEquiv hmf).1
    (isOrientationPreservingAt_euclideanDiffeomorph o f.toContinuousLinearEquiv x)

omit [CompactSpace M] in
/-- Pushing forward the local orientation of `o` at `x` along the linear-isometry recharting
diffeomorphism `euclideanDiffeomorph M f.toContinuousLinearEquiv` yields the local orientation of
`o.euclideanOrientation f.toContinuousLinearEquiv` at `Φ x`. -/
private theorem localHomologyMap_euclideanDiffeomorph_localOrientation
    (hE : finrank ℝ E = n + 1) (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (x : M) :
    let Φ := euclideanDiffeomorph M f.toContinuousLinearEquiv
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (Φ.toHomeomorph : C(M, _))
        (homeomorph_preimage_singleton_subset Φ.toHomeomorph x) (n + 1)
        (localOrientationOfManifoldOrientation o hE x).val =
      (localOrientationOfManifoldOrientation (o.euclideanOrientation f.toContinuousLinearEquiv)
        finrank_euclideanSpace_fin (Φ.toHomeomorph x)).val := by
  intro Φ
  rw [localOrientationOfManifoldOrientation_eq, localOrientationOfManifoldOrientation_eq]
  set ω₀ : _root_.Orientation ℝ E (Fin (n + 1)) := o.orientationAt x
  have hfwd := localHomologyMap_homeomorph_localOrientationOfOrientedChart_linearIsometryEquiv
    hE finrank_euclideanSpace_fin f Φ.toHomeomorph
    (chartAt E x) (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (Φ.toHomeomorph x))
    (mem_chart_source E x) (mem_chart_source _ (Φ.toHomeomorph x))
    (by
      rw [BoundarylessModel.chartAt_eq, BoundarylessModel.chart_source]
      ext z
      simp only [Φ, mem_preimage, Diffeomorph.coe_toHomeomorph, Diffeomorph.coe_toHomeomorph_symm,
        coe_euclideanDiffeomorph, coe_euclideanDiffeomorph_symm, Homeomorph.symm_apply_apply])
    (fun z ↦ by
      rw [BoundarylessModel.chartAt_eq, BoundarylessModel.chart_apply]
      simp only [Φ, Diffeomorph.coe_toHomeomorph, coe_euclideanDiffeomorph,
        Homeomorph.symm_apply_apply, ModelWithCorners.coe_transContinuousLinearEquiv,
        Function.comp_apply, modelWithCornersSelf_coe, id_eq,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv])
    ω₀
  rwa [orientationAt_euclideanOrientation_linearIsometryEquiv o f x] at hfwd

private theorem fundamentalClassSelf_eq_toHomologicalOrientation
    (hE : finrank ℝ E = n + 1) (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    o.fundamentalClassSelf = (o.toHomologicalOrientation hE).fundamentalClass hE := by
  let f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr
  set I' := 𝓘(ℝ, E).transContinuousLinearEquiv f.toContinuousLinearEquiv
  let Φ := euclideanDiffeomorph M f.toContinuousLinearEquiv
  rw [o.fundamentalClassSelf_eq f.toContinuousLinearEquiv]
  refine (o.toHomologicalOrientation hE).eq_fundamentalClass hE fun x ↦ ?_
  have hxpre :
      (Φ.symm.toHomeomorph : C(BoundarylessModel I' M, M)) ⁻¹' {x} ⊆ {Φ.toHomeomorph x} :=
    fun z hz ↦ by
      have hz' : Φ.symm z = x := by
        simpa [Diffeomorph.coe_toHomeomorph] using hz
      rw [mem_singleton_iff, Diffeomorph.coe_toHomeomorph]
      exact (Φ.apply_symm_apply z).symm.trans (congrArg Φ hz')
  refine (singularHomologyToLocalHomology_apply _ x _).trans ?_
  rw [HomologicalOrientation.singularHomologyπ_mapFundamentalClass, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap
      (hS := singleton_subset_iff.2 (mem_univ (Φ.toHomeomorph x))) (h := hxpre),
    ConcreteCategory.comp_apply,
    HomologicalOrientation.localHomologyRestriction_fundamentalClassOn
      (hx := mem_univ (Φ.toHomeomorph x)),
    toHomologicalOrientation_apply, toHomologicalOrientation_apply,
    ← localHomologyMap_euclideanDiffeomorph_localOrientation hE o f x,
    ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  have hid : (Φ.symm.toHomeomorph : C(BoundarylessModel I' M, M)).comp
      (Φ.toHomeomorph : C(M, BoundarylessModel I' M)) = ContinuousMap.id M := by
    ext z
    simp
  have hmap : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
      ((Φ.symm.toHomeomorph : C(BoundarylessModel I' M, M)).comp
        (Φ.toHomeomorph : C(M, BoundarylessModel I' M))) (S := {x}) (T := {x})
      (by rw [hid]; exact subset_rfl) (n + 1) = 𝟙 _ :=
    (localHomologyMap_congr _ hid _ _).trans
      ((localHomologyMap_id _ (S := {x}) (T := {x}) subset_rfl _).trans
        (localHomologyRestriction_refl _ {x} (n + 1)))
  exact (ConcreteCategory.congr_hom hmap _).trans (ModuleCat.id_apply _ _)

end SelfModelInnerProduct

section Boundaryless

section Model

variable {E H : Type*} {M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [T2Space M] [CompactSpace M] {n : ℕ}

/-- **The integral fundamental class of a compact oriented boundaryless `C¹` manifold** `(M, I)`:
the class in `Hₙ₊₁(M; ℤ)` obtained by passing to the interior vector-space atlas
`TauCeti.BoundarylessModel.interiorChartedSpace`, transporting to a self-modelled Euclidean copy,
and pushing forward its homological fundamental class. It agrees with
`(o.toHomologicalOrientation hE).fundamentalClass hE` on every `(n + 1)`-dimensional real inner
product model `𝓘(ℝ, E)` (`fundamentalClass_eq_toHomologicalOrientation`). -/
def fundamentalClass (o : Manifold.Orientation I M (Fin (n + 1))) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  letI : ChartedSpace E (BoundarylessModel I M) := BoundarylessModel.interiorChartedSpace I
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  let o₀ : Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel I M) (Fin (n + 1)) :=
    o.pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero) o.card_eq
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom (Φ.symm.toHomeomorph : C(BoundarylessModel I M, M)))).hom
    o₀.fundamentalClassSelf

/-- Reversing a manifold orientation negates its fundamental class. -/
@[simp]
theorem fundamentalClass_neg (o : Manifold.Orientation I M (Fin (n + 1))) :
    (-o).fundamentalClass = -o.fundamentalClass := by
  let : ChartedSpace E (BoundarylessModel I M) := BoundarylessModel.interiorChartedSpace I
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  have hneg :
      (-o).pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero) o.card_eq =
        -(o.pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero)
          o.card_eq) :=
    pullback_neg o _ _ _
  rw [fundamentalClass, fundamentalClass, hneg, fundamentalClassSelf_neg, map_neg]

/-- The image `f_*[M] ∈ Hₙ₊₁(X; ℤ)` of the fundamental class of a compact oriented boundaryless
`C¹` manifold `(M, I)` under a continuous map `f : C(M, X)`. -/
def mapFundamentalClass (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of X) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom o.fundamentalClass

/-- Equation lemma unfolding `Manifold.Orientation.mapFundamentalClass`. -/
theorem mapFundamentalClass_def (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    o.mapFundamentalClass f =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom o.fundamentalClass :=
  (rfl)

/-- The image of the fundamental class under the identity is the fundamental class. -/
@[simp]
theorem mapFundamentalClass_id (o : Manifold.Orientation I M (Fin (n + 1))) :
    o.mapFundamentalClass (ContinuousMap.id M) = o.fundamentalClass := by
  rw [mapFundamentalClass_def, TopCat.ofHom_id, CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- Functoriality of `mapFundamentalClass` under composition of continuous maps. -/
theorem mapFundamentalClass_comp (o : Manifold.Orientation I M (Fin (n + 1)))
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(X, Y)) (f : C(M, X)) :
    o.mapFundamentalClass (g.comp f) =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom g)).hom (o.mapFundamentalClass f) := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]

/-- Reversing the orientation negates `mapFundamentalClass`. -/
@[simp]
theorem mapFundamentalClass_neg (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    (-o).mapFundamentalClass f = -o.mapFundamentalClass f := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, fundamentalClass_neg, map_neg]

/-- Homotopic continuous maps carry `o.fundamentalClass` to the same homology class. -/
theorem mapFundamentalClass_eq_of_homotopic
    (o : Manifold.Orientation I M (Fin (n + 1))) {X : Type} [TopologicalSpace X]
    {f g : C(M, X)} (h : f.Homotopic g) :
    o.mapFundamentalClass f = o.mapFundamentalClass g := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def]
  congr 2
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} ℤ)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) h.some _ (n + 1)

end Model

section TwoModels

variable {E F H H' : Type*} {M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J 1 N] [BoundarylessManifold J N]
  [CompactSpace N]
  {n : ℕ}

/-- An orientation-preserving homeomorphism between compact boundaryless `C¹` manifolds carries
the fundamental class of the source to that of the target. -/
theorem mapFundamentalClass_homeomorph
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation J N (Fin (n + 1)))
    (e : M ≃ₜ N) (he : ∀ x, IsOrientationPreservingAt o o' e x) :
    o.mapFundamentalClass (e : C(M, N)) = o'.fundamentalClass := by
  let : ChartedSpace E (BoundarylessModel I M) := BoundarylessModel.interiorChartedSpace I
  let : ChartedSpace F (BoundarylessModel J N) := BoundarylessModel.interiorChartedSpace J
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  let Ψ := BoundarylessModel.interiorDiffeomorph J (M := N) 1
  let o₀ : Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel I M) (Fin (n + 1)) :=
    o.pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero) o.card_eq
  let o₀' : Manifold.Orientation 𝓘(ℝ, F) (BoundarylessModel J N) (Fin (n + 1)) :=
    o'.pullback Ψ.symm.contMDiff (fun _ ↦ Ψ.symm.isInvertible_mfderiv one_ne_zero) o'.card_eq
  have hΦs : ∀ z, IsOrientationPreservingAt o₀ o Φ.symm z :=
    isOrientationPreservingAt_pullback _ _ _ _
  have hΨ : ∀ y, IsOrientationPreservingAt o' o₀' Ψ y := fun y ↦ by
    refine (isOrientationPreservingAt_pullback _ _ _ _ (Ψ y)).of_comp ?_
      (Ψ.mdifferentiable one_ne_zero y)
    have hid : ⇑Ψ.symm ∘ ⇑Ψ = id := funext Ψ.symm_apply_apply
    rw [hid]
    exact isOrientationPreservingAt_id o' y
  let e₀ : BoundarylessModel I M ≃ₜ BoundarylessModel J N :=
    (Φ.symm.toHomeomorph.trans e).trans Ψ.toHomeomorph
  have he₀ : ∀ z, IsOrientationPreservingAt o₀ o₀' e₀ z := by
    intro z
    have hcoe : (e₀ : _ → _) = ⇑Ψ ∘ (⇑e ∘ ⇑Φ.symm) := by
      ext y
      simp only [e₀, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph, Function.comp_apply]
    rw [hcoe]
    exact (hΨ _).comp ((he (Φ.symm z)).comp (hΦs z))
  have hcomp : (e : C(M, N)).comp (Φ.symm.toHomeomorph : C(BoundarylessModel I M, M)) =
      (Ψ.symm.toHomeomorph : C(BoundarylessModel J N, N)).comp (e₀ : C(_, _)) := by
    ext z
    simp [e₀, Diffeomorph.coe_toHomeomorph]
  rw [mapFundamentalClass_def, fundamentalClass, fundamentalClass, ← ModuleCat.comp_apply,
    ← CategoryTheory.Functor.map_comp, ← TopCat.ofHom_comp, hcomp, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply,
    map_fundamentalClassSelf_homeomorph o₀ o₀' e₀ he₀]

end TwoModels

section InnerProductComparison

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {n : ℕ}

/-- On a compact manifold modelled on an `(n + 1)`-dimensional real inner product space `𝓘(ℝ, E)`,
`Manifold.Orientation.fundamentalClass` agrees with
`(o.toHomologicalOrientation hE).fundamentalClass hE`. -/
theorem fundamentalClass_eq_toHomologicalOrientation (hE : finrank ℝ E = n + 1)
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    o.fundamentalClass = (o.toHomologicalOrientation hE).fundamentalClass hE := by
  let : ChartedSpace E (BoundarylessModel 𝓘(ℝ, E) M) :=
    BoundarylessModel.interiorChartedSpace 𝓘(ℝ, E)
  let Φ := BoundarylessModel.interiorDiffeomorph 𝓘(ℝ, E) (M := M) 1
  let o₀ : Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel 𝓘(ℝ, E) M) (Fin (n + 1)) :=
    o.pullback Φ.symm.contMDiff (fun _ ↦ Φ.symm.isInvertible_mfderiv one_ne_zero) o.card_eq
  have hΦs : ∀ z, IsOrientationPreservingAt o₀ o Φ.symm.toHomeomorph z := by
    intro z
    rw [Diffeomorph.coe_toHomeomorph]
    exact isOrientationPreservingAt_pullback _ _ _ _ z
  rw [fundamentalClass, map_fundamentalClassSelf_homeomorph o₀ o Φ.symm.toHomeomorph hΦs,
    o.fundamentalClassSelf_eq_toHomologicalOrientation hE]

/-- On a compact manifold modelled on an `(n + 1)`-dimensional real inner product space `𝓘(ℝ, E)`,
`Manifold.Orientation.mapFundamentalClass` agrees with
`(o.toHomologicalOrientation hE).mapFundamentalClass hE`. -/
theorem mapFundamentalClass_eq_toHomologicalOrientation (hE : finrank ℝ E = n + 1)
    {X : Type} [TopologicalSpace X]
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) (f : C(M, X)) :
    o.mapFundamentalClass f =
      (o.toHomologicalOrientation hE).mapFundamentalClass hE f := by
  rw [o.mapFundamentalClass_def, o.fundamentalClass_eq_toHomologicalOrientation hE,
    HomologicalOrientation.mapFundamentalClass_def]

end InnerProductComparison

/-- On a compact manifold modelled on `𝓡 (n + 1)`, `Manifold.Orientation.fundamentalClass` agrees
with `(o.toHomologicalOrientation _).fundamentalClass _`. -/
@[simp]
theorem fundamentalClass_euclideanSpace {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) 1 M]
    [CompactSpace M] (o : Manifold.Orientation (𝓡 (n + 1)) M (Fin (n + 1))) :
    o.fundamentalClass =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).fundamentalClass
        finrank_euclideanSpace_fin :=
  o.fundamentalClass_eq_toHomologicalOrientation finrank_euclideanSpace_fin

/-- On a compact manifold modelled on `𝓡 (n + 1)`, `Manifold.Orientation.mapFundamentalClass`
agrees with `(o.toHomologicalOrientation _).mapFundamentalClass _`. -/
@[simp]
theorem mapFundamentalClass_euclideanSpace {n : ℕ} {M X : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) 1 M]
    [CompactSpace M] [TopologicalSpace X]
    (o : Manifold.Orientation (𝓡 (n + 1)) M (Fin (n + 1))) (f : C(M, X)) :
    o.mapFundamentalClass f =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).mapFundamentalClass
        finrank_euclideanSpace_fin f :=
  o.mapFundamentalClass_eq_toHomologicalOrientation finrank_euclideanSpace_fin f

end Boundaryless

end Manifold.Orientation

end TauCeti
