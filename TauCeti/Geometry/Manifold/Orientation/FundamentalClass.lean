/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Interior

/-!
# The integral fundamental class of a compact oriented smooth manifold

Let `(M, I)` be a compact boundaryless `C¹` manifold (`[BoundarylessManifold I M]`) of dimension
`n + 1`, with orientation `o : TauCeti.Manifold.Orientation I M (Fin (n + 1))`. While
`TauCeti.Manifold.Orientation.toHomologicalOrientation` requires a self-modelled real inner product
space `𝓘(ℝ, E)`, any boundaryless `C¹` manifold can be transported via
`TauCeti.BoundarylessModel.interiorDiffeomorph` to its interior vector-space atlas
`TauCeti.BoundarylessModel.interiorChartedSpace` and then recharted to a self-modelled Euclidean
copy via `TauCeti.BoundarylessModel.diffeomorphTransContinuousLinearEquiv`.

Because orientation-preserving open embeddings pull back `toHomologicalOrientation`
(`TauCeti.Manifold.Orientation.comap_toHomologicalOrientation`), the resulting class
`TauCeti.Manifold.Orientation.fundamentalClass o ∈ Hₙ₊₁(M; ℤ)` is independent of the chosen linear
equivalence with `EuclideanSpace ℝ (Fin (n + 1))`. It agrees with
`(o.toHomologicalOrientation hE).fundamentalClass hE` on every `(n + 1)`-dimensional real inner
product model `𝓘(ℝ, E)`
(`TauCeti.Manifold.Orientation.fundamentalClass_eq_toHomologicalOrientation`, specialized to
`𝓡 (n + 1)` in `TauCeti.Manifold.Orientation.fundamentalClass_euclideanSpace`), and is natural
under pointwise orientation-preserving homeomorphisms between compact boundaryless `C¹` manifolds
(with arbitrary models) (`TauCeti.Manifold.Orientation.mapFundamentalClass_homeomorph`).

## Main definitions

* `TauCeti.Manifold.Orientation.fundamentalClass`: the integral fundamental class `[M] ∈ Hₙ₊₁(M; ℤ)`
  of a compact oriented boundaryless `C¹` manifold `(M, I)`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass`: the pushforward `f_*[M] ∈ Hₙ₊₁(X; ℤ)` along
  a continuous map `f : C(M, X)`.

## Main results

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
  `TauCeti.Manifold.Orientation.mapFundamentalClass_euclideanSpace`: specializations to `𝓡 (n + 1)`.

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

namespace TauCeti

namespace Manifold.Orientation

section SelfModel

variable {E : Type*} {M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {n : ℕ}

/-- The integral fundamental class of a compact oriented self-modelled `C¹` manifold
`(M, 𝓘(ℝ, E))`. -/
private def fundamentalClassSelf (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  ((o.transContinuousLinearEquiv
    o.modelEquivEuclidean).toBoundarylessModel.toHomologicalOrientation
    finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
    ((BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
      o.modelEquivEuclidean 1).symm.toHomeomorph :
      C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv o.modelEquivEuclidean) M, M))

/-- Pushing forward the Euclidean-recharted fundamental class of `(M, o)` along an
orientation-preserving homeomorphism `h : M ≃ₜ N` produces the Euclidean-recharted fundamental
class of `(N, o')`, for any choices of linear equivalences `eM` and `eN`. -/
private theorem map_fundamentalClassSelf_of_homeomorph
    {F : Type*} {N : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [T2Space N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) 1 N] [CompactSpace N]
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1)))
    (eM : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (eN : F ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (h : M ≃ₜ N) (hh : ∀ x, IsOrientationPreservingAt o o' h x) :
    (((o.transContinuousLinearEquiv eM).toBoundarylessModel).toHomologicalOrientation
        finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
        ((h : C(M, N)).comp
          ((BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
            eM 1).symm.toHomeomorph :
            C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv eM) M, M))) =
      (((o'.transContinuousLinearEquiv eN).toBoundarylessModel).toHomologicalOrientation
        finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
        ((BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, F) (M := N)
          eN 1).symm.toHomeomorph :
          C(BoundarylessModel (𝓘(ℝ, F).transContinuousLinearEquiv eN) N, N)) := by
  set Φ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M) eM 1
  set Φ' := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, F) (M := N) eN 1
  let Θ := (Φ.symm.toHomeomorph.trans h).trans Φ'.toHomeomorph
  have hΘ : ∀ z, IsOrientationPreservingAt
      (o.transContinuousLinearEquiv eM).toBoundarylessModel
      (o'.transContinuousLinearEquiv eN).toBoundarylessModel Θ z := by
    intro z
    have hcoe : (Θ : _ → _) = ⇑Φ' ∘ (⇑h ∘ ⇑Φ.symm) := by
      ext y
      simp only [Θ, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph, Function.comp_apply]
    rw [hcoe]
    exact (o'.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv eN 1 _).comp
      ((hh (Φ.symm z)).comp
        (o.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv_symm eM 1 z))
  have hcomp : (h : C(M, N)).comp
      (Φ.symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv eM) M, M)) =
      (Φ'.symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, F).transContinuousLinearEquiv eN) N, N)).comp
        (Θ : C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv eM) M,
          BoundarylessModel (𝓘(ℝ, F).transContinuousLinearEquiv eN) N)) := by
    ext z
    simp [Θ, Diffeomorph.coe_toHomeomorph]
  rw [hcomp, ← comap_toHomologicalOrientation finrank_euclideanSpace_fin _ _ Θ.isOpenEmbedding hΘ,
    HomologicalOrientation.mapFundamentalClass_comap_comp]

/-- Any continuous linear equivalence `e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))` computes
`o.fundamentalClassSelf`. -/
private theorem fundamentalClassSelf_eq (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    o.fundamentalClassSelf =
      (((o.transContinuousLinearEquiv e).toBoundarylessModel).toHomologicalOrientation
        finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
        ((BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
          e 1).symm.toHomeomorph :
          C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv e) M, M)) := by
  have hrefl : (Homeomorph.refl M : C(M, M)) = ContinuousMap.id M := Homeomorph.coe_refl
  rw [fundamentalClassSelf,
    ← ContinuousMap.id_comp (f :=
      ((BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
        o.modelEquivEuclidean 1).symm.toHomeomorph :
        C(BoundarylessModel (𝓘(ℝ, E).transContinuousLinearEquiv o.modelEquivEuclidean) M, M))),
    ← hrefl]
  exact map_fundamentalClassSelf_of_homeomorph o o o.modelEquivEuclidean e (Homeomorph.refl M)
    (isOrientationPreservingAt_id o)

private theorem fundamentalClassSelf_neg (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    (-o).fundamentalClassSelf = -o.fundamentalClassSelf := by
  rw [(-o).fundamentalClassSelf_eq o.modelEquivEuclidean, fundamentalClassSelf,
    neg_transContinuousLinearEquiv, toBoundarylessModel_neg, toHomologicalOrientation_neg,
    HomologicalOrientation.mapFundamentalClass_neg]

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
  rw [fundamentalClassSelf, ← HomologicalOrientation.mapFundamentalClass_comp,
    map_fundamentalClassSelf_of_homeomorph o o' o.modelEquivEuclidean o'.modelEquivEuclidean e he,
    ← fundamentalClassSelf]

end SelfModel

section SelfModelInnerProduct

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {n : ℕ}

private theorem fundamentalClassSelf_eq_toHomologicalOrientation
    (hE : finrank ℝ E = n + 1) (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    o.fundamentalClassSelf = (o.toHomologicalOrientation hE).fundamentalClass hE := by
  let f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr
  set I' := 𝓘(ℝ, E).transContinuousLinearEquiv f.toContinuousLinearEquiv
  let Φ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
    f.toContinuousLinearEquiv 1
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
    ← o.localHomologyMap_diffeomorphTransContinuousLinearEquiv_localOrientation hE f 1 x,
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

attribute [local instance] BoundarylessModel.interiorChartedSpace

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
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom (Φ.symm.toHomeomorph : C(BoundarylessModel I M, M)))).hom
    o.interiorOrientation.fundamentalClassSelf

/-- Reversing a manifold orientation negates its fundamental class. -/
@[simp]
theorem fundamentalClass_neg (o : Manifold.Orientation I M (Fin (n + 1))) :
    (-o).fundamentalClass = -o.fundamentalClass := by
  rw [fundamentalClass, fundamentalClass, interiorOrientation_neg, fundamentalClassSelf_neg,
    map_neg]

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
  rw [mapFundamentalClass_def, mapFundamentalClass_def,
    ContinuousMap.singularHomologyFunctor_map_eq_of_homotopic (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)
      h]

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
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) 1
  let Ψ := BoundarylessModel.interiorDiffeomorph J (M := N) 1
  let e₀ : BoundarylessModel I M ≃ₜ BoundarylessModel J N :=
    (Φ.symm.toHomeomorph.trans e).trans Ψ.toHomeomorph
  have he₀ : ∀ z, IsOrientationPreservingAt o.interiorOrientation o'.interiorOrientation e₀ z := by
    intro z
    have hcoe : (e₀ : _ → _) = ⇑Ψ ∘ (⇑e ∘ ⇑Φ.symm) := by
      ext y
      simp only [e₀, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph, Function.comp_apply]
    rw [hcoe]
    exact (o'.isOrientationPreservingAt_interiorDiffeomorph 1 _).comp
      ((he (Φ.symm z)).comp (o.isOrientationPreservingAt_interiorDiffeomorph_symm 1 z))
  have hcomp : (e : C(M, N)).comp (Φ.symm.toHomeomorph : C(BoundarylessModel I M, M)) =
      (Ψ.symm.toHomeomorph : C(BoundarylessModel J N, N)).comp (e₀ : C(_, _)) := by
    ext z
    simp [e₀, Diffeomorph.coe_toHomeomorph]
  rw [mapFundamentalClass_def, fundamentalClass, fundamentalClass, ← ModuleCat.comp_apply,
    ← CategoryTheory.Functor.map_comp, ← TopCat.ofHom_comp, hcomp, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply,
    map_fundamentalClassSelf_homeomorph o.interiorOrientation o'.interiorOrientation e₀ he₀]

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
  let Φ := BoundarylessModel.interiorDiffeomorph 𝓘(ℝ, E) (M := M) 1
  have hΦs : ∀ z, IsOrientationPreservingAt o.interiorOrientation o Φ.symm.toHomeomorph z := by
    intro z
    rw [Diffeomorph.coe_toHomeomorph]
    exact o.isOrientationPreservingAt_interiorDiffeomorph_symm 1 z
  rw [fundamentalClass, map_fundamentalClassSelf_homeomorph o.interiorOrientation o
      Φ.symm.toHomeomorph hΦs, o.fundamentalClassSelf_eq_toHomologicalOrientation hE]

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
theorem fundamentalClass_euclideanSpace {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) 1 M]
    [CompactSpace M] (o : Manifold.Orientation (𝓡 (n + 1)) M (Fin (n + 1))) :
    o.fundamentalClass =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).fundamentalClass
        finrank_euclideanSpace_fin :=
  o.fundamentalClass_eq_toHomologicalOrientation finrank_euclideanSpace_fin

/-- On a compact manifold modelled on `𝓡 (n + 1)`, `Manifold.Orientation.mapFundamentalClass`
agrees with `(o.toHomologicalOrientation _).mapFundamentalClass _`. -/
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
