/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Square
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
import TauCeti.MeasureTheory.Integral.FullSimplex

/-!
# Integrals over spheres factor through the Hurewicz map

Let `φ` be a closed `C¹` two-form on a compact boundaryless manifold `M`, with values in a real
normed space `F`. Its integral over a class `a ∈ π₂(M, x)` (`TauCeti.sphereIntegral φ x a`) is the
integral of `φ` over the unit square along a smooth sphere representing `a`. This file shows that
these integrals factor through the integral Hurewicz map `π₂(M, x) → H₂(M; ℤ)`, uniformly in the
base point: there is an additive map `P : H₂(M; ℤ) → F` with `P (h a) = ∫_a φ` for every `x` and
every `a ∈ π₂(M, x)` (`TauCeti.exists_addMonoidHom_hurewiczIntHom_eq_sphereIntegralHom`). For the
symplectic form of a closed symplectic manifold, `P` is an area homomorphism on `H₂(M; ℤ)` that
agrees with the symplectic area of spheres on their Hurewicz classes, the compatibility through
which the capped action descends to cap classes
(`TauCeti.Floer.SphericalCapClass.action`).

The map is a period of `φ`. For a smooth sphere `v` at `x`, the two affine triangles of the unit
square composed with `v` are smooth singular simplices: on the full-dimensional simplex `Δ²` they
are `v ∘ A` for the shears `A y = (y₀ + y₁, y₁)` and `A y = (y₀, y₀ + y₁)`, both of determinant one.
So the triangulated cycle `GenLoop.squareChain` of the generalized loop of `v` is the image of a
smooth singular cycle, and the period of `φ` on its class (`TauCeti.smoothHomologyPeriodHom`) is the
sum of the integrals of `φ` over the two triangles. The two shears carry `Δ²` onto the lower and
upper halves of the unit square, which meet in a null set, so this sum is the integral of `φ` over
the square along `v`
(`TauCeti.IsSmoothSphere.smoothHomologyPeriodHom_smoothSingularHomologyIso_inv_squareClass`).
Since the square class is a universal integer multiple `k` of the Hurewicz class
(`GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz`), `P` is `k` times the period of `φ` read in
smooth singular homology through the smoothing isomorphism
(`TauCeti.smoothSingularHomologyIso`).

## Main results

* `TauCeti.IsSmoothSphere.smoothHomologyPeriodHom_smoothSingularHomologyIso_inv_squareClass`: the
  period of a closed two-form on the square class of a smooth sphere is its integral over the
  sphere.
* `TauCeti.exists_addMonoidHom_hurewiczIntHom_eq_sphereIntegralHom`: the integral of a closed
  two-form over spheres factors through the Hurewicz map into `H₂(M; ℤ)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (integration over smooth
  singular chains and the de Rham homomorphism).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 11.1, on the
  symplectic area of spherical classes.
-/

public section

noncomputable section

open Set MeasureTheory CategoryTheory Simplicial HomologicalComplex AlgebraicTopology
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The parametrization `y ↦ (y₀ + y₁, y₁)` of the lower triangle of the unit square by `Δ²`. -/
private def lowerTriangleMap : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) + EuclideanSpace.proj 1).prod (EuclideanSpace.proj 1)

/-- The parametrization `y ↦ (y₀, y₀ + y₁)` of the upper triangle of the unit square by `Δ²`. -/
private def upperTriangleMap : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).prod (EuclideanSpace.proj 0 + EuclideanSpace.proj 1)

private theorem lowerTriangleMap_apply (y : EuclideanSpace ℝ (Fin 2)) :
    lowerTriangleMap y = (y 0 + y 1, y 1) :=
  (rfl)

private theorem upperTriangleMap_apply (y : EuclideanSpace ℝ (Fin 2)) :
    upperTriangleMap y = (y 0, y 0 + y 1) :=
  (rfl)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The two-form `φ` evaluated along a map `v` of the plane on the coordinate vectors,
`z ↦ φ_{v z}(∂_s v, ∂_t v)`: the integrand of `TauCeti.rectangleIntegral φ v`. -/
private abbrev planeIntegrand (φ : RoughForm I M F 2) (v : ℝ × ℝ → M) (z : ℝ × ℝ) : F :=
  φ (v z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I v z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I v z (0, 1)]

/-- The pullback of a two-form by `v ∘ A` along a linear parametrization `A` of a triangle of the
unit square. Let `b₀ = (1, 0)` and `b₁ = (0, 1)`. If `A` sends the coordinate vector `eⱼ` of `Δ²`
to `bⱼ`, except that it sends `eᵢ` to `bᵢ + bₖ` for some `k ≠ i`, then on the coordinate vectors of
`Δ²` the pullback is the plane integrand of `v` at `A y`: the form does not see the added `bₖ`. -/
private theorem mpullback_comp_apply_of_update {v : ℝ × ℝ → M}
    (hv : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I v) (φ : RoughForm I M F 2)
    {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ} {i k : Fin 2} (hik : i ≠ k)
    (hA : ∀ j, A (EuclideanSpace.single j 1) =
      Function.update ![(1, 0), (0, 1)] i (![(1, 0), (0, 1)] i + ![(1, 0), (0, 1)] k) j)
    (y : EuclideanSpace ℝ (Fin 2)) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ A) φ y
        (fun j ↦ EuclideanSpace.single j 1) = planeIntegrand φ v (A y) := by
  set D := mfderiv 𝓘(ℝ, ℝ × ℝ) I v (A y)
  set m : Fin 2 → TangentSpace I (v (A y)) := fun j ↦ D (![(1, 0), (0, 1)] j)
  have hD : (fun j ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ A) y
      (EuclideanSpace.single j 1)) = Function.update m i (m i + m k) := by
    rw [mfderiv_comp y (hv _) A.mdifferentiableAt, ContinuousLinearMap.mfderiv_eq]
    ext j
    refine (congrArg D (hA j)).trans ?_
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact map_add D _ _
    · simp only [Function.update_of_ne hj, m]
  have hzero : φ (v (A y)) (Function.update m i (m k)) = 0 := (φ _).map_update_self _ hik
  refine (mpullback_apply (v ∘ A) φ y _).trans ?_
  rw [hD, Function.comp_apply, (φ _).map_update_add, Function.update_eq_self, hzero, add_zero]
  congr 1
  ext j
  fin_cases j <;> rfl

/-- Along the lower triangle parametrization `A y = (y₀ + y₁, y₁)`, the pullback of a two-form by
`v ∘ A` on the coordinate vectors of `Δ²` is the plane integrand of `v` at `A y`. -/
private theorem mpullback_comp_lowerTriangleMap_apply {v : ℝ × ℝ → M}
    (hv : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I v) (φ : RoughForm I M F 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ lowerTriangleMap) φ y
        (fun i ↦ EuclideanSpace.single i 1) = planeIntegrand φ v (lowerTriangleMap y) :=
  mpullback_comp_apply_of_update hv φ (i := 1) (k := 0) (by decide)
    (fun j ↦ by fin_cases j <;> simp [lowerTriangleMap_apply]) y

/-- Along the upper triangle parametrization `A y = (y₀, y₀ + y₁)`, the pullback of a two-form by
`v ∘ A` on the coordinate vectors of `Δ²` is the plane integrand of `v` at `A y`. -/
private theorem mpullback_comp_upperTriangleMap_apply {v : ℝ × ℝ → M}
    (hv : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I v) (φ : RoughForm I M F 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ upperTriangleMap) φ y
        (fun i ↦ EuclideanSpace.single i 1) = planeIntegrand φ v (upperTriangleMap y) :=
  mpullback_comp_apply_of_update hv φ (i := 0) (k := 1) (by decide)
    (fun j ↦ by fin_cases j <;> simp [upperTriangleMap_apply]) y

/-- Read on `Δ²`, the barycentric coordinates `w₁` and `w₂` are the coordinates `y₀` and `y₁`. -/
private theorem fullSimplexEquivStdSimplex_weights_one_two (y : fullSimplex 2) :
    (fullSimplexEquivStdSimplex 2 y).weights 1 = y.val 0 ∧
      (fullSimplexEquivStdSimplex 2 y).weights 2 = y.val 1 :=
  ⟨fullSimplexEquivStdSimplex_weights_succ y 0, fullSimplexEquivStdSimplex_weights_succ y 1⟩

/-- Read on `Δ²`, the lower triangle of the square is the parametrization `y ↦ (y₀ + y₁, y₁)`. -/
private theorem squareLowerTriangle_fullSimplexEquivStdSimplex (y : fullSimplex 2) :
    (((squareLowerTriangle (fullSimplexEquivStdSimplex 2 y) 0 : ℝ),
      (squareLowerTriangle (fullSimplexEquivStdSimplex 2 y) 1 : ℝ))) = lowerTriangleMap y := by
  simp [lowerTriangleMap_apply, fullSimplexEquivStdSimplex_weights_one_two]

/-- Read on `Δ²`, the upper triangle of the square is the parametrization `y ↦ (y₀, y₀ + y₁)`. -/
private theorem squareUpperTriangle_fullSimplexEquivStdSimplex (y : fullSimplex 2) :
    (((squareUpperTriangle (fullSimplexEquivStdSimplex 2 y) 0 : ℝ),
      (squareUpperTriangle (fullSimplexEquivStdSimplex 2 y) 1 : ℝ))) = upperTriangleMap y := by
  simp [upperTriangleMap_apply, fullSimplexEquivStdSimplex_weights_one_two]

namespace IsSmoothSphere

variable {x : M} {v : ℝ × ℝ → M}

/-- For a triangle `T` of the unit square which, read on `Δ²`, is a linear map `A : ℝ² → ℝ²`, the
singular simplex `p ∘ T` of the generalized loop `p` of a smooth sphere `v` is smooth: on `Δ²` it
is `v ∘ A`. -/
private def triangleSimplex (hv : IsSmoothSphere I x v)
    (T : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → unitInterval))
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ)
    (hTA : ∀ y : fullSimplex 2,
      ((T (fullSimplexEquivStdSimplex 2 y) 0 : ℝ), (T (fullSimplexEquivStdSimplex 2 y) 1 : ℝ)) =
        A y) :
    SmoothSimplex I M 2 :=
  ⟨((TopCat.of M).toSSetObjEquiv (.op ⦋2⦌)).symm ((hv.genLoop : C(Fin 2 → unitInterval, M)).comp T),
    mem_smoothSingularSubcomplex_of_contMDiffOn _ (hv.contMDiff.comp A.contMDiff).contMDiffOn
      Filter.univ_mem fun y ↦ by
        rw [Equiv.apply_symm_apply]
        exact (hv.genLoop_apply _).trans (congrArg v (hTA y))⟩

variable {T : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → unitInterval)}
  {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ}
  {hTA : ∀ y : fullSimplex 2,
    ((T (fullSimplexEquivStdSimplex 2 y) 0 : ℝ), (T (fullSimplexEquivStdSimplex 2 y) 1 : ℝ)) = A y}

/-- The underlying singular simplex of the triangle simplex of `v` is the singular simplex of
`p ∘ T`, for the generalized loop `p` of `v`. -/
private theorem triangleSimplex_val (hv : IsSmoothSphere I x v) :
    (hv.triangleSimplex T A hTA).val = ((TopCat.of M).toSSetObjEquiv (.op ⦋2⦌)).symm
      ((hv.genLoop : C(Fin 2 → unitInterval, M)).comp T) :=
  (rfl)

/-- Read on `Δ²`, the triangle simplex of a smooth sphere `v` is `v ∘ A`. -/
private theorem triangleSimplex_toContinuousMap_apply (hv : IsSmoothSphere I x v)
    (y : fullSimplex 2) : (hv.triangleSimplex T A hTA).toContinuousMap y = v (A y) := by
  rw [SmoothSimplex.toContinuousMap_apply]
  dsimp only [triangleSimplex]
  rw [Equiv.apply_symm_apply]
  exact (hv.genLoop_apply _).trans (congrArg v (hTA y))

/-- The integral of a two-form over a triangle simplex of a smooth sphere `v` is the integral over
`Δ²` of the pullback of the form by `v ∘ A` on the coordinate vectors. -/
private theorem integral_triangleSimplex (hv : IsSmoothSphere I x v) (φ : RoughForm I M F 2) :
    (hv.triangleSimplex T A hTA).integral φ = ∫ y in fullSimplex 2,
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ A) φ y
        (fun i ↦ EuclideanSpace.single i 1) :=
  (hv.triangleSimplex T A hTA).integral_eq_setIntegral_mpullback φ
    (fun y ↦ (hv.triangleSimplex_toContinuousMap_apply y).symm)
    fun _ _ ↦ (hv.contMDiff.comp (A.contMDiff (n := ∞))).mdifferentiableAt (by simp)

/-- The smooth simplex of the lower triangle of a smooth sphere. -/
private abbrev lowerSimplex (hv : IsSmoothSphere I x v) : SmoothSimplex I M 2 :=
  hv.triangleSimplex squareLowerTriangle lowerTriangleMap
    squareLowerTriangle_fullSimplexEquivStdSimplex

/-- The smooth simplex of the upper triangle of a smooth sphere. -/
private abbrev upperSimplex (hv : IsSmoothSphere I x v) : SmoothSimplex I M 2 :=
  hv.triangleSimplex squareUpperTriangle upperTriangleMap
    squareUpperTriangle_fullSimplexEquivStdSimplex

/-- The triangulated cycle of a smooth sphere `v`, as a smooth singular chain: the lower and upper
triangle simplices minus twice the constant simplex at `x`. -/
private def smoothSquareChain (hv : IsSmoothSphere I x v) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X 2 :=
  ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      hv.lowerSimplex).hom 1
    + ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      hv.upperSimplex).hom 1
    - 2 • ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (SmoothSimplex.const x)).hom 1

/-- As a singular chain, the smooth triangulated chain of a smooth sphere is the triangulated chain
of its generalized loop. -/
private theorem chainComplexMap_ι_f_smoothSquareChain (hv : IsSmoothSphere I x v) :
    ((SSet.chainComplexMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ)).f 2).hom
      hv.smoothSquareChain = GenLoop.squareChain hv.genLoop := by
  have h (σ : SmoothSimplex I M 2) :
      ((SSet.chainComplexMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ)).f 2).hom
        (((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      simplexChain (X := TopCat.of M) σ.val 1 := by
    rw [← ConcreteCategory.comp_apply, SSet.ι_chainComplexMap_f]
    -- `simplexChain` is `ιChainComplex` of `TopCat.toSSet.obj _`, whose chain complex is by
    -- definition `(singularChains ℤ).obj _`, and the inclusion of the subcomplex sends `σ` to
    -- `σ.val`.
    rfl
  rw [smoothSquareChain, map_sub, map_add, map_nsmul, h, h, h, GenLoop.squareChain_def,
    triangleSimplex_val, triangleSimplex_val, SmoothSimplex.coe_const]
  -- The two sides are the same chain, with its sum and difference taken in the degree-`2` chains
  -- of `SSet.chainComplex (TopCat.toSSet.obj _)` and of `(singularChains ℤ).obj _` respectively,
  -- which are the same module by definition.
  rfl

/-- The smooth triangulated chain of a smooth sphere is a cycle, since its image among all singular
chains is one and the inclusion of smooth chains is injective. -/
private theorem d_smoothSquareChain (hv : IsSmoothSphere I x v) :
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d 2 1).hom
      hv.smoothSquareChain = 0 := by
  apply (ModuleCat.mono_iff_injective
    ((SSet.chainComplexMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ)).f 1)).1
    inferInstance
  rw [map_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.Hom.comm, ModuleCat.comp_apply,
    chainComplexMap_ι_f_smoothSquareChain]
  exact GenLoop.d_squareChain hv.genLoop

/-- The class of the smooth triangulated cycle of a smooth sphere in smooth singular homology. -/
private def smoothSquareClass (hv : IsSmoothSphere I x v) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology 2 :=
  (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ 2).hom
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).moduleCatCyclesMk
      hv.smoothSquareChain 1 (ChainComplex.next_nat_succ 1) hv.d_smoothSquareChain)

/-- The inclusion of smooth chains sends the smooth square class of a smooth sphere to the square
class of its generalized loop. -/
private theorem homologyMap_ι_smoothSquareClass (hv : IsSmoothSphere I x v) :
    (SSet.homologyMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ) 2).hom
      hv.smoothSquareClass = GenLoop.squareClass hv.genLoop := by
  rw [smoothSquareClass, SSet.homologyMap, homologyMap_homologyπ_moduleCatCyclesMk,
    GenLoop.squareClass_def]
  simp only [chainComplexMap_ι_f_smoothSquareChain]
  -- The cycles and homology of `SSet.chainComplex (TopCat.toSSet.obj _)` are by definition those
  -- of `(singularChains ℤ).obj _`.
  rfl

variable {φ : RoughForm I M F 2}

section Period

variable [IsManifold I 2 M]

/-- The period of a closed `C¹` two-form on the smooth square class of a smooth sphere `v` is its
integral over `v` on the unit square. -/
private theorem smoothHomologyPeriodHom_smoothSquareClass (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hv : IsSmoothSphere I x v) :
    smoothHomologyPeriodHom φ hv.smoothSquareClass = rectangleIntegral φ v (0, 0) (1, 1) := by
  rw [smoothSquareClass, smoothHomologyPeriodHom_homologyπ hφ hdφ,
    HomologicalComplex.iCycles_moduleCatCyclesMk, smoothSquareChain, map_sub, map_add, map_nsmul,
    integrationCochain_ιChainComplex, integrationCochain_ιChainComplex,
    integrationCochain_ιChainComplex, SmoothSimplex.integral_const, integral_triangleSimplex,
    integral_triangleSimplex, one_smul, one_smul, one_smul, smul_zero, sub_zero]
  have hv' := hv.contMDiff.mdifferentiable (by simp)
  simp only [mpullback_comp_lowerTriangleMap_apply hv', mpullback_comp_upperTriangleMap_apply hv',
    lowerTriangleMap_apply, upperTriangleMap_apply]
  rw [setIntegral_fullSimplex_add_setIntegral_fullSimplex (f := planeIntegrand φ v)
      ((hφ.of_le (by simp)).continuous_apply_mfderiv (hv.contMDiff.of_le (by simp)) (1, 0)
        (0, 1)).integrableOn_Icc]
  exact (hφ.of_le (by simp)).setIntegral_eq_rectangleIntegral (hv.contMDiff.of_le (by simp))
    (by simp [Prod.le_def])

end Period

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **The period on the square class of a smooth sphere.** For a smooth sphere `v` at `x` and a
closed `C¹` two-form `φ`, the period of `φ` on the square class of the generalized loop of `v`,
read in smooth singular homology through the smoothing isomorphism, is the integral of `φ` over `v`
on the unit square. -/
theorem smoothHomologyPeriodHom_smoothSingularHomologyIso_inv_squareClass
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (hv : IsSmoothSphere I x v) :
    smoothHomologyPeriodHom φ ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) 2).inv.hom
      (GenLoop.squareClass hv.genLoop)) = rectangleIntegral φ v (0, 0) (1, 1) := by
  rw [← hv.homologyMap_ι_smoothSquareClass, ← smoothSingularHomologyIso_hom,
    ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply,
    hv.smoothHomologyPeriodHom_smoothSquareClass hφ hdφ]

end IsSmoothSphere

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

/-- **Integrals over spheres factor through the Hurewicz map.** For a closed `C¹` two-form `φ` on
a compact boundaryless manifold `M`, there is an additive map `P : H₂(M; ℤ) → F` whose value on the
Hurewicz class of every `a ∈ π₂(M, x)`, at every base point `x`, is the integral of `φ` over `a`.
For the symplectic form of a closed symplectic manifold, `P` is an area homomorphism on `H₂(M; ℤ)`
agreeing with the symplectic area of spheres on their Hurewicz classes. -/
theorem exists_addMonoidHom_hurewiczIntHom_eq_sphereIntegralHom {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    ∃ P : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of M) →+ F,
      ∀ (x : M) (a : Additive (π_ 2 M x)),
        P (HomotopyGroup.hurewiczIntHom M x 1 a) = sphereIntegralHom x hφ hdφ a := by
  obtain ⟨k, hk⟩ := GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz
  -- The period of `φ` on singular homology, read in smooth singular homology.
  let P₀ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of M) →+ F :=
    (smoothHomologyPeriodHom (R := ℤ) φ).toAddMonoidHom.comp
      (smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) 2).inv.hom.toAddMonoidHom
  refine ⟨k • P₀, fun x a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  obtain ⟨v, hv, rfl⟩ := exists_isSmoothSphere (I := I) a
  rw [HomotopyGroup.hurewiczIntHom_mk, AddMonoidHom.smul_apply, ← map_zsmul, ← hk,
    sphereIntegralHom_apply]
  exact (hv.smoothHomologyPeriodHom_smoothSingularHomologyIso_inv_squareClass hφ hdφ).trans
    (sphereIntegral_mk hφ hdφ hv).symm

end TauCeti
