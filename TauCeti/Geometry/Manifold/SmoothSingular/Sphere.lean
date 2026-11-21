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

/-- The coordinates `(y₀, y₁)` of a point of the Euclidean plane, as a volume-preserving
measurable equivalence onto `ℝ × ℝ`. -/
private def euclideanPlaneEquivProd : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem euclideanPlaneEquivProd_apply (y : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneEquivProd y = (y 0, y 1) :=
  (rfl)

private theorem measurePreserving_euclideanPlaneEquivProd :
    MeasurePreserving euclideanPlaneEquivProd :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

/-- A shear of the plane fixing one coordinate is a measurable embedding. -/
private theorem measurableEmbedding_shear_fst :
    MeasurableEmbedding fun z : ℝ × ℝ ↦ (z.1 + z.2, z.2) :=
  .of_measurable_inverse (by fun_prop) (by
      rw [Set.range_eq_univ.2 fun z ↦ ⟨(z.1 - z.2, z.2), by simp⟩]; exact .univ)
    (g := fun z : ℝ × ℝ ↦ (z.1 - z.2, z.2)) (by fun_prop) fun z ↦ by simp

private theorem measurableEmbedding_shear_snd :
    MeasurableEmbedding fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2) :=
  .of_measurable_inverse (by fun_prop) (by
      rw [Set.range_eq_univ.2 fun z ↦ ⟨(z.1, z.2 - z.1), by simp⟩]; exact .univ)
    (g := fun z : ℝ × ℝ ↦ (z.1, z.2 - z.1)) (by fun_prop) fun z ↦ by simp

/-- The lower half `{0 ≤ t ≤ s ≤ 1}` of the unit square. -/
private def squareLowerHalf : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 1}

/-- The upper half `{0 ≤ s ≤ t ≤ 1}` of the unit square. -/
private def squareUpperHalf : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 1}

/-- The shear `y ↦ (y₀ + y₁, y₁)` carries `Δ²` onto the lower half `{0 ≤ t ≤ s ≤ 1}` of the unit
square, preserving volume. -/
private theorem setIntegral_fullSimplex_comp_shear_fst (f : ℝ × ℝ → F) :
    ∫ y in fullSimplex 2, f (y 0 + y 1, y 1) =
      ∫ z in squareLowerHalf, f z := by
  have hmp : MeasurePreserving ((fun z : ℝ × ℝ ↦ (z.1 + z.2, z.2)) ∘ euclideanPlaneEquivProd) :=
    (measurePreserving_add_prod volume volume).comp measurePreserving_euclideanPlaneEquivProd
  have h := hmp.setIntegral_preimage_emb
      (measurableEmbedding_shear_fst.comp euclideanPlaneEquivProd.measurableEmbedding) f
      squareLowerHalf
  have hpre :
      (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.2)) ∘ euclideanPlaneEquivProd ⁻¹' squareLowerHalf =
        fullSimplex 2 := by
    ext y
    simp only [squareLowerHalf, mem_preimage, Function.comp_apply, euclideanPlaneEquivProd_apply,
      mem_ofPred_eq, mem_fullSimplex_iff, Fin.forall_fin_two, Fin.sum_univ_two]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨by linarith, h₁⟩, h₃⟩
    · rintro ⟨⟨h₀, h₁⟩, h₂⟩; exact ⟨h₁, by linarith, h₂⟩
  rw [hpre] at h
  simpa only [Function.comp_apply, euclideanPlaneEquivProd_apply] using h

/-- The shear `y ↦ (y₀, y₀ + y₁)` carries `Δ²` onto the upper half `{0 ≤ s ≤ t ≤ 1}` of the unit
square, preserving volume. -/
private theorem setIntegral_fullSimplex_comp_shear_snd (f : ℝ × ℝ → F) :
    ∫ y in fullSimplex 2, f (y 0, y 0 + y 1) =
      ∫ z in squareUpperHalf, f z := by
  have hmp : MeasurePreserving ((fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ∘ euclideanPlaneEquivProd) :=
    (measurePreserving_prod_add volume volume).comp measurePreserving_euclideanPlaneEquivProd
  have h := hmp.setIntegral_preimage_emb
      (measurableEmbedding_shear_snd.comp euclideanPlaneEquivProd.measurableEmbedding) f
      squareUpperHalf
  have hpre :
      (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ∘ euclideanPlaneEquivProd ⁻¹' squareUpperHalf =
        fullSimplex 2 := by
    ext y
    simp only [squareUpperHalf, mem_preimage, Function.comp_apply, euclideanPlaneEquivProd_apply,
      mem_ofPred_eq, mem_fullSimplex_iff, Fin.forall_fin_two, Fin.sum_univ_two]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, by linarith⟩, h₃⟩
    · rintro ⟨⟨h₀, h₁⟩, h₂⟩; exact ⟨h₀, by linarith, h₂⟩
  rw [hpre] at h
  simpa only [Function.comp_apply, euclideanPlaneEquivProd_apply] using h

/-- **The unit square is the union of two simplices.** For a function `f` integrable on the unit
square, the integrals of `f` over its lower and upper triangles, each parametrized by the
full-dimensional simplex `Δ²` through a shear of determinant one, add up to its integral over the
square. -/
private theorem setIntegral_fullSimplex_add_setIntegral_fullSimplex {f : ℝ × ℝ → F}
    (hf : IntegrableOn f (Icc (0, 0) (1, 1))) :
    (∫ y in fullSimplex 2, f (y 0 + y 1, y 1)) + ∫ y in fullSimplex 2, f (y 0, y 0 + y 1) =
      ∫ z in Icc (0, 0) (1, 1), f z := by
  have hunion : squareLowerHalf ∪ squareUpperHalf = Icc (0, 0) (1, 1) := by
    ext z
    simp only [mem_union, mem_ofPred_eq, squareLowerHalf, squareUpperHalf, mem_Icc]
    constructor
    · rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩)
      exacts [⟨⟨by linarith, h₁⟩, h₃, by linarith⟩, ⟨⟨h₁, by linarith⟩, by linarith, h₃⟩]
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      rcases le_total z.1 z.2 with h | h
      exacts [Or.inr ⟨h₁, h, h₄⟩, Or.inl ⟨h₂, h, h₃⟩]
  -- The two triangles meet in the diagonal, a line, which is a null set.
  have hdisj : AEDisjoint volume squareLowerHalf squareUpperHalf := by
    rw [AEDisjoint, Measure.volume_eq_prod]
    refine measure_mono_null (t := (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) :
      Set (ℝ × ℝ))) (fun z hz ↦ ?_) (Measure.addHaar_submodule _ _ fun h ↦ ?_)
    · simp only [mem_inter_iff, mem_ofPred_eq, squareLowerHalf, squareUpperHalf] at hz
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, sub_eq_zero]
      exact le_antisymm hz.2.2.1 hz.1.2.1
    · have h10 : ((1, 0) : ℝ × ℝ) ∈ LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) :=
        h ▸ Submodule.mem_top
      simp at h10
  have hT₂ : MeasurableSet squareUpperHalf :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  rw [setIntegral_fullSimplex_comp_shear_fst, setIntegral_fullSimplex_comp_shear_snd,
    ← setIntegral_union₀ hdisj hT₂.nullMeasurableSet
      (hf.mono_set (hunion ▸ subset_union_left)) (hf.mono_set (hunion ▸ subset_union_right)),
    hunion]

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

/-- Along the lower triangle parametrization `A y = (y₀ + y₁, y₁)`, the pullback of a two-form by
`v ∘ A` on the coordinate vectors of `Δ²` is the plane integrand of `v` at `A y`: the
derivative of `A` sends them to `(1, 0)` and `(1, 1)`, and the form does not see the added
`(1, 0)`. -/
private theorem mpullback_comp_lowerTriangleMap_apply {v : ℝ × ℝ → M}
    (hv : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I v) (φ : RoughForm I M F 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ lowerTriangleMap) φ y
        (fun i ↦ EuclideanSpace.single i 1) = planeIntegrand φ v (lowerTriangleMap y) := by
  set D := mfderiv 𝓘(ℝ, ℝ × ℝ) I v (lowerTriangleMap y)
  have hD : (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ lowerTriangleMap) y
      (EuclideanSpace.single i 1)) = Function.update ![D (1, 0), D (0, 1)] 1 (D (1, 0) + D (0, 1))
      := by
    rw [mfderiv_comp y (hv _) lowerTriangleMap.mdifferentiableAt, ContinuousLinearMap.mfderiv_eq]
    have h₀ : lowerTriangleMap (EuclideanSpace.single 0 1) = (1, 0) := by
      simp [lowerTriangleMap_apply]
    have h₁ : lowerTriangleMap (EuclideanSpace.single 1 1) = (1, 0) + (0, 1) := by
      simp [lowerTriangleMap_apply]
    ext i
    fin_cases i
    · exact (congrArg D h₀).trans (by simp)
    · exact (congrArg D h₁).trans ((map_add D _ _).trans (by simp))
  have hzero :
      φ (v (lowerTriangleMap y)) (Function.update ![D (1, 0), D (0, 1)] 1 (D (1, 0))) = 0 :=
    (φ _).map_update_self _ (i := 1) (j := 0) (by decide)
  refine (mpullback_apply (v ∘ lowerTriangleMap) φ y _).trans ?_
  rw [hD, Function.comp_apply, (φ _).map_update_add, hzero, zero_add]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Along the upper triangle parametrization `A y = (y₀, y₀ + y₁)`, the pullback of a two-form by
`v ∘ A` on the coordinate vectors of `Δ²` is the plane integrand of `v` at `A y`: the
derivative of `A` sends them to `(1, 1)` and `(0, 1)`, and the form does not see the added
`(0, 1)`. -/
private theorem mpullback_comp_upperTriangleMap_apply {v : ℝ × ℝ → M}
    (hv : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I v) (φ : RoughForm I M F 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ upperTriangleMap) φ y
        (fun i ↦ EuclideanSpace.single i 1) = planeIntegrand φ v (upperTriangleMap y) := by
  set D := mfderiv 𝓘(ℝ, ℝ × ℝ) I v (upperTriangleMap y)
  have hD : (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (v ∘ upperTriangleMap) y
      (EuclideanSpace.single i 1)) = Function.update ![D (1, 0), D (0, 1)] 0 (D (1, 0) + D (0, 1))
      := by
    rw [mfderiv_comp y (hv _) upperTriangleMap.mdifferentiableAt, ContinuousLinearMap.mfderiv_eq]
    have h₀ : upperTriangleMap (EuclideanSpace.single 0 1) = (1, 0) + (0, 1) := by
      simp [upperTriangleMap_apply]
    have h₁ : upperTriangleMap (EuclideanSpace.single 1 1) = (0, 1) := by
      simp [upperTriangleMap_apply]
    ext i
    fin_cases i
    · exact (congrArg D h₀).trans ((map_add D _ _).trans (by simp))
    · exact (congrArg D h₁).trans (by simp)
  have hzero :
      φ (v (upperTriangleMap y)) (Function.update ![D (1, 0), D (0, 1)] 0 (D (0, 1))) = 0 :=
    (φ _).map_update_self _ (i := 0) (j := 1) (by decide)
  refine (mpullback_apply (v ∘ upperTriangleMap) φ y _).trans ?_
  rw [hD, Function.comp_apply, (φ _).map_update_add, hzero, add_zero]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Read on `Δ²`, the lower triangle of the square is the parametrization `y ↦ (y₀ + y₁, y₁)`. -/
private theorem squareLowerTriangle_fullSimplexEquivStdSimplex (y : fullSimplex 2) :
    (((squareLowerTriangle (fullSimplexEquivStdSimplex 2 y) 0 : ℝ),
      (squareLowerTriangle (fullSimplexEquivStdSimplex 2 y) 1 : ℝ))) = lowerTriangleMap y := by
  have h₀ := fullSimplexEquivStdSimplex_weights_succ y 0
  have h₁ := fullSimplexEquivStdSimplex_weights_succ y 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h₀ h₁
  rw [squareLowerTriangle_apply_zero, squareLowerTriangle_apply_one, lowerTriangleMap_apply, h₀, h₁]

/-- Read on `Δ²`, the upper triangle of the square is the parametrization `y ↦ (y₀, y₀ + y₁)`. -/
private theorem squareUpperTriangle_fullSimplexEquivStdSimplex (y : fullSimplex 2) :
    (((squareUpperTriangle (fullSimplexEquivStdSimplex 2 y) 0 : ℝ),
      (squareUpperTriangle (fullSimplexEquivStdSimplex 2 y) 1 : ℝ))) = upperTriangleMap y := by
  have h₀ := fullSimplexEquivStdSimplex_weights_succ y 0
  have h₁ := fullSimplexEquivStdSimplex_weights_succ y 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h₀ h₁
  rw [squareUpperTriangle_apply_zero, squareUpperTriangle_apply_one, upperTriangleMap_apply, h₀, h₁]

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

end IsSmoothSphere

/-- The constant singular `2`-simplex at a point is smooth. -/
private def constSimplex (x : M) : SmoothSimplex I M 2 :=
  ⟨((TopCat.of M).toSSetObjEquiv (.op ⦋2⦌)).symm (ContinuousMap.const _ x),
    mem_smoothSingularSubcomplex_of_contMDiffOn _ (g := fun _ ↦ x) contMDiffOn_const
      Filter.univ_mem fun _ ↦ rfl⟩

/-- Read on `Δ²`, the constant simplex at `x` is constant. -/
private theorem constSimplex_toContinuousMap_apply (x : M) (y : fullSimplex 2) :
    (constSimplex (I := I) x).toContinuousMap y = x := by
  rw [SmoothSimplex.toContinuousMap_apply]
  dsimp only [constSimplex]
  rw [Equiv.apply_symm_apply, ContinuousMap.const_apply]

/-- The integral of a two-form over a constant simplex vanishes. -/
private theorem integral_constSimplex (x : M) (φ : RoughForm I M F 2) :
    (constSimplex (I := I) x).integral φ = 0 := by
  rw [(constSimplex x).integral_eq_setIntegral_mpullback φ (g := fun _ ↦ x)
    (fun y ↦ (constSimplex_toContinuousMap_apply x y).symm) fun _ _ ↦ mdifferentiableAt_const]
  refine (setIntegral_congr_fun (g := fun _ ↦ (0 : F)) (isClosed_fullSimplex 2).measurableSet
    fun y _ ↦ ?_).trans (integral_zero _ _)
  refine (mpullback_apply (fun _ ↦ x) φ y _).trans ((φ x).map_coord_zero 0 ?_)
  rw [mfderiv_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (I' := I) (M := EuclideanSpace ℝ (Fin 2))]
  rfl

namespace IsSmoothSphere

variable {x : M} {v : ℝ × ℝ → M}

/-- The triangulated cycle of a smooth sphere `v`, as a smooth singular chain: the lower and upper
triangle simplices minus twice the constant simplex at `x`. -/
private def smoothSquareChain (hv : IsSmoothSphere I x v) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X 2 :=
  ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      hv.lowerSimplex).hom 1
    + ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      hv.upperSimplex).hom 1
    - 2 • ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (constSimplex x)).hom 1

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
    rfl
  rw [smoothSquareChain, map_sub, map_add, map_nsmul, h, h, h, GenLoop.squareChain_def]
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
    integrationCochain_ιChainComplex, integral_constSimplex, integral_triangleSimplex,
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
