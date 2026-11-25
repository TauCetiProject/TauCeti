/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.WeightedCircle.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Sphere.LinearIsometry
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Isometry
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# The weighted ellipsoid is an analytic three-sphere

For natural numbers `a`, `b` and a real number `ε`, the ellipsoid

`E = {z ∈ ℂ² | a |z₁|² + b |z₂|² = 2 ε}`

(`TauCeti.Toric.weightedEllipsoid a b ε`) is the level `ε` of the moment map
`μ(z) = (a |z₁|² + b |z₂|²) / 2` of the circle acting on `ℂ²` with weights `a` and `b`. This file
gives it its smooth structure as a regular level and identifies it with the unit sphere.

* **The smooth structure.** At a point `z` of `E` the differential of
  `z ↦ a |z₁|² + b |z₂|²` (`TauCeti.Toric.weightedNormSq a b`) sends `z` itself to
  `2 (a |z₁|² + b |z₂|²) = 4 ε`, so for `ε ≠ 0` the value `2 ε` is regular
  (`TauCeti.Toric.isRegularValue_weightedNormSq`). The regular-level
  atlas `TauCeti.regularLevelChartedSpace` then makes `E` an analytic three-manifold, modelled on
  `ℝ³`, and its inclusion into `ℂ²` is an analytic embedding
  (`TauCeti.Toric.isSmoothEmbedding_coe_weightedEllipsoid`). No positivity of the weights is
  needed for this, and for `ε < 0`, or for `a = b = 0`, the level is empty. The weighted
  rotations are restrictions of the polynomial map `(u, z) ↦ (u ^ a z₁, u ^ b z₂)`, so the
  circle acts jointly analytically on `E` (a `ContMDiffSMul` instance).
* **The unit sphere.** For positive weights and `ε > 0` the real rescaling

  `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)`

  carries `E` onto the unit sphere `S³` of `ℂ²` with its Euclidean norm, with inverse
  `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. Both maps are restrictions of linear maps of `ℂ²`,
  so they are analytic, and this is an analytic diffeomorphism
  `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph` from `E` to Mathlib's sphere
  `sphere (0 : EuclideanSpace ℂ (Fin 2)) 1`. Its real scalars commute with complex
  multiplication, so it intertwines the weighted circle action `(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` on
  `E` with the action of the same weights on `S³` by the linear isometries
  `TauCeti.Toric.euclideanWeightedRotation a b u`
  (`TauCeti.Toric.weightedEllipsoidSphereDiffeomorph_smul`).

So the reduced space `E / S¹` of the weighted oscillator is the quotient of the round three-sphere
by the circle acting with weights `a` and `b`. For `a = b = 1` this is the Hopf action.

## Main declarations

* `TauCeti.Toric.weightedNormSq a b`: the function `z ↦ a |z₁|² + b |z₂|²` on `ℂ²`.
* `TauCeti.Toric.isRegularValue_weightedNormSq`: `2 ε` is a regular value of
  `z ↦ a |z₁|² + b |z₂|²` for `ε ≠ 0`.
* The instances `ChartedSpace (Fin 3 → ℝ) (weightedEllipsoid a b ε)` and
  `IsManifold 𝓘(ℝ, Fin 3 → ℝ) ω (weightedEllipsoid a b ε)`, for `[NeZero ε]`.
* `TauCeti.Toric.isSmoothEmbedding_coe_weightedEllipsoid`: the ellipsoid is an analytically
  embedded submanifold of `ℂ²`.
* The instance `ContMDiffSMul (𝓡 1) 𝓘(ℝ, Fin 3 → ℝ) n Circle (weightedEllipsoid a b ε)`, for
  `[NeZero ε]` and every `n`: the weighted circle action on the ellipsoid is jointly analytic.
* `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph`: the diffeomorphism of the ellipsoid with the
  unit sphere of `ℂ²`.
* `TauCeti.Toric.euclideanWeightedRotation a b`: the circle acting on `ℂ²`, and so on `S³`, with
  weights `a` and `b`.
* `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph_smul`,
  `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph_symm_smul`: it is equivariant for the circle
  actions with weights `a` and `b`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Part IX (symplectic reduction of `ℂⁿ` by circle actions, and the ellipsoid as a sphere).
* Eugene Lerman and Susan Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230 (weighted projective spaces as
  symplectic quotients).
-/

public section

noncomputable section

open Set Metric Function Module
open scoped Manifold ContDiff

namespace TauCeti.Toric

variable {a b : ℕ} {ε : ℝ}

/-! ### The ellipsoid as a regular level -/

variable (a b) in
/-- The function `z ↦ a |z₁|² + b |z₂|²` on `ℂ²`, twice the moment map of the circle acting with
weights `a` and `b`. The ellipsoid `TauCeti.Toric.weightedEllipsoid a b ε` is its level `2 ε`. -/
def weightedNormSq (z : ℂ × ℂ) : ℝ :=
  a * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2

theorem weightedNormSq_apply (z : ℂ × ℂ) : weightedNormSq a b z = a * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 :=
  (rfl)

theorem mem_weightedEllipsoid_iff_weightedNormSq {z : ℂ × ℂ} :
    z ∈ weightedEllipsoid a b ε ↔ weightedNormSq a b z = 2 * ε := by
  rw [mem_weightedEllipsoid, weightedNormSq_apply]

variable (a b) in
/-- The function `z ↦ a |z₁|² + b |z₂|²` cutting out the ellipsoid is analytic. -/
theorem contDiff_weightedNormSq {n : ℕ∞ω} : ContDiff ℝ n (weightedNormSq a b) :=
  ((contDiff_norm_sq ℝ).comp contDiff_fst).const_smul (a : ℝ) |>.add
    (((contDiff_norm_sq ℝ).comp contDiff_snd).const_smul (b : ℝ))

/-- The differential of `z ↦ a |z₁|² + b |z₂|²` at `z` sends `v` to
`2 a ⟪z₁, v₁⟫ + 2 b ⟪z₂, v₂⟫`, for the real inner product of `ℂ`. -/
theorem fderiv_weightedNormSq_apply (z v : ℂ × ℂ) :
    fderiv ℝ (weightedNormSq a b) z v = 2 * a * inner ℝ z.1 v.1 + 2 * b * inner ℝ z.2 v.2 := by
  have h₁ := ((hasStrictFDerivAt_norm_sq z.1).hasFDerivAt.comp z hasFDerivAt_fst).const_mul
    (a : ℝ)
  have h₂ := ((hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z hasFDerivAt_snd).const_mul
    (b : ℝ)
  have h : HasFDerivAt (weightedNormSq a b) _ z := h₁.add h₂
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The ellipsoid is a regular level.** For `ε ≠ 0`, the value `2 ε` is a regular value of
`z ↦ a |z₁|² + b |z₂|²`: at a point `z` of the level the differential sends `z` to `4 ε`. -/
theorem isRegularValue_weightedNormSq (hε : ε ≠ 0) :
    IsRegularValue 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ) (weightedNormSq a b) (2 * ε) := by
  refine isRegularValue_iff.2 fun z hz ↦ ?_
  rw [isRegularPoint_iff_surjective_fderiv]
  intro t
  refine ⟨(t / (4 * ε)) • z, ?_⟩
  rw [map_smul, fderiv_weightedNormSq_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, smul_eq_mul]
  rw [weightedNormSq_apply] at hz
  field_simp
  linear_combination (2 * t) * hz

/-- The ellipsoid as a subtype of `ℂ²` is the level `2 ε` of `z ↦ a |z₁|² + b |z₂|²`, as a
homeomorphism which is the identity on points. -/
private def levelHomeomorph (a b : ℕ) (ε : ℝ) :
    weightedEllipsoid a b ε ≃ₜ {z : ℂ × ℂ // weightedNormSq a b z = 2 * ε} :=
  (Homeomorph.refl _).subtype fun _ ↦ mem_weightedEllipsoid_iff_weightedNormSq

/-- `levelHomeomorph` is the identity on points: it is the restriction of `Homeomorph.refl`. -/
@[simp]
private theorem coe_levelHomeomorph (x : weightedEllipsoid a b ε) :
    (levelHomeomorph a b ε x : ℂ × ℂ) = x :=
  rfl

/-- `z ↦ a |z₁|² + b |z₂|²` is `C^n` at every point of the level, in the form the regular-level
API takes. -/
private theorem contMDiffAt_weightedNormSq {n : ℕ∞ω} (z : ℂ × ℂ)
    (_ : weightedNormSq a b z = 2 * ε) :
    ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ) n (weightedNormSq a b) z :=
  (contDiff_weightedNormSq a b).contMDiff.contMDiffAt

/-- The regular level `2 ε` of `z ↦ a |z₁|² + b |z₂|²` has dimension `4 - 1 = 3`. -/
private theorem finrank_sub_finrank_weightedNormSq :
    finrank ℝ (ℂ × ℂ) - finrank ℝ ℝ = 3 := by
  simp [Complex.finrank_real_complex]

/-- The preferred atlas of the regular level. -/
private abbrev levelChartedSpace (a b : ℕ) (ε : ℝ) [NeZero ε] :
    ChartedSpace (Fin 3 → ℝ)
      {z : ℂ × ℂ // weightedNormSq a b z = 2 * ε} :=
  regularLevelChartedSpace contMDiffAt_weightedNormSq (isRegularValue_weightedNormSq (NeZero.ne ε))
    finrank_sub_finrank_weightedNormSq

private theorem isManifold_levelChartedSpace [NeZero ε] :
    letI := levelChartedSpace a b ε
    IsManifold 𝓘(ℝ, Fin 3 → ℝ) ω
      {z : ℂ × ℂ // weightedNormSq a b z = 2 * ε} :=
  isManifold_regularLevel (m := ω) (by simp) contMDiffAt_weightedNormSq
    (isRegularValue_weightedNormSq (NeZero.ne ε)) finrank_sub_finrank_weightedNormSq

/-- The ellipsoid `a |z₁|² + b |z₂|² = 2 ε`, for `ε ≠ 0`, with the atlas of the regular level of
`z ↦ a |z₁|² + b |z₂|²` (`TauCeti.regularLevelChartedSpace`), modelled on `ℝ³`. -/
instance [NeZero ε] : ChartedSpace (Fin 3 → ℝ) (weightedEllipsoid a b ε) :=
  -- The body of a public instance is exposed, so it cannot mention the private
  -- `levelChartedSpace`, `levelHomeomorph` and `contMDiffAt_weightedNormSq`; this is the same term.
  letI := regularLevelChartedSpace (n := 3)
    (fun _ _ ↦ (contDiff_weightedNormSq a b).contMDiff.contMDiffAt)
    (isRegularValue_weightedNormSq (NeZero.ne ε)) (by simp [Complex.finrank_real_complex])
  ((Homeomorph.refl (ℂ × ℂ)).subtype (p := (· ∈ weightedEllipsoid a b ε))
    (q := fun z ↦ weightedNormSq a b z = 2 * ε)
    fun _ ↦ mem_weightedEllipsoid_iff_weightedNormSq).pullbackChartedSpace

/-- **The ellipsoid is an analytic three-manifold** for `ε ≠ 0`. -/
instance [NeZero ε] : IsManifold 𝓘(ℝ, Fin 3 → ℝ) ω (weightedEllipsoid a b ε) :=
  letI := levelChartedSpace a b ε
  haveI := isManifold_levelChartedSpace (a := a) (b := b) (ε := ε)
  (levelHomeomorph a b ε).pullback_isManifold _ _

/-- **The ellipsoid is an analytically embedded submanifold** of `ℂ²`, for `ε ≠ 0`. -/
theorem isSmoothEmbedding_coe_weightedEllipsoid [NeZero ε] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin 3 → ℝ) 𝓘(ℝ, ℂ × ℂ) ω
      (Subtype.val : weightedEllipsoid a b ε → ℂ × ℂ) := by
  let := levelChartedSpace a b ε
  have := isManifold_levelChartedSpace (a := a) (b := b) (ε := ε)
  have hcoe : (Subtype.val : weightedEllipsoid a b ε → ℂ × ℂ) =
      Subtype.val ∘ (levelHomeomorph a b ε).pullbackDiffeomorph 𝓘(ℝ, Fin 3 → ℝ) ω := by
    funext x
    rw [Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph, coe_levelHomeomorph]
  rw [hcoe]
  exact isSmoothEmbedding_comp_diffeomorph _
    (isSmoothEmbedding_coe_regularLevel (m := ω) (by simp) contMDiffAt_weightedNormSq
      (isRegularValue_weightedNormSq (NeZero.ne ε)) finrank_sub_finrank_weightedNormSq)

/-- The inclusion of the ellipsoid into `ℂ²` is analytic. -/
theorem contMDiff_coe_weightedEllipsoid [NeZero ε] {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin 3 → ℝ) 𝓘(ℝ, ℂ × ℂ) n (Subtype.val : weightedEllipsoid a b ε → ℂ × ℂ) :=
  isSmoothEmbedding_coe_weightedEllipsoid.contMDiff.of_le le_top

/-- A map into the ellipsoid is `C^n` exactly when it is `C^n` as a map into `ℂ²`. -/
theorem contMDiff_weightedEllipsoid_iff [NeZero ε] {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → weightedEllipsoid a b ε} {n : ℕ∞ω} :
    ContMDiff I 𝓘(ℝ, Fin 3 → ℝ) n f ↔ ContMDiff I 𝓘(ℝ, ℂ × ℂ) n (Subtype.val ∘ f) :=
  (isSmoothEmbedding_coe_weightedEllipsoid.of_le le_top).contMDiff_iff_comp

/-! ### The smooth circle action -/

attribute [local instance] finrank_real_complex_fact'

/-- **The circle acts analytically on the ellipsoid**, for `ε ≠ 0`: the weighted rotations
`(u, z) ↦ (u ^ a z₁, u ^ b z₂)` form a jointly `C^n` action `Circle × E → E`, for every `n`. -/
instance [NeZero ε] {n : ℕ∞ω} :
    ContMDiffSMul (𝓡 1) 𝓘(ℝ, Fin 3 → ℝ) n Circle (weightedEllipsoid a b ε) where
  contMDiff_smul := by
    have hrot : (Subtype.val ∘ fun p : Circle × weightedEllipsoid a b ε ↦ p.1 • p.2) =
        fun p ↦ ((p.1 : ℂ) ^ a * (p.2 : ℂ × ℂ).1, (p.1 : ℂ) ^ b * (p.2 : ℂ × ℂ).2) :=
      funext fun p ↦ by
        rw [Function.comp_apply, coe_smul_weightedEllipsoid]
        exact Prod.ext (weightedRotation_fst _ _) (weightedRotation_snd _ _)
    have hu : ContMDiff ((𝓡 1).prod 𝓘(ℝ, Fin 3 → ℝ)) 𝓘(ℝ, ℂ) n
        fun p : Circle × weightedEllipsoid a b ε ↦ (p.1 : ℂ) :=
      contMDiff_coe_sphere.comp contMDiff_fst
    have hz : ContMDiff ((𝓡 1).prod 𝓘(ℝ, Fin 3 → ℝ)) 𝓘(ℝ, ℂ × ℂ) n
        fun p : Circle × weightedEllipsoid a b ε ↦ (p.2 : ℂ × ℂ) :=
      contMDiff_coe_weightedEllipsoid.comp contMDiff_snd
    have hmul : ContDiff ℝ n fun q : ℂ × (ℂ × ℂ) ↦ (q.1 ^ a * q.2.1, q.1 ^ b * q.2.2) :=
      ((contDiff_fst.pow a).mul (contDiff_fst.comp contDiff_snd)).prodMk
        ((contDiff_fst.pow b).mul (contDiff_snd.comp contDiff_snd))
    rw [contMDiff_weightedEllipsoid_iff, hrot]
    exact hmul.comp_contMDiff (hu.prodMk_space hz)

/-! ### The diffeomorphism with the unit sphere -/

/-- The real rescaling `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)` of `ℂ²`, with values in
`ℂ²` with its Euclidean norm. It carries the ellipsoid onto the unit sphere. -/
def weightedEllipsoidToSphere (a b : ℕ) (ε : ℝ) : ℂ × ℂ →L[ℝ] EuclideanSpace ℂ (Fin 2) :=
  ((EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    (ContinuousLinearMap.pi fun i ↦ ![(√(a / (2 * ε)) : ℂ) • ContinuousLinearMap.fst ℝ ℂ ℂ,
      (√(b / (2 * ε)) : ℂ) • ContinuousLinearMap.snd ℝ ℂ ℂ] i)

@[simp]
theorem weightedEllipsoidToSphere_apply_zero (z : ℂ × ℂ) :
    weightedEllipsoidToSphere a b ε z 0 = (√(a / (2 * ε)) : ℂ) * z.1 :=
  (rfl)

@[simp]
theorem weightedEllipsoidToSphere_apply_one (z : ℂ × ℂ) :
    weightedEllipsoidToSphere a b ε z 1 = (√(b / (2 * ε)) : ℂ) * z.2 :=
  (rfl)

/-- The inverse rescaling `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)` from `ℂ²` with its
Euclidean norm. It carries the unit sphere onto the ellipsoid. -/
def sphereToWeightedEllipsoid (a b : ℕ) (ε : ℝ) : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℂ × ℂ :=
  (((√(2 * ε / a) : ℂ) • EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).restrictScalars ℝ).prod
    (((√(2 * ε / b) : ℂ) • EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).restrictScalars ℝ)

@[simp]
theorem sphereToWeightedEllipsoid_apply (w : EuclideanSpace ℂ (Fin 2)) :
    sphereToWeightedEllipsoid a b ε w = ((√(2 * ε / a) : ℂ) * w 0, (√(2 * ε / b) : ℂ) * w 1) :=
  (rfl)

theorem weightedEllipsoidToSphere_mem_sphere (hε : 0 < ε) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) : weightedEllipsoidToSphere a b ε z ∈ sphere 0 1 := by
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [weightedEllipsoidToSphere_apply_zero, weightedEllipsoidToSphere_apply_one,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a / (2 * ε)),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ b / (2 * ε))]
  rw [mem_weightedEllipsoid] at hz
  field_simp
  linarith

theorem sphereToWeightedEllipsoid_mem_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    {w : EuclideanSpace ℂ (Fin 2)} (hw : w ∈ sphere 0 1) :
    sphereToWeightedEllipsoid a b ε w ∈ weightedEllipsoid a b ε := by
  have hw' : ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 = 1 := by
    rw [← Fin.sum_univ_two (fun i ↦ ‖w i‖ ^ 2), ← EuclideanSpace.norm_sq_eq,
      mem_sphere_zero_iff_norm.1 hw, one_pow]
  have ha' : (a : ℝ) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by positivity
  simp only [mem_weightedEllipsoid, sphereToWeightedEllipsoid_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε / a),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε / b)]
  field_simp
  linear_combination hw'

/-- `√(c / (2 ε)) √(2 ε / c) = 1` for `c > 0` and `ε > 0`, as complex numbers. -/
private theorem sqrt_div_mul_sqrt_div (c : ℕ) (hc : 0 < c) (hε : 0 < ε) :
    (√(c / (2 * ε)) : ℂ) * √(2 * ε / c) = 1 ∧ (√(2 * ε / c) : ℂ) * √(c / (2 * ε)) = 1 := by
  have h : √(c / (2 * ε)) * √(2 * ε / c) = 1 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (c : ℝ),
      div_self (by positivity), Real.sqrt_one]
  exact ⟨by exact_mod_cast h, by rw [mul_comm]; exact_mod_cast h⟩

theorem sphereToWeightedEllipsoid_weightedEllipsoidToSphere (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (z : ℂ × ℂ) :
    sphereToWeightedEllipsoid a b ε (weightedEllipsoidToSphere a b ε z) = z := by
  rw [sphereToWeightedEllipsoid_apply, weightedEllipsoidToSphere_apply_zero,
    weightedEllipsoidToSphere_apply_one, ← mul_assoc, ← mul_assoc,
    (sqrt_div_mul_sqrt_div a ha hε).2, (sqrt_div_mul_sqrt_div b hb hε).2, one_mul, one_mul]

theorem weightedEllipsoidToSphere_sphereToWeightedEllipsoid (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (w : EuclideanSpace ℂ (Fin 2)) :
    weightedEllipsoidToSphere a b ε (sphereToWeightedEllipsoid a b ε w) = w := by
  ext i
  fin_cases i <;> dsimp only [Fin.zero_eta, Fin.mk_one]
  · rw [weightedEllipsoidToSphere_apply_zero, sphereToWeightedEllipsoid_apply, ← mul_assoc,
      (sqrt_div_mul_sqrt_div a ha hε).1, one_mul]
  · rw [weightedEllipsoidToSphere_apply_one, sphereToWeightedEllipsoid_apply, ← mul_assoc,
      (sqrt_div_mul_sqrt_div b hb hε).1, one_mul]

/-- The unit sphere `S³` of `ℂ²`, in the form in which Mathlib's analytic structure models it on
`ℝ³`. -/
local notation "S³" => sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

/-- **The weighted ellipsoid is the unit three-sphere.** For positive weights and `ε > 0`, the
rescaling `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)` is an analytic diffeomorphism from the
ellipsoid `a |z₁|² + b |z₂|² = 2 ε`, with its regular-level structure, to the unit sphere of `ℂ²`.
Its inverse is `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. -/
def weightedEllipsoidSphereDiffeomorph (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) [NeZero ε] :
    weightedEllipsoid a b ε ≃ₘ^ω⟮𝓘(ℝ, Fin 3 → ℝ), 𝓡 3⟯ S³ where
  toFun z := ⟨weightedEllipsoidToSphere a b ε z, weightedEllipsoidToSphere_mem_sphere hε z.property⟩
  invFun w :=
    ⟨sphereToWeightedEllipsoid a b ε w,
      sphereToWeightedEllipsoid_mem_weightedEllipsoid ha hb hε w.property⟩
  left_inv z := Subtype.ext (sphereToWeightedEllipsoid_weightedEllipsoidToSphere ha hb hε z)
  right_inv w := Subtype.ext (weightedEllipsoidToSphere_sphereToWeightedEllipsoid ha hb hε w)
  contMDiff_toFun :=
    ((weightedEllipsoidToSphere a b ε).contDiff.contMDiff.comp
      contMDiff_coe_weightedEllipsoid).codRestrict_sphere _
  contMDiff_invFun := contMDiff_weightedEllipsoid_iff.2 <|
    (sphereToWeightedEllipsoid a b ε).contDiff.contMDiff.comp contMDiff_coe_sphere

@[simp]
theorem coe_weightedEllipsoidSphereDiffeomorph_apply (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    [NeZero ε] (z : weightedEllipsoid a b ε) :
    (weightedEllipsoidSphereDiffeomorph ha hb hε z : EuclideanSpace ℂ (Fin 2)) =
      weightedEllipsoidToSphere a b ε z :=
  (rfl)

@[simp]
theorem coe_weightedEllipsoidSphereDiffeomorph_symm_apply (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    [NeZero ε] (w : S³) :
    ((weightedEllipsoidSphereDiffeomorph ha hb hε).symm w : ℂ × ℂ) =
      sphereToWeightedEllipsoid a b ε w :=
  (rfl)

/-- The weighted rotation `(w₁, w₂) ↦ (u ^ a w₁, u ^ b w₂)` of `ℂ²` with its Euclidean norm, as a
homomorphism from the circle to the real linear isometries. Through
`LinearIsometryEquiv.instMulActionUnitSphere` it acts on the unit sphere `S³`. -/
def euclideanWeightedRotation (a b : ℕ) :
    Circle →* (EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2)) where
  toFun u := LinearIsometryEquiv.piLpCongrRight 2 ![rotation (u ^ a), rotation (u ^ b)]
  map_one' := by ext w i; fin_cases i <;> simp
  map_mul' u v := by ext w i; fin_cases i <;> simp [mul_pow]

@[simp]
theorem euclideanWeightedRotation_apply_zero (u : Circle) (w : EuclideanSpace ℂ (Fin 2)) :
    euclideanWeightedRotation a b u w 0 = (u : ℂ) ^ a * w 0 := by
  simp [euclideanWeightedRotation, -map_pow]

@[simp]
theorem euclideanWeightedRotation_apply_one (u : Circle) (w : EuclideanSpace ℂ (Fin 2)) :
    euclideanWeightedRotation a b u w 1 = (u : ℂ) ^ b * w 1 := by
  simp [euclideanWeightedRotation, -map_pow]

/-- **The diffeomorphism with the unit sphere is equivariant.** It carries the weighted rotation
`(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` of the ellipsoid to the rotation of the sphere with the same
weights. -/
@[simp]
theorem weightedEllipsoidSphereDiffeomorph_smul (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    [NeZero ε] (u : Circle) (z : weightedEllipsoid a b ε) :
    weightedEllipsoidSphereDiffeomorph ha hb hε (u • z) =
      euclideanWeightedRotation a b u • weightedEllipsoidSphereDiffeomorph ha hb hε z := by
  ext i
  fin_cases i <;>
  simp [weightedRotation_fst, weightedRotation_snd, mul_left_comm]

/-- The inverse of the diffeomorphism with the unit sphere is equivariant. -/
@[simp]
theorem weightedEllipsoidSphereDiffeomorph_symm_smul (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    [NeZero ε] (u : Circle) (w : S³) :
    (weightedEllipsoidSphereDiffeomorph ha hb hε).symm (euclideanWeightedRotation a b u • w) =
      u • (weightedEllipsoidSphereDiffeomorph ha hb hε).symm w := by
  conv_lhs => rw [← (weightedEllipsoidSphereDiffeomorph ha hb hε).apply_symm_apply w]
  rw [← weightedEllipsoidSphereDiffeomorph_smul, Diffeomorph.symm_apply_apply]

end TauCeti.Toric
