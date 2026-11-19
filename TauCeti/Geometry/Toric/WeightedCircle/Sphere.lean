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
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic

/-!
# The weighted ellipsoid is an analytic three-sphere

For natural numbers `a`, `b` and a real number `ε`, the ellipsoid

`E = {z ∈ ℂ² | a |z₁|² + b |z₂|² = 2 ε}`

(`TauCeti.Toric.weightedEllipsoid a b ε`) is the level `ε` of the moment map
`μ(z) = (a |z₁|² + b |z₂|²) / 2` of the circle acting on `ℂ²` with weights `a` and `b`. This file
gives it its smooth structure as a regular level and identifies it with the unit sphere.

* **The smooth structure.** At a point `z` of `E` the differential of
  `z ↦ a |z₁|² + b |z₂|²` sends `z` itself to `2 (a |z₁|² + b |z₂|²) = 4 ε`, so for `ε ≠ 0` the
  value `2 ε` is regular (`TauCeti.Toric.isRegularValue_weightedEllipsoid`). The regular-level
  atlas `TauCeti.regularLevelChartedSpace` then makes `E` an analytic three-manifold, modelled on
  `ℝ³`, and its inclusion into `ℂ²` is an analytic embedding
  (`TauCeti.Toric.isSmoothEmbedding_coe_weightedEllipsoid`). No positivity of the weights is
  needed for this, and for `ε < 0`, or for `a = b = 0`, the level is empty.
* **The unit sphere.** For positive weights and `ε > 0` the real rescaling

  `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)`

  carries `E` onto the unit sphere `S³` of `ℂ²` with its Euclidean norm, with inverse
  `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. Both maps are restrictions of linear maps of `ℂ²`,
  so they are analytic, and this is an analytic diffeomorphism
  `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph` from `E` to Mathlib's sphere
  `sphere (0 : EuclideanSpace ℂ (Fin 2)) 1`. Its real scalars commute with complex
  multiplication, so it intertwines the weighted circle action `(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` on
  `E` with the action of the same weights on `S³`
  (`TauCeti.Toric.weightedEllipsoidSphereDiffeomorph_smul_apply`).

So the reduced space `E / S¹` of the weighted oscillator is the quotient of the round three-sphere
by the circle acting with weights `a` and `b`. For `a = b = 1` this is the Hopf action.

## Main declarations

* `TauCeti.Toric.isRegularValue_weightedEllipsoid`: `2 ε` is a regular value of
  `z ↦ a |z₁|² + b |z₂|²` for `ε ≠ 0`.
* The instances `ChartedSpace (Fin 3 → ℝ) (weightedEllipsoid a b ε)` and
  `IsManifold 𝓘(ℝ, Fin 3 → ℝ) ω (weightedEllipsoid a b ε)`, for `[NeZero ε]`.
* `TauCeti.Toric.isSmoothEmbedding_coe_weightedEllipsoid`: the ellipsoid is an analytically
  embedded submanifold of `ℂ²`.
* `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph`: the diffeomorphism of the ellipsoid with the
  unit sphere of `ℂ²`.
* `TauCeti.Toric.weightedEllipsoidSphereDiffeomorph_smul_apply`: it is equivariant for the circle
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
/-- The function `z ↦ a |z₁|² + b |z₂|²` cutting out the ellipsoid is analytic. -/
theorem contDiff_weightedEllipsoid {n : ℕ∞ω} :
    ContDiff ℝ n fun z : ℂ × ℂ ↦ (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 :=
  ((contDiff_norm_sq ℝ).comp contDiff_fst).const_smul (a : ℝ) |>.add
    (((contDiff_norm_sq ℝ).comp contDiff_snd).const_smul (b : ℝ))

/-- The differential of `z ↦ a |z₁|² + b |z₂|²` at `z` sends `v` to
`2 a ⟪z₁, v₁⟫ + 2 b ⟪z₂, v₂⟫`, for the real inner product of `ℂ`. -/
theorem fderiv_weightedEllipsoid_apply (z v : ℂ × ℂ) :
    fderiv ℝ (fun z : ℂ × ℂ ↦ (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2) z v =
      2 * a * inner ℝ z.1 v.1 + 2 * b * inner ℝ z.2 v.2 := by
  have h₁ := ((hasStrictFDerivAt_norm_sq z.1).hasFDerivAt.comp z hasFDerivAt_fst).const_mul
    (a : ℝ)
  have h₂ := ((hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z hasFDerivAt_snd).const_mul
    (b : ℝ)
  have h : HasFDerivAt (fun z : ℂ × ℂ ↦ (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2) _ z := h₁.add h₂
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The ellipsoid is a regular level.** For `ε ≠ 0`, the value `2 ε` is a regular value of
`z ↦ a |z₁|² + b |z₂|²`: at a point `z` of the level the differential sends `z` to `4 ε`. -/
theorem isRegularValue_weightedEllipsoid (hε : ε ≠ 0) :
    IsRegularValue 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ)
      (fun z : ℂ × ℂ ↦ (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2) (2 * ε) := by
  refine isRegularValue_iff.2 fun z hz ↦ ?_
  rw [isRegularPoint_iff_surjective_fderiv]
  intro t
  refine ⟨(t / (4 * ε)) • z, ?_⟩
  rw [map_smul, fderiv_weightedEllipsoid_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, smul_eq_mul]
  field_simp
  linear_combination (2 * t) * hz

/-- The ellipsoid as a subtype of `ℂ²` is the level `2 ε` of `z ↦ a |z₁|² + b |z₂|²`, as a
homeomorphism which is the identity on points. -/
private def levelHomeomorph (a b : ℕ) (ε : ℝ) :
    weightedEllipsoid a b ε ≃ₜ {z : ℂ × ℂ // (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε} :=
  (Homeomorph.refl _).subtype fun _ ↦ mem_weightedEllipsoid

/-- The regular level `2 ε` of `z ↦ a |z₁|² + b |z₂|²` has dimension `4 - 1 = 3`. -/
private theorem finrank_sub_finrank_weightedEllipsoid :
    finrank ℝ (ℂ × ℂ) - finrank ℝ ℝ = 3 := by
  simp [Complex.finrank_real_complex]

/-- The preferred atlas of the regular level. -/
private abbrev levelChartedSpace (a b : ℕ) (ε : ℝ) [NeZero ε] :
    ChartedSpace (Fin 3 → ℝ)
      {z : ℂ × ℂ // (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε} :=
  regularLevelChartedSpace (fun _ _ ↦ (contDiff_weightedEllipsoid a b).contMDiff.contMDiffAt)
    (isRegularValue_weightedEllipsoid (NeZero.ne ε)) finrank_sub_finrank_weightedEllipsoid

private theorem isManifold_levelChartedSpace [NeZero ε] :
    letI := levelChartedSpace a b ε
    IsManifold 𝓘(ℝ, Fin 3 → ℝ) ω
      {z : ℂ × ℂ // (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε} :=
  isManifold_regularLevel (m := ω) (by simp)
    (fun _ _ ↦ (contDiff_weightedEllipsoid a b).contMDiff.contMDiffAt)
    (isRegularValue_weightedEllipsoid (NeZero.ne ε)) finrank_sub_finrank_weightedEllipsoid

/-- The ellipsoid `a |z₁|² + b |z₂|² = 2 ε`, for `ε ≠ 0`, with the atlas of the regular level of
`z ↦ a |z₁|² + b |z₂|²` (`TauCeti.regularLevelChartedSpace`), modelled on `ℝ³`. -/
instance [NeZero ε] : ChartedSpace (Fin 3 → ℝ) (weightedEllipsoid a b ε) :=
  -- The body of a public instance is exposed, so it cannot mention the private
  -- `levelChartedSpace` and `levelHomeomorph`; this is the same term.
  letI := regularLevelChartedSpace (n := 3)
    (fun _ _ ↦ (contDiff_weightedEllipsoid a b).contMDiff.contMDiffAt)
    (isRegularValue_weightedEllipsoid (NeZero.ne ε)) (by simp [Complex.finrank_real_complex])
  ((Homeomorph.refl (ℂ × ℂ)).subtype (p := (· ∈ weightedEllipsoid a b ε))
    (q := fun z ↦ (a : ℝ) * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2 = 2 * ε)
    fun _ ↦ mem_weightedEllipsoid).pullbackChartedSpace

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
    rw [Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph]
    rfl
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  rw [hcoe]
  exact (isImmersionOfComplement_comp_diffeomorph _
    (isImmersionOfComplement_coe_regularLevel (m := ω) (by simp)
      (fun _ _ ↦ (contDiff_weightedEllipsoid a b).contMDiff.contMDiffAt)
      (isRegularValue_weightedEllipsoid (NeZero.ne ε))
      finrank_sub_finrank_weightedEllipsoid)).isImmersion

/-- The inclusion of the ellipsoid into `ℂ²` is analytic. -/
theorem contMDiff_coe_weightedEllipsoid [NeZero ε] {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin 3 → ℝ) 𝓘(ℝ, ℂ × ℂ) n (Subtype.val : weightedEllipsoid a b ε → ℂ × ℂ) :=
  isSmoothEmbedding_coe_weightedEllipsoid.contMDiff.of_le le_top

/-- A map into the ellipsoid is `C^n` exactly when it is `C^n` as a map into `ℂ²`. -/
theorem contMDiff_weightedEllipsoid_iff [NeZero ε] {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → weightedEllipsoid a b ε} :
    ContMDiff I 𝓘(ℝ, Fin 3 → ℝ) ω f ↔ ContMDiff I 𝓘(ℝ, ℂ × ℂ) ω (Subtype.val ∘ f) :=
  isSmoothEmbedding_coe_weightedEllipsoid.contMDiff_iff_comp

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

/-- The squared norm of a vector of `ℂ²` with its Euclidean norm. -/
private theorem norm_sq_euclideanSpace_fin_two (w : EuclideanSpace ℂ (Fin 2)) :
    ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

theorem weightedEllipsoidToSphere_mem_sphere (hε : 0 < ε) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) : weightedEllipsoidToSphere a b ε z ∈ sphere 0 1 := by
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    norm_sq_euclideanSpace_fin_two, weightedEllipsoidToSphere_apply_zero,
    weightedEllipsoidToSphere_apply_one, norm_mul, norm_mul, mul_pow, mul_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a / (2 * ε)),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ b / (2 * ε))]
  rw [mem_weightedEllipsoid] at hz
  field_simp
  linarith

theorem sphereToWeightedEllipsoid_mem_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    {w : EuclideanSpace ℂ (Fin 2)} (hw : w ∈ sphere 0 1) :
    sphereToWeightedEllipsoid a b ε w ∈ weightedEllipsoid a b ε := by
  have hw' : ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 = 1 := by
    rw [← norm_sq_euclideanSpace_fin_two, mem_sphere_zero_iff_norm.1 hw, one_pow]
  have ha' : (a : ℝ) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by positivity
  rw [mem_weightedEllipsoid, sphereToWeightedEllipsoid_apply, norm_mul, norm_mul, mul_pow,
    mul_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε / a),
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
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
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
  toFun z := ⟨weightedEllipsoidToSphere a b ε z, weightedEllipsoidToSphere_mem_sphere hε z.2⟩
  invFun w :=
    ⟨sphereToWeightedEllipsoid a b ε w,
      sphereToWeightedEllipsoid_mem_weightedEllipsoid ha hb hε w.2⟩
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

/-- **The diffeomorphism with the unit sphere is equivariant.** It carries the weighted rotation
`(z₁, z₂) ↦ (u ^ a z₁, u ^ b z₂)` of the ellipsoid to the rotation of the sphere with the same
weights: coordinate `i` of the image is multiplied by `u ^ a` for `i = 0` and by `u ^ b` for
`i = 1`. -/
theorem weightedEllipsoidSphereDiffeomorph_smul_apply (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    [NeZero ε] (u : Circle) (z : weightedEllipsoid a b ε) (i : Fin 2) :
    (weightedEllipsoidSphereDiffeomorph ha hb hε (u • z) : EuclideanSpace ℂ (Fin 2)) i =
      (u : ℂ) ^ ![a, b] i * (weightedEllipsoidSphereDiffeomorph ha hb hε z :
        EuclideanSpace ℂ (Fin 2)) i := by
  fin_cases i <;>
  simp [weightedRotation_fst, weightedRotation_snd, mul_left_comm]

end TauCeti.Toric
