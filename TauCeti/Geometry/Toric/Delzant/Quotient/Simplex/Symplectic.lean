/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Quotient.Simplex.Basic
public import TauCeti.Geometry.Toric.Delzant.Quotient.Symplectic
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Symplectic
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Delzant quotient of the standard simplex is `(ℂPⁿ, 2π a ω_FS)`

Let `Δ_a ⊆ (ℝⁿ)*` be the standard simplex `{y | 0 ≤ y_k, ∑ k, y_k ≤ a}` of size `a > 0`, with
Delzant quotient `M_Δ = Z / S¹` (`TauCeti.Toric.DelzantQuotient`): the level `Z` is the sphere
`‖q‖² + ‖p‖² = 2a` of `ℂ^(Option (Fin n))` (`TauCeti.Toric.mem_delzantLevel_simplex_iff`) and the
kernel torus is the diagonal circle. `TauCeti.Toric.DelzantQuotient.simplexHomeomorph` identifies
`M_Δ` with the space of complex lines of `ℂⁿ⁺¹` as a topological space. This file identifies it with
complex projective space `ℂPⁿ` (`TauCeti.ComplexProjectiveSpace n`), the quotient of the unit
sphere `S²ⁿ⁺¹` by the circle, as a smooth manifold and as a symplectic manifold with its moment map.

* **The level.** Listing the complex coordinates `q_o + i p_o` of `ℂ^(Option (Fin n))` as
  homogeneous coordinates of `ℂⁿ⁺¹`, with `none` first
  (`TauCeti.Toric.simplexHomogeneousCoord`), and dividing by `√(2a)` identifies the level `Z` with
  `S²ⁿ⁺¹` (`TauCeti.Toric.simplexLevelDiffeomorph`). These coordinates carry the standard symplectic
  form `Σ dq_o ∧ dp_o` to `Im ⟪·, ·⟫_ℂ`
  (`TauCeti.Toric.isSymplectomorphism_simplexHomogeneousCoord`).
* **The quotient.** Two points of `Z` have the same class in `M_Δ` exactly when their images in
  `S²ⁿ⁺¹` differ by a unit complex scalar
  (`TauCeti.Toric.DelzantQuotient.mk_eq_mk_iff_complexProjectiveSpaceMk_eq`). As the projections
  `Z → M_Δ` and `S²ⁿ⁺¹ → ℂPⁿ` are surjective submersions, the induced bijection
  `[z] ↦ [z / √(2a)]` is a diffeomorphism `M_Δ ≃ ℂPⁿ`
  (`TauCeti.Toric.DelzantQuotient.simplexDiffeomorph`).
* **The symplectic form.** The Fubini–Study form `ω_FS` pulls back to `S²ⁿ⁺¹` as `1 / π` times the
  restriction of `Im ⟪·, ·⟫_ℂ`, and the reduced form `ω_Δ` pulls back to `Z` as the restriction of
  `Σ dq_o ∧ dp_o`. Rescaling by `1 / √(2a)` multiplies the latter by `1 / (2a)`, so
  `simplexDiffeomorph` pulls `2π a ω_FS` back to `ω_Δ`
  (`TauCeti.Toric.DelzantQuotient.mpullback_simplexDiffeomorph_smul_fubiniStudyForm`): it is a
  symplectomorphism `(M_Δ, ω_Δ) ≃ (ℂPⁿ, 2π a ω_FS)`
  (`TauCeti.Toric.DelzantQuotient.isSymplectomorphism_simplexDiffeomorph`).
* **The moment map.** The reduced moment map of the residual torus sends the point of `ℂPⁿ` of a
  unit vector `w` to `(a |w_(k + 1)|²)_k`
  (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_simplexDiffeomorph_symm_mk_apply`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 29.1–29.4 (Delzant's construction and the example of `ℂPⁿ`).
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Complex (I)
open Metric Module Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

variable (n : ℕ) {a : ℝ}

/-- The complex coordinates `q_o + i p_o` of `ℂ^(Option (Fin n))`, listed as the homogeneous
coordinates of `ℂⁿ⁺¹`: the coordinate `none` comes first, and `some k` is in position `k + 1`. -/
def simplexHomogeneousCoord :
    (EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) ≃L[ℝ]
      EuclideanSpace ℂ (Fin (n + 1)) :=
  (complexEuclideanEquivRealProd (Option (Fin n))).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (finSuccEquiv n).symm).toContinuousLinearEquiv

variable {n}

/-- The homogeneous coordinate `k` of `(q, p)` is `q_o + i p_o` for the facet `o` listed in
position `k`. -/
@[simp]
theorem simplexHomogeneousCoord_apply
    (x : EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) (k : Fin (n + 1)) :
    simplexHomogeneousCoord n x k = x.1 (finSuccEquiv n k) + x.2 (finSuccEquiv n k) * I := by
  simp [simplexHomogeneousCoord]

/-- The `q`-coordinate of the facet `o` of a point `z` of `ℂⁿ⁺¹` is the real part of its
homogeneous coordinate in the position of `o`. -/
@[simp]
theorem simplexHomogeneousCoord_symm_apply_fst (z : EuclideanSpace ℂ (Fin (n + 1)))
    (o : Option (Fin n)) :
    ((simplexHomogeneousCoord n).symm z).1 o = (z ((finSuccEquiv n).symm o)).re  := by
  simp [simplexHomogeneousCoord]

/-- The `p`-coordinate of the facet `o` of a point `z` of `ℂⁿ⁺¹` is the imaginary part of its
homogeneous coordinate in the position of `o`. -/
@[simp]
theorem simplexHomogeneousCoord_symm_apply_snd (z : EuclideanSpace ℂ (Fin (n + 1)))
    (o : Option (Fin n)) :
    ((simplexHomogeneousCoord n).symm z).2 o = (z ((finSuccEquiv n).symm o)).im  := by
  simp [simplexHomogeneousCoord]

/-- The coordinates `simplexHomogeneousCoord` carry `‖q‖² + ‖p‖²` to the squared norm. -/
theorem norm_simplexHomogeneousCoord_sq
    (x : EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) :
    ‖simplexHomogeneousCoord n x‖ ^ 2 = ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := by
  rw [← norm_complexEuclideanEquivRealProd_symm_sq]
  simp [simplexHomogeneousCoord]

/-- On the level of the simplex of size `a`, the homogeneous coordinates have norm `√(2a)`. -/
theorem norm_simplexHomogeneousCoord_of_mem_delzantLevel
    {x : EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))}
    (hx : x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) :
    ‖simplexHomogeneousCoord n x‖ = √(2 * a) := by
  rw [← mem_delzantLevel_simplex_iff.1 hx, ← norm_simplexHomogeneousCoord_sq,
    Real.sqrt_sq (norm_nonneg _)]

/-- **The homogeneous coordinates are symplectic**: they carry the standard symplectic form
`Σ dq_o ∧ dp_o` of `ℂ^(Option (Fin n))` to the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹`. -/
theorem isSymplectomorphism_simplexHomogeneousCoord :
    SymplecticForm.IsSymplectomorphism stdSymplecticForm
      (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1))))
      (simplexHomogeneousCoord n).toLinearEquiv := by
  refine SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ ?_
  rw [← isSymplectomorphism_complexEuclideanEquivRealProd_symm.apply u w,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv]
  rw [imInnerSymplecticForm_apply, imInnerSymplecticForm_apply, PiLp.inner_apply,
    PiLp.inner_apply]
  -- Relabelling the homogeneous coordinates along `finSuccEquiv` does not change the sum.
  refine congrArg Complex.im (Fintype.sum_equiv (finSuccEquiv n) _ _ fun k ↦ ?_)
  rw [simplexHomogeneousCoord_apply, simplexHomogeneousCoord_apply]
  simp only [complexEuclideanEquivRealProd_symm_apply]

variable (n) in
/-- The homogeneous coordinates divided by `√(2a)`, as a real-linear map. -/
private def scaledHomogeneousCoord (a : ℝ) :
    (EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) →L[ℝ]
      EuclideanSpace ℂ (Fin (n + 1)) :=
  (√(2 * a))⁻¹ • (simplexHomogeneousCoord n :
    (EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) →L[ℝ]
      EuclideanSpace ℂ (Fin (n + 1)))

/-- `scaledHomogeneousCoord` divides the homogeneous coordinates by `√(2a)`. -/
private theorem scaledHomogeneousCoord_apply
    (x : EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) :
    scaledHomogeneousCoord n a x = (√(2 * a))⁻¹ • simplexHomogeneousCoord n x :=
  (rfl)

/-- Pulled back along the homogeneous coordinates divided by `√(2a)`, the constant form
`Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹` is `1 / (2a)` times the standard symplectic form of `ℂ^(Option (Fin n))`. -/
private theorem mpullback_scaledHomogeneousCoord_imInnerSymplecticForm (ha : 0 < a) :
    SmoothForm.mpullback (scaledHomogeneousCoord n a)
        (scaledHomogeneousCoord n a).contDiff.contMDiff
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth =
      (2 * a)⁻¹ • stdSymplecticForm.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, ContinuousLinearMap.mfderiv_eq,
    SymplecticForm.fromTangentSpace_constSmooth_apply, SmoothForm.eval₂_smul,
    SymplecticForm.fromTangentSpace_constSmooth_apply]
  simp only [NormedSpace.fromTangentSpace_apply, smul_eq_mul]
  -- The tangent vectors are vectors of the model spaces, where the computation takes place.
  have key (v w : EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) :
      imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1))) (scaledHomogeneousCoord n a v)
          (scaledHomogeneousCoord n a w) = (2 * a)⁻¹ * stdSymplecticForm v w := by
    have h := isSymplectomorphism_simplexHomogeneousCoord.apply v w
    rw [scaledHomogeneousCoord_apply, scaledHomogeneousCoord_apply]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at h ⊢
    rw [h, ← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt (by positivity)]
  exact key v w

/-- A point of the level of the simplex of size `a > 0`, rescaled by `1 / √(2a)`, is a unit vector
in the homogeneous coordinates. -/
private theorem smul_simplexHomogeneousCoord_mem_sphere (ha : 0 < a)
    (x : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) :
    (√(2 * a))⁻¹ • simplexHomogeneousCoord n x ∈ sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := by
  have hr : 0 < √(2 * a) := Real.sqrt_pos.2 (by positivity)
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_simplexHomogeneousCoord_of_mem_delzantLevel
    x.property, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']

/-- A unit vector of `ℂⁿ⁺¹`, rescaled by `√(2a)` and read in the coordinates of
`ℂ^(Option (Fin n))`, lies on the level of the simplex of size `a > 0`. -/
private theorem symm_simplexHomogeneousCoord_smul_mem_delzantLevel (ha : 0 < a)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (simplexHomogeneousCoord n).symm (√(2 * a) • (w : EuclideanSpace ℂ (Fin (n + 1)))) ∈
      delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
        (simplexSupport a) := by
  have hr : 0 < √(2 * a) := Real.sqrt_pos.2 (by positivity)
  rw [mem_delzantLevel_simplex_iff, ← norm_simplexHomogeneousCoord_sq,
    ContinuousLinearEquiv.apply_symm_apply, norm_smul, norm_eq_of_mem_sphere w, mul_one,
    Real.norm_eq_abs, abs_of_pos hr, Real.sq_sqrt (by positivity)]

variable [NeZero n]

/-- Rescaling the level of the simplex to the unit sphere is smooth. -/
private theorem contMDiff_simplexLevelToSphere (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    ContMDiff 𝓘(ℝ, Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ)
      (𝓡 (2 * n + 1)) ∞
      (fun x : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
          (simplexSupport a) ↦
        (⟨(√(2 * a))⁻¹ • simplexHomogeneousCoord n x,
          smul_simplexHomogeneousCoord_mem_sphere ha x⟩ :
            sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)) := by
  let _ := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  have := (isDelzant_simplex ha).isManifold_delzantLevel (isIntegralLattice_intCast n) ∞
  have h : ContMDiff 𝓘(ℝ, Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ)
      𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (fun x : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
          (simplexSupport a) ↦ (√(2 * a))⁻¹ • simplexHomogeneousCoord n x) :=
    (scaledHomogeneousCoord n a).contDiff.contMDiff.comp
      ((isDelzant_simplex ha).contMDiff_coe_delzantLevel (isIntegralLattice_intCast n))
  exact h.codRestrict_sphere (smul_simplexHomogeneousCoord_mem_sphere ha)

/-- Rescaling the unit sphere to the level of the simplex is smooth. -/
private theorem contMDiff_sphereToSimplexLevel (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    ContMDiff (𝓡 (2 * n + 1))
      𝓘(ℝ, Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ) ∞
      (fun w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
        (⟨_, symm_simplexHomogeneousCoord_smul_mem_delzantLevel ha w⟩ :
          delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
            (simplexSupport a))) := by
  have h : ContMDiff (𝓡 (2 * n + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) ∞
      (fun w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
        (simplexHomogeneousCoord n).symm (√(2 * a) • (w : EuclideanSpace ℂ (Fin (n + 1))))) :=
    ((simplexHomogeneousCoord n).symm.contDiff.comp
      (contDiff_id.const_smul (√(2 * a)))).contMDiff.comp contMDiff_coe_sphere
  exact (isDelzant_simplex ha).contMDiff_codRestrict_delzantLevel (isIntegralLattice_intCast n) h
    (symm_simplexHomogeneousCoord_smul_mem_delzantLevel ha)

variable (n) in
/-- **The level of the simplex is a sphere.** For `a > 0`, the level of the simplex of size `a`,
the sphere `‖q‖² + ‖p‖² = 2a` of `ℂ^(Option (Fin n))`, is diffeomorphic to the unit sphere
`S²ⁿ⁺¹` of `ℂⁿ⁺¹` by `z ↦ z / √(2a)`, read in the homogeneous coordinates
`simplexHomogeneousCoord`. -/
def simplexLevelDiffeomorph (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
        (simplexSupport a) ≃ₘ⟮
      𝓘(ℝ, Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ), 𝓡 (2 * n + 1)⟯
      sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  have hr : √(2 * a) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  { toFun x := ⟨_, smul_simplexHomogeneousCoord_mem_sphere ha x⟩
    invFun w := ⟨_, symm_simplexHomogeneousCoord_smul_mem_delzantLevel ha w⟩
    left_inv x := Subtype.ext <| by
      simp only [smul_inv_smul₀ hr, ContinuousLinearEquiv.symm_apply_apply]
    right_inv w := Subtype.ext <| by
      simp only [ContinuousLinearEquiv.apply_symm_apply, inv_smul_smul₀ hr]
    contMDiff_toFun := contMDiff_simplexLevelToSphere ha
    contMDiff_invFun := contMDiff_sphereToSimplexLevel ha }

/-- `simplexLevelDiffeomorph` divides the homogeneous coordinates by `√(2a)`. -/
@[simp]
theorem coe_simplexLevelDiffeomorph_apply (ha : 0 < a)
    (x : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    (simplexLevelDiffeomorph n ha x : EuclideanSpace ℂ (Fin (n + 1))) =
      (√(2 * a))⁻¹ • simplexHomogeneousCoord n x :=
  (rfl)

/-- The inverse of `simplexLevelDiffeomorph` multiplies a unit vector by `√(2a)`. -/
@[simp]
theorem coe_simplexLevelDiffeomorph_symm_apply (ha : 0 < a)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    ((simplexLevelDiffeomorph n ha).symm w :
        EuclideanSpace ℝ (Option (Fin n)) × EuclideanSpace ℝ (Option (Fin n))) =
      (simplexHomogeneousCoord n).symm (√(2 * a) • (w : EuclideanSpace ℂ (Fin (n + 1)))) :=
  (rfl)

namespace DelzantQuotient

/-- **The fibres of the two quotient maps agree.** Two points of the level of the simplex have the
same class in the Delzant quotient exactly when their images on the unit sphere `S²ⁿ⁺¹` have the
same image in `ℂPⁿ`, that is, when they differ by a unit complex scalar. -/
theorem mk_eq_mk_iff_complexProjectiveSpaceMk_eq (ha : 0 < a)
    (x y : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    mk x = mk y ↔ ComplexProjectiveSpace.mk n (simplexLevelDiffeomorph n ha x) =
      ComplexProjectiveSpace.mk n (simplexLevelDiffeomorph n ha y) := by
  let _ := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  have hr : 0 < √(2 * a) := Real.sqrt_pos.2 (by positivity)
  -- Both sides say that the complex coordinates of `x` are a scalar multiple of those of `y`.
  have hcoord (c : ℂ) : c • ⇑((complexEuclideanEquivRealProd (Option (Fin n))).symm y) =
      ⇑((complexEuclideanEquivRealProd (Option (Fin n))).symm x) ↔
      c • (simplexLevelDiffeomorph n ha y : EuclideanSpace ℂ (Fin (n + 1))) =
        simplexLevelDiffeomorph n ha x := by
    simp only [coe_simplexLevelDiffeomorph_apply, smul_comm c, funext_iff, Pi.smul_apply,
      smul_eq_mul]
    rw [(smul_right_injective _ (inv_ne_zero hr.ne')).eq_iff]
    constructor
    · intro h
      ext k
      simpa using h (finSuccEquiv n k)
    · intro h o
      simpa using congrArg (· ((finSuccEquiv n).symm o)) h
  rw [← (simplexHomeomorph (κ := Fin n) ha).injective.eq_iff, simplexHomeomorph_mk,
    simplexHomeomorph_mk, Projectivization.mk_eq_mk_iff', ComplexProjectiveSpace.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hc' := (hcoord c).1 hc
    have hnorm : ‖c‖ = 1 := by
      have h := congrArg norm hc'
      rwa [norm_smul, norm_eq_of_mem_sphere, norm_eq_of_mem_sphere, mul_one] at h
    exact ⟨⟨c, mem_sphere_zero_iff_norm.2 hnorm⟩, Subtype.ext hc'⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (hcoord c).2 (congrArg Subtype.val hc)⟩

variable (n) in
/-- **The Delzant quotient of the standard simplex is `ℂPⁿ` as a smooth manifold.** For `a > 0`,
the map `[z] ↦ [z / √(2a)]`, from the Delzant quotient of the simplex of size `a` in `ℝⁿ` to the
complex projective space `ℂPⁿ`, the quotient of the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` by the circle,
is a smooth diffeomorphism. The homogeneous coordinate `0` of `ℂPⁿ` corresponds to the facet
`∑ k, y_k ≤ a` of the simplex, and the coordinate `k + 1` to the facet `0 ≤ y_k`. -/
def simplexDiffeomorph (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
        (simplexSupport a) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n)))
        (Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ)),
      𝓘(ℝ, Fin n → ℂ)⟯ ComplexProjectiveSpace n :=
  letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  haveI := (isDelzant_simplex ha).isManifold_delzantLevel (isIntegralLattice_intCast n) ∞
  haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
  -- Both directions are smooth after composing with the projections from the level and from the
  -- sphere, which are surjective submersions.
  { toFun := lift (fun x ↦ ComplexProjectiveSpace.mk n (simplexLevelDiffeomorph n ha x))
      fun θ hθ x ↦ (mk_eq_mk_iff_complexProjectiveSpaceMk_eq ha _ _).1 (mk_vadd_of_mem_ker hθ x)
    invFun := ComplexProjectiveSpace.lift n (fun w ↦ mk ((simplexLevelDiffeomorph n ha).symm w))
      fun c w ↦ (mk_eq_mk_iff_complexProjectiveSpaceMk_eq ha _ _).2 (by simp)
    left_inv q := by
      induction q using DelzantQuotient.inductionOn with | h x => simp
    right_inv p := by
      induction p using ComplexProjectiveSpace.inductionOn with | h w => simp
    contMDiff_toFun :=
      (((isDelzant_simplex ha).isSubmersion_delzantQuotientMk
        (isIntegralLattice_intCast n)).contMDiff_comp_iff mk_surjective le_rfl).1 <| by
          convert (ComplexProjectiveSpace.contMDiff_mk ∞).comp
            (simplexLevelDiffeomorph n ha).contMDiff using 1
          exact funext fun x ↦ lift_mk _ _ x
    contMDiff_invFun :=
      ((ComplexProjectiveSpace.isSubmersion_mk ∞).contMDiff_comp_iff
        (ComplexProjectiveSpace.mk_surjective n) le_rfl).1 <| by
          convert ((isDelzant_simplex ha).isSubmersion_delzantQuotientMk
            (isIntegralLattice_intCast n)).contMDiff.comp
              (simplexLevelDiffeomorph n ha).symm.contMDiff using 1
          exact funext fun w ↦ ComplexProjectiveSpace.lift_mk _ _ _ w }

/-- `simplexDiffeomorph` sends the class of a point `z` of the level to the point of `ℂPⁿ` of the
unit vector `z / √(2a)`. -/
@[simp]
theorem simplexDiffeomorph_mk (ha : 0 < a)
    (x : delzantLevel ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    simplexDiffeomorph n ha (mk x) =
      ComplexProjectiveSpace.mk n (simplexLevelDiffeomorph n ha x) :=
  lift_mk _ _ x

/-- The inverse of `simplexDiffeomorph` sends the point of `ℂPⁿ` of a unit vector `w` to the class
of `√(2a) w`. -/
@[simp]
theorem simplexDiffeomorph_symm_mk (ha : 0 < a)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    letI := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    (simplexDiffeomorph n ha).symm (ComplexProjectiveSpace.mk n w) =
      mk ((simplexLevelDiffeomorph n ha).symm w) :=
  ComplexProjectiveSpace.lift_mk _ _ _ w

/-- **The Delzant quotient of the simplex of size `a` is `(ℂPⁿ, 2π a ω_FS)`.** The diffeomorphism
`simplexDiffeomorph` pulls `2π a` times the Fubini–Study form `ω_FS` of `ℂPⁿ`
(`TauCeti.ComplexProjectiveSpace.fubiniStudyForm`) back to the reduced symplectic form of the
Delzant quotient. -/
theorem mpullback_simplexDiffeomorph_smul_fubiniStudyForm (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
    SmoothForm.mpullback (simplexDiffeomorph n ha) (simplexDiffeomorph n ha).contMDiff
        ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm n) =
      (isDelzant_simplex ha).delzantQuotientSymplecticForm (isIntegralLattice_intCast n) := by
  let _ := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  have := (isDelzant_simplex ha).isManifold_delzantLevel (isIntegralLattice_intCast n) ∞
  have := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
  -- On the level, the rescaling to the unit sphere is the restriction of the scaled homogeneous
  -- coordinates.
  have hcomp : ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 →
      EuclideanSpace ℂ (Fin (n + 1))) ∘ simplexLevelDiffeomorph n ha =
      scaledHomogeneousCoord n a ∘ (↑) :=
    funext fun x ↦ (coe_simplexLevelDiffeomorph_apply ha x).trans
      (scaledHomogeneousCoord_apply _).symm
  -- Pulled back to the level along the rescaling and the Hopf projection, `ω_FS` is `1 / π` times
  -- `1 / (2a)` times the restriction of `Σ dq_o ∧ dp_o`.
  have hlevel : SmoothForm.mpullback (simplexLevelDiffeomorph n ha)
      (simplexLevelDiffeomorph n ha).contMDiff
        (SmoothForm.mpullback (ComplexProjectiveSpace.mk n) (ComplexProjectiveSpace.contMDiff_mk ∞)
          (ComplexProjectiveSpace.fubiniStudyForm n)) =
      π⁻¹ • (2 * a)⁻¹ • SmoothForm.mpullback _
        ((isDelzant_simplex ha).contMDiff_coe_delzantLevel (isIntegralLattice_intCast n))
          stdSymplecticForm.constSmooth := by
    rw [ComplexProjectiveSpace.mpullback_mk_fubiniStudyForm, SmoothForm.mpullback_smul,
      SmoothForm.mpullback_mpullback_of_comp_eq (simplexLevelDiffeomorph n ha).contMDiff
        contMDiff_coe_sphere
        ((isDelzant_simplex ha).contMDiff_coe_delzantLevel (isIntegralLattice_intCast n))
        (scaledHomogeneousCoord n a).contDiff.contMDiff hcomp,
      mpullback_scaledHomogeneousCoord_imInnerSymplecticForm ha, SmoothForm.mpullback_smul]
  -- Both forms are determined by their pullbacks to the level, where the projection followed by
  -- `simplexDiffeomorph` is the rescaling to the unit sphere followed by the Hopf projection.
  rw [(isDelzant_simplex ha).eq_delzantQuotientSymplecticForm_iff (isIntegralLattice_intCast n),
    SmoothForm.mpullback_mpullback_of_comp_eq
      ((isDelzant_simplex ha).isSubmersion_delzantQuotientMk
        (isIntegralLattice_intCast n)).contMDiff
      (simplexDiffeomorph n ha).contMDiff (simplexLevelDiffeomorph n ha).contMDiff
      (ComplexProjectiveSpace.contMDiff_mk ∞) (funext fun x ↦ simplexDiffeomorph_mk ha x),
    SmoothForm.mpullback_smul, SmoothForm.mpullback_smul, hlevel, smul_smul, smul_smul]
  convert one_smul ℝ _
  field_simp [ha.ne', Real.pi_ne_zero]

/-- **The Delzant quotient of the simplex of size `a` is symplectomorphic to `(ℂPⁿ, 2π a ω_FS)`**,
by `simplexDiffeomorph`. -/
theorem isSymplectomorphism_simplexDiffeomorph (ha : 0 < a) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
    SmoothTwoForm.IsSymplectomorphism
      ((isDelzant_simplex ha).delzantQuotientSymplecticForm (isIntegralLattice_intCast n))
      ((2 * π * a) • ComplexProjectiveSpace.fubiniStudyForm n) (simplexDiffeomorph n ha) :=
  letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
  SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2
    (mpullback_simplexDiffeomorph_smul_fubiniStudyForm ha)

/-- **The moment map of `ℂPⁿ`.** Under `simplexDiffeomorph`, the reduced moment map of the
residual torus sends the point of `ℂPⁿ` of a unit vector `w` to the covector with coordinates
`a |w_(k + 1)|²`. -/
theorem reducedMomentMap_simplexDiffeomorph_symm_mk_apply (ha : 0 < a)
    (w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (k : Fin n) :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    reducedMomentMap (i := (Int.castAddHom ℝ).compLeft (Fin n)) (u := simplexNormal (Fin n))
        (c := simplexSupport a) surjective_linearCombination_simplexNormal
        ((simplexDiffeomorph n ha).symm (ComplexProjectiveSpace.mk n w)) (Pi.single k 1) =
      a * ‖(w : EuclideanSpace ℂ (Fin (n + 1))) k.succ‖ ^ 2 := by
  let _ := (isDelzant_simplex ha).delzantLevelChartedSpace (isIntegralLattice_intCast n)
  let _ := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
  set x := (simplexLevelDiffeomorph n ha).symm w
  have hk := reducedMomentMap_mk_apply (i := (Int.castAddHom ℝ).compLeft (Fin n))
    (u := simplexNormal (Fin n)) surjective_linearCombination_simplexNormal x (some k)
  simp only [simplexNormal_some, AddMonoidHom.compLeft_single, Int.coe_castAddHom, Int.cast_one,
    simplexSupport_some, add_zero] at hk
  rw [simplexDiffeomorph_symm_mk, hk]
  -- The homogeneous coordinate `k + 1` of `x` is `√(2a) w_(k + 1)`.
  have hx := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) ↦ ‖v k.succ‖ ^ 2)
    ((simplexHomogeneousCoord n).apply_symm_apply (√(2 * a) • (w : EuclideanSpace ℂ (Fin (n + 1)))))
  simp only [simplexHomogeneousCoord_apply, finSuccEquiv_succ, PiLp.smul_apply,
    Complex.sq_norm, Complex.normSq_add_mul_I, norm_smul, mul_pow] at hx
  rw [coe_simplexLevelDiffeomorph_symm_apply ha w, hx, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), ← Complex.sq_norm]
  ring

end DelzantQuotient

end TauCeti.Toric
