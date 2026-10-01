/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# The special orthogonal group of the hyperbolic plane

The hyperbolic plane `hyperbolicPlane R`, the form `x₀² - x₁²` on `Fin 2 → R`, factors as
`(x₀ + x₁) (x₀ - x₁)`, so `![1, 1]` and `![1, -1]` span its two isotropic lines. For a unit `t`,
the linear automorphism scaling `![1, 1]` by `t` and `![1, -1]` by `t⁻¹` is a proper isometry: it
is the diagonal torus `diag(t, t⁻¹)` of the `xy`-model written in the diagonal coordinates.

Over a domain in which two is invertible these are all the proper isometries, so the torus is an
isomorphism `Rˣ ≃* SO(H)`. An isometry permutes the two isotropic lines; a proper one cannot
exchange them, since the exchanging isometries have determinant `-1`.

## Main definitions

* `TauCeti.hyperbolicTorus`: the homomorphism `Rˣ →* SO(H)`, `t ↦ diag(t, t⁻¹)` in the isotropic
  basis `![1, 1]`, `![1, -1]`.
* `TauCeti.hyperbolicTorusEquiv`: over a domain, the isomorphism `Rˣ ≃* SO(H)` it induces.

## Main results

* `TauCeti.hyperbolicTorus_apply_one_one`, `TauCeti.hyperbolicTorus_apply_one_neg_one`: the torus
  acts on the isotropic vectors by `t` and `t⁻¹`.
* `TauCeti.hyperbolicTorus_injective`, `TauCeti.hyperbolicTorus_surjective`: the torus is injective,
  and over a domain every proper isometry of the hyperbolic plane lies on it.
-/

public section

namespace TauCeti

open _root_.TauCeti.QuadraticMap

variable (R : Type*) [CommRing R] [Invertible (2 : R)]

/-- The matrix of `diag(t, t⁻¹)` in the diagonal coordinates of the hyperbolic plane. -/
private noncomputable def hyperbolicTorusMatrix (t : Rˣ) : Matrix (Fin 2) (Fin 2) R :=
  !![⅟2 * (t + ↑t⁻¹), ⅟2 * (t - ↑t⁻¹); ⅟2 * (t - ↑t⁻¹), ⅟2 * (t + ↑t⁻¹)]

private theorem hyperbolicTorusMatrix_mul (s t : Rˣ) :
    hyperbolicTorusMatrix R s * hyperbolicTorusMatrix R t = hyperbolicTorusMatrix R (s * t) := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicTorusMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (⅟2 * (s * t + ↑t⁻¹ * ↑s⁻¹ : R)) * h2
  · linear_combination (⅟2 * (s * t - ↑t⁻¹ * ↑s⁻¹ : R)) * h2
  · linear_combination (⅟2 * (s * t - ↑t⁻¹ * ↑s⁻¹ : R)) * h2
  · linear_combination (⅟2 * (s * t + ↑t⁻¹ * ↑s⁻¹ : R)) * h2

private theorem hyperbolicTorusMatrix_one : hyperbolicTorusMatrix R 1 = 1 := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicTorusMatrix, ← two_mul, h2]

/-- `diag(t, t⁻¹)` in the isotropic basis, as a linear automorphism of the hyperbolic plane. -/
private noncomputable def hyperbolicTorusLinearEquiv (t : Rˣ) : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (hyperbolicTorusMatrix R t))
    (Matrix.toLin' (hyperbolicTorusMatrix R t⁻¹))
    (by rw [← Matrix.toLin'_mul, hyperbolicTorusMatrix_mul, mul_inv_cancel,
      hyperbolicTorusMatrix_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hyperbolicTorusMatrix_mul, inv_mul_cancel,
      hyperbolicTorusMatrix_one, Matrix.toLin'_one])

private theorem hyperbolicTorusLinearEquiv_apply (t : Rˣ) (x : Fin 2 → R) :
    hyperbolicTorusLinearEquiv R t x =
      ![⅟2 * ((t + ↑t⁻¹) * x 0 + (t - ↑t⁻¹) * x 1),
        ⅟2 * ((t - ↑t⁻¹) * x 0 + (t + ↑t⁻¹) * x 1)] := by
  ext i
  fin_cases i <;>
    simp [hyperbolicTorusLinearEquiv, hyperbolicTorusMatrix, Matrix.mulVec, dotProduct] <;> ring

private theorem hyperbolicTorusLinearEquiv_mem (t : Rˣ) :
    hyperbolicTorusLinearEquiv R t ∈ specialOrthogonalGroup (hyperbolicPlane R) := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  have ht : (t : R) * ↑t⁻¹ = 1 := t.mul_inv
  refine mem_specialOrthogonalGroup_iff.mpr ⟨mem_orthogonalGroup_iff.mpr fun x ↦ ?_, Units.ext ?_⟩
  · rw [hyperbolicTorusLinearEquiv_apply, hyperbolicPlane_apply, hyperbolicPlane_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (x 0 ^ 2 - x 1 ^ 2) * ((t * ↑t⁻¹ * (⅟2 * 2 + 1) : R) * h2 + ht)
  · rw [LinearEquiv.coe_det, Units.val_one, hyperbolicTorusLinearEquiv,
      LinearEquiv.toLinearMap_ofLinearMap, LinearMap.det_toLin', hyperbolicTorusMatrix,
      Matrix.det_fin_two_of]
    linear_combination (t * ↑t⁻¹ * (⅟2 * 2 + 1) : R) * h2 + ht

/-- The diagonal torus of the hyperbolic plane: the proper isometry `diag(t, t⁻¹)` in the
isotropic basis `![1, 1]`, `![1, -1]`, which scales `![1, 1]` by `t` and `![1, -1]` by `t⁻¹`
(`hyperbolicTorus_apply_one_one`, `hyperbolicTorus_apply_one_neg_one`). -/
noncomputable def hyperbolicTorus : Rˣ →* specialOrthogonalGroup (hyperbolicPlane R) where
  toFun t := ⟨hyperbolicTorusLinearEquiv R t, hyperbolicTorusLinearEquiv_mem R t⟩
  map_one' := Subtype.ext <| LinearEquiv.toLinearMap_injective <| by
    simp [hyperbolicTorusLinearEquiv, hyperbolicTorusMatrix_one]
  map_mul' s t := Subtype.ext <| LinearEquiv.toLinearMap_injective <| by
    simp [hyperbolicTorusLinearEquiv, ← hyperbolicTorusMatrix_mul, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]

variable {R}

/-- The diagonal torus in the coordinates of the hyperbolic plane. -/
theorem hyperbolicTorus_apply (t : Rˣ) (x : Fin 2 → R) :
    (hyperbolicTorus R t : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) x =
      ![⅟2 * ((t + ↑t⁻¹) * x 0 + (t - ↑t⁻¹) * x 1),
        ⅟2 * ((t - ↑t⁻¹) * x 0 + (t + ↑t⁻¹) * x 1)] :=
  hyperbolicTorusLinearEquiv_apply R t x

/-- The diagonal torus scales the isotropic vector `![1, 1]` by `t`. -/
@[simp]
theorem hyperbolicTorus_apply_one_one (t : Rˣ) :
    (hyperbolicTorus R t : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) ![1, 1] = (t : R) • ![1, 1] := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  rw [hyperbolicTorus_apply]
  ext i
  fin_cases i <;> simp <;> linear_combination (t : R) * h2

/-- The diagonal torus scales the isotropic vector `![1, -1]` by `t⁻¹`. -/
@[simp]
theorem hyperbolicTorus_apply_one_neg_one (t : Rˣ) :
    (hyperbolicTorus R t : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) ![1, -1] = (↑t⁻¹ : R) • ![1, -1] := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  rw [hyperbolicTorus_apply]
  ext i
  fin_cases i <;> simp
  · linear_combination (↑t⁻¹ : R) * h2
  · linear_combination -(↑t⁻¹ : R) * h2

/-- The diagonal torus of the hyperbolic plane is injective. -/
theorem hyperbolicTorus_injective : Function.Injective (hyperbolicTorus R) := by
  intro s t h
  have h0 := congr_arg
    (fun g : specialOrthogonalGroup (hyperbolicPlane R) ↦
      (g : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) ![1, 1] 0) h
  exact Units.ext (by simpa using h0)

/-- Every vector of the hyperbolic plane in the isotropic basis `![1, 1]`, `![1, -1]`. -/
private theorem eq_smul_add_smul_isotropic (x : Fin 2 → R) :
    x = (⅟2 * (x 0 + x 1)) • ![1, 1] + (⅟2 * (x 0 - x 1)) • ![1, -1] := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  ext i
  fin_cases i <;> simp
  · linear_combination -(x 0) * h2
  · linear_combination -(x 1) * h2

/-- A linear endomorphism of the hyperbolic plane is determined by its values on the isotropic
vectors `![1, 1]` and `![1, -1]`. -/
private theorem linearMap_ext_isotropic {f g : (Fin 2 → R) →ₗ[R] (Fin 2 → R)}
    (h₁ : f ![1, 1] = g ![1, 1]) (h₂ : f ![1, -1] = g ![1, -1]) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  rw [eq_smul_add_smul_isotropic x]
  simp only [map_add, map_smul, h₁, h₂]

/-- The determinant of a linear endomorphism of the hyperbolic plane, from its values on the
isotropic vectors `![1, 1]` and `![1, -1]`. -/
private theorem det_eq_of_isotropic (f : (Fin 2 → R) →ₗ[R] (Fin 2 → R)) :
    LinearMap.det f = ⅟2 * (f ![1, -1] 0 * f ![1, 1] 1 - f ![1, 1] 0 * f ![1, -1] 1) := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply]
  rw [eq_smul_add_smul_isotropic (Pi.single 0 1), eq_smul_add_smul_isotropic (Pi.single 1 1)]
  simp only [map_add, map_smul]
  simp
  linear_combination ⅟2 * (f ![1, -1] 0 * f ![1, 1] 1 - f ![1, 1] 0 * f ![1, -1] 1) * h2

variable [IsDomain R]

/-- Over a domain in which two is invertible, every proper isometry of the hyperbolic plane lies on
the diagonal torus. An isometry permutes the two isotropic lines spanned by `![1, 1]` and
`![1, -1]`; one that exchanges them has determinant `-1`, and one that preserves them scales the
two isotropic vectors by `t` and `t⁻¹` for some unit `t`. -/
theorem hyperbolicTorus_surjective : Function.Surjective (hyperbolicTorus R) := by
  have h2 : ⅟2 * (2 : R) = 1 := invOf_mul_self 2
  have h2' : (2 : R) ≠ 0 := (isUnit_of_invertible (2 : R)).ne_zero
  rintro ⟨g, hg⟩
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hg
  obtain ⟨p, hp_def⟩ : ∃ p, g ![1, 1] = p := ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q, g ![1, -1] = q := ⟨_, rfl⟩
  -- The images of the isotropic vectors are isotropic, and pair to `polar H ![1, 1] ![1, -1] = 4`.
  have hp : (p 0 - p 1) * (p 0 + p 1) = 0 := by
    have h := map_app_of_mem_orthogonalGroup hO ![1, 1]
    simp only [hyperbolicPlane_apply] at h
    simp [hp_def] at h
    linear_combination h
  have hq : (q 0 - q 1) * (q 0 + q 1) = 0 := by
    have h := map_app_of_mem_orthogonalGroup hO ![1, -1]
    simp only [hyperbolicPlane_apply] at h
    simp [hq_def] at h
    linear_combination h
  have hpq : p 0 * q 0 - p 1 * q 1 = 2 := by
    have h := polar_apply_of_mem_orthogonalGroup hO ![1, 1] ![1, -1]
    simp only [hp_def, hq_def, polar_hyperbolicPlane, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    linear_combination ⅟2 * h - (p 0 * q 0 - p 1 * q 1 - 2) * h2
  have hdet' : ⅟2 * (q 0 * p 1 - p 0 * q 1) = 1 := by
    rw [← hp_def, ← hq_def, ← LinearEquiv.coe_coe,
      ← det_eq_of_isotropic, ← LinearEquiv.coe_det, hdet, Units.val_one]
  -- Each image lies on one of the two isotropic lines; only the line-preserving case survives.
  rcases mul_eq_zero.mp hp with hp | hp <;> rcases mul_eq_zero.mp hq with hq | hq
  · -- both images on the line of `![1, 1]`: then `polar` would vanish
    exact absurd (by linear_combination -hpq + q 0 * hp + p 1 * hq) h2'
  · -- the torus case: `g ![1, 1] = t • ![1, 1]` and `g ![1, -1] = t⁻¹ • ![1, -1]`
    have hp1 : p 1 = p 0 := by linear_combination -hp
    have hq1 : q 1 = -q 0 := by linear_combination hq
    rw [hp1, hq1] at hpq
    have ht : p 0 * q 0 = 1 := by linear_combination ⅟2 * hpq - (p 0 * q 0 - 1) * h2
    refine ⟨⟨p 0, q 0, ht, by rw [mul_comm, ht]⟩,
      Subtype.ext <| LinearEquiv.toLinearMap_injective <| linearMap_ext_isotropic ?_ ?_⟩
    · simp only [LinearEquiv.coe_coe, hyperbolicTorus_apply_one_one, hp_def]
      ext i
      fin_cases i <;> simp [hp1]
    · simp only [LinearEquiv.coe_coe, hyperbolicTorus_apply_one_neg_one, hq_def]
      ext i
      fin_cases i <;> simp [hq1]
  · -- the images exchange the two isotropic lines: then the determinant is `-1`
    have hp1 : p 1 = -p 0 := by linear_combination hp
    have hq1 : q 1 = q 0 := by linear_combination -hq
    rw [hp1, hq1] at hpq hdet'
    exact absurd (by linear_combination -hdet' - ⅟2 * hpq - h2) h2'
  · -- both images on the line of `![1, -1]`: then `polar` would vanish
    have hp1 : p 1 = -p 0 := by linear_combination hp
    have hq1 : q 1 = -q 0 := by linear_combination hq
    rw [hp1, hq1] at hpq
    exact absurd (by linear_combination -hpq) h2'

variable (R) in
/-- Over a domain in which two is invertible, the diagonal torus identifies the units with the
special orthogonal group of the hyperbolic plane. -/
noncomputable def hyperbolicTorusEquiv : Rˣ ≃* specialOrthogonalGroup (hyperbolicPlane R) :=
  MulEquiv.ofBijective (hyperbolicTorus R) ⟨hyperbolicTorus_injective, hyperbolicTorus_surjective⟩

/-- The isomorphism `hyperbolicTorusEquiv R` is the diagonal torus. -/
@[simp]
theorem hyperbolicTorusEquiv_apply (t : Rˣ) : hyperbolicTorusEquiv R t = hyperbolicTorus R t :=
  (rfl)

/-- The parameter of a proper isometry of the hyperbolic plane is the first coordinate of the image
of the isotropic vector `![1, 1]`. -/
theorem coe_hyperbolicTorusEquiv_symm_apply (g : specialOrthogonalGroup (hyperbolicPlane R)) :
    (((hyperbolicTorusEquiv R).symm g : Rˣ) : R) =
      (g : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) ![1, 1] 0 := by
  obtain ⟨t, rfl⟩ := (hyperbolicTorusEquiv R).surjective g
  rw [MulEquiv.symm_apply_apply, hyperbolicTorusEquiv_apply, hyperbolicTorus_apply_one_one]
  simp

end TauCeti
