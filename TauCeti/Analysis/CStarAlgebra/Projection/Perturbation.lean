/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
public import TauCeti.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.Connected.Clopen
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.Projection.Pair
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

/-!
# Nearby and homotopic projections

Two star projections `p` and `q` in a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a
unitary `u` with `‖u - 1‖ ≤ √2 * ‖p - q‖`. The unitary is the unitary part of the polar
decomposition of the intertwiner `z = q * p + (1 - q) * (1 - p)`: since
`star z * z = z * star z = 1 - (p - q) ^ 2` commutes with `p` and `q`, the element
`u = z * (1 - (p - q) ^ 2) ^ (-1 / 2)` is a unitary with `u * p * star u = q`, and its real part
`(1 - (p - q) ^ 2) ^ (1 / 2)` gives the norm estimate. Since `‖u - 1‖ < 2`, the unitary lies in
the path component of the identity of the unitary group.

Consequently the values of a norm-continuous family of projections over a preconnected space are
mutually unitarily equivalent, through unitaries joined to `1`, and two projections in a unital
C⋆-algebra are joined by a continuous path of projections if and only if they are conjugate by a
unitary in the path component of `1`. In a C⋆-algebra without unit, applying this in the
unitization shows that nearby projections, and the values of a continuous family of projections,
are Murray–von Neumann equivalent. For matrices over a C⋆-algebra this says that matrix projections
joined by a path of matrix projections are Murray–von Neumann equivalent, so they have the same
class in the projection monoid `V(A)`.

## Main statements

* `IsStarProjection.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one`: projections `p` and
  `q` of a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary `u` with
  `‖u - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one`: the conjugating
  unitary can be chosen in the path component of `1`.
* `IsStarProjection.exists_star_mul_self_eq_of_norm_sub_lt_one`: in a C⋆-algebra, possibly
  without unit, projections with `‖p - q‖ < 1` are Murray–von Neumann equivalent.
* `Continuous.exists_joined_one_mul_mul_star_eq`: the values of a continuous family of projections
  of a unital C⋆-algebra over a preconnected space are conjugate by unitaries joined to `1`.
* `IsStarProjection.exists_path_iff_exists_joined_one_mul_mul_star_eq`: projections `p` and `q` of
  a unital C⋆-algebra are joined by a continuous path of projections if and only if they are
  conjugate by a unitary joined to `1`.
* `Continuous.exists_star_mul_self_eq`: the values of a continuous family of projections over a
  preconnected space are Murray–von Neumann equivalent.
* `Continuous.isMurrayVonNeumannEquivalent`: the values of a continuous family of matrix
  projections over a C⋆-algebra are Murray–von Neumann equivalent matrix projections.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 2.2.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Section 4.6.
-/

public section

/-- For `|t| ≤ s < 1`, the defect `2 - 2 * √(1 - t)` is at most `2 * s` in absolute value. -/
private theorem abs_two_sub_two_mul_sqrt_one_sub_le {t s : ℝ} (hts : |t| ≤ s) (hs : s < 1) :
    |2 - 2 * √(1 - t)| ≤ 2 * s := by
  have ht : 0 ≤ 1 - t := by linarith [le_abs_self t]
  have hsq := Real.sq_sqrt ht
  have hnn := Real.sqrt_nonneg (1 - t)
  rw [abs_le] at hts ⊢
  constructor <;> nlinarith

namespace IsStarProjection

section Unital

variable {A : Type*} [CStarAlgebra A] {p q : A}

section Defect

/-! In this section `h` is a self-adjoint element with `‖h‖ < 1`, so that `1 - h` has the
inverse square root `cfc (fun t ↦ (√(1 - t))⁻¹) h`. -/

variable {h : A}

private theorem one_sub_eq_cfc (hh : IsSelfAdjoint h) : 1 - h = cfc (fun t : ℝ ↦ 1 - t) h := by
  rw [cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t) h, cfc_const_one ℝ h, cfc_id' ℝ h]

variable (hh : IsSelfAdjoint h) (h₁ : ‖h‖ < 1)
include h₁

private theorem one_sub_pos_of_mem_spectrum {t : ℝ} (ht : t ∈ spectrum ℝ h) : 0 < 1 - t := by
  have := spectrum.norm_le_norm_of_mem ht
  rw [Real.norm_eq_abs] at this
  linarith [le_abs_self t]

private theorem continuousOn_inv_sqrt_one_sub :
    ContinuousOn (fun t : ℝ ↦ (√(1 - t))⁻¹) (spectrum ℝ h) :=
  ContinuousOn.inv₀ (by fun_prop) fun _ ht ↦
    (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

include hh

/-- `(1 - h) ^ (-1 / 2) * (1 - h) = (1 - h) ^ (1 / 2)`. -/
private theorem cfc_inv_sqrt_one_sub_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = cfc (fun t : ℝ ↦ √(1 - t)) h := by
  rw [one_sub_eq_cfc hh, ← cfc_mul _ _ h (continuousOn_inv_sqrt_one_sub h₁) (by fun_prop)]
  refine cfc_congr fun t ht ↦ ?_
  have h₀ := one_sub_pos_of_mem_spectrum h₁ ht
  have := Real.sq_sqrt h₀.le
  have := (Real.sqrt_pos.2 h₀).ne'
  field_simp
  linarith

/-- `(1 - h) ^ (-1 / 2) * (1 - h) ^ (-1 / 2) * (1 - h) = 1`. -/
private theorem cfc_inv_sqrt_one_sub_mul_self_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = 1 := by
  have hc := continuousOn_inv_sqrt_one_sub h₁
  rw [mul_assoc, cfc_inv_sqrt_one_sub_mul_one_sub hh h₁, ← cfc_mul _ _ h hc (by fun_prop),
    ← cfc_const_one ℝ h]
  refine cfc_congr fun t ht ↦ ?_
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

/-- `‖2 - 2 * (1 - h) ^ (1 / 2)‖ ≤ 2 * ‖h‖`. -/
private theorem norm_two_sub_two_mul_cfc_sqrt_one_sub_le :
    ‖2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h‖ ≤ 2 * ‖h‖ := by
  rw [show 2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h = cfc (fun t : ℝ ↦ 2 - 2 * √(1 - t)) h by
    rw [cfc_sub (fun _ : ℝ ↦ (2 : ℝ)) (fun t : ℝ ↦ 2 * √(1 - t)) h, cfc_const_mul 2 _ h,
      cfc_const (2 : ℝ) h, map_ofNat, two_smul, two_mul]]
  refine norm_cfc_le (by positivity) fun t ht ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_two_sub_two_mul_sqrt_one_sub_le (spectrum.norm_le_norm_of_mem ht) h₁

end Defect

/-- **Nearby projections are unitarily equivalent.** Star projections `p` and `q` of a unital
C⋆-algebra with `‖p - q‖ < 1` are conjugate, `u * p * star u = q`, by a unitary `u` with
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u ∈ unitary A, u * p * star u = q ∧ ‖u - 1‖ ≤ √2 * ‖p - q‖ := by
  -- `h = (p - q) ^ 2` commutes with `p` and `q`, and `z` intertwines `p` with `q`.
  set h := (p - q) ^ 2
  set z := TauCeti.intertwiner p q with hz
  have hp' := hp.isIdempotentElem
  have hq' := hq.isIdempotentElem
  have hh : IsSelfAdjoint h := (hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2
  have hnorm : ‖h‖ ≤ ‖p - q‖ ^ 2 := norm_pow_le' _ two_pos
  have h₁ : ‖h‖ < 1 := hnorm.trans_lt (by nlinarith [norm_nonneg (p - q)])
  have hzz : star z * z = 1 - h := hp.star_intertwiner_mul_intertwiner hq
  have hzz' : z * star z = 1 - h := hp.intertwiner_mul_star_intertwiner hq
  have hzp : z * p = q * z := hp'.intertwiner_mul hq'
  -- `c = (1 - h) ^ (-1 / 2)` commutes with `p`, `q`, `h`, `z` and `star z`.
  set c := cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h
  have hc : star c = c := IsSelfAdjoint.cfc.star_eq
  have hcc : c * c * (1 - h) = 1 := cfc_inv_sqrt_one_sub_mul_self_mul_one_sub hh h₁
  have hcp : Commute c p := Commute.cfc_real (hp'.commute_sub_sq_left hq').symm _
  have hcq : Commute c q := Commute.cfc_real (hp'.commute_sub_sq_right hq').symm _
  have hc₁ : Commute c (1 - h) := (Commute.one_right c).sub_right (Commute.cfc_real (.refl h) _)
  have hcz : Commute c z := by
    rw [hz, TauCeti.intertwiner_def]
    exact (hcq.mul_right hcp).add_right
      (((Commute.one_right c).sub_right hcq).mul_right ((Commute.one_right c).sub_right hcp))
  have hcz' : Commute c (star z) := hc ▸ hcz.star_star
  -- The unitary `u = z * c`, the unitary part of the polar decomposition of `z`.
  have hu₁ : star (z * c) * (z * c) = 1 := by
    calc star (z * c) * (z * c) = c * (star z * z) * c := by simp only [star_mul, hc, mul_assoc]
      _ = c * c * (1 - h) := by rw [hzz, mul_assoc, ← hc₁.eq, ← mul_assoc]
      _ = 1 := hcc
  have hu₂ : z * c * star (z * c) = 1 := by
    calc z * c * star (z * c) = z * ((c * c) * star z) := by simp only [star_mul, hc, mul_assoc]
      _ = (1 - h) * (c * c) := by rw [(hcz'.mul_left hcz').eq, ← mul_assoc, hzz']
      _ = 1 := by rw [← (hc₁.mul_left hc₁).eq, hcc]
  have hconj : z * c * p * star (z * c) = q := by
    calc z * c * p * star (z * c) = z * p * (c * star (z * c)) := by
          rw [mul_assoc z c p, hcp.eq, ← mul_assoc z p c, mul_assoc]
      _ = q * (z * c * star (z * c)) := by rw [hzp, mul_assoc, mul_assoc, ← mul_assoc z c]
      _ = q := by rw [hu₂, mul_one]
  -- Its real part is `(1 - h) ^ (1 / 2)`, which gives the norm estimate.
  have hdefect : star (z * c - 1) * (z * c - 1) = 2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h := by
    have hzs : z + star z = 2 * (1 - h) := hp.intertwiner_add_star_intertwiner hq
    have hre : z * c + star (z * c) = 2 * cfc (fun t : ℝ ↦ √(1 - t)) h := by
      rw [star_mul, hc, ← hcz.eq, ← mul_add, hzs, two_mul, mul_add, ← two_mul,
        cfc_inv_sqrt_one_sub_mul_one_sub hh h₁]
    rw [← hre, star_sub, star_one, sub_mul, mul_sub, mul_sub, hu₁, mul_one, one_mul, one_mul,
      ← one_add_one_eq_two]
    abel
  have hbound : ‖z * c - 1‖ ^ 2 ≤ 2 * ‖p - q‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, hdefect]
    exact (norm_two_sub_two_mul_cfc_sqrt_one_sub_le hh h₁).trans (by gcongr)
  refine ⟨z * c, ⟨hu₁, hu₂⟩, hconj, ?_⟩
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt zero_le_two]

/-- **Nearby projections are homotopic through unitaries.** Star projections `p` and `q` of a
unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary in the path component of `1`. -/
theorem exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q := by
  obtain ⟨u, hu, hupq, hnorm⟩ := hp.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hq hpq
  refine ⟨⟨u, hu⟩, Unitary.joined 1 ⟨u, hu⟩ ?_, hupq⟩
  have hsqrt : √2 < 2 := by
    rw [Real.sqrt_lt' two_pos]
    norm_num
  calc ‖u - ((1 : unitary A) : A)‖ = ‖u - 1‖ := by rw [OneMemClass.coe_one]
    _ ≤ √2 * ‖p - q‖ := hnorm
    _ ≤ √2 * 1 := by gcongr
    _ < 2 := by rwa [mul_one]

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q : A}

/-- **Nearby projections are Murray–von Neumann equivalent.** Star projections `p` and `q` of a
C⋆-algebra, possibly without unit, with `‖p - q‖ < 1` satisfy `star v * v = p` and
`v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hp' := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  rw [Unitization.inrNonUnitalStarAlgHom_apply] at hp' hq'
  obtain ⟨u, hu, hupq, -⟩ := hp'.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hq'
    (by rwa [← Unitization.inr_sub, Unitization.norm_inr])
  exact hp.exists_star_mul_self_eq_of_mem_unitary_unitization hu hupq

end NonUnital

end IsStarProjection

section Continuous

/-! The statements below write `Star.star`: in a declaration named `Continuous.foo`, plain `star`
resolves to `Continuous.star`. -/

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- **Homotopic projections are unitarily equivalent.** For a continuous family `f` of star
projections of a unital C⋆-algebra over a preconnected space, any two values `f x` and `f y` are
conjugate by a unitary in the path component of `1`. For a path of projections this compares its
endpoints. -/
theorem Continuous.exists_joined_one_mul_mul_star_eq {A : Type*} [CStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y)
    (fun x ↦ ?_) ⟨fun a b c ⟨u, hu, hab⟩ ⟨v, hv, hbc⟩ ↦ ⟨v * u, ?_, ?_⟩⟩ x y
  · filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds (f x) one_pos)] with y hy
    rw [dist_eq_norm] at hy
    exact ⟨(hfp x).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hfp y)
      (by rwa [norm_sub_rev]), (hfp y).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one
      (hfp x) hy⟩
  · simpa using hv.mul hu
  · rw [Submonoid.coe_mul, star_mul, ← hbc, ← hab]
    simp only [mul_assoc]

/-- Two star projections `p` and `q` of a unital C⋆-algebra are joined by a continuous path of star
projections if and only if they are conjugate by a unitary in the path component of `1`. -/
theorem IsStarProjection.exists_path_iff_exists_joined_one_mul_mul_star_eq {A : Type*}
    [CStarAlgebra A] {p q : A} (hp : IsStarProjection p) :
    (∃ γ : Path p q, ∀ t, IsStarProjection (γ t)) ↔
      ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q :=
  ⟨fun ⟨γ, hγ⟩ ↦ by simpa only [γ.source, γ.target] using
      γ.continuous.exists_joined_one_mul_mul_star_eq hγ 0 1,
    fun ⟨_, hu, hq⟩ ↦ hq ▸ hp.exists_path_of_joined_one_unitary hu⟩

/-- **Homotopic projections are Murray–von Neumann equivalent.** For a continuous family `f` of
star projections of a C⋆-algebra, possibly without unit, over a preconnected space, any two values
satisfy `star v * v = f x` and `v * star v = f y` for some `v`. -/
theorem Continuous.exists_star_mul_self_eq {A : Type*} [NonUnitalCStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ v : A, Star.star v * v = f x ∧ v * Star.star v = f y := by
  have hfp' (x : X) : IsStarProjection ((f x : A) : Unitization ℂ A) := by
    simpa using (hfp x).map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨u, -, hu⟩ :=
    ((Unitization.continuous_inr (𝕜 := ℂ)).comp hf).exists_joined_one_mul_mul_star_eq hfp' x y
  exact (hfp x).exists_star_mul_self_eq_of_mem_unitary_unitization u.property hu

/-- **Homotopic matrix projections are Murray–von Neumann equivalent.** For a continuous family `f`
of matrix projections over a C⋆-algebra, possibly without unit, over a preconnected space, any two
values `f x` and `f y` are Murray–von Neumann equivalent. The topology on matrices is the entrywise
one, which is the norm topology of `CStarMatrix n n A`. -/
theorem Continuous.isMurrayVonNeumannEquivalent {A : Type*} [NonUnitalCStarAlgebra A]
    {n : Type*} [Fintype n] {f : X → Matrix n n A} (hf : Continuous f)
    (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    Matrix.IsMurrayVonNeumannEquivalent (f x) (f y) := by
  -- `CStarMatrix n n A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have hfp' (x : X) : IsStarProjection (CStarMatrix.ofMatrix (f x)) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 (hfp x)
  have hg : Continuous fun x ↦ CStarMatrix.ofMatrix (f x) := by
    rw [CStarMatrix.ofMatrix_eq_ofMatrixL]
    exact CStarMatrix.ofMatrixL.continuous.comp hf
  obtain ⟨v, hv₁, hv₂⟩ := hg.exists_star_mul_self_eq hfp' x y
  refine ⟨hfp x, hfp y, CStarMatrix.ofMatrix.symm v, ?_, ?_⟩
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₁,
      Equiv.symm_apply_apply]
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₂,
      Equiv.symm_apply_apply]

end Continuous
