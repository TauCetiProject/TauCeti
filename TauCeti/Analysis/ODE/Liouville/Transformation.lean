/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Liouville transformation

An increasing change of independent variable `z = z(ξ)` introduces a first-derivative term
in a scalar second-order equation. The rescaling `W(ξ) = w(z(ξ)) / √z'(ξ)` removes it.
We compute both derivatives of this rescaling and its transformed differential equation.
In particular, when `z'(ξ)² f(z(ξ)) = 1`, the equation `w'' = (u² f + g) w` becomes
`W'' = (u² + ψ) W`, where `ψ` is given explicitly in terms of the first three derivatives
of `z` and `g`.

For a vector-valued `h`, the rescaling `φ'^{-1/2} • h ∘ φ` has second derivative
`(φ'^{-1/2})'' • h ∘ φ + φ'^{-1/2} φ'² • h'' ∘ φ` (`iteratedDeriv_two_deriv_rpow_smul_comp`).

All statements are local: they apply at an interior point of any parameter interval.
The positivity of `z'` fixes the real square root used in the rescaling.

## References

* NIST Digital Library of Mathematical Functions, §2.8(i), equations (2.8.1)–(2.8.5),
  <https://dlmf.nist.gov/2.8.i>.
-/

public section

open Set
open scoped ContDiff Topology

namespace TauCeti

/-- The Liouville rescaling associated to a change of independent variable `z`.
Its differential-equation interpretation requires `deriv z` to be positive. -/
noncomputable def liouvilleTransform (z w : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  w (z ξ) / Real.sqrt (deriv z ξ)

@[simp]
theorem liouvilleTransform_apply (z w : ℝ → ℝ) (ξ : ℝ) :
    liouvilleTransform z w ξ = w (z ξ) / Real.sqrt (deriv z ξ) := (rfl)

@[simp]
theorem liouvilleTransform_id (w : ℝ → ℝ) : liouvilleTransform id w = w := by
  ext ξ
  simp

/-- Multiplying by the positive square-root factor recovers the original solution
in the new coordinate. Thus the rescaling does not lose information where `z' > 0`. -/
theorem sqrt_deriv_mul_liouvilleTransform (z w : ℝ → ℝ) {ξ : ℝ}
    (hpos : 0 < deriv z ξ) :
    Real.sqrt (deriv z ξ) * liouvilleTransform z w ξ = w (z ξ) := by
  rw [liouvilleTransform_apply]
  exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr hpos).ne'

/-- The Liouville rescaling loses one derivative of the change of independent variable. -/
theorem contDiffAt_liouvilleTransform (z w : ℝ → ℝ) {n : ℕ∞ω} {ξ : ℝ}
    (hz : ContDiffAt ℝ (n + 1) z ξ) (hw : ContDiffAt ℝ n w (z ξ))
    (hpos : 0 < deriv z ξ) : ContDiffAt ℝ n (liouvilleTransform z w) ξ := by
  have hz' : ContDiffAt ℝ n (deriv z) ξ := hz.derivWithin le_rfl
  exact (hw.comp ξ (hz.of_le le_self_add)).div (hz'.sqrt hpos.ne')
    (Real.sqrt_pos.mpr hpos).ne'

/-- The first derivative of the Liouville rescaling. -/
theorem hasDerivAt_liouvilleTransform (z w : ℝ → ℝ) {ξ : ℝ}
    (hz : ContDiffAt ℝ 2 z ξ) (hw : DifferentiableAt ℝ w (z ξ))
    (hpos : 0 < deriv z ξ) :
    HasDerivAt (liouvilleTransform z w)
      (Real.sqrt (deriv z ξ) * deriv w (z ξ) -
        deriv (deriv z) ξ * w (z ξ) / (2 * Real.sqrt (deriv z ξ) ^ 3)) ξ := by
  have hz' : ContDiffAt ℝ 1 (deriv z) ξ := hz.derivWithin (by norm_num)
  have hd := (hw.hasDerivAt.comp ξ (hz.differentiableAt (by norm_num)).hasDerivAt).div
    ((hz'.differentiableAt (by norm_num)).hasDerivAt.sqrt hpos.ne')
    (Real.sqrt_pos.mpr hpos).ne'
  apply hd.congr_deriv
  have hs := Real.sq_sqrt hpos.le
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  simp only [Function.comp_apply]
  generalize Real.sqrt (deriv z ξ) = s at *
  rw [← hs]
  field_simp

/-- The second derivative of the Liouville rescaling. The correction to the coefficient
is minus one half of the Schwarzian derivative of `z`. -/
theorem deriv_deriv_liouvilleTransform (z w : ℝ → ℝ) {ξ : ℝ}
    (hz : ContDiffAt ℝ 3 z ξ) (hw : ContDiffAt ℝ 2 w (z ξ))
    (hpos : 0 < deriv z ξ) :
    deriv (deriv (liouvilleTransform z w)) ξ =
      (deriv z ξ) ^ 2 * deriv (deriv w) (z ξ) / Real.sqrt (deriv z ξ) +
        (3 * (deriv (deriv z) ξ) ^ 2 / (4 * (deriv z ξ) ^ 2) -
          deriv (deriv (deriv z)) ξ / (2 * deriv z ξ)) * liouvilleTransform z w ξ := by
  have hz' : ContDiffAt ℝ 2 (deriv z) ξ := hz.derivWithin (by norm_num)
  have hz'' : ContDiffAt ℝ 1 (deriv (deriv z)) ξ := hz'.derivWithin (by norm_num)
  have hw' : ContDiffAt ℝ 1 (deriv w) (z ξ) := hw.derivWithin (by norm_num)
  have hdz := (hz.differentiableAt (by norm_num)).hasDerivAt
  have hds := (hz'.differentiableAt (by norm_num)).hasDerivAt.sqrt hpos.ne'
  have hdw := (hw.differentiableAt (by norm_num)).hasDerivAt.comp ξ hdz
  have hdw' := (hw'.differentiableAt (by norm_num)).hasDerivAt.comp ξ hdz
  have hdb := (hz''.differentiableAt (by norm_num)).hasDerivAt
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  have hdf := (hds.mul hdw').sub
    ((hdb.mul hdw).div ((hds.pow 3).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hs0)))
  have heq : deriv (liouvilleTransform z w) =ᶠ[nhds ξ]
      (fun t => Real.sqrt (deriv z t) * deriv w (z t) -
        deriv (deriv z) t * w (z t) / (2 * Real.sqrt (deriv z t) ^ 3)) := by
    have hznear := hz.eventually (by norm_num)
    have hwnear := hw.eventually (by norm_num)
    have hposnear := hz'.continuousAt.eventually (lt_mem_nhds hpos)
    filter_upwards [hznear, (hz.continuousAt.eventually hwnear), hposnear] with t hzt hwt hpt
    exact (hasDerivAt_liouvilleTransform z w (hzt.of_le (by norm_num))
      (hwt.differentiableAt (by norm_num)) hpt).deriv
  simp only [Function.comp_def, Pi.mul_def, Pi.sub_def, Pi.div_def, Pi.pow_apply] at hdf
  rw [heq.deriv_eq, hdf.deriv, liouvilleTransform_apply]
  have hs := Real.sq_sqrt hpos.le
  generalize Real.sqrt (deriv z ξ) = s at *
  rw [← hs]
  field_simp
  ring

/-- The potential after Liouville rescaling: the pulled-back potential plus the
correction coming from the second derivative of the inverse square-root factor.
This is the coefficient `ψ` of DLMF (2.8.4) when `q` is the lower-order potential. -/
noncomputable def liouvillePotential (z q : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (deriv z ξ) ^ 2 * q (z ξ) + Real.sqrt (deriv z ξ) *
    deriv (deriv (fun t => (Real.sqrt (deriv z t))⁻¹)) ξ

theorem liouvillePotential_apply (z q : ℝ → ℝ) (ξ : ℝ) :
    liouvillePotential z q ξ = (deriv z ξ) ^ 2 * q (z ξ) + Real.sqrt (deriv z ξ) *
      deriv (deriv (fun t => (Real.sqrt (deriv z t))⁻¹)) ξ := (rfl)

@[simp]
theorem liouvillePotential_id (q : ℝ → ℝ) : liouvillePotential id q = q := by
  ext ξ
  simp [liouvillePotential_apply]

/-- The transformed potential in terms of the first three derivatives of the coordinate
change. In particular it does not involve derivatives of the original potential. -/
theorem liouvillePotential_eq (z q : ℝ → ℝ) {ξ : ℝ}
    (hz : ContDiffAt ℝ 3 z ξ) (hpos : 0 < deriv z ξ) :
    liouvillePotential z q ξ = (deriv z ξ) ^ 2 * q (z ξ) +
      3 * (deriv (deriv z) ξ) ^ 2 / (4 * (deriv z ξ) ^ 2) -
        deriv (deriv (deriv z)) ξ / (2 * deriv z ξ) := by
  have hone : liouvilleTransform z (fun _ => 1) =
      (fun t => (Real.sqrt (deriv z t))⁻¹) := by
    ext t
    simp
  have h := deriv_deriv_liouvilleTransform z (fun _ => 1) hz contDiffAt_const hpos
  rw [hone] at h
  simp only [deriv_const', mul_zero, zero_div, zero_add] at h
  rw [liouvillePotential_apply, h]
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  ring

/-- Liouville rescaling carries `w'' = q w` to an equation without a first-derivative term.
The equation is required only at the image of the point under consideration. -/
theorem deriv_deriv_liouvilleTransform_of_eq (z w q : ℝ → ℝ) {ξ : ℝ}
    (hz : ContDiffAt ℝ 3 z ξ) (hw : ContDiffAt ℝ 2 w (z ξ))
    (hpos : 0 < deriv z ξ) (heq : deriv (deriv w) (z ξ) = q (z ξ) * w (z ξ)) :
    deriv (deriv (liouvilleTransform z w)) ξ =
      liouvillePotential z q ξ * liouvilleTransform z w ξ := by
  rw [deriv_deriv_liouvilleTransform z w hz hw hpos, heq,
    liouvillePotential_eq z q hz hpos, liouvilleTransform_apply]
  ring

/-- The normalized Liouville transformation (Case I): if `z'² f ∘ z = 1`, then
`w'' = (u² f + g) w` becomes `W'' = (u² + ψ) W`, with `ψ = liouvillePotential z g`.
No nonvanishing assumption on the solution or on the parameter `u` is needed. -/
theorem deriv_deriv_liouvilleTransform_of_normalized (z w f g : ℝ → ℝ) (u : ℝ) {ξ : ℝ}
    (hz : ContDiffAt ℝ 3 z ξ) (hw : ContDiffAt ℝ 2 w (z ξ)) (hpos : 0 < deriv z ξ)
    (heq : deriv (deriv w) (z ξ) = (u ^ 2 * f (z ξ) + g (z ξ)) * w (z ξ))
    (hnorm : (deriv z ξ) ^ 2 * f (z ξ) = 1) :
    deriv (deriv (liouvilleTransform z w)) ξ =
      (u ^ 2 + liouvillePotential z g ξ) * liouvilleTransform z w ξ := by
  rw [deriv_deriv_liouvilleTransform_of_eq z w (fun t => u ^ 2 * f t + g t)
    hz hw hpos heq]
  congr 1
  simp only [liouvillePotential_apply]
  linear_combination u ^ 2 * hnorm

/-- The second derivative of the Liouville rescaling `u • h ∘ φ`, `u = φ'^{-1/2}`, of a
vector-valued function `h`: the first-derivative terms cancel, and
`(u • h ∘ φ)'' = u'' • h ∘ φ + u φ'² • h'' ∘ φ`. Unlike `deriv_deriv_liouvilleTransform`, the
correction is kept as `u''` rather than expanded into the Schwarzian derivative of `φ`. -/
theorem iteratedDeriv_two_deriv_rpow_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJ : IsOpen J) (hU : IsOpen U) {φ : ℝ → ℝ} {h : ℝ → E}
    (hφ : ContDiffOn ℝ 3 φ J) (hd : ∀ t ∈ J, 0 < deriv φ t) (hh : ContDiffOn ℝ 2 h U)
    (hφU : MapsTo φ J U) {t : ℝ} (ht : t ∈ J) :
    iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ) • h (φ s)) t =
      iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)) t • h (φ t) +
        (deriv φ t ^ (-(1 / 2) : ℝ) * deriv φ t ^ 2) • iteratedDeriv 2 h (φ t) := by
  set d := deriv φ
  set u : ℝ → ℝ := fun s ↦ d s ^ (-(1 / 2) : ℝ)
  have hd2 : ContDiffOn ℝ 2 d J := hφ.deriv_of_isOpen hJ (by norm_num)
  have hu : ContDiffOn ℝ 2 u J := hd2.rpow_const_of_ne fun s hs ↦ (hd s hs).ne'
  have hφ1 (s : ℝ) (hs : s ∈ J) : HasDerivAt φ (d s) s :=
    ((hφ.contDiffAt (hJ.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hd1 (s : ℝ) (hs : s ∈ J) : HasDerivAt d (deriv d s) s :=
    ((hd2.contDiffAt (hJ.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hu1 (s : ℝ) (hs : s ∈ J) :
      HasDerivAt u (deriv d s * (-(1 / 2)) * d s ^ (-(1 / 2) - 1 : ℝ)) s :=
    (hd1 s hs).rpow_const (Or.inl (hd s hs).ne')
  have hu2 : HasDerivAt (deriv u) (iteratedDeriv 2 u t) t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((hu.deriv_of_isOpen hJ (m := 1) (by norm_num)).contDiffAt
      (hJ.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  have hh1 (y : ℝ) (hy : y ∈ U) : HasDerivAt h (deriv h y) y :=
    ((hh.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
  have hh2 : HasDerivAt (deriv h) (iteratedDeriv 2 h (φ t)) (φ t) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((hh.deriv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds (hφU ht))).differentiableAt (by norm_num)).hasDerivAt
  -- the first derivative, near `t`
  have hfirst : deriv (fun s ↦ u s • h (φ s)) =ᶠ[𝓝 t]
      fun s ↦ (u s * d s) • deriv h (φ s) + deriv u s • h (φ s) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    have h1 : HasDerivAt (fun s ↦ u s • h (φ s))
        (u s • d s • deriv h (φ s) + deriv u s • h (φ s)) s :=
      (hu1 s hs).differentiableAt.hasDerivAt.smul ((hh1 _ (hφU hs)).scomp s (hφ1 s hs))
    rw [h1.deriv, smul_smul]
  have hsec : HasDerivAt (fun s ↦ (u s * d s) • deriv h (φ s) + deriv u s • h (φ s))
      ((u t * d t) • d t • iteratedDeriv 2 h (φ t) +
        (deriv d t * (-(1 / 2)) * d t ^ (-(1 / 2) - 1 : ℝ) * d t + u t * deriv d t) •
          deriv h (φ t) +
        (deriv u t • d t • deriv h (φ t) + iteratedDeriv 2 u t • h (φ t))) t :=
    (((hu1 t ht).mul (hd1 t ht)).smul (hh2.scomp t (hφ1 t ht))).add
      (hu2.smul ((hh1 _ (hφU ht)).scomp t (hφ1 t ht)))
  rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst.deriv_eq, hsec.deriv, (hu1 t ht).deriv]
  have hdt := hd t ht
  have hpow : d t ^ (-(1 / 2) - 1 : ℝ) * d t = d t ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_sub_one hdt.ne', div_mul_cancel₀ _ hdt.ne']
  have key : deriv d t * (-(1 / 2)) * d t ^ (-(1 / 2) - 1 : ℝ) * d t + u t * deriv d t +
      deriv d t * (-(1 / 2)) * d t ^ (-(1 / 2) - 1 : ℝ) * d t = 0 := by
    simp only [u]
    linear_combination (-deriv d t) * hpow
  simp only [u] at key ⊢
  linear_combination (norm := module) key • deriv h (φ t)

end TauCeti
