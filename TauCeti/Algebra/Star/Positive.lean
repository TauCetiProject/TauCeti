/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Order.Archimedean.Real.Basic

/-!
# Real-linearity from positive star functionals

On a real star algebra, real-linearity plus strict positivity on `x * star x` forces
`StarModule ℝ E` (`TauCeti.starModule_of_forall_pos_mul_star`), and forces `star` to act by
complex conjugation on the image of any central `ℝ`-algebra map `ℂ →ₐ[ℝ] E`
(`AlgHom.star_apply_of_mem_center_of_forall_pos_mul_star`).
-/

public section

namespace TauCeti

/-- **Automatic real-linearity of the involution.** Positivity of `t (x * star x)` on nonzero
elements forces `star` to fix every real scalar (`StarModule ℝ E`). -/
theorem starModule_of_forall_pos_mul_star {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) : StarModule ℝ E := by
  by_cases hsub : Subsingleton E
  · exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
  let f : ℝ →+ ℝ := ⟨⟨fun a ↦ t (star (algebraMap ℝ E a)), by simp⟩, fun _ _ ↦ by simp⟩
  have htf (a : ℝ) : t (star (algebraMap ℝ E a)) = t (algebraMap ℝ E a) := by
    have hmono : Monotone f := ((strictMono_iff_map_pos f).2 fun b hb ↦ by
      have h := hpos (algebraMap ℝ E b) fun h0 ↦ (one_ne_zero : (1 : E) ≠ 0) <| by
        simpa [Algebra.algebraMap_eq_smul_one, smul_smul, hb.ne'] using congrArg (b⁻¹ • ·) h0
      rw [← Algebra.smul_def, map_smul, smul_eq_mul] at h
      exact pos_of_mul_pos_right (by simpa [f] using h) hb.le).monotone
    simpa [f, Algebra.algebraMap_eq_smul_one, smul_eq_mul] using
      f.apply_eq_mul_map_one_of_monotone hmono a
  have hstar_alg (r : ℝ) : star (algebraMap ℝ E r) = algebraMap ℝ E r := by
    set u : E := star (algebraMap ℝ E r) - algebraMap ℝ E r
    have hsq : star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r) =
        (2 * r) • u + u * u := by
      have hstar_r : star (algebraMap ℝ E r) = algebraMap ℝ E r + u := by simp [u]
      have hcomm : algebraMap ℝ E r * u + u * algebraMap ℝ E r = (2 * r) • u := by
        rw [← Algebra.commutes, ← Algebra.smul_def, two_mul, add_smul]
      calc star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r)
        _ = (algebraMap ℝ E r + u) * (algebraMap ℝ E r + u) -
              algebraMap ℝ E r * algebraMap ℝ E r := by rw [map_mul, star_mul, hstar_r]
        _ = (algebraMap ℝ E r * u + u * algebraMap ℝ E r) + u * u := by noncomm_ring
        _ = (2 * r) • u + u * u := by rw [hcomm]
    have htu2 : t (u * u) = 0 := by
      have h0 : t (star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r)) = 0 := by
        rw [map_sub, htf, sub_self]
      have htu : t u = 0 := by simp [u, htf]
      rwa [hsq, map_add, map_smul, htu, smul_zero, zero_add] at h0
    refine sub_eq_zero.mp (by_contra fun hne ↦ lt_irrefl 0 ?_)
    have hstar_u : star u = -u := by simp [u]
    simpa [hstar_u, htu2] using hpos u hne
  exact ⟨fun r _ ↦ by
    rw [Algebra.smul_def, star_mul, hstar_alg, ← Algebra.commutes, ← Algebra.smul_def,
      star_trivial r]⟩

end TauCeti

namespace AlgHom

/-- On a real star algebra with a linear functional strictly positive on `x * star x`, `star`
acts by complex conjugation on the image of any central `ℝ`-algebra map `f : ℂ →ₐ[ℝ] E`. -/
theorem star_apply_of_mem_center_of_forall_pos_mul_star {E : Type*} [Ring E] [Algebra ℝ E]
    [StarRing E] (f : ℂ →ₐ[ℝ] E) (hf : ∀ z : ℂ, f z ∈ Subalgebra.center ℝ E)
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (z : ℂ) :
    star (f z) = f (star z) := by
  have : StarModule ℝ E := TauCeti.starModule_of_forall_pos_mul_star t hpos
  let w : E := star (f Complex.I)
  have hcomm : f Complex.I * w = w * f Complex.I :=
    (Subalgebra.mem_center_iff.mp (hf Complex.I) w).symm
  have hfI2 : f Complex.I * f Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hw2 : w * w = -1 := by rw [← star_mul, hfI2, star_neg, star_one]
  let v : E := f Complex.I + w
  let u : E := 1 - f Complex.I * w
  have hv_star : star v = v := by simp [v, w, add_comm]
  have hu_star : star u = u := by simp [u, w, hcomm]
  have hsum : v * star v + u * star u = 0 := by
    calc v * star v + u * star u
      _ = (f Complex.I + w) * (f Complex.I + w) +
            (1 - f Complex.I * w) * (1 - f Complex.I * w) := by rw [hv_star, hu_star]
      _ = (f Complex.I * f Complex.I + 1) + (w * w + 1) + (w * f Complex.I - f Complex.I * w) +
            ((f Complex.I * w) * (f Complex.I * w) - 1) := by noncomm_ring
      _ = (f Complex.I * f Complex.I + 1) + (w * w + 1) + (w * f Complex.I - f Complex.I * w) +
            ((f Complex.I * f Complex.I) * (w * w) - 1) := by
          rw [mul_assoc, ← mul_assoc w, ← hcomm, mul_assoc, ← mul_assoc]
      _ = 0 := by rw [hfI2, hw2, ← hcomm]; simp
  have hv0 : v = 0 := by_contra fun hvne ↦ by
    have htu : 0 ≤ t (u * star u) := by
      rcases eq_or_ne u 0 with hu0 | hune <;> [simp [hu0]; exact (hpos u hune).le]
    have hlt : 0 < t (v * star v + u * star u) := by
      rw [map_add]; exact add_pos_of_pos_of_nonneg (hpos v hvne) htu
    rw [hsum, map_zero] at hlt
    exact lt_irrefl 0 hlt
  have hstar_I : star (f Complex.I) = -(f Complex.I) := eq_neg_of_add_eq_zero_right hv0
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp [Complex.real_smul]
  rw [hz]
  simp only [map_add, map_smul, map_one, star_add, star_smul, star_trivial, star_one, hstar_I,
    Complex.star_def, Complex.conj_I, smul_neg, map_neg]

end AlgHom

