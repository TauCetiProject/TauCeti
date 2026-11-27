/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.Order.Archimedean.Real.Basic

/-!
# Real-linearity from positive star functionals

On a real star algebra, real-linearity plus strict positivity on `x * star x` forces
`StarModule ℝ E` (`TauCeti.starModule_of_trace_mul_star_pos`).
-/

public section

namespace TauCeti

/-- **Automatic real-linearity of the involution.** Positivity of `t (x * star x)` on nonzero
elements forces `star` to fix every real scalar (`StarModule ℝ E`). -/
theorem starModule_of_trace_mul_star_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
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
    simpa [f, Algebra.algebraMap_eq_smul_one, smul_eq_mul] using f.real_eq_mul_one hmono a
  have hstar_alg (r : ℝ) : star (algebraMap ℝ E r) = algebraMap ℝ E r := by
    set u : E := star (algebraMap ℝ E r) - algebraMap ℝ E r
    have hsq : star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r) =
        (2 * r) • u + u * u := by
      have hmul : (algebraMap ℝ E r + u) * (algebraMap ℝ E r + u) -
          algebraMap ℝ E r * algebraMap ℝ E r =
          algebraMap ℝ E r * u + u * algebraMap ℝ E r + u * u := by noncomm_ring
      rw [map_mul, star_mul, show star (algebraMap ℝ E r) = algebraMap ℝ E r + u by simp [u],
        hmul, (Algebra.commutes r u).symm, ← Algebra.smul_def, two_mul, add_smul]
    have htu2 : t (u * u) = 0 := by
      have h0 : t (star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r)) = 0 := by
        rw [map_sub, htf, sub_self]
      rwa [hsq, map_add, map_smul, show t u = 0 by simp [u, htf], smul_zero, zero_add] at h0
    refine sub_eq_zero.mp (by_contra fun hne ↦ lt_irrefl 0 ?_)
    simpa [show star u = -u by simp [u], htu2] using hpos u hne
  exact ⟨fun r _ ↦ by
    rw [Algebra.smul_def, star_mul, hstar_alg, ← Algebra.commutes, ← Algebra.smul_def,
      star_trivial r]⟩

end TauCeti
