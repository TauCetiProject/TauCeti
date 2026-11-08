/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

/-!
# Degenerate functions of the height on the sphere

Let `h` be the height function on the unit sphere `Sⁿ` in the direction of a unit vector `v`
(`TauCeti.sphereHeight`). For a differentiable `φ : ℝ → ℝ` the differential of `φ ∘ h` is
`φ'(h) dh`, so the critical points of `φ ∘ h` are the two poles `v` and `-v` together with the
points whose height is a critical point of `φ` (`TauCeti.criticalPoints_comp_sphereHeight`). At a
pole where `φ' = 0` the critical Hessian of `φ ∘ h` vanishes. This gives two test functions for
statements about smooth functions with few critical points.

* **A function with two degenerate critical points.** For `f = h - h³ / 3` the differential is
  `(1 - h²) dh`, and `h = ±1` only at the poles, so the critical points of `f` are exactly the two
  poles (`TauCeti.criticalPoints_cubic_comp_sphereHeight`) and `f` has two critical points
  (`TauCeti.totalCriticalCount_cubic_comp_sphereHeight`). Both critical Hessians vanish
  (`TauCeti.criticalHessian_cubic_comp_sphereHeight_self` and
  `TauCeti.criticalHessian_cubic_comp_sphereHeight_neg`), so in positive dimension `f` is not a
  Morse function (`TauCeti.not_isMorse_cubic_comp_sphereHeight`). So `f` has exactly two critical
  points but lies outside the scope of Reeb's theorem for Morse functions
  (`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`) and of any argument
  through nondegenerate normal forms: it is the test case for the sphere theorem for smooth
  functions with two possibly degenerate critical points.
* **Two critical values but many critical points.** For `f = h²` the critical set is the two poles
  together with the whole equator `h = 0` (`TauCeti.criticalPoints_sq_comp_sphereHeight`). On `Sⁿ`
  with `n ≥ 2` the equator is infinite, so `f` has infinitely many critical points
  (`TauCeti.totalCriticalCount_sq_comp_sphereHeight_of_two_le`), and on the circle it has four
  (`TauCeti.totalCriticalCount_sq_comp_sphereHeight_of_eq_one`). So `f` has two critical values
  but never exactly two critical points in positive dimension: a count of critical values cannot
  replace the count of critical points in such a theorem.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1 after it.
-/

public section

open Set Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {φ : ℝ → ℝ}

/-- The critical points of a function `φ ∘ h` of the height `h` are the two poles together with
the points whose height is a critical point of `φ`, that is, a value at which `φ'` vanishes. -/
theorem criticalPoints_comp_sphereHeight (hφ : Differentiable ℝ φ) (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) (φ ∘ sphereHeight v) =
      sphereHeight v ⁻¹' {t | deriv φ t = 0} ∪ {v, -v} := by
  rw [criticalPoints_scalar_comp ((contMDiff_sphereHeight v).mdifferentiable one_ne_zero) hφ,
    criticalPoints_sphereHeight]

/-- At a pole whose height is a critical point of `φ`, the critical Hessian of `φ ∘ h`
vanishes. -/
theorem criticalHessian_comp_sphereHeight_eq_zero {v x : sphere (0 : E) 1}
    (hφ : ContDiffAt ℝ 2 φ (sphereHeight v x)) (hx : x = v ∨ x = -v)
    (hφ' : deriv φ (sphereHeight v x) = 0) :
    criticalHessian (𝓡 n) (φ ∘ sphereHeight v) x = 0 := by
  rw [criticalHessian_scalar_comp (contMDiff_sphereHeight v x) hφ
    (by rw [criticalPoints_sphereHeight]; exact hx), hφ']
  ext u w
  simp

/-! ### The function `h - h³ / 3` -/

/-- The derivative of `t - t³ / 3` is `1 - t²`. -/
private theorem deriv_cubic (t : ℝ) : deriv (fun s : ℝ ↦ s - s ^ 3 / 3) t = 1 - t ^ 2 := by
  refine HasDerivAt.deriv ?_
  convert (hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 3) using 1
  ring

/-- **The critical points of `h - h³ / 3` are the two poles.** -/
theorem criticalPoints_cubic_comp_sphereHeight (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) = {v, -v} := by
  rw [criticalPoints_comp_sphereHeight (by fun_prop), union_eq_right]
  intro x hx
  have hx' : (sphereHeight v x - 1) * (sphereHeight v x + 1) = 0 := by
    rw [mem_preimage, mem_ofPred_eq, deriv_cubic] at hx
    linear_combination -hx
  rcases mul_eq_zero.1 hx' with hx | hx
  · exact .inl (sphereHeight_eq_one_iff.1 (sub_eq_zero.1 hx))
  · exact .inr (sphereHeight_eq_neg_one_iff.1 (eq_neg_of_add_eq_zero_left hx))

/-- **The function `h - h³ / 3` has exactly two critical points.** -/
theorem totalCriticalCount_cubic_comp_sphereHeight (v : sphere (0 : E) 1) :
    totalCriticalCount (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) = 2 := by
  rw [totalCriticalCount_def, criticalPoints_cubic_comp_sphereHeight,
    encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]

/-- The critical Hessian of `h - h³ / 3` vanishes at the north pole. -/
theorem criticalHessian_cubic_comp_sphereHeight_self (v : sphere (0 : E) 1) :
    criticalHessian (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) v = 0 :=
  criticalHessian_comp_sphereHeight_eq_zero (by fun_prop) (.inl rfl) (by simp [deriv_cubic])

/-- The critical Hessian of `h - h³ / 3` vanishes at the south pole. -/
theorem criticalHessian_cubic_comp_sphereHeight_neg (v : sphere (0 : E) 1) :
    criticalHessian (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) (-v) = 0 :=
  criticalHessian_comp_sphereHeight_eq_zero (by fun_prop) (.inr rfl) (by simp [deriv_cubic])

/-- **`h - h³ / 3` is not a Morse function** on a sphere of positive dimension: its critical points
are degenerate. -/
theorem not_isMorse_cubic_comp_sphereHeight (hn : n ≠ 0) (v : sphere (0 : E) 1) :
    ¬IsMorse (𝓡 n) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) := fun hf ↦ by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [Nat.pos_of_ne_zero hn])
  refine (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    ?_).criticalHessian_ne_zero (criticalHessian_cubic_comp_sphereHeight_self v)
  rw [criticalPoints_cubic_comp_sphereHeight]
  exact mem_insert v _

/-! ### The function `h²` -/

/-- **The critical points of `h²` are the two poles and the equator.** -/
theorem criticalPoints_sq_comp_sphereHeight (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) =
      {x | sphereHeight v x = 0} ∪ {v, -v} := by
  rw [criticalPoints_comp_sphereHeight (by fun_prop)]
  congr 1
  ext x
  simp

/-- **On a sphere of dimension at least two, `h²` has infinitely many critical points.** -/
theorem totalCriticalCount_sq_comp_sphereHeight_of_two_le (hn : 2 ≤ n) (v : sphere (0 : E) 1) :
    totalCriticalCount (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) = ⊤ := by
  rw [totalCriticalCount_def, criticalPoints_sq_comp_sphereHeight, Set.encard_eq_top_iff]
  exact (infinite_setOf_sphereHeight_eq_zero (by rw [Fact.out (p := finrank ℝ E = n + 1)]; omega)
    v).mono subset_union_left

/-- **On the circle, `h²` has four critical points:** the two poles and the two points of the
equator. -/
theorem totalCriticalCount_sq_comp_sphereHeight_of_eq_one (hn : n = 1) (v : sphere (0 : E) 1) :
    totalCriticalCount (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) = 4 := by
  have hE : finrank ℝ E = 2 := by rw [Fact.out (p := finrank ℝ E = n + 1), hn]
  have hdisj : Disjoint {x | sphereHeight v x = 0} {v, -v} := by
    refine disjoint_left.2 fun x hx hx' ↦ ?_
    rcases hx' with rfl | rfl <;> simp_all
  have hfin : {x | sphereHeight v x = 0}.Finite :=
    finite_of_ncard_ne_zero (by rw [ncard_setOf_sphereHeight_eq_zero hE]; simp)
  rw [totalCriticalCount_def, criticalPoints_sq_comp_sphereHeight, encard_union_eq hdisj,
    ← hfin.cast_ncard_eq, ncard_setOf_sphereHeight_eq_zero hE,
    encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]
  norm_num

end TauCeti
