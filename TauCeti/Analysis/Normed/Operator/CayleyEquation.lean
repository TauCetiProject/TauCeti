/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.CayleyChart
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# Cayley equation for a real-linear map

`ContinuousLinearMap.complexAntilinearPart_eq_comp_cayleyCoord_iff` expresses
intertwining a real endomorphism with multiplication by `i` as an equation between
the two complex parts of the map. It uses `TauCeti.cayleyCoord_mul_add` to clear
the Cayley denominator. `ContinuousLinearMap.complexAntilinearPart_cayleyCoord_apply` identifies
the Cayley coordinate of a square root of `-1` with its conjugate-linear part.
-/

public section

open Complex TauCeti

namespace ContinuousLinearMap

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- When `i + A` is invertible, a real-linear map `L` intertwines `A` with multiplication
by `i` exactly when its complex-antilinear part is its complex-linear part
precomposed with the Cayley coordinate of `A`. -/
theorem complexAntilinearPart_eq_comp_cayleyCoord_iff {L : V →L[ℝ] W} {A : V →L[ℝ] V}
    (hA : IsUnit (lsmul ℝ ℂ I + A)) :
    (∀ v, L.complexAntilinearPart v = L.complexLinearPart (cayleyCoord (lsmul ℝ ℂ I) A v)) ↔
      ∀ v, L (A v) = I • L v := by
  have hsurj : Function.Surjective ((lsmul ℝ ℂ I : V →L[ℝ] V) + A) := by
    obtain ⟨u, hu⟩ := hA
    rw [← hu, ← funext (ContinuousLinearEquiv.unitsEquiv_apply ℝ V u)]
    exact (ContinuousLinearEquiv.unitsEquiv ℝ V u).surjective
  have hcomp (v : V) :
      L.complexAntilinearPart (((lsmul ℝ ℂ I : V →L[ℝ] V) + A) v) -
          L.complexLinearPart
            (cayleyCoord (lsmul ℝ ℂ I) A (((lsmul ℝ ℂ I : V →L[ℝ] V) + A) v)) =
        L (A v) - I • L v := by
    have hclear := congrArg (fun T : V →L[ℝ] V ↦ T v) (cayleyCoord_mul_add hA)
    simp only [mul_apply_eq_comp, sub_apply] at hclear
    rw [hclear]
    simp only [add_apply, lsmul_apply, map_add, map_sub, map_smul, map_smulₛₗ,
      Complex.conj_I, neg_smul]
    rw [← L.complexLinearPart_add_complexAntilinearPart_apply (A v),
      ← L.complexLinearPart_add_complexAntilinearPart_apply v, smul_add]
    abel
  constructor
  · intro h v
    exact sub_eq_zero.mp ((hcomp v).symm.trans (sub_eq_zero.mpr (h _)))
  · intro h v
    obtain ⟨w, rfl⟩ := hsurj v
    exact sub_eq_zero.mp ((hcomp w).trans (sub_eq_zero.mpr (h w)))

/-- The Cayley coordinate of a square root of `-1` equals its complex-antilinear part
on every vector. -/
theorem complexAntilinearPart_cayleyCoord_apply {A : V →L[ℝ] V} (hA : A * A = -1) (v : V) :
    (cayleyCoord (lsmul ℝ ℂ I) A).complexAntilinearPart v = cayleyCoord (lsmul ℝ ℂ I) A v := by
  have h := cayleyCoord_mul_eq_neg_mul lsmul_I_mul_lsmul_I hA
  have hC : (cayleyCoord (lsmul ℝ ℂ I) A).complexAntilinearPartL = cayleyCoord (lsmul ℝ ℂ I) A :=
    complexAntilinearPartL_eq_self_iff.2 fun w ↦ by
      simpa only [mul_apply_eq_comp, neg_apply, lsmul_apply] using
        congrArg (fun T : V →L[ℝ] V ↦ T w) h
  rw [complexAntilinearPart_apply, ← complexAntilinearPartL_apply_apply, hC]

end ContinuousLinearMap
