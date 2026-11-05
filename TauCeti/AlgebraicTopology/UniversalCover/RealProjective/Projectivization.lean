/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Algebra.Projectivization
import TauCeti.LinearAlgebra.Projectivization.UnitSphere

/-!
# The antipodal quotient and real projectivization

`RealProjectiveSpace.homeomorphProjectivization` identifies the antipodal quotient of
`Sⁿ` with the native projectivization of `Fin (n + 1) → ℝ`. It sends a unit vector to
its line in homogeneous coordinates, forgetting only the `WithLp` type synonym.
The inverse sends any nonzero homogeneous vector to its normalized antipodal class.
The comparison preserves the existing quotient topologies, including in dimension zero.

These representative formulas allow the covering and CW constructions on the sphere
quotient to be used with the homogeneous-coordinate atlas on projectivization.
The construction uses `RealProjectiveSpace.lift`, Mathlib's `Projectivization.mk`,
and the compact-to-Hausdorff homeomorphism theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (real projective space as lines and as the antipodal sphere quotient).
-/

public section

open Metric
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace TauCeti.RealProjectiveSpace

variable (n : ℕ)

/-- The homogeneous coordinates of a unit vector are nonzero. -/
private theorem ofLp_val_ne_zero (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    WithLp.ofLp v.val ≠ 0 :=
  fun h ↦ (ne_zero_of_mem_sphere one_ne_zero v)
    ((WithLp.ofLp_eq_zero (x := v.val) 2).mp h)

/-- Send an antipodal unit-vector class to the line spanned by its homogeneous coordinates. -/
private def toProjectivization : RealProjectiveSpace n → ℙ ℝ (Fin (n + 1) → ℝ) :=
  RealProjectiveSpace.lift n
    (fun v ↦ Projectivization.mk ℝ (WithLp.ofLp v.val) (ofLp_val_ne_zero n v))
    (fun v ↦ (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨-1, by simp⟩)

/-- The comparison sends a unit-vector representative to its projective class. -/
@[simp]
private theorem toProjectivization_mk (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    toProjectivization n (mk n v) =
      Projectivization.mk ℝ (WithLp.ofLp v.val) (ofLp_val_ne_zero n v) :=
  RealProjectiveSpace.lift_mk n _ _ v

/-- The sphere-quotient comparison is continuous for the native quotient topologies. -/
@[fun_prop]
private theorem continuous_toProjectivization : Continuous (toProjectivization n) := by
  apply (isQuotientMap_mk n).continuous_iff.2
  simpa only [Function.comp_def, toProjectivization_mk] using
    (Projectivization.continuous_mk
      ((PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp continuous_subtype_val)
      (ofLp_val_ne_zero n))

/-- Equality of real projective lines identifies precisely the antipodal classes. -/
private theorem toProjectivization_injective : Function.Injective (toProjectivization n) := by
  intro x y h
  obtain ⟨v, rfl⟩ := mk_surjective n x
  obtain ⟨w, rfl⟩ := mk_surjective n y
  rw [toProjectivization_mk, toProjectivization_mk, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have hval : a • w.val = v.val := WithLp.ofLp_injective 2 (by simpa using ha)
  have he : Projectivization.mk ℝ v.val (ne_zero_of_mem_sphere one_ne_zero v) =
      Projectivization.mk ℝ w.val (ne_zero_of_mem_sphere one_ne_zero w) :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨a, hval⟩
  rw [Projectivization.mk_eq_mk_iff_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp w.property)] at he
  exact (mk_eq_mk_iff n v w).2 (he.imp Subtype.ext Subtype.ext)

/-- Every real projective line has a unit-vector representative in the covering sphere. -/
private theorem toProjectivization_surjective : Function.Surjective (toProjectivization n) := by
  intro p
  let v : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 p.rep
  have hv : v ≠ 0 := by simpa [v] using p.rep_ne_zero
  let w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hv)⟩
  refine ⟨mk n w, ?_⟩
  rw [toProjectivization_mk, ← p.mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨‖v‖⁻¹, by simp [w, v]⟩

/-- The antipodal sphere quotient is homeomorphic to native real projectivization,
with its homogeneous-coordinate topology. -/
def homeomorphProjectivization : RealProjectiveSpace n ≃ₜ ℙ ℝ (Fin (n + 1) → ℝ) :=
  (continuous_toProjectivization n).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (toProjectivization n)
      ⟨toProjectivization_injective n, toProjectivization_surjective n⟩)

/-- The homeomorphism evaluates as the sphere-quotient comparison map. -/
private theorem homeomorphProjectivization_apply (x : RealProjectiveSpace n) :
    homeomorphProjectivization n x = toProjectivization n x :=
  congrArg (fun e : RealProjectiveSpace n ≃ ℙ ℝ (Fin (n + 1) → ℝ) ↦ e x)
    (Continuous.toEquiv_homeoOfEquivCompactToT2 (continuous_toProjectivization n))

/-- The homeomorphism sends a unit vector to the line of its coordinates. -/
@[simp]
theorem homeomorphProjectivization_mk
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    homeomorphProjectivization n (mk n v) =
      Projectivization.mk ℝ (WithLp.ofLp v.val) (by exact ofLp_val_ne_zero n v) := by
  rw [homeomorphProjectivization_apply, toProjectivization_mk]

/-- The inverse comparison recovers the antipodal class of any unit representative. -/
@[simp]
theorem homeomorphProjectivization_symm_mk
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (homeomorphProjectivization n).symm
      (Projectivization.mk ℝ (WithLp.ofLp v.val) (by exact ofLp_val_ne_zero n v)) = mk n v :=
  (homeomorphProjectivization n).symm_apply_eq.mpr (homeomorphProjectivization_mk n v).symm

/-- Inverse homogeneous coordinates: normalize a nonzero vector in the Euclidean norm,
then take its antipodal class. -/
theorem homeomorphProjectivization_symm_mk_eq_normalize
    (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) :
    (homeomorphProjectivization n).symm (Projectivization.mk ℝ v hv) =
      mk n ⟨‖WithLp.toLp 2 v‖⁻¹ • WithLp.toLp 2 v,
        mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (by simpa using hv))⟩ := by
  apply (homeomorphProjectivization n).injective
  rw [Homeomorph.apply_symm_apply, homeomorphProjectivization_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨‖WithLp.toLp 2 v‖, ?_⟩
  simp [smul_smul, norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hv)]

end TauCeti.RealProjectiveSpace
