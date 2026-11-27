/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.LinearAlgebra.Submodule.Primitive
import TauCeti.RingTheory.Localization.IntegerMultiple

/-!
# Idempotent matrices with integral entries

An idempotent matrix `ε` over a field `K` is the projection onto its column space along its
kernel, and the column space alone determines the matrices `ε * Y * (1 - ε)`, the endomorphisms
that kill the column space and take values in it. When `K` is the fraction field of a Dedekind
domain `R`, the column space of `ε` is also the column space of an idempotent matrix `e` with
entries in `R`: the vectors over `R` fixed by `ε` form a saturated submodule of `Rⁿ`, which has a
complement because its quotient is finitely generated and torsion-free, and `e` is the projection
onto it along that complement. In matrix terms `ε * e = e` and `e * ε = ε`.

Such an integral idempotent can then be reduced modulo an ideal, and its reduction stays nonzero:
over a domain, an idempotent matrix whose image under a ring homomorphism to a nontrivial ring
vanishes is zero.

## Main results

* `IsIdempotentElem.exists_isIdempotentElem_matrix_map`: over the fraction field of a Dedekind
  domain, every idempotent matrix has the column space of an idempotent matrix with integral
  entries.
* `IsIdempotentElem.eq_zero_of_matrix_map_eq_zero`: over a domain, an idempotent matrix whose image
  under a ring homomorphism to a nontrivial ring vanishes is zero.

## References

The complement is provided by `Submodule.exists_isCompl_iff_isTorsionFree_quotient`
(`TauCeti/LinearAlgebra/Submodule/Primitive.lean`), which rests on Mathlib's flatness of
torsion-free modules over a Dedekind domain (`IsDedekindDomain.flat_iff_torsion_eq_bot`) and on
`Module.Flat.projective_of_finitePresentation`.
-/

public section

open Matrix

namespace IsIdempotentElem

variable {n R : Type*} [Fintype n] [CommRing R]

/-- **An idempotent matrix with vanishing reduction is zero.** Over a domain `R`, if an idempotent
matrix `e` maps to `0` under a ring homomorphism to a nontrivial ring, then `e = 0`: the
determinant of `1 - e` maps to `1`, so it is nonzero, and `e * (1 - e) = 0`. -/
theorem eq_zero_of_matrix_map_eq_zero [IsDomain R] {S : Type*} [CommRing S] [Nontrivial S]
    {e : Matrix n n R} (he : IsIdempotentElem e) (f : R →+* S) (h : e.map f = 0) : e = 0 := by
  classical
  have hdet : (1 - e).det ≠ 0 := fun h0 ↦ by
    have h1 := congrArg f h0
    rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply, h, sub_zero, det_one,
      map_zero] at h1
    exact one_ne_zero h1
  have h1 : (1 - e).det • e = 0 :=
    calc (1 - e).det • e = e * ((1 - e) * (1 - e).adjugate) := by
          rw [mul_adjugate, mul_smul_comm, mul_one]
      _ = 0 := by rw [← mul_assoc, he.mul_one_sub_self, zero_mul]
  exact (smul_eq_zero.mp h1).resolve_left hdet

variable [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Integral idempotents with a prescribed column space.** Over the fraction field `K` of a
Dedekind domain `R`, every idempotent matrix `ε` has the column space of an idempotent matrix `e`
with entries in `R`: `ε * e = e` and `e * ε = ε` over `K`. -/
theorem exists_isIdempotentElem_matrix_map {ε : Matrix n n K} (hε : IsIdempotentElem ε) :
    ∃ e : Matrix n n R, IsIdempotentElem e ∧ ε * e.map (algebraMap R K) = e.map (algebraMap R K) ∧
      e.map (algebraMap R K) * ε = ε := by
  classical
  -- The vectors over `R` fixed by `ε` form the kernel of `φ`; its quotient is torsion-free, so it
  -- has a complement, and `e` is the matrix of the projection `P` onto it.
  let φ : (n → R) →ₗ[R] (n → K) :=
    ((ε - 1).mulVecLin.restrictScalars R) ∘ₗ LinearMap.compLeft (Algebra.linearMap R K) n
  have hφ (v : n → R) : φ v = (ε - 1) *ᵥ (algebraMap R K ∘ v) := (rfl)
  have hmap (M : Matrix n n R) (v : n → R) :
      M.map (algebraMap R K) *ᵥ (algebraMap R K ∘ v) = algebraMap R K ∘ (M *ᵥ v) :=
    funext fun i ↦ (RingHom.map_mulVec _ M v i).symm
  have hsingle (j : n) : algebraMap R K ∘ Pi.single j 1 = Pi.single j 1 := by
    ext i
    by_cases h : i = j <;> simp [h]
  have hS : Module.IsTorsionFree R ((n → R) ⧸ LinearMap.ker φ) := by
    refine Submodule.isTorsionFree_quotient_iff.mpr fun c z hc hz ↦ ?_
    rw [LinearMap.mem_ker, map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left hc.ne_zero
  obtain ⟨T, hT⟩ := (Submodule.exists_isCompl_iff_isTorsionFree_quotient _).mpr hS
  set P := (LinearMap.ker φ).projection T hT
  have he (v : n → R) : LinearMap.toMatrix' P *ᵥ v = P v := LinearMap.toMatrix'_mulVec P v
  -- Clear the denominators of `ε`: `N = d • ε` has its columns fixed by `ε`, hence by `P`.
  obtain ⟨d, N, hN⟩ := TauCeti.IsLocalization.exists_matrix_map_eq_smul (nonZeroDivisors R) ε
  have hPN : LinearMap.toMatrix' P * N = N := by
    refine ext_of_mulVec_single fun j ↦ ?_
    rw [← mulVec_mulVec, he]
    refine Submodule.projection_apply_of_mem_left hT ?_
    rw [LinearMap.mem_ker, hφ, ← hmap, hN, hsingle, mulVec_mulVec, mul_smul_comm, sub_mul, hε.eq,
      one_mul, sub_self, smul_zero, zero_mulVec]
  refine ⟨LinearMap.toMatrix' P, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, ← LinearMap.toMatrix'_comp]
    exact congrArg _ (Submodule.isIdempotentElem_projection hT).eq
  · -- The columns of `e` lie in the kernel of `φ`.
    rw [← sub_eq_zero, ← sub_one_mul]
    refine ext_of_mulVec_single fun j ↦ ?_
    rw [← mulVec_mulVec, ← hsingle, hmap, he, ← hφ, zero_mulVec]
    exact Submodule.projection_apply_mem hT _
  · -- Cancel the nonzero scalar `d` from `e * (d • ε) = d • ε`.
    have h := congrArg (Matrix.map · (algebraMap R K)) hPN
    simp only [Matrix.map_mul, hN, mul_smul_comm] at h
    rw [← algebraMap_smul K (d : R), ← algebraMap_smul K (d : R) ε] at h
    exact smul_right_injective _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property) h

end IsIdempotentElem
