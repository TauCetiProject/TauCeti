/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.LinearAlgebra.Charpoly.Invertible
public import TauCeti.LinearAlgebra.Charpoly.Trace
public import TauCeti.LinearAlgebra.Determinant.Idempotent

/-!
# Recovering the rank of a projection from a raising operator

Suppose `T * adjoint T = d • (1 + c • e)` on a finite-dimensional real or complex inner
product space, where `e` is idempotent and `c`, `d` are real. Taking determinants gives
`‖det T‖² = |d| ^ dim M * |1 + c| ^ dim (range e)`.

If `d ≠ 0`, `0 < 1 + c` and `c ≠ 0`, equal characteristic polynomials of two such operators
force equal ranks of the projections. Equal positive power traces suffice as well: the
relation makes both operators invertible, so those traces recover their dimensions.
The spaces may have different dimensions initially, and no self-adjointness of the
idempotents or normality of the raising operators is assumed.

This is the rank-recovery step of `New.LineRelation.trace_mul_mean_eq` in
`src/Lib/Adelic/TraceFormula/LineDeterminant.lean` of grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
In the trace comparison it is applied on the nonzero generalized eigenspaces of a commuting
operator. The formalization here uses Newton's identities and the determinant formula for
idempotents, without spectral decomposition of the raising operator.
-/

public section

namespace LinearMap

variable {𝕜 M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [FiniteDimensional 𝕜 N]

/-- The determinant identity for a raising operator whose product with its adjoint is a
scalar perturbation of an idempotent. No sign assumptions on the real scalars are needed. -/
theorem norm_det_sq_of_mul_adjoint_eq {T e : Module.End 𝕜 M} (he : IsIdempotentElem e)
    {d c : ℝ} (h : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e)) :
    ‖T.det‖ ^ 2 = |d| ^ Module.finrank 𝕜 M *
      |1 + c| ^ Module.finrank 𝕜 (range e) := by
  have hdet := congrArg (fun f : Module.End 𝕜 M ↦ ‖f.det‖) h
  rw [map_mul, det_adjoint, norm_mul, norm_star, ← pow_two] at hdet
  rw [det_smul, det_one_add_smul_of_isIdempotentElem he, norm_mul, norm_pow, norm_pow] at hdet
  have hcast : (1 : 𝕜) + (c : 𝕜) = ((1 + c : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_add, RCLike.ofReal_one]
  simpa only [hcast, RCLike.norm_ofReal] using hdet

/-- A raising operator in the projection relation has nonzero determinant when neither scalar
eigenvalue of its product with its adjoint vanishes. -/
theorem det_ne_zero_of_mul_adjoint_eq {T e : Module.End 𝕜 M} (he : IsIdempotentElem e)
    {d c : ℝ} (hd : d ≠ 0) (hc : 1 + c ≠ 0)
    (h : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e)) : T.det ≠ 0 := by
  have hnorm := norm_det_sq_of_mul_adjoint_eq he h
  have hpos : 0 < |d| ^ Module.finrank 𝕜 M * |1 + c| ^ Module.finrank 𝕜 (range e) :=
    mul_pos (pow_pos (abs_pos.mpr hd) _) (pow_pos (abs_pos.mpr hc) _)
  intro hzero
  rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  exact (ne_of_gt hpos) hnorm.symm

/-- For two raising operators satisfying the same projection relation, their characteristic
polynomials determine the ranks of the projections if `d ≠ 0`, `1 + c > 0` and `c ≠ 0`. -/
theorem finrank_range_eq_of_charpoly_eq_of_mul_adjoint_eq
    {T e : Module.End 𝕜 M} {S f : Module.End 𝕜 N}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    {d c : ℝ} (hd : d ≠ 0) (hc : 0 < 1 + c) (hc0 : c ≠ 0)
    (hT : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e))
    (hS : S * adjoint S = (d : 𝕜) • (1 + (c : 𝕜) • f))
    (hpoly : T.charpoly = S.charpoly) :
    Module.finrank 𝕜 (range e) = Module.finrank 𝕜 (range f) := by
  have hdim : Module.finrank 𝕜 M = Module.finrank 𝕜 N := by
    rw [← T.charpoly_natDegree, ← S.charpoly_natDegree, hpoly]
  have hnorm : |1 + c| ^ Module.finrank 𝕜 (range e) =
      |1 + c| ^ Module.finrank 𝕜 (range f) := by
    apply mul_left_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hd))
    rw [← norm_det_sq_of_mul_adjoint_eq he hT, hdim,
      ← norm_det_sq_of_mul_adjoint_eq hf hS, det_eq_of_charpoly_eq hpoly]
  rw [abs_of_pos hc] at hnorm
  apply (pow_right_injective₀ hc (by simpa using hc0)) hnorm

/-- Positive power traces recover the rank of the projection in the raising-operator relation,
without requiring the two ambient spaces to have the same dimension. -/
theorem finrank_range_eq_of_trace_pow_eq_of_mul_adjoint_eq
    {T e : Module.End 𝕜 M} {S f : Module.End 𝕜 N}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    {d c : ℝ} (hd : d ≠ 0) (hc : 0 < 1 + c) (hc0 : c ≠ 0)
    (hT : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e))
    (hS : S * adjoint S = (d : 𝕜) • (1 + (c : 𝕜) • f))
    (htrace : ∀ j, 0 < j → trace 𝕜 M (T ^ j) = trace 𝕜 N (S ^ j)) :
    Module.finrank 𝕜 (range e) = Module.finrank 𝕜 (range f) := by
  have hTdet := det_ne_zero_of_mul_adjoint_eq he hd hc.ne' hT
  have hSdet := det_ne_zero_of_mul_adjoint_eq hf hd hc.ne' hS
  exact finrank_range_eq_of_charpoly_eq_of_mul_adjoint_eq he hf hd hc hc0 hT hS
    (charpoly_eq_of_trace_pow_eq_of_det_ne_zero hTdet hSdet htrace)

end LinearMap
