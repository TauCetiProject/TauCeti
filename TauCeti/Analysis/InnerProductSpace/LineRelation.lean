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
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.LinearAlgebra.Eigenspace.Trace

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

## Traces from a raising operator

On a complex space, let `A` commute with `T` and with `adjoint T`. Then `A` commutes with `e`,
since `e` is a combination of `1` and `T * adjoint T`, and the trace of `A * e` is determined by
the traces of the operators `A ^ l * T ^ i` with `l, i ≥ 1`, although these involve neither
`adjoint T` nor `e` (`LinearMap.trace_mul_eq_of_trace_pow_mul_pow_eq_of_mul_adjoint_eq`). The
argument runs through the generalized eigenspaces `M_α` of `A`, which `T`, `adjoint T` and `e`
preserve.

* For `X` commuting with `A`, `tr (A ^ l * X) = ∑ α, α ^ l * tr (X|M_α)`, so the traces of
  `A ^ l * T ^ i` determine the traces of the positive powers of `T` on each `M_α` with `α ≠ 0`
  (`Module.End.trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq`).
* The relation restricts to `M_α`
  (`LinearMap.restrict_mul_adjoint_restrict_eq_of_mul_adjoint_eq`), so by the rank recovery above
  the rank `r_α` of `e` on `M_α` is determined.
* Finally `tr (A * e) = ∑ α, α * r_α`.

This is the assembly of `New.LineRelation.trace_mul_mean_eq`, whose argument through generalized
eigenspaces is the one followed here; the Lean proofs are written independently.
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

namespace LinearMap

variable {𝕜 M : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
  [FiniteDimensional 𝕜 M]

/-- An endomorphism commuting with a raising operator `T` and with its adjoint commutes with the
idempotent of the relation `T * adjoint T = d • (1 + c • e)` when `d ≠ 0` and `c ≠ 0`: `e` is a
combination of `1` and `T * adjoint T`. -/
theorem commute_of_mul_adjoint_eq {T e A : Module.End 𝕜 M} {d c : ℝ} (hd : d ≠ 0) (hc : c ≠ 0)
    (h : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e)) (hAT : Commute A T)
    (hAT' : Commute A (adjoint T)) : Commute A e := by
  have hdc : (d : 𝕜) * c ≠ 0 :=
    mul_ne_zero (RCLike.ofReal_ne_zero.mpr hd) (RCLike.ofReal_ne_zero.mpr hc)
  have he : e = ((d : 𝕜) * c)⁻¹ • (T * adjoint T - (d : 𝕜) • 1) := by
    rw [h, smul_add, add_sub_cancel_left, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hdc,
      one_smul]
  rw [he]
  exact ((hAT.mul_right hAT').sub_right ((Commute.one_right A).smul_right _)).smul_right _

/-- The relation `T * adjoint T = d • (1 + c • e)` restricts to a subspace invariant under the
raising operator, its adjoint and the idempotent. -/
theorem restrict_mul_adjoint_restrict_eq_of_mul_adjoint_eq {T e : Module.End 𝕜 M} {d c : ℝ}
    (h : T * adjoint T = (d : 𝕜) • (1 + (c : 𝕜) • e)) {W : Submodule 𝕜 M}
    (hT : ∀ x ∈ W, T x ∈ W) (hT' : ∀ x ∈ W, adjoint T x ∈ W) (he : ∀ x ∈ W, e x ∈ W) :
    T.restrict hT * adjoint (T.restrict hT) = (d : 𝕜) • (1 + (c : 𝕜) • e.restrict he) := by
  rw [adjoint_restrict hT hT']
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  have hx := LinearMap.congr_fun h x
  simp only [mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
    one_apply_eq_self] at hx
  simp only [mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
    one_apply_eq_self, coe_restrict_apply, Submodule.coe_smul, Submodule.coe_add, hx]

end LinearMap

namespace LinearMap

variable {M N : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]

/-- **Traces from a raising operator.** Let `T * adjoint T = d • (1 + c • e)` and
`S * adjoint S = d • (1 + c • f)` with idempotents `e`, `f` on complex spaces, the same real
scalars, `d ≠ 0`, `1 + c > 0` and `c ≠ 0`, and let `A` commute with `T` and `adjoint T` and `B`
with `S` and `adjoint S`. If `tr (A ^ l * T ^ i) = tr (B ^ l * S ^ i)` for all `l, i ≥ 1`, then
`tr (A * e) = tr (B * f)`. -/
theorem trace_mul_eq_of_trace_pow_mul_pow_eq_of_mul_adjoint_eq
    {T e A : Module.End ℂ M} {S f B : Module.End ℂ N}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    {d c : ℝ} (hd : d ≠ 0) (hc : 0 < 1 + c) (hc0 : c ≠ 0)
    (hT : T * adjoint T = (d : ℂ) • (1 + (c : ℂ) • e))
    (hS : S * adjoint S = (d : ℂ) • (1 + (c : ℂ) • f))
    (hAT : Commute A T) (hAT' : Commute A (adjoint T))
    (hBS : Commute B S) (hBS' : Commute B (adjoint S))
    (htrace : ∀ l i : ℕ, 0 < l → 0 < i →
      trace ℂ M (A ^ l * T ^ i) = trace ℂ N (B ^ l * S ^ i)) :
    trace ℂ M (A * e) = trace ℂ N (B * f) := by
  classical
  have hAe := commute_of_mul_adjoint_eq hd hc0 hT hAT hAT'
  have hBf := commute_of_mul_adjoint_eq hd hc0 hS hBS hBS'
  let s := A.finite_hasEigenvalue.toFinset ∪ B.finite_hasEigenvalue.toFinset
  have hs : ∀ α, A.HasEigenvalue α → α ∈ s := fun α hα ↦
    Finset.mem_union_left _ (A.finite_hasEigenvalue.mem_toFinset.mpr hα)
  have hs' : ∀ α, B.HasEigenvalue α → α ∈ s := fun α hα ↦
    Finset.mem_union_right _ (B.finite_hasEigenvalue.mem_toFinset.mpr hα)
  have heα (α : ℂ) : IsIdempotentElem (e.restrict (A.mapsTo_maxGenEigenspace_of_comm hAe α)) :=
    LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun he x)
  have hfα (α : ℂ) : IsIdempotentElem (f.restrict (B.mapsTo_maxGenEigenspace_of_comm hBf α)) :=
    LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun hf x)
  -- On the generalized `α`-eigenspaces with `α ≠ 0`, the idempotents have the same rank.
  have hrank (α : ℂ) (hα₀ : α ≠ 0) :
      Module.finrank ℂ (range (e.restrict (A.mapsTo_maxGenEigenspace_of_comm hAe α))) =
        Module.finrank ℂ (range (f.restrict (B.mapsTo_maxGenEigenspace_of_comm hBf α))) := by
    refine finrank_range_eq_of_trace_pow_eq_of_mul_adjoint_eq (heα α) (hfα α) hd hc hc0
      (restrict_mul_adjoint_restrict_eq_of_mul_adjoint_eq hT
        (A.mapsTo_maxGenEigenspace_of_comm hAT α) (A.mapsTo_maxGenEigenspace_of_comm hAT' α) _)
      (restrict_mul_adjoint_restrict_eq_of_mul_adjoint_eq hS
        (B.mapsTo_maxGenEigenspace_of_comm hBS α) (B.mapsTo_maxGenEigenspace_of_comm hBS' α) _)
      fun j hj ↦ ?_
    have hp : T.restrict (A.mapsTo_maxGenEigenspace_of_comm hAT α) ^ j =
        (T ^ j).restrict (A.mapsTo_maxGenEigenspace_of_comm (hAT.pow_right j) α) :=
      Module.End.pow_restrict _ _ _
    have hp' : S.restrict (B.mapsTo_maxGenEigenspace_of_comm hBS α) ^ j =
        (S ^ j).restrict (B.mapsTo_maxGenEigenspace_of_comm (hBS.pow_right j) α) :=
      Module.End.pow_restrict _ _ _
    rw [hp, hp']
    exact Module.End.trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq
      (hAT.pow_right _) (hBS.pow_right _) (fun l ↦ htrace (l + 1) j l.succ_pos hj) hα₀
  have hsum := Module.End.trace_pow_mul_eq_sum hAe s hs 1
  have hsum' := Module.End.trace_pow_mul_eq_sum hBf s hs' 1
  rw [pow_one] at hsum hsum'
  rw [hsum, hsum']
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rcases eq_or_ne α 0 with rfl | hα₀
  · simp
  · rw [(IsIdempotentElem.isProj_range _ (heα α)).trace,
      (IsIdempotentElem.isProj_range _ (hfα α)).trace, hrank α hα₀]

end LinearMap
