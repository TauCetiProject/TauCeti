/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.LinearAlgebra.Charpoly.Trace
import TauCeti.LinearAlgebra.Determinant.Idempotent
import TauCeti.LinearAlgebra.Eigenspace.Trace

/-!
# Traces from a raising operator satisfying a line relation

Let `E` be a finite-dimensional inner product space over `𝕜 = ℝ` or `ℂ`, `T` an endomorphism of
`E` (a *raising operator*) with adjoint `T†` (the *lowering operator*), and `e` an idempotent, such
that the **line relation**

`T T† = d (1 + c e)`

holds for scalars `d` and `c` (`TauCeti.IsLineRelation T e d c`). This is the shape of the relation
between the two Hecke operators of the stabiliser of a line modulo a uniformiser in `GL_n` of a
local field, on the vectors fixed by that stabiliser: `e` is the mean over `GL_n` of the integers,
`d = q ^ (n - 2)` and `c = q ^ n - 1`.

On a complex space, the trace of `A e` for an operator `A` commuting with `T` and `T†` is
determined by the traces of the operators `A ^ l T ^ i` with `l, i ≥ 1`, although these involve
neither `T†` nor `e` (`TauCeti.IsLineRelation.trace_mul_eq_of_trace_pow_mul_pow_eq`). This recovers
traces on the vectors fixed by a maximal compact subgroup from traces on the vectors fixed by the
smaller stabiliser of a line. The argument runs through the generalized eigenspaces `E_α` of `A`,
which `T`, `T†` and `e` preserve.

* For `X` commuting with `A`, `tr (A ^ l X) = ∑_α α ^ l tr (X|E_α)`, and distinct `α` give linearly
  independent sequences `l ↦ α ^ l`. So the traces of `A ^ l T ^ i` determine the traces of the
  positive powers of `T` on each `E_α` with `α ≠ 0`
  (`Module.End.trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq`).
* On `E_α` the line relation still holds (`TauCeti.IsLineRelation.restrict`), so
  `|det T|² = det (T T†) = d ^ dim E_α (1 + c) ^ r_α` with `r_α` the rank of `e` there
  (`TauCeti.IsLineRelation.star_det_mul_det`). In particular `T` is injective on `E_α`, so the
  traces of its positive powers determine its characteristic polynomial, hence `dim E_α` and
  `det T`, hence `r_α` (`TauCeti.IsLineRelation.finrank_range_eq_of_trace_pow_succ_eq`).
* Finally `tr (A e) = ∑_α α r_α`.

The hypotheses on the scalars are `d ≠ 0`, `1 + c ≠ 0` and `‖1 + c‖ ≠ 1`, the last so that
`(1 + c) ^ r` determines `r`; they hold for `d, c > 0`.

## Main definitions

* `TauCeti.IsLineRelation T e d c`: `e` is idempotent and `T T† = d • (1 + c • e)`.

## Main results

* `TauCeti.IsLineRelation.star_det_mul_det`: `conj (det T) * det T = d ^ dim E * (1 + c) ^ rank e`.
* `TauCeti.IsLineRelation.injective`: `T` is injective when `d ≠ 0` and `1 + c ≠ 0`.
* `TauCeti.IsLineRelation.finrank_range_eq_of_trace_pow_succ_eq`: two complex line relations with
  the same scalars whose raising operators have the same traces of positive powers have
  idempotents of the same rank.
* `TauCeti.IsLineRelation.trace_mul_eq_of_trace_pow_mul_pow_eq`: for two complex line relations
  with the same scalars and operators `A`, `A'` commuting with the raising and lowering operators,
  equal traces of `A ^ l T ^ i` and `A' ^ l T' ^ i` for all `l, i ≥ 1` give
  `tr (A e) = tr (A' e')`.

## Provenance

The notion and the comparison of traces correspond to `New.LineRelation` and
`New.LineRelation.trace_mul_mean_eq` of the shorter formal proof [ShortProof]
(`Lib/Adelic/TraceFormula/LineDeterminant.lean` in grh-lean, https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), whose argument through generalized eigenspaces and
`|det T|² = det (T T†)` is the one followed here; the Lean proofs here are written independently.
-/

public section

open Module LinearMap Function

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The **line relation** for an endomorphism `T` of a finite-dimensional inner product space, an
endomorphism `e` and scalars `d`, `c`: `e` is idempotent and `T T† = d (1 + c e)`, where `T†` is
the adjoint of `T`. -/
structure IsLineRelation (T e : Module.End 𝕜 E) (d c : 𝕜) : Prop where
  /-- The endomorphism `e` is idempotent. -/
  isIdempotentElem : IsIdempotentElem e
  /-- The raising operator times its adjoint is `d (1 + c e)`. -/
  mul_adjoint : T * adjoint T = d • (1 + c • e)

namespace IsLineRelation

variable {T e : Module.End 𝕜 E} {d c : 𝕜}

/-- An endomorphism commuting with the raising operator `T` and with its adjoint commutes with
the idempotent of a line relation, when `d ≠ 0` and `c ≠ 0`: `e` is a combination of `1` and
`T T†`. -/
theorem commute_of_commute_of_commute_adjoint (h : IsLineRelation T e d c) (hd : d ≠ 0)
    (hc : c ≠ 0) {A : Module.End 𝕜 E} (hAT : Commute A T) (hAT' : Commute A (adjoint T)) :
    Commute A e := by
  have he : e = (d * c)⁻¹ • (T * adjoint T - d • 1) := by
    rw [h.mul_adjoint, smul_add, add_sub_cancel_left, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero hd hc), one_smul]
  rw [he]
  exact ((hAT.mul_right hAT').sub_right ((Commute.one_right A).smul_right d)).smul_right _

/-- The line relation restricts to a subspace invariant under the raising operator, its adjoint
and the idempotent. -/
theorem restrict (h : IsLineRelation T e d c) {W : Submodule 𝕜 E} (hT : ∀ x ∈ W, T x ∈ W)
    (hT' : ∀ x ∈ W, adjoint T x ∈ W) (he : ∀ x ∈ W, e x ∈ W) :
    IsLineRelation (T.restrict hT) (e.restrict he) d c where
  isIdempotentElem := LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun h.isIdempotentElem x)
  mul_adjoint := by
    rw [adjoint_restrict hT hT']
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    have hx := LinearMap.congr_fun h.mul_adjoint x
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
      one_apply_eq_self] at hx
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
      one_apply_eq_self, coe_restrict_apply, Submodule.coe_smul, Submodule.coe_add, hx]

/-- **The determinant of the raising operator.** Under the line relation `T T† = d (1 + c e)`,
`conj (det T) * det T = d ^ dim E * (1 + c) ^ r`, with `r` the rank of the idempotent `e`. -/
theorem star_det_mul_det (h : IsLineRelation T e d c) :
    star (LinearMap.det T) * LinearMap.det T =
      d ^ finrank 𝕜 E * (1 + c) ^ finrank 𝕜 (range e) := by
  rw [← det_adjoint, mul_comm, ← map_mul, h.mul_adjoint, det_smul,
    det_one_add_smul_of_isIdempotentElem h.isIdempotentElem]

/-- Under the line relation with `d ≠ 0` and `1 + c ≠ 0`, the raising operator is injective: its
determinant does not vanish. -/
theorem injective (h : IsLineRelation T e d c) (hd : d ≠ 0) (hc : 1 + c ≠ 0) : Injective T := by
  have hdet : LinearMap.det T ≠ 0 := fun h0 ↦ by
    have := h.star_det_mul_det
    rw [h0, mul_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hc) this.symm
  exact ((Module.End.isUnit_iff T).mp
    ((LinearMap.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hdet))).injective

end IsLineRelation

/-! ### Complex line relations -/

variable {M M' : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup M'] [InnerProductSpace ℂ M'] [FiniteDimensional ℂ M']

namespace IsLineRelation

variable {T e : Module.End ℂ M} {d c : ℂ}

/-- **The rank of the idempotent from the traces of the raising operator.** For two line
relations `T T† = d (1 + c e)` and `T' T'† = d (1 + c e')` with the same scalars, `d ≠ 0`,
`1 + c ≠ 0` and `‖1 + c‖ ≠ 1`, if the positive powers of `T` and `T'` have the same traces, then
`e` and `e'` have the same rank. -/
theorem finrank_range_eq_of_trace_pow_succ_eq {T' e' : Module.End ℂ M'}
    (h : IsLineRelation T e d c) (h' : IsLineRelation T' e' d c) (hd : d ≠ 0) (hc₀ : 1 + c ≠ 0)
    (hc₁ : ‖1 + c‖ ≠ 1) (htr : ∀ i : ℕ, trace ℂ M (T ^ (i + 1)) = trace ℂ M' (T' ^ (i + 1))) :
    finrank ℂ (range e) = finrank ℂ (range e') := by
  have hcp := charpoly_eq_of_injective_of_trace_pow_succ_eq (h.injective hd hc₀)
    (h'.injective hd hc₀) htr
  have hdim : finrank ℂ M = finrank ℂ M' := by
    rw [← T.charpoly_natDegree, hcp, T'.charpoly_natDegree]
  have hpow : d ^ finrank ℂ M * (1 + c) ^ finrank ℂ (range e) =
      d ^ finrank ℂ M' * (1 + c) ^ finrank ℂ (range e') := by
    rw [← h.star_det_mul_det, ← h'.star_det_mul_det, det_eq_of_charpoly_eq hcp]
  rw [hdim] at hpow
  have hnorm := congrArg norm (mul_left_cancel₀ (pow_ne_zero _ hd) hpow)
  rw [norm_pow, norm_pow] at hnorm
  exact pow_right_injective₀ (norm_pos_iff.mpr hc₀) hc₁ hnorm

/-- **Traces from a raising operator.** Let `T T† = d (1 + c e)` and `T' T'† = d (1 + c e')` be
line relations on complex spaces with the same scalars, `d ≠ 0`, `1 + c ≠ 0` and `‖1 + c‖ ≠ 1`,
and let `A`, `A'` be endomorphisms commuting with `T`, `T†` and with `T'`, `T'†` respectively. If
`tr (A ^ l T ^ i) = tr (A' ^ l T' ^ i)` for all `l, i ≥ 1`, then `tr (A e) = tr (A' e')`. -/
theorem trace_mul_eq_of_trace_pow_mul_pow_eq {T' e' : Module.End ℂ M'}
    (h : IsLineRelation T e d c) (h' : IsLineRelation T' e' d c) (hd : d ≠ 0) (hc₀ : 1 + c ≠ 0)
    (hc₁ : ‖1 + c‖ ≠ 1) {A : Module.End ℂ M} {A' : Module.End ℂ M'} (hAT : Commute A T)
    (hAT' : Commute A (adjoint T)) (hA'T : Commute A' T') (hA'T' : Commute A' (adjoint T'))
    (htr : ∀ l i : ℕ,
      trace ℂ M (A ^ (l + 1) * T ^ (i + 1)) = trace ℂ M' (A' ^ (l + 1) * T' ^ (i + 1))) :
    trace ℂ M (A * e) = trace ℂ M' (A' * e') := by
  classical
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hc₁
  have hAe := h.commute_of_commute_of_commute_adjoint hd hc hAT hAT'
  have hA'e' := h'.commute_of_commute_of_commute_adjoint hd hc hA'T hA'T'
  let s := A.finite_hasEigenvalue.toFinset ∪ A'.finite_hasEigenvalue.toFinset
  have hs : ∀ α, A.HasEigenvalue α → α ∈ s := fun α hα ↦
    Finset.mem_union_left _ (A.finite_hasEigenvalue.mem_toFinset.mpr hα)
  have hs' : ∀ α, A'.HasEigenvalue α → α ∈ s := fun α hα ↦
    Finset.mem_union_right _ (A'.finite_hasEigenvalue.mem_toFinset.mpr hα)
  have hW (α : ℂ) := h.restrict (A.mapsTo_maxGenEigenspace_of_comm hAT α)
    (A.mapsTo_maxGenEigenspace_of_comm hAT' α) (A.mapsTo_maxGenEigenspace_of_comm hAe α)
  have hW' (α : ℂ) := h'.restrict (A'.mapsTo_maxGenEigenspace_of_comm hA'T α)
    (A'.mapsTo_maxGenEigenspace_of_comm hA'T' α) (A'.mapsTo_maxGenEigenspace_of_comm hA'e' α)
  -- On the generalized `α`-eigenspaces with `α ≠ 0`, the idempotents have the same rank.
  have hrank (α : ℂ) (hα₀ : α ≠ 0) :
      finrank ℂ (range (e.restrict (A.mapsTo_maxGenEigenspace_of_comm hAe α))) =
        finrank ℂ (range (e'.restrict (A'.mapsTo_maxGenEigenspace_of_comm hA'e' α))) := by
    refine (hW α).finrank_range_eq_of_trace_pow_succ_eq (hW' α) hd hc₀ hc₁ fun i ↦ ?_
    have hp : T.restrict (A.mapsTo_maxGenEigenspace_of_comm hAT α) ^ (i + 1) =
        (T ^ (i + 1)).restrict (A.mapsTo_maxGenEigenspace_of_comm (hAT.pow_right _) α) :=
      Module.End.pow_restrict _ _ _
    have hp' : T'.restrict (A'.mapsTo_maxGenEigenspace_of_comm hA'T α) ^ (i + 1) =
        (T' ^ (i + 1)).restrict (A'.mapsTo_maxGenEigenspace_of_comm (hA'T.pow_right _) α) :=
      Module.End.pow_restrict _ _ _
    rw [hp, hp']
    exact Module.End.trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq
      (hAT.pow_right _) (hA'T.pow_right _) (fun l ↦ htr l i) hα₀
  have hsum := Module.End.trace_pow_mul_eq_sum hAe s hs 1
  have hsum' := Module.End.trace_pow_mul_eq_sum hA'e' s hs' 1
  rw [pow_one] at hsum hsum'
  rw [hsum, hsum']
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rcases eq_or_ne α 0 with rfl | hα₀
  · simp
  · rw [(IsIdempotentElem.isProj_range _ (hW α).isIdempotentElem).trace,
      (IsIdempotentElem.isProj_range _ (hW' α).isIdempotentElem).trace, hrank α hα₀]

end IsLineRelation

end TauCeti
