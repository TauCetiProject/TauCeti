/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Thom.Basic
public import TauCeti.FieldTheory.RealClosure.IVT
import TauCeti.Algebra.Polynomial.RealClosed.Sign
import TauCeti.FieldTheory.RealClosure.AbstractRolle
import Mathlib.Data.Finset.Max

/-! # Thom's lemma: sign conditions on all derivatives are open intervals

Over a real closed ordered field, fix signs for every formal derivative of a polynomial `p`,
including `p` itself. The set of points realizing these signs is empty, a single point, or an
open interval whose endpoints are points of the field or infinite
(`Polynomial.preimage_derivativeSign_subsingleton_or_eq_Ioo`). The finite Thom sign conditions,
on the derivatives of orders `1, …, natDegree p`, have the same shape
(`Polynomial.preimage_thomEncoding_subsingleton_or_eq_Ioo`).

`Polynomial.ordConnected_preimage_derivativeSign` already shows that these sets are
order-convex. Over a non-Archimedean real closed field an order-convex set need not have
endpoints in the field, so the existence of the endpoints is the additional content here: when
the condition is realized at two points, the realizing set is a whole interval between
consecutive roots of the nonzero derivatives. Its endpoints are such roots or infinite.
Endpoints are written in `WithBot R` and `WithTop R`, so that `⊥` and `⊤` stand for the two
infinities. No assumption on `p` is needed: the zero polynomial realizes only the zero
condition, on the whole line.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Proposition 2.27 (Thom's lemma).
-/

public section

open Set

open TauCeti.RealClosure (polynomialRolle_of_isRealClosed)

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The roots of the nonzero derivatives of `p`, of every order, form a finite set. -/
theorem finite_setOfPred_isRoot_iterate_derivative (p : R[X]) :
    {z | ∃ k, derivative^[k] p ≠ 0 ∧ (derivative^[k] p).IsRoot z}.Finite := by
  have hk : {k | derivative^[k] p ≠ 0}.Finite := (finite_Iic p.natDegree).subset
    fun k hk ↦ not_lt.1 fun h ↦ hk (iterate_derivative_eq_zero h)
  exact (hk.biUnion fun k hk ↦ finite_setOfPred_isRoot hk).subset
    fun z ⟨k, hk, hz⟩ ↦ mem_biUnion hk hz

end CommRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- If no nonzero derivative of `p`, of any order, has a root between `a` and `b`, then every
derivative of `p` has the same sign at `a` as at `b`. -/
theorem derivativeSign_eq_of_forall_eval_ne_zero (p : R[X]) {a b : R}
    (h : ∀ z ∈ uIcc a b, ∀ k, derivative^[k] p ≠ 0 → (derivative^[k] p).eval z ≠ 0) :
    derivativeSign p a = derivativeSign p b := by
  funext k
  simp only [derivativeSign_def]
  by_cases hk : derivative^[k] p = 0
  · simp [hk]
  rcases le_total a b with hab | hba
  · exact sign_eval_const _ hab fun z hz ↦ h z (Icc_subset_uIcc hz) k hk
  · exact (sign_eval_const _ hba fun z hz ↦ h z (Icc_subset_uIcc' hz) k hk).symm

/-- **Thom's lemma.** For any signs `σ k` prescribed for the derivatives of every order of `p`,
including order zero, the set of points where `p` realizes them is empty, a single point, or an
open interval with endpoints `a ∈ WithBot R` and `b ∈ WithTop R`. -/
theorem preimage_derivativeSign_subsingleton_or_eq_Ioo (p : R[X]) (σ : ℕ → SignType) :
    (derivativeSign p ⁻¹' {σ}).Subsingleton ∨
      ∃ (a : WithBot R) (b : WithTop R), derivativeSign p ⁻¹' {σ} = {x : R | a < x ∧ x < b} := by
  rw [or_iff_not_imp_left, not_subsingleton_iff]
  rintro ⟨x, hx : derivativeSign p x = σ, y, hy : derivativeSign p y = σ, hxy⟩
  obtain ⟨Z, hZ⟩ := (finite_setOfPred_isRoot_iterate_derivative p).exists_finset
  -- A root `z` of a nonzero derivative of order `k` cannot realize `σ`: as the condition is
  -- realized at two distinct points, its entry of order `k` is nonzero.
  have hZS (z : R) (hz : z ∈ Z) : derivativeSign p z ≠ σ := fun hzσ ↦ by
    obtain ⟨k, hk, hk0⟩ := (hZ z).1 hz
    exact derivativeSign_ne_zero_of_derivativeSign_eq p polynomialRolle_of_isRealClosed hxy
      (hx.trans hy.symm) hk (by rw [hx, ← hzσ, derivativeSign_eq_zero_iff, hk0.eq_zero])
  have hconn := ordConnected_preimage_derivativeSign p polynomialRolle_of_isRealClosed σ
  -- The realizing set is the interval between the nearest roots of the nonzero derivatives on
  -- either side of `x`.
  refine ⟨(Z.filter (· < x)).max, (Z.filter (x < ·)).min, Set.ext fun t ↦ ?_⟩
  rw [mem_preimage, mem_singleton_iff, mem_ofPred_eq, Finset.max_eq_sup_coe,
    Finset.min_eq_inf_withTop, Finset.sup_lt_iff (WithBot.bot_lt_coe t),
    Finset.lt_inf_iff (WithTop.coe_lt_top t)]
  simp only [Finset.mem_filter, and_imp, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  refine ⟨fun ht ↦ ⟨fun z hz hzx ↦ lt_of_not_ge fun h ↦ hZS z hz (hconn.out ht hx ⟨h, hzx.le⟩),
    fun z hz hxz ↦ lt_of_not_ge fun h ↦ hZS z hz (hconn.out hx ht ⟨hxz.le, h⟩)⟩, ?_⟩
  rintro ⟨hlo, hhi⟩
  -- Conversely, no root of a nonzero derivative lies between `t` and `x`.
  refine (derivativeSign_eq_of_forall_eval_ne_zero p fun z hz k hk hz0 ↦ ?_).trans hx
  have hzZ := (hZ z).2 ⟨k, hk, hz0⟩
  obtain hzx | hxz := lt_or_gt_of_ne fun h : z = x ↦ hZS z hzZ (h ▸ hx)
  · exact (mem_uIcc.1 hz).elim (fun h ↦ h.1.not_gt (hlo z hzZ hzx)) fun h ↦ h.1.not_gt hzx
  · exact (mem_uIcc.1 hz).elim (fun h ↦ h.2.not_gt hxz) fun h ↦ h.2.not_gt (hhi z hzZ hxz)

/-- **Thom's lemma for finite Thom encodings.** For any signs `τ` prescribed for the
derivatives of orders `1, …, natDegree p`, the set of points where `p` realizes them is empty,
a single point, or an open interval with endpoints `a ∈ WithBot R` and `b ∈ WithTop R`. -/
theorem preimage_thomEncoding_subsingleton_or_eq_Ioo (p : R[X])
    (τ : Fin p.natDegree → SignType) :
    (thomEncoding p ⁻¹' {τ}).Subsingleton ∨
      ∃ (a : WithBot R) (b : WithTop R), thomEncoding p ⁻¹' {τ} = {x : R | a < x ∧ x < b} := by
  -- The finite encoding of `p` is the full derivative sign condition of `p'`, padded by zeros.
  have h : thomEncoding p ⁻¹' {τ} = derivativeSign p.derivative ⁻¹'
      {fun k ↦ if hk : k < p.natDegree then τ ⟨k, hk⟩ else 0} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · rintro rfl
      funext k
      rw [derivativeSign_derivative]
      split_ifs with hk
      · exact (thomEncoding_apply p x ⟨k, hk⟩).symm
      · exact derivativeSign_eq_zero p x (by omega)
    · intro hx
      funext i
      simpa [thomEncoding_apply, ← derivativeSign_derivative] using congrFun hx i
  rw [h]
  exact preimage_derivativeSign_subsingleton_or_eq_Ioo _ _

end Polynomial
