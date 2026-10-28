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

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Thom's lemma.** For any signs `σ k` prescribed for the derivatives of every order of `p`,
including order zero, the set of points where `p` realizes them is empty, a single point, or an
open interval with endpoints `a ∈ WithBot R` and `b ∈ WithTop R`. -/
theorem preimage_derivativeSign_subsingleton_or_eq_Ioo (p : R[X]) (σ : ℕ → SignType) :
    (derivativeSign p ⁻¹' {σ}).Subsingleton ∨
      ∃ (a : WithBot R) (b : WithTop R), derivativeSign p ⁻¹' {σ} = {x : R | a < x ∧ x < b} := by
  classical
  rw [or_iff_not_imp_left, not_subsingleton_iff]
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [mem_preimage, mem_singleton_iff] at hx hy
  -- The roots of the nonzero derivatives of `p`, of every order, form a finite set `Z`.
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset R, ∀ z, z ∈ Z ↔
      ∃ k, derivative^[k] p ≠ 0 ∧ (derivative^[k] p).eval z = 0 := by
    refine ⟨(Finset.range (p.natDegree + 1)).biUnion fun k ↦ (derivative^[k] p).roots.toFinset,
      fun z ↦ ?_⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Multiset.mem_toFinset, mem_roots',
      IsRoot.def]
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk, hz⟩ ↦ ⟨k, ?_, hk, hz⟩⟩
    by_contra! hdeg
    exact hk (iterate_derivative_eq_zero (by omega))
  -- A root `z` of a nonzero derivative of order `k` cannot realize `σ`: as the condition is
  -- realized at two distinct points, its entry of order `k` is nonzero.
  have hZS (z : R) (hz : z ∈ Z) : derivativeSign p z ≠ σ := by
    intro hzσ
    obtain ⟨k, hk, hk0⟩ := (hZ z).1 hz
    refine derivativeSign_ne_zero_of_derivativeSign_eq p polynomialRolle_of_isRealClosed hxy
      (hx.trans hy.symm) hk ?_
    rw [hx, ← hzσ, derivativeSign_eq_zero_iff, hk0]
  have hconn := ordConnected_preimage_derivativeSign p polynomialRolle_of_isRealClosed σ
  -- The realizing set is the interval between the nearest roots of the nonzero derivatives on
  -- either side of `x`.
  refine ⟨(Z.filter (· < x)).max, (Z.filter (x < ·)).min, Set.ext fun t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩
  · rw [mem_preimage, mem_singleton_iff] at ht
    constructor
    · by_contra! hle
      cases hm : (Z.filter (· < x)).max with
      | bot => exact (WithBot.bot_lt_coe t).not_ge (hm ▸ hle)
      | coe z =>
        obtain ⟨hz, hzx⟩ := Finset.mem_filter.1 (Finset.mem_of_max hm)
        rw [hm, WithBot.coe_le_coe] at hle
        exact hZS z hz (hconn.out (x := t) (y := x) ht hx ⟨hle, hzx.le⟩)
    · by_contra! hle
      cases hm : (Z.filter (x < ·)).min with
      | top => exact (WithTop.coe_lt_top t).not_ge (hm ▸ hle)
      | coe z =>
        obtain ⟨hz, hxz⟩ := Finset.mem_filter.1 (Finset.mem_of_min hm)
        rw [hm, WithTop.coe_le_coe] at hle
        exact hZS z hz (hconn.out (x := x) (y := t) hx ht ⟨hxz.le, hle⟩)
  · rintro ⟨hat, htb⟩
    rw [mem_preimage, mem_singleton_iff, ← hx]
    funext k
    by_cases hk : derivative^[k] p = 0
    · simp [derivativeSign_def, hk]
    -- No root of the derivative of order `k` lies between `x` and `t`.
    have hno (z : R) (hz : z ∈ uIcc x t) : (derivative^[k] p).eval z ≠ 0 := by
      intro hz0
      have hzZ := (hZ z).2 ⟨k, hk, hz0⟩
      rcases lt_trichotomy z x with hzx | rfl | hxz
      · have hzt : z < t := WithBot.coe_lt_coe.1
          ((Finset.le_max (Finset.mem_filter.2 ⟨hzZ, hzx⟩)).trans_lt hat)
        rcases mem_uIcc.1 hz with h | h
        · exact h.1.not_gt hzx
        · exact h.1.not_gt hzt
      · exact hZS z hzZ hx
      · have htz : t < z := WithTop.coe_lt_coe.1
          (htb.trans_le (Finset.min_le (Finset.mem_filter.2 ⟨hzZ, hxz⟩)))
        rcases mem_uIcc.1 hz with h | h
        · exact h.2.not_gt htz
        · exact h.2.not_gt hxz
    simp only [derivativeSign_def]
    rcases le_total x t with hxt | htx
    · exact (sign_eval_const _ hxt fun z hz ↦ hno z (Icc_subset_uIcc hz)).symm
    · exact sign_eval_const _ htx fun z hz ↦ hno z (Icc_subset_uIcc' hz)

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
