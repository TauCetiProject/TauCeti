/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Divisible.Prufer
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RatCast
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The primary rational circle as a p-adic quotient

Rational inclusion identifies the Prüfer group `prufer p` with `ℚ_p/ℤ_p`.

## Main definitions

* `TauCeti.ratCirclePrimaryEquivPadicQuotient`: the additive equivalence from the Prüfer group
  to the quotient of the p-adic field by its integers.

## Main results

* `Padic.exists_nat_lt_pow_quotient_mk_eq`: a denominator-controlled representative of a
  p-adic class whose product with a power of `p` is integral.
* `TauCeti.ratCirclePrimaryEquivPadicQuotient_apply` and
  `TauCeti.ratCirclePrimaryEquivPadicQuotient_symm_mk`: forward and inverse equations on rational
  representatives.
-/

public section

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- If `p ^ n * x` is integral, the class of `x` in `ℚ_p/ℤ_p` has a representative
`a / p ^ n` with `a < p ^ n`. The numerator is obtained by truncating the integral
multiple modulo `p ^ n`. -/
theorem exists_nat_lt_pow_quotient_mk_eq (x : ℚ_[p]) (n : ℕ)
    (hnorm : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    ∃ a : ℕ, a < p ^ n ∧
      (Submodule.Quotient.mk ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) :
        ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) = Submodule.Quotient.mk x := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let z : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, hnorm⟩
  let a := z.appr n
  obtain ⟨w, hw⟩ := PadicInt.dvd_sub_appr z n
  have hw' : (p : ℚ_[p]) ^ n * x - a = (p : ℚ_[p]) ^ n * w := by
    have h := congrArg (algebraMap ℤ_[p] ℚ_[p]) hw
    simp only [map_sub, map_mul, map_pow, map_natCast, PadicInt.algebraMap_apply] at h
    -- Only the projection of the locally constructed integral subtype remains.
    change (p : ℚ_[p]) ^ n * x - a = (p : ℚ_[p]) ^ n * w at h
    exact h
  refine ⟨a, z.appr_lt n, (Submodule.Quotient.eq _).mpr ?_⟩
  apply neg_mem_iff.mp
  refine Submodule.mem_one.mpr ⟨w, ?_⟩
  simp only [neg_sub, PadicInt.algebraMap_apply]
  apply mul_left_cancel₀ (pow_ne_zero n hp)
  rw [mul_sub, mul_div_cancel₀ _ (pow_ne_zero n hp)]
  exact hw'.symm

end Padic

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

private noncomputable def ratCircleToPadicQuotient :
    AddCircle (1 : ℚ) →+ ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    ((1 : Submodule ℤ_[p] ℚ_[p]).mkQ.toAddMonoidHom.comp
      (Rat.castHom ℚ_[p]).toAddMonoidHom) <| by
    rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
    rw [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, map_one, LinearMap.toAddMonoidHom_coe,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨1, map_one _⟩)

private theorem ratCircleToPadicQuotient_coe (q : ℚ) :
    ratCircleToPadicQuotient p (q : AddCircle (1 : ℚ)) =
      Submodule.Quotient.mk (q : ℚ_[p]) := by
  simp only [ratCircleToPadicQuotient, QuotientAddGroup.lift_mk,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, Rat.coe_castHom,
    Submodule.mkQ_apply]

private theorem ratCircleToPadicQuotient_eq_zero {q : ℚ}
    (hq : (q : AddCircle (1 : ℚ)) ∈ prufer p)
    (h : ratCircleToPadicQuotient p q = 0) : (q : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp hq
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hn
  obtain ⟨a, ha⟩ := hn
  rw [ratCircleToPadicQuotient_coe, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp h
  simpa using Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap
    (p := p) (r := q) (s := 0) (k := n) (n := a)
    (by simpa [nsmul_eq_mul] using ha.symm)
    (by simpa using hz.symm)

private theorem exists_rat_primary_representative (x : ℚ_[p]) :
    ∃ q : ℚ, (q : AddCircle (1 : ℚ)) ∈ prufer p ∧
      Submodule.Quotient.mk (q : ℚ_[p]) =
        (Submodule.Quotient.mk x : ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / (‖x‖ + 1)) (Padic.norm_p_lt_one (p := p))
  have hnorm : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    have h := (lt_div_iff₀ (by positivity : 0 < ‖x‖ + 1)).mp hn
    nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (p : ℚ_[p])) n]
  obtain ⟨a, _, ha⟩ := Padic.exists_nat_lt_pow_quotient_mk_eq x n hnorm
  refine ⟨(a : ℚ) / (p : ℚ) ^ n, ?_, ?_⟩
  · apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨n, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_pow]
    rw [mul_div_cancel₀ _ (pow_ne_zero n (Nat.cast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero))]
    exact (AddCircle.coe_eq_zero_iff _).mpr ⟨a, by simp⟩
  · simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow] using ha

/-- Rational inclusion identifies the `p`-primary component of the rational circle with
`ℚ_p/ℤ_p`. -/
noncomputable def ratCirclePrimaryEquivPadicQuotient :
    prufer p ≃+
      ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  AddEquiv.ofBijective ((ratCircleToPadicQuotient p).comp
    (prufer p).subtype) <| by
    constructor
    · intro x y hxy
      apply sub_eq_zero.mp
      apply Subtype.ext
      obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (x - y : AddCircle (1 : ℚ))
      apply Eq.trans hq.symm
      apply ratCircleToPadicQuotient_eq_zero p
      · rw [hq]
        exact (x - y).property
      · rw [hq, map_sub]
        exact sub_eq_zero.mpr hxy
    · intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨q, hq, heq⟩ := exists_rat_primary_representative p y
      exact ⟨⟨q, hq⟩, heq⟩

/-- The equivalence sends the class of a rational number to its class in `ℚ_p/ℤ_p`. -/
theorem ratCirclePrimaryEquivPadicQuotient_apply (q : ℚ)
    (hq : (q : AddCircle (1 : ℚ)) ∈ prufer p) :
    ratCirclePrimaryEquivPadicQuotient p ⟨q, hq⟩ =
      Submodule.Quotient.mk (q : ℚ_[p]) := by
  calc
    _ = ((ratCircleToPadicQuotient p).comp (prufer p).subtype) ⟨q, hq⟩ :=
      AddEquiv.ofBijective_apply _ _ _
    _ = _ := by
      rw [AddMonoidHom.comp_apply]
      exact ratCircleToPadicQuotient_coe p q

/-- The inverse equivalence sends a primary rational representative back to its class in
the primary component of `ℚ/ℤ`. -/
theorem ratCirclePrimaryEquivPadicQuotient_symm_mk (q : ℚ)
    (hq : (q : AddCircle (1 : ℚ)) ∈ prufer p) :
    (ratCirclePrimaryEquivPadicQuotient p).symm
      (Submodule.Quotient.mk (q : ℚ_[p])) = ⟨q, hq⟩ := by
  apply (ratCirclePrimaryEquivPadicQuotient p).injective
  rw [AddEquiv.apply_symm_apply, ratCirclePrimaryEquivPadicQuotient_apply]

end TauCeti
