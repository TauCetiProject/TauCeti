/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Instances.AddCircle.Defs
import TauCeti.Algebra.AddCircle
import TauCeti.NumberTheory.Padics.RatCast
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The primary rational circle as a p-adic quotient

Rational inclusion identifies the `p`-primary component of `ℚ/ℤ` with `ℚ_p/ℤ_p`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

private noncomputable def ratCircleToPadicQuotient :
    AddCircle (1 : ℚ) →+ ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    ((1 : Submodule ℤ_[p] ℚ_[p]).mkQ.toAddMonoidHom.comp
      (Rat.castHom ℚ_[p]).toAddMonoidHom) <| by
    rw [AddSubgroup.zmultiples_le]
    -- Evaluate the bundled composite on the generator to use the quotient's zero criterion.
    change Submodule.Quotient.mk (1 : ℚ_[p]) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨1, map_one _⟩)

private theorem ratCircleToPadicQuotient_coe (q : ℚ) :
    ratCircleToPadicQuotient p (q : AddCircle (1 : ℚ)) =
      Submodule.Quotient.mk (q : ℚ_[p]) := rfl

private theorem ratCircleToPadicQuotient_eq_zero {q : ℚ}
    (hq : (q : AddCircle (1 : ℚ)) ∈ AddCommGroup.primaryComponent _ p)
    (h : ratCircleToPadicQuotient p q = 0) : (q : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp hq
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hn
  obtain ⟨a, ha⟩ := hn
  rw [ratCircleToPadicQuotient_coe, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp h
  apply (AddCircle.coe_eq_zero_iff_den_eq_one q).mpr
  apply Padic.den_eq_one_of_pow_mul_eq_of_norm_rat_le_one
    (p := p) (k := n) (n := a)
  · simpa [nsmul_eq_mul] using ha.symm
  · rw [← hz, PadicInt.algebraMap_apply, PadicInt.norm_coe]
    exact PadicInt.norm_le_one z

private theorem exists_rat_primary_representative (x : ℚ_[p]) :
    ∃ q : ℚ, (q : AddCircle (1 : ℚ)) ∈ AddCommGroup.primaryComponent _ p ∧
      Submodule.Quotient.mk (q : ℚ_[p]) =
        (Submodule.Quotient.mk x : ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / (‖x‖ + 1)) (Padic.norm_p_lt_one (p := p))
  have hnorm : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    have h := (lt_div_iff₀ (by positivity : 0 < ‖x‖ + 1)).mp hn
    nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (p : ℚ_[p])) n]
  let z : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, hnorm⟩
  let a := z.appr n
  obtain ⟨w, hw⟩ := PadicInt.dvd_sub_appr z n
  have hw' : (p : ℚ_[p]) ^ n * x - a = (p : ℚ_[p]) ^ n * w := by
    have h := congrArg (algebraMap ℤ_[p] ℚ_[p]) hw
    simp only [map_sub, map_mul, map_pow, map_natCast] at h
    -- The algebra map on the integral subtype is its coercion to the field.
    change (p : ℚ_[p]) ^ n * x - a = (p : ℚ_[p]) ^ n * w at h
    exact h
  refine ⟨(a : ℚ) / (p : ℚ) ^ n, ?_, ?_⟩
  · apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨n, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_pow]
    rw [mul_div_cancel₀ _ (pow_ne_zero n (Nat.cast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero))]
    exact (AddCircle.coe_eq_zero_iff _).mpr ⟨a, by simp⟩
  · apply (Submodule.Quotient.eq _).mpr
    apply neg_mem_iff.mp
    refine Submodule.mem_one.mpr ⟨w, ?_⟩
    simp only [neg_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      PadicInt.algebraMap_apply]
    apply mul_left_cancel₀ (pow_ne_zero n hp)
    rw [mul_sub, mul_div_cancel₀ _ (pow_ne_zero n hp)]
    exact hw'.symm

/-- Rational inclusion identifies the `p`-primary component of the rational circle with
`ℚ_p/ℤ_p`. -/
noncomputable def ratCirclePrimaryEquivPadicQuotient :
    AddCommGroup.primaryComponent (AddCircle (1 : ℚ)) p ≃+
      ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  AddEquiv.ofBijective ((ratCircleToPadicQuotient p).comp
    (AddCommGroup.primaryComponent (AddCircle (1 : ℚ)) p).subtype) <| by
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
    (hq : (q : AddCircle (1 : ℚ)) ∈ AddCommGroup.primaryComponent _ p) :
    ratCirclePrimaryEquivPadicQuotient p ⟨q, hq⟩ =
      Submodule.Quotient.mk (q : ℚ_[p]) := by
  simp only [ratCirclePrimaryEquivPadicQuotient]
  exact ratCircleToPadicQuotient_coe p q

end TauCeti
