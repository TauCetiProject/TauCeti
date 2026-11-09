/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Quadratic

/-!
# Finite residue tests for quadratic norms

Let `(1, ω)` be an integral basis of a quadratic extension `L/K` of nonarchimedean local
fields. If all principal units of positive depth `n` are norms, a unit is a field norm
exactly when its residue modulo `𝓂[K]^n` is represented by the integral norm polynomial
`X² + Tr(ω) X Y + N(ω) Y²`. Both coordinates range over the finite ring `𝒪[K] / 𝓂[K]^n`.

An approximate norm at this precision is an actual norm: its ratio with the desired unit
is a principal unit of depth `n`. The lifting result works for every finite extension;
the binary criterion makes integral-basis descriptions usable for finite norm tables,
without assuming integral coordinates in a square-root suborder.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsLocalRing TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

namespace TauCeti

/-- An integral norm congruent to a unit modulo `𝓂[K]^n` lifts to an exact field norm
if every principal unit of depth `n > 0` is a norm. Unlike trace-based Hensel lifting,
this applies to ramified extensions as well. -/
theorem exists_norm_eq_of_norm_sub_mem_of_unitFiltration_le {n : ℕ} (hn : 0 < n)
    (hU : unitFiltration K n ≤ normGroup K L) (b : 𝒪[K]ˣ) {w : 𝒪[L]}
    (hw : Algebra.norm 𝒪[K] w - (b : 𝒪[K]) ∈ 𝓂[K] ^ n) :
    ∃ z : L, Algebra.norm K z = (b : K) := by
  -- The approximate norm is a unit, since its residue is that of b.
  have hres : residue 𝒪[K] (Algebra.norm 𝒪[K] w) = residue 𝒪[K] (b : 𝒪[K]) :=
    Ideal.Quotient.eq.mpr ((Ideal.pow_le_self hn.ne') hw)
  have hc : IsUnit (Algebra.norm 𝒪[K] w) :=
    (residue_ne_zero_iff_isUnit _).mp (hres ▸
      (residue_ne_zero_iff_isUnit _).mpr b.isUnit)
  let c := hc.unit
  let r := b * c⁻¹
  have hr : (Units.map (Subring.subtype 𝒪[K]) r) ∈ unitFiltration K n := by
    apply mem_unitFiltration_iff_exists.mpr
    refine ⟨r, ?_, rfl⟩
    have hcancel : Algebra.norm 𝒪[K] w * (↑c⁻¹ : 𝒪[K]) = 1 := by
      simpa only [c, IsUnit.unit_spec] using c.mul_inv
    have heq : (r : 𝒪[K]) - 1 =
        -((Algebra.norm 𝒪[K] w - (b : 𝒪[K])) * (↑c⁻¹ : 𝒪[K])) := by
      simp only [r, Units.val_mul]
      linear_combination hcancel
    rw [heq]
    exact neg_mem (Ideal.mul_mem_right _ _ hw)
  have hcN : Units.map (Subring.subtype 𝒪[K]) c ∈ normGroup K L := by
    apply mem_normGroup_iff.mpr
    have hwunit : IsUnit w := isUnit_norm_integerRing_iff.mp hc
    refine ⟨Units.map (Subring.subtype 𝒪[L]) hwunit.unit, ?_⟩
    simp [c]
  have hbN := (normGroup K L).mul_mem (hU hr) hcN
  have hrc : r * c = b := by simp [r]
  rw [← map_mul, hrc] at hbN
  obtain ⟨z, hz⟩ := mem_normGroup_iff.mp hbN
  exact ⟨z, hz⟩

end TauCeti

namespace Module.Basis

/-- An integral unit is a field norm if and only if its residue modulo `𝓂[K]^n` is a value
of the integral binary norm polynomial, provided every principal unit of depth `n > 0`
is a norm. The coordinates in this test belong to the finite quotient ring. -/
theorem exists_norm_eq_iff_exists_quotient_normForm
    (B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L]) (hB : B 0 = 1) {n : ℕ} (hn : 0 < n)
    (hU : unitFiltration K n ≤ normGroup K L) (b : 𝒪[K]ˣ) :
    (∃ z : L, Algebra.norm K z = (b : K)) ↔
      ∃ x y : 𝒪[K] ⧸ 𝓂[K] ^ n,
        x ^ 2 + Ideal.Quotient.mk (𝓂[K] ^ n) (Algebra.trace 𝒪[K] 𝒪[L] (B 1)) * x * y +
          Ideal.Quotient.mk (𝓂[K] ^ n) (Algebra.norm 𝒪[K] (B 1)) * y ^ 2 =
            Ideal.Quotient.mk (𝓂[K] ^ n) (b : 𝒪[K]) := by
  let q := Ideal.Quotient.mk (𝓂[K] ^ n)
  have hnorm (w : 𝒪[L]) : Algebra.norm 𝒪[K] w =
      B.repr w 0 ^ 2 + Algebra.trace 𝒪[K] 𝒪[L] (B 1) * B.repr w 0 * B.repr w 1 +
        Algebra.norm 𝒪[K] (B 1) * B.repr w 1 ^ 2 := by
    rw [B.norm_eq_of_apply_zero_eq_one hB]
    ring
  constructor
  · rintro ⟨z, hz⟩
    have hb : valuation K (b : K) = 1 :=
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp b.isUnit
    obtain ⟨w, hw, -⟩ := exists_integerRing_eq_and_isUnit_norm (hz ▸ hb)
    have hwN : Algebra.norm 𝒪[K] w = (b : 𝒪[K]) := by
      apply Subtype.val_injective
      simpa only [coe_norm_integerRing, hw] using hz
    refine ⟨q (B.repr w 0), q (B.repr w 1), ?_⟩
    simpa only [map_add, map_mul, map_pow] using congrArg q ((hnorm w).symm.trans hwN)
  · rintro ⟨x, y, hxy⟩
    obtain ⟨X, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective y
    let w := B.equivFun.symm ![X, Y]
    have hwN : q (Algebra.norm 𝒪[K] w) = q (b : 𝒪[K]) := by
      rw [hnorm]
      simpa only [w, ← B.equivFun_apply, LinearEquiv.apply_symm_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, map_pow] using hxy
    exact exists_norm_eq_of_norm_sub_mem_of_unitFiltration_le hn hU b
      (Ideal.Quotient.eq.mp hwN)

end Module.Basis
