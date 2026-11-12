/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Casimir.Basic
public import TauCeti.QuantumGroups.UqSl2.HighestWeight

import TauCeti.Algebra.Ring.Int.Units
import Mathlib.Tactic

/-!
# Casimir blocks of `U_q(sl₂)`-modules

The Casimir block `TauCeti.UqSl2.casimirBlock` of a `UqSl2 q`-module `V` for a scalar `c` is
the maximal generalized eigenspace of the action of the Casimir element `Ω` with eigenvalue `c`.
This file locates the blocks of a finite-dimensional module and their weights.

At a generic parameter, a finite-dimensional module has nonzero blocks only for the Casimir
scalars of the signed highest weights `ε q^m`, so it is the sum of the blocks for these scalars.
Inside the block for `ε q^m` every highest-weight vector has weight `ε q^m` and every
lowest-weight vector has weight `ε q^(-m)`. Consequently every generalized weight of the block
is `q^(-2j) ε q^m` for some `0 ≤ j ≤ m`, exactly the weights of the ladder module `L_m^ε`.

## Main results

* `TauCeti.UqSl2.iSup_casimirBlock_casimirScalar_eq_top`: a finite-dimensional module at a
  generic parameter is the sum of the blocks for the signed highest weights `ε q^m`.
* `TauCeti.UqSl2.exists_eq_of_mem_genWeightSpace_of_mem_casimirBlock`: every generalized weight
  of the block for `ε q^m` is one of the weights `q^(-2j) ε q^m` with `0 ≤ j ≤ m`.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VII.2.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-! ### The nonzero blocks of a finite-dimensional module -/

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, a nonzero Casimir block of a finite-dimensional module belongs to
the Casimir scalar of a signed highest weight `ε q^m`. -/
theorem exists_eq_casimirScalar_of_casimirBlock_ne_bot (hq : IsGenericQuantumParameter q)
    {c : ℂ} (h : casimirBlock q V c ≠ ⊥) :
    ∃ (m : ℕ) (ε : ℤˣ), c = casimirScalar q (ε * q ^ m) := by
  -- A highest-weight vector of the block, viewed as a module itself, has weight `ε q^m`.
  have : Nontrivial (casimirBlock q V c) := Submodule.nontrivial_iff_ne_bot.mpr h
  obtain ⟨μ, v, -, hv0, hk, he⟩ := exists_highest_weight_vector hq (V := casimirBlock q V c)
  have hv : v ∈ weightSpace q _ μ := mem_weightSpace_iff.mpr hk
  obtain ⟨m, ε, rfl, -, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq hv hv0 he
  exact ⟨m, ε, (casimirScalar_eq_of_mem_casimirBlock hv he
    (casimirBlock_casimirBlock_eq_top (q := q) (V := V) c ▸ Submodule.mem_top) hv0).symm⟩

/-- At a generic parameter, a finite-dimensional module is the sum of its Casimir blocks for the
Casimir scalars of the signed highest weights `ε q^m`. -/
theorem iSup_casimirBlock_casimirScalar_eq_top (hq : IsGenericQuantumParameter q) :
    ⨆ (m : ℕ) (ε : ℤˣ), casimirBlock q V (casimirScalar q (ε * q ^ m)) = ⊤ := by
  refine eq_top_iff.mpr (iSup_casimirBlock_eq_top (q := q) (V := V) ▸ iSup_le fun c => ?_)
  rcases eq_or_ne (casimirBlock q V c) ⊥ with h | h
  · exact h ▸ bot_le
  · obtain ⟨m, ε, rfl⟩ := exists_eq_casimirScalar_of_casimirBlock_ne_bot hq h
    exact le_iSup₂ (f := fun (m : ℕ) (ε : ℤˣ) => casimirBlock q V (casimirScalar q (ε * q ^ m)))
      m ε

/-! ### Weights of a block -/

/-- At a generic parameter, every generalized weight of the Casimir block for the signed highest
weight `ε q^m` of a finite-dimensional module is one of the weights `q^(-2j) ε q^m` with
`0 ≤ j ≤ m` of the ladder module `L_m^ε`. -/
theorem exists_eq_of_mem_genWeightSpace_of_mem_casimirBlock (hq : IsGenericQuantumParameter q)
    {m : ℕ} {ε : ℤˣ} {ν : ℂ} {w : V} (hw : w ∈ genWeightSpace q V ν)
    (hb : w ∈ casimirBlock q V (casimirScalar q (ε * q ^ m))) (hw0 : w ≠ 0) :
    ∃ j ≤ m, ν = (q⁻¹ ^ 2) ^ j * (ε * q ^ m) := by
  have hq0 := hq.ne_zero
  -- A highest-weight vector in the cyclic submodule of `w` has weight `q^(2n) ν`, and its
  -- Casimir scalar forces `q^(2n) ν = ε q^m`.
  obtain ⟨a, n, ha0, haw, hea⟩ := exists_smul_highest_weight_vector_of_mem_genWeightSpace hq hw hw0
  obtain ⟨m', ε', hm', -, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq haw ha0 hea
  have hab := casimirScalar_eq_of_mem_casimirBlock haw hea ((casimirBlock q V _).smul_mem a hb) ha0
  rw [hm', casimirScalar_units_mul_pow_inj hq] at hab
  obtain ⟨rfl, rfl⟩ := hab
  have hν : ν = (q⁻¹ ^ 2) ^ n * (ε' * q ^ m') := by
    rw [← hm', ← mul_assoc, ← mul_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hq0), one_pow,
      one_mul]
  refine ⟨n, ?_, hν⟩
  -- A lowest-weight vector in the cyclic submodule of `w` has weight `λ = q^(-2(n + n')) ε q^m`,
  -- and its Casimir scalar forces `λ = ε q^(-m)`, so `n + n' = m`.
  obtain ⟨b, n', hb0, hbw, hfb⟩ := exists_smul_lowest_weight_vector_of_mem_genWeightSpace hq hw hw0
  have hlow := casimirScalar_inv_eq_of_mem_casimirBlock hbw hfb
    ((casimirBlock q V _).smul_mem b hb) hb0
  set s : ℂ := ((ε' : ℤ) : ℂ)
  have hs : s ^ 2 = 1 := Int.cast_units_sq ε'
  have hs0 : s ≠ 0 := Int.cast_ne_zero.mpr ε'.ne_zero
  have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hqq (N : ℕ) : (q * q⁻¹) ^ N = 1 := by rw [mul_inv_cancel₀ hq0, one_pow]
  rw [hν, casimirScalar_eq_casimirScalar_iff hq.sub_inv_ne_zero (by simp [hq0, hs0])
    (by simp [hq0, hs0])] at hlow
  simp only [mul_inv, inv_pow, inv_inv] at hlow
  rcases hlow with h | h
  · have h2 : q ^ (2 * (n + n')) = q ^ (2 * m') := by
      linear_combination (s * q ^ m') * h - q ^ (2 * (n + n')) * hsi -
        q ^ (2 * (n + n')) * s * s⁻¹ * hqq m' + q ^ (2 * m') * hs
    have := hq.pow_injective h2
    omega
  · refine absurd ?_ (hq.pow_ne_one (n := 2 * (n + n') + 2) (by omega))
    linear_combination h - q ^ (2 * (n + n') + 2) * hsi -
      q ^ (2 * (n + n') + 2) * s * s⁻¹ * hqq m'

end TauCeti.UqSl2
