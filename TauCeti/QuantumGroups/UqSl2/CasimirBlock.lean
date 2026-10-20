/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Casimir
public import TauCeti.QuantumGroups.UqSl2.CompleteReducibility

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
On the top generalized weight space `W` of the block, for the weight `ε q^m`, the generator `E`
and the power `F^(m+1)` act by zero while `F^m` is injective, and `K` acts on `W` by the scalar
`ε q^m`. The last two facts follow by applying the results of
`TauCeti.QuantumGroups.UqSl2.CompleteReducibility` to the block viewed as a module itself.

## Main results

* `TauCeti.UqSl2.iSup_casimirBlock_casimirScalar_eq_top`: a finite-dimensional module at a
  generic parameter is the sum of the blocks for the signed highest weights `ε q^m`.
* `TauCeti.UqSl2.exists_eq_of_mem_genWeightSpace_of_mem_casimirBlock`: every generalized weight
  of the block for `ε q^m` is one of the weights `q^(-2j) ε q^m` with `0 ≤ j ≤ m`.
* `TauCeti.UqSl2.e_smul_eq_zero_of_mem_casimirBlock`,
  `TauCeti.UqSl2.f_pow_smul_eq_zero_of_mem_casimirBlock` and
  `TauCeti.UqSl2.f_pow_smul_ne_zero_of_mem_casimirBlock`: on the top generalized weight space of
  the block for `ε q^m`, `E` and `F^(m+1)` vanish and `F^m` is injective.
* `TauCeti.UqSl2.k_smul_eq_of_mem_casimirBlock`: `K` acts on that top generalized weight space
  by the scalar `ε q^m`.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VII.2.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- A signed power of a nonzero parameter is nonzero. -/
private theorem sign_mul_pow_ne_zero (hq : q ≠ 0) (ε : ℤˣ) (m : ℕ) : (ε : ℂ) * q ^ m ≠ 0 :=
  mul_ne_zero (Int.cast_ne_zero.mpr ε.ne_zero) (pow_ne_zero _ hq)

/-! ### The Casimir scalar on highest- and lowest-weight vectors of a block -/

/-- A vector on which the Casimir element acts by the scalar `s` lies in the Casimir block for
`c` only if it vanishes or `s = c`. -/
private theorem eq_of_casimir_smul_of_mem_casimirBlock {s c : ℂ} {v : V}
    (hs : casimir q • v = s • v) (hb : v ∈ casimirBlock q V c) (hv0 : v ≠ 0) : s = c := by
  by_contra hsc
  rw [← Submodule.restrictScalars_mem ℂ, restrictScalars_casimirBlock] at hb
  refine hv0 ((Submodule.disjoint_def.mp
    (Module.End.disjoint_genEigenspace (Algebra.lsmul ℂ ℂ V (casimir q)) hsc 1 ⊤)) v ?_ hb)
  exact Module.End.mem_eigenspace_iff.mpr (by rw [Algebra.lsmul_coe]; exact hs)

/-- A nonzero vector of weight `μ` killed by `E` lies in the Casimir block for `c` only if
`casimirScalar q μ = c`. -/
theorem casimirScalar_eq_of_mem_casimirBlock {μ c : ℂ} {v : V} (hv : v ∈ weightSpace q V μ)
    (he : e q • v = 0) (hb : v ∈ casimirBlock q V c) (hv0 : v ≠ 0) : casimirScalar q μ = c :=
  eq_of_casimir_smul_of_mem_casimirBlock (casimir_smul_of_e_smul_eq_zero hv he) hb hv0

/-- A nonzero vector of weight `μ` killed by `F` lies in the Casimir block for `c` only if
`casimirScalar q μ⁻¹ = c`. -/
theorem casimirScalar_inv_eq_of_mem_casimirBlock {μ c : ℂ} {v : V} (hv : v ∈ weightSpace q V μ)
    (hf : f q • v = 0) (hb : v ∈ casimirBlock q V c) (hv0 : v ≠ 0) :
    casimirScalar q μ⁻¹ = c :=
  eq_of_casimir_smul_of_mem_casimirBlock (casimir_smul_of_f_smul_eq_zero hv hf) hb hv0

/-! ### The nonzero blocks of a finite-dimensional module -/

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, a nonzero Casimir block of a finite-dimensional module belongs to
the Casimir scalar of a signed highest weight `ε q^m`. -/
theorem exists_eq_casimirScalar_of_casimirBlock_ne_bot (hq : IsGenericQuantumParameter q)
    {c : ℂ} (h : casimirBlock q V c ≠ ⊥) :
    ∃ (m : ℕ) (ε : ℤˣ), c = casimirScalar q (ε * q ^ m) := by
  obtain ⟨v, hvb, hv0⟩ := (Submodule.ne_bot_iff _).mp h
  -- The block is `K`-stable, so it is the sum of its intersections with the generalized weight
  -- spaces, and one of these intersections contains a nonzero vector `w`.
  have hv : v ∈ ⨆ μ, (casimirBlock q V c).restrictScalars ℂ ⊓ genWeightSpace q V μ := by
    have hsplit := Submodule.inf_iSup_genEigenspace (p := (casimirBlock q V c).restrictScalars ℂ)
      (f := Algebra.lsmul ℂ ℂ V (k q)) (fun x hx => by
        simpa only [Algebra.lsmul_coe, Submodule.restrictScalars_mem] using
          (casimirBlock q V c).smul_mem (k q) hx) ⊤
    have htop : ⨆ μ, (Algebra.lsmul ℂ ℂ V (k q)).genEigenspace μ ⊤ = ⊤ :=
      Module.End.iSup_maxGenEigenspace_eq_top _
    rw [htop, inf_top_eq] at hsplit
    simp only [genWeightSpace_def]
    exact hsplit.le hvb
  obtain ⟨μ, hμ⟩ : ∃ μ, (casimirBlock q V c).restrictScalars ℂ ⊓ genWeightSpace q V μ ≠ ⊥ := by
    by_contra! H
    simp only [H, iSup_bot, Submodule.mem_bot] at hv
    exact hv0 hv
  obtain ⟨w, ⟨hwb, hw⟩, hw0⟩ := (Submodule.ne_bot_iff _).mp hμ
  -- Move `w` to a highest-weight vector of the block; its weight is a signed `q^m`.
  obtain ⟨a, n, ha0, haw, hea⟩ := exists_smul_highest_weight_vector_of_mem_genWeightSpace hq hw hw0
  obtain ⟨m, ε, hm, -, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq haw ha0 hea
  refine ⟨m, ε, ?_⟩
  rw [← hm]
  exact (casimirScalar_eq_of_mem_casimirBlock haw hea
    ((casimirBlock q V c).smul_mem a hwb) ha0).symm

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

/-- At a generic parameter, `E` kills the top generalized weight space `ε q^m` of the Casimir
block for `ε q^m` of a finite-dimensional module. -/
theorem e_smul_eq_zero_of_mem_casimirBlock (hq : IsGenericQuantumParameter q) {m : ℕ}
    {ε : ℤˣ} {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m))
    (hb : w ∈ casimirBlock q V (casimirScalar q (ε * q ^ m))) : e q • w = 0 := by
  by_contra h0
  obtain ⟨j, -, hj⟩ := exists_eq_of_mem_genWeightSpace_of_mem_casimirBlock hq
    (e_smul_mem_genWeightSpace hw) ((casimirBlock q V _).smul_mem _ hb) h0
  -- The weight `q² ε q^m` would be `q^(-2j) ε q^m`, so `q^(2j + 2) = 1`.
  have h := mul_right_cancel₀ (sign_mul_pow_ne_zero hq.ne_zero ε m) hj
  refine hq.pow_ne_one (n := 2 * j + 2) (by omega) ?_
  have hqq : (q * q⁻¹) ^ (2 * j) = 1 := by rw [mul_inv_cancel₀ hq.ne_zero, one_pow]
  linear_combination q ^ (2 * j) * h + hqq

/-- At a generic parameter, `F^(m+1)` kills the top generalized weight space `ε q^m` of the
Casimir block for `ε q^m` of a finite-dimensional module. -/
theorem f_pow_smul_eq_zero_of_mem_casimirBlock (hq : IsGenericQuantumParameter q) {m : ℕ}
    {ε : ℤˣ} {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m))
    (hb : w ∈ casimirBlock q V (casimirScalar q (ε * q ^ m))) : f q ^ (m + 1) • w = 0 := by
  by_contra h0
  obtain ⟨j, hjm, hj⟩ := exists_eq_of_mem_genWeightSpace_of_mem_casimirBlock hq
    (f_pow_smul_mem_genWeightSpace hw (m + 1)) ((casimirBlock q V _).smul_mem _ hb) h0
  -- The weight `q^(-2(m+1)) ε q^m` would be `q^(-2j) ε q^m` with `j ≤ m`.
  have h := mul_right_cancel₀ (sign_mul_pow_ne_zero hq.ne_zero ε m) hj
  simp only [← pow_mul] at h
  have := hq.inv.pow_injective h
  omega

/-! ### The top weight space of a block -/

omit [FiniteDimensional ℂ V] in
/-- A vector of a submodule lies in one of its generalized weight spaces exactly when it lies in
the corresponding generalized weight space of the ambient module. -/
private theorem mem_genWeightSpace_submodule_iff {U : Submodule (UqSl2 q) V} {μ : ℂ} {w : U} :
    w ∈ genWeightSpace q U μ ↔ (w : V) ∈ genWeightSpace q V μ := by
  simp only [mem_genWeightSpace_iff, ← Submodule.coe_eq_zero, Submodule.coe_smul]

/-- At a generic parameter, `E` kills the top generalized weight space `ε q^m` of the Casimir
block for `ε q^m`, viewed as a module itself. -/
private theorem forall_e_smul_eq_zero_casimirBlock (hq : IsGenericQuantumParameter q) {m : ℕ}
    {ε : ℤˣ} (w : casimirBlock q V (casimirScalar q (ε * q ^ m)))
    (hw : w ∈ genWeightSpace q _ (ε * q ^ m)) : e q • w = 0 :=
  Subtype.ext (e_smul_eq_zero_of_mem_casimirBlock hq (mem_genWeightSpace_submodule_iff.mp hw) w.2)

/-- At a generic parameter, `F^m` is injective on the top generalized weight space `ε q^m` of
the Casimir block for `ε q^m` of a finite-dimensional module. -/
theorem f_pow_smul_ne_zero_of_mem_casimirBlock (hq : IsGenericQuantumParameter q) {m : ℕ}
    {ε : ℤˣ} {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m))
    (hb : w ∈ casimirBlock q V (casimirScalar q (ε * q ^ m))) (hw0 : w ≠ 0) :
    f q ^ m • w ≠ 0 := fun h =>
  hw0 (congrArg Subtype.val (eq_zero_of_f_pow_smul_eq_zero hq
    (forall_e_smul_eq_zero_casimirBlock hq) le_rfl
    ((mem_genWeightSpace_submodule_iff (w := ⟨w, hb⟩)).mpr hw) (Subtype.ext h)))

/-- At a generic parameter, `K` acts by the scalar `ε q^m` on the top generalized weight space
`ε q^m` of the Casimir block for `ε q^m` of a finite-dimensional module: these generalized
weight vectors are genuine weight vectors. -/
theorem k_smul_eq_of_mem_casimirBlock (hq : IsGenericQuantumParameter q) {m : ℕ} {ε : ℤˣ}
    {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m))
    (hb : w ∈ casimirBlock q V (casimirScalar q (ε * q ^ m))) :
    k q • w = (ε * q ^ m : ℂ) • w := by
  have : FiniteDimensional ℂ (casimirBlock q V (casimirScalar q (ε * q ^ m))) :=
    Module.Finite.of_injective ((casimirBlock q V _).subtype.restrictScalars ℂ)
      Subtype.val_injective
  have h := (mem_genWeightSpace_submodule_iff (w := ⟨w, hb⟩)).mpr hw
  rw [genWeightSpace_eq_weightSpace_of_forall_e_smul_eq_zero hq
    (forall_e_smul_eq_zero_casimirBlock hq)] at h
  exact congrArg Subtype.val (mem_weightSpace_iff.mp h)

end TauCeti.UqSl2
