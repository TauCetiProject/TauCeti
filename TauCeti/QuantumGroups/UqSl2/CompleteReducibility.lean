/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.Transport
public import TauCeti.QuantumGroups.UqSl2.Casimir
public import TauCeti.QuantumGroups.UqSl2.HighestWeight
public import TauCeti.QuantumGroups.UqSl2.LadderModule
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic

/-!
# Complete reducibility of finite-dimensional `U_q(sl₂)`-modules

At a generic parameter `q` (nonzero and not a root of unity), every finite-dimensional
`UqSl2 q`-module is semisimple. No diagonalizability of `K` is assumed.

Along the way, the generalized weight space of weight `ε q^m` on which `E` acts by zero is shown
to be an honest weight space killed by `F^(m+1)`, and taking generalized weight spaces is shown to
be exact.

## Implementation notes

The proof splits a finite-dimensional module into the generalized eigenspaces of the central
Casimir element `Ω`. Every highest-weight vector in such a Casimir block has weight `ε q^m` for one
fixed pair `(m, ε)`, so `E` kills the generalized weight space `W` of weight `ε q^m`. On `W` the
commutator formula
`E F^(r+1) = F^(r+1) E + [r+1]_q F^r (q^(-r) K - q^r K⁻¹) / (q - q⁻¹)` shows that `F^r` is
injective for `r ≤ m`, that `F^(m+1)` vanishes, and then that `K` acts on `W` by the scalar
`ε q^m`. Every vector of `W` is therefore the image of `v₀` under a module map from the ladder
module `L_m^ε`, and these images span a semisimple submodule `U ⊇ W`. Taking generalized weight
spaces is exact, so the quotient by `U` has no generalized weight `ε q^m`; being a Casimir block
with the same scalar, it is zero.

## Main results

* `TauCeti.UqSl2.map_genWeightSpace_of_surjective`: a surjective module map carries generalized
  weight spaces onto generalized weight spaces.
* `TauCeti.UqSl2.genWeightSpace_eq_weightSpace_of_forall_e_smul_eq_zero` and
  `TauCeti.UqSl2.f_pow_smul_eq_zero_of_forall_e_smul_eq_zero`: if `E` kills the generalized
  weight space of weight `ε q^m`, then `K` acts on it by `ε q^m` and `F^(m+1)` kills it.
* `TauCeti.UqSl2.isSemisimpleModule_of_finiteDimensional`: at a generic parameter, every
  finite-dimensional `UqSl2 q`-module is semisimple.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter VII, for the
  semisimplicity of finite-dimensional modules at a generic parameter.
-/

public noncomputable section

open Module

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- The square of a sign is one. -/
private theorem units_sq (ε : ℤˣ) : ((ε : ℤ) : ℂ) ^ 2 = 1 := by
  rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]

/-- A signed power `ε q^m` of a nonzero parameter is nonzero. -/
private theorem units_mul_pow_ne_zero (ε : ℤˣ) (m : ℕ) (hq : q ≠ 0) :
    (ε : ℂ) * q ^ m ≠ 0 :=
  mul_ne_zero (by rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num) (pow_ne_zero _ hq)

/-! ### Generalized weight spaces -/

/-- A vector of weight `α` in the generalized weight space of a different weight vanishes. -/
private theorem eq_zero_of_mem_weightSpace_of_mem_genWeightSpace {α ν : ℂ} (h : α ≠ ν) {v : V}
    (hα : v ∈ weightSpace q V α) (hν : v ∈ genWeightSpace q V ν) : v = 0 :=
  Submodule.disjoint_def.mp ((iSupIndep_genWeightSpace (q := q) (V := V)).pairwiseDisjoint h)
    v (weightSpace_le_genWeightSpace α hα) hν

/-- `K` preserves every generalized weight space. -/
private theorem k_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    k q • v ∈ genWeightSpace q V μ := by
  simpa using smul_mem_genWeightSpace_of_k_mul (a := k q) (c := 1) (by rw [one_smul]) hv

/-- `K⁻¹` preserves every generalized weight space. -/
private theorem kInv_smul_mem_genWeightSpace {μ : ℂ} {v : V} (hv : v ∈ genWeightSpace q V μ) :
    kInv q • v ∈ genWeightSpace q V μ := by
  simpa using smul_mem_genWeightSpace_of_k_mul (a := kInv q) (c := 1)
    (by rw [one_smul, k_mul_kInv, kInv_mul_k]) hv

/-- If `K² v = ρ² v` for a generalized weight vector `v` of weight `ν ≠ -ρ`, then `K v = ρ v`. -/
private theorem k_smul_eq_of_k_sq_smul_eq {ν ρ : ℂ} (h : -ρ ≠ ν) {v : V}
    (hv : v ∈ genWeightSpace q V ν) (hk : k q ^ 2 • v = ρ ^ 2 • v) : k q • v = ρ • v := by
  -- The vector `K v - ρ v` has weight `-ρ`, so it vanishes.
  have hw : k q • v - ρ • v ∈ weightSpace q V (-ρ) := by
    rw [mem_weightSpace_iff, smul_sub, smul_comm (k q) ρ v, ← mul_smul, ← sq, hk]
    generalize k q • v = x
    module
  exact sub_eq_zero.mp (eq_zero_of_mem_weightSpace_of_mem_genWeightSpace h hw
    (sub_mem (k_smul_mem_genWeightSpace hv) (Submodule.smul_mem _ ρ hv)))

/-- An element acting on `v` by the scalar `s` acts on `v` by `sⁿ` through its `n`-th power. -/
private theorem pow_smul_eq_of_smul_eq {a : UqSl2 q} {s : ℂ} {v : V} (h : a • v = s • v)
    (n : ℕ) : a ^ n • v = s ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, h, smul_comm, ih, smul_smul, ← pow_succ']

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- A surjective module map carries the generalized weight spaces of a finite-dimensional module
onto the generalized weight spaces of its target. In particular, taking generalized weight
spaces is exact on quotient modules. -/
theorem map_genWeightSpace_of_surjective {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    [Module (UqSl2 q) V'] [IsScalarTower ℂ (UqSl2 q) V'] {φ : V →ₗ[UqSl2 q] V'}
    (hφ : Function.Surjective φ) (μ : ℂ) :
    (genWeightSpace q V μ).map (φ.restrictScalars ℂ) = genWeightSpace q V' μ := by
  rw [genWeightSpace_def, genWeightSpace_def]
  exact map_maxGenEigenspace_eq_of_intertwine hφ (fun x => φ.map_smul (k q) x)
    (by simpa only [genWeightSpace_def] using iSup_genWeightSpace_eq_top (q := q) (V := V)) μ

/-- At a generic parameter, every nonzero generalized weight space of weight `ν` yields a nonzero
vector of weight `(q²)ⁿ ν`, for some `n`, killed by `E`. -/
private theorem exists_highest_weight_vector_of_genWeightSpace_ne_bot
    (hq : IsGenericQuantumParameter q) {ν : ℂ} (hν : genWeightSpace q V ν ≠ ⊥) :
    ∃ (n : ℕ) (v : V), v ∈ weightSpace q V ((q ^ 2) ^ n * ν) ∧ v ≠ 0 ∧ e q • v = 0 := by
  rw [genWeightSpace_def] at hν
  have hev : (Algebra.lsmul ℂ ℂ V (k q)).HasEigenvalue ν :=
    Module.End.HasUnifEigenvalue.lt zero_lt_one hν
  obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
  replace hv : v ∈ weightSpace q V ν := by rwa [weightSpace_def]
  obtain ⟨n, hn0, hn⟩ := exists_e_pow_smul_ne_zero_and_e_smul_eq_zero hq hv0
  exact ⟨n, e q ^ n • v, e_pow_smul_mem_weightSpace hv n, hn0, hn⟩

/-- In a module on which `Ω - c` is locally nilpotent, a nonzero vector of weight `μ` killed by
`E` has weight `ε q^m`, where `c` is the Casimir scalar of `ε q^m`. -/
private theorem exists_eq_casimirScalar_of_highest_weight_vector
    (hq : IsGenericQuantumParameter q) {c : ℂ}
    (hc : ∀ v : V, ∃ n : ℕ, (casimir q - algebraMap ℂ (UqSl2 q) c) ^ n • v = 0) {μ : ℂ}
    {v : V} (hv : v ∈ weightSpace q V μ) (hv0 : v ≠ 0) (he : e q • v = 0) :
    ∃ (m : ℕ) (ε : ℤˣ), μ = ε * q ^ m ∧ c = casimirScalar q (ε * q ^ m) := by
  obtain ⟨m, ε, rfl, -, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq hv hv0 he
  refine ⟨m, ε, rfl, ?_⟩
  obtain ⟨n, hn⟩ := hc v
  have h1 : (casimir q - algebraMap ℂ (UqSl2 q) c) • v =
      (casimirScalar q (ε * q ^ m) - c) • v := by
    rw [sub_smul, algebraMap_smul, casimir_smul_of_e_smul_eq_zero hv he, sub_smul]
  rw [pow_smul_eq_of_smul_eq h1, smul_eq_zero] at hn
  exact (sub_eq_zero.mp (pow_eq_zero_iff'.mp (hn.resolve_right hv0)).1).symm

end FiniteDimensional

/-! ### The top generalized weight space -/

section Top

variable {m : ℕ} {ε : ℤˣ}

/-- For a vector `w` killed by `E` and by `F^(r+1)`, the commutator formula gives
`F^r (q^(-r) K w - q^r K⁻¹ w) = 0`. -/
private theorem f_pow_smul_k_smul_sub_kInv_smul (hq : IsGenericQuantumParameter q) {r : ℕ}
    {w : V} (he : e q • w = 0) (hf : f q ^ (r + 1) • w = 0) :
    f q ^ r • (q⁻¹ ^ r • k q • w - q ^ r • kInv q • w) = 0 := by
  have h := congrArg (· • w) (e_mul_f_pow hq.sub_inv_ne_zero (r + 1))
  simp only [mul_smul, add_smul, smul_assoc, hf, he, smul_zero, zero_add, Nat.add_sub_cancel,
    sub_smul, smul_sub] at h
  have hc : quantumInteger q ((r + 1 : ℕ) : ℤ) * (q - q⁻¹)⁻¹ ≠ 0 :=
    mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (inv_ne_zero hq.sub_inv_ne_zero)
  rw [smul_sub]
  generalize f q ^ r • q⁻¹ ^ r • k q • w = X at h ⊢
  generalize f q ^ r • q ^ r • kInv q • w = Y at h ⊢
  apply smul_right_injective V hc
  linear_combination (norm := module) -h

/-- For a vector `w` killed by `E` and by `F^(r+1)`, the vector `p = F^r w` satisfies
`K² p = q^(-2r) p`. -/
private theorem k_sq_smul_f_pow_smul (hq : IsGenericQuantumParameter q) {r : ℕ} {w : V}
    (he : e q • w = 0) (hf : f q ^ (r + 1) • w = 0) :
    k q ^ 2 • f q ^ r • w = (q⁻¹ ^ r) ^ 2 • f q ^ r • w := by
  have hq0 := hq.ne_zero
  set p := f q ^ r • w with hp_def
  -- Commute `F^r` past `K` and `K⁻¹`.
  have hk : k q • p = (q⁻¹ ^ 2) ^ r • f q ^ r • k q • w := by
    rw [hp_def, ← mul_smul, k_mul_f_pow, smul_assoc, mul_smul]
  have hkInv : kInv q • p = (q ^ 2) ^ r • f q ^ r • kInv q • w := by
    rw [hp_def, ← mul_smul, kInv_mul_f_pow, smul_assoc, mul_smul]
  clear_value p
  have h := f_pow_smul_k_smul_sub_kInv_smul hq he hf
  rw [smul_sub, smul_comm _ (q⁻¹ ^ r), smul_comm _ (q ^ r)] at h
  -- Hence `q^r K p = q^(-r) K⁻¹ p`, and applying `K` gives `K² p = q^(-2r) p`.
  have hqr : q ^ r * q⁻¹ ^ r = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
  have hmain : q ^ r • k q • p = q⁻¹ ^ r • kInv q • p := by
    have hX : q ^ r * (q⁻¹ ^ 2) ^ r = q⁻¹ ^ r := by
      rw [← pow_mul, mul_comm 2 r, pow_mul, sq, ← mul_assoc, hqr, one_mul]
    have hY : q⁻¹ ^ r * (q ^ 2) ^ r = q ^ r := by
      rw [← pow_mul, mul_comm 2 r, pow_mul, sq, ← mul_assoc, mul_comm (q⁻¹ ^ r), hqr, one_mul]
    rw [hk, hkInv]
    generalize f q ^ r • k q • w = X at h ⊢
    generalize f q ^ r • kInv q • w = Y at h ⊢
    linear_combination (norm := module) h + hX • X - hY • Y
  have h2 := congrArg (k q • ·) hmain
  simp only [smul_comm (k q) (q ^ r), smul_comm (k q) (q⁻¹ ^ r), ← mul_smul, k_mul_kInv,
    one_smul] at h2
  rw [sq (k q)]
  generalize (k q * k q) • p = Z at h2 ⊢
  linear_combination (norm := module) q⁻¹ ^ r • h2 - hqr • Z

/-- At a generic parameter, the weight `(q⁻²)^r ε q^m` differs from `± q^(-r)` unless `r = m`. -/
private theorem mul_inv_pow_ne_of_ne (hq : IsGenericQuantumParameter q) {r : ℕ} (hr : r ≠ m)
    {s : ℂ} (hs : s ^ 2 = 1) : s * q⁻¹ ^ r ≠ (q⁻¹ ^ 2) ^ r * (ε * q ^ m) := by
  intro h
  have hq0 := hq.ne_zero
  have a1 : q⁻¹ ^ r * q ^ (2 * r) = q ^ r := by
    rw [two_mul, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, one_mul]
  have a2 : (q⁻¹ ^ 2) ^ r * q ^ (2 * r) = 1 := by
    rw [← pow_mul, ← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  have h1 : (ε : ℂ) * q ^ m = s * q ^ r := by
    linear_combination -q ^ (2 * r) * h + s * a1 - (ε * q ^ m) * a2
  have h2 : q ^ (2 * m) = q ^ (2 * r) := by
    linear_combination (ε * q ^ m + s * q ^ r) * h1 - q ^ (2 * m) * units_sq ε +
      q ^ (2 * r) * hs
  exact hr (by have := hq.pow_injective h2; omega)

/-- On a generalized weight vector of weight `ε q^m` killed by `E`, the power `F^(r+1)` loses no
information beyond `F^r` unless `r = m`. -/
private theorem f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero (hq : IsGenericQuantumParameter q)
    {r : ℕ} (hr : r ≠ m) {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m)) (he : e q • w = 0)
    (hf : f q ^ (r + 1) • w = 0) : f q ^ r • w = 0 := by
  -- `F^r w` has generalized weight `(q⁻²)^r ε q^m`, while `K` acts on it by `q^(-r)`.
  have hp := f_pow_smul_mem_genWeightSpace hw r
  have hkp := k_smul_eq_of_k_sq_smul_eq
    (by simpa using mul_inv_pow_ne_of_ne hq hr (s := -1) (by norm_num)) hp
    (k_sq_smul_f_pow_smul hq he hf)
  exact eq_zero_of_mem_weightSpace_of_mem_genWeightSpace
    (by simpa using mul_inv_pow_ne_of_ne hq hr (s := 1) (by norm_num))
    (mem_weightSpace_iff.mpr hkp) hp

variable (hq : IsGenericQuantumParameter q)
  (hE : ∀ w ∈ genWeightSpace q V (ε * q ^ m), e q • w = 0)
include hq hE

/-- If `E` kills the generalized weight space of weight `ε q^m`, then `F^r` is injective on it
for `r ≤ m`. -/
private theorem eq_zero_of_f_pow_smul_eq_zero {r : ℕ} (hr : r ≤ m) {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) (hf : f q ^ r • w = 0) : w = 0 := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    exact ih (by omega)
      (f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero hq (by omega) hw (hE w hw) hf)

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, if `E` kills the generalized weight space of weight `ε q^m` in a
finite-dimensional module, then so does `F^(m+1)`. -/
theorem f_pow_smul_eq_zero_of_forall_e_smul_eq_zero {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) : f q ^ (m + 1) • w = 0 := by
  -- Some power `F^(m+1+n)` kills `w`; the exponent can be lowered one step at a time.
  obtain ⟨n, hn⟩ := exists_f_pow_smul_eq_zero hq w
  have hn' : f q ^ (m + 1 + n) • w = 0 := by
    rw [pow_add, mul_smul, hn, smul_zero]
  clear hn
  induction n with
  | zero => simpa using hn'
  | succ n ih =>
    exact ih (f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero hq (by omega) hw (hE w hw)
      (by simpa [add_assoc] using hn'))

/-- At a generic parameter, if `E` kills the generalized weight space of weight `ε q^m` in a
finite-dimensional module, then `K` acts on it by the scalar `ε q^m`: the generalized weight
space is an honest weight space. -/
theorem genWeightSpace_eq_weightSpace_of_forall_e_smul_eq_zero :
    genWeightSpace q V (ε * q ^ m) = weightSpace q V (ε * q ^ m) := by
  refine le_antisymm (fun w hw => ?_) (weightSpace_le_genWeightSpace _)
  have hq0 := hq.ne_zero
  -- `X w = q^(-m) K w - q^m K⁻¹ w` lies in the generalized weight space and is killed by `F^m`.
  have hX : q⁻¹ ^ m • k q • w - q ^ m • kInv q • w ∈ genWeightSpace q V (ε * q ^ m) :=
    sub_mem (Submodule.smul_mem _ _ (k_smul_mem_genWeightSpace hw))
      (Submodule.smul_mem _ _ (kInv_smul_mem_genWeightSpace hw))
  have hX0 := eq_zero_of_f_pow_smul_eq_zero hq hE le_rfl hX
    (f_pow_smul_k_smul_sub_kInv_smul hq (hE w hw)
      (f_pow_smul_eq_zero_of_forall_e_smul_eq_zero hq hE hw))
  -- Applying `K` to `X w = 0` gives `K² w = q^(2m) w = (ε q^m)² w`.
  have hk2 : k q ^ 2 • w = ((ε : ℂ) * q ^ m) ^ 2 • w := by
    have h := congrArg (fun x => q ^ m • k q • x) hX0
    simp only [smul_sub, smul_comm (k q) (q⁻¹ ^ m), smul_comm (k q) (q ^ m), ← mul_smul (k q),
      k_mul_kInv, one_smul, smul_smul, smul_zero, sub_eq_zero] at h
    have hqm : q ^ m * q⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
    rw [hqm, one_smul] at h
    rw [sq (k q), h, mul_pow, units_sq, one_mul, sq]
  have hne : -((ε : ℂ) * q ^ m) ≠ ε * q ^ m := fun h =>
    units_mul_pow_ne_zero ε m hq0 (by linear_combination -h / 2)
  exact mem_weightSpace_iff.mpr (k_smul_eq_of_k_sq_smul_eq hne hw hk2)

end Top

/-! ### Complete reducibility -/

section CasimirBlock

variable [FiniteDimensional ℂ V] (hq : IsGenericQuantumParameter q) {c : ℂ}
  (hc : ∀ v : V, ∃ n : ℕ, (casimir q - algebraMap ℂ (UqSl2 q) c) ^ n • v = 0)
  {m : ℕ} {ε : ℤˣ} (hcm : c = casimirScalar q (ε * q ^ m))
include hq hc hcm

/-- In a Casimir block with the Casimir scalar of `ε q^m`, every highest weight is `ε q^m`, so
`E` kills the generalized weight space of weight `ε q^m`. -/
private theorem e_smul_eq_zero_of_casimir_block {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) : e q • w = 0 := by
  by_contra h0
  -- A highest weight `(q²)^(n+1) ε q^m` above `ε q^m` would have the same Casimir scalar.
  obtain ⟨n, x, hx, hx0, hex⟩ := exists_highest_weight_vector_of_genWeightSpace_ne_bot hq
    ((Submodule.ne_bot_iff _).mpr ⟨_, e_smul_mem_genWeightSpace hw, h0⟩)
  obtain ⟨m', ε', hμ, hc'⟩ := exists_eq_casimirScalar_of_highest_weight_vector hq hc hx hx0 hex
  obtain ⟨hm, hε⟩ := (casimirScalar_units_mul_pow_inj hq).mp (hc'.symm.trans hcm)
  rw [hm, hε] at hμ
  refine hq.pow_ne_one (n := 2 * (n + 1)) (by omega)
    (mul_right_cancel₀ (units_mul_pow_ne_zero ε m hq.ne_zero) ?_)
  linear_combination hμ

/-- In a Casimir block with the Casimir scalar of `ε q^m`, a submodule containing the generalized
weight space of weight `ε q^m` is everything: otherwise the quotient would be a nonzero Casimir
block whose highest weight `ε q^m` is not a generalized weight. -/
private theorem eq_top_of_genWeightSpace_le_of_casimir_block {U : Submodule (UqSl2 q) V}
    (hU : genWeightSpace q V (ε * q ^ m) ≤ U.restrictScalars ℂ) : U = ⊤ := by
  by_contra hU'
  have : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU'
  have hc' (y : V ⧸ U) : ∃ n : ℕ, (casimir q - algebraMap ℂ (UqSl2 q) c) ^ n • y = 0 := by
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨n, hn⟩ := hc x
      exact ⟨n, by rw [← Submodule.Quotient.mk_smul, hn, Submodule.Quotient.mk_zero]⟩
  obtain ⟨μ, y, -, hy0, hky, hey⟩ := exists_highest_weight_vector hq (V := V ⧸ U)
  obtain ⟨m', ε', rfl, hcm'⟩ :=
    exists_eq_casimirScalar_of_highest_weight_vector hq hc' (mem_weightSpace_iff.mpr hky) hy0 hey
  obtain ⟨hm, hε⟩ := (casimirScalar_units_mul_pow_inj hq).mp (hcm'.symm.trans hcm)
  rw [hm, hε] at hky
  have hy := weightSpace_le_genWeightSpace _ (mem_weightSpace_iff.mpr hky)
  rw [← map_genWeightSpace_of_surjective (Submodule.mkQ_surjective U)] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hy0 ((Submodule.Quotient.mk_eq_zero U).mpr (hU hx))

/-- At a generic parameter, a finite-dimensional Casimir block, with the Casimir scalar of
`ε q^m`, is the sum of the images of module maps `L_m^ε → V`, hence semisimple. -/
private theorem isSemisimpleModule_of_casimir_block : IsSemisimpleModule (UqSl2 q) V := by
  have : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hE (w : V) (hw : w ∈ genWeightSpace q V (ε * q ^ m)) : e q • w = 0 :=
    e_smul_eq_zero_of_casimir_block hq hc hcm hw
  -- Each vector of `W` is the image of `v₀` under a module map from `L_m^ε`.
  have hW (w : genWeightSpace q V (ε * q ^ m)) : (w : V) ∈ weightSpace q V (ε * q ^ m) := by
    rw [← genWeightSpace_eq_weightSpace_of_forall_e_smul_eq_zero hq hE]
    exact w.2
  let L (w : genWeightSpace q V (ε * q ^ m)) : Submodule (UqSl2 q) V :=
    LinearMap.range (LadderModule.lift hq (hW w) (hE w w.2)
      (f_pow_smul_eq_zero_of_forall_e_smul_eq_zero hq hE w.2))
  have : IsSimpleModule (UqSl2 q) (LadderModule q m ε) := LadderModule.isSimpleModule hq
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := L) (fun w => IsSemisimpleModule.range _) ?_
  exact eq_top_of_genWeightSpace_le_of_casimir_block hq hc hcm fun w hw =>
    (le_iSup L ⟨w, hw⟩) ⟨LadderModule.vec q m ε 0, LadderModule.lift_vec_zero _ _ _ _⟩

end CasimirBlock

/-- At a generic parameter, a finite-dimensional module on which `Ω - c` is locally nilpotent
for a scalar `c` is semisimple. -/
private theorem isSemisimpleModule_of_casimir_sub_pow_smul_eq_zero [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) {c : ℂ}
    (hc : ∀ v : V, ∃ n : ℕ, (casimir q - algebraMap ℂ (UqSl2 q) c) ^ n • v = 0) :
    IsSemisimpleModule (UqSl2 q) V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact IsSemisimpleModule.of_sSup_simples_eq_top (Subsingleton.elim _ _)
  -- A highest-weight vector determines the pair `(m, ε)` of the Casimir block.
  obtain ⟨μ, v, -, hv0, hk, he⟩ := exists_highest_weight_vector hq (V := V)
  obtain ⟨m, ε, -, hcm⟩ :=
    exists_eq_casimirScalar_of_highest_weight_vector hq hc (mem_weightSpace_iff.mpr hk) hv0 he
  exact isSemisimpleModule_of_casimir_block hq hc hcm

/-- **Complete reducibility.** At a generic parameter, every finite-dimensional
`UqSl2 q`-module is semisimple. -/
theorem isSemisimpleModule_of_finiteDimensional [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) : IsSemisimpleModule (UqSl2 q) V := by
  -- The generalized eigenspaces of the central Casimir element are submodules.
  let Ω : Module.End ℂ V := Algebra.lsmul ℂ ℂ V (casimir q)
  have hmem {c : ℂ} {v : V} : v ∈ Ω.maxGenEigenspace c ↔
      ∃ n : ℕ, (casimir q - algebraMap ℂ (UqSl2 q) c) ^ n • v = 0 := by
    rw [Module.End.mem_maxGenEigenspace, ← Algebra.algebraMap_eq_smul_one,
      ← AlgHom.commutes (Algebra.lsmul ℂ ℂ V (A := UqSl2 q))]
    simp only [Ω, ← map_sub, ← map_pow, Algebra.lsmul_coe]
  let B (c : ℂ) : Submodule (UqSl2 q) V :=
    { toAddSubmonoid := (Ω.maxGenEigenspace c).toAddSubmonoid
      smul_mem' := fun a v hv => Module.End.mapsTo_maxGenEigenspace_of_comm
        ((commute_casimir a).symm.map (Algebra.lsmul ℂ ℂ V)) c hv }
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := B) (fun c => ?_) ?_
  · -- Each Casimir block is semisimple.
    have : FiniteDimensional ℂ (B c) :=
      Module.Finite.of_injective ((B c).subtype.restrictScalars ℂ) Subtype.val_injective
    refine isSemisimpleModule_of_casimir_sub_pow_smul_eq_zero hq (c := c) fun v => ?_
    obtain ⟨n, hn⟩ := hmem.mp v.2
    exact ⟨n, Subtype.ext hn⟩
  · -- The Casimir blocks span the finite-dimensional module.
    refine eq_top_iff.mpr fun v _ => ?_
    have hv : v ∈ ⨆ c, Ω.maxGenEigenspace c := by
      rw [Module.End.iSup_maxGenEigenspace_eq_top]
      exact Submodule.mem_top
    refine (iSup_le fun c => ?_ : ⨆ c, Ω.maxGenEigenspace c ≤ (⨆ c, B c).restrictScalars ℂ) hv
    exact fun w hw => Submodule.mem_iSup_of_mem (p := B) c hw

end TauCeti.UqSl2
