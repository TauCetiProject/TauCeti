/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Casimir
public import TauCeti.QuantumGroups.UqSl2.HighestWeight
public import TauCeti.QuantumGroups.UqSl2.LadderModule
public import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.Algebra.Ring.Int.Units
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

* `TauCeti.UqSl2.genWeightSpace_eq_weightSpace_of_forall_e_smul_eq_zero` and
  `TauCeti.UqSl2.f_pow_smul_eq_zero_of_forall_e_smul_eq_zero`: if `E` kills the generalized
  weight space of weight `ε q^m`, then `K` acts on it by `ε q^m` and `F^(m+1)` kills it.
* `TauCeti.UqSl2.eq_zero_of_f_pow_smul_eq_zero`: if `E` kills the generalized weight space of
  weight `ε q^m`, then `F^r` is injective on it for `r ≤ m`.
* `TauCeti.UqSl2.e_smul_eq_zero_of_casimirBlock_eq_top`: in a module equal to its Casimir block
  for the Casimir scalar of `ε q^m`, `E` kills the generalized weight space of weight `ε q^m`.
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

/-- In a module equal to its Casimir block for `c`, a nonzero vector of weight `μ` killed by `E`
has weight `ε q^m`, where `c` is the Casimir scalar of `ε q^m`. -/
private theorem exists_eq_casimirScalar_of_highest_weight_vector [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) {c : ℂ} (hc : casimirBlock q V c = ⊤) {μ : ℂ}
    {v : V} (hv : v ∈ weightSpace q V μ) (hv0 : v ≠ 0) (he : e q • v = 0) :
    ∃ (m : ℕ) (ε : ℤˣ), μ = ε * q ^ m ∧ c = casimirScalar q (ε * q ^ m) := by
  obtain ⟨m, ε, rfl, -, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq hv hv0 he
  refine ⟨m, ε, rfl, ?_⟩
  obtain ⟨n, hn⟩ := mem_casimirBlock_iff.mp (hc ▸ Submodule.mem_top : v ∈ casimirBlock q V c)
  -- `v` is an eigenvector of `Ω - c` with eigenvalue `casimirScalar q (ε q^m) - c`.
  have h1 : (Algebra.lsmul ℂ ℂ V (casimir q - algebraMap ℂ (UqSl2 q) c)).HasEigenvector
      (casimirScalar q (ε * q ^ m) - c) v := by
    refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv0⟩
    simp only [Algebra.lsmul_coe]
    rw [sub_smul, algebraMap_smul, casimir_smul_of_e_smul_eq_zero hv he, sub_smul]
  have h2 := h1.pow_apply n
  simp only [← map_pow, Algebra.lsmul_coe] at h2
  rw [hn, eq_comm, smul_eq_zero] at h2
  exact (sub_eq_zero.mp (pow_eq_zero_iff'.mp (h2.resolve_right hv0)).1).symm

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
  have hqr : q ^ r * q⁻¹ ^ r = 1 := by simp [hq0]
  have hmain : q ^ r • k q • p = q⁻¹ ^ r • kInv q • p := by
    have hX : q ^ r * (q⁻¹ ^ 2) ^ r = q⁻¹ ^ r := by linear_combination q⁻¹ ^ r * hqr
    have hY : q⁻¹ ^ r * (q ^ 2) ^ r = q ^ r := by linear_combination q ^ r * hqr
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
  have hqr : q ^ r * q⁻¹ ^ r = 1 := by simp [hq0]
  have a1 : q⁻¹ ^ r * q ^ (2 * r) = q ^ r := by linear_combination q ^ r * hqr
  have a2 : (q⁻¹ ^ 2) ^ r * q ^ (2 * r) = 1 := by
    linear_combination (q ^ r * q⁻¹ ^ r + 1) * hqr
  have hε := Int.cast_units_sq (R := ℂ) ε
  have h1 : (ε : ℂ) * q ^ m = s * q ^ r := by
    linear_combination -q ^ (2 * r) * h + s * a1 - (ε * q ^ m) * a2
  have h2 : q ^ (2 * m) = q ^ (2 * r) := by
    linear_combination (ε * q ^ m + s * q ^ r) * h1 - q ^ (2 * m) * hε +
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
theorem eq_zero_of_f_pow_smul_eq_zero {r : ℕ} (hr : r ≤ m) {w : V}
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
    have hqm : q ^ m * q⁻¹ ^ m = 1 := by simp [hq0]
    rw [hqm, one_smul] at h
    rw [sq (k q), h, mul_pow, Int.cast_units_sq, one_mul, sq]
  have hne : -((ε : ℂ) * q ^ m) ≠ ε * q ^ m := fun h =>
    mul_ne_zero (Int.cast_ne_zero.mpr ε.ne_zero) (pow_ne_zero _ hq0) (by linear_combination -h / 2)
  exact mem_weightSpace_iff.mpr (k_smul_eq_of_k_sq_smul_eq hne hw hk2)

end Top

/-! ### Complete reducibility -/

section CasimirBlock

variable [FiniteDimensional ℂ V] (hq : IsGenericQuantumParameter q) {m : ℕ} {ε : ℤˣ}
  (hc : casimirBlock q V (casimirScalar q (ε * q ^ m)) = ⊤)
include hq hc

/-- In a module equal to its Casimir block for the Casimir scalar of `ε q^m`, every highest
weight is `ε q^m`, so `E` kills the generalized weight space of weight `ε q^m`. -/
theorem e_smul_eq_zero_of_casimirBlock_eq_top {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) : e q • w = 0 := by
  by_contra h0
  -- A highest weight `(q²)^(n+1) ε q^m` above `ε q^m` would have the same Casimir scalar.
  obtain ⟨n, x, hx, hx0, hex⟩ := exists_highest_weight_vector_of_genWeightSpace_ne_bot hq
    ((Submodule.ne_bot_iff _).mpr ⟨_, e_smul_mem_genWeightSpace hw, h0⟩)
  obtain ⟨m', ε', hμ, hc'⟩ := exists_eq_casimirScalar_of_highest_weight_vector hq hc hx hx0 hex
  obtain ⟨hm, hε⟩ := (casimirScalar_units_mul_pow_inj hq).mp hc'.symm
  rw [hm, hε] at hμ
  have hε0 : (ε : ℂ) * q ^ m ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ε.ne_zero) (pow_ne_zero _ hq.ne_zero)
  refine hq.pow_ne_one (n := 2 * (n + 1)) (by omega) (mul_right_cancel₀ hε0 ?_)
  linear_combination hμ

/-- In a module equal to its Casimir block for the Casimir scalar of `ε q^m`, a submodule
containing the generalized weight space of weight `ε q^m` is everything: otherwise the quotient
would be a nonzero Casimir block whose highest weight `ε q^m` is not a generalized weight. -/
private theorem eq_top_of_genWeightSpace_le_of_casimirBlock_eq_top {U : Submodule (UqSl2 q) V}
    (hU : genWeightSpace q V (ε * q ^ m) ≤ U.restrictScalars ℂ) : U = ⊤ := by
  by_contra hU'
  have : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU'
  have hc' : casimirBlock q (V ⧸ U) (casimirScalar q (ε * q ^ m)) = ⊤ := by
    refine top_unique ?_
    rw [← LinearMap.range_eq_top.mpr U.mkQ_surjective, LinearMap.range_eq_map, ← hc]
    exact map_casimirBlock_le _ _
  obtain ⟨μ, y, -, hy0, hky, hey⟩ := exists_highest_weight_vector hq (V := V ⧸ U)
  obtain ⟨m', ε', rfl, hcm'⟩ :=
    exists_eq_casimirScalar_of_highest_weight_vector hq hc' (mem_weightSpace_iff.mpr hky) hy0 hey
  obtain ⟨hm, hε⟩ := (casimirScalar_units_mul_pow_inj hq).mp hcm'.symm
  rw [hm, hε] at hky
  have hy := weightSpace_le_genWeightSpace _ (mem_weightSpace_iff.mpr hky)
  rw [← map_genWeightSpace_eq_of_surjective (Submodule.mkQ_surjective U)] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hy0 ((Submodule.Quotient.mk_eq_zero U).mpr (hU hx))

/-- At a generic parameter, a finite-dimensional module equal to its Casimir block for the Casimir
scalar of `ε q^m` is the sum of the images of module maps `L_m^ε → V`, hence semisimple. -/
private theorem isSemisimpleModule_of_casimirBlock_casimirScalar_eq_top :
    IsSemisimpleModule (UqSl2 q) V := by
  have : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hE (w : V) (hw : w ∈ genWeightSpace q V (ε * q ^ m)) : e q • w = 0 :=
    e_smul_eq_zero_of_casimirBlock_eq_top hq hc hw
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
  exact eq_top_of_genWeightSpace_le_of_casimirBlock_eq_top hq hc fun w hw =>
    (le_iSup L ⟨w, hw⟩) ⟨LadderModule.vec q m ε 0, LadderModule.lift_vec_zero _ _ _ _⟩

end CasimirBlock

/-- At a generic parameter, a finite-dimensional module equal to its Casimir block for some
scalar `c` is semisimple. -/
private theorem isSemisimpleModule_of_casimirBlock_eq_top [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) {c : ℂ} (hc : casimirBlock q V c = ⊤) :
    IsSemisimpleModule (UqSl2 q) V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact IsSemisimpleModule.of_sSup_simples_eq_top (Subsingleton.elim _ _)
  -- A highest-weight vector determines the pair `(m, ε)` of the Casimir block.
  obtain ⟨μ, v, -, hv0, hk, he⟩ := exists_highest_weight_vector hq (V := V)
  obtain ⟨m, ε, -, rfl⟩ :=
    exists_eq_casimirScalar_of_highest_weight_vector hq hc (mem_weightSpace_iff.mpr hk) hv0 he
  exact isSemisimpleModule_of_casimirBlock_casimirScalar_eq_top hq hc

/-- **Complete reducibility.** At a generic parameter, every finite-dimensional
`UqSl2 q`-module is semisimple. -/
theorem isSemisimpleModule_of_finiteDimensional [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) : IsSemisimpleModule (UqSl2 q) V := by
  -- Each Casimir block is semisimple, and the Casimir blocks span the module.
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := casimirBlock q V) (fun c => ?_)
    iSup_casimirBlock_eq_top
  have : FiniteDimensional ℂ (casimirBlock q V c) :=
    Module.Finite.of_injective ((casimirBlock q V c).subtype.restrictScalars ℂ)
      Subtype.val_injective
  exact isSemisimpleModule_of_casimirBlock_eq_top hq (casimirBlock_casimirBlock_eq_top c)

end TauCeti.UqSl2
