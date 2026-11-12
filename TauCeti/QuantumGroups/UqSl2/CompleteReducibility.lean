/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Casimir.Basic
public import TauCeti.QuantumGroups.UqSl2.HighestWeight
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic

/-!
# Complete reducibility of finite-dimensional `U_q(sl₂)`-modules

At a generic parameter `q` (nonzero and not a root of unity), every finite-dimensional
`UqSl2 q`-module is semisimple. No diagonalizability of `K` is assumed.

Along the way, taking generalized weight spaces is shown to be exact.

## Implementation notes

The proof splits a finite-dimensional module into the generalized eigenspaces of the central
Casimir element `Ω`. Every highest-weight vector in such a Casimir block has weight `ε q^m` for one
fixed pair `(m, ε)`, so `E` kills the generalized weight space `W` of weight `ε q^m`. By the
highest-weight results `F^(m+1)` vanishes on `W` and `K` acts on `W` by the scalar `ε q^m`
(`TauCeti.UqSl2.mem_weightSpace_of_e_smul_eq_zero`). Every vector of `W` is therefore the image
of `v₀` under a module map from the ladder module `L_m^ε`, and these images span a semisimple
submodule `U ⊇ W`. Taking generalized weight spaces is exact, so the quotient by `U` has no
generalized weight `ε q^m`; being a Casimir block with the same scalar, it is zero.

## Main results

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
  exact ⟨m, ε, rfl, (casimirScalar_eq_of_mem_casimirBlock hv he (hc ▸ Submodule.mem_top) hv0).symm⟩

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
  have hW (w : genWeightSpace q V (ε * q ^ m)) : (w : V) ∈ weightSpace q V (ε * q ^ m) :=
    mem_weightSpace_of_e_smul_eq_zero hq w.2 (hE w w.2)
  let L (w : genWeightSpace q V (ε * q ^ m)) : Submodule (UqSl2 q) V :=
    LinearMap.range (LadderModule.lift hq (hW w) (hE w w.2)
      (f_pow_smul_eq_zero_of_e_smul_eq_zero hq w.2 (hE w w.2)))
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
  exact isSemisimpleModule_of_casimirBlock_eq_top hq (casimirBlock_casimirBlock_eq_top c)

end TauCeti.UqSl2
