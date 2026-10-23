/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.HighestWeight
public import TauCeti.QuantumGroups.UqSl2.LadderModule

/-!
# Classification of the finite-dimensional simple `U_q(sl₂)`-modules

At a generic parameter `q` (nonzero and not a root of unity), every nonzero finite-dimensional
module has a highest-weight vector whose lowering string forces its weight to be `ε q^m`, because
the spectrum of `K` is finite; no diagonalizability of `K` is assumed. The universal property of
`LadderModule.lift` makes the resulting map from `L_m^ε` an isomorphism when the target is simple.
Together with the pairwise non-isomorphism of the ladder modules, this shows that at a generic
parameter every finite-dimensional simple `UqSl2 q`-module is isomorphic to exactly one `L_m^ε`.

## Main results

* `TauCeti.UqSl2.exists_linearEquiv_ladderModule`: at a generic parameter, every
  finite-dimensional simple `UqSl2 q`-module is isomorphic to a signed ladder module.
* `TauCeti.UqSl2.existsUnique_linearEquiv_ladderModule`: at a generic parameter, every
  finite-dimensional simple `UqSl2 q`-module is isomorphic to `L_m^ε` for exactly one pair
  `(m, ε)`.

## References

* A. Virelizier, *Quantum groups*, Section 2.4.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3.
-/

public noncomputable section

open Module

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

variable [Fact (q ≠ 0)] [FiniteDimensional ℂ V] [IsSimpleModule (UqSl2 q) V]

/-- At a generic parameter, every finite-dimensional simple `UqSl2 q`-module is isomorphic to a
signed ladder module `L_m^ε`. -/
theorem exists_linearEquiv_ladderModule (hq : IsGenericQuantumParameter q) :
    ∃ (m : ℕ) (ε : ℤˣ), Nonempty (LadderModule q m ε ≃ₗ[UqSl2 q] V) := by
  have : Nontrivial V := IsSimpleModule.nontrivial (UqSl2 q) V
  obtain ⟨μ, v, -, hv0, hk, he⟩ := exists_highest_weight_vector hq (V := V)
  have hv : v ∈ weightSpace q V μ := mem_weightSpace_iff.mpr hk
  obtain ⟨m, ε, rfl, hf, -⟩ := exists_eq_sign_mul_pow_of_highest_weight_vector hq hv hv0 he
  have := LadderModule.isSimpleModule (m := m) (ε := ε) hq
  have hne : LadderModule.lift hq hv he hf ≠ 0 := fun h0 => hv0 <| by
    rw [← LadderModule.lift_vec_zero hq hv he hf, h0, LinearMap.zero_apply]
  exact ⟨m, ε, ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hne)⟩⟩

/-- **Classification of finite-dimensional simple `U_q(sl₂)`-modules.** At a generic parameter,
every finite-dimensional simple `UqSl2 q`-module is isomorphic to `L_m^ε` for exactly one
natural number `m` and sign `ε`. -/
theorem existsUnique_linearEquiv_ladderModule (hq : IsGenericQuantumParameter q) :
    ∃! p : ℕ × ℤˣ, Nonempty (LadderModule q p.1 p.2 ≃ₗ[UqSl2 q] V) := by
  obtain ⟨m, ε, ⟨φ⟩⟩ := exists_linearEquiv_ladderModule hq (V := V)
  refine ⟨(m, ε), ⟨φ⟩, fun ⟨n, δ⟩ ⟨ψ⟩ => ?_⟩
  obtain ⟨rfl, rfl⟩ := (LadderModule.nonempty_linearEquiv_iff hq).mp ⟨ψ.trans φ.symm⟩
  rfl

end TauCeti.UqSl2
