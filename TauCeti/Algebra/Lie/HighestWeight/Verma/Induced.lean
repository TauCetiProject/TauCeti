/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.UniversalEnveloping.Induced

/-!
# The Verma module as an induced module

The Verma module `M(lam)` of `TauCeti/Algebra/Lie/HighestWeight/Verma.lean` is defined as the
quotient of `U(L)` by the left ideal of Verma relations. This file proves that it is the module
induced from the one-dimensional module `K_lam` of the Borel subalgebra `𝔟`:

`U(L) ⊗_{U(𝔟)} K_lam ≃ M(lam)`

as left `U(L)`-modules, where `U(L)` is a right `U(𝔟)`-module through the algebra map induced by
the inclusion `𝔟 → L`, and `U(𝔟)` acts on `K_lam` through the Borel character
`TauCeti.borelCharacter H b lam`, `h + n ↦ lam h`. The equivalence sends `1 ⊗ 1` to the canonical
generator `v_lam`, and more generally `u ⊗ a` to `a • (u · v_lam)`.

It specializes `LieSubalgebra.balancedTensorProductEquivQuotient` along
`TauCeti.vermaIdeal_eq_span_range_ι_sub_algebraMap`. The comparison does not use that `M(lam)` is
nonzero.

## Main definitions

* `TauCeti.balancedTensorProductEquivVermaModule`: the `U(L)`-linear equivalence
  `U(L) ⊗_{U(𝔟)} K_lam ≃ M(lam)`.

## Main results

* `TauCeti.balancedTensorProductEquivVermaModule_tmul` and
  `TauCeti.balancedTensorProductEquivVermaModule_tmul_one_one`: the equivalence sends `u ⊗ a` to
  `a • [u]`, and `1 ⊗ 1` to the canonical generator.
* `TauCeti.balancedTensorProductEquivVermaModule_symm_vermaMk` and
  `TauCeti.balancedTensorProductEquivVermaModule_symm_vermaGenerator`: its inverse sends `[u]` to
  `u ⊗ 1`, and the canonical generator to `1 ⊗ 1`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §20.3.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base) (lam : Dual K H)

local notation "U" => _root_.UniversalEnvelopingAlgebra K L
local notation "U𝔟" => _root_.UniversalEnvelopingAlgebra K (borelSubalgebra H b)

attribute [local instance] LieSubalgebra.envelopingRightModule
  LieSubalgebra.smulCommClass_envelopingRightModule
attribute [local instance] BalancedTensorProduct.leftModule

/-- **The Verma module is induced from the Borel subalgebra.** The tensor product
`U(L) ⊗_{U(𝔟)} K_lam`, of `U(L)` as a right `U(𝔟)`-module and the one-dimensional `U(𝔟)`-module of
the Borel character of weight `lam`, is isomorphic as a left `U(L)`-module to the Verma module
`M(lam)`. The isomorphism sends `1 ⊗ 1` to the canonical generator
(`balancedTensorProductEquivVermaModule_tmul_one_one`). -/
noncomputable def balancedTensorProductEquivVermaModule :
    letI := (borelCharacter H b lam).envelopingModule
    BalancedTensorProduct K U𝔟 U K ≃ₗ[U] VermaModule b lam :=
  ((borelSubalgebra H b).balancedTensorProductEquivQuotient (borelCharacter H b lam)).trans <|
    (Submodule.quotEquivOfEq _ _ <| (vermaIdeal_eq_span_range_ι_sub_algebraMap b lam).symm.trans <|
      Submodule.ext fun _ ↦ (vermaMk_eq_zero_iff b lam).symm).trans <|
    (vermaMk b lam).quotKerEquivOfSurjective (vermaMk_surjective b lam)

/-- The induced-module comparison sends `u ⊗ a` to `a • [u]`. -/
@[simp]
theorem balancedTensorProductEquivVermaModule_tmul (w : U) (a : K) :
    letI := (borelCharacter H b lam).envelopingModule
    balancedTensorProductEquivVermaModule b lam (BalancedTensorProduct.tmul K U𝔟 w a) =
      a • vermaMk b lam w := by
  let := (borelCharacter H b lam).envelopingModule
  rw [balancedTensorProductEquivVermaModule, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LieSubalgebra.balancedTensorProductEquivQuotient_tmul, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.map_smul_of_tower]

/-- The induced-module comparison sends `1 ⊗ 1` to the canonical generator `v_lam`. -/
theorem balancedTensorProductEquivVermaModule_tmul_one_one :
    letI := (borelCharacter H b lam).envelopingModule
    balancedTensorProductEquivVermaModule b lam (BalancedTensorProduct.tmul K U𝔟 1 1) =
      vermaGenerator b lam := by
  let := (borelCharacter H b lam).envelopingModule
  rw [balancedTensorProductEquivVermaModule_tmul, one_smul, ← smul_vermaGenerator, one_smul]

/-- The inverse of the induced-module comparison sends `[u]` to `u ⊗ 1`. -/
@[simp]
theorem balancedTensorProductEquivVermaModule_symm_vermaMk (w : U) :
    letI := (borelCharacter H b lam).envelopingModule
    (balancedTensorProductEquivVermaModule b lam).symm (vermaMk b lam w) =
      BalancedTensorProduct.tmul K U𝔟 w 1 := by
  let := (borelCharacter H b lam).envelopingModule
  rw [LinearEquiv.symm_apply_eq, balancedTensorProductEquivVermaModule_tmul, one_smul]

/-- The inverse of the induced-module comparison sends the canonical generator to `1 ⊗ 1`. -/
@[simp]
theorem balancedTensorProductEquivVermaModule_symm_vermaGenerator :
    letI := (borelCharacter H b lam).envelopingModule
    (balancedTensorProductEquivVermaModule b lam).symm (vermaGenerator b lam) =
      BalancedTensorProduct.tmul K U𝔟 1 1 := by
  let := (borelCharacter H b lam).envelopingModule
  rw [LinearEquiv.symm_apply_eq, balancedTensorProductEquivVermaModule_tmul_one_one]

end TauCeti
