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

as left `U(L)`-modules, where the tensor product is the extension of scalars
`TauCeti.BalancedExtension` along the algebra map `U(𝔟) → U(L)` induced by the inclusion `𝔟 → L`,
and `U(𝔟)` acts on `K_lam` through the Borel character
`TauCeti.borelCharacter H b lam`, `h + n ↦ lam h`. The equivalence sends `1 ⊗ 1` to the canonical
generator `v_lam`, and more generally `u ⊗ a` to `a • (u · v_lam)`.

It specializes `LieSubalgebra.balancedExtensionEquivQuotient` along
`TauCeti.vermaIdeal_eq_span_range_ι_sub_algebraMap`. The comparison does not use that `M(lam)` is
nonzero.

## Main definitions

* `TauCeti.balancedExtensionEquivVermaModule`: the `U(L)`-linear equivalence
  `U(L) ⊗_{U(𝔟)} K_lam ≃ M(lam)`.

## Main results

* `TauCeti.balancedExtensionEquivVermaModule_tmul` and
  `TauCeti.balancedExtensionEquivVermaModule_tmul_one_one`: the equivalence sends `u ⊗ a` to
  `a • [u]`, and `1 ⊗ 1` to the canonical generator.
* `TauCeti.balancedExtensionEquivVermaModule_symm_vermaMk` and
  `TauCeti.balancedExtensionEquivVermaModule_symm_vermaGenerator`: its inverse sends `[u]` to
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
local notation "Φ" => RingHomClass.toRingHom
  (UniversalEnvelopingAlgebra.map K (LieSubalgebra.incl (borelSubalgebra H b)))

/-- **The Verma module is induced from the Borel subalgebra.** The extension of scalars
`U(L) ⊗_{U(𝔟)} K_lam`, along the algebra map `U(𝔟) → U(L)`, of the one-dimensional `U(𝔟)`-module
of the Borel character of weight `lam` is isomorphic as a left `U(L)`-module to the Verma module
`M(lam)`. The isomorphism sends `1 ⊗ 1` to the canonical generator
(`balancedExtensionEquivVermaModule_tmul_one_one`). -/
noncomputable def balancedExtensionEquivVermaModule :
    letI := (borelCharacter H b lam).envelopingModule
    BalancedExtension Φ K ≃ₗ[U] VermaModule b lam :=
  ((borelSubalgebra H b).balancedExtensionEquivQuotient (borelCharacter H b lam)).trans <|
    (Submodule.quotEquivOfEq _ _ <| (vermaIdeal_eq_span_range_ι_sub_algebraMap b lam).symm.trans <|
      Submodule.ext fun _ ↦ (vermaMk_eq_zero_iff b lam).symm).trans <|
    (vermaMk b lam).quotKerEquivOfSurjective (vermaMk_surjective b lam)

/-- The induced-module comparison sends `u ⊗ a` to `a • [u]`. -/
@[simp]
theorem balancedExtensionEquivVermaModule_tmul (w : U) (a : K) :
    letI := (borelCharacter H b lam).envelopingModule
    balancedExtensionEquivVermaModule b lam (BalancedExtension.tmul Φ w a) =
      a • vermaMk b lam w := by
  let := (borelCharacter H b lam).envelopingModule
  rw [balancedExtensionEquivVermaModule, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LieSubalgebra.balancedExtensionEquivQuotient_tmul, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.map_smul_of_tower]

/-- The induced-module comparison sends `1 ⊗ 1` to the canonical generator `v_lam`. -/
theorem balancedExtensionEquivVermaModule_tmul_one_one :
    letI := (borelCharacter H b lam).envelopingModule
    balancedExtensionEquivVermaModule b lam (BalancedExtension.tmul Φ 1 1) =
      vermaGenerator b lam := by
  let := (borelCharacter H b lam).envelopingModule
  rw [balancedExtensionEquivVermaModule_tmul, one_smul, ← smul_vermaGenerator, one_smul]

/-- The inverse of the induced-module comparison sends `[u]` to `u ⊗ 1`. -/
@[simp]
theorem balancedExtensionEquivVermaModule_symm_vermaMk (w : U) :
    letI := (borelCharacter H b lam).envelopingModule
    (balancedExtensionEquivVermaModule b lam).symm (vermaMk b lam w) =
      BalancedExtension.tmul Φ w 1 := by
  let := (borelCharacter H b lam).envelopingModule
  rw [LinearEquiv.symm_apply_eq, balancedExtensionEquivVermaModule_tmul, one_smul]

/-- The inverse of the induced-module comparison sends the canonical generator to `1 ⊗ 1`. -/
@[simp]
theorem balancedExtensionEquivVermaModule_symm_vermaGenerator :
    letI := (borelCharacter H b lam).envelopingModule
    (balancedExtensionEquivVermaModule b lam).symm (vermaGenerator b lam) =
      BalancedExtension.tmul Φ 1 1 := by
  let := (borelCharacter H b lam).envelopingModule
  rw [LinearEquiv.symm_apply_eq, balancedExtensionEquivVermaModule_tmul_one_one]

end TauCeti
