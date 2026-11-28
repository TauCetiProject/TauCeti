/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Tensor.External
import TauCeti.RingTheory.TensorProduct.Finite

/-!
# A representation of `C₂ × C₂` that is not an external tensor product

Irreducibility cannot be dropped from
`Representation.exists_isIrreducible_nonempty_equiv_externalTensor` (and simplicity cannot be
dropped from `FDRep.externalTensor_classification`), which write every finite-dimensional
irreducible representation of a product `G × H` over an algebraically closed field as an external
tensor product.

Write `C₂ = ℤˣ`, with trivial representation `1` and sign representation `sgn` on `ℂ`. The
representation `τ = 1 ⊠ 1 ⊕ sgn ⊠ sgn` of `C₂ × C₂` on `ℂ²`, a sum of two lines, is not
equivalent to an external tensor product `ρ ⊠ σ` of representations of the two factors, of any
dimensions. Its character matrix `(χ_τ(g, h))_{g, h ∈ C₂}` is `2` times the identity, of rank two,
whereas the character `χ_ρ(g) χ_σ(h)` of an external tensor product has rank at most one:
`χ(1, 1) χ(-1, -1) = 4` but `χ(-1, 1) χ(1, -1) = 0`.
-/

public section

open Representation TensorProduct

namespace TauCeti.Examples.NotExternalTensor

/-- The sign character `ℤˣ →* ℂˣ` of `C₂ = ℤˣ`. -/
noncomputable def signChar : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ).toMonoidHom

/-- The trivial representation of `C₂`, as the linear character `1`. -/
noncomputable abbrev trivialRep : Representation ℂ ℤˣ ℂ := ofLinearCharacter 1

/-- The sign representation of `C₂` on `ℂ`. -/
noncomputable abbrev signRep : Representation ℂ ℤˣ ℂ := ofLinearCharacter signChar

/-- The representation `1 ⊠ 1 ⊕ sgn ⊠ sgn` of `C₂ × C₂`. -/
noncomputable abbrev τ : Representation ℂ (ℤˣ × ℤˣ) ((ℂ ⊗[ℂ] ℂ) × (ℂ ⊗[ℂ] ℂ)) :=
  (trivialRep.externalTensor trivialRep).prod (signRep.externalTensor signRep)

/-- The character of `τ` is `χ_τ(g, h) = 1 + g h`. -/
theorem char_τ (p : ℤˣ × ℤˣ) : τ.character p = 1 + ((p.1 : ℤ) : ℂ) * ((p.2 : ℤ) : ℂ) := by
  simp [signChar]

/-- **The character matrix of `τ` has rank two**: `χ(1, 1) χ(-1, -1) = 4` but
`χ(-1, 1) χ(1, -1) = 0`. -/
theorem char_τ_mul_ne :
    τ.character (1, 1) * τ.character (-1, -1) ≠ τ.character (-1, 1) * τ.character (1, -1) := by
  simp only [char_τ, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  norm_num

/-- **`τ` is not an external tensor product**: for no representations `ρ` and `σ` of `C₂` is
`τ ≃ ρ ⊠ σ`, because the character of `ρ ⊠ σ` is `χ_ρ(g) χ_σ(h)`, whose matrix has rank at most
one. -/
theorem not_nonempty_equiv_externalTensor {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ ℤˣ V) (σ : Representation ℂ ℤˣ W) :
    ¬ Nonempty (Representation.Equiv τ (ρ.externalTensor σ)) := by
  rintro ⟨e⟩
  have : FiniteDimensional ℂ (V ⊗[ℂ] W) := e.toLinearEquiv.finiteDimensional
  -- `V ⊗ W ≃ ℂ²` is nonzero, so both factors are nonzero, hence finite-dimensional.
  have : Nontrivial (ℂ ⊗[ℂ] ℂ) := (TensorProduct.lid ℂ ℂ).symm.injective.nontrivial
  have : Nontrivial (V ⊗[ℂ] W) := e.toLinearEquiv.injective.nontrivial
  have : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (V ⊗[ℂ] W) inferInstance
  have : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (V ⊗[ℂ] W) inferInstance
  have : FiniteDimensional ℂ V := Module.Finite.of_tensorProduct_left (N := W) inferInstance
  have : FiniteDimensional ℂ W :=
    Module.Finite.of_tensorProduct_left (N := V) (TensorProduct.comm ℂ V W).finiteDimensional
  apply char_τ_mul_ne
  simp only [char_iso e, char_externalTensor]
  ring

end TauCeti.Examples.NotExternalTensor
