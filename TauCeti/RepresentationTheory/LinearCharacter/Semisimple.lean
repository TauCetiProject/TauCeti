/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.WeightSpace
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Splitting a linear character off a semisimple representation

A semisimple representation `ρ` of a monoid `G` over a field `k` with a nonzero vector `v` on which
`G` acts through a linear character `χ : G →* kˣ` contains the line of `χ` as a direct factor: the
line spanned by `v` is a subrepresentation, isomorphic to the line of `χ`, and semisimplicity gives
it a complementary subrepresentation `σ`, so that `ρ ≃ σ × χ`.

## Main results

* `Representation.exists_equiv_prod_ofLinearCharacter`: a semisimple representation with a
  nonzero vector of weight `χ` is the product of a subrepresentation and the line of `χ`.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **Splitting off a line.** A semisimple representation `ρ` with a nonzero vector on which `G`
acts through the linear character `χ` is the product of a subrepresentation and the line of
`χ`. -/
theorem exists_equiv_prod_ofLinearCharacter {ρ : Representation k G V}
    [ρ.IsSemisimpleRepresentation] {χ : G →* kˣ}
    (h : ρ.weightSpace ((Units.coeHom k).comp χ) ≠ ⊥) :
    ∃ σ : Subrepresentation ρ,
      Nonempty (ρ.Equiv (σ.toRepresentation.prod (ofLinearCharacter χ))) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  -- the line through `v` is the image of the line of `χ` under `t ↦ t • v`
  let f : IntertwiningMap (ofLinearCharacter χ) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g t ↦ by
      simp [ofLinearCharacter_apply, mem_weightSpace.mp hv g, smul_smul, mul_comm]
  have hf : Function.Injective f := fun s t hst ↦ smul_left_injective k hv0 hst
  obtain ⟨σ, hσ⟩ := exists_isCompl f.range
  exact ⟨σ, ⟨(Subrepresentation.equivProdOfIsCompl hσ.symm).trans
    ((Equiv.refl _).prodCongr
      (f.equivOfRange hf (IntertwiningMap.range_toSubmodule _ _ f).symm).symm)⟩⟩

end Representation
