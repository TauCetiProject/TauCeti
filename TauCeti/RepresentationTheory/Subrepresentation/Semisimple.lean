/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Subrepresentations of a semisimple representation

A representation is semisimple when every subrepresentation has a complementary subrepresentation
(`Representation.IsSemisimpleRepresentation`). This file records two consequences.

A representation that maps injectively and equivariantly into a semisimple one is semisimple
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`). This is Mathlib's
`IsSemisimpleModule.of_injective` for the modules over the group algebra.

Every subrepresentation `S` of a semisimple representation has an equivariant projection onto it
(`Subrepresentation.exists_equivariant_projection`): the first component of the splitting
`Subrepresentation.equivProdOfIsCompl` along a complement of `S`.

## Main results

* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`: a representation with
  an injective intertwining map into a semisimple representation is semisimple.
* `Subrepresentation.exists_equivariant_projection`: a subrepresentation of a semisimple
  representation has an equivariant projection onto it.
-/

public section

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] {ρ : Representation k G W}

/-- **A representation embedding into a semisimple one is semisimple.** If `f : σ → ρ` is an
injective intertwining map and `ρ` is semisimple, then `σ` is semisimple. -/
theorem Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective
    {σ : Representation k G V} [ρ.IsSemisimpleRepresentation] (f : σ.IntertwiningMap ρ)
    (hf : Function.Injective f) : σ.IsSemisimpleRepresentation := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mpr
    (IsSemisimpleModule.of_injective (equivLinearMapAsModule σ ρ f) hf)

namespace Subrepresentation

/-- **Equivariant projection onto a subrepresentation.** Every subrepresentation `S` of a
semisimple representation `ρ` has a `G`-equivariant linear projection `P : W → S`. It is the first
component of the splitting of `ρ` along a complement of `S`. -/
theorem exists_equivariant_projection [ρ.IsSemisimpleRepresentation] (S : Subrepresentation ρ) :
    ∃ P : W →ₗ[k] S.toSubmodule, (∀ x : S.toSubmodule, P x = x) ∧
      ∀ g w, (P (ρ g w) : W) = ρ g (P w) := by
  obtain ⟨C, h⟩ := exists_isCompl S
  let e := equivProdOfIsCompl h
  refine ⟨LinearMap.fst k S.toSubmodule C.toSubmodule ∘ₗ e.toLinearMap, fun x ↦ ?_, fun g w ↦ ?_⟩
  · simp [e]
  · have he : e (ρ g w) = S.toRepresentation.prod C.toRepresentation g (e w) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) w
    simp [he, toRepresentation_apply]

end Subrepresentation
