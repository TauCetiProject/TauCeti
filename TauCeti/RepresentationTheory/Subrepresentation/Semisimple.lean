/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Subrepresentations of a semisimple representation

A representation is semisimple when every subrepresentation has a complementary subrepresentation
(`Representation.IsSemisimpleRepresentation`). This file records two consequences.

A representation that maps injectively and equivariantly into a semisimple one is semisimple
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`), and so is the image of
a semisimple representation under a surjective intertwining map
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`). These are Mathlib's
`IsSemisimpleModule.of_injective` and `IsSemisimpleModule.of_surjective` for the modules over the
group algebra.

A representation `σ` embedding into a semisimple representation `ρ` with a nondegenerate invariant
form also has a semisimple dual
(`TauCeti.Representation.IsInvariantForm.isSemisimpleRepresentation_dual_of_injective`): the form
identifies `ρ` with its dual, and restriction along the embedding maps that dual onto `σ.dual`.

Every subrepresentation `S` of a semisimple representation has an equivariant projection onto it
(`Subrepresentation.exists_equivariant_projection`): the first component of the splitting
`Subrepresentation.equivProdOfIsCompl` along a complement of `S`.

## Main results

* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`: a representation with
  an injective intertwining map into a semisimple representation is semisimple.
* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`: a representation with
  a surjective intertwining map from a semisimple representation is semisimple.
* `TauCeti.Representation.IsInvariantForm.isSemisimpleRepresentation_dual_of_injective`: the dual
  of a representation embedding into a semisimple representation with a nondegenerate invariant
  form is semisimple.
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

/-- **A quotient of a semisimple representation is semisimple.** If `f : ρ → σ` is a surjective
intertwining map and `ρ` is semisimple, then `σ` is semisimple. -/
theorem Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective
    {σ : Representation k G V} [ρ.IsSemisimpleRepresentation] (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : σ.IsSemisimpleRepresentation := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mpr
    (IsSemisimpleModule.of_surjective (equivLinearMapAsModule ρ σ f) hf)

/-- **The dual of a representation embedding into a self-dual semisimple one is semisimple.** Let
`ρ` be a semisimple representation on a finite-dimensional space preserving a nondegenerate form
`B`, and `f : σ → ρ` an injective intertwining map. Then `σ.dual` is semisimple: it is the image of
`ρ` under the surjective intertwining map `v ↦ B v ∘ f`, the identification `V ≃ V*` given by `B`
followed by restriction along `f`. -/
theorem TauCeti.Representation.IsInvariantForm.isSemisimpleRepresentation_dual_of_injective
    {G : Type*} [Group G] [FiniteDimensional k W] {ρ : Representation k G W}
    {σ : Representation k G V} [ρ.IsSemisimpleRepresentation] {B : LinearMap.BilinForm k W}
    (hB : IsInvariantForm ρ B) (hB' : B.Nondegenerate) (f : σ.IntertwiningMap ρ)
    (hf : Function.Injective f) : σ.dual.IsSemisimpleRepresentation := by
  refine ((f.toLinearMap.dualMap ∘ₗ B).intertwiningMap_of_isIntertwiningMap ρ σ.dual
    fun g w ↦ LinearMap.ext fun v ↦ ?_).isSemisimpleRepresentation_of_surjective
      ((LinearMap.dualMap_surjective_of_injective hf).comp (B.toDual hB').surjective)
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.isIntertwining, hB.apply_left]

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
