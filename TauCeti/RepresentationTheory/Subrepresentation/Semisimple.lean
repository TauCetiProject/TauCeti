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
(`Representation.IsSemisimpleRepresentation`). This file records some consequences.

A representation that maps injectively and equivariantly into a semisimple one is semisimple
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`), and so is the image of
a semisimple representation under a surjective intertwining map
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`). These are Mathlib's
`IsSemisimpleModule.of_injective` and `IsSemisimpleModule.of_surjective` for the modules over the
group algebra.

The dual of a finite-dimensional semisimple representation is semisimple
(`Representation.isSemisimpleRepresentation_dual`): annihilators exchange the subrepresentations
of `σ` and of `σ.dual` and carry complements to complements.

A representation is semisimple exactly when it is the sum of its irreducible subrepresentations
(`Representation.isSemisimpleRepresentation_iff_iSup_atoms_eq_top`).

Every subrepresentation `S` of a semisimple representation has an equivariant projection onto it
(`Subrepresentation.exists_equivariant_projection`): the first component of the splitting
`Subrepresentation.equivProdOfIsCompl` along a complement of `S`.

## Main results

* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`: a representation with
  an injective intertwining map into a semisimple representation is semisimple.
* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`: a representation with
  a surjective intertwining map from a semisimple representation is semisimple.
* `Representation.isSemisimpleRepresentation_dual`: the dual of a finite-dimensional semisimple
  representation is semisimple.
* `Representation.isSemisimpleRepresentation_iff_iSup_atoms_eq_top`: a representation is
  semisimple exactly when it is the sum of its irreducible subrepresentations.
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

/-- **The dual of a finite-dimensional semisimple representation is semisimple.** A
subrepresentation `S` of `σ.dual` is the annihilator of its coannihilator `S°`, a subrepresentation
of `σ`; the annihilator of an invariant complement of `S°` is an invariant complement of `S`. -/
instance Representation.isSemisimpleRepresentation_dual {G : Type*} [Group G]
    [FiniteDimensional k V] {σ : Representation k G V} [σ.IsSemisimpleRepresentation] :
    σ.dual.IsSemisimpleRepresentation := by
  refine ⟨fun S ↦ ?_⟩
  obtain ⟨C, hC⟩ := exists_isCompl S.dualCoannihilator
  refine ⟨C.dualAnnihilator, ?_⟩
  rw [← Subrepresentation.isCompl_toSubmodule, Subrepresentation.toSubmodule_dualAnnihilator]
  have h := Subspace.isCompl_dualAnnihilator (Subrepresentation.isCompl_toSubmodule.2 hC)
  rwa [Subrepresentation.toSubmodule_dualCoannihilator,
    Subspace.dualCoannihilator_dualAnnihilator_eq] at h

open scoped MonoidAlgebra in
/-- **A representation is semisimple exactly when it is the sum of its irreducible
subrepresentations**: the subspaces of its minimal nonzero subrepresentations span it. This is
`sSup_simples_eq_top_iff_isSemisimpleModule` for the module over the group algebra, read across
`Subrepresentation.subrepresentationSubmoduleOrderIso`. -/
theorem Representation.isSemisimpleRepresentation_iff_iSup_atoms_eq_top :
    ρ.IsSemisimpleRepresentation ↔
      ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, (σ : Subrepresentation ρ).toSubmodule = ⊤ := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  -- The sum of the atoms is itself a subrepresentation `τ`.
  let τ : Subrepresentation ρ :=
    ⟨⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, (σ : Subrepresentation ρ).toSubmodule,
      fun g w hw ↦ Submodule.iSup_induction _ (motive := fun w ↦ ρ g w ∈ _) hw
        (fun σ _ hx ↦ Submodule.mem_iSup_of_mem σ (σ.val.apply_mem_toSubmodule g hx))
        (by rw [map_zero]; exact zero_mem _)
        fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy⟩
  have hle (σ : Subrepresentation ρ) : τ ≤ σ ↔
      sSup {m : Submodule k[G] ρ.asModule | IsSimpleModule k[G] m} ≤ e σ := by
    rw [← Subrepresentation.toSubmodule_le_toSubmodule, sSup_le_iff]
    refine ⟨fun h m hm ↦ ?_, fun h ↦ iSup_le fun τ ↦ Subrepresentation.toSubmodule_le_toSubmodule.2
      (e.le_iff_le.1 <| h _ (Subrepresentation.isSimpleModule_asSubmodule_iff.2 τ.property))⟩
    rw [← e.apply_symm_apply m, e.le_iff_le, ← Subrepresentation.toSubmodule_le_toSubmodule]
    exact le_trans (le_iSup_of_le
      ⟨e.symm m, Subrepresentation.isSimpleModule_asSubmodule_iff.1 hm⟩ le_rfl) h
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  change _ ↔ τ.toSubmodule = ⊤
  rw [← Subrepresentation.toSubmodule_top (ρ := ρ), Subrepresentation.toSubmodule_injective.eq_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hτ := (hle τ).1 le_rfl
    rwa [h, top_le_iff, map_eq_top_iff] at hτ
  · have hτ := (hle (e.symm _)).2 (e.apply_symm_apply _).ge
    rw [h, top_le_iff] at hτ
    rw [← e.apply_symm_apply (sSup _), hτ, map_top]

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
