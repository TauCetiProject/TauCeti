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
(`Representation.IsSemisimpleRepresentation`). This file records consequences and criteria.

A representation that maps injectively and equivariantly into a semisimple one is semisimple
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`), and so is the image of
a semisimple representation under a surjective intertwining map
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`), in particular the range
of an intertwining map out of a semisimple representation
(`Representation.IntertwiningMap.isSemisimpleRepresentation_range`). These are Mathlib's
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

A representation spanned by subrepresentations that carry semisimple representations is semisimple
(`Representation.isSemisimpleRepresentation_of_iSup_eq_top`). This is Mathlib's statement for the
modules over the group algebra, carried across the supremum by
`Subrepresentation.mem_iSup_asSubmodule_iff`. Restriction along a surjective homomorphism does not
change semisimplicity (`MonoidHom.isSemisimpleRepresentation_comp_surjective_iff`).

## Main results

* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`: a representation with
  an injective intertwining map into a semisimple representation is semisimple.
* `Representation.IntertwiningMap.isSemisimpleRepresentation_of_surjective`: a representation with
  a surjective intertwining map from a semisimple representation is semisimple.
* `Representation.IntertwiningMap.isSemisimpleRepresentation_range`: the range of an intertwining
  map out of a semisimple representation is semisimple.
* `Representation.isSemisimpleRepresentation_dual`: the dual of a finite-dimensional semisimple
  representation is semisimple.
* `Representation.isSemisimpleRepresentation_iff_iSup_atoms_eq_top`: a representation is
  semisimple exactly when it is the sum of its irreducible subrepresentations.
* `Subrepresentation.exists_equivariant_projection`: a subrepresentation of a semisimple
  representation has an equivariant projection onto it.
* `MonoidHom.isSemisimpleRepresentation_comp_surjective_iff`: restriction along a surjective
  homomorphism preserves and reflects semisimplicity.
* `Representation.isSemisimpleRepresentation_of_iSup_eq_top`: a representation spanned by
  semisimple subrepresentations is semisimple.
-/

public section

open scoped MonoidAlgebra

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

/-- **The image of a semisimple representation is semisimple.** The range of an intertwining map
out of a semisimple representation carries a semisimple representation. -/
theorem Representation.IntertwiningMap.isSemisimpleRepresentation_range
    {σ : Representation k G V} [ρ.IsSemisimpleRepresentation] (f : ρ.IntertwiningMap σ) :
    f.range.toRepresentation.IsSemisimpleRepresentation :=
  (f.codRestrict f.range fun w ↦ ⟨w, rfl⟩).isSemisimpleRepresentation_of_surjective
    fun ⟨_, w, hw⟩ ↦ ⟨w, Subtype.ext ((f.codRestrict_apply_coe _ _ w).trans hw)⟩

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
  have hτ : τ.toSubmodule =
      ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, (σ : Subrepresentation ρ).toSubmodule :=
    rfl
  have hle (σ : Subrepresentation ρ) : τ ≤ σ ↔
      sSup {m : Submodule k[G] ρ.asModule | IsSimpleModule k[G] m} ≤ e σ := by
    rw [← Subrepresentation.toSubmodule_le_toSubmodule, sSup_le_iff]
    refine ⟨fun h m hm ↦ ?_, fun h ↦ iSup_le fun σ ↦ Subrepresentation.toSubmodule_le_toSubmodule.2
      (e.le_iff_le.1 <| h _ (Subrepresentation.isSimpleModule_asSubmodule_iff.2 σ.property))⟩
    rw [← e.apply_symm_apply m, e.le_iff_le, ← Subrepresentation.toSubmodule_le_toSubmodule]
    exact le_trans (le_iSup_of_le
      ⟨e.symm m, Subrepresentation.isSimpleModule_asSubmodule_iff.1 hm⟩ le_rfl) h
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule, ← hτ,
    ← Subrepresentation.toSubmodule_top (ρ := ρ), Subrepresentation.toSubmodule_injective.eq_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := (hle τ).1 le_rfl
    rwa [h, top_le_iff, map_eq_top_iff] at h'
  · have h' := (hle (e.symm _)).2 (e.apply_symm_apply _).ge
    rw [h, top_le_iff] at h'
    rw [← e.apply_symm_apply (sSup _), h', map_top]

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

/-- **Restriction along a surjective homomorphism preserves and reflects semisimplicity.** For
surjective `f`, the representation `ρ.comp f` is semisimple if and only if `ρ` is. -/
@[simp]
theorem MonoidHom.isSemisimpleRepresentation_comp_surjective_iff {H K : Type*} [Monoid H]
    [Monoid K] (f : H →* K) (hf : Function.Surjective f) (ρ : Representation k K W) :
    Representation.IsSemisimpleRepresentation (ρ.comp f) ↔
      Representation.IsSemisimpleRepresentation ρ :=
  OrderIso.complementedLattice_iff (f.resSubrepresentationOrderIso hf ρ)

/-- **Semisimplicity from a spanning family.** A representation spanned by a family of
subrepresentations, each of which carries a semisimple representation, is semisimple. -/
theorem Representation.isSemisimpleRepresentation_of_iSup_eq_top {ι : Type*}
    {σ : ι → Subrepresentation ρ} (hσ : ∀ i, (σ i).toRepresentation.IsSemisimpleRepresentation)
    (hspan : ⨆ i, (σ i).toSubmodule = ⊤) : ρ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun i ↦ (σ i).asSubmodule)
    (fun i ↦ ?_) (Submodule.eq_top_iff'.mpr fun x ↦ ?_)
  · have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp (hσ i)
    exact IsSemisimpleModule.congr (σ i).asModuleEquivAsSubmodule.symm
  · rw [← ρ.asModuleEquiv.symm_apply_apply x, Subrepresentation.mem_iSup_asSubmodule_iff, hspan]
    exact Submodule.mem_top
