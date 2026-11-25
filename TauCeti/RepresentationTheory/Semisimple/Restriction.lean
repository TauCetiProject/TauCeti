/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Basic
public import TauCeti.RepresentationTheory.Subrepresentation.RelativeMaschke
public import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Semisimplicity under restriction to normal and finite-index subgroups

Let `ρ` be a finite-dimensional semisimple representation of a group `G` over a field `k`. None of
the statements below asks `G` to be finite or `ρ` to factor through a finite quotient; only the
indices that occur are finite.

* **Restriction to a normal subgroup.** If `N` is normal, the restriction of `ρ` to `N` is
  semisimple, in any characteristic
  (`Representation.isSemisimpleRepresentation_comp_subtype_of_normal`): `ρ` is a sum of irreducible
  subrepresentations, and each restricts semisimply by Clifford theory
  (`Representation.isSemisimpleRepresentation_comp_subtype`).
* **Restriction to a subgroup containing a normal one.** If `N ≤ H` with `N` normal in `G` of
  `[H : N]` invertible in `k` (so finite), the restriction of `ρ` to `H` is semisimple
  (`Representation.isSemisimpleRepresentation_comp_subtype_of_normal_le`): restrict to `N`, then
  apply the relative Maschke theorem (`Representation.isSemisimpleRepresentation_of_comp_subtype`)
  to `N ≤ H`.

Two general facts are used along the way: a representation spanned by subrepresentations that
carry semisimple representations is semisimple
(`Representation.isSemisimpleRepresentation_of_le_iSup`), and composing with a surjective group
homomorphism does not change semisimplicity
(`Representation.isSemisimpleRepresentation_comp_iff_of_surjective`).

## References

* N. Jacobson, *Basic Algebra II*, 2nd ed., §5.2 (Clifford's theorem).
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Composing with a surjective homomorphism does not change semisimplicity. -/
theorem isSemisimpleRepresentation_comp_iff_of_surjective {G' : Type*} [Group G']
    (ρ : Representation k G V) {f : G' →* G} (hf : Function.Surjective f) :
    IsSemisimpleRepresentation (ρ.comp f) ↔ ρ.IsSemisimpleRepresentation :=
  OrderIso.complementedLattice_iff (MonoidHom.resSubrepresentationOrderIso f hf ρ)

/-- **Semisimplicity from a spanning family.** A representation spanned by a family of
subrepresentations, each of which carries a semisimple representation, is semisimple. -/
theorem isSemisimpleRepresentation_of_le_iSup {ι : Type*} (ρ : Representation k G V)
    (σ : ι → Subrepresentation ρ) (hσ : ∀ i, (σ i).toRepresentation.IsSemisimpleRepresentation)
    (hspan : ∀ v : V, v ∈ ⨆ i, (σ i).toSubmodule) : ρ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun i ↦ (σ i).asSubmodule)
    (fun i ↦ ?_) (eq_top_iff.mpr fun x _ ↦ ?_)
  · have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp (hσ i)
    exact IsSemisimpleModule.congr (σ i).asModuleEquivAsSubmodule.symm
  · rw [← ρ.asModuleEquiv.symm_apply_apply x]
    refine Submodule.iSup_induction _ (motive := fun v ↦
      ρ.asModuleEquiv.symm v ∈ ⨆ i, (σ i).asSubmodule) (hspan (ρ.asModuleEquiv x))
      (fun i v hv ↦ Submodule.mem_iSup_of_mem i ?_) (by simp) (fun v w hv hw ↦ ?_)
    · exact (Subrepresentation.mem_asSubmodule_iff (v := v)).mpr hv
    · rw [map_add]
      exact add_mem hv hw

/-- A semisimple representation is spanned by its minimal nonzero subrepresentations. -/
theorem mem_iSup_isAtom (ρ : Representation k G V) [ρ.IsSemisimpleRepresentation] (v : V) :
    v ∈ ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, (σ : Subrepresentation ρ).toSubmodule := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have hv : ρ.asModuleEquiv.symm v ∈
      sSup {m : Submodule k[G] ρ.asModule | IsSimpleModule k[G] m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hv
  rw [← ρ.asModuleEquiv.apply_symm_apply v]
  refine Submodule.iSup_induction _ (motive := fun x ↦ ρ.asModuleEquiv x ∈
    ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, (σ : Subrepresentation ρ).toSubmodule) hv
    (fun m x hx ↦ ?_) (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
  refine Submodule.mem_iSup_of_mem ⟨Subrepresentation.ofSubmodule' m.val,
    Subrepresentation.isSimpleModule_asSubmodule_iff.mp m.property⟩ ?_
  exact (Subrepresentation.mem_ofSubmodule'_iff (N := m.val)).mpr hx

/-- **Restriction to a normal subgroup preserves semisimplicity.** The restriction of a
finite-dimensional semisimple representation to a normal subgroup is semisimple, in any
characteristic. -/
theorem isSemisimpleRepresentation_comp_subtype_of_normal (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] [FiniteDimensional k V] [ρ.IsSemisimpleRepresentation] :
    IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  let σN : {σ : Subrepresentation ρ // IsAtom σ} → Subrepresentation (ρ.comp N.subtype) :=
    fun σ ↦ ⟨σ.val.toSubmodule, fun n _ hv ↦ σ.val.apply_mem_toSubmodule (n : G) hv⟩
  refine isSemisimpleRepresentation_of_le_iSup _ σN (fun σ ↦ ?_) (mem_iSup_isAtom ρ)
  have := isIrreducible_toRepresentation_of_isAtom σ.property
  exact isSemisimpleRepresentation_comp_subtype (N := N) σ.val.toRepresentation

/-- **Restriction to a subgroup containing a normal one.** Let `N ≤ H ≤ G` with `N` normal in `G`
and `[H : N]` invertible in `k` (so finite). Then the restriction of a finite-dimensional
semisimple representation of `G` to `H` is semisimple. -/
theorem isSemisimpleRepresentation_comp_subtype_of_normal_le (ρ : Representation k G V)
    {N H : Subgroup G} [N.Normal] (hNH : N ≤ H) [NeZero ((N.subgroupOf H).index : k)]
    [FiniteDimensional k V] [ρ.IsSemisimpleRepresentation] :
    IsSemisimpleRepresentation (ρ.comp H.subtype) := by
  have := isSemisimpleRepresentation_comp_subtype_of_normal ρ N
  have e : (ρ.comp H.subtype).comp (N.subgroupOf H).subtype =
      (ρ.comp N.subtype).comp (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom :=
    MonoidHom.ext fun _ ↦ rfl
  have : IsSemisimpleRepresentation ((ρ.comp H.subtype).comp (N.subgroupOf H).subtype) := by
    rw [e, isSemisimpleRepresentation_comp_iff_of_surjective _
      (Subgroup.subgroupOfEquivOfLe hNH).surjective]
    infer_instance
  exact isSemisimpleRepresentation_of_comp_subtype _ (N.subgroupOf H)

end Representation
