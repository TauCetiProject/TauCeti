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
  semisimple, in any characteristic (`Representation.isSemisimpleRepresentation_comp_subtype`):
  `ρ` is spanned by its irreducible subrepresentations
  (`Representation.isSemisimpleRepresentation_iff_iSup_atoms_eq_top`), and each restricts
  semisimply by Clifford theory
  (`Representation.isSemisimpleRepresentation_comp_subtype_of_isIrreducible`).
  If moreover `[G : N]` is invertible in `k`, the relative Maschke theorem gives the converse, so
  the restriction to `N` detects semisimplicity
  (`Representation.isSemisimpleRepresentation_comp_subtype_iff`).
* **Restriction to a subgroup containing a normal one.** If `N ≤ H` with `N` normal in `G` of
  `[H : N]` invertible in `k` (so finite), the restriction of `ρ` to `H` is semisimple
  (`Representation.isSemisimpleRepresentation_comp_subtype_of_normal_le`): restrict to `N`, then
  apply the relative Maschke theorem (`Representation.isSemisimpleRepresentation_of_comp_subtype`)
  to `N ≤ H`.

## References

* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11 (Clifford theory).
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **Restriction to a normal subgroup preserves semisimplicity.** The restriction of a
finite-dimensional semisimple representation to a normal subgroup is semisimple, in any
characteristic. -/
theorem isSemisimpleRepresentation_comp_subtype (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] [FiniteDimensional k V] [ρ.IsSemisimpleRepresentation] :
    IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  refine isSemisimpleRepresentation_of_iSup_eq_top
    (σ := fun σ : {σ : Subrepresentation ρ // IsAtom σ} ↦ σ.val.res N.subtype) (fun σ ↦ ?_)
    (isSemisimpleRepresentation_iff_iSup_atoms_eq_top.mp ‹_›)
  have := isIrreducible_toRepresentation_of_isAtom σ.property
  rw [Subrepresentation.toRepresentation_res]
  exact isSemisimpleRepresentation_comp_subtype_of_isIrreducible (N := N) σ.val.toRepresentation

/-- **Restriction to a normal subgroup of invertible index detects semisimplicity.** A
finite-dimensional representation is semisimple if and only if its restriction to a normal
subgroup `N` with `[G : N]` invertible in `k` is: restriction preserves semisimplicity
(`Representation.isSemisimpleRepresentation_comp_subtype`), and the relative Maschke theorem
(`Representation.isSemisimpleRepresentation_of_comp_subtype`) gives the converse. -/
@[simp]
theorem isSemisimpleRepresentation_comp_subtype_iff (ρ : Representation k G V) (N : Subgroup G)
    [N.Normal] [NeZero (N.index : k)] [FiniteDimensional k V] :
    IsSemisimpleRepresentation (ρ.comp N.subtype) ↔ IsSemisimpleRepresentation ρ :=
  ⟨fun _ ↦ isSemisimpleRepresentation_of_comp_subtype ρ N,
    fun _ ↦ isSemisimpleRepresentation_comp_subtype ρ N⟩

/-- **Restriction to a subgroup containing a normal one.** Let `N ≤ H ≤ G` with `N` normal in `G`
and `[H : N]` invertible in `k` (so finite). Then the restriction of a finite-dimensional
semisimple representation of `G` to `H` is semisimple. -/
theorem isSemisimpleRepresentation_comp_subtype_of_normal_le (ρ : Representation k G V)
    {N H : Subgroup G} [N.Normal] (hNH : N ≤ H) [NeZero ((N.subgroupOf H).index : k)]
    [FiniteDimensional k V] [ρ.IsSemisimpleRepresentation] :
    IsSemisimpleRepresentation (ρ.comp H.subtype) := by
  have := isSemisimpleRepresentation_comp_subtype ρ N
  have e : (ρ.comp H.subtype).comp (N.subgroupOf H).subtype =
      (ρ.comp N.subtype).comp (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom :=
    MonoidHom.ext fun _ ↦ rfl
  have : IsSemisimpleRepresentation ((ρ.comp H.subtype).comp (N.subgroupOf H).subtype) := by
    rw [e, MonoidHom.isSemisimpleRepresentation_comp_surjective_iff _
      (Subgroup.subgroupOfEquivOfLe hNH).surjective]
    infer_instance
  exact isSemisimpleRepresentation_of_comp_subtype _ (N.subgroupOf H)

end Representation
