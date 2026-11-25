/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.RepresentationTheory.Smooth.Basic
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# Admissible representations

Let `G` be a topological group, `A` a commutative ring and `ρ` a representation of `G` on an
`A`-module `V`. The representation is *admissible* (`Representation.IsAdmissible`) when it is
smooth and, for every compact open subgroup `U` of `G`, the invariants `V^U` form a finitely
generated `A`-module. Over a field this is Casselman's condition `dim V^U < ∞`. The definition is
meant for locally profinite groups: a group with no compact open subgroup imposes no finiteness.

## Main definitions

* `Representation.IsAdmissible ρ`: `ρ` is smooth and `V^U` is finitely generated for every compact
  open subgroup `U`.

## Main results

* `Representation.IsAdmissible.of_forall_le`: it suffices to check that `V^U` is noetherian for
  the members `U` of a family of subgroups refining every compact open subgroup, since `V^U` is a
  submodule of `V^{U'}` for `U' ≤ U`.
* `Representation.IsAdmissible.of_hasBasis`, `Representation.isAdmissible_iff_of_hasBasis`: over a
  noetherian ring, it suffices to check finite generation of `V^U` for the members `U` of a basis
  of neighbourhoods of `1` made of subgroups.
* `Representation.IsAdmissible.prod`, `Representation.IsAdmissible.directSum`: a direct sum of
  finitely many admissible representations is admissible.
* `Representation.IsAdmissible.comp`: the restriction of an admissible representation along a
  continuous open homomorphism, in particular to an open subgroup
  (`Representation.IsAdmissible.comp_openSubgroup`), is admissible.
* `Representation.IsAdmissible.of_injective_of_isNoetherian`: a representation with an injective
  intertwining map to a smooth one whose compact open invariants are noetherian is admissible.
* `Representation.IsAdmissible.of_injective`: over a noetherian ring, a representation with an
  injective intertwining map to an admissible one is admissible; in particular so is every
  subrepresentation of an admissible representation
  (`Subrepresentation.isAdmissible_toRepresentation`, and
  `Representation.IsAdmissible.subrepresentation` for `ρ.subrepresentation W _`).
* `Representation.Equiv.isAdmissible_iff`: equivalent representations are admissible together.
* `Representation.IsAdmissible.of_subsingleton`, `Representation.IsAdmissible.of_isTrivial`: the
  zero representation, and a trivial representation on a finitely generated module, are
  admissible.
* `Representation.isAdmissible_iff_finite_of_isTrivial`: for a group with a compact open subgroup,
  a trivial representation is admissible exactly when the module is finitely generated.
* `Representation.IsAdmissible.of_isNoetherian`: a smooth representation on a noetherian module
  is admissible.
* `Representation.IsAdmissible.of_forall_not_isCompact`: for a group with no compact open
  subgroup, every smooth representation is admissible.

## References

* W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, 1995, §0, conditions (a)-(b), p. 2.
* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Grundlehren 335,
  Springer, 2006, 2.1, p. 13.
-/

public section

namespace Representation

variable {A G V W : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

variable (ρ) in
/-- A representation of a topological group is *admissible* when it is smooth and the invariants
`V^U` of every compact open subgroup `U` form a finitely generated module. -/
class IsAdmissible : Prop extends IsSmooth ρ where
  finite_invariants (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    Module.Finite A (invariants (ρ.comp (U : Subgroup G).subtype))

/-- An admissible representation is smooth and has finitely generated invariants under every
compact open subgroup. -/
theorem isAdmissible_iff :
    IsAdmissible ρ ↔ IsSmooth ρ ∧ ∀ U : OpenSubgroup G, IsCompact (U : Set G) →
      Module.Finite A (invariants (ρ.comp (U : Subgroup G).subtype)) :=
  ⟨fun h ↦ ⟨h.toIsSmooth, h.finite_invariants⟩, fun ⟨_, h₂⟩ ↦ ⟨h₂⟩⟩

/-- **Admissibility on a refining family.** A smooth representation is admissible as soon as
`V^U` is noetherian for every member `U` of a family of subgroups refining every compact open
subgroup. -/
theorem IsAdmissible.of_forall_le [IsSmooth ρ] {ι : Type*} {p : ι → Prop} {U : ι → Subgroup G}
    (hU : ∀ K : OpenSubgroup G, IsCompact (K : Set G) → ∃ i, p i ∧ U i ≤ (K : Subgroup G))
    (hfin : ∀ i, p i → IsNoetherian A (invariants (ρ.comp (U i).subtype))) :
    IsAdmissible ρ := by
  refine ⟨fun K hK ↦ ?_⟩
  obtain ⟨i, hi, hle⟩ := hU K hK
  have := hfin i hi
  -- A vector fixed by `K` is fixed by its subgroup `U i`.
  have hinv : invariants (ρ.comp (K : Subgroup G).subtype) ≤ invariants (ρ.comp (U i).subtype) :=
    fun v hv ↦ mem_invariants_comp_subtype_iff.2 (hle.trans (mem_invariants_comp_subtype_iff.1 hv))
  exact Module.Finite.of_injective (Submodule.inclusion hinv) (Submodule.inclusion_injective _)

/-- **Admissibility on a basis.** Over a noetherian ring, a smooth representation is admissible as
soon as `V^U` is finitely generated for every member `U` of a basis of neighbourhoods of `1`
made of subgroups. -/
theorem IsAdmissible.of_hasBasis [IsNoetherianRing A] [IsSmooth ρ] {ι : Type*} {p : ι → Prop}
    {U : ι → Subgroup G} (hU : (nhds (1 : G)).HasBasis p fun i ↦ (U i : Set G))
    (hfin : ∀ i, p i → Module.Finite A (invariants (ρ.comp (U i).subtype))) :
    IsAdmissible ρ :=
  of_forall_le (fun K _ ↦ (hU.mem_iff.1 K.mem_nhds_one).imp fun _ ⟨hi, hsub⟩ ↦
    ⟨hi, SetLike.coe_subset_coe.1 hsub⟩) fun i hi ↦ by
      have := hfin i hi
      infer_instance

/-- Over a noetherian ring, a smooth representation is admissible exactly when `V^U` is finitely
generated for every member `U` of a basis of neighbourhoods of `1` made of compact open
subgroups. -/
theorem isAdmissible_iff_of_hasBasis [IsNoetherianRing A] [IsSmooth ρ] {ι : Type*}
    {p : ι → Prop} {U : ι → OpenSubgroup G} (hU : (nhds (1 : G)).HasBasis p fun i ↦ (U i : Set G))
    (hUc : ∀ i, p i → IsCompact (U i : Set G)) :
    IsAdmissible ρ ↔
      ∀ i, p i → Module.Finite A (invariants (ρ.comp (U i : Subgroup G).subtype)) :=
  ⟨fun h i hi ↦ h.finite_invariants (U i) (hUc i hi),
    IsAdmissible.of_hasBasis (U := fun i ↦ (U i : Subgroup G)) hU⟩

/-- Admissibility passes back along an injective intertwining map to a smooth representation
whose invariants under compact open subgroups are noetherian. -/
theorem IsAdmissible.of_injective_of_isNoetherian [IsSmooth σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f)
    (hσ : ∀ U : OpenSubgroup G, IsCompact (U : Set G) →
      IsNoetherian A (invariants (σ.comp (U : Subgroup G).subtype))) :
    IsAdmissible ρ := by
  have : IsSmooth ρ := IsSmooth.of_injective f hf
  refine ⟨fun U hU ↦ ?_⟩
  have := hσ U hU
  exact Module.Finite.of_injective _
    ((f.res (U : Subgroup G).subtype).invariantsMap_injective (by rwa [IntertwiningMap.coe_res]))

/-- Admissibility passes back along an injective intertwining map over a noetherian ring; in
particular a subrepresentation of an admissible representation is admissible. -/
theorem IsAdmissible.of_injective [IsNoetherianRing A] [IsAdmissible σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : IsAdmissible ρ :=
  of_injective_of_isNoetherian f hf fun U hU ↦ by
    have := IsAdmissible.finite_invariants (ρ := σ) U hU
    infer_instance

/-- A subrepresentation of an admissible representation over a noetherian ring is admissible. -/
instance _root_.Subrepresentation.isAdmissible_toRepresentation [IsNoetherianRing A]
    [IsAdmissible ρ] (ρ' : Subrepresentation ρ) :
    IsAdmissible ρ'.toRepresentation :=
  IsAdmissible.of_injective ρ'.subtype ρ'.subtype_injective

/-- The restriction of an admissible representation over a noetherian ring to an invariant
submodule is admissible. -/
instance IsAdmissible.subrepresentation [IsNoetherianRing A] [IsAdmissible ρ]
    (W : Submodule A V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    IsAdmissible (ρ.subrepresentation W le_comap) :=
  IsAdmissible.of_injective (σ := ρ) ⟨W.subtype, fun _ ↦ rfl⟩ W.injective_subtype

/-- An admissible representation transfers admissibility along an equivalence. -/
private theorem IsAdmissible.of_equiv [IsAdmissible ρ] (e : Equiv ρ σ) : IsAdmissible σ := by
  have : IsSmooth σ := (e.isSmooth_iff).1 inferInstance
  refine ⟨fun U hU ↦ ?_⟩
  have := IsAdmissible.finite_invariants (ρ := ρ) U hU
  exact Module.Finite.equiv (e.res (U : Subgroup G).subtype).invariantsLinearEquiv

/-- Equivalent representations are admissible together. -/
theorem Equiv.isAdmissible_iff (e : Equiv ρ σ) : IsAdmissible ρ ↔ IsAdmissible σ :=
  ⟨fun _ ↦ IsAdmissible.of_equiv e, fun _ ↦ IsAdmissible.of_equiv e.symm⟩

/-- The restriction of an admissible representation along a continuous open homomorphism is
admissible: the image of a compact open subgroup is a compact open subgroup of `G`. -/
theorem IsAdmissible.comp [IsAdmissible ρ] {H : Type*} [Group H] [TopologicalSpace H]
    {φ : H →* G} (hφ : Continuous φ) (hφo : IsOpenMap φ) : IsAdmissible (ρ.comp φ) := by
  have : IsSmooth (ρ.comp φ) := IsSmooth.comp hφ
  refine ⟨fun U hU ↦ ?_⟩
  have hopen : IsOpen ((U : Subgroup H).map φ : Set G) := by
    rw [Subgroup.coe_map]
    exact hφo _ U.isOpen
  let U' : OpenSubgroup G := ⟨(U : Subgroup H).map φ, hopen⟩
  have hU' : IsCompact ((U : Subgroup H).map φ : Set G) := by
    rw [Subgroup.coe_map]
    exact hU.image hφ
  have := IsAdmissible.finite_invariants (ρ := ρ) U' hU'
  rw [invariants_comp_comp_subtype]
  exact this

/-- The restriction of an admissible representation to an open subgroup is admissible. -/
instance IsAdmissible.comp_openSubgroup [IsAdmissible ρ] (H : OpenSubgroup G) :
    IsAdmissible (ρ.comp (H : Subgroup G).subtype) :=
  IsAdmissible.comp continuous_subtypeVal H.isOpen.isOpenMap_subtypeVal

/-- The direct sum of two admissible representations is admissible: the invariants of a direct
sum are the product of the invariants. -/
instance IsAdmissible.prod [IsAdmissible ρ] [IsAdmissible σ] :
    IsAdmissible (ρ.prod σ) := by
  refine ⟨fun U hU ↦ ?_⟩
  have h₁ := IsAdmissible.finite_invariants (ρ := ρ) U hU
  have h₂ := IsAdmissible.finite_invariants (ρ := σ) U hU
  rw [Module.Finite.iff_fg] at h₁ h₂ ⊢
  rw [prod_comp, invariants_prod]
  exact h₁.prod h₂

/-- The direct sum of a finite family of admissible representations is admissible: its
invariants correspond to the product of the invariants. -/
instance IsAdmissible.directSum {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] (ρ : ∀ i, Representation A G (V i))
    [∀ i, IsAdmissible (ρ i)] : IsAdmissible (directSum ρ) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun U hU ↦ ?_⟩
  have := fun i ↦ IsAdmissible.finite_invariants (ρ := ρ i) U hU
  rw [Module.Finite.iff_fg, directSum_comp, invariants_directSum,
    Submodule.comap_equiv_eq_map_symm]
  exact (Submodule.fg_pi fun i ↦ Module.Finite.iff_fg.1 (this i)).map _

/-- A representation on a module with at most one vector, such as the zero representation, is
admissible. -/
instance IsAdmissible.of_subsingleton [Subsingleton V] : IsAdmissible ρ :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- A trivial representation on a finitely generated module is admissible. -/
instance IsAdmissible.of_isTrivial [ρ.IsTrivial] [Module.Finite A V] : IsAdmissible ρ :=
  ⟨fun U _ ↦ by
    rw [Module.Finite.iff_fg, invariants_eq_top]
    exact Module.finite_def.1 inferInstance⟩

/-- A smooth representation on a noetherian module, such as a finitely generated module over a
noetherian ring, is admissible: each `V^U` is a submodule of the noetherian module `V`. -/
instance IsAdmissible.of_isNoetherian [IsNoetherian A V] [IsSmooth ρ] :
    IsAdmissible ρ :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- For a group with no compact open subgroup the finiteness condition of admissibility is empty,
so every smooth representation is admissible. -/
theorem IsAdmissible.of_forall_not_isCompact [IsSmooth ρ]
    (hG : ∀ U : OpenSubgroup G, ¬IsCompact (U : Set G)) : IsAdmissible ρ :=
  ⟨fun U hU ↦ (hG U hU).elim⟩

/-- For a group with a compact open subgroup, a trivial representation is admissible exactly when
the module is finitely generated. -/
theorem isAdmissible_iff_finite_of_isTrivial [ρ.IsTrivial]
    (hG : ∃ U : OpenSubgroup G, IsCompact (U : Set G)) :
    IsAdmissible ρ ↔ Module.Finite A V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hU⟩ := hG
  have := h.finite_invariants U hU
  rw [Module.Finite.iff_fg, invariants_eq_top] at this
  exact Module.finite_def.2 this

end Representation
