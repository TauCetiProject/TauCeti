/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.RepresentationTheory.Smooth.Basic

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

* `Representation.IsAdmissible.of_hasBasis`: over a noetherian ring, it suffices to check finite
  generation of `V^U` for the members `U` of a basis of neighbourhoods of `1` made of subgroups,
  since `V^U` is a submodule of `V^{U'}` for `U' ≤ U`.
* `Representation.IsAdmissible.prod`: a direct sum of two admissible representations is
  admissible.
* `Representation.IsAdmissible.of_injective`: over a noetherian ring, a representation with an
  injective intertwining map to an admissible one is admissible; in particular so is every
  subrepresentation of an admissible representation
  (`Representation.IsAdmissible.subrepresentation`).
* `Representation.Equiv.isAdmissible_iff`: equivalent representations are admissible together.
* `Representation.IsAdmissible.of_subsingleton`, `Representation.IsAdmissible.trivial`: the zero
  representation, and a trivial representation on a finitely generated module, are admissible.
* `Representation.isAdmissible_trivial_iff`: for a group with a compact open subgroup, a trivial
  representation is admissible exactly when the module is finitely generated.

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

/-- **Admissibility on a basis.** Over a noetherian ring, a smooth representation is admissible as
soon as `V^U` is finitely generated for every member `U` of a basis of neighbourhoods of `1`
made of subgroups. -/
theorem IsAdmissible.of_hasBasis [IsNoetherianRing A] [IsSmooth ρ] {ι : Type*} {p : ι → Prop}
    {U : ι → Subgroup G} (hU : (nhds (1 : G)).HasBasis p fun i ↦ (U i : Set G))
    (hfin : ∀ i, p i → Module.Finite A (invariants (ρ.comp (U i).subtype))) :
    IsAdmissible ρ := by
  refine ⟨fun U' _ ↦ ?_⟩
  obtain ⟨i, hi, hsub⟩ := hU.mem_iff.1 (U'.mem_nhds_one)
  have := hfin i hi
  have hle : invariants (ρ.comp (U' : Subgroup G).subtype) ≤ invariants (ρ.comp (U i).subtype) :=
    fun _ hv ↦ mem_invariants_comp_subtype_iff.2 fun _ hx ↦
      mem_invariants_comp_subtype_iff.1 hv (hsub hx)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)

/-- Admissibility passes back along an injective intertwining map over a noetherian ring; in
particular a subrepresentation of an admissible representation is admissible. -/
theorem IsAdmissible.of_injective [IsNoetherianRing A] [IsAdmissible σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : IsAdmissible ρ := by
  have : IsSmooth ρ := IsSmooth.of_injective f hf
  refine ⟨fun U hU ↦ ?_⟩
  have := IsAdmissible.finite_invariants (ρ := σ) U hU
  let g : invariants (ρ.comp (U : Subgroup G).subtype) →ₗ[A]
      invariants (σ.comp (U : Subgroup G).subtype) :=
    (f.toLinearMap.comp (Submodule.subtype _)).codRestrict _ fun v u ↦ by
      simpa [f.isIntertwining] using congrArg f (v.property u)
  exact Module.Finite.of_injective g fun v w hvw ↦ Subtype.ext (hf (congrArg Subtype.val hvw))

/-- A subrepresentation of an admissible representation over a noetherian ring is admissible. -/
instance IsAdmissible.subrepresentation [IsNoetherianRing A] [IsAdmissible ρ]
    (ρ' : Subrepresentation ρ) :
    IsAdmissible ρ'.toRepresentation :=
  IsAdmissible.of_injective (σ := ρ) ⟨ρ'.toSubmodule.subtype, fun _ ↦ rfl⟩
    ρ'.toSubmodule.injective_subtype

omit [TopologicalSpace G] in
/-- An equivalence of representations maps the invariants of every subgroup onto those of the
target. -/
private theorem Equiv.map_invariants_comp_subtype (e : Equiv ρ σ) (U : Subgroup G) :
    (invariants (ρ.comp U.subtype)).map e.toLinearEquiv.toLinearMap =
      invariants (σ.comp U.subtype) := by
  refine le_antisymm ?_ fun w hw ↦ ⟨e.symm w, fun u ↦ ?_, e.apply_symm_apply w⟩
  · rintro _ ⟨v, hv, rfl⟩ u
    have h := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap u v
    rw [show ρ u v = v from hv u] at h
    exact h.symm
  · have h := IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap u w
    rw [show σ u w = w from hw u] at h
    exact h.symm

/-- An admissible representation transfers admissibility along an equivalence. -/
private theorem IsAdmissible.of_equiv [IsAdmissible ρ] (e : Equiv ρ σ) : IsAdmissible σ := by
  have : IsSmooth σ := (e.isSmooth_iff).1 inferInstance
  refine ⟨fun U hU ↦ ?_⟩
  have := IsAdmissible.finite_invariants (ρ := ρ) U hU
  rw [Module.Finite.iff_fg] at this ⊢
  rw [← e.map_invariants_comp_subtype]
  exact this.map _

/-- Equivalent representations are admissible together. -/
theorem Equiv.isAdmissible_iff (e : Equiv ρ σ) : IsAdmissible ρ ↔ IsAdmissible σ :=
  ⟨fun _ ↦ IsAdmissible.of_equiv e, fun _ ↦ IsAdmissible.of_equiv e.symm⟩

omit [TopologicalSpace G] in
/-- The invariants of a direct sum are the product of the invariants. -/
private theorem invariants_prod_comp_subtype (U : Subgroup G) :
    invariants ((ρ.prod σ).comp U.subtype) =
      (invariants (ρ.comp U.subtype)).prod (invariants (σ.comp U.subtype)) := by
  ext x
  simp only [mem_invariants, Submodule.mem_prod, Prod.ext_iff, forall_and]
  rfl

/-- The direct sum of two admissible representations is admissible. -/
instance IsAdmissible.prod [IsAdmissible ρ] [IsAdmissible σ] :
    IsAdmissible (ρ.prod σ) := by
  have : IsSmooth (ρ.prod σ) := ⟨fun x ↦ ?_⟩
  · refine ⟨fun U hU ↦ ?_⟩
    have := IsAdmissible.finite_invariants (ρ := ρ) U hU
    have := IsAdmissible.finite_invariants (ρ := σ) U hU
    rw [Module.Finite.iff_fg] at *
    rw [invariants_prod_comp_subtype]
    exact Submodule.FG.prod ‹_› ‹_›
  · have h : (ρ.prod σ).stabilizer x = ρ.stabilizer x.1 ⊓ σ.stabilizer x.2 := by
      ext g
      simp [mem_stabilizer, Prod.ext_iff]
    rw [h, Subgroup.coe_inf]
    exact (IsSmooth.isOpen_stabilizer (ρ := ρ) x.1).inter (IsSmooth.isOpen_stabilizer (ρ := σ) x.2)

/-- A representation on a module with at most one vector, such as the zero representation, is
admissible. -/
instance IsAdmissible.of_subsingleton [Subsingleton V] : IsAdmissible ρ :=
  ⟨fun _ _ ↦ inferInstance⟩

omit [TopologicalSpace G] in
/-- Every vector of a trivial representation is invariant under every subgroup. -/
private theorem invariants_trivial_comp_subtype (U : Subgroup G) :
    invariants ((trivial A G V).comp U.subtype) = ⊤ :=
  eq_top_iff.2 fun _ _ _ ↦ rfl

/-- A trivial representation on a finitely generated module is admissible. -/
instance IsAdmissible.trivial [Module.Finite A V] : IsAdmissible (trivial A G V) :=
  ⟨fun U _ ↦ by
    rw [Module.Finite.iff_fg, invariants_trivial_comp_subtype]
    exact Module.finite_def.1 inferInstance⟩

/-- For a group with a compact open subgroup, a trivial representation is admissible exactly when
the module is finitely generated. -/
theorem isAdmissible_trivial_iff (hG : ∃ U : OpenSubgroup G, IsCompact (U : Set G)) :
    IsAdmissible (trivial A G V) ↔ Module.Finite A V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hU⟩ := hG
  have := h.finite_invariants U hU
  rw [Module.Finite.iff_fg, invariants_trivial_comp_subtype] at this
  exact Module.finite_def.2 this

end Representation
