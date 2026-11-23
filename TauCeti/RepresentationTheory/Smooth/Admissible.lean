/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
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

* `Representation.IsAdmissible.of_hasBasis`: over a noetherian ring, it suffices to check finite
  generation of `V^U` for the members `U` of a basis of neighbourhoods of `1` made of subgroups,
  since `V^U` is a submodule of `V^{U'}` for `U' ≤ U`.
* `Representation.IsAdmissible.prod`, `Representation.IsAdmissible.directSum`: a direct sum of
  finitely many admissible representations is admissible.
* `Representation.IsAdmissible.comp`: the restriction of an admissible representation along a
  continuous open homomorphism, in particular to an open subgroup
  (`Representation.IsAdmissible.comp_openSubgroup`), is admissible.
* `Representation.IsAdmissible.of_injective`: over a noetherian ring, a representation with an
  injective intertwining map to an admissible one is admissible; in particular so is every
  subrepresentation of an admissible representation
  (`Representation.IsAdmissible.subrepresentation`).
* `Representation.Equiv.isAdmissible_iff`: equivalent representations are admissible together.
* `Representation.IsAdmissible.of_subsingleton`, `Representation.IsAdmissible.of_isTrivial`: the
  zero representation, and a trivial representation on a finitely generated module, are
  admissible.
* `Representation.isAdmissible_iff_finite_of_isTrivial`: for a group with a compact open subgroup,
  a trivial representation is admissible exactly when the module is finitely generated.

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
    invariants_le_invariants_comp (ρ.comp (U' : Subgroup G).subtype)
      (Subgroup.inclusion (SetLike.coe_subset_coe.1 hsub))
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)

/-- Admissibility passes back along an injective intertwining map over a noetherian ring; in
particular a subrepresentation of an admissible representation is admissible. -/
theorem IsAdmissible.of_injective [IsNoetherianRing A] [IsAdmissible σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : IsAdmissible ρ := by
  have : IsSmooth ρ := IsSmooth.of_injective f hf
  refine ⟨fun U hU ↦ ?_⟩
  have := IsAdmissible.finite_invariants (ρ := σ) U hU
  -- `f` maps `U`-invariant vectors to `U`-invariant vectors, since it intertwines `ρ` and `σ`.
  let g := f.toLinearMap.restrict (p := invariants (ρ.comp (U : Subgroup G).subtype))
    (q := invariants (σ.comp (U : Subgroup G).subtype)) fun v hv u ↦ by
      simpa [f.isIntertwining] using congrArg f (hv u)
  exact Module.Finite.of_injective g fun v w hvw ↦ Subtype.ext (hf (congrArg Subtype.val hvw))

/-- A subrepresentation of an admissible representation over a noetherian ring is admissible. -/
instance IsAdmissible.subrepresentation [IsNoetherianRing A] [IsAdmissible ρ]
    (ρ' : Subrepresentation ρ) :
    IsAdmissible ρ'.toRepresentation :=
  IsAdmissible.of_injective ρ'.subtype ρ'.subtype_injective

/-- The restriction of an admissible representation over a noetherian ring to an invariant
submodule is admissible. -/
instance IsAdmissible.instSubrepresentation [IsNoetherianRing A] [IsAdmissible ρ]
    (W : Submodule A V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    IsAdmissible (ρ.subrepresentation W le_comap) :=
  IsAdmissible.subrepresentation (ρ := ρ) ⟨W, fun g _ hv ↦ le_comap g hv⟩

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
  -- Restricting `ρ.comp φ` to `U` is restricting `ρ` to `U' = φ(U)` after `φ : U → φ(U)`.
  have hcomp : (ρ.comp φ).comp (U : Subgroup H).subtype =
      (ρ.comp (U' : Subgroup G).subtype).comp (φ.subgroupMap (U : Subgroup H)) := by
    ext u : 1
    simp [U']
  rw [hcomp, invariants_comp_of_surjective _ _ (φ.subgroupMap_surjective _)]
  infer_instance

/-- The restriction of an admissible representation to an open subgroup is admissible. -/
instance IsAdmissible.comp_openSubgroup [IsAdmissible ρ] (H : OpenSubgroup G) :
    IsAdmissible (ρ.comp (H : Subgroup G).subtype) :=
  IsAdmissible.comp continuous_subtypeVal H.isOpen.isOpenMap_subtypeVal

/-- The direct sum of two admissible representations is admissible: the invariants of a direct
sum are the product of the invariants. -/
instance IsAdmissible.prod [IsAdmissible ρ] [IsAdmissible σ] :
    IsAdmissible (ρ.prod σ) := by
  refine ⟨fun U hU ↦ ?_⟩
  have := IsAdmissible.finite_invariants (ρ := ρ) U hU
  have := IsAdmissible.finite_invariants (ρ := σ) U hU
  -- Restricting `ρ.prod σ` to `U` is, by definition, the product of the restrictions.
  have h : invariants ((ρ.prod σ).comp (U : Subgroup G).subtype) =
      (invariants (ρ.comp (U : Subgroup G).subtype)).prod
        (invariants (σ.comp (U : Subgroup G).subtype)) :=
    invariants_prod (ρ.comp (U : Subgroup G).subtype) (σ.comp (U : Subgroup G).subtype)
  rw [Module.Finite.iff_fg, h]
  exact (Module.Finite.iff_fg.1 ‹_›).prod (Module.Finite.iff_fg.1 ‹_›)

/-- The direct sum of a finite family of admissible representations is admissible: its
invariants correspond to the product of the invariants. -/
instance IsAdmissible.directSum {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] (ρ : ∀ i, Representation A G (V i))
    [∀ i, IsAdmissible (ρ i)] : IsAdmissible (directSum ρ) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun U hU ↦ ?_⟩
  have := fun i ↦ IsAdmissible.finite_invariants (ρ := ρ i) U hU
  have h : invariants ((Representation.directSum ρ).comp (U : Subgroup G).subtype) =
      (Submodule.pi Set.univ fun i ↦ invariants ((ρ i).comp (U : Subgroup G).subtype)).comap
        (DirectSum.linearEquivFunOnFintype A ι V).toLinearMap :=
    -- Restricting `directSum ρ` to `U` is, by definition, the direct sum of the restrictions.
    invariants_directSum fun i ↦ (ρ i).comp (U : Subgroup G).subtype
  rw [Module.Finite.iff_fg, h, Submodule.comap_equiv_eq_map_symm]
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
