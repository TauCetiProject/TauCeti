/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP

/-!
# Profinite groups defined by generators and relators

This file constructs profinite and pro-`p` groups from generators and relators. In each case the
relators are quotiented by their **closed** normal closure, so the result remains profinite. The
quotient maps and factorisation theorems let maps out of a presented group be specified on its
generators together with the condition that they kill its relators.

The profinite construction allows finite quotients of any order. The pro-`p` construction starts
with the free pro-`p` group and therefore retains only finite `p`-group quotients.
Both universal properties are used to describe groups by finite sets of generators and relators.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 3.
-/

public section

namespace TauCeti

universe u v

/-- The closed normal closure of a set is a normal subgroup. This instance supplies the group
quotient structure used by the presented profinite and pro-`p` carriers below. -/
instance instNormal_topologicalClosure_normalClosure {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (s : Set G) :
    ((Subgroup.normalClosure s).topologicalClosure).Normal := by
  exact Subgroup.is_normal_topologicalClosure _

/-- The profinite group presented by generators `X` and relators `rels`, obtained by quotienting
the free profinite group by the closed normal closure of the relators. -/
noncomputable abbrev presentedProfiniteGroup (X : Type u)
    (rels : Set (freeProfiniteGroup X)) : Type u :=
  freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure

namespace presentedProfiniteGroup

/-- The canonical quotient map from the free profinite group to the presented profinite group. -/
noncomputable def mk {X : Type u} (rels : Set (freeProfiniteGroup X)) :
    freeProfiniteGroup X →ₜ* presentedProfiniteGroup X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical generator in a presented profinite group. -/
noncomputable def of {X : Type u} (rels : Set (freeProfiniteGroup X)) (x : X) :
    presentedProfiniteGroup X rels :=
  mk rels (freeProfiniteGroup.of x)

variable {X : Type u} {rels : Set (freeProfiniteGroup X)}

/-- A continuous homomorphism from the free profinite group that kills the relators factors through
the presented profinite group. -/
noncomputable def lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProfiniteGroup X rels →ₜ* G := by
  let R : Subgroup (freeProfiniteGroup X) := (Subgroup.normalClosure rels).topologicalClosure
  have hR : R ≤ ψ.toMonoidHom.ker := by
    exact Subgroup.topologicalClosure_minimal (Subgroup.normalClosure rels)
      (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hψ r hr))
      (isClosed_singleton.preimage ψ.continuous)
  let f : presentedProfiniteGroup X rels →* G := QuotientGroup.lift R ψ.toMonoidHom hR
  refine ⟨f, ?_⟩
  apply (QuotientGroup.isQuotientMap_mk R).continuous_iff.mpr
  -- The quotient-map criterion reduces continuity to this composite with the quotient projection.
  change Continuous (fun x => f (QuotientGroup.mk x))
  have hcomp : (fun x => f (QuotientGroup.mk x)) = ψ := by
    funext x
    exact QuotientGroup.lift_mk' (N := R) hR x
  rw [hcomp]
  exact ψ.continuous

/-- The factorisation through a presented profinite group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk rels) = ψ := by
  have hR : (Subgroup.normalClosure rels).topologicalClosure ≤ ψ.toMonoidHom.ker :=
    Subgroup.topologicalClosure_minimal (Subgroup.normalClosure rels)
      (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hψ r hr))
      (isClosed_singleton.preimage ψ.continuous)
  apply ContinuousMonoidHom.ext
  intro x
  -- Unfold the topological map wrappers to expose the quotient group's algebraic lift equation.
  change QuotientGroup.lift (N := (Subgroup.normalClosure rels).topologicalClosure)
    ψ.toMonoidHom hR (QuotientGroup.mk' _ x) = ψ x
  exact QuotientGroup.lift_mk' (N := (Subgroup.normalClosure rels).topologicalClosure) hR x

/-- The factorisation from a presented profinite group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of rels x) = ψ (freeProfiniteGroup.of x) := by
  -- Expand the named generator to the quotient-map composite this theorem characterizes.
  change (lift ψ hψ).comp (mk rels) (freeProfiniteGroup.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProfiniteGroup.of x)

/-- Two continuous homomorphisms out of a presented profinite group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {G : Type v} [Group G] [TopologicalSpace G]
    {φ ψ : presentedProfiniteGroup X rels →ₜ* G}
    (h : φ.comp (mk rels) = ψ.comp (mk rels)) : φ = ψ := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.topologicalClosure
    (Subgroup.normalClosure rels)) x
  exact DFunLike.congr_fun h y

/-- A continuous homomorphism out of the free profinite group that kills the relators factors
uniquely through the presented profinite group. -/
theorem existsUnique_lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    ∃! φ : presentedProfiniteGroup X rels →ₜ* G, φ.comp (mk rels) = ψ := by
  refine ⟨lift ψ hψ, lift_comp_mk ψ hψ, ?_⟩
  intro φ hφ
  exact hom_ext (hφ.trans (lift_comp_mk ψ hψ).symm)

end presentedProfiniteGroup

/-- The pro-`p` group presented by generators `X` and relators `rels`, obtained by quotienting the
free pro-`p` group by the closed normal closure of the relators. -/
noncomputable abbrev presentedProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) : Type u :=
  freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure

namespace presentedProP

/-- The canonical quotient map from the free pro-`p` group to the presented pro-`p` group. -/
noncomputable def mk (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) :
    freeProP p X →ₜ* presentedProP p X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical generator in a presented pro-`p` group. -/
noncomputable def of (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) (x : X) :
    presentedProP p X rels :=
  mk p rels (freeProP.of x)

/-- A presented pro-`p` group is pro-`p`, since it is a quotient of a free pro-`p` group. -/
theorem isProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) :
    IsProP p (presentedProP p X rels) :=
  (isProP_freeProP p X).quotient ((Subgroup.normalClosure rels).topologicalClosure)

variable {p : ℕ} {X : Type u} {rels : Set (freeProP p X)}

/-- A continuous homomorphism from the free pro-`p` group that kills the relators factors through
the presented pro-`p` group. -/
noncomputable def lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProP p X rels →ₜ* P := by
  let R : Subgroup (freeProP p X) := (Subgroup.normalClosure rels).topologicalClosure
  have hR : R ≤ ψ.toMonoidHom.ker := by
    exact Subgroup.topologicalClosure_minimal (Subgroup.normalClosure rels)
      (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hψ r hr))
      (isClosed_singleton.preimage ψ.continuous)
  let f : presentedProP p X rels →* P := QuotientGroup.lift R ψ.toMonoidHom hR
  refine ⟨f, ?_⟩
  apply (QuotientGroup.isQuotientMap_mk R).continuous_iff.mpr
  -- The quotient-map criterion reduces continuity to this composite with the quotient projection.
  change Continuous (fun x => f (QuotientGroup.mk x))
  have hcomp : (fun x => f (QuotientGroup.mk x)) = ψ := by
    funext x
    exact QuotientGroup.lift_mk' (N := R) hR x
  rw [hcomp]
  exact ψ.continuous

/-- The factorisation through a presented pro-`p` group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk p rels) = ψ := by
  have hR : (Subgroup.normalClosure rels).topologicalClosure ≤ ψ.toMonoidHom.ker :=
    Subgroup.topologicalClosure_minimal (Subgroup.normalClosure rels)
      (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hψ r hr))
      (isClosed_singleton.preimage ψ.continuous)
  apply ContinuousMonoidHom.ext
  intro x
  -- Unfold the topological map wrappers to expose the quotient group's algebraic lift equation.
  change QuotientGroup.lift (N := (Subgroup.normalClosure rels).topologicalClosure)
    ψ.toMonoidHom hR (QuotientGroup.mk' _ x) = ψ x
  exact QuotientGroup.lift_mk' (N := (Subgroup.normalClosure rels).topologicalClosure) hR x

/-- The factorisation from a presented pro-`p` group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of p rels x) = ψ (freeProP.of x) := by
  -- Expand the named generator to the quotient-map composite this theorem characterizes.
  change (lift ψ hψ).comp (mk p rels) (freeProP.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProP.of x)

/-- Two continuous homomorphisms out of a presented pro-`p` group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {P : Type v} [Group P] [TopologicalSpace P]
    {φ ψ : presentedProP p X rels →ₜ* P}
    (h : φ.comp (mk p rels) = ψ.comp (mk p rels)) : φ = ψ := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.topologicalClosure
    (Subgroup.normalClosure rels)) x
  exact DFunLike.congr_fun h y

/-- A continuous homomorphism out of the free pro-`p` group that kills the relators factors
uniquely through the presented pro-`p` group. -/
theorem existsUnique_lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    ∃! φ : presentedProP p X rels →ₜ* P, φ.comp (mk p rels) = ψ := by
  refine ⟨lift ψ hψ, lift_comp_mk ψ hψ, ?_⟩
  intro φ hφ
  exact hom_ext (hφ.trans (lift_comp_mk ψ hψ).symm)

end presentedProP

end TauCeti
