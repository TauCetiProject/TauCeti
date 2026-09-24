/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Subgroup

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

/-- The canonical quotient map onto a presented profinite group is surjective. -/
theorem mk_surjective {X : Type u} (rels : Set (freeProfiniteGroup X)) :
    Function.Surjective (mk rels) :=
  QuotientGroup.mk'_surjective _

/-- The canonical generator in a presented profinite group. -/
noncomputable def of {X : Type u} (rels : Set (freeProfiniteGroup X)) (x : X) :
    presentedProfiniteGroup X rels :=
  mk rels (freeProfiniteGroup.of x)

variable {X : Type u} {rels : Set (freeProfiniteGroup X)}

/-- The quotient map kills every relator. -/
@[simp]
theorem mk_relator (r : freeProfiniteGroup X) (hr : r ∈ rels) : mk rels r = 1 := by
  -- Reduce the named presentation carrier and map to the quotient form accepted by Mathlib's
  -- quotient kernel criterion.
  change (r : freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1
  exact (QuotientGroup.eq_one_iff r).mpr
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr))

/-- The kernel of the presentation map consists exactly of the closed normal closure of the
relators. -/
@[simp]
theorem mk_eq_one_iff (r : freeProfiniteGroup X) :
    mk rels r = 1 ↔ r ∈ (Subgroup.normalClosure rels).topologicalClosure := by
  -- Expose the quotient representation so Mathlib's general criterion applies.
  change (r : freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1 ↔ _
  exact QuotientGroup.eq_one_iff r

/-- A continuous homomorphism from the free profinite group that kills the relators factors through
the presented profinite group. -/
noncomputable def lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProfiniteGroup X rels →ₜ* G := by
  let R : Subgroup (freeProfiniteGroup X) := (Subgroup.normalClosure rels).topologicalClosure
  exact ContinuousMonoidHom.quotientLift R ψ
    (topologicalClosure_normalClosure_le_ker rels ψ hψ)

/-- The factorisation through a presented profinite group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk rels) = ψ := by
  -- Unfold the presentation's lift and map only far enough to apply Mathlib's quotient
  -- factorization equation.
  change (ContinuousMonoidHom.quotientLift (Subgroup.normalClosure rels).topologicalClosure ψ
    (topologicalClosure_normalClosure_le_ker rels ψ hψ)).comp
      (ContinuousMonoidHom.quotientMk (Subgroup.normalClosure rels).topologicalClosure) = ψ
  exact ContinuousMonoidHom.quotientLift_comp_quotientMk _ _ _

/-- The factorisation from a presented profinite group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of rels x) = ψ (freeProfiniteGroup.of x) := by
  -- Reduce the named generator and lift to the quotient-map composite characterized by
  -- `lift_comp_mk`; these definitions compute by unfolding to the corresponding quotient maps.
  change (lift ψ hψ).comp (mk rels) (freeProfiniteGroup.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProfiniteGroup.of x)

/-- Two continuous homomorphisms out of a presented profinite group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {G : Type v} [Group G] [TopologicalSpace G]
    {φ ψ : presentedProfiniteGroup X rels →ₜ* G}
    (h : φ.comp (mk rels) = ψ.comp (mk rels)) : φ = ψ := by
  let R : Subgroup (freeProfiniteGroup X) :=
    (Subgroup.normalClosure rels).topologicalClosure
  let f := ψ.comp (mk rels)
  have hR : R ≤ f.ker := ContinuousMonoidHom.le_ker_comp_quotientMk R ψ
  have hφ := ContinuousMonoidHom.quotientLift_unique R f hR φ (fun x => by
    exact DFunLike.congr_fun h x)
  have hψ := ContinuousMonoidHom.quotientLift_unique R f hR ψ (fun _ => rfl)
  exact hφ.trans hψ.symm

/-- Two continuous homomorphisms out of a presented profinite group are equal if they agree on
the canonical generators. -/
@[ext]
theorem hom_ext_of {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]
    {φ ψ : presentedProfiniteGroup X rels →ₜ* G}
    (h : ∀ x : X, φ (of rels x) = ψ (of rels x)) : φ = ψ := by
  apply hom_ext
  apply freeProfiniteGroup.hom_ext
  exact h

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

/-- The canonical quotient map onto a presented pro-`p` group is surjective. -/
theorem mk_surjective (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) :
    Function.Surjective (mk p rels) :=
  QuotientGroup.mk'_surjective _

/-- The canonical generator in a presented pro-`p` group. -/
noncomputable def of (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) (x : X) :
    presentedProP p X rels :=
  mk p rels (freeProP.of x)

/-- A presented pro-`p` group is pro-`p`, since it is a quotient of a free pro-`p` group. -/
theorem isProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) :
    IsProP p (presentedProP p X rels) :=
  (isProP_freeProP p X).quotient ((Subgroup.normalClosure rels).topologicalClosure)

variable {p : ℕ} {X : Type u} {rels : Set (freeProP p X)}

/-- The quotient map kills every relator. -/
@[simp]
theorem mk_relator (r : freeProP p X) (hr : r ∈ rels) : mk p rels r = 1 := by
  -- Reduce the named presentation carrier and map to the quotient form accepted by Mathlib's
  -- quotient kernel criterion.
  change (r : freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1
  exact (QuotientGroup.eq_one_iff r).mpr
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr))

/-- The kernel of the presentation map consists exactly of the closed normal closure of the
relators. -/
@[simp]
theorem mk_eq_one_iff (r : freeProP p X) :
    mk p rels r = 1 ↔ r ∈ (Subgroup.normalClosure rels).topologicalClosure := by
  -- Expose the quotient representation so Mathlib's general criterion applies.
  change (r : freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1 ↔ _
  exact QuotientGroup.eq_one_iff r

/-- A continuous homomorphism from the free pro-`p` group that kills the relators factors through
the presented pro-`p` group. -/
noncomputable def lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProP p X rels →ₜ* P := by
  let R : Subgroup (freeProP p X) := (Subgroup.normalClosure rels).topologicalClosure
  exact ContinuousMonoidHom.quotientLift R ψ
    (topologicalClosure_normalClosure_le_ker rels ψ hψ)

/-- The factorisation through a presented pro-`p` group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk p rels) = ψ := by
  -- Unfold the presentation's lift and map only far enough to apply Mathlib's quotient
  -- factorization equation.
  change (ContinuousMonoidHom.quotientLift (Subgroup.normalClosure rels).topologicalClosure ψ
    (topologicalClosure_normalClosure_le_ker rels ψ hψ)).comp
      (ContinuousMonoidHom.quotientMk (Subgroup.normalClosure rels).topologicalClosure) = ψ
  exact ContinuousMonoidHom.quotientLift_comp_quotientMk _ _ _

/-- The factorisation from a presented pro-`p` group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of p rels x) = ψ (freeProP.of x) := by
  -- Reduce the named generator and lift to the quotient-map composite characterized by
  -- `lift_comp_mk`; these definitions compute by unfolding to the corresponding quotient maps.
  change (lift ψ hψ).comp (mk p rels) (freeProP.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProP.of x)

/-- Two continuous homomorphisms out of a presented pro-`p` group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {P : Type v} [Group P] [TopologicalSpace P]
    {φ ψ : presentedProP p X rels →ₜ* P}
    (h : φ.comp (mk p rels) = ψ.comp (mk p rels)) : φ = ψ := by
  let R : Subgroup (freeProP p X) := (Subgroup.normalClosure rels).topologicalClosure
  let f := ψ.comp (mk p rels)
  have hR : R ≤ f.ker := ContinuousMonoidHom.le_ker_comp_quotientMk R ψ
  have hφ := ContinuousMonoidHom.quotientLift_unique R f hR φ (fun x => by
    exact DFunLike.congr_fun h x)
  have hψ := ContinuousMonoidHom.quotientLift_unique R f hR ψ (fun _ => rfl)
  exact hφ.trans hψ.symm

/-- Two continuous homomorphisms out of a presented pro-`p` group are equal if they agree on
the canonical generators. -/
@[ext]
theorem hom_ext_of {P : Type v} [Group P] [TopologicalSpace P] [T2Space P]
    {φ ψ : presentedProP p X rels →ₜ* P}
    (h : ∀ x : X, φ (of p rels x) = ψ (of p rels x)) : φ = ψ := by
  apply hom_ext
  apply freeProP.hom_ext
  exact h

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
