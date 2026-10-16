/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.GeodesicPath

/-!
# Nonbranching families of geodesics

A family of constant-speed geodesics is *nonbranching* if two members that agree for a positive
initial interval agree everywhere. This is a property of a family of paths, rather than of the
ambient space: measure-theoretic applications only require almost every path of a transport plan
to belong to one nonbranching family.

The full family of geodesics in a strictly convex real normed space is nonbranching. Indeed, every
constant-speed geodesic is the affine segment between its endpoints, and equality at one positive
time determines the second endpoint. This supplies the geometric input for essential
nonbranching of reference measures on such spaces.

## Main definitions and results

* `Set.IsNonbranchingGeodesics`: a set of geodesic paths in which agreement on a positive initial
  interval forces equality;
* `Set.IsNonbranchingGeodesics.mono`: every subfamily of a nonbranching family is nonbranching;
* `TauCeti.isNonbranchingGeodesics_geodesicPaths`: all geodesics in a strictly convex normed
  space form a nonbranching family.

## References

* F. Cavalletti and A. Mondino, *Optimal maps in essentially non-branching spaces*, Commun.
  Contemp. Math. 19 (2017), 1750007, Definition 2.1.
-/

public section

open Set
open scoped unitInterval

namespace Set

variable {X : Type*} [PseudoMetricSpace X]

/-- A set `Γ` of paths is a **nonbranching family of geodesics** if every member is a
constant-speed geodesic and two members that agree throughout some positive initial interval are
equal. The time witnessing agreement may be `1`; that case already says the paths agree
everywhere and does not change the notion. -/
def IsNonbranchingGeodesics (Γ : Set C(I, X)) : Prop :=
  Γ ⊆ TauCeti.geodesicPaths X ∧
    ∀ ⦃γ₁⦄, γ₁ ∈ Γ → ∀ ⦃γ₂⦄, γ₂ ∈ Γ →
      (∃ t : I, 0 < (t : ℝ) ∧ ∀ s : I, s ≤ t → γ₁ s = γ₂ s) → γ₁ = γ₂

/-- The defining characterization of a nonbranching family of geodesics. -/
theorem isNonbranchingGeodesics_iff {Γ : Set C(I, X)} :
    Γ.IsNonbranchingGeodesics ↔
      Γ ⊆ TauCeti.geodesicPaths X ∧
        ∀ ⦃γ₁⦄, γ₁ ∈ Γ → ∀ ⦃γ₂⦄, γ₂ ∈ Γ →
          (∃ t : I, 0 < (t : ℝ) ∧ ∀ s : I, s ≤ t → γ₁ s = γ₂ s) → γ₁ = γ₂ :=
  Iff.rfl

/-- Every path in a nonbranching family is a geodesic. -/
theorem IsNonbranchingGeodesics.subset_geodesicPaths {Γ : Set C(I, X)}
    (hΓ : Γ.IsNonbranchingGeodesics) : Γ ⊆ TauCeti.geodesicPaths X :=
  hΓ.1

/-- Two paths in a nonbranching family that agree on a positive initial interval are equal. -/
theorem IsNonbranchingGeodesics.eq_of_eqOn_Iic {Γ : Set C(I, X)}
    (hΓ : Γ.IsNonbranchingGeodesics) {γ₁ γ₂ : C(I, X)} (hγ₁ : γ₁ ∈ Γ) (hγ₂ : γ₂ ∈ Γ)
    {t : I} (ht : 0 < (t : ℝ)) (h : ∀ s : I, s ≤ t → γ₁ s = γ₂ s) : γ₁ = γ₂ :=
  hΓ.2 hγ₁ hγ₂ ⟨t, ht, h⟩

/-- A subfamily of a nonbranching family of geodesics is nonbranching. -/
theorem IsNonbranchingGeodesics.mono {Γ Δ : Set C(I, X)} (hΓ : Γ.IsNonbranchingGeodesics)
    (hΔ : Δ ⊆ Γ) : Δ.IsNonbranchingGeodesics :=
  ⟨hΔ.trans hΓ.1, fun _ hγ₁ _ hγ₂ ↦ hΓ.2 (hΔ hγ₁) (hΔ hγ₂)⟩

/-- A subsingleton family consisting of geodesic paths is nonbranching. -/
theorem Subsingleton.isNonbranchingGeodesics {Γ : Set C(I, X)} (hΓ : Γ.Subsingleton)
    (hgeo : Γ ⊆ TauCeti.geodesicPaths X) : Γ.IsNonbranchingGeodesics :=
  ⟨hgeo, fun _ hγ₁ _ hγ₂ _ ↦ hΓ hγ₁ hγ₂⟩

/-- The empty family is a nonbranching family of geodesics. -/
@[simp]
theorem isNonbranchingGeodesics_empty :
    (∅ : Set C(I, X)).IsNonbranchingGeodesics :=
  Set.subsingleton_empty.isNonbranchingGeodesics (by simp)

/-- A singleton is a nonbranching family of geodesics exactly when its member is a geodesic. -/
@[simp]
theorem isNonbranchingGeodesics_singleton {γ : C(I, X)} :
    ({γ} : Set C(I, X)).IsNonbranchingGeodesics ↔ γ ∈ TauCeti.geodesicPaths X := by
  refine ⟨fun h ↦ h.1 (mem_singleton γ), fun h ↦
    Set.subsingleton_singleton.isNonbranchingGeodesics ?_⟩
  simpa only [singleton_subset_iff]

end Set

namespace TauCeti

section StrictConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- The full family of constant-speed geodesics in a strictly convex real normed space is
nonbranching. -/
theorem isNonbranchingGeodesics_geodesicPaths :
    (geodesicPaths E).IsNonbranchingGeodesics := by
  refine ⟨Subset.rfl, ?_⟩
  intro γ₁ hγ₁ γ₂ hγ₂
  rintro ⟨t, ht, hagree⟩
  have h0 : γ₁ 0 = γ₂ 0 := hagree 0 (unitInterval.nonneg t)
  have heqt : γ₁ t = γ₂ t := hagree t le_rfl
  have hend : γ₁ 1 = γ₂ 1 := by
    rw [eq_segmentPath_of_mem_geodesicPaths hγ₁, eq_segmentPath_of_mem_geodesicPaths hγ₂,
      segmentPath_apply, segmentPath_apply,
      AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module, h0] at heqt
    exact smul_right_injective E ht.ne' (add_left_cancel heqt)
  rw [eq_segmentPath_of_mem_geodesicPaths hγ₁, eq_segmentPath_of_mem_geodesicPaths hγ₂, h0,
    hend]

end StrictConvex

end TauCeti
