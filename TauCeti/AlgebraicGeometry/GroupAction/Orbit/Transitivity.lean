/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Basic
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.Topology.Constructible.Jacobson
import TauCeti.Topology.JacobsonSpace

/-!
# Transitivity criteria for geometric orbits of scheme actions

Let a monoid or group scheme `G` act on a scheme `X` over a field `k`, and let `x : Spec k ⟶ X`
be a rational point of `X`. This file compares coverage of `X` by the geometric orbit
`orbit G x` (all scheme points, including nonclosed points) with closed-point coverage and
rational-point transitivity, without importing orbit local closedness or dimension theory.

## Main declarations

* `TauCeti.SchemeAction.orbit_inter_closedPoints`: over an algebraically closed field with `G`
  locally of finite type, the closed points of `orbit G x` are the rational translates `g • x`.
* `TauCeti.SchemeAction.left_apply_mem_orbit_iff`: over an algebraically closed field with `G`
  locally of finite type, a rational point lies in `orbit G x` iff it is a rational translate of
  `x`.
* `TauCeti.SchemeAction.forall_exists_smul_of_orbit_eq_univ`: if `orbit G x = Set.univ` over an
  algebraically closed field with `G` locally of finite type, then every rational point of `X` is a
  rational translate of `x`.
* `TauCeti.SchemeAction.orbit_eq_univ_iff_closedPoints_subset`: over any field, when `X` is
  locally of finite type and `orbitMap G x` is quasi-compact, `orbit G x = Set.univ` iff it
  contains every closed point of `X`.
* `TauCeti.SchemeAction.orbit_eq_univ_iff_forall_exists_smul` and
  `TauCeti.SchemeAction.surjective_orbitMap_iff_forall_exists_smul`: over an algebraically closed
  field, when `X` is locally of finite type and `orbitMap G x` is quasi-compact, `orbit G x`
  covers `X` (equivalently `orbitMap G x` is surjective) iff `G(k)` acts transitively on `X(k)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Topology
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))} [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]

/-- Over an algebraically closed field, with `G` locally of finite type, the orbit morphism sends
every closed point of `G` to a translate of `x` by a rational point of `G`. -/
theorem exists_orbitMap_left_apply_eq_smul_left_apply (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    {c : G.left} (hc : IsClosed {c}) (a : (𝟙_ (Over (Spec (.of k)))).left) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (orbitMap G x).left c = (g • x).left a := by
  let g : 𝟙_ (Over (Spec (.of k))) ⟶ G :=
    Over.homMk (U := 𝟙_ _) (V := G) (pointOfClosedPoint G.hom c hc)
      (pointOfClosedPoint_comp G.hom c _)
  refine ⟨g, ?_⟩
  rw [← left_comp_orbitMap_left, Scheme.Hom.comp_apply]
  exact congrArg _ (pointOfClosedPoint_apply G.hom c hc a).symm

/-- Over an algebraically closed field, with `G` locally of finite type, the closed points of the
geometric orbit of `x` are exactly the points underlying its translates by rational points of
`G`. -/
theorem orbit_inter_closedPoints (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    orbit G x ∩ closedPoints X.left =
      ⋃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range (g • x).left := by
  refine Set.Subset.antisymm (fun p ⟨hpo, hpc⟩ ↦ ?_) ?_
  · -- A closed point of the orbit is the image of a closed point of the Jacobson scheme `G`,
    -- which is a rational point of `G`.
    have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
    obtain ⟨c, hc, hfc⟩ := (orbitMap G x).left.continuous.exists_isClosed_singleton_of_mem_range
      (mem_closedPoints_iff.mp hpc).isLocallyClosed ((mem_orbit G x p).mp hpo)
    obtain ⟨g, hg⟩ :=
      exists_orbitMap_left_apply_eq_smul_left_apply G x hc (IsLocalRing.closedPoint k)
    exact Set.mem_iUnion.mpr ⟨g, _, hg.symm.trans hfc⟩
  simp only [Set.iUnion_subset_iff]
  rintro g _ ⟨a, rfl⟩
  refine ⟨smul_left_apply_mem_orbit G x g a, ?_⟩
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  exact mem_closedPoints_iff.mpr
    (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section (Over.w (g • x)))

/-- Over an algebraically closed field, with `G` locally of finite type, a rational point of `X`
lies in the geometric orbit of `x` exactly when it is a translate of `x` by a rational point of
`G`. -/
theorem left_apply_mem_orbit_iff (x y : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (a : (𝟙_ (Over (Spec (.of k)))).left) :
    y.left a ∈ orbit G x ↔ ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ smul_left_apply_mem_orbit G x g a⟩
  -- The rational point `y` is a closed point of the orbit, hence a translate `g • x` at the
  -- underlying point; two sections agreeing at a point of `Spec k` are equal.
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  have hy : y.left (IsLocalRing.closedPoint k) ∈ orbit G x ∩ closedPoints X.left :=
    ⟨h, mem_closedPoints_iff.mpr
      (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section (Over.w y))⟩
  rw [orbit_inter_closedPoints] at hy
  obtain ⟨g, b, hb⟩ := Set.mem_iUnion.mp hy
  obtain rfl : b = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  refine ⟨g, Over.OverMorphism.ext ?_⟩
  simpa only [Category.id_comp] using
    (TauCeti.AlgebraicGeometry.comp_eq_comp_iff_of_section (Over.w (g • x)) (Over.w y) (𝟙 _)
      (IsLocalRing.closedPoint k)).mpr hb

/-- Over an algebraically closed field, when `G` is locally of finite type and the geometric orbit
of `x` covers `X`, every rational point of `X` is a translate of `x` by a rational point of
`G`. -/
theorem forall_exists_smul_of_orbit_eq_univ (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (h : orbit G x = Set.univ) (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y :=
  (left_apply_mem_orbit_iff G x y (IsLocalRing.closedPoint k)).mp (h ▸ Set.mem_univ _)

end AlgClosed

section Field

/-- Over a field, the geometric orbit of a rational point covers a locally finite-type scheme `X`
if and only if it contains every closed point of `X`. -/
theorem orbit_eq_univ_iff_closedPoints_subset {k : Type u} [Field k] (G : Over (Spec (.of k)))
    {X : Over (Spec (.of k))} [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
    [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] :
    orbit G x = Set.univ ↔ closedPoints X.left ⊆ orbit G x := by
  refine ⟨fun h ↦ h ▸ Set.subset_univ _, fun h ↦ Set.eq_univ_iff_forall.mpr fun p ↦ ?_⟩
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : LocallyOfFinitePresentation (orbitMap G x).left :=
    locallyOfFinitePresentation_orbitMap G x
  have hloc : IsLocallyConstructible (orbit G x) := by
    simpa [orbit_def] using (orbitMap G x).left.isLocallyConstructible_image
      IsLocallyConstructible.univ
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top p)
  exact ((hV.isCompact.isConstructible V.isOpen).subset_iff_inter_closedPoints_subset
    (hloc.inter_of_isOpen_isCompact V.isOpen hV.isCompact)).mpr
      (fun q ⟨hqV, hqc⟩ ↦ ⟨⟨h hqc, hqV⟩, hqc⟩) hpV |>.1

end Field

section AlgClosedFiniteType

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))} [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
  [LocallyOfFiniteType X.hom]

/-- Over an algebraically closed field, the geometric orbit of `x` covers all of `X` (including
nonclosed points) if and only if every rational point of `X` is a translate of `x` by a rational
point of `G`. -/
theorem orbit_eq_univ_iff_forall_exists_smul (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] :
    orbit G x = Set.univ ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  refine ⟨forall_exists_smul_of_orbit_eq_univ G x, fun h ↦ ?_⟩
  rw [orbit_eq_univ_iff_closedPoints_subset]
  intro p hp
  have hpc : IsClosed {p} := mem_closedPoints_iff.mp hp
  let y : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
    Over.homMk (AlgebraicGeometry.pointOfClosedPoint X.hom p hpc)
      (AlgebraicGeometry.pointOfClosedPoint_comp X.hom p hpc)
  obtain ⟨g, hg⟩ := h y
  have hy : y.left (IsLocalRing.closedPoint k) = p :=
    AlgebraicGeometry.pointOfClosedPoint_apply X.hom p hpc _
  rw [← hy, ← hg]
  exact smul_left_apply_mem_orbit G x g _

/-- Over an algebraically closed field, the orbit morphism is surjective on all scheme points if
and only if every rational point of `X` is a translate of `x` by a rational point of `G`. -/
theorem surjective_orbitMap_iff_forall_exists_smul (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] :
    Surjective (orbitMap G x).left ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y :=
  (surjective_orbitMap_iff_orbit_eq_univ G x).trans (orbit_eq_univ_iff_forall_exists_smul G x)

end AlgClosedFiniteType

end TauCeti.SchemeAction
