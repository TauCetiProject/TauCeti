/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Stabilizer
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Proper
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Smooth
import TauCeti.Topology.Constructible.Jacobson
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Homogeneous schemes and orbit-scheme identification

When an algebraic group scheme `G` of finite type over an algebraically closed field `k` acts on
a finite-type `k`-scheme `X`, the orbit of a rational point `x : Spec k ⟶ X` covers all of `X`
(including nonclosed points) if and only if the rational points of `G` act transitively on the
rational points of `X`.

If moreover `X` is reduced, then the canonical equivariant orbit immersion
`orbitInclusion G x : orbitOver G x ⟶ X` is a surjective closed immersion into a reduced scheme,
hence an equivariant isomorphism `orbitInclusionIso G x h : orbitOver G x ≅ X`. Transporting the
orbit-scheme theory along this isomorphism shows that for a reduced finite-type group `G`:

* `X` itself is smooth over `Spec k`;
* the orbit morphism `orbitMap G x` is faithfully flat and locally of finite presentation;
* the orbit morphism `orbitMap G x` is smooth if and only if the scheme-theoretic stabilizer
  `stabilizer G x` is smooth over `Spec k` (and unconditionally so when `G` is affine in
  characteristic zero).

## Main declarations

* `TauCeti.SchemeAction.orbit_eq_univ_iff_closedPoints_subset`: over a field, a finite-type orbit
  covers `X` iff it contains every closed point of `X`.
* `TauCeti.SchemeAction.orbit_eq_univ_iff_forall_exists_smul`: over an algebraically closed field,
  the orbit of `x` covers `X` iff every rational point of `X` is a translate `g • x`.
* `TauCeti.SchemeAction.orbitInclusionIso`: for a reduced homogeneous scheme `X`, the equivariant
  isomorphism `orbitOver G x ≅ X`.
* `TauCeti.SchemeAction.smooth_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.flat_orbitMap_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.smooth_orbitMap_iff_of_orbit_eq_univ`: smoothness and flatness consequences
  for homogeneous schemes and their orbit morphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.e, Propositions 7.11 and 7.15.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Topology

namespace TauCeti.SchemeAction

universe u

section Field

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) {X : Over (Spec (.of k))}
  [MonObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- Over a field, the geometric orbit of a rational point covers a finite-type scheme `X` if and
only if it contains every closed point of `X`. -/
theorem orbit_eq_univ_iff_closedPoints_subset (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    orbit G x = Set.univ ↔ closedPoints X.left ⊆ orbit G x := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [(isConstructible_orbit G x).eq_iff_inter_closedPoints_eq IsConstructible.univ,
    Set.univ_inter, Set.inter_eq_right]

end Field

section Transitivity

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [MonObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- Over an algebraically closed field, the geometric orbit of `x` covers all of `X` (including
nonclosed points) if and only if every rational point of `X` is a translate of `x` by a rational
point of `G`. -/
theorem orbit_eq_univ_iff_forall_exists_smul (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    orbit G x = Set.univ ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  rw [orbit_eq_univ_iff_closedPoints_subset]
  refine ⟨fun h y ↦ ?_, fun h c hc ↦ ?_⟩
  · exact (left_apply_mem_orbit_iff G x y (IsLocalRing.closedPoint k)).mp <|
      h (mem_closedPoints_iff.mpr
        (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section (Over.w y)))
  · let y : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (U := 𝟙_ _) (V := X) (pointOfClosedPoint X.hom c hc)
        (pointOfClosedPoint_comp X.hom c _)
    have hmem : y.left (IsLocalRing.closedPoint k) ∈ orbit G x :=
      (left_apply_mem_orbit_iff G x y (IsLocalRing.closedPoint k)).mpr (h y)
    have hy : y.left (IsLocalRing.closedPoint k) = c := pointOfClosedPoint_apply X.hom c hc _
    rwa [hy] at hmem

/-- Over an algebraically closed field, the orbit morphism is surjective on all scheme points if
and only if every rational point of `X` is a translate of `x` by a rational point of `G`. -/
theorem surjective_orbitMap_iff_forall_exists_smul (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    Surjective (orbitMap G x).left ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y :=
  (surjective_orbitMap_iff_orbit_eq_univ G x).trans (orbit_eq_univ_iff_forall_exists_smul G x)

end Transitivity

section Homogeneous

variable {k : Type u} [Field k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- When a single orbit covers `X`, the orbit immersion is a closed immersion. -/
theorem isClosedImmersion_orbitι_of_orbit_eq_univ (h : orbit G x = Set.univ) :
    IsClosedImmersion (orbitι G x) :=
  (isClosedImmersion_orbitι_iff G x).mpr (h ▸ isClosed_univ)

/-- When a single orbit covers `X`, the orbit immersion is surjective. -/
theorem surjective_orbitι_of_orbit_eq_univ (h : orbit G x = Set.univ) :
    Surjective (orbitι G x) :=
  ⟨Set.range_eq_univ.mp ((range_orbitι G x).trans h)⟩

/-- When a single orbit covers a reduced finite-type scheme `X`, the orbit immersion is an
isomorphism of schemes. -/
theorem isIso_orbitι_of_orbit_eq_univ [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsIso (orbitι G x) := by
  have : IsClosedImmersion (orbitι G x) := isClosedImmersion_orbitι_of_orbit_eq_univ G x h
  have : Surjective (orbitι G x) := surjective_orbitι_of_orbit_eq_univ G x h
  exact isIso_of_isClosedImmersion_of_surjective (orbitι G x)

/-- When a single orbit covers a reduced finite-type scheme `X`, the orbit inclusion over `Spec k`
is an isomorphism. -/
theorem isIso_orbitInclusion_of_orbit_eq_univ [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsIso (orbitInclusion G x) := by
  have : IsIso ((Over.forget _).map (orbitInclusion G x)) := by
    rw [Over.forget_map, orbitInclusion_left]
    exact isIso_orbitι_of_orbit_eq_univ G x h
  exact isIso_of_reflects_iso (orbitInclusion G x) (Over.forget _)

/-- The canonical equivariant isomorphism between the orbit scheme `orbitOver G x` and a reduced
homogeneous scheme `X`. -/
def orbitInclusionIso [IsReduced X.left] (h : orbit G x = Set.univ) :
    orbitOver G x ≅ X :=
  have : IsIso (orbitInclusion G x) := isIso_orbitInclusion_of_orbit_eq_univ G x h
  asIso (orbitInclusion G x)

/-- The forward direction of `orbitInclusionIso` is the orbit inclusion. -/
@[simp]
theorem orbitInclusionIso_hom [IsReduced X.left] (h : orbit G x = Set.univ) :
    (orbitInclusionIso G x h).hom = orbitInclusion G x := (rfl)

/-- Composing the orbit morphism with the inverse of `orbitInclusionIso` recovers the orbit
projection. -/
@[reassoc (attr := simp)]
theorem orbitMap_comp_orbitInclusionIso_inv [IsReduced X.left] (h : orbit G x = Set.univ) :
    orbitMap G x ≫ (orbitInclusionIso G x h).inv = orbitProjection G x := by
  rw [← orbitProjection_inclusion G x, ← orbitInclusionIso_hom G x h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- `orbitInclusionIso` is equivariant. -/
instance [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsModHom G (orbitInclusionIso G x h).hom := by
  rw [orbitInclusionIso_hom]
  infer_instance

/-- Every reduced finite-type homogeneous scheme for a reduced finite-type group over an
algebraically closed field is smooth. -/
theorem smooth_of_orbit_eq_univ [IsAlgClosed k] [IsReduced G.left] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth X.hom := by
  have hcomp : (orbitInclusionIso G x h).inv.left ≫ orbitToBase G x = X.hom :=
    Over.w (orbitInclusionIso G x h).inv
  rw [← hcomp]
  infer_instance

/-- The orbit morphism onto a reduced finite-type homogeneous scheme for a reduced finite-type
group over an algebraically closed field is flat. -/
theorem flat_orbitMap_of_orbit_eq_univ [IsAlgClosed k] [IsReduced G.left] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Flat (orbitMap G x).left := by
  have hcomp : toOrbit G x ≫ (orbitInclusionIso G x h).hom.left = (orbitMap G x).left := by
    rw [orbitInclusionIso_hom, orbitInclusion_left, toOrbit_ι]
  rw [← hcomp]
  infer_instance

/-- For a reduced finite-type group acting transitively on a reduced finite-type scheme `X` over
an algebraically closed field, the orbit morphism `G ⟶ X` is smooth if and only if the
scheme-theoretic stabilizer `stabilizer G x` is smooth over `Spec k`. -/
theorem smooth_orbitMap_iff_of_orbit_eq_univ [IsAlgClosed k] [IsReduced G.left] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  refine Iff.trans ?_ (smooth_toOrbit_iff G x)
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have hinv : (orbitMap G x).left ≫ (orbitInclusionIso G x h).inv.left = toOrbit G x := by
      rw [← Over.comp_left, orbitMap_comp_orbitInclusionIso_inv, orbitProjection_left]
    rw [← hinv]
    infer_instance
  · have hcomp : toOrbit G x ≫ (orbitInclusionIso G x h).hom.left = (orbitMap G x).left := by
      rw [orbitInclusionIso_hom, orbitInclusion_left, toOrbit_ι]
    rw [← hcomp]
    infer_instance

/-- In characteristic zero, the orbit morphism from an affine finite-type group onto a reduced
finite-type homogeneous scheme over an algebraically closed field is smooth. -/
theorem smooth_orbitMap_of_orbit_eq_univ_of_charZero [CharZero k] [IsAffine G.left]
    [IsReduced X.left] (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left := by
  have hcomp : toOrbit G x ≫ (orbitInclusionIso G x h).hom.left = (orbitMap G x).left := by
    rw [orbitInclusionIso_hom, orbitInclusion_left, toOrbit_ι]
  rw [← hcomp]
  infer_instance

end Homogeneous

end TauCeti.SchemeAction
