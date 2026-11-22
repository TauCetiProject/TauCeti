/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Transitivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.Topology.Algebra.MulAction.Orbit
import TauCeti.Topology.Maps.OpenQuotient

/-!
# Orbits of algebraic group actions are locally closed

Let a group scheme `G` act on a scheme `X` over `S`. Global points of `G` act on the underlying
space of `X` by the translation homeomorphisms, and they preserve every geometric orbit
`TauCeti.SchemeAction.orbit G x`.

When `G` is of finite type and `X` is quasi-compact and locally Noetherian, the geometric orbit
is constructible, by Chevalley's theorem. Over an arbitrary field `k`, when `G` and `X` are
locally of finite type with quasi-compact underlying spaces and `x` is a `k`-rational point of
`X`, the geometric orbit `orbit G x` is locally closed (`isLocallyClosed_orbit`): it is open in
its closure, and its boundary is closed and of strictly smaller dimension.

No algebraic closedness of `k`, smoothness, reducedness, affineness, separatedness or
connectedness hypothesis is needed, and `X` need not be irreducible. The orbit is the full
topological image of the orbit morphism, including its nonclosed points; it is not replaced by
the set of rational points. No subscheme structure on the orbit is constructed here.

Over an algebraically closed field, a closed point of the orbit lifts to a closed point of the
Jacobson scheme `G` (`Continuous.exists_isClosed_singleton_of_mem_range`), which is a rational
point of `G`; thus the rational points of `G` act transitively on the closed points of the orbit,
and local closedness follows from
`TauCeti.isLocallyClosed_of_isConstructible_of_closedPoints_transitive`. Over a general field `k`,
base change to `AlgebraicClosure k` pulls the orbit back along the projection
`X ×_k Spec (AlgebraicClosure k) ⟶ X` (`orbit_pullback`). Because every morphism to `Spec k` is
universally open and `Spec (AlgebraicClosure k) ⟶ Spec k` is surjective, this projection is an
open quotient map on underlying topological spaces, so local closedness descends by
`IsOpenQuotientMap.isLocallyClosed_preimage_iff`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(b), pp. 26–27, and §7.c.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  Topology
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

/-- The geometric orbit of a section is constructible when the group is of finite type and the
acted-on scheme is quasi-compact and locally Noetherian. -/
theorem isConstructible_orbit {S : Scheme.{u}} (G : Over S) {X : Over S} [MonObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [IsLocallyNoetherian X.left]
    [CompactSpace X.left] (x : 𝟙_ (Over S) ⟶ X) :
    IsConstructible (orbit G x) := by
  have : LocallyOfFiniteType (orbitMap G x).left := locallyOfFiniteType_orbitMap G x
  have h : orbit G x = Set.range (orbitMap G x).left := Set.ext (mem_orbit G x)
  simpa [h] using (orbitMap G x).left.isConstructible_image IsConstructible.univ

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))}

section Transitivity

variable [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
  [LocallyOfFiniteType X.hom]

omit [LocallyOfFiniteType X.hom] in
/-- Over an algebraically closed field, with `G` locally of finite type, any two closed
points of the geometric orbit of `x` are related by translation by a rational point of `G`. -/
theorem exists_translation_eq_of_mem_orbit_inter_closedPoints
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {p q : X.left}
    (hp : p ∈ orbit G x ∩ closedPoints X.left)
    (hq : q ∈ orbit G x ∩ closedPoints X.left) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (translation X g).hom.left p = q := by
  let := translationMulAction G X
  rw [orbit_inter_closedPoints] at hp hq
  obtain ⟨g, a, rfl⟩ := Set.mem_iUnion.mp hp
  obtain ⟨h, b, rfl⟩ := Set.mem_iUnion.mp hq
  obtain rfl : b = a := Subsingleton.elim (α := Spec (.of k)) _ _
  refine ⟨h * g⁻¹, ?_⟩
  rw [← translationMulAction_smul, translationMulAction_smul_apply,
    mul_smul, inv_smul_smul]

/-- Over an algebraically closed field, with `G` and `X` locally of finite type, an immersed
scheme lying in the geometric orbit of `x` inherits transitivity on closed points from any family
of automorphisms intertwining the ambient translations by rational points of `G`. -/
theorem exists_eq_of_equivariant_of_range_subset_orbit
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {Y : Scheme.{u}} (i : Y ⟶ X.left)
    [IsImmersion i] (hrange : Set.range i ⊆ orbit G x)
    (e : (𝟙_ (Over (Spec (.of k))) ⟶ G) → (Y ≅ Y))
    (he : ∀ g, (e g).hom ≫ i = i ≫ (translation X g).hom.left)
    {y z : Y} (hy : y ∈ closedPoints Y) (hz : z ∈ closedPoints Y) :
    ∃ g, (e g).hom y = z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hp (p : Y) (hp : p ∈ closedPoints Y) :
      i p ∈ orbit G x ∩ closedPoints X.left := by
    have h : i p ∈ i '' closedPoints Y := ⟨p, hp, rfl⟩
    rw [Scheme.Hom.image_closedPoints_eq_range_inter_closedPoints] at h
    exact ⟨hrange h.1, h.2⟩
  obtain ⟨g, hg⟩ := exists_translation_eq_of_mem_orbit_inter_closedPoints G x
    (hp y hy) (hp z hz)
  refine ⟨g, i.isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, hg]

end Transitivity

private theorem isLocallyClosed_orbit_of_isAlgClosed [GrpObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsLocallyClosed (orbit G x) := by
  have : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let := translationMulAction G X
  have := continuousConstSMul_translationMulAction (G := G) (X := X)
  refine isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (isConstructible_orbit G x) (preimage_smul_orbit · x) ?_
  intro p hp q hq
  simpa only [translationMulAction_smul] using
    exists_translation_eq_of_mem_orbit_inter_closedPoints G x hp hq

end AlgClosed

section Field

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) {X : Over (Spec (.of k))}
  [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- Over any field, the geometric orbit of a rational point under a finite-type group scheme
acting on a finite-type scheme is locally closed. Neither algebraic closedness of the ground
field nor smoothness, reducedness, affineness or separatedness is required. -/
theorem isLocallyClosed_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsLocallyClosed (orbit G x) := by
  let f := Spec.algebraMap k (AlgebraicClosure k)
  let := (Over.pullback f).modObjObj G X
  rw [← (pullback.fst X.hom f).isOpenQuotientMap.isLocallyClosed_preimage_iff,
    ← orbit_pullback G f x]
  exact isLocallyClosed_orbit_of_isAlgClosed ((Over.pullback f).obj G) _

/-- Over any field, the geometric orbit of a rational point is open in its closure. -/
theorem isOpen_orbitClosure_preimage_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsOpen ((Subtype.val : orbitClosure G x → X.left) ⁻¹' orbit G x) := by
  rw [orbitClosure_def]
  exact (isLocallyClosed_orbit G x).isOpen_preimage_val_closure

/-- Over any field, the boundary of the geometric orbit of a rational point is closed. -/
theorem isClosed_orbitBoundary (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsClosed (orbitBoundary G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact isOpen_compl_iff.mp (isLocallyClosed_orbit G x).isOpen_coborder

/-- Over any field, the closure of the geometric orbit of a rational point has the same dimension
as the orbit. -/
theorem topologicalKrullDim_orbitClosure (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitClosure G x) = topologicalKrullDim (orbit G x) := by
  rw [orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x)

/-- Over any field, the boundary of the geometric orbit of a rational point has strictly smaller
dimension than the orbit, even when the group is disconnected or the orbit closure is
reducible. -/
theorem topologicalKrullDim_orbitBoundary_lt (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitBoundary G x) < topologicalKrullDim (orbit G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_sdiff_lt_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x)
    ⟨x.left (IsLocalRing.closedPoint k), left_apply_mem_orbit G x _⟩

end Field

end TauCeti.SchemeAction
