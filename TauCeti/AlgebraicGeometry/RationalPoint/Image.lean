/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
public import TauCeti.Topology.Constructible.Jacobson

/-!
# Rational points in images of scheme morphisms

Over an algebraically closed field `k`, a `k`-point of an arbitrary scheme lies in the topological
image of a morphism locally of finite type exactly when it lifts to a `k`-point of the source.
This compares the full scheme image, which can contain nonclosed points, with the image on
rational points. No reducedness, smoothness or separability hypothesis is needed.

Constructible subsets of a locally finite-type scheme are determined by their rational
points; in particular a nonempty locally closed subset contains a rational point. Chevalley's
theorem therefore detects on rational points the inclusion of the image of a morphism from a
locally finite-type scheme in the image of a morphism from a finite-type scheme, and the
surjectivity of a morphism from a finite-type scheme, all over a locally finite-type target.
These comparisons allow rational orbit calculations to control the full constructible image of an
algebraic orbit morphism.

The proofs use Mathlib's `pointOfClosedPoint` and Chevalley theorem. Lifting a rational point
along a morphism locally of finite type rests on the fact that a nonempty fibre locally of finite
type over an algebraically closed field has a rational point.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c, the comparison of geometric orbits with
  rational-point orbits.
-/

public section

open CategoryTheory Limits Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z : Scheme.{u}}

/-- A nonempty locally closed subset of a locally finite-type scheme over an algebraically
closed field contains a rational point. -/
theorem _root_.IsLocallyClosed.exists_rationalPoint_mem {s : Set Y} (hs : IsLocallyClosed s)
    (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType π] (hne : s.Nonempty) :
    ∃ p : Spec (.of k) ⟶ Y, p ≫ π = 𝟙 _ ∧ p (IsLocalRing.closedPoint k) ∈ s := by
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace π
  obtain ⟨y, hys, hyc⟩ := nonempty_inter_closedPoints hne hs
  have hyclosed : IsClosed {y} := mem_closedPoints_iff.mp hyc
  exact ⟨pointOfClosedPoint π y hyclosed, pointOfClosedPoint_comp π y hyclosed,
    (pointOfClosedPoint_apply π y hyclosed _).symm ▸ hys⟩

/-- For an algebraically closed field `k` and a morphism `f : X ⟶ Y` locally of finite type between
arbitrary schemes, a `k`-point `p : Spec k ⟶ Y` lifts along `f` to a `k`-point of `X` if and only
if its image point lies in the image of `f`. -/
theorem exists_comp_eq_iff_mem_range (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ Y) :
    (∃ q : Spec (.of k) ⟶ X, q ≫ f = p) ↔ p (IsLocalRing.closedPoint k) ∈ Set.range f := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q (IsLocalRing.closedPoint k), (q.comp_apply f _).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := p) x
      (IsLocalRing.closedPoint k) hx
    obtain ⟨s, hs, -⟩ := IsLocallyClosed.exists_rationalPoint_mem (Y := pullback f p)
      (isOpen_univ.isLocallyClosed) (pullback.snd f p) ⟨z, trivial⟩
    exact ⟨s ≫ pullback.fst f p, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩

/-- Inclusion between constructible subsets of a locally finite-type scheme over an
algebraically closed field can be tested on rational points. -/
theorem _root_.Topology.IsConstructible.subset_iff_forall_rationalPoint
    {s t : Set Y} (hs : IsConstructible s) (π : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType π] (ht : IsConstructible t) :
    s ⊆ t ↔ ∀ (p : Spec (.of k) ⟶ Y), p ≫ π = 𝟙 _ →
      p (IsLocalRing.closedPoint k) ∈ s → p (IsLocalRing.closedPoint k) ∈ t := by
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace π
  refine ⟨fun h _ _ hy ↦ h hy, fun h ↦ (hs.subset_iff_inter_closedPoints_subset ht).mpr ?_⟩
  rintro y ⟨hys, hyc⟩
  have hyclosed : IsClosed {y} := mem_closedPoints_iff.mp hyc
  refine ⟨?_, hyc⟩
  have heval := pointOfClosedPoint_apply π y hyclosed (IsLocalRing.closedPoint k)
  exact heval ▸ h (pointOfClosedPoint π y hyclosed)
    (pointOfClosedPoint_comp π y hyclosed) (heval.symm ▸ hys)

/-- Constructible subsets of a locally finite-type scheme over an algebraically closed
field are equal exactly when they have the same rational points. -/
theorem _root_.Topology.IsConstructible.eq_iff_forall_rationalPoint
    {s t : Set Y} (hs : IsConstructible s) (π : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType π] (ht : IsConstructible t) :
    s = t ↔ ∀ (p : Spec (.of k) ⟶ Y), p ≫ π = 𝟙 _ →
      (p (IsLocalRing.closedPoint k) ∈ s ↔ p (IsLocalRing.closedPoint k) ∈ t) := by
  rw [Set.Subset.antisymm_iff, hs.subset_iff_forall_rationalPoint π ht,
    ht.subset_iff_forall_rationalPoint π hs]
  exact ⟨fun h p hp ↦ ⟨h.1 p hp, h.2 p hp⟩,
    fun h ↦ ⟨fun p hp ↦ (h p hp).mp, fun p hp ↦ (h p hp).mpr⟩⟩

section FiniteType

variable (f : X ⟶ Y) (π : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType π] [LocallyOfFiniteType (f ≫ π)]

/-- Over an algebraically closed field `k`, the image of a morphism `f` from a locally finite-type
scheme is contained in the image of a morphism `g` from a finite-type scheme, both into a locally
finite-type scheme, exactly when every rational point that lifts along `f` lifts along `g`. -/
theorem range_subset_range_iff_forall_rationalPoint (g : Z ⟶ Y)
    [LocallyOfFiniteType (g ≫ π)] [CompactSpace Z] :
    Set.range f ⊆ Set.range g ↔
      ∀ (p : Spec (.of k) ⟶ Y), p ≫ π = 𝟙 _ →
        (∃ q : Spec (.of k) ⟶ X, q ≫ f = p) →
          ∃ r : Spec (.of k) ⟶ Z, r ≫ g = p := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g π
  have hg : IsConstructible (Set.range g) := by
    simpa using (g.isLocallyConstructible_image (s := Set.univ)
      IsLocallyConstructible.univ).isConstructible_of_subset_of_isCompact subset_rfl
        (isCompact_univ.image g.continuous)
  -- The inclusion is tested on the rational points of `X`, through the constructible preimage of
  -- the image of `g`; no compactness of `X` is needed for that preimage to be constructible.
  rw [← Set.image_univ, Set.image_subset_iff,
    IsConstructible.univ.subset_iff_forall_rationalPoint (f ≫ π) (f.isConstructible_preimage hg)]
  refine ⟨fun h p hp ⟨q, hq⟩ ↦ ?_, fun h q hq _ ↦ ?_⟩
  · subst hq
    obtain ⟨z, hz⟩ := h q (by rwa [Category.assoc] at hp) trivial
    exact (g.exists_comp_eq_iff_mem_range (q ≫ f)).mpr ⟨z, hz.trans (q.comp_apply f _).symm⟩
  · obtain ⟨r, hr⟩ := h (q ≫ f) (by rwa [Category.assoc]) ⟨q, rfl⟩
    obtain ⟨z, hz⟩ := (g.exists_comp_eq_iff_mem_range (q ≫ f)).mp ⟨r, hr⟩
    exact ⟨z, hz.trans (q.comp_apply f _)⟩

/-- A morphism from a finite-type scheme to a locally finite-type scheme over an algebraically
closed field is surjective on all scheme points exactly when every rational point has a rational
lift. -/
theorem surjective_iff_forall_rationalPoint [CompactSpace X] :
    Function.Surjective f ↔ ∀ (p : Spec (.of k) ⟶ Y), p ≫ π = 𝟙 _ →
      ∃ q : Spec (.of k) ⟶ X, q ≫ f = p := by
  constructor
  · intro hf p _
    let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f π
    exact (f.exists_comp_eq_iff_mem_range p).mpr (hf _)
  · intro h y
    exact ((𝟙 Y : Y ⟶ Y).range_subset_range_iff_forall_rationalPoint π f).mpr
      (fun p hp _ ↦ h p hp) ⟨y, rfl⟩

end FiniteType

end AlgebraicGeometry.Scheme.Hom
