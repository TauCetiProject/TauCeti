/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.LocallyClosed

/-!
# Existence of closed orbits

Let a group scheme `G` of finite type over an algebraically closed field `k` act on a scheme `X`
of finite type over `k`. The geometric orbit `O_x` of a rational point `x` of `X` is locally
closed, and its boundary `Z_x \ O_x` in the orbit closure `Z_x` is closed, stable under
translation by the rational points of `G`, and of strictly smaller dimension than `O_x`
(`TauCeti.SchemeAction.topologicalKrullDim_orbitBoundary_lt`).

A closed subset of `X` stable under rational translations contains the whole geometric orbit of
a rational point as soon as it contains that point: the closed points of the orbit are its
rational translates, and they are dense in the locally closed orbit. Hence the orbit of a
rational point `y` of the boundary of `O_x` lies in that boundary, and has strictly smaller
dimension than `O_x`. Since a nonempty closed subset of `X` contains a rational point, an orbit
whose dimension is minimal among the orbits of the rational points of its closure has empty
boundary, that is, it is closed. By induction on the dimension, every orbit closure contains a
closed orbit; in particular every nonempty closed subset of `X` stable under rational
translations, and every nonempty `X`, contains one.

No smoothness, reducedness, connectedness or separatedness hypothesis is needed, and `X` need not
be irreducible. The orbits are the full topological images of the orbit morphisms, including
their nonclosed points. The closed orbit produced is not claimed to be unique.

## Main declarations

* `TauCeti.SchemeAction.orbit_subset_iff_of_isClosed`: a closed translation-stable subset contains
  the orbit of a rational point exactly when it contains the point.
* `TauCeti.SchemeAction.orbitClosure_subset_iff_of_isClosed`: the same criterion for the orbit
  closure.
* `TauCeti.SchemeAction.orbitClosure_subset_orbitBoundary`: the orbit closure of a rational point
  of the boundary of `O_x` lies in that boundary.
* `TauCeti.SchemeAction.exists_rationalPoint_mem_orbitBoundary_of_not_isClosed`: a nonclosed
  orbit has a rational point in its boundary.
* `TauCeti.SchemeAction.isClosed_orbit_of_forall_mem_orbitClosure`: an orbit of minimal dimension
  is closed.
* `TauCeti.SchemeAction.exists_isClosed_orbit_subset_orbitClosure`: every orbit closure contains a
  closed orbit.
* `TauCeti.SchemeAction.exists_isClosed_orbit`: a nonempty `X` has a closed orbit.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8, the closed orbit lemma.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  Topology

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

variable (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
  [CompactSpace X.left]

/-- A closed subset of `X` stable under translation by the rational points of `G` contains the
geometric orbit of a rational point `y`, including its nonclosed points, exactly when it contains
`y`. -/
theorem orbit_subset_iff_of_isClosed {Z : Set X.left} (hZ : IsClosed Z)
    (hinv : ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.MapsTo (translation X g).hom.left Z Z)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (a : (𝟙_ (Over (Spec (.of k)))).left) :
    orbit G y ⊆ Z ↔ y.left a ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  refine ⟨fun h ↦ h ((left_apply_mem_orbit_iff G y y a).mpr ⟨1, one_smul _ _⟩), fun hy ↦ ?_⟩
  -- The closed points of the locally closed orbit are dense in it, and they are the rational
  -- translates of `y`.
  refine subset_closure.trans ?_
  rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure (isLocallyClosed_orbit G y),
    hZ.closure_subset_iff, orbit_inter_closedPoints]
  refine Set.iUnion_subset fun g ↦ ?_
  rintro _ ⟨b, rfl⟩
  obtain rfl : b = a := Subsingleton.elim (α := Spec (.of k)) _ _
  let := translationMulAction G X
  rw [← translationMulAction_smul_apply, translationMulAction_smul]
  exact hinv g hy

/-- A closed subset of `X` stable under translation by the rational points of `G` contains the
orbit closure of a rational point `y` exactly when it contains `y`. -/
theorem orbitClosure_subset_iff_of_isClosed {Z : Set X.left} (hZ : IsClosed Z)
    (hinv : ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.MapsTo (translation X g).hom.left Z Z)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (a : (𝟙_ (Over (Spec (.of k)))).left) :
    orbitClosure G y ⊆ Z ↔ y.left a ∈ Z := by
  rw [orbitClosure_def, hZ.closure_subset_iff]
  exact orbit_subset_iff_of_isClosed G hZ hinv y a

/-- The orbit closure of a rational point `y` lies in the orbit closure of `x` exactly when `y`
does. -/
theorem orbitClosure_subset_orbitClosure_iff (x y : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (a : (𝟙_ (Over (Spec (.of k)))).left) :
    orbitClosure G y ⊆ orbitClosure G x ↔ y.left a ∈ orbitClosure G x :=
  orbitClosure_subset_iff_of_isClosed G (isClosed_orbitClosure G x)
    (fun g ↦ Set.mapsTo_iff_image_subset.mpr (image_translation_orbitClosure G g x).subset) y a

/-- The orbit closure of a rational point `y` of the boundary of the orbit of `x` lies in that
boundary. -/
theorem orbitClosure_subset_orbitBoundary {x y : 𝟙_ (Over (Spec (.of k))) ⟶ X}
    {a : (𝟙_ (Over (Spec (.of k)))).left} (hy : y.left a ∈ orbitBoundary G x) :
    orbitClosure G y ⊆ orbitBoundary G x :=
  (orbitClosure_subset_iff_of_isClosed G (isClosed_orbitBoundary G x)
    (fun g ↦ Set.mapsTo_iff_image_subset.mpr (image_translation_orbitBoundary G g x).subset)
    y a).mpr hy

/-- The orbit of a rational point `y` of the boundary of the orbit of `x` has strictly smaller
dimension than the orbit of `x`. -/
theorem topologicalKrullDim_orbit_lt_of_mem_orbitBoundary {x y : 𝟙_ (Over (Spec (.of k))) ⟶ X}
    {a : (𝟙_ (Over (Spec (.of k)))).left} (hy : y.left a ∈ orbitBoundary G x) :
    topologicalKrullDim (orbit G y) < topologicalKrullDim (orbit G x) :=
  lt_of_le_of_lt
    (IsEmbedding.inclusion ((orbit_subset_orbitClosure G y).trans
      (orbitClosure_subset_orbitBoundary G hy))).isInducing.topologicalKrullDim_le
    (topologicalKrullDim_orbitBoundary_lt G x)

/-- A nonclosed orbit has a rational point in its boundary. -/
theorem exists_rationalPoint_mem_orbitBoundary_of_not_isClosed (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (h : ¬ IsClosed (orbit G x)) :
    ∃ (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (a : (𝟙_ (Over (Spec (.of k)))).left),
      y.left a ∈ orbitBoundary G x := by
  obtain ⟨y, hyπ, hy⟩ := (isClosed_orbitBoundary G x).isLocallyClosed.exists_rationalPoint_mem
    X.hom (Set.nonempty_iff_ne_empty.mpr ((isClosed_orbit_iff_orbitBoundary_eq_empty G x).not.mp h))
  exact ⟨Over.homMk y hyπ, _, hy⟩

/-- **Closed-orbit lemma.** If the orbit of `x` has minimal dimension among the orbits of the
rational points of its closure, then it is closed. -/
theorem isClosed_orbit_of_forall_mem_orbitClosure (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (hmin : ∀ (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (a : (𝟙_ (Over (Spec (.of k)))).left),
      y.left a ∈ orbitClosure G x →
        topologicalKrullDim (orbit G x) ≤ topologicalKrullDim (orbit G y)) :
    IsClosed (orbit G x) := by
  by_contra hne
  obtain ⟨y, a, hy⟩ := exists_rationalPoint_mem_orbitBoundary_of_not_isClosed G x hne
  exact (hmin y a (orbitBoundary_subset_orbitClosure G x hy)).not_gt
    (topologicalKrullDim_orbit_lt_of_mem_orbitBoundary G hy)

/-- **Existence of closed orbits.** The closure of the orbit of every rational point contains the
closed orbit of a rational point. -/
theorem exists_isClosed_orbit_subset_orbitClosure (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X, IsClosed (orbit G y) ∧ orbit G y ⊆ orbitClosure G x := by
  obtain ⟨d, hd⟩ : ∃ d, topologicalKrullDim (orbit G x) = d := ⟨_, rfl⟩
  -- Induction on the dimension of the orbit: a nonclosed orbit has a rational point in its
  -- boundary, and the orbit of that point is smaller and lies in the boundary.
  induction d using WellFoundedLT.induction generalizing x with
  | ind d ih =>
  by_cases hclosed : IsClosed (orbit G x)
  · exact ⟨x, hclosed, orbit_subset_orbitClosure G x⟩
  obtain ⟨y, a, hy⟩ := exists_rationalPoint_mem_orbitBoundary_of_not_isClosed G x hclosed
  obtain ⟨z, hz, hzy⟩ :=
    ih _ (hd ▸ topologicalKrullDim_orbit_lt_of_mem_orbitBoundary G hy) _ rfl
  exact ⟨z, hz, hzy.trans ((orbitClosure_subset_orbitBoundary G hy).trans
    (orbitBoundary_subset_orbitClosure G x))⟩

/-- Every nonempty closed subset of `X` stable under translation by the rational points of `G`
contains the closed orbit of a rational point. -/
theorem exists_isClosed_orbit_subset_of_isClosed {Z : Set X.left} (hZ : IsClosed Z)
    (hne : Z.Nonempty)
    (hinv : ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.MapsTo (translation X g).hom.left Z Z) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X, IsClosed (orbit G y) ∧ orbit G y ⊆ Z := by
  obtain ⟨x, hxπ, hx⟩ := hZ.isLocallyClosed.exists_rationalPoint_mem X.hom hne
  obtain ⟨y, hy, hyx⟩ := exists_isClosed_orbit_subset_orbitClosure G (Over.homMk x hxπ)
  exact ⟨y, hy, hyx.trans ((orbitClosure_subset_iff_of_isClosed G hZ hinv _ _).mpr hx)⟩

/-- **Existence of closed orbits.** A nonempty scheme of finite type over an algebraically closed
field, acted on by a group scheme of finite type, contains the closed orbit of a rational
point. -/
theorem exists_isClosed_orbit [Nonempty X.left] :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X, IsClosed (orbit G y) := by
  obtain ⟨y, hy, -⟩ := exists_isClosed_orbit_subset_of_isClosed G (X := X) isClosed_univ
    Set.univ_nonempty fun _ ↦ Set.mapsTo_univ _ _
  exact ⟨y, hy⟩

end TauCeti.SchemeAction
