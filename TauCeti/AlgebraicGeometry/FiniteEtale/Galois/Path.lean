/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Étale paths over a disconnected base

An étale path between two geometric points `x : Spec Ω ⟶ S` and `y : Spec Ω' ⟶ S` of a scheme
`S` is an isomorphism `fiber x ≅ fiber y` of their geometric fibre functors on finite étale
`S`-schemes. Paths compose, invert and include identities as isomorphisms of functors do, so the
geometric points of `S` form a groupoid with no global choice of base point; the automorphism
group of an object of this groupoid is the étale fundamental group. When `S` is connected any two
geometric points are joined by a path (`TauCeti.FiniteEtaleScheme.nonempty_fiber_iso`). This file
describes which geometric points are joined by a path when `S` is not connected.

* Geometric points that factor through a connected scheme over `S` are joined by a path, the
  base change of a path upstairs (`TauCeti.FiniteEtaleScheme.nonempty_fiber_comp_iso`).
* An open and closed subset `U` of `S` is a finite étale `S`-scheme whose geometric fibre at `x`
  is nonempty exactly when `x` lands in `U`. So a path cannot leave `U`: geometric points joined
  by a path lie on the same side of every open and closed subset
  (`TauCeti.FiniteEtaleScheme.range_subset_iff_of_fiber_iso`).
* Geometric points landing in a common connected open subset, such as a connected component which
  is open, are joined by a path, since that subset is a connected open subscheme
  (`TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_of_range_subset`).

When `S` is locally connected, for instance locally Noetherian
(`TauCeti.AlgebraicGeometry.locallyConnectedSpace_of_isLocallyNoetherian`), connected components
are open and closed, and these combine to the statement that two geometric points are joined by
an étale path if and only if they lie in the same connected component of `S`
(`TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_iff`). In particular geometric points in different
connected components of a locally Noetherian scheme admit no étale path. The spectrum of a field
has a single point, so each geometric point `x` has a single image point `x p`.

## Main results

* `TauCeti.FiniteEtaleScheme.nonempty_fiber_comp_iso`: geometric points factoring through a
  connected `S`-scheme are joined by an étale path.
* `TauCeti.FiniteEtaleScheme.range_subset_iff_of_fiber_iso`: geometric points joined by an étale
  path lie on the same side of every open and closed subset.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_of_range_subset`: geometric points in a common
  connected open subset are joined by an étale path.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_iff`: over a locally connected scheme, two
  geometric points are joined by an étale path if and only if they lie in the same connected
  component.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§5–7.
* The Stacks Project, Section 58.6 (tag 0BND), *Fundamental groups of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- **Paths through a connected scheme.** Geometric points of `S` that factor through a morphism
`f : T ⟶ S` from a connected scheme are joined by an étale path: base change along `f` carries a
path between their lifts to `T` to a path between them. -/
theorem nonempty_fiber_comp_iso [ConnectedSpace T] (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T)
    (y : Spec (.of Ω') ⟶ T) : Nonempty (fiber (x ≫ f) ≅ fiber (y ≫ f)) :=
  (nonempty_fiber_iso x y).map fun e ↦
    (pullbackCompFiberIso f x).symm ≪≫ Functor.isoWhiskerLeft (pullback f) e ≪≫
      pullbackCompFiberIso f y

/-- A geometric point lands in an open subscheme `U` of `S` which is closed if and only if the
geometric fibre at it of `U`, as a finite étale `S`-scheme, is nonempty. -/
private theorem range_subset_iff_nonempty_fiber_obj (x : Spec (.of Ω) ⟶ S) (U : S.Opens)
    [IsClosedImmersion U.ι] : Set.range x ⊆ U ↔ Nonempty ((fiber x).obj (ofHom U.ι)) := by
  -- The structure morphism changes type along `ofHom_obj`, so transport its range instead.
  have h : Set.range (Over.mk U.ι).hom = U := Scheme.Opens.range_ι U
  rw [nonempty_fiber_obj_iff_range_subset_range,
    congrArg (fun Z : Over S ↦ Set.range Z.hom) (ofHom_obj U.ι), h]

/-- **Paths stay in open and closed subsets.** Geometric points joined by an étale path lie on
the same side of every open and closed subset `U` of `S`: the finite étale `S`-scheme `U` has
nonempty geometric fibre exactly at the geometric points landing in `U`. -/
theorem range_subset_iff_of_fiber_iso {x : Spec (.of Ω) ⟶ S} {y : Spec (.of Ω') ⟶ S}
    (e : fiber x ≅ fiber y) {U : Set S} (hU : IsClopen U) :
    Set.range x ⊆ U ↔ Set.range y ⊆ U := by
  obtain ⟨V, rfl⟩ : ∃ V : S.Opens, (V : Set S) = U := ⟨⟨U, hU.isOpen⟩, rfl⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU.1)
  rw [range_subset_iff_nonempty_fiber_obj x V, range_subset_iff_nonempty_fiber_obj y V]
  exact (FintypeCat.equivEquivIso.symm (e.app _)).nonempty_congr

/-- **Paths within a connected open subset.** Geometric points landing in a common open and
preconnected subset `V` of `S`, such as a connected component of `S` which is open, are joined by an
étale path, through `V` as a connected open subscheme. -/
theorem nonempty_fiber_iso_of_range_subset {V : Set S} (hV : IsOpen V)
    (hVc : _root_.IsPreconnected V) {x : Spec (.of Ω) ⟶ S} {y : Spec (.of Ω') ⟶ S}
    (hx : Set.range x ⊆ V) (hy : Set.range y ⊆ V) : Nonempty (fiber x ≅ fiber y) := by
  let U : S.Opens := ⟨V, hV⟩
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp ⟨⟨x p, hx ⟨p, rfl⟩⟩, hVc⟩
  have hx' : Set.range x ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have hy' : Set.range y ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have := nonempty_fiber_comp_iso U.ι (IsOpenImmersion.lift U.ι x hx')
    (IsOpenImmersion.lift U.ι y hy')
  rwa [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac] at this

/-- **Étale paths over a locally connected scheme.** When `S` is locally connected, for instance
locally Noetherian, two geometric points `x` and `y` of `S` are joined by an étale path if and
only if their image points `x p` and `y q` lie in the same connected component of `S`. -/
theorem nonempty_fiber_iso_iff [LocallyConnectedSpace S] {x : Spec (.of Ω) ⟶ S}
    {y : Spec (.of Ω') ⟶ S} (p : Spec (.of Ω)) (q : Spec (.of Ω')) :
    Nonempty (fiber x ≅ fiber y) ↔ connectedComponent (x p) = connectedComponent (y q) := by
  -- The spectrum of a field is a single point, so `x` lands in a set exactly when `x p` does.
  have hrange {K : Type u} [Field K] (z : Spec (.of K) ⟶ S) (r : Spec (.of K)) {V : Set S} :
      Set.range z ⊆ V ↔ z r ∈ V := by
    rw [Set.range_subset_iff]
    exact ⟨fun h ↦ h r, fun h r' ↦ Subsingleton.elim r r' ▸ h⟩
  refine ⟨fun ⟨e⟩ ↦ connectedComponent_eq ?_, fun h ↦ ?_⟩
  · rw [← hrange y q, ← range_subset_iff_of_fiber_iso e isClopen_connectedComponent, hrange x p]
    exact mem_connectedComponent
  · refine nonempty_fiber_iso_of_range_subset isOpen_connectedComponent
      isPreconnected_connectedComponent ((hrange x p).mpr mem_connectedComponent)
      ((hrange y q).mpr ?_)
    exact h ▸ mem_connectedComponent

end TauCeti.FiniteEtaleScheme
