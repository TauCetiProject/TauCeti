/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Étale paths and connected components

An étale path between geometric points `x : Spec Ω ⟶ S` and `y : Spec Ω' ⟶ S` of a scheme `S`
is an isomorphism `FiniteEtaleScheme.fiber x ≅ FiniteEtaleScheme.fiber y` of geometric fibre
functors. Over a connected base any two geometric points are joined by an étale path
(`TauCeti.FiniteEtaleScheme.nonempty_fiber_iso`). This file treats disconnected bases.

An open and closed subset `U` of `S` is a finite étale `S`-scheme, whose geometric fibre at `x` is
a point if `x` lies in `U` and is empty otherwise. Hence no étale path joins a point of `U` to a
point outside `U`. Conversely, if `x` and `y` both factor through a connected `S`-scheme `T`, an
étale path in `T` is carried to an étale path in `S` by base change along `T ⟶ S`. Applying this to
the connected component of `x` when it is open shows that geometric points of the same connected
component are joined by an étale path.

## Main results

* `TauCeti.FiniteEtaleScheme.isEmpty_fiber_iso_of_isClopen`: geometric points separated by an open
  and closed subset of the base are not joined by an étale path.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_of_mem_connectedComponent`: geometric points of the
  same connected component are joined by an étale path when that component is open.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_iff_mem_connectedComponent`: if the base is locally
  connected, for instance locally Noetherian, two geometric points are joined by an étale path if
  and only if they lie in the same connected component.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§5–7.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- Let `U` be an open subscheme of the base whose inclusion is finite, that is, `U` is also
closed. The geometric fibre at `x` of `U`, as a finite étale `S`-scheme, is nonempty exactly when
`x` lies in `U`. -/
theorem nonempty_fiber_obj_ofHom_ι_iff (U : S.Opens) [IsFinite U.ι] (x : Spec (.of Ω) ⟶ S) :
    Nonempty ((fiber x).obj (ofHom U.ι)) ↔ x default ∈ U := by
  rw [nonempty_fiber_obj_iff_range_subset_range, Set.range_unique, Set.singleton_subset_iff,
    ofHom_obj]
  -- The structure morphism `(Over.mk U.ι).hom` is `U.ι` (`Over.mk_hom`), but its codomain is
  -- written differently, so `rw` cannot replace it under the coercion to functions.
  exact Iff.of_eq (congrArg (x default ∈ ·) (Scheme.Opens.range_ι U))

/-- Geometric points `x` and `y` separated by an open and closed subset `U` of the base are not
joined by an étale path: the geometric fibres of `U`, as a finite étale `S`-scheme, are a point at
`x` and empty at `y`. -/
theorem isEmpty_fiber_iso_of_isClopen {U : Set S} (hU : IsClopen U) {x : Spec (.of Ω) ⟶ S}
    {y : Spec (.of Ω') ⟶ S} (hx : x default ∈ U) (hy : y default ∉ U) :
    IsEmpty (fiber x ≅ fiber y) := by
  refine ⟨fun e ↦ hy ?_⟩
  let V : S.Opens := ⟨U, hU.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by simpa [V] using hU.isClosed)
  obtain ⟨a⟩ := (nonempty_fiber_obj_ofHom_ι_iff V x).mpr hx
  exact (nonempty_fiber_obj_ofHom_ι_iff V y).mp ⟨e.hom.app _ a⟩

/-- Geometric points that factor through a connected `S`-scheme `T` are joined by an étale path:
base change along `T ⟶ S` carries an étale path in `T` to one in `S`. -/
theorem nonempty_fiber_comp_iso {T : Scheme.{u}} [ConnectedSpace T] (f : T ⟶ S)
    (x : Spec (.of Ω) ⟶ T) (y : Spec (.of Ω') ⟶ T) : Nonempty (fiber (x ≫ f) ≅ fiber (y ≫ f)) :=
  (nonempty_fiber_iso x y).map fun e ↦
    (pullbackCompFiberIso f x).symm ≪≫ Functor.isoWhiskerLeft (pullback f) e ≪≫
      pullbackCompFiberIso f y

/-- Geometric points `x` and `y` of the same connected component of the base are joined by an
étale path, provided that component is open: both factor through the connected component, as an
open subscheme. -/
theorem nonempty_fiber_iso_of_mem_connectedComponent {x : Spec (.of Ω) ⟶ S}
    {y : Spec (.of Ω') ⟶ S} (hC : IsOpen (connectedComponent (x default)))
    (hy : y default ∈ connectedComponent (x default)) : Nonempty (fiber x ≅ fiber y) := by
  let C : S.Opens := ⟨_, hC⟩
  have : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hrange {Ω'' : Type u} [Field Ω''] (z : Spec (.of Ω'') ⟶ S) (hz : z default ∈ C) :
      Set.range z ⊆ Set.range C.ι := by
    rwa [Set.range_unique, Set.singleton_subset_iff, Scheme.Opens.range_ι]
  have := nonempty_fiber_comp_iso C.ι
    (IsOpenImmersion.lift C.ι x (hrange x mem_connectedComponent))
    (IsOpenImmersion.lift C.ι y (hrange y hy))
  rwa [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac] at this

/-- Over a locally connected base, for instance a locally Noetherian one, two geometric points are
joined by an étale path if and only if they lie in the same connected component. In particular,
geometric points of different connected components admit no étale path. -/
theorem nonempty_fiber_iso_iff_mem_connectedComponent [LocallyConnectedSpace S]
    {x : Spec (.of Ω) ⟶ S} {y : Spec (.of Ω') ⟶ S} :
    Nonempty (fiber x ≅ fiber y) ↔ y default ∈ connectedComponent (x default) :=
  ⟨fun ⟨e⟩ ↦ by_contra fun hy ↦
      (isEmpty_fiber_iso_of_isClopen isClopen_connectedComponent mem_connectedComponent hy).false e,
    nonempty_fiber_iso_of_mem_connectedComponent isOpen_connectedComponent⟩

end TauCeti.FiniteEtaleScheme
