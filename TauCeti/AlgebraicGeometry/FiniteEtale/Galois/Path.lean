/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.CategoryTheory.Aut.Torsor

/-!
# Étale fundamental groups and étale paths

Let `S` be a scheme and `x : Spec Ω ⟶ S` a geometric point, with `Ω` separably closed. The étale
fundamental group `π₁(S, x)` (`TauCeti.FiniteEtaleScheme.EtaleFundamentalGroup x`) is the group
`Aut (FiniteEtaleScheme.fiber x)` of automorphisms of the geometric fibre functor at `x` on finite
étale `S`-schemes. With the topology of pointwise convergence on the finite fibres it is a profinite
group: compact, Hausdorff and totally disconnected, by Mathlib's topology on automorphism groups of
functors to finite sets (`CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding`).

An étale path from `x` to a geometric point `y : Spec Ω' ⟶ S`
(`TauCeti.FiniteEtaleScheme.EtalePath x y`) is a natural isomorphism `fiber x ≅ fiber y` of
geometric fibre functors. Paths are not required to stay in a connected component, and no global
choice of base points is made, so the paths between all geometric points of `S` form a groupoid
whose identity, inverse and composition are those of natural isomorphisms (`Iso.refl`, `Iso.symm`,
`Iso.trans`).

The fundamental group `π₁(S, y)` acts on the paths from `x` to `y` by composition, and this
action is simply transitive (`CategoryTheory.Aut.existsUnique_smul_eq`, applied to paths). Over a
connected base any two geometric points are joined by a path
(the instance `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso`), so the paths from `x` to `y`
form a torsor under `π₁(S, y)` (`CategoryTheory.Aut.instTorsorIso`). Over a disconnected base,
paths exist exactly between geometric points of the same connected component when that component
is open
(`TauCeti.FiniteEtaleScheme.nonempty_fiber_iso_iff_mem_connectedComponent_of_isOpen`). A path
`γ` from `x` to `y` changes the base point by conjugation, `π₁(S, x) ≃ₜ* π₁(S, y)`
(`CategoryTheory.Iso.continuousConjAut`), and conjugation is compatible with the action on `γ`
(`CategoryTheory.Aut.conjAut_smul`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.EtaleFundamentalGroup x`: the étale fundamental group `π₁(S, x)`.
* `TauCeti.FiniteEtaleScheme.EtalePath x y`: étale paths from `x` to `y`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§5–7.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.6 (tag 0BND), *Fundamental groups of schemes*.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- The **étale fundamental group** `π₁(S, x)` of a scheme `S` at a geometric point
`x : Spec Ω ⟶ S`: the profinite group of automorphisms of the geometric fibre functor at `x` on
finite étale `S`-schemes. -/
abbrev EtaleFundamentalGroup (x : Spec (.of Ω) ⟶ S) :=
  Aut (fiber x)

/-- The **étale paths** from a geometric point `x` to a geometric point `y` of a scheme `S`: the
natural isomorphisms between their geometric fibre functors on finite étale `S`-schemes. -/
abbrev EtalePath (x : Spec (.of Ω) ⟶ S) (y : Spec (.of Ω') ⟶ S) :=
  fiber x ≅ fiber y

end TauCeti.FiniteEtaleScheme
