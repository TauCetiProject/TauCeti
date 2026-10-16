/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic

/-!
# The subspace quiver

The subspace quiver on an index type `ι` has a central vertex and one outer vertex for each
`i : ι`, with a single arrow running from each outer vertex into the centre. A representation of
it whose arrows act injectively is a family of subspaces of the vector space at the centre, which
is where the name comes from.

Its underlying graph is the star with `|ι|` leaves. With three leaves this is the Dynkin diagram
`D₄`, and the quiver is the same as `TauCeti.Quiver.D4`; with four leaves it is the extended
Dynkin diagram `D4~`, the graph of the classical four subspace problem, and the quiver has
infinite representation type (`TauCeti.RepresentationTheory.Quiver.Subspace.FiniteRepType`).

This file carries the vertex and arrow data alone.

## Main definitions

* `TauCeti.Quiver.Subspace`: the vertex type, with constructors `center` and `outer`, and a
  `Quiver` instance whose only arrows are the `outer i ⟶ center`.
* `TauCeti.Quiver.Subspace.arrow`: the arrow from an outer vertex into the centre.

## References

* I. M. Gelfand, V. A. Ponomarev, *Problems of linear algebra and classification of quadruples of
  subspaces in a finite-dimensional vector space*, Colloq. Math. Soc. János Bolyai **5** (1972),
  163--237.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

namespace Quiver

universe v

/-- The subspace quiver on `ι`: a central vertex together with one outer vertex for each `i : ι`,
with one arrow from each outer vertex into the centre. -/
inductive Subspace (ι : Type v) : Type v
  | /-- The central vertex, the head of every arrow. -/ center : Subspace ι
  | /-- The outer vertex indexed by `i`, the tail of a single arrow. -/ outer (i : ι) : Subspace ι

namespace Subspace

variable {ι : Type v}

instance : _root_.Quiver.{1} (Subspace ι) where
  Hom a b :=
    match a, b with
    | .outer _, .center => PUnit
    | _, _ => PEmpty

/-- The arrow running from the outer vertex indexed by `i` into the centre. -/
def arrow (i : ι) : outer i ⟶ center := PUnit.unit

instance instUniqueHomOuterCenter (i : ι) : Unique (outer i ⟶ center) :=
  inferInstanceAs (Unique PUnit)

instance : IsEmpty ((center : Subspace ι) ⟶ center) := inferInstanceAs (IsEmpty PEmpty)

instance (i : ι) : IsEmpty (center ⟶ outer i) := inferInstanceAs (IsEmpty PEmpty)

instance (i j : ι) : IsEmpty (outer i ⟶ outer j) := inferInstanceAs (IsEmpty PEmpty)

/-- Between any two vertices of the subspace quiver there is at most one arrow. -/
instance instSubsingletonHom : ∀ a b : Subspace ι, Subsingleton (a ⟶ b)
  | .outer _, .center => inferInstance
  | .center, .center => inferInstance
  | .center, .outer _ => inferInstance
  | .outer _, .outer _ => inferInstance

end Subspace

end Quiver

end TauCeti
