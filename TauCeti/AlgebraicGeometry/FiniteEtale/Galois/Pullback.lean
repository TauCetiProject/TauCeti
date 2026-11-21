/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Base change of finite étale schemes to a nonempty scheme over a connected base

Let `f : T ⟶ S` be a morphism of schemes with `S` connected and `T` nonempty. Base change of
finite étale schemes along `f` is then faithful and reflects isomorphisms. Indeed, for a
geometric point `x` of `T`, base change along `f` followed by the geometric fibre at `x` is the
geometric fibre at `x ≫ f` (`TauCeti.FiniteEtaleScheme.pullbackCompFiberIso`), which is a fibre
functor of the Galois category of finite étale `S`-schemes, hence faithful and conservative.

Neither hypothesis can be dropped. If `T` is empty and `S` is not, base change identifies the
two morphisms `S ⊔ S ⟶ S ⊔ S` over `S` that fold both summands onto the first, respectively the
second, summand. If `S` is the disjoint union of two points and `T` is one of them, base change
identifies the identity of `S ⊔ S` with the automorphism that swaps the two summands over the
other point.

The morphism `f` need not be dominant, in contrast with
`TauCeti.FiniteEtaleScheme.faithful_pullback`. The main example is a closed immersion into a
connected scheme, such as the inclusion of the punctured spectrum of a hypersurface section into
a connected punctured spectrum.

## Main results

* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_preconnectedSpace`: base change to a nonempty
  scheme over a connected base is faithful.
* `TauCeti.FiniteEtaleScheme.reflectsIsomorphisms_pullback_of_preconnectedSpace`: base change to a
  nonempty scheme over a connected base reflects isomorphisms.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §4.
* H. W. Lenstra, *Galois theory for schemes*, Section 3.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}} (f : T ⟶ S) [PreconnectedSpace S] [Nonempty T]

/-- Base change of finite étale schemes to a nonempty scheme over a connected base is
faithful. -/
instance faithful_pullback_of_preconnectedSpace : (pullback f).Faithful := by
  obtain ⟨t⟩ := ‹Nonempty T›
  exact Functor.Faithful.of_comp_iso (pullbackCompFiberIso f (T.fromSpecAlgebraicClosure t))

/-- Base change of finite étale schemes to a nonempty scheme over a connected base reflects
isomorphisms. -/
instance reflectsIsomorphisms_pullback_of_preconnectedSpace :
    (pullback f).ReflectsIsomorphisms := by
  obtain ⟨t⟩ := ‹Nonempty T›
  have := reflectsIsomorphisms_of_iso (pullbackCompFiberIso f (T.fromSpecAlgebraicClosure t)).symm
  exact reflectsIsomorphisms_of_comp (pullback f) (fiber (T.fromSpecAlgebraicClosure t))

end TauCeti.FiniteEtaleScheme
