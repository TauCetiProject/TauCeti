/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Abelian
-- Non-public: Fitting's lemma for finite-dimensional endomorphism algebras is used only in a proof.
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# The quiver of irreducible morphisms of a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`. This file specializes
`TauCeti.IrreducibleMorphismQuiver` to the finitely generated `A`-modules,
`IrreducibleMorphismQuiver k fun M : ModuleCat A ↦ Module.Finite A M`. Its vertices are the
isomorphism classes of finitely generated indecomposable `A`-modules, and its arrows index a
`k`-basis of `rad / rad²` between representatives. For `A = kQ/I` over an algebraically closed
field this is the underlying quiver of the Auslander–Reiten quiver of `A`; over other fields the
arrows count dimensions over `k`, not the valuations over the residue division rings.

The instances here make the general API apply without further hypotheses:

* the morphism spaces between representatives are finite-dimensional
  (`ModuleCat.finiteDimensional_hom_of_finite`), so every arrow set is finite;
* representatives have local endomorphism rings
  (`TauCeti.isLocalRing_end_of_indecomposable`, Fitting's lemma for the finite-dimensional
  endomorphism algebra), so
  `TauCeti.IrreducibleMorphismQuiver.nonempty_arrows_of_iff` and
  `TauCeti.exists_isIrreducibleMorphism_irreducibleMorphismMk_eq` apply to them.

No algebraic closedness is assumed.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.4.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), VII.1.
-/

public section

namespace TauCeti.IrreducibleMorphismQuiver

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (a : IrreducibleMorphismQuiver k fun M : ModuleCat.{w} A ↦ Module.Finite A M)

instance : Module.Finite A a.representative :=
  a.representative_property.1

instance : IsLocalRing (End a.representative) :=
  isLocalRing_end_of_indecomposable (k := k) a.representative_property.2

end TauCeti.IrreducibleMorphismQuiver
