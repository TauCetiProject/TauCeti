/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.Matrix.Spanning
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Irreducibility of the reductions of a spanning matrix representation

If the image of a monoid homomorphism `u : M →* M_n(R)` spans the matrix algebra `M_n(R)`, then
for every ring homomorphism `f : R →+* k` to a field the representation `g ↦ (u g).map f` of `M`
on `kⁿ` is irreducible, for `n` nonempty: its image spans `M_n(k)`
(`Matrix.span_range_map_eq_top`), and a monoid acting through a spanning image acts irreducibly
(`AlgHom.isIrreducible_toMonoidHom_comp_of_span_eq_top`). Since spanning survives every extension
of `k`, the reduction is even absolutely irreducible. For `R` local and `f` the residue map this
is the absolute irreducibility of the residual representation.

## Main results

* `MonoidHom.isIrreducible_map_of_span_range_eq_top`: a spanning `u : M →* M_n(R)` has
  irreducible reductions along every ring homomorphism to a field.

## Provenance

Adapted from `New.Selmer.eq_bot_or_eq_top_of_span_eq_top` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Module Submodule

namespace MonoidHom

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **A spanning image has absolutely irreducible reductions.** If the image of a monoid
homomorphism `u : M →* M_n(R)` spans `M_n(R)`, then for every ring homomorphism `f : R →+* k` to a
field and `n` nonempty, the representation `g ↦ (u g).map f` of `M` on `kⁿ` is irreducible: its
image spans `M_n(k)` (`Matrix.span_range_map_eq_top`), so it stays irreducible after any extension
of `k`. For `R` local and `f` the residue map this is the absolute irreducibility of the residual
representation. -/
theorem isIrreducible_map_of_span_range_eq_top {M k : Type*} [Monoid M] [Field k] [Nonempty n]
    (u : M →* Matrix n n R) (hu : span R (Set.range u) = ⊤) (f : R →+* k) :
    Representation.IsIrreducible
      (((Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom : Matrix n n k →* End k (n → k)).comp
        ((f.mapMatrix (m := n)).toMonoidHom.comp u)) :=
  Matrix.toLinAlgEquiv'.toAlgHom.isIrreducible_toMonoidHom_comp_of_span_eq_top
    Matrix.toLinAlgEquiv'.surjective ((f.mapMatrix (m := n)).toMonoidHom.comp u)
    (Matrix.span_range_map_eq_top f hu)


end MonoidHom
