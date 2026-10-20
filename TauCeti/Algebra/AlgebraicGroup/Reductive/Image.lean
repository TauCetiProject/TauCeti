/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility

/-!
# Reductivity of quotient images in characteristic zero

The target of a schematically dominant homomorphism from a reductive finite-type affine
group over a characteristic-zero field is reductive. Coordinate arrows reverse direction:
an injective morphism `O(Q) → O(G)` carries reductivity from `G` to `Q`. In particular, this
applies to affine quotient projections and to isogenies, without any condition on the kernel.

The proof uses the characteristic-zero equivalence between reductivity and linear
reductivity from `Reductive.CompleteReducibility`. Linear reductivity and geometric
connectedness descend along the injective coordinate map; Cartier's theorem supplies
smoothness. This argument does not establish quotient-image reductivity in positive
characteristic, where reductivity does not imply linear reductivity.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §§13 and 19.
-/

public section

open CategoryTheory

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The target of a schematically dominant homomorphism from a reductive affine group
in characteristic zero is reductive. The coordinate morphism points from `Q` to `G`;
neither finiteness nor centrality of the kernel is required. -/
theorem of_injective (hG : reductiveCommHopfAlgProperty k G)
    (f : Q.obj ⟶ G.obj) (hf : Function.Injective f.hom) :
    reductiveCommHopfAlgProperty k Q := by
  apply (reductiveCommHopfAlgProperty_iff_linearlyReductive Q
    (geometricallyConnectedCommHopfAlgProperty.of_injective
      f.hom.toAlgHom hf hG.geometricallyConnected)).mpr
  exact hG.linearlyReductive.of_injective f hf

end TauCeti.reductiveCommHopfAlgProperty
