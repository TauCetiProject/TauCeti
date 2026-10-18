/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Lie
public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility

/-!
# Semisimple affine groups are linearly reductive in characteristic zero

Every finite-dimensional rational representation of a semisimple affine group over a field
of characteristic zero is completely reducible. The ground field need not be algebraically
closed, and the group need not split.

The Lie-algebra comparison is in `Semisimple.Lie`. Linear reductivity supplies complete
reducibility for rational representations of semisimple groups over the original field.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.linearlyReductive`: semisimple affine groups in
  characteristic zero are linearly reductive.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 22.
* `Semisimple.Lie`: semisimplicity of the tangent Lie algebra.
* `Representation.CompleteReducibility`: the comodule form of Weyl's theorem.
-/

public section

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Semisimple affine groups are linearly reductive in characteristic zero.** Every
finite-dimensional rational representation is completely reducible, without a splitting or
algebraic-closedness assumption on the field. -/
theorem linearlyReductive (hH : semisimpleCommHopfAlgProperty k H) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let _ := hH.isKilling_lieAlgebra
  exact linearlyReductiveCommHopfAlgProperty.of_geometricallyConnected_of_isKilling
    hH.geometricallyConnected

end TauCeti.semisimpleCommHopfAlgProperty
