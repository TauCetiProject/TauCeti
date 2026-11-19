/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Etale.Reduced

/-!
# Étale kernels of isogenies in characteristic zero

Over a field of characteristic zero, the scheme-theoretic kernel of an affine isogeny is étale:
it is finite over the base field, and reduced by Cartier's theorem. Neither group needs to be of
finite type.

## Main declarations

* `TauCeti.CommHopfAlgCat.IsIsogeny.algebraEtale_quotient_kernelHopfIdeal_of_charZero`: in
  characteristic zero the kernel of an isogeny is étale.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 3 (Cartier's theorem).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.

The proof combines `moduleFinite_quotient_kernelHopfIdeal`, `HopfAlgebra.isReduced_of_charZero`
and `algebraEtale_iff_finite_and_isReduced`.
-/

public section

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u v

variable {k : Type u} [Field k] [CharZero k] {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K}

/-- In characteristic zero the scheme-theoretic kernel of an isogeny is étale. Neither group needs
to be of finite type. -/
theorem algebraEtale_quotient_kernelHopfIdeal_of_charZero (hf : IsIsogeny f) :
    Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal) :=
  let _ := moduleFinite_quotient_kernelHopfIdeal hf.finite
  algebraEtale_iff_finite_and_isReduced.2
    ⟨‹_›, HopfAlgebra.isReduced_of_charZero k (K ⧸ (kernelHopfIdeal f).toIdeal)⟩

end TauCeti.CommHopfAlgCat.IsIsogeny
