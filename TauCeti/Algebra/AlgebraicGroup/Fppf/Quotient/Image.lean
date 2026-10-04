/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.FaithfullyFlat

/-!
# Scheme-theoretic images as fppf quotients

The scheme-theoretic image of a homomorphism from a geometrically reduced finite-type affine
group is the fppf quotient of that group by its kernel. This holds over any field; the ambient
target can be nonreduced. For finite-type affine groups, geometric reducedness is equivalent
to smoothness. The kernel itself may be nonreduced, as with inseparable homomorphisms.

The image factorization has the original scheme-theoretic kernel, so the quotient is by the
original subgroup, including its possibly nonreduced scheme structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a--c and Proposition 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§14--16.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.FiniteType k K]

/-- The scheme-theoretic image of a homomorphism from a geometrically reduced finite-type
affine group is represented by the fppf quotient by its kernel. The image factor's kernel
is the original kernel, by `kernelHopfIdeal_imageι`. -/
theorem isIso_kernelFppfQuotientHom_imageι [Algebra.IsGeometricallyReduced k K]
    (f : H ⟶ K) : IsIso (kernelFppfQuotientHom (imageι f)) := by
  have : IsNoetherianRing (image f) := Algebra.FiniteType.isNoetherianRing k (image f)
  exact isIso_kernelFppfQuotientHom (imageι f) (faithfullyFlat_imageι f)
    (RingHom.FinitePresentation.of_finiteType.mp (imageι_finiteType f))

end TauCeti.CommHopfAlgCat
