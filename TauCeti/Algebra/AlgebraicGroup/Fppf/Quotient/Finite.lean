/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.GeometricallyReduced

/-!
# Fppf quotients by kernels of finite dominant homomorphisms

A finite dominant homomorphism to a geometrically reduced finite-type affine group over
any field presents the target as the fppf quotient by its scheme-theoretic kernel. Neither
flatness nor reducedness of the source is assumed. In particular, inseparable maps and
nonreduced kernels are allowed.

The comparison is the existing `kernelFppfQuotientHom`; its invertibility follows from the
finite dominant isogeny criterion and the fppf first isomorphism theorem. Finiteness over
the noetherian target coordinate algebra supplies finite presentation.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §15.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]

/-- A finite dominant homomorphism to a geometrically reduced finite-type affine group
presents its target as the fppf quotient by its kernel, over an arbitrary field. -/
theorem isIso_kernelFppfQuotientHom_of_finite_of_dominant (f : H ⟶ K)
    (hfin : f.hom.toAlgHom.Finite)
    (hdom : DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom)) :
    IsIso (kernelFppfQuotientHom f) := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  exact isIso_kernelFppfQuotientHom f
    ((isIsogeny_iff_finite_and_dominant f).mpr ⟨hfin, hdom⟩).faithfullyFlat
    (RingHom.FinitePresentation.of_finiteType.mp hfin.finiteType)

end TauCeti.CommHopfAlgCat
