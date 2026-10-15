/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat

/-!
# Faithful flatness of the morphism onto an affine group image

For a homomorphism of finite-type affine groups with geometrically reduced source over a field,
the morphism from the source to its scheme-theoretic image is faithfully flat. In coordinates,
the injective factor `imageι f : H / ker f ⟶ K` is faithfully flat. The ambient target may be
nonreduced, the field may be imperfect, and the homomorphism need not be finite.

This supplies the flatness needed to identify the image with the fppf quotient by the kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a and Proposition 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§14--16.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.FiniteType k K]
  [Algebra.IsGeometricallyReduced k K]

/-- The homomorphism from a geometrically reduced finite-type affine group onto its
scheme-theoretic image is faithfully flat, over any field. -/
theorem faithfullyFlat_imageι (f : H ⟶ K) :
    (imageι f).hom.toAlgHom.toRingHom.FaithfullyFlat := by
  have : Algebra.IsGeometricallyReduced k (image f) :=
    Algebra.IsGeometricallyReduced.of_injective (imageι f).hom.toAlgHom (imageι_injective f)
  exact (faithfullyFlat_iff_injective_of_isGeometricallyReduced (imageι f)).mpr
    (imageι_injective f)

end TauCeti.CommHopfAlgCat
