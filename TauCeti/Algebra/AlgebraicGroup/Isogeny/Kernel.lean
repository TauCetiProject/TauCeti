/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Kernels of isogenies

The kernel of an isogeny of affine group schemes is finite and faithfully flat over the base.
The kernel square is a pullback of the isogeny along the identity section, so each of
finiteness, flatness, and surjectivity is inherited by the structural morphism of the kernel:
the represented kernel is itself an isogeny over the base.

Over a field, the kernel of a central isogeny is therefore a finite locally free bicommutative
Hopf algebra, the shape required by Cartier duality.

## Main declarations

* `TauCeti.CommHopfAlgCat.IsIsogeny.isIsogeny_kernelSpec_to_trivial`: the structural
  morphism from the represented kernel to the trivial group scheme is an isogeny.
* `TauCeti.CommHopfAlgCat.IsCentralIsogeny.kernelFiniteLocallyFree`: over a field, the
  kernel of a central isogeny as a finite locally free bicommutative Hopf algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 4.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.21.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

namespace IsIsogeny

variable {H K : _root_.CommHopfAlgCat.{u} R} {f : H ⟶ K}

/-- The structural morphism from the represented kernel of an isogeny to the trivial group
scheme is itself an isogeny. Equivalently, the kernel is a finite faithfully flat group scheme
over the base. -/
theorem isIsogeny_kernelSpec_to_trivial (hf : IsIsogeny f) :
    GroupScheme.IsIsogeny
      (0 : kernelSpec f ⟶ Grp.trivial
        (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))) := by
  -- The kernel square is a pullback of group schemes; both forgetful functors create the
  -- limits it involves, so it stays a pullback of the underlying schemes.
  have hsq := ((isPullback_kernelSpec f).map
    (Grp.forget (Over (AlgebraicGeometry.Spec (CommRingCat.of R))))).map
      (Over.forget (AlgebraicGeometry.Spec (CommRingCat.of R)))
  have hiso := (isIsogeny_iff_isIsogeny_hopfSpec_map f).1 hf
  rw [GroupScheme.isIsogeny_iff] at hiso ⊢
  -- Each of the three defining properties is stable under base change.
  exact ⟨MorphismProperty.of_isPullback hsq hiso.1,
    MorphismProperty.of_isPullback hsq hiso.2.1,
    MorphismProperty.of_isPullback hsq hiso.2.2⟩

end IsIsogeny

namespace IsCentralIsogeny

section Field

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k} {f : H ⟶ K}

/-- Over a field, package the kernel of a central isogeny as a finite locally free
bicommutative Hopf algebra, ready for Cartier duality. -/
noncomputable abbrev kernelFiniteLocallyFree (hf : IsCentralIsogeny f) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  ⟨quotient K (kernelHopfIdeal f),
    (finiteLocallyFreeBicommutativeHopfAlgProperty_iff k _).2
      ⟨moduleFinite_quotient_kernelHopfIdeal hf.isIsogeny.finite, inferInstance,
        hf.isCocomm_quotient_kernelHopfIdeal⟩⟩

end Field

end IsCentralIsogeny

end TauCeti.CommHopfAlgCat
