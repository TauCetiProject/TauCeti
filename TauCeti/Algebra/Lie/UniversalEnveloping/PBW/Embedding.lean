/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The canonical embedding into an enveloping algebra

A Lie algebra `L` that is free as a module over a commutative ring `R` embeds in its universal
enveloping algebra. The degree-one map into the PBW associated graded is injective, since the
Poincaré--Birkhoff--Witt isomorphism identifies it with the canonical embedding into the symmetric
algebra. Consequently the canonical Lie map `ι : L → U(L)` is injective, and the images of any
basis of `L` are linearly independent.

These results identify `L` with its canonical copy in `U(L)`, so a quotient of `U(L)` separating
that copy gives a faithful representation of `L`. Over a field freeness is automatic; neither
finite-dimensionality nor a characteristic assumption is needed.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The degree-one generators of the PBW associated graded embed a Lie algebra that is free
as a module over the base ring. -/
theorem pbwGradedGenerator_injective [Module.Free R L] :
    Function.Injective (pbwGradedGenerator R L) := by
  intro x y h
  apply TauCeti.SymmetricAlgebra.ι_injective R L
  apply pbwAssociatedGradedMap_injective R L
  simpa only [pbwAssociatedGradedMap_ι] using h

/-- A Lie algebra that is free as a module over a commutative ring embeds in its universal
enveloping algebra. In particular, this holds for every Lie algebra over a field. -/
theorem ι_injective [Module.Free R L] :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : L → U) := by
  intro x y h
  apply pbwGradedGenerator_injective R L
  simp only [pbwGradedGenerator_apply]
  congr 2
  exact Subtype.ext h

/-- The images of a basis of a Lie algebra are linearly independent in its enveloping algebra. -/
theorem linearIndependent_ι_basis {κ : Type w} (b : Module.Basis κ R L) :
    LinearIndependent R fun i : κ ↦ (_root_.UniversalEnvelopingAlgebra.ι R (b i) : U) := by
  let := Module.Free.of_basis b
  exact b.linearIndependent.map'
    (_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U).toLinearMap
    (LinearMap.ker_eq_bot_of_injective (ι_injective R L))

end TauCeti.UniversalEnvelopingAlgebra
