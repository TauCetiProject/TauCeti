/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Cogenerator

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.Projectivization
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.RingTheory.Artinian.Subalgebra

/-!
# A coseparator is injective over its endomorphism ring

Over an Artin algebra `A`, with `A` small in the module universe, a coseparator `M` of `mod A` is an
injective module over its endomorphism ring (`FGModuleCat.injective_end_of_isCoseparator`), dually
to a generator being projective over it (`TauCeti.Module.IsGenerator.projective_end`). By
projectivization and the Hom-tensor adjunction the dual of `M` is projective as a right module over
the endomorphism ring (a left module over its opposite), and Matlis biduality returns to `M`. This
is the cogenerator half of the forward direction of the Morita-Tachikawa correspondence
(`TauCeti.two_le_dominantDimension_end`).

## Main results

* `FGModuleCat.injective_end_of_isCoseparator`: over an Artin algebra, a coseparator `M` of `mod A`
  is an injective module over its endomorphism ring.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- **A coseparator is injective over its endomorphism ring.** Over an Artin algebra `A`, a
coseparator `M` of `mod A` is an injective module over `Module.End A M`. The modules may live in
any universe in which `A` is small. -/
theorem _root_.FGModuleCat.injective_end_of_isCoseparator (R : Type u) [CommRing R]
    [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    {M : FGModuleCat.{w} A} (hM : IsCoseparator M) :
    Module.Injective (Module.End A M.obj) M.obj := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A`, which is small in the universe `w`, and take an injective
  -- hull `E` of `C ⧸ J(C)`.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  have : Small.{w} C := inferInstanceAs (Small.{w} {a : A // a ∈ C})
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{v, v} C
  have := hf.moduleInjective
  -- The dual `D_C A`, shrunk to the universe `w`, is a finitely generated injective module.
  have : Module.Finite Aᵐᵒᵖ A := .equiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm
  have : Module.Finite A (MatlisDual C E A) := hf.finite_matlisDual_of_finite_op
  have : Small.{w} (MatlisDual C E A) := Module.Finite.small A _
  let e := Shrink.linearEquiv.{w} A (MatlisDual C E A)
  have : Module.Finite A (Shrink.{w} (MatlisDual C E A)) := .equiv e.symm
  have : Module.Injective A (Shrink.{w} (MatlisDual C E A)) :=
    ((Module.Baer.of_injective inferInstance).of_equiv e.symm).injective
  let X := FGModuleCat.of A (Shrink.{w} (MatlisDual C E A))
  have : Injective X := FGModuleCat.injective_of_moduleInjective X
  -- As a finitely generated injective object, `X` lies in `add M`; so `D_C M` is projective as a
  -- right module over `End M` (a left module over its opposite).
  have := (FGModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure (R := C)
    (FGModuleCat.additiveClosure_of_isCoseparator_of_injective hM X) e).2
  exact moduleInjective_of_projective_op_matlisDual hf.length_quotient_linearMap_eq_one
    (isFiniteLength_of_finite_trans C A M.obj)

end TauCeti
