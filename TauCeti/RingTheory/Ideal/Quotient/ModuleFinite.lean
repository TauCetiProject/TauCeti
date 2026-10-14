/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Module-finite quotients by products of ideals

If `R / I` and `R / J` are finite modules over a commutative base ring and `I` is finitely
generated over `R`, then `R / IJ` is finite over the base ring. This follows from the filtration
with successive quotients `I / IJ` and `R / I`: the first is a base change of `I` to `R / J`.
In particular, this applies when `I` is an invertible module, without a domain hypothesis.

The filtration is extracted from the point-to-class surjectivity argument, adapted from
Chris Birkbeck's AINTLIB (`github.com/CBirkbeck/AINTLIB`,
`HasseWeil/Pic0/ToClassSurjective.lean`, revision `dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
-/

public section

open scoped TensorProduct

namespace Ideal

/-- Products preserve module-finite quotients when the first factor ideal is finitely generated.
This does not require that factor to be invertible. -/
theorem finite_quotient_mul {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (I J : Ideal R) [Module.Finite R I] [Module.Finite A (R ⧸ I)]
    [Module.Finite A (R ⧸ J)] : Module.Finite A (R ⧸ I * J) := by
  let g : I →ₗ[R] R ⧸ I * J := (I * J).mkQ.comp I.subtype
  let N := LinearMap.range g
  have hN : N = Submodule.map (I * J).mkQ I := by
    dsimp only [N, g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let eN : (R ⧸ J) ⊗[R] I ≃ₗ[R] N :=
    (TensorProduct.quotTensorEquivQuotSMul I J).trans
      ((Submodule.quotEquivOfEq _ _ (I.smul_top_eq_comap_mul J)).trans
        ((Submodule.quotEquivOfEq _ _ (by
          simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ])).trans g.quotKerEquivRange))
  have : Module.Finite (R ⧸ J) ((R ⧸ J) ⊗[R] I) :=
    Module.Finite.base_change R (R ⧸ J) I
  have : Module.Finite A ((R ⧸ J) ⊗[R] I) :=
    Module.Finite.trans (R ⧸ J) ((R ⧸ J) ⊗[R] I)
  have : Module.Finite A (N.restrictScalars A) :=
    Module.Finite.equiv ((eN.restrictScalars A).trans
      ((N.restrictScalarsEquiv A).restrictScalars A).symm)
  have eQ : ((R ⧸ I * J) ⧸ N) ≃ₗ[R] R ⧸ I := by
    rw [hN]
    exact Submodule.quotientQuotientEquivQuotient (I * J) I Ideal.mul_le_left
  have : Module.Finite A ((R ⧸ I * J) ⧸ N.restrictScalars A) :=
    Module.Finite.equiv ((eQ.restrictScalars A).symm.trans
      (Submodule.Quotient.restrictScalarsEquiv A N).symm)
  exact Module.Finite.of_submodule_quotient (N.restrictScalars A)

end Ideal
