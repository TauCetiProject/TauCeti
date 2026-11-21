/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Inversion of regular cochains on points

For a Hopf algebra `H`, applying its antipode to the coordinate factor of a regular
cochain `t : M ⊗ H` composes the corresponding function with inversion on points.
This is the regular-function operation relating right-translation and left-translation
conventions for algebraic induction. The coefficient module is arbitrary; it needs no
comodule structure.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §§3.3–3.4, pp. 52–54.
-/

public noncomputable section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
  (M : Type*) [AddCommMonoid M] [Module R M]
  {A : Type*} [CommSemiring A] [Algebra R A]

/-- The antipode on the coordinate factor represents inversion of the point argument. -/
@[simp]
theorem pointCochain_lTensor_antipode (g : WithConv (H →ₐ[R] A)) (t : M ⊗[R] H) :
    pointCochain M g.ofConv ((_root_.HopfAlgebraStruct.antipode R).lTensor M t) =
      pointCochain M (g⁻¹).ofConv t := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul m h => simp

end TauCeti.Comodule
