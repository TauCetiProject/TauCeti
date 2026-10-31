/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Matrix coefficients and the trace pairing

For a finite free comodule, the coefficient map from `M* ⊗ M` is dual to the
convolution action under the trace pairing on endomorphisms. This comparison
allows density of the convolution action to detect linear relations among coefficients.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {R C M : Type*} [CommRing R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [Module.Free R M] [Module.Finite R M]

/-- The coefficient tensor map is dual to the convolution action under the trace pairing. -/
theorem _root_.WithConv.apply_matrixCoefficientTensor_eq_trace (f : WithConv (Module.Dual R C))
    (z : Module.Dual R M ⊗[R] M) :
    f.ofConv (matrixCoefficientTensor (R := R) (C := C) z) =
      LinearMap.trace R M
        (convolutionAction (R := R) (C := C) f * dualTensorHom R M M z) := by
  induction z with
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | tmul φ m =>
    have hmul : convolutionAction (R := R) (C := C) f *
        dualTensorHom R M M (φ ⊗ₜ[R] m) =
          dualTensorHom R M M (φ ⊗ₜ[R] convolutionAction (R := R) (C := C) f m) := by
      ext x
      simp [Module.End.mul_apply]
    rw [hmul, LinearMap.trace_eq_contract_apply, contractLeft_apply,
      matrixCoefficientTensor_tmul, LinearMap.apply_matrixCoefficient]
    simp only [coactComponent_apply, convolutionAction_apply]

end TauCeti.Comodule
