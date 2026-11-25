/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Coeff
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Check: the algebraic tensor product of two Tate algebras is not complete

For a prime `p`, the series `Σₙ pⁿTⁿSⁿ` of `ℚ_p⟨T⟩ ⊗̂_{ℚ_p} ℚ_p⟨S⟩ ≃ ℚ_p⟨T, S⟩` is not the image of
an element of the algebraic tensor product `ℚ_p⟨T⟩ ⊗_{ℚ_p} ℚ_p⟨S⟩`: its matrix of coefficients
is diagonal with nonzero entries `pⁿ`, of infinite rank, while the image of a finite sum of pure
tensors has a coefficient matrix of finite rank. So the comparison of completed and algebraic
tensor products for finite algebras needs its finiteness hypothesis, including for `p = 2`.
-/

public section

open TauCeti.Huber

namespace TauCeti.Examples.PolydiscCoeff

variable (p : ℕ) [Fact p.Prime]

/-- `p` is topologically nilpotent in `ℚ_p`. -/
theorem isTopologicallyNilpotent_p : IsTopologicallyNilpotent (p : ℚ_[p]) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

-- `finite_tensor_infinite_rank`: `Σₙ pⁿTⁿSⁿ` is not in the image of the algebraic tensor product.
example : CompletedTensor.diagonalSeries (isTopologicallyNilpotent_p p) ∉
    Set.range fun x ↦ CompletedTensor.polydiscEquiv ℚ_[p] 1 1
      (CompletedTensor.toCompletion ℚ_[p] _ _ x) :=
  CompletedTensor.diagonalSeries_notMem_range _
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

-- The coefficients of `Σₙ pⁿTⁿSⁿ` are `pⁿ` on the diagonal and `0` off it.
example (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (toMvPowerSeries (1 + 1) ℚ_[p]
          (CompletedTensor.diagonalSeries (isTopologicallyNilpotent_p p))) =
      if i = j then (p : ℚ_[p]) ^ i else 0 :=
  CompletedTensor.coeff_diagonalSeries _ i j

-- For `p = 2` as well.
example : CompletedTensor.diagonalSeries (isTopologicallyNilpotent_p 2) ∉
    Set.range fun x ↦ CompletedTensor.polydiscEquiv ℚ_[2] 1 1
      (CompletedTensor.toCompletion ℚ_[2] _ _ x) :=
  CompletedTensor.diagonalSeries_notMem_range _ two_ne_zero

end TauCeti.Examples.PolydiscCoeff
