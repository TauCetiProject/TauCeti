/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.LocalRing

/-!
# Unit off-diagonal entries in even unimodular local forms

An even unimodular symmetric form over a local ring where `2` is not a unit cannot split off a
rank-one unimodular form: every self-pairing is divisible by `2`. The determinant then forces a
unit off the diagonal in every basis row. This provides the paired basis vectors used to construct
binary constituents in the dyadic classification.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter IX.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  (B : BilinForm R M)

/-- In a positive-rank even unimodular form over a local ring where `2` is not a unit, the first
basis vector pairs to a unit with a distinct basis vector. These two vectors begin a unimodular
binary constituent. -/
theorem exists_index_ne_zero_isUnit_apply_of_even_of_isUnit_det
    {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ i : Fin (n + 1), i.val ≠ 0 ∧
      IsUnit (B (b 0) (b i)) := by
  apply exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det B b _ hdet
  intro hu0
  exact h2 (isUnit_of_dvd_unit (heven (b 0)) hu0)

end LinearMap.BilinForm

end
