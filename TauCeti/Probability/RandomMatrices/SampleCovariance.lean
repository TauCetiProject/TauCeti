/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import TauCeti.Analysis.Matrix.SampleSecondMoment

/-!
# Sample covariance matrices

The sample covariance matrix of a complex data matrix is the empirical second-moment matrix of its
columns. The existing second-moment API supplies its entrywise characterization and Hermitian
property.

## Main declarations

* `TauCeti.Probability.sampleCovariance`: the empirical second-moment matrix of the columns.
* `TauCeti.Probability.sampleCovariance_apply`: its entries are sample means of coordinate
  products.
* `TauCeti.Probability.isHermitian_sampleCovariance`: the sample covariance matrix is Hermitian.
-/

public section

noncomputable section

namespace TauCeti

namespace Probability

/-- The sample covariance matrix of a `p × n` data matrix is the empirical second moment of its
columns. -/
def sampleCovariance {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin p) (Fin p) ℂ :=
  TauCeti.sampleSecondMoment (fun k i => X i k)

/-- The `(i, j)` entry of the sample covariance matrix is the sample mean of the products of
coordinates `i` and `j`. -/
@[simp]
theorem sampleCovariance_apply {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℂ) (i j : Fin p) :
    sampleCovariance X i j =
      finiteMean ℂ fun k : Fin n => X i k * star (X j k) :=
  TauCeti.sampleSecondMoment_apply _ _ _

/-- A sample covariance matrix is Hermitian. -/
theorem isHermitian_sampleCovariance {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℂ) :
    (sampleCovariance X).IsHermitian :=
  TauCeti.isHermitian_sampleSecondMoment _

end Probability

end TauCeti
