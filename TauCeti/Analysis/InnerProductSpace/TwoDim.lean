/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.InnerProductSpace.Orientation

/-!
# The continuous volume form on the complex plane

The continuous oriented volume form is normalized on the standard complex basis `(1, I)`.
-/

public section

noncomputable section

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

/-- The normalized complex volume form evaluates to one on the basis `(1, I)`. -/
theorem orientation_volumeFormL_one_I :
    Complex.orientation.volumeFormL ![1, I] = 1 := by
  simpa [coe_basisOneI] using
    Complex.orientation.volumeFormL_apply_orthonormal Complex.orthonormalBasisOneI rfl

end Complex
