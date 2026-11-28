/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.WithConv

/-!
# Scalar towers on the convolution type synonym

The scalar actions on `WithConv` are transported pointwise. They preserve scalar towers,
independently of any convolution multiplication.
-/

public section

namespace WithConv

/-- A scalar tower passes through the convolution type synonym. -/
instance isScalarTower {R S M : Type*} [Monoid R] [Monoid S] [SMul R S]
    [MulAction R M] [MulAction S M] [IsScalarTower R S M] :
    IsScalarTower R S (WithConv M) where
  smul_assoc r s m := WithConv.ofConv_injective (smul_assoc r s m.ofConv)

end WithConv
