/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The skew part of an alternating bilinear form

Over any commutative ring, subtracting the flipped alternating form doubles its values.
-/

public section

namespace LinearMap.BilinForm.IsAlt

/-- The skew part of an alternating bilinear form over a commutative ring is twice that form. -/
theorem sub_flip_apply_eq_two_mul {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    {Λ : LinearMap.BilinForm S M} (hΛ : Λ.IsAlt) (a b : M) :
    (Λ - Λ.flip) a b = 2 * Λ a b := by
  have hf : (Λ.flip a) b = Λ b a := LinearMap.flip_apply Λ b a
  simp only [LinearMap.sub_apply]
  rw [hf, ← hΛ.neg_eq a b, sub_neg_eq_add, two_mul]

end LinearMap.BilinForm.IsAlt
