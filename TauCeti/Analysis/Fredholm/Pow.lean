/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Powers of Fredholm operators

This file records the compositional calculus of a Fredholm endomorphism under natural-number
powers, over a complete nontrivially normed scalar field.

That a composite is Fredholm is Mathlib's `ContinuousLinearMap.IsFredholm.comp`, and that the
index of a composite of Fredholm operators is the sum of their indices is Mathlib's
`ContinuousLinearMap.IsFredholm.index_comp`. Iterating these gives the statements for powers.

## Main declarations

* `ContinuousLinearMap.IsFredholm.pow`: every power of a Fredholm endomorphism is Fredholm.
* `ContinuousLinearMap.index_pow`: the index of the `n`th power is `n` times the index.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Appendix A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]


section Pow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {A : X →L[𝕜] X}

/-- Over a complete nontrivially normed scalar field, every natural-number power of a Fredholm
endomorphism is Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.pow (hA : ContinuousLinearMap.IsFredholm A) :
    ∀ n : ℕ, ContinuousLinearMap.IsFredholm (A ^ n)
  | 0 => by
      rw [pow_zero, ContinuousLinearMap.one_def]
      exact .id
  | n + 1 => by
      rw [pow_succ, ContinuousLinearMap.mul_def]
      exact (hA.pow n).comp hA


/-- The index of the `n`th power of a Fredholm endomorphism is `n` times its index. -/
@[simp]
theorem _root_.ContinuousLinearMap.index_pow (A : X →L[𝕜] X) (hA : ContinuousLinearMap.IsFredholm A)
    (n : ℕ) :
    ContinuousLinearMap.index (A ^ n) = (n : ℤ) * ContinuousLinearMap.index A := by
  induction n with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.index_id, Nat.cast_zero,
        zero_mul]
  | succ n ih =>
      have hcomp : ContinuousLinearMap.index ((A ^ n).comp A) =
          ContinuousLinearMap.index (A ^ n) + ContinuousLinearMap.index A := by
        simpa only [ContinuousLinearMap.index_def, ContinuousLinearMap.toLinearMap_comp] using
          (hA.pow n).index_comp hA
      rw [pow_succ, ContinuousLinearMap.mul_def, hcomp, ih]
      push_cast
      ring


end Pow

end TauCeti
