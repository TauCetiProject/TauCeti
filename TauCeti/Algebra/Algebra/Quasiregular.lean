/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Tactic.NoncommRing

/-!
# The quasi-multiplication of a unital ring

In a nonunital semiring `B`, the operation `x ∘ y = y + x + x * y` makes `PreQuasiregular B` a
monoid with identity `0`, whose units are the quasiregular elements. When `B` is a ring with
identity, `(1 + x) * (1 + y) = 1 + (x ∘ y)`, so `x ↦ 1 + x` is an isomorphism of monoids from
`PreQuasiregular B` onto the multiplicative monoid of `B`. On units it identifies the quasi-units
with `Bˣ`, which bundles Mathlib's `isQuasiregular_iff_isUnit`.

## Main definitions

* `PreQuasiregular.oneAddMulEquiv`: the monoid isomorphism `PreQuasiregular B ≃* B`,
  `x ↦ 1 + x`, for a ring `B`.
-/

public section

noncomputable section

namespace PreQuasiregular

variable (B : Type*) [Ring B]

/-- In a unital ring `B`, the map `x ↦ 1 + x` is a monoid isomorphism from `PreQuasiregular B`,
with operation `x ∘ y = y + x + x * y`, onto the multiplicative monoid of `B`; its inverse is
`b ↦ b - 1`. -/
def oneAddMulEquiv : PreQuasiregular B ≃* B where
  toFun x := 1 + x.val
  invFun b := equiv (b - 1)
  left_inv x := equiv.symm.injective <| by simp
  right_inv b := by simp
  map_mul' x y := by
    simp only [val_mul]
    noncomm_ring

variable {B}

/-- `PreQuasiregular.oneAddMulEquiv` sends `x` to `1 + x`. -/
@[simp]
theorem oneAddMulEquiv_apply (x : PreQuasiregular B) : oneAddMulEquiv B x = 1 + x.val :=
  (rfl)

/-- The inverse of `PreQuasiregular.oneAddMulEquiv` sends `b` to `b - 1`. -/
@[simp]
theorem val_oneAddMulEquiv_symm_apply (b : B) : ((oneAddMulEquiv B).symm b).val = b - 1 :=
  (rfl)

end PreQuasiregular
