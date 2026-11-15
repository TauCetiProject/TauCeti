/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# Unit multiples of invariant forms

An invariant form of a root pairing is determined by its underlying bilinear form, and rescaling
the bilinear form by a unit of the coefficient ring gives again an invariant form. This file
records both facts: the extensionality lemma, and the action of the units `Rˣ` on
`P.InvariantForm` by rescaling, so that `(c • B).form = c • B.form`.

## Main definitions

* `RootPairing.InvariantForm.instMulActionUnits`: the units of the coefficient ring act on the
  invariant forms by rescaling.

## Main results

* `RootPairing.InvariantForm.ext`: an invariant form is determined by its bilinear form.
* `RootPairing.InvariantForm.smul_form`: the bilinear form of `c • B` is `c • B.form`.
-/

public section

namespace RootPairing.InvariantForm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- An invariant form is determined by its underlying bilinear form. -/
@[ext]
theorem ext {B C : P.InvariantForm} (h : B.form = C.form) : B = C := by
  cases B
  cases C
  congr

/-- The units of the coefficient ring act on the invariant forms by rescaling the bilinear form. -/
instance instMulActionUnits : MulAction Rˣ P.InvariantForm where
  smul c B :=
    { form := (c : R) • B.form
      symm := ⟨fun x y ↦ by simpa using congrArg ((c : R) * ·) (B.symm.eq x y)⟩
      ne_zero i := by simpa using B.ne_zero i
      isOrthogonal_reflection i x y := by simp [B.isOrthogonal_reflection i x y] }
  one_smul B := ext (one_smul R B.form)
  mul_smul c d B := ext (mul_smul (c : R) (d : R) B.form)

@[simp]
theorem smul_form (c : Rˣ) (B : P.InvariantForm) : (c • B).form = (c : R) • B.form :=
  (rfl)

end RootPairing.InvariantForm
