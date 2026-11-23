/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Derivations on generated intermediate fields

If an `R`-derivation `d : Derivation R F M` into an `F`-module vanishes on an intermediate base
field `E` and maps every generator in `s : Set F` into an `F`-submodule `S`, then `d` maps the
entire intermediate field `E(s)` into `S`.

## Main results

* `Derivation.map_mem_of_mem_adjoin`: derivatives on `IntermediateField.adjoin E s` stay in any
  `F`-submodule containing the derivatives of `s`, provided `d` vanishes on `E`.
-/

public section

namespace Derivation

/-- If an `R`-derivation `d : Derivation R F M` into an `F`-module vanishes on an intermediate
field `E` and maps every generator in `s` into an `F`-submodule `S`, then `d` maps the entire
intermediate field `E(s)` into `S`. -/
theorem map_mem_of_mem_adjoin {R E F M : Type*} [CommSemiring R] [Field E] [Field F]
    [Algebra R F] [Algebra E F] [AddCommMonoid M] [Module R M] [Module F M]
    (d : Derivation R F M) (S : Submodule F M) {s : Set F}
    (hE : ∀ e : E, d (algebraMap E F e) = 0) (hs : ∀ z ∈ s, d z ∈ S) {x : F}
    (hx : x ∈ IntermediateField.adjoin E s) : d x ∈ S := by
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz => exact hs z hz
  | algebraMap e => simp [hE e]
  | add a b _ _ ha hb => rw [map_add]; exact S.add_mem ha hb
  | mul a b _ _ ha hb => rw [d.leibniz]; exact S.add_mem (S.smul_mem a hb) (S.smul_mem b ha)
  | inv a _ ha =>
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hmul := congrArg d (mul_inv_cancel₀ ha0)
      rw [d.leibniz, d.map_one_eq_zero] at hmul
      have hinv : d a⁻¹ = (-1 : F) • (a⁻¹ • (a⁻¹ • d a)) := by
        calc d a⁻¹ = d a⁻¹ + (-1 : F) • (a⁻¹ • (a • d a⁻¹ + a⁻¹ • d a)) := by
              rw [hmul, smul_zero, smul_zero, add_zero]
          _ = (-1 : F) • (a⁻¹ • (a⁻¹ • d a)) := by
              rw [smul_add, smul_add, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ ha0,
                mul_one, ← add_assoc]
              nth_rw 1 [← one_smul F (d a⁻¹)]
              rw [← add_smul, add_neg_cancel, zero_smul, zero_add]
      rw [hinv]
      exact S.smul_mem (-1 : F) (S.smul_mem a⁻¹ (S.smul_mem a⁻¹ ha))

end Derivation
