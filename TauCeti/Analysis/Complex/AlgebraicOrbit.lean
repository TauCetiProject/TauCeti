/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.FieldEmbedding

/-!
# Bounded automorphism orbits in the complex field

A complex number with bounded images under all abstract field automorphisms of `ℂ` is
algebraic over `ℚ`. This gives an archimedean test for algebraicity without choosing a
nonarchimedean absolute value on `ℂ`.
-/

public section

namespace TauCeti.Complex

/-- A complex number with bounded images under all field automorphisms is algebraic over `ℚ`. -/
theorem isAlgebraic_of_forall_norm_ringEquiv_le {z : ℂ} {B : ℝ}
    (h : ∀ σ : ℂ ≃+* ℂ, ‖σ z‖ ≤ B) : IsAlgebraic ℚ z := by
  by_contra hz
  obtain ⟨n, hn⟩ := exists_nat_gt (B + ‖z‖)
  have htrans : Transcendental ℚ (z + (n : ℂ)) := by
    intro ha
    exact hz (by simpa using ha.sub (isAlgebraic_natCast (R := ℚ) n))
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq (k := ℚ) Cardinal.mk_complex hz htrans
  have hlarge := norm_sub_norm_le (n : ℂ) (-z)
  rw [norm_neg, _root_.Complex.norm_natCast, sub_neg_eq_add, add_comm (n : ℂ) z] at hlarge
  have hsmall : ‖z + (n : ℂ)‖ ≤ B := hσ ▸ h σ.toRingEquiv
  linarith

end TauCeti.Complex
