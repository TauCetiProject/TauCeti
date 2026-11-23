/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Analysis.Complex.Theta.Vanishing
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Boundary and level-0 dimension formulas for theta sections

This file records the `Module.finrank` dimension formulas for `TauCeti.thetaSections` outside the
positive-level upper half-plane regime (which is treated in
`TauCeti.NumberTheory.ModularForms.JacobiTheta.Sections`):

* `TauCeti.finrank_thetaSections_of_im_nonpos`: for `k > 0` and `τ.im ≤ 0`,
  `Module.finrank ℂ (thetaSections k τ α β) = 0`.
* `TauCeti.finrank_thetaSections_zero`: for `k = 0` and `τ.im ≠ 0`,
  `Module.finrank ℂ (thetaSections 0 τ α β)` is `1` when `(α, β) ∈ ℤ × ℤ` and `0` otherwise.

## Main results

* `TauCeti.finrank_thetaSections_of_im_nonpos`: vanishing dimension for `0 < k` and `τ.im ≤ 0`.
* `TauCeti.finrank_thetaSections_zero`: complete dimension formula at level `k = 0` for `τ.im ≠ 0`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

namespace TauCeti

/-- For positive level `k > 0` and `τ.im ≤ 0`, `thetaSections k τ α β` has dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, finrank_bot]

open scoped Classical in
/-- **Complete dimension formula at level `k = 0`.** For any non-real period `τ` (`τ.im ≠ 0`), the
space `thetaSections 0 τ α β` has dimension `1` when both characteristics are integers (the
trivial flat line bundle) and dimension `0` otherwise. -/
theorem finrank_thetaSections_zero (τ : ℂ) (hτ : τ.im ≠ 0) (α β : ℝ) :
    Module.finrank ℂ (thetaSections 0 τ α β) =
      if (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β) then 1 else 0 := by
  by_cases h : (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β)
  · rw [ite_eq_left h]
    have h1 : (fun _ : ℂ => (1 : ℂ)) ∈ thetaSections 0 τ α β :=
      (mem_thetaSections_zero_iff_const hτ h.left h.right).mpr ⟨1, rfl⟩
    refine finrank_eq_one ⟨fun _ => 1, h1⟩ ?_ fun s => ?_
    · intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      exact one_ne_zero this
    · obtain ⟨c, hc⟩ := (mem_thetaSections_zero_iff_const hτ h.left h.right).mp s.property
      refine ⟨c, Subtype.ext ?_⟩
      ext z
      simp [hc]
  · rw [ite_eq_right h, thetaSections_zero_eq_bot_of_not_int hτ h, finrank_bot]

end TauCeti
