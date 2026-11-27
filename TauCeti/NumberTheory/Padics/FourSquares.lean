/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SumFourSquares

/-!
# Four squares in the p-adic integers

Lagrange's four-square theorem extends to `ℤ_[p]` by compactness and density. In particular,
representing `-1` gives a tuple of integral scaling factors with first factor `1` and with
zero sum of squares, for cancelling quadratic terms under rescaling.
-/

public section

namespace PadicInt

/-- Every p-adic integer is a sum of four squared p-adic integers, including at `p = 2`. -/
theorem sum_four_squares {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    ∃ a b c d : ℤ_[p], a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = x := by
  let f (v : ℤ_[p] × ℤ_[p] × ℤ_[p] × ℤ_[p]) := v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hx : x ∈ Set.range f := by
    refine denseRange_natCast.induction_on x (isCompact_range hf).isClosed ?_
    intro n
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
    refine ⟨(a, b, c, d), ?_⟩
    simpa only [f, Nat.cast_add, Nat.cast_pow] using congrArg (Nat.cast : ℕ → ℤ_[p]) h
  obtain ⟨⟨a, b, c, d⟩, h⟩ := hx
  exact ⟨a, b, c, d, h⟩

end PadicInt
