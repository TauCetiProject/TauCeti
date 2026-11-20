/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation

/-!
# Generation by the standard type-A root generators

The raising and lowering generators of `SlStd` generate the special linear Lie algebra.
This is `TauCeti.lieSpan_specialLinear_adjacent_single_eq_top` expressed in the standard
carrier's numbered generators.
-/

public section

namespace TauCeti.SlStd

open LieAlgebra.SpecialLinear

/-- The standard numbered raising and lowering generators generate the special linear
Lie algebra. -/
theorem lieSpan_rootGenerator_eq_top (r : ℕ) :
    LieSubalgebra.lieSpan ℚ (sl (Fin (r + 1)) ℚ)
      (Set.range (fun i => rootGenerator r (.inl i)) ∪
        Set.range (fun i => rootGenerator r (.inr i))) = ⊤ := by
  have he : (fun i : Fin r => rootGenerator r (.inl i)) = fun i =>
      single i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne (1 : ℚ) := by
    funext i
    apply Subtype.ext
    simp
  have hf : (fun i : Fin r => rootGenerator r (.inr i)) = fun i =>
      single i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' (1 : ℚ) := by
    funext i
    apply Subtype.ext
    simp
  rw [he, hf]
  exact lieSpan_specialLinear_adjacent_single_eq_top r ℚ

end TauCeti.SlStd
