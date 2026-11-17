/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Compactly supported functions with a vanishing iterated derivative

On a noncompact space, a compactly supported `Cⁿ` function whose `n`-th iterated derivative
vanishes identically is zero (`HasCompactSupport.eq_zero_of_iteratedFDeriv_eq_zero`). Without the
support condition this fails for every `n ≥ 1`, since constants have vanishing derivative; without
the smoothness condition it fails already for `n = 1`, since the indicator function of a ball has
zero Fréchet derivative at every point in Mathlib's convention.

Equivalently, a nonzero compactly supported `Cⁿ` function has a point at which its `n`-th iterated
derivative is nonzero (`HasCompactSupport.exists_iteratedFDeriv_ne_zero`).
-/

public section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A compactly supported `Cⁿ` function on a noncompact space whose `n`-th iterated derivative
vanishes identically is zero. -/
theorem HasCompactSupport.eq_zero_of_iteratedFDeriv_eq_zero [NoncompactSpace E] :
    ∀ {n : ℕ} {f : E → F}, ContDiff 𝕜 n f → HasCompactSupport f →
      iteratedFDeriv 𝕜 n f = 0 → f = 0
  | 0, f, _, _, h => by
    ext x
    rw [Pi.zero_apply, ← norm_eq_zero, ← norm_iteratedFDeriv_zero (𝕜 := 𝕜), h, Pi.zero_apply,
      norm_zero]
  | n + 1, f, hf, hc, h => by
    -- The `n`-th iterated derivative has zero derivative, so it is constant; it is compactly
    -- supported, hence zero.
    have hd : iteratedFDeriv 𝕜 n f = 0 := by
      obtain ⟨y, hy⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp
        (hc.iteratedFDeriv (𝕜 := 𝕜) n).isCompact.ne_univ
      have hconst := is_const_of_fderiv_eq_zero
        (hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast n.lt_succ_self))
        fun x => by rw [← norm_eq_zero, norm_fderiv_iteratedFDeriv, h, Pi.zero_apply, norm_zero]
      ext1 x
      rw [hconst x y, image_eq_zero_of_notMem_tsupport hy, Pi.zero_apply]
    exact hc.eq_zero_of_iteratedFDeriv_eq_zero (hf.of_le (by exact_mod_cast n.le_succ)) hd

/-- A nonzero compactly supported `Cⁿ` function on a noncompact space has a point at which its
`n`-th iterated derivative is nonzero. -/
theorem HasCompactSupport.exists_iteratedFDeriv_ne_zero [NoncompactSpace E] {n : ℕ} {f : E → F}
    (hf : ContDiff 𝕜 n f) (hc : HasCompactSupport f) (h : f ≠ 0) :
    ∃ x, iteratedFDeriv 𝕜 n f x ≠ 0 := by
  by_contra! hzero
  exact h (hc.eq_zero_of_iteratedFDeriv_eq_zero hf (funext hzero))

end
