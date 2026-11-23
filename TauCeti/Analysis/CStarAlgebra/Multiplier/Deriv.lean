/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Star
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic

/-!
# Derivatives in multiplier algebras of C⋆-algebras

Transferring real-variable derivatives between a C⋆-algebra `A` and its multiplier algebra
`𝓜(ℂ, A)` (`DoubleCentralizer.hasDerivAt_coe_iff`, `DoubleCentralizer.hasDerivAt_conj_zero`).
-/

public section

open scoped MultiplierAlgebra

namespace DoubleCentralizer

/-- A real path in `A` has derivative `v` exactly when its image in the multiplier algebra has
derivative `v`: the inclusion `A → 𝓜(ℂ, A)` is a linear isometry. -/
theorem hasDerivAt_coe_iff {A : Type*} [NonUnitalCStarAlgebra A] {f : ℝ → A} {v : A} {x : ℝ} :
    HasDerivAt (fun t => (f t : 𝓜(ℂ, A))) (v : 𝓜(ℂ, A)) x ↔ HasDerivAt f v x := by
  have key (h : ℝ) : (f (x + h) : 𝓜(ℂ, A)) - f x - h • (v : 𝓜(ℂ, A)) =
      ((f (x + h) - f x - h • v : A) : 𝓜(ℂ, A)) := by
    simp only [← Complex.coe_smul, coe_sub, coe_smul]
  rw [hasDerivAt_iff_isLittleO_nhds_zero, hasDerivAt_iff_isLittleO_nhds_zero,
    ← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_left (f' := fun h => _ - _)]
  simp only [key, norm_coe]

/-- Conjugating a differentiable path in `A` by a path of multipliers `U` with `U 0 = 1` and
`U' 0 = i Q`, for self-adjoint `Q ∈ A`, adds the commutator `i[Q, ·]` to its derivative at
`0`. -/
theorem hasDerivAt_conj_zero {A : Type*} [NonUnitalCStarAlgebra A] {Q : A}
    (hQ : IsSelfAdjoint Q) {U : ℝ → 𝓜(ℂ, A)} (hU₀ : U 0 = 1)
    (hU : HasDerivAt U (Complex.I • (Q : 𝓜(ℂ, A))) 0) {f g : ℝ → A}
    (hfg : ∀ t, (g t : 𝓜(ℂ, A)) = U t * f t * star (U t)) {v : A} (hf : HasDerivAt f v 0) :
    HasDerivAt g (v + Complex.I • (Q * f 0 - f 0 * Q)) 0 := by
  rw [← hasDerivAt_coe_iff, funext hfg]
  convert (hU.mul (hasDerivAt_coe_iff.2 hf)).mul hU.star using 1
  simp only [Pi.mul_apply, hU₀, star_one, mul_one, one_mul, star_smul, Complex.star_def,
    Complex.conj_I, ← coe_star, hQ.star_eq, coe_add, coe_smul, coe_sub, coe_mul,
    smul_mul_assoc, mul_smul_comm, neg_smul, mul_neg, smul_sub]
  abel

end DoubleCentralizer
