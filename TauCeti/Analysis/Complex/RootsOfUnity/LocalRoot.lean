/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold
import TauCeti.Analysis.SpecialFunctions.Pow.LocalRoot
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Local roots on the rotated disc

The power map `TauCeti.rootsOfUnityBall.powMap` from the disc of radius `r` to the disc of radius
`r ^ m` has local sections away from the centre. This file chooses such a section `w` near a
nonzero point `t₀` together with a logarithm `L` of it, both `C^n` at `t₀` for the disc atlases,
hence holomorphic there for `n ≠ 0`. It restricts the branch
`TauCeti.exists_contDiffAt_pow_eq_and_exp_eq` of `ℂ` to the discs.

## Main declarations

* `TauCeti.rootsOfUnityBall.exists_contMDiffAt_powMap_eq_and_exp_eq`: near a nonzero point, the
  power map `u ↦ u ^ m` between the discs has a `C^n` local section together with a `C^n`
  logarithm of it (holomorphic for `n ≠ 0`).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ} {n : ℕ∞ω}

/-- **Holomorphic local roots and their logarithms.** For `0 ≤ r` and `t₀ ≠ 0` in the disc of
radius `r ^ m`, there are maps `w` to the disc of radius `r` and `L` to `ℂ`, both `C^n` at `t₀`
(holomorphic for `n ≠ 0`), such that every `t ≠ 0` has `w t ^ m = t` and `exp (L t) = w t`. -/
theorem rootsOfUnityBall.exists_contMDiffAt_powMap_eq_and_exp_eq (hr : 0 ≤ r)
    {t₀ : Metric.ball (0 : ℂ) (r ^ m)} (ht₀ : (t₀ : ℂ) ≠ 0) :
    ∃ (w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r)
      (L : Metric.ball (0 : ℂ) (r ^ m) → ℂ),
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n w t₀ ∧ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n L t₀ ∧
        ∀ t : Metric.ball (0 : ℂ) (r ^ m), (t : ℂ) ≠ 0 →
          rootsOfUnityBall.powMap m r (w t) = t ∧ Complex.exp (L t) = w t := by
  obtain ⟨f, L, hf, hL, -, hfm, hLf⟩ := exists_contDiffAt_pow_eq_and_exp_eq (n := n)
    (NeZero.ne m) ht₀ (c := rootsOfUnityBall.rootMap hr t₀)
    (by rw [← rootsOfUnityBall.coe_powMap, rootsOfUnityBall.powMap_rootMap])
  have hmem (t : Metric.ball (0 : ℂ) (r ^ m)) : f t ∈ rootsOfUnityBall m r :=
    mem_rootsOfUnityBall.2 <| mem_ball_zero_iff.1 <|
      (pow_mem_ball_zero_pow_iff hr).1 (by rw [hfm]; exact t.property)
  have hval := (contMDiff_subtypeVal_ball (I := 𝓘(ℂ)) (n := n) (c := (0 : ℂ))
    (r := r ^ m)).contMDiffAt (x := t₀)
  refine ⟨fun t ↦ ⟨f t, hmem t⟩, fun t ↦ L t, ?_, hL.contMDiffAt.comp t₀ hval,
    fun t ht ↦ ⟨Subtype.ext ?_, hLf t ht⟩⟩
  · -- Lift through the inclusion of the disc, which is a local diffeomorphism.
    refine contMDiffWithinAt_univ.1 (ContMDiffWithinAt.of_comp_isLocalDiffeomorph
      (p := ((↑) : rootsOfUnityBall m r → ℂ)) (isLocalDiffeomorph_coe_rootsOfUnityBall _) ?_
      (contMDiffWithinAt_univ.2 (hf.contMDiffAt.comp t₀ hval)))
    exact ((hf.continuousAt.comp hval.continuousAt).codRestrict hmem).continuousWithinAt
  · rw [rootsOfUnityBall.coe_powMap]
    exact hfm t

end TauCeti
