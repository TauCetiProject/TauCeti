/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.Perfectoid.IsAlgClosed

/-!
# `ℂ_p` is perfectoid and `ℚ_p` is not

The `p`-adic complex numbers `ℂ_p` form a perfectoid Tate ring, being a complete algebraically
closed nonarchimedean field with `‖p‖ < 1`
(`TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed`). The `p`-adic numbers `ℚ_p` do not,
even though Frobenius on `ℤ_p ⧸ p = 𝔽_p` is bijective: no pseudouniformiser `ϖ` of `ℚ_p` has
`ϖ ^ p ∣ p` in `ℤ_p`. In particular `ℚ_p` has no pseudouniformiser with compatible `p`-power
roots.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_padicComplex`: `ℂ_p` is a perfectoid Tate ring.
* `TauCeti.Perfectoid.not_pow_dvd_padic`: no pseudouniformiser `ϖ` of `ℚ_p` has `ϖ ^ p ∣ p` in
  `ℤ_p`.
* `TauCeti.Perfectoid.not_isPerfectoidTateRing_padic`: `ℚ_p` is not perfectoid.
* `TauCeti.Perfectoid.isEmpty_pseudoUniformizerRoots_padic`: `ℚ_p` has no pseudouniformiser with
  compatible `p`-power roots.
* `TauCeti.Perfectoid.not_isPerfectoidTateRing_padicComplex_prod_padic`: nor is `ℂ_p × ℚ_p`, a
  factor of a perfectoid product being perfectoid.

## References

* P. Scholze, *Étale cohomology of diamonds*, Remark 3.3.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime]

/-- **`ℂ_p` is a perfectoid Tate ring**: it is complete and algebraically closed, and
`‖p‖ = p⁻¹ < 1`. -/
instance isPerfectoidTateRing_padicComplex : IsPerfectoidTateRing p ℂ_[p] :=
  isPerfectoidTateRing_of_isAlgClosed (by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt))

/-- **No pseudouniformiser `ϖ` of `ℚ_p` has `ϖ ^ p ∣ p` in `ℤ_p`**: a pseudouniformiser has
`‖ϖ‖ ≤ p⁻¹`, so `‖ϖ ^ p‖ < ‖p‖` (Scholze, *Étale cohomology of diamonds*, Remark 3.3). -/
theorem not_pow_dvd_padic (ϖ : powerBoundedSubring ℚ_[p]) (hϖ : IsPseudoUniformizer (ϖ : ℚ_[p])) :
    ¬ ϖ ^ p ∣ (p : powerBoundedSubring ℚ_[p]) := by
  rintro ⟨c, hc⟩
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hϖ1 : ‖(ϖ : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (ϖ : ℚ_[p]) (-1)).mpr
      (by simpa using (isPseudoUniformizer_iff_norm_lt_one.mp hϖ).2)
    simpa using this
  have hc1 : ‖(c : ℚ_[p])‖ ≤ 1 := isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  have hceq : (p : ℚ_[p]) = (ϖ : ℚ_[p]) ^ p * c := by
    simpa using congrArg Subtype.val hc
  have : (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ ^ p := by
    calc (p : ℝ)⁻¹ = ‖(p : ℚ_[p])‖ := Padic.norm_p.symm
      _ = ‖(ϖ : ℚ_[p])‖ ^ p * ‖(c : ℚ_[p])‖ := by rw [hceq, norm_mul, norm_pow]
      _ ≤ (p : ℝ)⁻¹ ^ p * 1 := by gcongr
      _ = (p : ℝ)⁻¹ ^ p := mul_one _
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  exact absurd this (not_le.mpr (pow_lt_self_of_lt_one₀ (by positivity)
    (inv_lt_one_of_one_lt₀ hp) hp2))

/-- **`ℚ_p` is not a perfectoid Tate ring**, although Frobenius on `ℤ_p ⧸ p = 𝔽_p` is bijective:
no pseudouniformiser `ϖ` of `ℚ_p` has `ϖ ^ p ∣ p` in `ℤ_p` (Scholze, *Étale cohomology of
diamonds*, Remark 3.3). -/
theorem not_isPerfectoidTateRing_padic : ¬ IsPerfectoidTateRing p ℚ_[p] := by
  rintro ⟨-, ϖ, hϖ, h, -⟩
  exact not_pow_dvd_padic p ϖ hϖ h

/-- **`ℚ_p` has no pseudouniformiser with compatible `p`-power roots**: already no
pseudouniformiser `ϖ` of `ℚ_p` has `ϖ ^ p ∣ p` in `ℤ_p`. -/
instance isEmpty_pseudoUniformizerRoots_padic : IsEmpty (PseudoUniformizerRoots p ℚ_[p]) :=
  ⟨fun ϖ ↦ not_pow_dvd_padic p _ ϖ.isPseudoUniformizer ϖ.pow_dvd⟩

/-- **`ℂ_p × ℚ_p` is not a perfectoid Tate ring**: its factor `ℚ_p` is not, and both factors of a
perfectoid product are perfectoid. -/
theorem not_isPerfectoidTateRing_padicComplex_prod_padic :
    ¬ IsPerfectoidTateRing p (ℂ_[p] × ℚ_[p]) :=
  fun h ↦ not_isPerfectoidTateRing_padic p (isPerfectoidTateRing_prod_iff.mp h).2

end TauCeti.Perfectoid
