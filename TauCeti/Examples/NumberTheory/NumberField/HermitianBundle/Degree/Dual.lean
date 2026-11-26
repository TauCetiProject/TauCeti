/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.Class
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Dual

/-!
# The Arakelov degree of a dual line: checks

Over `ℚ`, the trivial line with generator norm `e^{-a}` has degree `a` and its dual has degree
`-a`, computed with any functional `f` and section `s` with `f s ≠ 0`, also when `s` does not
generate the line (for instance `s = 2`), and in particular with the generator `1` and the
identity functional. The section-free degree `lineDegree` and the degree of the class in the
compactified Picard group give the same values.
-/

public section

open NumberField TauCeti

namespace TauCeti.HermitianDualDegreeChecks

/-- Over `ℚ`, the dual of `(ℤ, e^{-a} |·|)` has degree `-a`, computed with any `f` and `s` with
`f s ≠ 0`. -/
example (a : ℝ) {s : 𝓞 ℚ} {f : Module.Dual (𝓞 ℚ) (𝓞 ℚ)} (hfs : f s ≠ 0) :
    ((HermitianMetric.trivial ℚ).rescale a).dual.sectionDegree f = -a := by
  have hs : s ≠ 0 := ne_zero_of_map hfs
  have h0 : (HermitianMetric.trivial ℚ).sectionDegree s = 0 :=
    HermitianBundle.sectionDegree_trivial hs
  rw [HermitianMetric.sectionDegree_dual_eq_neg _ hfs,
    HermitianMetric.sectionDegree_rescale _ _ hs, h0, Module.finrank_self]
  simp

/-- Over `ℚ`, the trivial line with generator norm `e^(-a)` has degree `a`, its dual degree `-a`,
computed with the generator `1` and the identity functional. -/
example (a : ℝ) :
    ((HermitianMetric.trivial ℚ).rescale a).sectionDegree 1 = a ∧
      ((HermitianMetric.trivial ℚ).rescale a).dual.sectionDegree LinearMap.id = -a := by
  have h1 : ((HermitianMetric.trivial ℚ).rescale a).sectionDegree 1 = a := by
    rw [HermitianMetric.sectionDegree_rescale _ _ one_ne_zero,
      HermitianMetric.sectionDegree_trivial_one, Module.finrank_self]
    simp
  refine ⟨h1, ?_⟩
  rw [HermitianMetric.sectionDegree_dual_eq_neg _ (s := 1) (by simp), h1]

/-- Over `ℚ`, the section-free degree of the dual of `(ℤ, e^{-a} |·|)` is `-a`. -/
example (a : ℝ) : ((HermitianMetric.trivial ℚ).rescale a).dual.lineDegree = -a := by
  simp [Module.finrank_self]

/-- Over `ℚ`, the class of the dual of `(ℤ, e^{-a} |·|)` in `Pic^(ℤ)` has degree `-a`. -/
example (a : ℝ) :
    ArakelovPicardGroup.degree ℚ ((HermitianMetric.trivial ℚ).rescale a).dual.arakelovClass =
      -a := by
  simp [Module.finrank_self]

end TauCeti.HermitianDualDegreeChecks
