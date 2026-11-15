/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ChoquetDeny
public import TauCeti.Probability.Renewal.Lattice.Basic

/-!
# Harmonic measures of a nonlattice law are multiples of Lebesgue measure

Let `F` be a probability law on `ℝ≥0` and write `F` also for its image on `ℝ`. A measure `η` on
`ℝ` is `F`-harmonic if `F ∗ η = η`. This file proves the rigidity theorem of renewal theory: if
`F` is nonlattice and `η` is uniformly locally bounded, that is `η [a, a + 1] ≤ C` for every
`a : ℝ`, then `η` is a multiple of Lebesgue measure, namely `η = η (0, 1] • volume`
(`MeasureTheory.Measure.eq_smul_volume_of_map_coe_conv_eq_self`).

Limits of translates of the renewal measure are harmonic and uniformly locally bounded, so this
theorem identifies them with multiples of Lebesgue measure. It is the step of Feller's proof of
Blackwell's renewal theorem for nonlattice laws that uses the nonlattice hypothesis.

Since `F` is nonlattice, the support of its image in `ℝ` generates a dense subgroup of `ℝ`
(`MeasureTheory.Measure.dense_addSubgroupClosure_support_map_coe_iff`). The theorem is then the
Choquet–Deny theorem on `ℝ`, `MeasureTheory.Measure.eq_smul_volume_of_conv_eq_self`, which holds
for every real law whose support generates a dense subgroup. No mean or moment assumption is made
on `F`, and `η` may have atoms a priori.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, §XI.2.
* G. Choquet and J. Deny, *Sur l'équation de convolution μ = μ ⋆ σ*, C. R. Acad. Sci. Paris
  250 (1960), 799–801.
-/

public section

open Set
open scoped NNReal

namespace MeasureTheory.Measure

/-- **Rigidity of harmonic measures.** Let `μ` be a nonlattice probability law on `ℝ≥0`. A measure
`η` on `ℝ` with `μ ∗ η = η`, the law `μ` being taken on `ℝ`, and with uniformly bounded mass on
the unit windows `[a, a + 1]`, is the multiple `η (0, 1] • volume` of Lebesgue measure. -/
theorem eq_smul_volume_of_map_coe_conv_eq_self {μ : Measure ℝ≥0} [IsProbabilityMeasure μ]
    {η : Measure ℝ} {C : ℝ≥0} (hμ : ¬ μ.IsLattice) (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (hη : μ.map ((↑) : ℝ≥0 → ℝ) ∗ η = η) :
    η = η (Ioc 0 1) • volume :=
  eq_smul_volume_of_conv_eq_self (dense_addSubgroupClosure_support_map_coe_iff.2 hμ) hC hη

end MeasureTheory.Measure
