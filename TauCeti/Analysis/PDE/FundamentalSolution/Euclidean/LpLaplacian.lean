/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakLaplacianLp
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
import TauCeti.Analysis.Distribution.Dirac
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The Newtonian singularity has no Laplacian in `Lᵖ`

For `n = 1` or `n ≥ 3` the Newtonian kernel `Gₙ` satisfies `-Δ Gₙ = δ₀` in the sense of
distributions (`TauCeti.integral_laplacian_mul_newtonianKernel`). This file draws the consequence
for the Laplacian on `Lᵖ(ℝⁿ)` in the sense of distributions (`TauCeti.weakLaplacianLp`): an `Lᵖ`
function which agrees near a point `a` with a nonzero multiple `c Gₙ(· - a)` of the kernel with pole
`a` is not in its domain
(`TauCeti.notMem_domain_weakLaplacianLp_of_ae_eq_mul_newtonianKernel_sub`). Its distributional
Laplacian is `-c δₐ` near `a`, and a nonzero multiple of a Dirac mass is not a locally integrable
function (`TauCeti.eq_zero_of_integral_contDiff_smul_eq_apply_smul`).

Such functions exist in `Lᵖ` whenever the singularity is `p`-integrable: a bounded cutoff `χ`
with bounded support makes `χ Gₙ(· - a)` an `Lᵖ` function as soon as `(n - 2) p < n`
(`TauCeti.memLp_mul_newtonianKernel_sub`), for instance for `p < 3` in dimension three, where
`G₃(x) = 1 / (4π ‖x‖)`, and for every finite `p` in dimension one. Taking `χ` equal to `1` near
`a`, the two results together exhibit an element of `Lᵖ(ℝⁿ)` outside the domain of the `Lᵖ`
Laplacian, which is the domain of the generator of the heat semigroup on `Lᵖ(ℝⁿ)`
(`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`): for such `p` that domain is a proper
subspace.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1 (the fundamental solution of
  Laplace's equation).
-/

public section

namespace TauCeti

open MeasureTheory Set Topology

open scoped ENNReal Distributions Laplacian

variable {n : ℕ}

/-- **An `Lᵖ` function with a Newtonian singularity has no Laplacian in `Lᵖ`.** For `n = 1` or
`n ≥ 3`, if `f ∈ Lᵖ(ℝⁿ)` agrees almost everywhere near `a` with `c Gₙ(· - a)` for some `c ≠ 0`,
then `f` is not in the domain of the Laplacian on `Lᵖ` in the sense of distributions: near `a`
its distributional Laplacian is `-c δₐ`. -/
theorem notMem_domain_weakLaplacianLp_of_ae_eq_mul_newtonianKernel_sub (hn : n ≠ 2)
    (hn0 : n ≠ 0) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin n)))} {a : EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ∈ 𝓝 a) {c : ℝ} (hc : c ≠ 0)
    (hf : ∀ᵐ x, x ∈ U → f x = c * newtonianKernel n (x - a)) :
    f ∉ (weakLaplacianLp (EuclideanSpace ℝ (Fin n)) ℝ p).domain := by
  intro hdom
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨g, hg⟩ := mem_domain_weakLaplacianLp_iff.1 hdom
  have hgU : LocallyIntegrableOn g U volume :=
    ((Lp.memLp g).locallyIntegrable Fact.out).locallyIntegrableOn U
  refine neg_ne_zero.2 hc
    (eq_zero_of_integral_contDiff_smul_eq_apply_smul hU hgU fun φ hφ hφc hφU ↦ ?_)
  have hΔ : ∫ x, Δ φ x * f x = ∫ x, φ x * g x := hg ⟨φ, hφ, hφc, subset_univ _⟩
  calc ∫ x, φ x • g x = ∫ x, c * (Δ φ x * newtonianKernel n (x - a)) := by
        simp only [smul_eq_mul]
        rw [← hΔ]
        refine integral_congr_ae ?_
        filter_upwards [hf] with x hx
        by_cases hxU : x ∈ U
        · rw [hx hxU]
          ring
        · rw [laplacian_of_notMem_tsupport fun h ↦ hxU (hφU h)]
          ring
    _ = φ a • -c := by
        rw [integral_const_mul, integral_laplacian_mul_newtonianKernel_sub hn hn0
          (hφ.of_le (by simp)) hφc, smul_eq_mul]
        ring

/-- **A cutoff Newtonian kernel lies in `Lᵖ`.** If `χ` is bounded, almost everywhere strongly
measurable and has bounded support, and `(n - 2) p < n`, then `χ Gₙ(· - a)` lies in `Lᵖ(ℝⁿ)`. -/
theorem memLp_mul_newtonianKernel_sub {p : ℝ≥0∞} (hp : p ≠ ∞)
    (hnp : ((n : ℝ) - 2) * p.toReal < n) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχm : AEStronglyMeasurable χ volume) {M : ℝ} (hχM : ∀ x, ‖χ x‖ ≤ M)
    (hχs : Bornology.IsBounded (Function.support χ)) (a : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x ↦ χ x * newtonianKernel n (x - a)) p volume := by
  obtain ⟨R, hR⟩ := hχs.subset_closedBall 0
  -- The kernel is a constant multiple of `‖y‖ ^ (2 - n)`; the value of the constant is irrelevant.
  obtain ⟨k, hk⟩ : ∃ k : ℝ, ∀ y, ‖newtonianKernel n y‖ = k * ‖y‖ ^ (2 - (n : ℝ)) :=
    ⟨_, fun y ↦ by
      rw [newtonianKernel_def, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]⟩
  have hind : (fun x ↦ χ x * newtonianKernel n (x - a)) =
      (Metric.closedBall 0 R).indicator fun x ↦ χ x * newtonianKernel n (x - a) := by
    refine (indicator_eq_self.2 fun x hx ↦ hR ?_).symm
    exact (Function.mem_support.2 fun h ↦ hx (by simp [h]))
  rw [hind, memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet]
  refine Metric.isBounded_closedBall.memLp_of_ae_norm_le_mul_norm_sub_rpow (s := 2 - n)
    (C := M * k) hp ?_ a ?_ (ae_of_all _ fun x ↦ ?_)
  · rw [finrank_euclideanSpace_fin]
    linarith
  · exact (hχm.mul ((measurable_newtonianKernel n).comp
      (measurable_id.sub_const a)).aestronglyMeasurable).restrict
  · rw [norm_sub_rev, mul_assoc, ← hk, norm_mul]
    exact mul_le_mul_of_nonneg_right (hχM x) (norm_nonneg _)

end TauCeti
