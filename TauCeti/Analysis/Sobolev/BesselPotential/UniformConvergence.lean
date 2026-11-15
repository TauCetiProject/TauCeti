/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Convergence in `H^s` and uniform convergence of continuous representatives

Let `E` be a finite-dimensional real inner product space of dimension `n`, and `s > n / 2`. The
quantitative Sobolev embedding `H^s ⊆ L^∞` bounds an `L²` function `u ∈ H^s` almost everywhere by
`C ‖u‖_{H^s}` (`TemperedDistribution.exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace`).
For a continuous representative the bound holds at every point, because a closed set of full
measure is everything
(`TemperedDistribution.exists_forall_norm_le_mul_norm_toBesselPotentialSpace_of_ae_eq`):

`sup_x |f(x)| ≤ C ‖u‖_{H^s}`,  `f` continuous, `u = f` almost everywhere.

Consequently a family of continuous functions whose differences with a continuous function `f`
tend to zero in `H^s` converges to `f` uniformly on `E`
(`TemperedDistribution.tendstoUniformly_of_tendsto_toBesselPotentialSpace`). This is how
convergence in a Sobolev space of order above half the dimension is turned into convergence of
the pointwise values of the continuous representatives, for instance in order to pass to the limit
in pointwise identities between them.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., §9.3.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology
open scoped SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Sobolev embedding `H^s ⊆ C_b` for continuous representatives**, `s > dim E / 2`. There
is a constant `C`, depending only on `s` and `E`, such that every continuous function `f` which
agrees almost everywhere with an `L²` function `u ∈ H^s` satisfies `‖f x‖ ≤ C ‖u‖_{H^s}` at every
point `x`. -/
theorem exists_forall_norm_le_mul_norm_toBesselPotentialSpace_of_ae_eq {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F)))
      {f : E → F}, Continuous f → u =ᵐ[volume] f →
        ∀ x, ‖f x‖ ≤ C * ‖hu.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC, hae⟩ := exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (F := F) hs
  refine ⟨C, hC, fun {u} hu {f} hf huf x ↦ ?_⟩
  -- The bound holds on a set of full measure, which is dense, and on a closed set, since `f` is
  -- continuous; so it holds everywhere.
  have hfae : ∀ᵐ y ∂volume, ‖f y‖ ≤ C * ‖hu.toBesselPotentialSpace‖ := by
    filter_upwards [hae hu, huf] with y hy hy'
    rwa [← hy']
  have hclosed : IsClosed {y | ‖f y‖ ≤ C * ‖hu.toBesselPotentialSpace‖} :=
    isClosed_le (by fun_prop) continuous_const
  have huniv := (Measure.dense_of_ae hfae).closure_eq
  rw [hclosed.closure_eq] at huniv
  exact Set.eq_univ_iff_forall.1 huniv x

/-- **Convergence in `H^s` implies uniform convergence**, `s > dim E / 2`. Let `fs i` and `f` be
continuous functions such that each difference `fs i - f` agrees almost everywhere with an `L²`
function `u i ∈ H^s`. If `u i → 0` in `H^s`, then `fs i → f` uniformly on `E`. -/
theorem tendstoUniformly_of_tendsto_toBesselPotentialSpace {ι : Type*} {l : Filter ι} {s : ℝ}
    (hs : finrank ℝ E < 2 * s) {fs : ι → E → F} {f : E → F} (hfs : ∀ i, Continuous (fs i))
    (hf : Continuous f) {u : ι → Lp F 2 (volume : Measure E)}
    (hu : ∀ i, MemSobolev s 2 (u i : 𝓢'(E, F))) (hae : ∀ i, u i =ᵐ[volume] fs i - f)
    (h : Tendsto (fun i ↦ (hu i).toBesselPotentialSpace) l (𝓝 0)) :
    TendstoUniformly fs f l := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_forall_norm_le_mul_norm_toBesselPotentialSpace_of_ae_eq (F := F) hs
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := by positivity
  filter_upwards [(tendsto_zero_iff_norm_tendsto_zero.1 h).eventually (gt_mem_nhds hδ)]
    with i hi x
  have hx := hbound (hu i) ((hfs i).sub hf) (hae i) x
  rw [dist_eq_norm', ← Pi.sub_apply]
  calc ‖(fs i - f) x‖ ≤ C * ‖(hu i).toBesselPotentialSpace‖ := hx
    _ ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

end TemperedDistribution
