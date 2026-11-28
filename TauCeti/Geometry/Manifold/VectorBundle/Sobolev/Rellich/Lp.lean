/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Lp
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
import TauCeti.Analysis.Normed.Operator.Compact.Pi
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich.Lp

/-!
# The Rellich–Kondrachov theorem for the spaces `H^{s,p}` of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`), which exists on every compact boundaryless manifold
(`TauCeti.exists_squareChartPartition`), with its Bessel-potential spaces `H^{s,p}` of real
functionals on the bundle tests of `V` (`TauCeti.SquareChartPartition.besselPotentialSpace`). Let
`n` be the dimension of the model space `E`.

This file proves compactness statements for the inclusions between these spaces.

* **Rellich.** For `1 < p < ∞` and real orders `r < s`, the inclusion `H^{s,p} ⊆ H^{r,p}` is
  compact (`TauCeti.SquareChartPartition.isCompactOperator_besselPotentialInclusion`).
* **Ehrling's inequality.** For `1 < p < ∞`, `t ≤ r < s` and every `ε > 0` there is `C` with
  `‖u‖_{H^{r,p}} ≤ ε ‖u‖_{H^{s,p}} + C ‖u‖_{H^{t,p}}` for all `u ∈ H^{s,p}`
  (`TauCeti.SquareChartPartition.exists_norm_besselPotentialInclusion_le_mul_norm_add_mul_norm`).
* **Rellich–Kondrachov.** Let `1 < p`, `δ > 0` with `1 / q = 1 / p - δ / n`, and `r < s`. Then
  the Sobolev embedding `H^{s + δ, p} ⊆ H^{s, q}`
  (`TauCeti.SquareChartPartition.besselPotentialSobolevEmbedding`) followed by the inclusion
  `H^{s, q} ⊆ H^{r, q}` is compact
  (`isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding`).
  In other words, for `p ≤ q` the inclusion of `H^{s + δ, p}` into `H^{r, q}` is compact as soon
  as the loss of order `s + δ - r` exceeds `n (1 / p - 1 / q)`.

An element of `H^{s,p}` is the tuple of the localizations `χᵢ Tᵢⱼ` of a functional `T`, and the
localization in the `i`-th chart is supported in the compact set `A.chartSupport i`. A Schwartz
function `φ` equal to `1` on all of these finitely many compact sets therefore fixes every
component (`TauCeti.SquareChartPartition.smulLeftCLMOfOneLt_apply_of_eqOn_one`), so in each
component the inclusion is the operator `u ↦ φ u` from `H^{s,p}(E, ℂ)` to `H^{r,p}(E, ℂ)`,
which is compact by the Euclidean Rellich theorem for a common compact support
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt`). A map into the finite
product of copies of `H^{r,p}(E, ℂ)` with compact components is compact, and so is its
corestriction to the closed subspace `H^{r,p}`. The Rellich–Kondrachov theorem follows by applying
this at the exponent `q`, after the Sobolev embedding.

The case `q < p` on a compact base, where every loss of order `s - r > 0` gives a compact map
`H^{s,p} → H^{r,q}`, is not treated here: it needs the inclusion `H^{s,p} ⊆ H^{s,q}` for a common
compact support, which is not available for the Euclidean spaces.

## Main results

* `TauCeti.SquareChartPartition.isCompactOperator_besselPotentialInclusion`: the Rellich theorem
  `H^{s,p} ⊆ H^{r,p}` for `1 < p < ∞` and `r < s`.
* `TauCeti.SquareChartPartition.exists_norm_besselPotentialInclusion_le_mul_norm_add_mul_norm`:
  Ehrling's inequality.
* `isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding`: the
  Rellich–Kondrachov theorem `H^{s + δ, p} ⊆ H^{r, q}` for `1 < p` and `r < s`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003,
  Theorem 6.3 (the Rellich–Kondrachov theorem).
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal NNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (Bundle.TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

/-- **Localizations are fixed by cutoffs equal to one on the chart supports.** For `1 < p < ∞`, if
a Schwartz function `φ` equals `1` on the compact set `A.chartSupport i`, then multiplication by
`φ` fixes every component, in the `i`-th chart, of an element of the Bessel-potential space
`H^{s,p}` of `A`. -/
theorem smulLeftCLMOfOneLt_apply_of_eqOn_one {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {φ : 𝓢(E, ℂ)} {i : ι}
    (hφ : EqOn φ 1 (A.chartSupport i)) (u : A.besselPotentialSpace s p)
    (j : Fin (Module.finrank ℝ F)) :
    BesselPotentialSpace.smulLeftCLMOfOneLt hp hp_top φ (u.val (i, j)) = u.val (i, j) :=
  BesselPotentialSpace.ext <| by
    rw [BesselPotentialSpace.toDistr_smulLeftCLMOfOneLt,
      ← A.localization_besselPotentialToDistribution u (i, j), localization_apply]
    exact Distribution.smulLeftCLM_cutoffTempered_of_eqOn_one _ _ φ.hasTemperateGrowth
      (hφ.mono (A.tsupport_chartCutoff_subset i))

/-- **The Rellich theorem.** For `1 < p < ∞` and real orders `r < s`, the inclusion
`H^{s,p} ⊆ H^{r,p}` of the Bessel-potential spaces of a square chart partition is a compact
operator. -/
theorem isCompactOperator_besselPotentialInclusion {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {r s : ℝ} (h : r < s) :
    IsCompactOperator (A.besselPotentialInclusion (p := p) h.le) := by
  -- A Schwartz function `φ` equal to `1` on the finitely many compact chart supports.
  obtain ⟨φ, -, -, hφ1⟩ :=
    (isCompact_iUnion fun i ↦ (A.chartSupport i).isCompact).exists_schwartzMap_cutoff isOpen_univ
      (subset_univ _)
  have hφ (i : ι) : EqOn φ 1 (A.chartSupport i) := fun y hy ↦
    hφ1.self_of_nhdsSet y (mem_iUnion_of_mem i hy)
  -- In every component, the inclusion is `w ↦ φ w`, which is compact from `H^{s,p}` to
  -- `H^{r,p}`; so it is compact into the product, and then into the closed subspace.
  have hg : IsCompactOperator fun u : A.besselPotentialSpace s p ↦
      fun k ↦ (BesselPotentialSpace.inclusion h.le ∘L
        BesselPotentialSpace.smulLeftCLMOfOneLt hp hp_top φ) (u.val k) :=
    IsCompactOperator.pi fun k ↦
      (BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLMOfOneLt hp hp_top φ
        h).comp_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ H^{s, p}(E, ℂ)) k ∘L
          (A.besselPotentialSpace s p).subtypeL)
  have heq : ∀ u, (fun k ↦ (BesselPotentialSpace.inclusion h.le ∘L
      BesselPotentialSpace.smulLeftCLMOfOneLt hp hp_top φ) (u.val k)) =
        (A.besselPotentialInclusion h.le u).val := fun u ↦ funext fun k ↦ by
    rw [ContinuousLinearMap.comp_apply,
      A.smulLeftCLMOfOneLt_apply_of_eqOn_one hp hp_top (hφ k.1) u k.2,
      besselPotentialInclusion_apply]
  have hcod := hg.codRestrict (V := A.besselPotentialSpace r p)
    (fun u ↦ by rw [heq]; exact (A.besselPotentialInclusion h.le u).property)
    (A.isClosed_besselPotentialSpace r p)
  convert hcod using 1
  exact funext fun u ↦ Subtype.ext (heq u).symm

/-- **Ehrling's inequality.** For `1 < p < ∞`, real orders `t ≤ r < s` and `ε > 0` there is
`C ≥ 0` with `‖u‖_{H^{r,p}} ≤ ε ‖u‖_{H^{s,p}} + C ‖u‖_{H^{t,p}}` for every `u` in the
Bessel-potential space `H^{s,p}` of a square chart partition. -/
theorem exists_norm_besselPotentialInclusion_le_mul_norm_add_mul_norm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {r s t : ℝ} (htr : t ≤ r) (hrs : r < s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : A.besselPotentialSpace s p,
      ‖A.besselPotentialInclusion hrs.le u‖ ≤
        ε * ‖u‖ + C * ‖A.besselPotentialInclusion (htr.trans hrs.le) u‖ := by
  obtain ⟨C, hC, hCu⟩ := (A.isCompactOperator_besselPotentialInclusion hp hp_top hrs)
    |>.exists_norm_le_mul_norm_add_mul_norm
      (j := (A.besselPotentialInclusion htr : A.besselPotentialSpace r p →L[ℝ] _))
      (A.besselPotentialInclusion_injective htr) hε
  exact ⟨C, hC, fun u ↦ by simpa using hCu u⟩

/-- **The Rellich–Kondrachov theorem.** Let `1 < p`, `δ > 0` with `1 / q = 1 / p - δ / n`, where
`n` is the dimension of `E`, and let `r < s`. Then the Sobolev embedding `H^{s + δ, p} ⊆ H^{s, q}`
of the Bessel-potential spaces of a square chart partition, followed by the inclusion
`H^{s, q} ⊆ H^{r, q}`, is a compact operator. -/
theorem isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding
    {δ r s : ℝ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hδ : 0 < δ)
    (hp : 1 < p) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) (h : r < s) :
    IsCompactOperator
      (A.besselPotentialInclusion h.le ∘L A.besselPotentialSobolevEmbedding s hδ hp hpq) := by
  -- The exponent `q` is at least `p`, since `1 / q ≤ 1 / p`.
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (ENNReal.coe_le_coe.1 (Fact.out : 1 ≤ (q : ℝ≥0∞)))
  have hpq' : (q : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := by rw [hpq]; exact sub_le_self _ (by positivity)
  have hq : (1 : ℝ≥0∞) < q := by
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp
    have : (p : ℝ) ≤ q := (inv_le_inv₀ (by linarith) (by linarith)).1 hpq'
    exact_mod_cast hp'.trans_le this
  exact (A.isCompactOperator_besselPotentialInclusion hq ENNReal.coe_ne_top h).comp_clm _

end SquareChartPartition

end TauCeti
