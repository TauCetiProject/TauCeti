/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Lp
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich.BesselPotential

/-!
# The Rellich–Kondrachov theorem for the spaces `H^{s,p}` of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`), which exists on every compact boundaryless manifold
(`TauCeti.exists_squareChartPartition`), with its Bessel-potential spaces `H^{s,p}` of real
functionals on the bundle tests of `V` (`TauCeti.SquareChartPartition.besselPotentialSpace`). Let
`n` be the dimension of the model space `E`.

This file proves compactness statements for the inclusions between these spaces.

* For `p = 2` and real orders `r < s`, the inclusion `H^{s,2} ⊆ H^{r,2}` is compact
  (`TauCeti.SquareChartPartition.isCompactOperator_besselPotentialInclusion_two`). This is the
  Rellich theorem for the Sobolev spaces `H^s` of `A`
  (`TauCeti.SquareChartPartition.isCompactOperator_inclusion`), transported along the isomorphisms
  `H^{s,2} ≃ H^s` (`TauCeti.SquareChartPartition.besselPotentialSpaceTwoEquivSobolevSpace`).
* **Rellich–Kondrachov.** Let `1 < p ≤ 2 ≤ q`, `δ > 0` with `1 / q = 1 / p - δ / n`, and `r < s`.
  Then the Sobolev embedding `H^{s + δ, p} ⊆ H^{s, q}`
  (`TauCeti.SquareChartPartition.besselPotentialSobolevEmbedding`) followed by the inclusion
  `H^{s, q} ⊆ H^{r, q}` is compact
  (`isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding`).
  In other words, the inclusion of `H^{s + δ, p}` into `H^{r, q}` is compact as soon as the loss
  of order `s + δ - r` exceeds `n (1 / p - 1 / q)`.

The second statement routes the inclusion through the exponent `2`. Split `δ = δ₁ + δ₂` with
`1 / 2 = 1 / p - δ₁ / n` and `1 / q = 1 / 2 - δ₂ / n`. The inclusion factors as

`H^{s + δ, p} ⊆ H^{s + δ₂, 2} ⊆ H^{r + δ₂, 2} ⊆ H^{r, q}`,

where the outer maps are Sobolev embeddings (or identities, when `p = 2` or `q = 2`) and the
middle one is compact by the case `p = 2`. Since every element of these spaces is determined by the
functional it represents (`TauCeti.SquareChartPartition.besselPotentialToDistribution_injective`),
the factorization only needs to be checked on represented functionals. The compactness of
`H^{s, p} ⊆ H^{r, q}` when `p` and `q` lie on the same side of `2`, other than `p = q = 2`, is not
proved here; it needs a Rellich theorem for the Euclidean spaces `H^{s,p}(E, ℂ)` with a common
compact support and `p ≠ 2`.

## Main results

* `TauCeti.SquareChartPartition.isCompactOperator_besselPotentialInclusion_two`: the Rellich
  theorem `H^{s,2} ⊆ H^{r,2}` for `r < s`.
* `isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding`: the
  Rellich–Kondrachov theorem `H^{s + δ, p} ⊆ H^{r, q}` for `1 < p ≤ 2 ≤ q` and `r < s`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003,
  Theorem 6.3 (the Rellich–Kondrachov theorem).
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts).
-/

public section

noncomputable section

open scoped Manifold ContDiff ENNReal NNReal

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

/-- **The Rellich theorem for `p = 2`.** For real orders `r < s`, the inclusion `H^{s,2} ⊆ H^{r,2}`
of the Bessel-potential spaces of a square chart partition is a compact operator. -/
theorem isCompactOperator_besselPotentialInclusion_two {r s : ℝ} (h : r < s) :
    IsCompactOperator (A.besselPotentialInclusion (p := 2) h.le) := by
  have heq : A.besselPotentialInclusion (p := 2) h.le =
      (A.besselPotentialSpaceTwoEquivSobolevSpace r).symm.toContinuousLinearMap ∘L
        A.inclusion h.le ∘L (A.besselPotentialSpaceTwoEquivSobolevSpace s).toContinuousLinearMap :=
    ContinuousLinearMap.ext fun u ↦ Subtype.ext <| funext fun k ↦ by simp
  rw [heq]
  exact ((A.isCompactOperator_inclusion h).comp_clm
    (A.besselPotentialSpaceTwoEquivSobolevSpace s).toContinuousLinearMap).clm_comp
    (A.besselPotentialSpaceTwoEquivSobolevSpace r).symm.toContinuousLinearMap

/-- A bounded operator `H^{t' + δ, p} → H^{t', q}` representing the same functionals, for `δ ≥ 0`
and `1 / q = 1 / p - δ / n`: the Sobolev embedding for `δ > 0`, and the identity for `δ = 0`,
where `q = p`. -/
private theorem exists_besselPotentialToDistribution_eq {δ t t' : ℝ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hδ : 0 ≤ δ) (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) (ht : t' + δ = t) :
    ∃ L : A.besselPotentialSpace t p →L[ℝ] A.besselPotentialSpace t' q,
      ∀ u, A.besselPotentialToDistribution t' q (L u) = A.besselPotentialToDistribution t p u := by
  subst ht
  rcases hδ.eq_or_lt with rfl | hδ
  · obtain rfl : q = p := by
      rwa [zero_div, sub_zero, inv_inj, NNReal.coe_inj] at hpq
    exact ⟨A.besselPotentialInclusion (add_zero t').ge, fun u ↦ by simp⟩
  · exact ⟨A.besselPotentialSobolevEmbedding t' hδ hp hpq, fun u ↦ by simp⟩

/-- **The Rellich–Kondrachov theorem across the exponent `2`.** Let `1 < p ≤ 2 ≤ q`, `δ > 0` with
`1 / q = 1 / p - δ / n`, where `n` is the dimension of `E`, and let `r < s`. Then the Sobolev
embedding `H^{s + δ, p} ⊆ H^{s, q}` of the Bessel-potential spaces of a square chart partition,
followed by the inclusion `H^{s, q} ⊆ H^{r, q}`, is a compact operator. -/
theorem isCompactOperator_besselPotentialInclusion_comp_besselPotentialSobolevEmbedding
    {δ r s : ℝ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hδ : 0 < δ)
    (hp : 1 < p) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) (hp2 : p ≤ 2)
    (hq2 : 2 ≤ q) (h : r < s) :
    IsCompactOperator
      (A.besselPotentialInclusion h.le ∘L A.besselPotentialSobolevEmbedding s hδ hp hpq) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hp2' : (2 : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := inv_anti₀ (by positivity) (by exact_mod_cast hp2)
  have hq2' : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hq2)
  -- Split `δ = δ₁ + δ₂`, the losses of order from `p` to `2` and from `2` to `q`.
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, h₁, h₂, rfl⟩ : ∃ δ₁ δ₂ : ℝ, 0 ≤ δ₁ ∧ 0 ≤ δ₂ ∧
      ((2 : ℝ≥0) : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ₁ / n ∧ (q : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - δ₂ / n ∧
      δ = δ₁ + δ₂ := by
    rcases eq_or_ne n 0 with hn | hn
    · -- In dimension `0`, the relation forces `p = q = 2`.
      rw [hn, div_zero, sub_zero] at hpq
      exact ⟨δ, 0, hδ.le, le_rfl, by push_cast; rw [hn, div_zero]; linarith,
        by push_cast; rw [hn, div_zero]; linarith, by ring⟩
    · have hδn : δ / n = (p : ℝ)⁻¹ - (q : ℝ)⁻¹ := by linarith
      have hn0 : 0 < n := lt_of_le_of_ne (Nat.cast_nonneg _) hn.symm
      refine ⟨n * ((p : ℝ)⁻¹ - 2⁻¹), n * (2⁻¹ - (q : ℝ)⁻¹), by nlinarith, by nlinarith, ?_, ?_, ?_⟩
      · push_cast; field_simp; ring
      · push_cast; field_simp; ring
      · rw [div_eq_iff hn] at hδn; rw [hδn]; ring
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨L₁, hL₁⟩ := A.exists_besselPotentialToDistribution_eq (t := s + (δ₁ + δ₂))
    (t' := s + δ₂) hδ₁ hp h₁ (by ring)
  obtain ⟨L₂, hL₂⟩ := A.exists_besselPotentialToDistribution_eq (t' := r) hδ₂
    (by norm_num) h₂ rfl
  -- The middle exponent is the coercion of `(2 : ℝ≥0)`, equal to `(2 : ℝ≥0∞)` only
  -- propositionally, so the case `p = 2` is applied after generalizing the exponent.
  have hK : IsCompactOperator
      (A.besselPotentialInclusion (p := ((2 : ℝ≥0) : ℝ≥0∞)) (by linarith : r + δ₂ ≤ s + δ₂)) := by
    have key : ∀ {p₂ : ℝ≥0∞} [Fact (1 ≤ p₂)], p₂ = 2 → IsCompactOperator
        (A.besselPotentialInclusion (p := p₂) (by linarith : r + δ₂ ≤ s + δ₂)) := by
      rintro p₂ _ rfl
      exact A.isCompactOperator_besselPotentialInclusion_two (by linarith)
    exact key (by norm_num)
  have heq : A.besselPotentialInclusion h.le ∘L A.besselPotentialSobolevEmbedding s hδ hp hpq =
      L₂ ∘L A.besselPotentialInclusion (by linarith : r + δ₂ ≤ s + δ₂) ∘L L₁ :=
    ContinuousLinearMap.ext fun u ↦ A.besselPotentialToDistribution_injective <| by
      simp only [ContinuousLinearMap.comp_apply, hL₁, hL₂,
        besselPotentialToDistribution_besselPotentialInclusion,
        besselPotentialToDistribution_besselPotentialSobolevEmbedding]
  rw [heq]
  exact (hK.comp_clm L₁).clm_comp L₂

end SquareChartPartition

end TauCeti
