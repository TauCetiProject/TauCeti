/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
public import TauCeti.Analysis.Normed.Operator.Compact.Domination
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.Data.ENNReal.Inv
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Embedding

/-!
# Rellich–Kondrachov compactness and Ehrling's inequality for Sobolev sections of a vector bundle

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p ≤ ∞` and every order
`k`, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` of `TauCeti.SectionChartData.lowerOrderL` is a
compact operator (`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`). The endpoint `p = ∞`
is included: smooth sections are not dense in `W^{k+1,∞}(V)`, but neither ingredient below needs
that density. Composing these, the inclusion `W^{k+d+1,p}(V) → W^{k,p}(V)` is compact as well.

Together with the injectivity of the chart data (`TauCeti.SectionChartData.chartValuesL`), which
forget all derivatives, compactness gives **Ehrling's inequality**: the `W^{k,p}` norm of a section
is bounded by an arbitrarily small multiple of its `W^{k+d+1,p}` norm plus a multiple of its `Lᵖ`
norm (`TauCeti.SobolevSection.exists_norm_lowerOrdersL_le`). This is how the intermediate norm in an
a priori estimate on a compact base is replaced by the `Lᵖ` norm.

The local input is Rellich compactness on relatively compact subdomains,
`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, which holds for every `1 ≤ p ≤ ∞`. It does
not apply directly to the chart images `A.image j`, whose closures need not lie inside an open set
on which the chart data are controlled. Instead the chart data in chart `j` are transferred from
the other charts with `TauCeti.FiniteBundleAtlas.transferL`
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`), a change of variables in `W^{k,p}` that is
also available for every `1 ≤ p ≤ ∞` (`TauCeti.Wkp.compL`).

Shrink the chart domains to open sets `D i` with `closure (D i) ⊆ A.dom i` that still cover `M`.
The chart image `A.image j` is covered by the finitely many pieces `A.chart j '' (A.dom j ∩ D i)`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover`). On each piece the chart-`j` data are
transferred from the chart-`i` data restricted to `A.chart i '' D i`, which has compact closure
inside `A.image i`, so the piece data depend compactly on the section from order `k + 1` to order
`k`. The finite-cover norm estimate and domination by these compact restrictions give compactness
on `A.image j` (`IsCompactOperator.of_norm_le_mul_sum`), and compactness of every chart component
gives compactness into the Sobolev sections, which are closed in the product of the chartwise
Sobolev spaces (`TauCeti.SectionChartData.isCompactOperator_of_forall_apply`).

Changing the exponent gives the Rellich–Kondrachov theorem. Let `n ≥ 2` be the dimension, `r ≥ 1`
and `1 ≤ q < ∞` with `1/p < 1/q + r/n`. Then `W^{k+r,p}(V) → W^{k,q}(V)` is compact
(`TauCeti.SobolevSection.exists_isCompactOperator_of_inv_lt_inv_add`): for `rp < n` this is every
`q` strictly below the Sobolev exponent `np/(n - rp)`, and for `rp ≥ n` every finite `q`. For
`r = 1` and `p < q`, first lower `p` if necessary, so that its Sobolev exponent `s`,
`1/s = 1/p - 1/n`, is finite and still satisfies `q < s`. The embedding into `W^{k,s}(V)`
(`TauCeti.SobolevSection.exists_sobolevEmbeddingL`) is bounded, and lowered to `W^{k,p}(V)` it is
the compact Rellich inclusion. Since `1/q = (1 - θ)/p + θ/s` with `0 < θ < 1`, the `W^{k,q}` norm is
at most the `W^{k,p}` norm to the power `1 - θ` times the `W^{k,s}` norm to the power `θ`
(`TauCeti.SectionChartData.norm_ofExponentLEL_le_norm_rpow_mul_norm_rpow`), so compactness passes
to `W^{k,q}(V)` (`IsCompactOperator.of_norm_le_mul_rpow_mul_rpow`). For `q ≤ p` the Rellich
inclusion at the exponent `q` suffices (`TauCeti.SobolevSection.exists_isCompactOperator_of_le`).
Each further order `r` first applies one Sobolev embedding and then the case `r - 1`.

## Main results

* `TauCeti.SobolevSection.isCompactOperator_lowerOrdersL_comp_ofExponentLEL`:
  `W^{k+d+1,q}(V) → W^{k,p}(V)` is compact for `1 ≤ p ≤ q ≤ ∞`.
* `TauCeti.SectionChartData.isCompactOperator_of_forall_apply`: a map into the Sobolev sections is
  a compact operator as soon as all its chart components are.
* `TauCeti.SectionChartData.isCompactOperator_lowerOrdersL`,
  `TauCeti.SectionChartData.exists_norm_lowerOrdersL_le`: for general chart data, Rellich for any
  loss of derivatives and Ehrling's inequality follow from one-step compactness; they serve bases
  with and without boundary.
* `TauCeti.SobolevSection.isCompactOperator_lowerOrderL`: **Rellich's theorem** for Sobolev
  sections, `W^{k+1,p}(V) → W^{k,p}(V)` is compact.
* `TauCeti.SobolevSection.isCompactOperator_lowerOrdersL`: `W^{k+d+1,p}(V) → W^{k,p}(V)` is compact.
* `TauCeti.SobolevSection.isCompactOperator_lowerToZeroL`: `W^{k+1,p}(V) → W^{0,p}(V)` is compact.
* `TauCeti.SobolevSection.exists_norm_lowerOrdersL_le`: **Ehrling's inequality**
  `‖w‖_{W^{k,p}} ≤ ε ‖w‖_{W^{k+d+1,p}} + C_ε ‖w‖_{Lᵖ}`.
* `TauCeti.SobolevSection.exists_isCompactOperator_of_le`: `W^{k+1,p}(V) → W^{k,q}(V)` is compact
  for `q ≤ p`, including infinite exponents.
* `TauCeti.SobolevSection.exists_isCompactOperator_of_inv_lt_inv_add`: **the Rellich–Kondrachov
  theorem** for Sobolev sections, `W^{k+r,p}(V) → W^{k,q}(V)` is compact for `1/p < 1/q + r/n`,
  `q < ∞`, in dimension `n ≥ 2`.
* `TauCeti.SobolevSection.exists_isCompactOperator_of_finrank_le`: `W^{k+1,p}(V) → W^{k,q}(V)` is
  compact for `p ≥ n` and every finite `q`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, Theorem 2.6.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press (2003), Theorem 6.3
  (the Rellich–Kondrachov theorem, with the interpolation argument for the intermediate
  exponents).
* G. Ehrling, *On a type of eigenvalue problem for certain elliptic differential operators*,
  Math. Scand. **2** (1954), 267–285.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

section Components

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] {C : SectionChartData E F S}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Compactness into Sobolev sections is componentwise.** If the chart transitions carry null
sets to null sets, a map into the Sobolev sections is a compact operator as soon as all its chart
components are. -/
theorem SectionChartData.isCompactOperator_of_forall_apply (hC : C.AETransition μ) {X : Type*}
    [TopologicalSpace X] [AddCommMonoid X] {f : X → C.sobolevSections μ p k}
    (hf : ∀ i m, IsCompactOperator fun x ↦ (f x : C.SobolevData μ p k) i m) :
    IsCompactOperator f :=
  (IsCompactOperator.pi fun i ↦ IsCompactOperator.pi fun m ↦ hf i m).codRestrict
    (fun x ↦ (f x).property) (isClosed_sobolevSections hC)

/-- **Rellich for any loss of derivatives.** If the inclusion of order `k + d + 1` into order
`k + d` is compact, so is the inclusion of order `k + d + 1` into order `k`. -/
theorem SectionChartData.isCompactOperator_lowerOrdersL {d : ℕ}
    (h : IsCompactOperator (C.lowerOrderL μ p (k + d))) :
    IsCompactOperator (C.lowerOrdersL μ p k (d + 1)) := by
  rw [lowerOrdersL_succ]
  exact h.clm_comp _

/-- **Ehrling's inequality for Sobolev sections.** If the inclusion `W^{k+d+1,p} → W^{k,p}` of the
Sobolev sections of `C` is compact, then for every `ε > 0` there is `K ≥ 0` with

`‖w‖_{W^{k,p}} ≤ ε ‖w‖_{W^{k+d+1,p}} + K ‖w‖_{Lᵖ}`

for every `w ∈ W^{k+d+1,p}`, where `‖w‖_{Lᵖ}` is the norm of the chart data of `w`
(`TauCeti.SectionChartData.chartValuesL`), which determine it. -/
theorem SectionChartData.exists_norm_lowerOrdersL_le {d : ℕ}
    (h : IsCompactOperator (C.lowerOrdersL μ p k (d + 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, 0 ≤ K ∧ ∀ w : C.sobolevSections μ p (k + (d + 1)),
      ‖C.lowerOrdersL μ p k (d + 1) w‖ ≤ ε * ‖w‖ + K * ‖C.chartValuesL μ p (k + (d + 1)) w‖ := by
  obtain ⟨K, hK, hw⟩ := h.exists_norm_le_mul_norm_add_mul_norm (C.chartValuesL_injective μ p k) hε
  exact ⟨K, hK, fun w ↦ by simpa using hw w⟩

end Components

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-! ### Rellich compactness -/

namespace SobolevSection

/-- **Rellich's theorem for Sobolev sections.** On a compact manifold without boundary, given by a
finite bundle atlas of a Hausdorff manifold, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` is a compact
operator for every order `k` and every `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerOrderL [T2Space M] :
    IsCompactOperator (A.sectionChartData.lowerOrderL μ p k) := by
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := A.exists_transfer_cover
  have hPj (i j : Fin A.n) : P i j ≤ A.image j :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image i j))
  have hQi (i : Fin A.n) : Q i ≤ A.image i :=
    SetLike.coe_subset_coe.1 (subset_closure.trans (hQ i))
  -- By local Rellich compactness, the chart-`i` data on `Q i` depend compactly on the section.
  have hrel (i : Fin A.n) : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦ fun l ↦
      Wkp.restrictL (hQi i) k
        ((A.sectionChartData.lowerOrderL μ p k w : A.sectionChartData.SobolevData μ p k) i l) :=
    IsCompactOperator.pi fun l ↦ by
      convert (Wkp.isCompactOperator_restrictL_lowerOrderL (hQc i) (hQ i) k).comp_clm
        ((ContinuousLinearMap.proj l).comp (A.sectionChartData.componentsL μ p (k + 1) i))
        using 1
      funext w
      simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
      exact congrArg _ ((SectionChartData.lowerOrderL_apply _ _ _ _ w i l).trans
        ((Wkp.lowerOrderL_apply k _).symm.trans (congrArg _
          (congrFun (A.sectionChartData.componentsL_apply μ p (k + 1) i w) l).symm)))
  refine SectionChartData.isCompactOperator_of_forall_apply (A.aeTransition_sectionChartData μ)
    fun j m ↦ ?_
  -- The pieces `P i j` cover the image of chart `j`, and on `P i j` the chart-`j` data are
  -- transferred from the chart-`i` data on `Q i`.
  let T : SobolevSection A μ p (k + 1) →L[ℝ] Wkp μ (A.image j) p k :=
    ((ContinuousLinearMap.proj m).comp ((ContinuousLinearMap.proj j).comp
    (A.sectionChartData.sobolevSections μ p k).subtypeL)).comp
      (A.sectionChartData.lowerOrderL μ p k)
  refine IsCompactOperator.of_norm_le_mul_sum T.toLinearMap
    (fun i ↦ (Wkp.restrictL (hPj i j) k).comp T) (fun i ↦ ?_) (C := 1) ?_
  · convert (hrel i).clm_comp ((ContinuousLinearMap.proj m).comp
      (A.transferL μ p k i j (hPc i j) (hPD i j) (hPQ i j))) using 1
    funext w
    exact A.restrictL_eq_transferL μ p k (A.sectionChartData.lowerOrderL μ p k w).property (hP i j)
      (hPc i j) (hPD i j) (hQi i) (hPQ i j) m
  · intro w
    simpa only [one_mul, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      Function.comp_apply] using
      Wkp.norm_le_sum_norm_restrictL (fun i ↦ hPj i j) (hcov j) k (T w)

/-- **Rellich's theorem for Sobolev sections**, for any loss of derivatives: the inclusion
`W^{k+d+1,p}(V) → W^{k,p}(V)` is a compact operator for `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerOrdersL [T2Space M] (d : ℕ) :
    IsCompactOperator (A.sectionChartData.lowerOrdersL μ p k (d + 1)) :=
  SectionChartData.isCompactOperator_lowerOrdersL (isCompactOperator_lowerOrderL A μ p (k + d))

/-- **Rellich's theorem for Sobolev sections**, forgetting all derivatives: the inclusion
`W^{k+1,p}(V) → W^{0,p}(V)` is a compact operator for `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerToZeroL [T2Space M] :
    IsCompactOperator (A.sectionChartData.lowerToZeroL μ p (k + 1)) := by
  have h := (isCompactOperator_lowerOrderL A μ p k).clm_comp
    (A.sectionChartData.lowerToZeroL μ p k)
  simpa only [Function.comp_def, SectionChartData.lowerToZeroL_lowerOrderL] using h

/-- **Rellich with exponent change.** The inclusion `W^{k+d+1,q} → W^{k,p}` is compact
for `1 ≤ p ≤ q`; both exponents may be infinite. -/
theorem isCompactOperator_lowerOrdersL_comp_ofExponentLEL [T2Space M]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) (d : ℕ) :
    IsCompactOperator ((A.sectionChartData.lowerOrdersL μ p k (d + 1)).comp
      (A.sectionChartData.ofExponentLEL μ (k + (d + 1)) hpq)) :=
  (isCompactOperator_lowerOrdersL A μ p k d).comp_clm _

/-- **Ehrling's inequality for Sobolev sections.** On a compact manifold without boundary, given by
a finite bundle atlas of a Hausdorff manifold, for `1 ≤ p ≤ ∞`, orders `k < k + d + 1` and every
`ε > 0` there is `C ≥ 0` with

`‖w‖_{W^{k,p}} ≤ ε ‖w‖_{W^{k+d+1,p}} + C ‖w‖_{Lᵖ}`

for every `w ∈ W^{k+d+1,p}(V)`, where `‖w‖_{Lᵖ}` is the norm of the chart data of `w`
(`TauCeti.SectionChartData.chartValuesL`). -/
theorem exists_norm_lowerOrdersL_le [T2Space M] (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ w : SobolevSection A μ p (k + (d + 1)),
      ‖A.sectionChartData.lowerOrdersL μ p k (d + 1) w‖ ≤
        ε * ‖w‖ + C * ‖A.sectionChartData.chartValuesL μ p (k + (d + 1)) w‖ :=
  SectionChartData.exists_norm_lowerOrdersL_le (isCompactOperator_lowerOrdersL A μ p k d) hε

/-! ### Compactness at other exponents -/

variable {p} {q : ℝ≥0∞} [Fact (1 ≤ q)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- Lowering the exponent of the source keeps a compact map with prescribed chart data compact,
with the same chart data. -/
private theorem exists_isCompactOperator_of_ofExponentLE {p' : ℝ≥0∞} [Fact (1 ≤ p')]
    {j : ℕ} (hp' : p' ≤ p)
    (h : ∃ T : SobolevSection A μ p' j →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p' j i w) :
    ∃ T : SobolevSection A μ p j →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p j i w := by
  obtain ⟨T, hT, hTc⟩ := h
  refine ⟨T.comp (A.sectionChartData.ofExponentLEL μ j hp'), hT.comp_clm _, fun w i ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply]
  refine (hTc _ i).trans (.of_eq ?_)
  rw [SectionChartData.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]

/-- **Rellich compactness at a lower exponent.** On a compact manifold without boundary, given by a
finite bundle atlas of a Hausdorff manifold, let `1 ≤ q ≤ p ≤ ∞`. Then for every order `k` there
is a compact operator `W^{k+1,p}(V) → W^{k,q}(V)` keeping the underlying section. The exponents may
be infinite. -/
theorem exists_isCompactOperator_of_le [T2Space M] (hqp : q ≤ p) :
    ∃ T : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + 1) i w :=
  exists_isCompactOperator_of_ofExponentLE A μ k hqp
    ⟨A.sectionChartData.lowerOrderL μ q k, isCompactOperator_lowerOrderL A μ q k,
      fun w i ↦ .of_eq (by rw [SectionChartData.chartValueL_coe_lowerOrderL])⟩

/-- **Rellich–Kondrachov compactness by interpolation.** If `p < q` and `W^{k+1,p}(V)` embeds into
`W^{k,s}(V)` for a finite exponent `s > q` with `s⁻¹ + 1/n = p⁻¹`, then the embedding
`W^{k+1,p}(V) → W^{k,q}(V)` is compact: it is compact into `W^{k,p}(V)` by Rellich's theorem and
bounded into `W^{k,s}(V)`, and the `W^{k,q}` norm is controlled by these two norms. -/
private theorem exists_isCompactOperator_of_inv_add_eq_of_lt [T2Space M] {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (hexp : s⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hpq : p < q) (hqs : q < s) :
    ∃ T : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + 1) i w := by
  have : Fact (1 ≤ s) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  obtain ⟨θ, hθ, hθq⟩ := exists_inv_eq_of_mem_Ioo (one_pos.trans_le Fact.out).ne' ⟨hpq, hqs⟩
  obtain ⟨S, hS⟩ := exists_sobolevEmbeddingL A μ hs hexp k
  -- Lowering the exponent of the embedding back to `p` gives the compact Rellich inclusion.
  have hlow (w : SobolevSection A μ p (k + 1)) :
      A.sectionChartData.ofExponentLEL μ k (hpq.trans hqs).le (S w) =
        A.sectionChartData.lowerOrderL μ p k w :=
    SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ by
      rw [SectionChartData.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL,
        SectionChartData.chartValueL_coe_lowerOrderL]
      exact hS w i
  refine ⟨(A.sectionChartData.ofExponentLEL μ k hqs.le).comp S, ?_, fun w i ↦ ?_⟩
  · refine IsCompactOperator.of_norm_le_mul_rpow_mul_rpow
      (isCompactOperator_lowerOrderL A μ p k)
      (T₀ := (A.sectionChartData.lowerOrderL μ p k).toLinearMap) S (C := 1) hθ.1.le hθ.2 fun w ↦ ?_
    rw [one_mul, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ← hlow]
    exact SectionChartData.norm_ofExponentLEL_le_norm_rpow_mul_norm_rpow (hpq.trans hqs).le hqs.le
      (Set.Ioo_subset_Icc_self hθ) hθq (S w)
  · rw [ContinuousLinearMap.comp_apply, SectionChartData.chartValueL_ofExponentLEL,
      Lp.coeFn_ofExponentLEL]
    exact hS w i

/-- **The Rellich–Kondrachov theorem for Sobolev sections.** On a compact manifold without boundary
of dimension `n ≥ 2`, given by a finite bundle atlas of a Hausdorff manifold, let `1 ≤ p ≤ ∞`,
`1 ≤ q < ∞` and `r ≥ 1` with `1/p < 1/q + r/n`. Then for every order `k` there is a compact operator
`W^{k+r,p}(V) → W^{k,q}(V)` keeping the underlying section.

For `rp < n` this is compactness for every `q` strictly below the Sobolev exponent `np/(n - rp)`
of `exists_sobolevEmbeddingL_of_inv_add_eq`; for `rp ≥ n` it is compactness for every finite `q`.
-/
theorem exists_isCompactOperator_of_inv_lt_inv_add [T2Space M] (hn : 1 < finrank ℝ E) {r : ℕ}
    (hr : r ≠ 0) (hq : q ≠ ⊤) (hpq : p⁻¹ < q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹) :
    ∃ T : SobolevSection A μ p (k + r) →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + r) i w := by
  set ν := (finrank ℝ E : ℝ≥0∞)⁻¹
  have hν : ν < 1 := ENNReal.inv_lt_one.2 (by exact_mod_cast hn)
  have hq₀ : q⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hq
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr
  clear hr
  induction r generalizing p with
  | zero =>
    -- Lower `p` to an exponent `p' = t⁻¹` with finite Sobolev exponent `s`, `s⁻¹ = t - 1/n`.
    obtain ⟨t, hpt, ht₁, hνt, htq⟩ :=
      ENNReal.exists_le_lt_lt_add (ENNReal.inv_le_one.2 Fact.out) hν hq₀ (by simpa using hpq)
    have : Fact (1 ≤ t⁻¹) := ⟨ENNReal.one_le_inv.2 ht₁⟩
    refine exists_isCompactOperator_of_ofExponentLE A μ k (ENNReal.inv_le_iff_inv_le.1 hpt) ?_
    rcases le_or_gt q t⁻¹ with hqt | htq'
    · exact exists_isCompactOperator_of_le A μ k hqt
    · refine exists_isCompactOperator_of_inv_add_eq_of_lt A μ k
        (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hνt).ne') ?_ htq' (ENNReal.inv_lt_inv.1 ?_)
      · rw [inv_inv, inv_inv, tsub_add_cancel_of_le hνt.le]
      · rw [inv_inv]
        exact ENNReal.sub_lt_of_lt_add hνt.le htq
  | succ r ih =>
    -- Lose one derivative from `p'` to the finite exponent `s`, then `r + 1` more by induction.
    obtain ⟨t, hpt, ht₁, hνt, htq⟩ := ENNReal.exists_le_lt_lt_add (ENNReal.inv_le_one.2 Fact.out)
      hν (b := q⁻¹ + (r + 1 : ℕ) * ν) (by simp [hq₀]) (by convert hpq using 1; push_cast; ring)
    have : Fact (1 ≤ t⁻¹) := ⟨ENNReal.one_le_inv.2 ht₁⟩
    have hexp : ((t - ν)⁻¹)⁻¹ + ν = (t⁻¹)⁻¹ := by
      rw [inv_inv, inv_inv, tsub_add_cancel_of_le hνt.le]
    have : Fact (1 ≤ (t - ν)⁻¹) := ⟨one_le_of_inv_add_eq_inv hexp⟩
    obtain ⟨S, hS⟩ := exists_sobolevEmbeddingL A μ
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hνt).ne') hexp (k + (r + 1))
    obtain ⟨T, hT, hTc⟩ := ih (p := (t - ν)⁻¹) (by
      rw [inv_inv]
      exact ENNReal.sub_lt_of_lt_add hνt.le htq)
    refine exists_isCompactOperator_of_ofExponentLE A μ k (ENNReal.inv_le_iff_inv_le.1 hpt)
      ⟨T.comp S, hT.comp_clm S, fun w i ↦ (hTc (S w) i).trans (hS w i)⟩

/-- **Rellich–Kondrachov compactness above the dimension.** On a compact manifold without boundary
of dimension `n ≥ 2`, given by a finite bundle atlas of a Hausdorff manifold, let `n ≤ p ≤ ∞`. Then
for every order `k` and every finite `q ≥ 1` there is a compact operator `W^{k+1,p}(V) → W^{k,q}(V)`
keeping the underlying section: `1/p ≤ 1/n < 1/q + 1/n`. On a surface this puts `W^{1,p}`, `p ≥ 2`,
in every `L^q`, `q < ∞`. -/
theorem exists_isCompactOperator_of_finrank_le [T2Space M] (hn : 1 < finrank ℝ E)
    (hp : (finrank ℝ E : ℝ≥0∞) ≤ p) (hq : q ≠ ⊤) :
    ∃ T : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ q k, IsCompactOperator T ∧
      ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + 1) i w :=
  exists_isCompactOperator_of_inv_lt_inv_add A μ k hn one_ne_zero hq (by
    rw [Nat.cast_one, one_mul]
    exact ENNReal.inv_lt_inv_add_inv_of_le hp (by exact_mod_cast (zero_lt_one.trans hn).ne') hq)

end SobolevSection

end Sobolev

end TauCeti
