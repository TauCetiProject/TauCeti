/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Convex.Combination
import Mathlib.Order.Disjointed

/-!
# Integrating continuous maps from a compact space into a locally convex space

Let `K` be a compact space whose open sets are measurable, `μ` a finite measure on `K`, and `E` a
complete Hausdorff locally convex real topological vector space. This file constructs the integral
`ContinuousMap.compactIntegral μ f : E` of a continuous map `f : C(K, E)`. No norm on `E` is
assumed: the integral serves spaces such as `ℂ^ℕ` with its product topology, or the Fréchet space
of smooth vectors of a Banach representation, where Mathlib's Bochner integral does not apply.

The integral is the limit of the Riemann sums `∑ i, μ (A i) • f (x i)` over finite measurable
partitions `(A i)` of `K` with tags `x i`, ordered by fineness. A partition is fine for a gauge
`U`, an assignment of a neighbourhood `U x` to every point `x`, when each piece `A i` lies in
`U (x i)`. Compactness gives fine partitions for every gauge. If, on every piece of two
partitions, each value of `f` differs from the value of `f` at the piece's tag by an element of a
convex neighbourhood `C` of `0`, the two Riemann sums differ by an element of `μ univ • (C - C)`.
Indeed, their difference is a combination, with weights the measures of the common refinement, of
differences `f (x i) - f (y j)` of tag values over nonempty common pieces; comparing both tag
values with the value of `f` at a point of the common piece puts each difference in `C - C`. So the
Riemann sums of a continuous map form a Cauchy net, whose limit in the complete space `E` is the
integral.

Every identity between Riemann sums passes to the limit. This gives linearity, commutation with
continuous linear maps into any Hausdorff topological module, the bound `p (∫ f) ≤ ∫ x, p (f x) ∂μ`
for every continuous seminorm `p`, and the value of a constant map. Likewise, when the values of `f`
lie in a convex neighbourhood `C` of `0` inside a closed set `D`, the Riemann sums scaled by
`(μ univ + 1)⁻¹` lie in `C`, so the scaled integral lies in `D`; hence the integral is continuous
for uniform convergence. When `E` is a Banach space the integral is Mathlib's Bochner integral,
since the Bochner integral is also the limit of the Riemann sums. Continuous linear functionals
separate the points of a Hausdorff locally convex space, so the integral is characterised as the
unique vector `v` with `ℓ v = ∫ x, ℓ (f x) ∂μ` for every continuous linear functional `ℓ`. This
transfers change of variables along measure-preserving maps from the scalar case, and with it
invariance of the integral against an invariant measure under translation and inversion, for
instance on a compact group.

## Main definitions

* `ContinuousMap.compactIntegral μ f`: the integral of `f : C(K, E)` against `μ`.
* `ContinuousMap.compactIntegralₗ μ R`: the integral as an `R`-linear map on `C(K, E)`.

## Main statements

* `ContinuousMap.compactIntegral_eq_integral`: in a Banach space, the integral is the Bochner
  integral.
* `ContinuousMap.continuous_compactIntegral`: the integral is continuous for the topology of
  uniform convergence.
* `ContinuousLinearMap.compactIntegral_comp_comm`: continuous linear maps commute with the
  integral.
* `ContinuousMap.eq_compactIntegral_iff`: the integral is the unique vector whose image under every
  continuous linear functional is the integral of the functional applied to `f`.
* `Seminorm.apply_compactIntegral_le`: `p (∫ f) ≤ ∫ x, p (f x) ∂μ` for a continuous seminorm `p`.
* `MeasureTheory.MeasurePreserving.compactIntegral_comp`: change of variables along a continuous
  measure-preserving map.
* `ContinuousMap.compactIntegral_comp_mulLeft`, `ContinuousMap.compactIntegral_comp_mulRight`,
  `ContinuousMap.compactIntegral_comp_inv`: invariance under translation and inversion, for
  instance on a compact group.

## References

* R. Beuzart-Plessis, P.-H. Chaudouard, M. Zydor, *The global Gan–Gross–Prasad conjecture for
  unitary groups: the endoscopic case*, Publ. Math. IHÉS 135 (2022), Appendix A.
* N. Bourbaki, *Integration I*, Springer (2004), Chapter III, §3.
-/

public section

open MeasureTheory Filter Function Topology Set Pointwise

namespace ContinuousMap

section Definition

variable {K : Type*} [MeasurableSpace K]

/-- A finite measurable partition of `K` into the pieces `piece i`, with a tag `tag i` attached to
each piece. The tag need not lie in its piece. -/
private structure TaggedPartition (K : Type*) [MeasurableSpace K] where
  /-- The number of pieces. -/
  n : ℕ
  /-- The pieces of the partition. -/
  piece : Fin n → Set K
  /-- The tag attached to each piece. -/
  tag : Fin n → K
  measurableSet_piece : ∀ i, MeasurableSet (piece i)
  pairwise_disjoint : Pairwise (Disjoint on piece)
  iUnion_piece : ⋃ i, piece i = univ

/-- A tagged partition is fine for a gauge `U` when each piece lies in the value of `U` at its
tag. -/
private def TaggedPartition.IsFine (P : TaggedPartition K) (U : K → Set K) : Prop :=
  ∀ i, P.piece i ⊆ U (P.tag i)

section Fineness

variable [TopologicalSpace K]

variable (K) in
/-- The fineness filter on tagged partitions: it is generated by the sets of partitions that are
fine for a gauge assigning a neighbourhood to each point. -/
private def fineFilter : Filter (TaggedPartition K) :=
  ⨅ U ∈ {U : K → Set K | ∀ x, U x ∈ 𝓝 x}, 𝓟 {P | P.IsFine U}

private theorem hasBasis_fineFilter :
    (fineFilter K).HasBasis (fun U : K → Set K ↦ ∀ x, U x ∈ 𝓝 x) fun U ↦ {P | P.IsFine U} :=
  hasBasis_biInf_principal
    (fun U hU U' hU' ↦ ⟨fun x ↦ U x ∩ U' x, fun x ↦ inter_mem (hU x) (hU' x),
      fun _ hP i ↦ (hP i).trans inter_subset_left, fun _ hP i ↦ (hP i).trans inter_subset_right⟩)
    ⟨fun _ ↦ univ, fun _ ↦ univ_mem⟩

private theorem isFine_mem_fineFilter {U : K → Set K} (hU : ∀ x, U x ∈ 𝓝 x) :
    {P : TaggedPartition K | P.IsFine U} ∈ fineFilter K :=
  hasBasis_fineFilter.mem_of_mem hU

/-- Compactness gives a fine tagged partition for every gauge: cover `K` by finitely many
interiors of the gauge's neighbourhoods and make the cover disjoint. -/
private theorem exists_isFine [CompactSpace K] [OpensMeasurableSpace K] {U : K → Set K}
    (hU : ∀ x, U x ∈ 𝓝 x) : ∃ P : TaggedPartition K, P.IsFine U := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x ↦ interior (U x))
    fun x _ ↦ interior_mem_nhds.2 (hU x)
  let tag : Fin t.card → K := fun i ↦ t.equivFin.symm i
  let O : Fin t.card → Set K := fun i ↦ interior (U (tag i))
  refine ⟨⟨t.card, disjointed O, tag, fun i ↦ ?_, disjoint_disjointed O, ?_⟩,
    fun i ↦ (disjointed_subset O i).trans interior_subset⟩
  · exact disjointedRec (p := MeasurableSet) (fun _ j ht ↦ ht.diff isOpen_interior.measurableSet)
      isOpen_interior.measurableSet
  · rw [iUnion_disjointed]
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨x, hx, hz⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, by simpa [O, tag] using hz⟩

private theorem fineFilter_neBot [CompactSpace K] [OpensMeasurableSpace K] :
    (fineFilter K).NeBot :=
  hasBasis_fineFilter.neBot_iff.2 fun hU ↦ exists_isFine hU

end Fineness

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Riemann sum `∑ i, μ (P.piece i) • f (P.tag i)` of `f` over a tagged partition `P`. -/
private noncomputable def riemannSum (μ : Measure K) (f : K → E) (P : TaggedPartition K) : E :=
  ∑ i, μ.real (P.piece i) • f (P.tag i)

private theorem riemannSum_add (μ : Measure K) (f g : K → E) (P : TaggedPartition K) :
    riemannSum μ (f + g) P = riemannSum μ f P + riemannSum μ g P := by
  simp [riemannSum, smul_add, Finset.sum_add_distrib]

private theorem riemannSum_smul {R : Type*} [Monoid R] [DistribMulAction R E]
    [SMulCommClass ℝ R E] (μ : Measure K) (c : R) (f : K → E) (P : TaggedPartition K) :
    riemannSum μ (c • f) P = c • riemannSum μ f P := by
  simp [riemannSum, Finset.smul_sum, smul_comm _ c]

private theorem map_riemannSum {F : Type*} [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F)
    (μ : Measure K) (f : K → E) (P : TaggedPartition K) :
    T (riemannSum μ f P) = riemannSum μ (T ∘ f) P := by
  simp [riemannSum, map_sum, map_smul]

section Riemann

variable {μ : Measure K} [IsFiniteMeasure μ]

private theorem sum_measureReal_piece (P : TaggedPartition K) :
    ∑ i, μ.real (P.piece i) = μ.real univ := by
  rw [← measureReal_iUnion_fintype P.pairwise_disjoint P.measurableSet_piece, P.iUnion_piece]

private theorem measureReal_piece_eq_sum (P Q : TaggedPartition K) (i : Fin P.n) :
    μ.real (P.piece i) = ∑ j, μ.real (P.piece i ∩ Q.piece j) := by
  rw [← measureReal_iUnion_fintype
      (fun j j' h ↦ (Q.pairwise_disjoint h).mono inter_subset_right inter_subset_right)
      fun j ↦ (P.measurableSet_piece i).inter (Q.measurableSet_piece j),
    ← inter_iUnion, Q.iUnion_piece, inter_univ]

/-- Two Riemann sums over partitions in which every value `f z` on a piece satisfies
`f z - f x ∈ V` for the piece's tag `x` differ by an element of `(μ univ + 1) • C`, for a convex
`C ∋ 0` containing `V - V`. Both sums are rewritten over the common refinement; a nonempty common
piece carries a point `z`, and the difference of the two tag values `x` and `y` is
`f x - f y = (f z - f y) - (f z - f x)`. -/
private theorem riemannSum_sub_riemannSum_mem {f : K → E} {V C : Set E} (hC : Convex ℝ C)
    (h0 : (0 : E) ∈ C) (hVC : ∀ a ∈ V, ∀ b ∈ V, a - b ∈ C) {P Q : TaggedPartition K}
    (hP : P.IsFine fun x ↦ {z | f z - f x ∈ V}) (hQ : Q.IsFine fun x ↦ {z | f z - f x ∈ V}) :
    (μ.real univ + 1)⁻¹ • (riemannSum μ f P - riemannSum μ f Q) ∈ C := by
  classical
  let c : Fin P.n × Fin Q.n → ℝ := fun ij ↦ μ.real (P.piece ij.1 ∩ Q.piece ij.2)
  let w : Fin P.n × Fin Q.n → E := fun ij ↦
    if (P.piece ij.1 ∩ Q.piece ij.2).Nonempty then f (P.tag ij.1) - f (Q.tag ij.2) else 0
  have hP' : riemannSum μ f P = ∑ ij, c ij • f (P.tag ij.1) := by
    simp_rw [riemannSum, measureReal_piece_eq_sum P Q, Finset.sum_smul]
    rw [Fintype.sum_prod_type]
  have hQ' : riemannSum μ f Q = ∑ ij, c ij • f (Q.tag ij.2) := by
    simp_rw [riemannSum, measureReal_piece_eq_sum Q P, Finset.sum_smul, inter_comm (Q.piece _)]
    rw [Fintype.sum_prod_type_right]
  have hsum : ∑ ij, c ij = μ.real univ := by
    rw [Fintype.sum_prod_type]
    simp_rw [c, ← measureReal_piece_eq_sum]
    exact sum_measureReal_piece P
  have hdiff : riemannSum μ f P - riemannSum μ f Q = ∑ ij, c ij • w ij := by
    rw [hP', hQ', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    by_cases h : (P.piece ij.1 ∩ Q.piece ij.2).Nonempty
    · simp [w, h, smul_sub]
    · simp [c, w, not_nonempty_iff_eq_empty.1 h]
  have hm : 0 < μ.real univ + 1 := by positivity
  rw [hdiff, Finset.smul_sum]
  simp_rw [smul_smul]
  refine hC.sum_mem_of_zero_mem h0 (fun _ _ ↦ by positivity) ?_ fun ij _ ↦ ?_
  · rw [← Finset.mul_sum, hsum, inv_mul_le_one₀ hm]
    linarith
  simp only [w]
  split_ifs with h
  · obtain ⟨z, hzP, hzQ⟩ := h
    simpa using hVC _ (hQ ij.2 hzQ) _ (hP ij.1 hzP)
  · exact h0

end Riemann

variable [TopologicalSpace K] [TopologicalSpace E]

/-- The integral of a continuous map `f` from a compact space into a complete Hausdorff locally
convex real space, against a finite measure `μ`: the limit of the Riemann sums
`∑ i, μ (A i) • f (x i)` over finite measurable partitions `(A i)` of `K` with tags `x i`, as the
partitions become finer.

The value is meaningful when `K` is compact with measurable open sets, `μ` is finite, and `E` is a
complete Hausdorff locally convex space: then the Riemann sums converge, and the integral is the
unique vector `v` with `ℓ v = ∫ x, ℓ (f x) ∂μ` for every continuous linear functional `ℓ`
(`ContinuousMap.eq_compactIntegral_iff`). In a Banach space it is the Bochner integral
(`ContinuousMap.compactIntegral_eq_integral`). -/
noncomputable def compactIntegral (μ : Measure K) (f : C(K, E)) : E :=
  limUnder (fineFilter K) (riemannSum μ f)

variable [CompactSpace K] [OpensMeasurableSpace K] {μ : Measure K}

private theorem compactIntegral_eq_of_tendsto [T2Space E] {f : C(K, E)} {v : E}
    (h : Tendsto (riemannSum μ f) (fineFilter K) (𝓝 v)) : f.compactIntegral μ = v :=
  have := fineFilter_neBot (K := K)
  h.limUnder_eq

variable [IsFiniteMeasure μ]

/-- The integral of a constant map is the total mass times the constant. -/
@[simp]
theorem compactIntegral_const [T2Space E] (v : E) :
    (ContinuousMap.const K v).compactIntegral μ = μ.real univ • v :=
  compactIntegral_eq_of_tendsto <| tendsto_const_nhds.congr fun P ↦ by
    simp [riemannSum, ← Finset.sum_smul, sum_measureReal_piece]

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Bochner integral differs from a Riemann sum by at most `ε * μ univ` when every value of
`f` on a piece lies within `ε` of the value of `f` at the piece's tag. -/
private theorem norm_integral_sub_riemannSum_le (f : C(K, F)) {ε : ℝ} {P : TaggedPartition K}
    (hP : P.IsFine fun x ↦ {z | f z - f x ∈ Metric.ball 0 ε}) :
    ‖∫ x, f x ∂μ - riemannSum μ f P‖ ≤ ε * μ.real univ := by
  have hpiece (i : Fin P.n) : ∫ x in P.piece i, f x ∂μ - μ.real (P.piece i) • f (P.tag i) =
      ∫ x in P.piece i, (f x - f (P.tag i)) ∂μ := by
    rw [integral_sub (f.integrable μ).integrableOn (integrableOn_const (by finiteness)),
      setIntegral_const]
  calc ‖∫ x, f x ∂μ - riemannSum μ f P‖
      = ‖∑ i, ∫ x in P.piece i, (f x - f (P.tag i)) ∂μ‖ := by
        rw [← setIntegral_univ, ← P.iUnion_piece, integral_iUnion_fintype P.measurableSet_piece
          P.pairwise_disjoint fun _ ↦ (f.integrable μ).integrableOn, riemannSum,
          ← Finset.sum_sub_distrib]
        simp_rw [hpiece]
    _ ≤ ∑ i, ε * μ.real (P.piece i) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        refine norm_setIntegral_le_of_norm_le_const (by finiteness) fun z hz ↦ ?_
        exact (mem_ball_zero_iff.1 (hP i hz)).le
    _ = ε * μ.real univ := by rw [← Finset.mul_sum, sum_measureReal_piece]

/-- In a Banach space, the Riemann sums of a continuous map converge to its Bochner integral. -/
private theorem tendsto_riemannSum_integral (f : C(K, F)) :
    Tendsto (riemannSum μ f) (fineFilter K) (𝓝 (∫ x, f x ∂μ)) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hδ : 0 < ε / (μ.real univ + 1) := div_pos hε (by positivity)
  filter_upwards [isFine_mem_fineFilter fun x ↦
    tendsto_sub_nhds_zero_iff.2 (f.continuousAt x) (Metric.ball_mem_nhds 0 hδ)]
    with P hP
  rw [dist_comm, dist_eq_norm]
  calc ‖∫ x, f x ∂μ - riemannSum μ f P‖ ≤ ε / (μ.real univ + 1) * μ.real univ :=
        norm_integral_sub_riemannSum_le f hP
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity), mul_add, mul_one]
        linarith

/-- In a Banach space, the integral of a continuous map is its Bochner integral. -/
theorem compactIntegral_eq_integral (f : C(K, F)) : f.compactIntegral μ = ∫ x, f x ∂μ :=
  compactIntegral_eq_of_tendsto (tendsto_riemannSum_integral f)

end Normed

end Definition

section LocallyConvex

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [CompactSpace K]
  [OpensMeasurableSpace K] {μ : Measure K} [IsFiniteMeasure μ]
  {E : Type*} [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Riemann sums of a continuous map form a Cauchy net. -/
private theorem cauchy_map_riemannSum (f : C(K, E)) :
    Cauchy (map (riemannSum μ f) (fineFilter K)) := by
  have := fineFilter_neBot (K := K)
  refine (IsUniformAddGroup.cauchy_map_iff_tendsto _ _).2 ⟨inferInstance, fun W hW ↦ ?_⟩
  have hW' : ((μ.real univ + 1) • ·) ⁻¹' W ∈ 𝓝 (0 : E) :=
    (continuous_const_smul (μ.real univ + 1)).tendsto' 0 0 (smul_zero _) hW
  obtain ⟨C, ⟨hC0, hCc⟩, hCW⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hW'
  obtain ⟨V, hV, hVC⟩ := exists_nhds_half_neg hC0
  have hU := fun x ↦ tendsto_sub_nhds_zero_iff.2 (f.continuousAt x) hV
  refine mem_map.2 <| mem_of_superset
    (prod_mem_prod (isFine_mem_fineFilter hU) (isFine_mem_fineFilter hU)) fun PQ hPQ ↦ ?_
  have hd := hCW <| riemannSum_sub_riemannSum_mem (μ := μ) hCc (mem_of_mem_nhds hC0) hVC hPQ.1
    hPQ.2
  rwa [mem_preimage, smul_inv_smul₀ (by positivity)] at hd

private theorem tendsto_riemannSum (f : C(K, E)) :
    Tendsto (riemannSum μ f) (fineFilter K) (𝓝 (f.compactIntegral μ)) :=
  tendsto_nhds_limUnder (CompleteSpace.complete (cauchy_map_riemannSum f))

/-- Continuous linear maps into any Hausdorff topological module commute with the integral. The
maps may be linear over any scalar ring `𝕜` whose action is compatible with the real one, such as
`ℂ`. -/
@[simp]
theorem _root_.ContinuousLinearMap.compactIntegral_comp_comm {𝕜 F : Type*} [Semiring 𝕜]
    [Module 𝕜 E] [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [LinearMap.CompatibleSMul E F ℝ 𝕜]
    [TopologicalSpace F] [T2Space F] (T : E →L[𝕜] F) (f : C(K, E)) :
    ((T : C(E, F)).comp f).compactIntegral μ = T (f.compactIntegral μ) :=
  compactIntegral_eq_of_tendsto <| ((T.continuous.tendsto _).comp (tendsto_riemannSum f)).congr
    fun P ↦ by simpa using map_riemannSum ((T : E →ₗ[𝕜] F).restrictScalars ℝ) μ f P

/-- A continuous linear map into a Banach space takes the integral to the Bochner integral of the
composite. The map may be linear over any scalar ring `𝕜` whose action is compatible with the real
one, such as `ℂ`. -/
theorem _root_.ContinuousLinearMap.apply_compactIntegral {𝕜 F : Type*} [Semiring 𝕜] [Module 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module 𝕜 F] [LinearMap.CompatibleSMul E F ℝ 𝕜]
    [CompleteSpace F] (T : E →L[𝕜] F) (f : C(K, E)) :
    T (f.compactIntegral μ) = ∫ x, T (f x) ∂μ := by
  rw [← T.compactIntegral_comp_comm, compactIntegral_eq_integral]
  simp

/-- A continuous seminorm of the integral is at most the integral of the seminorm. -/
theorem _root_.Seminorm.apply_compactIntegral_le (p : Seminorm ℝ E) (hp : Continuous p)
    (f : C(K, E)) : p (f.compactIntegral μ) ≤ ∫ x, p (f x) ∂μ := by
  have := fineFilter_neBot (K := K)
  refine le_of_tendsto_of_tendsto' ((hp.tendsto _).comp (tendsto_riemannSum f))
    (tendsto_riemannSum_integral ⟨fun x ↦ p (f x), hp.comp f.continuous⟩) fun P ↦ ?_
  rw [Function.comp_apply, riemannSum, riemannSum]
  refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  simp [map_smul_eq_mul, Real.norm_of_nonneg measureReal_nonneg]

variable [T2Space E]

@[simp]
theorem compactIntegral_add (f g : C(K, E)) :
    (f + g).compactIntegral μ = f.compactIntegral μ + g.compactIntegral μ :=
  compactIntegral_eq_of_tendsto <| ((tendsto_riemannSum f).add (tendsto_riemannSum g)).congr
    fun P ↦ by rw [coe_add, riemannSum_add]

@[simp]
theorem compactIntegral_smul {R : Type*} [Monoid R] [DistribMulAction R E] [SMulCommClass ℝ R E]
    [ContinuousConstSMul R E] (c : R) (f : C(K, E)) :
    (c • f).compactIntegral μ = c • f.compactIntegral μ :=
  compactIntegral_eq_of_tendsto <| ((tendsto_riemannSum f).const_smul c).congr
    fun P ↦ by rw [coe_smul, riemannSum_smul]

variable (μ) in
/-- The integral against `μ`, as an `R`-linear map on continuous maps `K → E`. -/
noncomputable def compactIntegralₗ (R : Type*) [Semiring R] [Module R E] [SMulCommClass ℝ R E]
    [ContinuousConstSMul R E] : C(K, E) →ₗ[R] E where
  toFun f := f.compactIntegral μ
  map_add' := compactIntegral_add
  map_smul' := compactIntegral_smul

@[simp]
theorem compactIntegralₗ_apply (R : Type*) [Semiring R] [Module R E] [SMulCommClass ℝ R E]
    [ContinuousConstSMul R E] (f : C(K, E)) : compactIntegralₗ μ R f = f.compactIntegral μ :=
  (rfl)

@[simp]
theorem compactIntegral_zero : (0 : C(K, E)).compactIntegral μ = 0 :=
  (compactIntegralₗ μ ℝ).map_zero

@[simp]
theorem compactIntegral_neg (f : C(K, E)) : (-f).compactIntegral μ = -f.compactIntegral μ :=
  (compactIntegralₗ μ ℝ).map_neg f

@[simp]
theorem compactIntegral_sub (f g : C(K, E)) :
    (f - g).compactIntegral μ = f.compactIntegral μ - g.compactIntegral μ :=
  (compactIntegralₗ μ ℝ).map_sub f g

/-- The integral is continuous on `C(K, E)` with its compact-open topology, the topology of uniform
convergence on the compact space `K`. -/
theorem continuous_compactIntegral : Continuous fun f : C(K, E) ↦ f.compactIntegral μ := by
  -- By linearity it suffices to prove continuity at `0`. If every value of `f` lies in a convex
  -- neighbourhood `C` of `0` contained in a closed set `D`, every Riemann sum lies in
  -- `(μ univ + 1) • C`, so the integral lies in `(μ univ + 1) • D`.
  refine continuous_of_continuousAt_zero (compactIntegralₗ μ ℝ) fun W hW ↦ ?_
  rw [map_zero] at hW
  have hW' : ((μ.real univ + 1) • ·) ⁻¹' W ∈ 𝓝 (0 : E) :=
    (continuous_const_smul (μ.real univ + 1)).tendsto' 0 0 (smul_zero _) hW
  obtain ⟨D, hD, hDc, hDW⟩ := exists_mem_nhds_isClosed_subset hW'
  obtain ⟨C, ⟨hC0, hCc⟩, hCD⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hD
  have := fineFilter_neBot (K := K)
  refine mem_map.2 ?_
  filter_upwards [eventually_mapsTo (X := K) (f := 0) isCompact_univ isOpen_interior
    fun _ _ ↦ mem_interior_iff_mem_nhds.2 hC0] with f hf
  have hm : 0 < μ.real univ + 1 := by positivity
  have hfD : (μ.real univ + 1)⁻¹ • f.compactIntegral μ ∈ D := by
    refine hDc.mem_of_tendsto ((tendsto_riemannSum f).const_smul _) (.of_forall fun P ↦ hCD ?_)
    rw [riemannSum, Finset.smul_sum]
    simp_rw [smul_smul]
    refine hCc.sum_mem_of_zero_mem (mem_of_mem_nhds hC0) (fun _ _ ↦ by positivity) ?_
      fun i _ ↦ interior_subset (hf (mem_univ _))
    rw [← Finset.mul_sum, sum_measureReal_piece, inv_mul_le_one₀ hm]
    linarith
  have hd := hDW hfD
  rwa [mem_preimage, smul_inv_smul₀ hm.ne'] at hd

/-- The integral is the unique vector whose value under every continuous linear functional `ℓ` is
the integral of `ℓ ∘ f`. Continuous linear functionals separate the points of a Hausdorff locally
convex space. -/
theorem eq_compactIntegral_iff {f : C(K, E)} {v : E} :
    v = f.compactIntegral μ ↔ ∀ ℓ : StrongDual ℝ E, ℓ v = ∫ x, ℓ (f x) ∂μ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl ℓ
    exact ℓ.apply_compactIntegral f
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ ↦ ?_
    rw [h, ℓ.apply_compactIntegral]

/-- **Change of variables**: precomposing with a continuous measure-preserving map does not
change the integral. -/
theorem _root_.MeasureTheory.MeasurePreserving.compactIntegral_comp {K' : Type*}
    [TopologicalSpace K'] [MeasurableSpace K'] [CompactSpace K'] [OpensMeasurableSpace K']
    {μ' : Measure K'} {φ : C(K', K)} (hφ : MeasurePreserving φ μ' μ) (f : C(K, E)) :
    (f.comp φ).compactIntegral μ' = f.compactIntegral μ := by
  have : IsFiniteMeasure μ' :=
    (Measure.isFiniteMeasure_map_iff hφ.measurable.aemeasurable).1 (hφ.map_eq ▸ inferInstance)
  refine (eq_compactIntegral_iff.2 fun ℓ ↦ ?_).symm
  rw [ℓ.apply_compactIntegral, ← hφ.map_eq]
  simpa using integral_map (f := fun y ↦ ℓ (f y)) hφ.measurable.aemeasurable
    (ℓ.continuous.comp f.continuous).aestronglyMeasurable

section Group

variable {G : Type*} [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] {ν : Measure G} [IsFiniteMeasure ν]

/-- The integral against a left-invariant measure is unchanged by left translation. -/
@[simp]
theorem compactIntegral_comp_mulLeft [Mul G] [SeparatelyContinuousMul G] [MeasurableMul G]
    [ν.IsMulLeftInvariant] (f : C(G, E)) (g : G) :
    (f.comp (ContinuousMap.mulLeft g)).compactIntegral ν = f.compactIntegral ν :=
  (measurePreserving_mul_left ν g).compactIntegral_comp f

/-- The integral against a right-invariant measure is unchanged by right translation. -/
@[simp]
theorem compactIntegral_comp_mulRight [Mul G] [SeparatelyContinuousMul G] [MeasurableMul G]
    [ν.IsMulRightInvariant] (f : C(G, E)) (g : G) :
    (f.comp (ContinuousMap.mulRight g)).compactIntegral ν = f.compactIntegral ν :=
  (measurePreserving_mul_right ν g).compactIntegral_comp f

/-- The integral against an inversion-invariant measure is unchanged by inversion. -/
@[simp]
theorem compactIntegral_comp_inv [InvolutiveInv G] [ContinuousInv G] [MeasurableInv G]
    [ν.IsInvInvariant] (f : C(G, E)) :
    (f.comp (Homeomorph.inv G : C(G, G))).compactIntegral ν = f.compactIntegral ν :=
  (Measure.measurePreserving_inv ν).compactIntegral_comp f

end Group

end LocallyConvex

end ContinuousMap
