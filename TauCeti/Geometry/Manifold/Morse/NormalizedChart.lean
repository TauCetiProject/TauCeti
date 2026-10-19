/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Morse.Lemma
public import TauCeti.Geometry.Manifold.Morse.ModelTransport

/-!
# Normalized Morse charts

A `TauCeti.MorseChart` writes a function near a nondegenerate critical point as
`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²` with unordered weights `wᵢ = ±1`. This file reorders
the coordinates so that the negative weights come first, divides by `√2`, and takes Euclidean
coordinates. The result is a partial diffeomorphism `ψ` onto an open subset of
`EuclideanSpace ℝ (Fin m)`, `m = dim M`, centred at the critical point, in which

`f y = f x - Σ_{i < λ} (ψ y)ᵢ² + Σ_{i ≥ λ} (ψ y)ᵢ²`

on the whole source, where `λ` is the manifold Morse index. Through the boundaryless model
transport this holds for every boundaryless model, not only for self-modelled manifolds. This is
the coordinate form in which handles are attached to sublevel sets.

As a first application, a nondegenerate critical point of index `0` is a strict local minimum,
and one of index `dim M` is a strict local maximum. For every other index, explicit coordinate
curves approach the critical point through values below and above the critical value; in
dimension two this is the index-one saddle model `f = f x - u² + v²`.

## Main declarations

* `TauCeti.MorseChart.normalizedCoord`: the reordered, rescaled Euclidean coordinates of a Morse
  chart.
* `TauCeti.MorseChart.normalizedChart`: a Morse chart as a partial diffeomorphism into Euclidean
  space, with `TauCeti.MorseChart.eq_quadratic_normalizedChart` its sum-of-squares equation.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart`: the normalized
  Morse lemma on a manifold with an arbitrary boundaryless model.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_twoDimensional_saddleChart`: the
  index-one normal form in dimension two.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_saddleCurves`: curves approaching a
  critical point of index strictly between `0` and `dim M` through lower and higher values.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_lt_of_manifoldMorseIndex_eq_zero` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_lt_of_manifoldMorseIndex_eq_finrank`:
  strict local extrema at critical points of extreme index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 2.2 and Corollary 2.3.
-/

public section

open Function Set Topology Filter
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace MorseChart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
  (φ : MorseChart E f x)

/-- Sorting the coordinates of a Morse chart by weight puts the `λ` negative weights first,
where `λ` is the Morse index. -/
theorem weight_sort_apply (i : Fin (Module.finrank ℝ E)) :
    φ.weight (Tuple.sort φ.weight i) =
      if i.val < manifoldMorseIndex 𝓘(ℝ, E) f x then -1 else 1 := by
  classical
  have hcard : (Finset.univ.filter fun j ↦ (φ.weight ∘ Tuple.sort φ.weight) j < 0).card =
      manifoldMorseIndex 𝓘(ℝ, E) f x := by
    rw [← φ.ncard_weight_neg, ← Set.ncard_coe_finset]
    simpa using Set.ncard_preimage_of_injective_subset_range (s := {j | φ.weight j < 0})
      (Tuple.sort φ.weight).injective (by simp)
  have hlt := Tuple.lt_card_lt_iff_apply_lt_of_monotone (j := i) (a := (0 : ℝ))
    (Tuple.monotone_sort φ.weight)
  rw [hcard, comp_apply] at hlt
  rcases φ.weight_eq_neg_one_or_eq_one (Tuple.sort φ.weight i) with h | h <;>
    · rw [h] at hlt ⊢
      split_ifs <;> norm_num at hlt ⊢
      omega

variable [FiniteDimensional ℝ E]

/-- The normalized linear coordinates of a Morse chart: the coordinates `L` of the chart, sorted
so that the negative weights come first, divided by `√2`, and read in Euclidean space. -/
noncomputable def normalizedCoord : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (φ.coord.trans ((LinearEquiv.funCongrLeft ℝ ℝ (Tuple.sort φ.weight)).trans
    ((LinearEquiv.smulOfNeZero ℝ _ (√2)⁻¹ (by positivity)).trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm.toLinearEquiv)))
    |>.toContinuousLinearEquiv

/-- The `i`-th normalized coordinate is the `σ i`-th chart coordinate divided by `√2`, where `σ`
sorts the weights increasingly. -/
@[simp]
theorem normalizedCoord_apply (v : E) (i : Fin (Module.finrank ℝ E)) :
    φ.normalizedCoord v i = (√2)⁻¹ * φ.coord v (Tuple.sort φ.weight i) := by
  simp [normalizedCoord, LinearEquiv.funCongrLeft_apply]

/-- In normalized coordinates the quadratic form `(1/2) Σᵢ wᵢ (L v)ᵢ²` of a Morse chart is the
signed sum of squares of its Morse index. -/
theorem sum_ite_mul_normalizedCoord_sq (v : E) :
    ∑ i, (if i.val < manifoldMorseIndex 𝓘(ℝ, E) f x then -1 else 1) *
        φ.normalizedCoord v i ^ 2 =
      (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.coord v i ^ 2 := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Tuple.sort φ.weight)
    fun j ↦ (2 : ℝ)⁻¹ * (φ.weight j * φ.coord v j ^ 2)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [normalizedCoord_apply, ← φ.weight_sort_apply, mul_pow, inv_pow,
    Real.sq_sqrt zero_le_two]
  ring

/-- A Morse chart in normalized coordinates, as a partial diffeomorphism onto an open subset of
Euclidean space. In these coordinates `f` is `f x` plus the signed sum of squares of its Morse
index (`TauCeti.MorseChart.eq_quadratic_normalizedChart`). -/
noncomputable def normalizedChart :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞ where
  toPartialEquiv := (φ.toChart.transHomeomorph φ.normalizedCoord.toHomeomorph).toPartialEquiv
  open_source := (φ.toChart.transHomeomorph φ.normalizedCoord.toHomeomorph).open_source
  open_target := (φ.toChart.transHomeomorph φ.normalizedCoord.toHomeomorph).open_target
  contMDiffOn_toFun :=
    φ.normalizedCoord.contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas φ.mem_maximalAtlas)
  contMDiffOn_invFun :=
    (contMDiffOn_symm_of_mem_maximalAtlas φ.mem_maximalAtlas).comp
      φ.normalizedCoord.symm.contDiff.contMDiff.contMDiffOn fun _ hv ↦ hv

/-- The normalized chart has the same source as the Morse chart. -/
@[simp]
theorem normalizedChart_source : φ.normalizedChart.source = φ.toChart.source :=
  (rfl)

/-- The target of the normalized chart is the target of the Morse chart in normalized
coordinates. -/
@[simp]
theorem normalizedChart_target :
    φ.normalizedChart.target = φ.normalizedCoord.symm ⁻¹' φ.toChart.target :=
  (rfl)

/-- The normalized chart is the Morse chart followed by the normalized linear coordinates. -/
@[simp]
theorem normalizedChart_apply (y : M) : φ.normalizedChart y = φ.normalizedCoord (φ.toChart y) :=
  (rfl)

/-- The inverse of the normalized chart undoes the normalized coordinates, then the chart. -/
@[simp]
theorem normalizedChart_symm_apply (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    φ.normalizedChart.toPartialEquiv.symm v = φ.toChart.symm (φ.normalizedCoord.symm v) :=
  (rfl)

/-- The normalized chart is centred at the critical point. -/
theorem normalizedChart_apply_self : φ.normalizedChart x = 0 := by
  simp

/-- The critical point is the only point of the source with normalized coordinates `0`. -/
theorem normalizedChart_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) :
    φ.normalizedChart y = 0 ↔ y = x := by
  rw [normalizedChart_apply, map_eq_zero_iff _ φ.normalizedCoord.injective,
    φ.toChart_eq_zero_iff hy]

/-- **The normalized Morse lemma.** On the whole source of a Morse chart,
`f y = f x - Σ_{i < λ} (ψ y)ᵢ² + Σ_{i ≥ λ} (ψ y)ᵢ²` in the normalized chart `ψ`, where `λ` is the
Morse index. -/
theorem eq_quadratic_normalizedChart {y : M} (hy : y ∈ φ.toChart.source) :
    f y = f x + ∑ i, (if i.val < manifoldMorseIndex 𝓘(ℝ, E) f x then -1 else 1) *
      φ.normalizedChart y i ^ 2 := by
  rw [normalizedChart_apply, sum_ite_mul_normalizedCoord_sq, φ.eq_quadratic y hy]

end MorseChart

variable [FiniteDimensional ℝ E] {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {f : M → ℝ} {x : M}

/-- **The normalized Morse lemma on a manifold.** At a nondegenerate critical point `x` of a
function `f` which is smooth near `x`, on a manifold with a boundaryless model, there is a partial
diffeomorphism `ψ` onto an open subset of `EuclideanSpace ℝ (Fin m)`, `m = dim M`, with
`ψ x = 0` and

`f y = f x - Σ_{i < λ} (ψ y)ᵢ² + Σ_{i ≥ λ} (ψ y)ᵢ²`

on its whole source, where `λ` is the manifold Morse index of `f` at `x`. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
      x ∈ ψ.source ∧ ψ x = 0 ∧ ∀ y ∈ ψ.source,
        f y = f x + ∑ i, (if i.val < manifoldMorseIndex I f x then -1 else 1) * ψ y i ^ 2 := by
  -- Work on the self-modelled copy of `M`, which has the same extended charts.
  set e := BoundarylessModel.diffeomorph I (M := M) ∞
  set x' := BoundarylessModel.homeomorph I M x
  have hx' : (BoundarylessModel.homeomorph I M).symm x' = x := Homeomorph.symm_apply_apply _ _
  have hsymm : ContMDiff 𝓘(ℝ, E) I ∞ (BoundarylessModel.homeomorph I M).symm := by
    rw [← BoundarylessModel.coe_diffeomorph_symm I ∞]
    exact e.symm.contMDiff
  have hg : ∀ᶠ y in 𝓝 x',
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (BoundarylessModel.homeomorph I M).symm) y := by
    rw [← hx'] at hf
    filter_upwards
      [((BoundarylessModel.homeomorph I M).symm.continuous.tendsto x').eventually hf] with y hy
    exact hy.comp y (hsymm y)
  have hcrit : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E)
      (f ∘ (BoundarylessModel.homeomorph I M).symm) x' := by
    rwa [BoundarylessModel.isManifoldNondegenerateCriticalPoint_iff, hx']
  obtain ⟨φ⟩ := hcrit.nonempty_morseChart hg
  have hsource : (e.toPartialDiffeomorph.trans φ.normalizedChart).source =
      BoundarylessModel.homeomorph I M ⁻¹' φ.toChart.source := by
    simp [e]
  have hcoe (y : M) : (e.toPartialDiffeomorph.trans φ.normalizedChart) y =
      φ.normalizedChart (BoundarylessModel.homeomorph I M y) := by
    simp [e]
  refine ⟨e.toPartialDiffeomorph.trans φ.normalizedChart, ?_, ?_, fun y hy ↦ ?_⟩
  · rw [hsource]
    exact φ.mem_source
  · rw [hcoe]
    exact φ.normalizedChart_apply_self
  · rw [hsource] at hy
    have hq := φ.eq_quadratic_normalizedChart (y := BoundarylessModel.homeomorph I M y) hy
    rw [BoundarylessModel.manifoldMorseIndex_eq, hx', ← hcoe] at hq
    simpa only [comp_apply, Homeomorph.symm_apply_apply, hx'] using hq

/-- **The two-dimensional saddle normal form.** At a nondegenerate critical point of index one
on a two-dimensional manifold, there are smooth Euclidean coordinates `(u, v)` centred at the
point in which `f = f x - u² + v²` on the whole chart source. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_twoDimensional_saddleChart
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hdim : Module.finrank ℝ E = 2)
    (hindex : manifoldMorseIndex I f x = 1) :
    ∃ ψ : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
      x ∈ ψ.source ∧ ψ x = 0 ∧ ∀ y ∈ ψ.source,
        f y = f x - (ψ y (finCongr hdim.symm 0)) ^ 2 +
          (ψ y (finCongr hdim.symm 1)) ^ 2 := by
  obtain ⟨ψ, hxψ, hψx, hψ⟩ := h.exists_normalized_morseChart hf
  refine ⟨ψ, hxψ, hψx, fun y hy ↦ ?_⟩
  rw [hψ y hy, hindex, ← Equiv.sum_comp (finCongr hdim.symm)
    (fun i ↦ (if i.val < 1 then -1 else 1) * ψ y i ^ 2), Fin.sum_univ_two]
  norm_num [Fin.val_cast]
  ring

/-- At a nondegenerate critical point whose Morse index is neither `0` nor `dim M`, two
coordinate-axis curves of a normalized Morse chart converge to the critical point through values
strictly below and strictly above its value. The curves are defined on all of `ℝ`; the
inequalities hold for every sufficiently small nonzero parameter. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_saddleCurves
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hpos : 0 < manifoldMorseIndex I f x)
    (hlt : manifoldMorseIndex I f x < Module.finrank ℝ E) :
    ∃ γneg γpos : ℝ → M,
      Tendsto γneg (𝓝 0) (𝓝 x) ∧ γneg 0 = x ∧
      Tendsto γpos (𝓝 0) (𝓝 x) ∧ γpos 0 = x ∧
      ∀ᶠ t in 𝓝[≠] 0, f (γneg t) < f x ∧ f x < f (γpos t) := by
  obtain ⟨ψ, hxψ, hψx, hψ⟩ := h.exists_normalized_morseChart hf
  -- Pull back the first (negative) and last (positive) coordinate axes through the inverse chart.
  let i0 : Fin (Module.finrank ℝ E) := ⟨0, hpos.trans hlt⟩
  let i1 : Fin (Module.finrank ℝ E) := ⟨Module.finrank ℝ E - 1, by omega⟩
  let uneg : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t ↦ EuclideanSpace.single i0 t
  let upos : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t ↦ EuclideanSpace.single i1 t
  let γneg : ℝ → M := fun t ↦ ψ.toOpenPartialHomeomorph.symm (uneg t)
  let γpos : ℝ → M := fun t ↦ ψ.toOpenPartialHomeomorph.symm (upos t)
  have huneg : Continuous uneg := by
    unfold uneg EuclideanSpace.single PiLp.single
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (Module.finrank ℝ E) ↦ ℝ)).comp
    apply continuous_pi
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> fun_prop
  have hupos : Continuous upos := by
    unfold upos EuclideanSpace.single PiLp.single
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (Module.finrank ℝ E) ↦ ℝ)).comp
    apply continuous_pi
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> fun_prop
  have hzero : (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∈ ψ.target := by
    simpa only [hψx] using ψ.map_source hxψ
  have hinvzero : ψ.toOpenPartialHomeomorph.symm 0 = x := by
    rw [← hψx]
    exact ψ.left_inv hxψ
  have huneg0 : uneg 0 = 0 := by simp [uneg]
  have hupos0 : upos 0 = 0 := by simp [upos]
  -- Openness of the chart target makes both inverse-chart curves valid near zero.
  have hunegTarget : ∀ᶠ t in 𝓝 0, uneg t ∈ ψ.target := by
    apply huneg.continuousAt
    simpa only [huneg0] using ψ.open_target.mem_nhds hzero
  have huposTarget : ∀ᶠ t in 𝓝 0, upos t ∈ ψ.target := by
    apply hupos.continuousAt
    simpa only [hupos0] using ψ.open_target.mem_nhds hzero
  have hγneg : Tendsto γneg (𝓝 0) (𝓝 x) := by
    have hcont : ContinuousAt ψ.toOpenPartialHomeomorph.symm (uneg 0) := by
      rw [huneg0]
      exact ψ.toOpenPartialHomeomorph.continuousAt_symm hzero
    have hbase : ψ.toOpenPartialHomeomorph.symm (uneg 0) = x := by
      rw [huneg0, hinvzero]
    rw [← hbase]
    -- `ContinuousAt.comp` bundles the displayed lambda as a function composition.
    change Tendsto (ψ.toOpenPartialHomeomorph.symm ∘ uneg) (𝓝 0)
      (𝓝 (ψ.toOpenPartialHomeomorph.symm (uneg 0)))
    exact hcont.comp (huneg.continuousAt : ContinuousAt uneg 0)
  have hγpos : Tendsto γpos (𝓝 0) (𝓝 x) := by
    have hcont : ContinuousAt ψ.toOpenPartialHomeomorph.symm (upos 0) := by
      rw [hupos0]
      exact ψ.toOpenPartialHomeomorph.continuousAt_symm hzero
    have hbase : ψ.toOpenPartialHomeomorph.symm (upos 0) = x := by
      rw [hupos0, hinvzero]
    rw [← hbase]
    -- `ContinuousAt.comp` bundles the displayed lambda as a function composition.
    change Tendsto (ψ.toOpenPartialHomeomorph.symm ∘ upos) (𝓝 0)
      (𝓝 (ψ.toOpenPartialHomeomorph.symm (upos 0)))
    exact hcont.comp (hupos.continuousAt : ContinuousAt upos 0)
  refine ⟨γneg, γpos, hγneg, by simp [γneg, huneg0, hinvzero], hγpos,
    by simp [γpos, hupos0, hinvzero], ?_⟩
  filter_upwards [hunegTarget.filter_mono nhdsWithin_le_nhds,
    huposTarget.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htn htp ht
  have hsourceNeg : γneg t ∈ ψ.source := ψ.map_target htn
  have hsourcePos : γpos t ∈ ψ.source := ψ.map_target htp
  have hrightNeg : ψ (γneg t) = uneg t := ψ.right_inv htn
  have hrightPos : ψ (γpos t) = upos t := ψ.right_inv htp
  have ht0 : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
  -- On the two axes the normalized Morse equation reduces respectively to `-t²` and `t²`.
  constructor
  · rw [hψ (γneg t) hsourceNeg, hrightNeg]
    simp [uneg, i0, EuclideanSpace.single, PiLp.single_apply, hpos]
    nlinarith [sq_pos_of_ne_zero ht0]
  · rw [hψ (γpos t) hsourcePos, hrightPos]
    have hle : ¬Module.finrank ℝ E - 1 < manifoldMorseIndex I f x := by omega
    simp [upos, i1, EuclideanSpace.single, PiLp.single_apply, hle]
    nlinarith [sq_pos_of_ne_zero ht0]

/-- At a nondegenerate critical point of Morse index `0` of a function smooth near it, on a
manifold with a boundaryless model, the function has a strict local minimum. -/
theorem IsManifoldNondegenerateCriticalPoint.eventually_lt_of_manifoldMorseIndex_eq_zero
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hidx : manifoldMorseIndex I f x = 0) :
    ∀ᶠ y in 𝓝[≠] x, f x < f y := by
  obtain ⟨ψ, hxψ, hψx, hψ⟩ := h.exists_normalized_morseChart hf
  filter_upwards [nhdsWithin_le_nhds (ψ.open_source.mem_nhds hxψ), self_mem_nhdsWithin]
    with y hy hyx
  -- With index `0` every sign is `+1`, so `f y - f x = ‖ψ y‖²`, and `ψ y ≠ 0` off the centre.
  rw [hψ y hy, hidx, lt_add_iff_pos_right]
  have hne : ψ y ≠ 0 := fun h0 ↦
    hyx (ψ.toOpenPartialHomeomorph.injOn hy hxψ (by simpa [hψx] using h0))
  obtain ⟨i, hi⟩ : ∃ i, ψ y i ≠ 0 := by
    by_contra! hall
    exact hne (PiLp.ext hall)
  simp only [Nat.not_lt_zero, ite_false, one_mul]
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩

/-- At a nondegenerate critical point of Morse index `dim M` of a function smooth near it, on a
manifold with a boundaryless model, the function has a strict local maximum. -/
theorem IsManifoldNondegenerateCriticalPoint.eventually_lt_of_manifoldMorseIndex_eq_finrank
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hidx : manifoldMorseIndex I f x = Module.finrank ℝ E) :
    ∀ᶠ y in 𝓝[≠] x, f y < f x := by
  -- `-f` has the complementary index `0` at `x`.
  have hneg : manifoldMorseIndex I (-f) x = 0 := by
    have := h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  filter_upwards [h.neg.eventually_lt_of_manifoldMorseIndex_eq_zero
    (hf.mono fun y hy ↦ contDiff_neg.contMDiff.contMDiffAt.comp y hy) hneg] with y hy
  simpa using hy

end TauCeti
