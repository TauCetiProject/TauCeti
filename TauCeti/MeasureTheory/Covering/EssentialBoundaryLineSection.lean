/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.Polish
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Essential boundaries of line sections

Let `s` be a Lebesgue-measurable set in a finite-dimensional real inner product space and `e` a
unit vector. For almost every `y` in the orthogonal hyperplane `(ℝ ∙ e)ᗮ`, a point of the
one-dimensional essential boundary of the line section `{t | y + t • e ∈ s}` either lies on the
essential boundary `∂ᵉs` of `s` or is an accumulation point of the parameters `t` at which the line
meets `∂ᵉs`. In particular, if a line meets `∂ᵉs` in finitely many points, the essential boundary
of its section consists of some of these points
(`TauCeti.ae_essentialBoundary_lineSection_subset`), and the same holds inside any open set of
parameters (`TauCeti.ae_essentialBoundary_lineSection_inter_subset`).

The finiteness hypothesis cannot be dropped. In the plane, let `S` be the union over `j` of the
strips `A_j × [r_j, 2 r_j]`, where `r_j → 0` quickly and the sets `A_j ⊆ ℝ` are periodic with
periods much smaller than `r_j`, have densities tending to `0`, and are arranged in blocks so that
every vertical line meets infinitely many of them. Then `(y, 0)` is a point of density one of
`s = Sᶜ` for every `y`, while `0` lies on the essential boundary of every vertical line section.
Such a set has infinite perimeter near the horizontal axis; for a set whose essential boundary has
locally finite `Hⁿ⁻¹` measure, almost every line meets `∂ᵉs` in a locally finite set.

The proof follows Evans and Gariepy. Let `I` and `O` be the essential interior and exterior of `s`.
Their points lie in closed sets `G k` around which `sᶜ`, respectively `s`, fills at most a small
fraction `c` of every ball of radius below `1 / (k + 1)`. The key estimate
(`volume_setOf_exists_eq_zero`) is that the points of such a closed set from which a segment
parallel to `e` runs into `O` (respectively `I`) lie on a null set of lines: in every ball of the
hyperplane, stacking these segments above the points of almost maximal height produces a set of
volume comparable to the ball, inside a ball where `sᶜ` is sparse. On any other line, an open
interval of parameters avoiding `∂ᵉs` lies in `I` or in `O`. Otherwise, by Baire's theorem applied
to the parameters in the closures of both parts, some `G k` contains all such parameters near one
of them, and the end of a maximal run of `O` next to it starts a segment in `O` from a point of
`G k`. Lebesgue's density theorem then identifies the line section with `I` or `O` near every
parameter off `∂ᵉs`.

## Main results

* `TauCeti.ae_essentialBoundary_lineSection_inter_subset`: for almost every line parallel to `e`
  and every open set `U ⊆ ℝ` of parameters at which the line meets `∂ᵉs` finitely often, the
  essential boundary of the line section inside `U` lies on `∂ᵉs`.
* `TauCeti.ae_essentialBoundary_lineSection_subset`: the version with `U = ℝ`.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.11, proof of Theorem 5.23 (Claims 1 and 2).
* H. Federer, *Geometric Measure Theory*, 4.5.11.
-/

public section

open Filter Metric MeasureTheory Module Set Topology
open scoped ENNReal Pointwise

namespace TauCeti

/-! ### Closedness and a density criterion for null sets -/

section Metric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The points around which a set fills at most a prescribed amount `K r` of every open ball of
radius `r < ρ` form a closed set. -/
private theorem isClosed_setOf_forall_measure_inter_ball_le (μ : Measure X) (A : Set X) (ρ : ℝ)
    (K : ℝ → ℝ≥0∞) : IsClosed {x | ∀ r ∈ Ioo 0 ρ, μ (A ∩ ball x r) ≤ K r} := by
  refine closure_subset_iff_isClosed.1 fun x hx r hr => ?_
  have hrestr (z : X) (ρ' : ℝ) : μ (A ∩ ball z ρ') = μ.restrict A (ball z ρ') := by
    rw [Measure.restrict_apply measurableSet_ball, inter_comm]
  rw [hrestr]
  refine Measure.measure_ball_le_of_forall_lt _ fun r' hr' => ?_
  obtain ⟨x', hx', hxx'⟩ := Metric.mem_closure_iff.1 hx (r - r') (sub_pos.2 hr')
  rw [← hrestr]
  calc μ (A ∩ ball x r') ≤ μ (A ∩ ball x' r) :=
        measure_mono (inter_subset_inter_right _ (ball_subset_ball' (by linarith)))
    _ ≤ K r := hx' r hr

end Metric

section Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [SecondCountableTopology X]
  [BorelSpace X] [HasBesicovitchCovering X]

/-- A set filling at most half of every small closed ball around every point is null, by
Lebesgue's density theorem. No measurability is assumed. -/
private theorem measure_eq_zero_of_forall_measure_inter_closedBall_le (ν : Measure X)
    [IsLocallyFiniteMeasure ν] (Q : Set X)
    (h : ∀ z, ∀ᶠ r in 𝓝[>] 0, ν (Q ∩ closedBall z r) ≤ 2⁻¹ * ν (closedBall z r)) : ν Q = 0 := by
  by_contra hQ
  have : (ae (ν.restrict Q)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  obtain ⟨z, hz⟩ := (Besicovitch.ae_tendsto_measure_inter_div ν Q).exists
  have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Q ∩ closedBall z r) / ν (closedBall z r) ≤ 2⁻¹ :=
    (h z).mono fun r hr => ENNReal.div_le_of_le_mul hr
  exact absurd (le_of_tendsto hz h1) (not_le.2 (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))

end Besicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Lines leaving a point of small density into a set -/

/-- The set `A` fills at most `c` times the volume of each closed ball of radius `r < ρ` in the
open ball of radius `r` around `x`. -/
private def SparseAt (c : ℝ≥0∞) (ρ : ℝ) (A : Set E) (x : E) : Prop :=
  ∀ r ∈ Ioo 0 ρ, volume (A ∩ ball x r) ≤ c * volume (closedBall (0 : E) r)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point `q + τ • e` above a base point `q` lies in `C`, and near a point `yb + tb • e`, when
`q` is close to `yb` and the heights `σ * tq` and `σ * τ` sit just below and just above
`σ * tb`, for a point `q + tq • e` from which the segment of length `δ` in the direction `σ • e`
lies in `C`. -/
private theorem add_smul_mem_inter_ball (e : E) (he : ‖e‖ = 1) {C : Set E} {δ σ r : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hr : 0 < r) (hrδ : 2 * r < δ) {q yb : (ℝ ∙ e)ᗮ} {tq tb τ : ℝ}
    (hCq : ∀ τ ∈ Ioo 0 δ, (q : E) + (tq + σ * τ) • e ∈ C) (hlow : σ * tb - δ / 2 < σ * tq)
    (hup : σ * tq < σ * tb + r / 2) (hτ : σ * τ ∈ Icc (σ * tb + r / 2) (σ * tb + r))
    (hdist : dist q yb ≤ 2 * r) :
    (q : E) + τ • e ∈ C ∩ ball ((yb : E) + tb • e) (4 * r) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · have hτ' : (q : E) + τ • e = (q : E) + (tq + σ * (σ * τ - σ * tq)) • e := by
      congr 2
      linear_combination (tq - τ) * hσσ
    rw [hτ']
    exact hCq _ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  · have htb : |τ - tb| ≤ r := by
      rw [← one_mul |τ - tb|, ← hσabs, ← abs_mul, abs_le]
      constructor <;> nlinarith [hτ.1, hτ.2]
    rw [mem_ball, dist_eq_norm]
    calc ‖(q : E) + τ • e - ((yb : E) + tb • e)‖ = ‖((q : E) - yb) + (τ - tb) • e‖ := by
          rw [sub_smul]
          abel_nf
      _ ≤ ‖(q : E) - yb‖ + ‖(τ - tb) • e‖ := norm_add_le _ _
      _ = dist q yb + |τ - tb| := by
          rw [norm_smul, he, mul_one, Real.norm_eq_abs, ← dist_eq_norm, Subtype.dist_eq]
      _ < 4 * r := by linarith

/-- The dimension count behind `volume_inter_closedBall_le`: if a set `S` of the hyperplane times
a segment of length `r / 2` has volume at most `c` times that of a ball of radius `4 r` in `E`,
then `S` fills at most half of a ball of radius `r` of the hyperplane, for `c` small enough. -/
private theorem volume_le_inv_two_mul (e : E) (he : ‖e‖ = 1) {c : ℝ≥0∞}
    (hc : c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) ≤
      2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1))
    {S : Set (ℝ ∙ e)ᗮ} (z : (ℝ ∙ e)ᗮ) {r : ℝ} (hr : 0 < r)
    (h : volume S * ENNReal.ofReal (r / 2) ≤ c * volume (closedBall (0 : E) (4 * r))) :
    volume S ≤ 2⁻¹ * volume (closedBall z r) := by
  have hdim : finrank ℝ E = finrank ℝ (ℝ ∙ e)ᗮ + 1 := by
    rw [← (ℝ ∙ e).finrank_add_finrank_orthogonal, finrank_span_singleton (by
      rintro rfl
      simp at he), add_comm]
  set d := finrank ℝ (ℝ ∙ e)ᗮ
  have hpow : ENNReal.ofReal ((4 * r) ^ finrank ℝ E) =
      ENNReal.ofReal (2 * 4 ^ finrank ℝ E) * ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hdim]
    congr 1
    ring
  have hr2 : ENNReal.ofReal (r / 2) ≠ 0 := by simpa using hr
  refine (ENNReal.mul_le_mul_iff_left hr2 ENNReal.ofReal_ne_top).1 (h.trans ?_)
  rw [Measure.addHaar_closedBall _ _ hr.le, Measure.addHaar_closedBall _ _ (by positivity), hpow]
  calc c * (ENNReal.ofReal (2 * 4 ^ finrank ℝ E) * ENNReal.ofReal (r ^ d) *
        ENNReal.ofReal (r / 2) * volume (ball (0 : E) 1))
      = c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) *
          (ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r / 2)) := by ring
    _ ≤ 2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1) *
          (ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r / 2)) := by gcongr
    _ = 2⁻¹ * (ENNReal.ofReal (r ^ d) * volume (ball (0 : (ℝ ∙ e)ᗮ) 1)) *
          ENNReal.ofReal (r / 2) := by ring

/-- The core estimate. Points `y + t • e` around which `A` is sparse below scale `ρ`, and from
which the segment of length `δ` in the direction `σ • e` lies in `C ⊆ A`, are sorted by the height
`σ * t` into slabs of thickness `δ / 2`. In every closed ball of radius `r` of the hyperplane, the
base points `y` coming from one slab fill at most half of the ball. Indeed, take a point `b` of the
slab over the ball at almost maximal height. Above every such base point, the segment of heights
between `σ * t_b + r / 2` and `σ * t_b + r` lies in `C` and in the ball of radius `4 r` around `b`,
where `A` is sparse. -/
private theorem volume_inter_closedBall_le (e : E) (he : ‖e‖ = 1) {A C : Set E}
    (hCA : C ≤ᵐ[volume] A) {c : ℝ≥0∞}
    (hc : c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) ≤
      2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1))
    {ρ δ σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (j : ℤ) (z : (ℝ ∙ e)ᗮ) {r : ℝ} (hr : 0 < r)
    (hrρ : 4 * r < ρ) (hrδ : 2 * r < δ) :
    volume ({y : (ℝ ∙ e)ᗮ | ∃ t : ℝ, (SparseAt c ρ A ((y : E) + t • e) ∧
      ∀ τ ∈ Ioo 0 δ, (y : E) + (t + σ * τ) • e ∈ C) ∧
      σ * t ∈ Ico (j * (δ / 2)) ((j + 1) * (δ / 2))} ∩ closedBall z r) ≤
      2⁻¹ * volume (closedBall z r) := by
  set S := {y : (ℝ ∙ e)ᗮ | ∃ t : ℝ, (SparseAt c ρ A ((y : E) + t • e) ∧
      ∀ τ ∈ Ioo 0 δ, (y : E) + (t + σ * τ) • e ∈ C) ∧
      σ * t ∈ Ico (j * (δ / 2)) ((j + 1) * (δ / 2))} ∩ closedBall z r
  rcases S.eq_empty_or_nonempty with hS | ⟨y₀, ⟨t₀, ht₀, ht₀j⟩, hy₀⟩
  · simp [hS]
  -- the heights of the points over the ball, and a point `b` of almost maximal height
  set W := {w : ℝ | ∃ y ∈ S, ∃ t : ℝ, (SparseAt c ρ A ((y : E) + t • e) ∧
      ∀ τ ∈ Ioo 0 δ, (y : E) + (t + σ * τ) • e ∈ C) ∧
      σ * t ∈ Ico (j * (δ / 2)) ((j + 1) * (δ / 2)) ∧ w = σ * t}
  have hWbdd : BddAbove W := ⟨(j + 1) * (δ / 2), by
    rintro _ ⟨_, _, t, _, htj, rfl⟩
    exact htj.2.le⟩
  have hWne : W.Nonempty := ⟨σ * t₀, y₀, ⟨⟨t₀, ht₀, ht₀j⟩, hy₀⟩, t₀, ht₀, ht₀j, rfl⟩
  obtain ⟨_, ⟨yb, hyb, tb, hLb, hjb, rfl⟩, hb⟩ :=
    exists_lt_of_lt_csSup hWne (sub_lt_self (sSup W) (half_pos hr))
  -- the region above `S` lies in `C` near `b`, where `A` is sparse
  have hreg : S ×ˢ ((σ * ·) ⁻¹' Icc (σ * tb + r / 2) (σ * tb + r)) ⊆
      orthogonalLineEquiv e he ⁻¹' (C ∩ ball ((yb : E) + tb • e) (4 * r)) := by
    rintro ⟨q, τ⟩ ⟨hq, hτ⟩
    obtain ⟨⟨tq, hLq, hjq⟩, hqz⟩ := hq
    have hqW : σ * tq ≤ sSup W := le_csSup hWbdd ⟨q, ⟨⟨tq, hLq, hjq⟩, hqz⟩, tq, hLq, hjq, rfl⟩
    have := hjq.1
    have := hjb.2
    have := hyb.2
    rw [mem_closedBall] at hqz this
    rw [mem_preimage, orthogonalLineEquiv_apply]
    exact add_smul_mem_inter_ball e he hσ hr hrδ hLq.2 (by push_cast at *; linarith)
      (by linarith) hτ ((dist_triangle_right q yb z).trans (by linarith))
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ⁻¹| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine volume_le_inv_two_mul e he hc z hr ?_
  calc volume S * ENNReal.ofReal (r / 2)
      = (volume.prod volume) (S ×ˢ ((σ * ·) ⁻¹' Icc (σ * tb + r / 2) (σ * tb + r))) := by
        rw [Measure.prod_prod, Real.volume_preimage_mul_left hσ0, Real.volume_Icc, hσabs]
        norm_num
        ring_nf
    _ ≤ (volume.prod volume)
          (orthogonalLineEquiv e he ⁻¹' (C ∩ ball ((yb : E) + tb • e) (4 * r))) :=
        measure_mono hreg
    _ = volume (C ∩ ball ((yb : E) + tb • e) (4 * r)) :=
        MeasurePreserving.measure_preimage_equiv
          (f := (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv)
          (measurePreserving_orthogonalLineEquiv e he) _
    _ ≤ volume (A ∩ ball ((yb : E) + tb • e) (4 * r)) :=
        measure_mono_ae (hCA.inter Filter.EventuallySubset.rfl)
    _ ≤ c * volume (closedBall (0 : E) (4 * r)) := hLb.1 _ ⟨by linarith, hrρ⟩

/-- The points `y + t • e` around which `A` is sparse below scale `ρ`, and from which the segment
of length `δ` in the direction `σ • e` lies in `C ⊆ A`, lie over a null set of the hyperplane.
This is Claim 1 in the proof of Evans–Gariepy, Theorem 5.23. -/
private theorem volume_setOf_exists_eq_zero (e : E) (he : ‖e‖ = 1) {A C : Set E}
    (hCA : C ≤ᵐ[volume] A) {c : ℝ≥0∞}
    (hc : c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) ≤
      2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1))
    {ρ δ σ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1) :
    volume {y : (ℝ ∙ e)ᗮ | ∃ t : ℝ, SparseAt c ρ A ((y : E) + t • e) ∧
      ∀ τ ∈ Ioo 0 δ, (y : E) + (t + σ * τ) • e ∈ C} = 0 := by
  refine measure_mono_null (t := ⋃ j : ℤ, {y : (ℝ ∙ e)ᗮ | ∃ t : ℝ,
      (SparseAt c ρ A ((y : E) + t • e) ∧ ∀ τ ∈ Ioo 0 δ, (y : E) + (t + σ * τ) • e ∈ C) ∧
      σ * t ∈ Ico (j * (δ / 2)) ((j + 1) * (δ / 2))}) (fun y hy => ?_)
    (measure_iUnion_null fun j : ℤ =>
    measure_eq_zero_of_forall_measure_inter_closedBall_le _ _ fun z => ?_)
  · obtain ⟨t, ht⟩ := hy
    refine mem_iUnion.2 ⟨⌊σ * t / (δ / 2)⌋, t, ht, ?_, ?_⟩
    · have := Int.floor_le (σ * t / (δ / 2))
      rwa [le_div_iff₀ (by positivity)] at this
    · have := Int.lt_floor_add_one (σ * t / (δ / 2))
      rwa [div_lt_iff₀ (by positivity)] at this
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (ρ / 4) (δ / 2) by positivity)] with r hr
    have h1 := hr.2.trans_le (min_le_left _ _)
    have h2 := hr.2.trans_le (min_le_right _ _)
    exact volume_inter_closedBall_le e he hCA hc hσ j z hr.1 (by linarith) (by linarith)

/-- A constant `c` small enough for `volume_setOf_exists_eq_zero` and for
`not_sparseAt_compl_and_sparseAt`. -/
private theorem exists_const (e : E) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ 2 * c < 1 ∧
      c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) ≤
        2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1) := by
  set X := volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E)
  set Y := 2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1)
  have hX : X ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hX0 : X ≠ 0 := mul_ne_zero (measure_ball_pos _ _ one_pos).ne' (by simp)
  have hY : Y ≠ 0 := mul_ne_zero (by simp) (measure_ball_pos _ _ one_pos).ne'
  refine ⟨min 4⁻¹ (Y / X), (lt_min (by simp) (ENNReal.div_pos hY hX)).ne', ?_, ?_⟩
  · calc 2 * min 4⁻¹ (Y / X) ≤ 2 * 4⁻¹ := by gcongr; exact min_le_left _ _
      _ < 1 := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
          ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
        exact ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  · rw [mul_assoc]
    calc min 4⁻¹ (Y / X) * X ≤ Y / X * X := by gcongr; exact min_le_right _ _
      _ = Y := ENNReal.div_mul_cancel hX0 hX

/-- Around a point of the essential interior of a null-measurable set `s`, the complement is
sparse at some scale `1 / (k + 1)`. -/
private theorem exists_nat_sparseAt_compl {s : Set E} (hs : NullMeasurableSet s volume) {x : E}
    (hx : x ∈ essentialInterior volume s) {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∃ k : ℕ, SparseAt c (1 / (k + 1)) sᶜ x := by
  have h0 : HasDensityAt volume sᶜ x 0 := by
    simpa using (mem_essentialInterior.1 hx).compl hs
      (eventually_measure_closedBall_ne_zero_ne_top volume x)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      volume (sᶜ ∩ closedBall x r) / volume (closedBall x r) < c :=
    (hasDensityAt_iff.1 h0).eventually (gt_mem_nhds (pos_iff_ne_zero.2 hc))
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ρ from hρ)
  refine ⟨k, fun r hr => ?_⟩
  have hlt : volume (sᶜ ∩ closedBall x r) / volume (closedBall x r) < c :=
    hsub ⟨hr.1, hr.2.trans hk⟩
  rw [ENNReal.div_lt_iff (Or.inl (measure_closedBall_pos _ _ hr.1).ne')
    (Or.inl measure_closedBall_lt_top.ne)] at hlt
  calc volume (sᶜ ∩ ball x r) ≤ volume (sᶜ ∩ closedBall x r) :=
        measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
    _ ≤ c * volume (closedBall x r) := hlt.le
    _ = c * volume (closedBall (0 : E) r) := by rw [Measure.addHaar_closedBall_center]

/-- A set and its complement cannot both be sparse around a point for `c < 1 / 2`. -/
private theorem not_sparseAt_compl_and_sparseAt [Nontrivial E] {s : Set E} {c : ℝ≥0∞}
    (hc : 2 * c < 1) {x : E} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (h : SparseAt c ρ sᶜ x) (h' : SparseAt c ρ' s x) : False := by
  set r := min ρ ρ' / 2 with hr_def
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hr_def]; linarith [min_le_left ρ ρ']
  have hrρ' : r < ρ' := by rw [hr_def]; linarith [min_le_right ρ ρ']
  have hcb : volume (closedBall (0 : E) r) = volume (ball x r) := by
    rw [← Measure.addHaar_closedBall_center volume x, Measure.addHaar_closedBall_eq_addHaar_ball]
  have hle : 1 * volume (ball x r) ≤ (2 * c) * volume (ball x r) := calc
    1 * volume (ball x r) ≤ volume (s ∩ ball x r) + volume (sᶜ ∩ ball x r) := by
        rw [one_mul]
        refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
        by_cases hzs : z ∈ s
        exacts [Or.inl ⟨hzs, hz⟩, Or.inr ⟨hzs, hz⟩]
    _ ≤ c * volume (ball x r) + c * volume (ball x r) := by
        rw [← hcb]
        exact add_le_add (h' r ⟨hr, hrρ'⟩) (h r ⟨hr, hrρ⟩)
    _ = (2 * c) * volume (ball x r) := by ring
  exact absurd ((ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ hr).ne'
    measure_ball_lt_top.ne).1 hle) (not_le.2 hc)

/-! ### Separating essential interior and exterior points on a line -/

/-- If `t₀ < o`, `t₀` lies in the closure of `P` but `o` does not, and `[t₀, o]` is covered by
`P` and `N`, then some point `a ∈ [t₀, o]` lies in both closures, and a segment to the right of `a`
lies in `N`. -/
private theorem exists_mem_forall_add_mem_of_lt (P N g : Set ℝ) {t₀ o : ℝ} (hto : t₀ < o)
    (ht₀ : t₀ ∈ closure P) (ho : o ∉ closure P) (hcover : Icc t₀ o ⊆ P ∪ N)
    (hg : ∀ t ∈ Icc t₀ o, t ∈ closure P → t ∈ closure N → t ∈ g) :
    ∃ a ∈ g, ∃ δ > 0, ∀ τ ∈ Ioo 0 δ, a + τ ∈ N := by
  set K := closure P ∩ Icc t₀ o
  have hKbdd : BddAbove K := ⟨o, fun t ht => ht.2.2⟩
  have haK : sSup K ∈ K := (isClosed_closure.inter isClosed_Icc).csSup_mem
    ⟨t₀, ht₀, left_mem_Icc.2 hto.le⟩ hKbdd
  have hao : sSup K < o := lt_of_le_of_ne haK.2.2 fun h => ho (h ▸ haK.1)
  have hN : Ioc (sSup K) o ⊆ N := fun t ht => by
    have htI : t ∈ Icc t₀ o := ⟨haK.2.1.trans ht.1.le, ht.2⟩
    have htP : t ∉ closure P := fun h => (not_le.2 ht.1) (le_csSup hKbdd ⟨h, htI⟩)
    exact (hcover htI).resolve_left fun h => htP (subset_closure h)
  refine ⟨sSup K, hg _ haK.2 haK.1 ?_, o - sSup K, sub_pos.2 hao,
    fun τ hτ => hN ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  have : sSup K ∈ closure (Ioo (sSup K) o) := by
    rw [closure_Ioo hao.ne]
    exact left_mem_Icc.2 hao.le
  exact closure_mono (Ioo_subset_Ioc_self.trans hN) this

/-- The mirror image of `exists_mem_forall_add_mem_of_lt`. -/
private theorem exists_mem_forall_sub_mem_of_lt (P N g : Set ℝ) {t₀ o : ℝ} (hot : o < t₀)
    (ht₀ : t₀ ∈ closure P) (ho : o ∉ closure P) (hcover : Icc o t₀ ⊆ P ∪ N)
    (hg : ∀ t ∈ Icc o t₀, t ∈ closure P → t ∈ closure N → t ∈ g) :
    ∃ a ∈ g, ∃ δ > 0, ∀ τ ∈ Ioo 0 δ, a + -1 * τ ∈ N := by
  obtain ⟨a, ha, δ, hδ, h⟩ := exists_mem_forall_add_mem_of_lt (-P) (-N) (-g) (neg_lt_neg hot)
    (by rwa [← neg_closure, Set.mem_neg, neg_neg]) (by rwa [← neg_closure, Set.mem_neg, neg_neg])
    (fun t ht => by
      simpa using hcover (show -t ∈ Icc o t₀ from ⟨by linarith [ht.2], by linarith [ht.1]⟩))
    (fun t ht h1 h2 => by
      rw [← neg_closure] at h1 h2
      exact hg (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ h1 h2)
  refine ⟨-a, ha, δ, hδ, fun τ hτ => ?_⟩
  have := h τ hτ
  rw [Set.mem_neg] at this
  convert this using 1
  ring

/-- Let `P` and `N` cover an open set `T`, and let `W` be open. If every point of `T ∩ W` in the
closures of both `P` and `N` lies in a set `g` disjoint from `N`, and there is such a point, then
some point of `g` is followed, on one side, by a segment contained in `N`. -/
private theorem exists_mem_forall_add_mul_mem (T W P N g : Set ℝ) (hT : IsOpen T) (hW : IsOpen W)
    (hTPN : T ⊆ P ∪ N) (hgN : Disjoint g N)
    (hZ : T ∩ (closure P ∩ closure N) ∩ W ⊆ g) {t₀ : ℝ}
    (ht₀ : t₀ ∈ T ∩ (closure P ∩ closure N) ∩ W) :
    ∃ a ∈ g, ∃ δ > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hT.inter hW) t₀ ⟨ht₀.1.1, ht₀.2⟩
  obtain ⟨o, hoN, hdo⟩ := Metric.mem_closure_iff.1 ht₀.1.2.2 ε hε
  have hg' (t : ℝ) (ht : t ∈ ball t₀ ε) (h1 : t ∈ closure P) (h2 : t ∈ closure N) : t ∈ g :=
    hZ ⟨⟨(hball ht).1, h1, h2⟩, (hball ht).2⟩
  have hoP : o ∉ closure P := fun h =>
    hgN.ne_of_mem (hg' o (by rwa [mem_ball, dist_comm]) h (subset_closure hoN)) hoN rfl
  have hoball : o ∈ ball t₀ ε := by rwa [mem_ball, dist_comm]
  have hIcc {u v : ℝ} (hu : u ∈ ball t₀ ε) (hv : v ∈ ball t₀ ε) : Icc u v ⊆ ball t₀ ε :=
    (convex_ball t₀ ε).ordConnected.out hu hv
  have hcov (t : ℝ) (ht : t ∈ ball t₀ ε) : t ∈ P ∪ N := hTPN (hball ht).1
  have ht₀g : t₀ ∈ g := hZ ht₀
  rcases lt_trichotomy t₀ o with h | rfl | h
  · obtain ⟨a, ha, δ, hδ, hN⟩ := exists_mem_forall_add_mem_of_lt P N g h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc (mem_ball_self hε) hoball ht))
      (fun t ht => hg' t (hIcc (mem_ball_self hε) hoball ht))
    exact ⟨a, ha, δ, hδ, 1, Or.inl rfl, by simpa using hN⟩
  · exact absurd hoN (hgN.notMem_of_mem_left ht₀g)
  · obtain ⟨a, ha, δ, hδ, hN⟩ := exists_mem_forall_sub_mem_of_lt P N g h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc hoball (mem_ball_self hε) ht))
      (fun t ht => hg' t (hIcc hoball (mem_ball_self hε) ht))
    exact ⟨a, ha, δ, hδ, -1, Or.inr rfl, hN⟩

/-- **A Baire category argument on a line.** Let an open preconnected set `T ⊆ ℝ` be covered by
sets `P` and `N`, and cover `P` and `N` by countably many closed sets `gP k`, disjoint from `N`,
and `gN k`, disjoint from `P`. If no point of a `gP k` is followed on either side by a segment in
`N`, and no point of a `gN k` by a segment in `P`, then `T` misses `P` or misses `N`. -/
private theorem disjoint_or_disjoint_of_isPreconnected {T P N : Set ℝ} (hT : IsOpen T)
    (hTc : IsPreconnected T) (hTPN : T ⊆ P ∪ N) (gP gN : ℕ → Set ℝ)
    (hgP : ∀ k, IsClosed (gP k)) (hgN : ∀ k, IsClosed (gN k)) (hPg : P ⊆ ⋃ k, gP k)
    (hNg : N ⊆ ⋃ k, gN k) (hdP : ∀ k, Disjoint (gP k) N) (hdN : ∀ k, Disjoint (gN k) P)
    (hbP : ∀ k a δ σ, a ∈ gP k → 0 < δ → (σ = 1 ∨ σ = -1) → ¬ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ N)
    (hbN : ∀ k a δ σ, a ∈ gN k → 0 < δ → (σ = 1 ∨ σ = -1) → ¬ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ P) :
    Disjoint T P ∨ Disjoint T N := by
  by_contra! h
  obtain ⟨⟨p, hpT, hpP⟩, ⟨q, hqT, hqN⟩⟩ :=
    And.intro (not_disjoint_iff.1 h.1) (not_disjoint_iff.1 h.2)
  set Z := T ∩ (closure P ∩ closure N)
  obtain ⟨z₀, hz₀⟩ : Z.Nonempty := isPreconnected_closed_iff.1 hTc _ _ isClosed_closure
    isClosed_closure (hTPN.trans (union_subset_union subset_closure subset_closure))
    ⟨p, hpT, subset_closure hpP⟩ ⟨q, hqT, subset_closure hqN⟩
  have hZG : IsGδ Z := hT.isGδ.inter (isClosed_closure.inter isClosed_closure).isGδ
  have := hZG.isCompletelyMetrizableSpace
  have : Nonempty Z := ⟨⟨z₀, hz₀⟩⟩
  have hfc : ∀ i, IsClosed (Sum.elim (fun k => ((↑) : Z → ℝ) ⁻¹' gP k)
      (fun k => ((↑) : Z → ℝ) ⁻¹' gN k) i) := by
    rintro (k | k)
    exacts [(hgP k).preimage continuous_subtypeVal, (hgN k).preimage continuous_subtypeVal]
  have hfU : ⋃ i, Sum.elim (fun k => ((↑) : Z → ℝ) ⁻¹' gP k)
      (fun k => ((↑) : Z → ℝ) ⁻¹' gN k) i = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    rcases hTPN z.property.1 with hz | hz
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hPg hz)
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hNg hz)
      exact ⟨Sum.inr k, hk⟩
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  obtain ⟨V, hVf, hVo, hzV⟩ := mem_interior.1 hz
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hVo
  rcases i with k | k
  · obtain ⟨a, ha, δ, hδ, σ, hσ, haN⟩ := exists_mem_forall_add_mul_mem T W P N (gP k) hT hWo
      hTPN (hdP k) (fun t ht => hVf (show (⟨t, ht.1⟩ : Z) ∈ (↑) ⁻¹' W from ht.2)) ⟨z.property, hzV⟩
    exact hbP k a δ σ ha hδ hσ haN
  · obtain ⟨a, ha, δ, hδ, σ, hσ, haP⟩ := exists_mem_forall_add_mul_mem T W N P (gN k) hT hWo
      (by rwa [union_comm]) (hdN k)
      (fun t ht => hVf (show (⟨t, ht.1.1, ht.1.2.2, ht.1.2.1⟩ : Z) ∈ (↑) ⁻¹' W from ht.2))
      ⟨⟨z.property.1, z.property.2.2, z.property.2.1⟩, hzV⟩
    exact hbN k a δ σ ha hδ hσ haP


/-! ### The main theorem -/

/-- On a line `t ↦ y + t • e` that avoids the null sets of `volume_setOf_exists_eq_zero` for the
essential interior `I` and exterior `O` of `s`, an open interval of parameters covered by `I` and
`O` misses one of them. -/
private theorem disjoint_or_disjoint_of_isPreconnected_lineSection [Nontrivial E] {s : Set E}
    (hs : NullMeasurableSet s volume) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc2 : 2 * c < 1) {e : E}
    {y : (ℝ ∙ e)ᗮ}
    (hO : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ k m : ℕ, ∀ t : ℝ,
      SparseAt c (1 / (k + 1)) sᶜ ((y : E) + t • e) →
      ¬ ∀ τ ∈ Ioo (0 : ℝ) (1 / (m + 1)), (y : E) + (t + σ * τ) • e ∈ essentialExterior volume s)
    (hI : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ k m : ℕ, ∀ t : ℝ,
      SparseAt c (1 / (k + 1)) s ((y : E) + t • e) →
      ¬ ∀ τ ∈ Ioo (0 : ℝ) (1 / (m + 1)), (y : E) + (t + σ * τ) • e ∈ essentialInterior volume s)
    {T : Set ℝ} (hT : IsOpen T) (hTc : IsPreconnected T)
    (hTPN : T ⊆ {t | (y : E) + t • e ∈ essentialInterior volume s} ∪
      {t | (y : E) + t • e ∈ essentialExterior volume s}) :
    Disjoint T {t | (y : E) + t • e ∈ essentialInterior volume s} ∨
      Disjoint T {t | (y : E) + t • e ∈ essentialExterior volume s} := by
  have hG (A : Set E) (k : ℕ) : IsClosed {t : ℝ | SparseAt c (1 / (k + 1)) A ((y : E) + t • e)} :=
    (isClosed_setOf_forall_measure_inter_ball_le volume A _ _).preimage
      (continuous_const.add (continuous_id.smul continuous_const))
  have hPg : {t | (y : E) + t • e ∈ essentialInterior volume s} ⊆
      ⋃ k : ℕ, {t : ℝ | SparseAt c (1 / (k + 1)) sᶜ ((y : E) + t • e)} :=
    fun t ht => mem_iUnion.2 (exists_nat_sparseAt_compl hs ht hc0)
  have hNg : {t | (y : E) + t • e ∈ essentialExterior volume s} ⊆
      ⋃ k : ℕ, {t : ℝ | SparseAt c (1 / (k + 1)) s ((y : E) + t • e)} := fun t ht =>
    mem_iUnion.2 (by
      simpa using exists_nat_sparseAt_compl hs.compl (by rwa [essentialInterior_compl hs]) hc0)
  have hpos (k : ℕ) : (0 : ℝ) < 1 / (k + 1) := by positivity
  refine disjoint_or_disjoint_of_isPreconnected hT hTc hTPN _ _ (hG sᶜ) (hG s) hPg hNg
    (fun k => disjoint_left.2 fun t h h' => ?_) (fun k => disjoint_left.2 fun t h h' => ?_)
    (fun k a δ σ ha hδ hσ hall => ?_) (fun k a δ σ ha hδ hσ hall => ?_)
  · obtain ⟨k', hk'⟩ := mem_iUnion.1 (hNg h')
    exact not_sparseAt_compl_and_sparseAt hc2 (hpos k) (hpos k') h hk'
  · obtain ⟨k', hk'⟩ := mem_iUnion.1 (hPg h')
    exact not_sparseAt_compl_and_sparseAt hc2 (hpos k') (hpos k) hk' h
  · obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact hO σ hσ k m a ha fun τ hτ => hall τ ⟨hτ.1, hτ.2.trans hm⟩
  · obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact hI σ hσ k m a ha fun τ hτ => hall τ ⟨hτ.1, hτ.2.trans hm⟩

/-- The lines meeting a set of `volume_setOf_exists_eq_zero` at some scales `1 / (k + 1)` and
`1 / (m + 1)` form a null set. -/
private theorem ae_forall_not_sparseAt_and (e : E) (he : ‖e‖ = 1) {A C : Set E}
    (hCA : C ≤ᵐ[volume] A) {c : ℝ≥0∞}
    (hc : c * volume (ball (0 : E) 1) * ENNReal.ofReal (2 * 4 ^ finrank ℝ E) ≤
      2⁻¹ * volume (ball (0 : (ℝ ∙ e)ᗮ) 1)) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ k m : ℕ, ∀ t : ℝ,
      SparseAt c (1 / (k + 1)) A ((y : E) + t • e) →
      ¬ ∀ τ ∈ Ioo (0 : ℝ) (1 / (m + 1)), (y : E) + (t + σ * τ) • e ∈ C := by
  have h (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : ∀ᵐ y : (ℝ ∙ e)ᗮ, ∀ k m : ℕ, ∀ t : ℝ,
      SparseAt c (1 / (k + 1)) A ((y : E) + t • e) →
      ¬ ∀ τ ∈ Ioo (0 : ℝ) (1 / (m + 1)), (y : E) + (t + σ * τ) • e ∈ C := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun m => ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_setOf_exists_eq_zero e he hCA hc
      (ρ := 1 / (k + 1)) (δ := 1 / (m + 1)) (by positivity) (by positivity) hσ)] with y hy t ht hτ
    exact hy ⟨t, ht, hτ⟩
  filter_upwards [h 1 (Or.inl rfl), h (-1) (Or.inr rfl)] with y h₁ hm₁ σ hσ
  rcases hσ with rfl | rfl
  exacts [h₁, hm₁]

/-- **Essential boundaries of line sections.** Let `s` be a null-measurable set and `e` a unit
vector. For almost every `y` in the orthogonal hyperplane, the following holds for every open set
`U ⊆ ℝ`: if the line `t ↦ y + t • e` meets the essential boundary `∂ᵉs` at only finitely many
parameters `t ∈ U`, then every point of `U` in the one-dimensional essential boundary of the line
section `{t | y + t • e ∈ s}` is one of them.

The finiteness hypothesis cannot be dropped: there is a planar set `s` such that on every
vertical line, a point of density one of `s` lies on the essential boundary of the line section
(see the module docstring). -/
theorem ae_essentialBoundary_lineSection_inter_subset {s : Set E}
    (hs : NullMeasurableSet s volume) (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, ∀ U : Set ℝ, IsOpen U →
      {t ∈ U | (y : E) + t • e ∈ essentialBoundary volume s}.Finite →
      essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s} ∩ U ⊆
        {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s} := by
  have : Nontrivial E := nontrivial_of_ne e 0 (by rintro rfl; simp at he)
  obtain ⟨c, hc0, hc2, hc⟩ := exists_const (E := E) e
  filter_upwards [ae_forall_not_sparseAt_and e he (essentialExterior_ae_eq hs).subset hc,
    ae_forall_not_sparseAt_and e he (essentialInterior_ae_eq hs).subset hc,
    ae_lineSection_eq e he (essentialInterior_ae_eq hs),
    ae_lineSection_eq e he (essentialExterior_ae_eq hs)] with y hO hI hIs hOs
  intro U hU hfin t ⟨ht, htU⟩
  by_contra htB
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (hU.sdiff hfin.isClosed) t ⟨htU, fun h => htB h.2⟩
  have hTPN : ball t ε ⊆ {t | (y : E) + t • e ∈ essentialInterior volume s} ∪
      {t | (y : E) + t • e ∈ essentialExterior volume s} := fun t' ht' => by
    have hnB : (y : E) + t' • e ∉ essentialBoundary volume s := fun h =>
      (hεsub ht').2 ⟨(hεsub ht').1, h⟩
    exact (not_and_or.1 (mt mem_essentialBoundary.2 hnB)).imp not_not.1 not_not.1
  have htT : t ∈ interior (ball t ε) := by rw [isOpen_ball.interior_eq]; exact mem_ball_self hε
  rcases disjoint_or_disjoint_of_isPreconnected_lineSection hs hc0 hc2 hO hI isOpen_ball
    (convex_ball t ε).isPreconnected hTPN with hd | hd
  · -- the ball lies in the essential exterior, so the section has density zero at `t`
    have hsub : {t : ℝ | (y : E) + t • e ∈ s} ≤ᵐ[volume] (ball t ε)ᶜ := by
      filter_upwards [hOs] with t' ht' hts ht'T
      exact (ht'.mp ((hTPN ht'T).resolve_left fun h => hd.ne_of_mem ht'T h rfl) :
        (y : E) + t' • e ∈ sᶜ) hts
    refine (mem_essentialBoundary.1 ht).2 (essentialExterior_anti_ae hsub
      (compl_closure_subset_essentialExterior ?_))
    rwa [closure_compl, compl_compl]
  · -- the ball lies in the essential interior, so the section has density one at `t`
    have hsub : ball t ε ≤ᵐ[volume] {t : ℝ | (y : E) + t • e ∈ s} := by
      filter_upwards [hIs] with t' ht' ht'T
      exact ht'.mp ((hTPN ht'T).resolve_right fun h => hd.ne_of_mem ht'T h rfl)
    exact (mem_essentialBoundary.1 ht).1
      (essentialInterior_mono_ae hsub (interior_subset_essentialInterior htT))

/-- **Essential boundaries of line sections.** Let `s` be a null-measurable set and `e` a unit
vector. For almost every `y` in the orthogonal hyperplane, if the line `t ↦ y + t • e` meets the
essential boundary `∂ᵉs` in finitely many points, then the one-dimensional essential boundary of
the line section `{t | y + t • e ∈ s}` consists of some of these points. -/
theorem ae_essentialBoundary_lineSection_subset {s : Set E} (hs : NullMeasurableSet s volume)
    (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s}.Finite →
      essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s} ⊆
        {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s} := by
  filter_upwards [ae_essentialBoundary_lineSection_inter_subset hs e he] with y hy hfin t ht
  exact hy univ isOpen_univ (by simpa using hfin) ⟨ht, mem_univ t⟩

end TauCeti
