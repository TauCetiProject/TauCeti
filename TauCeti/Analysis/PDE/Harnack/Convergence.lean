/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse
import TauCeti.Analysis.PDE.Harnack.Basic

/-!
# Limits of harmonic functions

Let `E` be a finite-dimensional real inner product space. This file proves two classical
convergence theorems for harmonic functions `E → ℝ` on an open set `U`.

* A locally uniform limit of harmonic functions is harmonic. The limit is continuous and inherits
  the mean-value property on small balls, so it is harmonic by the converse of the mean-value
  property (`TauCeti.harmonicOnNhd_of_setAverage_ball_eq`).
* **Harnack's convergence theorem.** A monotone family of harmonic functions on a preconnected
  open set `U` that is bounded above at one point of `U` converges locally uniformly on `U`, and
  its limit is harmonic. For `F m ≤ F n` the difference `F n - F m` is harmonic and nonnegative, so
  Harnack's inequality (`IsCompact.harnack_inequality`) bounds it on a compact set `K ⊆ U` by a
  multiple of its value at the base point, which tends to zero.

These are the compactness inputs of Perron's method for the Dirichlet problem, which takes the
limit of increasing sequences of harmonic functions on a ball.

## Main declarations

* `TauCeti.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic
  functions is harmonic.
* `TauCeti.tendstoLocallyUniformlyOn_iSup_of_monotone`: **Harnack's convergence theorem**, the
  locally uniform convergence of a monotone family of harmonic functions.
* `TauCeti.harmonicOnNhd_iSup_of_monotone`: the limit of such a family is harmonic.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.8 and Theorem 2.9.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.3.
-/

public section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {F : ι → E → ℝ} {f : E → ℝ} {U : Set E}

/-- **Locally uniform limits of harmonic functions are harmonic.** If eventually along a nontrivial
filter `p` the functions `F i` are harmonic on the open set `U`, and `F i` tends to `f` locally
uniformly on `U`, then `f` is harmonic on `U`. -/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn {p : Filter ι} [p.NeBot] (hU : IsOpen U)
    (hF : ∀ᶠ i in p, HarmonicOnNhd (F i) U) (hlim : TendstoLocallyUniformlyOn F f p U) :
    HarmonicOnNhd f U := by
  borelize E
  let μ : Measure E := Measure.addHaar
  refine harmonicOnNhd_of_setAverage_ball_eq (μ := μ) hU
    (hlim.continuousOn (hF.mono fun i hi ↦ hi.continuousOn).frequently) fun x hx ↦ ?_
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  refine (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr ↦ ?_).frequently
  have hrU : closedBall x r ⊆ U := (closedBall_subset_closedBall hr.2.le).trans hεU
  have hunif : TendstoUniformlyOn F f p (closedBall x r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hrU (isCompact_closedBall x r)
  have hfi : IntegrableOn f (ball x r) μ :=
    (((hlim.continuousOn (hF.mono fun i hi ↦ hi.continuousOn).frequently).mono
      hrU).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hμ : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr.1).ne'
  -- The averages of `F i` over `ball x r` converge to the average of `f`: wherever `F i` is
  -- uniformly `δ`-close to `f`, so are the averages.
  have havg : Tendsto (fun i ↦ ⨍ y in ball x r, F i y ∂μ) p (𝓝 (⨍ y in ball x r, f y ∂μ)) := by
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ, hF] with i hi hFi
    have hFii : IntegrableOn (F i) (ball x r) μ :=
      (((hFi.mono hrU).continuousOn).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall
    have hsub := setAverage_sub hFii hfi
    obtain ⟨y, hy, hyle⟩ := exists_setAverage_le hμ measure_ball_lt_top.ne (hFii.sub hfi)
    obtain ⟨z, hz, hzle⟩ := exists_le_setAverage hμ measure_ball_lt_top.ne (hFii.sub hfi)
    have hy' := hi y (ball_subset_closedBall hy)
    have hz' := hi z (ball_subset_closedBall hz)
    rw [Real.dist_eq] at hy' hz' ⊢
    rw [abs_lt]
    simp only [Pi.sub_apply] at hsub hyle hzle
    constructor <;> linarith [abs_lt.1 hy', abs_lt.1 hz']
  -- Each `F i` equals its average at the centre, so the two limits agree.
  exact tendsto_nhds_unique
    (havg.congr' (hF.mono fun i hi ↦ HarmonicOnNhd.setAverage_ball_eq (hi.mono hrU) hr.1))
    (hunif.tendsto_at (mem_closedBall_self hr.1.le))

variable [SemilatticeSup ι] [Nonempty ι]

/-- **Harnack's convergence theorem.** Let `F` be a monotone family of functions harmonic on a
preconnected open set `U`, bounded above at some point `x₀ ∈ U`. Then `F` converges locally
uniformly on `U` to its pointwise supremum. -/
theorem tendstoLocallyUniformlyOn_iSup_of_monotone (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, HarmonicOnNhd (F i) U) (hmono : Monotone F) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hbdd : BddAbove (range fun i ↦ F i x₀)) :
    TendstoLocallyUniformlyOn F (fun x ↦ ⨆ i, F i x) atTop U := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun K hKU hK ↦ ?_
  obtain ⟨C, hC, hharnack⟩ :=
    (hK.insert x₀).harnack_inequality hU hUc (insert_subset_iff.2 ⟨hx₀, hKU⟩)
  -- For `m ≤ n`, Harnack's inequality for `F n - F m ≥ 0` compares its values on `K` with its
  -- value at `x₀`.
  have hcomp : ∀ m n, m ≤ n → ∀ x ∈ K, F n x - F m x ≤ C * (F n x₀ - F m x₀) := fun m n hmn x hx ↦
    hharnack (F n - F m) ((hF n).sub (hF m)) (fun z _ ↦ sub_nonneg.2 (hmono hmn z)) x
      (mem_insert_of_mem _ hx) x₀ (mem_insert _ _)
  have hlim₀ : Tendsto (fun i ↦ F i x₀) atTop (𝓝 (⨆ i, F i x₀)) :=
    tendsto_atTop_ciSup (fun _ _ h ↦ hmono h x₀) hbdd
  -- Every `F n x` with `x ∈ K` lies below `F m x + C * (⨆ i, F i x₀ - F m x₀)`.
  have hupper : ∀ m n, ∀ x ∈ K, F n x ≤ F m x + C * ((⨆ i, F i x₀) - F m x₀) := by
    intro m n x hx
    have h := hcomp m (n ⊔ m) le_sup_right x hx
    have hx₀le : F (n ⊔ m) x₀ ≤ ⨆ i, F i x₀ := le_ciSup hbdd _
    nlinarith [hmono (le_sup_left : n ≤ n ⊔ m) x]
  have hbddK : ∀ x ∈ K, BddAbove (range fun i ↦ F i x) := fun x hx ↦
    ⟨_, forall_mem_range.2 fun n ↦ hupper (Classical.arbitrary ι) n x hx⟩
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  have hsmall : ∀ᶠ m in atTop, C * ((⨆ i, F i x₀) - F m x₀) < ε := by
    have : Tendsto (fun m ↦ C * ((⨆ i, F i x₀) - F m x₀)) atTop
        (𝓝 (C * ((⨆ i, F i x₀) - ⨆ i, F i x₀))) :=
      (tendsto_const_nhds.sub hlim₀).const_mul C
    exact this.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hsmall] with m hm x hx
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (le_ciSup (hbddK x hx) m))]
  linarith [ciSup_le fun n ↦ hupper m n x hx]

/-- **The limit in Harnack's convergence theorem is harmonic.** Let `F` be a monotone family of
functions harmonic on a preconnected open set `U`, bounded above at some point `x₀ ∈ U`. Then its
pointwise supremum is harmonic on `U`. -/
theorem harmonicOnNhd_iSup_of_monotone (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, HarmonicOnNhd (F i) U) (hmono : Monotone F) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hbdd : BddAbove (range fun i ↦ F i x₀)) :
    HarmonicOnNhd (fun x ↦ ⨆ i, F i x) U :=
  harmonicOnNhd_of_tendstoLocallyUniformlyOn hU (.of_forall hF)
    (tendstoLocallyUniformlyOn_iSup_of_monotone hU hUc hF hmono hx₀ hbdd)

end TauCeti
