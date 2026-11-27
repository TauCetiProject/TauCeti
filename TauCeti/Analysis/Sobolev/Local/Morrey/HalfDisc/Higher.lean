/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.Local.Reflection.Bound
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.Sets.Opens

/-!
# Higher-order continuity and local bounds on half-discs

Let `Ω ⊆ ℂ` be open and let `U = Ω ∩ {0 ≤ im}`. The half-disc Sobolev class
`TauCeti.MemWkpLoc p U k` tests weak derivatives in the interior and imposes local bounds on
compact sets that may meet the real axis. For `k p > 2` and `p ≥ 1`, its members have continuous
representatives up to that axis, including when `p ≤ 2` and higher derivatives are needed. The
order-`k` reflection across the axis carries the interior local `L^∞` bound for `kp > 2` to
half-discs, so convergence of continuous maps in `W^{k,p}` on compact subsets of `U` is locally
uniform on `U`, up to the axis.

For real-valued maps and finite `q > 2`, this file also gives quantitative local bounds for every
derivative through order `j` of a `W^{j+1,q}` map on a half-disc. A representative extends as a
`Cʲ` map across the axis; its derivatives and their Hölder constants are bounded by a constant
times the Sobolev norm on the open half-disc. The bounds pass to the real segment by continuity.
The open `Cʲ` representative is supplied by
`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg` in the half-disc Morrey theory.
For values in a finite-dimensional space the same bounds hold by the Sobolev norms of the
coordinates in a finite basis, applying the real-valued bounds to each coordinate.

## Main declarations

* `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg`: continuous
  representatives when `k p > 2`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul_halfPlane`: the local `L^∞` bound
  for `k p > 2` up to the real axis.
* `TauCeti.tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg`:
  for `k p > 2`, convergence of continuous maps in `W^{k,p}` on compact subsets of
  `Ω ∩ {0 ≤ im}` is locally uniform.
* `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg`:
  local derivative and Hölder bounds through the real axis, with constants controlled by the
  open-half-disc Sobolev norm.
* The same bounds for values in a finite-dimensional space, by the open-half-disc Sobolev norms
  of the coordinates in a finite basis:
`TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg_basis`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.1.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {k : ℕ} {u : ℂ → F}

variable [FiniteDimensional ℝ F]

/-- **Morrey for `kp > 2` up to the real axis: continuous representatives.** If `1 ≤ p ≤ ∞` and
`2 < k p`, every `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
a map continuous on `Ω ∩ {0 ≤ im}`. For `p ≤ 2` this needs `k ≥ 2`. -/
theorem MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    ∃ g : ℂ → F, ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g := by
  have hSV := Ω.inter_setOf_im_nonneg_subset_reflectionCore
  have hV := hu.planarReflection_higherReflectionCoeff_reflectionCore hp
  obtain ⟨g, hg, hrg⟩ := hV.exists_continuousOn_ae_eq_of_two_lt_mul hp hkp
  refine ⟨g, hg.mono hSV, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSV hrg,
    ae_restrict_mem (Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
      Complex.measurable_im))] with z hz hzS
  rw [← hz, planarReflection_of_nonneg _ _ hzS.2]

/-- **The local `L^∞` bound for `kp > 2` up to the real axis.** Let `1 ≤ p ≤ ∞` with `2 < k p`
and let `U` have compact closure contained in `Ω`. There is a constant `C` such that, with
`U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`, `‖u‖_{L^∞(U⁺)} ≤ C ‖u‖_{W^{k,p}(Ω⁺)}` for every
`u : ℂ → F`. The set `U` may meet the real axis. -/
theorem exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul_halfPlane (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u ∞ (volume.restrict (U ∩ {z | 0 ≤ z.im})) ≤
      C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F)
    (W := Ω.reflectionCore) hp hkp
    (hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore hUΩ)
  refine ⟨C * (higherReflectionBound k p).toNNReal, fun u => ?_⟩
  -- The order-`k` reflection of `u` agrees with `u` on `U⁺`.
  calc eLpNorm u ∞ (volume.restrict (U ∩ {z | 0 ≤ z.im}))
      = eLpNorm (planarReflection (higherReflectionCoeff k) u) ∞
          (volume.restrict (U ∩ {z | 0 ≤ z.im})) :=
        eLpNorm_congr_ae (planarReflection_ae_eq_inter_setOf_im_nonneg _ u U).symm
    _ ≤ C * eLpNormWkp p Ω.reflectionCore k (planarReflection (higherReflectionCoeff k) u) :=
        hC _
    _ ≤ C * (higherReflectionBound k p * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) := by
        gcongr
        exact eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le hp u
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (higherReflectionBound_ne_top k p), mul_assoc]

/-- Uniform convergence on one compact subset `K` of `Ω ∩ {0 ≤ im}`, for
`TauCeti.tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg`. -/
private theorem tendstoUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg
    (hp : 1 ≤ p) (hkp : 2 < (k : ℝ≥0∞) * p) {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F}
    (huc : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hu₀c : ContinuousOn u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Filter.Tendsto (fun n => eLpNormWkp p K k (u n - u₀)) l (nhds 0))
    {K : Set ℂ} (hKS : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hK : IsCompact K) :
    TendstoUniformlyOn u u₀ l K := by
  -- Open sets `K ⊆ V`, `closure V ⊆ W` and `closure W ⊆ Ω` with compact closures, and the
  -- compact sets `closure V ∩ {0 ≤ im}` and `closure W ∩ {0 ≤ im}` inside `Ω ∩ {0 ≤ im}`.
  obtain ⟨V, hKV, hVΩ, hVc⟩ :=
    Opens.exists_between_and_isCompact_closure hK (hKS.trans inter_subset_left)
  obtain ⟨W, hVW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hVc hVΩ
  have hH := Complex.isClosed_setOfPred_le_im 0
  obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul_halfPlane (F := F) hp hkp
    hVc hVW
  have hT : Filter.Tendsto (fun n => (C : ℝ≥0∞) *
      eLpNormWkp p (closure (W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (u n - u₀)) l (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (hlim _ (inter_subset_inter_left _ hWΩ)
      (hWc.inter_right hH)) (Or.inr ENNReal.coe_ne_top)
  refine EMetric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [huc _ (inter_subset_inter_left _ hVΩ) (hVc.inter_right hH),
    hT.eventually (gt_mem_nhds hε)] with n hnc hn z hz
  -- `z` lies in the closure of the interior of `V ∩ {0 ≤ im}`, where `uₙ - u₀` is continuous.
  have hcont : ContinuousWithinAt (u n - u₀) ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) z :=
    ((hnc.sub (hu₀c.mono (inter_subset_inter_left _ hVΩ))).mono
      (inter_subset_inter_left _ subset_closure)) z ⟨hKV hz, (hKS hz).2⟩
  rw [edist_comm, eDist_eq_eNorm_sub, ← Pi.sub_apply]
  calc ‖(u n - u₀) z‖ₑ ≤ eLpNorm (u n - u₀) ∞ (volume.restrict ((V : Set ℂ) ∩ {z | 0 ≤ z.im})) :=
      hcont.eNorm_le_eLpNorm_top_restrict_of_mem_closure_interior
        (subset_closure_interior_inter_setOf_im_nonneg V.isOpen ⟨hKV hz, (hKS hz).2⟩)
    _ ≤ C * eLpNormWkp p ((W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (u n - u₀) := hC _
    _ ≤ C * eLpNormWkp p (closure (W : Set ℂ) ∩ {z | 0 ≤ z.im}) k (u n - u₀) := by
      gcongr
      exact eLpNormWkp_mono_set (inter_subset_inter_left _ subset_closure)
    _ < ε := hn

/-- **Morrey for `kp > 2` up to the real axis: convergence in `W^{k,p}` is locally uniform.** Let
`1 ≤ p ≤ ∞` with `2 < k p`. If maps `uₙ`, eventually continuous on every compact subset of
`Ω ∩ {0 ≤ im}`, converge in `W^{k,p}` on every compact subset of `Ω ∩ {0 ≤ im}` to a map `u₀`
continuous on `Ω ∩ {0 ≤ im}`, then `uₙ → u₀` locally uniformly on `Ω ∩ {0 ≤ im}`, including at
the points of the real axis. -/
theorem tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg
    (hp : 1 ≤ p) (hkp : 2 < (k : ℝ≥0∞) * p) {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F}
    (huc : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hu₀c : ContinuousOn u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Filter.Tendsto (fun n => eLpNormWkp p K k (u n - u₀)) l (nhds 0)) :
    TendstoLocallyUniformlyOn u u₀ l ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  -- A compact neighbourhood `N ⊆ Ω` of `x`; its closed upper half is a compact neighbourhood of
  -- `x` within `Ω ∩ {0 ≤ im}`.
  obtain ⟨N, hN, hNΩ, hNc⟩ := local_compact_nhds (Ω.isOpen.mem_nhds hx.1)
  exact ⟨N ∩ {z | 0 ≤ z.im}, Filter.mem_of_superset (inter_mem_nhdsWithin _ hN)
      fun z hz => ⟨hz.2, hz.1.2⟩,
    tendstoUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg hp hkp huc hu₀c
      hlim (inter_subset_inter_left _ hNΩ) (hNc.inter_right (Complex.isClosed_setOfPred_le_im 0))⟩

/-! ### Local bounds -/

variable {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- **Local `C^{j,1-2/q}` bounds on a half-disc, up to the real axis.** For `2 < q < ∞`, a real
centre `x` and a radius `s` there is a constant `K` such that, for every open `Ω` containing the
closure of `ball x s`, every real `u ∈ MemWkpLoc q (Ω ∩ {0 ≤ im}) (j + 1)` is represented on the
open half-disc `ball x s ∩ {0 < im}` by some `v` in `W^{j+1,q}` of it, and agrees almost everywhere
on the half-disc `ball x s ∩ {0 ≤ im}` with a map `g` that is `Cʲ` on an open neighbourhood of it,
whose derivatives of order `i ≤ j` are bounded by `K ‖v‖` and Hölder of exponent `1 - 2 / q` with
constant `K ‖v‖` on `ball x s ∩ {0 ≤ im}`, including its segment of the real axis. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg
    (hq : 2 < q) (x s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → ℝ), closure (ball (x : ℂ) s) ⊆ Ω →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (j + 1) u →
      ∃ v : Wkp volume (Opens.upperHalf ⟨ball (x : ℂ) s, isOpen_ball⟩) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 < z.im})] u ∧
        ∃ V : Opens ℂ, ball (x : ℂ) s ∩ {z | 0 ≤ z.im} ⊆ V ∧ ∃ g : ℂ → ℝ, ContDiffOn ℝ j g V ∧
          u =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 ≤ z.im})] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball (x : ℂ) s ∩ {z | 0 ≤ z.im}, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
              HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g)
                (ball (x : ℂ) s ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall_upperHalf x s hq j
  refine ⟨K, fun {Ω} u hsub hu => ?_⟩
  set B := ball (x : ℂ) s
  set O := B ∩ {z | 0 < z.im}
  -- The bounds hold for the representative `g₁` of the Sobolev space of the open half-disc `O`.
  obtain ⟨v, hv⟩ := hu.exists_wkp_upperHalf (W := ⟨B, isOpen_ball⟩)
    ((isCompact_closedBall _ s).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hsub
  simp only [Opens.coe_upperHalf, Opens.coe_mk] at hv
  obtain ⟨g₁, hg₁, hvg₁, hb⟩ := hK v
  -- A representative `g` that is `Cʲ` across the real axis agrees with `g₁` on `O`, with all its
  -- derivatives, and the bounds pass to the closure of `O` by continuity.
  obtain ⟨V, hSV, -, g, hg, hug⟩ :=
    hu.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg (by exact_mod_cast hq)
  have hTS : B ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ (subset_closure.trans hsub)
  have hOT : O ⊆ B ∩ {z | 0 ≤ z.im} := by
    simpa only [O, Opens.coe_upperHalf, Opens.coe_mk] using
      Opens.coe_upperHalf_subset (⟨B, isOpen_ball⟩ : Opens ℂ)
  have hO : IsOpen O := by
    simpa only [O, Opens.coe_upperHalf, Opens.coe_mk] using
      (Opens.upperHalf ⟨B, isOpen_ball⟩).isOpen
  have hOV : O ⊆ V := (hOT.trans hTS).trans hSV
  have hug₁ : u =ᵐ[volume.restrict O] g₁ := hv.symm.trans hvg₁
  have hug' : u =ᵐ[volume.restrict O] g := ae_restrict_of_ae_restrict_of_subset (hOT.trans hTS) hug
  have hgg₁ : EqOn g g₁ O := Measure.eqOn_open_of_ae_eq (hug'.symm.trans hug₁) hO
    (hg.continuousOn.mono hOV) hg₁.continuousOn
  have heq (i : ℕ) : EqOn (iteratedFDeriv ℝ i g) (iteratedFDeriv ℝ i g₁) O := fun z hz =>
    ((Filter.eventuallyEq_of_mem (hO.mem_nhds hz) hgg₁).iteratedFDeriv ℝ i).eq_of_nhds
  have hcl : B ∩ {z | 0 ≤ z.im} ⊆ closure O := fun z hz => by
    have h := subset_closure_interior_inter_setOf_im_nonneg (Ω := B) isOpen_ball hz
    rwa [interior_inter_setOf_im_nonneg isOpen_ball] at h
  have hcont {i : ℕ} (hi : i ≤ j) (z : ℂ) (hz : z ∈ B ∩ {z | 0 ≤ z.im}) :
      ContinuousAt (iteratedFDeriv ℝ i g) z :=
    (ContinuousOn.continuousOn_iteratedFDeriv hg V.isOpen (by exact_mod_cast hi)).continuousAt
      (V.isOpen.mem_nhds (hSV (hTS hz)))
  refine ⟨v, hv, V, hTS.trans hSV, g, hg, ae_restrict_of_ae_restrict_of_subset hTS hug,
    fun i hi => ⟨fun z hz => ?_, ?_⟩⟩
  · exact ContinuousWithinAt.closure_le (hcl hz) (hcont hi z hz).norm.continuousWithinAt
      continuousWithinAt_const fun y hy => heq i hy ▸ (hb i hi).1 y hy
  · refine HolderOnWith.of_subset_closure (fun a ha b hb' => ?_) hcl
      (fun z hz => (hcont hi z hz).continuousWithinAt)
    rw [heq i ha, heq i hb']
    exact (hb i hi).2 a ha b hb'

omit [FiniteDimensional ℝ F] in
/-- **Local `C^{j,1-2/q}` bounds on a half-disc, for finite-dimensional values.** For `2 < q < ∞`,
a finite basis `b` of `F`, a real centre `x` and a radius `s` there is a constant `K` such that,
for every open `Ω` containing the closure of `ball x s`, every
`u ∈ MemWkpLoc q (Ω ∩ {0 ≤ im}) (j + 1)` with values in `F` has coordinates in `b` represented on
the open half-disc `ball x s ∩ {0 < im}` by elements `v l` of `W^{j+1,q}` of it, and agrees almost
everywhere on the half-disc `ball x s ∩ {0 ≤ im}` with a map `g` that is `Cʲ` on an open
neighbourhood of it, whose derivatives of order `i ≤ j` are bounded by `K ∑ₗ ‖v l‖` and Hölder of
exponent `1 - 2 / q` with constant `K ∑ₗ ‖v l‖` on `ball x s ∩ {0 ≤ im}`, including its segment of
the real axis. This is
`TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg`
applied to each coordinate. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg_basis
    (hq : 2 < q) {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) (x s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → F), closure (ball (x : ℂ) s) ⊆ Ω →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (j + 1) u →
      ∃ v : ι → Wkp volume (Opens.upperHalf ⟨ball (x : ℂ) s, isOpen_ball⟩) q (j + 1),
        (∀ l, Wkp.value (j + 1) (v l) =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 < z.im})]
          fun z => b.coord l (u z)) ∧
        ∃ V : Opens ℂ, ball (x : ℂ) s ∩ {z | 0 ≤ z.im} ⊆ V ∧ ∃ g : ℂ → F, ContDiffOn ℝ j g V ∧
          u =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 ≤ z.im})] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball (x : ℂ) s ∩ {z | 0 ≤ z.im}, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ∑ l, ‖v l‖) ∧
              HolderOnWith (K * ∑ l, ‖v l‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g)
                (ball (x : ℂ) s ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg
    hq x s j
  have : FiniteDimensional ℝ F := .of_basis b
  -- Coordinates `ℓ l` and the inverse maps `A l : t ↦ t • b l`.
  set ℓ : ι → F →L[ℝ] ℝ := fun l => (b.coord l).toContinuousLinearMap
  set A : ι → ℝ →L[ℝ] F := fun l => (ContinuousLinearMap.id ℝ ℝ).smulRight (b l)
  refine ⟨(∑ l, ‖A l‖₊) * K, fun {Ω} u hsub hu => ?_⟩
  set T := ball (x : ℂ) s ∩ {z | 0 ≤ z.im}
  choose v hv V hTV g hg hug hb using fun l =>
    hK (Ω := Ω) (fun z => ℓ l (u z)) hsub (hu.clm_comp (ℓ l))
  -- Each coordinate `g l` is `Cʲ` near every point of the closed half-disc `T`.
  have hgT (l : ι) {i : ℕ} (hi : i ≤ j) (z : ℂ) (hz : z ∈ T) : ContDiffAt ℝ i (g l) z :=
    ((hg l).contDiffAt ((V l).isOpen.mem_nhds (hTV l hz))).of_le (by exact_mod_cast hi)
  refine ⟨v, hv, ⟨⋂ l, V l, isOpen_iInter_of_finite fun l => (V l).isOpen⟩,
    subset_iInter hTV, fun z => ∑ l, A l (g l z), ContDiffOn.sum fun l _ =>
      (A l).contDiff.comp_contDiffOn ((hg l).mono (iInter_subset _ l)), ?_, fun i hi => ?_⟩
  · exact (b.ae_eq_sum_smul_of_coord_ae_eq hug).trans
      (Filter.Eventually.of_forall fun z => by simp [A])
  · have h := norm_iteratedFDeriv_le_and_holderOnWith_sum_comp_left A (c := fun l => ‖v l‖₊)
      (fun l => hgT l hi) fun l => ⟨fun z hz => by simpa using (hb l i hi).1 z hz, (hb l i hi).2⟩
    exact ⟨fun z hz => by simpa using h.1 z hz, h.2⟩

end TauCeti
