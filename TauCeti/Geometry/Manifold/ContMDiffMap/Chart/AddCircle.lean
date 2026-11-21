/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Topology.MetricSpace.Pseudo.Basic

/-!
# The weak Whitney topology on functions on a circle

The charts of the circle `AddCircle p` are local real lifts: on the target of the chart at `x`,
the inverse chart is the quotient map `ℝ → AddCircle p`. So the coordinate derivatives of a
vector-valued `C^n` map `f` on the circle, which define the weak Whitney topology, are the
derivatives of its periodic lift `f ∘ (↑)` on `ℝ`, restricted to the chart targets
(`ContMDiffMap.chartIteratedFDeriv_addCircle_apply`).

Consequently a family of `C^n` maps on the circle converges in the weak Whitney topology as soon
as the derivatives of order at most `n` of their lifts converge locally uniformly on `ℝ`
(`ContMDiffMap.tendsto_addCircle_of_tendstoLocallyUniformly`). In particular lifts of periodic
functions converge when, for each order `m ≤ n`, the `m`-th derivatives of their differences are
bounded uniformly by constants tending to `0`
(`ContMDiffMap.tendsto_addCircle_of_norm_iteratedDeriv_sub_le`). This is how explicit families of
functions on the circle, given by periodic formulas, are shown to converge in the `C^n` topology.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {p : ℝ} [Fact (0 < p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω}

/-- The coordinate derivatives of a map on the circle are the derivatives of its periodic lift. -/
theorem chartIteratedFDeriv_addCircle_apply (f : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯)
    (x : AddCircle p) (m : ℕ) (hm : m ≤ n) (y : (extChartAt 𝓘(ℝ) x).target) :
    chartIteratedFDeriv f x m hm y = iteratedFDeriv ℝ m (f ∘ ((↑) : ℝ → AddCircle p)) y := by
  have hT : IsOpen (extChartAt 𝓘(ℝ) x).target := isOpen_extChartAt_target x
  rw [chartIteratedFDeriv_self_target_apply, iteratedFDerivWithin_of_isOpen m hT y.property]
  -- Near `y`, the map read in the chart is the lift, since the inverse chart is the quotient map.
  refine (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ m).eq_of_nhds
  filter_upwards [hT.mem_nhds y.property] with u hu
  simp only [Function.comp_apply, AddCircle.extChartAt_symm_apply x hu]

/-- A family of `C^n` maps on the circle converges in the weak Whitney topology when the
derivatives of order at most `n` of their lifts to `ℝ` converge locally uniformly. -/
theorem tendsto_addCircle_of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {f : ι → C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯} {g : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯}
    (h : ∀ m : ℕ, m ≤ n → TendstoLocallyUniformly
      (fun i ↦ iteratedFDeriv ℝ m (f i ∘ ((↑) : ℝ → AddCircle p)))
      (iteratedFDeriv ℝ m (g ∘ ((↑) : ℝ → AddCircle p))) l) :
    Tendsto f l (𝓝 g) := by
  refine tendsto_manifoldWeakWhitney_iff_chartIteratedFDeriv.2 fun x m hm ↦ ?_
  refine ContinuousMap.tendsto_of_tendstoLocallyUniformly ?_
  have hφ (φ : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯) : ⇑(chartIteratedFDeriv φ x m hm) =
      iteratedFDeriv ℝ m (φ ∘ ((↑) : ℝ → AddCircle p)) ∘ Subtype.val :=
    funext (chartIteratedFDeriv_addCircle_apply φ x m hm)
  simp only [hφ]
  exact (h m hm).comp _ continuous_subtypeVal

/-- Lifts of `p`-periodic `C^n` functions `f i` converge to the lift of `g` in the weak Whitney
topology when, for each order `m ≤ n`, eventually `‖(f i - g)⁽ᵐ⁾ t‖ ≤ b m i` for all `t`, with
bounds `b m i` tending to `0`. -/
theorem tendsto_addCircle_of_norm_iteratedDeriv_sub_le {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → F} {g : ℝ → F} (hf : ∀ i, Function.Periodic (f i) p)
    (hg : Function.Periodic g p) (hfn : ∀ i, ContDiff ℝ n (f i)) (hgn : ContDiff ℝ n g)
    {b : ℕ → ι → ℝ} (hb : ∀ m : ℕ, m ≤ n → Tendsto (b m) l (𝓝 0))
    (h : ∀ m : ℕ, m ≤ n → ∀ᶠ i in l, ∀ t, ‖iteratedDeriv m (f i - g) t‖ ≤ b m i) :
    Tendsto (β := C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯)
      (fun i ↦ ⟨(hf i).lift, (hf i).contMDiff_lift (hfn i)⟩) l
      (𝓝 ⟨hg.lift, hg.contMDiff_lift hgn⟩) := by
  refine tendsto_addCircle_of_tendstoLocallyUniformly fun m hm ↦ ?_
  simp only [coeFn_mk, Function.Periodic.lift_comp_coe]
  refine (tendstoUniformlyOn_univ.1 (TauCeti.tendstoUniformlyOn_of_dist_le (hb m hm)
    ((h m hm).mono fun i hi t _ ↦ ?_))).tendstoLocallyUniformly
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply ((hfn i).contDiffAt.of_le hm)
    (hgn.contDiffAt.of_le hm), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hi t

end ContMDiffMap
