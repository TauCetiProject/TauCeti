/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Piecewise
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Topology.DiscreteSubset

/-!
# Hartogs' extension theorem across product shells and isolated singularities

In complex dimension at least two, holomorphic functions have no isolated singularities: a map into
a complete complex normed space that is complex differentiable on a punctured neighbourhood of a
point has a limit there and extends analytically across the point, with no boundedness assumption.

This file proves the local Cauchy-integral form of Hartogs' extension theorem on product shells in
`V × ℂ`, for a nontrivial finite-dimensional complex normed space `V`, and deduces the removable
singularity theorems for isolated, finite, and closed discrete sets in any finite-dimensional
complex normed space `E` of dimension at least two, together with two classical consequences:
holomorphic functions in dimension at least two have no isolated zeros, whereas on `ℂ` the function
`z ↦ z⁻¹` on `{0}ᶜ` admits no continuous (hence no holomorphic) extension across `0`.

Near a shell `(ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂)` with
`0 ≤ r₁ < R₁` and `0 ≤ r₂ < ρ < R₂`, the extension on `ball w₀ R₁ ×ˢ ball c ρ` is given by the
one-variable Cauchy integral
`(w, z) ↦ (2πi)⁻¹ • ∮ ζ in C(c, ρ), (ζ - z)⁻¹ • f (w, ζ)`,
which is jointly analytic by `TauCeti.analyticAt_circleIntegral`, agrees with `f` when
`w ∈ ball w₀ R₁ \ closedBall w₀ r₁` by `DifferentiableOn.circleIntegral_sub_inv_smul`, and agrees
with `f` on the rest of the overlap by analytic continuation in `w` along the convex ball
`ball w₀ R₁`.

## Main results

* `TauCeti.exists_analyticOnNhd_prod_ball_eqOn_sdiff_prod_closedBall`: **Hartogs' extension theorem
  on product shells** in `V × ℂ` for nontrivial finite-dimensional `V`.
* `TauCeti.eqOn_prod_ball_of_eqOn_sdiff_prod_closedBall`: uniqueness of analytic extensions across a
  product shell.
* `TauCeti.exists_analyticAt_and_eventuallyEq_nhdsNE`,
  `TauCeti.analyticAt_update_limUnder_of_eventually_differentiableAt`,
  `TauCeti.tendsto_limUnder_of_eventually_differentiableAt`: **local Hartogs removable
  singularity** at a single point when `2 ≤ Module.finrank ℂ E`.
* `TauCeti.exists_analyticOnNhd_eqOn_sdiff_of_isDiscrete`,
  `TauCeti.exists_analyticOnNhd_eqOn_sdiff_of_finite`,
  `TauCeti.exists_analyticOnNhd_eqOn_sdiff_singleton`,
  `TauCeti.exists_differentiable_eqOn_compl_of_codiscrete`,
  `TauCeti.exists_differentiable_eqOn_compl_singleton`: extension across closed discrete, finite,
  and singleton subsets of open sets in `E`, and globally across closed discrete sets.
* `TauCeti.frequently_nhdsNE_eq_zero_of_analyticAt`: **holomorphic functions in dimension at least
  two have no isolated zeros.**
* `TauCeti.not_exists_continuousAt_and_eqOn_inv_compl_zero`,
  `TauCeti.not_exists_differentiable_and_eqOn_inv_compl_zero`: in dimension one, `z ↦ z⁻¹` on
  `{0}ᶜ` has no continuous or complex-differentiable extension across `0`.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §B,
  Theorem 5.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.3, Theorem 2.3.2.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4.
-/

public section

open Complex Filter Function Metric Real Set Topology

namespace TauCeti

/-! ### Product-shell extension -/

section ProdShell

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Uniqueness of analytic extensions across a product shell.** Two functions analytic on
`ball w₀ R₁ ×ˢ ball c R₂`, with `V` nontrivial and `r₁ < R₁`, that agree outside
`closedBall w₀ r₁ ×ˢ closedBall c r₂` agree on the entire product ball. -/
theorem eqOn_prod_ball_of_eqOn_sdiff_prod_closedBall {g₁ g₂ : V × ℂ → F} {w₀ : V} {c : ℂ}
    {r₁ R₁ r₂ R₂ : ℝ} (hR₁ : r₁ < R₁)
    (hg₁ : AnalyticOnNhd ℂ g₁ (ball w₀ R₁ ×ˢ ball c R₂))
    (hg₂ : AnalyticOnNhd ℂ g₂ (ball w₀ R₁ ×ˢ ball c R₂))
    (heq : EqOn g₁ g₂ ((ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂))) :
    EqOn g₁ g₂ (ball w₀ R₁ ×ˢ ball c R₂) := by
  rcases le_or_gt R₁ 0 with hR₁_le | hR₁_pos
  · simp [ball_eq_empty.2 hR₁_le]
  rcases le_or_gt R₂ 0 with hR₂_le | hR₂_pos
  · simp [ball_eq_empty.2 hR₂_le]
  obtain ⟨w₁, hw₁⟩ := (ball_sdiff_closedBall_nonempty_iff (x := w₀)).2 ⟨hR₁, hR₁_pos⟩
  have hopen : IsOpen ((ball w₀ R₁ \ closedBall w₀ r₁) ×ˢ ball c R₂) :=
    (isOpen_ball.sdiff isClosed_closedBall).prod isOpen_ball
  have hw₁c : (w₁, c) ∈ ball w₀ R₁ ×ˢ ball c R₂ := ⟨hw₁.1, mem_ball_self hR₂_pos⟩
  refine hg₁.eqOn_of_preconnected_of_eventuallyEq hg₂
    ((convex_ball w₀ R₁).prod (convex_ball c R₂)).isPreconnected hw₁c ?_
  filter_upwards [hopen.mem_nhds ⟨hw₁, mem_ball_self hR₂_pos⟩] with p hp
  exact heq ⟨⟨hp.1.1, hp.2⟩, fun hc ↦ hp.1.2 hc.1⟩

omit [Nontrivial V] in
private noncomputable def shellCauchy (f : V × ℂ → F) (c : ℂ) (ρ : ℝ) (x : V × ℂ) : F :=
  (2 * π * I)⁻¹ • ∮ ζ in C(c, ρ), (ζ - x.2)⁻¹ • f (x.1, ζ)

omit [Nontrivial V] in
private theorem analyticOnNhd_shellCauchy [FiniteDimensional ℂ V] {f : V × ℂ → F} {w₀ : V} {c : ℂ}
    {r₁ R₁ r₂ R₂ ρ : ℝ} (hρ : 0 < ρ) (hr₂ρ : r₂ < ρ) (hρR₂ : ρ < R₂)
    (hfa : AnalyticOnNhd ℂ f
      ((ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂))) :
    AnalyticOnNhd ℂ (shellCauchy f c ρ) (ball w₀ R₁ ×ˢ ball c ρ) := by
  rintro ⟨w, z⟩ ⟨hw, hz⟩
  refine (analyticAt_circleIntegral
    (f := fun y : (V × ℂ) × ℂ ↦ (y.2 - y.1.2)⁻¹ • f (y.1.1, y.2)) fun ζ hζ ↦ ?_).const_smul
  rw [abs_of_pos hρ] at hζ
  have hζz : ζ - z ≠ 0 := sub_ne_zero.2 (sphere_disjoint_ball.ne_of_mem hζ hz)
  have hζS : (w, ζ) ∈ (ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂) :=
    ⟨⟨hw, by simpa [mem_ball, mem_sphere.1 hζ] using hρR₂⟩,
      fun hc ↦ by linarith [mem_closedBall.1 hc.2, mem_sphere.1 hζ, hr₂ρ]⟩
  exact ((analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)).inv hζz).smul
    ((hfa (w, ζ) hζS).comp_of_eq ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl)

omit [Nontrivial V] in
private theorem shellCauchy_eq_of_notMem_closedBall [CompleteSpace F] {f : V × ℂ → F} {w₀ : V}
    {c : ℂ} {r₁ R₁ r₂ R₂ ρ : ℝ} (hρR₂ : ρ < R₂)
    (hfa : AnalyticOnNhd ℂ f
      ((ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂)))
    {w : V} (hw : w ∈ ball w₀ R₁ \ closedBall w₀ r₁) {z : ℂ} (hz : z ∈ ball c ρ) :
    shellCauchy f c ρ (w, z) = f (w, z) := by
  have hslice : DifferentiableOn ℂ (fun ζ ↦ f (w, ζ)) (closedBall c ρ) := fun ζ hζ ↦
    ((hfa (w, ζ) ⟨⟨hw.1, closedBall_subset_ball hρR₂ hζ⟩, fun hc ↦ hw.2 hc.1⟩).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.differentiableWithinAt
  rw [shellCauchy, hslice.circleIntegral_sub_inv_smul hz, inv_smul_smul₀ two_pi_I_ne_zero]

variable [FiniteDimensional ℂ V] [CompleteSpace F]

/-- **Hartogs' extension theorem on product shells.** Let `V` be a nontrivial finite-dimensional
complex normed space and `F` a complete complex normed space. For `r₁ < R₁` and `r₂ < R₂`, every
map `f : V × ℂ → F` complex differentiable on
`(ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂)` extends to an analytic map on
`ball w₀ R₁ ×ˢ ball c R₂`. -/
theorem exists_analyticOnNhd_prod_ball_eqOn_sdiff_prod_closedBall {f : V × ℂ → F} {w₀ : V} {c : ℂ}
    {r₁ R₁ r₂ R₂ : ℝ} (hR₁ : r₁ < R₁) (hR₂ : r₂ < R₂)
    (hf : DifferentiableOn ℂ f
      ((ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂))) :
    ∃ g : V × ℂ → F, AnalyticOnNhd ℂ g (ball w₀ R₁ ×ˢ ball c R₂) ∧
      EqOn g f ((ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂)) := by
  classical
  set S := (ball w₀ R₁ ×ˢ ball c R₂) \ (closedBall w₀ r₁ ×ˢ closedBall c r₂)
  have hS_open : IsOpen S :=
    (isOpen_ball.prod isOpen_ball).sdiff (isClosed_closedBall.prod isClosed_closedBall)
  have hfa : AnalyticOnNhd ℂ f S := hf.analyticOnNhd_of_finiteDimensional hS_open
  rcases lt_or_ge r₁ 0 with hr₁ | hr₁
  · exact ⟨f, by simpa [S, closedBall_eq_empty.2 hr₁] using hfa, eqOn_refl f S⟩
  rcases lt_or_ge r₂ 0 with hr₂ | hr₂
  · exact ⟨f, by simpa [S, closedBall_eq_empty.2 hr₂] using hfa, eqOn_refl f S⟩
  set ρ : ℝ := (r₂ + R₂) / 2
  have hr₂ρ : r₂ < ρ := left_lt_add_div_two.2 hR₂
  have hρR₂ : ρ < R₂ := add_div_two_lt_right.2 hR₂
  have hH_an : AnalyticOnNhd ℂ (shellCauchy f c ρ) (ball w₀ R₁ ×ˢ ball c ρ) :=
    analyticOnNhd_shellCauchy (hr₂.trans_lt hr₂ρ) hr₂ρ hρR₂ hfa
  -- By analytic continuation along `ball w₀ R₁`, `shellCauchy` and `f` agree on the overlap.
  have hH_overlap : EqOn (shellCauchy f c ρ) f ((ball w₀ R₁ ×ˢ ball c ρ) ∩ S) := by
    rintro ⟨w, z⟩ ⟨⟨hw, hz⟩, hwzS⟩
    by_cases hw_in : w ∈ closedBall w₀ r₁
    · have hz_out : z ∉ closedBall c r₂ := fun hz_in ↦ hwzS.2 ⟨hw_in, hz_in⟩
      obtain ⟨w₁, hw₁⟩ := (ball_sdiff_closedBall_nonempty_iff (x := w₀)).2 ⟨hR₁, hr₁.trans_lt hR₁⟩
      have h₁ : AnalyticOnNhd ℂ (fun w' ↦ shellCauchy f c ρ (w', z)) (ball w₀ R₁) := fun w' hw' ↦
        (hH_an (w', z) ⟨hw', hz⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
      have h₂ : AnalyticOnNhd ℂ (fun w' ↦ f (w', z)) (ball w₀ R₁) := fun w' hw' ↦
        (hfa (w', z) ⟨⟨hw', ball_subset_ball hρR₂.le hz⟩, fun hc ↦ hz_out hc.2⟩).comp_of_eq
          (analyticAt_id.prod analyticAt_const) rfl
      refine h₁.eqOn_of_preconnected_of_eventuallyEq h₂ (convex_ball w₀ R₁).isPreconnected hw₁.1 ?_
        hw
      filter_upwards [(isOpen_ball.sdiff isClosed_closedBall).mem_nhds hw₁] with w' hw'
      exact shellCauchy_eq_of_notMem_closedBall hρR₂ hfa hw' hz
    · exact shellCauchy_eq_of_notMem_closedBall hρR₂ hfa ⟨hw, hw_in⟩ hz
  -- Glue `shellCauchy f c ρ` on `ball w₀ R₁ ×ˢ ball c ρ` with `f` on `S`.
  set g : V × ℂ → F := fun p ↦ if p ∈ ball w₀ R₁ ×ˢ ball c ρ then shellCauchy f c ρ p else f p
  have hg_eq_f : EqOn g f S := fun p hp ↦ by
    simp only [g]; split_ifs with hp'; exacts [hH_overlap ⟨hp', hp⟩, rfl]
  refine ⟨g, fun p hp ↦ ?_, hg_eq_f⟩
  by_cases hp_in : p ∈ closedBall w₀ r₁ ×ˢ closedBall c r₂
  · have hp_ball : p ∈ ball w₀ R₁ ×ˢ ball c ρ := ⟨hp.1, closedBall_subset_ball hr₂ρ hp_in.2⟩
    refine (hH_an p hp_ball).congr ?_
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hp_ball] with q hq
    simp only [g, hq, ↓reduceIte]
  · refine (hfa p ⟨hp, hp_in⟩).congr ?_
    filter_upwards [hS_open.mem_nhds ⟨hp, hp_in⟩] with q hq
    exact (hg_eq_f hq).symm

end ProdShell

/-! ### Isolated and discrete singularities in dimension at least two -/

section IsolatedSingularity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Hartogs' local removable singularity theorem.** In a finite-dimensional complex normed space
`E` of dimension at least two, any map `f : E → F` into a complete complex normed space that is
complex differentiable on a punctured neighbourhood of `p` agrees on a punctured neighbourhood of
`p` with a function analytic at `p`. -/
theorem exists_analyticAt_and_eventuallyEq_nhdsNE (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {p : E} (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z) :
    ∃ g : E → F, AnalyticAt ℂ g p ∧ g =ᶠ[𝓝[≠] p] f := by
  set m := Module.finrank ℂ E - 1
  have hm : 1 ≤ m := by omega
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (Fin m → ℂ) := Function.nontrivial
  have hfin : Module.finrank ℂ E = Module.finrank ℂ ((Fin m → ℂ) × ℂ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  set L : E ≃L[ℂ] (Fin m → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq hfin
  set φ : (Fin m → ℂ) × ℂ → E := fun q ↦ p + L.symm q
  obtain ⟨U, hUf, hU_open, hpU⟩ := _root_.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hf)
  have hφ_cont : Continuous φ := continuous_const.add L.symm.continuous
  have hpre : φ ⁻¹' U ∈ 𝓝 (0 : (Fin m → ℂ) × ℂ) := by
    refine hφ_cont.continuousAt.preimage_mem_nhds ?_
    simpa [φ] using hU_open.mem_nhds hpU
  obtain ⟨R, hR, hRU⟩ := nhds_basis_ball.mem_iff.1 hpre
  have hshell : (ball (0 : Fin m → ℂ) R ×ˢ ball (0 : ℂ) R) \
      (closedBall 0 0 ×ˢ closedBall 0 0) = ball (0 : (Fin m → ℂ) × ℂ) R \ {0} := by
    rw [ball_prod_same, closedBall_prod_same, closedBall_zero]
    rfl
  have hdiff : DifferentiableOn ℂ (f ∘ φ)
      ((ball 0 R ×ˢ ball 0 R) \ (closedBall 0 0 ×ˢ closedBall 0 0)) := by
    rw [hshell]
    intro q ⟨hqR, hq0⟩
    have hφq_ne : φ q ≠ p := by simp [φ, mem_compl_singleton_iff.1 hq0]
    have hφ_diff : DifferentiableAt ℂ φ q :=
      (differentiableAt_const p).add (L.symm : (Fin m → ℂ) × ℂ →L[ℂ] E).differentiableAt
    exact ((hUf (φ q) (hRU hqR) hφq_ne).comp q hφ_diff).differentiableWithinAt
  obtain ⟨G, hG_an, hG_eq⟩ :=
    exists_analyticOnNhd_prod_ball_eqOn_sdiff_prod_closedBall hR hR hdiff
  rw [ball_prod_same] at hG_an
  rw [hshell] at hG_eq
  set g : E → F := fun z ↦ G (L (z - p))
  have hg_an : AnalyticAt ℂ g p := by
    have hL_an : AnalyticAt ℂ (fun z : E ↦ L (z - p)) p :=
      (L : E →L[ℂ] (Fin m → ℂ) × ℂ).analyticAt _ |>.comp (analyticAt_id.sub analyticAt_const)
    exact (hG_an 0 (mem_ball_self hR)).comp_of_eq hL_an (by simp)
  refine ⟨g, hg_an, ?_⟩
  have hL_cont : Continuous (fun z : E ↦ L (z - p)) :=
    L.continuous.comp (continuous_id.sub continuous_const)
  have hnhds : (fun z : E ↦ L (z - p)) ⁻¹' ball (0 : (Fin m → ℂ) × ℂ) R ∈ 𝓝 p := by
    refine hL_cont.continuousAt.preimage_mem_nhds ?_
    simpa only [sub_self, map_zero] using isOpen_ball.mem_nhds (mem_ball_self hR)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with z hz hzp
  have hLz0 : L (z - p) ≠ 0 := by simp [sub_eq_zero, mem_compl_singleton_iff.1 hzp]
  simpa [g, φ] using hG_eq ⟨hz, hLz0⟩

/-- In complex dimension at least two, updating `f` at `p` by its punctured limit produces a map
analytic at `p`, without any boundedness hypothesis. -/
theorem analyticAt_update_limUnder_of_eventually_differentiableAt [DecidableEq E]
    (hE : 2 ≤ Module.finrank ℂ E) {f : E → F} {p : E}
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z) :
    AnalyticAt ℂ (update f p (limUnder (𝓝[≠] p) f)) p := by
  obtain ⟨g, hg, hgf⟩ := exists_analyticAt_and_eventuallyEq_nhdsNE hE hf
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have : (𝓝[≠] p).NeBot := Module.punctured_nhds_neBot ℂ E p
  have hlim : Tendsto f (𝓝[≠] p) (𝓝 (g p)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf
  exact hg.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    (hgf.trans ((Function.update_eventuallyEq f p _).filter_mono inf_le_right).symm)
    (by simp [hlim.limUnder_eq]))

/-- In complex dimension at least two, a map into a complete complex normed space that is complex
differentiable on a punctured neighbourhood of `p` automatically has a limit at `p`. -/
theorem tendsto_limUnder_of_eventually_differentiableAt (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {p : E} (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z) :
    Tendsto f (𝓝[≠] p) (𝓝 (limUnder (𝓝[≠] p) f)) := by
  classical
  exact continuousAt_update_same.1
    (analyticAt_update_limUnder_of_eventually_differentiableAt hE hf).continuousAt

/-- **Hartogs' extension theorem across a closed discrete set.** Let `E` be a finite-dimensional
complex normed space with `2 ≤ Module.finrank ℂ E`, `U ⊆ E` an open set, and `S ⊆ E` a set such
that `U \ S` is open and `U ∩ S` is discrete. Every map `f : E → F` into a complete complex normed
space that is complex differentiable on `U \ S` extends to an analytic map on `U`. Such an
extension is unique on `U` by `IsOpen.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_of_isDiscrete (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {U S : Set E} (hU : IsOpen U) (hUS : IsOpen (U \ S)) (hS : IsDiscrete (U ∩ S))
    (hf : DifferentiableOn ℂ f (U \ S)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ S) := by
  classical
  set g : E → F := fun x ↦ if x ∈ U ∩ S then limUnder (𝓝[≠] x) f else f x
  have hgf : EqOn g f (U \ S) := fun x hx ↦ by
    have hx' : x ∉ U ∩ S := fun h ↦ hx.2 h.2
    simp only [g, hx', ↓reduceIte]
  refine ⟨g, fun x hx ↦ ?_, hgf⟩
  by_cases hxS : x ∈ S
  · have hmem : U \ S ∈ 𝓝[≠] x := hU.sdiff_mem_nhdsNE_of_isDiscrete hS hx hxS
    have hdiff_nhds : ∀ᶠ y in 𝓝[≠] x, DifferentiableAt ℂ f y :=
      eventually_of_mem hmem fun y hy ↦ (hf y hy).differentiableAt (hUS.mem_nhds hy)
    refine (analyticAt_update_limUnder_of_eventually_differentiableAt hE hdiff_nhds).congr
      (eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ (by simp [g, hx, hxS]))
    exact ((Function.update_eventuallyEq f x _).filter_mono inf_le_right).trans
      (eventually_of_mem hmem fun y hy ↦ (hgf hy).symm)
  · refine ((hf.analyticOnNhd_of_finiteDimensional hUS) x ⟨hx, hxS⟩).congr ?_
    filter_upwards [hUS.mem_nhds ⟨hx, hxS⟩] with y hy
    exact (hgf hy).symm

/-- **Hartogs' extension theorem across a finite set.** If `2 ≤ Module.finrank ℂ E`, `U ⊆ E` is
open, and `S ⊆ E` is finite, every map `f : E → F` complex differentiable on `U \ S` extends to an
analytic map on `U`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_of_finite (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {U S : Set E} (hU : IsOpen U) (hS : S.Finite) (hf : DifferentiableOn ℂ f (U \ S)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ S) :=
  exists_analyticOnNhd_eqOn_sdiff_of_isDiscrete hE hU (hU.sdiff hS.isClosed)
    (hS.subset inter_subset_right).isDiscrete hf

/-- **Hartogs' extension theorem across a point in an open set.** If `2 ≤ Module.finrank ℂ E` and
`U ⊆ E` is open, every map `f : E → F` complex differentiable on `U \ {p}` extends to an analytic
map on `U`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_singleton (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {U : Set E} (hU : IsOpen U) (p : E) (hf : DifferentiableOn ℂ f (U \ {p})) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {p}) :=
  exists_analyticOnNhd_eqOn_sdiff_of_finite hE hU (finite_singleton p) hf

/-- **Global Hartogs extension across a closed discrete set.** If `2 ≤ Module.finrank ℂ E` and
`Sᶜ ∈ codiscrete E`, every map `f : E → F` complex differentiable on `Sᶜ` extends to a globally
complex-differentiable map on `E`. -/
theorem exists_differentiable_eqOn_compl_of_codiscrete (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    {S : Set E} (hS : Sᶜ ∈ codiscrete E) (hf : DifferentiableOn ℂ f Sᶜ) :
    ∃ g : E → F, Differentiable ℂ g ∧ EqOn g f Sᶜ := by
  obtain ⟨hS_closed, hS_disc⟩ := compl_mem_codiscrete_iff.1 hS
  have hf' : DifferentiableOn ℂ f (univ \ S) := by simpa [compl_eq_univ_sdiff] using hf
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_eqOn_sdiff_of_isDiscrete hE isOpen_univ
    (isOpen_univ.sdiff hS_closed) (by simpa using hS_disc) hf'
  exact ⟨g, differentiableOn_univ.1 hg.differentiableOn, by simpa [compl_eq_univ_sdiff] using hgf⟩

/-- **Global Hartogs extension across a point.** If `2 ≤ Module.finrank ℂ E`, every map
`f : E → F` complex differentiable on `{p}ᶜ` extends to a globally complex-differentiable map on
`E`. -/
theorem exists_differentiable_eqOn_compl_singleton (hE : 2 ≤ Module.finrank ℂ E) {f : E → F}
    (p : E) (hf : DifferentiableOn ℂ f {p}ᶜ) :
    ∃ g : E → F, Differentiable ℂ g ∧ EqOn g f {p}ᶜ :=
  exists_differentiable_eqOn_compl_of_codiscrete hE (finite_singleton p).compl_mem_codiscrete hf

end IsolatedSingularity

/-! ### Nonexistence of isolated zeros and dimension-one sharpness -/

section ZerosAndSharpness

/-- **Holomorphic functions in complex dimension at least two have no isolated zeros.** If
`2 ≤ Module.finrank ℂ E`, `f : E → ℂ` is analytic at `p`, and `f p = 0`, then `p` is an
accumulation point of `{z | f z = 0}`. -/
theorem frequently_nhdsNE_eq_zero_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (hE : 2 ≤ Module.finrank ℂ E) {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hfp : f p = 0) : ∃ᶠ z in 𝓝[≠] p, f z = 0 := by
  by_contra hne
  rw [Filter.not_frequently] at hne
  have hinv : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ (fun y ↦ (f y)⁻¹) z := by
    filter_upwards [nhdsWithin_le_nhds hf.eventually_analyticAt, hne] with z hz hfz
    exact hz.differentiableAt.inv hfz
  obtain ⟨g, hg, hgf⟩ := exists_analyticAt_and_eventuallyEq_nhdsNE hE hinv
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have : (𝓝[≠] p).NeBot := Module.punctured_nhds_neBot ℂ E p
  have hmul : Tendsto (fun z ↦ g z * f z) (𝓝[≠] p) (𝓝 (g p * f p)) :=
    (hg.continuousAt.mul hf.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hone : (fun z ↦ g z * f z) =ᶠ[𝓝[≠] p] fun _ ↦ (1 : ℂ) := by
    filter_upwards [hgf, hne] with z hgz hfz
    rw [hgz, inv_mul_cancel₀ hfz]
  have h10 : (1 : ℂ) = g p * f p := tendsto_nhds_unique (tendsto_const_nhds.congr' hone.symm) hmul
  simp [hfp] at h10

/-- **Sharpness in complex dimension one:** no function continuous at `0` agrees with `z ↦ z⁻¹` on
`{0}ᶜ ⊆ ℂ` (where `z ↦ z⁻¹` is complex differentiable by `differentiableOn_inv`). -/
theorem not_exists_continuousAt_and_eqOn_inv_compl_zero :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g 0 ∧ EqOn g Inv.inv {(0 : ℂ)}ᶜ := by
  rintro ⟨g, hg, hgf⟩
  have : (𝓝[≠] (0 : ℂ)).NeBot := Module.punctured_nhds_neBot ℂ ℂ 0
  have hlim : Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf.eventuallyEq_nhdsWithin
  exact not_tendsto_atTop_of_tendsto_nhds hlim.norm tendsto_norm_inv_nhdsNE_zero_atTop

/-- In complex dimension one, no globally complex-differentiable map `g : ℂ → ℂ` agrees with
`z ↦ z⁻¹` on `{0}ᶜ`. -/
theorem not_exists_differentiable_and_eqOn_inv_compl_zero :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ EqOn g Inv.inv {(0 : ℂ)}ᶜ := by
  rintro ⟨g, hg, hgf⟩
  exact not_exists_continuousAt_and_eqOn_inv_compl_zero ⟨g, (hg 0).continuousAt, hgf⟩

end ZerosAndSharpness

end TauCeti
