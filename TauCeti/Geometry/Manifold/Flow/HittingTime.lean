/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Hitting times of transverse sections

Let `v` be a `C^n` vector field (`n ≥ 1`) on a boundaryless finite-dimensional manifold `M`, and
suppose the flow carries `p` to `q = flowOf v T p` at time `T`. A local transverse section through
`q` is described by a function `g : M → ℝ`, `C^n` near `q`, whose derivative along the field does
not vanish at `q`: `dg_q (v q) ≠ 0`. Nearby points `z` reach the level `{g = g q}` at a time close
to `T`, and this time depends `C^n` on `z`.

`TauCeti.flowHittingTime v g T p` is this **hitting-time branch**. It is the implicit function of
the equation `g (flowOf v t z) = g q` in the unknown `t`, read in the extended chart at `p`; the
implicit function theorem applies because the derivative of the left side in `t` at `(T, p)` is
`dg_q (v q)` (`TauCeti.hasDerivAt_comp_flowOf`). It has the value `T` at `p`
(`TauCeti.flowHittingTime_self`), is `C^n` at `p` (`TauCeti.contMDiffAt_flowHittingTime`), and the
flow at time `flowHittingTime v g T p z` carries every `z` near `p` into the level
(`TauCeti.eventually_flowHittingTime`). Near `(T, p)` it is the only solution of the equation
(`TauCeti.eventually_eq_flowHittingTime_iff`), so any other hitting time continuous at `p` with
the value `T` agrees with it near `p` (`TauCeti.eventuallyEq_flowHittingTime`). The induced
transition `TauCeti.flowTransition v g T p`, which sends `z` to
`flowOf v (flowHittingTime v g T p z) z`, maps a neighbourhood of `p` to the level of `g` through
`q` and is `C^n` at `p` (`TauCeti.contMDiffAt_flowTransition`).

These are the local hitting times and transition maps between transverse sections of a periodic
orbit: restricting `z` to a section through `p` gives the transition map between the sections,
and taking `q = p` and `T` a period gives a local return branch near `T`. This branch need not be
the Poincaré first return map: `T` may be a multiple of the primitive period, and earlier
intersections with the section are not excluded.

## Main definitions

* `TauCeti.flowHittingTime v g T p`: the hitting time of the level of `g` through `flowOf v T p`,
  for points near `p` and times near `T`.
* `TauCeti.flowTransition v g T p`: the transition `z ↦ flowOf v (flowHittingTime v g T p z) z`
  to that level.

## Main results

* `TauCeti.contMDiffAt_flowHittingTime`: the hitting time is `C^n`.
* `TauCeti.eventually_flowHittingTime`: the flow at the hitting time lands in the level.
* `TauCeti.eventually_eq_flowHittingTime_iff`: local uniqueness of the hitting time.
* `TauCeti.eventuallyEq_flowHittingTime`: uniqueness of the germ of continuous hitting times.
* `TauCeti.contMDiffAt_flowTransition`: the transition map to the level is `C^n`.
* `TauCeti.mdifferentiableAt_flowHittingTime_of_eq`,
  `TauCeti.mdifferentiableAt_flowTransition_of_eq`: differentiability at `p`, for a section
  through a point `q` with `flowOf v T p = q`.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1
  (transversal sections and the Poincaré map).
* M. W. Hirsch, S. Smale, R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, 3rd ed., Academic Press 2013, Section 10.3.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g : M → ℝ} {T : ℝ} {p : M}

/-- The hypotheses under which the hitting time is the implicit function: a `C¹` field, a flow
time `T` defined at `p`, and a `C¹` function whose derivative along the field at `flowOf v T p`
does not vanish. -/
private def HittingData (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) : Prop :=
  CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) ∧ (T, p) ∈ flowDomain v ∧
    ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p) ∧ mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0

/-- The equation of the hitting time read in the extended chart at `p`: the value of `g` after
flowing for time `u.2` from the point with coordinates `u.1`. -/
private def chartLevel (v : (x : M) → TangentSpace I x) (g : M → ℝ) (p : M) (u : E × ℝ) : ℝ :=
  g (flowOf v u.2 ((extChartAt I p).symm u.1))

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
private theorem chartLevel_extChartAt {z : M} (hz : z ∈ (extChartAt I p).source) (t : ℝ) :
    chartLevel v g p (extChartAt I p z, t) = g (flowOf v t z) := by
  simp only [chartLevel, (extChartAt I p).left_inv hz]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
private theorem chartLevel_self (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) :
    chartLevel v g p (extChartAt I p p, T) = g (flowOf v T p) :=
  chartLevel_extChartAt (mem_extChartAt_source p) T

/-- The equation of the hitting time is `C^n` in chart coordinates and time. -/
private theorem contDiffAt_chartLevel {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hT : (T, p) ∈ flowDomain v)
    (hg : ContMDiffAt I 𝓘(ℝ) n g (flowOf v T p)) :
    ContDiffAt ℝ n (chartLevel v g p) (extChartAt I p p, T) := by
  rw [← contMDiffAt_iff_contDiffAt]
  have htarget : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) :=
    mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I p).symm (extChartAt I p p) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt htarget
  have hflow := contMDiffAt_flowOf_comp (z := (extChartAt I p p, T)) (τ := Prod.snd)
    (f := fun u ↦ (extChartAt I p).symm u.1) hn hv contDiffAt_snd.contMDiffAt
    (hsymm.comp_of_eq contDiffAt_fst.contMDiffAt rfl) (by simpa only [extChartAt_to_inv] using hT)
  exact hg.comp_of_eq hflow (by simp)

/-- The derivative of the equation of the hitting time in the time variable is the derivative of
`g` along the field. -/
private theorem fderiv_chartLevel_comp_inr (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hT : (T, p) ∈ flowDomain v) (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p)) :
    fderiv ℝ (chartLevel v g p) (extChartAt I p p, T) ∘L .inr ℝ E ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv I g (flowOf v T p) (v (flowOf v T p))) := by
  have hdiff : DifferentiableAt ℝ (chartLevel v g p) (extChartAt I p p, T) :=
    (contDiffAt_chartLevel le_rfl hv hT hg).differentiableAt one_ne_zero
  have h₁ := hdiff.hasFDerivAt.comp T (hasFDerivAt_prodMk_right (extChartAt I p p) T)
  have h₂ : HasDerivAt (fun t ↦ chartLevel v g p (extChartAt I p p, t))
      (mvfderiv I g (flowOf v T p) (v (flowOf v T p))) T := by
    simpa [chartLevel] using hasDerivAt_comp_flowOf hv hT (hg.mdifferentiableAt one_ne_zero)
  exact h₁.unique (hasDerivAt_iff_hasFDerivAt.mp h₂)

private theorem isInvertible_fderiv_chartLevel (h : HittingData v g T p) :
    (fderiv ℝ (chartLevel v g p) (extChartAt I p p, T) ∘L .inr ℝ E ℝ).IsInvertible := by
  rw [fderiv_chartLevel_comp_inr h.1 h.2.1 h.2.2.1]
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h.2.2.2), ?_⟩
  ext
  simp

open Classical in
/-- **The hitting time of a transverse section.** Let `v` be a `C¹` vector field whose flow carries
`p` to `q = flowOf v T p`, and let `g` be `C¹` at `q` with `dg_q (v q) ≠ 0`, so that the level
`{g = g q}` is a local section through `q` transverse to `v`. Then `flowHittingTime v g T p z` is,
for `z` near `p`, the time near `T` at which the trajectory of `z` meets this level. It is the
implicit function of `g (flowOf v t z) = g q`, read in the extended chart at `p`.

Outside these hypotheses it is the constant `T`. -/
def flowHittingTime (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) : M → ℝ :=
  if h : HittingData v g T p then
    fun z ↦ (contDiffAt_chartLevel le_rfl h.1 h.2.1 h.2.2.1).implicitFunction one_ne_zero
      (isInvertible_fderiv_chartLevel h) (extChartAt I p z)
  else fun _ ↦ T

private theorem flowHittingTime_of_hittingData (h : HittingData v g T p) :
    flowHittingTime v g T p = fun z ↦
      (contDiffAt_chartLevel le_rfl h.1 h.2.1 h.2.2.1).implicitFunction one_ne_zero
        (isInvertible_fderiv_chartLevel h) (extChartAt I p z) := by
  simp only [flowHittingTime, h, dite_true]

/-- The hitting time of the section through `flowOf v T p` is `T` at `p`. -/
@[simp]
theorem flowHittingTime_self (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) :
    flowHittingTime v g T p p = T := by
  by_cases h : HittingData v g T p
  · rw [flowHittingTime_of_hittingData h]
    exact ContDiffAt.implicitFunction_apply_self (u := (extChartAt I p p, T)) _ _ _
  · simp [flowHittingTime, h]

/-- **The transition to a transverse section.** Flowing each point `z` for its hitting time
`flowHittingTime v g T p z` carries `z` near `p` into the level of `g` through `flowOf v T p`. -/
def flowTransition (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) (z : M) : M :=
  flowOf v (flowHittingTime v g T p z) z

theorem flowTransition_def (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) :
    flowTransition v g T p = fun z ↦ flowOf v (flowHittingTime v g T p z) z :=
  (rfl)

theorem flowTransition_apply (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p z : M) :
    flowTransition v g T p z = flowOf v (flowHittingTime v g T p z) z :=
  (rfl)

/-- The transition to the section through `flowOf v T p` carries `p` to `flowOf v T p`. -/
@[simp]
theorem flowTransition_self (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T : ℝ) (p : M) :
    flowTransition v g T p p = flowOf v T p := by
  rw [flowTransition_apply, flowHittingTime_self]

section Hypotheses

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hT : (T, p) ∈ flowDomain v)
  (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hv hT hg hgv

/-- **Local uniqueness of the hitting time.** Near `(T, p)`, the trajectory of `z` is in the level
of `g` through `flowOf v T p` at time `t` exactly when `t` is the hitting time of `z`. -/
theorem eventually_eq_flowHittingTime_iff :
    ∀ᶠ x in 𝓝 (T, p),
      g (flowOf v x.1 x.2) = g (flowOf v T p) ↔ x.1 = flowHittingTime v g T p x.2 := by
  have h : HittingData v g T p := ⟨hv, hT, hg, hgv⟩
  have hchart := (contDiffAt_chartLevel le_rfl hv hT hg).eventually_apply_eq_iff_implicitFunction
    one_ne_zero (isInvertible_fderiv_chartLevel h)
  have hchartAt : ContinuousAt (fun x : ℝ × M ↦ extChartAt I p x.2) (T, p) :=
    (continuousAt_extChartAt p).comp_of_eq continuousAt_snd rfl
  have hcont : ContinuousAt (fun x : ℝ × M ↦ (extChartAt I p x.2, x.1)) (T, p) :=
    hchartAt.prodMk continuousAt_fst
  filter_upwards [hcont.preimage_mem_nhds hchart,
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) p)] with x hx hsrc
  rw [mem_preimage] at hsrc
  rw [mem_preimage, mem_ofPred_eq, chartLevel_self, chartLevel_extChartAt hsrc] at hx
  rw [flowHittingTime_of_hittingData h, eq_comm (a := x.1)]
  exact hx

/-- **The flow at the hitting time lands in the section.** For every `z` near `p`, the flow is
defined at the hitting time of `z` and carries `z` into the level of `g` through
`flowOf v T p`. -/
theorem eventually_flowHittingTime :
    ∀ᶠ z in 𝓝 p, (flowHittingTime v g T p z, z) ∈ flowDomain v ∧
      g (flowOf v (flowHittingTime v g T p z) z) = g (flowOf v T p) := by
  have h : HittingData v g T p := ⟨hv, hT, hg, hgv⟩
  have hτ : ContinuousAt (flowHittingTime v g T p) p := by
    rw [flowHittingTime_of_hittingData h]
    exact ((contDiffAt_chartLevel le_rfl hv hT hg).contDiffAt_implicitFunction one_ne_zero
      (isInvertible_fderiv_chartLevel h)).continuousAt.comp_of_eq (continuousAt_extChartAt p) rfl
  have hcont : Tendsto (fun z ↦ (flowHittingTime v g T p z, z)) (𝓝 p) (𝓝 (T, p)) := by
    simpa only [flowHittingTime_self, id_eq] using (hτ.prodMk continuousAt_id).tendsto
  filter_upwards [hcont.eventually ((isOpen_flowDomain hv).mem_nhds hT),
    hcont.eventually (eventually_eq_flowHittingTime_iff hv hT hg hgv)] with z hz hz'
  exact ⟨hz, hz'.2 rfl⟩

/-- **Uniqueness of the hitting time.** A function `τ`, continuous at `p` with `τ p = T`, whose
flow carries every point near `p` into the level of `g` through `flowOf v T p`, agrees with the
hitting time near `p`. -/
theorem eventuallyEq_flowHittingTime {τ : M → ℝ} (hτ : ContinuousAt τ p) (hτp : τ p = T)
    (hτg : ∀ᶠ z in 𝓝 p, g (flowOf v (τ z) z) = g (flowOf v T p)) :
    τ =ᶠ[𝓝 p] flowHittingTime v g T p := by
  have hcont : Tendsto (fun z ↦ (τ z, z)) (𝓝 p) (𝓝 (T, p)) := by
    simpa only [hτp, id_eq] using (hτ.prodMk continuousAt_id).tendsto
  filter_upwards [hcont.eventually (eventually_eq_flowHittingTime_iff hv hT hg hgv), hτg]
    with z hz hzg
  exact hz.1 hzg

end Hypotheses

section Smooth

variable {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
  (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hT : (T, p) ∈ flowDomain v)
  (hg : ContMDiffAt I 𝓘(ℝ) n g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hn hv hT hg hgv

/-- **The hitting time is `C^n`.** For a `C^n` vector field and a `C^n` function `g`, the hitting
time of the level of `g` through `flowOf v T p` is `C^n` at `p`. -/
theorem contMDiffAt_flowHittingTime : ContMDiffAt I 𝓘(ℝ) n (flowHittingTime v g T p) p := by
  have hn' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hv₁ := hv.of_le hn'
  have hg₁ := hg.of_le hn'
  have hchart := contDiffAt_chartLevel hn hv hT hg
  have hn0 : ((n : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hinv := isInvertible_fderiv_chartLevel ⟨hv₁, hT, hg₁, hgv⟩
  -- The `C^n` implicit function of the same equation is a hitting time continuous at `p`, so it
  -- agrees with `flowHittingTime` near `p`.
  set τ : M → ℝ := fun z ↦ hchart.implicitFunction hn0 hinv (extChartAt I p z)
  have hτ : ContMDiffAt I 𝓘(ℝ) n τ p :=
    (hchart.contDiffAt_implicitFunction hn0 hinv).contMDiffAt.comp p contMDiffAt_extChartAt
  refine hτ.congr_of_eventuallyEq (eventuallyEq_flowHittingTime hv₁ hT hg₁ hgv hτ.continuousAt
    (hchart.implicitFunction_apply_self (u := (extChartAt I p p, T)) hn0 hinv) ?_).symm
  filter_upwards [(continuousAt_extChartAt p).preimage_mem_nhds
      (hchart.eventually_apply_implicitFunction hn0 hinv),
    extChartAt_source_mem_nhds (I := I) p] with z hzlevel hsrc
  rwa [mem_preimage, mem_ofPred_eq, chartLevel_self, chartLevel_extChartAt hsrc] at hzlevel

/-- **The transition to a transverse section is `C^n`.** Flowing each point near `p` for its
hitting time is a `C^n` map at `p`, with value `flowOf v T p` at `p`. -/
theorem contMDiffAt_flowTransition : ContMDiffAt I I n (flowTransition v g T p) p := by
  rw [flowTransition_def]
  exact contMDiffAt_flowOf_comp hn hv (contMDiffAt_flowHittingTime hn hv hT hg hgv)
    contMDiffAt_id (by simpa using hT)

end Smooth

section Continuous

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hT : (T, p) ∈ flowDomain v)
  (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hv hT hg hgv

/-- The hitting time of a transverse section is continuous at `p`. -/
theorem continuousAt_flowHittingTime : ContinuousAt (flowHittingTime v g T p) p :=
  (contMDiffAt_flowHittingTime le_rfl hv hT hg hgv).continuousAt

/-- The transition to a transverse section is continuous at `p`. -/
theorem continuousAt_flowTransition : ContinuousAt (flowTransition v g T p) p :=
  (contMDiffAt_flowTransition le_rfl hv hT hg hgv).continuousAt

end Continuous

section Differentiable

variable {q : M} (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hg : ContMDiffAt I 𝓘(ℝ) 1 g q)
  (hgv : mvfderiv I g q (v q) ≠ 0)
include hv hT hq hg hgv

/-- The hitting time of a section through `q = flowOf v T p` transverse to `v` is differentiable
at `p`. -/
theorem mdifferentiableAt_flowHittingTime_of_eq :
    MDifferentiableAt I 𝓘(ℝ) (flowHittingTime v g T p) p := by
  subst hq
  exact (contMDiffAt_flowHittingTime le_rfl hv hT hg hgv).mdifferentiableAt one_ne_zero

/-- The transition to a section through `q = flowOf v T p` transverse to `v` is differentiable
at `p`. -/
theorem mdifferentiableAt_flowTransition_of_eq :
    MDifferentiableAt I I (flowTransition v g T p) p := by
  subst hq
  exact (contMDiffAt_flowTransition le_rfl hv hT hg hgv).mdifferentiableAt one_ne_zero

end Differentiable

end TauCeti
