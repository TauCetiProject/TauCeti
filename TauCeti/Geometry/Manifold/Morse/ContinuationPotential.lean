/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ContinuationPotential
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The large-constant continuation potential on a manifold

Let `f : M × ℝ → ℝ` be a path `f_t = f (·, t)` of functions on a manifold `M`, independent of `t`
near `t = 0` and near `t = 1`. The continuation from `f₀` to `f₁` is realized by the single
function

`F(x, t) = C h(t) + f(x, t)`, with `h(t) = (t² - 1)² / 4`,

on the product manifold `M × ℝ` (`TauCeti.continuationPotential`, defined for any type `M`). This
file transfers the endpoint analysis of `TauCeti.Analysis.Calculus.Morse.ContinuationPotential`
from normed spaces to manifolds. The preferred chart of `M × ℝ` at `(x, t)` is the product of the
preferred chart of `M` at `x` and the identity of `ℝ`, so the coordinate expression of `F` is the
continuation potential of the coordinate expression of `f`, and the time derivative of `F` is
`-C t (1 - t²) + ∂ₜ f`, read without any chart.

* **Critical points.** `(x, t)` is a critical point of `F` exactly when `x` is a critical point of
  `f_t` and `∂ₜ f (x, t) = C t (1 - t²)`. If `∂ₜ f < C t (1 - t²)` in the open slab `0 < t < 1`,
  the critical points of `F` in the slab `M × [0, 1]` are the points `(p, 0)` and `(q, 1)` for
  critical points `p` of `f₀` and `q` of `f₁`.
* **The two ends.** For `C ≠ 0`, `(p, 0)` is nondegenerate exactly when `p` is a nondegenerate
  critical point of `f₀`, and then its Morse index is `ind p + 1` for `C > 0`. At the other end,
  `(q, 1)` has the index of `q`. These are the index shifts of a continuation: a trajectory from
  `(p, 0)` to `(q, 1)` that is rigid up to translation joins critical points of equal index.
* **Morse on the slab.** If `f₀` and `f₁` are Morse, `F` is a Morse function on `M × [0, 1]`.
  On a compact manifold every sufficiently large constant `C` works
  (`TauCeti.exists_forall_lt_isMorseOn_continuationPotential`), because the time derivative
  `∂ₜ f` is bounded on the compact inner slab `M × [δ, 1 - δ]` and vanishes outside it.

## Main results

* `TauCeti.mem_criticalPoints_continuationPotential_iff`: the critical points of `F`.
* `TauCeti.mem_criticalPoints_continuationPotential_iff_of_mem_Icc`: the critical points in the
  slab lie over critical points of `f₀` at `t = 0` and of `f₁` at `t = 1`.
* `TauCeti.isManifoldNondegenerateCriticalPoint_continuationPotential_zero_iff` and
  `TauCeti.isManifoldNondegenerateCriticalPoint_continuationPotential_one_iff`: nondegeneracy at
  the two ends.
* `TauCeti.manifoldMorseIndex_continuationPotential_zero` and
  `TauCeti.manifoldMorseIndex_continuationPotential_one`: the index shifts `+1` and `0`.
* `TauCeti.isMorseOn_continuationPotential`: `F` is Morse on the slab.
* `ContMDiff.continuous_deriv_prodMk`: the time derivative of a `C¹` function on `M × ℝ` is
  continuous.
* `TauCeti.exists_forall_lt_isMorseOn_continuationPotential`: on a compact manifold, `F` is Morse
  on the slab for every large constant.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (continuation maps).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {C : ℝ} {f : M × ℝ → ℝ}

/-! ### Coordinate expressions -/

/-- **The coordinate expression of the continuation potential** in the preferred chart of `M × ℝ`
is the continuation potential of the coordinate expression of `f`, since the chart is the identity
on the time factor. -/
theorem continuationPotential_comp_extChartAt_symm (z : M × ℝ) :
    continuationPotential C f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm =
      continuationPotential C (f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm) := by
  funext u
  simp only [comp_apply, continuationPotential_apply, extChartAt_prod_modelSpace_symm_apply]

/-- The time slice of the coordinate expression of `f` through the chart image of a point `x` of
the chart source is the time slice of `f` through `x`. -/
private theorem comp_extChartAt_symm_prodMk_left (z : M × ℝ) {x : M}
    (hx : x ∈ (extChartAt I z.1).source) :
    (fun s ↦ (f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm) ((extChartAt I z.1 x, s))) =
      fun s ↦ f (x, s) := by
  funext s
  simp only [comp_apply, extChartAt_prod_modelSpace_symm_apply, (extChartAt I z.1).left_inv hx]

/-- The space slice of the coordinate expression of `f` at time `s` is the coordinate expression
of the space slice of `f` at time `s`. -/
private theorem comp_extChartAt_symm_prodMk_right (z : M × ℝ) (s : ℝ) :
    (fun v ↦ (f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm) (v, s)) =
      (fun x ↦ f (x, s)) ∘ (extChartAt I z.1).symm := by
  funext v
  simp only [comp_apply, extChartAt_prod_modelSpace_symm_apply]

/-- **The time derivative in coordinates.** At the chart image of a point `(x, s)` of the chart
source, the derivative of the coordinate expression of `f` in the time direction `(0, 1)` is the
derivative of the time slice of `f` through `x`. -/
private theorem fderiv_comp_extChartAt_symm_apply_zero_one {z : M × ℝ} {x : M} {s : ℝ}
    (hx : x ∈ (extChartAt I z.1).source)
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm) (extChartAt I z.1 x, s)) :
    fderiv ℝ (f ∘ (extChartAt (I.prod 𝓘(ℝ)) z).symm) (extChartAt I z.1 x, s) (0, 1) =
      deriv (fun s' ↦ f (x, s')) s := by
  have h : HasDerivAt (fun s' : ℝ ↦ (extChartAt I z.1 x, s')) ((0 : E), (1 : ℝ)) s :=
    HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id _)
  rw [← comp_extChartAt_symm_prodMk_left z hx]
  exact ((hf.hasFDerivAt.comp_hasDerivAt s h).deriv).symm

/-- A function on `M × ℝ` independent of the time near `(x, t₀)` has zero time derivative at
`(x, t₀)`. -/
private theorem deriv_eq_zero_of_eventually_eq {x : M} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (x, t₀), f z = f (z.1, t₀)) : deriv (fun s ↦ f (x, s)) t₀ = 0 := by
  have h : (fun s ↦ f (x, s)) =ᶠ[𝓝 t₀] fun _ ↦ f (x, t₀) :=
    ((continuous_const.prodMk continuous_id).tendsto t₀).eventually hf
  rw [h.deriv_eq, deriv_const]

/-- A function on `M × ℝ` independent of the time near `(p, t₀)` has a coordinate expression
independent of the time near the chart image of `(p, t₀)`. -/
private theorem eventually_comp_extChartAt_symm_eq {p : M} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀)) :
    ∀ᶠ w in 𝓝 (extChartAt I p p, t₀),
      (f ∘ (extChartAt (I.prod 𝓘(ℝ)) (p, t₀)).symm) w =
        (f ∘ (extChartAt (I.prod 𝓘(ℝ)) (p, t₀)).symm) (w.1, t₀) := by
  have ht : Tendsto (extChartAt (I.prod 𝓘(ℝ)) (p, t₀)).symm (𝓝 (extChartAt I p p, t₀))
      (𝓝 (p, t₀)) := by
    have hc := (continuousAt_extChartAt_symm (I := I.prod 𝓘(ℝ)) (p, t₀)).tendsto
    rwa [extChartAt_to_inv, extChartAt_prod_modelSpace_apply] at hc
  filter_upwards [ht.eventually hf] with w hw
  simp only [comp_apply, extChartAt_prod_modelSpace_symm_apply] at hw ⊢
  exact hw

/-! ### Smoothness -/

/-- The continuation potential of a `C^n` function on `M × ℝ` is `C^n`. -/
theorem _root_.ContMDiff.continuationPotential {n : WithTop ℕ∞}
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) n f) :
    ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) n (continuationPotential C f) := by
  rw [continuationPotential_eq_add]
  exact ((contDiff_intervalBasePotential C).contMDiff.comp contMDiff_snd).add hf

/-! ### The two ends -/

/-- Where `f` is independent of the time near `(p, t₀)`, the point `(p, t₀)` is a nondegenerate
critical point of the continuation potential exactly when `p` is one of the slice `f (·, t₀)` and
`t₀` is one of the base potential. -/
theorem isManifoldNondegenerateCriticalPoint_continuationPotential_iff {p : M} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀)) :
    IsManifoldNondegenerateCriticalPoint (I.prod 𝓘(ℝ)) (continuationPotential C f) (p, t₀) ↔
      IsManifoldNondegenerateCriticalPoint I (fun x ↦ f (x, t₀)) p ∧
        IsNondegenerateCriticalPoint (intervalBasePotential C) t₀ := by
  rw [isManifoldNondegenerateCriticalPoint_iff, isManifoldNondegenerateCriticalPoint_iff,
    continuationPotential_comp_extChartAt_symm, extChartAt_prod_modelSpace_apply,
    isNondegenerateCriticalPoint_continuationPotential_iff (eventually_comp_extChartAt_symm_eq hf),
    comp_extChartAt_symm_prodMk_right]

/-- **The source end.** For `C ≠ 0`, if `f` is independent of the time near `(p, 0)`, then
`(p, 0)` is a nondegenerate critical point of the continuation potential exactly when `p` is one
of `f₀`. -/
theorem isManifoldNondegenerateCriticalPoint_continuationPotential_zero_iff {p : M} (hC : C ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (p, 0), f z = f (z.1, 0)) :
    IsManifoldNondegenerateCriticalPoint (I.prod 𝓘(ℝ)) (continuationPotential C f) (p, 0) ↔
      IsManifoldNondegenerateCriticalPoint I (fun x ↦ f (x, 0)) p := by
  simp [isManifoldNondegenerateCriticalPoint_continuationPotential_iff hf,
    isNondegenerateCriticalPoint_intervalBasePotential_zero hC]

/-- **The target end.** For `C ≠ 0`, if `f` is independent of the time near `(q, 1)`, then
`(q, 1)` is a nondegenerate critical point of the continuation potential exactly when `q` is one
of `f₁`. -/
theorem isManifoldNondegenerateCriticalPoint_continuationPotential_one_iff {q : M} (hC : C ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (q, 1), f z = f (z.1, 1)) :
    IsManifoldNondegenerateCriticalPoint (I.prod 𝓘(ℝ)) (continuationPotential C f) (q, 1) ↔
      IsManifoldNondegenerateCriticalPoint I (fun x ↦ f (x, 1)) q := by
  simp [isManifoldNondegenerateCriticalPoint_continuationPotential_iff hf,
    isNondegenerateCriticalPoint_intervalBasePotential_one hC]

/-- Where `f` is independent of the time near `(p, t₀)`, the Morse index of the continuation
potential at `(p, t₀)` is the sum of the indices of the slice `f (·, t₀)` at `p` and of the base
potential at `t₀`. -/
theorem manifoldMorseIndex_continuationPotential [FiniteDimensional ℝ E] {p : M} {t₀ : ℝ}
    (hf : ∀ᶠ z in 𝓝 (p, t₀), f z = f (z.1, t₀))
    (hp : ContDiffAt ℝ 2 ((fun x ↦ f (x, t₀)) ∘ (extChartAt I p).symm) (extChartAt I p p)) :
    manifoldMorseIndex (I.prod 𝓘(ℝ)) (continuationPotential C f) (p, t₀) =
      manifoldMorseIndex I (fun x ↦ f (x, t₀)) p + morseIndex (intervalBasePotential C) t₀ := by
  rw [← comp_extChartAt_symm_prodMk_right (I := I) (p, t₀)] at hp
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, continuationPotential_comp_extChartAt_symm,
    extChartAt_prod_modelSpace_apply,
    morseIndex_continuationPotential (eventually_comp_extChartAt_symm_eq hf) hp,
    comp_extChartAt_symm_prodMk_right]

/-- **The index shift at the source end is `1`.** -/
theorem manifoldMorseIndex_continuationPotential_zero [FiniteDimensional ℝ E] {p : M} (hC : 0 < C)
    (hf : ∀ᶠ z in 𝓝 (p, 0), f z = f (z.1, 0))
    (hp : ContDiffAt ℝ 2 ((fun x ↦ f (x, 0)) ∘ (extChartAt I p).symm) (extChartAt I p p)) :
    manifoldMorseIndex (I.prod 𝓘(ℝ)) (continuationPotential C f) (p, 0) =
      manifoldMorseIndex I (fun x ↦ f (x, 0)) p + 1 := by
  rw [manifoldMorseIndex_continuationPotential hf hp, morseIndex_intervalBasePotential_zero hC]

/-- **The index shift at the target end is `0`.** -/
theorem manifoldMorseIndex_continuationPotential_one [FiniteDimensional ℝ E] {q : M} (hC : 0 < C)
    (hf : ∀ᶠ z in 𝓝 (q, 1), f z = f (z.1, 1))
    (hq : ContDiffAt ℝ 2 ((fun x ↦ f (x, 1)) ∘ (extChartAt I q).symm) (extChartAt I q q)) :
    manifoldMorseIndex (I.prod 𝓘(ℝ)) (continuationPotential C f) (q, 1) =
      manifoldMorseIndex I (fun x ↦ f (x, 1)) q := by
  rw [manifoldMorseIndex_continuationPotential hf hq, morseIndex_intervalBasePotential_one hC,
    add_zero]

variable [I.Boundaryless]

/-! ### Critical points -/

/-- **The critical points of the continuation potential.** At a point `(x, t)` where `f` is
differentiable, `(x, t)` is a critical point of `F(x, t) = C h(t) + f(x, t)` exactly when `x` is a
critical point of the slice `f (·, t)` and the time derivative of `f` there is `C t (1 - t²)`. -/
theorem mem_criticalPoints_continuationPotential_iff {z : M × ℝ}
    (hf : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) f z) :
    z ∈ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) ↔
      z.1 ∈ criticalPoints I (fun x ↦ f (x, z.2)) ∧
        deriv (fun s ↦ f (z.1, s)) z.2 = C * z.2 * (1 - z.2 ^ 2) := by
  have hd := mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.1 hf
  rw [extChartAt_prod_modelSpace_apply] at hd
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    continuationPotential_comp_extChartAt_symm, extChartAt_prod_modelSpace_apply,
    fderiv_continuationPotential_eq_zero_iff hd, comp_extChartAt_symm_prodMk_right,
    ← mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    fderiv_comp_extChartAt_symm_apply_zero_one (mem_extChartAt_source z.1) hd]

/-- **The critical points of the continuation potential in the slab** `M × [0, 1]` lie over
critical points of `f₀` at `t = 0` and of `f₁` at `t = 1`, provided `∂ₜ f < C t (1 - t²)` in the
open slab and `∂ₜ f = 0` at its two ends. -/
theorem mem_criticalPoints_continuationPotential_iff_of_mem_Icc {z : M × ℝ}
    (hf : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) f z) (hz : z.2 ∈ Icc 0 1)
    (hlt : z.2 ∈ Ioo 0 1 → deriv (fun s ↦ f (z.1, s)) z.2 < C * z.2 * (1 - z.2 ^ 2))
    (hend : z.2 ∉ Ioo 0 1 → deriv (fun s ↦ f (z.1, s)) z.2 = 0) :
    z ∈ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) ↔
      (z.2 = 0 ∨ z.2 = 1) ∧ z.1 ∈ criticalPoints I (fun x ↦ f (x, z.2)) := by
  have hd := mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.1 hf
  rw [extChartAt_prod_modelSpace_apply] at hd
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    continuationPotential_comp_extChartAt_symm, extChartAt_prod_modelSpace_apply,
    fderiv_continuationPotential_eq_zero_iff_of_mem_Icc hd hz
      (by rwa [fderiv_comp_extChartAt_symm_apply_zero_one (mem_extChartAt_source z.1) hd])
      (by rwa [fderiv_comp_extChartAt_symm_apply_zero_one (mem_extChartAt_source z.1) hd]),
    comp_extChartAt_symm_prodMk_right, ← mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero]

/-! ### Morse on the slab -/

/-- **The continuation potential is a Morse function on the slab** `M × [0, 1]`. Let `f` be a smooth
function on `M × ℝ`, independent of the time near `M × {0}` and near `M × {1}`, whose ends `f₀`
and `f₁` are Morse, and let `C ≠ 0` satisfy `∂ₜ f < C t (1 - t²)` in the open slab. Then the
critical points of `F(x, t) = C h(t) + f(x, t)` in the slab are nondegenerate. -/
theorem isMorseOn_continuationPotential (hC : C ≠ 0) (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ f)
    (h₀ : IsMorse I (fun x ↦ f (x, 0))) (h₁ : IsMorse I (fun x ↦ f (x, 1)))
    (hf₀ : ∀ x, ∀ᶠ z in 𝓝 (x, 0), f z = f (z.1, 0))
    (hf₁ : ∀ x, ∀ᶠ z in 𝓝 (x, 1), f z = f (z.1, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2)) :
    IsMorseOn (I.prod 𝓘(ℝ)) (continuationPotential C f) (univ ×ˢ Icc 0 1) := by
  refine isMorseOn_iff_criticalPoints.2 ⟨hf.continuationPotential.contMDiffOn, ?_⟩
  rintro ⟨x, t⟩ ⟨-, ht⟩ hcrit
  -- At the two ends `f` is independent of the time, so its time derivative vanishes there.
  have hend : t ∉ Ioo 0 1 → deriv (fun s ↦ f (x, s)) t = 0 := fun hto ↦ by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | h
    · exact deriv_eq_zero_of_eventually_eq (hf₀ x)
    · exact deriv_eq_zero_of_eventually_eq (hf₁ x)
    · exact absurd h hto
  obtain ⟨rfl | rfl, hx⟩ := (mem_criticalPoints_continuationPotential_iff_of_mem_Icc
    (hf.mdifferentiableAt (by simp)) ht (hlt x t) hend).1 hcrit
  · exact (isManifoldNondegenerateCriticalPoint_continuationPotential_zero_iff hC (hf₀ x)).2
      (h₀.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx)
  · exact (isManifoldNondegenerateCriticalPoint_continuationPotential_one_iff hC (hf₁ x)).2
      (h₁.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx)

/-! ### The choice of the constant on a compact manifold -/

/-- **The time derivative of a `C¹` function on `M × ℝ` is continuous.** The map
`(x, t) ↦ ∂ₜ f (x, t)` is continuous; near each point it is the derivative of the coordinate
expression of `f` in the time direction, which is unchanged by the charts. -/
theorem _root_.ContMDiff.continuous_deriv_prodMk (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) :
    Continuous fun z : M × ℝ ↦ deriv (fun s ↦ f (z.1, s)) z.2 := by
  refine continuous_iff_continuousAt.2 fun z₀ ↦ ?_
  set G := f ∘ (extChartAt (I.prod 𝓘(ℝ)) z₀).symm with hG
  have hG₀ : ContDiffAt ℝ 1 G (extChartAt I z₀.1 z₀.1, z₀.2) := by
    simpa [hG, extChartAt_prod_modelSpace_apply] using
      contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 (hf z₀)
  -- The chart image of `(x, t)`, which tends to that of `z₀`.
  have hφ : ContinuousAt (fun z : M × ℝ ↦ (extChartAt I z₀.1 z.1, z.2)) z₀ :=
    ((continuousAt_extChartAt z₀.1).comp continuousAt_fst).prodMk continuousAt_snd
  have hsrc : ∀ᶠ z : M × ℝ in 𝓝 z₀, z.1 ∈ (extChartAt I z₀.1).source :=
    continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds z₀.1)
  -- Near `z₀`, the time derivative is the derivative of `G` in the time direction.
  have heq : (fun z : M × ℝ ↦ fderiv ℝ G (extChartAt I z₀.1 z.1, z.2) (0, 1)) =ᶠ[𝓝 z₀]
      fun z ↦ deriv (fun s ↦ f (z.1, s)) z.2 := by
    filter_upwards [hsrc, hφ.eventually (hG₀.eventually (by simp))] with z hz hzG
    exact fderiv_comp_extChartAt_symm_apply_zero_one hz (hzG.differentiableAt one_ne_zero)
  refine ContinuousAt.congr ?_ heq
  exact ((hG₀.continuousAt_fderiv one_ne_zero).comp_of_eq hφ rfl).clm_apply continuousAt_const

/-- **The choice of the constant on a compact manifold.** Let `f` be a smooth function on `M × ℝ`,
for a compact manifold `M`, with `f (x, t) = f (x, 0)` for `t < δ` and `f (x, t) = f (x, 1)` for
`t > 1 - δ`, whose ends `f₀` and `f₁` are Morse. Then for every sufficiently large `C` the
continuation potential `F(x, t) = C h(t) + f(x, t)` is a Morse function on the slab `M × [0, 1]`.
-/
theorem exists_forall_lt_isMorseOn_continuationPotential [CompactSpace M]
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ f) {δ : ℝ} (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (h₀ : IsMorse I (fun x ↦ f (x, 0))) (h₁ : IsMorse I (fun x ↦ f (x, 1))) :
    ∃ K, ∀ C, K < C → IsMorseOn (I.prod 𝓘(ℝ)) (continuationPotential C f) (univ ×ˢ Icc 0 1) := by
  -- Near the two ends, `f` is independent of the time.
  have hgerm₀ : ∀ x t, t < δ → ∀ᶠ z in 𝓝 (x, t), f z = f (z.1, t) := fun x t ht ↦ by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (Iio_mem_nhds ht)] with z hz
    rw [hf₀ z.1 z.2 hz, hf₀ z.1 t ht]
  have hgerm₁ : ∀ x t, 1 - δ < t → ∀ᶠ z in 𝓝 (x, t), f z = f (z.1, t) := fun x t ht ↦ by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)] with z hz
    rw [hf₁ z.1 z.2 hz, hf₁ z.1 t ht]
  -- The time derivative is bounded by `K t (1 - t²)` on the open slab.
  obtain ⟨K, hK, hKle⟩ := (isCompact_univ (X := M)).exists_forall_le_mul_one_sub_sq
    (g := fun x t ↦ deriv (fun s ↦ f (x, s)) t) hδ
    ((hf.of_le (m := 1) (by simp)).continuous_deriv_prodMk.continuousOn)
    fun x _ t _ ht ↦ by
      rcases lt_or_ge t δ with htδ | htδ
      · exact (deriv_eq_zero_of_eventually_eq (hgerm₀ x t htδ)).le
      · have h1 : 1 - δ < t := lt_of_not_ge fun h ↦ ht ⟨htδ, h⟩
        exact (deriv_eq_zero_of_eventually_eq (hgerm₁ x t h1)).le
  refine ⟨K, fun C hKC ↦ isMorseOn_continuationPotential (hK.trans_lt hKC).ne' hf h₀ h₁
    (fun x ↦ by simpa using hgerm₀ x 0 hδ) (fun x ↦ by simpa using hgerm₁ x 1 (by linarith))
    fun x t ht ↦ ?_⟩
  have hpos : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
  calc deriv (fun s ↦ f (x, s)) t ≤ K * t * (1 - t ^ 2) := hKle x (mem_univ x) t ht
    _ < C * t * (1 - t ^ 2) := by nlinarith

end TauCeti
