/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Analysis.Calculus.Morse.ContinuationPotential
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Analysis.Calculus.Deriv.Const
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
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
  `∂ₜ f` is bounded on the compact inner slab `M × [δ, 1 - δ]` and vanishes outside it. The
  continuity of `∂ₜ f` is `ContMDiff.continuous_deriv_prodMk`.
* **The rescaled field.** Let `V` be a vector field on `M × ℝ` whose time component is
  `C t (1 - t²) - ∂ₜ f`, as for the negative gradient of `F` for any metric `dt² + g_t`. The
  rescaled field `λ • V`, for the factor `λ = C t (1 - t²) / (C t (1 - t²) - ∂ₜ f)` of
  `TauCeti.continuationRescaling`, projects to the base field: the time component of each of its
  integral curves solves `τ' = C τ (1 - τ²)`. On a compact manifold, for every large `C`, the
  factor `λ` is smooth, positive, bounded above and below, and `1` near the two ends, so the
  integral curves of `V` and of `λ • V` are the same oriented curves up to increasing changes of
  time, with the same limits at `±∞`. This identifies the trajectory spaces of the two fields
  between critical points, and the fields agree near the critical points themselves.

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
* `TauCeti.exists_forall_lt_isMorseOn_continuationPotential`: on a compact manifold, `F` is Morse
  on the slab for every large constant.
* `TauCeti.exists_abs_deriv_le_mul_one_sub_sq`: on a compact manifold, `|∂ₜ f| ≤ K t (1 - t²)`.
* `ContMDiff.continuationRescaling`: the rescaling factor is smooth.
* `IsMIntegralCurve.hasDerivAt_snd_of_continuationRescaling_smul`: the rescaled field projects to
  the base field.
* `IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_continuationRescaling_smul` and
  `IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_of_continuationRescaling_smul`: the
  integral curves of the two fields correspond under increasing changes of time.

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
    · exact deriv_prodMk_eq_zero_of_eventually_eq (hf₀ x)
    · exact deriv_prodMk_eq_zero_of_eventually_eq (hf₁ x)
    · exact absurd h hto
  obtain ⟨rfl | rfl, hx⟩ := (mem_criticalPoints_continuationPotential_iff_of_mem_Icc
    (hf.mdifferentiableAt (by simp)) ht (hlt x t) hend).1 hcrit
  · exact (isManifoldNondegenerateCriticalPoint_continuationPotential_zero_iff hC (hf₀ x)).2
      (h₀.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx)
  · exact (isManifoldNondegenerateCriticalPoint_continuationPotential_one_iff hC (hf₁ x)).2
      (h₁.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx)

/-! ### The choice of the constant on a compact manifold -/

/-- **The time derivative is bounded by `K t (1 - t²)` on a compact manifold.** Let `f` be a `C¹`
function on `M × ℝ`, for a compact manifold `M`, independent of the time for `t < δ` and for
`t > 1 - δ`. Then `|∂ₜ f| ≤ K t (1 - t²)` in the open slab `0 < t < 1` for some `K ≥ 0`; every
`C > K` then satisfies the hypotheses of `TauCeti.continuationRescaling_mem_Icc`. -/
theorem exists_abs_deriv_le_mul_one_sub_sq [CompactSpace M]
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) {δ : ℝ} (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) :
    ∃ K, 0 ≤ K ∧ ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, |deriv (fun s ↦ f (x, s)) t| ≤ K * t * (1 - t ^ 2) := by
  obtain ⟨K, hK, hKle⟩ := (isCompact_univ (X := M)).exists_forall_le_mul_one_sub_sq
    (g := fun x t ↦ |deriv (fun s ↦ f (x, s)) t|) hδ
    (continuous_abs.comp hf.continuous_deriv_prodMk).continuousOn
    fun x _ t _ ht ↦ by
      rcases lt_or_ge t δ with htδ | htδ
      · simp [deriv_prodMk_eq_zero_of_lt (z := (x, t)) hf₀ htδ]
      · simp [deriv_prodMk_eq_zero_of_gt (z := (x, t)) hf₁ (lt_of_not_ge fun h ↦ ht ⟨htδ, h⟩)]
  exact ⟨K, hK, fun x t ht ↦ hKle x (mem_univ x) t ht⟩

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
  obtain ⟨K, hK, hKle⟩ := exists_abs_deriv_le_mul_one_sub_sq (hf.of_le (by simp)) hδ hf₀ hf₁
  refine ⟨K, fun C hKC ↦ isMorseOn_continuationPotential (hK.trans_lt hKC).ne' hf h₀ h₁
    (fun x ↦ by simpa using hgerm₀ x 0 hδ) (fun x ↦ by simpa using hgerm₁ x 1 (by linarith))
    fun x t ht ↦ ?_⟩
  have hpos : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
  calc deriv (fun s ↦ f (x, s)) t ≤ K * t * (1 - t ^ 2) := (le_abs_self _).trans (hKle x t ht)
    _ < C * t * (1 - t ^ 2) := by nlinarith

/-! ### The rescaled continuation field -/

section Rescaling

variable {δ K : ℝ}

/-- **The rescaling factor is smooth.** Let `f` be a `C^(n + 1)` function on `M × ℝ`, independent
of the time for `t < δ` and for `t > 1 - δ`, with `∂ₜ f ≠ C t (1 - t²)` in the open slab. Then the
rescaling factor `λ = C t (1 - t²) / (C t (1 - t²) - ∂ₜ f)` is `C^n` on all of `M × ℝ`: it is a
quotient with nonvanishing denominator in the open slab, and `1` near the end levels. -/
theorem _root_.ContMDiff.continuationRescaling {n : WithTop ℕ∞}
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) (n + 1) f) (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hne : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t ≠ C * t * (1 - t ^ 2)) :
    ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) n (TauCeti.continuationRescaling C f) := by
  intro z
  by_cases ht : z.2 ∈ Ioo 0 1
  · -- In the open slab, `λ` is `(b, a) ↦ 1 + b / (a - b)` applied to `∂ₜ f` and `C t (1 - t²)`.
    have ha : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) n fun z : M × ℝ ↦ C * z.2 * (1 - z.2 ^ 2) :=
      (by fun_prop : ContDiff ℝ n fun t : ℝ ↦ C * t * (1 - t ^ 2)).contMDiff.comp contMDiff_snd
    have hden : C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2 ≠ 0 :=
      sub_ne_zero.2 (hne z.1 z.2 ht).symm
    have hg : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ 1 + p.1 / (p.2 - p.1))
        (deriv (fun s ↦ f (z.1, s)) z.2, C * z.2 * (1 - z.2 ^ 2)) :=
      contDiffAt_const.add (contDiffAt_fst.div (contDiffAt_snd.sub contDiffAt_fst) hden)
    rw [show TauCeti.continuationRescaling C f = fun z ↦ 1 + deriv (fun s ↦ f (z.1, s)) z.2 /
      (C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2) from
        funext (continuationRescaling_apply C f)]
    exact ContDiffAt.comp_contMDiffAt
      (f := fun z : M × ℝ ↦ (deriv (fun s ↦ f (z.1, s)) z.2, C * z.2 * (1 - z.2 ^ 2))) hg
      ((hf.contMDiff_deriv_prodMk z).prodMk_space (ha z))
  · -- Outside the open slab, `λ = 1` near `z`, since `f` is independent of the time there.
    have hz : z.2 ∈ (Icc δ (1 - δ))ᶜ := fun h ↦ ht ⟨hδ.trans_le h.1, by linarith [h.2]⟩
    refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds (isClosed_Icc.isOpen_compl.mem_nhds hz)]
      with w hw
    exact continuationRescaling_eq_one hf₀ hf₁ hw

/-- Under the hypotheses of the trajectory comparison, the rescaling factor is continuous and lies
between `C / (C + K)` and `C / (C - K)`. -/
private theorem continuous_continuationRescaling_and_mem_Icc
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hK : 0 ≤ K) (hKC : K < C)
    (hb : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, |deriv (fun s ↦ f (x, s)) t| ≤ K * t * (1 - t ^ 2)) :
    Continuous (continuationRescaling C f) ∧
      ∀ z : M × ℝ, continuationRescaling C f z ∈ Icc (C / (C + K)) (C / (C - K)) := by
  have hne : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t ≠ C * t * (1 - t ^ 2) :=
    fun x t ht ↦ by
      have hw : 0 < t * (1 - t ^ 2) := mul_pos ht.1 (by nlinarith [ht.1, ht.2])
      have := (le_abs_self _).trans (hb x t ht)
      exact ne_of_lt (by nlinarith)
  refine ⟨(ContMDiff.continuationRescaling (n := 0) (by simpa using hf) hδ hf₀ hf₁ hne).continuous,
    fun z ↦ continuationRescaling_mem_Icc hK hKC (hb z.1 z.2) fun ht ↦ ?_⟩
  exact deriv_prodMk_eq_zero_of_notMem_Icc hf₀ hf₁ fun h ↦ ht ⟨hδ.trans_le h.1, by linarith [h.2]⟩

variable {V : (z : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ)) z} {γ : ℝ → M × ℝ}

omit [I.Boundaryless] in
/-- **The rescaled continuation field projects to the base field.** Let `V` be a vector field on
`M × ℝ` whose time component is `C t (1 - t²) - ∂ₜ f`, as for the negative gradient of the
continuation potential for any metric `dt² + g_t`, with `∂ₜ f ≠ C t (1 - t²)` in the open slab and
`∂ₜ f = 0` outside it. Along an integral curve of `λ • V`, the time component `τ` solves the base
equation `τ' = C τ (1 - τ²)` of `TauCeti.intervalBasePotential`. -/
theorem _root_.IsMIntegralCurve.hasDerivAt_snd_of_continuationRescaling_smul
    (hγ : IsMIntegralCurve γ fun z ↦ continuationRescaling C f z • V z)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hne : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t ≠ C * t * (1 - t ^ 2))
    (hend : ∀ x, ∀ t ∉ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t = 0) (s : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (C * (γ s).2 * (1 - (γ s).2 ^ 2)) s := by
  have hmap : IsMIntegralCurveOn (Prod.snd ∘ γ)
      (fun t : ℝ ↦ (C * t * (1 - t ^ 2) : TangentSpace 𝓘(ℝ) t)) univ := by
    refine (hγ.isMIntegralCurveOn univ).map_of_mfderiv_eq (fun t _ ↦ mdifferentiableAt_snd)
      fun t _ ↦ ?_
    set z := γ t
    have hz : deriv (fun s ↦ f (z.1, s)) z.2 ≠ C * z.2 * (1 - z.2 ^ 2) ∨
        deriv (fun s ↦ f (z.1, s)) z.2 = 0 := by
      by_cases ht : z.2 ∈ Ioo 0 1
      · exact .inl (hne z.1 z.2 ht)
      · exact .inr (hend z.1 z.2 ht)
    rw [mfderiv_snd]
    -- The tangent space of `M × ℝ` is the product `E × ℝ`, on which `snd` and the scalar action
    -- act componentwise; the dependent tangent space types block a rewrite with `Prod.smul_snd`.
    calc _ = continuationRescaling C f z * (V z : E × ℝ).2 := rfl
      _ = C * z.2 * (1 - z.2 ^ 2) := by rw [hV]; exact continuationRescaling_mul_sub hz
  exact (isMIntegralCurveOn_iff_isIntegralCurveOn.1 hmap s (mem_univ s)).hasDerivAt univ_mem

/-- **Trajectories of the continuation field are trajectories of the rescaled field.** Let `f` be
a `C¹` function on `M × ℝ`, independent of the time for `t < δ` and for `t > 1 - δ`, with
`|∂ₜ f| ≤ K t (1 - t²)` in the open slab for some `0 ≤ K < C`. If `γ` is an integral curve of a
vector field `V`, then `γ ∘ ψ` is an integral curve of `λ • V` for an order automorphism `ψ` of `ℝ`
fixing `0`. So `γ ∘ ψ` traces the same oriented trajectory, with the same limits at `±∞`. -/
theorem _root_.IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_continuationRescaling_smul
    (hγ : IsMIntegralCurve γ V) (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hK : 0 ≤ K) (hKC : K < C)
    (hb : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, |deriv (fun s ↦ f (x, s)) t| ≤ K * t * (1 - t ^ 2)) :
    ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      IsMIntegralCurve (γ ∘ ψ) fun z ↦ continuationRescaling C f z • V z := by
  obtain ⟨hcont, hmem⟩ := continuous_continuationRescaling_and_mem_Icc hf hδ hf₀ hf₁ hK hKC hb
  exact hγ.exists_orderIso_isMIntegralCurve_comp (hcont.comp hγ.continuous)
    (fun t ↦ (div_pos (hK.trans_lt hKC) (by linarith)).trans_le (hmem (γ t)).1)
    (fun t ↦ (hmem (γ t)).2) fun t ↦ rfl

/-- **Trajectories of the rescaled field are trajectories of the continuation field.** Under the
hypotheses of `IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_continuationRescaling_smul`,
if `η` is an integral curve of `λ • V`, then `η ∘ ψ` is an integral curve of `V` for an order
automorphism `ψ` of `ℝ` fixing `0`. -/
theorem _root_.IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_of_continuationRescaling_smul
    (hγ : IsMIntegralCurve γ fun z ↦ continuationRescaling C f z • V z)
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hK : 0 ≤ K) (hKC : K < C)
    (hb : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, |deriv (fun s ↦ f (x, s)) t| ≤ K * t * (1 - t ^ 2)) :
    ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧ IsMIntegralCurve (γ ∘ ψ) V := by
  obtain ⟨hcont, hmem⟩ := continuous_continuationRescaling_and_mem_Icc hf hδ hf₀ hf₁ hK hKC hb
  have hpos : ∀ z : M × ℝ, 0 < continuationRescaling C f z := fun z ↦
    (div_pos (hK.trans_lt hKC) (by linarith)).trans_le (hmem z).1
  -- The factor `1 / λ` is at most `(C + K) / C`, since `λ ≥ C / (C + K)`.
  refine hγ.exists_orderIso_isMIntegralCurve_comp (h := fun t ↦ (continuationRescaling C f (γ t))⁻¹)
    ((hcont.comp hγ.continuous).inv₀ fun t ↦ (hpos _).ne') (fun t ↦ inv_pos.2 (hpos _))
    (c := (C / (C + K))⁻¹) (fun t ↦ inv_anti₀ (div_pos (hK.trans_lt hKC) (by linarith))
      (hmem (γ t)).1) fun t ↦ (inv_smul_smul₀ (hpos _).ne' _).symm

end Rescaling

end TauCeti
