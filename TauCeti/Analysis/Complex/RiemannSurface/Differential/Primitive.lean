/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
import Mathlib.Analysis.Complex.HasPrimitives
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local primitives of holomorphic `1`-forms and flat charts

A holomorphic `1`-form `ω` on a Riemann surface `X` is locally the differential of a holomorphic
function: in a chart `z` with `ω = c(z) dz`, a primitive of `c` on a disc is such a function
(`TauCeti.RiemannSurface.OneForm.HolomorphicAt.exists_mvfderiv_eventuallyEq`, from Mathlib's
`DifferentiableOn.isExactOn_ball`). Two functions with the same differential near a point differ
by a constant near that point
(`TauCeti.RiemannSurface.sub_eventuallyEq_const_of_mvfderiv_eventuallyEq`).

Where `ω` does not vanish, a primitive has nonzero differential, so it is a local coordinate. This
gives a **flat chart** of `ω`: a chart `e` of the maximal holomorphic atlas with `de = ω` on its
whole domain, which may be centred at any point and chosen inside any neighbourhood
(`TauCeti.RiemannSurface.OneForm.HolomorphicAt.exists_mem_maximalAtlas_mvfderiv_eq`). Two flat
charts of the same `1`-form differ by a translation near each common point
(`TauCeti.RiemannSurface.OneForm.sub_eventuallyEq_const_of_mvfderiv_eq`). So a nowhere vanishing
holomorphic `1`-form gives a translation atlas, in which `ω = dz` in every chart; this is the local
structure behind integrating a holomorphic `1`-form on a surface of genus one.

## Main results

* `TauCeti.RiemannSurface.OneForm.HolomorphicAt.exists_mvfderiv_eventuallyEq`: local primitives.
* `TauCeti.RiemannSurface.sub_eventuallyEq_const_of_mvfderiv_eventuallyEq`: primitives are unique
  up to a locally constant function.
* `TauCeti.RiemannSurface.OneForm.HolomorphicAt.exists_mem_maximalAtlas_mvfderiv_eq`: flat charts.
* `TauCeti.RiemannSurface.OneForm.sub_eventuallyEq_const_of_mvfderiv_eq`: flat charts of one
  `1`-form differ locally by translations.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §10 (local primitives of closed differential forms).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter VIII §1 (local primitives of holomorphic
  `1`-forms and the Abel–Jacobi map).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- **Primitives are locally unique up to a constant.** Two functions holomorphic near `y` with the
same differential near `y` differ by a constant near `y`. -/
theorem sub_eventuallyEq_const_of_mvfderiv_eventuallyEq {f g : X → ℂ} {y : X}
    (hf : ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z)
    (hg : ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z)
    (hfg : ∀ᶠ z in 𝓝 y, mvfderiv 𝓘(ℂ) f z = mvfderiv 𝓘(ℂ) g z) :
    (fun z ↦ f z - g z) =ᶠ[𝓝 y] fun _ ↦ f y - g y := by
  -- Work on a ball in the chart at `y`, where the chart representatives have equal derivatives.
  let c := chartAt ℂ y
  have hc : c ∈ maximalAtlas 𝓘(ℂ) 1 X := chart_mem_maximalAtlas y
  have hy : y ∈ c.source := mem_chart_source ℂ y
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 ((hf.and hg).and hfg)
  have hV : c.target ∩ c.symm ⁻¹' (c.source ∩ U) ∈ 𝓝 (c y) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (c.open_source.inter hUo)
      |>.mem_nhds ⟨c.map_source hy, by simpa [c.left_inv hy] using ⟨hy, hyU⟩⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hpt : ∀ z ∈ Metric.ball (c y) r, z ∈ c.target ∧ c.symm z ∈ c.source ∧ c.symm z ∈ U :=
    fun z hz ↦ ⟨(hball hz).1, (hball hz).2.1, (hball hz).2.2⟩
  have hdiff : ∀ {h : X → ℂ}, (∀ z ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h z) →
      DifferentiableOn ℂ (h ∘ c.symm) (Metric.ball (c y) r) := fun hh z hz ↦
    (mdifferentiableAt_iff_differentiableAt.1 ((hh _ (hpt z hz).2.2).comp z
      (mdifferentiableAt_symm_of_mem_maximalAtlas hc (hpt z hz).1))).differentiableWithinAt
  have hF := hdiff fun z hz ↦ (hU z hz).1.1
  have hG := hdiff fun z hz ↦ (hU z hz).1.2
  -- `df = (f ∘ c⁻¹)' dc` and `dg = (g ∘ c⁻¹)' dc` with `dc ≠ 0`.
  have hderiv : (Metric.ball (c y) r).EqOn (deriv (f ∘ c.symm)) (deriv (g ∘ c.symm)) := by
    intro z hz
    obtain ⟨hzt, hzs, hzU⟩ := hpt z hz
    have h := (hU _ hzU).2
    rw [OneForm.mvfderiv_eq_deriv_smul (f := f) hc hzs,
      OneForm.mvfderiv_eq_deriv_smul (f := g) hc hzs, c.right_inv hzt] at h
    exact smul_left_injective ℂ (OneForm.mvfderiv_ne_zero hc hzs) h
  obtain ⟨a, ha⟩ := Metric.isOpen_ball.exists_eq_add_of_deriv_eq
    (convex_ball _ _).isPreconnected hF hG hderiv
  have hya : f y - g y = a := by
    have h := ha (Metric.mem_ball_self hr)
    simp only [comp_apply, c.left_inv hy] at h
    rw [h]
    ring
  filter_upwards [c.open_source.mem_nhds hy,
    c.continuousAt hy |>.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))]
    with z hzs hz
  have h := ha hz
  simp only [comp_apply, c.left_inv hzs] at h
  rw [h, hya]
  ring

namespace OneForm

variable {ω : OneForm X} {x : X}

/-- **Local primitives.** A `1`-form holomorphic at `x` is, near `x`, the differential of a
function holomorphic near `x`. -/
theorem HolomorphicAt.exists_mvfderiv_eventuallyEq (hω : ω.HolomorphicAt x) :
    ∃ f : X → ℂ, (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) ∧
      ∀ᶠ y in 𝓝 x, mvfderiv 𝓘(ℂ) f y = ω y := by
  -- In the chart `c` at `x`, `ω = c' dc` for a primitive `G` of the coefficient on a disc.
  let c := chartAt ℂ x
  have hc : c ∈ maximalAtlas 𝓘(ℂ) 1 X := chart_mem_maximalAtlas x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hev : ∀ᶠ z in 𝓝 (c x), AnalyticAt ℂ (ω.coeff c) z ∧ z ∈ c.target :=
    ((holomorphicAt_def ω x).1 hω).eventually_analyticAt.and
      (c.open_target.mem_nhds (c.map_source hx))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hev
  obtain ⟨G, hG⟩ := DifferentiableOn.isExactOn_ball (f := ω.coeff c) (c := c x) (r := r)
    fun z hz ↦ (hball hz).1.differentiableAt.differentiableWithinAt
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ c y ∈ Metric.ball (c x) r :=
    (c.open_source.eventually_mem hx).and
      (c.continuousAt hx |>.eventually
        (Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hr)))
  refine ⟨G ∘ c, hnear.mono fun y hy ↦ ?_, hnear.mono fun y hy ↦ ?_⟩
  · exact (hG _ hy.2).differentiableAt.mdifferentiableAt.comp y
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hy.1)
  · -- The chart representative of `G ∘ c` is `G` near `c y`.
    have hrep : G ∘ c ∘ c.symm =ᶠ[𝓝 (c y)] G := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hy.1)] with z hz
      simp [c.right_inv hz]
    rw [mvfderiv_eq_deriv_smul hc hy.1, ← (coeff_eq_iff ω hc hy.1).1 rfl, comp_assoc,
      hrep.deriv_eq, (hG _ hy.2).deriv]

/-- **Flat charts.** If a `1`-form `ω` is holomorphic and nonzero at `x`, there is a chart `e` of
the maximal holomorphic atlas, centred at `x` and with domain inside any prescribed neighbourhood
of `x`, in which `ω = de` on the whole domain of `e`. -/
theorem HolomorphicAt.exists_mem_maximalAtlas_mvfderiv_eq (hω : ω.HolomorphicAt x)
    (hx : ω x ≠ 0) {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ W ∧ ∀ y ∈ e.source, mvfderiv 𝓘(ℂ) e y = ω y := by
  obtain ⟨f, hf, hdf⟩ := hω.exists_mvfderiv_eventuallyEq
  -- A primitive of `ω` has nonzero differential at `x`, so local multiplicity one there.
  have hnc : ¬EventuallyConst f (𝓝 x) := fun h ↦ hx <| by
    obtain ⟨b, hb⟩ := eventuallyConst_iff_exists_eventuallyEq.1 h
    rw [← hdf.self_of_nhds, Filter.EventuallyEq.mvfderiv_eq hb,
      TauCeti.mvfderiv_eq_zero_iff.2 (mfderiv_const ..)]
  have hm : localMultiplicity f x = 1 := by
    have h := order_mvfderiv_eq_localMultiplicity_sub_one hf hnc
    rw [order_congr (hdf.filter_mono nhdsWithin_le_nhds), hω.order_eq_zero hx] at h
    have h' : ((localMultiplicity f x : ℤ) - 1) = 0 := by exact_mod_cast h.symm
    omega
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 (hf.and hdf)
  obtain ⟨e, he, hxe, he0, hsub, hpow⟩ := exists_chart_eq_pow_localMultiplicity hf hnc
    (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x)) (inter_mem hW (hUo.mem_nhds hxU))
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq, hm, pow_one] at hpow
  refine ⟨e, he, hxe, he0, fun y hy ↦ (hsub hy).1, fun y hy ↦ ?_⟩
  -- On its open domain, `e` is `f` minus a constant.
  have heq : (fun z ↦ f z + -f x) =ᶠ[𝓝 y] e := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    rw [← sub_eq_add_neg, (hpow z hz).2]
  rw [← Filter.EventuallyEq.mvfderiv_eq heq, TauCeti.mvfderiv_add_const, (hU y (hsub hy).2).2]

/-- **Flat charts differ by translations.** Two charts with `ω = de` and `ω = de'` on their
domains differ by a constant near each common point of their domains. -/
theorem sub_eventuallyEq_const_of_mvfderiv_eq {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (hω : ∀ y ∈ e.source, mvfderiv 𝓘(ℂ) e y = ω y)
    (hω' : ∀ y ∈ e'.source, mvfderiv 𝓘(ℂ) e' y = ω y) {y : X} (hy : y ∈ e.source)
    (hy' : y ∈ e'.source) : (fun z ↦ e' z - e z) =ᶠ[𝓝 y] fun _ ↦ e' y - e y := by
  have hs : ∀ᶠ z in 𝓝 y, z ∈ e.source ∧ z ∈ e'.source :=
    (e.open_source.eventually_mem hy).and (e'.open_source.eventually_mem hy')
  refine sub_eventuallyEq_const_of_mvfderiv_eventuallyEq
    (hs.mono fun z hz ↦ mdifferentiableAt_of_mem_maximalAtlas he' hz.2)
    (hs.mono fun z hz ↦ mdifferentiableAt_of_mem_maximalAtlas he hz.1)
    (hs.mono fun z hz ↦ ?_)
  rw [hω z hz.1, hω' z hz.2]

end OneForm

end TauCeti.RiemannSurface
