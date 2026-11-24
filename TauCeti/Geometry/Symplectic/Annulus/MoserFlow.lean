/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Symplectic.Area.StripMoser
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Dynamics.Flow.Variational
import TauCeti.Geometry.Symplectic.Liouville.Plane
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The Moser flow of a periodic density on the annulus strip

Let `ρ = 1 + g` be a `C^r` density on the plane (`r ≥ 1`), `1`-periodic in the first coordinate
and positive on the strip `ℝ × [0, 1]`, so that `ρ dx ∧ dy` is an area form on the strip covering
the closed annulus `(ℝ / ℤ) × [0, 1]`. Suppose the annulus has the same area for `ρ dx ∧ dy` as
for `dx ∧ dy`, that is `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`. This file integrates the Moser vector field
`X_t = (1 + t g)⁻¹ (-b, a)` of `TauCeti.Geometry.Symplectic.Area.StripMoser`
(`TauCeti.stripMoserVectorField`) on the strip, and shows that its time-one map `ψ₁` is a
diffeomorphism pulling `ρ dx ∧ dy` back to `dx ∧ dy`:

`ρ(ψ₁ p) det Dψ₁(p) = 1` for every `p` in the strip.

This is the correction that makes a smooth isotopy of the closed annulus area preserving: if a
diffeomorphism `h` of the strip satisfies `h^* (dx ∧ dy) = ρ dx ∧ dy`, then `h ∘ ψ₁` preserves
`dx ∧ dy`. The construction keeps everything the annulus needs: each `ψ_t` commutes with the
deck translation `(x, y) ↦ (x + 1, y)`, maps each of the boundary lines `y = 0` and `y = 1`
into itself, and maps the strip bijectively onto itself.

The field `X_t` is only defined where `1 + t g ≠ 0`, which contains `[0, 1] × (ℝ × [0, 1])`, and
it is not globally Lipschitz there. So the proof cuts it off, by a bump function equal to one
near `[0, 1]` in the time and in the height coordinate, to a field that is `C^r`, periodic in `x`,
and supported in a band of bounded time and height. A `C¹` field with these properties is
globally Lipschitz, and its global time-dependent flow `TauCeti.timeDependentFlow` exists. Its
second component vanishes on both boundary lines, because `X_t` is tangent to them. By uniqueness
of solutions of the scalar equation satisfied by the height, the flow preserves both boundary
lines (`TauCeti.timeDependentFlow_snd_eq_of_snd_eq`), and then, by the intermediate value theorem,
the strip (`TauCeti.timeDependentFlow_snd_mem_Icc`). On the strip the cut-off field is
`X_t` for `t ∈ [0, 1]`, so Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField`) applies along every orbit
starting in the strip. Periodicity of the flow follows from uniqueness of solutions as well
(`TauCeti.timeDependentFlow_add_const`).

## Main results

* `TauCeti.exists_stripMoserFlow`: the Moser flow of a periodic density of the correct total
  area exists on the strip, consists of `C^r` diffeomorphisms of the plane commuting with the
  deck translation and preserving both boundary lines and the strip, and its time-one map pulls
  `ρ dx ∧ dy` back to `dx ∧ dy`.

## References

* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965),
  286–294.
* Charles Conley and Eduard Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Set Filter Function Metric
open scoped Topology Manifold ContDiff NNReal

namespace TauCeti

variable {g : ℝ × ℝ → ℝ}

/-! ### Uniform positivity near the strip -/

/-- On `[0, 1]`, `1 + t c = (1 - t) + t (1 + c)` is a convex combination of `1` and `1 + c`, so it
is positive when `1 + c` is. -/
private theorem one_add_mul_pos {t c : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hc : 0 < 1 + c) :
    0 < 1 + t * c := by
  obtain ⟨ht₀, ht₁⟩ := ht
  nlinarith [mul_nonneg (sub_nonneg.2 ht₁) hc.le, mul_nonneg ht₀ hc.le]

/-- A point of `[-d, 1 + d]` lies within `d` of `[0, 1]`. -/
private theorem exists_mem_Icc_dist_le {d t : ℝ} (hd : 0 ≤ d) (ht : t ∈ Icc (-d) (1 + d)) :
    ∃ t₀ ∈ Icc (0 : ℝ) 1, dist t t₀ ≤ d := by
  rcases le_total t 0 with h0 | h0
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1]
  rcases le_total t 1 with h1 | h1
  · exact ⟨t, ⟨h0, h1⟩, by simpa using hd⟩
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.2]

/-- For a periodic `g` with `1 + g` positive on the strip, the densities `1 + t g` stay positive,
uniformly in `x`, for `t` and the height `y` in a neighbourhood `[-d, 1 + d]` of `[0, 1]`. -/
private theorem exists_pos_forall_one_add_mul_pos (hg : Continuous g)
    (hper : ∀ x y, g (x + 1, y) = g (x, y)) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g (x, y)) :
    ∃ d > 0, ∀ t ∈ Icc (-d) (1 + d), ∀ y ∈ Icc (-d) (1 + d), ∀ x, 0 < 1 + t * g (x, y) := by
  set S : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hU : IsOpen {q : ℝ × ℝ × ℝ | 0 < 1 + q.1 * g q.2} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_fst.mul (hg.comp continuous_snd)))
  have hSU : S ⊆ {q : ℝ × ℝ × ℝ | 0 < 1 + q.1 * g q.2} := fun q hq ↦
    one_add_mul_pos hq.1 (hpos _ _ hq.2.2)
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_thickening_subset_open hU hSU
  refine ⟨δ / 2, half_pos hδ, fun t ht y hy x ↦ ?_⟩
  obtain ⟨t₀, ht₀, htt₀⟩ := exists_mem_Icc_dist_le (half_pos hδ).le ht
  obtain ⟨y₀, hy₀, hyy₀⟩ := exists_mem_Icc_dist_le (half_pos hδ).le hy
  -- Move `x` into `[0, 1)` by periodicity; the point is then within `δ` of `S`.
  have hfract : g (Int.fract x, y) = g (x, y) := by
    have h := Function.Periodic.sub_int_mul_eq (f := fun x ↦ g (x, y)) (x := x)
      (fun x ↦ hper x y) ⌊x⌋
    simpa only [mul_one, Int.self_sub_floor] using h
  have hmem : (t, Int.fract x, y) ∈ thickening δ S := mem_thickening_iff.2
    ⟨(t₀, Int.fract x, y₀), ⟨ht₀, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, hy₀⟩, by
      simp only [Prod.dist_eq, dist_self]
      exact max_lt (htt₀.trans_lt (half_lt_self hδ)) (max_lt hδ (hyy₀.trans_lt (half_lt_self hδ)))⟩
  have h : 0 < 1 + t * g (Int.fract x, y) := hδU hmem
  rwa [hfract] at h

/-! ### The cut-off Moser field -/

/-- The Moser vector field cut off by the bump `χ`, centred at `1 / 2`, in the time and in the
height coordinate. -/
private def cutoffField (g : ℝ × ℝ → ℝ) (χ : ContDiffBump (1 / 2 : ℝ)) (t : ℝ) (p : ℝ × ℝ) :
    ℝ × ℝ :=
  (χ t * χ p.2) • stripMoserVectorField g t p

/-- The cut-off field vanishes near every point whose time or height lies outside the support of
the bump. -/
private theorem cutoffField_eventuallyEq_zero (χ : ContDiffBump (1 / 2 : ℝ)) {q : ℝ × ℝ × ℝ}
    (hq : ¬(q.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧ q.2.2 ∈ closedBall (1 / 2 : ℝ) χ.rOut)) :
    (fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2) =ᶠ[𝓝 q] 0 := by
  rw [← χ.tsupport_eq, not_and_or] at hq
  rcases hq with hq | hq
  · filter_upwards [(continuous_fst.tendsto q).eventually (notMem_tsupport_iff_eventuallyEq.1 hq)]
      with q' hq'
    simp [cutoffField, hq']
  · filter_upwards [(continuous_snd.snd.tendsto q).eventually
      (notMem_tsupport_iff_eventuallyEq.1 hq)] with q' hq'
    simp [cutoffField, hq']

/-- The cut-off field is `C^n` when `g` is and `1 + t g` does not vanish on the support of the
cut-off. -/
private theorem contDiff_cutoffField {n : ℕ∞} (hg : ContDiff ℝ n g)
    (χ : ContDiffBump (1 / 2 : ℝ))
    (hχ : ∀ t ∈ closedBall (1 / 2 : ℝ) χ.rOut, ∀ y ∈ closedBall (1 / 2 : ℝ) χ.rOut, ∀ x,
      0 < 1 + t * g (x, y)) :
    ContDiff ℝ n fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2 := by
  refine contDiff_iff_contDiffAt.2 fun q ↦ ?_
  by_cases hq : q.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧ q.2.2 ∈ closedBall (1 / 2 : ℝ) χ.rOut
  · have hne : 1 + q.1 * g q.2 ≠ 0 := (hχ _ hq.1 _ hq.2 q.2.1).ne'
    have hopen : IsOpen {q : ℝ × ℝ × ℝ | 1 + q.1 * g q.2 ≠ 0} :=
      isOpen_ne_fun (continuous_const.add (continuous_fst.mul (hg.continuous.comp
        continuous_snd))) continuous_const
    exact ((χ.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd.snd)).contDiffAt.smul
      ((contDiffOn_stripMoserVectorField hg).contDiffAt (hopen.mem_nhds hne))
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoffField_eventuallyEq_zero χ hq)

/-- A `C¹` cut-off field which is periodic in `x` is globally Lipschitz: its derivative is
bounded on one period of its support, which is compact. -/
private theorem exists_lipschitzWith_cutoffField (χ : ContDiffBump (1 / 2 : ℝ))
    (hF : ContDiff ℝ 1 fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2)
    (hper : ∀ t x y, cutoffField g χ t (x + 1, y) = cutoffField g χ t (x, y)) :
    ∃ C, LipschitzWith C fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2 := by
  set F := fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2
  set B := closedBall (1 / 2 : ℝ) χ.rOut
  obtain ⟨C, hC⟩ := ((isCompact_closedBall _ _).prod (isCompact_Icc.prod
    (isCompact_closedBall _ _))).exists_bound_of_continuousOn
      (s := B ×ˢ (Icc (0 : ℝ) 1 ×ˢ B)) (hF.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨C.toNNReal, lipschitzWith_of_nnNorm_fderiv_le (hF.differentiable one_ne_zero)
    fun q ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal']
  by_cases hq : q.1 ∈ B ∧ q.2.2 ∈ B
  · -- Translate `q` by an integer in `x` into the compact set `B × [0, 1] × B`.
    set w : ℝ × ℝ × ℝ := (0, ((⌊q.2.1⌋ : ℤ) : ℝ), 0)
    have hFw : (fun q' ↦ F (q' + w)) = F := by
      funext ⟨t, x, y⟩
      have h := (Function.Periodic.int_mul (f := fun x ↦ cutoffField g χ t (x, y)) (c := 1)
        (fun x ↦ hper t x y) ⌊q.2.1⌋) x
      simpa [F, w] using h
    have hq' : q - w ∈ B ×ˢ (Icc (0 : ℝ) 1 ×ˢ B) :=
      ⟨by simpa [w] using hq.1, ⟨by simp [w],
        by simpa [w] using (Int.fract_lt_one q.2.1).le⟩, by simpa [w] using hq.2⟩
    have hd : fderiv ℝ F q = fderiv ℝ F (q - w) := by
      conv_rhs => rw [← hFw]
      rw [fderiv_comp_add_right, sub_add_cancel]
    rw [hd]
    exact (hC _ hq').trans (le_max_left _ _)
  · rw [(cutoffField_eventuallyEq_zero χ hq).fderiv_eq, fderiv_zero]
    simp

/-- The cut-off Moser field: a `C^r` field on the plane with a globally Lipschitz suspension,
periodic in `x`, tangent to both boundary lines of the strip, and equal to the Moser field near
every point of the strip at the times `t ∈ [0, 1]`. -/
private theorem exists_cutoff_stripMoserVectorField {r : ℕ∞} (hr : 1 ≤ r) (hg : ContDiff ℝ r g)
    (hper : ∀ x y, g (x + 1, y) = g (x, y)) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g (x, y))
    (harea : ∫ y in (0 : ℝ)..1, stripRowMean g y = 0) :
    ∃ (Y : ℝ → ℝ × ℝ → ℝ × ℝ) (K : ℝ≥0) (_ : LipschitzWith K (timeDependentSuspension Y)),
      ContDiff ℝ r (fun q : ℝ × ℝ × ℝ ↦ Y q.1 q.2) ∧ (∀ t p, Y t (p + (1, 0)) = Y t p) ∧
      (∀ t x, (Y t (x, 0)).2 = 0) ∧ (∀ t x, (Y t (x, 1)).2 = 0) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
        Y t =ᶠ[𝓝 p] stripMoserVectorField g t := by
  obtain ⟨d, hd, hdpos⟩ := exists_pos_forall_one_add_mul_pos hg.continuous hper hpos
  -- The bump is one on `[-d / 2, 1 + d / 2]` and supported in `[-d, 1 + d]`.
  let χ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 + d / 2, 1 / 2 + d, by positivity, by linarith⟩
  have hB : closedBall (1 / 2 : ℝ) χ.rOut = Icc (-d) (1 + d) := by
    simp only [χ, Real.closedBall_eq_Icc]
    congr 1 <;> ring
  have hone (t : ℝ) (ht : t ∈ Ioo (-(d / 2)) (1 + d / 2)) : χ t = 1 := by
    refine χ.one_of_mem_closedBall ?_
    simp only [χ, Real.closedBall_eq_Icc, mem_Icc]
    constructor <;> linarith [ht.1, ht.2]
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-(d / 2)) (1 + d / 2) := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hY : ContDiff ℝ r fun q : ℝ × ℝ × ℝ ↦ cutoffField g χ q.1 q.2 :=
    contDiff_cutoffField hg χ (by rw [hB]; exact hdpos)
  have hYper (t : ℝ) (p : ℝ × ℝ) : cutoffField g χ t (p + (1, 0)) = cutoffField g χ t p := by
    obtain ⟨x, y⟩ := p
    simp only [cutoffField, Prod.mk_add_mk, add_zero,
      stripMoserVectorField_add_one hg.continuous hper]
  obtain ⟨C, hC⟩ := exists_lipschitzWith_cutoffField χ (hY.of_le (by exact_mod_cast hr))
    fun t x y ↦ by simpa using hYper t (x, y)
  refine ⟨cutoffField g χ, C, lipschitzWith_timeDependentSuspension hC, hY, hYper,
    fun t x ↦ by simp [cutoffField], fun t x ↦ by
      simp [cutoffField, stripMoserDxCoeff_one_eq_zero_iff.2 harea], fun t ht p hp ↦ ?_⟩
  filter_upwards [(continuous_snd.tendsto p).eventually (isOpen_Ioo.mem_nhds (hIcc hp))]
    with p' hp'
  simp only [cutoffField, hone t (hIcc ht), hone p'.2 hp', mul_one, one_smul]

/-! ### The Moser flow -/

/-- **The Moser flow on the annulus strip.** Let `1 + g` be a `C^r` density (`r ≥ 1`),
`1`-periodic in `x`, positive on the strip `ℝ × [0, 1]`, with `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`, so that
`(1 + g) dx ∧ dy` gives the annulus the same area as `dx ∧ dy`. Then there is a family `ψ_t` of
`C^r` diffeomorphisms of the plane such that

* `ψ₀ = id`, and for `t ∈ [0, 1]` the orbit of every point of the strip solves
  `∂ₜ ψ_t = X_t ∘ ψ_t` for the Moser vector field `X_t` (`TauCeti.stripMoserVectorField`);
* each `ψ_t` commutes with the deck translation `(x, y) ↦ (x + 1, y)`, maps each boundary line
  `y = 0` and `y = 1` into itself, and maps the strip bijectively onto itself;
* `ψ₁` pulls `(1 + g) dx ∧ dy` back to `dx ∧ dy` on the strip:
  `(1 + g (ψ₁ p)) det Dψ₁(p) = 1`. -/
theorem exists_stripMoserFlow {r : ℕ∞} (hr : 1 ≤ r) (hg : ContDiff ℝ r g)
    (hper : ∀ x y, g (x + 1, y) = g (x, y)) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g (x, y))
    (harea : ∫ y in (0 : ℝ)..1, stripRowMean g y = 0) :
    ∃ ψ : ℝ → (ℝ × ℝ) ≃ₘ^r⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
      (∀ p, ψ 0 p = p) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
        HasDerivAt (fun s ↦ ψ s p) (stripMoserVectorField g t (ψ t p)) t) ∧
      (∀ t p, ψ t (p + (1, 0)) = ψ t p + (1, 0)) ∧
      (∀ t x, (ψ t (x, 0)).2 = 0) ∧ (∀ t x, (ψ t (x, 1)).2 = 1) ∧
      (∀ t, BijOn (ψ t) (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (1 + g (ψ 1 p)) * (fderiv ℝ (ψ 1) p).det = 1 := by
  obtain ⟨Y, K, hS, hY, hYper, h₀, h₁, hYX⟩ :=
    exists_cutoff_stripMoserVectorField hr hg hper hpos harea
  have hstrip (s t : ℝ) : MapsTo (timeDependentFlow Y hS s t) (univ ×ˢ Icc (0 : ℝ) 1)
      (univ ×ˢ Icc (0 : ℝ) 1) := fun p hp ↦
    ⟨trivial, timeDependentFlow_snd_mem_Icc hS h₀ h₁ s t hp.2⟩
  let ψ (t : ℝ) : (ℝ × ℝ) ≃ₘ^r⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ) :=
    ⟨⟨timeDependentFlow Y hS 0 t, timeDependentFlow Y hS t 0,
      leftInverse_timeDependentFlow Y hS 0 t, rightInverse_timeDependentFlow Y hS 0 t⟩,
      (contDiff_timeDependentFlow_apply hS hY 0 t).contMDiff,
      (contDiff_timeDependentFlow_apply hS hY t 0).contMDiff⟩
  have hψ (t : ℝ) : ⇑(ψ t) = timeDependentFlow Y hS 0 t := rfl
  have horbit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ ψ s p) (stripMoserVectorField g t (ψ t p)) t := by
    simp only [hψ]
    rw [← (hYX t ht _ (hstrip 0 t hp).2).eq_of_nhds]
    exact hasDerivAt_timeDependentFlow Y hS 0 t p
  refine ⟨ψ, fun p ↦ timeDependentFlow_self Y hS 0 p, horbit,
    fun t p ↦ timeDependentFlow_add_const Y hS (hYper ·) 0 t p,
    fun t x ↦ timeDependentFlow_snd_eq_of_snd_eq hS h₀ 0 t rfl,
    fun t x ↦ timeDependentFlow_snd_eq_of_snd_eq hS h₁ 0 t rfl,
    fun t ↦ InvOn.bijOn ⟨fun p _ ↦ leftInverse_timeDependentFlow Y hS 0 t p,
      fun p _ ↦ rightInverse_timeDependentFlow Y hS 0 t p⟩ (hstrip 0 t) (hstrip t 0),
    fun p hp ↦ ?_⟩
  -- Moser's identity along the orbit of `p`, evaluated on the standard basis.
  have h := compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField
    (hg.of_le (by exact_mod_cast hr)) (ψ := fun t ↦ ψ t) (x := p)
    (fun t ht ↦ (one_add_mul_pos ht (hpos _ _ (hstrip 0 t hp).2)).ne')
    (fun t ht ↦ horbit t ht p hp)
    (fun t ht ↦ by
      simp only [hψ]
      rw [← (hYX t ht _ (hstrip 0 t hp).2).fderiv_eq]
      exact hasDerivAt_fderiv_timeDependentFlow hS (hY.of_le (by exact_mod_cast hr)) 0 t p)
  have hψ₀ : ⇑(ψ 0) = id := funext fun q ↦ timeDependentFlow_self Y hS 0 q
  have hb := congrArg (fun F ↦ F (Module.Basis.finTwoProd ℝ)) h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis,
    ContinuousAlternatingMap.smul_apply, hψ₀, fderiv_id, smul_eq_mul] at hb
  rw [Prod.realPlaneDx_wedge_realPlaneDy_finTwoProd,
    Prod.realPlaneDx_wedge_realPlaneDy_finTwoProd] at hb
  simpa [mul_comm] using hb

end TauCeti
