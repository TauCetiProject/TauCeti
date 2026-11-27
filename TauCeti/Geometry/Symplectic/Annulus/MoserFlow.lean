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
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Dynamics.Flow.Variational
import TauCeti.Geometry.Symplectic.Liouville.Plane
import TauCeti.Topology.Algebra.Module.Determinant
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

An isotopy `h_u`, `u ∈ [0, 1]`, has a whole family of densities `1 + g u`, one for each `u`, and its
correction `h_u ∘ ψ_u` must again depend smoothly on `u`. So the construction is carried out for a
family `g`, jointly `C^r` in the parameter and the point. The Moser flows `ψ_u` of the densities
`1 + g u` are then jointly `C^r` in `u` and the point, together with their inverses, and `ψ_u` is
the identity whenever `g u` vanishes identically on the plane, so the correction leaves `h_u`
unchanged when `g u` is chosen to vanish identically, for example at the endpoints of an isotopy
from the identity to an area-preserving map.

The field `X_t` is only defined where `1 + t g ≠ 0`, which contains `[0, 1] × (ℝ × [0, 1])`, and
it is not globally Lipschitz there. So the proof cuts it off, by a bump function equal to one
near `[0, 1]` in the parameter, in the time and in the height coordinate, to a field that is
`C^r`, periodic in `x`, and supported in a band of bounded parameter, time and height. A `C¹` field
with these properties is globally Lipschitz, and its global time-dependent flow
`TauCeti.timeDependentFlow` exists. Its second component vanishes on both boundary lines, because
`X_t` is tangent to them. By uniqueness of solutions of the scalar equation satisfied by the
height, the flow preserves both boundary lines (`TauCeti.timeDependentFlow_snd_eq_of_snd_eq`), and
then, by the intermediate value theorem, the strip (`TauCeti.timeDependentFlow_snd_mem_Icc`). On
the strip the cut-off field is `X_t` for `t ∈ [0, 1]`, so Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField`) applies along every orbit
starting in the strip. Periodicity of the flow follows from uniqueness of solutions as well
(`TauCeti.timeDependentFlow_add_const`). Smoothness in the parameter comes from the flow on
`(ℝ × ℝ) × ℝ` of the field `(X_t, 0)`, which freezes the parameter and is `C^r` in all its
variables; by uniqueness of solutions its orbits are those of the flows of the individual fields
(`TauCeti.timeDependentFlow_freeze`).

## Main results

* `TauCeti.exists_stripMoserFlow_family`: the Moser flows of a family of periodic densities of
  the correct total area exist on the strip, consist of `C^r` diffeomorphisms of the plane
  commuting with the deck translation, depend jointly `C^r` on the parameter, and are the identity
  for the density `1`; for parameters in `[0, 1]` they preserve both boundary lines and the strip,
  and their time-one maps pull `(1 + g u) dx ∧ dy` back to `dx ∧ dy`.
* `TauCeti.exists_stripMoserFlow`: the case of a single density.
* `TauCeti.exists_det_fderiv_comp_stripMoserFlow_eq_one`: a path of maps `h u` of the strip with
  Jacobian determinants `1 + g u` becomes area preserving after composing with the time-one maps of
  the Moser flows, smoothly in `u` and without changing `h u` when `g u` vanishes identically.

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

variable {g : ℝ → ℝ × ℝ → ℝ}

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

/-- For a family of periodic functions `g u` with `1 + g u` positive on the strip for `u ∈ [0, 1]`,
the densities `1 + t g u` stay positive, uniformly in `x`, for the parameter `u`, the time `t` and
the height `y` in a neighbourhood `[-d, 1 + d]` of `[0, 1]`. -/
private theorem exists_pos_forall_one_add_mul_pos (hg : Continuous (uncurry g))
    (hper : ∀ u x y, g u (x + 1, y) = g u (x, y))
    (hpos : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g u (x, y)) :
    ∃ d > 0, ∀ u ∈ Icc (-d) (1 + d), ∀ t ∈ Icc (-d) (1 + d), ∀ y ∈ Icc (-d) (1 + d), ∀ x,
      0 < 1 + t * g u (x, y) := by
  set S : Set (ℝ × ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1))
  have hU : IsOpen {q : ℝ × ℝ × ℝ × ℝ | 0 < 1 + q.2.1 * g q.1 q.2.2} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_snd.fst.mul
      (hg.comp (continuous_fst.prodMk continuous_snd.snd))))
  have hSU : S ⊆ {q : ℝ × ℝ × ℝ × ℝ | 0 < 1 + q.2.1 * g q.1 q.2.2} := fun q hq ↦
    one_add_mul_pos hq.2.1 (hpos _ hq.1 _ _ hq.2.2.2)
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_Icc.prod (isCompact_Icc.prod
    (isCompact_Icc.prod isCompact_Icc))).exists_thickening_subset_open hU hSU
  refine ⟨δ / 2, half_pos hδ, fun u hu t ht y hy x ↦ ?_⟩
  obtain ⟨u₀, hu₀, huu₀⟩ := exists_mem_Icc_dist_le (half_pos hδ).le hu
  obtain ⟨t₀, ht₀, htt₀⟩ := exists_mem_Icc_dist_le (half_pos hδ).le ht
  obtain ⟨y₀, hy₀, hyy₀⟩ := exists_mem_Icc_dist_le (half_pos hδ).le hy
  -- Move `x` into `[0, 1)` by periodicity; the point is then within `δ` of `S`.
  have hfract : g u (Int.fract x, y) = g u (x, y) := by
    have h := Function.Periodic.sub_int_mul_eq (f := fun x ↦ g u (x, y)) (x := x)
      (fun x ↦ hper u x y) ⌊x⌋
    simpa only [mul_one, Int.self_sub_floor] using h
  have hmem : (u, t, Int.fract x, y) ∈ thickening δ S := mem_thickening_iff.2
    ⟨(u₀, t₀, Int.fract x, y₀),
      ⟨hu₀, ht₀, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, hy₀⟩, by
      simp only [Prod.dist_eq, dist_self]
      exact max_lt (huu₀.trans_lt (half_lt_self hδ)) (max_lt (htt₀.trans_lt (half_lt_self hδ))
        (max_lt hδ (hyy₀.trans_lt (half_lt_self hδ))))⟩
  have h : 0 < 1 + t * g u (Int.fract x, y) := hδU hmem
  rwa [hfract] at h

/-! ### The cut-off Moser field -/

/-- The Moser vector field of `g u` cut off by the bump `χ`, centred at `1 / 2`, in the parameter
`u`, the time `t` and the height coordinate. -/
private def cutoffField (g : ℝ → ℝ × ℝ → ℝ) (χ : ContDiffBump (1 / 2 : ℝ)) (u t : ℝ)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  (χ u * χ t * χ p.2) • stripMoserVectorField (g u) t p

/-- The cut-off field vanishes near every point whose parameter, time or height lies outside the
support of the bump. -/
private theorem cutoffField_eventuallyEq_zero (χ : ContDiffBump (1 / 2 : ℝ))
    {q : ℝ × ℝ × (ℝ × ℝ)}
    (hq : ¬(q.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧ q.2.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧
      q.2.2.2 ∈ closedBall (1 / 2 : ℝ) χ.rOut)) :
    (fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2) =ᶠ[𝓝 q] 0 := by
  rw [← χ.tsupport_eq, not_and_or, not_and_or] at hq
  rcases hq with hq | hq | hq
  · filter_upwards [(continuous_fst.tendsto q).eventually (notMem_tsupport_iff_eventuallyEq.1 hq)]
      with q' hq'
    simp [cutoffField, hq']
  · filter_upwards [(continuous_snd.fst.tendsto q).eventually
      (notMem_tsupport_iff_eventuallyEq.1 hq)] with q' hq'
    simp [cutoffField, hq']
  · filter_upwards [(continuous_snd.snd.snd.tendsto q).eventually
      (notMem_tsupport_iff_eventuallyEq.1 hq)] with q' hq'
    simp [cutoffField, hq']

/-- The cut-off field is `C^n` when `g` is jointly `C^n` and `1 + t g u` does not vanish on the
support of the cut-off. -/
private theorem contDiff_cutoffField {n : ℕ∞} (hg : ContDiff ℝ n (uncurry g))
    (χ : ContDiffBump (1 / 2 : ℝ))
    (hχ : ∀ u ∈ closedBall (1 / 2 : ℝ) χ.rOut, ∀ t ∈ closedBall (1 / 2 : ℝ) χ.rOut,
      ∀ y ∈ closedBall (1 / 2 : ℝ) χ.rOut, ∀ x, 0 < 1 + t * g u (x, y)) :
    ContDiff ℝ n fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2 := by
  refine contDiff_iff_contDiffAt.2 fun q ↦ ?_
  by_cases hq : q.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧ q.2.1 ∈ closedBall (1 / 2 : ℝ) χ.rOut ∧
    q.2.2.2 ∈ closedBall (1 / 2 : ℝ) χ.rOut
  · have hne : 1 + q.2.1 * g q.1 q.2.2 ≠ 0 := (hχ _ hq.1 _ hq.2.1 _ hq.2.2 q.2.2.1).ne'
    have hopen : IsOpen {q : ℝ × ℝ × (ℝ × ℝ) | 1 + q.2.1 * g q.1 q.2.2 ≠ 0} :=
      isOpen_ne_fun (continuous_const.add (continuous_snd.fst.mul (hg.continuous.comp
        (continuous_fst.prodMk continuous_snd.snd)))) continuous_const
    exact (((χ.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd.fst)).mul
      (χ.contDiff.comp contDiff_snd.snd.snd)).contDiffAt.smul
      ((contDiffOn_parametric_stripMoserVectorField hg).contDiffAt (hopen.mem_nhds hne))
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoffField_eventuallyEq_zero χ hq)

/-- A `C¹` cut-off field which is periodic in `x` is globally Lipschitz: its derivative is
bounded on one period of its support, which is compact. -/
private theorem exists_lipschitzWith_cutoffField (χ : ContDiffBump (1 / 2 : ℝ))
    (hF : ContDiff ℝ 1 fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2)
    (hper : ∀ u t x y, cutoffField g χ u t (x + 1, y) = cutoffField g χ u t (x, y)) :
    ∃ C, LipschitzWith C fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2 := by
  set F := fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2
  set B := closedBall (1 / 2 : ℝ) χ.rOut
  obtain ⟨C, hC⟩ := ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
    (isCompact_Icc.prod (isCompact_closedBall _ _)))).exists_bound_of_continuousOn
      (s := B ×ˢ (B ×ˢ (Icc (0 : ℝ) 1 ×ˢ B))) (hF.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨C.toNNReal, lipschitzWith_of_nnNorm_fderiv_le (hF.differentiable one_ne_zero)
    fun q ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal']
  by_cases hq : q.1 ∈ B ∧ q.2.1 ∈ B ∧ q.2.2.2 ∈ B
  · -- Translate `q` by an integer in `x` into the compact set `B × B × [0, 1] × B`.
    set w : ℝ × ℝ × (ℝ × ℝ) := (0, 0, ((⌊q.2.2.1⌋ : ℤ) : ℝ), 0)
    have hFw : (fun q' ↦ F (q' + w)) = F := by
      funext ⟨u, t, x, y⟩
      have h := (Function.Periodic.int_mul (f := fun x ↦ cutoffField g χ u t (x, y)) (c := 1)
        (fun x ↦ hper u t x y) ⌊q.2.2.1⌋) x
      simpa [F, w] using h
    have hq' : q - w ∈ B ×ˢ (B ×ˢ (Icc (0 : ℝ) 1 ×ˢ B)) :=
      ⟨by simpa [w] using hq.1, by simpa [w] using hq.2.1, ⟨by simp [w],
        by simpa [w] using (Int.fract_lt_one q.2.2.1).le⟩, by simpa [w] using hq.2.2⟩
    have hd : fderiv ℝ F q = fderiv ℝ F (q - w) := by
      conv_rhs => rw [← hFw]
      rw [fderiv_comp_add_right, sub_add_cancel]
    rw [hd]
    exact (hC _ hq').trans (le_max_left _ _)
  · rw [(cutoffField_eventuallyEq_zero χ hq).fderiv_eq, fderiv_zero]
    simp

/-- The cut-off Moser fields: a family `Y u` of fields on the plane, jointly `C^r` and Lipschitz in
the parameter, the time and the point, periodic in `x`, tangent to the bottom boundary line of the
strip, and zero when `g u` is. For `u ∈ [0, 1]`, `Y u` is moreover tangent to the top boundary line
and equal to the Moser field of `g u` near every point of the strip at the times `t ∈ [0, 1]`. -/
private theorem exists_cutoff_stripMoserVectorField {r : ℕ∞} (hr : 1 ≤ r)
    (hg : ContDiff ℝ r (uncurry g)) (hper : ∀ u x y, g u (x + 1, y) = g u (x, y))
    (hpos : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g u (x, y))
    (harea : ∀ u ∈ Icc (0 : ℝ) 1, ∫ y in (0 : ℝ)..1, stripRowMean (g u) y = 0) :
    ∃ (Y : ℝ → ℝ → ℝ × ℝ → ℝ × ℝ) (K : ℝ≥0),
      LipschitzWith K (fun q : ℝ × ℝ × (ℝ × ℝ) ↦ Y q.1 q.2.1 q.2.2) ∧
      ContDiff ℝ r (fun q : ℝ × ℝ × (ℝ × ℝ) ↦ Y q.1 q.2.1 q.2.2) ∧
      (∀ u t p, Y u t (p + (1, 0)) = Y u t p) ∧ (∀ u t x, (Y u t (x, 0)).2 = 0) ∧
      (∀ u, (∀ p, g u p = 0) → ∀ t p, Y u t p = 0) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (∀ t x, (Y u t (x, 1)).2 = 0) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
          Y u t =ᶠ[𝓝 p] stripMoserVectorField (g u) t := by
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
  have hY : ContDiff ℝ r fun q : ℝ × ℝ × (ℝ × ℝ) ↦ cutoffField g χ q.1 q.2.1 q.2.2 :=
    contDiff_cutoffField hg χ (by rw [hB]; exact hdpos)
  have hYper (u t : ℝ) (p : ℝ × ℝ) : cutoffField g χ u t (p + (1, 0)) = cutoffField g χ u t p := by
    obtain ⟨x, y⟩ := p
    simp only [cutoffField, Prod.mk_add_mk, add_zero,
      stripMoserVectorField_add_one
        (show Continuous (g u) from hg.continuous.comp (continuous_const.prodMk continuous_id))
        (hper u)]
  obtain ⟨C, hC⟩ := exists_lipschitzWith_cutoffField χ (hY.of_le (by exact_mod_cast hr))
    fun u t x y ↦ by simpa using hYper u t (x, y)
  refine ⟨cutoffField g χ, C, hC, hY, hYper, fun u t x ↦ by simp [cutoffField],
    fun u hu t p ↦ ?_, fun u hu ↦ ⟨fun t x ↦ ?_, fun t ht p hp ↦ ?_⟩⟩
  · have h0 : g u = 0 := funext hu
    simp [cutoffField, h0]
  · simp [cutoffField, stripMoserDxCoeff_one_eq_zero_iff.2 (harea u hu)]
  · filter_upwards [(continuous_snd.tendsto p).eventually (isOpen_Ioo.mem_nhds (hIcc hp))]
      with p' hp'
    simp only [cutoffField, hone u (hIcc hu), hone t (hIcc ht), hone p'.2 hp', mul_one, one_smul]

/-! ### The Moser flow -/

/-- The flow of a globally Lipschitz `C^r` field on the plane which is tangent to both boundary
lines of the strip and equals the Moser field of `1 + g` near the strip at the times `t ∈ [0, 1]`
moves the points of the strip along the Moser field, maps the strip bijectively onto itself, and
its time-one map pulls `(1 + g) dx ∧ dy` back to `dx ∧ dy` on the strip. -/
private theorem timeDependentFlow_of_eventuallyEq_stripMoserVectorField {r : ℕ∞} (hr : 1 ≤ r)
    {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ r g) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g (x, y))
    {Y : ℝ → ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0} (hS : LipschitzWith K (timeDependentSuspension Y))
    (hY : ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ Y q.1 q.2) (h₀ : ∀ t x, (Y t (x, 0)).2 = 0)
    (h₁ : ∀ t x, (Y t (x, 1)).2 = 0)
    (hYX : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
      Y t =ᶠ[𝓝 p] stripMoserVectorField g t) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ timeDependentFlow Y hS 0 s p)
        (stripMoserVectorField g t (timeDependentFlow Y hS 0 t p)) t) ∧
      (∀ t, BijOn (timeDependentFlow Y hS 0 t) (univ ×ˢ Icc (0 : ℝ) 1)
        (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
        (1 + g (timeDependentFlow Y hS 0 1 p)) * (fderiv ℝ (timeDependentFlow Y hS 0 1) p).det =
          1 := by
  have hstrip (s t : ℝ) : MapsTo (timeDependentFlow Y hS s t) (univ ×ˢ Icc (0 : ℝ) 1)
      (univ ×ˢ Icc (0 : ℝ) 1) := fun p hp ↦
    ⟨trivial, timeDependentFlow_snd_mem_Icc hS h₀ h₁ s t hp.2⟩
  have horbit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ timeDependentFlow Y hS 0 s p)
        (stripMoserVectorField g t (timeDependentFlow Y hS 0 t p)) t := by
    rw [← (hYX t ht _ (hstrip 0 t hp).2).eq_of_nhds]
    exact hasDerivAt_timeDependentFlow Y hS 0 t p
  refine ⟨horbit, fun t ↦ InvOn.bijOn ⟨fun p _ ↦ leftInverse_timeDependentFlow Y hS 0 t p,
      fun p _ ↦ rightInverse_timeDependentFlow Y hS 0 t p⟩ (hstrip 0 t) (hstrip t 0),
    fun p hp ↦ ?_⟩
  -- Moser's identity along the orbit of `p`, evaluated on the standard basis.
  have h := compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField
    (hg.of_le (by exact_mod_cast hr)) (ψ := timeDependentFlow Y hS 0) (x := p)
    (fun t ht ↦ (one_add_mul_pos ht (hpos _ _ (hstrip 0 t hp).2)).ne')
    (fun t ht ↦ horbit t ht p hp)
    (fun t ht ↦ by
      rw [← (hYX t ht _ (hstrip 0 t hp).2).fderiv_eq]
      exact hasDerivAt_fderiv_timeDependentFlow hS (hY.of_le (by exact_mod_cast hr)) 0 t p)
  have hψ₀ : timeDependentFlow Y hS 0 0 = id := funext fun q ↦ timeDependentFlow_self Y hS 0 q
  have hb := congrArg (fun F ↦ F (Module.Basis.finTwoProd ℝ)) h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis,
    ContinuousAlternatingMap.smul_apply, hψ₀, fderiv_id, smul_eq_mul] at hb
  rw [Prod.realPlaneDx_wedge_realPlaneDy_finTwoProd,
    Prod.realPlaneDx_wedge_realPlaneDy_finTwoProd] at hb
  simpa [mul_comm] using hb

/-- **The Moser flows of a family of densities on the annulus strip.** Let `1 + g u` be a family
of densities on the plane, jointly `C^r` in the parameter `u` and the point (`r ≥ 1`),
`1`-periodic in `x`, and for `u ∈ [0, 1]` positive on the strip `ℝ × [0, 1]` with
`∫₀¹ ∫₀¹ g u (x, y) dx dy = 0`, so that `(1 + g u) dx ∧ dy` gives the annulus the same area as
`dx ∧ dy`. Then there is a family `ψ u t` of `C^r` diffeomorphisms of the plane such that

* for each time `t`, `ψ u t p` and its inverse are jointly `C^r` in the parameter `u` and the
  point `p`;
* `ψ u 0 = id`, and `ψ u t = id` for every `t` whenever `g u = 0`;
* each `ψ u t` commutes with the deck translation `(x, y) ↦ (x + 1, y)` and maps the boundary line
  `y = 0` into itself;
* for `u ∈ [0, 1]`: for `t ∈ [0, 1]` the orbit of every point of the strip solves
  `∂ₜ ψ u t = X_t ∘ ψ u t` for the Moser vector field `X_t` of `g u`
  (`TauCeti.stripMoserVectorField`); each `ψ u t` maps the boundary line `y = 1` into itself and
  the strip bijectively onto itself; and `ψ u 1` pulls `(1 + g u) dx ∧ dy` back to `dx ∧ dy` on
  the strip: `(1 + g u (ψ u 1 p)) det D(ψ u 1)(p) = 1`. -/
theorem exists_stripMoserFlow_family {r : ℕ∞} (hr : 1 ≤ r) (hg : ContDiff ℝ r (uncurry g))
    (hper : ∀ u x y, g u (x + 1, y) = g u (x, y))
    (hpos : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g u (x, y))
    (harea : ∀ u ∈ Icc (0 : ℝ) 1, ∫ y in (0 : ℝ)..1, stripRowMean (g u) y = 0) :
    ∃ ψ : ℝ → ℝ → (ℝ × ℝ) ≃ₘ^r⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
      (∀ t, ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ ψ q.1 t q.2) ∧
      (∀ t, ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ (ψ q.1 t).symm q.2) ∧
      (∀ u p, ψ u 0 p = p) ∧ (∀ u, (∀ p, g u p = 0) → ∀ t p, ψ u t p = p) ∧
      (∀ u t p, ψ u t (p + (1, 0)) = ψ u t p + (1, 0)) ∧ (∀ u t x, (ψ u t (x, 0)).2 = 0) ∧
      ∀ u ∈ Icc (0 : ℝ) 1,
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
          HasDerivAt (fun s ↦ ψ u s p) (stripMoserVectorField (g u) t (ψ u t p)) t) ∧
        (∀ t x, (ψ u t (x, 1)).2 = 1) ∧
        (∀ t, BijOn (ψ u t) (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1)) ∧
        ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (1 + g u (ψ u 1 p)) * (fderiv ℝ (ψ u 1) p).det = 1 := by
  obtain ⟨Y, K, hYK, hY, hYper, h₀, hY0, hYu⟩ :=
    exists_cutoff_stripMoserVectorField hr hg hper hpos harea
  -- For each parameter `u`, the flow of the cut-off field `Y u` on the plane.
  have hS := lipschitzWith_timeDependentSuspension_apply hYK
  have hYs (u : ℝ) : ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ Y u q.1 q.2 :=
    hY.comp ((contDiff_const (c := u)).prodMk contDiff_id)
  let ψ (u t : ℝ) : (ℝ × ℝ) ≃ₘ^r⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ) :=
    ⟨⟨timeDependentFlow (Y u) (hS u) 0 t, timeDependentFlow (Y u) (hS u) t 0,
      leftInverse_timeDependentFlow (Y u) (hS u) 0 t,
      rightInverse_timeDependentFlow (Y u) (hS u) 0 t⟩,
      (contDiff_timeDependentFlow_apply (hS u) (hYs u) 0 t).contMDiff,
      (contDiff_timeDependentFlow_apply (hS u) (hYs u) t 0).contMDiff⟩
  have hψ (u t : ℝ) : ⇑(ψ u t) = timeDependentFlow (Y u) (hS u) 0 t := rfl
  have hψsymm (u t : ℝ) : ⇑(ψ u t).symm = timeDependentFlow (Y u) (hS u) t 0 := rfl
  -- Joint smoothness in the parameter: these are the flows of `(Y u t p, 0)` on `(ℝ × ℝ) × ℝ`.
  have hjoint (s t : ℝ) :
      ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ timeDependentFlow (Y q.1) (hS q.1) s t q.2 := by
    have hVs : ContDiff ℝ r fun q : ℝ × ((ℝ × ℝ) × ℝ) ↦ (Y q.2.2 q.1 q.2.1, (0 : ℝ)) :=
      (hY.comp (contDiff_snd.snd.prodMk (contDiff_fst.prodMk contDiff_snd.fst))).prodMk
        contDiff_const
    have hV := lipschitzWith_timeDependentSuspension_freeze hYK
    have heq : (fun q : ℝ × (ℝ × ℝ) ↦ timeDependentFlow (Y q.1) (hS q.1) s t q.2) = fun q ↦
        (timeDependentFlow (fun t (q' : (ℝ × ℝ) × ℝ) ↦ (Y q'.2 t q'.1, (0 : ℝ))) hV s t
          (q.2, q.1)).1 :=
      funext fun q ↦ by rw [timeDependentFlow_freeze hYK]
    have hΦ := contDiff_timeDependentFlow_apply hV hVs s t
    have hswap : ContDiff ℝ r fun q : ℝ × (ℝ × ℝ) ↦ (q.2, q.1) := contDiff_snd.prodMk contDiff_fst
    rw [heq]
    exact contDiff_fst.comp (hΦ.comp hswap)
  refine ⟨ψ, fun t ↦ ?_, fun t ↦ ?_, fun u p ↦ timeDependentFlow_self (Y u) (hS u) 0 p,
    fun u hu t p ↦ ?_, fun u t p ↦ timeDependentFlow_add_const (Y u) (hS u) (hYper u) 0 t p,
    fun u t x ↦ timeDependentFlow_snd_eq_of_snd_eq (hS u) (h₀ u) 0 t rfl, fun u hu ↦ ?_⟩
  · simpa only [hψ] using hjoint 0 t
  · simpa only [hψsymm] using hjoint t 0
  · -- A zero field has constant orbits.
    have h := eq_timeDependentFlow (Y u) (hS u) (y := fun _ ↦ p)
      (fun τ ↦ by simpa only [hY0 u hu τ p] using hasDerivAt_const τ p) 0 t
    exact h.symm
  obtain ⟨h₁, hYX⟩ := hYu u hu
  obtain ⟨horbit, hbij, hdet⟩ := timeDependentFlow_of_eventuallyEq_stripMoserVectorField hr
    (hg.comp ((contDiff_const (c := u)).prodMk contDiff_id)) (hpos u hu) (hS u) (hYs u) (h₀ u) h₁
    hYX
  exact ⟨horbit, fun t x ↦ timeDependentFlow_snd_eq_of_snd_eq (hS u) h₁ 0 t rfl, hbij, hdet⟩

/-- **The Moser flow on the annulus strip.** Let `1 + g` be a `C^r` density (`r ≥ 1`),
`1`-periodic in `x`, positive on the strip `ℝ × [0, 1]`, with `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`, so that
`(1 + g) dx ∧ dy` gives the annulus the same area as `dx ∧ dy`. Then there is a family `ψ_t` of
`C^r` diffeomorphisms of the plane such that

* `ψ₀ = id`, and for `t ∈ [0, 1]` the orbit of every point of the strip solves
  `∂ₜ ψ_t = X_t ∘ ψ_t` for the Moser vector field `X_t` (`TauCeti.stripMoserVectorField`);
* each `ψ_t` commutes with the deck translation `(x, y) ↦ (x + 1, y)`, maps each boundary line
  `y = 0` and `y = 1` into itself, and maps the strip bijectively onto itself;
* `ψ₁` pulls `(1 + g) dx ∧ dy` back to `dx ∧ dy` on the strip:
  `(1 + g (ψ₁ p)) det Dψ₁(p) = 1`.

This is the constant family of `TauCeti.exists_stripMoserFlow_family`. -/
theorem exists_stripMoserFlow {r : ℕ∞} (hr : 1 ≤ r) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ r g)
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
  obtain ⟨ψ, -, -, h₀, -, hdeck, hbot, hu⟩ := exists_stripMoserFlow_family hr
    (g := fun _ ↦ g) (hg.comp contDiff_snd) (fun _ ↦ hper) (fun _ _ ↦ hpos) (fun _ _ ↦ harea)
  obtain ⟨horbit, htop, hbij, hdet⟩ := hu 0 ⟨le_rfl, zero_le_one⟩
  exact ⟨ψ 0, h₀ 0, horbit, hdeck 0, hbot 0, htop, hbij, hdet⟩

/-! ### Area-preserving correction of an isotopy -/

/-- **Area-preserving correction of a path of maps of the strip.** Let `h u`, `u ∈ [0, 1]`, be
maps of the plane with Jacobian determinants `det D(h u) = 1 + g u` on the strip `ℝ × [0, 1]`,
where the densities `1 + g u` satisfy the hypotheses of `TauCeti.exists_stripMoserFlow_family`.
Then there are `C^r` diffeomorphisms `ψ u` of the plane, jointly `C^r` in `u` and the point
together with their inverses, such that every `h u ∘ ψ u`, `u ∈ [0, 1]`, preserves `dx ∧ dy` on
the strip. Each `ψ u` commutes with the deck translation `(x, y) ↦ (x + 1, y)`; for `u ∈ [0, 1]`
it maps each of the boundary lines `y = 0` and `y = 1` into itself and the strip bijectively onto
itself; and `ψ u = id` whenever `g u` vanishes identically on the plane (not only on the strip),
so the correction leaves `h u` unchanged when `g u` is chosen to vanish identically, for example at
the endpoints of an isotopy from `id` to an area-preserving map. -/
theorem exists_det_fderiv_comp_stripMoserFlow_eq_one {r : ℕ∞} (hr : 1 ≤ r)
    (hg : ContDiff ℝ r (uncurry g)) (hper : ∀ u x y, g u (x + 1, y) = g u (x, y))
    (hpos : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + g u (x, y))
    (harea : ∀ u ∈ Icc (0 : ℝ) 1, ∫ y in (0 : ℝ)..1, stripRowMean (g u) y = 0)
    {h : ℝ → ℝ × ℝ → ℝ × ℝ}
    (hdet : ∀ u ∈ Icc (0 : ℝ) 1, ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
      (fderiv ℝ (h u) p).det = 1 + g u p) :
    ∃ ψ : ℝ → (ℝ × ℝ) ≃ₘ^r⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
      ContDiff ℝ r (fun q : ℝ × (ℝ × ℝ) ↦ ψ q.1 q.2) ∧
      ContDiff ℝ r (fun q : ℝ × (ℝ × ℝ) ↦ (ψ q.1).symm q.2) ∧
      (∀ u, (∀ p, g u p = 0) → ⇑(ψ u) = id) ∧ (∀ u p, ψ u (p + (1, 0)) = ψ u p + (1, 0)) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (∀ x, (ψ u (x, 0)).2 = 0) ∧ (∀ x, (ψ u (x, 1)).2 = 1) ∧
        BijOn (ψ u) (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1) ∧
        ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ (h u ∘ ψ u) p).det = 1 := by
  obtain ⟨ψ, hψ, hψsymm, -, hid, hdeck, hbot, hfam⟩ :=
    exists_stripMoserFlow_family hr hg hper hpos harea
  refine ⟨fun u ↦ ψ u 1, hψ 1, hψsymm 1, fun u hu ↦ funext (hid u hu 1), fun u ↦ hdeck u 1,
    fun u hu ↦ ?_⟩
  obtain ⟨-, htop, hbij, hdet₁⟩ := hfam u hu
  refine ⟨hbot u 1, htop 1, hbij 1, fun p hp ↦ ?_⟩
  -- The chain rule and the multiplicativity of the determinant.
  have hmem := (hbij 1).mapsTo hp
  -- `h u` is differentiable on the strip, where its Jacobian determinant `1 + g u` is nonzero.
  have hh : DifferentiableAt ℝ (h u) (ψ u 1 p) := differentiableAt_of_det_fderiv_ne_zero <| by
    rw [hdet u hu _ hmem]
    exact (hpos u hu (ψ u 1 p).1 (ψ u 1 p).2 hmem.2).ne'
  have hψd : DifferentiableAt ℝ (ψ u 1) p :=
    ((ψ u 1).contMDiff.contDiff.of_le (by exact_mod_cast hr)).differentiable one_ne_zero p
  have hcomp : (fderiv ℝ (h u ∘ ψ u 1) p).det =
      (fderiv ℝ (h u) (ψ u 1 p)).det * (fderiv ℝ (ψ u 1) p).det := by
    rw [fderiv_comp p hh hψd, ContinuousLinearMap.det_comp]
  rw [hcomp, hdet u hu _ hmem, hdet₁ p hp]

end TauCeti
