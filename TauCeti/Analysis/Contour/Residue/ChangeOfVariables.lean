/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.StarConvex
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# Change of variables for residues

If `φ` is analytic at `p` with `φ'(p) ≠ 0` (a local biholomorphism at `p`), then for every `f`
the residue of the pulled-back function `(f ∘ φ) · φ'` at `p` equals the residue of `f` at `φ p`:
`Res_p ((f ∘ φ) · φ') = Res_{φ p} f`. In the language of differentials, the residue of the
`1`-form `f(w) dw` at an isolated singularity does not depend on the holomorphic coordinate `w` used
to compute it, which is what makes the residue of a `1`-form on a Riemann surface well defined.

More generally, if `φ` is merely analytic at `p`, with `φ − φ p` vanishing to some order `m`, and
`f` is differentiable on a punctured neighbourhood of `φ p` (an isolated singularity of any kind:
removable, a pole or essential), then `Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`. This is the local
form of the statement that pullback along a holomorphic map multiplies residues by the local
multiplicity. The proof is by contour integration: `φ` maps a small circle about `p` to a closed
curve winding `m` times about `φ p`, its winding number being the residue `m` of the logarithmic
derivative `φ' / (φ − φ p)`, and the residue theorem along that curve gives `m · Res_{φ p} f`.

## Main results

* `TauCeti.Contour.residue_deriv_eq_zero`: `Res_p g' = 0` for `g` differentiable on a punctured
  neighbourhood of `p`: exact differentials have no residue.
* `TauCeti.Contour.residue_deriv_div_sub_pow_of_analyticOrderAt_eq`: if `φ − φ p` vanishes to
  order `m` at `p`, then `Res_p (φ' / (φ − φ p) ^ (k + 1))` is `m` for `k = 0` and `0` otherwise.
* `TauCeti.Contour.residue_deriv_div_sub_pow`: `Res_p (φ' / (φ − φ p) ^ (k + 1))` is `1` for
  `k = 0` and `0` otherwise, the pull-back of `TauCeti.Contour.residue_const_div_sub_pow`.
* `TauCeti.Contour.residue_comp_mul_deriv_eq_analyticOrderNatAt_mul`: the branched
  change-of-variables formula `Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`.
* `TauCeti.Contour.residue_comp_mul_deriv`: the change-of-variables formula
  `Res_p ((f ∘ φ) · φ') = Res_{φ p} f`.
* `TauCeti.Contour.residue_comp_add_const`, `TauCeti.Contour.residue_comp_const_mul`: the
  translation and dilation special cases.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §9, where the residue of a
  meromorphic differential is defined chart by chart and shown to be independent of the chart.
-/

public section

open Filter Topology Metric Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Exact differentials have no residue.** If `g` is differentiable on a punctured neighbourhood
of `z₀` (for instance meromorphic at `z₀`), then the residue of its derivative `g'` at `z₀`
vanishes: around a small circle, `∮ g' = 0`. -/
@[simp]
theorem residue_deriv_eq_zero {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z) : residue (deriv g) z₀ = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hg)
  have hV : IsOpen (ball z₀ ε \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  have hgV : DifferentiableOn ℂ g (ball z₀ ε \ {z₀}) :=
    fun z hz ↦ (hball hz.1 hz.2).differentiableWithinAt
  have hsub : closedBall z₀ (ε / 2) \ {z₀} ⊆ ball z₀ ε \ {z₀} :=
    fun z hz ↦ ⟨(mem_closedBall.1 hz.1).trans_lt (half_lt_self hε), hz.2⟩
  rw [residue_eq_circleIntegral (half_pos hε) ((hgV.deriv hV).mono hsub),
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt (half_pos hε).le fun z hz ↦
      (hgV.differentiableAt (hV.mem_nhds (hsub ⟨sphere_subset_closedBall hz,
        ne_of_mem_sphere hz (half_pos hε).ne'⟩))).hasDerivAt.hasDerivWithinAt, smul_zero]

/-- **Residue of a pulled-back Laurent monomial along a branched map.** If `φ` is analytic at `p`
and `φ − φ p` vanishes to finite order `m` at `p`, then `φ' / (φ − φ p) ^ (k + 1)`, the pull-back
along `φ` of the form `dw / (w − φ p) ^ (k + 1)`, has residue `m` at `p` for `k = 0` and `0` for
`k ≥ 1`. In the local normal form `φ = φ p + z ^ m` the `k = 0` form is `m · dz / z`. -/
theorem residue_deriv_div_sub_pow_of_analyticOrderAt_eq {φ : ℂ → ℂ} {p : ℂ} {m : ℕ}
    (hφ : AnalyticAt ℂ φ p) (hm : analyticOrderAt (fun z ↦ φ z - φ p) p = m) (k : ℕ) :
    residue (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1)) p = if k = 0 then (m : ℂ) else 0 := by
  have hsub : AnalyticAt ℂ (fun z ↦ φ z - φ p) p := hφ.sub analyticAt_const
  rcases k with _ | k
  · -- `φ' / (φ − φ p)` is the logarithmic derivative of `φ − φ p`, which vanishes to order `m`.
    have hlog : (fun z ↦ deriv φ z / (φ z - φ p) ^ (0 + 1)) = logDeriv (fun z ↦ φ z - φ p) := by
      ext z
      simp [logDeriv_apply]
    have hord : meromorphicOrderAt (fun z ↦ φ z - φ p) p = ((m : ℤ) : WithTop ℤ) := by
      rw [hsub.meromorphicOrderAt_eq, hm]
      simp
    rw [hlog, residue_logDeriv_eq_meromorphicOrderAt hsub.meromorphicAt hord]
    simp
  · -- `φ − φ p` has isolated zeros, and off them `φ' / (φ − φ p) ^ (k + 2)` is the derivative of
    -- `−(k + 1)⁻¹ · ((φ − φ p) ^ (k + 1))⁻¹`.
    have hnc : ¬ EventuallyConst φ (𝓝 p) := by
      rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hm]
      exact ENat.natCast_ne_top m
    have hne : ∀ᶠ z in 𝓝[≠] p, φ z - φ p ≠ 0 :=
      (Tendsto.eventually (hφ.map_nhdsNE hnc) self_mem_nhdsWithin).mono fun _ hz ↦ sub_ne_zero.2 hz
    set G : ℂ → ℂ := fun z ↦ -((k : ℂ) + 1)⁻¹ * ((φ z - φ p) ^ (k + 1))⁻¹
    have hG : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ G z := by
      filter_upwards [hne, hφ.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz hφz
      exact (differentiableAt_const _).mul
        (((hφz.differentiableAt.sub_const _).pow _).inv (pow_ne_zero _ hz))
    have heq : (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1 + 1)) =ᶠ[𝓝[≠] p] deriv G := by
      filter_upwards [hne, nhdsWithin_le_nhds hφ.eventually_analyticAt] with z hsub hφz
      rw [(((hφz.differentiableAt.hasDerivAt.sub_const (φ p)).fun_pow (k + 1)).fun_inv
        (pow_ne_zero _ hsub)).const_mul _ |>.deriv]
      simp only [Nat.add_sub_cancel]
      field_simp
      push_cast
      ring
    rw [residue_congr_nhdsNE heq, residue_deriv_eq_zero hG]
    simp

/-- **Residue of a pulled-back Laurent monomial.** If `φ` is analytic at `p` with `φ'(p) ≠ 0`,
then `φ' / (φ − φ p) ^ (k + 1)`, the pull-back along `φ` of the form `dw / (w − φ p) ^ (k + 1)`,
has residue `1` at `p` for `k = 0` and `0` for `k ≥ 1`. For `φ = id` this is
`TauCeti.Contour.residue_const_div_sub_pow` with coefficient `1`. -/
@[simp]
theorem residue_deriv_div_sub_pow {φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hφ' : deriv φ p ≠ 0) (k : ℕ) :
    residue (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1)) p = if k = 0 then 1 else 0 := by
  simpa using residue_deriv_div_sub_pow_of_analyticOrderAt_eq hφ (m := 1)
    (by simpa using hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ') k

/-- The branched change of variables on a disc. Let `f` be differentiable on the punctured disc of
radius `R` about `φ p`, and let `φ`, with `φ − φ p` vanishing to order `m` at `p`, be analytic at
every point of a punctured closed disc of radius `r` about `p`, map it into the disc of radius `R`
and miss `φ p` there. Then `Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`: the image `Γ = φ ∘ C(p, r)` of
the circle of radius `r` winds `m` times about `φ p`, and the residue theorem along `Γ` gives the
formula. -/
private theorem residue_comp_mul_deriv_eq_mul_of_closedBall {f φ : ℂ → ℂ} {p : ℂ} {m : ℕ} {R r : ℝ}
    (hφ : AnalyticAt ℂ φ p) (hm : analyticOrderAt (fun z ↦ φ z - φ p) p = m)
    (hfR : ∀ ⦃w⦄, dist w (φ p) < R → w ∈ ({φ p}ᶜ : Set ℂ) → DifferentiableAt ℂ f w) (hr : 0 < r)
    (hP : ∀ z ∈ closedBall p r \ {p},
      (AnalyticAt ℂ φ z ∧ φ z ∈ ball (φ p) R) ∧ φ z ∈ ({φ p}ᶜ : Set ℂ)) :
    residue (fun z ↦ f (φ z) * deriv φ z) p = m * residue f (φ p) := by
  have hsph : ∀ z ∈ sphere p r, z ∈ closedBall p r \ {p} :=
    fun z hz ↦ ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hr.ne'⟩
  have hcirc : ∀ θ, circleMap p r θ ∈ closedBall p r \ {p} :=
    fun θ ↦ hsph _ (circleMap_mem_sphere p hr.le θ)
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp (hP _ (hcirc 0)).1.2)
  have hφd : ∀ z ∈ sphere p r, DifferentiableAt ℂ φ z :=
    fun z hz ↦ (hP z (hsph z hz)).1.1.differentiableAt
  -- Pulling a circle integral back along `φ` gives the contour integral along `φ ∘ C(p, r)`.
  have hpull (F : ℂ → ℂ) : ∮ z in C(p, r), F (φ z) * deriv φ z =
      ∫ θ in 0..2 * π, deriv (φ ∘ circleMap p r) θ • F ((φ ∘ circleMap p r) θ) := by
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    have h : HasDerivAt (φ ∘ circleMap p r)
        (deriv φ (circleMap p r θ) * (circleMap 0 r θ * Complex.I)) θ :=
      (hφd _ (circleMap_mem_sphere p hr.le θ)).hasDerivAt.comp θ (hasDerivAt_circleMap p r θ)
    simp only [h.deriv, deriv_circleMap, Function.comp_apply, smul_eq_mul]
    ring
  -- The image `Γ = φ ∘ C(p, r)` is a closed absolutely continuous curve in the punctured disc.
  have hΓ : AbsolutelyContinuousOnInterval (φ ∘ circleMap p r) 0 (2 * π) :=
    (absolutelyContinuousOnInterval_circleMap p r 0 (2 * π)).comp_of_contDiffAt <| by
      rintro _ ⟨θ, -, rfl⟩
      exact ((hP _ (hcirc θ)).1.1.contDiffAt (n := 1)).restrict_scalars ℝ
  have hΓU : ∀ θ ∈ uIcc 0 (2 * π), (φ ∘ circleMap p r) θ ∈ ball (φ p) R :=
    fun θ _ ↦ (hP _ (hcirc θ)).1.2
  have hclosed : (φ ∘ circleMap p r) 0 = (φ ∘ circleMap p r) (2 * π) :=
    congrArg φ (periodic_circleMap p r).eq.symm
  -- The residue theorem along `Γ`, about its only singularity `φ p`.
  have hres := classicalResidueTheorem_nullHomologous (S := {φ p}) (f := f) isOpen_ball
    (fun w hw ↦ (hfR hw.1 (by simpa using hw.2)).differentiableWithinAt) hΓ hΓU hclosed
    (fun θ _ h ↦ (hP _ (hcirc θ)).2 (by simpa using h))
    (hΓ.isNullHomologous_of_starConvex ((convex_ball _ _).starConvex (mem_ball_self hR))
      hclosed hΓU)
  -- `Γ` winds `m` times about `φ p`: its winding number is `Res_p (φ' / (φ − φ p)) = m`.
  have hwind : windingNumber (φ ∘ circleMap p r) 0 (2 * π) (φ p) = m := by
    have hk := residue_eq_circleIntegral (f := fun z ↦ deriv φ z / (φ z - φ p) ^ (0 + 1)) hr
      fun z hz ↦
      ((hP z hz).1.1.deriv.differentiableAt.div (((hP z hz).1.1.differentiableAt.sub_const
        (φ p)).pow (0 + 1)) (pow_ne_zero _ (sub_ne_zero.2 (hP z hz).2))).differentiableWithinAt
    rw [residue_deriv_div_sub_pow_of_analyticOrderAt_eq hφ hm 0, ite_eq_left rfl] at hk
    simp only [zero_add, pow_one, div_eq_inv_mul] at hk
    rw [hΓ.windingNumber_eq_integral fun ⟨θ, _, h⟩ ↦ (hP _ (hcirc θ)).2 h, hk,
      hpull fun w ↦ (w - φ p)⁻¹, smul_eq_mul]
    simp only [smul_eq_mul, mul_comm]
  rw [residue_eq_circleIntegral (f := fun z ↦ f (φ z) * deriv φ z) hr fun z hz ↦
      (((hfR (hP z hz).1.2 (hP z hz).2).comp z (hP z hz).1.1.differentiableAt).mul
        (hP z hz).1.1.deriv.differentiableAt).differentiableWithinAt,
    hpull f, hres, Finset.sum_singleton, hwind,
    inv_smul_smul₀ Complex.two_pi_I_ne_zero, smul_eq_mul]

/-- **Change of variables for residues along a branched map.** If `φ` is analytic at `p` and `f` is
differentiable on a punctured neighbourhood of `φ p` (an isolated singularity of any kind), then
the residue of `(f ∘ φ) · φ'` at `p` is the residue of `f` at `φ p` multiplied by the order `m` of
vanishing of `φ − φ p` at `p`:
`Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`.
Near a point where `φ` is not constant, `φ` maps a small circle about `p` to a closed curve winding
`m` times about `φ p`, and the residue theorem along that curve gives `m · Res_{φ p} f`. If `φ` is
constant near `p`, then `analyticOrderNatAt` takes the value `0`, and so does the residue, since
`φ' = 0` near `p`. -/
theorem residue_comp_mul_deriv_eq_analyticOrderNatAt_mul {f φ : ℂ → ℂ} {p : ℂ}
    (hf : ∀ᶠ w in 𝓝[≠] φ p, DifferentiableAt ℂ f w) (hφ : AnalyticAt ℂ φ p) :
    residue (fun z ↦ f (φ z) * deriv φ z) p =
      analyticOrderNatAt (fun z ↦ φ z - φ p) p * residue f (φ p) := by
  generalize hm' : analyticOrderAt (fun z ↦ φ z - φ p) p = r
  cases r with
  | top =>
    -- `φ` is constant near `p`, so `φ'` and the pulled-back function vanish near `p`.
    have hc : φ =ᶠ[𝓝 p] fun _ ↦ φ p := by
      filter_upwards [analyticOrderAt_eq_top.1 hm'] with z hz
      exact sub_eq_zero.1 hz
    have hzero : (fun z ↦ f (φ z) * deriv φ z) =ᶠ[𝓝[≠] p] fun _ ↦ (0 : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds hc.deriv] with z hz
      simp [hz]
    rw [residue_congr_nhdsNE hzero, residue_eq_zero_of_analyticAt analyticAt_const,
      analyticOrderNatAt, hm']
    simp
  | coe m =>
  have hnc : ¬ EventuallyConst φ (𝓝 p) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hm']
    exact ENat.natCast_ne_top m
  -- `f` is differentiable on a punctured disc of radius `R` about `φ p`; on a punctured closed
  -- disc of radius `ρ / 2` about `p`, `φ` is analytic, maps into that disc and misses `φ p`.
  obtain ⟨R, hR, hfR⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hf)
  obtain ⟨ρ, hρ, hρP⟩ := Metric.mem_nhdsWithin_iff.1 (((hφ.eventually_analyticAt.and
    (hφ.continuousAt.eventually_mem (ball_mem_nhds _ hR))).filter_mono nhdsWithin_le_nhds).and
    (Tendsto.eventually (hφ.map_nhdsNE hnc) self_mem_nhdsWithin))
  rw [analyticOrderNatAt, hm', ENat.toNat_natCast]
  exact residue_comp_mul_deriv_eq_mul_of_closedBall hφ hm' hfR (half_pos hρ) fun z hz ↦
    hρP ⟨(mem_closedBall.1 hz.1).trans_lt (half_lt_self hρ), hz.2⟩

/-- **Change of variables for residues.** If `φ` is analytic at `p` with `φ'(p) ≠ 0`, then for
every `f : ℂ → ℂ` the residue of `(f ∘ φ) · φ'` at `p` is the residue of `f` at `φ p`. Equivalently,
the residue of the `1`-form `f(w) dw` at an isolated singularity is independent of the local
coordinate.

No hypothesis on `f` is needed: since `φ` is a local biholomorphism, `(f ∘ φ) · φ'` is
differentiable on a punctured neighbourhood of `p` exactly when `f` is on one of `φ p`, and
otherwise both residues take the junk value `0`. -/
theorem residue_comp_mul_deriv {f φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hφ' : deriv φ p ≠ 0) :
    residue (fun z ↦ f (φ z) * deriv φ z) p = residue f (φ p) := by
  by_cases hf : ∀ᶠ w in 𝓝[≠] φ p, DifferentiableAt ℂ f w
  · rw [residue_comp_mul_deriv_eq_analyticOrderNatAt_mul hf hφ, analyticOrderNatAt,
      hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ']
    simp
  · rw [residue_of_not_eventually_differentiableAt hf]
    refine residue_of_not_eventually_differentiableAt fun hg ↦ hf ?_
    -- Near `φ p`, `f` is the pull-back composed with the local inverse `ψ` of `φ`, divided by
    -- `φ' ∘ ψ`, so it is differentiable on a punctured neighbourhood of `φ p` too.
    set ψ := hφ.hasStrictDerivAt.localInverse _ _ _ hφ'
    have hψ : AnalyticAt ℂ ψ (φ p) := hφ.analyticAt_localInverse hφ'
    have hψp : ψ (φ p) = p := HasStrictFDerivAt.localInverse_apply_image ..
    have hright : ∀ᶠ w in 𝓝 (φ p), φ (ψ w) = w := HasStrictDerivAt.eventually_right_inverse ..
    have hψt : Tendsto ψ (𝓝 (φ p)) (𝓝 p) := by
      have h := hψ.continuousAt.tendsto
      rwa [hψp] at h
    -- `ψ` maps a punctured neighbourhood of `φ p` into one of `p`.
    have hψt' : Tendsto ψ (𝓝[≠] φ p) (𝓝[≠] p) := tendsto_nhdsWithin_iff.2
      ⟨hψt.mono_left nhdsWithin_le_nhds, by
        filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw₀ h
        exact hw₀ (by rw [mem_singleton_iff, ← hw, mem_singleton_iff.1 h])⟩
    -- Near `p`, `φ` is analytic with nonvanishing derivative.
    have hnear : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ φ z ∧ deriv φ z ≠ 0 :=
      hφ.eventually_analyticAt.and (hφ.deriv.continuousAt.eventually_ne hφ')
    filter_upwards [hψt'.eventually hg, (hψ.eventually_analyticAt.and (hright.eventually_nhds.and
      (hψt.eventually hnear).eventually_nhds)).filter_mono nhdsWithin_le_nhds]
      with w hgw ⟨hψw, hrw, hnw⟩
    -- Near `w`, `f` is the pull-back along `ψ` divided by `φ' ∘ ψ`.
    have heq : f =ᶠ[𝓝 w] fun v ↦ f (φ (ψ v)) * deriv φ (ψ v) / deriv φ (ψ v) := by
      filter_upwards [hrw, hnw] with v hv hv'
      rw [mul_div_cancel_right₀ _ hv'.2, hv]
    exact ((hgw.comp w hψw.differentiableAt).div (hnw.self_of_nhds.1.deriv.differentiableAt.comp w
      hψw.differentiableAt) hnw.self_of_nhds.2).congr_of_eventuallyEq heq

/-- **Translation invariance of the residue.** The residue of `z ↦ f (z + c)` at `p` is the residue
of `f` at `p + c`. -/
@[simp]
theorem residue_comp_add_const (f : ℂ → ℂ) (c p : ℂ) :
    residue (fun z ↦ f (z + c)) p = residue f (p + c) := by
  simpa using residue_comp_mul_deriv (f := f) (φ := fun z ↦ z + c) (p := p) (by fun_prop)
    (by simp)

/-- **Scaling of the residue under dilation.** The residue of `z ↦ f (c * z)` at `p` is `c⁻¹` times
the residue of `f` at `c * p`. For `c = 0` both sides vanish: the left side is the residue of a
constant function, and `0⁻¹ = 0`. -/
@[simp]
theorem residue_comp_const_mul (f : ℂ → ℂ) (c p : ℂ) :
    residue (fun z ↦ f (c * z)) p = c⁻¹ * residue f (c * p) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using residue_eq_zero_of_analyticAt (f := fun _ : ℂ ↦ f 0) (z₀ := p) analyticAt_const
  have h : residue (fun z ↦ c * f (c * z)) p = residue f (c * p) := by
    simpa [mul_comm _ c] using residue_comp_mul_deriv (f := f) (φ := fun z ↦ c * z) (p := p)
      (by fun_prop) (by simpa using hc)
  rw [residue_const_mul] at h
  rw [← h, inv_mul_cancel_left₀ hc]

end TauCeti.Contour

end
