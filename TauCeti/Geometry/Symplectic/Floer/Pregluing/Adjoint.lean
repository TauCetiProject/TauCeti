/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.Splicing

/-!
# The formal adjoint along the pre-glued map

Let `u` and `v` be Floer cylinders for the cylindrical datum `K = H_t dt` and a structure `J_t`
independent of `s`, with `u` converging to an orbit `x` as `s → +∞` and `v` converging to `x` as
`s → -∞`, and let `w_R` be their pre-glued map (`TauCeti.Floer.preglue`). The gluing theorem
corrects `w_R` to a solution by a Newton iteration, which needs a right inverse of the linearized
operator `D_{w_R}` bounded uniformly in `R`. When `D_u` and `D_v` are onto, the uniform bound comes
from an injectivity estimate `‖η‖²_{W^{1,2}} ≤ C' ‖D^*_{w_R} η‖²_{L²}` for the formal adjoint
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`) with `C'` independent of `R`. This file proves
that estimate from the corresponding estimates for `D^*_u` and `D^*_v`.

The estimate is stated for the adjoint rather than for `D` itself: for `s`-independent data the
translates of a nonstationary trajectory `u` are solutions, so `∂s u` lies in the kernel of `D_u`
and `D_u` satisfies no injectivity estimate. On the Sobolev completion, the estimate for `D^*_u`
instead expresses that `D_u` is onto, which is the regularity of `u`.

* **Closeness of the coefficients.** The formal adjoint is
  `D^* η = -(∂s η + (∂t η) ∘ J(z, w z) + η ∘ A(z))` with `A = ∂t J - C`
  (`TauCeti.SymplecticForm.floerLinearizationAdjoint_eq_neg`). For cylindrical data its
  coefficients at `z = (s, t)` are continuous functions of `t`, `w(z)` and `∂t w(z)`. On the part
  `s ≤ R / 2` of the fundamental domain, `w_R` either agrees with the translate `u(· + R, ·)`
  near `z`, for `s < -1`, or both are close to the stationary cylinder over `x` together with their
  `t`-derivatives, since there `u` is evaluated at `s + R ≥ R - 1` and `v` at `s - R ≤ -R / 2`,
  and no derivative of the cutoff enters the `t`-derivative of `w_R`
  (`TauCeti.Floer.norm_fderiv_preglue_apply_sub_le`). Uniform continuity at the
  compact curve `t ↦ (t, x(t), x'(t))` then makes the coefficients of `D^*_{w_R}` and of the adjoint
  along `u(· + R, ·)` uniformly close for large `R`, and symmetrically for `s ≥ -R / 2` and
  `v(· - R, ·)` (`TauCeti.SymplecticForm.eventually_forall_norm_sub_le_preglue`). Only uniform
  convergence of `u` and `v` and of their `t`-derivatives to `x` and `x'` on `t ∈ [0, 1]` is used,
  not its exponential rate, nor any convergence of the `s`-derivatives.
* **The uniform estimate.** If `D^*_u` and `D^*_v` satisfy the injectivity estimate with constant
  `C`, then for all large `R` so does `D^*_{w_R}`, with the constant `64 C`
  (`eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue`).
  This is the spliced estimate
  `setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice` with the neck
  `[-R / 2, R / 2]` (in the namespace `TauCeti.SymplecticForm`), the estimates for the translates
  coming from translation invariance
  (`TauCeti.Floer.setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right`).

The target is a symplectic vector space and sections are `C²` covector fields of period one in `t`
vanishing outside a strip, as in `TauCeti.Geometry.Symplectic.Floer.Splicing`. The Sobolev
completion and the construction of the right inverse from the estimate are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the uniformly bounded right inverses of glued Cauchy–Riemann operators.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

open Set Filter Topology Function ContinuousLinearMap

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **The pre-glued map in the middle of the neck.** If `u` is within `θ` of the orbit `x` at
`(s + R, t)`, and `v` at `(s - R, t)`, with `t`-derivatives within `θ` of `X = x'(t)`, then the
value and slice velocity of the pre-glued map at `(s, t)` are within `2 θ` of those of the
stationary cylinder over `x`. No derivative of the cutoff enters. -/
private theorem norm_preglue_prod_sub_le {x : ℝ → V} {u v : ℝ × ℝ → V} {R θ s t : ℝ} {X : V}
    (hx : HasDerivAt x X t) (hu : DifferentiableAt ℝ u (s + R, t))
    (hv : DifferentiableAt ℝ v (s - R, t)) (hu₀ : ‖u (s + R, t) - x t‖ ≤ θ)
    (hu₁ : ‖fderiv ℝ u (s + R, t) stdComplexLineImag - X‖ ≤ θ)
    (hv₀ : ‖v (s - R, t) - x t‖ ≤ θ)
    (hv₁ : ‖fderiv ℝ v (s - R, t) stdComplexLineImag - X‖ ≤ θ) :
    ‖(preglue x u v R (s, t), fderiv ℝ (preglue x u v R) (s, t) stdComplexLineImag) - (x t, X)‖ ≤
      2 * θ := by
  have hzR : (s, t) + (R, 0) = (s + R, t) := by simp
  have hzR' : (s, t) - (R, 0) = (s - R, t) := by simp
  have h₀ := norm_preglue_sub_le (x := x) (u := u) (v := v) (R := R) (z := (s, t))
  have h₁ := norm_fderiv_preglue_apply_sub_le (z := (s, t)) (R := R) hx (by rwa [hzR])
    (by rwa [hzR'])
  rw [hzR, hzR'] at h₀ h₁
  exact norm_prod_le_iff.2 ⟨h₀.trans (by linarith), h₁.trans (by linarith)⟩

/-- **The middle of the neck.** If `u` and `v` converge to the orbit `x` together with their
`t`-derivatives, uniformly in `t ∈ [0, 1]`, as `s → +∞` and `s → -∞`, then for every `δ > 0`
there is `S` such that, at the points `z = (s, t)` with `t ∈ [0, 1]`, `S ≤ s + R` and
`s - R ≤ -S`, the value and slice velocity of the pre-glued map at `z`, of `u` at `z + (R, 0)` and
of `v` at `z - (R, 0)` are all within `δ` of those of the stationary cylinder over `x`. -/
private theorem exists_forall_norm_prod_sub_le_preglue (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {x : ℝ → V} {u v : ℝ × ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atBot (Icc 0 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ S, ∀ (R : ℝ) (z : ℝ × ℝ), z.2 ∈ Icc (0 : ℝ) 1 → S ≤ z.1 + R → z.1 - R ≤ -S →
      ‖(preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ ∧
        ‖(u (z + (R, 0)), fderiv ℝ u (z + (R, 0)) stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ ∧
        ‖(v (z - (R, 0)), fderiv ℝ v (z - (R, 0)) stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ := by
  -- `θ`-closeness of `u` and `v` to the stationary cylinder gives `δ`-closeness of the pre-glued
  -- map, for `2 θ = δ`.
  set θ := δ / 2
  have hθ : 0 < θ := by positivity
  have hθδ : 2 * θ = δ := by ring
  have hθδ' : θ ≤ δ := by linarith
  obtain ⟨Su, hSu⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hux θ hθ).and
    (Metric.tendstoUniformlyOn_iff.1 hdux θ hθ))
  obtain ⟨Sv, hSv⟩ := eventually_atBot.1 ((Metric.tendstoUniformlyOn_iff.1 hvx θ hθ).and
    (Metric.tendstoUniformlyOn_iff.1 hdvx θ hθ))
  refine ⟨max Su (-Sv), fun R ⟨s, t⟩ ht hzu hzv ↦ ?_⟩
  have hsu : Su ≤ s + R := (le_max_left _ _).trans hzu
  have hsv : s - R ≤ Sv := by linarith [le_max_right Su (-Sv)]
  have hu₀ := (hSu (s + R) hsu).1 t ht
  have hu₁ := (hSu (s + R) hsu).2 t ht
  have hv₀ := (hSv (s - R) hsv).1 t ht
  have hv₁ := (hSv (s - R) hsv).2 t ht
  rw [dist_comm, dist_eq_norm] at hu₀ hu₁ hv₀ hv₁
  rw [show (s, t) + (R, 0) = (s + R, t) by simp, show (s, t) - (R, 0) = (s - R, t) by simp]
  exact ⟨(norm_preglue_prod_sub_le (hx t) (hu _) (hv _) hu₀.le hu₁.le hv₀.le
    hv₁.le).trans_eq hθδ, (norm_prod_le_iff.2 ⟨hu₀.le, hu₁.le⟩).trans hθδ',
    (norm_prod_le_iff.2 ⟨hv₀.le, hv₁.le⟩).trans hθδ'⟩

/-- **The coefficients of the formal adjoint along the pre-glued map.** Let `J_t` be `C¹` and
`H_t` be `C²`, jointly in `t`, let `x` be an orbit of `X_{H_t}`, and let `u` and `v` be
differentiable maps converging to `x` together with their `t`-derivatives, uniformly in
`t ∈ [0, 1]`, as `s → +∞` and as `s → -∞` respectively. Then for every `ε > 0` and all large
`R`, at the points `z = (s, t)` with `t ∈ [0, 1]`:

* for `s ≤ R / 2`, the coefficients `J_t(w_R z)` and `A(z) = ∂t J - C` of the formal adjoint along
  the pre-glued map `w_R` are `ε`-close to those along the translate `u(· + R, ·)`;
* for `s ≥ -R / 2`, they are `ε`-close to those along the translate `v(· - R, ·)`.

These are the closeness hypotheses of
`setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice` for the neck
`[-R / 2, R / 2]`. -/
theorem eventually_forall_norm_sub_le_preglue (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} (hJ : ContDiff ℝ 1 (uncurry J))
    (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atBot (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop,
      (∀ z : ℝ × ℝ, z.1 ≤ R / 2 → z.2 ∈ Icc (0 : ℝ) 1 →
        ‖J z.2 (preglue x u v R z) - J z.2 (u (z + (R, 0)))‖ ≤ ε ∧
        ‖(fderiv ℝ (fun w ↦ J w.2 (preglue x u v R w)) z stdComplexLineImag -
              ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
                (preglue x u v R) z) -
            (fderiv ℝ (fun w ↦ J w.2 (u (w + (R, 0)))) z stdComplexLineImag -
              ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
                (fun w ↦ u (w + (R, 0))) z)‖ ≤ ε) ∧
      (∀ z : ℝ × ℝ, -(R / 2) ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 →
        ‖J z.2 (preglue x u v R z) - J z.2 (v (z - (R, 0)))‖ ≤ ε ∧
        ‖(fderiv ℝ (fun w ↦ J w.2 (preglue x u v R w)) z stdComplexLineImag -
              ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
                (preglue x u v R) z) -
            (fderiv ℝ (fun w ↦ J w.2 (v (w - (R, 0)))) z stdComplexLineImag -
              ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
                (fun w ↦ v (w - (R, 0))) z)‖ ≤ ε) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ, hδ, hnear⟩ := ω.exists_pos_forall_norm_cylindricalAdjointCoeff_sub_le hJ hH hxc hε
  obtain ⟨S, hmid⟩ := exists_forall_norm_prod_sub_le_preglue ω hx hu hv hux hdux hvx hdvx hδ
  have hwd (R : ℝ) : Differentiable ℝ (preglue x u v R) :=
    differentiable_preglue (fun t ↦ (hx t).differentiableAt) hu hv
  have hJd : Differentiable ℝ (uncurry J) := hJ.differentiable one_ne_zero
  -- Off the middle of the neck the pre-glued map is a translate near `z`; in it, use `hmid`.
  filter_upwards [eventually_ge_atTop (S + 1), eventually_ge_atTop (2 * S)] with R h₁ h₂
  refine ⟨fun z hz ht ↦ ?_, fun z hz ht ↦ ?_⟩
  · have hu' : DifferentiableAt ℝ (fun w ↦ u (w + (R, 0))) z :=
      (hu _).comp z (differentiableAt_id.add_const _)
    rw [ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff hJd (hwd R z),
      ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff hJd hu',
      fderiv_comp_add_right]
    by_cases hs : z.1 < -1
    · rw [preglue_of_le_neg_one hs.le, fderiv_preglue_of_lt_neg_one hs]
      simp [hε.le]
    · obtain ⟨hw, hu₀, -⟩ := hmid R z ht (by linarith) (by linarith)
      exact hnear z.2 ht (preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag)
        (u (z + (R, 0)), fderiv ℝ u (z + (R, 0)) stdComplexLineImag) hw hu₀
  · have hv' : DifferentiableAt ℝ (fun w ↦ v (w - (R, 0))) z :=
      (hv _).comp z (differentiableAt_id.sub_const _)
    rw [ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff hJd (hwd R z),
      ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff hJd hv',
      fderiv_comp_sub]
    by_cases hs : 1 < z.1
    · rw [preglue_of_one_le hs.le, fderiv_preglue_of_one_lt hs]
      simp [hε.le]
    · obtain ⟨hw, -, hv₀⟩ := hmid R z ht (by linarith) (by linarith)
      exact hnear z.2 ht (preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag)
        (v (z - (R, 0)), fderiv ℝ v (z - (R, 0)) stdComplexLineImag) hw hv₀

/-- **The uniform estimate for the formal adjoint along the pre-glued map.** Let `J_t` be `C¹` and
`H_t` be `C²`, jointly in `t`, let `x` be an orbit of `X_{H_t}`, and let `u` and `v` be `C¹` maps
converging to `x` together with their `t`-derivatives, uniformly in `t ∈ [0, 1]`, as `s → +∞` and
as `s → -∞` respectively; no convergence of the `s`-derivatives is needed.
Suppose that the formal adjoints `D^*_u` and `D^*_v` of the linearized Floer operators along `u`
and `v`, for the cylindrical datum `K = H_t dt` and the structure `J_t`, satisfy the injectivity
estimate `‖η‖²_{W^{1,2}} ≤ C ‖D^* η‖²_{L²}` on `C²` covector fields of period one in `t` vanishing
outside a strip. Then for all large gluing parameters `R` the formal adjoint along the pre-glued
map `w_R` satisfies the injectivity estimate with the constant `64 C`, independent of `R`. -/
theorem eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue
    (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
    {u v : ℝ × ℝ → V} (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atBot (Icc 0 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hestu : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint (fun p ↦ J p.2)
            (fun _ _ ↦ 0) (fun p ↦ H p.2) u η z‖ ^ 2)
    (hestv : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint (fun p ↦ J p.2)
            (fun _ _ ↦ 0) (fun p ↦ H p.2) v η z‖ ^ 2) :
    ∀ᶠ R in atTop, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b →
        (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
            (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) η z‖ ^ 2 := by
  -- The comparison is good enough once the coefficients are `ε`-close, `8 C ε² ≤ 1`.
  set ε := 1 / (8 * C + 1)
  have hε : 0 < ε := by positivity
  have hCε : 8 * C * ε ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  -- Regularity of the data and of the three maps.
  have hxc : ContDiff ℝ 1 x :=
    ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH.of_le (by norm_num)) hx
  have hJ' (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
      ContDiffAt ℝ 1 (uncurry fun p : ℝ × ℝ ↦ J p.2) (z, w z) :=
    (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  have hKs' (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
      ContDiffAt ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) (z, w z) :=
    contDiffAt_const
  have hKt' (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
      ContDiffAt ℝ 2 (uncurry fun p : ℝ × ℝ ↦ H p.2) (z, w z) :=
    (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  filter_upwards [eventually_forall_norm_sub_le_preglue ω hJ hH hx
    (hu.differentiable one_ne_zero) (hv.differentiable one_ne_zero) hux hdux hvx hdvx hε,
    eventually_ge_atTop (16 * (C + 1))] with R hclose hR
  intro η hη hper a b hab hη₀
  have hR0 : 0 < R / 2 := by linarith
  have hCT : 64 * C ≤ (R / 2) ^ 2 := by nlinarith
  have hvR : (fun w : ℝ × ℝ ↦ v (w + (-R, 0))) = fun w ↦ v (w - (R, 0)) :=
    funext fun w ↦ by rw [sub_eq_add_neg, Prod.neg_mk, neg_zero]
  -- The estimates for the translates of `u` and `v` come from translation invariance.
  exact setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice ω
    (u₁ := fun w ↦ u (w + (R, 0))) (u₂ := fun w ↦ v (w - (R, 0)))
    (hJ' _) (hKs' _) (hKt' _) (contDiff_preglue hxc hu hv)
    (hJ' _) (hKs' _) (hKt' _) (hu.comp (contDiff_id.add contDiff_const))
    (hJ' _) (hKs' _) (hKt' _) (hv.comp (contDiff_id.sub contDiff_const)) hC hR0 hCT hCε
    (fun z hz ht ↦ (hclose.1 z hz ht).1) (fun z hz ht ↦ (hclose.1 z hz ht).2)
    (fun z hz ht ↦ (hclose.2 z hz ht).1) (fun z hz ht ↦ (hclose.2 z hz ht).2)
    (fun η hη hper a b hab hη₀ ↦ by
      simpa only [Prod.snd_add, add_zero] using
        Floer.setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right R
          (fun η z ↦ ω.floerLinearizationAdjoint_comp_add_right _ _ _ u η (R, 0) z) hestu hη hper
          hab hη₀)
    (fun η hη hper a b hab hη₀ ↦ by
      simpa only [Prod.snd_add, add_zero, hvR] using
        Floer.setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right (-R)
          (fun η z ↦ ω.floerLinearizationAdjoint_comp_add_right _ _ _ v η (-R, 0) z) hestv hη
          hper hab hη₀)
    hη hper hab hη₀

end TauCeti.SymplecticForm
