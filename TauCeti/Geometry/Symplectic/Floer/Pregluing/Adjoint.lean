/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.Splicing
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Topology.Compactness.Normed

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
  near `z`, for `s < -1`, or both are `C¹`-close to the stationary cylinder over `x`, since there
  `u` is evaluated at `s + R ≥ R - 1` and `v` at `s - R ≤ -R / 2`. Uniform continuity at the
  compact curve `t ↦ (t, x(t), x'(t))` then makes the coefficients of `D^*_{w_R}` and of the adjoint
  along `u(· + R, ·)` uniformly close for large `R`, and symmetrically for `s ≥ -R / 2` and
  `v(· - R, ·)` (`TauCeti.SymplecticForm.eventually_forall_norm_sub_le_preglue`). Only uniform
  `C¹` convergence of `u` and `v` to `x` on `t ∈ [0, 1]` is used, not its exponential rate.
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

/-- The zeroth-order coefficient `A = ∂t J - C` of the formal adjoint for the cylindrical datum,
as a function of `t`, the value `y = w(z)` and the slice velocity `d = ∂t w(z)` of the map. -/
private noncomputable def adjointCoeff (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (p : ℝ × V × V) : V →L[ℝ] V :=
  fderiv ℝ (uncurry J) (p.1, p.2.1) (1, p.2.2) -
    ((fderiv ℝ (J p.1) p.2.1).flip (p.2.2 - ω.hamiltonianVectorField (H p.1) p.2.1) -
      (J p.1 p.2.1).comp (fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2.1))

/-- For the cylindrical datum, the zeroth-order coefficient of the formal adjoint along `w` at `z`
is `adjointCoeff` at `(t, w z, ∂t w z)`. -/
private theorem adjointCoeff_eq (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} (hJ : Differentiable ℝ (uncurry J)) {w : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hw : DifferentiableAt ℝ w z) :
    fderiv ℝ (fun p ↦ J p.2 (w p)) z stdComplexLineImag -
        ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      adjointCoeff ω J H (z.2, w z, fderiv ℝ w z stdComplexLineImag) := by
  have hd := (hJ (z.2, w z)).hasFDerivAt.comp z (hasFDerivAt_snd.prodMk hw.hasFDerivAt)
  rw [show (fun p : ℝ × ℝ ↦ J p.2 (w p)) = uncurry J ∘ fun p ↦ (p.2, w p) from
    funext fun p ↦ (uncurry_apply_pair J p.2 (w p)).symm, hd.fderiv, adjointCoeff]
  congr 1
  ext y
  simp [floerLinearizationCoeff_apply]

/-- `adjointCoeff` is continuous for `C¹` structures and `C²` Hamiltonians. -/
private theorem continuous_adjointCoeff (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) :
    Continuous (adjointCoeff ω J H) := by
  have hX := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hg : Continuous fun p : ℝ × V × V ↦ (p.1, p.2.1) :=
    continuous_fst.prodMk continuous_snd.fst
  have hdJ : Continuous fun p : ℝ × V × V ↦ fderiv ℝ (J p.1) p.2.1 :=
    (ContDiff.fderiv (f := fun p : ℝ × V × V ↦ J p.1) (g := fun p ↦ p.2.1) (n := 0)
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd.fst (by simp)).continuous
  have hdX : Continuous fun p : ℝ × V × V ↦ fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2.1 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V × V) y ↦ ω.hamiltonianVectorField (H p.1) y)
      (g := fun p ↦ p.2.1) (n := 0) (hX.comp (contDiff_fst.fst.prodMk contDiff_snd))
      contDiff_snd.fst (by simp)).continuous
  have hXp : Continuous fun p : ℝ × V × V ↦ ω.hamiltonianVectorField (H p.1) p.2.1 :=
    hX.continuous.comp hg
  have hJp : Continuous fun p : ℝ × V × V ↦ J p.1 p.2.1 := hJ.continuous.comp hg
  exact (((hJ.continuous_fderiv one_ne_zero).comp hg).clm_apply
    (continuous_const.prodMk continuous_snd.snd)).sub
    ((((flipₗᵢ ℝ V V V).continuous.comp hdJ).clm_apply (continuous_snd.snd.sub hXp)).sub
      (hJp.clm_comp hdX))


/-- Near the curve `t ↦ (x t, X_{H_t}(x t))`, `t ∈ [0, 1]`, of the stationary cylinder over `x`,
the values of `J_t` and of `adjointCoeff` are uniformly continuous: for `ε > 0` there is `δ > 0`
such that two points `δ`-close to the curve over the same `t` have `ε`-close values. -/
private theorem exists_pos_forall_norm_adjointCoeff_sub_le (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} (hJ : ContDiff ℝ 1 (uncurry J))
    (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ q q' : V × V,
      ‖q - (x t, ω.hamiltonianVectorField (H t) (x t))‖ ≤ δ →
      ‖q' - (x t, ω.hamiltonianVectorField (H t) (x t))‖ ≤ δ →
      ‖J t q.1 - J t q'.1‖ ≤ ε ∧ ‖adjointCoeff ω J H (t, q) - adjointCoeff ω J H (t, q')‖ ≤ ε := by
  have hc : Continuous fun t ↦ (x t, ω.hamiltonianVectorField (H t) (x t)) :=
    hx.prodMk ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous.comp
      (continuous_id.prodMk hx))
  -- Both values at once, as the pair `(J_t, adjointCoeff)` in the product space.
  have hΦ : Continuous fun p : ℝ × V × V ↦ (J p.1 p.2.1, adjointCoeff ω J H p) :=
    (hJ.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (continuous_adjointCoeff ω hJ hH)
  obtain ⟨δ, hδ, h⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le
    hc.continuousOn (fun _ _ ↦ hΦ.continuousAt) (half_pos hε)
  refine ⟨δ, hδ, fun t ht q q' hq hq' ↦ ?_⟩
  have hb := h t ht q' hq'
  rw [norm_sub_rev] at hb
  simpa using norm_prod_le_iff.1
    ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (h t ht q hq) hb))

omit [FiniteDimensional ℝ V] in
/-- A map within `θ` of `y` at `z`, whose derivative there is within `θ` of `(σ, τ) ↦ τ X`, has
value and slice velocity within `θ` of `(y, X)`. -/
private theorem norm_prod_sub_le_of_le {f : ℝ × ℝ → V} {z : ℝ × ℝ} {y X : V} {θ : ℝ}
    (h₀ : ‖f z - y‖ ≤ θ) (h₁ : ‖fderiv ℝ f z - (snd ℝ ℝ ℝ).smulRight X‖ ≤ θ) :
    ‖(f z, fderiv ℝ f z stdComplexLineImag) - (y, X)‖ ≤ θ := by
  refine norm_prod_le_iff.2 ⟨h₀, ?_⟩
  have hS : (snd ℝ ℝ ℝ).smulRight X stdComplexLineImag = X := by simp [stdComplexLineImag_snd]
  rw [Prod.snd_sub, ← hS, ← sub_apply]
  refine (le_opNorm _ _).trans ?_
  simpa [stdComplexLineImag_eq] using h₁

omit [FiniteDimensional ℝ V] in
/-- **The pre-glued map in the middle of the neck.** If `u` is within `θ` of the orbit `x` in `C¹`
at `(s + R, t)`, and `v` at `(s - R, t)`, and the derivative of the cutoff is at most `B`, then the
value and slice velocity of the pre-glued map at `(s, t)` are within `(2 B + 2) θ` of those of the
stationary cylinder over `x`. -/
private theorem norm_preglue_prod_sub_le {x : ℝ → V} {u v : ℝ × ℝ → V} {R B θ s t : ℝ} {X : V}
    (hx : HasDerivAt x X t) (hu : DifferentiableAt ℝ u (s + R, t))
    (hv : DifferentiableAt ℝ v (s - R, t)) (hB : ∀ s, |deriv pregluingCutoff s| ≤ B)
    (hu₀ : ‖u (s + R, t) - x t‖ ≤ θ)
    (hu₁ : ‖fderiv ℝ u (s + R, t) - (snd ℝ ℝ ℝ).smulRight X‖ ≤ θ)
    (hv₀ : ‖v (s - R, t) - x t‖ ≤ θ)
    (hv₁ : ‖fderiv ℝ v (s - R, t) - (snd ℝ ℝ ℝ).smulRight X‖ ≤ θ) :
    ‖(preglue x u v R (s, t), fderiv ℝ (preglue x u v R) (s, t) stdComplexLineImag) - (x t, X)‖ ≤
      (2 * B + 2) * θ := by
  have hzR : (s, t) + (R, 0) = (s + R, t) := by simp
  have hzR' : (s, t) - (R, 0) = (s - R, t) := by simp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hθ : 0 ≤ θ := (norm_nonneg _).trans hu₀
  have h₀ := norm_preglue_sub_le (x := x) (u := u) (v := v) (R := R) (z := (s, t))
  have h₁ := norm_fderiv_preglue_sub_le (z := (s, t)) (R := R) hx (by rwa [hzR]) (by rwa [hzR'])
  rw [hzR, hzR'] at h₀ h₁
  refine norm_prod_sub_le_of_le (h₀.trans (by nlinarith)) (h₁.trans ?_)
  nlinarith [hB s, hB (-s), abs_nonneg (deriv pregluingCutoff s),
    abs_nonneg (deriv pregluingCutoff (-s)), norm_nonneg (u (s + R, t) - x t),
    norm_nonneg (v (s - R, t) - x t)]

/-- **The middle of the neck.** If `u` and `v` converge to the orbit `x` in `C¹`, uniformly in
`t ∈ [0, 1]`, as `s → +∞` and `s → -∞`, then for every `δ > 0` there is `S` such that, at the points
`z = (s, t)` with `t ∈ [0, 1]`, `S ≤ s + R` and `s - R ≤ -S`, the value and slice velocity of the
pre-glued map at `z`, of `u` at `z + (R, 0)` and of `v` at `z - (R, 0)` are all within `δ` of those
of the stationary cylinder over `x`. -/
private theorem exists_forall_norm_prod_sub_le_preglue (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {x : ℝ → V} {u v : ℝ × ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot (Icc 0 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ S, ∀ (R : ℝ) (z : ℝ × ℝ), z.2 ∈ Icc (0 : ℝ) 1 → S ≤ z.1 + R → z.1 - R ≤ -S →
      ‖(preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ ∧
        ‖(u (z + (R, 0)), fderiv ℝ u (z + (R, 0)) stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ ∧
        ‖(v (z - (R, 0)), fderiv ℝ v (z - (R, 0)) stdComplexLineImag) -
          (x z.2, ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤ δ := by
  -- With `B` bounding the cutoff derivative, `θ`-closeness of `u` and `v` to the stationary
  -- cylinder in `C¹` gives `δ`-closeness of the pre-glued map, for `(2 B + 2) θ = δ`.
  obtain ⟨B, hB⟩ := exists_abs_deriv_pregluingCutoff_le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set θ := δ / (2 * B + 2)
  have hθ : 0 < θ := by positivity
  have hθδ : (2 * B + 2) * θ = δ := by
    simp only [θ]
    field_simp
  have hθδ' : θ ≤ δ := by nlinarith
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
  exact ⟨(norm_preglue_prod_sub_le (hx t) (hu _) (hv _) hB hu₀.le hu₁.le hv₀.le
    hv₁.le).trans_eq hθδ, (norm_prod_sub_le_of_le hu₀.le hu₁.le).trans hθδ',
    (norm_prod_sub_le_of_le hv₀.le hv₁.le).trans hθδ'⟩

/-- **The coefficients of the formal adjoint along the pre-glued map.** Let `J_t` be `C¹` and
`H_t` be `C²`, jointly in `t`, let `x` be an orbit of `X_{H_t}`, and let `u` and `v` be
differentiable maps converging to `x` in `C¹`, uniformly in `t ∈ [0, 1]`, as `s → +∞` and as
`s → -∞` respectively. Then for every `ε > 0` and all large `R`, at the points `z = (s, t)` with
`t ∈ [0, 1]`:

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
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot (Icc 0 1))
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
  obtain ⟨δ, hδ, hnear⟩ := exists_pos_forall_norm_adjointCoeff_sub_le ω hJ hH hxc hε
  obtain ⟨S, hmid⟩ := exists_forall_norm_prod_sub_le_preglue ω hx hu hv hux hdux hvx hdvx hδ
  have hwd (R : ℝ) : Differentiable ℝ (preglue x u v R) :=
    differentiable_preglue (fun t ↦ (hx t).differentiableAt) hu hv
  have hJd : Differentiable ℝ (uncurry J) := hJ.differentiable one_ne_zero
  -- Off the middle of the neck the pre-glued map is a translate near `z`; in it, use `hmid`.
  filter_upwards [eventually_ge_atTop (S + 1), eventually_ge_atTop (2 * S)] with R h₁ h₂
  refine ⟨fun z hz ht ↦ ?_, fun z hz ht ↦ ?_⟩
  · have hu' : DifferentiableAt ℝ (fun w ↦ u (w + (R, 0))) z :=
      (hu _).comp z (differentiableAt_id.add_const _)
    rw [adjointCoeff_eq ω hJd (hwd R z), adjointCoeff_eq ω hJd hu', fderiv_comp_add_right]
    by_cases hs : z.1 < -1
    · rw [preglue_of_le_neg_one hs.le, fderiv_preglue_of_lt_neg_one hs]
      simp [hε.le]
    · obtain ⟨hw, hu₀, -⟩ := hmid R z ht (by linarith) (by linarith)
      exact hnear z.2 ht (preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag)
        (u (z + (R, 0)), fderiv ℝ u (z + (R, 0)) stdComplexLineImag) hw hu₀
  · have hv' : DifferentiableAt ℝ (fun w ↦ v (w - (R, 0))) z :=
      (hv _).comp z (differentiableAt_id.sub_const _)
    rw [adjointCoeff_eq ω hJd (hwd R z), adjointCoeff_eq ω hJd hv', fderiv_comp_sub]
    by_cases hs : 1 < z.1
    · rw [preglue_of_one_le hs.le, fderiv_preglue_of_one_lt hs]
      simp [hε.le]
    · obtain ⟨hw, -, hv₀⟩ := hmid R z ht (by linarith) (by linarith)
      exact hnear z.2 ht (preglue x u v R z, fderiv ℝ (preglue x u v R) z stdComplexLineImag)
        (v (z - (R, 0)), fderiv ℝ v (z - (R, 0)) stdComplexLineImag) hw hv₀

/-- **The uniform estimate for the formal adjoint along the pre-glued map.** Let `J_t` be `C¹` and
`H_t` be `C²`, jointly in `t`, let `x` be an orbit of `X_{H_t}`, and let `u` and `v` be `C¹` maps
converging to `x` in `C¹`, uniformly in `t ∈ [0, 1]`, as `s → +∞` and as `s → -∞` respectively.
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
    (hdux : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop (Icc 0 1))
    (hvx : TendstoUniformlyOn (fun s t ↦ v (s, t)) x atBot (Icc 0 1))
    (hdvx : TendstoUniformlyOn (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot (Icc 0 1))
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
    contDiff_one_of_hasDerivAt (X := fun t ↦ ω.hamiltonianVectorField (H t))
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
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
