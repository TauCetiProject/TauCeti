/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Gluing
public import TauCeti.Geometry.Symplectic.Floer.Pregluing.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.ODE.Regularity

/-!
# Uniformly bounded right inverses along pre-glued Floer cylinders

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H_t` a Hamiltonian and `J_t(y)` a
family of endomorphisms, both of period one in `t`, and let `x` be a one-periodic orbit of
`X_{H_t}`. Let `u` and `v` be `C¹` maps, `u` converging to `x` in `C¹` as `s → +∞` and `v` as
`s → -∞`, uniformly in `t`, such as the two levels of a once-broken Floer trajectory meeting at
`x`. The pre-glued map `w_R` (`TauCeti.Floer.preglue`) is `u(s + R, t)` for `s ≤ -1` and
`v(s - R, t)` for `s ≥ 1`, and passes through `x` on the neck.

This file proves that if the linearized operators
`D_u, D_v : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the datum `K = H_t dt`
(`TauCeti.SymplecticForm.floerSobolevOperator`) have bounded right inverses `Q₁` and `Q₂`, as they
do along regular Floer trajectories, then for every sufficiently large `R` the linearized operator
`D_{w_R}` along the pre-glued map has a bounded right inverse `Q_R` with
`‖Q_R‖ ≤ 8 (‖Q₁‖ + ‖Q₂‖)`, a bound independent of `R`
(`TauCeti.SymplecticForm.eventually_exists_rightInverse_floerSobolevOperator_preglue`). This is
the linear input of the Newton iteration that corrects `w_R` to an actual Floer trajectory when
gluing broken trajectories.

* **The model.** The coefficient fields of `D_u` and `D_v` on jets converge at the glued ends to
  that of the stationary cylinder over `x`
  (`TauCeti.SymplecticForm.tendstoUniformly_floerLinearizationCoeff`). The gluing theorem on the
  cylinder, `TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff`,
  then gives the operators `T_R` of the glued coefficient fields, equal to those along `u(· + R, ·)`
  for `s < 0` and along `v(· - R, ·)` for `s ≥ 0`, right inverses of norm at most
  `4 (‖Q₁‖ + ‖Q₂‖)`.
* **The perturbation.** By
  `TauCeti.SymplecticForm.eventually_norm_floerLinearizationCoeff_preglue_sub_le`, the coefficients
  of `D_{w_R}` are uniformly within any given `ε` of those along `u(· + R, ·)` on `s ≤ R / 2` and of
  those along `v(· - R, ·)` on `s ≥ -R / 2`, for every large `R`. So `D_{w_R} - T_R` is the
  first-order operator of a coefficient field bounded by `2 ε`, and for small `ε`,
  `‖D_{w_R} Q - id‖ = ‖(D_{w_R} - T_R) Q‖ ≤ 1 / 2` for the right inverse `Q` of `T_R`. A Neumann
  series then turns `Q` into a right inverse of `D_{w_R}` of at most twice its norm
  (`TauCeti.exists_rightInverse_jetOperator_comp_subtypeL_of_norm_sub_le`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the linearized operator along a pre-glued curve and its uniformly bounded right inverse.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on gluing Floer trajectories.
-/

public section

open Filter Set Function MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace TauCeti.SymplecticForm

open Floer CylinderSobolev
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
  {u v : ℝ × ℝ → V}

/-- The coefficient field on jets of the linearized operator of the datum `K = H_t dt` along a map
converging to `x` in `C¹` along `l` converges uniformly to that of the stationary cylinder over
`x`, the coefficient field of `∂s + J_t(x t) ∂t - J_t(x t) dX_{H_t}(x t)`. -/
private theorem tendstoUniformlyOn_floerJetCoeff (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : Continuous x) (hxp : Periodic x 1) {l : Filter ℝ}
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x l)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) l) :
    TendstoUniformlyOn (curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
      (fun t ↦ firstOrderJetCoeff (J t (x t))
        (-(J t (x t)).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)))) l (Icc 0 1) := by
  obtain ⟨hJu, hCu⟩ := ω.tendstoUniformly_floerLinearizationCoeff hJ hH hJp hHp hx hxp hux hdux
  refine (Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_).tendstoUniformlyOn
  filter_upwards [Metric.tendstoUniformly_iff.1 hJu (ε / 2) (half_pos hε),
    Metric.tendstoUniformly_iff.1 hCu (ε / 2) (half_pos hε)] with s h₁ h₂ t
  have e₁ := h₁ t
  have e₂ := h₂ t
  rw [dist_comm, dist_eq_norm] at e₁ e₂ ⊢
  rw [curry_apply, floerJetCoeff_def]
  exact (norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le _ _ _ _).trans_lt
    ((add_lt_add e₁ e₂).trans_eq (add_halves ε))

/-- The coefficient field on jets of the datum `K = H_t dt` along `u` at `z + (a, 0)` is that
along the translate `u(· + a, ·)` at `z`. -/
private theorem floerJetCoeff_add_fst (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) (a : ℝ) :
    ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u (z + (a, 0)) =
      ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (fun p ↦ u (p + (a, 0))) z := by
  rw [← floerJetCoeff_comp_add_right]
  exact floerJetCoeff_congr_data ω _ (by simp) rfl (by simp)

/-- **The coefficients along the pre-glued map and the glued coefficients.** For every `ε > 0`
and every large `R`, the coefficient field on jets of the linearized operator along the pre-glued
map `w_R` is everywhere within `2 ε` of the coefficient field obtained by gluing those along `u`
and `v` along a neck of length `2 R` (`TauCeti.gluedCoeff`). -/
private theorem eventually_norm_floerJetCoeff_preglue_sub_le (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop, ∀ z : ℝ × ℝ,
      ‖ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z -
        uncurry (gluedCoeff
          (curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
          (curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v)) R) z‖ ≤
        2 * ε := by
  filter_upwards [ω.eventually_norm_floerLinearizationCoeff_preglue_sub_le hJ hH hJp hHp hx hxp
    (.of_forall fun _ _ ↦ hu.differentiable one_ne_zero _) hux hdux
    (.of_forall fun _ _ ↦ hv.differentiable one_ne_zero _) hvx hdvx hε,
    eventually_ge_atTop 0] with R ⟨h₁, h₂⟩ hR z
  rcases lt_or_ge z.1 0 with hz | hz
  · -- On `s < 0` the glued field is that along `u(· + R, ·)`.
    obtain ⟨hJz, hCz⟩ := h₁ z (by linarith)
    rw [uncurry_gluedCoeff_of_neg _ _ _ hz, floerJetCoeff_add_fst, floerJetCoeff_def,
      floerJetCoeff_def]
    exact (norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le _ _ _ _).trans
      ((add_le_add hJz hCz).trans_eq (two_mul ε).symm)
  · -- On `s ≥ 0` the glued field is that along `v(· - R, ·)`.
    obtain ⟨hJz, hCz⟩ := h₂ z (by linarith)
    have hvR : (fun p : ℝ × ℝ ↦ v (p + (-R, 0))) = fun p ↦ v (p - (R, 0)) :=
      funext fun p ↦ by rw [sub_eq_add_neg, Prod.neg_mk, neg_zero]
    rw [uncurry_gluedCoeff_of_nonneg _ _ _ hz, floerJetCoeff_add_fst, hvR, floerJetCoeff_def,
      floerJetCoeff_def]
    exact (norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le _ _ _ _).trans
      ((add_le_add hJz hCz).trans_eq (two_mul ε).symm)

/-- The coefficient field on jets of the datum `K = H_t dt` along the pre-glued map is
continuous. -/
private theorem continuous_floerJetCoeff_preglue (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (R : ℝ) :
    Continuous
      (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R)) := by
  have hx₁ : ContDiff ℝ 1 x := contDiff_one_of_hasDerivAt
    (X := fun t ↦ ω.hamiltonianVectorField (H t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
  have hJ' : ContDiff ℝ 1 (uncurry fun (p : ℝ × ℝ) ↦ J p.2) :=
    hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hKt : ContDiff ℝ 2 (uncurry fun (p : ℝ × ℝ) ↦ H p.2) :=
    hH.comp (contDiff_fst.snd.prodMk contDiff_snd)
  exact ω.continuous_floerJetCoeff (fun _ ↦ hJ'.contDiffAt) (fun _ ↦ contDiff_const.contDiffAt)
    (fun _ ↦ hKt.contDiffAt) (contDiff_preglue hx₁ hu hv)

/-- **Uniformly bounded right inverses along pre-glued Floer cylinders.** Let `J` be a `C¹`
family of endomorphisms and `H` a `C²` Hamiltonian, both of period one in `t`, and let `x` be an
orbit of `X_{H_t}` of period one. Let `u` and `v` be `C¹` maps, `u` converging to `x` in `C¹` as
`s → +∞` and `v` as `s → -∞`, uniformly in `t`. Suppose that the linearized operators
`D_u, D_v : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the datum `K = H_t dt` have bounded linear
right inverses `Q₁` and `Q₂`. Then for every sufficiently large `R`, the linearized operator along
the pre-glued map `w_R = TauCeti.Floer.preglue x u v R` has a bounded linear right inverse of norm
at most `8 (‖Q₁‖ + ‖Q₂‖)`. -/
theorem eventually_exists_rightInverse_floerSobolevOperator_preglue (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {Q₁ Q₂ : Lp V 2 stripMeasure →L[ℝ] H1 V}
    (hQ₁ : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v).comp Q₂ =
      ContinuousLinearMap.id ℝ _) :
    ∀ᶠ R in atTop, ∃ Q : Lp V 2 stripMeasure →L[ℝ] H1 V,
      (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglue x u v R)).comp Q = ContinuousLinearMap.id ℝ _ ∧
        ‖Q‖ ≤ 8 * (‖Q₁‖ + ‖Q₂‖) := by
  -- On the zero space `0` is a right inverse.
  rcases subsingleton_or_nontrivial (Lp V 2 stripMeasure) with hL | hL
  · exact .of_forall fun R ↦
      ⟨0, ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _, by rw [opNorm_zero]; positivity⟩
  have hMu := ω.memLp_floerJetCoeff_of_comp_eq_id hQ₁
  have hMv := ω.memLp_floerJetCoeff_of_comp_eq_id hQ₂
  simp only [floerSobolevOperator_def] at hQ₁ hQ₂ ⊢
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  -- The operators of the glued coefficient fields have uniformly bounded right inverses.
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff hMu hMv
    (tendstoUniformlyOn_floerJetCoeff ω hJ hH hJp hHp hxc hxp hux hdux)
    (tendstoUniformlyOn_floerJetCoeff ω hJ hH hJp hHp hxc hxp hvx hdvx) hQ₁ hQ₂
  obtain ⟨K, hK⟩ : ∃ K, K = ‖Q₁‖ + ‖Q₂‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (16 * (K + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ by positivity
  filter_upwards [eventually_norm_floerJetCoeff_preglue_sub_le ω hJ hH hJp hHp hx hxp hu hv hux
    hdux hvx hdvx hε0, eventually_ge_atTop R₀] with R hclose hR
  obtain ⟨Q₀, hQ₀, hQ₀n⟩ := hR₀ R hR
  -- The coefficient field along `w_R` is within `2 ε` of the glued one, which is small enough
  -- for the right inverse `Q₀` of the glued operator.
  have hεQ : 2 * ε * ‖Q₀‖ ≤ 1 / 2 := by
    have h : 2 * ε * (4 * K) ≤ 1 / 2 := by
      rw [hε, show 2 * (1 / (16 * (K + 1))) * (4 * K) = K / (2 * (K + 1)) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      linarith
    exact (mul_le_mul_of_nonneg_left (hK ▸ hQ₀n) (by positivity)).trans h
  obtain ⟨Q, hQ, hQn⟩ := exists_rightInverse_jetOperator_comp_subtypeL_of_norm_sub_le
    (memLp_uncurry_gluedCoeff hMu hMv R).1
    (continuous_floerJetCoeff_preglue ω hJ hH hx hu hv R).aestronglyMeasurable
    (.of_forall hclose) hQ₀ hεQ
  exact ⟨Q, hQ, hQn.trans (by linarith)⟩

end TauCeti.SymplecticForm
