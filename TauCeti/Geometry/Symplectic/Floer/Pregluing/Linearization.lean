/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Gluing
public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
public import TauCeti.Geometry.Symplectic.Floer.Splicing
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# The linearized Floer operator along a pre-glued map

Let `(V, ω)` be a symplectic vector space, `H_t` a Hamiltonian and `J_t(y)` a family of
endomorphisms, both of period one in `t`, and let `x` be a one-periodic orbit of `X_{H_t}`. Let `u`
be a map converging to `x` in `C¹` as `s → +∞` and `v` a map converging to `x` in `C¹` as
`s → -∞`, uniformly in `t`. The pre-glued map `w_R` (`TauCeti.Floer.preglue`) is `u(s + R, t)` for
`s ≤ -1` and `v(s - R, t)` for `s ≥ 1`, and interpolates between them through `x` on the neck. This
file compares the linearized Floer operator `D_{w_R} ξ = ∂s ξ + J_t(w_R) ∂t ξ + C_{w_R} ξ` of the
cylindrical datum `K = H_t dt` (`TauCeti.SymplecticForm.floerLinearization`, with zeroth-order part
`C = TauCeti.SymplecticForm.floerLinearizationCoeff`) with the operators along the two translates
`u_R = u(· + R, ·)` and `v_R = v(· - R, ·)`.

* **Closeness of the coefficients.** For every `ε > 0` and every large `R`, the coefficients
  `J_t(w_R)` and `C_{w_R}` of `D_{w_R}` are within `ε` of those of `D_{u_R}` on the half-cylinder
  `s ≤ R / 2`, and within `ε` of those of `D_{v_R}` on `s ≥ -R / 2`
  (`TauCeti.SymplecticForm.eventually_norm_floerLinearizationCoeff_preglue_sub_le`). Away from the
  neck `w_R` is a translate, so the coefficients agree. On the rest of the half-cylinder both maps
  are `C¹`-close to the stationary cylinder over `x`. The coefficients are continuous functions of
  the time `t`, the value and the slice velocity `∂t w`, so they are close too. Periodicity in `t`
  makes the continuity uniform over all times, since the times then range over the compact
  interval `[0, 1]`.
* **The uniform estimate.** These are the closeness hypotheses of the splicing estimate
  `TauCeti.SymplecticForm.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_of_splice`,
  on the half-cylinders `s ≤ T` and `s ≥ -T` for the neck length `T = R / 2`, which grows with
  `R`. Hence if `D_u` and `D_v` satisfy the injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖D ξ‖²_{L²}`
  on `C²` maps of period one in `t` vanishing outside a strip, then for every large `R` so does
  `D_{w_R}`, with the constant `64 C`, independent of `R`
  (`eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearization_preglue`).
* **Comparison with the glued operator.** Gluing the positive end of the coefficient field on jets
  of `D_u` to the negative end of that of `D_v` along a neck of length `2 R` gives the glued
  coefficient field `TauCeti.gluedCoeff`, equal to that of `D_u` at `(s + R, t)` for `s < 0` and to
  that of `D_v` at `(s - R, t)` for `s ≥ 0`. For every `ε > 0` and every large `R`, the
  coefficient field of `D_{w_R}` is within `ε` of it at every point of the cylinder
  (`eventually_forall_norm_floerJetCoeff_preglue_sub_le`). Hence, when the coefficients of `D_u`
  and `D_v` are essentially bounded, so are those of `D_{w_R}`
  (`eventually_memLp_floerJetCoeff_preglue`), and on the Sobolev completion
  `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` (`TauCeti.SymplecticForm.floerSobolevOperator`) the
  operator `D_{w_R}` is within `ε` in operator norm of the operator of the glued coefficient field
  (`eventually_norm_floerSobolevOperator_preglue_sub_le`).
* **Uniformly bounded right inverses.** On the ends, the coefficient fields of `D_u` and `D_v`
  converge uniformly to that of the linearized operator along the stationary cylinder over `x`.
  So if the realizations of `D_u` and `D_v` have bounded linear right inverses `Q_u` and `Q_v`,
  the linear gluing estimate
  `TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff` gives the
  operators of the glued coefficient fields right inverses of norm at most `4 (‖Q_u‖ + ‖Q_v‖)`,
  and since `D_{w_R}` is close to them in operator norm, a Neumann series turns these into right
  inverses of `D_{w_R}` of norm at most `8 (‖Q_u‖ + ‖Q_v‖)`, for every large `R`
  (`eventually_exists_rightInverse_floerSobolevOperator_preglue`). In particular `D_{w_R}` is onto
  for every large `R` (`eventually_surjective_floerSobolevOperator_preglue`). A right inverse of
  the linearization along the approximate solution `w_R`, bounded independently of `R`, is the
  linear estimate on which the gluing of regular broken trajectories rests.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the linearized operator along a pre-glued curve and its uniformly bounded right inverse.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

open Filter Set Function ContinuousLinearMap

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
  {u v : ℝ × ℝ → V}

/-- The zeroth-order coefficient of the linearized Floer operator for the cylindrical datum
`K = H_t dt`, as a function of the time `t`, the value `y` and the slice velocity `η`. -/
private noncomputable def cylCoeff (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (t : ℝ) (y η : V) : V →L[ℝ] V :=
  (fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y) -
    (J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y)

/-- The zeroth-order coefficient of the linearized operator along `w` at `z`, for the datum
`K = H_t dt`, depends only on the time `z.2`, the value `w z` and the slice velocity `∂t w z`. -/
private theorem floerLinearizationCoeff_eq_cylCoeff (ω : SymplecticForm V)
    (J : ℝ → V → V →L[ℝ] V) (H : ℝ → V → ℝ) (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      cylCoeff ω J H z.2 (w z) (fderiv ℝ w z stdComplexLineImag) := by
  ext y
  simp [floerLinearizationCoeff_apply, cylCoeff]

/-- **The coefficients near an orbit.** For a continuous loop `x` and a compact set `T` of times,
the coefficients `J_t(y)` and `C(t, y, η)` of the linearized operator are uniformly close to their
values at the jet `(x t, X_{H_t}(x t))` of `x`, at every jet `(y, η)` close enough to it. -/
private theorem exists_pos_forall_cylCoeff_sub_lt_of_mem (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) {T : Set ℝ}
    (hT : IsCompact T) (hx : ContinuousOn x T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ T, ∀ y η, ‖y - x t‖ < δ → ‖η - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
      ‖J t y - J t (x t)‖ < ε ∧
        ‖cylCoeff ω J H t y η -
          cylCoeff ω J H t (x t) (ω.hamiltonianVectorField (H t) (x t))‖ < ε := by
  -- The coefficient fields `X_H`, `dJ` and `J dX_H` are continuous in `(t, y)`.
  have hX := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hdJ := continuous_fderiv_slice_right (f := fun t y ↦ J t y) hJ
  have hJS := hJ.continuous.clm_comp
    (continuous_fderiv_slice_right (f := fun t ↦ ω.hamiltonianVectorField (H t)) hX)
  -- `dJ` is bounded along the orbit, by `M`, and hence by `M' = |M| + 1` near it.
  obtain ⟨M, hM⟩ := (hT.image_of_continuousOn
    ((continuousOn_id' _).prodMk hx)).exists_bound_of_continuousOn hdJ.continuousOn
  set M' := |M| + 1
  have hM'0 : 0 < M' := by positivity
  set ε' := ε / (4 * M')
  obtain ⟨δ₁, hδ₁, h₁⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hJ.continuous.continuousAt) hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hJS.continuousAt)
    (half_pos hε)
  obtain ⟨δ₃, hδ₃, h₃⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hX.continuous.continuousAt)
    (by positivity : 0 < ε')
  obtain ⟨δ₄, hδ₄, h₄⟩ := hT.exists_pos_forall_dist_lt hx (fun _ _ ↦ hdJ.continuousAt) one_pos
  simp only [dist_eq_norm] at h₁ h₂ h₃ h₄
  refine ⟨min (min δ₁ δ₂) (min (min δ₃ δ₄) ε'), by positivity, fun t ht y η hy hη ↦ ?_⟩
  simp only [lt_min_iff] at hy hη
  obtain ⟨e₂, e₃, e₄, hMt⟩ := And.intro (h₂ t ht y hy.1.2) <| And.intro (h₃ t ht y hy.2.1.1) <|
    And.intro (h₄ t ht y hy.2.1.2) (hM _ (mem_image_of_mem _ ht))
  simp only [uncurry_apply_pair] at e₂ e₃ e₄ hMt
  refine ⟨h₁ t ht y hy.1.1, ?_⟩
  -- The term `dJ(y) (η - X(y))` is at most `M' ‖η - X(y)‖ ≤ ε / 2`, and the term `J(y) dX(y)` is
  -- within `ε / 2` of its value along `x`.
  have hdJy : ‖fderiv ℝ (J t) y‖ ≤ M' := by
    linarith [norm_le_insert' (fderiv ℝ (J t) y) (fderiv ℝ (J t) (x t)), le_abs_self M]
  have hd : ‖η - ω.hamiltonianVectorField (H t) y‖ ≤ 2 * ε' := by
    linarith [norm_sub_le_norm_sub_add_norm_sub η (ω.hamiltonianVectorField (H t) (x t))
      (ω.hamiltonianVectorField (H t) y), norm_sub_rev (ω.hamiltonianVectorField (H t) (x t))
      (ω.hamiltonianVectorField (H t) y)]
  have hF : ‖(fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y)‖ ≤ ε / 2 := by
    calc _ ≤ ‖(fderiv ℝ (J t) y).flip‖ * ‖η - ω.hamiltonianVectorField (H t) y‖ := le_opNorm _ _
      _ ≤ M' * (2 * ε') := by
          rw [opNorm_flip]
          exact mul_le_mul hdJy hd (norm_nonneg _) hM'0.le
      _ = ε / 2 := by simp only [ε']; field_simp; ring
  have hc : cylCoeff ω J H t y η - cylCoeff ω J H t (x t) (ω.hamiltonianVectorField (H t) (x t)) =
      (fderiv ℝ (J t) y).flip (η - ω.hamiltonianVectorField (H t) y) -
        ((J t y).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) y) -
          (J t (x t)).comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))) := by
    simp only [cylCoeff, sub_self, map_zero]
    abel
  rw [hc]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- **Closeness of the coefficients near a periodic orbit.** For `J` and `H` of period one in `t`
and a continuous loop `x` of period one, the coefficients `J_t(y)` and `C(t, y, η)` of the
linearized operator are uniformly close at any two jets `(y, η)`, `(y', η')` close enough to the jet
`(x t, X_{H_t}(x t))` of `x`, at every time `t`. -/
private theorem exists_pos_forall_cylCoeff_sub_lt (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : Continuous x) (hxp : Periodic x 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t y y' η η', ‖y - x t‖ < δ → ‖y' - x t‖ < δ →
      ‖η - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
      ‖η' - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
      ‖J t y - J t y'‖ < ε ∧ ‖cylCoeff ω J H t y η - cylCoeff ω J H t y' η'‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_cylCoeff_sub_lt_of_mem ω hJ hH
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    hx.continuousOn (half_pos hε)
  refine ⟨δ, hδ, fun t y y' η η' hy hy' hη hη' ↦ ?_⟩
  -- Reduce to a time `t' ∈ [0, 1)`, where `J`, `H` and `x` take the same values.
  obtain ⟨t', ht', he⟩ := (show Periodic (fun t ↦ (J t, H t, x t)) 1 from fun t ↦ by
    simp only [hJp t, hHp t, hxp t]).exists_mem_Ico₀ one_pos t
  simp only [Prod.mk.injEq] at he
  obtain ⟨hJt, hHt, hxt⟩ := he
  have hc (y η : V) : cylCoeff ω J H t y η = cylCoeff ω J H t' y η := by
    simp only [cylCoeff, hJt, hHt]
  rw [hJt, hc, hc]
  simp only [hxt, hHt] at hy hy' hη hη'
  obtain ⟨e₁, e₂⟩ := h t' (Ico_subset_Icc_self ht') y η hy hη
  obtain ⟨e₁', e₂'⟩ := h t' (Ico_subset_Icc_self ht') y' η' hy' hη'
  refine ⟨(norm_sub_le_norm_sub_add_norm_sub _ (J t' (x t')) _).trans_lt ?_,
    (norm_sub_le_norm_sub_add_norm_sub _
      (cylCoeff ω J H t' (x t') (ω.hamiltonianVectorField (H t') (x t'))) _).trans_lt ?_⟩
  · rw [norm_sub_rev (J t' (x t'))]
    linarith
  · rw [norm_sub_rev (cylCoeff ω J H t' (x t') _)]
    linarith

omit [FiniteDimensional ℝ V] in
/-- **The jet of the pre-glued map on the neck.** If the map `u` is within `δ` of the loop `x` at
`(s + R, t)`, and `v` at `(s - R, t)`, both in value and in derivative measured against the
derivative `(σ, τ) ↦ τ x'` of the stationary cylinder, then at `z = (s, t)` the value and the slice
velocity of the pre-glued map at `z` are within `2 (B + 1) δ` of `x t` and `x'`, where `B` bounds
the derivative of the cutoff, and so are those of the translates `u(· + R, ·)` and `v(· - R, ·)`. -/
private theorem norm_preglue_sub_lt_and_norm_fderiv_preglue_sub_lt {R δ B : ℝ} {z : ℝ × ℝ}
    {x' : V} (hB : ∀ s, |deriv pregluingCutoff s| ≤ B) (hB0 : 0 ≤ B) (hx : HasDerivAt x x' z.2)
    (hud : DifferentiableAt ℝ u (z.1 + R, z.2)) (hvd : DifferentiableAt ℝ v (z.1 - R, z.2))
    (ha : dist (x z.2) (u (z.1 + R, z.2)) < δ)
    (hb : dist ((snd ℝ ℝ ℝ).smulRight x') (fderiv ℝ u (z.1 + R, z.2)) < δ)
    (hc : dist (x z.2) (v (z.1 - R, z.2)) < δ)
    (hd : dist ((snd ℝ ℝ ℝ).smulRight x') (fderiv ℝ v (z.1 - R, z.2)) < δ) :
    (‖preglue x u v R z - x z.2‖ < 2 * (B + 1) * δ ∧
      ‖fderiv ℝ (preglue x u v R) z stdComplexLineImag - x'‖ < 2 * (B + 1) * δ) ∧
    (‖u (z + (R, 0)) - x z.2‖ < 2 * (B + 1) * δ ∧
      ‖fderiv ℝ (fun p ↦ u (p + (R, 0))) z stdComplexLineImag - x'‖ < 2 * (B + 1) * δ) ∧
    (‖v (z - (R, 0)) - x z.2‖ < 2 * (B + 1) * δ ∧
      ‖fderiv ℝ (fun p ↦ v (p - (R, 0))) z stdComplexLineImag - x'‖ < 2 * (B + 1) * δ) := by
  have hzu : (z.1 + R, z.2) = z + (R, 0) := by ext <;> simp
  have hzv : (z.1 - R, z.2) = z - (R, 0) := by ext <;> simp
  rw [hzu] at hud ha hb
  rw [hzv] at hvd hc hd
  rw [dist_comm, dist_eq_norm] at ha hb hc hd
  have hδ : 0 < δ := (norm_nonneg _).trans_lt ha
  have hδB : δ ≤ 2 * (B + 1) * δ := by nlinarith
  rw [fderiv_comp_add_right, fderiv_comp_sub]
  refine ⟨⟨norm_preglue_sub_le.trans_lt (by nlinarith), ?_⟩,
    ⟨ha.trans_le hδB, (ContinuousLinearMap.norm_apply_stdComplexLineImag_sub_le _ _).trans_lt
      (hb.trans_le hδB)⟩,
    ⟨hc.trans_le hδB, (ContinuousLinearMap.norm_apply_stdComplexLineImag_sub_le _ _).trans_lt
      (hd.trans_le hδB)⟩⟩
  refine (ContinuousLinearMap.norm_apply_stdComplexLineImag_sub_le _ _).trans_lt
    ((norm_fderiv_preglue_sub_le hx hud hvd).trans_lt ?_)
  have h₁ := mul_le_mul (hB z.1) ha.le (norm_nonneg _) hB0
  have h₂ := mul_le_mul (hB (-z.1)) hc.le (norm_nonneg _) hB0
  nlinarith

/-- **The coefficients along the pre-glued map.** Let `J` be a `C¹` family and `H` a `C²`
Hamiltonian, both of period one in `t`, and let `x` be an orbit of `X_{H_t}` of period one. Let
`u` be differentiable on a positive end, converging to `x` in `C¹` as `s → +∞`, and `v`
differentiable on a negative end, converging to `x` in `C¹` as `s → -∞`, both uniformly in `t`.
Then for every `ε > 0` and every large `R`, the coefficients `J_t(w_R)` and `C_{w_R}` of the
linearized operator along the pre-glued map `w_R`, for the datum `K = H_t dt`, are within `ε`
of those along the translate `u(· + R, ·)` on the half-cylinder `s ≤ R / 2`, and within `ε` of
those along the translate `v(· - R, ·)` on `s ≥ -R / 2`. -/
theorem eventually_norm_floerLinearizationCoeff_preglue_sub_le (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hud : ∀ᶠ s in atTop, ∀ t, DifferentiableAt ℝ u (s, t))
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvd : ∀ᶠ s in atBot, ∀ t, DifferentiableAt ℝ v (s, t))
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop,
      (∀ z : ℝ × ℝ, z.1 ≤ R / 2 →
        ‖J z.2 (preglue x u v R z) - J z.2 (u (z + (R, 0)))‖ ≤ ε ∧
        ‖ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
            (preglue x u v R) z -
          ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
            (fun p ↦ u (p + (R, 0))) z‖ ≤ ε) ∧
      (∀ z : ℝ × ℝ, -(R / 2) ≤ z.1 →
        ‖J z.2 (preglue x u v R z) - J z.2 (v (z - (R, 0)))‖ ≤ ε ∧
        ‖ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
            (preglue x u v R) z -
          ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
            (fun p ↦ v (p - (R, 0))) z‖ ≤ ε) := by
  set X : ℝ → V := fun t ↦ ω.hamiltonianVectorField (H t) (x t)
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ, hδ, hjet⟩ := exists_pos_forall_cylCoeff_sub_lt ω hJ hH hJp hHp hxc hxp hε
  obtain ⟨B, hB⟩ := exists_abs_deriv_pregluingCutoff_le
  set B' := max B 0
  have hB' (s : ℝ) : |deriv pregluingCutoff s| ≤ B' := (hB s).trans (le_max_left _ _)
  have hB'0 : 0 ≤ B' := le_max_right _ _
  -- On the far ends, `u` and `v` are `δ'`-close to `x` in `C¹`.
  set δ' := δ / (2 * (B' + 1))
  have hδ' : 0 < δ' := by positivity
  have hδδ' : 2 * (B' + 1) * δ' = δ := by simp only [δ']; field_simp
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (hud.and ((Metric.tendstoUniformly_iff.1 hux δ' hδ').and
    (Metric.tendstoUniformly_iff.1 hdux δ' hδ')))
  obtain ⟨s₂, hs₂⟩ := eventually_atBot.1 (hvd.and ((Metric.tendstoUniformly_iff.1 hvx δ' hδ').and
    (Metric.tendstoUniformly_iff.1 hdvx δ' hδ')))
  filter_upwards [eventually_ge_atTop (2 * s₁), eventually_ge_atTop (-(2 * s₂)),
    eventually_ge_atTop 2] with R hR₁ hR₂ hR₃
  -- On the neck `|s| ≤ R / 2`, the jets of `w_R`, `u(· + R, ·)` and `v(· - R, ·)` are `δ`-close to
  -- the jet of `x`.
  have hneck (z : ℝ × ℝ) (hz₁ : -(R / 2) ≤ z.1) (hz₂ : z.1 ≤ R / 2) :
      (‖preglue x u v R z - x z.2‖ < δ ∧
        ‖fderiv ℝ (preglue x u v R) z stdComplexLineImag - X z.2‖ < δ) ∧
      (‖u (z + (R, 0)) - x z.2‖ < δ ∧
        ‖fderiv ℝ (fun p ↦ u (p + (R, 0))) z stdComplexLineImag - X z.2‖ < δ) ∧
      (‖v (z - (R, 0)) - x z.2‖ < δ ∧
        ‖fderiv ℝ (fun p ↦ v (p - (R, 0))) z stdComplexLineImag - X z.2‖ < δ) := by
    obtain ⟨hud', hu', hdu'⟩ := hs₁ (z.1 + R) (by linarith)
    obtain ⟨hvd', hv', hdv'⟩ := hs₂ (z.1 - R) (by linarith)
    rw [← hδδ']
    exact norm_preglue_sub_lt_and_norm_fderiv_preglue_sub_lt hB' hB'0 (hx z.2) (hud' z.2)
      (hvd' z.2) (hu' z.2) (hdu' z.2) (hv' z.2) (hdv' z.2)
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · simp only [floerLinearizationCoeff_eq_cylCoeff]
    by_cases hz₁ : z.1 < -1
    · -- Off the neck, `w_R` is the translate of `u`.
      rw [preglue_of_le_neg_one hz₁.le, fderiv_preglue_of_lt_neg_one hz₁, fderiv_comp_add_right]
      simp [hε.le]
    · obtain ⟨⟨hw, hdw⟩, ⟨hu, hdu⟩, -⟩ := hneck z (by linarith) hz
      exact (hjet z.2 _ _ _ _ hw hu hdw hdu).imp le_of_lt le_of_lt
  · simp only [floerLinearizationCoeff_eq_cylCoeff]
    by_cases hz₁ : 1 < z.1
    · -- Off the neck, `w_R` is the translate of `v`.
      rw [preglue_of_one_le hz₁.le, fderiv_preglue_of_one_lt hz₁, fderiv_comp_sub]
      simp [hε.le]
    · obtain ⟨⟨hw, hdw⟩, -, ⟨hv, hdv⟩⟩ := hneck z hz (by linarith)
      exact (hjet z.2 _ _ _ _ hw hv hdw hdv).imp le_of_lt le_of_lt

/-- **The uniform estimate along the pre-glued map.** Under the hypotheses of
`TauCeti.SymplecticForm.eventually_norm_floerLinearizationCoeff_preglue_sub_le`, with `u` and `v`
of class `C¹`, suppose that the linearized operators `D_u` and `D_v` of the datum `K = H_t dt`
satisfy the injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖D ξ‖²_{L²}` on `C²` maps of period one in `t`
vanishing outside a strip `(a, b) × ℝ`, the norms being over `[a, b] × [0, 1]`. Then for every large
gluing parameter `R`, the linearized operator along the pre-glued map `w_R` satisfies the
injectivity estimate with the constant `64 C`, independent of `R`. -/
theorem eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearization_preglue
    (ω : SymplecticForm V) (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H))
    (hJp : Periodic J 1) (hHp : Periodic H 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {C : ℝ} (hC : 0 ≤ C)
    (hestu : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
            ‖ω.floerLinearization (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u ξ z‖ ^ 2)
    (hestv : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
            ‖ω.floerLinearization (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v ξ z‖ ^ 2) :
    ∀ᶠ R in atTop, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
            ‖ω.floerLinearization (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
              (preglue x u v R) ξ z‖ ^ 2 := by
  -- The comparison constant `ε` with `8 C ε² ≤ 1`.
  set ε := 1 / (8 * (C + 1))
  have hε : 0 < ε := by positivity
  have h8 : 8 * C * ε ^ 2 ≤ 1 := by
    simp only [ε]
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hcl := ω.eventually_norm_floerLinearizationCoeff_preglue_sub_le hJ hH hJp hHp hx hxp
    (Eventually.of_forall fun _ _ ↦ hu.differentiable one_ne_zero _) hux hdux
    (Eventually.of_forall fun _ _ ↦ hv.differentiable one_ne_zero _) hvx hdvx hε
  -- Regularity of the data and of the three maps.
  have hx₁ : ContDiff ℝ 1 x := contDiff_one_of_hasDerivAt
    (X := fun t ↦ ω.hamiltonianVectorField (H t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
  have hJ' : ContDiff ℝ 1 (uncurry fun (p : ℝ × ℝ) ↦ J p.2) :=
    hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hKs : ContDiff ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) := contDiff_const
  have hKt : ContDiff ℝ 2 (uncurry fun (p : ℝ × ℝ) ↦ H p.2) :=
    hH.comp (contDiff_fst.snd.prodMk contDiff_snd)
  filter_upwards [hcl, eventually_ge_atTop (16 * (C + 1))] with R ⟨h₁, h₂⟩ hR
  intro ξ hξ hper a b hab hξ₀
  have hT : 0 < R / 2 := by linarith
  have hCT : 64 * C ≤ (R / 2) ^ 2 := by nlinarith
  -- The injectivity estimates of the two translates.
  have hest₁ := fun ⦃ξ : ℝ × ℝ → V⦄ (hξ : ContDiff ℝ 2 ξ) hper ⦃a b : ℝ⦄ (hab : a ≤ b) hξ₀ ↦
    ω.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_comp_add_right R hestu hξ hper
      hab hξ₀
  have hest₂ := fun ⦃ξ : ℝ × ℝ → V⦄ (hξ : ContDiff ℝ 2 ξ) hper ⦃a b : ℝ⦄ (hab : a ≤ b) hξ₀ ↦
    ω.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_comp_add_right (-R) hestv hξ hper
      hab hξ₀
  have hvR : (fun w : ℝ × ℝ ↦ v (w + (-R, 0))) = fun p ↦ v (p - (R, 0)) :=
    funext fun p ↦ by rw [sub_eq_add_neg, Prod.neg_mk, neg_zero]
  simp only [Prod.snd_add, add_zero] at hest₁ hest₂
  rw [hvR] at hest₂
  exact ω.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_of_splice
    (u₁ := fun p ↦ u (p + (R, 0))) (u₂ := fun p ↦ v (p - (R, 0)))
    (fun _ ↦ hJ'.contDiffAt) (fun _ ↦ hKs.contDiffAt) (fun _ ↦ hKt.contDiffAt)
    (contDiff_preglue hx₁ hu hv) (fun _ ↦ hJ'.contDiffAt) (fun _ ↦ hKs.contDiffAt)
    (fun _ ↦ hKt.contDiffAt) (hu.comp (contDiff_id.add contDiff_const)) (fun _ ↦ hJ'.contDiffAt)
    (fun _ ↦ hKs.contDiffAt) (fun _ ↦ hKt.contDiffAt) (hv.comp (contDiff_id.sub contDiff_const))
    hC hT hCT h8 (fun z hz _ ↦ (h₁ z hz).1) (fun z hz _ ↦ (h₁ z hz).2) (fun z hz _ ↦ (h₂ z hz).1)
    (fun z hz _ ↦ (h₂ z hz).2) hest₁ hest₂ hξ hper hab hξ₀

/-! ### Uniformly bounded right inverses along the pre-glued map -/

section RightInverse

open MeasureTheory CylinderSobolev
open StripSobolev (stripMeasure)
open scoped ENNReal

/-- The coefficient field on jets of the linearized operator of the datum `K = H_t dt` along `w`,
through the time, the value and the slice velocity of `w`. -/
private theorem floerJetCoeff_eq_cylCoeff (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      firstOrderJetCoeff (J z.2 (w z))
        (cylCoeff ω J H z.2 (w z) (fderiv ℝ w z stdComplexLineImag)) := by
  simp only [floerJetCoeff_def, floerLinearizationCoeff_eq_cylCoeff]

/-- For the datum `K = H_t dt`, the coefficient field along the translate `w(· + R, ·)` at `(s, t)`
is that along `w` at `(s + R, t)`. -/
private theorem floerJetCoeff_comp_add_eq (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (w : ℝ × ℝ → V) (R s t : ℝ) :
    ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (fun p ↦ w (p + (R, 0)))
        (s, t) =
      ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w (s + R, t) := by
  simpa using ω.floerJetCoeff_comp_add_right (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w
    (R, 0) (s, t)

/-- For the datum `K = H_t dt`, the coefficient field along the translate `w(· - R, ·)` at `(s, t)`
is that along `w` at `(s - R, t)`. -/
private theorem floerJetCoeff_comp_sub_eq (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (w : ℝ × ℝ → V) (R s t : ℝ) :
    ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (fun p ↦ w (p - (R, 0)))
        (s, t) =
      ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w (s - R, t) := by
  have hw : (fun p ↦ w (p - (R, 0))) = fun p ↦ w (p + (-R, 0)) :=
    funext fun p ↦ by rw [sub_eq_add_neg, Prod.neg_mk, neg_zero]
  simpa [hw, ← sub_eq_add_neg] using ω.floerJetCoeff_comp_add_right (fun p ↦ J p.2)
    (fun _ _ ↦ 0) (fun p ↦ H p.2) w (-R, 0) (s, t)

/-- **The coefficients on an end converge to those along the orbit.** If `u` converges in `C¹` to
the stationary cylinder over the orbit `x` along a filter `l` of `s`, uniformly in `t`, then the
coefficient field on jets of the linearized operator along `u` at `(s, t)` converges along `l`,
uniformly in `t ∈ [0, 1]`, to that along the stationary cylinder. -/
private theorem tendstoUniformlyOn_curry_floerJetCoeff (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : Continuous x) (hxp : Periodic x 1) {l : Filter ℝ}
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x l)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) l) :
    TendstoUniformlyOn
      (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
      (fun t ↦ firstOrderJetCoeff (J t (x t))
        (cylCoeff ω J H t (x t) (ω.hamiltonianVectorField (H t) (x t)))) l (Icc 0 1) := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hjet⟩ := exists_pos_forall_cylCoeff_sub_lt ω hJ hH hJp hHp hx hxp (half_pos hε)
  filter_upwards [Metric.tendstoUniformly_iff.1 hux δ hδ,
    Metric.tendstoUniformly_iff.1 hdux δ hδ] with s hu hdu t _
  have hy : ‖u (s, t) - x t‖ < δ := by
    rw [← dist_eq_norm, dist_comm]
    exact hu t
  have hη : ‖fderiv ℝ u (s, t) stdComplexLineImag - ω.hamiltonianVectorField (H t) (x t)‖ < δ :=
    (ContinuousLinearMap.norm_apply_stdComplexLineImag_sub_le _ _).trans_lt (by
      rw [← dist_eq_norm, dist_comm]
      exact hdu t)
  obtain ⟨hJt, hC⟩ := hjet t (u (s, t)) (x t) _ (ω.hamiltonianVectorField (H t) (x t)) hy
    (by simpa using hδ) hη (by simpa using hδ)
  rw [dist_eq_norm, Function.curry_apply, floerJetCoeff_eq_cylCoeff, norm_sub_rev]
  dsimp only
  exact (norm_firstOrderJetCoeff_sub_le _ _ _ _).trans_lt (by linarith)

/-- **The coefficients along the pre-glued map are close to the glued ones.** Under the hypotheses
of `TauCeti.SymplecticForm.eventually_norm_floerLinearizationCoeff_preglue_sub_le`, for every
`ε > 0` and every large `R`, at every point of the cylinder, the coefficient field on jets of the
linearized operator along the pre-glued map `w_R`, for the datum `K = H_t dt`, is within `ε` of the
glued coefficient field `TauCeti.gluedCoeff` of the linearized operators along `u` and `v`: that
along `u` at `(s + R, t)` for `s < 0`, and that along `v` at `(s - R, t)` for `s ≥ 0`. -/
theorem eventually_forall_norm_floerJetCoeff_preglue_sub_le (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hud : ∀ᶠ s in atTop, ∀ t, DifferentiableAt ℝ u (s, t))
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvd : ∀ᶠ s in atBot, ∀ t, DifferentiableAt ℝ v (s, t))
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop, ∀ z : ℝ × ℝ,
      ‖ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z -
        Function.uncurry (gluedCoeff
          (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
          (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v))
          R) z‖ ≤ ε := by
  filter_upwards [ω.eventually_norm_floerLinearizationCoeff_preglue_sub_le hJ hH hJp hHp hx hxp
    hud hux hdux hvd hvx hdvx (half_pos hε), eventually_ge_atTop 0] with R ⟨h₁, h₂⟩ hR ⟨s, t⟩
  rw [Function.uncurry_apply_pair]
  rcases lt_or_ge s 0 with hs | hs
  · -- For `s < 0` the glued coefficient is that along the translate `u(· + R, ·)`.
    obtain ⟨hJt, hC⟩ := h₁ (s, t) (by dsimp only; linarith)
    rw [gluedCoeff_of_neg _ _ _ hs, Function.curry_apply, ← floerJetCoeff_comp_add_eq,
      floerJetCoeff_def, floerJetCoeff_def]
    exact (norm_firstOrderJetCoeff_sub_le _ _ _ _).trans (by linarith)
  · -- For `s ≥ 0` the glued coefficient is that along the translate `v(· - R, ·)`.
    obtain ⟨hJt, hC⟩ := h₂ (s, t) (by dsimp only; linarith)
    rw [gluedCoeff_of_nonneg _ _ _ hs, Function.curry_apply, ← floerJetCoeff_comp_sub_eq,
      floerJetCoeff_def, floerJetCoeff_def]
    exact (norm_firstOrderJetCoeff_sub_le _ _ _ _).trans (by linarith)

/-- The coefficient field on jets of the linearized operator of the datum `K = H_t dt` along a `C¹`
map is continuous. -/
private theorem continuous_floerJetCoeff_snd (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) {w : ℝ × ℝ → V}
    (hw : ContDiff ℝ 1 w) :
    Continuous (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w) :=
  ω.continuous_floerJetCoeff
    (fun _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    (fun _ ↦ contDiff_const.contDiffAt)
    (fun _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt) hw

/-- **The coefficients along the pre-glued map are bounded.** Let `J` be a `C¹` family and `H` a
`C²` Hamiltonian, both of period one in `t`, and let `x` be an orbit of `X_{H_t}` of period one.
Let `u` and `v` be `C¹` maps converging to `x` in `C¹`, uniformly in `t`, as `s → +∞` and as
`s → -∞` respectively, along which the coefficients of the linearized operators of the datum
`K = H_t dt` are essentially bounded. Then for every large `R` the coefficients of the linearized
operator along the pre-glued map `w_R` are essentially bounded. -/
theorem eventually_memLp_floerJetCoeff_preglue (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    (hMu : MemLp (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u) ∞
      stripMeasure)
    (hMv : MemLp (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v) ∞
      stripMeasure) :
    ∀ᶠ R in atTop, MemLp
      (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R)) ∞
        stripMeasure := by
  have hx₁ : ContDiff ℝ 1 x := contDiff_one_of_hasDerivAt
    (X := fun t ↦ ω.hamiltonianVectorField (H t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
  filter_upwards [ω.eventually_forall_norm_floerJetCoeff_preglue_sub_le hJ hH hJp hHp hx hxp
    (Eventually.of_forall fun _ _ ↦ hu.differentiable one_ne_zero _) hux hdux
    (Eventually.of_forall fun _ _ ↦ hv.differentiable one_ne_zero _) hvx hdvx one_pos] with R hR
  -- The coefficient field is continuous and within `1` of the bounded glued coefficient field.
  obtain ⟨-, hGB⟩ := memLp_uncurry_gluedCoeff hMu hMv R
  set B := lpNorm (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u) ∞
    stripMeasure + lpNorm (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v) ∞
      stripMeasure
  refine memLp_top_of_bound
    (continuous_floerJetCoeff_snd ω hJ hH (contDiff_preglue hx₁ hu hv)).aestronglyMeasurable
    (B + 1) (hGB.mono fun z hz ↦ ?_)
  exact (norm_le_norm_add_norm_sub' _ _).trans (by linarith [hR z])

/-- **The linearized operator along the pre-glued map is close to the glued operator.** Under the
hypotheses of `TauCeti.SymplecticForm.eventually_memLp_floerJetCoeff_preglue`, for every `ε > 0`
and every large `R`, the realization `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized
operator along the pre-glued map `w_R`, for the datum `K = H_t dt`, is within `ε` in operator norm
of the realization of the first-order operator of the glued coefficient field `TauCeti.gluedCoeff`
of the linearized operators along `u` and `v`. -/
theorem eventually_norm_floerSobolevOperator_preglue_sub_le (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    (hMu : MemLp (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u) ∞
      stripMeasure)
    (hMv : MemLp (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v) ∞
      stripMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop,
      ‖ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) -
        (jetOperator stripMeasure (Function.uncurry (gluedCoeff
          (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
          (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v))
          R))).comp (H1 V).subtypeL‖ ≤ ε := by
  filter_upwards [ω.eventually_memLp_floerJetCoeff_preglue hJ hH hJp hHp hx hxp hu hv hux hdux
    hvx hdvx hMu hMv, ω.eventually_forall_norm_floerJetCoeff_preglue_sub_le hJ hH hJp hHp hx hxp
    (Eventually.of_forall fun _ _ ↦ hu.differentiable one_ne_zero _) hux hdux
    (Eventually.of_forall fun _ _ ↦ hv.differentiable one_ne_zero _) hvx hdvx hε] with R hM hR
  have hG := (memLp_uncurry_gluedCoeff hMu hMv R).1
  -- The operators differ by at most the essential supremum of the difference of the coefficients.
  have hsup : (eLpNorm (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
      (preglue x u v R) - Function.uncurry (gluedCoeff
        (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u))
        (Function.curry (ω.floerJetCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v))
        R)) ∞ stripMeasure).toReal ≤ ε := by
    rw [eLpNorm_exponent_top (hM.sub hG).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le
      (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hR))
  rw [floerSobolevOperator_def, ← ContinuousLinearMap.sub_comp]
  refine (opNorm_comp_le _ _).trans ?_
  calc _ ≤ ε * 1 := mul_le_mul ((norm_jetOperator_sub_le hM hG).trans hsup)
          (Submodule.norm_subtypeL_le _) (by positivity) hε.le
    _ = ε := mul_one ε

/-- **Uniformly bounded right inverses along the pre-glued map.** Let `J` be a `C¹` family of
endomorphisms and `H` a `C²` Hamiltonian, both of period one in `t`, and let `x` be an orbit of
`X_{H_t}` of period one. Let `u` and `v` be `C¹` maps converging to `x` in `C¹`, uniformly in `t`,
as `s → +∞` and as `s → -∞` respectively. Suppose that the realizations of the linearized operators
`D_u` and `D_v` of the datum `K = H_t dt`, from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, V)`, have
bounded linear right inverses `Q_u` and `Q_v`, as they do when `u` and `v` are regular Floer
trajectories. Then for every large gluing parameter `R`, the realization of the linearized operator
`D_{w_R}` along the pre-glued map `w_R` has a bounded linear right inverse of norm at most
`8 (‖Q_u‖ + ‖Q_v‖)`, independent of `R`. -/
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
    {Qu Qv : Lp V 2 stripMeasure →L[ℝ] H1 V}
    (hQu : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u).comp Qu =
      ContinuousLinearMap.id ℝ _)
    (hQv : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v).comp Qv =
      ContinuousLinearMap.id ℝ _) :
    ∀ᶠ R in atTop, ∃ Q : Lp V 2 stripMeasure →L[ℝ] H1 V,
      (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglue x u v R)).comp Q = ContinuousLinearMap.id ℝ _ ∧
        ‖Q‖ ≤ 8 * (‖Qu‖ + ‖Qv‖) := by
  -- If `L²` is trivial, so is every operator into it.
  rcases subsingleton_or_nontrivial (Lp V 2 stripMeasure) with hL | hL
  · exact Eventually.of_forall fun R ↦ ⟨0, ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _,
      (norm_zero (E := Lp V 2 stripMeasure →L[ℝ] H1 V)).trans_le (by positivity)⟩
  have hMu := memLp_floerJetCoeff_of_comp_eq_id ω hQu
  have hMv := memLp_floerJetCoeff_of_comp_eq_id ω hQv
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  -- The operators of the glued coefficient fields have right inverses bounded by `4 K`.
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff hMu hMv
    (tendstoUniformlyOn_curry_floerJetCoeff ω hJ hH hJp hHp hxc hxp hux hdux)
    (tendstoUniformlyOn_curry_floerJetCoeff ω hJ hH hJp hHp hxc hxp hvx hdvx)
    (by rw [← floerSobolevOperator_def]; exact hQu) (by rw [← floerSobolevOperator_def]; exact hQv)
  obtain ⟨K, hK⟩ : ∃ K, K = ‖Qu‖ + ‖Qv‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  filter_upwards [eventually_ge_atTop R₀, ω.eventually_norm_floerSobolevOperator_preglue_sub_le hJ
    hH hJp hHp hx hxp hu hv hux hdux hvx hdvx hMu hMv (by positivity : 0 < 1 / (8 * (K + 1)))]
    with R hR hS
  obtain ⟨Q, hQ, hQn⟩ := hR₀ R hR
  rw [← hK] at hQn
  -- `D_{w_R} Q` is within `1 / 2` of the identity, and a Neumann series corrects `Q`.
  have hE : ‖(ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
      (preglue x u v R)).comp Q - ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2 := by
    rw [← hQ, ← ContinuousLinearMap.sub_comp]
    refine (opNorm_comp_le _ _).trans ?_
    calc _ ≤ 1 / (8 * (K + 1)) * (4 * K) := mul_le_mul hS hQn (by positivity) (by positivity)
      _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith
  obtain ⟨Q', hQ', hQ'n⟩ :=
    ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_le_half _ Q hE
  exact ⟨Q', hQ', hK ▸ hQ'n.trans (by linarith)⟩

/-- **The linearized operator along the pre-glued map is onto.** Under the hypotheses of
`TauCeti.SymplecticForm.eventually_exists_rightInverse_floerSobolevOperator_preglue`, for every
large gluing parameter `R` the realization `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized
operator along the pre-glued map `w_R` is onto. -/
theorem eventually_surjective_floerSobolevOperator_preglue (ω : SymplecticForm V)
    (hJ : ContDiff ℝ 1 (uncurry J)) (hH : ContDiff ℝ 2 (uncurry H)) (hJp : Periodic J 1)
    (hHp : Periodic H 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t))
      (fun t ↦ (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))) atBot)
    {Qu Qv : Lp V 2 stripMeasure →L[ℝ] H1 V}
    (hQu : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u).comp Qu =
      ContinuousLinearMap.id ℝ _)
    (hQv : (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v).comp Qv =
      ContinuousLinearMap.id ℝ _) :
    ∀ᶠ R in atTop, Surjective
      (ω.floerSobolevOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R)) := by
  filter_upwards [ω.eventually_exists_rightInverse_floerSobolevOperator_preglue hJ hH hJp hHp hx
    hxp hu hv hux hdux hvx hdvx hQu hQv] with R ⟨Q, hQ, _⟩
  exact fun f ↦ ⟨Q f, by simpa using DFunLike.congr_fun hQ f⟩

end RightInverse

end TauCeti.SymplecticForm
