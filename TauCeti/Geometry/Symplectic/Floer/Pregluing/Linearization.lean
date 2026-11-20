/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.Splicing
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
  have hdJ := (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ J p.1 y) (g := Prod.snd) (n := 0)
    (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  have hJS := hJ.continuous.clm_comp (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦
    ω.hamiltonianVectorField (H p.1) y) (g := Prod.snd) (n := 0)
    (hX.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
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

end TauCeti.SymplecticForm
