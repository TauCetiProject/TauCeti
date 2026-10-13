/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.FourierMultiplier
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Hessian
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Calderón–Zygmund estimates for the Laplacian

The second directional derivatives of a Schwartz function on `ℝⁿ` are controlled in
`Lᵖ`, `1 < p < ∞`, by its Laplacian.  The proof identifies `∂_v ∂_w Δ⁻¹` with the
Fourier multiplier `TauCeti.hessianSymbolLp` and applies the strong-type Calderón–Zygmund theorem
to its Newtonian Hessian kernel.

The restriction `n ≥ 3` comes from the available kernel representation through the power-law
Newtonian potential.  The planar logarithmic kernel requires a separate identification.

## Main declarations

* `TauCeti.exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le`: for `1 < p < ∞`, the
  Hessian Fourier multiplier satisfies an `Lᵖ` estimate on its `L²` domain.
* `SchwartzMap.exists_eLpNorm_lineDerivOp_lineDerivOp_le_laplacian`: for `1 < p < ∞`, every
  second directional derivative of a complex Hilbert-space-valued Schwartz map has `Lᵖ` norm
  bounded by the `Lᵖ` norm of the Laplacian.
* `SchwartzMap.exists_eLpNorm_lineDerivOp_lineDerivOp_le_laplacian_real`: the corresponding
  estimate for real-valued Schwartz maps.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace MeasureTheory Metric Set
open scoped ENNReal Laplacian LineDeriv NNReal RealInnerProductSpace SchwartzMap

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The real-linear Newtonian Hessian kernel representing the Hessian Fourier multiplier. -/
private def newtonianHessianKernel (v w : EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) : F →L[ℝ] F :=
  (-iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]) •
    ContinuousLinearMap.id ℝ F

private theorem stronglyMeasurable_newtonianHessianKernel (v w : EuclideanSpace ℝ (Fin n)) :
    StronglyMeasurable (Function.uncurry (newtonianHessianKernel (F := F) v w)) := by
  have hD : Measurable (fun z : EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ 2 (newtonianKernel n) z ![v, w]) :=
    measurable_of_continuousOn_compl_singleton 0 fun z hz ↦
      ((((contDiffAt_newtonianKernel n hz).continuousAt_iteratedFDeriv le_rfl).eval_const _)
        |>.continuousWithinAt)
  exact ((hD.comp (measurable_fst.sub measurable_snd)).neg.stronglyMeasurable.smul_const
    (ContinuousLinearMap.id ℝ F))

private theorem norm_newtonianHessianKernel_le (v w : EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y) :
    ‖newtonianHessianKernel (F := F) v w x y‖ ≤
      (((n : ℝ) + 1) * ((n : ℝ) * volume.real
          (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖)) *
        dist x y ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  calc
    ‖newtonianHessianKernel (F := F) v w x y‖ ≤
        ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]‖ := by
      rw [newtonianHessianKernel, norm_smul, norm_neg]
      simpa using mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (norm_nonneg (iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]))
    _ ≤ ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)‖ * (‖v‖ * ‖w‖) := by
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)).le_opNorm ![v, w]
    _ ≤ (((n : ℝ) + 1) * ((n : ℝ) * volume.real
          (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * ‖x - y‖ ^ (-(n : ℝ))) *
          (‖v‖ * ‖w‖) := by
      gcongr
      exact norm_iteratedFDeriv_two_newtonianKernel_le hsub
    _ = _ := by
      rw [finrank_euclideanSpace_fin, dist_eq_norm]
      ring

private theorem norm_newtonianHessianKernel_sub_le
    (v w : EuclideanSpace ℝ (Fin n)) (x y y' : EuclideanSpace ℝ (Fin n))
    (h : 2 * dist y y' < dist x y') :
    ‖newtonianHessianKernel (F := F) v w x y -
        newtonianHessianKernel (F := F) v w x y'‖ ≤
      (2 ^ (n + 1) * ((n : ℝ) + 5) *
          (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖)) *
        (dist y y' ^ (1 : ℝ) *
          dist x y' ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + (1 : ℝ)))) := by
  have hgeom : 2 * ‖(x - y) - (x - y')‖ ≤ ‖x - y'‖ := by
    simpa only [sub_sub_sub_cancel_left, norm_sub_rev, dist_eq_norm] using h.le
  calc
    ‖newtonianHessianKernel (F := F) v w x y -
        newtonianHessianKernel (F := F) v w x y'‖ ≤
        ‖(iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) -
          iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y')) ![v, w]‖ := by
      rw [newtonianHessianKernel, newtonianHessianKernel, ← sub_smul, norm_smul]
      calc
        ‖-iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] -
            -iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y') ![v, w]‖ *
            ‖ContinuousLinearMap.id ℝ F‖ ≤
            ‖-iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] -
              -iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y') ![v, w]‖ * 1 := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ = ‖(iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) -
            iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y')) ![v, w]‖ := by
          -- Factor out the common negation so the norm can eliminate it.
          have hneg : -iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] -
              -iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y') ![v, w] =
              -(iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] -
                iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y') ![v, w]) := by
            ring
          rw [hneg, norm_neg, mul_one]
          rfl
    _ ≤ ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) -
          iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y')‖ * (‖v‖ * ‖w‖) := by
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) -
          iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y')).le_opNorm ![v, w]
    _ ≤ (2 ^ (n + 1) * ((n : ℝ) + 5) *
          (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
          ‖(x - y) - (x - y')‖ * ‖x - y'‖ ^ (-((n : ℝ) + 1))) *
          (‖v‖ * ‖w‖) := by
      gcongr
      exact norm_iteratedFDeriv_two_newtonianKernel_sub_le hgeom
    _ = _ := by
      rw [finrank_euclideanSpace_fin, dist_eq_norm, dist_eq_norm, Real.rpow_one,
        sub_sub_sub_cancel_left, norm_sub_rev]
      ring

/-- The Hessian Fourier multiplier satisfies an `Lᵖ` estimate on its `L²` domain in dimension at
least three. The constant may depend on `n`, `p`, `v`, and `w`, but not on the input. -/
theorem exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le [CompleteSpace F]
    (hn : 3 ≤ n) (v w : EuclideanSpace ℝ (Fin n)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
      eLpNorm (Lp.fourierMultiplierCLM F (hessianSymbolLp v w) f) p volume ≤
        C * eLpNorm f p volume := by
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let _ := InnerProductSpace.rclikeToReal ℂ F
  have _ := IsScalarTower.restrictScalars ℝ ℂ F
  let T := (Lp.fourierMultiplierCLM F (hessianSymbolLp v w)).restrictScalars ℝ
  let k := newtonianHessianKernel (F := F) v w
  let C₀ : ℝ≥0 := ⟨((n : ℝ) + 1) * ((n : ℝ) * volume.real
    (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖), by positivity⟩
  let C₁ : ℝ≥0 := ⟨2 ^ (n + 1) * ((n : ℝ) + 5) *
    (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖), by positivity⟩
  have hrep : ∀ (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (s : Set (EuclideanSpace ℝ (Fin n))), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z) := by
    intro f s hs hf
    have h := ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral hn v w f hs hf
    filter_upwards [h] with x hx hxs
    simp only [T, ContinuousLinearMap.coe_restrictScalars']
    rw [hx hxs, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    simp [k, newtonianHessianKernel]
  have hTc : adjoint (Lp.fourierMultiplierCLM F (hessianSymbolLp v w)) =
      Lp.fourierMultiplierCLM F (hessianSymbolLp v w) := by
    simp [Lp.adjoint_fourierMultiplierCLM]
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hTc)
  have hsymmRestrict := hsymm.restrictScalars
  have real_inner_eq_re_inner_L2
      (f g : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      ⟪f, g⟫_ℝ = RCLike.re ⟪f, g⟫_ℂ := by
    rw [L2.inner_def, L2.inner_def]
    simp only [real_inner_eq_re_inner ℂ]
    rw [integral_re (L2.integrable_inner (𝕜 := ℂ) f g)]
  have hsymmReal : T.toLinearMap.IsSymmetric := fun f g ↦ by
    rw [real_inner_eq_re_inner_L2, real_inner_eq_re_inner_L2]
    exact hsymmRestrict f g
  have hself : adjoint (𝕜 := ℝ) T = T := hsymmReal.clm_adjoint_eq
  have hrep' : ∀ (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (s : Set (EuclideanSpace ℝ (Fin n))), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) →
        ∀ᵐ x, x ∉ s → adjoint (𝕜 := ℝ) T f x = ∫ z, k x z (f z) := by
    rw [hself]
    exact hrep
  have hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤
      (C₀ : ℝ) * dist x y ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) := by
    intro x y hxy
    -- Expose the local kernel and its nonnegative real constant to apply the Hessian bound.
    change ‖newtonianHessianKernel (F := F) v w x y‖ ≤
      (((n : ℝ) + 1) * ((n : ℝ) * volume.real
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖)) *
          dist x y ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))
    exact norm_newtonianHessianKernel_le v w x y hxy
  have hsmooth : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ (C₁ : ℝ) *
        (dist y y' ^ (1 : ℝ) *
          dist x y' ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + (1 : ℝ)))) := by
    intro x y y' h
    -- Expose the local kernel and constant to apply the Hessian smoothness bound.
    change ‖newtonianHessianKernel (F := F) v w x y -
        newtonianHessianKernel (F := F) v w x y'‖ ≤
      (2 ^ (n + 1) * ((n : ℝ) + 5) *
        (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖)) *
          (dist y y' ^ (1 : ℝ) *
            dist x y' ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + (1 : ℝ))))
    exact norm_newtonianHessianKernel_sub_le v w x y y' h
  simpa only [T, ContinuousLinearMap.coe_restrictScalars'] using
    T.exists_eLpNorm_le_of_norm_sub_le_mul_rpow
      (stronglyMeasurable_newtonianHessianKernel v w)
      (stronglyMeasurable_newtonianHessianKernel v w)
      (C₀ := C₀) (C := C₁) (C₀' := C₀) (C' := C₁) (δ := 1) (δ' := 1)
      (by norm_num) (by norm_num) hsize hsize hsmooth hsmooth
      hrep hrep' hp hp_top

end TauCeti

namespace SchwartzMap

open TauCeti
open MeasureTheory
open scoped ENNReal Laplacian LineDeriv NNReal SchwartzMap

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The whole-space Calderón–Zygmund estimate for the Laplacian.** In dimension at least three,
for every `1 < p < ∞` and directions `v`, `w`, there is a constant `C` such that

`\| ∂_v ∂_w u \|_{Lᵖ} ≤ C \| Δu \|_{Lᵖ}`

for every Schwartz function `u : ℝⁿ → F`.  The constant may depend on `n`, `p`, `v` and `w`,
but not on `u`. -/
theorem exists_eLpNorm_lineDerivOp_lineDerivOp_le_laplacian (hn : 3 ≤ n)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (v w : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ≥0, ∀ u : SchwartzMap (EuclideanSpace ℝ (Fin n)) F,
      eLpNorm ((∂_{v} (∂_{w} u) : SchwartzMap (EuclideanSpace ℝ (Fin n)) F).toLp 2)
          p volume ≤
        C * eLpNorm ((Δ u : SchwartzMap (EuclideanSpace ℝ (Fin n)) F).toLp 2) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le
    (F := F) hn v w hp hp_top
  refine ⟨C, fun u ↦ ?_⟩
  have h := hC ((Δ u).toLp 2)
  rw [← u.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM v w] at h
  exact h

/-- **The real-valued whole-space Calderón–Zygmund estimate for the Laplacian.** In dimension at
least three, every second directional derivative of a real-valued Schwartz function is bounded in
`Lᵖ`, for `1 < p < ∞`, by its Laplacian. -/
theorem exists_eLpNorm_lineDerivOp_lineDerivOp_le_laplacian_real (hn : 3 ≤ n)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (v w : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ≥0, ∀ u : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ,
      eLpNorm ((∂_{v} (∂_{w} u) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ).toLp 2)
          p volume ≤
        C * eLpNorm ((Δ u : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ).toLp 2) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_lineDerivOp_lineDerivOp_le_laplacian
    (F := ℂ) hn hp hp_top v w
  refine ⟨C, fun u ↦ ?_⟩
  let uℂ := u.postcompCLM Complex.ofRealCLM
  have h := hC uℂ
  have hderiv : ∂_{v} (∂_{w} uℂ) =
      (∂_{v} (∂_{w} u)).postcompCLM Complex.ofRealCLM := by
    simp [uℂ, TauCeti.lineDerivOp_postcompCLM]
  have hlaplacian : Δ uℂ = (Δ u).postcompCLM Complex.ofRealCLM := by
    rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ _) uℂ,
      SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ _) u]
    simp only [uℂ, TauCeti.lineDerivOp_postcompCLM, map_sum]
  have eLpNorm_postcomp_ofReal
      (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) :
      eLpNorm ((f.postcompCLM Complex.ofRealCLM).toLp 2) p volume =
        eLpNorm (f.toLp 2) p volume := by
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [SchwartzMap.coeFn_toLp (f.postcompCLM Complex.ofRealCLM) 2,
      SchwartzMap.coeFn_toLp f 2] with x hx hxf
    rw [hx, hxf, SchwartzMap.postcompCLM_apply]
    exact Complex.norm_real (f x)
  rw [hderiv, hlaplacian, eLpNorm_postcomp_ofReal, eLpNorm_postcomp_ofReal] at h
  exact h

end SchwartzMap
