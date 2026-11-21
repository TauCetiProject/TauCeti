/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.ModularConjugation
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
import TauCeti.RepresentationTheory.Continuous.Unitary.StronglyContinuous

/-!
# Tomita commutation for KMS states

For a β-KMS state `ω` of a point-norm continuous real action `α` on a unital C⋆-algebra `A`,
this file proves the reverse Tomita commutation inclusion `J₀ M' J₀ ⊆ M`
(`TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin`) and hence `J₀ M J₀ = M'` for
the GNS von Neumann algebra `M = π_ω(A)''` and its modular conjugation `J₀`.

For `β = 0` (tracial states), `J₀ (R Ω) = R⋆ Ω` holds directly for every `R ∈ M'`. For `β ≠ 0`,
`ω` is invariant with strongly continuous implementing unitary group `U_t` commuting with `J₀`;
every `R ∈ M'` is approximated strongly by Gaussian smearings `R_c(z) = ∫ k_c(t - z) U_t R U_{-t}`
in `M'`, for which analytic continuation gives `J₀ (S(0) Ω) = S(iβ/2)⋆ Ω` and commutation of
`J₀ R J₀` with `M'`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_zero`:
  `J₀ (R Ω) = R⋆ Ω` for `R ∈ M'` at `β = 0`.
* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_commute`:
  `J₀ (R Ω) = R⋆ Ω` for `R ∈ M'` commuting with `U_t` when `β ≠ 0`.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin`: `J₀ M' J₀ ⊆ M`.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin_iff`: `J₀ T J₀ ∈ M ↔ T ∈ M'`.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_centralizer_iff`:
  `J₀ T J₀ ∈ M' ↔ T ∈ M`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Section 5.3.1 and Theorem 5.3.30.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory PositiveLinearMap Real Topology
open scoped ComplexConjugate ComplexOrder Convolution CStarAlgebra InnerProductSpace Pointwise

namespace TauCeti.CStarAction

private theorem conj_half_mul_I (β : ℝ) : conj ((β / 2 : ℝ) * I) = -((β / 2 : ℝ) * I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

private theorem star_mem_centralizer_gnsStarAlgHom {f : A →ₚ[ℂ] ℂ} {R : f.GNS →L[ℂ] f.GNS}
    (hR : R ∈ Set.centralizer (Set.range f.gnsStarAlgHom)) :
    star R ∈ Set.centralizer (Set.range f.gnsStarAlgHom) := by
  rintro _ ⟨x, rfl⟩
  simpa [star_mul, ← map_star] using (congrArg star (hR _ ⟨star x, rfl⟩)).symm

private theorem mem_adjoin_gnsStarAlgHom_iff (f : A →ₚ[ℂ] ℂ) {x : f.GNS →L[ℂ] f.GNS} :
    x ∈ VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) ↔
      x ∈ Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) := by
  have hrange : (f.gnsNonUnitalStarAlgHom.range : Set _) = Set.range f.gnsStarAlgHom :=
    NonUnitalStarAlgHom.coe_range f.gnsNonUnitalStarAlgHom
  rw [← SetLike.mem_coe, ← hrange,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset, hrange]

/-! ### The `β = 0` commutation theorem -/

/-- At `β = 0` (tracial states), `J₀ (R Ω) = R⋆ Ω` for every operator `R` in the commutant
`π_ω(A)'`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_zero (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  refine ext_inner_left ℂ fun u =>
    f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have hcomm := star_mem_centralizer_gnsStarAlgHom hR (ρ (star a)) ⟨star a, rfl⟩
  rw [hω.inner_modularConjugation_right, hω.modularConjugation_apply_toGNS_of_zero a]
  calc ⟪R f.gnsVector, f.toGNS (star a)⟫_ℂ
      = ⟪f.gnsVector, (star R * ρ (star a)) f.gnsVector⟫_ℂ := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_right]; simp [ρ, toGNS_apply]
    _ = ⟪f.gnsVector, (ρ (star a) * star R) f.gnsVector⟫_ℂ := by rw [hcomm]
    _ = ⟪f.toGNS a, (star R) f.gnsVector⟫_ℂ := by
        rw [mul_apply_eq_comp, map_star, star_eq_adjoint, adjoint_inner_right]
        simp [ρ, toGNS_apply]

/-- Tomita commutation at `β = 0`: `J₀ R J₀ ∈ π_ω(A)''` for every `R ∈ π_ω(A)'`. -/
private theorem conjModularConjugation_mem_adjoin_of_zero (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  rw [mem_adjoin_gnsStarAlgHom_iff]
  intro R' hR'
  ext v
  refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  let La := hω.conjModularConjugation (ρ a)
  have hLa : La ∈ Set.centralizer (Set.range ρ) :=
    hω.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer a
  have hprod : R * La * star R' ∈ Set.centralizer (Set.range ρ) := fun S hS => by
    rw [mul_assoc, mul_assoc, ← mul_assoc S, hR S hS, mul_assoc R, ← mul_assoc S, hLa S hS,
      mul_assoc La, star_mem_centralizer_gnsStarAlgHom hR' S hS]
    simp only [mul_assoc]
  have h1 : R' (f.toGNS a) = ρ a (R' f.gnsVector) := by
    simpa [ρ, mul_apply_eq_comp, toGNS_apply] using
      (congrArg (fun T => T f.gnsVector) (hR' (ρ a) ⟨a, rfl⟩)).symm
  have h2 : hω.modularConjugation (R' (f.toGNS a)) = (La * star R') f.gnsVector := by
    rw [h1, mul_apply_eq_comp, ← hω.modularConjugation_apply_gnsVector_of_zero hR']; simp [La, f]
  have h3 : (hω.conjModularConjugation R * R') (f.toGNS a) =
      hω.modularConjugation ((R * La * star R') f.gnsVector) := by
    simp only [mul_apply_eq_comp, hω.conjModularConjugation_apply, h2]
  rw [h3, hω.modularConjugation_apply_gnsVector_of_zero hprod,
    show star (R * La * star R') = R' * star La * star R by simp [star_mul, mul_assoc]]
  simp only [mul_apply_eq_comp]
  rw [← hω.modularConjugation_apply_gnsVector_of_zero hR,
    show star La = hω.conjModularConjugation (ρ (star a)) by
      rw [← hω.conjModularConjugation_star, map_star]]
  simp only [hω.conjModularConjugation_apply, hω.modularConjugation_modularConjugation]
  have hcommR : ρ (star a) (R f.gnsVector) = R (ρ (star a) f.gnsVector) := by
    simpa [mul_apply_eq_comp] using
      congrArg (fun T => T f.gnsVector) (hR (ρ (star a)) ⟨star a, rfl⟩)
  rw [hcommR, show ρ (star a) f.gnsVector = hω.modularConjugation (f.toGNS a) by
    rw [hω.modularConjugation_apply_toGNS_of_zero a]; simp [ρ, f, toGNS_apply]]

/-! ### Gaussian smearing of commutant operators and the `β ≠ 0` commutation theorem -/

section Nonzero

/-- Complex Gaussian kernel `(c / √π) * exp (-(c * (t - z))²)`. -/
private def smearKernel (c t : ℝ) (z : ℂ) : ℂ :=
  ((c : ℂ) / √π) * cexp (-((c : ℂ) * (t - z)) ^ 2)

private theorem norm_smearKernel_le (c t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖smearKernel c t z‖ ≤
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  rw [smearKernel, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (Complex.norm_cexp_neg_mul_sub_sq_le c t hz) (norm_nonneg _)

private theorem integrable_norm_smearKernel (c : ℝ) (z : ℂ) :
    Integrable fun t : ℝ => ‖smearKernel c t z‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [smearKernel]
  refine ((integrable_exp_neg_mul_sq (by positivity : 0 < c ^ 2 / 2)).const_mul
    (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * ‖z‖ ^ 2))).mono'
    (Continuous.norm (by unfold smearKernel; fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_smearKernel_le c t (le_refl ‖z‖)

/-- Integrating a bounded continuous function against the complex Gaussian kernel is entire. -/
private theorem differentiable_gaussianIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (c : ℝ) :
    Differentiable ℂ fun z : ℂ => ∫ t : ℝ, smearKernel c t z • f t := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [smearKernel]
  intro z₀
  have hb : 0 < c ^ 2 / 2 := by positivity
  set D := ‖z₀‖ + 1
  have hD (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : ‖z‖ ≤ D := (norm_lt_of_mem_ball hz).le
  have hG := integrable_exp_neg_mul_sq hb
  have hG' : Integrable fun t : ℝ => (|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2) :=
    ((integrable_mul_exp_neg_mul_sq hb).norm.add (hG.const_mul D)).congr
      (ae_of_all _ fun t => by
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]; ring)
  have hcontF (z : ℂ) : Continuous fun t : ℝ => smearKernel c t z • f t :=
    (by unfold smearKernel; fun_prop : Continuous fun t : ℝ => smearKernel c t z).smul hf
  have hcontF' : Continuous fun t : ℝ =>
      (smearKernel c t z₀ * (2 * (c : ℂ) ^ 2 * (t - z₀))) • f t :=
    (by unfold smearKernel; fun_prop : Continuous fun t : ℝ =>
      smearKernel c t z₀ * (2 * (c : ℂ) ^ 2 * (t - z₀))).smul hf
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (F := fun z t => smearKernel c t z • f t)
    (F' := fun z t => (smearKernel c t z * (2 * (c : ℂ) ^ 2 * (t - z))) • f t)
    (bound := fun t => ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * (2 * c ^ 2) * B *
      ((|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2)))
    (.of_forall fun z => (hcontF z).aestronglyMeasurable) ?_ hcontF'.aestronglyMeasurable
    (ae_of_all _ fun t z hz => ?_) (hG'.const_mul _)
    (ae_of_all _ fun t z _ => by
      simpa only [smearKernel, mul_assoc] using
        ((Complex.hasDerivAt_cexp_neg_mul_sub_sq c t z).const_mul ((c : ℂ) / √π)).smul_const
          (f t))).2.differentiableAt
  · refine (hG.const_mul (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * B)).mono'
      (hcontF z₀).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [norm_smul]
    exact (mul_le_mul (norm_smearKernel_le c t (hD z₀ (Metric.mem_ball_self one_pos))) (hB t)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · have hlin : ‖2 * (c : ℂ) ^ 2 * (t - z)‖ ≤ 2 * c ^ 2 * (|t| + D) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Complex.norm_two]
      gcongr
      exact (norm_sub_le _ _).trans (by
        rw [Complex.norm_real, Real.norm_eq_abs]; gcongr; exact hD z hz)
    rw [norm_smul, norm_mul]
    exact (by
      gcongr
      · exact norm_smearKernel_le c t (hD z hz)
      · exact hB t :
      ‖smearKernel c t z‖ * ‖2 * (c : ℂ) ^ 2 * (t - z)‖ * ‖f t‖ ≤
        (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)) *
          (2 * c ^ 2 * (|t| + D)) * B).trans_eq (by ring)

/-- As `c → ∞`, integrating a bounded continuous function against `smearKernel c · 0` tends to
`f 0`. -/
private theorem tendsto_gaussianIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) {B : ℝ}
    (hB : ∀ t, ‖f t‖ ≤ B) :
    Tendsto (fun c : ℝ => ∫ t : ℝ, smearKernel c t 0 • f t) atTop (𝓝 (f 0)) := by
  let g : ℝ → E := fun u => f (-u)
  have hg : Continuous g := hf.comp continuous_neg
  have htime : Tendsto (fun c : ℝ => 4 * c ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop (by norm_num : 0 < (4 : ℝ))
  have ht : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [one_div] using! htime.inv_tendsto_atTop,
      (eventually_gt_atTop 0).mono fun c hc => Set.mem_Ioi.mpr (by positivity)⟩
  have hlim := (tendsto_heatKernel_convolution hg.aestronglyMeasurable
    (ae_of_all _ fun u => hB (-u)) (x₀ := 0) hg.continuousAt).comp (ht.prodMk tendsto_const_nhds)
  rw [show g 0 = f 0 by simp [g]] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
  have hkernel (t : ℝ) : heatKernel (1 / (4 * c ^ 2)) t = gaussianDensity c t := by
    rw [heatKernel_apply]
    simp only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs]
    rw [neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show 4 * π * (1 / (4 * c ^ 2)) = π / c ^ 2 by field_simp,
      Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le,
      show -t ^ 2 / (4 * (1 / (4 * c ^ 2))) = -(c * t) ^ 2 by field_simp, gaussianDensity_def]
    simp only [inv_div]; ring
  simp only [Function.comp_apply, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    hkernel, g, neg_neg]
  congr 1 with t
  rw [smearKernel, gaussianDensity_def, ← Complex.coe_smul]
  congr 1; push_cast; ring_nf

section SmearOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {U : ContRepresentation ℂ (Multiplicative ℝ) H}

private theorem continuous_unitaryConj_apply (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (v : H) :
    Continuous fun t : ℝ => U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  have h1 : Continuous fun t : ℝ => U (.ofAdd (-t)) v := by
    convert (hU.continuous_inv_apply hcont v).comp continuous_ofAdd using 1
    ext t; simp [ofAdd_neg]
  exact (hU.continuous_apply_prod hcont).comp (continuous_ofAdd.prodMk (R.continuous.comp h1))

private theorem norm_unitaryConj_apply_le (hU : U.IsUnitary) (R : H →L[ℂ] H) (v : H) (t : ℝ) :
    ‖U (.ofAdd t) (R (U (.ofAdd (-t)) v))‖ ≤ ‖R‖ * ‖v‖ := by
  rw [hU.norm_map]; simpa only [hU.norm_map] using R.le_opNorm (U (.ofAdd (-t)) v)

private theorem integrable_smear (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z : ℂ) (v : H) :
    Integrable fun t : ℝ => smearKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  refine ((integrable_norm_smearKernel c z).mul_const (‖R‖ * ‖v‖)).mono'
    ((by unfold smearKernel; fun_prop : Continuous fun t : ℝ => smearKernel c t z).smul
      (continuous_unitaryConj_apply hU hcont R v)).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_unitaryConj_apply_le hU R v t) (norm_nonneg _)

/-- Complex-time Gaussian smearing of an operator `R` under the unitary group `U`. -/
private def smearOp (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    (c : ℝ) (z : ℂ) : H →L[ℂ] H :=
  ({ toFun v := ∫ t : ℝ, smearKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v))
     map_add' u v := by
       simp only [map_add, smul_add]
       exact integral_add (integrable_smear hU hcont R c z u)
         (integrable_smear hU hcont R c z v)
     map_smul' a v := by
       simp only [map_smul, smul_comm _ a, RingHom.id_apply]; exact integral_smul a _ } :
    H →ₗ[ℂ] H).mkContinuous ((∫ t : ℝ, ‖smearKernel c t z‖) * ‖R‖) fun v => by
      refine (norm_integral_le_of_norm_le ((integrable_norm_smearKernel c z).mul_const (‖R‖ * ‖v‖))
        (ae_of_all _ fun t => ?_)).trans_eq (by rw [integral_mul_const, mul_assoc])
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_unitaryConj_apply_le hU R v t) (norm_nonneg _)

private theorem locallyBounded_smearOp (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z₀ : ℂ) :
    ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖smearOp hU hcont R c z‖ ≤ M := by
  set D := ‖z₀‖ + 1
  refine ⟨1, one_pos, (∫ t : ℝ, ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) *
    rexp (-(c ^ 2 / 2) * t ^ 2)) * ‖R‖, fun z hz => ?_⟩
  refine (LinearMap.mkContinuous_norm_le _
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg R)) _).trans ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp [smearKernel]
  · exact mul_le_mul_of_nonneg_right
      (integral_mono (integrable_norm_smearKernel c z)
        ((integrable_exp_neg_mul_sq (by positivity : 0 < c ^ 2 / 2)).const_mul _)
        fun t => norm_smearKernel_le c t (norm_lt_of_mem_ball hz).le) (norm_nonneg R)

variable [CompleteSpace H]

private theorem star_smearOp_conj (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z : ℂ) :
    star (smearOp hU hcont R c (conj z)) = smearOp hU hcont (star R) c z := by
  ext v
  refine ext_inner_left ℂ fun u => ?_
  rw [star_eq_adjoint, adjoint_inner_right, ← inner_conj_symm]
  simp only [smearOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← innerSL_apply_apply (𝕜 := ℂ) v, ← innerSL_apply_apply (𝕜 := ℂ) u,
    ← (innerSL ℂ v).integral_comp_comm (integrable_smear hU hcont R c (conj z) u),
    ← (innerSL ℂ u).integral_comp_comm (integrable_smear hU hcont (star R) c z v), ← integral_conj]
  congr 1 with t
  simp only [innerSL_apply_apply, inner_smul_right, map_mul]
  have hstar_U (r : ℝ) : (U (.ofAdd r)).adjoint = U (.ofAdd (-r)) := by
    rw [hU.adjoint_eq_inv, ofAdd_neg]
  rw [show conj (smearKernel c t (conj z)) = smearKernel c t z by
    simp [smearKernel, ← Complex.exp_conj]]
  congr 1
  rw [inner_conj_symm, ← adjoint_inner_right, hstar_U, star_eq_adjoint, ← adjoint_inner_right,
    ← adjoint_inner_right, hstar_U, neg_neg]

/-- At real time `s`, `smearOp R c s = U_s * smearOp R c 0 * U_{-s}`. -/
private theorem smearOp_ofReal (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c s : ℝ) :
    smearOp hU hcont R c s = U (.ofAdd s) * smearOp hU hcont R c 0 * U (.ofAdd (-s)) := by
  ext v
  simp only [mul_apply_eq_comp, smearOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [← (U (.ofAdd s)).integral_comp_comm (integrable_smear hU hcont R c 0 (U (.ofAdd (-s)) v)),
    ← integral_add_right_eq_self _ s]
  congr 1 with u
  rw [map_smul]
  congr 1
  · simp only [smearKernel, sub_zero]; push_cast; ring_nf
  · have hm1 : U (.ofAdd s) * U (.ofAdd u) = U (.ofAdd (u + s)) := by
      rw [← map_mul, ← ofAdd_add, add_comm]
    have hm2 : U (.ofAdd (-u)) * U (.ofAdd (-s)) = U (.ofAdd (-(u + s))) := by
      rw [← map_mul, ← ofAdd_add, neg_add]
    simpa only [mul_apply_eq_comp] using congrArg (fun X => X v) (by rw [hm1, hm2] :
      U (.ofAdd (u + s)) * R * U (.ofAdd (-(u + s))) =
        U (.ofAdd s) * U (.ofAdd u) * R * (U (.ofAdd (-u)) * U (.ofAdd (-s))))

omit [CompleteSpace H] in
/-- Product rule for strongly entire operator families when the outer factor is locally bounded. -/
private theorem differentiable_comp_apply {S₁ S₂ : ℂ → (H →L[ℂ] H)}
    (h1 : ∀ w, Differentiable ℂ fun z => S₁ z w) (h2 : ∀ w, Differentiable ℂ fun z => S₂ z w)
    (hb : ∀ z₀, ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖S₁ z‖ ≤ M) (v : H) :
    Differentiable ℂ fun z => S₁ z (S₂ z v) := by
  intro z₀
  set w₂ := deriv (fun z => S₂ z v) z₀
  set w₁ := deriv (fun z => S₁ z (S₂ z₀ v)) z₀
  obtain ⟨r, hr, M, hM⟩ := hb z₀
  refine HasDerivAt.differentiableAt (f' := w₁ + S₁ z₀ w₂) (hasDerivAt_iff_isLittleO.mpr ?_)
  have ho1 := hasDerivAt_iff_isLittleO.mp (h1 (S₂ z₀ v) z₀).hasDerivAt
  have ho2 : (fun z => S₁ z (S₂ z v - S₂ z₀ v - (z - z₀) • w₂)) =o[𝓝 z₀] fun z => z - z₀ :=
    (Asymptotics.isBigO_iff.mpr ⟨max M 0, Metric.eventually_nhds_iff.mpr ⟨r, hr, fun z hz =>
      (S₁ z).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right
        ((hM z hz).trans (le_max_left M 0)) (norm_nonneg _))⟩⟩).trans_isLittleO
      (hasDerivAt_iff_isLittleO.mp (h2 v z₀).hasDerivAt)
  have ho3 : (fun z => (z - z₀) • (S₁ z w₂ - S₁ z₀ w₂)) =o[𝓝 z₀] fun z => z - z₀ := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have ht : Tendsto (fun z => S₁ z w₂ - S₁ z₀ w₂) (𝓝 z₀) (𝓝 0) := by
      simpa only [sub_self] using
        ((h1 w₂).continuous.tendsto z₀).sub (tendsto_const_nhds (x := S₁ z₀ w₂))
    filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 hε)] with z hz
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Metric.mem_ball, dist_eq_norm] using hz.le)
      (norm_nonneg _)
  refine ((ho1.add ho2).add ho3).congr' (.of_forall fun z => ?_) (.of_forall fun _ => rfl)
  simp only [map_sub, map_smul, smul_add, smul_sub]; abel

end SmearOp

private abbrev kmsUnitary (hω : α.IsKMSState β ω) (hβ : β ≠ 0) :
    ContRepresentation ℂ (Multiplicative ℝ) ω.toPositiveLinearMap.GNS :=
  α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a)

private theorem star_kmsUnitary (hω : α.IsKMSState β ω) (hβ : β ≠ 0) (r : ℝ) :
    star (kmsUnitary hω hβ (.ofAdd r)) = kmsUnitary hω hβ (.ofAdd (-r)) := by
  rw [star_eq_adjoint, (α.isUnitary_gnsImplementingGroup _).adjoint_eq_inv, ofAdd_neg]

/-- An analytic family in the GNS commutant for `β ≠ 0`: a locally bounded strongly entire family
(along with its reflected adjoint) in `π_ω(A)'` whose restriction to `ℝ` is conjugation by `U_t`. -/
private structure IsAnalyticCommutantFamily (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    (S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)) : Prop where
  differentiable_apply (v : ω.toPositiveLinearMap.GNS) : Differentiable ℂ fun z => S z v
  differentiable_star_conj_apply (v : ω.toPositiveLinearMap.GNS) :
    Differentiable ℂ fun z => star (S (conj z)) v
  locallyBounded (z₀ : ℂ) : ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖S z‖ ≤ M
  mem_centralizer (z : ℂ) :
    S z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)
  apply_ofReal (t : ℝ) :
    S t = kmsUnitary hω hβ (.ofAdd t) * S 0 * kmsUnitary hω hβ (.ofAdd (-t))

/-- Real time translation of an analytic commutant family conjugates at every complex time. -/
private theorem IsAnalyticCommutantFamily.add_ofReal {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) (w : ℂ) (t : ℝ) :
    S (w + t) = kmsUnitary hω hβ (.ofAdd t) * S w * kmsUnitary hω hβ (.ofAdd (-t)) := by
  let U := kmsUnitary hω hβ
  ext v
  refine congrFun (((hS.differentiable_apply v).comp (differentiable_id.add_const (t : ℂ)))
    |>.eq_of_ofReal_eq ((U (.ofAdd t)).differentiable.comp (hS.differentiable_apply _))
      fun s => ?_) w
  have heq : S (s + t : ℝ) = U (.ofAdd t) * S s * U (.ofAdd (-t)) := by
    rw [hS.apply_ofReal (s + t), hS.apply_ofReal s,
      show U (.ofAdd (s + t)) = U (.ofAdd t) * U (.ofAdd s) by rw [add_comm, ofAdd_add, map_mul],
      show U (.ofAdd (-(s + t))) = U (.ofAdd (-s)) * U (.ofAdd (-t)) by
        rw [neg_add, ofAdd_add, map_mul]]
    simp only [U, mul_assoc]
  simpa [Complex.ofReal_add, mul_apply_eq_comp] using congrArg (fun X => X v) heq

/-- **Key identity for analytic commutant families:** `J₀ (S 0 Ω) = (S (iβ/2))⋆ Ω`. -/
private theorem IsAnalyticCommutantFamily.modularConjugation_apply_gnsVector
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) :
    hω.modularConjugation (S 0 ω.toPositiveLinearMap.gnsVector) =
      (star (S ((β / 2 : ℝ) * I))) ω.toPositiveLinearMap.gnsVector := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  let U := kmsUnitary hω hβ
  have hUΩ (r : ℝ) : U (.ofAdd r) f.gnsVector = f.gnsVector := by simp [U, f, gnsVector_def]
  refine ext_inner_left ℂ fun u => (denseRange_toGNS_entireAnalytic α f).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.2
  let F : ℂ → ℂ := fun z => ⟪f.toGNS (a : A), star (S (conj z)) f.gnsVector⟫_ℂ
  let G : ℂ → ℂ := fun z => ⟪S 0 f.gnsVector, f.toGNS (α.entireExtension (star (a : A)) (-z))⟫_ℂ
  have hF : Differentiable ℂ F :=
    (innerSL ℂ (f.toGNS (a : A))).differentiable.comp
      (hS.differentiable_star_conj_apply f.gnsVector)
  have hG : Differentiable ℂ G :=
    ((innerSL ℂ (S 0 f.gnsVector)).comp f.toGNS).differentiable.comp
      ((differentiable_entireExtension α (star (a : A))).comp differentiable_neg)
  have hFG : F = G := hF.eq_of_ofReal_eq hG fun t => by
    have hTt : star (S (conj (t : ℂ))) = U (.ofAdd t) * star (S 0) * U (.ofAdd (-t)) := by
      simp only [U, Complex.conj_ofReal, hS.apply_ofReal t, star_mul, star_kmsUnitary, neg_neg,
        mul_assoc]
    have hcomm := congrArg (fun X => X f.gnsVector)
      (hS.mem_centralizer 0 (ρ (α (.ofAdd (-t)) (a : A))) ⟨α (.ofAdd (-t)) (a : A), rfl⟩).symm
    have h1 : ⟪f.toGNS (a : A), U (.ofAdd t) ((star (S 0)) f.gnsVector)⟫_ℂ =
        ⟪U (.ofAdd (-t)) (f.toGNS (a : A)), (star (S 0)) f.gnsVector⟫_ℂ := by
      rw [← star_kmsUnitary hω hβ t]; exact (adjoint_inner_left (U (.ofAdd t)) _ _).symm
    simp only [F, G, hTt, mul_apply_eq_comp, hUΩ]
    rw [h1, star_eq_adjoint, adjoint_inner_right,
      show U (.ofAdd (-t)) (f.toGNS (a : A)) = ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector by
        simp [U, ρ, f, toGNS_apply],
      show S 0 (ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector) =
        ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector) by simpa [mul_apply_eq_comp] using hcomm,
      show ⟪ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector), f.gnsVector⟫_ℂ =
        ⟪S 0 f.gnsVector, ρ (star (α (.ofAdd (-t)) (a : A))) f.gnsVector⟫_ℂ by
        rw [map_star, star_eq_adjoint, adjoint_inner_right]]
    congr 1
    rw [← map_star (α (.ofAdd (-t))) (a : A), ← Complex.ofReal_neg,
      ha.star.entireExtension_ofReal (-t)]
    simp [ρ, toGNS_apply]
  have heval := congrFun hFG (-((β / 2 : ℝ) * I))
  have hconj : conj (-((β / 2 : ℝ) * I)) = (β / 2 : ℝ) * I := by
    rw [map_neg, conj_half_mul_I, neg_neg]
  simp only [F, G, hconj, neg_neg] at heval
  rw [← hω.modularConjugation_apply_toGNS ha, hω.inner_modularConjugation_right] at heval
  exact heval.symm

/-- Product of two analytic commutant families. -/
private theorem IsAnalyticCommutantFamily.mul {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S₁ S₂ : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (h₁ : IsAnalyticCommutantFamily hω hβ S₁) (h₂ : IsAnalyticCommutantFamily hω hβ S₂) :
    IsAnalyticCommutantFamily hω hβ (fun z => S₁ z * S₂ z) where
  differentiable_apply v :=
    differentiable_comp_apply h₁.differentiable_apply h₂.differentiable_apply h₁.locallyBounded v
  differentiable_star_conj_apply v := by
    have hb2 : ∀ z₀, ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖star (S₂ (conj z))‖ ≤ M := fun z₀ => by
      obtain ⟨r, hr, M, hM⟩ := h₂.locallyBounded (conj z₀)
      refine ⟨r, hr, M, fun z hz => ?_⟩
      rw [star_eq_adjoint, LinearIsometryEquiv.norm_map]
      exact hM _ (by simpa [Metric.mem_ball, dist_eq_norm, ← map_sub] using hz)
    simpa only [star_mul, mul_apply_eq_comp] using
      differentiable_comp_apply h₂.differentiable_star_conj_apply h₁.differentiable_star_conj_apply
        hb2 v
  locallyBounded z₀ := by
    obtain ⟨r₁, hr₁, M₁, hM₁⟩ := h₁.locallyBounded z₀
    obtain ⟨r₂, hr₂, M₂, hM₂⟩ := h₂.locallyBounded z₀
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, max M₁ 0 * max M₂ 0, fun z hz =>
      (opNorm_comp_le (S₁ z) (S₂ z)).trans (mul_le_mul
        ((hM₁ z (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)))).trans
          (le_max_left _ _))
        ((hM₂ z (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)))).trans
          (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))⟩
  mem_centralizer z X hX := by
    rw [← mul_assoc, h₁.mem_centralizer z X hX, mul_assoc, h₂.mem_centralizer z X hX, ← mul_assoc]
  apply_ofReal t := by
    let U := kmsUnitary hω hβ
    have hcancel : U (.ofAdd (-t)) * U (.ofAdd t) = 1 := by
      rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
    rw [h₁.apply_ofReal t, h₂.apply_ofReal t]
    calc U (.ofAdd t) * S₁ 0 * U (.ofAdd (-t)) * (U (.ofAdd t) * S₂ 0 * U (.ofAdd (-t)))
        = U (.ofAdd t) * S₁ 0 * (U (.ofAdd (-t)) * U (.ofAdd t)) * S₂ 0 * U (.ofAdd (-t)) := by
          simp only [mul_assoc]
      _ = U (.ofAdd t) * (S₁ 0 * S₂ 0) * U (.ofAdd (-t)) := by
          rw [hcancel, mul_one]; simp only [mul_assoc]

/-- Shifted adjoint `z ↦ (R'(conj z + iβ/2))⋆` of an analytic commutant family. -/
private theorem IsAnalyticCommutantFamily.shiftedStar {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR' : IsAnalyticCommutantFamily hω hβ R') :
    IsAnalyticCommutantFamily hω hβ (fun z => star (R' (conj z + (β / 2 : ℝ) * I))) where
  differentiable_apply v := by
    rw [show (fun z : ℂ => star (R' (conj z + (β / 2 : ℝ) * I)) v) =
        fun z => star (R' (conj (z - (β / 2 : ℝ) * I))) v from
      funext fun z => by rw [map_sub, conj_half_mul_I, sub_neg_eq_add]]
    exact (hR'.differentiable_star_conj_apply v).comp (differentiable_id.sub_const _)
  differentiable_star_conj_apply v := by
    rw [show (fun z : ℂ => star (star (R' (conj (conj z) + (β / 2 : ℝ) * I))) v) =
        fun z => R' (z + (β / 2 : ℝ) * I) v from funext fun z => by simp]
    exact (hR'.differentiable_apply v).comp (differentiable_id.add_const _)
  locallyBounded z₀ := by
    obtain ⟨r, hr, M, hM⟩ := hR'.locallyBounded (conj z₀ + (β / 2 : ℝ) * I)
    refine ⟨r, hr, M, fun z hz => ?_⟩
    rw [star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact hM _ (by simpa [Metric.mem_ball, dist_eq_norm, ← map_sub] using hz)
  mem_centralizer _ := star_mem_centralizer_gnsStarAlgHom (hR'.mem_centralizer _)
  apply_ofReal t := by
    rw [Complex.conj_ofReal, add_comm (t : ℂ), hR'.add_ofReal ((β / 2 : ℝ) * I) t, star_mul,
      star_mul, star_kmsUnitary, star_kmsUnitary, neg_neg, map_zero, zero_add]
    simp only [mul_assoc]

/-- The right-multiplication analytic commutant family `z ↦ J₀ π_ω(α_{conj z}(a)) J₀` for an
entire analytic element `a`. -/
private theorem isAnalyticCommutantFamily_rightMul (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {a : A} (ha : α.IsEntireAnalytic a) :
    IsAnalyticCommutantFamily hω hβ
      (fun z => hω.conjModularConjugation
        (ω.toPositiveLinearMap.gnsStarAlgHom (α.entireExtension a (conj z)))) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  let U := kmsUnitary hω hβ
  let Φ : (f.GNS →L[ℂ] f.GNS) →L[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    ({ toFun T := hω.conjModularConjugation (star T)
       map_add' _ _ := by simp
       map_smul' _ _ := by simp } : (f.GNS →L[ℂ] f.GNS) →ₗ[ℂ] _).mkContinuous 1 fun T => by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hω.norm_conjModularConjugation, star_eq_adjoint, LinearIsometryEquiv.norm_map, one_mul]
  let ρL : A →L[ℂ] (f.GNS →L[ℂ] f.GNS) := { toLinearMap := ρ.toLinearMap, cont := map_continuous ρ }
  have hdiff : Differentiable ℂ fun z : ℂ =>
      hω.conjModularConjugation (ρ (α.entireExtension a (conj z))) := by
    rw [show (fun z : ℂ => hω.conjModularConjugation (ρ (α.entireExtension a (conj z)))) =
        fun z => Φ (ρL (α.entireExtension (star a) z)) from funext fun z => by
      change _ = hω.conjModularConjugation (star (ρ (α.entireExtension (star a) z)))
      rw [← map_star, entireExtension_star, star_star]]
    exact (Φ.comp ρL).differentiable.comp (differentiable_entireExtension α (star a))
  refine ⟨fun v => (ContinuousLinearMap.apply ℂ f.GNS v).differentiable.comp hdiff,
    fun v => ?_, fun z₀ => ?_,
    fun _ => hω.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer _, fun t => ?_⟩
  · rw [show (fun z : ℂ => star (hω.conjModularConjugation
        (ρ (α.entireExtension a (conj (conj z))))) v) =
        fun z => Φ (ρL (α.entireExtension a z)) v from funext fun z => by
      rw [RingHomCompTriple.comp_apply, RingHom.id_apply]
      exact congrArg (fun X => X v) (hω.conjModularConjugation_star _).symm]
    exact ((ContinuousLinearMap.apply ℂ f.GNS v).comp (Φ.comp ρL)).differentiable.comp
      (differentiable_entireExtension α a)
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
      ((hdiff.continuous.norm.continuousAt (x := z₀)).eventually (gt_mem_nhds (lt_add_one _)))
    exact ⟨r, hr, ‖hω.conjModularConjugation (ρ (α.entireExtension a (conj z₀)))‖ + 1,
      fun _ hz => (hball hz).le⟩
  · rw [Complex.conj_ofReal, ha.entireExtension_ofReal t, map_zero, ha.entireExtension_apply_zero]
    have hcov : ρ (α (.ofAdd t) a) = U (.ofAdd t) * ρ a * U (.ofAdd (-t)) := by
      simpa [U, ρ, ofAdd_neg] using
        (α.gnsCovariantRepresentation (fun s x => hω.apply_action hβ s x)).coefficient_action
          (.ofAdd t) a
    have hUconj (r : ℝ) : hω.conjModularConjugation (U (.ofAdd r)) = U (.ofAdd r) := by
      ext v; simp [U, hω.modularConjugation_gnsImplementingGroup hβ]
    rw [hcov, hω.conjModularConjugation_mul, hω.conjModularConjugation_mul, hUconj, hUconj]

/-- Gaussian smearing of a commutant operator `R ∈ π_ω(A)'` produces an analytic commutant family.
-/
private theorem isAnalyticCommutantFamily_smearOp (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) (c : ℝ) :
    IsAnalyticCommutantFamily hω hβ
      (smearOp (U := kmsUnitary hω hβ) (α.isUnitary_gnsImplementingGroup _)
        (α.continuous_gnsImplementingGroup_apply _) R c) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  let U := kmsUnitary hω hβ
  have hU := α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
  have hcont := α.continuous_gnsImplementingGroup_apply (fun s a => hω.apply_action hβ s a)
  refine ⟨fun v => differentiable_gaussianIntegral (continuous_unitaryConj_apply hU hcont R v)
      (norm_unitaryConj_apply_le hU R v) c,
    fun v => by
      rw [show (fun z => star (smearOp hU hcont R c (conj z)) v) =
          fun z => ∫ t : ℝ, smearKernel c t z • U (.ofAdd t) ((star R) (U (.ofAdd (-t)) v)) from
        funext fun z => by rw [star_smearOp_conj hU hcont R c z]; rfl]
      exact differentiable_gaussianIntegral (continuous_unitaryConj_apply hU hcont (star R) v)
        (norm_unitaryConj_apply_le hU (star R) v) c,
    locallyBounded_smearOp hU hcont R c, ?_, smearOp_ofReal hU hcont R c⟩
  intro z
  rintro _ ⟨a, rfl⟩
  ext v
  simp only [mul_apply_eq_comp, smearOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [← (ρ a).integral_comp_comm (integrable_smear hU hcont R c z v)]
  congr 1 with t
  rw [map_smul]
  congr 1
  have hcov (r : ℝ) (x : A) : U (.ofAdd r) * ρ x = ρ (α (.ofAdd r) x) * U (.ofAdd r) := by
    ext w
    simpa [U, ρ, mul_apply_eq_comp] using
      (α.gnsCovariantRepresentation (fun s a => hω.apply_action hβ s a)).covariance (.ofAdd r) x w
  have h1 : ρ a * U (.ofAdd t) = U (.ofAdd t) * ρ (α (.ofAdd (-t)) a) := by
    simpa [← CStarAction.mul_apply, ← ofAdd_add] using (hcov t (α (.ofAdd (-t)) a)).symm
  have hcomm : ρ (α (.ofAdd (-t)) a) * R = R * ρ (α (.ofAdd (-t)) a) := hR _ ⟨_, rfl⟩
  have htot : ρ a * (U (.ofAdd t) * R * U (.ofAdd (-t))) =
      (U (.ofAdd t) * R * U (.ofAdd (-t))) * ρ a := by
    calc ρ a * (U (.ofAdd t) * R * U (.ofAdd (-t)))
        = (ρ a * U (.ofAdd t)) * R * U (.ofAdd (-t)) := by simp only [mul_assoc]
      _ = U (.ofAdd t) * (ρ (α (.ofAdd (-t)) a) * R) * U (.ofAdd (-t)) := by
            rw [h1]; simp only [mul_assoc]
      _ = U (.ofAdd t) * R * (ρ (α (.ofAdd (-t)) a) * U (.ofAdd (-t))) := by
            rw [hcomm]; simp only [mul_assoc]
      _ = U (.ofAdd t) * R * U (.ofAdd (-t)) * ρ a := by
            rw [← hcov (-t) a]; simp only [mul_assoc]
  simpa [U, ρ, f, mul_apply_eq_comp] using congrArg (fun X => X v) htot

/-- For two analytic commutant families `R, R'`, `J₀ (R 0) J₀` commutes with `R' 0`. -/
private theorem commute_conjModularConjugation_of_isAnalyticCommutantFamily
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR : IsAnalyticCommutantFamily hω hβ R) (hR' : IsAnalyticCommutantFamily hω hβ R') :
    hω.conjModularConjugation (R 0) * R' 0 = R' 0 * hω.conjModularConjugation (R 0) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  ext v
  refine (denseRange_toGNS_entireAnalytic α f).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.2
  let La : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z =>
    hω.conjModularConjugation (ρ (α.entireExtension (a : A) (conj z)))
  let S' : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z => star (R' (conj z + (β / 2 : ℝ) * I))
  have hkey := ((hR.mul (isAnalyticCommutantFamily_rightMul hω hβ ha)).mul
    hR'.shiftedStar).modularConjugation_apply_gnsVector
  have hlhs : hω.modularConjugation ((R 0 * La 0 * S' 0) f.gnsVector) =
      (hω.conjModularConjugation (R 0) * R' 0) (f.toGNS (a : A)) := by
    have hS'0 : S' 0 f.gnsVector = hω.modularConjugation (R' 0 f.gnsVector) := by
      simpa only [S', map_zero, zero_add] using hR'.modularConjugation_apply_gnsVector.symm
    have hcommR' : ρ (a : A) (R' 0 f.gnsVector) = R' 0 (f.toGNS (a : A)) := by
      simpa [ρ, mul_apply_eq_comp, toGNS_apply] using
        congrArg (fun X => X f.gnsVector) (hR'.mem_centralizer 0 (ρ (a : A)) ⟨a, rfl⟩)
    simp only [mul_apply_eq_comp, hS'0, show La 0 = hω.conjModularConjugation (ρ (a : A)) by
      simp [La, ha.entireExtension_apply_zero], hω.conjModularConjugation_apply,
      hω.modularConjugation_modularConjugation, hcommR']
  have hrhs : (star (R ((β / 2 : ℝ) * I) * La ((β / 2 : ℝ) * I) * S' ((β / 2 : ℝ) * I)))
      f.gnsVector = (R' 0 * hω.conjModularConjugation (R 0)) (f.toGNS (a : A)) := by
    have hS'val : star (S' ((β / 2 : ℝ) * I)) = R' 0 := by
      simp only [S', star_star, conj_half_mul_I, neg_add_cancel]
    have hLaval : star (La ((β / 2 : ℝ) * I)) =
        hω.conjModularConjugation (ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))) := by
      simp only [La, ← hω.conjModularConjugation_star, ← map_star]
      congr 2; rw [entireExtension_star]
    have hcommR : ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) (R 0 f.gnsVector) =
        R 0 (hω.modularConjugation (f.toGNS (a : A))) := by
      rw [hω.modularConjugation_apply_toGNS ha]
      simpa [ρ, mul_apply_eq_comp, toGNS_apply] using congrArg (fun X => X f.gnsVector)
        (hR.mem_centralizer 0 (ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))) ⟨_, rfl⟩)
    rw [star_mul, star_mul, hS'val, hLaval, mul_apply_eq_comp, mul_apply_eq_comp,
      hR.modularConjugation_apply_gnsVector.symm, hω.conjModularConjugation_apply,
      hω.modularConjugation_modularConjugation, hcommR]
    simp only [mul_apply_eq_comp, hω.conjModularConjugation_apply]
  rw [← hlhs, ← hrhs]
  exact hkey

/-- For `β ≠ 0`, any operator `R ∈ π_ω(A)'` commuting with the GNS implementing unitary group
satisfies `J₀ (R Ω) = R⋆ Ω`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_commute (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom))
    (hcomm : ∀ t : Multiplicative ℝ,
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t * R =
        R * α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector := by
  have hconst : IsAnalyticCommutantFamily hω hβ (fun _ => R) :=
    ⟨fun _ => differentiable_const _, fun _ => differentiable_const _,
      fun _ => ⟨1, one_pos, ‖R‖, fun _ _ => le_rfl⟩, fun _ => hR, fun t => by
        rw [hcomm (.ofAdd t), mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero,
          map_one, mul_one]⟩
  exact hconst.modularConjugation_apply_gnsVector

/-- Tomita commutation for `β ≠ 0`: `J₀ R J₀ ∈ π_ω(A)''` for every `R ∈ π_ω(A)'`. -/
private theorem conjModularConjugation_mem_adjoin_of_ne_zero (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  let f := ω.toPositiveLinearMap
  let U := kmsUnitary hω hβ
  have hU := α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
  have hcont := α.continuous_gnsImplementingGroup_apply (fun s a => hω.apply_action hβ s a)
  rw [mem_adjoin_gnsStarAlgHom_iff]
  intro R' hR'
  have hlim (S : f.GNS →L[ℂ] f.GNS) (v : f.GNS) :
      Tendsto (fun c : ℝ => smearOp (U := U) hU hcont S c 0 v) atTop (𝓝 (S v)) := by
    simpa [smearOp] using tendsto_gaussianIntegral
      (continuous_unitaryConj_apply (U := U) hU hcont S v)
      (norm_unitaryConj_apply_le (U := U) hU S v)
  have hstep1 (c : ℝ) :
      hω.conjModularConjugation (smearOp (U := U) hU hcont R c 0) * R' =
        R' * hω.conjModularConjugation (smearOp (U := U) hU hcont R c 0) := by
    ext v
    set T := hω.conjModularConjugation (smearOp (U := U) hU hcont R c 0)
    refine tendsto_nhds_unique (((T.continuous.tendsto _).comp (hlim R' v)).congr fun c' => ?_)
      (hlim R' (T v))
    simpa [T, mul_apply_eq_comp] using congrArg (fun X => X v)
      (commute_conjModularConjugation_of_isAnalyticCommutantFamily
        (isAnalyticCommutantFamily_smearOp hω hβ hR c)
        (isAnalyticCommutantFamily_smearOp hω hβ hR' c'))
  ext v
  simp only [mul_apply_eq_comp, hω.conjModularConjugation_apply]
  refine (tendsto_nhds_unique
    (((hω.modularConjugation.continuous.tendsto _).comp
        (hlim R (hω.modularConjugation (R' v)))).congr fun c => ?_)
    ((R'.continuous.tendsto _).comp
      ((hω.modularConjugation.continuous.tendsto _).comp
        (hlim R (hω.modularConjugation v))))).symm
  simpa [mul_apply_eq_comp, hω.conjModularConjugation_apply] using
    congrArg (fun X => X v) (hstep1 c)

end Nonzero

/-! ### Tomita commutation for all `β` -/

/-- **Tomita commutation for KMS states (`J₀ M' J₀ ⊆ M`).** For every real `β` (including `β = 0`),
conjugating any operator in the commutant `π_ω(A)'` by the modular conjugation `J₀` yields an
operator in the von Neumann algebra `π_ω(A)''`. -/
theorem IsKMSState.conjModularConjugation_mem_adjoin (hω : α.IsKMSState β ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · exact conjModularConjugation_mem_adjoin_of_zero hω hR
  · exact conjModularConjugation_mem_adjoin_of_ne_zero hω hβ hR

/-- Conjugation by `J₀` sends an operator into `π_ω(A)''` if and only if it lies in `π_ω(A)'`. -/
theorem IsKMSState.conjModularConjugation_mem_adjoin_iff (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.conjModularConjugation T ∈
        VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ↔
      T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) :=
  ⟨fun h => by
      have h' := hω.conjModularConjugation_mem_centralizer h
      rw [hω.conjModularConjugation_conjModularConjugation] at h'
      exact h',
    hω.conjModularConjugation_mem_adjoin⟩

/-- Conjugation by `J₀` sends an operator into `π_ω(A)'` if and only if it lies in `π_ω(A)''`. -/
theorem IsKMSState.conjModularConjugation_mem_centralizer_iff (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.conjModularConjugation T ∈
        Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ↔
      T ∈ VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) :=
  ⟨fun h => by simpa using hω.conjModularConjugation_mem_adjoin h,
    hω.conjModularConjugation_mem_centralizer⟩

end TauCeti.CStarAction
