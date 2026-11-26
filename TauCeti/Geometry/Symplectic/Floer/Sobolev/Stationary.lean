/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.DenseRange
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine

/-!
# The stationary cylinder operator on `W^{1,2}` and its invertibility

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a continuous loop of
`ω`-compatible complex structures and `S_t` a continuous loop of infinitesimally symplectic maps,
the linearized Hamiltonian vector field along an orbit. The stationary cylinder operator

`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`

(`TauCeti.Floer.stationaryCylinderOperator`) is the linearized Floer operator at the stationary
cylinder over the orbit. It is the model operator on every cylindrical end of a punctured Floer
domain, and its invertibility at a nondegenerate orbit is what makes the stationary cylinders of
Floer theory regular and what gluing at an orbit is built on.

This file realizes `D` on the Sobolev space `W^{1,2}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.H1`).
At a nondegenerate orbit, `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1)` of `ζ' = S_t ζ`, it
proves that `D` is bounded below, and that in a unitary frame (`J_t = i`) it is an isomorphism onto
`L²(ℝ × S¹, V)`.

* `TauCeti.Floer.stationaryJetCoeff` is the coefficient field of `D` on jets,
  `(v, v_s, v_t) ↦ v_s + J_t (v_t - S_t v)`, so that on the jet of a section it gives `D ξ`
  (`TauCeti.Floer.stationaryJetCoeff_jet`). It is essentially bounded on the cylinder
  (`TauCeti.Floer.memLp_stationaryJetCoeff`), and `TauCeti.Floer.stationarySobolevOperator` is the
  resulting bounded operator `W^{1,2} → L²`.
* **Bounded below.** At a nondegenerate orbit the cylinder estimate
  `TauCeti.Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator` controls
  the whole `W^{1,2}` norm of a section by `D`, which gives the semi-Fredholm estimate
  (`TauCeti.Floer.exists_hasSemiFredholmEstimate_stationaryJetCoeff`), and the spectral gap
  estimate bounds the `L²` norm on the whole cylinder. Together they make `D` bounded below on
  `W^{1,2}` (`TauCeti.Floer.exists_forall_norm_le_mul_norm_stationarySobolevOperator`), so it is
  injective with closed range (`TauCeti.Floer.injective_stationarySobolevOperator`,
  `TauCeti.Floer.isClosed_range_stationarySobolevOperator`).
* **Onto in a unitary frame.** Let `F` be a finite-dimensional complex inner product space with
  `J_t = i` and `S_t` a `C¹` loop, infinitesimally symplectic for `Im ⟪·, ·⟫`. An element of `L²`
  orthogonal to the range of `D` is orthogonal to `D ξ` for every test section, so it vanishes by
  `TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`: the
  range is dense (`TauCeti.Floer.denseRange_stationarySobolevOperator_ofComplexModule`). Since
  `Im ⟪·, ·⟫` is a symplectic form compatible with `i`, the range is also closed, so `D` is
  bijective (`TauCeti.Floer.bijective_stationarySobolevOperator_ofComplexModule`), and by the open
  mapping theorem it is an isomorphism of Banach spaces (`TauCeti.Floer.stationarySobolevEquiv`).
  The determinant condition gives the nondegeneracy hypothesis of the dense range theorem through
  the loop operator `ζ ↦ ζ' - S_t ζ`
  (`TauCeti.CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero`,
  `TauCeti.CircleSobolev.isInvertible_loopOperator_iff`).
* **The stationary cylinder of Floer theory.** At the stationary cylinder `u(s, t) = x(t)` over an
  orbit `x` of a Hamiltonian `H`, the coefficient field of the linearized Floer operator is
  `TauCeti.Floer.stationaryJetCoeff` with `S_t = dX_{H_t}(x(t))`
  (`TauCeti.SymplecticForm.floerJetCoeff_eq_stationaryJetCoeff`). So when `x` is nondegenerate,
  the realization `D_u` of the linearized Floer operator is bounded below on `W^{1,2}`
  (`exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt`) and
  injective (`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt`).
* **The weighted operator in a unitary trivialization.** With the constant weight slope `δ`, the
  weighted operator `D_u - δ` (`TauCeti.SymplecticForm.floerWeightedSobolevOperator`) at the
  stationary cylinder over a loop `x` and with `J = i` is the stationary cylinder operator with
  `S_t = dX_{H_t}(x(t)) - δ i`, because `-δ = i (δ i)`
  (`TauCeti.SymplecticForm.floerJetCoeff_sub_smul_fst_eq_stationaryJetCoeff`). The shift `δ i` is
  infinitesimally symplectic for `Im ⟪·, ·⟫`, so for a one-periodic `C¹` loop `x` the operator is
  an isomorphism as soon as the shifted field has a nondegenerate return map
  (`TauCeti.SymplecticForm.isInvertible_floerWeightedSobolevOperator_comp_snd`); along an orbit of
  `H` this says that `δ` is not an eigenvalue of the asymptotic operator.

Surjectivity of `D_u`, which reduces to the unitary case by conjugating with a loop of unitary
frames, is in `TauCeti/Geometry/Symplectic/Floer/Sobolev/UnitaryFrame.lean`, together with its
case of a unitary trivialization, where `ω = Im ⟪·, ·⟫` and `J = i`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the invertibility of `∂s + A` at a nondegenerate orbit.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Section 3.1 and Appendix B.
-/

public section

noncomputable section

open Filter Set MeasureTheory ContinuousLinearMap
open scoped NNReal ENNReal Manifold

namespace TauCeti.Floer

open CylinderSobolev
open StripSobolev (jet jet_apply stripMeasure jetLp jetLp_mem_jetClosure jetOperator_jetLp_ae_eq)

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field of the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` on
jets: at `z = (s, t)`, the linear map `(v, v_s, v_t) ↦ v_s + J_t (v_t - S_t v)`. -/
def stationaryJetCoeff (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V) (z : ℝ × ℝ) :
    V × V × V →L[ℝ] V :=
  (fst ℝ V V).comp (snd ℝ V (V × V)) + (J z.2).toLinearMap.toContinuousLinearMap.comp
    ((snd ℝ V V).comp (snd ℝ V (V × V)) - (S z.2).comp (fst ℝ V (V × V)))

/-- The coefficient field of the stationary cylinder operator, evaluated on a jet. -/
theorem stationaryJetCoeff_apply (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (z : ℝ × ℝ) (v : V × V × V) :
    stationaryJetCoeff J S z v = v.2.1 + J z.2 (v.2.2 - S z.2 v.1) := by
  simp [stationaryJetCoeff]

/-- On the jet `(ξ, ∂s ξ, ∂t ξ)` of a section, the coefficient field gives the stationary cylinder
operator `D ξ`. -/
@[simp]
theorem stationaryJetCoeff_jet (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    stationaryJetCoeff J S z (jet ξ z) = stationaryCylinderOperator J S ξ z := by
  simp only [stationaryJetCoeff_apply, stationaryCylinderOperator_def, jet_apply,
    stdComplexLineReal_eq, stdComplexLineImag_eq]

variable {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

/-- The coefficient field of the stationary cylinder operator at `(s, t)` depends only on `t`. -/
theorem stationaryJetCoeff_eq_of_snd_eq {z z' : ℝ × ℝ} (h : z.2 = z'.2) :
    stationaryJetCoeff J S z = stationaryJetCoeff J S z' :=
  ContinuousLinearMap.ext fun v ↦ by simp only [stationaryJetCoeff_apply, h]

/-- For continuous loops `J_t` and `S_t`, the coefficient field of the stationary cylinder operator
is continuous. -/
theorem continuous_stationaryJetCoeff
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) (hSc : Continuous S) :
    Continuous (stationaryJetCoeff J S) := by
  unfold stationaryJetCoeff
  exact continuous_const.add ((hJc.comp continuous_snd).clm_comp (continuous_const.sub
    ((hSc.comp continuous_snd).clm_comp continuous_const)))

/-- For continuous loops `J_t` and `S_t`, the coefficients of the stationary cylinder operator are
essentially bounded on the cylinder. -/
theorem memLp_stationaryJetCoeff
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) (hSc : Continuous S) :
    MemLp (stationaryJetCoeff J S) ∞ stripMeasure :=
  -- The coefficient field depends only on `t`, through the loops `J_t` and `S_t`.
  memLp_top_of_eq_comp_snd
    ((continuous_stationaryJetCoeff hJc hSc).comp (continuous_const.prodMk continuous_id))
    fun _ ↦ stationaryJetCoeff_eq_of_snd_eq rfl

variable (J S) in
/-- The stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` as an operator from the
Sobolev space `W^{1,2}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.H1`) to `L²(ℝ × S¹, V)`. It is `0`
by convention when its coefficients are not essentially bounded on the cylinder. -/
def stationarySobolevOperator : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator stripMeasure (stationaryJetCoeff J S)).comp (H1 V).subtypeL

variable (J S) in
/-- The definition of the Sobolev realization of the stationary cylinder operator: the first-order
operator `TauCeti.jetOperator stripMeasure` of its coefficient field on jets, restricted to
`TauCeti.CylinderSobolev.H1`. -/
theorem stationarySobolevOperator_def :
    stationarySobolevOperator J S =
      (jetOperator stripMeasure (stationaryJetCoeff J S)).comp (H1 V).subtypeL :=
  (rfl)

/-- For continuous loops `J_t` and `S_t`, the Sobolev realization of the stationary cylinder
operator acts pointwise on an `L²` jet `x ∈ H1` by the coefficient field. -/
theorem coeFn_stationarySobolevOperator
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) (hSc : Continuous S)
    (x : H1 V) :
    stationarySobolevOperator J S x =ᵐ[stripMeasure]
      fun z ↦ stationaryJetCoeff J S z ((x : Lp (V × V × V) 2 stripMeasure) z) :=
  coeFn_jetOperator (memLp_stationaryJetCoeff hJc hSc) x

/-- For continuous loops `J_t` and `S_t`, the Sobolev realization of the stationary cylinder
operator is `D ξ` on the jet of a test section `ξ`. -/
theorem stationarySobolevOperator_jetLp_ae_eq
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) (hSc : Continuous S)
    (ξ : testSection V) :
    stationarySobolevOperator J S ⟨jetLp (testSection V) ξ, jetLp_mem_jetClosure ξ⟩
      =ᵐ[stripMeasure] stationaryCylinderOperator J S ξ := by
  filter_upwards [jetOperator_jetLp_ae_eq (memLp_stationaryJetCoeff hJc hSc) ξ] with z hz
  rw [stationarySobolevOperator_def, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hz,
    stationaryJetCoeff_jet]

variable {ω : SymplecticForm V}

/-- **The semi-Fredholm estimate of the stationary cylinder operator.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, let each `S_t` be infinitesimally symplectic and
`S` continuous, and suppose that `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1)` of `ζ' = S_t ζ`.
Then the stationary cylinder operator satisfies the semi-Fredholm estimate
(`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`), with no compact error term:
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖D ξ‖²` over `[a, b] × [0, 1]` for every `C²` section `ξ` of
period one in `t` vanishing for `s ∉ (a, b)`. -/
theorem exists_hasSemiFredholmEstimate_stationaryJetCoeff (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, HasSemiFredholmEstimate (stationaryJetCoeff J S) C 0 := by
  have hJc' : Continuous fun p : ℝ × V ↦ J p.1 p.2 := by
    simpa using (hJc.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨C, hC, hest⟩ :=
    exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator hJ hJc' hS hSc hdet
  -- The forms `g_t = ω(·, J_t ·)` are uniformly equivalent to the norm for `t ∈ [0, 1]`.
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc hJc.continuousOn fun t _ ↦ (hJ t).tames
  obtain ⟨σ, hσ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hSc.continuousOn (s := Icc 0 1))
  refine ⟨(2 + 2 * σ ^ 2) / a * C * b,
    hasSemiFredholmEstimate_iff.2 fun ξ hξ hper s₁ s₂ hs hξ0 ↦ ?_⟩
  set R : Set (ℝ × ℝ) := Icc s₁ s₂ ×ˢ Icc 0 1
  have hint {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f R :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv two_ne_zero
  have hD : Continuous (stationaryCylinderOperator J S ξ) :=
    continuous_stationaryCylinderOperator hJc hSc (hξ.of_le one_le_two)
  set g : ℝ × ℝ → V → ℝ := fun z v ↦ ω.associatedBilinForm (J z.2) v v
  set G : ℝ × ℝ → ℝ := fun z ↦ (g z (fderiv ℝ ξ z stdComplexLineReal) +
    g z (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) + g z (ξ z)
  have hG : Continuous G := ((continuous_associatedBilinForm_apply_self hJc'
    (hdξ.clm_apply continuous_const)).add (continuous_associatedBilinForm_apply_self hJc'
    ((hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply
      hξ.continuous)))).add (continuous_associatedBilinForm_apply_self hJc' hξ.continuous)
  -- On `R`, the `W^{1,2}` density is controlled by `G`, and `g (D ξ)` by `‖D ξ‖²`.
  calc ∫ z in R, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2)
      ≤ ∫ z in R, (2 + 2 * σ ^ 2) / a * G z :=
        setIntegral_mono_on (hint (by fun_prop)) (hint (continuous_const.mul hG)) hRm fun z hz ↦ by
          rw [← stdComplexLineReal_eq, ← stdComplexLineImag_eq]
          exact norm_sq_add_norm_sq_add_norm_sq_le ha (fun v ↦ (hab _ hz.2 v).1) (hσ _ hz.2) _ _ _
    _ ≤ (2 + 2 * σ ^ 2) / a * (C * ∫ z in R, g z (stationaryCylinderOperator J S ξ z)) := by
        rw [integral_const_mul]
        gcongr
        exact hest hξ hper hs (fun t ↦ hξ0 s₁ t fun h ↦ lt_irrefl _ h.1)
          (fun t ↦ hξ0 s₂ t fun h ↦ lt_irrefl _ h.2)
    _ ≤ (2 + 2 * σ ^ 2) / a *
          (C * (b * ∫ z in R, ‖stationaryJetCoeff J S z (jet ξ z)‖ ^ 2)) := by
        gcongr
        rw [← integral_const_mul]
        refine setIntegral_mono_on (hint (continuous_associatedBilinForm_apply_self hJc' hD))
          (hint (continuous_const.mul ?_)) hRm fun z hz ↦ ?_
        · simp only [stationaryJetCoeff_jet]
          exact hD.norm.pow 2
        · rw [stationaryJetCoeff_jet]
          exact (hab _ hz.2 _).2
    _ ≤ (2 + 2 * σ ^ 2) / a * C * b * ((∫ z in R, ‖stationaryJetCoeff J S z (jet ξ z)‖ ^ 2) +
          ∫ z in Icc (-0 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
        have : 0 ≤ (2 + 2 * σ ^ 2) / a * C * b := by positivity
        nlinarith [mul_nonneg this (integral_nonneg fun z ↦ by positivity :
          0 ≤ ∫ z in Icc (-0 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)]

/-- **The stationary cylinder operator is bounded below on `W^{1,2}`.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, let each `S_t` be infinitesimally symplectic and
`S` continuous, and suppose that `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1)` of `ζ' = S_t ζ`.
Then the realization `D : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the stationary cylinder operator
satisfies `‖ξ‖_{W^{1,2}} ≤ K ‖D ξ‖_{L²}` for a constant `K`. -/
theorem exists_forall_norm_le_mul_norm_stationarySobolevOperator (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ K : ℝ≥0, ∀ x : H1 V, ‖x‖ ≤ K * ‖stationarySobolevOperator J S x‖ := by
  obtain ⟨C, hest⟩ := exists_hasSemiFredholmEstimate_stationaryJetCoeff hJ hJc hS hSc hdet
  obtain ⟨C', hL2⟩ :=
    exists_integral_norm_sq_le_mul_integral_norm_sq_stationaryCylinderOperator hJ hJc hS hSc hdet
  exact exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL
    (memLp_stationaryJetCoeff hJc hSc) hest fun ξ ↦ by simpa using hL2 ξ ξ.property

/-- **The stationary cylinder operator is injective on `W^{1,2}`.** Under the hypotheses of
`TauCeti.Floer.exists_forall_norm_le_mul_norm_stationarySobolevOperator`, the realization of the
stationary cylinder operator on `W^{1,2}(ℝ × S¹, V)` is injective. -/
theorem injective_stationarySobolevOperator (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    Function.Injective (stationarySobolevOperator J S) := by
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_stationarySobolevOperator hJ hJc hS hSc hdet
  exact (ContinuousLinearMap.antilipschitz_of_bound _ hK).injective

/-- **The stationary cylinder operator has closed range.** Under the hypotheses of
`TauCeti.Floer.exists_forall_norm_le_mul_norm_stationarySobolevOperator`, the realization of the
stationary cylinder operator on `W^{1,2}(ℝ × S¹, V)` has closed range in `L²(ℝ × S¹, V)`. -/
theorem isClosed_range_stationarySobolevOperator (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    IsClosed (range (stationarySobolevOperator J S)) := by
  obtain ⟨C, hest⟩ := exists_hasSemiFredholmEstimate_stationaryJetCoeff hJ hJc hS hSc hdet
  exact isClosed_range_jetOperator_comp_subtypeL (memLp_stationaryJetCoeff hJc hSc) hest

end General

section Unitary

/-! ### Invertibility in a unitary frame -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The stationary cylinder operator at a nondegenerate orbit has dense range in a unitary
frame.** Let `F` be a finite-dimensional complex inner product space, with `J_t = i`, and let `S`
be a `C¹` loop of real-linear maps of `F`, infinitesimally symplectic for `Im ⟪·, ·⟫`, with
`det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1)` of `ζ' = S_t ζ`. Then the realization
`D : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of `D ξ = ∂s ξ + i (∂t ξ - S_t ξ)` has dense range. -/
theorem denseRange_stationarySobolevOperator_ofComplexModule
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) :
    DenseRange (stationarySobolevOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) fun t : ℝ ↦ S t) := by
  set D := stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
    fun t : ℝ ↦ S t
  have hSc : Continuous fun t : ℝ ↦ S t := hS₁.continuous
  -- In the real Hilbert space `L²`, the orthogonal complement of the range is trivial.
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  set K : Submodule ℝ (Lp F 2 stripMeasure) :=
    LinearMap.range (D : H1 F →ₗ[ℝ] Lp F 2 stripMeasure)
  have hperp : Kᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun η hη ↦ (Lp.eq_zero_iff_ae_eq_zero).2
      (ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero hS₁ hS
        ((CircleSobolev.isInvertible_loopOperator_iff 1 S).1
          ((CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero 1 S).2 (by simpa using hdet)))
        (Lp.memLp η) fun ξ hξ ↦ ?_)
    -- `η` is orthogonal to `D ξ` for every test section `ξ`.
    have h₀ := (Submodule.mem_orthogonal K η).1 hη
      (D ⟨jetLp (testSection F) ⟨ξ, hξ⟩, jetLp_mem_jetClosure _⟩) (LinearMap.mem_range_self _ _)
    rw [MeasureTheory.L2.inner_def] at h₀
    rw [← h₀]
    refine integral_congr_ae ?_
    filter_upwards [stationarySobolevOperator_jetLp_ae_eq continuous_const hSc ⟨ξ, hξ⟩] with z hz
    rw [hz, real_inner_eq_re_inner, RCLike.re_to_complex]
  have hK : Dense (K : Set (Lp F 2 stripMeasure)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 hperp)
  rwa [LinearMap.coe_range] at hK

/-- **The stationary cylinder operator at a nondegenerate orbit is bijective in a unitary frame.**
Under the hypotheses of `TauCeti.Floer.denseRange_stationarySobolevOperator_ofComplexModule`, the
realization `D : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of `D ξ = ∂s ξ + i (∂t ξ - S_t ξ)` is
bijective. -/
theorem bijective_stationarySobolevOperator_ofComplexModule
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) :
    Function.Bijective (stationarySobolevOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) fun t : ℝ ↦ S t) := by
  set J₀ := AlmostComplexStructure.ofComplexModule F with hJ₀def
  have hSc : Continuous fun t : ℝ ↦ S t := hS₁.continuous
  have hJc : Continuous fun _ : ℝ ↦ J₀.toLinearMap.toContinuousLinearMap := continuous_const
  -- The standard symplectic form `ω₀ = Im ⟪·, ·⟫` of `F`, which is compatible with `J₀ = i`.
  set B : LinearMap.BilinForm ℝ F := LinearMap.mk₂ ℝ (fun v w ↦ (inner ℂ v w).im)
    (fun v v' w ↦ by simp [inner_add_left]) (fun c v w ↦ by
      simp [← Complex.coe_smul, inner_smul_left])
    (fun v w w' ↦ by simp [inner_add_right]) (fun c v w ↦ by
      simp [← Complex.coe_smul, inner_smul_right])
  have hB (v w : F) : B v w = (inner ℂ v w).im := LinearMap.mk₂_apply ..
  have hBJ (v : F) : B v (J₀ v) = ‖v‖ ^ 2 := by
    rw [hB, AlmostComplexStructure.ofComplexModule_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  set ω₀ : SymplecticForm F := SymplecticForm.ofTames B
    (fun v ↦ by simp [hB, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow])
    fun v hv ↦ by rw [hBJ]; positivity
  have hω₀ (v w : F) : ω₀ v w = (inner ℂ v w).im := SymplecticForm.ofTames_apply _ _ v w
  have hJ₀ : ω₀.Compatible J₀ := .of_tames ((SymplecticForm.invariant_iff _ _).2 fun v w ↦ by
      simp only [hω₀, hJ₀def, AlmostComplexStructure.ofComplexModule_apply, inner_smul_left,
        inner_smul_right]
      simp [← mul_assoc]) (SymplecticForm.tames_ofTames _ _)
  have hSω (t : ℝ) (v w : F) : ω₀ (S t v) w + ω₀ v (S t w) = 0 := by
    simpa only [hω₀] using hS t v w
  -- `D` is injective with closed and dense range.
  refine ⟨injective_stationarySobolevOperator (fun _ ↦ hJ₀) hJc hSω hSc hdet, ?_⟩
  rw [← range_eq_univ, ← (isClosed_range_stationarySobolevOperator (fun _ ↦ hJ₀) hJc hSω hSc
    hdet).closure_eq]
  exact (denseRange_stationarySobolevOperator_ofComplexModule hS₁ hS hdet).closure_range

/-- **The stationary cylinder operator at a nondegenerate orbit, as an isomorphism.** Under the
hypotheses of `TauCeti.Floer.bijective_stationarySobolevOperator_ofComplexModule`, the realization
of `D ξ = ∂s ξ + i (∂t ξ - S_t ξ)` is an isomorphism of Banach spaces
`W^{1,2}(ℝ × S¹, F) ≃ L²(ℝ × S¹, F)`; in particular its inverse is bounded. -/
def stationarySobolevEquiv {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) :
    H1 F ≃L[ℝ] Lp F 2 stripMeasure :=
  ContinuousLinearEquiv.ofBijective
    (stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
      fun t : ℝ ↦ S t)
    (LinearMap.ker_eq_bot.2 (bijective_stationarySobolevOperator_ofComplexModule hS₁ hS hdet).1)
    (LinearMap.range_eq_top.2 (bijective_stationarySobolevOperator_ofComplexModule hS₁ hS hdet).2)

/-- The isomorphism `TauCeti.Floer.stationarySobolevEquiv` is the Sobolev realization of the
stationary cylinder operator. -/
@[simp]
theorem coe_stationarySobolevEquiv {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) :
    (stationarySobolevEquiv hS₁ hS hdet : H1 F →L[ℝ] Lp F 2 stripMeasure) =
      stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        fun t : ℝ ↦ S t :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- The isomorphism `TauCeti.Floer.stationarySobolevEquiv` acts as the Sobolev realization of the
stationary cylinder operator. -/
@[simp]
theorem coeFn_stationarySobolevEquiv {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) :
    ⇑(stationarySobolevEquiv hS₁ hS hdet) =
      ⇑(stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        fun t : ℝ ↦ S t) :=
  ContinuousLinearEquiv.coeFn_ofBijective _ _ _

/-- The inverse of `TauCeti.Floer.stationarySobolevEquiv` is a right inverse of the Sobolev
realization of the stationary cylinder operator. -/
@[simp]
theorem stationarySobolevOperator_stationarySobolevEquiv_symm_apply
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) (η : Lp F 2 stripMeasure) :
    stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun t : ℝ ↦ S t) ((stationarySobolevEquiv hS₁ hS hdet).symm η) = η :=
  ContinuousLinearEquiv.ofBijective_apply_symm_apply _ _ _ η

/-- The inverse of `TauCeti.Floer.stationarySobolevEquiv` is a left inverse of the Sobolev
realization of the stationary cylinder operator. -/
@[simp]
theorem stationarySobolevEquiv_symm_stationarySobolevOperator_apply
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) :
      F →ₗ[ℝ] F) ≠ 0) (ξ : H1 F) :
    (stationarySobolevEquiv hS₁ hS hdet).symm
        (stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
          (fun t : ℝ ↦ S t) ξ) = ξ :=
  ContinuousLinearEquiv.ofBijective_symm_apply_apply _ _ _ ξ

end Unitary

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (jet jet_apply stripMeasure jetLp jetLp_mem_jetClosure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The coefficients of the linearization at a stationary cylinder.** Let `x` be an orbit of the
time-dependent Hamiltonian `H` and `u(s, t) = x(t)` the stationary cylinder over it. The coefficient
field on jets of the linearized Floer operator at `u` is that of the stationary cylinder operator
`∂s + J_t(x(t)) (∂t - S_t)` with `S_t = dX_{H_t}(x(t))`. -/
theorem floerJetCoeff_eq_stationaryJetCoeff (ω : SymplecticForm V)
    (J : ℝ → V → AlmostComplexStructure V) (H : ℝ → V → ℝ) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) :
    ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ x w.2) =
      Floer.stationaryJetCoeff (fun t ↦ J t (x t))
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) := by
  funext z
  refine ContinuousLinearMap.ext fun v ↦ ?_
  -- Compare the two operators on the constant section `v.1`, whose derivatives vanish.
  have h := ω.floerLinearization_eq_stationaryCylinderOperator J H hx (fun _ ↦ v.1) z
  rw [floerLinearization_eq_add, Floer.stationaryCylinderOperator_def] at h
  simp only [fderiv_const_apply, zero_apply, map_zero, zero_add, zero_sub] at h
  rw [floerJetCoeff_apply, Floer.stationaryJetCoeff_apply, h]
  simp [sub_eq_add_neg, add_assoc]

section Weighted

/-! ### The weighted operator at a stationary cylinder in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The weighted operator at a stationary cylinder is a stationary cylinder operator.** For the
complex structure `i` of `F`, the coefficient field of `D_u - δ` at the stationary cylinder
`u(s, t) = x(t)`, with Floer data `(i, 0, H_t)`, is that of the stationary cylinder operator
`∂s + i (∂t - (S_t - δ i))` with `S_t = dX_{H_t}(x(t))`, since `-δ = i (δ i)`. The loop `x` need
not be an orbit of `H`. -/
theorem floerJetCoeff_sub_smul_fst_eq_stationaryJetCoeff (ω : SymplecticForm F) (H : ℝ → F → ℝ)
    (x : ℝ → F) (δ : ℝ) (z : ℝ × ℝ) :
    ω.floerJetCoeff
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z - δ • fst ℝ F (F × F) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
          δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) z := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [floerJetCoeff_const]
  simp [Floer.stationaryJetCoeff_apply, AlmostComplexStructure.ofComplexModule_apply, smul_smul,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- **The weighted operator at a stationary cylinder is invertible away from the spectrum.** Let
`F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, let `H` be a one-periodic, jointly `C³` time-dependent Hamiltonian and `x` a
one-periodic `C¹` loop, and let `δ` be a real number such that the shifted field
`dX_{H_t}(x(t)) - δ i` has a nondegenerate return map, `det (1 - Ψ(1)) ≠ 0`; for an orbit `x` of
`H` this says that `δ` is not an eigenvalue of the asymptotic operator at `x`. Then at the
stationary cylinder `u(s, t) = x(t)`, with Floer data `(i, 0, H_t)`, the realization
`D_u - δ : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator with the constant
weight slope `δ` is an isomorphism of Banach spaces. -/
theorem isInvertible_floerWeightedSobolevOperator_comp_snd (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ}
    (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Function.Periodic H 1) {x : ℝ → F}
    (hx : ContDiff ℝ 1 x) (hxp : Function.Periodic x 1) {δ : ℝ}
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
        δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) fun _ ↦ δ).IsInvertible := by
  obtain ⟨S, hS, hS₁⟩ := ω.exists_loop_eq_fderiv_hamiltonianVectorField hH hHp hx hxp
  -- `S_t = dX_{H_t}(x(t))` is infinitesimally symplectic for `Im ⟪·, ·⟫`, and so is `S_t - δ i`.
  have hSω (θ : AddCircle (1 : ℝ)) (v w : F) :
      (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0 := by
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [hS, ← hω, ← hω]
    exact ω.apply_fderiv_hamiltonianVectorField_add
      ((hH.of_le (by norm_num)).comp (contDiff_prodMk_right t)).contDiffAt v w
  set S' := S - δ • ContinuousMap.const _ (Complex.I • ContinuousLinearMap.id ℝ F)
  have hS'f : (fun t : ℝ ↦ S' t) = fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
      δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap := by
    ext t v
    simp [S', hS, AlmostComplexStructure.ofComplexModule_apply]
  have hS'₁ : ContDiff ℝ 1 fun t : ℝ ↦ S' t :=
    hS₁.sub (contDiff_const (c := δ • Complex.I • ContinuousLinearMap.id ℝ F))
  rw [← hS'f] at hdet
  simp only [floerWeightedSobolevOperator_def, floerJetCoeff_sub_smul_fst_eq_stationaryJetCoeff,
    ← hS'f, ← Floer.stationarySobolevOperator_def]
  exact ⟨Floer.stationarySobolevEquiv hS'₁
    (CircleSobolev.im_inner_sub_smul_const_I_add_eq_zero 1 hSω δ) hdet,
    Floer.coe_stationarySobolevEquiv ..⟩

end Weighted

section Stationary

/-! ### The stationary cylinder at a nondegenerate orbit -/

variable (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 2 (Function.uncurry H)) {x : ℝ → V}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
  {J : ℝ → V → AlmostComplexStructure V}
  (hJc : Continuous fun t ↦ (J t (x t)).toLinearMap.toContinuousLinearMap)
  (hJx : ∀ t, ω.Compatible (J t (x t)))

include hX hH hx hJc hJx in
/-- **The linearized Floer operator at a nondegenerate orbit is bounded below on `W^{1,2}`.**
Let `x` be an orbit of a jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is
globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t(y)`
be a family of almost complex structures that is continuous and `ω`-compatible along `x`. At the
stationary cylinder `u(s, t) = x(t)`, the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of
the linearized Floer operator, which is the translation-invariant operator
`∂s + J_t(x(t)) (∂t - dX_{H_t}(x(t)))`, satisfies `‖ξ‖_{W^{1,2}} ≤ K ‖D_u ξ‖_{L²}` for a
constant `K`. -/
theorem exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ C : ℝ≥0, ∀ ξ : H1 V, ‖ξ‖ ≤ C * ‖ω.floerSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ x w.2) ξ‖ := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  rw [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω J H hx,
    ← Floer.stationarySobolevOperator_def]
  exact Floer.exists_forall_norm_le_mul_norm_stationarySobolevOperator hJx hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt)
    (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc)
    (ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hH hx hnd)

include hX hH hx hJc hJx in
/-- **The linearized Floer operator at a nondegenerate orbit is injective on `W^{1,2}`.** Under the
hypotheses of `exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt`,
the realization of the linearized Floer operator at the stationary cylinder `u(s, t) = x(t)` has
trivial kernel. -/
theorem ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).ker = ⊥ := by
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt ω hX hH hx hJc
      hJx hnd
  exact LinearMap.ker_eq_bot.2 (ContinuousLinearMap.antilipschitz_of_bound _ hC).injective

end Stationary

end TauCeti.SymplecticForm
