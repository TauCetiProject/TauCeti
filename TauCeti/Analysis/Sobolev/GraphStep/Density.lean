/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Test functions are dense in vector-valued `W^{1,p}`

The first-order weak-derivative graph over the identity of `Lᵖ(E, F)` is the vector-valued
Sobolev space `W^{1,p}(E; F)`. For a finite-dimensional target `F` and `1 ≤ p < ∞`, smooth
compactly supported maps `E → F` are dense in it.

The proof is coordinatewise. A scalar Sobolev function `w` and a vector `v ∈ F` give the
vector-valued Sobolev function `w v`, with weak derivative `x ↦ ⟪∇w(x), ·⟫ v`
(`TauCeti.WeakDerivStep.ofW1pL`). In a basis `bᵢ` of `F` with coordinate functionals `ℓᵢ`,
every `u` is the sum of `ℓᵢ(u) bᵢ` (`TauCeti.WeakDerivStep.sum_ofW1pL_toW1pL`), where
`ℓᵢ(u)` is the scalar projection `TauCeti.WeakDerivStep.toW1pL`. Approximating each coordinate
by test functions in scalar `W^{1,p}` (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`) and
recombining gives the vector-valued statement.

The density lets estimates proved for smooth compactly supported paths, such as the energy
estimates for first-order operators `d/ds + A(s)`, pass to all Sobolev paths by continuity.

## Main declarations

* `TauCeti.WeakDerivStep.ofW1pL`: the Sobolev function `w v` for scalar `w` and a vector `v`.
* `TauCeti.WeakDerivStep.sum_ofW1pL_toW1pL`: reconstruction from coordinates in a basis.
* `TauCeti.WeakDerivStep.dense_setOf_contDiff_hasCompactSupport`: Sobolev functions with a
  smooth compactly supported representative are dense.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2. The vector-valued extension is
coordinatewise.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti.WeakDerivStep

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

section GradientSMul

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of `x ↦ w(x) v` in terms of the gradient of the scalar function `w`:
a vector `g` goes to the map `h ↦ ⟪g, h⟫ v`. -/
private def gradientSMulL (v : F) : E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E ℝ F (ContinuousLinearMap.toSpanSingleton ℝ v)).comp
    (innerSL ℝ)

private theorem gradientSMulL_apply (v : F) (g h : E) : gradientSMulL v g h = ⟪g, h⟫_ℝ • v := by
  simp [gradientSMulL]

private theorem norm_gradientSMulL_le (v : F) : ‖gradientSMulL (E := E) v‖ ≤ ‖v‖ := by
  refine (gradientSMulL v).opNorm_le_bound (norm_nonneg v) fun g ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [gradientSMulL_apply, norm_smul, Real.norm_eq_abs]
  calc |⟪g, h⟫_ℝ| * ‖v‖ ≤ ‖g‖ * ‖h‖ * ‖v‖ := by
        gcongr
        exact abs_real_inner_le_norm g h
    _ = ‖v‖ * ‖g‖ * ‖h‖ := by ring

end GradientSMul

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem hasWeakFDerivOn_ofW1p (v : F) (w : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
        ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL p (mu.restrict Omega) (W1p.value w)))
      ((gradientSMulL v).compLpL p (mu.restrict Omega) (W1p.gradient w)) := by
  rw [ContinuousLinearMap.id_apply]
  refine (((W1p.hasWeakFDerivOn w).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ v)).congr_ae
    (ContinuousLinearMap.coeFn_compLpL _ _).symm).congr_ae_deriv ?_
  filter_upwards [(gradientSMulL v).coeFn_compLpL (W1p.gradient w)] with x hx
  ext h
  simp [hx, gradientSMulL_apply]

/-- The vector-valued Sobolev function `x ↦ w(x) v` built from a scalar Sobolev function `w` and
a vector `v`. Its weak derivative is `x ↦ ⟪∇w(x), ·⟫ v`. -/
def ofW1pL (v : F) :
    W1p mu Omega p →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  LinearMap.mkContinuous
    { toFun := fun w ↦ mk _
        ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL p (mu.restrict Omega) (W1p.value w))
        ((gradientSMulL v).compLpL p (mu.restrict Omega) (W1p.gradient w))
        (hasWeakFDerivOn_ofW1p v w)
      map_add' := fun w w' ↦ ext_prev_weakFDeriv
        (by
          simp only [← prevL_apply, map_add]
          simp only [prevL_apply, prev_mk, ← W1p.valueL_apply, map_add])
        (by
          simp only [← weakFDerivL_apply, map_add]
          simp only [weakFDerivL_apply, weakFDeriv_mk, ← W1p.gradientL_apply, map_add])
      map_smul' := fun c w ↦ ext_prev_weakFDeriv
        (by
          simp only [← prevL_apply, map_smul]
          simp only [prevL_apply, prev_mk, ← W1p.valueL_apply, map_smul, RingHom.id_apply])
        (by
          simp only [← weakFDerivL_apply, map_smul]
          simp only [weakFDerivL_apply, weakFDeriv_mk, ← W1p.gradientL_apply, map_smul,
            RingHom.id_apply]) }
    (2 * ‖v‖) fun w ↦ by
      refine (norm_le_norm_prev_add_norm_weakFDeriv _ _).trans ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, prev_mk, weakFDeriv_mk]
      have hval := ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL p
        (mu.restrict Omega)).le_opNorm (W1p.value w)
      have hgrad := ((gradientSMulL v).compLpL p (mu.restrict Omega)).le_opNorm
        (W1p.gradient w)
      have h1 := (ContinuousLinearMap.toSpanSingleton ℝ v).norm_compLpL_le (p := p)
        (μ := mu.restrict Omega)
      rw [ContinuousLinearMap.norm_toSpanSingleton] at h1
      have h2 := ((gradientSMulL (E := E) v).norm_compLpL_le (p := p)
        (μ := mu.restrict Omega)).trans (norm_gradientSMulL_le v)
      calc _ ≤ ‖v‖ * ‖W1p.value w‖ + ‖v‖ * ‖W1p.gradient w‖ := by
            gcongr
            · exact hval.trans (by gcongr)
            · exact hgrad.trans (by gcongr)
        _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := by
            gcongr
            exacts [W1p.norm_value_le w, W1p.norm_gradient_le w]
        _ = 2 * ‖v‖ * ‖w‖ := by ring

/-- The field of `ofW1pL v w` is the scalar field of `w` times `v`. -/
@[simp]
theorem prev_ofW1pL (v : F) (w : W1p mu Omega p) :
    prev _ (ofW1pL v w) =
      (ContinuousLinearMap.toSpanSingleton ℝ v).compLpL p (mu.restrict Omega) (W1p.value w) := by
  simp [ofW1pL]

/-- The weak derivative of `ofW1pL v w` is almost everywhere `h ↦ ⟪∇w, h⟫ v`. -/
theorem weakFDeriv_ofW1pL_ae (v : F) (w : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ h : E,
      weakFDeriv _ (ofW1pL v w) x h = ⟪W1p.gradient w x, h⟫_ℝ • v := by
  simp only [ofW1pL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    weakFDeriv_mk]
  filter_upwards [(gradientSMulL v).coeFn_compLpL (W1p.gradient w)] with x hx h
  rw [hx, gradientSMulL_apply]

/-- **Reconstruction from coordinates.** In a basis `bᵢ` of a finite-dimensional target, a
vector-valued Sobolev function is the sum of its scalar coordinates times the basis vectors. -/
theorem sum_ofW1pL_toW1pL [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ∑ i, ofW1pL (b i) (toW1pL _ (b.coord i).toContinuousLinearMap u) = u := by
  ext1
  rw [← prevL_apply, map_sum]
  simp only [prevL_apply, prev_ofW1pL, value_toW1pL, ContinuousLinearMap.id_apply]
  exact (eq_sum_basis_compLpL b _).symm

/-- **Test functions are dense in vector-valued `W^{1,p}`.** For a finite-dimensional target and
`1 ≤ p < ∞`, the Sobolev functions on the whole space with a smooth compactly supported
representative `f` are dense; their weak derivative is then `fderiv ℝ f`. -/
theorem dense_setOf_contDiff_hasCompactSupport [FiniteDimensional ℝ F] (hp : p ≠ ⊤) :
    Dense {u : WeakDerivStep mu ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) |
      ∃ f : E → F, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        prev _ u =ᵐ[mu.restrict (⊤ : Opens E)] f ∧
        weakFDeriv _ u =ᵐ[mu.restrict (⊤ : Opens E)] fderiv ℝ f} := by
  classical
  let b := Module.finBasis ℝ F
  let R : (Fin (Module.finrank ℝ F) → W1p mu ⊤ p) →
      WeakDerivStep mu ⊤ p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict (⊤ : Opens E)))) :=
    fun w ↦ ∑ i, ofW1pL (b i) (w i)
  have hR : Continuous R :=
    continuous_finsetSum _ fun i _ ↦ (ofW1pL (b i)).continuous.comp (continuous_apply i)
  have htest :
      DenseRange (Pi.map fun (_ : Fin (Module.finrank ℝ F)) ↦ W1p.ofTestFunctionₗ mu ⊤ p) :=
    DenseRange.piMap fun _ ↦ W1p.denseRange_ofTestFunctionₗ_top hp
  -- The images of tuples of test functions have smooth compactly supported representatives.
  have hrange :
      R '' range (Pi.map fun (_ : Fin (Module.finrank ℝ F)) ↦ W1p.ofTestFunctionₗ mu ⊤ p) ⊆
      {u | ∃ f : E → F, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        prev _ u =ᵐ[mu.restrict (⊤ : Opens E)] f ∧
        weakFDeriv _ u =ᵐ[mu.restrict (⊤ : Opens E)] fderiv ℝ f} := by
    rintro _ ⟨_, ⟨φ, rfl⟩, rfl⟩
    let f : E → F := fun x ↦ ∑ i, φ i x • b i
    have hf : ContDiff ℝ ∞ f :=
      ContDiff.sum fun i _ ↦ (φ i).contDiff.smul contDiff_const
    have hcf : HasCompactSupport f := by
      rw [show f = ∑ i, fun x ↦ φ i x • b i from funext fun x ↦ by simp [f]]
      exact Finset.sum_induction _ HasCompactSupport (fun _ _ ↦ HasCompactSupport.add)
        HasCompactSupport.zero fun i _ ↦ (φ i).hasCompactSupport.smul_right
    have hprev : prev _ (R (Pi.map (fun _ ↦ W1p.ofTestFunctionₗ mu ⊤ p) φ))
        =ᵐ[mu.restrict (⊤ : Opens E)] f := by
      have hsum : prev _ (R (Pi.map (fun _ ↦ W1p.ofTestFunctionₗ mu ⊤ p) φ)) =
          ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (mu.restrict (⊤ : Opens E))
            (testFunctionLp p (φ i)) := by
        simp only [R, ← prevL_apply, map_sum]
        simp only [prevL_apply, Pi.map_apply, prev_ofW1pL, W1p.value_ofTestFunctionₗ]
      rw [hsum]
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i ↦
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (mu.restrict (⊤ : Opens E))
            (testFunctionLp p (φ i)),
        ae_all_iff.2 fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
          (μ := mu.restrict (⊤ : Opens E)) (testFunctionLp p (φ i)),
        ae_all_iff.2 fun i ↦ testFunctionLp_apply_ae (mu := mu) p (φ i)] with x hx hc ht
      simp only [hx, hc, ht, f, ContinuousLinearMap.toSpanSingleton_apply]
    refine ⟨f, hf, hcf, hprev, ?_⟩
    have hweak := (hasWeakFDerivOn_base_prev _
      (R (Pi.map (fun _ ↦ W1p.ofTestFunctionₗ mu ⊤ p) φ))).congr_ae hprev
    exact hweak.ae_eq_fderiv
      ((hf.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ (hf.differentiable (by simp)).differentiableAt
  intro u
  have hu : u = R fun i ↦ toW1pL _ (b.coord i).toContinuousLinearMap u :=
    (sum_ofW1pL_toW1pL b u).symm
  rw [hu]
  exact closure_mono hrange (map_mem_closure hR (htest _) fun _ h ↦ mem_image_of_mem R h)

end TauCeti.WeakDerivStep
