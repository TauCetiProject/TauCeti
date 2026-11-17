/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.SpectralGap
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Topology.UniformSpace.UniformConvergence.Bounded

/-!
# The linearized Floer operator on `W^{1,2}` of the cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `D_u` be the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u : ℝ × ℝ → V` of period one
in `t`, a section-level differential operator

`D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + A(z) ξ`,

with zeroth-order part `A = TauCeti.SymplecticForm.floerLinearizationCoeff`. This file realizes
`D_u` as a bounded operator `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` and proves that along a Floer
trajectory between nondegenerate one-periodic orbits it has finite-dimensional kernel and closed
range: the Fredholm property of `D_u` minus the finiteness of its cokernel.

* `TauCeti.SymplecticForm.floerJetCoeff` is the coefficient field of `D_u` on jets:
  `(v, v_s, v_t) ↦ v_s + J(z, u z) v_t + A(z) v`, so that on the jet `(ξ, ∂s ξ, ∂t ξ)` of a section
  it gives `D_u ξ` (`TauCeti.SymplecticForm.floerJetCoeff_jet`).
* `TauCeti.SymplecticForm.floerSobolevOperator` is the resulting operator on the Sobolev space
  `TauCeti.CylinderSobolev.H1` (`TauCeti.SymplecticForm.floerSobolevOperator_def`). It acts
  pointwise by the coefficient field (`TauCeti.SymplecticForm.coeFn_floerSobolevOperator`), and on
  the jet of a test section it is `D_u ξ`
  (`TauCeti.SymplecticForm.floerSobolevOperator_jetₗ_ae_eq`), provided its coefficients are
  essentially bounded on the cylinder.
* Along a Floer trajectory of `K = H_t dt`, whose loops and slice defect `∂t u - X_{H_t}(u)`
  converge uniformly at both ends, the coefficients are bounded
  (`TauCeti.SymplecticForm.memLp_floerJetCoeff`).
* If moreover the asymptotic orbits are nondegenerate, the semi-Fredholm estimate
  `TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`
  holds, and Peetre's argument on the cylinder
  (`TauCeti.CylinderSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`,
  `TauCeti.CylinderSobolev.isClosed_range_jetOperator_comp_subtypeL`) gives finite-dimensional
  kernel (`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator`) and closed range
  (`TauCeti.SymplecticForm.isClosed_range_floerSobolevOperator`).
* At the stationary cylinder `u(s, t) = x(t)` over a nondegenerate orbit `x`, `D_u` is the
  translation-invariant operator `∂s + J_t(x(t)) (∂t - dX_{H_t}(x(t)))`, and the spectral gap
  estimate `TauCeti.Floer.exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator` bounds
  every test section in `L²` by `D_u`. So `D_u` is bounded below on `W^{1,2}`, `‖ξ‖ ≤ K ‖D_u ξ‖`
  (`exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt`), and injective
  (`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt`). This is
  the injective half of the invertibility of `D_u` at a stationary cylinder; its surjectivity
  is not proved here.

The finiteness of the cokernel, hence the Fredholm property and the index, needs the same estimate
for the formal adjoint of `D_u`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` along a Floer
  trajectory.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Peetre's argument.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open ContinuousLinearMap (norm_fst_le norm_snd_le)
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field of the linearized Floer operator on jets: at `z`, the linear map
`(v, v_s, v_t) ↦ v_s + J(z, u z) v_t + A(z) v`, where `A` is the zeroth-order part
`TauCeti.SymplecticForm.floerLinearizationCoeff`. -/
def floerJetCoeff (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V →L[ℝ] V :=
  (fst ℝ V V).comp (snd ℝ V (V × V)) + (J z (u z)).comp ((snd ℝ V V).comp (snd ℝ V (V × V))) +
    (ω.floerLinearizationCoeff J Ks Kt u z).comp (fst ℝ V (V × V))

/-- The coefficient field of the linearized Floer operator, evaluated on a jet. -/
theorem floerJetCoeff_apply (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V × V × V) :
    ω.floerJetCoeff J Ks Kt u z v =
      v.2.1 + J z (u z) v.2.2 + ω.floerLinearizationCoeff J Ks Kt u z v.1 :=
  (rfl)

/-- On the jet `(ξ, ∂s ξ, ∂t ξ)` of a section, the coefficient field gives the linearized Floer
operator `D_u ξ`. -/
@[simp]
theorem floerJetCoeff_jet (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerJetCoeff J Ks Kt u z (jet ξ z) = ω.floerLinearization J Ks Kt u ξ z := by
  simp only [floerJetCoeff_apply, floerLinearization_eq_add, jet_apply, stdComplexLineReal_eq,
    stdComplexLineImag_eq]

/-- The linearized Floer operator `D_u` along `u`, as an operator from the Sobolev space
`W^{1,2}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.H1`) to `L²(ℝ × S¹, V)`. It is `0` by convention
when the coefficients of `D_u` are not essentially bounded on the cylinder. -/
def floerSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator (ω.floerJetCoeff J Ks Kt u)).comp (H1 V).subtypeL

/-- The definition of the Sobolev realization of the linearized Floer operator: the first-order
operator `TauCeti.CylinderSobolev.jetOperator` of the coefficient field on jets, restricted to
`TauCeti.CylinderSobolev.H1`. -/
theorem floerSobolevOperator_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) :
    ω.floerSobolevOperator J Ks Kt u =
      (jetOperator (ω.floerJetCoeff J Ks Kt u)).comp (H1 V).subtypeL :=
  (rfl)

/-- When the coefficients of `D_u` are essentially bounded on the cylinder, the Sobolev realization
of the linearized Floer operator acts pointwise on an `L²` jet `x ∈ H1` by the coefficient field. -/
theorem coeFn_floerSobolevOperator (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure) (x : H1 V) :
    ω.floerSobolevOperator J Ks Kt u x =ᵐ[stripMeasure]
      fun z ↦ ω.floerJetCoeff J Ks Kt u z ((x : Lp (V × V × V) 2 stripMeasure) z) :=
  coeFn_jetOperator hM x

/-- On the jet of a test section `ξ`, the Sobolev realization of the linearized Floer operator is
`D_u ξ`, when the coefficients of `D_u` are essentially bounded on the cylinder. -/
theorem floerSobolevOperator_jetₗ_ae_eq (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure) (ξ : testSection V) :
    ω.floerSobolevOperator J Ks Kt u ⟨jetₗ V ξ, jetₗ_mem_H1 ξ⟩ =ᵐ[stripMeasure]
      ω.floerLinearization J Ks Kt u ξ := by
  filter_upwards [coeFn_floerSobolevOperator ω hM ⟨jetₗ V ξ, jetₗ_mem_H1 ξ⟩, coeFn_jetₗ ξ]
    with z h₁ h₂
  rw [h₁, h₂, floerJetCoeff_jet]

/-- The norm of the coefficient field on jets is at most `1 + ‖J(z, u z)‖ + ‖A(z)‖`. -/
private theorem norm_floerJetCoeff_le (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖ω.floerJetCoeff J Ks Kt u z‖ ≤
      1 + ‖J z (u z)‖ + ‖ω.floerLinearizationCoeff J Ks Kt u z‖ := by
  refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_fst_le ℝ V V)).trans (norm_snd_le ℝ V (V × V)))
  · refine (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_snd_le ℝ V V)).trans (norm_snd_le ℝ V (V × V)))
  · exact (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (norm_fst_le ℝ V (V × V)))

/-- For the datum `K = H_t dt`, the zeroth-order part of the linearized Floer operator is bounded
by `‖dJ(u)‖ ‖∂t u - X_{H_t}(u)‖ + ‖J(u)‖ ‖dX_{H_t}(u)‖`. -/
private theorem norm_floerLinearizationCoeff_le (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V} (z : ℝ × ℝ) :
    ‖ω.floerLinearizationCoeff J (fun _ _ ↦ 0) (fun w ↦ H w.2) u z‖ ≤
      ‖fderiv ℝ (J z) (u z)‖ * ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ +
        ‖J z (u z)‖ * ‖fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z)‖ := by
  have hδ : fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z) =
      sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z := by
    rw [sliceDefect_def, stdComplexLineImag_eq]
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  simp only [floerLinearizationCoeff_apply, hamiltonianVectorField_const, fderiv_zero,
    Pi.zero_apply, zero_apply, sub_zero, hδ]
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ ‖fderiv ℝ (J z) (u z)‖ * ‖v‖ *
          ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ +
        ‖J z (u z)‖ * (‖fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z)‖ * ‖v‖) := by
        gcongr
        · exact (le_opNorm _ _).trans (by gcongr; exact le_opNorm _ _)
        · exact (le_opNorm _ _).trans (by gcongr; exact le_opNorm _ _)
    _ = _ := by ring

/-- For the datum `K = H_t dt` with `H` jointly `C²`, `J_t(y)` a `C¹` family and `u` a `C¹` map,
the coefficient field of the linearized Floer operator on jets is continuous. -/
private theorem continuous_floerJetCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) :
    Continuous (ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u) := by
  have hJ' : ∀ z, ContDiffAt ℝ 1 (Function.uncurry fun (w : ℝ × ℝ) y ↦
      (J w.2 y).toLinearMap.toContinuousLinearMap) (z, u z) := fun z ↦
    (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  have hHt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry fun w : ℝ × ℝ ↦ H w.2) (z, u z) := fun z ↦
    (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
  have hA : Continuous (ω.floerLinearizationCoeff
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u) :=
    continuous_iff_continuousAt.2 fun z ↦
      ω.continuousAt_floerLinearizationCoeff (hJ' z) contDiffAt_const (hHt z) hu.contDiffAt
  have hJu := hJ.continuous.comp (continuous_snd.prodMk hu.continuous)
  exact (continuous_const.add (hJu.clm_comp continuous_const)).add (hA.clm_comp continuous_const)

/-- **The coefficients of the linearized Floer operator along a Floer trajectory are bounded.**
Let `H` be a jointly `C²` Hamiltonian, `J_t(y)` a `C¹` family of almost complex structures and
`u` a `C¹` map whose loops converge uniformly to loops `xm` at `-∞` and `xp` at `+∞`, with slice
defect `∂t u - X_{H_t}(u)` tending uniformly to zero at both ends. Then the coefficient field of
the linearized Floer operator of the datum `K = H_t dt` is essentially bounded on the cylinder. -/
theorem memLp_floerJetCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    MemLp (ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ H w.2) u) ∞ stripMeasure := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap
  have hX := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) (K := H) hH
  -- The data as continuous functions of `(t, y)`.
  have hdJ : Continuous fun p : ℝ × V ↦
      fderiv ℝ (fun y ↦ (J p.1 y).toLinearMap.toContinuousLinearMap) p.2 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V) y ↦ (J p.1 y).toLinearMap.toContinuousLinearMap)
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) (contDiff_snd (n := 0)) (by simp)).continuous
  have hdX : Continuous fun p : ℝ × V ↦ fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V) y ↦ ω.hamiltonianVectorField (H p.1) y)
      (hX.comp (contDiff_fst.fst.prodMk contDiff_snd)) (contDiff_snd (n := 0)) (by simp)).continuous
  -- The slice defect and the map are bounded on the strip.
  have hδc : Continuous (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u) := by
    have h₁ := (hu.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := ((0 : ℝ), (1 : ℝ))))
    rw [show sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u = _ from
      funext (sliceDefect_def _ u)]
    exact h₁.sub (hX.continuous.comp (continuous_snd.prodMk hu.continuous))
  obtain ⟨Cu, hCu⟩ := exists_forall_norm_le_of_tendstoUniformlyOn isCompact_Icc
    hu.continuous.continuousOn huxm huxp
  obtain ⟨Cδ, hCδ⟩ := exists_forall_norm_le_of_tendstoUniformlyOn isCompact_Icc hδc.continuousOn hδm
    hδp
  set K : Set (ℝ × V) := Icc 0 1 ×ˢ Metric.closedBall 0 Cu
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 Cu)
  obtain ⟨BJ, hBJ⟩ := hK.exists_bound_of_continuousOn hJ.continuous.continuousOn
  obtain ⟨BdJ, hBdJ⟩ := hK.exists_bound_of_continuousOn hdJ.continuousOn
  obtain ⟨BdX, hBdX⟩ := hK.exists_bound_of_continuousOn hdX.continuousOn
  have hM := ω.continuous_floerJetCoeff hH hJ hu
  refine memLp_top_of_bound hM.aestronglyMeasurable (1 + BJ + (BdJ * Cδ + BJ * BdX)) ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
  obtain ⟨s, t⟩ := z
  have ht : t ∈ Icc (0 : ℝ) 1 := hz.2
  have hp : (t, u (s, t)) ∈ K := ⟨ht, mem_closedBall_zero_iff.2 (hCu s t ht)⟩
  have hJb : ‖J' (s, t) (u (s, t))‖ ≤ BJ := hBJ (t, u (s, t)) hp
  have hBJ0 : 0 ≤ BJ := (norm_nonneg _).trans hJb
  have hdJ : ‖fderiv ℝ (J' (s, t)) (u (s, t))‖ ≤ BdJ := hBdJ (t, u (s, t)) hp
  have hdX : ‖fderiv ℝ (ω.hamiltonianVectorField (H t)) (u (s, t))‖ ≤ BdX :=
    hBdX (t, u (s, t)) hp
  have hBdJ0 : 0 ≤ BdJ := le_trans (norm_nonneg (fderiv ℝ (J' (s, t)) (u (s, t)))) hdJ
  have hA_le : ‖ω.floerLinearizationCoeff J' (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t)‖ ≤
      BdJ * Cδ + BJ * BdX :=
    (norm_floerLinearizationCoeff_le ω (H := H) (J := J') (u := u) (s, t)).trans (add_le_add
      (mul_le_mul hdJ (hCδ s t ht) (norm_nonneg _) hBdJ0)
      (mul_le_mul hJb hdX (norm_nonneg _) hBJ0))
  exact (norm_floerJetCoeff_le ω _ _ _ _ (s, t)).trans (add_le_add (add_le_add le_rfl hJb) hA_le)

/-- **The semi-Fredholm estimate along a Floer trajectory**, in the form
`TauCeti.CylinderSobolev.HasSemiFredholmEstimate` consumed by Peetre's argument on the cylinder:
the estimate
`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`
for the coefficient field of the linearized Floer operator on jets. -/
theorem exists_hasSemiFredholmEstimate_floerJetCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C T : ℝ, HasSemiFredholmEstimate (ω.floerJetCoeff
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u)
      C T := by
  obtain ⟨C, -, T, hest⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    hX hH hxm hndm hxp hndp hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  refine ⟨C, T, hasSemiFredholmEstimate_iff.2 fun ξ hξ hper a b hab hvan ↦ ?_⟩
  simpa only [floerJetCoeff_jet, stdComplexLineReal_eq, stdComplexLineImag_eq] using
    hest hξ hper hab hvan

/-- **The linearized Floer operator along a Floer trajectory has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`
(a Floer trajectory `u` of `K = H_t dt` between nondegenerate one-periodic orbits `xm` and `xp`),
the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerSobolevOperator (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        u).ker := by
  obtain ⟨C, T, hest⟩ := exists_hasSemiFredholmEstimate_floerJetCoeff ω hX hH hxm hndm hxp hndp hJ
    hJxm hJxp hu hJu huxm huxp hδm hδp
  exact finiteDimensional_ker_jetOperator_comp_subtypeL
    (ω.memLp_floerJetCoeff hH hJ hu huxm huxp hδm hδp) hest

/-- **The linearized Floer operator along a Floer trajectory has closed range on `W^{1,2}`.**
Under the hypotheses of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator`, the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator has closed range. -/
theorem isClosed_range_floerSobolevOperator (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    IsClosed ((ω.floerSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        u).range : Set (Lp V 2 stripMeasure)) := by
  obtain ⟨C, T, hest⟩ := exists_hasSemiFredholmEstimate_floerJetCoeff ω hX hH hxm hndm hxp hndp hJ
    hJxm hJxp hu hJu huxm huxp hδm hδp
  exact isClosed_range_jetOperator_comp_subtypeL
    (ω.memLp_floerJetCoeff hH hJ hu huxm huxp hδm hδp) hest

end TauCeti.SymplecticForm

namespace TauCeti.Floer

open CylinderSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}
  {ξ : ℝ × ℝ → V}

omit [FiniteDimensional ℝ V] in
/-- The stationary cylinder operator vanishes wherever the jet of the map vanishes. -/
private theorem stationaryCylinderOperator_eq_zero_of_jet_eq_zero {z : ℝ × ℝ} (h : jet ξ z = 0) :
    stationaryCylinderOperator J S ξ z = 0 := by
  rw [jet_apply, Prod.mk_eq_zero, Prod.mk_eq_zero] at h
  simp only [stationaryCylinderOperator_def, stdComplexLineReal_eq, stdComplexLineImag_eq, h.1,
    h.2.1, h.2.2, map_zero, sub_zero, add_zero]

/-- **The `L²` estimate of the stationary cylinder operator on test sections.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, let each `S_t` be infinitesimally symplectic and
depend continuously on `t`, and suppose that `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1)` of
`ζ' = S_t ζ`. Then there is a constant `C` with `∫ ‖ξ‖² ≤ C ∫ ‖D ξ‖²` over the strip
`ℝ × [0, 1]` for every test section `ξ` of the cylinder, where `D = ∂s + J_t (∂t - S_t)`. This is
`TauCeti.Floer.exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator` with the forms
`g_t = ω(·, J_t ·)` replaced by the norm, to which they are uniformly equivalent for
`t ∈ [0, 1]`. -/
theorem exists_integral_norm_sq_le_mul_integral_norm_sq_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, ∀ ξ ∈ testSection V, ∫ z, ‖ξ z‖ ^ 2 ∂stripMeasure ≤
      C * ∫ z, ‖stationaryCylinderOperator J S ξ z‖ ^ 2 ∂stripMeasure := by
  have hJc' : Continuous fun p : ℝ × V ↦ J p.1 p.2 := by
    simpa using (hJc.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨C, hC, hest⟩ :=
    exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator hJ hJc' hS hSc hdet
  -- The forms `g_t` are uniformly equivalent to the norm for `t ∈ [0, 1]`.
  obtain ⟨a, ha, b, -, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc hJc.continuousOn fun t _ ↦ (hJ t).tames
  refine ⟨a⁻¹ * C * b, fun ξ hξm ↦ ?_⟩
  obtain ⟨hξ, hper, -⟩ := mem_testSection_iff.1 hξm
  set D := stationaryCylinderOperator J S ξ
  have hDc : Continuous D := continuous_stationaryCylinderOperator hJc hSc (hξ.of_le one_le_two)
  have hgD : Integrable (fun z ↦ ω.associatedBilinForm (J z.2) (D z) (D z)) stripMeasure :=
    integrable_of_jet_eq_zero hξm (continuous_associatedBilinForm_apply_self hJc' hDc)
      fun z h ↦ by simp [D, stationaryCylinderOperator_eq_zero_of_jet_eq_zero h]
  have hdecay : Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0) := by
    simpa [Function.comp_def, jet_apply, stdComplexLineImag_eq, Prod.mk_zero_zero] using
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto
        (0 : V × V × V)).comp (tendsto_jet_comap_fst_cocompact hξm)
  obtain ⟨hgξ, hle⟩ := hest ξ hξ hper hdecay hgD
  have hstrip : MeasurableSet ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Icc
  -- Compare the norms with the forms `g_t` on the strip.
  have h₁ : ∫ z in univ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      a⁻¹ * ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (ξ z) (ξ z) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrable_of_jet_eq_zero hξm (hξ.continuous.norm.pow 2)
      fun z h ↦ ?_) (hgξ.const_mul _) hstrip fun z hz ↦ ?_
    · rw [jet_apply, Prod.mk_eq_zero] at h
      simp [h.1]
    · rw [le_inv_mul_iff₀ ha]
      exact (hab z.2 hz.2 _).1
  have h₂ : ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (D z) (D z) ≤
      b * ∫ z in univ ×ˢ Icc 0 1, ‖D z‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hgD ((integrable_of_jet_eq_zero hξm (hDc.norm.pow 2) fun z h ↦ by
      simp [D, stationaryCylinderOperator_eq_zero_of_jet_eq_zero h]).const_mul b) hstrip
      fun z hz ↦ (hab z.2 hz.2 _).2
  calc ∫ z in univ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2
      ≤ a⁻¹ * (C * (b * ∫ z in univ ×ˢ Icc 0 1, ‖D z‖ ^ 2)) :=
        h₁.trans (mul_le_mul_of_nonneg_left (hle.trans (mul_le_mul_of_nonneg_left h₂ hC))
          (inv_nonneg.2 ha.le))
    _ = a⁻¹ * C * b * ∫ z in univ ×ˢ Icc 0 1, ‖D z‖ ^ 2 := by ring

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open CylinderSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Stationary

/-! ### The stationary cylinder at a nondegenerate orbit -/

variable (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 2 (Function.uncurry H)) {x : ℝ → V}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
  {J : ℝ → V → AlmostComplexStructure V}
  (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
  (hJx : ∀ t, ω.Compatible (J t (x t)))

include hX hH hx hJ hJx in
/-- At the stationary cylinder over a nondegenerate orbit, the coefficients of the linearized Floer
operator are bounded and satisfy the semi-Fredholm estimate. -/
private theorem memLp_and_exists_hasSemiFredholmEstimate_floerJetCoeff_stationary
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    MemLp (ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ x w.2)) ∞ stripMeasure ∧
      ∃ C T : ℝ, HasSemiFredholmEstimate (ω.floerJetCoeff
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (fun w ↦ x w.2)) C T := by
  have hu : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ x w.2 :=
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH.of_le one_le_two) hx).comp
      contDiff_snd
  -- The loops of `u` and its slice defect do not depend on `s`, so they converge uniformly.
  have hc (f : ℝ → V) (l : Filter ℝ) : TendstoUniformlyOn (fun (_ : ℝ) t ↦ f t) f l (Icc 0 1) :=
    fun _ hU ↦ Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hU
  have h₀ (l : Filter ℝ) : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H t)) (fun w : ℝ × ℝ ↦ x w.2) (s, t)) 0 l (Icc 0 1) := by
    simpa only [sliceDefect_comp_snd_eq_zero hx, Pi.zero_apply] using hc 0 l
  exact ⟨ω.memLp_floerJetCoeff hH hJ hu (hc x _) (hc x _) (h₀ _) (h₀ _),
    ω.exists_hasSemiFredholmEstimate_floerJetCoeff hX hH hx hnd hx hnd hJ hJx hJx hu
      (fun z ↦ hJx z.2) (hc x _) (hc x _) (h₀ _) (h₀ _)⟩

include hX hH hx hJ hJx in
/-- **The global `L²` bound at a stationary cylinder.** At the stationary cylinder over a
nondegenerate orbit, the linearized Floer operator bounds every test section in `L²` over the whole
strip: `∫ ‖ξ‖² ≤ C ∫ ‖D ξ‖²`. This is the spectral gap estimate
`TauCeti.Floer.exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator` for the forms
`g_t = ω(·, J_t(x(t)) ·)`, which are uniformly equivalent to the norm for `t ∈ [0, 1]`. -/
private theorem exists_integral_norm_sq_le_mul_integral_floerJetCoeff_stationary
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ C : ℝ, ∀ ξ : testSection V, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C * ∫ z, ‖ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2
          ∂stripMeasure := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨C, hC⟩ := Floer.exists_integral_norm_sq_le_mul_integral_norm_sq_stationaryCylinderOperator
    (J := fun t ↦ J t (x t)) (S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) hJx
    (hJ.continuous.comp (continuous_id.prodMk hxc))
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt)
    (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc)
    (ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hH hx hnd)
  refine ⟨C, fun ξ ↦ ?_⟩
  simp only [floerJetCoeff_jet, floerLinearization_eq_stationaryCylinderOperator ω J H hx]
  exact hC ξ ξ.2

include hX hH hx hJ hJx in
/-- **The linearized Floer operator at a nondegenerate orbit is bounded below on `W^{1,2}`.**
Let `x` be an orbit of a jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is
globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t(y)`
be a `C¹` family of almost complex structures that is `ω`-compatible along `x`. At the stationary
cylinder `u(s, t) = x(t)`, the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the
linearized Floer operator, which is the translation-invariant operator
`∂s + J_t(x(t)) (∂t - dX_{H_t}(x(t)))`, satisfies `‖ξ‖_{W^{1,2}} ≤ K ‖D_u ξ‖_{L²}` for a
constant `K`. -/
theorem exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ C : ℝ≥0, ∀ ξ : H1 V, ‖ξ‖ ≤ C * ‖ω.floerSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ x w.2) ξ‖ := by
  obtain ⟨hM, C, T, hest⟩ :=
    memLp_and_exists_hasSemiFredholmEstimate_floerJetCoeff_stationary ω hX hH hx hJ hJx hnd
  obtain ⟨C', hL2⟩ :=
    exists_integral_norm_sq_le_mul_integral_floerJetCoeff_stationary ω hX hH hx hJ hJx hnd
  exact exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL hM hest hL2

include hX hH hx hJ hJx in
/-- **The linearized Floer operator at a nondegenerate orbit is injective on `W^{1,2}`.** Under the
hypotheses of `exists_forall_norm_le_mul_norm_floerSobolevOperator_of_isNondegenerateFixedPt`,
the realization of the linearized Floer operator at the stationary cylinder `u(s, t) = x(t)` has
trivial kernel. -/
theorem ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).ker = ⊥ := by
  obtain ⟨hM, C, T, hest⟩ :=
    memLp_and_exists_hasSemiFredholmEstimate_floerJetCoeff_stationary ω hX hH hx hJ hJx hnd
  obtain ⟨C', hL2⟩ :=
    exists_integral_norm_sq_le_mul_integral_floerJetCoeff_stationary ω hX hH hx hJ hJx hnd
  exact ker_jetOperator_comp_subtypeL_eq_bot hM hest hL2

end Stationary

end TauCeti.SymplecticForm
