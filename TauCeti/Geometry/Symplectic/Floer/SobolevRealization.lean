/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import Mathlib.Analysis.Normed.Operator.Prod

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
  `TauCeti.CylinderSobolev.H1`. On the jet of a test section it is `D_u ξ`
  (`TauCeti.SymplecticForm.floerSobolevOperator_jetL_ae_eq`), provided its coefficients are
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
  rw [floerJetCoeff_apply, floerLinearization_eq_add, jet_apply, stdComplexLineReal_eq,
    stdComplexLineImag_eq]

/-- The linearized Floer operator `D_u` along `u`, as an operator from the Sobolev space
`W^{1,2}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.H1`) to `L²(ℝ × S¹, V)`. It is `0` by convention
when the coefficients of `D_u` are not essentially bounded on the cylinder. -/
def floerSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator (ω.floerJetCoeff J Ks Kt u)).comp (H1 V).subtypeL

/-- On the jet of a test section `ξ`, the Sobolev realization of the linearized Floer operator is
`D_u ξ`, when the coefficients of `D_u` are essentially bounded on the cylinder. -/
theorem floerSobolevOperator_jetL_ae_eq (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerJetCoeff J Ks Kt u) ∞ stripMeasure) (ξ : testSection V) :
    ω.floerSobolevOperator J Ks Kt u ⟨jetL V ξ, jetL_mem_H1 ξ⟩ =ᵐ[stripMeasure]
      ω.floerLinearization J Ks Kt u ξ := by
  filter_upwards [jetOperator_jetL_ae_eq hM ξ] with z hz
  rw [floerSobolevOperator, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hz,
    floerJetCoeff_jet]

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
`u` a `C¹` map whose loops converge uniformly to orbits `xm` at `-∞` and `xp` at `+∞`, with slice
defect `∂t u - X_{H_t}(u)` tending uniformly to zero at both ends. Then the coefficient field of
the linearized Floer operator of the datum `K = H_t dt` is essentially bounded on the cylinder. -/
theorem memLp_floerJetCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
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
  obtain ⟨Cu, hCu⟩ := exists_forall_norm_le_of_tendstoUniformlyOn hu.continuous
    (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt).continuousOn
    (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt).continuousOn huxm huxp
  obtain ⟨Cδ, hCδ⟩ := exists_forall_norm_le_of_tendstoUniformlyOn hδc continuousOn_const
    continuousOn_const hδm hδp
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

/-- The semi-Fredholm estimate along a Floer trajectory, in the form consumed by Peetre's argument
on the cylinder. -/
private theorem exists_estimate_floerJetCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
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
    ∃ C T : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
            ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerJetCoeff
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u z (jet ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  obtain ⟨C, -, T, hest⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    hX hH hxm hndm hxp hndp hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  refine ⟨C, T, fun ξ hξ hper a b hab hvan ↦ ?_⟩
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
  obtain ⟨C, T, hest⟩ := exists_estimate_floerJetCoeff ω hX hH hxm hndm hxp hndp hJ hJxm hJxp hu
    hJu huxm huxp hδm hδp
  exact finiteDimensional_ker_jetOperator_comp_subtypeL
    (ω.memLp_floerJetCoeff hH hxm hxp hJ hu huxm huxp hδm hδp) hest

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
  obtain ⟨C, T, hest⟩ := exists_estimate_floerJetCoeff ω hX hH hxm hndm hxp hndp hJ hJxm hJxp hu
    hJu huxm huxp hδm hδp
  exact isClosed_range_jetOperator_comp_subtypeL
    (ω.memLp_floerJetCoeff hH hxm hxp hJ hu huxm huxp hδm hδp) hest

end TauCeti.SymplecticForm
