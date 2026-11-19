/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Normed.Group.Basic
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
  (`TauCeti.SymplecticForm.isClosed_range_floerSobolevOperator`). Both are proved as the case
  `c = 0` of the weighted results below.

The same holds on Sobolev spaces with an exponential weight `e^{κ(s)}` whose slope `c = κ'` is
continuous and equal to constants `δ±` near `±∞`. Multiplication by `e^{κ}` identifies them with the
unweighted spaces, and turns `D_u` into `D_u - c(s)`
(`TauCeti.SymplecticForm.floerLinearization_exp_neg_smul`), realized on `W^{1,2}` as
`TauCeti.SymplecticForm.floerWeightedSobolevOperator`, which acts pointwise by the coefficient
field of `D_u - c(s)` (`TauCeti.SymplecticForm.coeFn_floerWeightedSobolevOperator`); along a Floer
trajectory, and for a bounded slope, these coefficients are bounded
(`TauCeti.SymplecticForm.memLp_floerJetCoeff_sub_smul_fst`). The weights need not be small: if the
fields `dX_{H_t}(x±(t)) - δ± J_t(x±(t))` have nondegenerate return maps (for one-periodic `H`, `J`
and `x±`, if `δ±` are not eigenvalues of the asymptotic operators at `x±`), the weighted operator
has finite-dimensional kernel
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerWeightedSobolevOperator`) and closed range
(`TauCeti.SymplecticForm.isClosed_range_floerWeightedSobolevOperator`). Here the asymptotic loops
need only be continuous, and their nondegeneracy as Hamiltonian orbits is replaced by that of the
shifted fields.

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

/-! ### The operator on exponentially weighted Sobolev spaces -/

/-- The linearized Floer operator `D_u` along `u`, conjugated by an exponential weight `e^{κ(s)}`
of slope `c = κ'`, as an operator from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, V)`: the first-order
operator `ξ ↦ D_u ξ - c(s) ξ`. Since `D_u (e^{-κ} ξ) = e^{-κ} (D_u ξ - κ' ξ)`
(`TauCeti.SymplecticForm.floerLinearization_exp_neg_smul`), it is `D_u` acting between the
Sobolev spaces with weight `e^{κ(s)}`, read through multiplication by `e^{κ(s)}`. It is `0` by
convention when its coefficients are not essentially bounded on the cylinder. -/
def floerWeightedSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (c : ℝ → ℝ) : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator fun z ↦ ω.floerJetCoeff J Ks Kt u z - c z.1 • fst ℝ V (V × V)).comp
    (H1 V).subtypeL

/-- The definition of `TauCeti.SymplecticForm.floerWeightedSobolevOperator`: the first-order
operator `TauCeti.CylinderSobolev.jetOperator` of the coefficient field of `D_u - c(s)` on jets,
restricted to `TauCeti.CylinderSobolev.H1`. -/
theorem floerWeightedSobolevOperator_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (c : ℝ → ℝ) :
    ω.floerWeightedSobolevOperator J Ks Kt u c =
      (jetOperator fun z ↦ ω.floerJetCoeff J Ks Kt u z - c z.1 • fst ℝ V (V × V)).comp
        (H1 V).subtypeL :=
  (rfl)

/-- Without weight, the weighted operator is the Sobolev realization of `D_u`. -/
@[simp]
theorem floerWeightedSobolevOperator_zero (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) :
    ω.floerWeightedSobolevOperator J Ks Kt u 0 = ω.floerSobolevOperator J Ks Kt u := by
  simp only [floerWeightedSobolevOperator_def, floerSobolevOperator_def, Pi.zero_apply, zero_smul,
    sub_zero]

/-- The weighted operator acts pointwise by the coefficient field of `D_u - c(s)` on jets, when
these coefficients are essentially bounded on the cylinder. -/
theorem coeFn_floerWeightedSobolevOperator (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {c : ℝ → ℝ}
    (hM : MemLp (fun z ↦ ω.floerJetCoeff J Ks Kt u z - c z.1 • fst ℝ V (V × V)) ∞ stripMeasure)
    (x : H1 V) :
    ω.floerWeightedSobolevOperator J Ks Kt u c x =ᵐ[stripMeasure] fun z ↦
      (ω.floerJetCoeff J Ks Kt u z - c z.1 • fst ℝ V (V × V))
        ((x : Lp (V × V × V) 2 stripMeasure) z) :=
  coeFn_jetOperator hM x

/-- On the jet of a test section `ξ`, the weighted operator is `D_u ξ - c(s) ξ`, when its
coefficients are essentially bounded on the cylinder. -/
theorem floerWeightedSobolevOperator_jetₗ_ae_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {c : ℝ → ℝ}
    (hM : MemLp (fun z ↦ ω.floerJetCoeff J Ks Kt u z - c z.1 • fst ℝ V (V × V)) ∞ stripMeasure)
    (ξ : testSection V) :
    ω.floerWeightedSobolevOperator J Ks Kt u c ⟨jetₗ V ξ, jetₗ_mem_H1 ξ⟩ =ᵐ[stripMeasure]
      fun z ↦ ω.floerLinearization J Ks Kt u ξ z - c z.1 • (ξ : ℝ × ℝ → V) z := by
  filter_upwards [coeFn_floerWeightedSobolevOperator ω hM ⟨jetₗ V ξ, jetₗ_mem_H1 ξ⟩, coeFn_jetₗ ξ]
    with z h₁ h₂
  rw [h₁, h₂]
  simp only [sub_apply, smul_apply, coe_fst', floerJetCoeff_jet]
  simp only [jet_apply]

/-- **The coefficients of the weighted linearized Floer operator along a Floer trajectory are
bounded.** Under the hypotheses of `TauCeti.SymplecticForm.memLp_floerJetCoeff`, and for a
measurable bounded `c : ℝ → ℝ`, the coefficient field of `D_u - c(s)` on jets is essentially bounded
on the cylinder. -/
theorem memLp_floerJetCoeff_sub_smul_fst (ω : SymplecticForm V) {H : ℝ → V → ℝ}
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
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Measurable c) {B : ℝ} (hB : ∀ s, ‖c s‖ ≤ B) :
    MemLp (fun z ↦ ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z - c z.1 • fst ℝ V (V × V)) ∞ stripMeasure := by
  refine (ω.memLp_floerJetCoeff hH hJ hu huxm huxp hδm hδp).sub
    (memLp_top_of_bound ((hc.comp measurable_fst).aestronglyMeasurable.smul
      aestronglyMeasurable_const) B (Eventually.of_forall fun z ↦ ?_))
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (norm_fst_le ℝ V (V × V)) (norm_nonneg _)).trans
    ((mul_one _).trans_le (hB z.1))

/-- The weighted semi-Fredholm estimate along a Floer trajectory, in the form consumed by
Peetre's argument on the cylinder. -/
private theorem exists_estimate_floerJetCoeff_sub_smul_fst (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxp : Continuous xp) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Continuous c) {R δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xm t) -
        δm • (J t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xp t) -
        δp • (J t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C T : ℝ, HasSemiFredholmEstimate (fun z ↦ ω.floerJetCoeff
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u z -
        c z.1 • fst ℝ V (V × V)) C T := by
  obtain ⟨C, -, T, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add hH hxm hxp hJ
      hJxm hJxp hu hJu huxm huxp hδm hδp hc hcm hcp hdetm hdetp
  refine ⟨C, T, hasSemiFredholmEstimate_iff.2 fun ξ hξ hper a b hab hvan ↦ ?_⟩
  simp only [sub_apply, smul_apply, coe_fst', floerJetCoeff_jet]
  simpa only [jet_apply, stdComplexLineReal_eq, stdComplexLineImag_eq] using
    hest hξ hper hab hvan

/-- **The weighted linearized Floer operator along a Floer trajectory has finite-dimensional
kernel.** Let `u` be a Floer trajectory of `K = H_t dt`, with loops converging uniformly to
continuous loops `xm` at `-∞` and `xp` at `+∞` and slice defect tending to zero at both ends, as
in `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add`, and let the
slope `c` of the weight be continuous and equal to `δm` near `-∞` and to `δp` near `+∞`, where
the shifted fields `dX_{H_t}(x±(t)) - δ± J_t(x±(t))` have nondegenerate return maps; for
one-periodic `H`, `J` and `x±` this says that `δ±` are not eigenvalues of the asymptotic operators
at `x±`. Then the realization
`D_u - c(s) : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of `D_u` conjugated by the weight `e^{κ(s)}`,
`κ' = c`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerWeightedSobolevOperator (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxp : Continuous xp) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Continuous c) {R δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xm t) -
        δm • (J t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xp t) -
        δp • (J t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    FiniteDimensional ℝ (ω.floerWeightedSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        u c).ker := by
  obtain ⟨C, T, hest⟩ := exists_estimate_floerJetCoeff_sub_smul_fst ω hH hxm hxp hJ hJxm hJxp hu hJu
    huxm huxp hδm hδp hc hcm hcp hdetm hdetp
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_eventually_eq hc
    (eventually_atBot.2 ⟨-R, hcm⟩) (eventually_atTop.2 ⟨R, hcp⟩)
  exact finiteDimensional_ker_jetOperator_comp_subtypeL
    (memLp_floerJetCoeff_sub_smul_fst ω hH hJ hu huxm huxp hδm hδp hc.measurable hB) hest

/-- **The weighted linearized Floer operator along a Floer trajectory has closed range.** Under
the hypotheses of `TauCeti.SymplecticForm.finiteDimensional_ker_floerWeightedSobolevOperator`,
the realization `D_u - c(s) : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of `D_u` conjugated by the
weight `e^{κ(s)}`, `κ' = c`, has closed range. -/
theorem isClosed_range_floerWeightedSobolevOperator (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxp : Continuous xp) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Continuous c) {R δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xm t) -
        δm • (J t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xp t) -
        δp • (J t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    IsClosed ((ω.floerWeightedSobolevOperator
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        u c).range : Set (Lp V 2 stripMeasure)) := by
  obtain ⟨C, T, hest⟩ := exists_estimate_floerJetCoeff_sub_smul_fst ω hH hxm hxp hJ hJxm hJxp hu hJu
    huxm huxp hδm hδp hc hcm hcp hdetm hdetp
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_eventually_eq hc
    (eventually_atBot.2 ⟨-R, hcm⟩) (eventually_atTop.2 ⟨R, hcp⟩)
  exact isClosed_range_jetOperator_comp_subtypeL
    (memLp_floerJetCoeff_sub_smul_fst ω hH hJ hu huxm huxp hδm hδp hc.measurable hB) hest

/-! ### The unweighted operator -/

/-- **The linearized Floer operator along a Floer trajectory has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`
(a Floer trajectory `u` of `K = H_t dt` between nondegenerate one-periodic orbits `xm` and `xp`),
the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator has
finite-dimensional kernel. This is the case `c = 0` of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerWeightedSobolevOperator`. -/
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
  rw [← floerWeightedSobolevOperator_zero]
  exact ω.finiteDimensional_ker_floerWeightedSobolevOperator hH
    (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt)
    (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt) hJ hJxm hJxp hu hJu huxm huxp
    hδm hδp continuous_const (R := 0) (δm := 0) (δp := 0) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
      hX hH hxm hndm _)
    (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
      hX hH hxp hndp _)

/-- **The linearized Floer operator along a Floer trajectory has closed range on `W^{1,2}`.**
Under the hypotheses of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator`, the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator has closed range.
This is the case `c = 0` of `TauCeti.SymplecticForm.isClosed_range_floerWeightedSobolevOperator`. -/
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
  rw [← floerWeightedSobolevOperator_zero]
  exact ω.isClosed_range_floerWeightedSobolevOperator hH
    (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt)
    (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt) hJ hJxm hJxp hu hJu huxm huxp
    hδm hδp continuous_const (R := 0) (δm := 0) (δp := 0) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
      hX hH hxm hndm _)
    (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
      hX hH hxp hndp _)

end TauCeti.SymplecticForm
