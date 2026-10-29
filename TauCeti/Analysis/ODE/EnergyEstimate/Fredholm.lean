/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.ODE.EnergyEstimate.Adjoint
public import TauCeti.Analysis.ODE.EnergyEstimate.Sobolev
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# The trajectory operator is Fredholm

Let `A : ℝ → End(E)` be a `C¹` family of symmetric operators on a finite-dimensional real inner
product space `E`, with invertible limits `A±` at `±∞` and with `A'` tending to zero at both ends.
This file proves that the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`) is a Fredholm operator.

The kernel of `D_A` is finite dimensional and its range is closed
(`TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator`,
`TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator`), so what remains is the cokernel.
Since the range is closed, the cokernel is the orthogonal complement of the range in `L²`. A path
`v` orthogonal to the range pairs to zero with `D_A (φ • e)` for every test function `φ` and every
vector `e`. By symmetry of `A` this says that `v` has weak derivative `A v`, so `v` lies in
`W^{1,2}(ℝ, E)` and solves the formal adjoint equation `-v' + A v = 0`: it is in the kernel of
`D_{-A}`. The family `-A` satisfies the same hypotheses as `A`, so this kernel is finite
dimensional, and hence so is the cokernel of `D_A`.

Conversely, by density of test functions in `W^{1,2}(ℝ, E)`, every element of the kernel of
`D_{-A}` is orthogonal to the range of `D_A`. The cokernel of `D_A` is therefore identified with
the kernel of `D_{-A}`, and the index of `D_A` is `dim ker D_A - dim ker D_{-A}`.

The inclusion of the orthogonal complement of the range in the kernel of `D_{-A}` needs neither
finite dimensionality of `E` nor any hypothesis on `A` beyond essential boundedness and
almost-everywhere symmetry, and is stated in that generality; the reverse inclusion uses only
finite dimensionality of `E` in addition. The index formula holds for any such coefficient whose
trajectory operator has closed range.

## Main declarations

* `TauCeti.WeakDerivStep.hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator`: a path
  orthogonal to the range of `D_A` has weak derivative `A v`.
* `TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_le_map_ker`: such a path is the value
  of an element of the kernel of `D_{-A}`.
* `TauCeti.WeakDerivStep.map_ker_le_orthogonal_range_trajectoryOperator` and
  `TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_eq_map_ker`: the values of the kernel
  of `D_{-A}` are exactly the orthogonal complement of the range of `D_A`.
* `TauCeti.WeakDerivStep.finiteDimensional_coker_trajectoryOperator`: the cokernel of `D_A` is
  finite dimensional.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`: `D_A` is a Fredholm operator.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_of_isClosed_range`: whenever the range of `D_A`
  is closed, its index is `dim ker D_A - dim ker D_{-A}`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator`: in particular, this holds under the
  asymptotic hypotheses above.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (the cokernel of a first-order operator through its formal adjoint).
* M. Schwarz, *Morse Homology*, Chapter 2 (the Fredholm property of linearized trajectory
  operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace Distributions

namespace TauCeti.WeakDerivStep

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pairing `v` with `D_A (φ • e)` for a test function `φ` and a vector `e` gives the pairing of
`e` with `∫ φ' v + ∫ φ A v`, when `A` is almost everywhere symmetric. Both directions of the
identification of the cokernel of `D_A` with the kernel of `D_{-A}` are read off from it. -/
private theorem inner_trajectoryOperator_smulRightW1pL
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric)
    (v : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (e : E)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ⟪trajectoryOperator (p := 2) AL (smulRightW1pL e (W1p.ofTestFunctionₗ volume ⊤ 2 φ)), v⟫_ℝ =
      ⟪e, (∫ s, lineDeriv ℝ (φ : ℝ → ℝ) s 1 • v s) + ∫ s, (φ : ℝ → ℝ) s • AL s (v s)⟫_ℝ := by
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Lp.locallyIntegrableOn v (by norm_num)) φ 1
  have hi2 := integrable_smul_of_locallyIntegrableOn (w := fun s ↦ AL s (v s))
    ((Lp.locallyIntegrableOn _ (by norm_num)).congr
      ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2) AL v)) φ
  have hψ : ContDiff ℝ 1 fun s ↦ (φ : ℝ → ℝ) s • e :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).smul contDiff_const
  have hDu := trajectoryOperator_apply_ae_eq_deriv_add AL _
    (prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (p := 2) e φ)
    ((hψ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
    fun s _ ↦ hψ.differentiable one_ne_zero s
  have hvol (g : ℝ → ℝ) : ∫ s, g s = ∫ s, g s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ) := by
    simp
  rw [inner_add_right, ← integral_inner hi1, ← integral_inner hi2,
    ← integral_add (hi1.const_inner e) (hi2.const_inner e), L2.inner_def, hvol]
  refine integral_congr_ae ?_
  filter_upwards [hDu, hsym] with s hs hsyms
  have hφd : DifferentiableAt ℝ (φ : ℝ → ℝ) s := φ.contDiff.differentiable (by simp) s
  rw [hs, deriv_smul_const hφd, lineDeriv_one]
  simp only [map_smul, inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    hsyms.apply_clm]

/-- An element `z` of `W^{1,2}(ℝ, E)` lies in the kernel of `D_{-A}` exactly when its value `v`
has weak derivative `A v`. -/
private theorem trajectoryOperator_neg_eq_zero_iff
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (z : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectoryOperator (-AL) z = 0 ↔ HasWeakLineDerivOn volume ⊤
      (prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z
        : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (fun s ↦ AL s
        (prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z s))
      1 := by
  rw [trajectoryOperator_eq_iff_hasWeakLineDerivOn]
  refine ⟨fun h ↦ h.congr_ae_deriv ?_, fun h ↦ h.congr_ae_deriv ?_⟩ <;>
  · filter_upwards [Lp.coeFn_zero E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      Lp.coeFn_neg AL] with s h0 hneg
    rw [h0, hneg]
    simp

/-- **A path orthogonal to the range solves the adjoint equation weakly.** If the coefficient of
the trajectory operator `D_A u = u' + A u` is almost everywhere symmetric, then every
`v ∈ L²(ℝ, E)` orthogonal to the range of `D_A` has weak derivative `A v`: it is a weak solution
of the formal adjoint equation `-v' + A v = 0`. -/
theorem hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric)
    {v : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hv : v ∈ (trajectoryOperator (p := 2) AL).rangeᗮ) :
    HasWeakLineDerivOn volume ⊤ v (fun s ↦ AL s (v s)) 1 := by
  refine hasWeakLineDerivOn_iff_testFunction.mpr ⟨inferInstance,
    Lp.locallyIntegrableOn v (by norm_num), (Lp.locallyIntegrableOn _ (by norm_num)).congr
      ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2) AL v), fun φ ↦ ?_⟩
  -- The pairing of `∫ φ' v + ∫ φ A v` with every vector vanishes, so this vector is zero.
  have hpair (e : E) := (inner_trajectoryOperator_smulRightW1pL hsym v e φ).symm.trans
    ((Submodule.mem_orthogonal _ _).mp hv _ (LinearMap.mem_range_self _ _))
  exact eq_neg_of_add_eq_zero_left (inner_self_eq_zero.mp (hpair _))

/-- **Paths orthogonal to the range lie in the kernel of the formal adjoint.** If the coefficient
of `D_A u = u' + A u` is almost everywhere symmetric, every `v ∈ L²(ℝ, E)` orthogonal to the
range of `D_A` is the value of an element of `W^{1,2}(ℝ, E)` in the kernel of `D_{-A}`; that is,
`v` solves `v' - A v = 0` in `W^{1,2}`. -/
theorem orthogonal_range_trajectoryOperator_le_map_ker
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric) :
    (trajectoryOperator (p := 2) AL).rangeᗮ ≤
      (trajectoryOperator (p := 2) (-AL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) := by
  intro v hv
  have h := hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator hsym hv
  obtain ⟨z, hzv, hz⟩ := exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn (F := E)
    (-AL) (f := 0) <| h.congr_ae_deriv <| by
      filter_upwards [Lp.coeFn_zero E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
        Lp.coeFn_neg AL] with s h0 hneg
      rw [h0, hneg]
      simp
  exact ⟨z, hz, by simpa using hzv⟩

/-- **The kernel of the formal adjoint is orthogonal to the range.** If the coefficient of
`D_A u = u' + A u` is almost everywhere symmetric and `E` is finite dimensional, the value of
every solution of `v' - A v = 0` in `W^{1,2}(ℝ, E)` is orthogonal to the range of `D_A`. -/
theorem map_ker_le_orthogonal_range_trajectoryOperator [FiniteDimensional ℝ E]
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric) :
    (trajectoryOperator (p := 2) (-AL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) ≤
      (trajectoryOperator (p := 2) AL).rangeᗮ := by
  rintro _ ⟨z, hz, rfl⟩
  set v := prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z
  -- The value `v` of `z` has weak derivative `A v`.
  have h : HasWeakLineDerivOn volume ⊤ v (fun s ↦ AL s (v s)) 1 :=
    (trajectoryOperator_neg_eq_zero_iff AL z).mp hz
  -- The paths `u` with `⟪v, D_A u⟫ = 0` form a closed subspace containing the test fields.
  let K := ((innerSL ℝ v).comp (trajectoryOperator (p := 2) AL)).ker
  have hK := ((innerSL ℝ v).comp (trajectoryOperator (p := 2) AL)).isClosed_ker
  have mem_K (u) : u ∈ K ↔ ⟪v, trajectoryOperator (p := 2) AL u⟫_ℝ = 0 := by simp [K]
  have htest (e : E) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
      smulRightW1pL e (W1p.ofTestFunctionₗ volume ⊤ 2 φ) ∈ K := by
    rw [mem_K, real_inner_comm, inner_trajectoryOperator_smulRightW1pL hsym,
      h.integral_lineDeriv_smul_eq_neg_integral_smul, neg_add_cancel, inner_zero_right]
  -- By density of test functions, `K` contains every coordinate field, hence every path.
  have hcoord (e : E) (w : W1p volume ⊤ 2) : smulRightW1pL e w ∈ K :=
    (W1p.denseRange_ofTestFunctionₗ_top (by norm_num)).induction_on w
      (hK.preimage (smulRightW1pL e).continuous) (htest e)
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ K := by
    rw [← sum_smulRightW1pL_toW1pL (Module.finBasis ℝ E) u]
    exact K.sum_mem fun i _ ↦ hcoord _ _
  simpa [v, prevL_apply] using (mem_K u).mp hu

/-- **The orthogonal complement of the range of `D_A` is the kernel of its formal adjoint.** If
the coefficient of
`D_A u = u' + A u` is almost everywhere symmetric and `E` is finite dimensional, the orthogonal
complement of the range of `D_A` in `L²(ℝ, E)` consists exactly of the values of the solutions of
`v' - A v = 0` in `W^{1,2}(ℝ, E)`, the kernel of `D_{-A}`. -/
theorem orthogonal_range_trajectoryOperator_eq_map_ker [FiniteDimensional ℝ E]
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric) :
    (trajectoryOperator (p := 2) AL).rangeᗮ =
      (trajectoryOperator (p := 2) (-AL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) :=
  (orthogonal_range_trajectoryOperator_le_map_ker hsym).antisymm
    (map_ker_le_orthogonal_range_trajectoryOperator hsym)

/-- **The index of a trajectory operator with closed range.** If the coefficient of
`D_A u = u' + A u` is almost everywhere symmetric, `E` is finite dimensional and the range of
`D_A` is closed, then the index of `D_A` is `dim ker D_A - dim ker D_{-A}`: its cokernel is the
kernel of the formal adjoint `-d/ds + A`, whose solutions are those of `v' - A v = 0`. -/
theorem index_trajectoryOperator_of_isClosed_range [FiniteDimensional ℝ E]
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric)
    (hclosed : IsClosed ((trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker : ℤ) -
        Module.finrank ℝ (trajectoryOperator (p := 2) (-AL)).ker := by
  have := hclosed.completeSpace_coe
  -- The value map `W^{1,2}(ℝ, E) → L²(ℝ, E)` is injective.
  have hinj : Function.Injective
      (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
    fun u w h ↦ ext (by simpa using h)
  -- The cokernel is the orthogonal complement of the range, which is the image of the kernel of
  -- `D_{-A}` under the injective value map.
  have hcoker : Module.finrank ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) =
        Module.finrank ℝ (trajectoryOperator (p := 2) (-AL)).ker :=
    (((trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.trans
      (LinearEquiv.ofEq _ _ (orthogonal_range_trajectoryOperator_eq_map_ker hsym))).trans
      (Submodule.equivMapOfInjective _ hinj _).symm).finrank_eq
  rw [ContinuousLinearMap.index_eq_finrank_sub, hcoker]

end Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- A symmetric family has almost everywhere symmetric `L∞` classes. -/
private theorem ae_isSymmetric (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric := by
  filter_upwards [hAL] with s hs
  rw [hs]
  exact hsym s

/-- The family `-A` satisfies the hypotheses of
`TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator` whenever `A` does, so the kernel
of `D_{-A}` is finite dimensional. -/
private theorem finiteDimensional_ker_trajectoryOperator_neg
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (trajectoryOperator (p := 2) (-AL)).ker := by
  obtain ⟨hB, hBsym, hBminus, hBplus, hdBbot, hdBtop⟩ :=
    neg_trajectory_hypotheses hA hsym hminus hplus hdbot hdtop
  exact finiteDimensional_ker_trajectoryOperator hB hBsym hα hBminus hBplus hbot.neg htop.neg
    hdBbot hdBtop (-AL)
    (by filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs; simp only [hs, Pi.neg_apply, hAs])

/-- Under the hypotheses of `TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator`, the range
of `D_A` is complete, so its orthogonal complement in `L²(ℝ, E)` is a complement of it. -/
private theorem completeSpace_range_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    CompleteSpace (trajectoryOperator (p := 2) AL).range :=
  (isClosed_range_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL
    hAL).completeSpace_coe

/-- **The cokernel of the trajectory operator is finite dimensional.** For a `C¹` family of
symmetric operators with invertible limits at both ends and derivative tending to zero, the
quotient of `L²(ℝ, E)` by the range of `u ↦ u' + A u` is finite dimensional. -/
theorem finiteDimensional_coker_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) := by
  have := completeSpace_range_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL
    hAL
  -- The orthogonal complement of the range lies in the image of the kernel of `D_{-A}`.
  have := finiteDimensional_ker_trajectoryOperator_neg hA hsym hα hminus hplus hbot htop hdbot
    hdtop AL hAL
  have : FiniteDimensional ℝ (trajectoryOperator (p := 2) AL).rangeᗮ :=
    Submodule.finiteDimensional_of_le
      (orthogonal_range_trajectoryOperator_le_map_ker (ae_isSymmetric hsym hAL))
  exact (trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.symm
    |>.finiteDimensional

/-- **The trajectory operator is Fredholm.** For a `C¹` family `A` of symmetric operators on a
finite-dimensional real inner product space, with invertible limits at both ends and derivative
tending to zero, `u ↦ u' + A u` is a Fredholm operator from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`. -/
theorem isFredholm_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  .of_finite_ker_coker _
    (finiteDimensional_ker_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL hAL)
    (finiteDimensional_coker_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL
      hAL)

/-- **The index of the trajectory operator.** Under the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`, the index of `D_A u = u' + A u` is
`dim ker D_A - dim ker D_{-A}`: its cokernel is the kernel of the formal adjoint `-d/ds + A`,
whose solutions are those of `v' - A v = 0`. This specializes
`TauCeti.WeakDerivStep.index_trajectoryOperator_of_isClosed_range`. -/
theorem index_trajectoryOperator
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker : ℤ) -
        Module.finrank ℝ (trajectoryOperator (p := 2) (-AL)).ker :=
  index_trajectoryOperator_of_isClosed_range (ae_isSymmetric hsym hAL)
    (isClosed_range_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL hAL)

end TauCeti.WeakDerivStep
