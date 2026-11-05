/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LyapunovForm
public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
public import TauCeti.Analysis.ODE.EnergyEstimate.Cokernel
public import TauCeti.Analysis.ODE.EnergyEstimate.Global

/-!
# The trajectory operator with hyperbolic limits

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner product
space `E`, with limits `A±` at `±∞` that have Lyapunov forms
(`ContinuousLinearMap.HasLyapunovForm`): there are symmetric `S±` and `c > 0` with
`c ‖v‖² ≤ ⟪S± (A± v), v⟫`. By the inertia theorem this says exactly that `A±` are hyperbolic, with
no eigenvalue on the imaginary axis; only the easy half of that equivalence is formalized, in
`TauCeti.Analysis.InnerProductSpace.LyapunovForm`. This file proves
that the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`) is a Fredholm operator, with
index `dim ker D_A - dim ker D_{-A†}`. Neither symmetry of `A` nor any derivative of `A` is
assumed. A symmetric operator bounded below has the Lyapunov form `S = A`
(`ContinuousLinearMap.hasLyapunovForm_of_isSymmetric`), and a limit of symmetric operators is
symmetric (`ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric`), so this applies in
particular to every continuous family of symmetric operators with invertible limits.

The estimate behind the theorem replaces the energy identity of the symmetric case by the
monotonicity of a quadratic form. For a `C¹` family `S(s)` of symmetric operators and a compactly
supported `C¹` path `u`, integrating the derivative of `⟪S u, u⟫` gives

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`

(`TauCeti.integral_inner_apply_deriv_add_eq`). Interpolating between `S-` and `S+` across a
bounded interval `[-R, R]`, the right side controls `∫ ‖u‖²` up to an error supported in
`[-R, R]`, while the left side is at most `‖S‖ ‖u' + A u‖ ‖u‖`. This gives the estimate

`‖u‖²_{W^{1,2}} ≤ C ‖D_A u‖²_{L²} + C ‖u‖²_{L²(-R, R)}`

first on test paths (in `TauCeti.Analysis.ODE.EnergyEstimate.Global`) and then, by density, on
`W^{1,2}(ℝ, E)`. Restriction to a bounded interval is compact, so Peetre's lemma gives a
finite-dimensional kernel and a closed range. The cokernel is the
orthogonal complement of the range, which lies in the kernel of the formal adjoint
`D_{-A†} = d/ds - A†` (`TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_le_map_ker`). The
family `-A†` has limits `-A±†`, which again have Lyapunov forms
(`ContinuousLinearMap.HasLyapunovForm.neg_adjoint`), so that kernel is finite dimensional too.

## Main declarations

* `TauCeti.WeakDerivStep.exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm`:
  the estimate on `W^{1,2}(ℝ, E)`.
* `TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm` and
  `TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator_of_hasLyapunovForm`: the kernel of
  `D_A` is finite dimensional and its range is closed.
* `TauCeti.WeakDerivStep.finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm`: the
  cokernel of `D_A` is finite dimensional.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`: `D_A` is Fredholm.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_of_hasLyapunovForm`: its index is
  `dim ker D_A - dim ker D_{-A†}`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the operator `d/ds + A(s)` with hyperbolic limits).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the Fredholm property of linearized
  trajectory operators).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1
  (estimates with a compact error and the Fredholm criterion).
-/

public section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace

/-! ### The trajectory operator on Sobolev paths -/

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- **The trajectory estimate for hyperbolic limits on Sobolev paths.** Let `A` be a continuous
family of operators whose limits at `±∞` have Lyapunov forms. Then the trajectory operator
satisfies `‖u‖² ≤ C ‖D_A u‖² + C ‖u‖²_{L²(-R, R)}` on `W^{1,2}(ℝ, E)`. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ R > 0, ∃ C ≥ 0, ∀ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ‖u‖ ^ 2 ≤ C * ‖trajectoryOperator AL u‖ ^ 2 +
        C * ‖restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u‖ ^ 2 := by
  obtain ⟨R, hR, C, hC, hest⟩ :=
    exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm hA
      hminus hplus hbot htop
  refine ⟨R + 1, by linarith, C, hC, fun u ↦ ?_⟩
  have := mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff AL hAL (a := 1)
    (b := 1) (c := C) hC (lt_add_one R) (fun φ hφ hφc ↦ by simpa using hest φ hφ hφc) u
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
  linarith

/-- The trajectory estimate in the form of Peetre's lemma: `‖u‖ ≤ K ‖D_A u‖ + ‖K • ρ u‖`, where `ρ`
is the restriction to a bounded interval. -/
private theorem exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ R > 0, ∃ K ≥ 0, ∀ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ‖u‖ ≤ K * ‖trajectoryOperator AL u‖ +
      ‖(K • restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top) u‖ := by
  obtain ⟨R, hR, C, hC, hest⟩ :=
    exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm hA hminus hplus hbot
      htop AL hAL
  refine ⟨R, hR, √C, Real.sqrt_nonneg _, fun u ↦ ?_⟩
  have key := hest u
  have ha := norm_nonneg (trajectoryOperator AL u)
  have hb := norm_nonneg (restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u)
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← mul_add]
  generalize ‖trajectoryOperator AL u‖ = a at key ha ⊢
  generalize ‖restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u‖ = b at key hb ⊢
  refine (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [mul_nonneg hC (mul_nonneg ha hb)]

/-- **The kernel of the trajectory operator is finite dimensional for hyperbolic limits.** For a
continuous family of operators whose limits at `±∞` have Lyapunov forms, the solutions in
`W^{1,2}(ℝ, E)` of `u' + A u = 0` form a finite-dimensional space. -/
theorem finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (trajectoryOperator (p := 2) AL).ker := by
  obtain ⟨R, -, K, -, hest⟩ := exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    hA hminus hplus hbot htop AL hAL
  exact (trajectoryOperator (p := 2) AL).finiteDimensional_ker_of_compact_estimate
    (isCompactOperator_smul_restrictBaseL K R) hest

/-- **The range of the trajectory operator is closed for hyperbolic limits.** For a continuous
family of operators whose limits at `±∞` have Lyapunov forms, the image of `u ↦ u' + A u` from
`W^{1,2}(ℝ, E)` is a closed subspace of `L²(ℝ, E)`. -/
theorem isClosed_range_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    IsClosed ((trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
  obtain ⟨R, -, K, -, hest⟩ := exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    hA hminus hplus hbot htop AL hAL
  exact (trajectoryOperator (p := 2) AL).isClosed_range_of_compact_estimate
    (isCompactOperator_smul_restrictBaseL K R) hest

/-- **The cokernel of the trajectory operator is finite dimensional for hyperbolic limits.** For a
continuous family of operators whose limits at `±∞` have Lyapunov forms, the quotient of
`L²(ℝ, E)` by the range of `u ↦ u' + A u` is finite dimensional. -/
theorem finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) := by
  have := (isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL
    hAL).completeSpace_coe
  obtain ⟨BL, hBL⟩ := exists_ae_eq_adjoint AL hAL
  -- The family `-A†` of the formal adjoint has limits `-A±†`, which have Lyapunov forms.
  have hadj := (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E)).continuous
  have hnegBL : ⇑(-BL) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -ContinuousLinearMap.adjoint (A s) := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with s hs hBs
    rw [hs, Pi.neg_apply, hBs]
  have := finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm (hadj.comp hA).neg
    hminus.neg_adjoint hplus.neg_adjoint ((hadj.tendsto Aminus).comp hbot).neg
    ((hadj.tendsto Aplus).comp htop).neg (-BL) hnegBL
  -- The orthogonal complement of the range lies in the image of the kernel of `D_{-A†}`.
  have : FiniteDimensional ℝ (trajectoryOperator (p := 2) AL).rangeᗮ :=
    Submodule.finiteDimensional_of_le
      (orthogonal_range_trajectoryOperator_le_map_ker (ae_eq_adjoint_of_ae_eq hAL hBL))
  exact (trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.symm
    |>.finiteDimensional

/-- **The trajectory operator with hyperbolic limits is Fredholm.** For a continuous family `A`
of operators on a finite-dimensional real inner product space whose limits at `±∞` have Lyapunov
forms, `u ↦ u' + A u` is a Fredholm operator from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`. Neither symmetry
nor differentiability of `A` is assumed. -/
theorem isFredholm_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  .of_finite_ker_coker _
    (finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL hAL)
    (finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL
      hAL)

/-- **The index of the trajectory operator with hyperbolic limits.** Under the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, the index of
`D_A u = u' + A u` is `dim ker D_A - dim ker D_{-A†}`, where `BL` is an `L∞` class of the pointwise
adjoint `A†`: the cokernel of `D_A` is the kernel of the formal adjoint `-d/ds + A†`. Such a class
exists by `TauCeti.WeakDerivStep.exists_ae_eq_adjoint`; for a symmetric family, `AL` itself is
one. -/
theorem index_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ContinuousLinearMap.adjoint (A s)) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker : ℤ) -
        Module.finrank ℝ (trajectoryOperator (p := 2) (-BL)).ker :=
  index_trajectoryOperator_of_isClosed_range (ae_eq_adjoint_of_ae_eq hAL hBL)
    (isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL hAL)

end TauCeti.WeakDerivStep
