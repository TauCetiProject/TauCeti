/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.GelfandTriple
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.Holder

/-!
# The trajectory operator of a symmetric invertible operator with a domain

Let `ι : W →L[ℝ] H` be a continuous linear map from a normed space `W` into a real Banach space
`H`, and `A : W →L[ℝ] H`. Read `A` as an operator on `H` with domain `W`, such as the asymptotic
operator `A ζ = J₀ (ζ' - S ζ)` of a Hamiltonian orbit, which maps loops in `W = H¹(S¹)` to loops
in `H = L²(S¹)`. Its trajectory operator

`D_A ξ = (ι ξ)' + A ξ`

(`TauCeti.domainTrajectoryOperator`) acts on the paths `ξ ∈ L²(ℝ, W)` whose image `ι ξ` has a
weak derivative in `L²(ℝ, H)` (`TauCeti.TrajectoryDomain`), with the graph norm
`(‖ξ‖² + ‖(ι ξ)'‖²)^(1/2)`, and takes values in `L²(ℝ, H)`. For the asymptotic operator this is
the linearized Floer operator `∂s + J₀ (∂t - S)` at the stationary cylinder over the orbit, acting
on `L²(ℝ, H¹(S¹)) ∩ W^{1,2}(ℝ, L²(S¹))`, the anisotropic description of the Sobolev space
`W^{1,2}` of the cylinder. Unlike `TauCeti.WeakDerivStep.trajectoryOperator`, the coefficient need
not be a bounded operator on `H`.

For any Banach space `H`, solving `D_A ξ = f` is the weak equation `(ι ξ)' = f - A ξ`
(`TauCeti.domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn`), `‖D_A‖ ≤ 1 + ‖A‖`, and `D_A`
depends `1`-Lipschitz continuously on `A` (`TauCeti.lipschitzWith_domainTrajectoryOperator`), so
for complete `W` its invertibility is an open condition on `A`
(`TauCeti.eventually_isInvertible_domainTrajectoryOperator`).

Now let `W` be complete, let `H` be a real Hilbert space, and suppose `A` is **symmetric**
relative to `ι`, `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x, y ∈ W`.

* **The energy identity.** For every `ξ` in the domain,

  `‖D_A ξ‖² = ‖(ι ξ)'‖² + ‖A ξ‖²`

  (`TauCeti.norm_domainTrajectoryOperator_sq`): the cross term `2 ∫ ⟪(ι ξ)', A ξ⟫` vanishes
  because it is the integral of the weak derivative of the integrable function
  `s ↦ ⟪ι ξ(s), A ξ(s)⟫` (`TauCeti.integral_inner_weakFDeriv_apply_prev_eq_zero`). This uses the
  weak product rule `TauCeti.HasWeakLineDerivOn.bilin_self` for the symmetric form
  `(x, y) ↦ ⟪ι x, A y⟫`; no derivative of `A ξ` is needed.
* **Injectivity and the coercive estimate.** If `ι` and `A` have no common kernel, then `D_A` is
  injective (`TauCeti.injective_domainTrajectoryOperator`). If `‖w‖ ≤ C ‖A w‖` on `W`, then
  `‖ξ‖ ≤ max C 1 ‖D_A ξ‖` (`TauCeti.norm_le_mul_norm_domainTrajectoryOperator`), so `D_A` has
  closed range.
* **Invertibility.** If moreover `A` is invertible, then `D_A` is invertible
  (`TauCeti.isInvertible_domainTrajectoryOperator`), with `‖D_A⁻¹‖ ≤ max ‖A⁻¹‖ 1`. An element `g`
  orthogonal to the range is `A ζ` for `ζ = A⁻¹ g ∈ L²(ℝ, W)`. Testing the orthogonality against
  the paths `s ↦ φ(s) w`, for test functions `φ` and `w ∈ W`, and using the symmetry and
  surjectivity of `A`, shows `(ι ζ)' = A ζ`, that is, `D_{-A} ζ = 0`. The energy identity for the
  symmetric operator `-A` then gives `A ζ = 0`, so `g = 0`.
* **Small weights.** By openness, the operators `D_{A - δ C}` are invertible for small `δ`, for
  every `C : W →L[ℝ] H` (`TauCeti.eventually_isInvertible_domainTrajectoryOperator_sub_smul`).
  For `C = ι` these are the operators `d/ds + A - δ` into which the exponential weight `e^{δ s}`
  turns `D_A`.

No spectral decomposition of `A`, no density of `ι`, no compactness and no injectivity of `ι` is
used. Applied to the asymptotic operator of a nondegenerate orbit, which is invertible from
`H¹(S¹)` to `L²(S¹)` and symmetric for a constant compatible complex structure `J₀`, this is the
invertibility of the linearized Floer operator at the stationary cylinder, and of its weighted
versions on the cylindrical ends.

## Main declarations

* `TauCeti.TrajectoryDomain ι`: the domain `{ξ ∈ L²(ℝ, W) | (ι ξ)' ∈ L²(ℝ, H)}`.
* `TauCeti.domainTrajectoryOperator ι A`: the operator `ξ ↦ (ι ξ)' + A ξ`.
* `TauCeti.domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn`: the weak equation.
* `TauCeti.norm_domainTrajectoryOperator_le`, `TauCeti.norm_domainTrajectoryOperator_sub_le`:
  the operator-norm bound and the dependence on the coefficient.
* `TauCeti.norm_domainTrajectoryOperator_sq`: the energy identity.
* `TauCeti.norm_le_mul_norm_domainTrajectoryOperator`: the coercive estimate.
* `TauCeti.isInvertible_domainTrajectoryOperator`,
  `TauCeti.norm_inverse_domainTrajectoryOperator_le`: invertibility and the inverse bound.
* `TauCeti.eventually_isInvertible_domainTrajectoryOperator_sub_smul`: invertibility for small
  weights.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the operator `d/ds + A` with an invertible self-adjoint
  asymptotic operator.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33, on the operators `d/ds + A(s)` with self-adjoint `A(s)`.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped InnerProductSpace ENNReal Distributions Topology

namespace TauCeti

open WeakDerivStep

section Banach

variable {W H : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The domain of the trajectory operator `d/ds + A` of an operator `A` on `H` with domain `W`,
embedded by `ι`: the paths `ξ ∈ L²(ℝ, W)` whose image `ι ξ` has a weak derivative in
`L²(ℝ, H)`, with the graph norm `(‖ξ‖² + ‖(ι ξ)'‖²)^(1/2)`. For the inclusion of `H¹(S¹)` in
`L²(S¹)` it is `L²(ℝ, H¹(S¹)) ∩ W^{1,2}(ℝ, L²(S¹))`, the anisotropic description of the Sobolev
space `W^{1,2}` of the cylinder `ℝ × S¹`. -/
abbrev TrajectoryDomain (ι : W →L[ℝ] H) : Type _ :=
  WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))

variable {ι A : W →L[ℝ] H}

/-- The weak derivative of `ι ξ` on the line, in the direction `1`. -/
theorem TrajectoryDomain.hasWeakLineDerivOn_prev (ξ : TrajectoryDomain ι) :
    HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (prev _ ξ s)) (fun s ↦ weakFDeriv _ ξ s 1) 1 :=
  ((hasWeakFDerivOn_base_prev _ ξ).hasWeakLineDerivOn 1).congr_ae (ι.coeFn_compLp _)

/-- The trajectory operator `ξ ↦ (ι ξ)' + A ξ` of `A : W →L[ℝ] H`, read as an operator on `H` with
domain `W` embedded by `ι`, from `TauCeti.TrajectoryDomain ι` to `L²(ℝ, H)`. -/
def domainTrajectoryOperator (ι A : W →L[ℝ] H) :
    TrajectoryDomain ι →L[ℝ] Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).comp (weakFDerivL _) +
    (A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).comp (prevL _)

/-- The trajectory operator is the weak derivative in the direction `1` plus the coefficient. -/
theorem domainTrajectoryOperator_apply (ξ : TrajectoryDomain ι) :
    domainTrajectoryOperator ι A ξ =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ ξ) + A.compLp (prev _ ξ) := by
  simp only [domainTrajectoryOperator, add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, weakFDerivL_apply, prevL_apply]
  -- Mathlib's `compLpL` has no application equality lemma, only an a.e. formula.
  rfl

/-- On representatives, the trajectory operator is `s ↦ (ι ξ)'(s) + A (ξ s)` almost everywhere. -/
theorem domainTrajectoryOperator_apply_ae (ξ : TrajectoryDomain ι) :
    domainTrajectoryOperator ι A ξ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ weakFDeriv _ ξ s 1 + A (prev _ ξ s) := by
  rw [domainTrajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ ξ))
      (A.compLp (prev _ ξ)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp (weakFDeriv _ ξ),
    A.coeFn_compLp (prev _ ξ)] with s hs hd hA
  rw [hs, Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply]

/-- Solving `(ι ξ)' + A ξ = f` is the weak ordinary differential equation `(ι ξ)' = f - A ξ`. -/
theorem domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ξ : TrajectoryDomain ι)
    (f : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    domainTrajectoryOperator ι A ξ = f ↔
      HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (prev _ ξ s)) (fun s ↦ f s - A (prev _ ξ s)) 1 := by
  constructor
  · intro h
    refine ξ.hasWeakLineDerivOn_prev.congr_ae_deriv ?_
    filter_upwards [h ▸ domainTrajectoryOperator_apply_ae (A := A) ξ] with s hs
    exact eq_sub_of_add_eq hs.symm
  · intro h
    refine Lp.ext ?_
    filter_upwards [domainTrajectoryOperator_apply_ae (A := A) ξ,
      ξ.hasWeakLineDerivOn_prev.ae_eq h] with s hs hd
    rw [hs, hd, sub_add_cancel]

/-- The trajectory operator of the element `mkLine _ ζ g h` with value `ζ` and weak derivative
`(ι ζ)' = g` is `g + A ζ`. -/
theorem domainTrajectoryOperator_mkLine (ζ : Lp W 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (h : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ζ) g
      1) :
    domainTrajectoryOperator ι A (mkLine _ ζ g h) = g + A.compLp ζ := by
  rw [domainTrajectoryOperator_apply, apply_one_compLp_weakFDeriv_mkLine, prev_mkLine]

/-- The operator norm of the trajectory operator is at most `1 + ‖A‖`. -/
theorem norm_domainTrajectoryOperator_le : ‖domainTrajectoryOperator ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ ↦ ?_
  rw [domainTrajectoryOperator_apply, add_mul, one_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Lp.norm_apply_one_compLp]
    exact norm_weakFDeriv_le _ ξ
  · exact (A.norm_compLp_le _).trans (by gcongr; exact norm_prev_le _ ξ)

/-- Changing the coefficient changes the trajectory operator by the multiplication by the
difference of the coefficients. -/
theorem domainTrajectoryOperator_sub (ι A B : W →L[ℝ] H) :
    domainTrajectoryOperator ι A - domainTrajectoryOperator ι B =
      ((A - B).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).comp (prevL _) := by
  ext1 ξ
  rw [sub_apply, domainTrajectoryOperator_apply,
    domainTrajectoryOperator_apply, add_sub_add_left_eq_sub, ContinuousLinearMap.coe_comp,
    Function.comp_apply, prevL_apply]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (A.compLp (prev _ ξ)) (B.compLp (prev _ ξ)),
    A.coeFn_compLp (prev _ ξ), B.coeFn_compLp (prev _ ξ),
    (A - B).coeFn_compLpL (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (p := 2) (prev _ ξ)]
    with s h₁ h₂ h₃ h₄
  rw [h₁, Pi.sub_apply, h₂, h₃, h₄, sub_apply]

/-- Changing the coefficient changes the trajectory operator by at most the same amount in
operator norm. -/
theorem norm_domainTrajectoryOperator_sub_le (ι A B : W →L[ℝ] H) :
    ‖domainTrajectoryOperator ι A - domainTrajectoryOperator ι B‖ ≤ ‖A - B‖ := by
  rw [domainTrajectoryOperator_sub]
  have hprev : ‖prevL (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ ↦ by
      simpa using norm_prev_le _ ξ
  calc _ ≤ ‖(A - B).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))‖ *
        ‖prevL (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A - B‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_compLpL_le _
    _ = ‖A - B‖ := mul_one _

/-- The trajectory operator depends `1`-Lipschitz continuously on its coefficient, for the
operator norm. -/
theorem lipschitzWith_domainTrajectoryOperator (ι : W →L[ℝ] H) :
    LipschitzWith 1 (domainTrajectoryOperator ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_domainTrajectoryOperator_sub_le ι A B

/-- **Invertibility is open in the coefficient.** If the trajectory operator of `A` is
invertible, so is that of every coefficient `B` close to `A` in operator norm. -/
theorem eventually_isInvertible_domainTrajectoryOperator [CompleteSpace W]
    (hd : (domainTrajectoryOperator ι A).IsInvertible) :
    ∀ᶠ B in 𝓝 A, (domainTrajectoryOperator ι B).IsInvertible :=
  ((lipschitzWith_domainTrajectoryOperator ι).continuous.tendsto A).eventually hd.eventually_nhds

end Banach

section Hilbert

variable {W H : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A : W →L[ℝ] H}

/-- The derivative field `s ↦ (ι ξ)'(s)` is square integrable. -/
private theorem memLp_weakFDeriv_apply_one (ξ : TrajectoryDomain ι) :
    MemLp (fun s ↦ weakFDeriv _ ξ s 1) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (Lp.memLp (weakFDeriv _ ξ)).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ H (1 : ℝ))

/-- Integrals over the restriction of `volume` to the whole line are integrals over `ℝ`. -/
private theorem integral_restrict_top (f : ℝ → ℝ) :
    ∫ s, f s ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) = ∫ s, f s := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- The restriction of `volume` to the whole line is `volume`. -/
private theorem volume_le_restrict_top :
    (volume : Measure ℝ) ≤ volume.restrict ((⊤ : Opens ℝ) : Set ℝ) := by
  rw [Opens.coe_top, Measure.restrict_univ]

variable [CompleteSpace W]

/-- **The cross term vanishes.** For `A` symmetric relative to `ι`, the `L²` pairing of the weak
derivative `(ι ξ)'` with `A ξ` is zero, for every `ξ` in the domain. -/
theorem integral_inner_weakFDeriv_apply_prev_eq_zero
    (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (ξ : TrajectoryDomain ι) :
    ∫ s, ⟪weakFDeriv _ ξ s 1, A (prev _ ξ s)⟫_ℝ = 0 := by
  -- The symmetric form `B x y = ⟪ι x, A y⟫`.
  set B : W →L[ℝ] W →L[ℝ] ℝ := A.gelfandDual.comp ι
  have hB : B.flip = B := by
    ext x y
    simp only [ContinuousLinearMap.flip_apply, B, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.gelfandDual_apply]
    rw [real_inner_comm, hA]
  have hval := Lp.memLp (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) ξ)
  have hder := (memLp_weakFDeriv_apply_one ξ).continuousLinearMap_comp A.gelfandDual
  have hweak := HasWeakLineDerivOn.bilin_self hB
    (ξ.hasWeakLineDerivOn_prev.clm_comp A.gelfandDual) hval hder
  -- The quadratic form and its weak derivative are integrable, so the derivative integrates to `0`.
  have hint {f : ℝ → ℝ} (hf : MemLp f 1 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
      Integrable f := by
    simpa [Measure.restrict_univ] using memLp_one_iff_integrable.1 hf
  have h0 := hweak.integral_eq_zero (hint (B.memLp_of_bilin 1 hval hval))
    ((hint ((ContinuousLinearMap.id ℝ (StrongDual ℝ W)).memLp_of_bilin 1 hder hval)).const_mul 2)
  simp only [ContinuousLinearMap.gelfandDual_apply, integral_const_mul, mul_eq_zero,
    two_ne_zero, false_or] at h0
  exact h0

/-- **The energy identity.** For `A` symmetric relative to `ι`,
`‖(ι ξ)' + A ξ‖² = ‖(ι ξ)'‖² + ‖A ξ‖²` in `L²(ℝ, H)`. -/
theorem norm_domainTrajectoryOperator_sq (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (ξ : TrajectoryDomain ι) :
    ‖domainTrajectoryOperator ι A ξ‖ ^ 2 = ‖weakFDeriv _ ξ‖ ^ 2 + ‖A.compLp (prev _ ξ)‖ ^ 2 := by
  have hinner : ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ ξ),
      A.compLp (prev _ ξ)⟫_ℝ = 0 := by
    rw [L2.inner_def, ← integral_inner_weakFDeriv_apply_prev_eq_zero hA ξ, ← integral_restrict_top]
    refine integral_congr_ae ?_
    filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp (weakFDeriv _ ξ),
      A.coeFn_compLp (prev _ ξ)] with s hd hA
    rw [hd, hA, ContinuousLinearMap.apply_apply]
  rw [domainTrajectoryOperator_apply, norm_add_sq_real, hinner, Lp.norm_apply_one_compLp]
  ring

/-- **The coercive estimate.** If `A` is symmetric relative to `ι` and `‖w‖ ≤ C ‖A w‖` on `W`,
then every `ξ` in the domain satisfies `‖ξ‖ ≤ max C 1 * ‖(ι ξ)' + A ξ‖`. -/
theorem norm_le_mul_norm_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    {C : ℝ} (hC : ∀ w, ‖w‖ ≤ C * ‖A w‖) (ξ : TrajectoryDomain ι) :
    ‖ξ‖ ≤ max C 1 * ‖domainTrajectoryOperator ι A ξ‖ := by
  have hprev : ‖prev _ ξ‖ ≤ max C 1 * ‖A.compLp (prev _ ξ)‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [A.coeFn_compLp (prev _ ξ)] with s hs
    rw [hs]
    exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))
  have hC1 : 1 ≤ max C 1 := le_max_right C 1
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, norm_domainTrajectoryOperator_sq hA, norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
  have h1 : ‖prev _ ξ‖ ^ 2 ≤ max C 1 ^ 2 * ‖A.compLp (prev _ ξ)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hprev 2
  have h2 : ‖weakFDeriv _ ξ‖ ^ 2 ≤ max C 1 ^ 2 * ‖weakFDeriv _ ξ‖ ^ 2 :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ hC1)
  linarith

/-- A trajectory operator with a symmetric coefficient is injective as soon as `ι` and `A` have
no common kernel: a path in the kernel has `(ι ξ)' = 0` and `A ξ = 0` by the energy identity,
so `ι ξ` is a constant in `L²(ℝ, H)`, hence `0`. -/
theorem injective_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hker : ∀ w, ι w = 0 → A w = 0 → w = 0) :
    Function.Injective (domainTrajectoryOperator ι A) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
  have hE := norm_domainTrajectoryOperator_sq hA ξ
  rw [hξ, norm_zero] at hE
  have hd : weakFDeriv _ ξ = 0 := norm_eq_zero.1 <| (pow_eq_zero_iff two_ne_zero).1 <| by
    nlinarith [sq_nonneg ‖weakFDeriv _ ξ‖, sq_nonneg ‖A.compLp (prev _ ξ)‖]
  have hAξ : A.compLp (prev _ ξ) = 0 := norm_eq_zero.1 <| (pow_eq_zero_iff two_ne_zero).1 <| by
    nlinarith [sq_nonneg ‖weakFDeriv _ ξ‖, sq_nonneg ‖A.compLp (prev _ ξ)‖]
  -- `ι ξ` has weak derivative `0`, so it is almost everywhere a constant `c`.
  have hw : HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (prev _ ξ s)) 0 1 := by
    refine ξ.hasWeakLineDerivOn_prev.congr_ae_deriv ?_
    filter_upwards [hd ▸ Lp.coeFn_zero (ℝ →L[ℝ] H) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))]
      with s hs
    rw [hs]
    rfl
  obtain ⟨c, hc⟩ := hw.exists_ae_eq_add_intervalIntegral_top 0
  simp only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero] at hc
  -- A constant in `L²(ℝ, H)` vanishes.
  have hmem : MemLp (fun _ : ℝ ↦ c) 2 volume :=
    (((Lp.memLp (prev _ ξ)).continuousLinearMap_comp ι).mono_measure volume_le_restrict_top).ae_eq
      hc
  have hc0 : c = 0 := ((memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top).1 hmem).resolve_right
    (by simp)
  have hprev : prev _ ξ = 0 := by
    refine Lp.ext ?_
    filter_upwards [ae_restrict_of_ae hc, A.coeFn_compLp (prev _ ξ),
      hAξ ▸ Lp.coeFn_zero H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      Lp.coeFn_zero W 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))] with s h₁ h₂ h₃ h₄
    rw [h₄]
    exact hker _ (h₁.trans hc0) (h₂.symm.trans h₃)
  exact ext_prev_weakFDeriv (by rw [hprev, prev_zero]) (by rw [hd, ← weakFDerivL_apply, map_zero])

/-- A trajectory operator with a symmetric coefficient bounded below has closed range. -/
theorem isClosed_range_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    {C : ℝ} (hC : ∀ w, ‖w‖ ≤ C * ‖A w‖) :
    IsClosed (Set.range (domainTrajectoryOperator ι A)) := by
  have hanti : AntilipschitzWith ⟨max C 1, le_trans zero_le_one (le_max_right C 1)⟩
      (domainTrajectoryOperator ι A) :=
    (domainTrajectoryOperator ι A).antilipschitz_of_bound
      (norm_le_mul_norm_domainTrajectoryOperator hA hC)
  exact hanti.isClosed_range (domainTrajectoryOperator ι A).uniformContinuous

/-! ### Surjectivity -/

/-- A test function `φ` times a vector `v`, as an `L²` field. -/
private def testField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (v : E) : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).compLp (testFunctionLp (mu := volume) 2 φ)

private theorem testField_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (v : E) :
    testField φ v =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ φ s • v := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLp
    (testFunctionLp (mu := volume) 2 φ), testFunctionLp_apply_ae (mu := volume) 2 φ] with s h₁ h₂
  rw [testField, h₁, ContinuousLinearMap.toSpanSingleton_apply, h₂]

omit [CompleteSpace W] in
/-- The weak derivative of `s ↦ ι (φ s • w)` is `s ↦ φ'(s) • ι w`. -/
private theorem hasWeakLineDerivOn_testField (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (w : W) :
    HasWeakLineDerivOn volume ⊤
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (testField φ w))
      (testField (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w)) 1 := by
  have hφ : HasWeakLineDerivOn volume ⊤ (φ : ℝ → ℝ) (fun s ↦ lineDeriv ℝ (φ : ℝ → ℝ) s 1) 1 := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      (φ.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ fun s _ ↦
        ((φ.contDiff.differentiable (by simp)) s).lineDifferentiableAt.hasLineDerivAt
    rw [← TestFunction.coe_lineDerivCLM]
    exact (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ).continuous.locallyIntegrable.locallyIntegrableOn _
  refine ((hφ.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (ι w))).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [testField_ae φ w, ι.coeFn_compLpL (testField φ w)] with s hs hι
    rw [hι, hs]
    simp
  · filter_upwards [testField_ae (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w)] with s hs
    simp [hs]

omit [CompleteSpace W] in
/-- An `L²` field orthogonal to the range of the trajectory operator is orthogonal to the image
`s ↦ φ'(s) • ι w + φ s • A w` of every path `s ↦ φ s • w`. -/
private theorem integral_inner_eq_zero_of_mem_orthogonal
    {g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hg : g ∈ (LinearMap.range (domainTrajectoryOperator ι A).toLinearMap)ᗮ)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (w : W) :
    ∫ s, (lineDeriv ℝ (φ : ℝ → ℝ) s 1 * ⟪ι w, g s⟫_ℝ + φ s * ⟪A w, g s⟫_ℝ) = 0 := by
  have h := (Submodule.mem_orthogonal _ g).1 hg _
    (LinearMap.mem_range_self (domainTrajectoryOperator ι A).toLinearMap
      (mkLine _ _ _ (hasWeakLineDerivOn_testField (ι := ι) φ w)))
  rw [ContinuousLinearMap.coe_coe, domainTrajectoryOperator_mkLine, L2.inner_def] at h
  rw [← integral_restrict_top, ← h]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (testField (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w))
      (A.compLp (testField φ w)),
    testField_ae (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w), A.coeFn_compLp (testField φ w),
    testField_ae φ w] with s h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, TestFunction.coe_lineDerivCLM]
  simp [inner_add_left, real_inner_smul_left]

omit [CompleteSpace W] [CompleteSpace H] in
/-- For invertible `A`, `‖w‖ ≤ ‖A⁻¹‖ ‖A w‖`. -/
private theorem norm_le_norm_inverse_mul (hinv : A.IsInvertible) (w : W) :
    ‖w‖ ≤ ‖A.inverse‖ * ‖A w‖ := by
  simpa [hinv.inverse_apply_self] using A.inverse.le_opNorm (A w)

/-- For a symmetric invertible `A`, an `L²` field orthogonal to the range of the trajectory
operator vanishes. -/
private theorem eq_zero_of_mem_orthogonal (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) {g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hg : g ∈ (LinearMap.range (domainTrajectoryOperator ι A).toLinearMap)ᗮ) : g = 0 := by
  -- `g = A ζ` for `ζ = A⁻¹ g`.
  set ζ := A.inverse.compLp g
  have hAζ : A.compLp ζ = g := by
    refine Lp.ext ?_
    filter_upwards [A.coeFn_compLp ζ, A.inverse.coeFn_compLp g] with s h₁ h₂
    rw [h₁, h₂, hinv.self_apply_inverse]
  have hζ : MemLp (fun s ↦ ι (ζ s)) 2 volume :=
    ((Lp.memLp ζ).continuousLinearMap_comp ι).mono_measure volume_le_restrict_top
  have hgL : MemLp g 2 volume := (Lp.memLp g).mono_measure volume_le_restrict_top
  have hζloc := (hζ.locallyIntegrable one_le_two).locallyIntegrableOn ((⊤ : Opens ℝ) : Set ℝ)
  have hgloc := (hgL.locallyIntegrable one_le_two).locallyIntegrableOn ((⊤ : Opens ℝ) : Set ℝ)
  -- Orthogonality to the paths `s ↦ φ s • w` says that `(ι ζ)' = g` weakly.
  have hweak : HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (ζ s)) g 1 := by
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hζloc, hgloc, fun φ ↦ ?_⟩
    have h₁ := integrable_lineDeriv_smul_of_locallyIntegrableOn hζloc φ 1
    have h₂ := TestFunction.integrable_smul φ hgloc
    rw [eq_neg_iff_add_eq_zero, ← integral_add h₁ h₂]
    refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ (h₁.add h₂) fun c ↦ ?_
    rw [← hinv.self_apply_inverse c, ← integral_inner_eq_zero_of_mem_orthogonal hg φ (A.inverse c)]
    refine integral_congr_ae ?_
    filter_upwards [ae_mono volume_le_restrict_top (A.inverse.coeFn_compLp g)] with s hs
    -- By symmetry, `⟪A w, ι ζ⟫ = ⟪ι w, A ζ⟫ = ⟪ι w, g⟫` with `w = A⁻¹ c`.
    have hs' : ζ s = A.inverse (g s) := hs
    have hc : ⟪c, ι (ζ s)⟫_ℝ = ⟪ι (A.inverse c), g s⟫_ℝ := by
      conv_lhs => rw [← hinv.self_apply_inverse c]
      rw [hA, hs', hinv.self_apply_inverse]
    simp only [inner_add_right, real_inner_smul_right, hc, hinv.self_apply_inverse]
  have hweak' := hweak.congr_ae (ι.coeFn_compLpL ζ).symm
  -- Then `D_{-A} ζ = 0`, and the energy identity for `-A` gives `A ζ = 0`.
  have hA' : ∀ x y, ⟪(-A) x, ι y⟫_ℝ = ⟪ι x, (-A) y⟫_ℝ := fun x y ↦ by simp [hA]
  have hneg : (-A).compLp ζ = -g := by
    simpa only [neg_one_smul, hAζ] using ContinuousLinearMap.smul_compLp (-1 : ℝ) A ζ
  have hD : domainTrajectoryOperator ι (-A) (mkLine _ ζ g hweak') = 0 := by
    rw [domainTrajectoryOperator_mkLine, hneg, add_neg_cancel]
  have hE := norm_domainTrajectoryOperator_sq hA' (mkLine _ ζ g hweak')
  rw [hD, prev_mkLine, hneg, norm_zero, norm_neg, norm_weakFDeriv_mkLine] at hE
  have hg0 : ‖g‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hg0)

/-- **Surjectivity.** For `A` symmetric relative to `ι` and invertible, every `f ∈ L²(ℝ, H)` is
`(ι ξ)' + A ξ` for some `ξ` in the domain. -/
theorem surjective_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) : Function.Surjective (domainTrajectoryOperator ι A) := by
  set K := LinearMap.range (domainTrajectoryOperator ι A).toLinearMap
  have hK : IsClosed (K : Set (Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact isClosed_range_domainTrajectoryOperator hA (norm_le_norm_inverse_mul hinv)
  have hperp : Kᗮ = ⊥ := (Submodule.eq_bot_iff _).2 fun g hg ↦ eq_zero_of_mem_orthogonal hA hinv hg
  have htop : K = ⊤ := by
    rw [← hK.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.2 hperp
  exact LinearMap.range_eq_top.1 htop

/-- **Invertibility of the trajectory operator.** For `A : W →L[ℝ] H` symmetric relative to
`ι` and invertible, `ξ ↦ (ι ξ)' + A ξ` is an isomorphism from the domain
`TauCeti.TrajectoryDomain ι` onto `L²(ℝ, H)`. -/
theorem isInvertible_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) : (domainTrajectoryOperator ι A).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le
    (surjective_domainTrajectoryOperator hA hinv)
    (norm_le_mul_norm_domainTrajectoryOperator hA (norm_le_norm_inverse_mul hinv))

/-- **The inverse bound.** For `A` symmetric relative to `ι` and invertible, the inverse of the
trajectory operator has operator norm at most `max ‖A⁻¹‖ 1`. -/
theorem norm_inverse_domainTrajectoryOperator_le (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) :
    ‖(domainTrajectoryOperator ι A).inverse‖ ≤ max ‖A.inverse‖ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le
      (surjective_domainTrajectoryOperator hA hinv)
      (norm_le_mul_norm_domainTrajectoryOperator hA (norm_le_norm_inverse_mul hinv)))

/-- **The weighted trajectory operator.** For `A` symmetric relative to `ι` and invertible, and
any `C : W →L[ℝ] H`, the trajectory operator of `A - δ C` is invertible for every `δ` close to
`0`. For `C = ι` this is the operator `d/ds + A - δ` into which the exponential weight `e^{δ s}`
turns `d/ds + A`. -/
theorem eventually_isInvertible_domainTrajectoryOperator_sub_smul
    (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hinv : A.IsInvertible) (C : W →L[ℝ] H) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (domainTrajectoryOperator ι (A - δ • C)).IsInvertible := by
  have hcont : Continuous fun δ : ℝ ↦ A - δ • C :=
    continuous_const.sub (continuous_id.smul continuous_const)
  exact (hcont.tendsto' 0 A (by simp)).eventually <|
    eventually_isInvertible_domainTrajectoryOperator (isInvertible_domainTrajectoryOperator hA hinv)

end Hilbert

end TauCeti
