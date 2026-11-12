/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.Holder

/-!
# The trajectory operator of a symmetric invertible operator with a domain

Let `ι : W →L[ℝ] H` be a continuous linear map from a Banach space `W` into a real Hilbert space
`H`, and `A : W →L[ℝ] H`. Read `A` as an operator on `H` with domain `W`, such as the asymptotic
operator `A ζ = J₀ (ζ' - S ζ)` of a Hamiltonian orbit, which maps loops in `W = H¹(S¹)` to loops
in `H = L²(S¹)`. Its trajectory operator

`D_A ξ = (ι ξ)' + A ξ`

(`ContinuousLinearMap.domainTrajectoryOperator`) acts on the paths `ξ ∈ L²(ℝ, W)` whose image
`ι ξ` has a weak derivative in `L²(ℝ, H)` (`TauCeti.TrajectoryDomain`), with the graph norm
`(‖ξ‖² + ‖(ι ξ)'‖²)^(1/2)`, and takes values in `L²(ℝ, H)`. For the asymptotic operator this is
the linearized Floer operator `∂s + J₀ (∂t - S)` at the stationary cylinder over the orbit, acting
on `L²(ℝ, H¹(S¹)) ∩ W^{1,2}(ℝ, L²(S¹))`, the anisotropic description of the Sobolev space
`W^{1,2}` of the cylinder. Unlike `TauCeti.WeakDerivStep.trajectoryOperator`, the coefficient need
not be a bounded operator on `H`.

Suppose `A` is **symmetric** relative to `ι`, `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x, y ∈ W`.

* **The energy identity.** For every `ξ` in the domain,

  `‖D_A ξ‖² = ‖(ι ξ)'‖² + ‖A ξ‖²`

  (`ContinuousLinearMap.norm_domainTrajectoryOperator_sq`): the cross term `2 ∫ ⟪(ι ξ)', A ξ⟫`
  vanishes because it is the integral of the weak derivative of the integrable function
  `s ↦ ⟪ι ξ(s), A ξ(s)⟫` (`ContinuousLinearMap.integral_inner_weakFDeriv_apply_prev_eq_zero`).
  This uses the weak product rule `TauCeti.HasWeakLineDerivOn.bilin_self` for the symmetric form
  `(x, y) ↦ ⟪ι x, A y⟫`; no derivative of `A ξ` is needed.
* **The coercive estimate.** If `‖w‖ ≤ C ‖A w‖` on `W`, then `‖ξ‖ ≤ max C 1 ‖D_A ξ‖`
  (`ContinuousLinearMap.norm_le_mul_norm_domainTrajectoryOperator`), so `D_A` is injective with
  closed range.
* **Invertibility.** If moreover `A` is invertible, then `D_A` is invertible
  (`ContinuousLinearMap.isInvertible_domainTrajectoryOperator`). An element `g` orthogonal to the
  range is `A ζ` for `ζ = A⁻¹ g ∈ L²(ℝ, W)`. Testing the orthogonality against the paths
  `s ↦ φ(s) w`, for test functions `φ` and `w ∈ W`, and using the symmetry and surjectivity of
  `A`, shows `(ι ζ)' = A ζ`, that is, `D_{-A} ζ = 0`. The energy identity for the symmetric
  operator `-A` then gives `A ζ = 0`, so `g = 0`.
* **Small weights.** Since `A - δ ι` is again symmetric, and invertible for `δ` close to `0`, the
  operators `D_{A - δ ι} = d/ds + A - δ`, into which the exponential weight `e^{δ s}` turns `D_A`,
  are invertible for small `δ`
  (`ContinuousLinearMap.eventually_isInvertible_domainTrajectoryOperator_sub_smul`).

No spectral decomposition of `A`, no density of `ι`, no compactness and no injectivity of `ι` is
used. Applied to the asymptotic operator of a nondegenerate orbit, which is invertible from
`H¹(S¹)` to `L²(S¹)` and symmetric for a constant compatible complex structure `J₀`, this is the
invertibility of the linearized Floer operator at the stationary cylinder, and of its weighted
versions on the cylindrical ends.

## Main declarations

* `TauCeti.TrajectoryDomain ι`: the domain `{ξ ∈ L²(ℝ, W) | (ι ξ)' ∈ L²(ℝ, H)}`.
* `ContinuousLinearMap.domainTrajectoryOperator ι A`: the operator `ξ ↦ (ι ξ)' + A ξ`.
* `ContinuousLinearMap.norm_domainTrajectoryOperator_sq`: the energy identity.
* `ContinuousLinearMap.norm_le_mul_norm_domainTrajectoryOperator`: the coercive estimate.
* `ContinuousLinearMap.isInvertible_domainTrajectoryOperator`: invertibility.
* `ContinuousLinearMap.eventually_isInvertible_domainTrajectoryOperator_sub_smul`: invertibility
  for small weights.

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

variable {W H : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The domain of the trajectory operator `d/ds + A` of an operator `A` on `H` with domain `W`,
embedded by `ι`: the paths `ξ ∈ L²(ℝ, W)` whose image `ι ξ` has a weak derivative in
`L²(ℝ, H)`, with the graph norm `(‖ξ‖² + ‖(ι ξ)'‖²)^(1/2)`. For the inclusion of `H¹(S¹)` in
`L²(S¹)` it is `L²(ℝ, H¹(S¹)) ∩ W^{1,2}(ℝ, L²(S¹))`, the anisotropic description of the Sobolev
space `W^{1,2}` of the cylinder `ℝ × S¹`. -/
abbrev TrajectoryDomain (ι : W →L[ℝ] H) : Type _ :=
  WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.WeakDerivStep

variable {W H : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A : W →L[ℝ] H}

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
  simp only [domainTrajectoryOperator, add_apply, coe_comp, Function.comp_apply,
    weakFDerivL_apply, prevL_apply]
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

/-- The weak derivative of `ι ξ` on the line, in the direction `1`. -/
private theorem hasWeakLineDerivOn_prev (ξ : TrajectoryDomain ι) :
    HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (prev _ ξ s)) (fun s ↦ weakFDeriv _ ξ s 1) 1 :=
  ((hasWeakFDerivOn_base_prev _ ξ).hasWeakLineDerivOn 1).congr_ae (ι.coeFn_compLp _)

/-- The derivative field `s ↦ (ι ξ)'(s)` is square integrable. -/
private theorem memLp_weakFDeriv_apply_one (ξ : TrajectoryDomain ι) :
    MemLp (fun s ↦ weakFDeriv _ ξ s 1) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (Lp.memLp (weakFDeriv _ ξ)).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ H (1 : ℝ))

/-- Integrals over the restriction of `volume` to the whole line are integrals over `ℝ`. -/
private theorem integral_restrict_top (f : ℝ → ℝ) :
    ∫ s, f s ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) = ∫ s, f s := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- The functional `h ↦ (w ↦ ⟪h, A w⟫)` from `H` to the dual of `W`. -/
private def innerComp (A : W →L[ℝ] H) : H →L[ℝ] StrongDual ℝ W :=
  ((ContinuousLinearMap.compL ℝ W H ℝ).flip A).comp (innerSL ℝ)

omit [CompleteSpace H] in
private theorem innerComp_apply (A : W →L[ℝ] H) (h : H) (w : W) :
    innerComp A h w = ⟪h, A w⟫_ℝ := by
  simp [innerComp]

/-- The evaluation of the weak Fréchet derivative at `1` has the same `L²` norm. -/
private theorem norm_compLp_apply_one (ξ : TrajectoryDomain ι) :
    ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ ξ)‖ = ‖weakFDeriv _ ξ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp (weakFDeriv _ ξ)] with s hs
  rw [hs, ContinuousLinearMap.apply_apply]
  exact (ContinuousLinearMap.toSpanSingletonLIE ℝ H).symm.norm_map (weakFDeriv _ ξ s)

variable [CompleteSpace W]

/-- **The cross term vanishes.** For `A` symmetric relative to `ι`, the `L²` pairing of the weak
derivative `(ι ξ)'` with `A ξ` is zero, for every `ξ` in the domain. -/
theorem integral_inner_weakFDeriv_apply_prev_eq_zero
    (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (ξ : TrajectoryDomain ι) :
    ∫ s, ⟪weakFDeriv _ ξ s 1, A (prev _ ξ s)⟫_ℝ = 0 := by
  -- The symmetric form `B x y = ⟪ι x, A y⟫`.
  set B : W →L[ℝ] W →L[ℝ] ℝ := (innerComp A).comp ι
  have hB : B.flip = B := by
    ext x y
    simp only [flip_apply, B, coe_comp, Function.comp_apply, innerComp_apply]
    rw [real_inner_comm, hA]
  have hval := Lp.memLp (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) ξ)
  have hder := (memLp_weakFDeriv_apply_one ξ).continuousLinearMap_comp (innerComp A)
  have hweak := HasWeakLineDerivOn.bilin_self hB
    ((hasWeakLineDerivOn_prev ξ).clm_comp (innerComp A)) hval hder
  -- The quadratic form and its weak derivative are integrable, so the derivative integrates to `0`.
  have hint {f : ℝ → ℝ} (hf : MemLp f 1 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
      Integrable f := by
    simpa [Measure.restrict_univ] using memLp_one_iff_integrable.1 hf
  have h0 := hweak.integral_eq_zero (hint (B.memLp_of_bilin 1 hval hval))
    ((hint ((ContinuousLinearMap.id ℝ (StrongDual ℝ W)).memLp_of_bilin 1 hder hval)).const_mul 2)
  simp only [innerComp_apply, integral_const_mul, mul_eq_zero, two_ne_zero, false_or] at h0
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
  rw [domainTrajectoryOperator_apply, norm_add_sq_real, hinner, norm_compLp_apply_one]
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

/-- A trajectory operator with a symmetric coefficient bounded below is injective. -/
theorem injective_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    {C : ℝ} (hC : ∀ w, ‖w‖ ≤ C * ‖A w‖) :
    Function.Injective (domainTrajectoryOperator ι A) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
  simpa [hξ] using norm_le_mul_norm_domainTrajectoryOperator hA hC ξ

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

/-- An `L²` field `g` of vectors, as the field `s ↦ (t ↦ t • g s)` of derivatives. -/
private def liftDeriv (g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    Lp (ℝ →L[ℝ] H) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry.toContinuousLinearMap.compLp g

omit [CompleteSpace W] in
/-- The element of the domain with value `ζ` and weak derivative `(ι ζ)' = g`. -/
private def ofDeriv (ζ : Lp W 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (h : HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (ζ s)) g 1) : TrajectoryDomain ι :=
  WeakDerivStep.mk _ ζ (liftDeriv g) <| by
    rw [hasWeakFDerivOn_iff]
    intro v
    have hv := (h.smul_direction v).congr_ae (ι.coeFn_compLpL ζ).symm
    simp only [smul_eq_mul, mul_one] at hv
    refine hv.congr_ae_deriv ?_
    filter_upwards [(ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry
      |>.toContinuousLinearMap.coeFn_compLp g] with t ht
    simp only [liftDeriv, ht, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.toSpanSingletonLIE_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]

omit [CompleteSpace W] in
/-- The trajectory operator of `ofDeriv ζ g h` is `g + A ζ`. -/
private theorem domainTrajectoryOperator_ofDeriv
    (ζ : Lp W 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (g : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (h : HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (ζ s)) g 1) :
    domainTrajectoryOperator ι A (ofDeriv ζ g h) = g + A.compLp ζ := by
  rw [domainTrajectoryOperator_apply, ofDeriv, weakFDeriv_mk, prev_mk]
  congr 1
  refine Lp.ext ?_
  filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLp (liftDeriv g),
    (ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry
      |>.toContinuousLinearMap.coeFn_compLp g] with t h₁ h₂
  rw [h₁, liftDeriv, h₂]
  simp

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

/-- The derivative `s ↦ φ'(s)` of a test function on the line, as a test function. -/
private theorem coe_lineDerivCLM (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ((TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓((⊤ : Opens ℝ), ℝ)) : ℝ → ℝ) =
      fun s ↦ lineDeriv ℝ (φ : ℝ → ℝ) s 1 :=
  funext fun _ ↦ TestFunction.lineDerivCLM_apply_of_le le_top

omit [CompleteSpace W] in
/-- The weak derivative of `s ↦ ι (φ s • w)` is `s ↦ φ'(s) • ι w`. -/
private theorem hasWeakLineDerivOn_testField (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (w : W) :
    HasWeakLineDerivOn volume ⊤ (fun s ↦ ι (testField φ w s))
      (testField (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w)) 1 := by
  have hφ : HasWeakLineDerivOn volume ⊤ (φ : ℝ → ℝ) (fun s ↦ lineDeriv ℝ (φ : ℝ → ℝ) s 1) 1 := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      (φ.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ fun s _ ↦
        ((φ.contDiff.differentiable (by simp)) s).lineDifferentiableAt.hasLineDerivAt
    rw [← coe_lineDerivCLM]
    exact (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ).continuous.locallyIntegrable.locallyIntegrableOn _
  refine ((hφ.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (ι w))).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [testField_ae φ w] with s hs
    simp [hs]
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
      (ofDeriv _ _ (hasWeakLineDerivOn_testField (ι := ι) φ w)))
  rw [ContinuousLinearMap.coe_coe, domainTrajectoryOperator_ofDeriv, L2.inner_def] at h
  rw [← integral_restrict_top, ← h]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (testField (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w))
      (A.compLp (testField φ w)),
    testField_ae (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) (ι w), A.coeFn_compLp (testField φ w),
    testField_ae φ w] with s h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, coe_lineDerivCLM]
  simp [inner_add_left, real_inner_smul_left]

/-- The restriction of `volume` to the whole line is `volume`. -/
private theorem volume_le_restrict_top :
    (volume : Measure ℝ) ≤ volume.restrict ((⊤ : Opens ℝ) : Set ℝ) := by
  rw [Opens.coe_top, Measure.restrict_univ]

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
  -- Then `D_{-A} ζ = 0`, and the energy identity for `-A` gives `A ζ = 0`.
  have hA' : ∀ x y, ⟪(-A) x, ι y⟫_ℝ = ⟪ι x, (-A) y⟫_ℝ := fun x y ↦ by simp [hA]
  have hneg : (-A).compLp ζ = -g := by
    rw [← hAζ]
    refine Lp.ext ?_
    filter_upwards [(-A).coeFn_compLp ζ, Lp.coeFn_neg (A.compLp ζ), A.coeFn_compLp ζ]
      with s h₁ h₂ h₃
    rw [h₁, h₂, Pi.neg_apply, h₃, neg_apply]
  have hD : domainTrajectoryOperator ι (-A) (ofDeriv ζ g hweak) = 0 := by
    rw [domainTrajectoryOperator_ofDeriv, hneg, add_neg_cancel]
  have hE := norm_domainTrajectoryOperator_sq hA' (ofDeriv ζ g hweak)
  rw [hD, ofDeriv, prev_mk, hneg, norm_zero, norm_neg] at hE
  have hg0 : ‖g‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖weakFDeriv _ (ofDeriv ζ g hweak)‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hg0)

/-- **Surjectivity.** For `A` symmetric relative to `ι` and invertible, every `f ∈ L²(ℝ, H)` is
`(ι ξ)' + A ξ` for some `ξ` in the domain. -/
theorem surjective_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) : Function.Surjective (domainTrajectoryOperator ι A) := by
  have hC (w : W) : ‖w‖ ≤ ‖A.inverse‖ * ‖A w‖ := by
    simpa [hinv.inverse_apply_self] using A.inverse.le_opNorm (A w)
  set K := LinearMap.range (domainTrajectoryOperator ι A).toLinearMap
  have hK : IsClosed (K : Set (Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact isClosed_range_domainTrajectoryOperator hA hC
  have hperp : Kᗮ = ⊥ := (Submodule.eq_bot_iff _).2 fun g hg ↦ eq_zero_of_mem_orthogonal hA hinv hg
  have htop : K = ⊤ := by
    rw [← hK.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.2 hperp
  exact LinearMap.range_eq_top.1 htop

/-- **Invertibility of the trajectory operator.** For `A : W →L[ℝ] H` symmetric relative to
`ι` and invertible, `ξ ↦ (ι ξ)' + A ξ` is an isomorphism from the domain
`TauCeti.TrajectoryDomain ι` onto `L²(ℝ, H)`. -/
theorem isInvertible_domainTrajectoryOperator (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hinv : A.IsInvertible) : (domainTrajectoryOperator ι A).IsInvertible := by
  have hC (w : W) : ‖w‖ ≤ ‖A.inverse‖ * ‖A w‖ := by
    simpa [hinv.inverse_apply_self] using A.inverse.le_opNorm (A w)
  exact ⟨ContinuousLinearEquiv.ofBijective (domainTrajectoryOperator ι A)
    (LinearMap.ker_eq_bot.2 (injective_domainTrajectoryOperator hA hC))
    (LinearMap.range_eq_top.2 (surjective_domainTrajectoryOperator hA hinv)), rfl⟩

/-- **The weighted trajectory operator.** For `A` symmetric relative to `ι` and invertible, the
trajectory operator `ξ ↦ (ι ξ)' + A ξ - δ ι ξ` of `A - δ ι` is invertible for every `δ` close to
`0`. This is the operator `d/ds + A - δ` into which the exponential weight `e^{δ s}` turns
`d/ds + A`. -/
theorem eventually_isInvertible_domainTrajectoryOperator_sub_smul
    (hA : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hinv : A.IsInvertible) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (domainTrajectoryOperator ι (A - δ • ι)).IsInvertible := by
  have hcont : Continuous fun δ : ℝ ↦ A - δ • ι :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), (A - δ • ι).IsInvertible :=
    hcont.continuousAt.eventually (by simpa using hinv.eventually_nhds)
  filter_upwards [hev] with δ hδ
  refine isInvertible_domainTrajectoryOperator (fun x y ↦ ?_) hδ
  simp only [sub_apply, smul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hA]

end ContinuousLinearMap
