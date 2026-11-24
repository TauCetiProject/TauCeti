/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Partially linear regression: identification

In the partially linear regression model a response `Y` depends on a regressor `D` with values
in `ℝ^d` and a covariate `X` through `E[Y | D, X] = Dᵀβ + g(X)`, with an unknown function `g`.
Here the covariate and the pair `(D, X)` enter only through σ-algebras `mX ≤ mDX`, and `g` is an
a.e. `mX`-measurable function on the sample space.

Partialling out the covariate identifies the coefficient. With the residuals
`V = D - E[D | X]` and `Q = E[V Vᵀ]`, for a finite measure and a square-integrable `Y`,

  `Q β = E[V (Y - E[Y | X])]`,

so `β = Q⁻¹ E[V (Y - E[Y | X])]` when `Q` is positive definite. Indeed
`Y - E[Y | X] - Vᵀβ` is the sum of the residual `Y - E[Y | D, X]`, which is orthogonal to the
`mDX`-measurable `V`, and the `mX`-measurable function `g + E[D | X]ᵀβ - E[Y | X]`, which is
orthogonal to each residual `V j = D j - E[D j | X]`. The normal equations need the residuals
`V j` to be square integrable; under positive definiteness of `Q` this is automatic, since a
diagonal entry `E[(V j)²]` that is not the junk value `0` of a non-integrable function makes
`(V j)²` integrable. No square integrability of `D` itself is assumed.

## Main results

* `TauCeti.partiallyLinear_mulVec`: the normal equations `Q β = E[V (Y - E[Y | X])]`.
* `TauCeti.partiallyLinear_identification`: `β = Q⁻¹ E[V (Y - E[Y | X])]` for positive definite
  `Q`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.11.3.
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner, *Efficient and Adaptive
  Estimation for Semiparametric Models*, Johns Hopkins University Press, 1993, §4.3, Example 5.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d : ℕ}

/-- Under the partially linear model, `Y - E[Y | X]` is `(Y - E[Y | D, X]) + Vᵀβ + h` for a
square-integrable, a.e. `mX`-measurable `h`. -/
private lemma partiallyLinear_exists_decomposition {D : Ω → EuclideanSpace ℝ (Fin d)}
    {Y : Ω → ℝ} {mX mDX : MeasurableSpace Ω}
    (hV2 : ∀ j, MemLp (fun ω ↦ D ω j - μ[fun ω ↦ D ω j | mX] ω) 2 μ) (hY : MemLp Y 2 μ)
    {β : EuclideanSpace ℝ (Fin d)} {g : Ω → ℝ} (hg : AEStronglyMeasurable[mX] g μ)
    (hmodel : μ[Y | mDX] =ᵐ[μ] fun ω ↦ inner ℝ (D ω) β + g ω) :
    ∃ h : Ω → ℝ, AEStronglyMeasurable[mX] h μ ∧ MemLp h 2 μ ∧
      ∀ᵐ ω ∂μ, Y ω - μ[Y | mX] ω = (Y ω - μ[Y | mDX] ω) +
        ∑ i, β i * (D ω i - μ[fun ω ↦ D ω i | mX] ω) + h ω := by
  set h : Ω → ℝ := fun ω ↦ g ω + ∑ i, β i * μ[fun ω ↦ D ω i | mX] ω - μ[Y | mX] ω with hh
  have hdec : ∀ᵐ ω ∂μ, Y ω - μ[Y | mX] ω = (Y ω - μ[Y | mDX] ω) +
      ∑ i, β i * (D ω i - μ[fun ω ↦ D ω i | mX] ω) + h ω := by
    filter_upwards [hmodel] with ω hω
    simp only [hh, hω, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_sub,
      Finset.sum_sub_distrib]
    simp only [mul_comm (β _)]
    ring
  refine ⟨h, ?_, ?_, hdec⟩
  · have hc : StronglyMeasurable[mX] fun ω ↦ ∑ i, β i * μ[fun ω ↦ D ω i | mX] ω :=
      Finset.stronglyMeasurable_fun_sum _ fun i _ ↦ stronglyMeasurable_condExp.const_mul (β i)
    exact (hg.add hc.aestronglyMeasurable).sub stronglyMeasurable_condExp.aestronglyMeasurable
  · refine (((hY.condExp (m := mDX) one_le_two).sub
      (memLp_finsetSum Finset.univ fun i _ ↦ (hV2 i).const_mul (β i))).sub
      (hY.condExp (m := mX) one_le_two)).ae_eq ?_
    filter_upwards [hdec] with ω hω
    simp only [Pi.sub_apply]
    linarith

/-- **Normal equations of partially linear regression.** If `E[Y | D, X] = Dᵀβ + g(X)` with `g`
a.e. `mX`-measurable and the residuals `V j = D j - E[D j | X]` are square integrable, then the
vector `β` solves `∑ i, E[V j V i] β i = E[V j (Y - E[Y | X])]` for every `j`. -/
theorem partiallyLinear_mulVec [IsFiniteMeasure μ] {D : Ω → EuclideanSpace ℝ (Fin d)} {Y : Ω → ℝ}
    {mX mDX : MeasurableSpace Ω} (hmDX : mDX ≤ mΩ) (hXDX : mX ≤ mDX)
    (hV2 : ∀ j, MemLp (fun ω ↦ D ω j - μ[fun ω ↦ D ω j | mX] ω) 2 μ) (hY : MemLp Y 2 μ)
    (hDm : AEStronglyMeasurable[mDX] D μ) {β : EuclideanSpace ℝ (Fin d)} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable[mX] g μ)
    (hmodel : μ[Y | mDX] =ᵐ[μ] fun ω ↦ inner ℝ (D ω) β + g ω) :
    (Matrix.of fun i j ↦ ∫ ω, (D ω i - μ[fun ω ↦ D ω i | mX] ω) *
        (D ω j - μ[fun ω ↦ D ω j | mX] ω) ∂μ).mulVec (WithLp.ofLp β) =
      fun j ↦ ∫ ω, (D ω j - μ[fun ω ↦ D ω j | mX] ω) * (Y ω - μ[Y | mX] ω) ∂μ := by
  obtain ⟨h, hhm, hh2, hdec⟩ := partiallyLinear_exists_decomposition hV2 hY hg hmodel
  set V : Fin d → Ω → ℝ := fun j ω ↦ D ω j - μ[fun ω ↦ D ω j | mX] ω
  ext j
  -- `D j` is integrable: otherwise `E[D j | X] = 0` and `D j = V j` would be.
  have hDi : Integrable (fun ω ↦ D ω j) μ := by
    by_contra hj
    refine hj ((hV2 j).integrable one_le_two |>.congr (ae_of_all _ fun ω ↦ ?_))
    simp [condExp_of_not_integrable hj]
  have hA : MemLp (fun ω ↦ Y ω - μ[Y | mDX] ω) 2 μ := hY.sub (hY.condExp one_le_two)
  -- `V j` is `mDX`-measurable, so it is orthogonal to `Y - E[Y | D, X]`.
  have horthDX : ∫ ω, V j ω * (Y ω - μ[Y | mDX] ω) ∂μ = 0 :=
    MeasureTheory.integral_mul_sub_condExp hmDX
      (((EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hDm).sub
        (stronglyMeasurable_condExp.mono hXDX).aestronglyMeasurable)
      (hY.integrable one_le_two)
  -- `V j = D j - E[D j | X]` is orthogonal to the `mX`-measurable `h`.
  have horthX : ∫ ω, V j ω * h ω ∂μ = 0 := by
    simpa only [mul_comm (h _)] using MeasureTheory.integral_mul_sub_condExp (hXDX.trans hmDX)
      hhm hDi
  have hsum2 : MemLp (fun ω ↦ ∑ i, β i * V i ω) 2 μ :=
    memLp_finsetSum _ fun i _ ↦ (hV2 i).const_mul (β i)
  have h1 : Integrable (fun ω ↦ V j ω * (Y ω - μ[Y | mDX] ω)) μ := (hV2 j).integrable_mul hA
  have h2 : Integrable (fun ω ↦ V j ω * ∑ i, β i * V i ω) μ := (hV2 j).integrable_mul hsum2
  have h3 : Integrable (fun ω ↦ V j ω * h ω) μ := (hV2 j).integrable_mul hh2
  have hres : ∫ ω, V j ω * (Y ω - μ[Y | mX] ω) ∂μ = ∑ i, (∫ ω, V j ω * V i ω ∂μ) * β i := by
    rw [integral_congr_ae (hdec.mono fun ω hω ↦ by rw [hω])]
    simp only [mul_add]
    rw [integral_add (h1.fun_add h2) h3, integral_add h1 h2, horthDX, horthX, zero_add,
      add_zero]
    simp only [Finset.mul_sum]
    rw [integral_finsetSum (f := fun i ω ↦ V j ω * (β i * V i ω)) _
      fun i _ ↦ (hV2 j).integrable_mul ((hV2 i).const_mul (β i))]
    simp only [← integral_mul_const]
    exact Finset.sum_congr rfl fun i _ ↦ integral_congr_ae (ae_of_all _ fun ω ↦ by ring)
  simpa [Matrix.mulVec, dotProduct] using hres.symm

/-- **Identification in partially linear regression.** If `E[Y | D, X] = Dᵀβ + g(X)` with `g`
a.e. `mX`-measurable, `V = D - E[D | X]` and `Q = E[V Vᵀ]` is positive definite, then
`β = Q⁻¹ E[V (Y - E[Y | X])]`. -/
theorem partiallyLinear_identification [IsFiniteMeasure μ] {D : Ω → EuclideanSpace ℝ (Fin d)}
    {Y : Ω → ℝ} {mX mDX : MeasurableSpace Ω} (hmDX : mDX ≤ mΩ) (hXDX : mX ≤ mDX) (hY : MemLp Y 2 μ)
    (hDm : AEStronglyMeasurable[mDX] D μ) {β : EuclideanSpace ℝ (Fin d)} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable[mX] g μ)
    (hmodel : μ[Y | mDX] =ᵐ[μ] fun ω ↦ inner ℝ (D ω) β + g ω) :
    let V : Fin d → Ω → ℝ := fun j ↦ (fun ω ↦ D ω j) - μ[fun ω ↦ D ω j | mX]
    let Q : Matrix (Fin d) (Fin d) ℝ := fun i j ↦ ∫ ω, V i ω * V j ω ∂μ
    Q.PosDef →
      WithLp.ofLp β = Q⁻¹.mulVec (fun j ↦ ∫ ω, V j ω * (Y ω - μ[Y | mX] ω) ∂μ) := by
  intro V Q hQ
  -- `Q j j = E[(V j)²] ≠ 0`, so `(V j)²` is integrable (the integral is not the junk value).
  have hV2 : ∀ j, MemLp (fun ω ↦ D ω j - μ[fun ω ↦ D ω j | mX] ω) 2 μ := fun j ↦ by
    have hm : AEStronglyMeasurable[mΩ] (fun ω ↦ D ω j - μ[fun ω ↦ D ω j | mX] ω) μ :=
      (((EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hDm).mono hmDX).sub
        integrable_condExp.aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hm).2 (Integrable.of_integral_ne_zero ?_)
    simpa [Q, V, sq] using (hQ.diag_pos (i := j)).ne'
  have hnormal : Q.mulVec (WithLp.ofLp β) = fun j ↦ ∫ ω, V j ω * (Y ω - μ[Y | mX] ω) ∂μ :=
    partiallyLinear_mulVec hmDX hXDX hV2 hY hDm hg hmodel
  rw [← hnormal, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det Q).1 hQ.isUnit), Matrix.one_mulVec]

end TauCeti
