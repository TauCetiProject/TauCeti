/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SemiFredholm
public import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The trajectory operator over a compactly embedded domain is Fredholm

Let `ι : D →L[ℝ] H` be a compact embedding of a Banach space `D` into a Hilbert space `H`, and
let `A : ℝ → (D →L[ℝ] H)` be an essentially bounded family of operators, given as a class `AL` in
`L∞(ℝ, D →L[ℝ] H)`. The operator `D_A u = (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`
to `L²(ℝ, H)` is `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`. A typical case is
the linearized Floer operator on a strip or a cylinder in a unitary trivialization, where
`A(s) = J₀ ∂ₜ + S(s, t)` acts on loops or paths in `t`, with `D = H¹` and `H = L²`.

Suppose, as in `TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SemiFredholm`, that `A(s)`
converges to invertible `ι`-symmetric operators `B₋` and `B₊` (`⟪B x, ι y⟫ = ⟪ι x, B y⟫`) as
`s → -∞` and `s → ∞`, and that on every bounded interval `A(s)` differs from `B₊` by an operator
bounded through `ι`. That file shows that `D_A` has finite-dimensional kernel and closed range.
This file supplies the missing third property, the finite dimension of the cokernel, and so
proves that `D_A` is Fredholm
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`).

The cokernel is controlled by a right parametrix modulo compact operators
(`TauCeti.WeakDerivStep.exists_isCompactOperator_familyDomainTrajectoryOperator_comp_sub_one`),
built from the autonomous operators `D_{B±}`, which are invertible. No regularity theory for weak
solutions of the adjoint equation is used.

* **The pieces.** Fix smooth cutoffs `γ₋ + γ₊ = 1` in `s`, with `γ₋` supported far out near `-∞`,
  and cutoffs `β±` equal to one on the supports of `γ±`. For `v = D_{B±}⁻¹ (γ± f)`, the
  commutator of `D_A` with `β±` gives
  `D_A (β± v) = γ± f + β± (A - B±) v + β±' (ι ∘ v)`.
  The commutator term `β±' (ι ∘ v)` lives on a bounded window, so it is compact by the
  Aubin–Lions lemma `TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`.
* **The coefficient error.** On `β₋`, which is supported near `-∞`, `A(s)` is close to `B₋`, so
  `β₋ (A - B₋) v` is small. A further cutoff `ρ` splits `β₊ (A - B₊) v` into a part near `+∞`,
  where `A(s)` is close to `B₊`, which is small, and a part on a bounded window, where `A(s) - B₊`
  is bounded through `ι`, which is compact. So `D_A Q = 1 + S + K` for
  `Q f = β₋ D_{B₋}⁻¹ (γ₋ f) + β₊ D_{B₊}⁻¹ (γ₊ f)`, with `‖S‖ < 1` and `K` compact, and
  `Q (1 + S)⁻¹` is a right parametrix modulo compact operators.
* **Fredholm.** The range of `D_A` contains that of the Fredholm operator `D_A Q (1 + S)⁻¹`, so it
  has finite codimension (`ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one`). With
  the finite-dimensional kernel, `D_A` is Fredholm.

Since the Fredholm property holds along the segment between two such families with the same limits
`B±`, the index of `D_A` depends only on `B₋` and `B₊`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`). In particular, a family with
equal limits `B₋ = B₊` gives an operator of index zero
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero`), the index of the
autonomous operator `D_{B}`. The identification of the index with minus the spectral flow of `A`
is not treated here.

## Main results

* `TauCeti.WeakDerivStep.exists_isCompactOperator_familyDomainTrajectoryOperator_comp_sub_one`:
  a right parametrix of `D_A` modulo compact operators.
* `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`: `D_A` is Fredholm.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`: the index depends only on the
  limits `B±`.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero`: equal limits give index
  zero.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the Fredholm property of `d/ds + A(s)` for a family of self-adjoint
  operators over a compactly embedded domain with invertible limits).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7** (1999), Lecture 2 (the Fredholm theory of `∂ₛ + J₀ ∂ₜ + S(s, t)`).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology ContDiff

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι : D →L[ℝ] H}

/-- Almost everywhere for `μ₀` is almost everywhere on the line. -/
private theorem ae_restrict_top : ae μ₀ = ae (volume : Measure ℝ) := by simp

/-! ### Multiplication operators -/

/-- Multiplication of `L²(ℝ, H)` by a bounded continuous function `φ`. -/
private def mulLp (φ : ℝ → ℝ) (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C) :
    Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀ :=
  Lp.multiplicationOperator (linftyOfContinuousOn volume hφ.continuousOn
    (⊤ : Opens ℝ).isOpen.measurableSet ⟨C, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hC s)⟩)

private theorem mulLp_ae {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C)
    (g : Lp H 2 μ₀) : mulLp φ hφ hC g =ᵐ[μ₀] fun s ↦ φ s • g s :=
  Lp.multiplicationOperator_linftyOfContinuousOn_ae _ _ _ g

private theorem norm_mulLp_le {φ : ℝ → ℝ} (hφ : Continuous φ) (hC : ∀ s, |φ s| ≤ 1)
    (g : Lp H 2 μ₀) : ‖mulLp φ hφ hC g‖ ≤ ‖g‖ := by
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) ?_).trans_eq (one_mul _)
  filter_upwards [mulLp_ae hφ hC g] with s hs
  rw [hs, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _)

/-- Multiplications by two functions summing to one add up to the identity. -/
private theorem mulLp_add_mulLp {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {C C' : ℝ}
    (hC : ∀ s, |φ s| ≤ C) (hC' : ∀ s, |ψ s| ≤ C') (h : ∀ s, φ s + ψ s = 1) :
    mulLp (H := H) φ hφ hC + mulLp ψ hψ hC' = 1 := by
  ext g : 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (mulLp φ hφ hC g) (mulLp ψ hψ hC' g), mulLp_ae hφ hC g,
    mulLp_ae hψ hC' g] with s h₁ h₂ h₃
  rw [add_apply, h₁, Pi.add_apply, h₂, h₃, ← add_smul, h s, one_smul,
    one_apply_eq_self]

variable [CompleteSpace H]

/-- Multiplication of the graph space by a smooth cutoff `β` with `|β| ≤ 1` and `|β'| ≤ L`. -/
private def mulGraph (ι : D →L[ℝ] H) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ₀ : ∀ s, |β s| ≤ 1)
    {L : ℝ} (hβ₁ : ∀ s, |deriv β s| ≤ L) :
    WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) :=
  smulLeftCLM β hβ.contDiffOn ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hβ₀ s)⟩
    ⟨L, fun s _ ↦ by rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]; exact hβ₁ s⟩
    ι.compLpL_multiplicationOperator

/-! ### The error terms -/

/-- The coefficient error `u ↦ φ(s) (A(s) - B) u(s)` of a model `B`, cut off by `φ`. -/
private def coeffL (ι : D →L[ℝ] H) (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C) :
    WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] Lp H 2 μ₀ :=
  (mulLp φ hφ hC).comp (familyDomainTrajectoryOperator ι AL - domainTrajectoryOperator ι B)

private theorem coeffL_ae (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    coeffL ι AL B φ hφ hC u =ᵐ[μ₀] fun s ↦ φ s • (AL s - B) (prev _ u s) := by
  rw [coeffL, ContinuousLinearMap.comp_apply, sub_apply]
  filter_upwards [mulLp_ae hφ hC (familyDomainTrajectoryOperator ι AL u -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B u),
    familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B u] with s h₁ h₂
  rw [h₁, h₂]

/-- The commutator term `u ↦ φ(s) ι(u(s))`, for `φ` the derivative of a cutoff. -/
private def commL (ι : D →L[ℝ] H) (φ : ℝ → ℝ) (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ s, |φ s| ≤ C) : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] Lp H 2 μ₀ :=
  (mulLp φ hφ hC).comp ((ι.compLpL 2 μ₀).comp (prevL _))

private theorem commL_ae {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    commL ι φ hφ hC u =ᵐ[μ₀] fun s ↦ φ s • ι (prev _ u s) := by
  filter_upwards [mulLp_ae hφ hC (ι.compLpL 2 μ₀ (prev _ u)),
    ι.coeFn_compLpL (μ := μ₀) (prev _ u)] with s h₁ h₂
  rw [commL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, prevL_apply, h₁, h₂]

/-- The coefficient error splits along a decomposition `β = ρ β + (1 - ρ) β`. -/
private theorem coeffL_eq_add (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) {β ρ : ℝ → ℝ}
    (hβ : Continuous β) (hρ : Continuous ρ) {C C₁ C₂ : ℝ} (hC : ∀ s, |β s| ≤ C)
    (hC₁ : ∀ s, |ρ s * β s| ≤ C₁) (hC₂ : ∀ s, |(1 - ρ s) * β s| ≤ C₂) :
    coeffL ι AL B β hβ hC = coeffL ι AL B (fun s ↦ ρ s * β s) (hρ.mul hβ) hC₁ +
      coeffL ι AL B (fun s ↦ (1 - ρ s) * β s) ((continuous_const.sub hρ).mul hβ) hC₂ := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [coeffL_ae AL B hβ hC u,
    coeffL_ae (φ := fun s ↦ ρ s * β s) AL B (hρ.mul hβ) hC₁ u,
    coeffL_ae (φ := fun s ↦ (1 - ρ s) * β s) AL B ((continuous_const.sub hρ).mul hβ) hC₂ u,
    Lp.coeFn_add (coeffL ι AL B (fun s ↦ ρ s * β s) (hρ.mul hβ) hC₁ u)
      (coeffL ι AL B (fun s ↦ (1 - ρ s) * β s) ((continuous_const.sub hρ).mul hβ) hC₂ u)]
    with s h h₁ h₂ h₃
  rw [add_apply, h₃, Pi.add_apply, h, h₁, h₂, ← add_smul]
  ring_nf

/-- Where `A(s)` is within `ε` of `B` on the support of `φ`, with `|φ| ≤ 1`, the coefficient error
has norm at most `ε`. -/
private theorem norm_coeffL_le (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hC : ∀ s, |φ s| ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ᵐ s ∂μ₀, φ s ≠ 0 → ‖AL s - B‖ ≤ ε) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖coeffL ι AL B φ hφ hC u‖ ≤ ε * ‖u‖ := by
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev _ u) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) hε)
  filter_upwards [coeffL_ae AL B hφ hC u, h] with s hs hsε
  rw [hs, norm_smul, Real.norm_eq_abs]
  by_cases hφs : φ s = 0
  · rw [hφs, abs_zero, zero_mul]
    exact mul_nonneg hε (norm_nonneg _)
  · calc |φ s| * ‖(AL s - B) (prev _ u s)‖ ≤ 1 * (ε * ‖prev _ u s‖) :=
          mul_le_mul (hC s) (((AL s - B).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hsε hφs) (norm_nonneg _))) (norm_nonneg _) zero_le_one
      _ = ε * ‖prev _ u s‖ := one_mul _

/-- Where `A(s) - B` is bounded through `ι` on the support of `φ`, and `φ` vanishes off a bounded
window, the coefficient error is compact. -/
private theorem isCompactOperator_coeffL [CompleteSpace D] (hι : IsCompactOperator ι)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hC : ∀ s, |φ s| ≤ 1) {b c : ℝ} (hc₀ : 0 ≤ c)
    (h : ∀ᵐ s ∂μ₀, φ s ≠ 0 → ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖)
    (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0) : IsCompactOperator (coeffL ι AL B φ hφ hC) := by
  have hW : (⟨Ioo (-b) b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤ := le_top
  refine IsCompactOperator.of_norm_le_mul_norm (C := c)
    (isCompactOperator_restrictBaseL_compLpL (p := 2) hι hW)
    fun u ↦ norm_le_mul_norm_restrictBaseL hc₀ u ?_ ?_
  · simp only [ContinuousLinearMap.coe_coe]
    rw [← ae_restrict_top]
    filter_upwards [coeffL_ae AL B hφ hC u, h] with s hs hsc
    rw [hs, norm_smul, Real.norm_eq_abs]
    by_cases hφs : φ s = 0
    · rw [hφs, abs_zero, zero_mul]
      exact mul_nonneg hc₀ (norm_nonneg _)
    · exact (mul_le_mul (hC s) (hsc hφs _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simp only [ContinuousLinearMap.coe_coe]
    rw [← ae_restrict_top]
    filter_upwards [coeffL_ae AL B hφ hC u] with s hs hsW
    rw [hs, hφ₀ s hsW, zero_smul]

/-- A commutator term whose coefficient vanishes off a bounded window is compact. -/
private theorem isCompactOperator_commL [CompleteSpace D] (hι : IsCompactOperator ι) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L b : ℝ} (hC : ∀ s, |φ s| ≤ L) (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0) :
    IsCompactOperator (commL ι φ hφ hC) := by
  have hL : 0 ≤ L := (abs_nonneg _).trans (hC 0)
  have hW : (⟨Ioo (-b) b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤ := le_top
  refine IsCompactOperator.of_norm_le_mul_norm (C := L)
    (isCompactOperator_restrictBaseL_compLpL (p := 2) hι hW)
    fun u ↦ norm_le_mul_norm_restrictBaseL hL u ?_ ?_
  · simp only [ContinuousLinearMap.coe_coe]
    rw [← ae_restrict_top]
    filter_upwards [commL_ae hφ hC u] with s hs
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _)
  · simp only [ContinuousLinearMap.coe_coe]
    rw [← ae_restrict_top]
    filter_upwards [commL_ae hφ hC u] with s hs hsW
    rw [hs, hφ₀ s hsW, zero_smul]

/-! ### One piece of the parametrix -/

/-- **The commutator identity of a piece.** Let `R` be a right inverse of `D_B`, and let the cutoff
`β` be one on the support of `γ`. For `v = R (γ f)`,
`D_A (β v) = γ f + β (A - B) v + β' (ι ∘ v)`. -/
private theorem familyDomainTrajectoryOperator_comp_mulGraph (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    {B : D →L[ℝ] H} {R : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hR : ∀ g, domainTrajectoryOperator ι B (R g) = g) {β γ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ₀ : ∀ s, |β s| ≤ 1) {L : ℝ} (hβ₁ : ∀ s, |deriv β s| ≤ L) (hγ : Continuous γ)
    (hγ₀ : ∀ s, |γ s| ≤ 1) (hβγ : ∀ s, β s * γ s = γ s) :
    (familyDomainTrajectoryOperator ι AL).comp
        ((mulGraph ι β hβ hβ₀ hβ₁).comp (R.comp (mulLp γ hγ hγ₀))) =
      mulLp γ hγ hγ₀ + (coeffL ι AL B β hβ.continuous hβ₀ +
        commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁).comp (R.comp (mulLp γ hγ hγ₀)) := by
  ext f : 1
  set v := R (mulLp γ hγ hγ₀ f)
  have hv : domainTrajectoryOperator ι B v = mulLp γ hγ hγ₀ f := hR _
  refine Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  filter_upwards [familyDomainTrajectoryOperator_smulLeftCLM_ae ι AL hβ.contDiffOn
      ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hβ₀ s)⟩
      ⟨L, fun s _ ↦ by rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]; exact hβ₁ s⟩ v,
    familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B v,
    Lp.coeFn_sub (familyDomainTrajectoryOperator ι AL v) (domainTrajectoryOperator ι B v),
    mulLp_ae hγ hγ₀ f, coeffL_ae AL B hβ.continuous hβ₀ v,
    commL_ae (hβ.continuous_deriv (by simp)) hβ₁ v,
    Lp.coeFn_add (mulLp γ hγ hγ₀ f) (coeffL ι AL B β hβ.continuous hβ₀ v +
      commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁ v),
    Lp.coeFn_add (coeffL ι AL B β hβ.continuous hβ₀ v)
      (commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁ v)]
    with s h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  -- `D_A v = D_B v + (A - B) v` and `D_B v = γ f`.
  have hDA : familyDomainTrajectoryOperator ι AL v s =
      γ s • f s + (AL s - B) (prev _ v s) := by
    rw [← h₂, h₃, Pi.sub_apply, hv, h₄, add_sub_cancel]
  rw [mulGraph, h₁, hDA, h₇, Pi.add_apply, h₄, h₈, Pi.add_apply, h₅, h₆, smul_add, smul_smul,
    hβγ, add_assoc]

/-- **One piece of the parametrix.** Let `R` be a right inverse of `D_B`, let the cutoff `β` be
one on the support of `γ`, and split `β = ρ β + (1 - ρ) β` with `0 ≤ ρ ≤ 1`. If `A(s)` is within
`ε` of `B` on the support of `(1 - ρ) β`, and on the support of `ρ β`, which lies in a bounded
window carrying the support of `β'`, `A(s) - B` is bounded through `ι`, then
`D_A ∘ β ∘ R ∘ γ = γ + S + K` with `‖S f‖ ≤ ε ‖R‖ ‖f‖` and `K` compact. -/
private theorem exists_familyDomainTrajectoryOperator_comp_mulGraph_eq [CompleteSpace D]
    (hι : IsCompactOperator ι)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) {B : D →L[ℝ] H}
    {R : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hR : ∀ g, domainTrajectoryOperator ι B (R g) = g) {β ρ γ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ₀ : ∀ s, |β s| ≤ 1) {L : ℝ} (hβ₁ : ∀ s, |deriv β s| ≤ L) (hγ : Continuous γ)
    (hγ₀ : ∀ s, |γ s| ≤ 1) (hβγ : ∀ s, β s * γ s = γ s) (hρ : Continuous ρ)
    (hρ₀ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) {ε b c : ℝ} (hε : 0 ≤ ε) (hc₀ : 0 ≤ c)
    (hsmall : ∀ᵐ s ∂μ₀, (1 - ρ s) * β s ≠ 0 → ‖AL s - B‖ ≤ ε)
    (hlow : ∀ᵐ s ∂μ₀, ρ s * β s ≠ 0 → ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖)
    (hρβ : ∀ s ∉ Ioo (-b) b, ρ s * β s = 0) (hβ' : ∀ s ∉ Ioo (-b) b, deriv β s = 0) :
    ∃ S K : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀,
      (familyDomainTrajectoryOperator ι AL).comp
          ((mulGraph ι β hβ hβ₀ hβ₁).comp (R.comp (mulLp γ hγ hγ₀))) = mulLp γ hγ hγ₀ + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * ‖R‖ * ‖f‖) ∧ IsCompactOperator K := by
  have hb₁ (s : ℝ) : |ρ s * β s| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (hρ₀ s).1]
    exact (mul_le_mul (hρ₀ s).2 (hβ₀ s) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hb₂ (s : ℝ) : |(1 - ρ s) * β s| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hρ₀ s).2)]
    exact (mul_le_mul (by linarith [(hρ₀ s).1]) (hβ₀ s) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  refine ⟨(coeffL ι AL B (fun s ↦ (1 - ρ s) * β s)
      ((continuous_const.sub hρ).mul hβ.continuous) hb₂).comp (R.comp (mulLp γ hγ hγ₀)),
    (coeffL ι AL B (fun s ↦ ρ s * β s) (hρ.mul hβ.continuous) hb₁ +
      commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁).comp (R.comp (mulLp γ hγ hγ₀)),
    ?_, fun f ↦ ?_, ?_⟩
  · rw [familyDomainTrajectoryOperator_comp_mulGraph AL hR hβ hβ₀ hβ₁ hγ hγ₀ hβγ,
      coeffL_eq_add AL B hβ.continuous hρ hβ₀ hb₁ hb₂]
    simp only [ContinuousLinearMap.add_comp]
    abel
  · refine (norm_coeffL_le AL B _ hb₂ hε hsmall (R (mulLp γ hγ hγ₀ f))).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((R.le_opNorm _).trans ?_) hε
    exact mul_le_mul_of_nonneg_left (norm_mulLp_le hγ hγ₀ f) (by positivity)
  · refine ((isCompactOperator_coeffL hι AL B _ hb₁ hc₀ hlow hρβ).add
      (isCompactOperator_commL hι _ hβ₁ hβ')).comp_clm (R.comp (mulLp γ hγ hγ₀))

/-! ### The cutoffs -/

private theorem continuous_smoothTransition_sub (c : ℝ) :
    Continuous fun s ↦ Real.smoothTransition (s - c) :=
  Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)

/-- The rising cutoff `s ↦ ψ (s - c)` and the falling cutoff `s ↦ 1 - ψ (s - c)`, for the smooth
transition `ψ`, are smooth, and their derivatives are bounded by a common constant and vanish off
`(c, c + 1)`. -/
private theorem exists_forall_smoothTransition_sub : ∃ L, ∀ c : ℝ,
    (ContDiff ℝ ∞ fun s ↦ Real.smoothTransition (s - c)) ∧
    (∀ s, |deriv (fun s ↦ Real.smoothTransition (s - c)) s| ≤ L) ∧
    (∀ s ∉ Ioo c (c + 1), deriv (fun s ↦ Real.smoothTransition (s - c)) s = 0) ∧
    (ContDiff ℝ ∞ fun s ↦ 1 - Real.smoothTransition (s - c)) ∧
    (∀ s, |deriv (fun s ↦ 1 - Real.smoothTransition (s - c)) s| ≤ L) ∧
    (∀ s ∉ Ioo c (c + 1), deriv (fun s ↦ 1 - Real.smoothTransition (s - c)) s = 0) := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hc (c : ℝ) : ContDiff ℝ ∞ fun s ↦ Real.smoothTransition (s - c) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have h0 (c s : ℝ) (hs : s ∉ Ioo c (c + 1)) : deriv Real.smoothTransition (s - c) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · exact Real.smoothTransition.deriv_of_nonpos (by linarith)
    · exact Real.smoothTransition.deriv_of_one_le (by linarith)
  refine ⟨L, fun c ↦ ⟨hc c, fun s ↦ ?_, fun s hs ↦ ?_, contDiff_const.sub (hc c), fun s ↦ ?_,
    fun s hs ↦ ?_⟩⟩
  · rw [deriv_comp_sub_const, ← Real.norm_eq_abs]
    exact hL _
  · rw [deriv_comp_sub_const, h0 c s hs]
  · rw [deriv_const_sub, deriv_comp_sub_const, abs_neg, ← Real.norm_eq_abs]
    exact hL _
  · rw [deriv_const_sub, deriv_comp_sub_const, h0 c s hs, neg_zero]

/-! ### The parametrix -/

/-- **The piece at `-∞`.** If `A(s)` is within `ε` of `B` for `s ≤ t`, and `R` is a right inverse
of `D_B`, then, for the falling cutoff `γ(s) = 1 - ψ(s - (t - 2))`, there are `Q`, `S` and a compact
`K` with `D_A Q = γ + S + K` and `‖S f‖ ≤ ε ‖R‖ ‖f‖`. -/
private theorem exists_familyDomainTrajectoryOperator_comp_eq_bot [CompleteSpace D]
    (hι : IsCompactOperator ι) (AL : Lp (D →L[ℝ] H) ∞ μ₀) {B : D →L[ℝ] H}
    {R : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hR : ∀ g, domainTrajectoryOperator ι B (R g) = g) {ε t : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ᵐ s ∂μ₀, s ≤ t → ‖AL s - B‖ ≤ ε) :
    ∃ (Q : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))
      (S K : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀),
      (familyDomainTrajectoryOperator ι AL).comp Q =
          mulLp (fun s ↦ 1 - Real.smoothTransition (s - (t - 2)))
            (continuous_const.sub (continuous_smoothTransition_sub _))
            (fun s ↦ Real.smoothTransition.abs_one_sub_le_one _) + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * ‖R‖ * ‖f‖) ∧ IsCompactOperator K := by
  obtain ⟨L, hψ⟩ := exists_forall_smoothTransition_sub
  obtain ⟨-, -, -, hβ, hβ₁, hβ'⟩ := hψ (t - 1)
  have hβ₀ (s : ℝ) := Real.smoothTransition.abs_one_sub_le_one (s - (t - 1))
  -- The cutoff `β(s) = 1 - ψ(s - (t - 1))` is one where `γ` is nonzero, and vanishes for `s ≥ t`.
  have hβγ (s : ℝ) : (1 - Real.smoothTransition (s - (t - 1))) *
      (1 - Real.smoothTransition (s - (t - 2))) = 1 - Real.smoothTransition (s - (t - 2)) := by
    rcases le_or_gt s (t - 1) with hs | hs
    · rw [Real.smoothTransition.zero_of_nonpos (x := s - (t - 1)) (by linarith), sub_zero,
        one_mul]
    · rw [Real.smoothTransition.one_of_one_le (x := s - (t - 2)) (by linarith), sub_self,
        mul_zero]
  have hsmall' : ∀ᵐ s ∂μ₀, (1 - 0) * (1 - Real.smoothTransition (s - (t - 1))) ≠ 0 →
      ‖AL s - B‖ ≤ ε := by
    filter_upwards [hsmall] with s hs h
    refine hs (le_of_not_gt fun hst ↦ h ?_)
    rw [Real.smoothTransition.one_of_one_le (x := s - (t - 1)) (by linarith), sub_zero,
      sub_self, mul_zero]
  have hβ'' : ∀ s ∉ Ioo (-(|t| + 2)) (|t| + 2),
      deriv (fun s ↦ 1 - Real.smoothTransition (s - (t - 1))) s = 0 := fun s hs ↦
    hβ' s fun h ↦ hs ⟨by linarith [h.1, neg_abs_le t], by linarith [h.2, le_abs_self t]⟩
  obtain ⟨S, K, hQ, hS, hK⟩ := exists_familyDomainTrajectoryOperator_comp_mulGraph_eq hι AL hR hβ
    hβ₀ hβ₁ (continuous_const.sub (continuous_smoothTransition_sub _))
    (fun s ↦ Real.smoothTransition.abs_one_sub_le_one _) hβγ (ρ := fun _ ↦ 0) continuous_const
    (fun _ ↦ ⟨le_rfl, zero_le_one⟩) (c := 0) hε le_rfl hsmall'
    (Eventually.of_forall fun s h ↦ absurd (zero_mul _) h) (fun s _ ↦ zero_mul _) hβ''
  exact ⟨_, S, K, hQ, hS, hK⟩

/-- **The piece at `+∞`.** If `A(s)` is within `ε` of `B` for `s ≥ t'`, differs from `B` on every
bounded window by an operator bounded through `ι`, and `R` is a right inverse of `D_B`, then, for
the rising cutoff `χ(s) = ψ(s - (t - 2))`, there are `Q`, `S` and a compact `K` with
`D_A Q = χ + S + K` and `‖S f‖ ≤ ε ‖R‖ ‖f‖`. -/
private theorem exists_familyDomainTrajectoryOperator_comp_eq_top [CompleteSpace D]
    (hι : IsCompactOperator ι) (AL : Lp (D →L[ℝ] H) ∞ μ₀) {B : D →L[ℝ] H}
    {R : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hR : ∀ g, domainTrajectoryOperator ι B (R g) = g) {ε t t' : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ᵐ s ∂μ₀, t' ≤ s → ‖AL s - B‖ ≤ ε)
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂μ₀, s ∈ Ioo (-T) T → ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖) :
    ∃ (Q : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))
      (S K : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀),
      (familyDomainTrajectoryOperator ι AL).comp Q =
          mulLp (fun s ↦ Real.smoothTransition (s - (t - 2))) (continuous_smoothTransition_sub _)
            (fun s ↦ Real.smoothTransition.abs_le_one _) + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * ‖R‖ * ‖f‖) ∧ IsCompactOperator K := by
  obtain ⟨L, hψ⟩ := exists_forall_smoothTransition_sub
  obtain ⟨hβ, hβ₁, hβ', -, -, -⟩ := hψ (t - 3)
  obtain ⟨-, -, -, hρ, -, -⟩ := hψ t'
  set b := |t| + |t'| + 4
  obtain ⟨c, hc⟩ := hc b
  -- The cutoff `β(s) = ψ(s - (t - 3))` is one where `χ` is nonzero, and `ρ(s) = 1 - ψ(s - t')`
  -- vanishes for `s ≥ t' + 1`.
  have hβχ (s : ℝ) : Real.smoothTransition (s - (t - 3)) * Real.smoothTransition (s - (t - 2)) =
      Real.smoothTransition (s - (t - 2)) := by
    rcases le_or_gt (t - 2) s with hs | hs
    · rw [Real.smoothTransition.one_of_one_le (x := s - (t - 3)) (by linarith), one_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (x := s - (t - 2)) (by linarith), mul_zero]
  have hρβ (s : ℝ) (hs : s ∉ Ioo (-b) b) :
      (1 - Real.smoothTransition (s - t')) * Real.smoothTransition (s - (t - 3)) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · rw [Real.smoothTransition.zero_of_nonpos (x := s - (t - 3))
        (by linarith [neg_abs_le t, abs_nonneg t']), mul_zero]
    · rw [Real.smoothTransition.one_of_one_le (x := s - t')
        (by linarith [le_abs_self t', abs_nonneg t]), sub_self, zero_mul]
  have hsmall' : ∀ᵐ s ∂μ₀, (1 - (1 - Real.smoothTransition (s - t'))) *
      Real.smoothTransition (s - (t - 3)) ≠ 0 → ‖AL s - B‖ ≤ ε := by
    filter_upwards [hsmall] with s hs h
    refine hs (le_of_not_gt fun hst ↦ h ?_)
    rw [Real.smoothTransition.zero_of_nonpos (x := s - t') (by linarith), sub_zero, sub_self,
      zero_mul]
  have hlow : ∀ᵐ s ∂μ₀, (1 - Real.smoothTransition (s - t')) *
      Real.smoothTransition (s - (t - 3)) ≠ 0 → ∀ x, ‖(AL s - B) x‖ ≤ max c 0 * ‖ι x‖ := by
    filter_upwards [hc] with s hs h x
    refine (hs (by_contra fun hsb ↦ h (hρβ s hsb)) x).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hβ'' : ∀ s ∉ Ioo (-b) b, deriv (fun s ↦ Real.smoothTransition (s - (t - 3))) s = 0 :=
    fun s hs ↦ hβ' s fun h ↦ hs ⟨by linarith [h.1, neg_abs_le t, abs_nonneg t'],
      by linarith [h.2, le_abs_self t, abs_nonneg t']⟩
  obtain ⟨S, K, hQ, hS, hK⟩ := exists_familyDomainTrajectoryOperator_comp_mulGraph_eq hι AL hR hβ
    (fun s ↦ Real.smoothTransition.abs_le_one _) hβ₁ (continuous_smoothTransition_sub _)
    (fun s ↦ Real.smoothTransition.abs_le_one _) hβχ hρ.continuous
    (fun s ↦ ⟨sub_nonneg.2 (Real.smoothTransition.le_one _),
      sub_le_self _ (Real.smoothTransition.nonneg _)⟩) hε (le_max_right c 0) hsmall' hlow hρβ hβ''
  exact ⟨_, S, K, hQ, hS, hK⟩

/-- **The parametrix up to a small error.** Under the hypotheses of the Fredholm theorem, with
`A(s)` within `ε` of `Bbot` for `s ≤ t` and of `Btop` for `s ≥ t'`, and right inverses `Rbot`,
`Rtop` of `D_{Bbot}`, `D_{Btop}`, there are `Q`, `S` and a compact `K` with `D_A Q = 1 + S + K`
and `‖S f‖ ≤ ε (‖Rbot‖ + ‖Rtop‖) ‖f‖`. -/
private theorem exists_familyDomainTrajectoryOperator_comp_eq_one_add_add [CompleteSpace D]
    (hι : IsCompactOperator ι) (AL : Lp (D →L[ℝ] H) ∞ μ₀) {Bbot Btop : D →L[ℝ] H}
    {Rbot Rtop : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hRbot : ∀ g, domainTrajectoryOperator ι Bbot (Rbot g) = g)
    (hRtop : ∀ g, domainTrajectoryOperator ι Btop (Rtop g) = g) {ε t t' : ℝ} (hε : 0 ≤ ε)
    (hbot : ∀ᵐ s ∂μ₀, s ≤ t → ‖AL s - Bbot‖ ≤ ε) (htop : ∀ᵐ s ∂μ₀, t' ≤ s → ‖AL s - Btop‖ ≤ ε)
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂μ₀, s ∈ Ioo (-T) T → ∀ x, ‖(AL s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ (Q : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))
      (S K : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀),
      (familyDomainTrajectoryOperator ι AL).comp Q = 1 + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * (‖Rbot‖ + ‖Rtop‖) * ‖f‖) ∧ IsCompactOperator K := by
  obtain ⟨Qbot, Sbot, Kbot, hbot, hSbot, hKbot⟩ :=
    exists_familyDomainTrajectoryOperator_comp_eq_bot hι AL hRbot hε hbot
  obtain ⟨Qtop, Stop, Ktop, htop, hStop, hKtop⟩ :=
    exists_familyDomainTrajectoryOperator_comp_eq_top hι AL hRtop (t := t) hε htop hc
  refine ⟨Qbot + Qtop, Sbot + Stop, Kbot + Ktop, ?_, fun f ↦ ?_, hKbot.add hKtop⟩
  · rw [ContinuousLinearMap.comp_add, hbot, htop, ← mulLp_add_mulLp
      (φ := fun s ↦ 1 - Real.smoothTransition (s - (t - 2)))
      (ψ := fun s ↦ Real.smoothTransition (s - (t - 2)))
      (continuous_const.sub (continuous_smoothTransition_sub (t - 2)))
      (continuous_smoothTransition_sub (t - 2))
      (fun s ↦ Real.smoothTransition.abs_one_sub_le_one _)
      (fun s ↦ Real.smoothTransition.abs_le_one _) fun s ↦ sub_add_cancel _ _]
    ac_rfl
  · rw [add_apply, mul_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hSbot f) (hStop f))

variable [CompleteSpace D] {Bbot Btop : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H}
  {AL : Lp (D →L[ℝ] H) ∞ μ₀}

/-- **A right parametrix of the trajectory operator modulo compact operators.** Let `ι` be a
compact operator, and let `A(s)` converge to invertible `ι`-symmetric operators `Bbot` and `Btop`
at `-∞` and `∞` and differ from `Btop` on every bounded interval by an operator bounded through
`ι`: for every `T` there is `c` with `‖(A(s) - Btop) x‖ ≤ c ‖ι x‖` for almost every `s ∈ (-T, T)`.
Then there is `Q : L²(ℝ, H) → L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` such that `D_A Q - 1` is compact, for
`D_A u = (ι ∘ u)' + A u`. -/
theorem exists_isCompactOperator_familyDomainTrajectoryOperator_comp_sub_one
    (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ Q : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      IsCompactOperator ((familyDomainTrajectoryOperator (p := 2) ι AL).comp Q - 1 :
        Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀) := by
  set Rbot := (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι Bbot).inverse
  set Rtop := (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι Btop).inverse
  set ε := (2 * (‖Rbot‖ + ‖Rtop‖ + 1))⁻¹
  have hε : 0 < ε := by positivity
  -- `A(s)` is within `ε` of its limits far out on the two ends.
  obtain ⟨t, ht⟩ := eventually_atBot.1 (hbot.eventually (Metric.closedBall_mem_nhds Bbot hε))
  obtain ⟨t', ht'⟩ := eventually_atTop.1 (htop.eventually (Metric.closedBall_mem_nhds Btop hε))
  obtain ⟨Q, S, K, hQ, hS, hK⟩ := exists_familyDomainTrajectoryOperator_comp_eq_one_add_add hι AL
    ((isInvertible_domainTrajectoryOperator hSymmbot hBbot).self_apply_inverse)
    ((isInvertible_domainTrajectoryOperator hSymmtop hBtop).self_apply_inverse) hε.le
    (hAL.mono fun s hs hst ↦ by rw [hs, ← dist_eq_norm]; exact ht s hst)
    (hAL.mono fun s hs hst ↦ by rw [hs, ← dist_eq_norm]; exact ht' s hst)
    (fun T ↦ (hc T).imp fun c h ↦ by
      filter_upwards [hAL, ae_restrict_of_ae h] with s hs h'
      rwa [hs])
  -- `‖S‖ ≤ 1 / 2`, so `1 + S` is invertible, and `Q (1 + S)⁻¹` is the parametrix.
  have hSn : ‖-S‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]
    refine (S.opNorm_le_bound (by positivity) hS).trans_lt ?_
    rw [inv_mul_lt_one₀ (by positivity)]
    linarith [norm_nonneg Rbot, norm_nonneg Rtop]
  set U := Units.oneSub (-S) hSn
  set V : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀ := ↑U⁻¹
  refine ⟨Q.comp V, ?_⟩
  have hU : (U : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀).comp V = 1 := U.mul_inv
  have : (familyDomainTrajectoryOperator ι AL).comp (Q.comp V) - 1 = K.comp V := by
    rw [← ContinuousLinearMap.comp_assoc, hQ, show (1 : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀) + S =
      U by rw [Units.val_oneSub, sub_neg_eq_add], ContinuousLinearMap.add_comp, hU]
    abel
  rw [this]
  exact hK.comp_clm _

/-- **The trajectory operator over a compactly embedded domain is Fredholm.** Let `ι` be a compact
operator, and let `A(s)` converge to invertible `ι`-symmetric operators `Bbot` and `Btop` at `-∞`
and `∞` and differ from `Btop` on every bounded interval by an operator bounded through `ι`: for
every `T` there is `c` with `‖(A(s) - Btop) x‖ ≤ c ‖ι x‖` for almost every `s ∈ (-T, T)`. Then
`u ↦ (ι ∘ u)' + A u` is a Fredholm operator from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)`. -/
theorem isFredholm_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm := by
  obtain ⟨Q, hQ⟩ := exists_isCompactOperator_familyDomainTrajectoryOperator_comp_sub_one hι
    hSymmbot hBbot hSymmtop hBtop hAL hbot htop hc
  exact .of_finite_ker_coker _ (finiteDimensional_ker_familyDomainTrajectoryOperator hι hSymmbot
    hBbot hSymmtop hBtop hAL hbot htop hc)
    (ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one _ hQ)

/-- **The index depends only on the limits.** Let `A` and `A'` both converge to the invertible
`ι`-symmetric operators `Bbot` at `-∞` and `Btop` at `∞`, and differ from `Btop` on every bounded
interval by operators bounded through `ι`. For compact `ι`, the operators `u ↦ (ι ∘ u)' + A u` and
`u ↦ (ι ∘ u)' + A' u` have the same Fredholm index. -/
theorem index_familyDomainTrajectoryOperator_eq (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖)
    {A' : ℝ → D →L[ℝ] H} {AL' : Lp (D →L[ℝ] H) ∞ μ₀} (hAL' : AL' =ᵐ[μ₀] A')
    (hbot' : Tendsto A' atBot (𝓝 Bbot)) (htop' : Tendsto A' atTop (𝓝 Btop))
    (hc' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A' s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index =
      (familyDomainTrajectoryOperator (p := 2) ι AL').index := by
  -- Every family on the segment from `A` to `A'` satisfies the hypotheses of the Fredholm theorem.
  have hF (r : ℝ) :
      (familyDomainTrajectoryOperator (p := 2) ι ((1 - r) • AL + r • AL')).IsFredholm := by
    refine isFredholm_familyDomainTrajectoryOperator (A := fun s ↦ (1 - r) • A s + r • A' s) hι
      hSymmbot hBbot hSymmtop hBtop ?_ ?_ ?_ fun T ↦ ?_
    · filter_upwards [Lp.coeFn_add ((1 - r) • AL) (r • AL'), Lp.coeFn_smul (1 - r) AL,
        Lp.coeFn_smul r AL', hAL, hAL'] with s h₁ h₂ h₃ h₄ h₅
      rw [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, Pi.smul_apply, h₄, h₅]
    · simpa [← add_smul] using (hbot.const_smul (1 - r)).add (hbot'.const_smul r)
    · simpa [← add_smul] using (htop.const_smul (1 - r)).add (htop'.const_smul r)
    obtain ⟨c, hc⟩ := hc T
    obtain ⟨c', hc'⟩ := hc' T
    refine ⟨|1 - r| * c + |r| * c', ?_⟩
    filter_upwards [hc, hc'] with s hs hs' hsT x
    have : ((1 - r) • A s + r • A' s - Btop) x =
        (1 - r) • (A s - Btop) x + r • (A' s - Btop) x := by
      simp only [sub_apply, add_apply, smul_apply, smul_sub]
      module
    rw [this, add_mul, mul_assoc, mul_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs] <;>
      gcongr
    exacts [hs hsT x, hs' hsT x]
  have hcont : Continuous fun r : ℝ ↦
      familyDomainTrajectoryOperator (p := 2) ι ((1 - r) • AL + r • AL') :=
    (continuous_familyDomainTrajectoryOperator ι).comp (by fun_prop)
  simpa using hcont.continuousOn.index_eq_of_isPreconnected (fun r _ ↦ hF r) isPreconnected_Icc
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)

/-- **Equal limits give index zero.** If `A(s)` converges to the same invertible `ι`-symmetric
operator `B` at `-∞` and at `∞`, and differs from `B` on every bounded interval by an operator
bounded through `ι`, then for compact `ι` the operator `u ↦ (ι ∘ u)' + A u` is Fredholm of index
zero, the index of the autonomous operator `u ↦ (ι ∘ u)' + B u`. -/
theorem index_familyDomainTrajectoryOperator_eq_zero (hι : IsCompactOperator ι) {B : D →L[ℝ] H}
    (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (hB : B.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 B)) (htop : Tendsto A atTop (𝓝 B))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index = 0 := by
  rw [index_familyDomainTrajectoryOperator_eq hι hSymm hB hSymm hB hAL hbot htop hc
    (memLp_top_const (μ := μ₀) B).coeFn_toLp tendsto_const_nhds tendsto_const_nhds
    fun T ↦ ⟨0, Eventually.of_forall fun s _ x ↦ by simp⟩,
    familyDomainTrajectoryOperator_toLp_const]
  exact index_domainTrajectoryOperator hSymm hB

end TauCeti.WeakDerivStep
