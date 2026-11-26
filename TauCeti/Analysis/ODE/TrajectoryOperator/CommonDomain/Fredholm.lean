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
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Fredholm property and index of the trajectory operator over a compactly embedded domain

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
autonomous operator `D_{B}`.

**Catenation.** Gluing two operators along an invertible model adds their indices. Let `D_B` be
invertible, and let `A₁ = B` on `[a, ∞)` and `A₂ = B` on `(-∞, b]`, with `a < b`. The glued
coefficient `A₃ = A₁ + A₂ - B` agrees with `A₁` on `(-∞, a]` and with `A₂` on `[b, ∞)`, and
`D_{A₃} = D_{A₁} + D_{A₂} - D_B`. With `G = D_B⁻¹` and `Mᵢ = D_{Aᵢ} - D_B`, so that
`D_{Aᵢ} G = 1 + Mᵢ G`, this reads `D_{A₃} G = (D_{A₁} G) (D_{A₂} G) - M₁ G M₂ G`. For a cutoff `χ`
vanishing on `(-∞, a]` and equal to one on `[b, ∞)`, `M₂ = χ M₂` and `M₁ χ = 0`, while `G` commutes
with `χ` up to `G χ' ι G`. So the cross term is `M₁ G M₂ G = -M₁ G χ' ι G M₂ G`, which is compact by
the Aubin–Lions lemma since `χ'` vanishes off `[a, b]`. Hence `D_{A₃}` is Fredholm when `D_{A₁}` and
`D_{A₂}` are (`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_add_sub`), with
`ind D_{A₃} = ind D_{A₁} + ind D_{A₂}`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_add_sub`). No estimate along a long
neck is needed. Since the index depends only on the limits, this gives the catenation law
`ind D_{A''} = ind D_A + ind D_{A'}` for families `A` from `B₀` to `B₁`, `A'` from `B₁` to `B₂`
and `A''` from `B₀` to `B₂`, provided `B₁ - B₂` is bounded through `ι`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add`): cut `A` off to `B₁` and
`A'` off to `B₁` on overlapping half-lines and glue. The identification of the index with minus
the spectral flow of `A` is not treated here.

## Main results

* `TauCeti.WeakDerivStep.exists_isCompactOperator_familyDomainTrajectoryOperator_comp_sub_one`:
  a right parametrix of `D_A` modulo compact operators.
* `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`: `D_A` is Fredholm.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`: the index depends only on the
  limits `B±`.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero`: equal limits give index
  zero.
* `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_add_sub`,
  `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_add_sub`: gluing two Fredholm
  operators along an invertible model gives a Fredholm operator, and the indices add.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_add`: the index is additive under
  catenation of families.

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

/-! ### Multiplication operators -/

/-- Multiplication of `L²(ℝ, H)` by a bounded continuous function `φ`. -/
private def mulLp (φ : ℝ → ℝ) (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C) :
    Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀ :=
  Lp.multiplicationOperator (linftyOfContinuousOn volume hφ.continuousOn
    (⊤ : Opens ℝ).isOpen.measurableSet ⟨C, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hC s)⟩)

private theorem mulLp_ae {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C)
    (g : Lp H 2 μ₀) : mulLp φ hφ hC g =ᵐ[μ₀] fun s ↦ φ s • g s :=
  Lp.multiplicationOperator_linftyOfContinuousOn_ae _ _ _ g

variable [CompleteSpace H]

/-- Multiplication of the graph space by a smooth cutoff `β` with `|β| ≤ 1` and `|β'| ≤ L`. -/
private def mulGraph (ι : D →L[ℝ] H) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ₀ : ∀ s, |β s| ≤ 1)
    {L : ℝ} (hβ₁ : ∀ s, |deriv β s| ≤ L) :
    WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) :=
  smulLeftCLM β hβ.contDiffOn ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hβ₀ s)⟩
    (exists_forall_norm_fderiv_le_of_abs_deriv_le fun s _ ↦ hβ₁ s)
    ι.compLpL_multiplicationOperator

/-! ### The error terms -/

/-- The coefficient error `u ↦ φ(s) (A(s) - B) u(s)` of a model `B`, cut off by `φ`. -/
private def coeffL (ι : D →L[ℝ] H) (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {C : ℝ} (hC : ∀ s, |φ s| ≤ C) :
    WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] Lp H 2 μ₀ :=
  (mulLp φ hφ hC).comp (familyDomainTrajectoryOperator (p := 2) ι AL -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B)

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
  congr 1
  ring

/-- The pointwise bound behind the coefficient error: `|a| ‖y‖ ≤ k` when `|a| ≤ 1` and `‖y‖ ≤ k`
unless `a = 0`. -/
private theorem abs_mul_norm_le {E : Type*} [SeminormedAddCommGroup E] {a k : ℝ} {y : E}
    (ha : |a| ≤ 1) (hk : 0 ≤ k) (h : a ≠ 0 → ‖y‖ ≤ k) : |a| * ‖y‖ ≤ k := by
  by_cases ha₀ : a = 0
  · rwa [ha₀, abs_zero, zero_mul]
  · exact (mul_le_mul ha (h ha₀) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

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
  exact abs_mul_norm_le (hC s) (mul_nonneg hε (norm_nonneg _)) fun hφs ↦
    ((AL s - B).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsε hφs) (norm_nonneg _))

/-- Where `A(s) - B` is bounded through `ι` on the support of `φ`, and `φ` vanishes off a bounded
window, the coefficient error is compact. -/
private theorem isCompactOperator_coeffL [CompleteSpace D] (hι : IsCompactOperator ι)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (B : D →L[ℝ] H) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hC : ∀ s, |φ s| ≤ 1) {b c : ℝ} (hc₀ : 0 ≤ c)
    (h : ∀ᵐ s ∂μ₀, φ s ≠ 0 → ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖)
    (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0) : IsCompactOperator (coeffL ι AL B φ hφ hC) := by
  refine isCompactOperator_of_ae_norm_le hι (a := -b) (b := b) le_top hc₀ (fun u ↦ ?_)
    (fun u ↦ ?_)
  · filter_upwards [coeffL_ae AL B hφ hC u, h] with s hs hsc
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact abs_mul_norm_le (hC s) (mul_nonneg hc₀ (norm_nonneg _)) fun hφs ↦ hsc hφs _
  · filter_upwards [coeffL_ae AL B hφ hC u] with s hs hsW
    rw [hs, hφ₀ s hsW, zero_smul]

/-- A commutator term whose coefficient vanishes off a bounded window is compact. -/
private theorem isCompactOperator_commL [CompleteSpace D] (hι : IsCompactOperator ι) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L b : ℝ} (hC : ∀ s, |φ s| ≤ L) (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0) :
    IsCompactOperator (commL ι φ hφ hC) := by
  refine isCompactOperator_of_ae_norm_le hι (a := -b) (b := b) le_top
    ((abs_nonneg _).trans (hC 0)) (fun u ↦ ?_) (fun u ↦ ?_)
  · filter_upwards [commL_ae hφ hC u] with s hs
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _)
  · filter_upwards [commL_ae hφ hC u] with s hs hsW
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
      (exists_forall_norm_fderiv_le_of_abs_deriv_le fun s _ ↦ hβ₁ s) v,
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
    exact mul_le_mul_of_nonneg_left (Lp.norm_multiplicationOperator_linftyOfContinuousOn_apply_le
      _ _ _ (fun s _ ↦ (Real.norm_eq_abs _).trans_le (hγ₀ s)) f) (by positivity)
  · refine ((isCompactOperator_coeffL hι AL B _ hb₁ hc₀ hlow hρβ).add
      (isCompactOperator_commL hι _ hβ₁ hβ')).comp_clm (R.comp (mulLp γ hγ hγ₀))

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
            (by fun_prop)
            (fun s ↦ Real.smoothTransition.abs_one_sub_le_one _) + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * ‖R‖ * ‖f‖) ∧ IsCompactOperator K := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hβ : ContDiff ℝ ∞ fun s ↦ 1 - Real.smoothTransition (s - (t - 1)) := by fun_prop
  have hβ₁ (s : ℝ) : |deriv (fun s ↦ 1 - Real.smoothTransition (s - (t - 1))) s| ≤ L := by
    rw [deriv_const_sub, abs_neg]
    exact Real.smoothTransition.abs_deriv_comp_sub_const_le hL _ _
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
      deriv (fun s ↦ 1 - Real.smoothTransition (s - (t - 1))) s = 0 := fun s hs ↦ by
    rw [deriv_const_sub, Real.smoothTransition.deriv_comp_sub_const_of_notMem_Ioo, neg_zero]
    exact fun h ↦ hs ⟨by linarith [h.1, neg_abs_le t], by linarith [h.2, le_abs_self t]⟩
  obtain ⟨S, K, hQ, hS, hK⟩ := exists_familyDomainTrajectoryOperator_comp_mulGraph_eq hι AL hR hβ
    hβ₀ hβ₁ (by fun_prop)
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
          mulLp (fun s ↦ Real.smoothTransition (s - (t - 2))) (by fun_prop)
            (fun s ↦ Real.smoothTransition.abs_le_one _) + S + K ∧
        (∀ f, ‖S f‖ ≤ ε * ‖R‖ * ‖f‖) ∧ IsCompactOperator K := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hβ : ContDiff ℝ ∞ fun s ↦ Real.smoothTransition (s - (t - 3)) := by fun_prop
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
    fun s hs ↦ Real.smoothTransition.deriv_comp_sub_const_of_notMem_Ioo fun h ↦
      hs ⟨by linarith [h.1, neg_abs_le t, abs_nonneg t'],
        by linarith [h.2, le_abs_self t, abs_nonneg t']⟩
  obtain ⟨S, K, hQ, hS, hK⟩ := exists_familyDomainTrajectoryOperator_comp_mulGraph_eq hι AL hR hβ
    (fun s ↦ Real.smoothTransition.abs_le_one _)
    (Real.smoothTransition.abs_deriv_comp_sub_const_le hL _) (by fun_prop)
    (fun s ↦ Real.smoothTransition.abs_le_one _) hβχ (by fun_prop)
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
  · have h₁ : mulLp (H := H) (fun s ↦ 1 - Real.smoothTransition (s - (t - 2))) (by fun_prop)
          (fun s ↦ Real.smoothTransition.abs_one_sub_le_one _) +
        mulLp (fun s ↦ Real.smoothTransition (s - (t - 2))) (by fun_prop)
          (fun s ↦ Real.smoothTransition.abs_le_one _) = 1 :=
      Lp.multiplicationOperator_linftyOfContinuousOn_add_eq_one _ _ _ _ _
        fun s _ ↦ sub_add_cancel _ _
    rw [ContinuousLinearMap.comp_add, hbot, htop, ← h₁]
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
bounded through `ι`, then for compact `ι` the operator `u ↦ (ι ∘ u)' + A u` has index zero, the
index of the autonomous operator `u ↦ (ι ∘ u)' + B u`. It is Fredholm by
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`. -/
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

/-! ### Catenation of the index -/

omit [CompleteSpace D] in
/-- **The commutator of the trajectory operator with a cutoff.** Multiplying by a smooth cutoff `β`
before applying `D_A` is multiplying by `β` afterwards, up to the term `β' (ι ∘ u)`:
`D_A (β u) = β D_A u + β' (ι ∘ u)`. -/
private theorem familyDomainTrajectoryOperator_comp_mulGraph_eq_add
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ₀ : ∀ s, |β s| ≤ 1) {L : ℝ}
    (hβ₁ : ∀ s, |deriv β s| ≤ L) :
    (familyDomainTrajectoryOperator ι AL).comp (mulGraph ι β hβ hβ₀ hβ₁) =
      (mulLp β hβ.continuous hβ₀).comp (familyDomainTrajectoryOperator ι AL) +
        commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁ := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [familyDomainTrajectoryOperator_smulLeftCLM_ae ι AL hβ.contDiffOn
      ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hβ₀ s)⟩
      (exists_forall_norm_fderiv_le_of_abs_deriv_le fun s _ ↦ hβ₁ s) u,
    Lp.coeFn_add (mulLp β hβ.continuous hβ₀ (familyDomainTrajectoryOperator ι AL u))
      (commL ι (deriv β) (hβ.continuous_deriv (by simp)) hβ₁ u),
    mulLp_ae hβ.continuous hβ₀ (familyDomainTrajectoryOperator ι AL u),
    commL_ae (hβ.continuous_deriv (by simp)) hβ₁ u] with s h₁ h₂ h₃ h₄
  rw [ContinuousLinearMap.comp_apply, mulGraph, h₁, add_apply,
    ContinuousLinearMap.comp_apply, h₂, Pi.add_apply, h₃, h₄]

omit [CompleteSpace D] in
/-- Where `χ` vanishes on `(-∞, a]` and `A = B` almost everywhere on `[a, ∞)`, the coefficient
error `A - B` annihilates `χ u`. -/
private theorem familyDomainTrajectoryOperator_sub_mulGraph_eq_zero {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    {B : D →L[ℝ] H} {a : ℝ} (h : ∀ᵐ s ∂μ₀, a ≤ s → AL s = B) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ₀ : ∀ s, |χ s| ≤ 1) {L : ℝ} (hχ₁ : ∀ s, |deriv χ s| ≤ L) (hχa : ∀ s, s ≤ a → χ s = 0)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    (familyDomainTrajectoryOperator (p := 2) ι AL -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B)
      (mulGraph ι χ hχ hχ₀ hχ₁ u) = 0 := by
  refine Lp.ext ?_
  filter_upwards [familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B
      (mulGraph ι χ hχ hχ₀ hχ₁ u),
    prev_smulLeftCLM_ae hχ.contDiffOn ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hχ₀ s)⟩
      (exists_forall_norm_fderiv_le_of_abs_deriv_le fun s _ ↦ hχ₁ s)
      ι.compLpL_multiplicationOperator u,
    h, Lp.coeFn_zero H 2 μ₀] with s hs hp hsa h0
  rw [sub_apply, hs, h0, Pi.zero_apply, mulGraph, hp, map_smul]
  rcases le_total s a with h' | h'
  · rw [hχa s h', zero_smul]
  · rw [hsa h', sub_self, zero_apply, smul_zero]

omit [CompleteSpace D] in
/-- Where `χ` is one on `[b, ∞)` and `A = B` almost everywhere on `(-∞, b]`, multiplying the
coefficient error `(A - B) u` by `χ` does not change it. -/
private theorem mulLp_familyDomainTrajectoryOperator_sub {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    {B : D →L[ℝ] H} {b : ℝ} (h : ∀ᵐ s ∂μ₀, s ≤ b → AL s = B) {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hχ₀ : ∀ s, |χ s| ≤ 1) (hχb : ∀ s, b ≤ s → χ s = 1)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    mulLp χ hχ hχ₀ ((familyDomainTrajectoryOperator (p := 2) ι AL -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B) u) =
      (familyDomainTrajectoryOperator (p := 2) ι AL -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B) u := by
  refine Lp.ext ?_
  filter_upwards [mulLp_ae hχ hχ₀
      ((familyDomainTrajectoryOperator (p := 2) ι AL -
      domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B) u),
    familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B u, h] with s hs hs' hsb
  rw [hs, sub_apply, hs']
  rcases le_total s b with h' | h'
  · rw [hsb h', sub_self, zero_apply, smul_zero]
  · rw [hχb s h', one_smul]

omit [CompleteSpace D] in
/-- **The inverse of `D_B` commutes with a cutoff up to a compact term.** If `e` identifies `D_B`
with an isomorphism, then `e⁻¹ (χ f) = χ e⁻¹ f - e⁻¹ (χ' ι (e⁻¹ f))`. -/
private theorem symm_mulLp_eq_mulGraph_symm_sub {B : D →L[ℝ] H}
    (e : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) ≃L[ℝ] Lp H 2 μ₀)
    (he : (e : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] Lp H 2 μ₀) =
      domainTrajectoryOperator ι B) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ₀ : ∀ s, |χ s| ≤ 1)
    {L : ℝ} (hχ₁ : ∀ s, |deriv χ s| ≤ L) (f : Lp H 2 μ₀) :
    e.symm (mulLp χ hχ.continuous hχ₀ f) = mulGraph ι χ hχ hχ₀ hχ₁ (e.symm f) -
      e.symm (commL ι (deriv χ) (hχ.continuous_deriv (by simp)) hχ₁ (e.symm f)) := by
  have h := congrArg (· (e.symm f)) (familyDomainTrajectoryOperator_comp_mulGraph_eq_add (ι := ι)
    ((memLp_top_const (μ := μ₀) B).toLp _) hχ hχ₀ hχ₁)
  simp only [familyDomainTrajectoryOperator_toLp_const, ← he, ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
  rw [eq_sub_of_add_eq h.symm, map_sub, ContinuousLinearEquiv.symm_apply_apply]

/-- **The glued operator through an invertible model.** Let `e` identify `D_B` with an isomorphism,
and let `A₁ = B` on `[a, ∞)` and `A₂ = B` on `(-∞, b]`, with `a < b`. For the glued coefficient
`A₃ = A₁ + A₂ - B`, the operator `D_{A₃} e⁻¹` is the product `(D_{A₁} e⁻¹) (D_{A₂} e⁻¹)` up to a
compact operator. -/
private theorem exists_isCompactOperator_familyDomainTrajectoryOperator_add_sub_comp_eq
    (hι : IsCompactOperator ι) {B : D →L[ℝ] H}
    (e : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) ≃L[ℝ] Lp H 2 μ₀)
    (he : (e : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ] Lp H 2 μ₀) =
      domainTrajectoryOperator ι B) {AL₁ AL₂ : Lp (D →L[ℝ] H) ∞ μ₀} {a b : ℝ} (hab : a < b)
    (h₁ : ∀ᵐ s ∂μ₀, a ≤ s → AL₁ s = B) (h₂ : ∀ᵐ s ∂μ₀, s ≤ b → AL₂ s = B) :
    ∃ K : Lp H 2 μ₀ →L[ℝ] Lp H 2 μ₀, IsCompactOperator K ∧
      (familyDomainTrajectoryOperator ι (AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _)).comp
          (e.symm : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) =
        ((familyDomainTrajectoryOperator ι AL₁).comp
          (e.symm : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))).comp
          ((familyDomainTrajectoryOperator ι AL₂).comp
            (e.symm : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀))) + K := by
  obtain ⟨χ, hχ, hχ₀, hχa, hχb, hχ₁, hχ'⟩ := exists_contDiff_step hab
  set DB := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B
  set G : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) := ↑e.symm
  set M₁ := familyDomainTrajectoryOperator ι AL₁ - DB
  set M₂ := familyDomainTrajectoryOperator ι AL₂ - DB
  set Mχ := mulGraph ι χ hχ hχ₀ hχ₁
  set Cχ := commL ι (deriv χ) (hχ.continuous_deriv (by simp)) hχ₁
  have hDG (f : Lp H 2 μ₀) : DB (G f) = f := by simp [DB, G, ← he]
  -- The glued operator is `D_{A₁} + (D_{A₂} - D_B)`.
  have hD₃ : familyDomainTrajectoryOperator ι (AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _) =
      familyDomainTrajectoryOperator ι AL₁ + M₂ := by
    rw [← sub_eq_iff_eq_add', familyDomainTrajectoryOperator_sub,
      show AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _ - AL₁ =
        AL₂ - (memLp_top_const (μ := μ₀) B).toLp _ by abel,
      ← familyDomainTrajectoryOperator_sub, familyDomainTrajectoryOperator_toLp_const]
  -- `A₁ - B` vanishes where `χ` does not, and `χ = 1` where `A₂ - B` does not vanish.
  have hM₁ (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) : M₁ (Mχ u) = 0 :=
    familyDomainTrajectoryOperator_sub_mulGraph_eq_zero h₁ hχ hχ₀ hχ₁ hχa u
  have hM₂ (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
      mulLp χ hχ.continuous hχ₀ (M₂ u) = M₂ u :=
    mulLp_familyDomainTrajectoryOperator_sub h₂ hχ.continuous hχ₀ hχb u
  -- The inverse `G` of `D_B` commutes with `χ` up to `G Cχ G`.
  have hG (f : Lp H 2 μ₀) : G (mulLp χ hχ.continuous hχ₀ f) = Mχ (G f) - G (Cχ (G f)) :=
    symm_mulLp_eq_mulGraph_symm_sub e he hχ hχ₀ hχ₁ f
  refine ⟨M₁.comp (G.comp (Cχ.comp (G.comp (M₂.comp G)))), ?_, ?_⟩
  · have hc (s : ℝ) (hs : s ∉ Ioo (-(|a| + |b|)) (|a| + |b|)) : deriv χ s = 0 :=
      hχ' s fun h ↦ hs ⟨by linarith [h.1, neg_abs_le a, abs_nonneg b],
        by linarith [h.2, le_abs_self b, abs_nonneg a]⟩
    exact (((isCompactOperator_commL hι (hχ.continuous_deriv (by simp)) hχ₁ hc).comp_clm
      (G.comp (M₂.comp G))).clm_comp G).clm_comp M₁
  -- Expand both sides through `D_{Aᵢ} = D_B + Mᵢ` and `D_B G = 1`.
  ext f : 1
  have hD₁ (v : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
      familyDomainTrajectoryOperator ι AL₁ v = DB v + M₁ v := by simp [M₁]
  have hD₂ (v : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
      familyDomainTrajectoryOperator ι AL₂ v = DB v + M₂ v := by simp [M₂]
  have hcross : M₁ (G (M₂ (G f))) = -M₁ (G (Cχ (G (M₂ (G f))))) := by
    have h := hG (M₂ (G f))
    rw [hM₂] at h
    rw [congrArg M₁ h, map_sub, hM₁, zero_sub]
  simp only [ContinuousLinearMap.comp_apply, add_apply, hD₃, hD₁, hD₂, hDG,
    map_add, hcross]
  abel

variable {B : D →L[ℝ] H} {AL₁ AL₂ : Lp (D →L[ℝ] H) ∞ μ₀} {a b : ℝ}

/-- **Gluing preserves the Fredholm property.** Let `ι` be compact and `D_B` invertible, and let
`A₁ = B` almost everywhere on `[a, ∞)` and `A₂ = B` almost everywhere on `(-∞, b]`, with `a < b`.
If `D_{A₁}` and `D_{A₂}` are Fredholm, then so is the operator `D_{A₃}` of the glued coefficient
`A₃ = A₁ + A₂ - B`, which is `A₁` on `(-∞, a]` and `A₂` on `[b, ∞)`. Here
`D_A u = (ι ∘ u)' + A u`. -/
theorem isFredholm_familyDomainTrajectoryOperator_add_sub (hι : IsCompactOperator ι)
    (hB : (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B).IsInvertible)
    (hab : a < b) (h₁ : ∀ᵐ s ∂μ₀, a ≤ s → AL₁ s = B) (h₂ : ∀ᵐ s ∂μ₀, s ≤ b → AL₂ s = B)
    (hF₁ : (familyDomainTrajectoryOperator (p := 2) ι AL₁).IsFredholm)
    (hF₂ : (familyDomainTrajectoryOperator (p := 2) ι AL₂).IsFredholm) :
    (familyDomainTrajectoryOperator (p := 2) ι
      (AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _)).IsFredholm := by
  obtain ⟨e, he⟩ := hB
  obtain ⟨K, hK, hEq⟩ :=
    exists_isCompactOperator_familyDomainTrajectoryOperator_add_sub_comp_eq hι e he hab h₁ h₂
  have hG : (e.symm : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)).IsFredholm :=
    ContinuousLinearMap.IsInvertible.isFredholm ⟨e.symm, rfl⟩
  have h₃ := ((hF₁.comp hG).comp (hF₂.comp hG)).add_of_isCompactOperator hK
  rw [← hEq] at h₃
  simpa using h₃.comp (ContinuousLinearMap.IsInvertible.isFredholm ⟨e, rfl⟩)

/-- **The index is additive under gluing.** Let `ι` be compact and `D_B` invertible, and let
`A₁ = B` almost everywhere on `[a, ∞)` and `A₂ = B` almost everywhere on `(-∞, b]`, with `a < b`.
If `D_{A₁}` and `D_{A₂}` are Fredholm, then the operator `D_{A₃}` of the glued coefficient
`A₃ = A₁ + A₂ - B`, which is `A₁` on `(-∞, a]` and `A₂` on `[b, ∞)`, has index
`ind D_{A₃} = ind D_{A₁} + ind D_{A₂}`. Here `D_A u = (ι ∘ u)' + A u`. -/
theorem index_familyDomainTrajectoryOperator_add_sub (hι : IsCompactOperator ι)
    (hB : (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι B).IsInvertible)
    (hab : a < b) (h₁ : ∀ᵐ s ∂μ₀, a ≤ s → AL₁ s = B) (h₂ : ∀ᵐ s ∂μ₀, s ≤ b → AL₂ s = B)
    (hF₁ : (familyDomainTrajectoryOperator (p := 2) ι AL₁).IsFredholm)
    (hF₂ : (familyDomainTrajectoryOperator (p := 2) ι AL₂).IsFredholm) :
    (familyDomainTrajectoryOperator (p := 2) ι
      (AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _)).index =
      (familyDomainTrajectoryOperator (p := 2) ι AL₁).index +
        (familyDomainTrajectoryOperator (p := 2) ι AL₂).index := by
  obtain ⟨e, he⟩ := hB
  obtain ⟨K, hK, hEq⟩ :=
    exists_isCompactOperator_familyDomainTrajectoryOperator_add_sub_comp_eq hι e he hab h₁ h₂
  set G : Lp H 2 μ₀ →L[ℝ] WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) := ↑e.symm
  have hG : G.IsFredholm := ContinuousLinearMap.IsInvertible.isFredholm ⟨e.symm, rfl⟩
  have hF := (hF₁.comp hG).comp (hF₂.comp hG)
  set D₃ := familyDomainTrajectoryOperator (p := 2) ι
    (AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B).toLp _)
  -- `D_{A₃} = (D_{A₃} G) e`, and composing with an isomorphism does not change the index.
  have hD₃ : D₃ = (D₃.comp G).comp (e : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ]
      Lp H 2 μ₀) := by
    ext u
    simp [G]
  rw [hD₃, ContinuousLinearMap.index_comp_equiv, hEq,
    ContinuousLinearMap.index_add_of_isCompactOperator hF hK,
    ContinuousLinearMap.index_comp (hF₁.comp hG) (hF₂.comp hG)]
  simp only [G, ContinuousLinearMap.index_comp_equiv]

omit [CompleteSpace H] [CompleteSpace D] in
/-- An `L∞` class of the interpolation `s ↦ (1 - φ s) • A s + φ s • A' s` of two coefficients by a
continuous function `φ` with `|φ| ≤ 1`. -/
private theorem exists_ae_eq_one_sub_smul_add_smul {A A' : ℝ → D →L[ℝ] H}
    {AL AL' : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) (hAL' : AL' =ᵐ[μ₀] A') {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφ₀ : ∀ s, |φ s| ≤ 1) :
    ∃ AL₁ : Lp (D →L[ℝ] H) ∞ μ₀, AL₁ =ᵐ[μ₀] fun s ↦ (1 - φ s) • A s + φ s • A' s := by
  have h₂ : ∃ C, ∀ s ∈ ((⊤ : Opens ℝ) : Set ℝ), ‖1 - φ s‖ ≤ C := ⟨2, fun s _ ↦ by
    rw [Real.norm_eq_abs]
    linarith [abs_sub (1 : ℝ) (φ s), abs_one (α := ℝ), hφ₀ s]⟩
  have h₁ : ∃ C, ∀ s ∈ ((⊤ : Opens ℝ) : Set ℝ), ‖φ s‖ ≤ C :=
    ⟨1, fun s _ ↦ (Real.norm_eq_abs _).trans_le (hφ₀ s)⟩
  refine ⟨Lp.multiplicationOperator (linftyOfContinuousOn volume
      (continuous_const.sub hφ).continuousOn (⊤ : Opens ℝ).isOpen.measurableSet h₂) AL +
    Lp.multiplicationOperator (linftyOfContinuousOn volume hφ.continuousOn
      (⊤ : Opens ℝ).isOpen.measurableSet h₁) AL', ?_⟩
  filter_upwards [Lp.coeFn_add (Lp.multiplicationOperator (linftyOfContinuousOn volume
      (continuous_const.sub hφ).continuousOn (⊤ : Opens ℝ).isOpen.measurableSet h₂) AL)
      (Lp.multiplicationOperator (linftyOfContinuousOn volume hφ.continuousOn
        (⊤ : Opens ℝ).isOpen.measurableSet h₁) AL'),
    Lp.multiplicationOperator_linftyOfContinuousOn_ae _ _ _ AL,
    Lp.multiplicationOperator_linftyOfContinuousOn_ae _ _ _ AL', hAL, hAL'] with s h h₃ h₄ h₅ h₆
  rw [h, Pi.add_apply, h₃, h₄, h₅, h₆]
  rfl

omit [CompleteSpace H] [CompleteSpace D] in
/-- **Cutting a family off to its limit at `+∞`.** A family `A` with limit `B₁` at `+∞`, differing
from `B₁` on bounded windows by operators bounded through `ι`, agrees with a family `A₁` on
`(-∞, 0]` such that `A₁ = B₁` on `[1, ∞)` and `A₁ - B₁` is still bounded through `ι` on bounded
windows. -/
private theorem exists_eq_of_le_zero_and_eq_of_one_le {B₁ : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H}
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B₁) x‖ ≤ c * ‖ι x‖) :
    ∃ (A₁ : ℝ → D →L[ℝ] H) (AL₁ : Lp (D →L[ℝ] H) ∞ μ₀), AL₁ =ᵐ[μ₀] A₁ ∧
      (∀ s, s ≤ 0 → A₁ s = A s) ∧ (∀ s, 1 ≤ s → A₁ s = B₁) ∧
      ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A₁ s - B₁) x‖ ≤ c * ‖ι x‖ := by
  obtain ⟨AL₁, hAL₁⟩ := exists_ae_eq_one_sub_smul_add_smul hAL
    (memLp_top_const (μ := μ₀) B₁).coeFn_toLp Real.smoothTransition.continuous
    Real.smoothTransition.abs_le_one
  refine ⟨_, AL₁, hAL₁, fun s hs ↦ by simp [Real.smoothTransition.zero_of_nonpos hs],
    fun s hs ↦ by simp [Real.smoothTransition.one_of_one_le hs], fun T ↦ ?_⟩
  obtain ⟨c, hc⟩ := hc T
  refine ⟨c, ?_⟩
  filter_upwards [hc] with s hs hsT x
  have : ((1 - Real.smoothTransition s) • A s + Real.smoothTransition s • B₁ - B₁) x =
      (1 - Real.smoothTransition s) • (A s - B₁) x := by
    simp only [sub_apply, add_apply, smul_apply]
    module
  rw [this, norm_smul, Real.norm_eq_abs]
  exact abs_mul_norm_le (Real.smoothTransition.abs_one_sub_le_one _)
    ((norm_nonneg _).trans (hs hsT x)) fun _ ↦ hs hsT x

omit [CompleteSpace H] [CompleteSpace D] in
/-- **Cutting a family off to its limit at `-∞`.** A family `A'` from `B₁` to `B₂`, differing from
`B₂` on bounded windows by operators bounded through `ι`, agrees with a family `A₂` on `[3, ∞)` such
that `A₂ = B₁` on `(-∞, 2]` and, if `B₁ - B₂` is bounded through `ι`, `A₂ - B₂` is still bounded
through `ι` on bounded windows. -/
private theorem exists_eq_of_le_two_and_eq_of_three_le {B₁ B₂ : D →L[ℝ] H}
    (h₁₂ : ∃ c, ∀ x, ‖(B₁ - B₂) x‖ ≤ c * ‖ι x‖) {A' : ℝ → D →L[ℝ] H}
    {AL' : Lp (D →L[ℝ] H) ∞ μ₀} (hAL' : AL' =ᵐ[μ₀] A')
    (hc' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A' s - B₂) x‖ ≤ c * ‖ι x‖) :
    ∃ (A₂ : ℝ → D →L[ℝ] H) (AL₂ : Lp (D →L[ℝ] H) ∞ μ₀), AL₂ =ᵐ[μ₀] A₂ ∧
      (∀ s, s ≤ 2 → A₂ s = B₁) ∧ (∀ s, 3 ≤ s → A₂ s = A' s) ∧
      ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A₂ s - B₂) x‖ ≤ c * ‖ι x‖ := by
  obtain ⟨AL₂, hAL₂⟩ := exists_ae_eq_one_sub_smul_add_smul
    (memLp_top_const (μ := μ₀) B₁).coeFn_toLp hAL' (φ := fun s ↦ Real.smoothTransition (s - 2))
    (by fun_prop) fun s ↦ Real.smoothTransition.abs_le_one _
  refine ⟨_, AL₂, hAL₂,
    fun s hs ↦ by simp [Real.smoothTransition.zero_of_nonpos (by linarith : s - 2 ≤ 0)],
    fun s hs ↦ by simp [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s - 2)],
    fun T ↦ ?_⟩
  obtain ⟨c₁₂, h₁₂⟩ := h₁₂
  obtain ⟨c, hc⟩ := hc' T
  refine ⟨c₁₂ + c, ?_⟩
  filter_upwards [hc] with s hs hsT x
  have : ((1 - Real.smoothTransition (s - 2)) • B₁ + Real.smoothTransition (s - 2) • A' s - B₂) x =
      (1 - Real.smoothTransition (s - 2)) • (B₁ - B₂) x +
        Real.smoothTransition (s - 2) • (A' s - B₂) x := by
    simp only [sub_apply, add_apply, smul_apply]
    module
  rw [this, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact abs_mul_norm_le (Real.smoothTransition.abs_one_sub_le_one _)
      ((norm_nonneg _).trans (h₁₂ x)) fun _ ↦ h₁₂ x
  · exact abs_mul_norm_le (Real.smoothTransition.abs_le_one _)
      ((norm_nonneg _).trans (hs hsT x)) fun _ ↦ hs hsT x

/-- **The index is additive under catenation.** Let `ι` be compact and let `B₀`, `B₁`, `B₂` be
invertible `ι`-symmetric operators, with `B₁ - B₂` bounded through `ι`. Let `A` run from `B₀` at
`-∞` to `B₁` at `∞`, and `A'` and `A''` from `B₁` and from `B₀` to `B₂`, each differing from its
limit at `∞` on every bounded interval by an operator bounded through `ι`, as in
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`. Then the Fredholm indices of
`D_A u = (ι ∘ u)' + A u` satisfy `ind D_{A''} = ind D_A + ind D_{A'}`. -/
theorem index_familyDomainTrajectoryOperator_eq_add (hι : IsCompactOperator ι)
    {B₀ B₁ B₂ : D →L[ℝ] H} (hSymm₀ : ∀ x y : D, ⟪B₀ x, ι y⟫_ℝ = ⟪ι x, B₀ y⟫_ℝ)
    (hB₀ : B₀.IsInvertible) (hSymm₁ : ∀ x y : D, ⟪B₁ x, ι y⟫_ℝ = ⟪ι x, B₁ y⟫_ℝ)
    (hB₁ : B₁.IsInvertible) (hSymm₂ : ∀ x y : D, ⟪B₂ x, ι y⟫_ℝ = ⟪ι x, B₂ y⟫_ℝ)
    (hB₂ : B₂.IsInvertible) (h₁₂ : ∃ c, ∀ x, ‖(B₁ - B₂) x‖ ≤ c * ‖ι x‖)
    {A A' A'' : ℝ → D →L[ℝ] H} {AL AL' AL'' : Lp (D →L[ℝ] H) ∞ μ₀}
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 B₀)) (htop : Tendsto A atTop (𝓝 B₁))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - B₁) x‖ ≤ c * ‖ι x‖)
    (hAL' : AL' =ᵐ[μ₀] A') (hbot' : Tendsto A' atBot (𝓝 B₁)) (htop' : Tendsto A' atTop (𝓝 B₂))
    (hc' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A' s - B₂) x‖ ≤ c * ‖ι x‖)
    (hAL'' : AL'' =ᵐ[μ₀] A'') (hbot'' : Tendsto A'' atBot (𝓝 B₀))
    (htop'' : Tendsto A'' atTop (𝓝 B₂))
    (hc'' : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A'' s - B₂) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL'').index =
      (familyDomainTrajectoryOperator (p := 2) ι AL).index +
        (familyDomainTrajectoryOperator (p := 2) ι AL').index := by
  -- Replace `A` by `A₁ = B₁` on `[1, ∞)` and `A'` by `A₂ = B₁` on `(-∞, 2]`, and glue them.
  obtain ⟨A₁, AL₁, hAL₁, hA₁l, hA₁r, hc₁⟩ := exists_eq_of_le_zero_and_eq_of_one_le hAL hc
  obtain ⟨A₂, AL₂, hAL₂, hA₂l, hA₂r, hc₂⟩ := exists_eq_of_le_two_and_eq_of_three_le h₁₂ hAL' hc'
  have hbot₁ : Tendsto A₁ atBot (𝓝 B₀) :=
    hbot.congr' ((eventually_le_atBot 0).mono fun s hs ↦ (hA₁l s hs).symm)
  have htop₁ : Tendsto A₁ atTop (𝓝 B₁) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun s hs ↦ (hA₁r s hs).symm)
  have hbot₂ : Tendsto A₂ atBot (𝓝 B₁) :=
    tendsto_const_nhds.congr' ((eventually_le_atBot 2).mono fun s hs ↦ (hA₂l s hs).symm)
  have htop₂ : Tendsto A₂ atTop (𝓝 B₂) :=
    htop'.congr' ((eventually_ge_atTop 3).mono fun s hs ↦ (hA₂r s hs).symm)
  -- The glued family `A₃ = A₁ + A₂ - B₁` runs from `B₀` to `B₂`.
  have hAL₃ : AL₁ + AL₂ - (memLp_top_const (μ := μ₀) B₁).toLp _ =ᵐ[μ₀]
      fun s ↦ A₁ s + A₂ s - B₁ := by
    filter_upwards [Lp.coeFn_sub (AL₁ + AL₂) ((memLp_top_const (μ := μ₀) B₁).toLp _),
      Lp.coeFn_add AL₁ AL₂, hAL₁, hAL₂, (memLp_top_const (μ := μ₀) B₁).coeFn_toLp]
      with s h h' h₁ h₂ h₃
    rw [h, Pi.sub_apply, h', Pi.add_apply, h₁, h₂, h₃]
  have hbot₃ : Tendsto (fun s ↦ A₁ s + A₂ s - B₁) atBot (𝓝 B₀) :=
    hbot.congr' ((eventually_le_atBot 0).mono fun s hs ↦ by
      beta_reduce
      rw [hA₁l s hs, hA₂l s (by linarith), add_sub_cancel_right])
  have htop₃ : Tendsto (fun s ↦ A₁ s + A₂ s - B₁) atTop (𝓝 B₂) :=
    htop'.congr' ((eventually_ge_atTop 3).mono fun s hs ↦ by
      beta_reduce
      rw [hA₁r s (by linarith), hA₂r s hs, add_sub_cancel_left])
  have hc₃ (T : ℝ) : ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T →
      ∀ x, ‖((A₁ s + A₂ s - B₁) - B₂) x‖ ≤ c * ‖ι x‖ := by
    obtain ⟨c₁, hc₁⟩ := hc₁ T
    obtain ⟨c₂, hc₂⟩ := hc₂ T
    refine ⟨c₁ + c₂, ?_⟩
    filter_upwards [hc₁, hc₂] with s hs₁ hs₂ hsT x
    rw [show (A₁ s + A₂ s - B₁ - B₂) x = (A₁ s - B₁) x + (A₂ s - B₂) x by
      simp only [sub_apply, add_apply]; abel, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hs₁ hsT x) (hs₂ hsT x))
  rw [index_familyDomainTrajectoryOperator_eq hι hSymm₀ hB₀ hSymm₂ hB₂ hAL'' hbot'' htop'' hc''
      hAL₃ hbot₃ htop₃ hc₃,
    index_familyDomainTrajectoryOperator_add_sub hι
      (isInvertible_domainTrajectoryOperator hSymm₁ hB₁) one_lt_two
      (hAL₁.mono fun s hs h ↦ hs.trans (hA₁r s h))
      (hAL₂.mono fun s hs h ↦ hs.trans (hA₂l s h))
      (isFredholm_familyDomainTrajectoryOperator hι hSymm₀ hB₀ hSymm₁ hB₁ hAL₁ hbot₁ htop₁ hc₁)
      (isFredholm_familyDomainTrajectoryOperator hι hSymm₁ hB₁ hSymm₂ hB₂ hAL₂ hbot₂ htop₂ hc₂),
    index_familyDomainTrajectoryOperator_eq hι hSymm₀ hB₀ hSymm₁ hB₁ hAL₁ hbot₁ htop₁ hc₁ hAL hbot
      htop hc,
    index_familyDomainTrajectoryOperator_eq hι hSymm₁ hB₁ hSymm₂ hB₂ hAL₂ hbot₂ htop₂ hc₂ hAL'
      hbot' htop' hc']

end TauCeti.WeakDerivStep
