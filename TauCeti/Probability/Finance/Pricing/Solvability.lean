/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
import TauCeti.Analysis.PDE.Parabolic.Holder.Line

/-!
# Solvability of the pricing equation in weighted log-spot parabolic Hölder spaces

Let `a = σ² / 2` and let `r` be the short rate on a closed time slab `ℝ × [t₀, t₁]`, `t₀ < t₁`.
In weighted log-spot coordinates `u(y, t) = C(e^y, t) / (1 + e^y)`, the backward pricing operator

`P u = ∂ₜu + a ∂ᵧ²u + (r + a (2 sigmoid y - 1)) ∂ᵧu - r (1 - sigmoid y) u`

acts as a bounded linear map `weightedLogSpotPricingOperatorL` from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])`
to `C_b^{α,α/2}(ℝ × [t₀, t₁])` for `α ≤ 1` and general bounded parabolic Hölder slab fields
`a, r`. When `a` is uniformly bounded away from zero (`δ ≤ a` with `0 < δ`) and `0 < α < 1`, this
file proves that the terminal-data map `u ↦ (P u, u(·, t₁))` is an isomorphism of Banach spaces
onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. When in addition `‖a‖ ≤ K`, `‖r‖ ≤ K` for a
common coefficient norm bound `K` and `t₁ - t₀ ≤ T₀` for a horizon bound `T₀`, the solution
operator admits uniform Schauder bounds and Lipschitz dependence on `(a, r)` in operator norm.

Evaluating the inverse at `(0, g)` solves the weighted terminal-value problem `P u = 0`,
`u(·, t₁) = g`. The specialization to market spot-coordinate data (`a = σ² / 2` in log-spot
coordinates and a time-only Hölder short rate `r`) and the resulting classical pricing PDE existence
and uniqueness theorems live in `TauCeti.Probability.Finance.Pricing.Existence`.

## Main declarations

All financial declarations are in the `TauCeti.Finance` namespace.

* `isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL` and
  `weightedLogSpotTerminalDataCLE`: the Banach-space isomorphism `u ↦ (P u, u(·, t₁))`, with
  `weightedLogSpotTerminalDataCLE_apply`,
  `weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply`,
  `spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply`,
  `weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right`, and
  `abs_weightedLogSpotTerminalDataCLE_symm_apply_le`.
* `exists_norm_weightedLogSpotTerminalDataCLE_symm_le` and
  `exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le`: uniform Schauder bound and Lipschitz
  dependence on `(a, r)` under the common coefficient bound `‖a‖ ≤ K`, `‖r‖ ≤ K` and horizon
  bound `t₁ - t₀ ≤ T₀`.

## References

* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 2,
  Section 4 and Chapter 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

open Real Set Filter Topology ContinuousLinearMap
open scoped NNReal ENNReal
open TauCeti.ParabolicSpaceTime TauCeti.ParabolicC2HolderSpace

namespace TauCeti.Finance

-- These shortcuts keep instance search shallow for nested line coefficient spaces.
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance

/-! ### The weighted log-spot terminal-data isomorphism -/

section TerminalDataCLE

/-- **The weighted terminal-value problem is well posed.** For `0 < α < 1`, `t₀ < t₁`, and
bounded parabolic Hölder coefficients `a, r ∈ C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a ≥ lam > 0`, the
terminal-data map `u ↦ (P u, u(·, t₁))` of the weighted log-spot pricing operator `P` is an
isomorphism of Banach spaces from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. -/
theorem isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL {α : ℝ≥0} {t₀ t₁ : ℝ}
    {ht : t₀ < t₁} (hα₀ : 0 < α) (hα₁ : α < 1)
    {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p, lam ≤ a p) :
    ((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)).IsInvertible := by
  rw [weightedLogSpotPricingOperatorL_def]
  exact isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real hα₀ hα₁ ht _ _ hlam
    fun p ↦ (realSecondOrderCoeff_apply_mul a p).symm ▸ ha p

/-- **The weighted log-spot terminal-data isomorphism.** For `0 < α < 1`, `t₀ < t₁`, and parabolic
Hölder coefficients `a, r` on `ℝ × [t₀, t₁]` where `a` has a uniform positive lower bound
`a ≥ δ > 0`, the map `u ↦ (P u, u(·, t₁))` of `weightedLogSpotPricingOperatorL` as an isomorphism
of Banach spaces from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def weightedLogSpotTerminalDataCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ δ : ℝ, 0 < δ ∧ ∀ p, δ ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  realTerminalDataCLE hα₀ hα₁ ht
    (realSecondOrderCoeff a)
    (weightedLogSpotFirstOrderCoeff hα₁.le a r)
    (weightedLogSpotZerothOrderCoeff hα₁.le r)
    (ha.imp fun _ ⟨hδ, h⟩ ↦ ⟨hδ, fun p ↦ (realSecondOrderCoeff_apply_mul a p).symm ▸ h p⟩)

section WeightedCLEProps

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
  {ha : ∃ δ : ℝ, 0 < δ ∧ ∀ p, δ ≤ a p}

/-- The weighted log-spot terminal-data isomorphism sends `u` to its backward pricing residual
`P u` and its terminal trace `u(·, t₁)`. -/
@[simp]
theorem weightedLogSpotTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  dsimp only [weightedLogSpotTerminalDataCLE]
  rw [weightedLogSpotPricingOperatorL_def]
  exact realTerminalDataCLE_apply u

/-- The solution of the weighted log-spot terminal-value problem with forcing `f` and terminal
datum `g` has backward pricing residual `f`. -/
@[simp]
theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  dsimp only [weightedLogSpotTerminalDataCLE]
  rw [weightedLogSpotPricingOperatorL_def]
  exact backwardParabolicOperatorL_realTerminalDataCLE_symm_apply d

/-- The solution of the weighted log-spot terminal-value problem with forcing `f` and terminal
datum `g` has terminal trace `g`. -/
@[simp]
theorem spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  dsimp only [weightedLogSpotTerminalDataCLE]
  exact spatialTrace_realTerminalDataCLE_symm_apply d

/-- The solution of the weighted log-spot terminal-value problem with terminal datum `g` takes the
value `g y` at `(y, t₁)`. -/
@[simp]
theorem weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (y : ℝ) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d
      (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 y := by
  rw [← spatialTrace_apply, spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

/-- **Pointwise exponential bound for the weighted log-spot solution operator.** If `r ≥ -γ` with
`0 ≤ γ`, `|f| ≤ K` and `|g| ≤ M`, then the solution `u` of `P u = f`, `u(·, t₁) = g` satisfies
`|u(y, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. For a nonnegative short rate, `γ = 0`. -/
theorem abs_weightedLogSpotTerminalDataCLE_symm_apply_le {γ M K : ℝ}
    (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ)
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ)
    (hd₁ : ∀ p, |d.1 p| ≤ K) (hd₂ : ∀ y, |d.2 y| ≤ M) (p : slab (E := ℝ) t₀ t₁) :
    |(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d p| ≤
      Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  obtain ⟨δ, hδ, ha'⟩ := ha
  refine abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le
    (fun q ↦ hδ.le.trans (ha' q)) hr hγ _ ?_ ?_ p
  · intro q
    rw [weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]
    exact hd₁ q
  · intro y
    rw [weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]
    exact hd₂ y

end WeightedCLEProps

private def weightedCoeffBound {α : ℝ≥0} (hα : α ≤ 1) (K : ℝ≥0) : ℝ≥0 :=
  K + K + 2 * K * ‖logOneAddExpGrad hα‖₊ + K * (1 + ‖logOneAddExpGrad hα‖₊)

private theorem norm_weightedCoeffs_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1) {K : ℝ≥0}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (hak : ‖a‖ ≤ K) (hrk : ‖r‖ ≤ K) :
    ‖realSecondOrderCoeff a‖ ≤ (weightedCoeffBound hα K : ℝ) ∧
      ‖weightedLogSpotFirstOrderCoeff hα a r‖ ≤ (weightedCoeffBound hα K : ℝ) ∧
      ‖weightedLogSpotZerothOrderCoeff hα r‖ ≤ (weightedCoeffBound hα K : ℝ) := by
  set L : ℝ := ‖logOneAddExpGrad hα‖
  have hK : (weightedCoeffBound hα K : ℝ) = K + K + 2 * K * L + K * (1 + L) := by
    simp [weightedCoeffBound, L]
  have h2 : ‖realSecondOrderCoeff a‖ ≤ (weightedCoeffBound hα K : ℝ) := by
    refine (norm_realSecondOrderCoeff_le a).trans (hak.trans ?_)
    rw [hK]
    have hL : 0 ≤ L := norm_nonneg _
    nlinarith [K.coe_nonneg]
  have h1 : ‖weightedLogSpotFirstOrderCoeff hα a r‖ ≤ (weightedCoeffBound hα K : ℝ) := by
    refine (norm_weightedLogSpotFirstOrderCoeff_le hα a r).trans ?_
    rw [hK]
    have hL : 0 ≤ L := norm_nonneg _
    nlinarith [K.coe_nonneg]
  have h0 : ‖weightedLogSpotZerothOrderCoeff hα r‖ ≤ (weightedCoeffBound hα K : ℝ) := by
    refine (norm_weightedLogSpotZerothOrderCoeff_le hα r).trans ?_
    rw [hK]
    have hL : 0 ≤ L := norm_nonneg _
    nlinarith [K.coe_nonneg]
  exact ⟨h2, h1, h0⟩

/-- **Uniform Schauder estimate for the weighted log-spot terminal-value problem.** For `0 < α < 1`,
`0 < δ`, a coefficient bound `K` and a horizon bound `T₀`, the solution operators of the weighted
log-spot terminal-value problems on `ℝ × [t₀, t₁]` with `t₁ - t₀ ≤ T₀`, `δ ≤ a`, `‖a‖ ≤ K` and
`‖r‖ ≤ K` are uniformly bounded in operator norm. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_le {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, δ ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_realTerminalDataCLE_symm_le (α := α) hα₀ hα₁ hδ
    (weightedCoeffBound hα₁.le K) T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ a r ha hak hrk ↦ ?_⟩
  obtain ⟨h2, h1, h0⟩ := norm_weightedCoeffs_le hα₁.le hak hrk
  exact hest ht hTT₀ (realSecondOrderCoeff a)
    (weightedLogSpotFirstOrderCoeff hα₁.le a r) (weightedLogSpotZerothOrderCoeff hα₁.le r)
    (fun p ↦ (realSecondOrderCoeff_apply_mul a p).symm ▸ ha p) h2 h1 h0

/-- **Lipschitz dependence of the weighted log-spot solution operator on `(a, r)`.** Under the
bounds of `exists_norm_weightedLogSpotTerminalDataCLE_symm_le`, the solution operators for `(a, r)`
and `(a', r')` differ in operator norm by at most `C (‖a - a'‖ + ‖r - r'‖)`. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
        (ha : ∀ p, δ ≤ a p) (ha' : ∀ p, δ ≤ a' p),
        ‖a‖ ≤ K → ‖r‖ ≤ K → ‖a'‖ ≤ K → ‖r'‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap -
          (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r'
            ⟨δ, hδ, ha'⟩).symm.toContinuousLinearMap‖ ≤ C * (‖a - a'‖ + ‖r - r'‖) := by
  let L : ℝ := ‖logOneAddExpGrad hα₁.le‖
  obtain ⟨C, hC, hest⟩ := exists_norm_realTerminalDataCLE_symm_sub_le (α := α) hα₀ hα₁ hδ
    (weightedCoeffBound hα₁.le K) T₀
  refine ⟨C * (2 + 2 * L), by positivity,
    fun {t₀ t₁} ht hTT₀ a a' r r' ha ha' hak hrk hak' hrk' ↦ ?_⟩
  obtain ⟨h2, h1, h0⟩ := norm_weightedCoeffs_le hα₁.le hak hrk
  obtain ⟨h2', h1', h0'⟩ := norm_weightedCoeffs_le hα₁.le hak' hrk'
  have hmid := hest ht hTT₀
    (realSecondOrderCoeff a) (realSecondOrderCoeff a')
    (weightedLogSpotFirstOrderCoeff hα₁.le a r) (weightedLogSpotFirstOrderCoeff hα₁.le a' r')
    (weightedLogSpotZerothOrderCoeff hα₁.le r) (weightedLogSpotZerothOrderCoeff hα₁.le r')
    (fun p ↦ (realSecondOrderCoeff_apply_mul a p).symm ▸ ha p)
    (fun p ↦ (realSecondOrderCoeff_apply_mul a' p).symm ▸ ha' p)
    h2 h1 h0 h2' h1' h0'
  have hd2 : ‖realSecondOrderCoeff a - realSecondOrderCoeff a'‖ ≤ ‖a - a'‖ := by
    rw [← realSecondOrderCoeff_sub]
    exact norm_realSecondOrderCoeff_le (a - a')
  have hd1 : ‖weightedLogSpotFirstOrderCoeff hα₁.le a r -
        weightedLogSpotFirstOrderCoeff hα₁.le a' r'‖ ≤
      ‖r - r'‖ + ‖a - a'‖ + 2 * ‖a - a'‖ * L := by
    rw [← weightedLogSpotFirstOrderCoeff_sub]
    exact norm_weightedLogSpotFirstOrderCoeff_le hα₁.le (a - a') (r - r')
  have hd0 : ‖weightedLogSpotZerothOrderCoeff hα₁.le r -
        weightedLogSpotZerothOrderCoeff hα₁.le r'‖ ≤
      ‖r - r'‖ * (1 + L) := by
    rw [← weightedLogSpotZerothOrderCoeff_sub]
    exact norm_weightedLogSpotZerothOrderCoeff_le hα₁.le (r - r')
  have hsum :
      ‖realSecondOrderCoeff a - realSecondOrderCoeff a'‖ +
          ‖weightedLogSpotFirstOrderCoeff hα₁.le a r -
            weightedLogSpotFirstOrderCoeff hα₁.le a' r'‖ +
          ‖weightedLogSpotZerothOrderCoeff hα₁.le r -
            weightedLogSpotZerothOrderCoeff hα₁.le r'‖ ≤
        (2 + 2 * L) * (‖a - a'‖ + ‖r - r'‖) := by
    have hL : 0 ≤ L := norm_nonneg _
    nlinarith [norm_nonneg (a - a'), norm_nonneg (r - r')]
  refine le_of_eq_of_le ?_ ((hmid.trans (mul_le_mul_of_nonneg_left hsum hC)).trans_eq (by ring))
  dsimp only [weightedLogSpotTerminalDataCLE]

end TerminalDataCLE

end TauCeti.Finance
