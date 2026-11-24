/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Backward
public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Analysis.Holder.Inclusion

/-!
# The initial-data and terminal-data isomorphisms at every order

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+α}`, `0 < α < 1`, with `a`
uniformly elliptic. This file proves that the initial-data map `u ↦ (P u, u(·, 0))` is an
isomorphism of Banach spaces

`C_{par,b}^{k+2+α}(ℝⁿ × [0, T]) ≃ C_{par,b}^{k+α}(ℝⁿ × [0, T]) × C_b^{k+2,α}(ℝⁿ)`

(`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`), and that the same holds for the
terminal-data map `u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, T))` of the backward operator
(`TauCeti.ParabolicCkHolderSpace.euclideanTerminalDataCLE`). No symmetry of `a`, no sign condition
on `c` and no compatibility condition between the data is needed on the whole space. The solution
operator depends continuously on the coefficients in operator norm
(`TauCeti.ParabolicCkHolderSpace.continuousAt_inverse_initialDataL`).

## The argument

Reading a map of order `k + 2` at order two commutes with the operators
(`TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_parabolicOperatorL`), so uniqueness follows from
uniqueness in `C_b^{2+α,1+α/2}`. For existence, solve the problem in `C_b^{2+α,1+α/2}`
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`); by higher regularity
(`TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply`) the solution
has order `k + 2`. The open mapping theorem makes the inverse bounded. The terminal-value problem
reduces to the Cauchy problem by the time reversal `R (x, s) = (x, T - s)`: `u` solves
`P_back u = f`, `u(·, T) = g` exactly when `u ∘ R` solves `P_R v = -f ∘ R`, `v(·, 0) = g`, where
`P_R` has the reversed coefficients.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.bijective_initialDataL_euclidean` and
  `bijective_terminalDataL_euclidean`: existence and uniqueness.
* `TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE` and `euclideanTerminalDataCLE`: the
  isomorphisms, with the equation and the trace of their inverses.
* `TauCeti.ParabolicCkHolderSpace.coe_euclideanInitialDataCLE_symm_of_le`: the isomorphisms at
  different orders agree on the smaller spaces.
* `TauCeti.ParabolicCkHolderSpace.continuousAt_inverse_initialDataL`: continuity of the solution
  operator in the coefficients.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal

namespace ParabolicCkHolderSpace

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

variable {ι : Type*} [Fintype ι]

/-! ### The initial-data isomorphism -/

section Initial

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A coefficient of order `k`, read in `C_b^{α,α/2}`. -/
private def lower (hα : α ≤ 1) (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
  equivHolderSpace (inclusionOfLEL hα k.zero_le f)

omit [DecidableEq ι] in
private theorem lower_apply (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) : lower hα f p = f p := by
  rw [lower, equivHolderSpace_apply, inclusionOfLEL_apply]

omit [DecidableEq ι] in
/-- A map of order `k + 2`, read in `C_b^{2+α,1+α/2}`. -/
private def lowerTwo (hα : α ≤ 1) (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT :=
  equivParabolicC2HolderSpace (inclusionOfLEL hα (Nat.le_add_left 2 k) u)

omit [DecidableEq ι] in
private theorem lowerTwo_apply (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) : lowerTwo hα u p = u p := by
  rw [lowerTwo, equivParabolicC2HolderSpace_apply, inclusionOfLEL_apply]

/-- Reading the Euclidean operator of order `k` in `C_b^{α,α/2}` gives the operator of order two
with the coefficients read in `C_b^{α,α/2}`. -/
private theorem lower_parabolicOperatorL (hα : α ≤ 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    lower hα (parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
        (euclideanZerothOrderCoeff c) u) =
      ParabolicC2HolderSpace.euclideanParabolicOperatorL hα (fun i j ↦ lower hα (a i j))
        (fun i ↦ lower hα (b i)) (lower hα c) (lowerTwo hα u) := by
  rw [lower, inclusionOfLEL_parabolicOperatorL, equivHolderSpace_parabolicOperatorL,
    ParabolicC2HolderSpace.euclideanParabolicOperatorL_def]
  have hA : equivHolderSpace (inclusionOfLEL hα k.zero_le (euclideanSecondOrderCoeff a)) =
      ParabolicC2HolderSpace.euclideanSecondOrderCoeff fun i j ↦ lower hα (a i j) :=
    HolderSpace.ext fun p ↦ ContinuousLinearMap.ext fun H ↦ by
      simp [equivHolderSpace_apply, inclusionOfLEL_apply, lower_apply]
  have hB : equivHolderSpace (inclusionOfLEL hα k.zero_le (euclideanFirstOrderCoeff b)) =
      ParabolicC2HolderSpace.euclideanFirstOrderCoeff fun i ↦ lower hα (b i) :=
    HolderSpace.ext fun p ↦ ContinuousLinearMap.ext fun v ↦ by
      simp [equivHolderSpace_apply, inclusionOfLEL_apply, lower_apply]
  have hC : equivHolderSpace (inclusionOfLEL hα k.zero_le (euclideanZerothOrderCoeff c)) =
      ParabolicC2HolderSpace.euclideanZerothOrderCoeff (lower hα c) :=
    HolderSpace.ext fun p ↦ ContinuousLinearMap.ext fun y ↦ by
      simp [equivHolderSpace_apply, inclusionOfLEL_apply, lower_apply]
  rw [hA, hB, hC, lowerTwo]

/-- Uniform ellipticity of coefficients of order `k` is that of their values in `C_b^{α,α/2}`. -/
private theorem lower_elliptic (hα : α ≤ 1)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ lower hα (a i j) p).toQuadraticForm' ξ := by
  simpa only [lower_apply] using ha

/-- Uniqueness for the Cauchy problem in `C_{par,b}^{k+2+α}`. -/
private theorem initialDataL_euclidean_injective (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Injective (initialDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) := by
  intro u v huv
  have hP := congrArg Prod.fst huv
  have hg := congrArg Prod.snd huv
  simp only [initialDataL_fst, initialDataL_snd] at hP hg
  have h : lowerTwo hα₁.le u = lowerTwo hα₁.le v := by
    refine (ParabolicC2HolderSpace.euclideanInitialDataCLE hα₀ hα₁ hT
      (fun i j ↦ lower hα₁.le (a i j)) (fun i ↦ lower hα₁.le (b i)) (lower hα₁.le c)
      (lower_elliptic hα₁.le ha)).injective ?_
    rw [ParabolicC2HolderSpace.euclideanInitialDataCLE_apply,
      ParabolicC2HolderSpace.euclideanInitialDataCLE_apply, ← lower_parabolicOperatorL,
      ← lower_parabolicOperatorL, hP]
    refine Prod.ext rfl (CkHolderSpace.ext fun x ↦ ?_)
    simpa [ParabolicC2HolderSpace.spatialTrace_apply, lowerTwo_apply] using
      DFunLike.congr_fun hg x
  exact ext fun p ↦ by rw [← lowerTwo_apply hα₁.le u p, h, lowerTwo_apply]

/-- Existence for the Cauchy problem in `C_{par,b}^{k+2+α}`: the solution in `C_b^{2+α,1+α/2}` has
order `k + 2` by higher regularity. -/
private theorem initialDataL_euclidean_surjective (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Surjective (initialDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) := by
  rintro ⟨f, g⟩
  obtain ⟨g₂, hg₂⟩ := CkHolderSpace.exists_coe_eq_of_le hα₁.le (Nat.le_add_left 2 k) g
  have hl (w : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT) :
      ∃ W : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑W = ⇑(lower hα₁.le w) :=
    ⟨w, funext fun p ↦ (lower_apply hα₁.le w p).symm⟩
  obtain ⟨V, hV⟩ := ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply
    (a := fun i j ↦ lower hα₁.le (a i j)) (b := fun i ↦ lower hα₁.le (b i))
    (c := lower hα₁.le c) (ha := lower_elliptic hα₁.le ha) hα₀ hα₁ k
    (fun i j ↦ hl (a i j)) (fun i ↦ hl (b i)) (hl c) (hl f) (g := g₂) ⟨g, hg₂.symm⟩
  have hVU : lowerTwo hα₁.le V = (ParabolicC2HolderSpace.euclideanInitialDataCLE hα₀ hα₁ hT
      (fun i j ↦ lower hα₁.le (a i j)) (fun i ↦ lower hα₁.le (b i)) (lower hα₁.le c)
      (lower_elliptic hα₁.le ha)).symm (lower hα₁.le f, g₂) :=
    ParabolicC2HolderSpace.ext fun p ↦ by rw [lowerTwo_apply, hV]
  refine ⟨V, Prod.ext ?_ ?_⟩
  · refine ext fun p ↦ ?_
    have h := lower_parabolicOperatorL hα₁.le a b c V
    rw [hVU, ParabolicC2HolderSpace.euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply]
      at h
    simpa [lower_apply] using congrArg (fun w ↦ w p) h
  · refine CkHolderSpace.ext fun x ↦ ?_
    simp only [initialDataL_snd, spatialTrace_apply]
    rw [← lowerTwo_apply hα₁.le V, hVU,
      ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_apply_slabMk_zero]
    exact congrFun hg₂ x

/-- **The Cauchy problem is well posed at every order.** For `0 < α < 1` and coefficients in
`C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, every `(f, g)` in
`C_{par,b}^{k+α} × C_b^{k+2,α}` is the data `(P u, u(·, 0))` of exactly one `u` in
`C_{par,b}^{k+2+α}`. -/
theorem bijective_initialDataL_euclidean (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective (initialDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) :=
  ⟨initialDataL_euclidean_injective hα₀ hα₁ a b c ha,
    initialDataL_euclidean_surjective hα₀ hα₁ a b c ha⟩

/-- **The initial-data isomorphism of order `k`.** For `0 < α < 1` and coefficients in
`C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, the map
`u ↦ (∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u, u(·, 0))` as an isomorphism of Banach spaces from
`C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`. -/
def euclideanInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
        CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := bijective_initialDataL_euclidean hα₀ hα₁ a b c ha
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

/-- The initial-data isomorphism is the initial-data operator. -/
@[simp]
theorem euclideanInitialDataCLE_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanInitialDataCLE hα₀ hα₁ a b c ha u = initialDataL hα₁.le
      (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u :=
  by simp [euclideanInitialDataCLE]

/-- The solution of the Cauchy problem with data `(f, g)` has forcing `f`. -/
@[simp]
theorem parabolicOperatorL_euclideanInitialDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
      (euclideanZerothOrderCoeff c) ((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm d) = d.1 := by
  have h := (euclideanInitialDataCLE hα₀ hα₁ a b c ha).apply_symm_apply d
  rw [euclideanInitialDataCLE_apply] at h
  simpa using congrArg Prod.fst h

/-- The solution of the Cauchy problem with data `(f, g)` has initial trace `g`. -/
@[simp]
theorem spatialTrace_euclideanInitialDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm d).spatialTrace
      ⟨0, left_mem_Icc.2 hT.le⟩ = d.2 := by
  have h := (euclideanInitialDataCLE hα₀ hα₁ a b c ha).apply_symm_apply d
  rw [euclideanInitialDataCLE_apply] at h
  simpa using congrArg Prod.snd h

/-- **Consistency between orders.** For `m ≤ k`, the solution at order `k` with data `(f, g)` has
the same values as the solution at order `m` with the coefficients read at order `m` and data
`(f', g')` having the values of `(f, g)`: the order-`k` isomorphism is the restriction of the
order-`m` one to the smaller spaces. -/
theorem coe_euclideanInitialDataCLE_symm_of_le (hα₀ : 0 < α) (hα₁ : α < 1) {m : ℕ} (hm : m ≤ k)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    {g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ}
    {f' : ParabolicCkHolderSpace m α (EuclideanSpace ℝ ι) ℝ hT}
    {g' : CkHolderSpace (m + 2) α (EuclideanSpace ℝ ι) ℝ} (hf : ⇑f' = ⇑f) (hg : ⇑g' = ⇑g) :
    ⇑((euclideanInitialDataCLE hα₀ hα₁ (fun i j ↦ inclusionOfLEL hα₁.le hm (a i j))
        (fun i ↦ inclusionOfLEL hα₁.le hm (b i)) (inclusionOfLEL hα₁.le hm c)
        (by simpa only [inclusionOfLEL_apply] using ha)).symm (f', g')) =
      ⇑((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm (f, g)) := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm (f, g)
  have hA : inclusionOfLEL hα₁.le hm (euclideanSecondOrderCoeff a) =
      euclideanSecondOrderCoeff fun i j ↦ inclusionOfLEL hα₁.le hm (a i j) :=
    ext fun p ↦ ContinuousLinearMap.ext fun H ↦ by simp [inclusionOfLEL_apply]
  have hB : inclusionOfLEL hα₁.le hm (euclideanFirstOrderCoeff b) =
      euclideanFirstOrderCoeff fun i ↦ inclusionOfLEL hα₁.le hm (b i) :=
    ext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp [inclusionOfLEL_apply]
  have hC : inclusionOfLEL hα₁.le hm (euclideanZerothOrderCoeff c) =
      euclideanZerothOrderCoeff (inclusionOfLEL hα₁.le hm c) :=
    ext fun p ↦ ContinuousLinearMap.ext fun y ↦ by simp [inclusionOfLEL_apply]
  have hP := parabolicOperatorL_euclideanInitialDataCLE_symm_apply hα₀ hα₁ a b c ha (f, g)
  have htr := spatialTrace_euclideanInitialDataCLE_symm_apply hα₀ hα₁ a b c ha (f, g)
  have hdata : euclideanInitialDataCLE hα₀ hα₁ (fun i j ↦ inclusionOfLEL hα₁.le hm (a i j))
      (fun i ↦ inclusionOfLEL hα₁.le hm (b i)) (inclusionOfLEL hα₁.le hm c)
      (by simpa only [inclusionOfLEL_apply] using ha)
      (inclusionOfLEL hα₁.le (Nat.add_le_add_right hm 2) u) = (f', g') := by
    rw [euclideanInitialDataCLE_apply]
    refine Prod.ext ?_ (CkHolderSpace.ext fun x ↦ ?_)
    · rw [initialDataL_fst, ← hA, ← hB, ← hC, ← inclusionOfLEL_parabolicOperatorL, hP]
      exact ext fun p ↦ by rw [inclusionOfLEL_apply]; exact (congrFun hf p).symm
    · rw [initialDataL_snd, spatialTrace_apply, inclusionOfLEL_apply, ← spatialTrace_apply, htr]
      exact (congrFun hg x).symm
  rw [← hdata, ContinuousLinearEquiv.symm_apply_apply]
  exact funext fun p ↦ inclusionOfLEL_apply _ _ _ p

end Initial

/-! ### Dependence on the coefficients -/

section Continuity

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {a b : ℝ} {hab : a < b}

/-- **The solution operator depends continuously on the coefficients.** If the initial-data
operator with coefficients `(A, B, C)` is invertible, its inverse is continuous in operator norm
as a function of the coefficients at `(A, B, C)`. -/
theorem continuousAt_inverse_initialDataL (hα : α ≤ 1)
    {A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab}
    {B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab}
    {C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab}
    (h : (initialDataL hα A B C).IsInvertible) :
    ContinuousAt (fun abc : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab ↦
      (initialDataL hα abc.1 abc.2.1 abc.2.2).inverse) (A, B, C) := by
  have hL : Continuous fun abc : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab ×
      ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab ×
      ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab ↦ initialDataL hα abc.1 abc.2.1 abc.2.2 := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ norm_initialDataL_sub_le hα) ?_
    have hc : Continuous fun y : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab ×
        ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab ↦
        21 * ((k : ℝ) + 1) ^ 2 * 2 ^ k * (‖y.1 - x.1‖ + 8 * ((k : ℝ) + 1) ^ 2 * ‖y.2.1 - x.2.1‖ +
          64 * ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2 * ‖y.2.2 - x.2.2‖) := by
      fun_prop
    simpa using hc.tendsto x
  exact ContinuousAt.comp (g := ContinuousLinearMap.inverse)
    (h.contDiffAt_map_inverse (n := 0)).continuousAt hL.continuousAt

end Continuity

/-! ### The terminal-data isomorphism -/

section Terminal

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} [DecidableEq ι]

/-- Time reversal `u ↦ u ∘ R`, `R (x, s) = (x, T - s)`, on the slab `ℝⁿ × [0, T]`. -/
private abbrev rev {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) G hT ≃ₗᵢ[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) G hT :=
  timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm

omit [DecidableEq ι] in
/-- The time reversal of `u` has as initial trace the terminal trace of `u`. -/
private theorem spatialTrace_rev (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    (rev u).spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ =
      u.spatialTrace ⟨T, right_mem_Icc.2 hT.le⟩ := by
  refine CkHolderSpace.ext fun x ↦ ?_
  simp only [spatialTrace_apply, timeReverseLIE_apply, slabTimeReverse_slabMk]
  congr 2
  ext
  simp

/-- The data of the reversed forward problem are the reversed data of the backward problem. -/
private theorem initialDataL_rev (hα : α ≤ 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    initialDataL hα (euclideanSecondOrderCoeff fun i j ↦ rev (a i j))
        (euclideanFirstOrderCoeff fun i ↦ rev (b i)) (euclideanZerothOrderCoeff (rev c)) (rev u) =
      (-rev (backwardParabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u),
        u.spatialTrace ⟨T, right_mem_Icc.2 hT.le⟩) := by
  have hA : euclideanSecondOrderCoeff (fun i j ↦ rev (a i j)) =
      rev (euclideanSecondOrderCoeff a) :=
    ext fun p ↦ ContinuousLinearMap.ext fun H ↦ by simp
  have hB : euclideanFirstOrderCoeff (fun i ↦ rev (b i)) = rev (euclideanFirstOrderCoeff b) :=
    ext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp
  have hC : euclideanZerothOrderCoeff (rev c) = rev (euclideanZerothOrderCoeff c) :=
    ext fun p ↦ ContinuousLinearMap.ext fun y ↦ by simp
  rw [hA, hB, hC]
  refine Prod.ext ?_ ?_
  · rw [initialDataL_fst]
    exact parabolicOperatorL_timeReverseLIE hα _ _ _ u
  · rw [initialDataL_snd]
    exact spatialTrace_rev u

/-- **The terminal-value problem is well posed at every order.** For `0 < α < 1` and coefficients
in `C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, every `(f, g)` in
`C_{par,b}^{k+α} × C_b^{k+2,α}` is the data `(P_back u, u(·, T))` of exactly one `u` in
`C_{par,b}^{k+2+α}`. -/
theorem bijective_terminalDataL_euclidean (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective (terminalDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) := by
  have hR := bijective_initialDataL_euclidean hα₀ hα₁ (fun i j ↦ rev (a i j))
    (fun i ↦ rev (b i)) (rev c) (ha.imp fun lam h ↦ ⟨h.1, fun p ξ ↦ by
      simpa only [timeReverseLIE_apply] using h.2 _ ξ⟩)
  refine ⟨fun u v huv ↦ rev.injective (hR.1 ?_), fun d ↦ ?_⟩
  · have h₁ := congrArg Prod.fst huv
    have h₂ := congrArg Prod.snd huv
    simp only [terminalDataL_fst, terminalDataL_snd] at h₁ h₂
    rw [initialDataL_rev, initialDataL_rev, h₁, h₂]
  · obtain ⟨w, hw⟩ := hR.2 (-rev d.1, d.2)
    refine ⟨rev.symm w, ?_⟩
    have h := initialDataL_rev hα₁.le a b c (rev.symm w)
    rw [LinearIsometryEquiv.apply_symm_apply, hw] at h
    refine Prod.ext (rev.injective (neg_injective ?_)) ?_
    · simpa using (congrArg Prod.fst h).symm
    · simpa using (congrArg Prod.snd h).symm

/-- **The terminal-data isomorphism of order `k`.** For `0 < α < 1` and coefficients in
`C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, the map
`u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, T))` as an isomorphism of Banach spaces from
`C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`. -/
def euclideanTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
        CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := bijective_terminalDataL_euclidean hα₀ hα₁ a b c ha
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

/-- The terminal-data isomorphism is the terminal-data operator. -/
@[simp]
theorem euclideanTerminalDataCLE_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanTerminalDataCLE hα₀ hα₁ a b c ha u = terminalDataL hα₁.le
      (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u :=
  by simp [euclideanTerminalDataCLE]

/-- The solution of the terminal-value problem with data `(f, g)` has forcing `f`. -/
@[simp]
theorem backwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    backwardParabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
      (euclideanZerothOrderCoeff c) ((euclideanTerminalDataCLE hα₀ hα₁ a b c ha).symm d) = d.1 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  simpa using congrArg Prod.fst h

/-- The solution of the terminal-value problem with data `(f, g)` has terminal trace `g`. -/
@[simp]
theorem spatialTrace_euclideanTerminalDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanTerminalDataCLE hα₀ hα₁ a b c ha).symm d).spatialTrace
      ⟨T, right_mem_Icc.2 hT.le⟩ = d.2 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  simpa using congrArg Prod.snd h

end Terminal

end ParabolicCkHolderSpace

end TauCeti
