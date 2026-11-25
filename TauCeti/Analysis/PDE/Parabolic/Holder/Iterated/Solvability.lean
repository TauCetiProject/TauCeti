/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Backward
import TauCeti.Analysis.Holder.Inclusion

/-!
# The initial-data and terminal-data isomorphisms at every order

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]` with `T > 0`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+α}`, `0 < α < 1`, with `a`
uniformly elliptic. This file proves that the initial-data map `u ↦ (P u, u(·, 0))` is an
isomorphism of Banach spaces

`C_{par,b}^{k+2+α}(ℝⁿ × [0, T]) ≃ C_{par,b}^{k+α}(ℝⁿ × [0, T]) × C_b^{k+2,α}(ℝⁿ)`

(`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`), and that the same holds for the
terminal-data map `u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, T))` of the backward operator
(`TauCeti.ParabolicCkHolderSpace.euclideanTerminalDataCLE`). No symmetry of `a`, no sign condition
on `c` and no compatibility condition between the data is needed on the whole space. Since the
initial-data operator is invertible, its inverse is continuous in operator norm as a function of
the coefficients at every such triple
(`TauCeti.ParabolicCkHolderSpace.continuousAt_inverse_initialDataL`).

## The argument

Reading a map of order `k + 2` at order two commutes with the operators
(`TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_parabolicOperatorL`,
`TauCeti.ParabolicCkHolderSpace.equivHolderSpace_euclideanParabolicOperatorL`), so uniqueness
follows from uniqueness in `C_b^{2+α,1+α/2}`. For existence, solve the problem in
`C_b^{2+α,1+α/2}` (`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`); by higher regularity
(`TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply`) the solution
has order `k + 2`. The open mapping theorem makes the inverse bounded. The terminal-value problem
reduces to the Cauchy problem by the time reversal `R (x, s) = (x, T - s)`: `u` solves
`P_back u = f`, `u(·, T) = g` exactly when `u ∘ R` solves `P_R v = -f ∘ R`, `v(·, 0) = g`, where
`P_R` has the reversed coefficients (`TauCeti.ParabolicCkHolderSpace.bijective_terminalDataL_iff`).
This follows the order-two terminal theory,
`TauCeti.ParabolicC2HolderSpace.euclideanTerminalDataCLE` with its reversal identity
`TauCeti.ParabolicC2HolderSpace.timeReverseLIE_euclideanTerminalDataCLE_symm_apply`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.initialDataL_euclidean_bijective` and
  `terminalDataL_euclidean_bijective`: existence and uniqueness.
* `TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE` and `euclideanTerminalDataCLE`: the
  isomorphisms, with the equation and the trace of their inverses.
* `TauCeti.ParabolicCkHolderSpace.coe_euclideanInitialDataCLE_symm_of_le` and
  `coe_euclideanTerminalDataCLE_symm_of_le`: the isomorphisms at different orders agree on the
  smaller spaces.
* `TauCeti.ParabolicCkHolderSpace.timeReverseLIE_euclideanTerminalDataCLE_symm_apply`: the terminal
  solution operator is the reversed initial solution operator.

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

/-! ### Consistency between orders -/

/-- Isomorphisms `e` of order `k` and `e'` of order `m ≤ k` onto forcing and trace data, with `e'`
of `u` read at order `m + 2` being `e u` read at order `m`, have inverses with the same values on
data with the same values. -/
private theorem coe_symm_eq_of_inclusionOfLEL {k m : ℕ} {α : ℝ≥0} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}
    {hab : a < b} (hα : α ≤ 1) (hm : m ≤ k)
    (e : ParabolicCkHolderSpace (k + 2) α E F hab ≃L[ℝ]
      ParabolicCkHolderSpace k α E F hab × CkHolderSpace (k + 2) α E F)
    (e' : ParabolicCkHolderSpace (m + 2) α E F hab ≃L[ℝ]
      ParabolicCkHolderSpace m α E F hab × CkHolderSpace (m + 2) α E F)
    (hfst : ∀ u, (e' (inclusionOfLEL hα (Nat.add_le_add_right hm 2) u)).1 =
      inclusionOfLEL hα hm (e u).1)
    (hsnd : ∀ u, ⇑(e' (inclusionOfLEL hα (Nat.add_le_add_right hm 2) u)).2 = ⇑(e u).2)
    {f : ParabolicCkHolderSpace k α E F hab} {g : CkHolderSpace (k + 2) α E F}
    {f' : ParabolicCkHolderSpace m α E F hab} {g' : CkHolderSpace (m + 2) α E F}
    (hf : ⇑f' = ⇑f) (hg : ⇑g' = ⇑g) :
    ⇑(e'.symm (f', g')) = ⇑(e.symm (f, g)) := by
  -- The order-`k` solution, read at order `m`, has the data `(f', g')`.
  have hdata : e' (inclusionOfLEL hα (Nat.add_le_add_right hm 2) (e.symm (f, g))) = (f', g') := by
    refine Prod.ext (ext fun p ↦ ?_) (CkHolderSpace.ext fun x ↦ ?_)
    · rw [hfst, e.apply_symm_apply, inclusionOfLEL_apply]
      exact (congrFun hf p).symm
    · rw [congrFun (hsnd _) x, e.apply_symm_apply]
      exact (congrFun hg x).symm
  rw [← hdata, ContinuousLinearEquiv.symm_apply_apply]
  exact funext fun p ↦ inclusionOfLEL_apply _ _ _ p

/-! ### The initial-data isomorphism -/

section Initial

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A coefficient of order `k`, read in `C_b^{α,α/2}`. -/
private def lower (hα : α ≤ 1) (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
  equivHolderSpace (inclusionOfLEL hα k.zero_le f)

omit [DecidableEq ι] in
/-- A map of order `k + 2`, read in `C_b^{2+α,1+α/2}`. -/
private def lowerTwo (hα : α ≤ 1) (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT :=
  equivParabolicC2HolderSpace (inclusionOfLEL hα (Nat.le_add_left 2 k) u)

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
  rw [lower, inclusionOfLEL_parabolicOperatorL, inclusionOfLEL_euclideanSecondOrderCoeff,
    inclusionOfLEL_euclideanFirstOrderCoeff, inclusionOfLEL_euclideanZerothOrderCoeff,
    equivHolderSpace_euclideanParabolicOperatorL]
  rfl

/-- Uniform ellipticity of coefficients of order `k` is that of their values in `C_b^{α,α/2}`. -/
private theorem lower_elliptic (hα : α ≤ 1)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ lower hα (a i j) p).toQuadraticForm' ξ := by
  simpa only [lower, equivHolderSpace_apply] using ellipticity_inclusionOfLEL hα k.zero_le ha

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
    simpa [ParabolicC2HolderSpace.spatialTrace_apply, lowerTwo] using DFunLike.congr_fun hg x
  exact ext fun p ↦ by simpa [lowerTwo] using congrArg (fun w ↦ w p) h

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
    ⟨w, funext fun p ↦ by simp [lower]⟩
  obtain ⟨V, hV⟩ := ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply
    (a := fun i j ↦ lower hα₁.le (a i j)) (b := fun i ↦ lower hα₁.le (b i))
    (c := lower hα₁.le c) (ha := lower_elliptic hα₁.le ha) hα₀ hα₁ k
    (fun i j ↦ hl (a i j)) (fun i ↦ hl (b i)) (hl c) (hl f) (g := g₂) ⟨g, hg₂.symm⟩
  have hVU : lowerTwo hα₁.le V = (ParabolicC2HolderSpace.euclideanInitialDataCLE hα₀ hα₁ hT
      (fun i j ↦ lower hα₁.le (a i j)) (fun i ↦ lower hα₁.le (b i)) (lower hα₁.le c)
      (lower_elliptic hα₁.le ha)).symm (lower hα₁.le f, g₂) :=
    ParabolicC2HolderSpace.ext fun p ↦ by simpa [lowerTwo] using congrFun hV p
  refine ⟨V, Prod.ext ?_ ?_⟩
  · refine ext fun p ↦ ?_
    have h := lower_parabolicOperatorL hα₁.le a b c V
    rw [hVU, ParabolicC2HolderSpace.euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply]
      at h
    simpa [lower] using congrArg (fun w ↦ w p) h
  · refine CkHolderSpace.ext fun x ↦ ?_
    have h := congrArg (fun w ↦ w (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)) hVU
    simp only [lowerTwo, equivParabolicC2HolderSpace_apply, inclusionOfLEL_apply,
      ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_apply_slabMk_zero] at h
    simpa [h] using congrFun hg₂ x

/-- **The Cauchy problem is well posed at every order.** For `0 < α < 1`, `T > 0` and coefficients
in `C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, every `(f, g)` in
`C_{par,b}^{k+α} × C_b^{k+2,α}` is the data `(P u, u(·, 0))` of exactly one `u` in
`C_{par,b}^{k+2+α}`. -/
theorem initialDataL_euclidean_bijective (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective (initialDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) :=
  ⟨initialDataL_euclidean_injective hα₀ hα₁ a b c ha,
    initialDataL_euclidean_surjective hα₀ hα₁ a b c ha⟩

/-- **The initial-data isomorphism of order `k`.** For `0 < α < 1`, `T > 0` and coefficients in
`C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, the map
`u ↦ (∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u, u(·, 0))` as an isomorphism of Banach spaces from
`C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`. -/
def euclideanInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
        CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := initialDataL_euclidean_bijective hα₀ hα₁ a b c ha
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

/-- As a continuous linear map, the initial-data isomorphism is the initial-data operator. -/
@[simp]
theorem coe_euclideanInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    (euclideanInitialDataCLE hα₀ hα₁ a b c ha : _ →L[ℝ] _) = initialDataL hα₁.le
      (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) :=
  ContinuousLinearMap.ext (euclideanInitialDataCLE_apply hα₀ hα₁ a b c ha)

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
        (ellipticity_inclusionOfLEL hα₁.le hm ha)).symm (f', g')) =
      ⇑((euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm (f, g)) := by
  refine coe_symm_eq_of_inclusionOfLEL hα₁.le hm _ _ (fun u ↦ ?_) (fun u ↦ ?_) hf hg <;>
    rw [euclideanInitialDataCLE_apply, euclideanInitialDataCLE_apply,
      ← inclusionOfLEL_euclideanSecondOrderCoeff, ← inclusionOfLEL_euclideanFirstOrderCoeff,
      ← inclusionOfLEL_euclideanZerothOrderCoeff]
  exacts [initialDataL_inclusionOfLEL_fst _ _ _ _ _ _,
    coe_initialDataL_inclusionOfLEL_snd _ _ _ _ _ _]

end Initial

/-! ### The terminal-data isomorphism

This follows the order-two terminal theory:
`TauCeti.ParabolicC2HolderSpace.euclideanTerminalDataCLE` and its reversal identity
`TauCeti.ParabolicC2HolderSpace.timeReverseLIE_euclideanTerminalDataCLE_symm_apply`. -/

section Terminal

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} [DecidableEq ι]

/-- **The terminal-value problem is well posed at every order.** For `0 < α < 1`, `T > 0` and
coefficients in `C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, every `(f, g)` in
`C_{par,b}^{k+α} × C_b^{k+2,α}` is the data `(P_back u, u(·, T))` of exactly one `u` in
`C_{par,b}^{k+2+α}`. -/
theorem terminalDataL_euclidean_bijective (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective (terminalDataL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)) := by
  rw [bijective_terminalDataL_iff (T := T) (ha := (sub_self (T : ℝ)).symm)
    (hb := (sub_zero (T : ℝ)).symm), timeReverseLIE_euclideanSecondOrderCoeff,
    timeReverseLIE_euclideanFirstOrderCoeff, timeReverseLIE_euclideanZerothOrderCoeff]
  exact initialDataL_euclidean_bijective hα₀ hα₁ _ _ _ (ellipticity_timeReverseLIE ha)

/-- **The terminal-data isomorphism of order `k`.** For `0 < α < 1`, `T > 0` and coefficients in
`C_{par,b}^{k+α}(ℝⁿ × [0, T])` with `a` uniformly elliptic, the map
`u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, T))` as an isomorphism of Banach spaces from
`C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.euclideanTerminalDataCLE`. -/
def euclideanTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
        CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := terminalDataL_euclidean_bijective hα₀ hα₁ a b c ha
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

/-- As a continuous linear map, the terminal-data isomorphism is the terminal-data operator. -/
@[simp]
theorem coe_euclideanTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    (euclideanTerminalDataCLE hα₀ hα₁ a b c ha : _ →L[ℝ] _) = terminalDataL hα₁.le
      (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) :=
  ContinuousLinearMap.ext (euclideanTerminalDataCLE_apply hα₀ hα₁ a b c ha)

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

/-- **The terminal-value problem is a reversed Cauchy problem.** With `R (x, s) = (x, T - s)`, the
time reversal `u ∘ R` of the solution `u` of `P_back u = f`, `u(·, T) = g` is the solution of the
Cauchy problem `P_R v = -f ∘ R`, `v(·, 0) = g` for the forward operator `P_R` with the reversed
coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`. -/
theorem timeReverseLIE_euclideanTerminalDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm
        ((euclideanTerminalDataCLE hα₀ hα₁ a b c ha).symm d) =
      (euclideanInitialDataCLE hα₀ hα₁
        (fun i j ↦ timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm (a i j))
        (fun i ↦ timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm (b i))
        (timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm c)
        (ellipticity_timeReverseLIE ha)).symm
        (-timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm d.1, d.2) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanInitialDataCLE_apply,
    ← timeReverseLIE_euclideanSecondOrderCoeff, ← timeReverseLIE_euclideanFirstOrderCoeff,
    ← timeReverseLIE_euclideanZerothOrderCoeff, initialDataL_timeReverseLIE,
    ← euclideanTerminalDataCLE_apply hα₀ hα₁ a b c ha, ContinuousLinearEquiv.apply_symm_apply]

/-- **Consistency between orders.** For `m ≤ k`, the solution of the terminal-value problem at
order `k` with data `(f, g)` has the same values as the solution at order `m` with the
coefficients read at order `m` and data `(f', g')` having the values of `(f, g)`. -/
theorem coe_euclideanTerminalDataCLE_symm_of_le (hα₀ : 0 < α) (hα₁ : α < 1) {m : ℕ} (hm : m ≤ k)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    {g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ}
    {f' : ParabolicCkHolderSpace m α (EuclideanSpace ℝ ι) ℝ hT}
    {g' : CkHolderSpace (m + 2) α (EuclideanSpace ℝ ι) ℝ} (hf : ⇑f' = ⇑f) (hg : ⇑g' = ⇑g) :
    ⇑((euclideanTerminalDataCLE hα₀ hα₁ (fun i j ↦ inclusionOfLEL hα₁.le hm (a i j))
        (fun i ↦ inclusionOfLEL hα₁.le hm (b i)) (inclusionOfLEL hα₁.le hm c)
        (ellipticity_inclusionOfLEL hα₁.le hm ha)).symm (f', g')) =
      ⇑((euclideanTerminalDataCLE hα₀ hα₁ a b c ha).symm (f, g)) := by
  refine coe_symm_eq_of_inclusionOfLEL hα₁.le hm _ _ (fun u ↦ ?_) (fun u ↦ ?_) hf hg <;>
    rw [euclideanTerminalDataCLE_apply, euclideanTerminalDataCLE_apply,
      ← inclusionOfLEL_euclideanSecondOrderCoeff, ← inclusionOfLEL_euclideanFirstOrderCoeff,
      ← inclusionOfLEL_euclideanZerothOrderCoeff]
  exacts [terminalDataL_inclusionOfLEL_fst _ _ _ _ _ _,
    coe_terminalDataL_inclusionOfLEL_snd _ _ _ _ _ _]

end Terminal

end ParabolicCkHolderSpace

end TauCeti
