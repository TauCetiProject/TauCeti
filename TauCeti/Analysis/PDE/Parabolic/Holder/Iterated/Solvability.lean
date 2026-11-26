/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Backward
import TauCeti.Analysis.Holder.Inclusion
import TauCeti.Analysis.Normed.Operator.ContinuousLinearEquiv
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.DifferentiatedEquation

/-!
# The initial-data and terminal-data isomorphisms at every order, with their estimates

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

The inverses are bounded uniformly in the coefficients: for an ellipticity constant `λ > 0`, a bound
`K` on the norms of the coefficients in `C_{par,b}^{k+α}` and a bound `T₀` on the horizon, there is
a constant `C` with

`‖u‖_{k+2+α} ≤ C (‖P u‖_{k+α} + ‖u(·, 0)‖_{C^{k+2,α}})`

for every `u ∈ C_{par,b}^{k+2+α}(ℝⁿ × [0, T])` and all such coefficients and `T ≤ T₀`
(`TauCeti.ParabolicCkHolderSpace.exists_norm_le_parabolicOperatorL`). This is the Schauder estimate
at every order; at order zero it is
`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`.

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

The estimate is proved by induction on the order, as the a priori estimate for maps already in the
higher space. For the step from `k` to `k + 1`, each directional derivative `∂ₑu` in a coordinate
direction solves the differentiated equation
`P (∂ₑu) = ∂ₑ(P u) + (∂ₑaⁱʲ) ∂ᵢ∂ⱼu + (∂ₑbⁱ) ∂ᵢu + (∂ₑc) u`
(`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_spatialLineDerivL`), by the product rule and
the commutation of derivatives.
Its coefficients are those of `P` read at order `k`, and its forcing has order `k` and is bounded by
`‖P u‖` and the norm of `u` at order `k + 2`. The estimate at order `k` bounds that norm, and then
`∂ₑu`. The equation `∂ₜu = P u + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` bounds the time derivative at order
`k + 1`, and a map is bounded by its values, its spatial gradient and its time derivative
(`TauCeti.ParabolicCkHolderSpace.norm_ofSpatialFDerivTimeDeriv_le`). The uniform bounds on the
solution operators follow, for the terminal-value problem by time reversal, which preserves the
norms of the coefficients and of the data.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.initialDataL_euclidean_bijective` and
  `terminalDataL_euclidean_bijective`: existence and uniqueness.
* `TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE` and `euclideanTerminalDataCLE`: the
  isomorphisms, with the equation and the trace of their inverses.
* `TauCeti.ParabolicCkHolderSpace.coe_euclideanInitialDataCLE_symm_of_le` and
  `coe_euclideanTerminalDataCLE_symm_of_le`: the isomorphisms at different orders agree on the
  smaller spaces.
* `TauCeti.ParabolicCkHolderSpace.exists_norm_le_parabolicOperatorL`: the Schauder estimate at
  every order, uniform in the coefficients.
* `TauCeti.ParabolicCkHolderSpace.exists_norm_euclideanInitialDataCLE_symm_le` and
  `exists_norm_euclideanTerminalDataCLE_symm_le`: the solution operators are bounded uniformly in
  the coefficients and the horizon.
* `TauCeti.ParabolicCkHolderSpace.exists_norm_euclideanInitialDataCLE_symm_sub_le` and
  `exists_norm_euclideanTerminalDataCLE_symm_sub_le`: the solution operators depend Lipschitz
  continuously on the coefficients, in operator norm.
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

/-! ### The Schauder estimate at every order

The argument is the induction on the order described in the module docstring. -/

section Estimate

variable [DecidableEq ι] {α : ℝ≥0}

omit [DecidableEq ι] in
/-- Products of scalar coefficients of order `j` with scalar fields of order `j`, summed as in a
second-order operator, with the product bound. -/
private theorem exists_eq_sum_mul_and_norm_le (hα : α ≤ 1) {j : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (A H : ι → ι → ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT)
    (B G : ι → ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT)
    (C V : ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT) :
    ∃ Z : ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT,
      (∀ p, Z p = ∑ i, ∑ l, A i l p * H i l p + ∑ i, B i p * G i p + C p * V p) ∧
      ‖Z‖ ≤ 21 * (j + 1) ^ 2 * 2 ^ j *
        (∑ i, ∑ l, ‖A i l‖ * ‖H i l‖ + ∑ i, ‖B i‖ * ‖G i‖ + ‖C‖ * ‖V‖) := by
  set mulL := (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ (k := j)
    (E := EuclideanSpace ℝ ι) (hab := hT) hα
  set c : ℝ := 21 * (j + 1) ^ 2 * 2 ^ j
  have hmul (X Y : ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT) :
      ‖mulL X Y‖ ≤ c * (‖X‖ * ‖Y‖) :=
    ContinuousLinearMap.norm_mul_compParabolicCkHolder₂_apply_le hα X Y
  refine ⟨∑ i, ∑ l, mulL (A i l) (H i l) + ∑ i, mulL (B i) (G i) + mulL C V,
    fun p ↦ by simp [mulL, Finset.sum_apply], ?_⟩
  have h₁ : ‖∑ i, ∑ l, mulL (A i l) (H i l)‖ ≤ c * ∑ i, ∑ l, ‖A i l‖ * ‖H i l‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ hmul _ _)
  have h₂ : ‖∑ i, mulL (B i) (G i)‖ ≤ c * ∑ i, ‖B i‖ * ‖G i‖ := by
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hmul _ _)
  have h₃ := hmul C V
  refine (norm_add₃_le).trans ?_
  rw [mul_add, mul_add]
  linarith

omit [DecidableEq ι] in
/-- Reading a map of order `k + 1` at order `k` costs at most `8 (k + 1)²`. -/
private theorem norm_inclusionOfLEL_succ_le (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (f : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT) :
    ‖inclusionOfLEL hα k.le_succ f‖ ≤ 8 * (k + 1) ^ 2 * ‖f‖ := by
  have h := norm_inclusionOfLEL_le (E := EuclideanSpace ℝ ι) (F := ℝ) (hab := hT) hα k.le_succ
  rw [show k.succ - k = 1 by omega, pow_one] at h
  push_cast at h
  exact ContinuousLinearMap.le_of_opNorm_le _ h f

omit [DecidableEq ι] in
/-- The inclusion of consecutive orders, applied to a scalar map on `ℝⁿ`. -/
private theorem norm_inclusionL_apply_le (hα : α ≤ 1) {m : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (f : ParabolicCkHolderSpace (m + 1) α (EuclideanSpace ℝ ι) ℝ hT) :
    ‖inclusionL hα f‖ ≤ 8 * (m + 1) ^ 2 * ‖f‖ :=
  ContinuousLinearMap.le_of_opNorm_le _ (norm_inclusionL_le_mul_sq hα) _

/-- A directional derivative in a coordinate direction does not increase the norm. -/
private theorem norm_spatialLineDerivL_single_apply_le {m : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (f : ParabolicCkHolderSpace (m + 1) α (EuclideanSpace ℝ ι) ℝ hT) (i : ι) :
    ‖spatialLineDerivL (EuclideanSpace.single i (1 : ℝ)) f‖ ≤ ‖f‖ :=
  (norm_spatialLineDerivL_apply_le _ _).trans (by simp)

omit [DecidableEq ι] in
/-- The initial traces of a map of order `k + 3`, read at order `k + 2`. -/
private theorem norm_spatialTrace_inclusionOfLEL_le (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (t : Icc (0 : ℝ) T) :
    ‖(inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u).spatialTrace t‖ ≤
      (k + 6) * ‖u.spatialTrace t‖ := by
  have h : (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u).spatialTrace t =
      CkHolderSpace.inclusionSuccL hα (u.spatialTrace t) :=
    CkHolderSpace.ext fun x ↦ by simp
  rw [h]
  refine (ContinuousLinearMap.le_of_opNorm_le _ (CkHolderSpace.norm_inclusionSuccL_le hα) _).trans
    (le_of_eq ?_)
  push_cast
  ring

section Gradient

/- The spatial gradient below is assembled in the order-`k` space of covectors with Mathlib's
instances, as `TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv` expects: with the shortcut
instances of the coefficient fields, the kernel would have to unfold the norm structures of
operator spaces to identify the two. -/
attribute [-instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

/-- The spatial gradient of `u` as a field with Mathlib's instances, with its norm bounded by the
directional derivatives in the coordinate directions. -/
private theorem exists_eq_spatialFDerivL_and_norm_le {m : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (u : ParabolicCkHolderSpace (m + 1) α (EuclideanSpace ℝ ι) ℝ hT) :
    ∃ G : ParabolicCkHolderSpace m α (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι →L[ℝ] ℝ) hT,
      (∀ p, G p = spatialFDerivL m α (EuclideanSpace ℝ ι) ℝ hT u p) ∧
        ‖G‖ ≤ ∑ l, ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ :=
  ⟨_, fun _ ↦ rfl, norm_spatialFDerivL_apply_le_sum u⟩

omit [DecidableEq ι] in
/-- A map of order `k + 3` is controlled by its values, a field with the values of its spatial
gradient and a field with the values of its time derivative, of orders `k + 2` and `k + 1`. -/
private theorem norm_le_of_eq_spatialFDerivL_of_eq_timeDerivL (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    {G : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι →L[ℝ] ℝ) hT}
    {H : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT}
    (hG : ∀ p, G p = spatialFDerivL (k + 2) α (EuclideanSpace ℝ ι) ℝ hT u p)
    (hH : ∀ p, H p = timeDerivL (k + 1) α (EuclideanSpace ℝ ι) ℝ hT u p) :
    ‖u‖ ≤ 4 * (k + 4) ^ 2 *
      (‖inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u‖ + ‖G‖ + ‖H‖) := by
  set v := inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u
  have hval : ⇑(valueL v) = ⇑u := funext fun p ↦ by simp [v]
  have hu : u = ofSpatialFDerivTimeDeriv (k := k + 1) (valueL v) G H
      (fun t x ↦ by rw [hval, hG]; exact u.hasSpatialFDerivAt t x)
      (fun x t ↦ by rw [hval, hH]; exact u.hasTimeDerivWithinAt x t) :=
    ext fun p ↦ by rw [ofSpatialFDerivTimeDeriv_apply, hval]
  calc ‖u‖ = ‖ofSpatialFDerivTimeDeriv (k := k + 1) (valueL v) G H _ _‖ := congrArg _ hu
    _ ≤ 4 * ((k + 1 : ℕ) + 3) ^ 2 * (‖valueL v‖ + ‖G‖ + ‖H‖) :=
      norm_ofSpatialFDerivTimeDeriv_le ..
    _ = 4 * (k + 4) ^ 2 * (‖valueL v‖ + ‖G‖ + ‖H‖) := by push_cast; ring
    _ ≤ 4 * (k + 4) ^ 2 * (‖v‖ + ‖G‖ + ‖H‖) := by grw [norm_valueL_le v]

end Gradient

variable (ι) in
/-- The Schauder estimate at order `k`, uniform over coefficients with a fixed ellipticity
constant and a fixed bound on their norms, and over horizons below a fixed bound. -/
private def SchauderBound (α : ℝ≥0) (hα₁ : α < 1) (lam : ℝ) (k : ℕ) : Prop :=
  ∀ K T₀ : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
    ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
      (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
      (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
        ‖u‖ ≤ C * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
          (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ +
          ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖)

/-- The Schauder estimate at order zero is the global Schauder estimate on `C_b^{2+α,1+α/2}`. -/
private theorem schauderBound_zero (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) :
    SchauderBound ι α hα₁ lam 0 := by
  intro K T₀
  obtain ⟨C, hC, hest⟩ :=
    ParabolicC2HolderSpace.exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨2 * C, by positivity, fun T hT hTT₀ a b c ha hak hbk hck u ↦ ?_⟩
  have ha₂ : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ (equivHolderSpace (a i j) :) p).toQuadraticForm' ξ := by
    simpa only [equivHolderSpace_apply] using ha
  set e := ParabolicC2HolderSpace.euclideanInitialDataCLE hα₀ hα₁ hT
    (fun i j ↦ (equivHolderSpace (a i j) :)) (fun i ↦ (equivHolderSpace (b i) :))
    (equivHolderSpace c :) ⟨lam, hlam, ha₂⟩
  have hb := hest T hT hTT₀ _ _ _ ha₂ (fun i j ↦ (norm_equivHolderSpace_le _).trans (hak i j))
    (fun i ↦ (norm_equivHolderSpace_le _).trans (hbk i)) ((norm_equivHolderSpace_le _).trans hck)
  set u₂ := equivParabolicC2HolderSpace u
  have h₁ : ‖u₂‖ ≤ C * ‖e u₂‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e u₂)
    rw [show e.symm.toContinuousLinearMap (e u₂) = u₂ from e.symm_apply_apply u₂] at h
    exact h.trans (by gcongr)
  have hP : ParabolicC2HolderSpace.euclideanParabolicOperatorL hα₁.le
      (fun i j ↦ (equivHolderSpace (a i j) :)) (fun i ↦ (equivHolderSpace (b i) :))
      (equivHolderSpace c :) u₂ = equivHolderSpace (parabolicOperatorL hα₁.le
        (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c)
        u) :=
    (equivHolderSpace_euclideanParabolicOperatorL hα₁.le a b c u).symm
  have htr : u₂.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ :=
    CkHolderSpace.ext fun x ↦ by
      simp [u₂, ParabolicC2HolderSpace.spatialTrace_apply]
  have h₂ : ‖e u₂‖ ≤ ‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
      (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ +
      ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ := by
    rw [ParabolicC2HolderSpace.euclideanInitialDataCLE_apply, Prod.norm_def, hP, htr]
    exact max_le (le_add_of_le_of_nonneg (norm_equivHolderSpace_le _) (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  have h₀ := norm_le_two_mul_norm_equivParabolicC2HolderSpace u
  have h₃ := mul_le_mul_of_nonneg_left h₂ hC
  nlinarith

/-- By the equation, the time derivative of `u` is the forcing plus the spatial part of the
operator, a field of order `k + 1` bounded through the directional derivatives of `u`. -/
private theorem exists_eq_timeDerivL_and_norm_le (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    ∃ H : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT,
      (∀ p, H p = timeDerivL (k + 1) α (EuclideanSpace ℝ ι) ℝ hT u p) ∧
      ‖H‖ ≤ ‖parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
          (euclideanZerothOrderCoeff c) u‖ + 21 * (k + 2) ^ 2 * 2 ^ (k + 1) *
        (∑ i, ∑ l, ‖a i l‖ * ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ +
          ∑ i, ‖b i‖ * (8 * (k + 2) ^ 2 * ‖spatialLineDerivL (EuclideanSpace.single i (1 : ℝ)) u‖) +
          ‖c‖ * (8 * (k + 2) ^ 2 * ‖inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u‖)) := by
  set v := inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u
  obtain ⟨Y, hY, hYn⟩ := exists_eq_sum_mul_and_norm_le hα (j := k + 1) a
    (fun i l ↦ spatialLineDerivL (EuclideanSpace.single i 1)
      (spatialLineDerivL (EuclideanSpace.single l 1) u)) b
    (fun i ↦ inclusionL hα (spatialLineDerivL (EuclideanSpace.single i 1) u)) c (inclusionL hα v)
  refine ⟨parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u + Y, fun p ↦ ?_, ?_⟩
  · rw [coe_add, Pi.add_apply, hY]
    simp [v, spatialFDerivBCF_apply, ← Matrix.vec_single_eq_const]
  · push_cast at hYn
    rw [show (k : ℝ) + 1 + 1 = k + 2 by ring] at hYn
    refine (norm_add_le _ _).trans (add_le_add le_rfl (hYn.trans ?_))
    have h₃ := norm_inclusionL_apply_le hα (m := k + 1) v
    have h₄ (i : ι) := norm_inclusionL_apply_le hα (m := k + 1)
      (spatialLineDerivL (EuclideanSpace.single i (1 : ℝ)) u)
    push_cast at h₃ h₄
    rw [show (k : ℝ) + 1 + 1 = k + 2 by ring] at h₃ h₄
    gcongr
    exacts [norm_spatialLineDerivL_single_apply_le _ _, h₄ _]

/-- The lower-order part `(∂ₑaⁱʲ) ∂ᵢ∂ⱼv + (∂ₑbⁱ) ∂ᵢv + (∂ₑc) v` of the forcing of the
differentiated equation `parabolicOperatorL_spatialLineDerivL`, along a coordinate direction `e`,
is bounded at order `k` by the norm of `v` at order `k + 2`. -/
private theorem norm_spatialOperatorL_spatialLineDerivL_le (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} {K : ℝ}
    (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (hak : ∀ i j, ‖a i j‖ ≤ K) (hbk : ∀ i, ‖b i‖ ≤ K) (hck : ‖c‖ ≤ K)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) (l : ι) :
    ‖spatialOperatorL hα
        (euclideanSecondOrderCoeff fun i j ↦ spatialLineDerivL (EuclideanSpace.single l 1) (a i j))
        (euclideanFirstOrderCoeff fun i ↦ spatialLineDerivL (EuclideanSpace.single l 1) (b i))
        (euclideanZerothOrderCoeff (spatialLineDerivL (EuclideanSpace.single l 1) c)) v‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * (Fintype.card ι * Fintype.card ι * K +
        Fintype.card ι * K * (8 * (k + 1) ^ 2) + K * (8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2))) *
          ‖v‖ := by
  set e := EuclideanSpace.single l (1 : ℝ)
  obtain ⟨Z, hZ, hZn⟩ := exists_eq_sum_mul_and_norm_le hα (j := k)
    (fun i j ↦ spatialLineDerivL e (a i j))
    (fun i j ↦ spatialLineDerivL (EuclideanSpace.single i 1)
      (spatialLineDerivL (EuclideanSpace.single j 1) v))
    (fun i ↦ spatialLineDerivL e (b i))
    (fun i ↦ inclusionL hα (spatialLineDerivL (EuclideanSpace.single i 1) v))
    (spatialLineDerivL e c) (inclusionL hα (inclusionL hα v))
  have hZe : spatialOperatorL hα (euclideanSecondOrderCoeff fun i j ↦ spatialLineDerivL e (a i j))
      (euclideanFirstOrderCoeff fun i ↦ spatialLineDerivL e (b i))
      (euclideanZerothOrderCoeff (spatialLineDerivL e c)) v = Z :=
    ext fun p ↦ by
      rw [spatialOperatorL_apply, hZ]
      simp [spatialFDerivBCF_apply, ← Matrix.vec_single_eq_const]
  rw [hZe]
  refine hZn.trans ?_
  have hK : 0 ≤ K := (norm_nonneg _).trans hck
  have hs₁ : ∑ i, ∑ j, ‖spatialLineDerivL e (a i j)‖ * ‖spatialLineDerivL
      (EuclideanSpace.single i 1) (spatialLineDerivL (EuclideanSpace.single j 1) v)‖ ≤
      ∑ _i : ι, ∑ _j : ι, K * ‖v‖ :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ mul_le_mul
      ((norm_spatialLineDerivL_single_apply_le _ l).trans (hak i j))
      ((norm_spatialLineDerivL_single_apply_le _ i).trans
        (norm_spatialLineDerivL_single_apply_le v j)) (norm_nonneg _) hK
  have hs₂ : ∑ i, ‖spatialLineDerivL e (b i)‖ *
      ‖inclusionL hα (spatialLineDerivL (EuclideanSpace.single i 1) v)‖ ≤
      ∑ _i : ι, K * (8 * (k + 1) ^ 2 * ‖v‖) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul
      ((norm_spatialLineDerivL_single_apply_le _ l).trans (hbk i))
      ((norm_inclusionL_apply_le hα _).trans (by
        gcongr; exact norm_spatialLineDerivL_single_apply_le v i)) (norm_nonneg _) hK
  have hs₃ : ‖spatialLineDerivL e c‖ * ‖inclusionL hα (inclusionL hα v)‖ ≤
      K * (8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2) * ‖v‖) := by
    refine mul_le_mul ((norm_spatialLineDerivL_single_apply_le _ l).trans hck)
      ((norm_inclusionL_apply_le hα _).trans ?_) (norm_nonneg _) hK
    have := norm_inclusionL_apply_le hα (m := k + 1) v
    push_cast at this
    calc 8 * ((k : ℝ) + 1) ^ 2 * ‖inclusionL hα v‖
        ≤ 8 * (k + 1) ^ 2 * (8 * (k + 1 + 1) ^ 2 * ‖v‖) := by gcongr
      _ = 8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2) * ‖v‖ := by ring
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs₁ hs₂
  calc _ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * (Fintype.card ι * (Fintype.card ι * (K * ‖v‖)) +
        Fintype.card ι * (K * (8 * (k + 1) ^ 2 * ‖v‖)) +
        K * (8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2) * ‖v‖)) := by gcongr
    _ = _ := by ring

/-- **The induction step for one direction.** If the order-`k` estimate holds with constant `C₁`
for the coefficients read at order `k`, then each directional derivative `∂ₑu`, which solves the
differentiated equation, is bounded by the data of `u` and the norm of `u` at order `k + 2`. -/
private theorem norm_spatialLineDerivL_single_le (hα₁ : α < 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} {C₁ K : ℝ}
    (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (hak : ∀ i j, ‖a i j‖ ≤ K) (hbk : ∀ i, ‖b i‖ ≤ K) (hck : ‖c‖ ≤ K)
    (est : ∀ v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ‖v‖ ≤ C₁ * (‖parabolicOperatorL hα₁.le
        (euclideanSecondOrderCoeff fun i j ↦ inclusionOfLEL hα₁.le k.le_succ (a i j))
        (euclideanFirstOrderCoeff fun i ↦ inclusionOfLEL hα₁.le k.le_succ (b i))
        (euclideanZerothOrderCoeff (inclusionOfLEL hα₁.le k.le_succ c)) v‖ +
        ‖v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    (hC₁ : 0 ≤ C₁) (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT) (l : ι) :
    ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ ≤
      C₁ * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
          (euclideanZerothOrderCoeff c) u‖ +
        21 * (k + 1) ^ 2 * 2 ^ k * (Fintype.card ι * Fintype.card ι * K +
          Fintype.card ι * K * (8 * (k + 1) ^ 2) + K * (8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2))) *
          ‖inclusionOfLEL hα₁.le (Nat.add_le_add_right k.le_succ 2) u‖ +
        ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  have hZn := norm_spatialOperatorL_spatialLineDerivL_le hα₁.le a b c hak hbk hck
    (inclusionOfLEL hα₁.le (Nat.add_le_add_right k.le_succ 2) u) l
  set e := EuclideanSpace.single l (1 : ℝ)
  have hP := est (spatialLineDerivL e u)
  rw [parabolicOperatorL_spatialLineDerivL hα₁.le a b c u e] at hP
  have hf := norm_spatialLineDerivL_single_apply_le (parabolicOperatorL hα₁.le
    (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u) l
  have ht := norm_spatialTrace_spatialLineDerivL_le e u ⟨0, left_mem_Icc.2 hT.le⟩
  rw [show ‖e‖ = 1 by simp [e], one_mul] at ht
  refine hP.trans (mul_le_mul_of_nonneg_left
    ((add_le_add (norm_add_le _ _) le_rfl).trans ?_) hC₁)
  linarith

/-- **Reassembly.** A map of order `k + 3` is bounded through its norm at order `k + 2`, its
directional derivatives in the coordinate directions and the forcing: these bound its spatial
gradient, and with the equation its time derivative. -/
private theorem norm_le_of_norm_spatialLineDerivL_le (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} {K V W : ℝ}
    (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (hak : ∀ i j, ‖a i j‖ ≤ K) (hbk : ∀ i, ‖b i‖ ≤ K) (hck : ‖c‖ ≤ K)
    (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (hv : ‖inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u‖ ≤ V)
    (hw : ∀ l, ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ ≤ W) :
    ‖u‖ ≤ 4 * (k + 4) ^ 2 * (V + Fintype.card ι * W +
      (‖parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
          (euclideanZerothOrderCoeff c) u‖ + 21 * (k + 2) ^ 2 * 2 ^ (k + 1) *
        (Fintype.card ι * (Fintype.card ι * (K * W)) +
          Fintype.card ι * (K * (8 * (k + 2) ^ 2 * W)) + K * (8 * (k + 2) ^ 2 * V)))) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hck
  obtain ⟨G, hG, hGn⟩ := exists_eq_spatialFDerivL_and_norm_le (m := k + 2) u
  obtain ⟨H, hH, hHn⟩ := exists_eq_timeDerivL_and_norm_le hα a b c u
  have hGW : ‖G‖ ≤ Fintype.card ι * W :=
    hGn.trans ((Finset.sum_le_sum fun l _ ↦ hw l).trans (by simp))
  have hs₁ : ∑ i, ∑ l, ‖a i l‖ * ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ ≤
      ∑ _i : ι, ∑ _l : ι, K * W :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun l _ ↦
      mul_le_mul (hak i l) (hw l) (norm_nonneg _) hK
  have hs₂ : ∑ i, ‖b i‖ * (8 * (k + 2) ^ 2 *
      ‖spatialLineDerivL (EuclideanSpace.single i (1 : ℝ)) u‖) ≤
      ∑ _i : ι, K * (8 * (k + 2) ^ 2 * W) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul (hbk i)
      (mul_le_mul_of_nonneg_left (hw i) (by positivity)) (by positivity) hK
  have hs₃ : ‖c‖ * (8 * (k + 2) ^ 2 * ‖inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u‖) ≤
      K * (8 * (k + 2) ^ 2 * V) :=
    mul_le_mul hck (mul_le_mul_of_nonneg_left hv (by positivity)) (by positivity) hK
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs₁ hs₂
  refine (norm_le_of_eq_spatialFDerivL_of_eq_timeDerivL hα u hG hH).trans ?_
  gcongr
  exact hHn.trans (by gcongr)

/-- **The induction step.** The Schauder estimate at order `k` gives it at order `k + 1`. -/
private theorem schauderBound_succ (hα₁ : α < 1) {lam : ℝ} {k : ℕ}
    (ih : SchauderBound ι α hα₁ lam k) : SchauderBound ι α hα₁ lam (k + 1) := by
  intro K T₀
  obtain ⟨C₁, hC₁, est⟩ := ih (8 * (k + 1) ^ 2 * K) T₀
  set c₃ : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k * (Fintype.card ι * Fintype.card ι * K +
    Fintype.card ι * K * (8 * (k + 1) ^ 2) + K * (8 * (k + 1) ^ 2 * (8 * (k + 2) ^ 2)))
  set D₁ : ℝ := C₁ * (8 * (k + 1) ^ 2 + (k + 6))
  set D₂ : ℝ := C₁ * (1 + c₃ * D₁)
  set D₃ : ℝ := 1 + 21 * (k + 2) ^ 2 * 2 ^ (k + 1) * (Fintype.card ι * (Fintype.card ι * (K * D₂)) +
    Fintype.card ι * (K * (8 * (k + 2) ^ 2 * D₂)) + K * (8 * (k + 2) ^ 2 * D₁)) with hD₃
  refine ⟨4 * (k + 4) ^ 2 * (D₁ + Fintype.card ι * D₂ + D₃), by positivity,
    fun T hT hTT₀ a b c ha hak hbk hck u ↦ ?_⟩
  set f := parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u
  set g := u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩
  set v := inclusionOfLEL hα₁.le (Nat.add_le_add_right k.le_succ 2) u
  -- The order-`k` estimate applies to the coefficients read at order `k`.
  have est' := est T hT hTT₀ (fun i j ↦ inclusionOfLEL hα₁.le k.le_succ (a i j))
    (fun i ↦ inclusionOfLEL hα₁.le k.le_succ (b i)) (inclusionOfLEL hα₁.le k.le_succ c)
    (by simpa only [inclusionOfLEL_apply] using ha)
    (fun i j ↦ (norm_inclusionOfLEL_succ_le hα₁.le _).trans (by push_cast; gcongr; exact hak i j))
    (fun i ↦ (norm_inclusionOfLEL_succ_le hα₁.le _).trans (by push_cast; gcongr; exact hbk i))
    ((norm_inclusionOfLEL_succ_le hα₁.le _).trans (by push_cast; gcongr))
  -- It bounds `u` read at order `k + 2`, and the directional derivatives of `u`.
  have hv : ‖v‖ ≤ D₁ * (‖f‖ + ‖g‖) := by
    have h := est' v
    rw [← inclusionOfLEL_euclideanSecondOrderCoeff, ← inclusionOfLEL_euclideanFirstOrderCoeff,
      ← inclusionOfLEL_euclideanZerothOrderCoeff, ← inclusionOfLEL_parabolicOperatorL] at h
    have h₁ := norm_inclusionOfLEL_succ_le hα₁.le f
    have h₂ := norm_spatialTrace_inclusionOfLEL_le hα₁.le u ⟨0, left_mem_Icc.2 hT.le⟩
    refine h.trans ?_
    calc C₁ * (_ + _) ≤ C₁ * (8 * (k + 1) ^ 2 * ‖f‖ + (k + 6) * ‖g‖) := by gcongr
      _ ≤ D₁ * (‖f‖ + ‖g‖) := by
        nlinarith [mul_nonneg (mul_nonneg hC₁ (by positivity : (0 : ℝ) ≤ 8 * (k + 1) ^ 2))
          (norm_nonneg g), mul_nonneg (mul_nonneg hC₁ (by positivity : (0 : ℝ) ≤ k + 6))
          (norm_nonneg f)]
  have hw (l : ι) : ‖spatialLineDerivL (EuclideanSpace.single l (1 : ℝ)) u‖ ≤
      D₂ * (‖f‖ + ‖g‖) := by
    refine (norm_spatialLineDerivL_single_le hα₁ a b c hak hbk hck est' hC₁ u l).trans ?_
    calc _ ≤ C₁ * (‖f‖ + c₃ * (D₁ * (‖f‖ + ‖g‖)) + ‖g‖) := by gcongr
      _ = D₂ * (‖f‖ + ‖g‖) := by ring
  -- The gradient and the time derivative, and the reassembly.
  refine (norm_le_of_norm_spatialLineDerivL_le hα₁.le a b c hak hbk hck u hv hw).trans ?_
  have hf : ‖f‖ ≤ ‖f‖ + ‖g‖ := le_add_of_nonneg_right (norm_nonneg g)
  calc _ ≤ 4 * (k + 4) ^ 2 * (D₁ * (‖f‖ + ‖g‖) + Fintype.card ι * (D₂ * (‖f‖ + ‖g‖)) +
        ((‖f‖ + ‖g‖) + 21 * (k + 2) ^ 2 * 2 ^ (k + 1) *
          (Fintype.card ι * (Fintype.card ι * (K * (D₂ * (‖f‖ + ‖g‖)))) +
            Fintype.card ι * (K * (8 * (k + 2) ^ 2 * (D₂ * (‖f‖ + ‖g‖)))) +
            K * (8 * (k + 2) ^ 2 * (D₁ * (‖f‖ + ‖g‖)))))) := by gcongr
    _ = 4 * (k + 4) ^ 2 * (D₁ + Fintype.card ι * D₂ + D₃) * (‖f‖ + ‖g‖) := by rw [hD₃]; ring

/-- The Schauder estimate holds at every order. -/
private theorem schauderBound (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    SchauderBound ι α hα₁ lam k := by
  induction k with
  | zero => exact schauderBound_zero hα₀ hα₁ hlam
  | succ k ih => exact schauderBound_succ hα₁ ih

/-- **The Schauder estimate for the Cauchy problem at every order.** Let `0 < α < 1` and `k : ℕ`,
let `λ > 0` be an ellipticity constant, `K` a bound on the norms of the coefficients and `T₀` a
bound on the horizon. There is a constant `C`, depending only on these and on the dimension, such
that on every slab `ℝⁿ × [0, T]` with `T ≤ T₀`, for coefficients `aⁱʲ`, `bⁱ`, `c` in
`C_{par,b}^{k+α}` of norms at most `K` with `λ ‖ξ‖² ≤ ξᵀ a ξ`, every `u ∈ C_{par,b}^{k+2+α}`
satisfies

`‖u‖_{k+2+α} ≤ C (‖∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u‖_{k+α} + ‖u(·, 0)‖_{C^{k+2,α}})`.

No symmetry of `a` and no sign condition on `c` is needed. At order `k = 0` this is the global
Schauder estimate `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`. -/
theorem exists_norm_le_parabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
          ‖u‖ ≤ C * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
            (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ +
            ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) :=
  schauderBound hα₀ hα₁ hlam k K T₀

/-- **The Cauchy problem at every order: uniform bound on the solution operators.** For
`0 < α < 1`, `k : ℕ`, an ellipticity constant `λ > 0`, a bound `K` on the norms of the
coefficients in `C_{par,b}^{k+α}` and a bound `T₀` on the horizon, the inverses of the initial-data
isomorphisms `TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE` on `ℝⁿ × [0, T]`, `T ≤ T₀`,
are bounded uniformly: the solution `u` of `P u = f`, `u(·, 0) = g` satisfies
`‖u‖_{k+2+α} ≤ C max (‖f‖_{k+α}) (‖g‖_{C^{k+2,α}})`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanInitialDataCLE_symm_le`. -/
theorem exists_norm_euclideanInitialDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖(euclideanInitialDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_le_parabolicOperatorL (ι := ι) hα₀ hα₁ hlam k K T₀
  refine ⟨2 * C, by positivity, fun T hT hTT₀ a b c ha hak hbk hck ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d ↦ ?_⟩
  have h := hest T hT hTT₀ a b c ha hak hbk hck
    ((euclideanInitialDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm d)
  rw [parabolicOperatorL_euclideanInitialDataCLE_symm_apply,
    spatialTrace_euclideanInitialDataCLE_symm_apply] at h
  refine h.trans ?_
  have h₁ := norm_fst_le d
  have h₂ := norm_snd_le d
  nlinarith

/-- **The terminal-value problem at every order: uniform bound on the solution operators.** Under
the bounds of `exists_norm_euclideanInitialDataCLE_symm_le`, the inverses of the terminal-data
isomorphisms `TauCeti.ParabolicCkHolderSpace.euclideanTerminalDataCLE` are bounded uniformly: the
solution `u` of `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f`, `u(·, T) = g` satisfies
`‖u‖_{k+2+α} ≤ C max (‖f‖_{k+α}) (‖g‖_{C^{k+2,α}})`. The time reversal `R (x, s) = (x, T - s)` is an
isometry of the solution space and of the coefficient spaces, and it turns the terminal-value
problem into a Cauchy problem (`timeReverseLIE_euclideanTerminalDataCLE_symm_apply`). -/
theorem exists_norm_euclideanTerminalDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam k K T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck ↦
    ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_⟩
  have h := hest T hT hTT₀
    (fun i j ↦ timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm (a i j))
    (fun i ↦ timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm (b i))
    (timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm c)
    (fun p ξ ↦ by simpa only [timeReverseLIE_apply] using ha _ ξ)
    (fun i j ↦ ((LinearIsometryEquiv.norm_map _ _).trans_le (hak i j)))
    (fun i ↦ ((LinearIsometryEquiv.norm_map _ _).trans_le (hbk i)))
    ((LinearIsometryEquiv.norm_map _ _).trans_le hck)
  calc ‖(euclideanTerminalDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap d‖
      = ‖timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm
          ((euclideanTerminalDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm d)‖ :=
        (LinearIsometryEquiv.norm_map _ _).symm
    _ ≤ C * ‖(-timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm d.1,
          d.2)‖ := by
        rw [timeReverseLIE_euclideanTerminalDataCLE_symm_apply]
        exact ContinuousLinearMap.le_of_opNorm_le _ h _
    _ = C * ‖d‖ := by simp [Prod.norm_def]

/-- The perturbation bound of the initial-data and terminal-data operators
(`TauCeti.ParabolicCkHolderSpace.norm_initialDataL_sub_le`,
`TauCeti.ParabolicCkHolderSpace.norm_terminalDataL_sub_le`), evaluated at the coefficient fields of
two triples of scalar coefficients, is at most `1344 (k + 1)⁴ (k + 2)² 2ᵏ` times the total distance
`∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖` between the triples. -/
private theorem coeffPerturbation_le {k : ℕ} {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT) :
    21 * (k + 1) ^ 2 * 2 ^ k * (‖euclideanSecondOrderCoeff a - euclideanSecondOrderCoeff a'‖ +
        8 * (k + 1) ^ 2 * ‖euclideanFirstOrderCoeff b - euclideanFirstOrderCoeff b'‖ +
        64 * (k + 1) ^ 2 * (k + 2) ^ 2 *
          ‖euclideanZerothOrderCoeff c - euclideanZerothOrderCoeff c'‖) ≤
      1344 * (k + 1) ^ 4 * (k + 2) ^ 2 * 2 ^ k *
        (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  rw [← euclideanSecondOrderCoeff_sub, ← euclideanFirstOrderCoeff_sub,
    ← euclideanZerothOrderCoeff_sub]
  set N : ℝ := 64 * (k + 1) ^ 2 * (k + 2) ^ 2
  have hN₁ : 1 ≤ N := by simp only [N]; nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hN₈ : 8 * ((k : ℝ) + 1) ^ 2 ≤ N := by
    simp only [N]; nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hA := (norm_euclideanSecondOrderCoeff_le (a - a')).trans
    (le_mul_of_one_le_left (by positivity) hN₁)
  have hB := mul_le_mul hN₈ (norm_euclideanFirstOrderCoeff_le (b - b')) (norm_nonneg _)
    (by positivity)
  have hC := mul_le_mul_of_nonneg_left (norm_euclideanZerothOrderCoeff_le (c - c'))
    (by positivity : 0 ≤ N)
  simp only [Pi.sub_apply] at hA hB
  calc _ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * (N * ∑ i, ∑ j, ‖a i j - a' i j‖ +
        N * ∑ i, ‖b i - b' i‖ + N * ‖c - c'‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hB) hC) (by positivity)
    _ = _ := by simp only [N]; ring

/-- **The Cauchy problem at every order: Lipschitz dependence on the coefficients.** Under the
bounds of `exists_norm_euclideanInitialDataCLE_symm_le`, the solution operators of two Cauchy
problems on `ℝⁿ × [0, T]`, `T ≤ T₀`, differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`, with the norms of `C_{par,b}^{k+α}`. This is the
order-`k` form of `TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanInitialDataCLE_symm_sub_le`.
-/
theorem exists_norm_euclideanInitialDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        ‖(euclideanInitialDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanInitialDataCLE hα₀ hα₁ a' b' c'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam k K T₀
  set M : ℝ := 1344 * (k + 1) ^ 4 * (k + 2) ^ 2 * 2 ^ k
  refine ⟨C * M * C, by positivity,
    fun T hT hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  -- The two isomorphisms differ only in their forcing component.
  have hdiff : ‖(euclideanInitialDataCLE hα₀ hα₁ a' b' c' ⟨lam, hlam, ha'⟩).toContinuousLinearMap -
      (euclideanInitialDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).toContinuousLinearMap‖ ≤
      M * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
    rw [norm_sub_rev, coe_euclideanInitialDataCLE, coe_euclideanInitialDataCLE]
    exact (norm_initialDataL_sub_le hα₁.le).trans (coeffPerturbation_le a a' b b' c c')
  exact (ContinuousLinearEquiv.norm_coe_symm_sub_coe_symm_le_of_le
    (hest T hT hTT₀ a b c ha hak hbk hck) (hest T hT hTT₀ a' b' c' ha' hak' hbk' hck')
    hdiff).trans_eq (by ring)

/-- **The terminal-value problem at every order: Lipschitz dependence on the coefficients.** Under
the bounds of `exists_norm_euclideanTerminalDataCLE_symm_le`, the solution operators of two
terminal-value problems on `ℝⁿ × [0, T]`, `T ≤ T₀`, differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`, with the norms of `C_{par,b}^{k+α}`. This is the
order-`k` form of `TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanTerminalDataCLE_symm_sub_le`.
-/
theorem exists_norm_euclideanTerminalDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanTerminalDataCLE hα₀ hα₁ a' b' c'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanTerminalDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam k K T₀
  set M : ℝ := 1344 * (k + 1) ^ 4 * (k + 2) ^ 2 * 2 ^ k
  refine ⟨C * M * C, by positivity,
    fun T hT hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  -- The two isomorphisms differ only in their forcing component.
  have hdiff : ‖(euclideanTerminalDataCLE hα₀ hα₁ a' b' c' ⟨lam, hlam, ha'⟩).toContinuousLinearMap -
      (euclideanTerminalDataCLE hα₀ hα₁ a b c ⟨lam, hlam, ha⟩).toContinuousLinearMap‖ ≤
      M * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
    rw [norm_sub_rev, coe_euclideanTerminalDataCLE, coe_euclideanTerminalDataCLE]
    exact (norm_terminalDataL_sub_le hα₁.le _ _ _ _ _ _).trans
      (coeffPerturbation_le a a' b b' c c')
  exact (ContinuousLinearEquiv.norm_coe_symm_sub_coe_symm_le_of_le
    (hest T hT hTT₀ a b c ha hak hbk hck) (hest T hT hTT₀ a' b' c' ha' hak' hbk' hck')
    hdiff).trans_eq (by ring)

end Estimate


end ParabolicCkHolderSpace

end TauCeti
