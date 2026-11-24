/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Jet
public import TauCeti.Analysis.ODE.Complex.System
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.ODE.Gronwall.Uniqueness

/-!
# Analytic scalar equations, companion systems, and disc initial-value theorems

`TauCeti.LinearEquation U n` is a monic analytic scalar equation of positive order `n`
on an open complex domain. Its coefficients are bundled holomorphic functions on `U`,
so equality of equations does not depend on values outside the domain, and equations
along with their bundled solution spaces restrict functorially along inclusions `V ≤ U`.

The companion matrix has superdiagonal entries one and last row the negatives of the
coefficients. Scalar solutions correspond to analytic vector solutions of this system:
the vector consists of the successive, unscaled derivatives of its first coordinate.
In particular, its value at an initial point is the native `HolomorphicFunctions.jet`,
not the vector of Taylor coefficients.

Combining this companion reduction with the holomorphic matrix-system solver from
`TauCeti.Analysis.ODE.Complex.System` and Grönwall uniqueness from
`TauCeti.Analysis.ODE.Gronwall.Uniqueness` yields uniqueness of scalar solutions on
preconnected open domains, existence and uniqueness on open discs (giving Cauchy's local
initial-value theorem when `0 < r`, and holding vacuously on the empty ball when `r ≤ 0`), the
initial-jet linear isomorphism `LinearEquation.initialJetEquivBall` on positive-radius discs,
and `Module.finrank ℂ E.solutionSpace = n`. Non-monic scalar equations
`∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0` with nowhere-zero leading coefficient
`p (Fin.last m)` normalize to monic equations via `LinearEquation.ofLeadingNeZero`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §1.2,
  equation (1.18), and §4.3, Theorem 4.7.
* Frits Beukers, *E-functions and G-functions* (Arizona Winter School 2008 lecture notes),
  §2.1--2.2, Theorem 2.2.1.
-/

public noncomputable section

open Set TopologicalSpace
open scoped Matrix

namespace TauCeti

/-- A monic complex linear differential equation
`y⁽ⁿ⁾ + ∑ j < n, aⱼ y⁽ʲ⁾ = 0`, with holomorphic coefficients on an open domain. -/
@[ext]
structure LinearEquation (U : Opens ℂ) (n : ℕ) where
  /-- The order of the equation is positive. -/
  order_pos : 0 < n
  /-- The coefficients, indexed in increasing derivative order. -/
  coeff : Fin n → holomorphicFunctions U

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ} (E : LinearEquation U n)

/-- An ambient scalar representative solves the equation when it is analytic on the domain
and satisfies the homogeneous equation there. Values outside the domain are irrelevant. -/
def IsSolution (y : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U,
    iteratedDeriv n y z + ∑ j, HolomorphicFunctions.extend (E.coeff j) z *
      iteratedDeriv j y z = 0

/-- Scalar solutionhood is analyticity together with the homogeneous equation on the domain. -/
theorem isSolution_iff (y : ℂ → ℂ) :
    E.IsSolution y ↔ AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U,
      iteratedDeriv n y z + ∑ j, HolomorphicFunctions.extend (E.coeff j) z *
        iteratedDeriv j y z = 0 := (Iff.rfl)

/-- The companion matrix: superdiagonal ones, followed by the negative coefficient row. -/
def companion (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ if i.val + 1 < n then
    if j.val = i.val + 1 then 1 else 0
  else -HolomorphicFunctions.extend (E.coeff j) z

/-- Each companion-matrix entry is a superdiagonal entry or a negative coefficient. -/
@[simp]
theorem companion_apply (z : ℂ) (i j : Fin n) :
    E.companion z i j = if i.val + 1 < n then
      if j.val = i.val + 1 then 1 else 0
    else -HolomorphicFunctions.extend (E.coeff j) z := (rfl)

/-- The nonfinal rows of the companion matrix shift coordinates to the left. -/
@[simp]
theorem companion_mulVec_of_lt (z : ℂ) (v : Fin n → ℂ) (i : Fin n)
    (hi : i.val + 1 < n) :
    (E.companion z *ᵥ v) i = v ⟨i.val + 1, hi⟩ := by
  classical
  simp only [companion, hi, ↓reduceIte, Matrix.mulVec, dotProduct, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin n)]
  · simp
  · intro j _ hj
    simp [show j.val ≠ i.val + 1 from fun h ↦ hj (Fin.ext h)]
  · simp

/-- The final row gives the negative coefficient-weighted sum. -/
@[simp]
theorem companion_mulVec_of_not_lt (z : ℂ) (v : Fin n → ℂ) (i : Fin n)
    (hi : ¬i.val + 1 < n) :
    (E.companion z *ᵥ v) i = -∑ j, HolomorphicFunctions.extend (E.coeff j) z * v j := by
  simp [companion, Matrix.mulVec, dotProduct, hi, Finset.sum_neg_distrib]

/-- The companion matrix is analytic on the domain, entry by entry. -/
theorem analyticOnNhd_companion (i j : Fin n) :
    AnalyticOnNhd ℂ (fun z ↦ E.companion z i j) U := by
  simp only [companion_apply]
  split_ifs
  · exact analyticOnNhd_const
  · exact analyticOnNhd_const
  · exact (HolomorphicFunctions.analyticOnNhd_extend (Subset.refl _) (E.coeff j)).neg

variable {E} {y f g : ℂ → ℂ}

/-- A scalar solution is analytic on the domain. -/
theorem IsSolution.analyticOnNhd (hy : E.IsSolution y) : AnalyticOnNhd ℂ y U :=
  hy.1

/-- A scalar solution satisfies the homogeneous equation at every point of the domain. -/
theorem IsSolution.eq_zero (hy : E.IsSolution y) (z : ℂ) (hz : z ∈ U) :
    iteratedDeriv n y z + ∑ j, HolomorphicFunctions.extend (E.coeff j) z *
      iteratedDeriv j y z = 0 :=
  hy.2 z hz

/-- Solutionhood respects equality of scalar representatives on the domain. -/
theorem IsSolution.congr (hy : E.IsSolution y) (hyf : EqOn y f U) : E.IsSolution f := by
  refine ⟨hy.1.congr U.isOpen hyf, fun z hz ↦ ?_⟩
  have heq : y =ᶠ[nhds z] f := by
    filter_upwards [U.isOpen.mem_nhds hz] with w hw
    exact hyf hw
  simpa only [← heq.iteratedDeriv_eq] using hy.2 z hz

/-- The zero function solves every homogeneous equation. -/
@[simp]
theorem isSolution_zero : E.IsSolution 0 := by
  exact ⟨analyticOnNhd_const, fun z _ ↦ by simp⟩

/-- Sums of analytic solutions are solutions. -/
theorem IsSolution.add (hf : E.IsSolution f) (hg : E.IsSolution g) :
    E.IsSolution (f + g) := by
  refine ⟨hf.1.add hg.1, fun z hz ↦ ?_⟩
  simp only [iteratedDeriv_add (hf.1 z hz).contDiffAt (hg.1 z hz).contDiffAt,
    mul_add, Finset.sum_add_distrib]
  linear_combination hf.2 z hz + hg.2 z hz

/-- Constant complex multiples of analytic solutions are solutions. -/
theorem IsSolution.const_smul (hf : E.IsSolution f) (c : ℂ) : E.IsSolution (c • f) := by
  refine ⟨hf.1.const_smul, ?_⟩
  intro z hz
  simp only [iteratedDeriv_const_smul_field, smul_eq_mul]
  simpa [Finset.mul_sum, mul_add, mul_left_comm] using congrArg (c * ·) (hf.2 z hz)

/-- The subspace of holomorphic functions on the domain that solve the equation.
Unlike ambient representatives, its elements carry no values outside the domain. -/
def solutionSpace : Submodule ℂ (holomorphicFunctions U) where
  carrier := {f | E.IsSolution (HolomorphicFunctions.extend f)}
  zero_mem' := E.isSolution_zero.congr (fun z hz ↦ by
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩])
  add_mem' {f g} hf hg := (hf.add hg).congr (fun z hz ↦ by
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, Subalgebra.coe_add])
  smul_mem' c f hf := (hf.const_smul c).congr (fun z hz ↦ by
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩])

/-- Shortcut additive-group instance on `E.solutionSpace`, avoiding expensive ring-instance
backtracking on `holomorphicFunctions U`. -/
instance instAddCommGroupSolutionSpace : AddCommGroup E.solutionSpace :=
  letI : AddCommGroup (holomorphicFunctions U) :=
    AddSubgroupClass.toAddCommGroup (holomorphicFunctions U)
  Submodule.addCommGroup E.solutionSpace

/-- Membership in the solution subspace is the scalar equation for the zero extension. -/
@[simp]
theorem mem_solutionSpace (f : holomorphicFunctions U) :
    f ∈ E.solutionSpace ↔ E.IsSolution (HolomorphicFunctions.extend f) := Iff.rfl

/-- The unscaled initial jet on the solution space, obtained by restricting the native
holomorphic-function jet. No factorials enter this linear map. -/
def initialJet {a : ℂ} (ha : a ∈ U) : E.solutionSpace →ₗ[ℂ] (Fin n → ℂ) :=
  (HolomorphicFunctions.jet ha n).comp E.solutionSpace.subtype

/-- The components of an initial jet are the successive complex derivatives. -/
@[simp]
theorem initialJet_apply {a : ℂ} (ha : a ∈ U) (f : E.solutionSpace) (j : Fin n) :
    E.initialJet ha f j = iteratedDeriv j (HolomorphicFunctions.extend f.val) a :=
  HolomorphicFunctions.jet_apply ha n f.val j

/-- An analytic vector solves the companion system if its derivative is the matrix action. -/
def IsCompanionSolution (v : ℂ → Fin n → ℂ) : Prop :=
  AnalyticOnNhd ℂ v U ∧ ∀ z ∈ U, HasDerivAt v (E.companion z *ᵥ v z) z

/-- Companion solutionhood is analyticity together with the matrix derivative equation. -/
theorem isCompanionSolution_iff (v : ℂ → Fin n → ℂ) :
    E.IsCompanionSolution v ↔ AnalyticOnNhd ℂ v U ∧
      ∀ z ∈ U, HasDerivAt v (E.companion z *ᵥ v z) z := (Iff.rfl)

/-- A companion-system solution is analytic on the domain. -/
theorem IsCompanionSolution.analyticOnNhd {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) : AnalyticOnNhd ℂ v U :=
  hv.1

/-- A companion-system solution has the derivative prescribed by the matrix action. -/
theorem IsCompanionSolution.hasDerivAt {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) (z : ℂ) (hz : z ∈ U) :
    HasDerivAt v (E.companion z *ᵥ v z) z :=
  hv.2 z hz

/-- The derivative vector of a scalar solution solves the companion system. -/
theorem IsSolution.isCompanionSolution (hy : E.IsSolution y) :
    E.IsCompanionSolution (fun z j ↦ iteratedDeriv j y z) := by
  have ha (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k y) U := by
    simpa only [iteratedDeriv_eq_iterate] using hy.1.iterated_deriv k
  refine ⟨analyticOnNhd_pi_iff.mpr (fun j ↦ ha j), fun z hz ↦ ?_⟩
  apply hasDerivAt_pi.mpr
  intro i
  have hd := ((ha i) z hz).differentiableAt.hasDerivAt
  by_cases hi : i.val + 1 < n
  · rw [E.companion_mulVec_of_lt z _ i hi]
    simpa only [iteratedDeriv_succ] using hd
  · rw [E.companion_mulVec_of_not_lt z _ i hi]
    have hin : i.val + 1 = n := by omega
    convert hd using 1
    rw [← iteratedDeriv_succ, hin]
    exact (eq_neg_iff_add_eq_zero.mpr (hy.2 z hz)).symm

/-- Every coordinate of a companion-system solution is the corresponding unscaled derivative
of its first coordinate. -/
theorem IsCompanionSolution.eq_iteratedDeriv {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) (z : ℂ) (hz : z ∈ U) (j : Fin n) :
    v z j = iteratedDeriv j (fun w ↦ v w ⟨0, E.order_pos⟩) z := by
  have hj : ∀ k (hk : k < n), EqOn (fun w ↦ v w ⟨k, hk⟩)
      (iteratedDeriv k (fun w ↦ v w ⟨0, E.order_pos⟩)) U := by
    intro k
    induction k with
    | zero => intro hk w _; simp
    | succ k ih =>
      intro hk w hw
      have hk' : k < n := by omega
      have hd := (hasDerivAt_pi.mp (hv.2 w hw)) (⟨k, hk'⟩ : Fin n)
      rw [E.companion_mulVec_of_lt w _ _ hk] at hd
      rw [iteratedDeriv_succ, ← (ih hk').deriv U.isOpen hw]
      exact hd.deriv.symm
  exact hj j j.isLt hz

/-- The first coordinate of a companion-system solution solves the scalar equation. -/
theorem IsCompanionSolution.isSolution {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) :
    E.IsSolution (fun z ↦ v z ⟨0, E.order_pos⟩) := by
  refine ⟨analyticOnNhd_pi_iff.mp hv.1 _, fun z hz ↦ ?_⟩
  let i : Fin n := ⟨n - 1, by have := E.order_pos; omega⟩
  have hi : ¬i.val + 1 < n := by dsimp [i]; omega
  have hin : i.val + 1 = n := by dsimp [i]; have := E.order_pos; omega
  have hd := (hasDerivAt_pi.mp (hv.2 z hz)) i
  rw [E.companion_mulVec_of_not_lt z _ i hi] at hd
  have heq : EqOn (fun w ↦ v w i)
      (iteratedDeriv i (fun w ↦ v w ⟨0, E.order_pos⟩)) U :=
    fun w hw ↦ hv.eq_iteratedDeriv w hw i
  have htop : iteratedDeriv n (fun w ↦ v w ⟨0, E.order_pos⟩) z =
      -∑ j, HolomorphicFunctions.extend (E.coeff j) z * v z j := by
    calc
      iteratedDeriv n (fun w ↦ v w ⟨0, E.order_pos⟩) z =
          iteratedDeriv (i.val + 1) (fun w ↦ v w ⟨0, E.order_pos⟩) z :=
        congrArg (fun k ↦ iteratedDeriv k (fun w ↦ v w ⟨0, E.order_pos⟩) z) hin.symm
      _ = _ := by rw [iteratedDeriv_succ, ← heq.deriv U.isOpen hz]; exact hd.deriv
  rw [htop]
  simp only [← hv.eq_iteratedDeriv z hz]
  exact neg_add_cancel _

/-- The first coordinate of a companion-system solution, bundled on the domain as a
scalar solution. -/
def IsCompanionSolution.toSolutionSpace {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) : E.solutionSpace :=
  ⟨HolomorphicFunctions.of U (fun z ↦ v z ⟨0, E.order_pos⟩)
      hv.isSolution.analyticOnNhd.differentiableOn,
    hv.isSolution.congr (fun z hz ↦ by
      simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩])⟩

/-- The bundled scalar solution evaluates to the first vector coordinate on the domain. -/
@[simp]
theorem IsCompanionSolution.toSolutionSpace_apply {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) (z : U) :
    hv.toSolutionSpace.val.val z = v z ⟨0, E.order_pos⟩ := by
  simp [toSolutionSpace]

/-- The initial jet of the bundled scalar solution is the companion solution's value. -/
@[simp]
theorem IsCompanionSolution.initialJet_toSolutionSpace {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) {a : ℂ} (ha : a ∈ U) :
    E.initialJet ha hv.toSolutionSpace = v a := by
  ext j
  exact (HolomorphicFunctions.jet_of ha n _ _ j).trans (hv.eq_iteratedDeriv a ha j).symm

/-- Scalar solutions are exactly those whose unscaled derivative vector solves the
companion system. -/
theorem isSolution_iff_isCompanionSolution :
    E.IsSolution y ↔ E.IsCompanionSolution (fun z j ↦ iteratedDeriv j y z) := by
  constructor
  · exact IsSolution.isCompanionSolution
  · intro h
    simpa only [iteratedDeriv_zero] using h.isSolution

/-- A bundled holomorphic function lies in `E.solutionSpace` iff its zero extension satisfies the
monic differential equation at every point of `U`. -/
theorem mem_solutionSpace_iff (E : LinearEquation U n) (f : holomorphicFunctions U) :
    f ∈ E.solutionSpace ↔ ∀ z : U,
      iteratedDeriv n (HolomorphicFunctions.extend f) z +
        ∑ j, (E.coeff j).val z * iteratedDeriv j (HolomorphicFunctions.extend f) z = 0 := by
  refine ⟨fun hf z ↦ ?_, fun hf ↦ ⟨HolomorphicFunctions.analyticOnNhd_extend Subset.rfl f,
    fun z hz ↦ ?_⟩⟩
  · simpa [HolomorphicFunctions.extend_apply _ z] using hf.2 z z.property
  · simpa [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩] using hf ⟨z, hz⟩

/-! ### Restriction along open subdomains -/

/-- Restrict a monic linear differential equation to a smaller open domain. -/
def restrict (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U) : LinearEquation V n where
  order_pos := E.order_pos
  coeff j := HolomorphicFunctions.restrict h (E.coeff j)

/-- Coefficients of a restricted equation are the restricted holomorphic coefficients. -/
@[simp]
theorem restrict_coeff (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U) (j : Fin n) :
    (E.restrict h).coeff j = HolomorphicFunctions.restrict h (E.coeff j) := by rfl

/-- At a point of the smaller domain, the zero extensions of the restricted coefficients agree
with those of the original coefficients. -/
theorem extend_restrict_coeff_of_mem (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U)
    {z : ℂ} (hz : z ∈ V) (j : Fin n) :
    HolomorphicFunctions.extend ((E.restrict h).coeff j) z =
      HolomorphicFunctions.extend (E.coeff j) z := by
  simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩,
    HolomorphicFunctions.extend_apply _ ⟨z, h hz⟩]

/-- Restricting an equation to its own domain leaves it unchanged. -/
@[simp]
theorem restrict_refl (E : LinearEquation U n) :
    E.restrict (le_refl U) = E := by
  ext j z
  simp

/-- Successive restriction of an equation along nested open subdomains equals direct
restriction. -/
@[simp]
theorem restrict_restrict (E : LinearEquation U n) {V W : Opens ℂ}
    (hVU : V ≤ U) (hWV : W ≤ V) :
    (E.restrict hVU).restrict hWV = E.restrict (hWV.trans hVU) := by
  ext j z
  simp

/-- On the smaller domain, the companion matrix of `E.restrict h` agrees with `E.companion`. -/
theorem companion_restrict_eq_of_mem (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U)
    {z : ℂ} (hz : z ∈ V) : (E.restrict h).companion z = E.companion z := by
  ext i j
  simp only [companion_apply, E.extend_restrict_coeff_of_mem h hz]

/-- Any ambient scalar solution on `U` restricts to a scalar solution on `V ≤ U`. -/
theorem IsSolution.restrict {V : Opens ℂ} (h : V ≤ U) (hy : E.IsSolution y) :
    (E.restrict h).IsSolution y := by
  refine ⟨hy.1.mono h, fun z hz ↦ ?_⟩
  convert hy.2 z (h hz) using 2
  exact Finset.sum_congr rfl fun j _ ↦ by rw [E.extend_restrict_coeff_of_mem h hz]

/-- Any ambient companion solution on `U` restricts to a companion solution on `V ≤ U`. -/
theorem IsCompanionSolution.restrict {V : Opens ℂ} (h : V ≤ U) {v : ℂ → Fin n → ℂ}
    (hv : E.IsCompanionSolution v) : (E.restrict h).IsCompanionSolution v :=
  ⟨hv.1.mono h, fun z hz ↦ by
    rw [E.companion_restrict_eq_of_mem h hz]
    exact hv.2 z (h hz)⟩

/-- Restriction of bundled holomorphic solutions along an inclusion `V ≤ U` of open domains. -/
def restrictSolutionSpace (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U) :
    E.solutionSpace →ₗ[ℂ] (E.restrict h).solutionSpace where
  toFun f := ⟨HolomorphicFunctions.restrict h f.val,
    (f.property.restrict h).congr fun z hz ↦ by
      simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩,
        HolomorphicFunctions.extend_apply _ ⟨z, h hz⟩]⟩
  map_add' f₁ f₂ := Subtype.ext (map_add (HolomorphicFunctions.restrict h) f₁.val f₂.val)
  map_smul' c f₁ := Subtype.ext
    ((HolomorphicFunctions.restrict h).toLinearMap.map_smul c f₁.val)

/-- Restricting a bundled solution restricts its underlying holomorphic function. -/
@[simp]
theorem coe_restrictSolutionSpace (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U)
    (f : E.solutionSpace) :
    (E.restrictSolutionSpace h f).val = HolomorphicFunctions.restrict h f.val := by rfl

/-- Restricting a bundled solution preserves its initial jet at any point of the subdomain. -/
@[simp]
theorem initialJet_restrictSolutionSpace (E : LinearEquation U n) {V : Opens ℂ} (h : V ≤ U)
    {a : ℂ} (ha : a ∈ V) (f : E.solutionSpace) :
    (E.restrict h).initialJet ha (E.restrictSolutionSpace h f) = E.initialJet (h ha) f :=
  HolomorphicFunctions.jet_restrict h ha n f.val

/-- Restricting a solution to its own domain acts as the identity under the canonical
identification of equal solution submodules. -/
@[simp]
theorem ofEq_restrictSolutionSpace_refl (E : LinearEquation U n)
    (h : (E.restrict (le_refl U)).solutionSpace = E.solutionSpace) (f : E.solutionSpace) :
    LinearEquiv.ofEq _ _ h (E.restrictSolutionSpace (le_refl U) f) = f := by
  apply Subtype.ext
  simp

/-- Restricting the solution space to its own domain is the identity linear map up to the
canonical identification of equal solution submodules. -/
@[simp]
theorem ofEq_comp_restrictSolutionSpace_refl (E : LinearEquation U n)
    (h : (E.restrict (le_refl U)).solutionSpace = E.solutionSpace) :
    (LinearEquiv.ofEq _ _ h).toLinearMap.comp (E.restrictSolutionSpace (le_refl U)) =
      LinearMap.id :=
  LinearMap.ext fun _ ↦ by simp

/-- Successive restriction of a solution along nested open subdomains equals direct restriction
under the canonical identification of equal solution submodules. -/
@[simp]
theorem ofEq_restrictSolutionSpace_restrictSolutionSpace (E : LinearEquation U n)
    {V W : Opens ℂ} (hVU : V ≤ U) (hWV : W ≤ V)
    (h : ((E.restrict hVU).restrict hWV).solutionSpace =
      (E.restrict (hWV.trans hVU)).solutionSpace)
    (f : E.solutionSpace) :
    LinearEquiv.ofEq _ _ h
        ((E.restrict hVU).restrictSolutionSpace hWV (E.restrictSolutionSpace hVU f)) =
      E.restrictSolutionSpace (hWV.trans hVU) f := by
  apply Subtype.ext
  simp only [LinearEquiv.coe_ofEq_apply, coe_restrictSolutionSpace, ← AlgHom.comp_apply,
    HolomorphicFunctions.restrict_comp_restrict]

/-- Successive restriction of solution spaces along nested open subdomains equals direct
restriction up to the canonical identification of equal solution submodules. -/
@[simp]
theorem ofEq_comp_restrictSolutionSpace_comp (E : LinearEquation U n)
    {V W : Opens ℂ} (hVU : V ≤ U) (hWV : W ≤ V)
    (h : ((E.restrict hVU).restrict hWV).solutionSpace =
      (E.restrict (hWV.trans hVU)).solutionSpace) :
    (LinearEquiv.ofEq _ _ h).toLinearMap.comp
        (((E.restrict hVU).restrictSolutionSpace hWV).comp (E.restrictSolutionSpace hVU)) =
      E.restrictSolutionSpace (hWV.trans hVU) :=
  LinearMap.ext fun _ ↦ by simp

/-! ### Uniqueness on preconnected open domains -/

/-- **Uniqueness for companion systems on preconnected open domains.** Two solutions of
`E.IsCompanionSolution` on a preconnected open domain `U` that agree at one point of `U` agree
throughout `U`. -/
theorem IsCompanionSolution.eqOn_of_isPreconnected (hU : IsPreconnected (U : Set ℂ))
    {v w : ℂ → Fin n → ℂ} (hv : E.IsCompanionSolution v) (hw : E.IsCompanionSolution w)
    {a : ℂ} (ha : a ∈ U) (h : v a = w a) : EqOn v w U :=
  U.isOpen.eqOn_of_hasDerivAt_mulVec hU
    (fun i j ↦ (E.analyticOnNhd_companion i j).continuousOn)
    hv.hasDerivAt hw.hasDerivAt ha h

/-- **Uniqueness for scalar linear equations on preconnected open domains.** Two scalar solutions on
a preconnected open domain `U` whose first `n` iterated derivatives agree at one point of `U` agree
throughout `U`. -/
theorem IsSolution.eqOn_of_isPreconnected_of_iteratedDeriv_eq
    (hU : IsPreconnected (U : Set ℂ)) (hf : E.IsSolution f) (hg : E.IsSolution g)
    {a : ℂ} (ha : a ∈ U) (h : ∀ j : Fin n, iteratedDeriv j f a = iteratedDeriv j g a) :
    EqOn f g U := by
  intro z hz
  have hvec := hf.isCompanionSolution.eqOn_of_isPreconnected hU hg.isCompanionSolution
    ha (funext h) hz
  simpa using congrFun hvec ⟨0, E.order_pos⟩

/-- On a preconnected open domain `U`, the unscaled initial-jet map at any `a ∈ U` is injective on
`E.solutionSpace`. -/
theorem initialJet_injective_of_isPreconnected (E : LinearEquation U n)
    (hU : IsPreconnected (U : Set ℂ)) {a : ℂ} (ha : a ∈ U) :
    Function.Injective (E.initialJet ha) := by
  intro f₁ f₂ hjet
  apply Subtype.ext
  apply Subtype.ext
  ext z
  have heq := f₁.property.eqOn_of_isPreconnected_of_iteratedDeriv_eq hU f₂.property ha
    (fun j ↦ by simpa only [initialJet_apply] using congrFun hjet j) z.property
  simpa [HolomorphicFunctions.extend_apply _ z] using heq

/-! ### Disc existence, uniqueness, and dimension of the solution space -/

/-- **Disc existence and uniqueness for companion systems.** For any `E` on `ball z₀ r` and any
vector `c : Fin n → ℂ`, there exists an ambient companion solution `v` of `E` with `v z₀ = c`,
unique on `ball z₀ r` among companion solutions taking value `c` at `z₀`. When `0 < r`,
`z₀ ∈ ball z₀ r` and this is Cauchy's local initial-value theorem for the companion system; when
`r ≤ 0`, `ball z₀ r` is empty so `E.IsCompanionSolution` and `EqOn` uniqueness on `ball z₀ r` hold
vacuously while `v z₀ = c` still holds. -/
theorem exists_isCompanionSolution_ball {z₀ : ℂ} {r : ℝ}
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) (c : Fin n → ℂ) :
    ∃ v : ℂ → Fin n → ℂ, E.IsCompanionSolution v ∧ v z₀ = c ∧
      ∀ w : ℂ → Fin n → ℂ, E.IsCompanionSolution w → w z₀ = c →
        EqOn w v (Metric.ball z₀ r) := by
  obtain ⟨v, hv_an, hv_deriv, hv0, huniq⟩ :=
    exists_analyticOnNhd_ball_hasDerivAt_mulVec
      (fun i j ↦ (E.analyticOnNhd_companion i j).differentiableOn) c
  exact ⟨v, ⟨hv_an, hv_deriv⟩, hv0, fun w hw hw0 ↦ huniq w hw.hasDerivAt hw0⟩

/-- **Disc existence and uniqueness for monic scalar linear equations.** For any `E` on `ball z₀ r`
and any `c : Fin n → ℂ`, there exists a scalar solution `y` of `E` whose first `n` iterated
derivatives at `z₀` equal `c`, unique on `ball z₀ r` among solutions with the same derivatives at
`z₀`. When `0 < r`, `z₀ ∈ ball z₀ r` and this is Cauchy's initial-value theorem on `ball z₀ r`;
when `r ≤ 0`, `ball z₀ r` is empty so `E.IsSolution` and `EqOn` uniqueness on `ball z₀ r` hold
vacuously while `y` still realizes the prescribed derivatives at `z₀`. -/
theorem exists_isSolution_ball {z₀ : ℂ} {r : ℝ}
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) (c : Fin n → ℂ) :
    ∃ y : ℂ → ℂ, E.IsSolution y ∧ (∀ j : Fin n, iteratedDeriv j y z₀ = c j) ∧
      ∀ w : ℂ → ℂ, E.IsSolution w → (∀ j : Fin n, iteratedDeriv j w z₀ = c j) →
        EqOn w y (Metric.ball z₀ r) := by
  by_cases hr : 0 < r
  · obtain ⟨v, hv, hv0, huniq⟩ := E.exists_isCompanionSolution_ball c
    refine ⟨fun z ↦ v z ⟨0, E.order_pos⟩, hv.isSolution, fun j ↦ ?_, fun w hw hwc z hz ↦ ?_⟩
    · rw [← hv.eq_iteratedDeriv z₀ (Metric.mem_ball_self hr) j, hv0]
    · have hvec := huniq _ hw.isCompanionSolution (funext hwc) hz
      simpa using congrFun hvec ⟨0, E.order_pos⟩
  · let E₁ : LinearEquation ⟨Metric.ball z₀ 1, Metric.isOpen_ball⟩ n := ⟨E.order_pos, fun _ ↦ 0⟩
    obtain ⟨v, hv, hv0, -⟩ := E₁.exists_isCompanionSolution_ball c
    have hfalse {z : ℂ} (hz : z ∈ Metric.ball z₀ r) : False := hr (Metric.pos_of_mem_ball hz)
    refine ⟨fun z ↦ v z ⟨0, E.order_pos⟩,
      ⟨fun _ hz ↦ (hfalse hz).elim, fun _ hz ↦ (hfalse hz).elim⟩,
      fun j ↦ ?_, fun _ _ _ _ hz ↦ (hfalse hz).elim⟩
    rw [← hv.eq_iteratedDeriv z₀ (Metric.mem_ball_self zero_lt_one) j, hv0]

/-- **Initial-jet linear isomorphism on a positive-radius disc.** On `ball z₀ r` (`0 < r`), the
unscaled initial-jet map at `z₀` is a `ℂ`-linear isomorphism `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)`. -/
def initialJetEquivBall {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet (Metric.mem_ball_self hr))
    ⟨E.initialJet_injective_of_isPreconnected (convex_ball z₀ r).isPreconnected
        (Metric.mem_ball_self hr),
      fun c ↦ by
        obtain ⟨v, hv, hv0, -⟩ := E.exists_isCompanionSolution_ball c
        exact ⟨hv.toSolutionSpace,
          (hv.initialJet_toSolutionSpace (Metric.mem_ball_self hr)).trans hv0⟩⟩

/-- Forward application of `initialJetEquivBall` is `E.initialJet` at the disc center `z₀`. -/
@[simp]
theorem initialJetEquivBall_apply {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) (f : E.solutionSpace) :
    E.initialJetEquivBall hr f = E.initialJet (Metric.mem_ball_self hr) f := by rfl

/-- The bundled solution space of a monic linear differential equation on `ball z₀ r` is a finitely
generated `ℂ`-module for every radius `r : ℝ`. -/
theorem finite_solutionSpace_ball {z₀ : ℂ} {r : ℝ}
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) :
    Module.Finite ℂ E.solutionSpace := by
  by_cases hr : 0 < r
  · exact Module.Finite.equiv (E.initialJetEquivBall hr).symm
  · have hzero : ∀ f : E.solutionSpace, f = 0 := fun _ ↦
      Subtype.ext <| Subtype.ext <| ContinuousMap.ext fun z ↦ False.elim <| by
        linarith [dist_nonneg (x := (z : ℂ)) (y := z₀),
          Metric.mem_ball.mp z.property, not_lt.mp hr]
    exact Module.Finite.of_surjective (0 : ℂ →ₗ[ℂ] E.solutionSpace)
      fun f ↦ ⟨0, (hzero f).symm⟩

/-- **Dimension of the solution space on a positive-radius disc.** For `0 < r`, the bundled solution
space of an order-`n` monic linear equation on `ball z₀ r` has complex dimension `n`. -/
theorem finrank_solutionSpace_ball {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) :
    Module.finrank ℂ E.solutionSpace = n := by
  simpa using (E.initialJetEquivBall hr).finrank_eq

/-! ### Normalization of equations with nowhere-zero leading coefficient -/

/-- Normalize a homogeneous linear differential equation
`∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0` of positive order `m` with holomorphic
coefficients on `U` and nowhere-zero leading coefficient `p (Fin.last m)` into a monic
`LinearEquation U m`. -/
def ofLeadingNeZero {U : Opens ℂ} {m : ℕ} (hm : 0 < m) (p : Fin (m + 1) → ℂ → ℂ)
    (hp : ∀ i, DifferentiableOn ℂ (p i) U) (hne : ∀ z ∈ U, p (Fin.last m) z ≠ 0) :
    LinearEquation U m where
  order_pos := hm
  coeff j := HolomorphicFunctions.of U (fun z ↦ p j.castSucc z / p (Fin.last m) z)
    ((hp j.castSucc).div (hp (Fin.last m)) hne)

/-- Coefficients of `ofLeadingNeZero` divide the lower-order coefficients by `p (Fin.last m)`. -/
@[simp]
theorem ofLeadingNeZero_coeff_apply {U : Opens ℂ} {m : ℕ} (hm : 0 < m)
    (p : Fin (m + 1) → ℂ → ℂ) (hp : ∀ i, DifferentiableOn ℂ (p i) U)
    (hne : ∀ z ∈ U, p (Fin.last m) z ≠ 0) (j : Fin m) (z : U) :
    ((ofLeadingNeZero hm p hp hne).coeff j).val z =
      p j.castSucc z / p (Fin.last m) z := by
  simp [ofLeadingNeZero]

/-- Ambient solutions of `ofLeadingNeZero` are precisely analytic functions on `U` satisfying
`∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0` on `U`. -/
theorem isSolution_ofLeadingNeZero_iff {U : Opens ℂ} {m : ℕ} (hm : 0 < m)
    (p : Fin (m + 1) → ℂ → ℂ) (hp : ∀ i, DifferentiableOn ℂ (p i) U)
    (hne : ∀ z ∈ U, p (Fin.last m) z ≠ 0) (y : ℂ → ℂ) :
    (ofLeadingNeZero hm p hp hne).IsSolution y ↔
      AnalyticOnNhd ℂ y U ∧
        ∀ z ∈ U, ∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0 := by
  refine and_congr_right fun _ ↦ forall₂_congr fun z hz ↦ ?_
  have hlead : p (Fin.last m) z ≠ 0 := hne z hz
  have hsum :
      p (Fin.last m) z *
        (iteratedDeriv m y z +
          ∑ j : Fin m,
            HolomorphicFunctions.extend ((ofLeadingNeZero hm p hp hne).coeff j) z *
              iteratedDeriv j y z) =
        ∑ i : Fin (m + 1), p i z * iteratedDeriv i y z := by
    rw [mul_add, Finset.mul_sum, Fin.sum_univ_castSucc, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, ofLeadingNeZero_coeff_apply]
    field_simp [hlead]
    rfl
  rw [← mul_eq_zero_iff_left hlead, hsum]

/-- Bundled holomorphic solutions of `ofLeadingNeZero` are the holomorphic functions on `U` whose
zero extension satisfies `∑ i : Fin (m + 1), p i z * iteratedDeriv i (extend f) z = 0` at every
point of `U`. -/
theorem mem_solutionSpace_ofLeadingNeZero {U : Opens ℂ} {m : ℕ} (hm : 0 < m)
    (p : Fin (m + 1) → ℂ → ℂ) (hp : ∀ i, DifferentiableOn ℂ (p i) U)
    (hne : ∀ z ∈ U, p (Fin.last m) z ≠ 0) (f : holomorphicFunctions U) :
    f ∈ (ofLeadingNeZero hm p hp hne).solutionSpace ↔
      ∀ z : U, ∑ i : Fin (m + 1),
        p i z * iteratedDeriv i (HolomorphicFunctions.extend f) z = 0 := by
  rw [mem_solutionSpace, isSolution_ofLeadingNeZero_iff]
  exact ⟨fun h z ↦ h.2 z z.property, fun h ↦
    ⟨HolomorphicFunctions.analyticOnNhd_extend Subset.rfl f, fun z hz ↦ h ⟨z, hz⟩⟩⟩

/-! The following checks fix the coefficient sign, unscaled-jet convention, and disc dimension. -/

example : (⟨by omega, fun _ ↦ 1⟩ : LinearEquation U 1).IsSolution
    (fun z ↦ Complex.exp (-z)) := by
  refine ⟨fun z _ ↦ (analyticAt_id.neg.cexp), fun z hz ↦ ?_⟩
  have hd := ((hasDerivAt_id z).neg.cexp).deriv
  simp only [Pi.neg_apply, id_eq] at hd
  simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, iteratedDeriv_one, hd]

example : ¬ (⟨by omega, fun _ ↦ 1⟩ : LinearEquation (⊤ : Opens ℂ) 1).IsSolution
    (fun _ ↦ 1) := by
  intro h
  have := h.2 0 (by simp)
  have hc : HolomorphicFunctions.extend (1 : holomorphicFunctions (⊤ : Opens ℂ)) 0 = 1 :=
    HolomorphicFunctions.extend_apply _ ⟨0, Set.mem_univ _⟩
  norm_num [iteratedDeriv_one, hc] at this

example (a b : ℂ) : (⟨by omega, fun _ ↦ 0⟩ : LinearEquation U 2).IsSolution
    (fun z ↦ a + b * z) := by
  refine ⟨fun z _ ↦ analyticAt_const.add (analyticAt_const.mul analyticAt_id),
    fun z hz ↦ ?_⟩
  simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, iteratedDeriv_succ]

example : HolomorphicFunctions.jet (U := (⊤ : Opens ℂ)) (a := 0) (by simp) 3
    (HolomorphicFunctions.of ⊤ (fun z ↦ z ^ 2) (by fun_prop)) = ![0, 0, 2] := by
  ext j
  fin_cases j <;> simp [HolomorphicFunctions.jet_of, iteratedDeriv_pow]

end LinearEquation

/-- **Disc existence and uniqueness for scalar linear differential equations.** For any order
`m : ℕ`, coefficients `p : Fin (m + 1) → ℂ → ℂ` complex differentiable on `ball z₀ r` with
nowhere-zero leading coefficient `p (Fin.last m)` on `ball z₀ r`, and `c : Fin m → ℂ`, there exists
`y : ℂ → ℂ` analytic on `ball z₀ r` solving `∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0` on
`ball z₀ r` with `iteratedDeriv j y z₀ = c j` for all `j : Fin m`, unique on `ball z₀ r`. When
`0 < r`, `z₀ ∈ ball z₀ r` and this is Cauchy's initial-value theorem on `ball z₀ r`; when `r ≤ 0`,
`ball z₀ r` is empty so the hypotheses and conclusions on `ball z₀ r` hold vacuously while `y` still
realizes the prescribed derivatives at `z₀`. -/
theorem exists_analyticOnNhd_ball_sum_iteratedDeriv_eq_zero
    {z₀ : ℂ} {r : ℝ} {m : ℕ} {p : Fin (m + 1) → ℂ → ℂ}
    (hp : ∀ i, DifferentiableOn ℂ (p i) (Metric.ball z₀ r))
    (hne : ∀ z ∈ Metric.ball z₀ r, p (Fin.last m) z ≠ 0) (c : Fin m → ℂ) :
    ∃ y : ℂ → ℂ, AnalyticOnNhd ℂ y (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, ∑ i : Fin (m + 1), p i z * iteratedDeriv i y z = 0) ∧
      (∀ j : Fin m, iteratedDeriv j y z₀ = c j) ∧
      ∀ w : ℂ → ℂ, AnalyticOnNhd ℂ w (Metric.ball z₀ r) →
        (∀ z ∈ Metric.ball z₀ r, ∑ i : Fin (m + 1), p i z * iteratedDeriv i w z = 0) →
        (∀ j : Fin m, iteratedDeriv j w z₀ = c j) → EqOn w y (Metric.ball z₀ r) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, analyticOnNhd_const, fun _ _ ↦ by simp, fun j ↦ Fin.elim0 j,
      fun w _ hw _ z hz ↦ ?_⟩
    have h0 := hw z hz
    rw [Fin.sum_univ_one, Fin.val_zero, iteratedDeriv_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hne z hz)
  · let E := LinearEquation.ofLeadingNeZero
      (U := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩) hm p hp hne
    obtain ⟨y, hy, hyc, huniq⟩ := E.exists_isSolution_ball c
    rw [LinearEquation.isSolution_ofLeadingNeZero_iff] at hy
    refine ⟨y, hy.1, hy.2, hyc, fun w hw_an hw_eq hwc ↦ huniq w ?_ hwc⟩
    exact (LinearEquation.isSolution_ofLeadingNeZero_iff hm p hp hne w).mpr ⟨hw_an, hw_eq⟩

example :
    let U : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
    let p : Fin 2 → ℂ → ℂ := ![fun _ ↦ -1, fun z ↦ z - 1]
    have hp : ∀ i, DifferentiableOn ℂ (p i) U := by
      intro i; fin_cases i <;> dsimp [p] <;> fun_prop
    have hne : ∀ z ∈ U, p (Fin.last 1) z ≠ 0 := fun z hz h0 ↦ by
      have hz1 : z = 1 := sub_eq_zero.mp h0
      subst hz1
      norm_num [U] at hz
    Module.finrank ℂ (LinearEquation.ofLeadingNeZero Nat.one_pos p hp hne).solutionSpace = 1 := by
  intro U p hp hne
  exact (LinearEquation.ofLeadingNeZero Nat.one_pos p hp hne).finrank_solutionSpace_ball
    zero_lt_one

example : ¬ ∃ y : ℂ → ℂ,
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      ∑ i : Fin 2, (![fun _ : ℂ ↦ (-1 : ℂ), fun z : ℂ ↦ z] i z) * iteratedDeriv i y z = 0) ∧
    y 0 = 1 := by
  rintro ⟨y, hy, hy0⟩
  have h0 := hy 0 (Metric.mem_ball_self zero_lt_one)
  simp [Fin.sum_univ_two, hy0] at h0

end TauCeti
