/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Jet
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic scalar equations and their companion systems

`TauCeti.LinearEquation U n` is a monic analytic scalar equation of positive order `n`
on an open complex domain. Its coefficients are bundled holomorphic functions on `U`,
so equality of equations does not depend on values outside the domain.

The companion matrix has superdiagonal entries one and last row the negatives of the
coefficients. Scalar solutions correspond to analytic vector solutions of this system:
the vector consists of the successive, unscaled derivatives of its first coordinate.
In particular, its value at an initial point is the native `HolomorphicFunctions.jet`,
not the vector of Taylor coefficients. These comparisons allow scalar initial-value
problems to be treated as first-order vector equations.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §1.2,
  equation (1.18), for the companion-system reduction.
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

/-! The following checks fix the coefficient sign and the unscaled-jet convention. -/

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

end TauCeti
