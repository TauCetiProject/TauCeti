/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
public import TauCeti.Algebra.Category.ModuleCat.DirectedUnion
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Boundary examples for the Mittag–Leffler criterion

The zero-transition tower over F_p is Mittag–Leffler with zero limit and first derived limit,
although none of its transitions is surjective. The inclusion tower pⁿZ_p is not Mittag–Leffler,
but also has zero first derived limit: summable p-adic tails solve its shift equation.
The nonzero first derived limit of the multiplication-by-p tower over Z is computed in
`TauCeti.Algebra.Category.ModuleCat.Tower.Padic`. The inclusion diagram uses
`TauCeti.ModuleCat.submoduleFunctor`; its convergent tails use `PadicInt.summable_pow_mul`.
-/

public section

open CategoryTheory Opposite TauCeti
namespace TauCeti.Examples.ModuleTower

variable (p : ℕ) [hp : Fact p.Prime]

/-- The tower of ideals pⁿZ_p with their inclusion maps. -/
noncomputable abbrev padicIdealTower : ModuleTower ℤ_[p] :=
  let K : ℕᵒᵈ → Submodule ℤ_[p] ℤ_[p] := fun n =>
    Ideal.span {(p : ℤ_[p]) ^ OrderDual.ofDual n}
  let hK : Monotone K := fun _ _ h =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h)
  let F := TauCeti.ModuleCat.submoduleFunctor K hK
  -- Keep the native ideal carriers while reusing the submodule diagram and its functor laws.
  let G := ((orderDualEquivalence ℕ).inverse ⋙ F).copyObj
    (fun n => ModuleCat.of ℤ_[p] (K (OrderDual.toDual n.unop)))
    (fun n => eqToIso
      (TauCeti.ModuleCat.submoduleFunctor_obj K hK (OrderDual.toDual n.unop)))
  -- Expose the ideal carrier also for subtype coercions at reducible transparency.
  { G with obj n := ModuleCat.of ℤ_[p] (Ideal.span {(p : ℤ_[p]) ^ n.unop}) }

/-- The term at n is the native ideal pⁿZ_p. -/
@[simp]
theorem padicIdealTower_obj (n : ℕ) : (padicIdealTower p).obj (op n) =
    ModuleCat.of ℤ_[p] (Ideal.span {(p : ℤ_[p]) ^ n}) := rfl

/-- Every composite transition is the native submodule inclusion. -/
theorem padicIdealTower_transitionOfLE {n m : ℕ} (h : n ≤ m) :
    (padicIdealTower p).transitionOfLE h = Submodule.inclusion
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : ℤ_[p]) h)) := by
  rw [ModuleTower.transitionOfLE_def]
  exact congrArg ModuleCat.Hom.hom (TauCeti.ModuleCat.submoduleFunctor_map _ _ _)

/-- A single transition is the native inclusion of successive powers. -/
theorem padicIdealTower_transition (n : ℕ) :
    (padicIdealTower p).transition n = Submodule.inclusion
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : ℤ_[p]) n.le_succ)) := by
  rw [← ModuleTower.transitionOfLE_succ, padicIdealTower_transitionOfLE]

/-- Composite transitions preserve the underlying p-adic integer. -/
@[simp]
theorem padicIdealTower_transitionOfLE_coe {n m : ℕ} (h : n ≤ m)
    (x : (padicIdealTower p).obj (op m)) :
    ((padicIdealTower p).transitionOfLE h x : ℤ_[p]) = x := by
  rw [padicIdealTower_transitionOfLE, Submodule.coe_inclusion]

/-- Single transitions preserve the underlying p-adic integer. -/
@[simp]
theorem padicIdealTower_transition_coe (n : ℕ)
    (x : (padicIdealTower p).obj (op (n + 1))) :
    ((padicIdealTower p).transition n x : ℤ_[p]) = x := by
  rw [padicIdealTower_transition, Submodule.coe_inclusion]

/-- The inclusion tower pⁿZ_p is not Mittag–Leffler: its images strictly decrease. -/
theorem not_isMittagLeffler_padicIdealTower : ¬(padicIdealTower p).IsMittagLeffler := by
  intro h
  obtain ⟨N, h0N, hN⟩ := ((padicIdealTower p).isMittagLeffler_iff_ranges.mp h) 0
  have he : (p : ℤ_[p]) ^ N ∈ Ideal.span {(p : ℤ_[p]) ^ N} := Ideal.subset_span (by simp)
  let e : (padicIdealTower p).obj (op N) := ⟨(p : ℤ_[p]) ^ N, he⟩
  have hm : (padicIdealTower p).transitionOfLE h0N e ∈
      LinearMap.range ((padicIdealTower p).transitionOfLE (h0N.trans N.le_succ)) := by
    rw [hN (N + 1) N.le_succ]
    exact LinearMap.mem_range_self _ e
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hm
  have heq : (b : ℤ_[p]) = (p : ℤ_[p]) ^ N := by
    simpa only [padicIdealTower_transitionOfLE_coe p] using congrArg Subtype.val hb
  have hdiv : (p : ℤ_[p]) ^ (N + 1) ∣ (p : ℤ_[p]) ^ N := by
    rw [← heq]
    exact Ideal.mem_span_singleton.mp b.property
  exact (Nat.not_succ_le_self N)
    ((pow_dvd_pow_iff PadicInt.prime_p.ne_zero PadicInt.prime_p.not_isUnit).mp hdiv)

/-- Convergent p-adic tails solve the shift equation, so the inclusion tower has zero lim¹. -/
theorem subsingleton_limOne_padicIdealTower : Subsingleton (padicIdealTower p).limOne := by
  apply (padicIdealTower p).subsingleton_limOne_iff.mpr
  intro a
  have ha (n : ℕ) : (p : ℤ_[p]) ^ n ∣ (a n : ℤ_[p]) :=
    Ideal.mem_span_singleton.mp (a n).property
  choose c hc using ha
  let x (n : ℕ) : ℤ_[p] := ∑' k, (p : ℤ_[p]) ^ k * c (n + k)
  have hs (n : ℕ) : Summable fun k => (p : ℤ_[p]) ^ k * c (n + k) :=
    PadicInt.summable_pow_mul _
  have hx (n : ℕ) : x n = c n + (p : ℤ_[p]) * x (n + 1) := by
    dsimp only [x]
    rw [(hs n).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Nat.add_zero]
    congr 1
    rw [← (hs (n + 1)).tsum_mul_left]
    apply tsum_congr
    intro k
    have hindex : n + (k + 1) = n + 1 + k := by omega
    rw [pow_succ, hindex]
    ring
  let b : (padicIdealTower p).Product := fun n =>
    ⟨(p : ℤ_[p]) ^ n * x n, Ideal.mem_span_singleton.mpr ⟨x n, rfl⟩⟩
  refine ⟨b, funext fun n => Subtype.ext ?_⟩
  rw [ModuleTower.shift_apply, Submodule.coe_sub, padicIdealTower_transition_coe p n]
  dsimp only [b]
  rw [hc n, hx n, pow_succ]
  ring

/-- Zero transitions over F_p give stable images and zero limits, without surjectivity. -/
theorem isMittagLeffler_multiplicationTower_zero :
    (ModuleTower.multiplicationTower (0 : ZMod p)).IsMittagLeffler ∧
    (ModuleTower.multiplicationTower (0 : ZMod p)).shift = LinearMap.id ∧
    (ModuleTower.multiplicationTower (0 : ZMod p)).lim = ⊥ ∧
    Subsingleton (ModuleTower.multiplicationTower (0 : ZMod p)).limOne ∧
    ¬Function.Surjective ((ModuleTower.multiplicationTower (0 : ZMod p)).transition 0) := by
  have h : (ModuleTower.multiplicationTower (0 : ZMod p)).IsProZero :=
    (ModuleTower.isProZero_multiplicationTower_iff (0 : ZMod p)).mpr ⟨1, by simp⟩
  refine ⟨ModuleTower.isMittagLeffler_of_isProZero h, ?_,
    ModuleTower.lim_eq_bot_of_isProZero h, ModuleTower.subsingleton_limOne_of_isProZero h, ?_⟩
  · ext x n
    simp [ModuleTower.shift_apply, ModuleTower.multiplicationTower_transition]
    rfl
  · intro hs
    obtain ⟨x, hx⟩ := hs (1 : ZMod p)
    have hz : (ModuleTower.multiplicationTower (0 : ZMod p)).transition 0 = 0 := by
      rw [ModuleTower.multiplicationTower_transition]
      simp
      rfl
    rw [hz, LinearMap.zero_apply] at hx
    exact (zero_ne_one : (0 : ZMod p) ≠ 1) hx

end TauCeti.Examples.ModuleTower
