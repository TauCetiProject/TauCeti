/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import TauCeti.Dynamics.Entropy.Pressure
public import TauCeti.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import TauCeti.Dynamics.SymbolicDynamics.Shift

/-!
# Pressure of one-coordinate potentials on the one-sided full shift

For a finite nonempty discrete alphabet `α` and `f : α → ℝ`, the potential `x ↦ f (x 0)` on the
one-sided full shift `ℕ → α` has topological pressure `log (∑ a, exp (f a))`. The Birkhoff sum
of the potential over `n` steps is `∑ k < n, f (x k)`, so it only depends on the first `n`
coordinates.

* Upper bound: every entourage contains agreement on the first `c` coordinates for some `c`.
  Two points of a net for this entourage over `n` steps differ in one of the first `n + c`
  coordinates, so the pressure sum is at most the sum over all words of length `n + c`, which is
  `card α ^ c * (∑ a, exp (f a)) ^ n`.
* Lower bound: for agreement at the coordinate `0`, one point for each word of length `n` gives a
  net whose sum is `(∑ a, exp (f a)) ^ n`.

For two symbols with `f 0 = a`, `f 1 = b` this is `log (exp a + exp b)`, and for `f = 0` it is the
topological entropy `log (card α)` of the full shift.

## Main results

* `TauCeti.topologicalPressure_shift_nat_comp_eval_zero`:
  `P(shift 1, f ∘ eval 0) = log (∑ a, exp (f a))`.
* `TauCeti.topologicalPressure_shift_nat_two`: the two-symbol case `log (exp a + exp b)`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth SymbolicDynamics.FullShift
open scoped Uniformity ENNReal

variable {α : Type*}

/-- Agreement on the first `c` coordinates. -/
private def agreeBelow (c : ℕ) : SetRel (ℕ → α) (ℕ → α) := {p | ∀ i < c, p.1 i = p.2 i}

private lemma shift_one_iterate_apply (x : ℕ → α) (k i : ℕ) :
    (shift (1 : ℕ))^[k] x i = x (k + i) := by
  simp

/-- The Birkhoff sums of a one-coordinate potential on the full shift. -/
private lemma birkhoffSum_shift_comp_eval_zero (f : α → ℝ) (n : ℕ) (x : ℕ → α) :
    birkhoffSum (shift (1 : ℕ)) (fun y ↦ f (y 0)) n x = ∑ k ∈ Finset.range n, f (x k) := by
  simp [birkhoffSum, shift_one_iterate_apply]

/-- The weight `exp (birkhoffSum ...)` as a product over the first `n` coordinates. -/
private lemma ofReal_exp_birkhoffSum_shift (f : α → ℝ) (n : ℕ) (x : ℕ → α) :
    ENNReal.ofReal (Real.exp (birkhoffSum (shift (1 : ℕ)) (fun y ↦ f (y 0)) n x)) =
      ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (x k))) := by
  rw [birkhoffSum_shift_comp_eval_zero, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Fin.prod_univ_eq_prod_range]

variable [Fintype α]

/-- Summing the product weights over all words of length `n + c`. -/
private lemma sum_prod_ofReal_exp (f : α → ℝ) (n c : ℕ) :
    ∑ w : Fin (n + c) → α, ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (w (Fin.castAdd c k)))) =
      (Fintype.card α : ℝ≥0∞) ^ c * (∑ a, ENNReal.ofReal (Real.exp (f a))) ^ n := by
  classical
  rw [← (Fin.appendEquiv n c).sum_comp, Fintype.sum_prod_type, Fintype.sum_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Upper bound: the pressure sums at agreement on the first `c` coordinates grow at most like
`card α ^ c * (∑ a, exp (f a)) ^ n`. -/
private lemma pressureNetSum_agreeBelow_le (f : α → ℝ) (c n : ℕ) :
    pressureNetSum (shift (1 : ℕ)) (fun y ↦ f (y 0)) (agreeBelow c) n ≤
      (Fintype.card α : ℝ≥0∞) ^ c * (∑ a, ENNReal.ofReal (Real.exp (f a))) ^ n := by
  classical
  rw [pressureNetSum_le_iff]
  intro s hs
  -- the restriction to the first `n + c` coordinates is injective on a net
  let r : (ℕ → α) → (Fin (n + c) → α) := fun x k ↦ x k
  have hinj : Set.InjOn r s := by
    intro x hx y hy hxy
    by_contra hne
    have hxy' : (x, y) ∈ dynEntourage (shift (1 : ℕ)) (agreeBelow c) n := by
      rw [mem_dynEntourage]
      intro k hk i hi
      simp only [shift_one_iterate_apply]
      exact congrFun hxy ⟨k + i, by omega⟩
    have hyy : (y, y) ∈ dynEntourage (shift (1 : ℕ)) (agreeBelow c) n :=
      mem_dynEntourage.mpr fun _ _ _ _ ↦ rfl
    exact Set.disjoint_left.mp (hs.2 hx hy hne) (show y ∈ _ by simpa using hxy')
      (show y ∈ _ by simpa using hyy)
  calc ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum (shift (1 : ℕ)) (fun y ↦ f (y 0)) n x))
      = ∑ x ∈ s, ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (r x (Fin.castAdd c k)))) :=
        Finset.sum_congr rfl fun x _ ↦ ofReal_exp_birkhoffSum_shift f n x
    _ = ∑ w ∈ s.image r, ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (w (Fin.castAdd c k)))) :=
        (Finset.sum_image (f := fun w : Fin (n + c) → α ↦
          ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (w (Fin.castAdd c k)))))
          fun x hx y hy h ↦ hinj hx hy h).symm
    _ ≤ ∑ w : Fin (n + c) → α, ∏ k : Fin n, ENNReal.ofReal (Real.exp (f (w (Fin.castAdd c k)))) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := sum_prod_ofReal_exp f n c

variable [Nonempty α]

/-- Lower bound: at agreement on the coordinate `0`, the pressure sums are at least
`(∑ a, exp (f a)) ^ n`. -/
private lemma pow_le_pressureNetSum_agreeBelow_one (f : α → ℝ) (n : ℕ) :
    (∑ a, ENNReal.ofReal (Real.exp (f a))) ^ n ≤
      pressureNetSum (shift (1 : ℕ)) (fun y ↦ f (y 0)) (agreeBelow 1) n := by
  classical
  let e : (Fin n → α) → (ℕ → α) := fun w i ↦ if h : i < n then w ⟨i, h⟩ else Classical.arbitrary α
  have he : ∀ w (k : Fin n), e w k = w k := fun w k ↦ by simp [e, k.isLt]
  have heinj : Function.Injective e := fun w w' h ↦ funext fun k ↦ by
    rw [← he w k, ← he w' k, h]
  have hnet : IsDynNetIn (shift (1 : ℕ)) univ (agreeBelow 1) n
      ((Finset.univ.image e : Finset (ℕ → α)) : Set (ℕ → α)) := by
    refine ⟨subset_univ _, fun x hx y hy hne ↦ Set.disjoint_left.mpr fun z hzx hzy ↦ hne ?_⟩
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_range] at hx hy
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    congr 1
    refine funext fun k ↦ ?_
    have h1 := (mem_dynEntourage.mp hzx) k k.isLt 0 one_pos
    have h2 := (mem_dynEntourage.mp hzy) k k.isLt 0 one_pos
    simp only [shift_one_iterate_apply, add_zero] at h1 h2
    rw [← he w k, ← he w' k]
    exact h1.trans h2.symm
  refine le_trans (le_of_eq ?_) hnet.sum_le_pressureNetSum
  rw [Finset.sum_image fun w _ w' _ h ↦ heinj h]
  simp only [ofReal_exp_birkhoffSum_shift, he]
  exact Fintype.sum_pow _ n

variable [UniformSpace α] [DiscreteUniformity α]

/-- **Pressure of a one-coordinate potential on the full shift.** For a finite nonempty discrete
alphabet `α` and `f : α → ℝ`, the potential `x ↦ f (x 0)` on the one-sided full shift has
topological pressure `log (∑ a, exp (f a))`. -/
theorem topologicalPressure_shift_nat_comp_eval_zero (f : α → ℝ) :
    topologicalPressure (shift (1 : ℕ)) (fun x : ℕ → α ↦ f (x 0)) =
      Real.log (∑ a, Real.exp (f a)) := by
  have hZ : (∑ a, ENNReal.ofReal (Real.exp (f a))) = ENNReal.ofReal (∑ a, Real.exp (f a)) :=
    (ENNReal.ofReal_sum_of_nonneg fun a _ ↦ (Real.exp_pos _).le).symm
  have hpos : 0 < ∑ a, Real.exp (f a) :=
    Finset.sum_pos (fun a _ ↦ Real.exp_pos _) Finset.univ_nonempty
  rw [← ENNReal.log_ofReal_of_pos hpos, ← hZ, ← expGrowthSup_pow]
  refine le_antisymm (topologicalPressure_le_iff.mpr fun U hU ↦ ?_) ?_
  · obtain ⟨S, hS, hSU⟩ := Pi.hasBasis_uniformity_of_discreteUniformity.mem_iff.mp hU
    obtain ⟨c, hc⟩ := hS.bddAbove
    have hsub : (agreeBelow (c + 1) : SetRel (ℕ → α) (ℕ → α)) ⊆ U := fun p hp ↦
      hSU fun i hi ↦ hp i (Nat.lt_succ_of_le (hc hi))
    refine (netPressureEntourage_antitone _ _ hsub).trans ?_
    rw [netPressureEntourage_def]
    exact expGrowthSup_le_of_eventually_le (by simp)
      (Eventually.of_forall (pressureNetSum_agreeBelow_le f (c + 1)))
  · have hU : (agreeBelow 1 : SetRel (ℕ → α) (ℕ → α)) ∈ 𝓤 (ℕ → α) :=
      Pi.hasBasis_uniformity_of_discreteUniformity.mem_iff.mpr ⟨{0}, finite_singleton 0,
        fun p hp i hi ↦ hp i (by simpa using hi)⟩
    refine le_trans ?_ (netPressureEntourage_le_topologicalPressure hU)
    rw [netPressureEntourage_def]
    exact expGrowthSup_monotone (pow_le_pressureNetSum_agreeBelow_one f)

/-- **The two-symbol Check.** On the one-sided full shift on two symbols, the potential equal to
`a` where the first symbol is `false` and to `b` where it is `true` has pressure
`log (exp a + exp b)`. -/
theorem topologicalPressure_shift_nat_two (a b : ℝ) :
    topologicalPressure (shift (1 : ℕ)) (fun x : ℕ → Bool ↦ if x 0 then b else a) =
      Real.log (Real.exp a + Real.exp b) := by
  rw [topologicalPressure_shift_nat_comp_eval_zero (fun c : Bool ↦ if c then b else a)]
  simp [add_comm]

end TauCeti
