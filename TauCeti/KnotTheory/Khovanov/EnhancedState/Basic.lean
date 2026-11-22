/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.KnotTheory.PDCode.Jones.Basic
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Basic

/-!
# Enhanced states and the Jones polynomial

An enhanced state of a PD-code is a state `s` together with a label `1` or `X` on every circle of
the diagram smoothed according to `s`. The enhanced states form the standard basis of the
Khovanov chain groups (Bar-Natan §1), and this file fixes their bigrading. A state selects
the `B`-smoothing at the crossings `S` where it is `false`. For an oriented code with `n₊` positive
and `n₋` negative crossings, the enhanced state has cochain degree `|S| - n₋`. Its quantum degree
is `|S| + n₊ - 2 n₋` plus `1` for each circle labelled `1` and minus `1` for each circle labelled
`X` (`TauCeti.OrientedPDCode.stateCochainDegree`, `TauCeti.OrientedPDCode.enhancedQuantumDegree`).

The signed count of enhanced states by bidegree is the sum
`TauCeti.OrientedPDCode.enhancedStateSum` of `(-1) ^ i q ^ j` over all enhanced states; here the
generator `T` of `ℤ[T;T⁻¹]` plays the role of `q`. With `Cⁱʲ` the Khovanov chain group, the free
module on the enhanced states of bidegree `(i, j)`, this sum is the graded Euler characteristic
`∑ (-1) ^ i q ^ j rank Cⁱʲ`.
This file proves that, for a nonempty diagram, this sum is the Jones polynomial in Khovanov's
normalization: with the substitution `t ^ (1/2) ↦ -q`, it is `(q + q⁻¹)` times
`TauCeti.OrientedPDCode.jonesPolynomial`
(`TauCeti.OrientedPDCode.enhancedStateSum_eq_mul_eval₂_jonesPolynomial`).

The proof is a state-by-state comparison. Summing over the labels of the `k` circles of a state
gives `(q + q⁻¹) ^ k`. The substitution turns the Jones weight of a state into the signed monomial
`(-1) ^ (|S| - n₋) q ^ (|S| + n₊ - 2 n₋)`, crossing by crossing. The Jones state sum raises the
loop value only to the truncated power `k - 1`, so the extra factor `q + q⁻¹` completes it to the
`k`-th power exactly when every state has a circle, that is, when the diagram is nonempty. The
empty diagram has a single enhanced state and sum `1`
(`TauCeti.OrientedPDCode.enhancedStateSum_empty`). More generally, a diagram without crossings
and with `c` circles has sum `(q + q⁻¹) ^ c` (`TauCeti.OrientedPDCode.enhancedStateSum_eq_pow`).

Specializing at `q = 1` gives the normalized enhanced-state Euler sum
`TauCeti.OrientedPDCode.enhancedStateEulerSum`, `E(D) = ∑_s (-1) ^ (|S| + n₋) 2 ^ k(s)`
(`TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum`), together with its crossing-free values and
basic diagram symmetries (`reverse`, `rotateCrossing`, `mirror`, `relabel`).

## Main definitions

* `TauCeti.PDCode.EnhancedState`: a state with a `1`/`X` label on every resolved circle.
* `TauCeti.Khovanov.labelingQuantumDegree`: the quantum degree contributed by the circle labels.
* `TauCeti.OrientedPDCode.stateCochainDegree`: the cochain degree `|S| - n₋` of a state.
* `TauCeti.OrientedPDCode.stateQuantumShift`: the quantum shift `|S| + n₊ - 2 n₋` of a state.
* `TauCeti.OrientedPDCode.enhancedQuantumDegree`: the quantum degree of an enhanced state.
* `TauCeti.OrientedPDCode.enhancedStateSum`: the signed sum of `q ^ j` over all enhanced states.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum`: the `q = 1` specialization
  `∑_s (-1) ^ (|S| + n₋) 2 ^ k(s)` of the enhanced state sum.

## Main results

* `TauCeti.Khovanov.sum_T_labelingQuantumDegree`: the labellings of `k` circles, counted by quantum
  degree, give `(q + q⁻¹) ^ k`.
* `TauCeti.OrientedPDCode.enhancedStateSum_eq_sum`: the sum over enhanced states as a sum over
  states, with `(q + q⁻¹) ^ k` for a state with `k` circles.
* `TauCeti.OrientedPDCode.eval₂_neg_genericUnit_jonesStateWeight`: at `t ^ (1/2) = -q` the Jones
  weight of a state is `(-1) ^ (|S| - n₋) q ^ (|S| + n₊ - 2 n₋)`.
* `TauCeti.OrientedPDCode.enhancedStateSum_eq_mul_eval₂_jonesPolynomial`: for a nonempty diagram
  the enhanced state sum is `(q + q⁻¹)` times the Jones polynomial at `t ^ (1/2) = -q`.
* `TauCeti.OrientedPDCode.enhancedStateSum_eq_pow`, `TauCeti.OrientedPDCode.enhancedStateSum_empty`:
  the crossing-free diagrams, including the empty one.
* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum`: evaluating `enhancedStateSum` at `q = 1`
  yields `enhancedStateEulerSum`.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_of_zero`,
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_empty`,
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_unknot`: crossing-free values of
  `enhancedStateEulerSum`.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_reverse`,
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_rotateCrossing`,
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_mirror`,
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_relabel`: invariance of `enhancedStateEulerSum`
  under basic diagram symmetries.
* `TauCeti.enhancedStateSum_rightHandedTrefoilPDCode`: the right-handed trefoil has enhanced state
  sum `q + q³ + q⁵ - q⁹`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337-370, §1 (enhanced states, the bigrading, and the unnormalized Jones polynomial
  `(q + q⁻¹) J`).
-/

public section

namespace TauCeti

open LaurentPolynomial Finset

namespace PDCode

variable {n : ℕ}

/-- An enhanced state of a PD-code: a state `s`, together with a label on every circle of the
diagram smoothed according to `s`. The label `false` stands for the generator `1` and `true` for
the generator `X` of the rank-two Khovanov module. -/
abbrev EnhancedState (D : PDCode n) : Type :=
  Σ s : Fin n → Bool, D.ResolvedCircle s → Bool

end PDCode

namespace Khovanov

variable {ι : Type*} [Fintype ι]

variable (ι) in
/-- The quantum degree of a labelling of the circles: `+1` for each circle labelled `1` and `-1`
for each circle labelled `X`. -/
def labelingQuantumDegree (l : ι → Bool) : ℤ :=
  ∑ i, bif l i then -1 else 1

/-- The defining sum of the quantum degree of a labelling. -/
theorem labelingQuantumDegree_def (l : ι → Bool) :
    labelingQuantumDegree ι l = ∑ i, bif l i then -1 else 1 := (rfl)

/-- Complementary labellings have opposite quantum degrees. -/
@[simp]
theorem labelingQuantumDegree_not (l : ι → Bool) :
    labelingQuantumDegree ι (fun i ↦ !l i) = -labelingQuantumDegree ι l := by
  rw [labelingQuantumDegree_def, labelingQuantumDegree_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by cases l i <;> rfl

/-- The quantum degree of a labelling is the number of circles minus twice the number of
`X`-labels. -/
theorem labelingQuantumDegree_eq (l : ι → Bool) :
    labelingQuantumDegree ι l = Fintype.card ι - 2 * #{i | l i = true} := by
  rw [labelingQuantumDegree_def, Finset.natCast_card_filter, Finset.mul_sum, Fintype.card,
    Finset.cast_card, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by cases l i <;> simp

/-- The quantum degree of a labelling of `k` circles lies between `-k` and `k`. -/
theorem abs_labelingQuantumDegree_le (l : ι → Bool) :
    |labelingQuantumDegree ι l| ≤ Fintype.card ι := by
  have h := Finset.card_filter_le (Finset.univ : Finset ι) (fun i ↦ l i = true)
  rw [Finset.card_univ] at h
  rw [labelingQuantumDegree_eq, abs_le]
  constructor <;> omega

/-- **The graded count of labellings**: labelling `k` circles by `1` or `X` in all possible ways
gives `∑ q ^ (quantum degree) = (q + q⁻¹) ^ k`. -/
theorem sum_T_labelingQuantumDegree [DecidableEq ι] :
    ∑ l : ι → Bool, (T (labelingQuantumDegree ι l) : ℤ[T;T⁻¹]) =
      (T 1 + T (-1)) ^ Fintype.card ι := by
  simp_rw [labelingQuantumDegree_def, T_sum]
  rw [← Fintype.prod_sum fun _ (b : Bool) ↦ (T (bif b then -1 else 1) : ℤ[T;T⁻¹]),
    ← Finset.card_univ, ← Finset.prod_const]
  simp [add_comm]

/-- Relabelling a circle from `1` to `X` lowers the quantum degree by two. -/
theorem labelingQuantumDegree_update_true [DecidableEq ι] {l : ι → Bool} {i : ι}
    (hi : l i = false) :
    labelingQuantumDegree ι (Function.update l i true) = labelingQuantumDegree ι l - 2 := by
  have hne : ∀ j ∈ ({i}ᶜ : Finset ι),
      (bif Function.update l i true j then (-1 : ℤ) else 1) = bif l j then -1 else 1 :=
    fun j hj ↦ by rw [Function.update_of_ne (by simpa using hj)]
  rw [labelingQuantumDegree_def, labelingQuantumDegree_def, Fintype.sum_eq_add_sum_compl i,
    Fintype.sum_eq_add_sum_compl i (fun j ↦ bif l j then -1 else 1), Finset.sum_congr rfl hne]
  simp only [Function.update_self, hi, Bool.cond_true, Bool.cond_false]
  ring

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

/-- When no fibre of `f` carries two `X`-labels of `l`, merging along `f` changes the quantum degree
of `l` by `|τ| - |σ|`. -/
theorem labelingQuantumDegree_merge {f : σ → τ} {l : σ → Bool}
    (h : ∀ j, #{i | f i = j ∧ l i = true} ≤ 1) :
    labelingQuantumDegree τ (fun j ↦ decide (∃ i, f i = j ∧ l i = true)) =
      labelingQuantumDegree σ l + (Fintype.card τ - Fintype.card σ) := by
  -- The circles of `τ` labelled `X` are the images of those of `σ`, on which `f` is injective.
  have himage : ({j | decide (∃ i, f i = j ∧ l i = true) = true} : Finset τ) =
      Finset.image f {i | l i = true} := by
    ext j
    simp [and_comm]
  have hinj : Set.InjOn f ({i | l i = true} : Finset σ) := by
    intro i hi i' hi' hii'
    exact Finset.card_le_one.mp (h (f i)) i (by simpa using hi) i'
      (by simpa [hii'] using hi')
  rw [labelingQuantumDegree_eq, labelingQuantumDegree_eq, himage,
    Finset.card_image_of_injOn hinj]
  ring

end Khovanov

namespace OrientedPDCode

variable {n : ℕ}

/-- The cochain degree `|S| - n₋` of a state `s` of an oriented code, where `S` is the set of
crossings at which `s` selects the `B`-smoothing, that is, where `s` is `false`. -/
def stateCochainDegree (D : OrientedPDCode n) (s : Fin n → Bool) : ℤ :=
  #{i | s i = false} - D.negativeCrossingCount

/-- The defining formula of the cochain degree of a state. -/
theorem stateCochainDegree_def (D : OrientedPDCode n) (s : Fin n → Bool) :
    D.stateCochainDegree s = #{i | s i = false} - D.negativeCrossingCount := (rfl)

/-- The cochain-degree sign `(-1) ^ (|s| - n₋)` equals `(-1) ^ (|s| + n₋)`. -/
theorem coe_negOnePow_stateCochainDegree (D : OrientedPDCode n) (s : Fin n → Bool) :
    ((D.stateCochainDegree s).negOnePow : ℤ) =
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) := by
  rw [D.stateCochainDegree_def, Int.negOnePow_sub, ← Int.negOnePow_add, ← Nat.cast_add,
    Int.coe_negOnePow_natCast]

/-- The quantum shift `|S| + n₊ - 2 n₋` of a state `s` of an oriented code, where `S` is the set
of crossings at which `s` selects the `B`-smoothing. -/
def stateQuantumShift (D : OrientedPDCode n) (s : Fin n → Bool) : ℤ :=
  #{i | s i = false} + D.positiveCrossingCount - 2 * D.negativeCrossingCount

/-- The defining formula of the quantum shift of a state. -/
theorem stateQuantumShift_def (D : OrientedPDCode n) (s : Fin n → Bool) :
    D.stateQuantumShift s =
      #{i | s i = false} + D.positiveCrossingCount - 2 * D.negativeCrossingCount := (rfl)

/-- The quantum degree of an enhanced state: the quantum shift of its state, plus `1` for each
circle labelled `1` and minus `1` for each circle labelled `X`. -/
def enhancedQuantumDegree (D : OrientedPDCode n) (e : D.toPDCode.EnhancedState) : ℤ :=
  D.stateQuantumShift e.1 + Khovanov.labelingQuantumDegree _ e.2

/-- The defining formula of the quantum degree of an enhanced state. -/
theorem enhancedQuantumDegree_def (D : OrientedPDCode n) (e : D.toPDCode.EnhancedState) :
    D.enhancedQuantumDegree e =
      D.stateQuantumShift e.1 + Khovanov.labelingQuantumDegree _ e.2 := (rfl)

/-- **The enhanced state sum** of an oriented code: the sum of `(-1) ^ i q ^ j` over all enhanced
states, where `i` is the cochain degree and `j` the quantum degree, with `q = T`; that is, the
signed count of enhanced states by bidegree. With `Cⁱʲ` the free module on the enhanced states of
bidegree `(i, j)`, this is the graded Euler characteristic `∑ (-1) ^ i q ^ j rank Cⁱʲ`. -/
noncomputable def enhancedStateSum (D : OrientedPDCode n) : ℤ[T;T⁻¹] :=
  ∑ e : D.toPDCode.EnhancedState,
    (D.stateCochainDegree e.1).negOnePow • T (D.enhancedQuantumDegree e)

/-- The defining sum of the enhanced state sum. -/
theorem enhancedStateSum_def (D : OrientedPDCode n) :
    D.enhancedStateSum = ∑ e : D.toPDCode.EnhancedState,
      (D.stateCochainDegree e.1).negOnePow • T (D.enhancedQuantumDegree e) := (rfl)

/-- **The enhanced state sum as a sum over states**: the labels of the `k` circles of a state
contribute `(q + q⁻¹) ^ k` to the signed monomial `(-1) ^ (|S| - n₋) q ^ (|S| + n₊ - 2 n₋)` of
the state. -/
theorem enhancedStateSum_eq_sum (D : OrientedPDCode n) :
    D.enhancedStateSum = ∑ s : Fin n → Bool,
      (D.stateCochainDegree s).negOnePow • T (D.stateQuantumShift s) *
        (T 1 + T (-1)) ^ D.stateLoopCount s := by
  rw [enhancedStateSum_def, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp_rw [enhancedQuantumDegree_def, T_add, ← smul_mul_assoc, ← Finset.mul_sum,
    Khovanov.sum_T_labelingQuantumDegree, PDCode.card_resolvedCircle]

/-- The cochain degree of a state is the sum over the crossings of `1` for a `B`-smoothing, minus
`1` for a negative crossing. -/
private theorem stateCochainDegree_eq_sum (D : OrientedPDCode n) (s : Fin n → Bool) :
    D.stateCochainDegree s =
      ∑ i, ((bif s i then 0 else 1) - (if D.crossingSign i = 1 then 0 else 1)) := by
  rw [stateCochainDegree_def, negativeCrossingCount_def, Finset.natCast_card_filter,
    Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> cases s i <;> simp [h]

/-- The quantum shift of a state is the sum of the exponents of `t ^ (1/2)` in its Jones weight. -/
private theorem stateQuantumShift_eq_sum (D : OrientedPDCode n) (s : Fin n → Bool) :
    D.stateQuantumShift s =
      ∑ i, (if D.crossingSign i = 1 then bif s i then 1 else 2 else bif s i then -2 else -1) := by
  rw [stateQuantumShift_def, positiveCrossingCount_def, negativeCrossingCount_def,
    Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> cases s i <;> simp [h]

/-- **The Jones weight of a state at `t ^ (1/2) = -q`** is the signed monomial
`(-1) ^ (|S| - n₋) q ^ (|S| + n₊ - 2 n₋)`. Crossing by crossing, a positive crossing contributes
`q` to a state that smooths it by `A` and `-q²` to one that smooths it by `B`, and a negative
crossing contributes `-q⁻²` and `q⁻¹`. -/
theorem eval₂_neg_genericUnit_jonesStateWeight (D : OrientedPDCode n) (s : Fin n → Bool) :
    eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) (D.jonesStateWeight s) =
      (D.stateCochainDegree s).negOnePow • T (D.stateQuantumShift s) := by
  rw [Units.smul_def, zsmul_eq_mul, ← negOnePowCast_eq_intCast, stateCochainDegree_eq_sum,
    stateQuantumShift_eq_sum, negOnePowCast_sum, T_sum, ← Finset.prod_mul_distrib,
    jonesStateWeight_def, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> cases s i <;>
    simp [h]

/-- **The enhanced state sum of a nonempty diagram is `(q + q⁻¹)` times its Jones polynomial at
`t ^ (1/2) = -q`.** The hypothesis `0 < componentCount` says that the diagram is nonempty; it
excludes the empty diagram, whose enhanced state sum is `1`. -/
theorem enhancedStateSum_eq_mul_eval₂_jonesPolynomial (D : OrientedPDCode n)
    (h : 0 < D.toPDCode.componentCount) :
    D.enhancedStateSum =
      (T 1 + T (-1)) * eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial := by
  -- At `t ^ (1/2) = -q`, the Jones loop value `-(t ^ (1/2) + t ^ (-1/2))` becomes `q + q⁻¹`.
  have hloop : eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) (-(T 1 + T (-1)) : ℤ[T;T⁻¹]) =
      T 1 + T (-1) := by
    simp [add_comm]
  rw [enhancedStateSum_eq_sum, jonesPolynomial_def, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_pow, eval₂_neg_genericUnit_jonesStateWeight, hloop,
    mul_left_comm, mul_pow_sub_one (Nat.one_le_iff_ne_zero.mp
      (D.toPDCode.one_le_stateLoopCount_of_componentCount_pos h s))]

/-- **A diagram without crossings has enhanced state sum `(q + q⁻¹) ^ c`**, where `c` is the
number of its crossing-free circles. -/
theorem enhancedStateSum_eq_pow (D : OrientedPDCode 0) :
    D.enhancedStateSum = (T 1 + T (-1)) ^ D.crossinglessComponentCount := by
  rw [enhancedStateSum_eq_sum, Fintype.sum_unique]
  simp [stateCochainDegree_def, stateQuantumShift_def, negativeCrossingCount_def,
    positiveCrossingCount_def]

/-- **The empty diagram has enhanced state sum `1`**: its only enhanced state is the empty state
with no circles, in bidegree `(0, 0)`. -/
@[simp]
theorem enhancedStateSum_empty : empty.enhancedStateSum = 1 := by
  rw [enhancedStateSum_eq_pow, ← card_crossinglessComponents, crossinglessComponents_empty]
  simp

/-- The unknot has enhanced state sum `q + q⁻¹`. -/
@[simp]
theorem enhancedStateSum_unknot (orientation : Bool) :
    (unknot orientation).enhancedStateSum = T 1 + T (-1) := by
  rw [enhancedStateSum_eq_pow, ← card_crossinglessComponents, crossinglessComponents_unknot]
  simp

/-! ### The normalized enhanced-state Euler sum (`q = 1`) -/

/-- **The normalized enhanced-state Euler sum** `E(D) = ∑_s (-1) ^ (|s| + n₋) 2 ^ k(s)` of an
oriented PD-code `D`, where `|s| = #{i | s i = false}` counts the `B`-smoothings in `s`, `n₋` is
`D.negativeCrossingCount`, and `k(s)` is `D.toPDCode.stateLoopCount s`. -/
noncomputable def enhancedStateEulerSum (D : OrientedPDCode n) : ℤ :=
  ∑ s : Fin n → Bool,
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) * 2 ^ D.toPDCode.stateLoopCount s

/-- Defining sum of `TauCeti.OrientedPDCode.enhancedStateEulerSum`. -/
theorem enhancedStateEulerSum_def (D : OrientedPDCode n) :
    D.enhancedStateEulerSum = ∑ s : Fin n → Bool,
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
        2 ^ D.toPDCode.stateLoopCount s := (rfl)

/-- **Evaluating the enhanced state sum at `q = 1`** yields the normalized enhanced-state Euler
sum `E(D)`, without any planarity assumption. -/
@[simp] theorem eval₂_one_enhancedStateSum (D : OrientedPDCode n) :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = D.enhancedStateEulerSum := by
  rw [D.enhancedStateSum_eq_sum, D.enhancedStateEulerSum_def, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul, map_mul, map_mul, map_intCast, map_pow, map_add,
    eval₂_T, eval₂_T, eval₂_T, D.coe_negOnePow_stateCochainDegree s]
  norm_num

/-- **A crossing-free diagram with `c` circles has `E(D) = 2 ^ c`.** -/
theorem enhancedStateEulerSum_of_zero (D : OrientedPDCode 0) :
    D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount := by
  rw [← D.eval₂_one_enhancedStateSum, D.enhancedStateSum_eq_pow, PDCode.componentCount_eq,
    PDCode.crossingComponentCount_eq_zero, zero_add, map_pow, map_add, eval₂_T, eval₂_T]
  norm_num

/-- The empty diagram has enhanced-state Euler sum `1`. -/
@[simp] theorem enhancedStateEulerSum_empty : empty.enhancedStateEulerSum = 1 := by
  rw [← empty.eval₂_one_enhancedStateSum, enhancedStateSum_empty, map_one]

/-- Either orientation of the crossing-free unknot has enhanced-state Euler sum `2`. -/
@[simp] theorem enhancedStateEulerSum_unknot (o : Bool) :
    (unknot o).enhancedStateEulerSum = 2 := by
  rw [← (unknot o).eval₂_one_enhancedStateSum, enhancedStateSum_unknot, map_add, eval₂_T, eval₂_T]
  norm_num

/-- Reversing all component orientations preserves `E(D)`. -/
@[simp] theorem enhancedStateEulerSum_reverse (D : OrientedPDCode n) :
    D.reverse.enhancedStateEulerSum = D.enhancedStateEulerSum := by
  simp [enhancedStateEulerSum_def]

/-- Reading a crossing from its next slot preserves `E(D)`. -/
@[simp] theorem enhancedStateEulerSum_rotateCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.rotateCrossing i).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  simp [enhancedStateEulerSum_def, negativeCrossingCount_def]

/-- Mirroring an oriented PD-code preserves `E(D)`, without any planarity assumption. -/
@[simp] theorem enhancedStateEulerSum_mirror (D : OrientedPDCode n) :
    D.mirror.enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def]
  refine Fintype.sum_bijective (fun s i ↦ !s i)
    (Function.Involutive.bijective fun s ↦ by funext i; simp) _ _ fun s ↦ ?_
  have hcard : #{j | (!s j) = false} + #{j | s j = false} = n := by
    have htrue : #{j | (!s j) = false} = #{j | ¬(s j = false)} := by
      refine congrArg card (Finset.ext fun j ↦ ?_)
      simp
    rw [htrue, add_comm, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hn := D.positiveCrossingCount_add_negativeCrossingCount
  have hsign : (-1 : ℤ) ^ (#{j | s j = false} + D.mirror.negativeCrossingCount) =
      (-1 : ℤ) ^ (#{j | (!s j) = false} + D.negativeCrossingCount) := by
    rw [negativeCrossingCount_mirror]
    exact neg_one_pow_congr (by simp only [Nat.even_iff]; omega)
  rw [hsign, mirror_toPDCode, D.toPDCode.stateLoopCount_mirror]

/-- Relabelling half-edges and crossings preserves `E(D)`. -/
@[simp] theorem enhancedStateEulerSum_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def,
    ← (Equiv.arrowCongr cross (Equiv.refl Bool)).sum_comp]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hcard : #{j | Equiv.arrowCongr cross (Equiv.refl Bool) s j = false} =
      #{j | s j = false} :=
    Finset.card_equiv cross.symm fun j ↦ by simp [Equiv.arrowCongr_apply]
  have hloop : (D.relabel half cross).toPDCode.stateLoopCount
      (Equiv.arrowCongr cross (Equiv.refl Bool) s) = D.toPDCode.stateLoopCount s := by
    rw [relabel_toPDCode, PDCode.stateLoopCount_relabel]
    congr 1
    ext j
    simp [Equiv.arrowCongr_apply]
  rw [hcard, negativeCrossingCount_relabel, hloop]

end OrientedPDCode

/-- **The enhanced state sum of the right-handed trefoil** is `q + q³ + q⁵ - q⁹`. This agrees with
Khovanov's computation of its homology, whose free summands lie in bidegrees `(0, 1)`, `(0, 3)`,
`(2, 5)` and `(3, 9)`. -/
theorem enhancedStateSum_rightHandedTrefoilPDCode :
    rightHandedTrefoilPDCode.enhancedStateSum = T 1 + T 3 + T 5 - T 9 := by
  rw [OrientedPDCode.enhancedStateSum_eq_mul_eval₂_jonesPolynomial _
      (PDCode.componentCount_pos _ three_ne_zero), jonesPolynomial_rightHandedTrefoilPDCode]
  simp only [map_add, map_sub, eval₂_T, Even.neg_zpow (by decide : Even (2 : ℤ)),
    Even.neg_zpow (by decide : Even (6 : ℤ)), Even.neg_zpow (by decide : Even (8 : ℤ)),
    genericUnit_zpow_val, add_mul, mul_add, mul_sub, ← T_add]
  norm_num
  abel

end TauCeti
