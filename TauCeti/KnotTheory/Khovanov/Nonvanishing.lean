/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.PDCode.Oriented.ResolveCrossing
import TauCeti.KnotTheory.Khovanov.Parity

/-!
# The ungraded Euler state sum and nonvanishing of Khovanov homology

Specializing the enhanced state sum `TauCeti.OrientedPDCode.enhancedStateSum` of an oriented
PD-code `D` at `q = 1` gives the normalized ungraded Euler state sum

`E(D) = ∑ₛ (-1) ^ (|S| + n₋) 2 ^ k(s)` (`TauCeti.OrientedPDCode.normalizedEulerSum`),

where `S` is the set of `B`-smoothed crossings (`s i = false`), `n₋` is the number of negative
crossings, and `k(s)` is the number of circles in the state `s`. Because `|S| + n₋` and the
cochain degree `|S| - n₋` have the same parity, `E(D)` is the sum of all coefficients of
`D.enhancedStateSum`, and over a Noetherian ring with the rank-nullity property it is also the
evaluation at `q = 1` of the graded Euler characteristic `D.khovanovEulerChar hD R`.

Switching a single crossing exchanges its `A`- and `B`-smoothings while flipping both `(-1) ^ |S|`
and `(-1) ^ n₋`, so `E(D)` is invariant under crossing changes without any planarity hypothesis
(`TauCeti.OrientedPDCode.normalizedEulerSum_changeCrossing`).

When `D` is planar, quantum-degree parity
(`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two`)
determines the change of `n₋` modulo two between `D` and any oriented code realizing either
resolution of a crossing `c`: for arbitrary oriented resolutions `D₀` (`A`-smoothing) and `D₁`
(`B`-smoothing),

`E(D) = -(-1) ^ c [(-1) ^ c₀ E(D₀) + (-1) ^ c₁ E(D₁)]`,

where `c`, `c₀`, `c₁` are the component counts of `D`, `D₀`, `D₁`
(`TauCeti.OrientedPDCode.normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing`). Combining this
recurrence with the concrete oriented resolutions `TauCeti.OrientedPDCode.resolveCrossingOriented`
and the component-count dichotomy `TauCeti.OrientedPDCode.componentCount_resolveCrossing_dichotomy`
proves by induction on the number of crossings that

`E(D) = 2 ^ c` (`TauCeti.OrientedPDCode.normalizedEulerSum_eq_two_pow`)

for every planar oriented PD-code `D`, including the empty diagram (`c = 0`). For a nonempty planar
oriented diagram (`0 < c`), comparing with `(q + q⁻¹) J(D)|_{t ^ (1/2) = -q}` recovers the classical
evaluation `J(D)|_{t ^ (1/2) = -1} = 2 ^ (c - 1)`
(`TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`).

Finally, since `2 ^ c ≠ 0` in `ℤ`, the graded Euler characteristic `χ_q Kh(D; R)` is nonzero over
every nontrivial Noetherian commutative ring `R` with the rank-nullity property. Together with the
vanishing of `Khⁱʲ(D; R)` outside `[-n₋, n₊]` in cochain degree and outside quantum degrees of the
parity of `c` (`TauCeti.OrientedPDCode.isZero_khovanovHomology_of_mod_two_ne`), this shows that
every planar oriented link diagram—including the empty diagram—has a bidegree `(i, j)` with
`i ∈ [-n₋, n₊]`, `j ≡ c (mod 2)`, and `0 < Module.finrank R (D.khovanovHomology hD R i j)`, hence
nontrivial Khovanov homology over `R` (and in particular over `ℤ` and `ℚ`).

## Main definitions

* `TauCeti.OrientedPDCode.normalizedEulerSum`: the normalized ungraded Euler state sum
  `E(D) = ∑ₛ (-1) ^ (|S| + n₋) 2 ^ k(s)` of an oriented PD-code.

## Main results

* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum`: evaluating `D.enhancedStateSum` at `q = 1`
  yields `D.normalizedEulerSum`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_changeCrossing`: `E(D)` is invariant under switching a
  single crossing.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_resolveCrossing`: unnormalized resolution formula
  for `E(D)` at a crossing, without planarity.
* `TauCeti.OrientedPDCode.negOnePow_negativeCrossingCount_sub_resolveCrossing`: planar parity law
  relating `n₋(D) - n₋(E)` and `c(D) + c(E)` modulo two for any oriented resolution `E`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing`,
  `TauCeti.OrientedPDCode.normalizedEulerSum_resolveCrossingOriented`: normalized planar recurrence
  `E(D) = -(-1) ^ c [(-1) ^ c₀ E(D₀) + (-1) ^ c₁ E(D₁)]`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_two_pow`: `E(D) = 2 ^ D.componentCount` for every
  planar oriented PD-code `D`.
* `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`: for a nonempty planar oriented PD-code,
  evaluating `D.jonesPolynomial` at `-1` gives `2 ^ (D.componentCount - 1)`.
* `TauCeti.OrientedPDCode.isZero_khovanovHomology_of_mod_two_ne`: `Khⁱʲ(D; R)` vanishes whenever
  `j % 2 ≠ D.componentCount % 2`, over any commutative ring `R`.
* `TauCeti.OrientedPDCode.khovanovEulerChar_ne_zero`,
  `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos`,
  `TauCeti.OrientedPDCode.exists_nontrivial_khovanovHomology`: nonvanishing of the graded Euler
  characteristic and of Khovanov homology over nontrivial Noetherian rings with rank-nullity, with
  explicit specializations to `ℤ` and `ℚ`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370, §§1–2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset HomologicalComplex LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

section NormalizedEulerSum

variable {n : ℕ}

/-- **The normalized ungraded Euler state sum** of an oriented PD-code `D`:
`E(D) = ∑ₛ (-1) ^ (|S| + n₋) 2 ^ k(s)`, where `S = {i | s i = false}` is the set of `B`-smoothed
crossings, `n₋` is the number of negative crossings, and `k(s)` is the number of circles in the
smoothed state `s`. -/
def normalizedEulerSum (D : OrientedPDCode n) : ℤ :=
  ∑ s : Fin n → Bool,
    ((#{i | s i = false} : ℤ) + D.negativeCrossingCount).negOnePow •
      (2 : ℤ) ^ D.stateLoopCount s

/-- Defining sum of `normalizedEulerSum`. -/
theorem normalizedEulerSum_def (D : OrientedPDCode n) :
    D.normalizedEulerSum =
      ∑ s : Fin n → Bool,
        ((#{i | s i = false} : ℤ) + D.negativeCrossingCount).negOnePow •
          (2 : ℤ) ^ D.stateLoopCount s :=
  (rfl)

private theorem negOnePow_card_false_add_negativeCrossingCount (D : OrientedPDCode n)
    (s : Fin n → Bool) :
    ((#{i | s i = false} : ℤ) + D.negativeCrossingCount).negOnePow =
      (D.stateCochainDegree s).negOnePow := by
  rw [stateCochainDegree_def, Int.negOnePow_eq_iff]
  exact ⟨D.negativeCrossingCount, by omega⟩

/-- Because `|S| + n₋` and the cochain degree `|S| - n₋` differ by `2 n₋`, the normalized Euler
state sum equals `∑ₛ (-1) ^ (|S| - n₋) 2 ^ k(s)`. -/
theorem normalizedEulerSum_eq_sum_stateCochainDegree (D : OrientedPDCode n) :
    D.normalizedEulerSum =
      ∑ s : Fin n → Bool, (D.stateCochainDegree s).negOnePow • (2 : ℤ) ^ D.stateLoopCount s := by
  rw [normalizedEulerSum_def]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [D.negOnePow_card_false_add_negativeCrossingCount s]

/-- A crossing-free oriented PD-code has normalized Euler state sum `2 ^ c`, where `c` is its
number of components. -/
theorem normalizedEulerSum_of_zero_crossings (D : OrientedPDCode 0) :
    D.normalizedEulerSum = 2 ^ D.componentCount := by
  rw [normalizedEulerSum_def, Fintype.sum_unique]
  simp [PDCode.componentCount_eq, PDCode.crossingComponentCount_eq_zero, negativeCrossingCount_def]

/-- The empty diagram has normalized Euler state sum `1`. -/
@[simp]
theorem normalizedEulerSum_empty : empty.normalizedEulerSum = 1 := by
  rw [normalizedEulerSum_of_zero_crossings]
  simp [PDCode.componentCount_eq, PDCode.crossingComponentCount_eq_zero,
    ← empty.card_crossinglessComponents, crossinglessComponents_empty]

/-- Either orientation of the crossing-free unknot has normalized Euler state sum `2`. -/
@[simp]
theorem normalizedEulerSum_unknot (orientation : Bool) :
    (unknot orientation).normalizedEulerSum = 2 := by
  rw [normalizedEulerSum_of_zero_crossings]
  simp [PDCode.componentCount_eq, PDCode.crossingComponentCount_eq_zero,
    ← (unknot orientation).card_crossinglessComponents, crossinglessComponents_unknot]

/-- **Evaluating the enhanced state sum at `q = 1`** yields the normalized Euler state sum. -/
theorem eval₂_one_enhancedStateSum (D : OrientedPDCode n) :
    eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) D.enhancedStateSum = D.normalizedEulerSum := by
  rw [enhancedStateSum_eq_sum, normalizedEulerSum_eq_sum_stateCochainDegree, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_mul_assoc, Units.smul_def, map_zsmul, map_mul, map_pow, map_add, eval₂_T,
    one_zpow, Units.val_one, one_mul]
  rfl

/-- Evaluating the enhanced state sum at `1` via `TauCeti.laurentEval` yields
`normalizedEulerSum`. -/
theorem laurentEval_one_enhancedStateSum (D : OrientedPDCode n) :
    laurentEval (1 : ℤˣ) D.enhancedStateSum = D.normalizedEulerSum := by
  rw [laurentEval_eq_eval₂, RingHom.ext_int (algebraMap ℤ ℤ) (Int.castRingHom ℤ),
    eval₂_one_enhancedStateSum]

/-- The sum of all Laurent coefficients of `D.enhancedStateSum` is `D.normalizedEulerSum`. -/
theorem sum_coeff_enhancedStateSum (D : OrientedPDCode n) :
    (D.enhancedStateSum.coeff.sum fun _ c ↦ c) = D.normalizedEulerSum := by
  rw [← laurentEval_one_eq_sum, laurentEval_one_enhancedStateSum]

/-- **Crossing-change invariance of `normalizedEulerSum`.** Switching the over- and under-strands
at a single crossing `c` exchanges the `A`- and `B`-smoothings at `c` while flipping both
`(-1) ^ |S|` and `(-1) ^ n₋`, leaving `normalizedEulerSum` unchanged. No planarity hypothesis is
needed. -/
@[simp]
theorem normalizedEulerSum_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).normalizedEulerSum = D.normalizedEulerSum := by
  rw [normalizedEulerSum_def, normalizedEulerSum_def,
    ← Equiv.sum_comp (PDCode.changeCrossingStateEquiv c)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hsign :
      ((#{i | PDCode.changeCrossingStateEquiv c s i = false} : ℤ) +
          (D.changeCrossing c).negativeCrossingCount).negOnePow =
        ((#{i | s i = false} : ℤ) + D.negativeCrossingCount).negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add, PDCode.negOnePow_card_false_changeCrossingStateEquiv,
      D.negOnePow_negativeCrossingCount_changeCrossing c, neg_mul_neg]
  rw [toPDCode_changeCrossing, PDCode.stateLoopCount_changeCrossing_changeCrossingStateEquiv, hsign]

private theorem card_false_insertNth (c : Fin (n + 1)) (t : Bool) (s : Fin n → Bool) :
    #{i : Fin (n + 1) | c.insertNth (α := fun _ ↦ Bool) t s i = false} =
      #{j : Fin n | s j = false} + bif t then 0 else 1 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ c]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  cases t <;> simp [Nat.add_comm]

/-- **Unnormalized resolution recurrence for `normalizedEulerSum`.** Splitting states according to
their value at crossing `c` expresses `D.normalizedEulerSum` in terms of any two oriented PD-codes
`D₀` and `D₁` realizing the `A`- and `B`-resolutions of `c`, without assuming planarity. -/
theorem normalizedEulerSum_eq_resolveCrossing (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))
    {D₀ D₁ : OrientedPDCode n} (h₀ : D₀.toPDCode = D.toPDCode.resolveCrossing c true)
    (h₁ : D₁.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.normalizedEulerSum =
      ((D.negativeCrossingCount : ℤ) - D₀.negativeCrossingCount).negOnePow •
          D₀.normalizedEulerSum +
        ((D.negativeCrossingCount : ℤ) - D₁.negativeCrossingCount + 1).negOnePow •
          D₁.normalizedEulerSum := by
  rw [normalizedEulerSum_def, D₀.normalizedEulerSum_def, D₁.normalizedEulerSum_def,
    ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hs :
        ((#{j | s j = false} : ℤ) + D.negativeCrossingCount).negOnePow =
          ((D.negativeCrossingCount : ℤ) - D₀.negativeCrossingCount).negOnePow *
            ((#{j | s j = false} : ℤ) + D₀.negativeCrossingCount).negOnePow := by
      rw [← Int.negOnePow_add]
      congr 1
      ring
    change ((#{i : Fin (n + 1) | c.insertNth (α := fun _ ↦ Bool) true s i = false} : ℤ) +
        D.negativeCrossingCount).negOnePow •
      (2 : ℤ) ^ D.toPDCode.stateLoopCount (c.insertNth true s) = _
    rw [D.toPDCode.stateLoopCount_insertNth c true s, ← h₀, card_false_insertNth c true s,
      Bool.cond_true, add_zero, hs, mul_smul]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hs :
        (((#{j | s j = false} + 1 : ℕ) : ℤ) + D.negativeCrossingCount).negOnePow =
          ((D.negativeCrossingCount : ℤ) - D₁.negativeCrossingCount + 1).negOnePow *
            ((#{j | s j = false} : ℤ) + D₁.negativeCrossingCount).negOnePow := by
      rw [← Int.negOnePow_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    change ((#{i : Fin (n + 1) | c.insertNth (α := fun _ ↦ Bool) false s i = false} : ℤ) +
        D.negativeCrossingCount).negOnePow •
      (2 : ℤ) ^ D.toPDCode.stateLoopCount (c.insertNth false s) = _
    rw [D.toPDCode.stateLoopCount_insertNth c false s, ← h₁, card_false_insertNth c false s,
      Bool.cond_false, hs, mul_smul]

/-- **Planar parity of the negative-crossing shift across a resolution.** For a planar oriented
PD-code `D` and any oriented PD-code `E` realizing the `t`-resolution of `D` at crossing `c`, the
cochain-degree shift `n₋(D) - n₋(E) + (0 if t else 1)` has parity opposite to `c(D) + c(E)`. -/
theorem negOnePow_negativeCrossingCount_sub_resolveCrossing (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) (t : Bool) {E : OrientedPDCode n}
    (hE : E.toPDCode = D.toPDCode.resolveCrossing c t) :
    ((D.negativeCrossingCount : ℤ) - E.negativeCrossingCount + bif t then 0 else 1).negOnePow =
      -((D.componentCount : ℤ).negOnePow * (E.componentCount : ℤ).negOnePow) := by
  rw [← Int.negOnePow_add]
  apply Int.negOnePow_eq_neg_of_odd_sub
  rw [Int.odd_iff]
  let s₀ : Fin n → Bool := fun _ ↦ true
  have hEp : E.toPDCode.IsPlanar := hE ▸ hD.resolveCrossing _ c t
  have hparD := D.stateQuantumShift_add_stateLoopCount_mod_two hD (c.insertNth t s₀)
  have hparE := E.stateQuantumShift_add_stateLoopCount_mod_two hEp s₀
  have hs₀ : #{j | s₀ j = false} = 0 := by simp [s₀]
  have hins : #{i : Fin (n + 1) | c.insertNth (α := fun _ ↦ Bool) t s₀ i = false} =
      bif t then 0 else 1 := by
    rw [card_false_insertNth, hs₀, zero_add]
  have hloop : D.toPDCode.stateLoopCount (c.insertNth t s₀) = E.toPDCode.stateLoopCount s₀ := by
    rw [D.toPDCode.stateLoopCount_insertNth c t s₀, ← hE]
  rw [D.stateQuantumShift_def, hins, hloop] at hparD
  rw [E.stateQuantumShift_def, hs₀] at hparE
  have hnD := D.positiveCrossingCount_add_negativeCrossingCount
  have hnE := E.positiveCrossingCount_add_negativeCrossingCount
  cases t <;> simp only [Bool.cond_true, Bool.cond_false] at hparD ⊢ <;> omega

/-- **Normalized planar recurrence for `normalizedEulerSum`.** For a planar oriented PD-code `D`
and any oriented PD-codes `D₀` and `D₁` realizing the `A`- and `B`-resolutions of crossing `c`,
`E(D) = -(-1) ^ c(D) [(-1) ^ c(D₀) E(D₀) + (-1) ^ c(D₁) E(D₁)]`. -/
theorem normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) {D₀ D₁ : OrientedPDCode n}
    (h₀ : D₀.toPDCode = D.toPDCode.resolveCrossing c true)
    (h₁ : D₁.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.normalizedEulerSum =
      -((D.componentCount : ℤ).negOnePow •
        ((D₀.componentCount : ℤ).negOnePow • D₀.normalizedEulerSum +
          (D₁.componentCount : ℤ).negOnePow • D₁.normalizedEulerSum)) := by
  have hs₀ := D.negOnePow_negativeCrossingCount_sub_resolveCrossing hD c true h₀
  have hs₁ := D.negOnePow_negativeCrossingCount_sub_resolveCrossing hD c false h₁
  simp only [Bool.cond_true, add_zero] at hs₀
  simp only [Bool.cond_false] at hs₁
  rw [D.normalizedEulerSum_eq_resolveCrossing c h₀ h₁, hs₀, hs₁, Units.neg_smul, Units.neg_smul,
    mul_smul, mul_smul, smul_add, neg_add]

/-- Concrete specialization of `normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing` to the
canonical oriented smoothings `D.resolveCrossingOriented`. -/
theorem normalizedEulerSum_resolveCrossingOriented (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    D.normalizedEulerSum =
      -((D.componentCount : ℤ).negOnePow •
        (((D.toPDCode.resolveCrossing c true).componentCount : ℤ).negOnePow •
            (D.resolveCrossingOriented c true detached choice).normalizedEulerSum +
          ((D.toPDCode.resolveCrossing c false).componentCount : ℤ).negOnePow •
            (D.resolveCrossingOriented c false detached choice).normalizedEulerSum)) := by
  have h₀ := D.toPDCode_resolveCrossingOriented c true detached choice
  have h₁ := D.toPDCode_resolveCrossingOriented c false detached choice
  rw [D.normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing hD c h₀ h₁,
    congrArg PDCode.componentCount h₀, congrArg PDCode.componentCount h₁]

/-- **Every planar oriented PD-code with `c` components has `normalizedEulerSum = 2 ^ c`.** -/
theorem normalizedEulerSum_eq_two_pow :
    ∀ {n : ℕ} (D : OrientedPDCode n), D.toPDCode.IsPlanar →
      D.normalizedEulerSum = 2 ^ D.componentCount
  | 0, D, _ => D.normalizedEulerSum_of_zero_crossings
  | n + 1, D, hD => by
    let D₀ := D.resolveCrossingOriented 0 true (fun _ ↦ true) (fun _ ↦ true)
    let D₁ := D.resolveCrossingOriented 0 false (fun _ ↦ true) (fun _ ↦ true)
    have h₀ : D₀.toPDCode = D.toPDCode.resolveCrossing 0 true :=
      D.toPDCode_resolveCrossingOriented 0 true _ _
    have h₁ : D₁.toPDCode = D.toPDCode.resolveCrossing 0 false :=
      D.toPDCode_resolveCrossingOriented 0 false _ _
    have hp₀ : D₀.toPDCode.IsPlanar := h₀ ▸ hD.resolveCrossing _ 0 true
    have hp₁ : D₁.toPDCode.IsPlanar := h₁ ▸ hD.resolveCrossing _ 0 false
    have ih₀ : D₀.normalizedEulerSum =
        2 ^ (D.toPDCode.resolveCrossing 0 true).componentCount := by
      simpa [h₀] using normalizedEulerSum_eq_two_pow D₀ hp₀
    have ih₁ : D₁.normalizedEulerSum =
        2 ^ (D.toPDCode.resolveCrossing 0 false).componentCount := by
      simpa [h₁] using normalizedEulerSum_eq_two_pow D₁ hp₁
    have hc₀ : D₀.componentCount = (D.toPDCode.resolveCrossing 0 true).componentCount :=
      congrArg PDCode.componentCount h₀
    have hc₁ : D₁.componentCount = (D.toPDCode.resolveCrossing 0 false).componentCount :=
      congrArg PDCode.componentCount h₁
    rw [D.normalizedEulerSum_eq_neg_negOnePow_mul_resolveCrossing hD 0 h₀ h₁, ih₀, ih₁, hc₀, hc₁]
    rcases D.componentCount_resolveCrossing_dichotomy 0 with
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have hB' : (D.toPDCode.resolveCrossing 0 false).componentCount =
          (D.toPDCode.resolveCrossing 0 true).componentCount := by omega
      rw [hB', ← hA, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, neg_neg,
        ← smul_add, negOnePow_smul_negOnePow_smul, pow_succ]
      ring
    · rw [hA, hB, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, smul_add,
        smul_neg, negOnePow_smul_negOnePow_smul, negOnePow_smul_negOnePow_smul, pow_succ]
      ring
    · rw [hA, hB, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, smul_add,
        smul_neg, negOnePow_smul_negOnePow_smul, negOnePow_smul_negOnePow_smul, pow_succ]
      ring

/-- Evaluating the enhanced state sum of a planar oriented PD-code at `q = 1` gives `2 ^ c`. -/
theorem eval₂_one_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) D.enhancedStateSum = 2 ^ D.componentCount := by
  rw [D.eval₂_one_enhancedStateSum, D.normalizedEulerSum_eq_two_pow hD]

/-- The sum of all Laurent coefficients of `D.enhancedStateSum` for a planar oriented PD-code is
`2 ^ D.componentCount`. -/
theorem sum_coeff_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    (D.enhancedStateSum.coeff.sum fun _ c ↦ c) = 2 ^ D.componentCount := by
  rw [D.sum_coeff_enhancedStateSum, D.normalizedEulerSum_eq_two_pow hD]

/-- **Evaluating the Jones polynomial at `t ^ (1/2) = -1`.** For any nonempty planar oriented
PD-code `D`, evaluating `D.jonesPolynomial` at `-1` yields `2 ^ (D.componentCount - 1)`. -/
theorem eval₂_neg_one_jonesPolynomial (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
    (hc : 0 < D.toPDCode.componentCount) :
    eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ) D.jonesPolynomial = 2 ^ (D.componentCount - 1) := by
  let φ : ℤ[T;T⁻¹] →ₐ[ℤ] ℤ := laurentEval (1 : ℤˣ)
  have hsum : φ D.enhancedStateSum = 2 ^ D.componentCount := by
    rw [D.laurentEval_one_enhancedStateSum, D.normalizedEulerSum_eq_two_pow hD]
  rw [D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hc, map_mul] at hsum
  have htwo : φ (T 1 + T (-1)) = 2 := by simp [φ]
  have hcomp : φ.toRingHom.comp (Int.castRingHom ℤ[T;T⁻¹]) = Int.castRingHom ℤ :=
    RingHom.ext_int _ _
  have hunit : Units.map (φ.toRingHom : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) = (-1 : ℤˣ) := by
    ext
    simp [φ]
  have hjones :
      φ (eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial) =
        eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ) D.jonesPolynomial := by
    change φ.toRingHom (eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial) = _
    rw [LaurentPolynomial.hom_eval₂, hcomp, hunit]
  rw [htwo, hjones] at hsum
  have hpow : (2 : ℤ) ^ D.componentCount = 2 * 2 ^ (D.componentCount - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hc, pow_succ']
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (hsum.trans hpow)

end NormalizedEulerSum

/-! ### Quantum-parity vanishing and nonvanishing of Khovanov homology -/

section Nonvanishing

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

section AnyCommRing

variable (R : Type u) [CommRing R]

/-- Every chain group of the normalized Khovanov complex vanishes in quantum degrees whose parity
differs from `D.componentCount`, over any commutative coefficient ring. -/
theorem isZero_khovanovComplex_X_of_mod_two_ne {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) (i : ℤ) :
    IsZero ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X, Functor.isZero_cubeComplex_X_iff]
  intro S
  rw [D.resolutionCube_obj_normalized hD R j S.1, ModuleCat.isZero_of_iff_subsingleton,
    Submodule.subsingleton_iff_eq_bot]
  exact D.circleQuantumGrading_piece_eq_bot_of_mod_two_ne hD R (PDCode.cubeState S.1) hj

/-- The entire quantum-component Khovanov complex vanishes when `j % 2 ≠ D.componentCount % 2`. -/
theorem isZero_khovanovComplex_of_mod_two_ne {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    IsZero (D.khovanovComplex hD R j) := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (D.isZero_khovanovComplex_X_of_mod_two_ne hD R hj i).eq_of_src _ _

/-- **Quantum-parity vanishing of Khovanov homology**: `Khⁱʲ(D; R)` is zero whenever `j` does not
have the parity of `D.componentCount`, over any commutative coefficient ring `R`. -/
theorem isZero_khovanovHomology_of_mod_two_ne (i : ℤ) {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    IsZero (D.khovanovHomology hD R i j) :=
  (ExactAt.of_isZero (D.isZero_khovanovComplex_X_of_mod_two_ne hD R hj i)).isZero_homology

/-- Over any nontrivial commutative ring `R`, the coefficient of `q ^ j` in `D.khovanovEulerChar`
vanishes whenever `j % 2 ≠ D.componentCount % 2`. -/
theorem coeff_khovanovEulerChar_eq_zero_of_mod_two_ne [Nontrivial R] {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    (D.khovanovEulerChar hD R).coeff j = 0 := by
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [ModuleCat.finrank_eq_zero_of_isZero (D.isZero_khovanovHomology_of_mod_two_ne hD R i hj),
    Nat.cast_zero, mul_zero]

end AnyCommRing

/-- Every coefficient of `D.enhancedStateSum` in a quantum degree of parity opposite to
`D.componentCount` vanishes. -/
theorem coeff_enhancedStateSum_eq_zero_of_mod_two_ne (hD : D.toPDCode.IsPlanar) {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    D.enhancedStateSum.coeff j = 0 := by
  rw [← D.khovanovEulerChar_eq_enhancedStateSum hD ℤ]
  exact D.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne hD ℤ hj

section RankNullity

variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- Over a nontrivial Noetherian ring with the rank-nullity property, evaluating the graded Euler
characteristic `χ_q Kh(D; R)` at `q = 1` gives `2 ^ D.componentCount`. -/
theorem eval₂_one_khovanovEulerChar_eq_two_pow :
    eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **Nonvanishing of the graded Euler characteristic of Khovanov homology**: for every planar
oriented PD-code `D` (including the empty diagram), `χ_q Kh(D; R) ≠ 0` over any nontrivial
Noetherian commutative ring `R` with the rank-nullity property. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := by
  intro h0
  have h := D.eval₂_one_khovanovEulerChar_eq_two_pow hD R
  rw [h0, map_zero] at h
  exact pow_ne_zero D.componentCount (by decide : (2 : ℤ) ≠ 0) h.symm

/-- For every planar oriented PD-code `D`, some quantum degree `j ≡ D.componentCount (mod 2)` has a
nonzero coefficient in `D.khovanovEulerChar hD R`. -/
theorem exists_coeff_khovanovEulerChar_ne_zero :
    ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧ (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
  have hex : ∃ j : ℤ, (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
    by_contra! hall
    exact D.khovanovEulerChar_ne_zero hD R
      (AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun j ↦ hall j)
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_, hj⟩
  by_contra hmod
  exact hj (D.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne hD R hmod)

/-- **Nonvanishing of Khovanov homology (positive rank)**: for every planar oriented PD-code `D`
(including the empty diagram) and every nontrivial Noetherian commutative ring `R` with the
rank-nullity property, there exist a cochain degree `i ∈ [-n₋, n₊]` and a quantum degree
`j ≡ D.componentCount (mod 2)` such that `0 < Module.finrank R (D.khovanovHomology hD R i j)`. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  obtain ⟨j, hjmod, hjne⟩ := D.exists_coeff_khovanovEulerChar_ne_zero hD R
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j] at hjne
  obtain ⟨i, himem, hine⟩ := Finset.exists_ne_zero_of_sum_ne_zero hjne
  have hpos : 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
    refine Nat.pos_of_ne_zero fun h0 ↦ hine ?_
    rw [h0, Nat.cast_zero, mul_zero]
  exact ⟨i, Finset.mem_Icc.mp himem, j, hjmod, hpos⟩

/-- **Nonvanishing of Khovanov homology (categorical form)**: for every planar oriented PD-code `D`
and every nontrivial Noetherian commutative ring `R` with the rank-nullity property, some
`Khⁱʲ(D; R)` with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is non-zero as an object of
`ModuleCat R`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬ IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, hj, fun hZ ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hZ)⟩

/-- **Nonvanishing of Khovanov homology (module form)**: for every planar oriented PD-code `D` and
every nontrivial Noetherian commutative ring `R` with the rank-nullity property, some underlying
`R`-module `Khⁱʲ(D; R)` with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is `Nontrivial`. -/
theorem exists_nontrivial_khovanovHomology :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, hj, Module.nontrivial_of_finrank_pos hpos⟩

end RankNullity

/-! ### Integral and rational specializations -/

/-- The integral graded Euler characteristic `χ_q Kh(D; ℤ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_int_ne_zero : D.khovanovEulerChar hD ℤ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℤ

/-- Integral Khovanov homology `Kh(D; ℤ)` has positive free rank in at least one bidegree `(i, j)`
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- Integral Khovanov homology `Kh(D; ℤ)` is nontrivial in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_int :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℤ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℤ

/-- The rational graded Euler characteristic `χ_q Kh(D; ℚ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_rat_ne_zero : D.khovanovEulerChar hD ℚ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℚ

/-- Rational Khovanov homology `Kh(D; ℚ)` has positive dimension in at least one bidegree `(i, j)`
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- Rational Khovanov homology `Kh(D; ℚ)` is nontrivial in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_rat :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℚ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℚ

end Nonvanishing

end TauCeti.OrientedPDCode
