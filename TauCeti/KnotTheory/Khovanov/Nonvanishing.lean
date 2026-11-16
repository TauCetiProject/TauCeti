/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.PDCode.ChangeCrossing
public import TauCeti.KnotTheory.PDCode.Oriented.ResolveCrossing
import TauCeti.Data.Fin.Basic
import TauCeti.KnotTheory.Khovanov.Parity

/-! # The ungraded Euler state sum and nonvanishing of Khovanov homology

Specializing `TauCeti.OrientedPDCode.enhancedStateSum` at `q = 1` gives the normalized ungraded
Euler state sum `E(D) = ∑ₛ (-1) ^ (|S| + n₋) 2 ^ k(s)`
(`TauCeti.OrientedPDCode.normalizedEulerSum`), which equals the sum of all coefficients of
`D.enhancedStateSum` (`eval₂_one_enhancedStateSum`, `sum_coeff_enhancedStateSum`) and, for a planar
oriented PD-code `D` over a nontrivial Noetherian commutative ring `R` with the rank-nullity
property, the evaluation of `D.khovanovEulerChar hD R` at `q = 1`.

Without planarity, `E(D)` is invariant under switching a single crossing
(`normalizedEulerSum_changeCrossing`) and decomposes at any crossing `c` into the two smoothings
(`normalizedEulerSum_eq_resolveCrossing`). When `D` is planar, quantum-degree parity fixes the
Euler-sum sign shift `n₋(D) - n₋(E) + (0 if t else 1)` modulo `2`
(`negOnePow_negativeCrossingCount_sub_resolveCrossing`), giving the recurrence
`E(D) = -(-1) ^ m [(-1) ^ m₀ E(D₀) + (-1) ^ m₁ E(D₁)]` for any oriented smoothings `D₀, D₁`
with component counts `m = D.componentCount`, `m₀`, `m₁`
(`normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossing`,
`normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossingOriented`). Induction with
`PDCode.componentCount_resolveCrossing_dichotomy` yields `E(D) = 2 ^ m`
(`normalizedEulerSum_eq_two_pow`) and hence `J(D)|_{t ^ (1/2) = -1} = 2 ^ (m - 1)` for `0 < m`
(`eval₂_neg_one_jonesPolynomial`).

Since `2 ^ m ≠ 0`, `χ_q Kh(D; R) ≠ 0` (`khovanovEulerChar_ne_zero`), so over every nontrivial
Noetherian commutative ring `R` with rank-nullity (in particular `ℤ` and `ℚ`), every planar
oriented PD-code has a bidegree `(i, j)` with `i ∈ [-n₋, n₊]`, `j ≡ m (mod 2)`, and
`0 < Module.finrank R (D.khovanovHomology hD R i j)` (`exists_finrank_khovanovHomology_pos`,
`exists_not_isZero_khovanovHomology`, `exists_nontrivial_khovanovHomology`).

References: M. Khovanov, Duke Math. J. 101 (2000), 359–426; D. Bar-Natan, Algebr. Geom. Topol. 2
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
          (2 : ℤ) ^ D.stateLoopCount s := (rfl)

private theorem negOnePow_card_false_add_negativeCrossingCount (D : OrientedPDCode n)
    (s : Fin n → Bool) :
    ((#{i | s i = false} : ℤ) + D.negativeCrossingCount).negOnePow =
      (D.stateCochainDegree s).negOnePow := by
  rw [stateCochainDegree_def, Int.negOnePow_eq_iff]; exact ⟨D.negativeCrossingCount, by omega⟩

/-- Because `|S| + n₋` and the cochain degree `|S| - n₋` differ by `2 n₋`, the normalized Euler
state sum equals `∑ₛ (-1) ^ (|S| - n₋) 2 ^ k(s)`. -/
theorem normalizedEulerSum_eq_sum_stateCochainDegree (D : OrientedPDCode n) :
    D.normalizedEulerSum =
      ∑ s : Fin n → Bool, (D.stateCochainDegree s).negOnePow • (2 : ℤ) ^ D.stateLoopCount s := by
  rw [normalizedEulerSum_def]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [D.negOnePow_card_false_add_negativeCrossingCount s]

/-- A crossing-free oriented PD-code has normalized Euler state sum `2 ^ D.componentCount`. -/
theorem normalizedEulerSum_of_zero_crossings (D : OrientedPDCode 0) :
    D.normalizedEulerSum = 2 ^ D.componentCount := by
  rw [normalizedEulerSum_def, Fintype.sum_unique]
  simp [PDCode.componentCount_eq, PDCode.crossingComponentCount_eq_zero, negativeCrossingCount_def]

/-- The empty diagram has normalized Euler state sum `1`. -/
@[simp] theorem normalizedEulerSum_empty : empty.normalizedEulerSum = 1 := by
  rw [normalizedEulerSum_of_zero_crossings]
  simp [PDCode.componentCount_eq, PDCode.crossingComponentCount_eq_zero,
    ← empty.card_crossinglessComponents, crossinglessComponents_empty]

/-- Either orientation of the crossing-free unknot has normalized Euler state sum `2`. -/
@[simp] theorem normalizedEulerSum_unknot (orientation : Bool) :
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
    one_zpow, Units.val_one, one_mul]; rfl

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
@[simp] theorem normalizedEulerSum_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).normalizedEulerSum = D.normalizedEulerSum := by
  rw [normalizedEulerSum_def, normalizedEulerSum_def,
    ← Equiv.sum_comp (PDCode.changeCrossingStateEquiv c)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [toPDCode_changeCrossing, PDCode.stateLoopCount_changeCrossing_changeCrossingStateEquiv,
    Int.negOnePow_add, Int.negOnePow_add, PDCode.negOnePow_card_false_changeCrossingStateEquiv,
    D.negOnePow_negativeCrossingCount_changeCrossing c, neg_mul_neg]

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
  have hbranch (t : Bool) {E : OrientedPDCode n}
      (hE : E.toPDCode = D.toPDCode.resolveCrossing c t) :
      (∑ s : Fin n → Bool,
          ((#{i | (Fin.insertNthEquiv (fun _ ↦ Bool) c) (t, s) i = false} : ℤ) +
              D.negativeCrossingCount).negOnePow •
            (2 : ℤ) ^ D.stateLoopCount ((Fin.insertNthEquiv (fun _ ↦ Bool) c) (t, s))) =
        ((D.negativeCrossingCount : ℤ) - E.negativeCrossingCount + bif t then 0 else 1).negOnePow •
          E.normalizedEulerSum := by
    rw [E.normalizedEulerSum_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hcard : (#{i | (Fin.insertNthEquiv (fun _ ↦ Bool) c) (t, s) i = false} : ℤ) =
        (#{j | s j = false} : ℤ) + bif t then 0 else 1 := by
      rw [Finset.filter_congr fun i _ ↦ by rw [Fin.insertNthEquiv_apply],
        Fin.card_filter_insertNth (fun _ b ↦ b = false) c t s]
      cases t <;> simp
    have hs :
        ((#{j | s j = false} : ℤ) + (bif t then 0 else 1) + D.negativeCrossingCount).negOnePow =
          ((D.negativeCrossingCount : ℤ) - E.negativeCrossingCount +
              bif t then 0 else 1).negOnePow *
            ((#{j | s j = false} : ℤ) + E.negativeCrossingCount).negOnePow := by
      rw [← Int.negOnePow_add]; congr 1; ring
    rw [hcard, Fin.insertNthEquiv_apply, D.toPDCode.stateLoopCount_insertNth, ← hE, hs, mul_smul]
  rw [normalizedEulerSum_def, ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool, hbranch true h₀, hbranch false h₁]
  simp only [Bool.cond_true, Bool.cond_false, add_zero]

/-- **Planar parity of the negative-crossing shift across a resolution.** For a planar oriented
PD-code `D` and any oriented PD-code `E` realizing the `t`-resolution of `D` at crossing `c`, the
Euler-sum sign shift `n₋(D) - n₋(E) + (0 if t else 1)` (the change in `|S| + n₋`) has parity
opposite to `D.componentCount + E.componentCount`. -/
theorem negOnePow_negativeCrossingCount_sub_resolveCrossing (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) (t : Bool) {E : OrientedPDCode n}
    (hE : E.toPDCode = D.toPDCode.resolveCrossing c t) :
    ((D.negativeCrossingCount : ℤ) - E.negativeCrossingCount + bif t then 0 else 1).negOnePow =
      -((D.componentCount : ℤ).negOnePow * (E.componentCount : ℤ).negOnePow) := by
  rw [← Int.negOnePow_add]
  apply Int.negOnePow_eq_neg_of_odd_sub
  rw [Int.odd_iff]
  let s₀ : Fin n → Bool := fun _ ↦ true
  have hparD := D.stateQuantumShift_add_stateLoopCount_mod_two hD (c.insertNth t s₀)
  have hparE := E.stateQuantumShift_add_stateLoopCount_mod_two (hE ▸ hD.resolveCrossing _ c t) s₀
  have hs₀ : #{j | s₀ j = false} = 0 := by simp [s₀]
  have hins : #{i : Fin (n + 1) | c.insertNth (α := fun _ ↦ Bool) t s₀ i = false} =
      bif t then 0 else 1 := by
    rw [Fin.card_filter_insertNth (fun _ b ↦ b = false) c t s₀, hs₀, zero_add]; cases t <;> rfl
  have hloop : D.toPDCode.stateLoopCount (c.insertNth t s₀) = E.toPDCode.stateLoopCount s₀ := by
    rw [D.toPDCode.stateLoopCount_insertNth c t s₀, ← hE]
  rw [D.stateQuantumShift_def, hins, hloop] at hparD
  rw [E.stateQuantumShift_def, hs₀] at hparE
  have hnD := D.positiveCrossingCount_add_negativeCrossingCount
  have hnE := E.positiveCrossingCount_add_negativeCrossingCount
  cases t <;> simp only [Bool.cond_true, Bool.cond_false] at hparD ⊢ <;> omega

/-- **Normalized planar recurrence for `normalizedEulerSum`.** For a planar oriented PD-code `D`
and any oriented PD-codes `D₀` and `D₁` realizing the `A`- and `B`-resolutions of crossing `c`,
`E(D) = -(-1) ^ m [(-1) ^ m₀ E(D₀) + (-1) ^ m₁ E(D₁)]`, where `m`, `m₀`, `m₁` are the component
counts of `D`, `D₀`, `D₁`. -/
theorem normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossing (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) {D₀ D₁ : OrientedPDCode n}
    (h₀ : D₀.toPDCode = D.toPDCode.resolveCrossing c true)
    (h₁ : D₁.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.normalizedEulerSum =
      -((D.componentCount : ℤ).negOnePow •
        ((D₀.componentCount : ℤ).negOnePow • D₀.normalizedEulerSum +
          (D₁.componentCount : ℤ).negOnePow • D₁.normalizedEulerSum)) := by
  have hs₀ := D.negOnePow_negativeCrossingCount_sub_resolveCrossing hD c true h₀
  have hs₁ := D.negOnePow_negativeCrossingCount_sub_resolveCrossing hD c false h₁
  simp only [Bool.cond_true, add_zero] at hs₀; simp only [Bool.cond_false] at hs₁
  rw [D.normalizedEulerSum_eq_resolveCrossing c h₀ h₁, hs₀, hs₁, Units.neg_smul, Units.neg_smul,
    mul_smul, mul_smul, smul_add, neg_add]

/-- Concrete specialization of `normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossing` to the
canonical oriented smoothings `D.resolveCrossingOriented`. -/
theorem normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossingOriented
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
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
  rw [D.normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossing hD c h₀ h₁,
    congrArg PDCode.componentCount h₀, congrArg PDCode.componentCount h₁]

/-- **Every planar oriented PD-code has `normalizedEulerSum = 2 ^ D.componentCount`.** -/
theorem normalizedEulerSum_eq_two_pow :
    ∀ {n : ℕ} (D : OrientedPDCode n), D.toPDCode.IsPlanar →
      D.normalizedEulerSum = 2 ^ D.componentCount
  | 0, D, _ => D.normalizedEulerSum_of_zero_crossings
  | n + 1, D, hD => by
    let D₀ := D.resolveCrossingOriented 0 true (fun _ ↦ true) (fun _ ↦ true)
    let D₁ := D.resolveCrossingOriented 0 false (fun _ ↦ true) (fun _ ↦ true)
    have h₀ := D.toPDCode_resolveCrossingOriented 0 true (fun _ ↦ true) (fun _ ↦ true)
    have h₁ := D.toPDCode_resolveCrossingOriented 0 false (fun _ ↦ true) (fun _ ↦ true)
    have ih₀ := normalizedEulerSum_eq_two_pow D₀ (h₀ ▸ hD.resolveCrossing _ 0 true)
    have ih₁ := normalizedEulerSum_eq_two_pow D₁ (h₁ ▸ hD.resolveCrossing _ 0 false)
    rw [D.normalizedEulerSum_eq_neg_negOnePow_smul_resolveCrossing hD 0 h₀ h₁, ih₀, ih₁,
      congrArg PDCode.componentCount h₀, congrArg PDCode.componentCount h₁]
    rcases D.toPDCode.componentCount_resolveCrossing_dichotomy 0 with
      ⟨hA, hB⟩ | (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · have hB' : (D.toPDCode.resolveCrossing 0 false).componentCount =
          (D.toPDCode.resolveCrossing 0 true).componentCount := by omega
      rw [hB', ← hA, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, neg_neg,
        ← smul_add, negOnePow_smul_negOnePow_smul, pow_succ]; ring
    · rw [hA, hB, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, smul_add,
        smul_neg, negOnePow_smul_negOnePow_smul, negOnePow_smul_negOnePow_smul, pow_succ]; ring
    · rw [hA, hB, Nat.cast_add_one, Int.negOnePow_succ, Units.neg_smul, smul_add,
        smul_neg, negOnePow_smul_negOnePow_smul, negOnePow_smul_negOnePow_smul, pow_succ]; ring

/-- Evaluating the enhanced state sum of a planar oriented PD-code at `q = 1` gives
`2 ^ D.componentCount`. -/
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
  have hunit : Units.map (φ.toRingHom : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) = (-1 : ℤˣ) := by
    ext; simp [φ]
  have hjones :
      φ (eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial) =
        eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ) D.jonesPolynomial := by
    rw [← φ.coe_toRingHom, ← φ.toRingHom_eq_coe, LaurentPolynomial.hom_eval₂,
      RingHom.ext_int (φ.toRingHom.comp (Int.castRingHom ℤ[T;T⁻¹])) (Int.castRingHom ℤ), hunit]
  rw [htwo, hjones] at hsum
  have hpow : (2 : ℤ) ^ D.componentCount = 2 * 2 ^ (D.componentCount - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hc, pow_succ']
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (hsum.trans hpow)

end NormalizedEulerSum

/-! ### Nonvanishing of Khovanov homology -/

section Nonvanishing
variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

section RankNullity
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- For a planar oriented PD-code `D` over a nontrivial Noetherian commutative ring `R` with the
rank-nullity property, evaluating the graded Euler characteristic `χ_q Kh(D; R)` at `q = 1` gives
`2 ^ D.componentCount`. -/
theorem eval₂_one_khovanovEulerChar_eq_two_pow :
    eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **Nonvanishing of the graded Euler characteristic of Khovanov homology**: for every planar
oriented PD-code `D` (including the empty diagram), `χ_q Kh(D; R) ≠ 0` over any nontrivial
Noetherian commutative ring `R` with the rank-nullity property. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := fun h0 ↦ by
  have h := D.eval₂_one_khovanovEulerChar_eq_two_pow hD R
  rw [h0, map_zero] at h
  exact pow_ne_zero D.componentCount (by decide : (2 : ℤ) ≠ 0) h.symm

/-- For every planar oriented PD-code `D`, some quantum degree `j ≡ D.componentCount (mod 2)` has a
nonzero coefficient in `D.khovanovEulerChar hD R`. -/
theorem exists_coeff_khovanovEulerChar_ne_zero :
    ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧ (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
  have ⟨j, hj⟩ : ∃ j : ℤ, (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
    by_contra! hall
    exact D.khovanovEulerChar_ne_zero hD R
      (AddMonoidAlgebra.coeff_injective <| Finsupp.ext hall)
  exact ⟨j, by_contra fun hmod ↦ hj (D.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne hD R hmod), hj⟩

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
  exact ⟨i, Finset.mem_Icc.mp himem, j, hjmod, Nat.pos_of_ne_zero fun h0 ↦ hine (by simp [h0])⟩

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
