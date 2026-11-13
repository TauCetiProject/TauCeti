/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Parity
public import TauCeti.KnotTheory.PDCode.ChangeCrossing
public import TauCeti.KnotTheory.PDCode.Oriented.VertexResolution

/-!
# The enhanced-state Euler sum and nonvanishing of Khovanov homology

Specializing the enhanced state sum `TauCeti.OrientedPDCode.enhancedStateSum` of an oriented
PD-code `D` at `q = 1` gives the **normalized enhanced-state Euler sum**
`TauCeti.OrientedPDCode.enhancedStateEulerSum`:

`E(D) = ∑_s (-1) ^ (|s| + n₋) 2 ^ k(s)`,

where `|s| = #{i | s i = false}` is the number of `B`-smoothings selected by `s`, `n₋` is the
number of negative crossings of `D`, and `k(s)` is the number of resolved circles of `s`.

Without any planarity hypothesis, `E(D)` is invariant under crossing changes: flipping the
smoothing bit at `i` via `TauCeti.PDCode.flipStateEquiv` preserves `k(s)` on `D.changeCrossing i`
while preserving the parity of `|s| + n₋`
(`TauCeti.OrientedPDCode.enhancedStateEulerSum_changeCrossing`).

When `D` is planar with `c` link components, the quantum-grading parity theorem
`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two` shows two things:

* `E(D)` depends only on the underlying unoriented planar diagram, so reorienting any subset of
  components leaves `E(D)` unchanged
  (`TauCeti.OrientedPDCode.enhancedStateEulerSum_congr_toPDCode`);
* resolving any crossing `c₀` into planar oriented diagrams `D_A` and `D_B` (with any choice of
  component orientations on the two smoothings) satisfies the normalized parity recurrence
  `E(D) = -(-1) ^ c * ((-1) ^ c_A * E(D_A) + (-1) ^ c_B * E(D_B))`
  (`TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing`).

Combining this recurrence with the crossing-free base value `E(D) = 2 ^ c` and the component-count
alternatives from `TauCeti.KnotTheory.PDCode.Oriented.VertexResolution`—at a crossing between two
different components both smoothings have `c - 1` components, whereas at a self-crossing their
component counts are `{c, c + 1}`—inducting on the number of crossings proves `E(D) = 2 ^ c` for
every planar oriented diagram
(`TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`).

Consequently, over every nontrivial Noetherian commutative ring `R` satisfying rank-nullity—and in
particular over `ℤ` and `ℚ`—the graded Euler characteristic `χ_q Kh(D; R)` evaluates to `2 ^ c` at
`q = 1`, hence is nonzero, so `Khⁱʲ(D; R)` is nonzero in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` for every planar link diagram, including the empty diagram.

## Main definitions

* `TauCeti.OrientedPDCode.enhancedStateEulerSum`: the normalized enhanced-state Euler sum
  `E(D) = ∑_s (-1) ^ (|s| + n₋) 2 ^ k(s)`.

## Main results

* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum`: evaluating `enhancedStateSum` at `q = 1`
  yields `enhancedStateEulerSum`.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_changeCrossing`: crossing-change invariance of
  `E(D)` via the `A`/`B` state bijection.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_congr_toPDCode`: reorientation invariance of `E(D)`
  for planar diagrams.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing` and
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_resolveCrossingOriented`: the normalized parity
  recurrence across arbitrary oriented smoothings of a crossing.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`: `E(D) = 2 ^ c` for
  every planar oriented code `D` with `c` components.
* `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`: for a nonempty planar code, evaluating
  the Jones polynomial at `t ^ (1/2) = -1` gives `2 ^ (c - 1)`.
* `TauCeti.OrientedPDCode.eval₂_one_khovanovEulerChar` and
  `TauCeti.OrientedPDCode.khovanovEulerChar_ne_zero`: `χ_q Kh(D; R)` evaluates to `2 ^ c` at
  `q = 1` and is nonzero, including for the empty diagram.
* `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos` and
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology` (with explicit specializations to `ℤ`
  and `ℚ`): Khovanov homology is nonzero for every planar oriented link diagram, including the
  empty diagram.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Proposition 3.7.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), §12.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ}

/-! ### Definition, `q = 1` specialization, and crossing-free base cases -/

/-- **The normalized enhanced-state Euler sum** `E(D) = ∑_s (-1) ^ (|s| + n₋) 2 ^ k(s)` of an
oriented PD-code `D`, where `|s| = #{i | s i = false}` counts the `B`-smoothings in `s`, `n₋` is
`D.negativeCrossingCount`, and `k(s)` is `D.toPDCode.stateLoopCount s`. -/
def enhancedStateEulerSum (D : OrientedPDCode n) : ℤ :=
  ∑ s : Fin n → Bool,
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) * 2 ^ D.toPDCode.stateLoopCount s

/-- Defining sum of `TauCeti.OrientedPDCode.enhancedStateEulerSum`. -/
theorem enhancedStateEulerSum_def (D : OrientedPDCode n) :
    D.enhancedStateEulerSum = ∑ s : Fin n → Bool,
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
        2 ^ D.toPDCode.stateLoopCount s := (rfl)

/-- The cochain-degree sign `(-1) ^ (|s| - n₋)` equals `(-1) ^ (|s| + n₋)`. -/
theorem coe_negOnePow_stateCochainDegree (D : OrientedPDCode n) (s : Fin n → Bool) :
    ((D.stateCochainDegree s).negOnePow : ℤ) =
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) := by
  rw [D.stateCochainDegree_def, Int.negOnePow_sub, ← Int.negOnePow_add, ← Nat.cast_add,
    Int.coe_negOnePow_natCast]

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

/-! ### Crossing-change invariance and diagram symmetries -/

/-- **Crossing-change invariance of `E(D)`.** Switching crossing `i` between over and under leaves
`E(D)` unchanged, proved directly by the `A`/`B` state-flip bijection
`TauCeti.PDCode.flipStateEquiv i` without any planarity assumption. -/
theorem enhancedStateEulerSum_changeCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.changeCrossing i).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def,
    ← Equiv.sum_comp (PDCode.flipStateEquiv i)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hmod := D.card_false_flipStateEquiv_add_negativeCrossingCount_mod_two i s
  have hsign : (-1 : ℤ) ^ (#{j | PDCode.flipStateEquiv i s j = false} +
        (D.changeCrossing i).negativeCrossingCount) =
      (-1 : ℤ) ^ (#{j | s j = false} + D.negativeCrossingCount) := by
    rw [← Int.coe_negOnePow_natCast, ← Int.coe_negOnePow_natCast]
    congr 1
    rw [Int.negOnePow_eq_iff, Int.even_iff]
    omega
  rw [hsign, toPDCode_changeCrossing, D.toPDCode.stateLoopCount_changeCrossing_flipStateEquiv i s]

/-- Reversing all component orientations preserves `E(D)`. -/
@[simp] theorem enhancedStateEulerSum_reverse (D : OrientedPDCode n) :
    D.reverse.enhancedStateEulerSum = D.enhancedStateEulerSum := by
  simp [enhancedStateEulerSum_def]

/-- Relabelling half-edges and crossings preserves `E(D)`. -/
@[simp] theorem enhancedStateEulerSum_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def,
    ← (Equiv.arrowCongr cross (Equiv.refl Bool)).sum_comp]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hcard : #{j | Equiv.arrowCongr cross (Equiv.refl Bool) s j = false} =
      #{j | s j = false} := by
    refine Finset.card_bij (fun j _ ↦ cross.symm j) (fun j hj ↦ ?_)
      (fun _ _ _ _ h ↦ cross.symm.injective h)
      (fun j hj ↦ ⟨cross j, by simpa [Equiv.arrowCongr_apply] using hj, cross.symm_apply_apply j⟩)
    simpa [Equiv.arrowCongr_apply] using hj
  have hloop : (D.relabel half cross).toPDCode.stateLoopCount
      (Equiv.arrowCongr cross (Equiv.refl Bool) s) = D.toPDCode.stateLoopCount s := by
    have hfn : Equiv.arrowCongr cross (Equiv.refl Bool) s = s ∘ cross.symm := rfl
    rw [relabel_toPDCode, PDCode.stateLoopCount_relabel, hfn]
    congr 1
    ext j
    simp
  rw [hcard, negativeCrossingCount_relabel, hloop]

/-! ### Planar parity, reorientation invariance, and the normalized recurrence -/

/-- **Reorientation invariance of `E(D)` for planar diagrams.** Any two oriented PD-codes sharing
the same underlying planar PD-code have the same `negativeCrossingCount` modulo `2`, hence the same
enhanced-state Euler sum. -/
theorem enhancedStateEulerSum_congr_toPDCode {D₁ D₂ : OrientedPDCode n}
    (hD₁ : D₁.toPDCode.IsPlanar) (h : D₁.toPDCode = D₂.toPDCode) :
    D₁.enhancedStateEulerSum = D₂.enhancedStateEulerSum := by
  have hD₂ : D₂.toPDCode.IsPlanar := h ▸ hD₁
  have hp₁ := D₁.stateQuantumShift_add_stateLoopCount_mod_two hD₁ (fun _ ↦ true)
  have hp₂ := D₂.stateQuantumShift_add_stateLoopCount_mod_two hD₂ (fun _ ↦ true)
  have hc₁ := D₁.positiveCrossingCount_add_negativeCrossingCount
  have hc₂ := D₂.positiveCrossingCount_add_negativeCrossingCount
  have hloop : D₁.toPDCode.stateLoopCount (fun _ ↦ true) =
      D₂.toPDCode.stateLoopCount (fun _ ↦ true) := by rw [h]
  have hcomp : D₁.toPDCode.componentCount = D₂.toPDCode.componentCount := by rw [h]
  rw [stateQuantumShift_def] at hp₁ hp₂
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hsign : (-1 : ℤ) ^ (#{i | s i = false} + D₁.negativeCrossingCount) =
      (-1 : ℤ) ^ (#{i | s i = false} + D₂.negativeCrossingCount) := by
    rw [← Int.coe_negOnePow_natCast, ← Int.coe_negOnePow_natCast]
    congr 1
    rw [Int.negOnePow_eq_iff, Int.even_iff]
    omega
  have hs_loop : D₁.toPDCode.stateLoopCount s = D₂.toPDCode.stateLoopCount s := by rw [h]
  rw [hsign, hs_loop]

/-- At a single smoothing branch `t : Bool` of crossing `c` of a planar diagram `D`, the signed
state sum over states sending `c ↦ t` equals `-(-1) ^ c(D) * (-1) ^ c(E) * E.enhancedStateEulerSum`
for **any** orientation `E` of `D.toPDCode.resolveCrossing c t`. -/
private theorem sum_insertNth_eq_of_toPDCode_resolveCrossing
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) (t : Bool)
    {E : OrientedPDCode n} (hE : E.toPDCode = D.toPDCode.resolveCrossing c t) :
    (∑ s : Fin n → Bool,
        (-1 : ℤ) ^ (#{j | Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s) j = false} +
            D.negativeCrossingCount) *
          2 ^ D.toPDCode.stateLoopCount (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s))) =
      -(-1 : ℤ) ^ D.componentCount * ((-1 : ℤ) ^ E.componentCount * E.enhancedStateEulerSum) := by
  have hE_planar : E.toPDCode.IsPlanar := by
    rw [hE]
    exact PDCode.IsPlanar.resolveCrossing D.toPDCode c t hD
  rw [E.enhancedStateEulerSum_def, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hpD := D.stateQuantumShift_add_stateLoopCount_mod_two hD
    (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s))
  have hpE := E.stateQuantumShift_add_stateLoopCount_mod_two hE_planar s
  have hcD := D.positiveCrossingCount_add_negativeCrossingCount
  have hcE := E.positiveCrossingCount_add_negativeCrossingCount
  have hloop : D.toPDCode.stateLoopCount (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s)) =
      E.toPDCode.stateLoopCount s := by
    rw [Fin.insertNthEquiv_apply, hE, D.toPDCode.stateLoopCount_insertNth c t s]
  rw [stateQuantumShift_def] at hpD hpE
  have hsign : (-1 : ℤ) ^ (#{j | Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s) j = false} +
        D.negativeCrossingCount) =
      (-1 : ℤ) ^ (1 + D.toPDCode.componentCount + E.toPDCode.componentCount +
        (#{j | s j = false} + E.negativeCrossingCount)) := by
    rw [← Int.coe_negOnePow_natCast, ← Int.coe_negOnePow_natCast]
    congr 1
    rw [Int.negOnePow_eq_iff, Int.even_iff]
    omega
  rw [hsign, hloop, pow_add, pow_add, pow_add, pow_one]
  ring

/-- **Normalized parity recurrence for `E(D)` across arbitrary oriented smoothings.** For any
planar oriented diagram `D` with `n + 1` crossings, any crossing `c`, and any oriented diagrams
`D_A` and `D_B` whose underlying unoriented codes are the `A`- and `B`-resolutions of `c`
(regardless of how their components are reoriented),
`E(D) = -(-1) ^ c(D) * ((-1) ^ c(D_A) * E(D_A) + (-1) ^ c(D_B) * E(D_B))`. -/
theorem enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
    {D_A D_B : OrientedPDCode n}
    (hA : D_A.toPDCode = D.toPDCode.resolveCrossing c true)
    (hB : D_B.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.enhancedStateEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ D_A.componentCount * D_A.enhancedStateEulerSum +
          (-1 : ℤ) ^ D_B.componentCount * D_B.enhancedStateEulerSum) := by
  rw [D.enhancedStateEulerSum_def, ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool,
    D.sum_insertNth_eq_of_toPDCode_resolveCrossing hD c true hA,
    D.sum_insertNth_eq_of_toPDCode_resolveCrossing hD c false hB, mul_add]

/-- Specialization of `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing`
to `TauCeti.OrientedPDCode.resolveCrossingOriented`. -/
theorem enhancedStateEulerSum_eq_resolveCrossingOriented
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) :
    D.enhancedStateEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ (D.resolveCrossingOriented c true).componentCount *
            (D.resolveCrossingOriented c true).enhancedStateEulerSum +
          (-1 : ℤ) ^ (D.resolveCrossingOriented c false).componentCount *
            (D.resolveCrossingOriented c false).enhancedStateEulerSum) :=
  D.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing hD c
    (D.toPDCode_resolveCrossingOriented c true) (D.toPDCode_resolveCrossingOriented c false)

/-! ### Closed form `E(D) = 2 ^ c` and evaluations -/

/-- **For every planar oriented PD-code `D` with `c` link components, `E(D) = 2 ^ c`.** -/
theorem enhancedStateEulerSum_eq_two_pow_componentCount :
    ∀ {n : ℕ} (D : OrientedPDCode n), D.toPDCode.IsPlanar →
      D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount
  | 0, D, _ => D.enhancedStateEulerSum_of_zero
  | n + 1, D, hD => by
    have hA_planar : (D.resolveCrossingOriented 0 true).toPDCode.IsPlanar := by
      rw [toPDCode_resolveCrossingOriented]
      exact PDCode.IsPlanar.resolveCrossing D.toPDCode 0 true hD
    have hB_planar : (D.resolveCrossingOriented 0 false).toPDCode.IsPlanar := by
      rw [toPDCode_resolveCrossingOriented]
      exact PDCode.IsPlanar.resolveCrossing D.toPDCode 0 false hD
    have ihA := enhancedStateEulerSum_eq_two_pow_componentCount _ hA_planar
    have ihB := enhancedStateEulerSum_eq_two_pow_componentCount _ hB_planar
    rw [D.enhancedStateEulerSum_eq_resolveCrossingOriented hD 0, ihA, ihB]
    simp only [toPDCode_resolveCrossingOriented]
    by_cases hc : D.crossingComponentOfHalfEdge (D.crossing 0 0) =
        D.crossingComponentOfHalfEdge (D.crossing 0 1)
    · have hsq : (-1 : ℤ) ^ D.toPDCode.componentCount *
          (-1 : ℤ) ^ D.toPDCode.componentCount = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rcases D.componentCount_resolveCrossing_true_and_false_of_eq 0 hc with
          ⟨hcA, hcB⟩ | ⟨hcA, hcB⟩
      · rw [hcA, hcB, pow_succ (-1 : ℤ), pow_succ (2 : ℤ)]
        calc _ = ((-1 : ℤ) ^ D.toPDCode.componentCount * (-1 : ℤ) ^ D.toPDCode.componentCount) *
              (2 : ℤ) ^ D.toPDCode.componentCount := by ring
          _ = (2 : ℤ) ^ D.toPDCode.componentCount := by rw [hsq, one_mul]
      · rw [hcA, hcB, pow_succ (-1 : ℤ), pow_succ (2 : ℤ)]
        calc _ = ((-1 : ℤ) ^ D.toPDCode.componentCount * (-1 : ℤ) ^ D.toPDCode.componentCount) *
              (2 : ℤ) ^ D.toPDCode.componentCount := by ring
          _ = (2 : ℤ) ^ D.toPDCode.componentCount := by rw [hsq, one_mul]
    · have hcA := D.componentCount_resolveCrossing_add_one_of_ne 0 hc true
      have hcB := D.componentCount_resolveCrossing_add_one_of_ne 0 hc false
      set m := (D.toPDCode.resolveCrossing 0 true).componentCount
      have hmB : (D.toPDCode.resolveCrossing 0 false).componentCount = m := by omega
      have hmD : D.toPDCode.componentCount = m + 1 := hcA.symm
      have hsq : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [hmB, hmD, pow_succ (-1 : ℤ) m, pow_succ (2 : ℤ) m]
      calc _ = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * ((2 : ℤ) ^ m * 2) := by ring
        _ = (2 : ℤ) ^ m * 2 := by rw [hsq, one_mul]

/-- **Evaluating the enhanced state sum of a planar diagram at `q = 1` gives `2 ^ c`.** -/
theorem eval₂_one_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = (2 : ℤ) ^ D.componentCount := by
  rw [D.eval₂_one_enhancedStateSum, D.enhancedStateEulerSum_eq_two_pow_componentCount hD]

/-- **Evaluating the Jones polynomial of a nonempty planar diagram at `t ^ (1/2) = -1` gives
`2 ^ (c - 1)`** (Jones 1985, §12; Lickorish 1997, Proposition 3.7). -/
theorem eval₂_neg_one_jonesPolynomial (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
    (hpos : 0 < D.toPDCode.componentCount) :
    eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial = (2 : ℤ) ^ (D.componentCount - 1) := by
  have hsum := congrArg (eval₂ (RingHom.id ℤ) (1 : ℤˣ))
    (D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hpos)
  rw [D.eval₂_one_enhancedStateSum_eq_two_pow hD, map_mul, map_add, eval₂_T, eval₂_T,
    LaurentPolynomial.hom_eval₂] at hsum
  have hhom : (eval₂ (RingHom.id ℤ) (1 : ℤˣ)).comp (Int.castRingHom ℤ[T;T⁻¹]) =
      RingHom.id ℤ := Subsingleton.elim _ _
  have hunit : Units.map (eval₂ (RingHom.id ℤ) (1 : ℤˣ) : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) =
      (-1 : ℤˣ) := by
    ext
    simp
  rw [hhom, hunit] at hsum
  obtain ⟨k, hk⟩ : ∃ k, D.toPDCode.componentCount = k + 1 := ⟨D.toPDCode.componentCount - 1, by
    omega⟩
  rw [hk, pow_succ'] at hsum
  rw [hk, Nat.add_sub_cancel]
  norm_num at hsum
  omega

/-! ### Graded Euler characteristic and nonvanishing of Khovanov homology -/

section Homology

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **At `q = 1`, the graded Euler characteristic `χ_q Kh(D; R)` equals `2 ^ c`.** -/
theorem eval₂_one_khovanovEulerChar :
    eval₂ (RingHom.id ℤ) 1 (D.khovanovEulerChar hD R) = (2 : ℤ) ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **The graded Euler characteristic of Khovanov homology is nonzero** for every planar oriented
diagram, including the empty diagram. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := by
  intro hzero
  have heval := D.eval₂_one_khovanovEulerChar hD R
  rw [hzero, map_zero] at heval
  exact (by positivity : (0 : ℤ) < (2 : ℤ) ^ D.componentCount).ne heval

/-- **Khovanov homology has positive rank in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`**,
for every planar oriented diagram (including the empty diagram) over any nontrivial Noetherian
ring satisfying rank-nullity. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  by_contra h
  refine D.khovanovEulerChar_ne_zero hD R
    (AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun j ↦ ?_)
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hzero : Module.finrank R (D.khovanovHomology hD R i j) = 0 :=
    Nat.eq_zero_of_not_pos fun hpos ↦ h ⟨i, hi, j, hpos⟩
  simp [hzero]

/-- **Nonvanishing of Khovanov homology**: for every planar oriented diagram (including the empty
diagram) and every nontrivial Noetherian ring `R` satisfying rank-nullity, `Khⁱʲ(D; R)` is nonzero
in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, fun hz ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hz)⟩

end Homology

section IntAndRat

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

/-- **Integral Khovanov homology has positive free rank in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- **Integral Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_int :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℤ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℤ

/-- **Rational Khovanov homology has positive dimension in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- **Rational Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_rat :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℚ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℚ

end IntAndRat

end TauCeti.OrientedPDCode

end
