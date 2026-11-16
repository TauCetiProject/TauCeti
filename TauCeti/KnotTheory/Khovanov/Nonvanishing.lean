/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.PDCode.ChangeCrossing
public import TauCeti.KnotTheory.PDCode.VertexResolution
import Mathlib.Algebra.Field.Rat
import TauCeti.KnotTheory.Khovanov.Parity
import TauCeti.KnotTheory.PDCode.Oriented.Component
import TauCeti.Logic.Equiv.Basic

/-!
# The normalized enhanced-state Euler sum and nonvanishing of Khovanov homology

Specializing the enhanced state sum `TauCeti.OrientedPDCode.enhancedStateSum` of an oriented
PD-code `D` at `q = 1` sets `q + q⁻¹ = 2` and `q ^ shift = 1`, giving the **normalized
enhanced-state Euler sum**

`E(D) = ∑_s (-1) ^ (|S| + n₋) 2 ^ k(s)`

(`TauCeti.OrientedPDCode.normalizedEulerSum`), where `S = {i | s i = false}` is the set of
`B`-smoothed crossings, `n₋` is the number of negative crossings, and `k(s)` is the number of
resolved circles.

Switching a single crossing `i` exchanges its `A`- and `B`-smoothings and shifts `n₋` by `±1`;
toggling each state at `i` via `Function.Involutive.updatePerm` changes `|S|` by `±1` while
preserving `k(s)`, so `E(D)` is invariant under crossing changes without any planarity assumption
(`TauCeti.OrientedPDCode.normalizedEulerSum_changeCrossing`).

When `D` is planar, the quantum-grading parity theorem
(`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two`) rewrites the sign of each
state purely in terms of the unoriented data `(componentCount, k(s), n)`:

`(-1) ^ (|S| + n₋) = (-1) ^ (c + k(s) + n)`.

In particular, `E(D)` does not depend on the choice of orientation of `D`
(`TauCeti.OrientedPDCode.normalizedEulerSum_eq_of_toPDCode_eq`), and splitting the state sum at a
crossing `c` into the `A`- and `B`-faces yields the normalized skein recurrence

`E(D) = -(-1) ^ c * ((-1) ^ c_A * E(D_A) + (-1) ^ c_B * E(D_B))`

(`TauCeti.OrientedPDCode.normalizedEulerSum_eq_resolveCrossing`) for any orientations chosen on the
two smoothings `D_A` and `D_B`. Combining this recurrence with orientability of smoothings
(`TauCeti.PDCode.exists_orientedPDCode`) and the component-count dichotomy (`c - 1` for both
smoothings of a two-component crossing, `{c, c + 1}` for a self-crossing) proves by induction on
the number of crossings that

`E(D) = 2 ^ c`

for every planar oriented code `D`, including crossing-free codes and the empty diagram
(`TauCeti.OrientedPDCode.normalizedEulerSum_eq_two_pow`).

Over any Noetherian commutative ring `R` with the rank-nullity property (in particular `ℤ` and `ℚ`),
Euler–Poincaré identifies `χ_q Kh(D; R)` with the enhanced state sum, so evaluating at `q = 1` gives
`2 ^ c ≥ 1`. Consequently `Kh(D; R)` has a bidegree `(i, j)` of positive rank — hence a nonzero
cohomology module — for every planar oriented diagram `D`, including the empty diagram.

## Main definitions

* `TauCeti.OrientedPDCode.normalizedEulerSum`: the normalized enhanced-state Euler sum `E(D)`.

## Main results

* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum` and
  `TauCeti.OrientedPDCode.laurentEval_one_enhancedStateSum`: evaluating `enhancedStateSum` at
  `q = 1` gives `normalizedEulerSum`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_changeCrossing`: crossing-change invariance of `E(D)`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_of_toPDCode_eq`: orientation independence of `E(D)`
  for planar codes.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_resolveCrossing`: normalized skein recurrence for
  `E(D)` across arbitrary oriented smoothings `D_A` and `D_B`.
* `TauCeti.OrientedPDCode.normalizedEulerSum_eq_two_pow`: `E(D) = 2 ^ D.componentCount` for every
  planar oriented code `D`.
* `TauCeti.OrientedPDCode.laurentEval_neg_one_jonesPolynomial` and
  `TauCeti.OrientedPDCode.jonesPolynomial_ne_zero`: for a nonempty planar diagram, evaluating the
  Jones polynomial at `t ^ (1/2) = -1` gives `2 ^ (c - 1)`, so `D.jonesPolynomial ≠ 0`.
* `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos` and
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology` (with specializations to `ℤ` and `ℚ`):
  Khovanov homology is nonzero for every planar oriented diagram, including `empty`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3 and
  Corollary 1.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Proposition 3.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset HomologicalComplex LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ}

/-! ### Definition and specialization from the enhanced state sum -/

/-- **The normalized enhanced-state Euler sum** `E(D) = ∑_s (-1) ^ (|S| + n₋) * 2 ^ k(s)` of an
oriented PD-code `D`, where `S = {i | s i = false}` is the set of crossings smoothed by `B`, `n₋`
is `D.negativeCrossingCount`, and `k(s) = D.stateLoopCount s`. -/
def normalizedEulerSum (D : OrientedPDCode n) : ℤ :=
  ∑ s : Fin n → Bool,
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) * 2 ^ D.stateLoopCount s

/-- The defining state sum of `normalizedEulerSum`. -/
theorem normalizedEulerSum_def (D : OrientedPDCode n) :
    D.normalizedEulerSum = ∑ s : Fin n → Bool,
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) * 2 ^ D.stateLoopCount s :=
  (rfl)

/-- `normalizedEulerSum` written over subsets `S : Finset (Fin n)` of `B`-smoothed crossings. -/
theorem normalizedEulerSum_eq_sum_cubeState (D : OrientedPDCode n) :
    D.normalizedEulerSum = ∑ S : Finset (Fin n),
      (-1 : ℤ) ^ (#S + D.negativeCrossingCount) * 2 ^ D.stateLoopCount (PDCode.cubeState S) := by
  rw [normalizedEulerSum_def, ← Fintype.sum_bijective _ PDCode.cubeState_bijective _ _ fun S ↦ by
    rw [PDCode.filter_cubeState_eq_false]]

private theorem negOnePow_stateCochainDegree_eq (D : OrientedPDCode n) (s : Fin n → Bool) :
    ((D.stateCochainDegree s).negOnePow : ℤ) =
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) := by
  have h : (D.stateCochainDegree s).negOnePow =
      ((#{i | s i = false} + D.negativeCrossingCount : ℕ) : ℤ).negOnePow := by
    rw [stateCochainDegree_def, Int.negOnePow_eq_iff]
    exact ⟨-(D.negativeCrossingCount : ℤ), by push_cast; ring⟩
  rw [h, Int.negOnePow_def, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- **Evaluating the enhanced state sum at `q = 1`** in any commutative ring `S` casts
`D.normalizedEulerSum` to `S`. -/
theorem eval₂_one_enhancedStateSum {S : Type*} [CommRing S] (D : OrientedPDCode n) :
    eval₂ (Int.castRingHom S) 1 D.enhancedStateSum = (D.normalizedEulerSum : S) := by
  rw [enhancedStateSum_eq_sum, normalizedEulerSum_def, map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp [Units.smul_def, zsmul_eq_mul, negOnePow_stateCochainDegree_eq, one_add_one_eq_two]

/-- **Evaluating the enhanced state sum at `1 : ℤˣ`** gives `D.normalizedEulerSum`. -/
@[simp] theorem laurentEval_one_enhancedStateSum (D : OrientedPDCode n) :
    laurentEval (1 : ℤˣ) D.enhancedStateSum = D.normalizedEulerSum := by
  rw [laurentEval_eq_eval₂, Subsingleton.elim (algebraMap ℤ ℤ) (Int.castRingHom ℤ),
    eval₂_one_enhancedStateSum, Int.cast_id]

/-! ### Crossing-free diagrams, symmetries, and crossing-change invariance -/

/-- A crossing-free diagram has normalized Euler sum `2 ^ c`. -/
theorem normalizedEulerSum_eq_two_pow_of_zero_crossings (D : OrientedPDCode 0) :
    D.normalizedEulerSum = 2 ^ D.componentCount := by
  have h := congrArg (laurentEval (R := ℤ) (1 : ℤˣ)) (enhancedStateSum_eq_pow D)
  simpa [PDCode.componentCount_eq, one_add_one_eq_two] using h

/-- The empty diagram has normalized Euler sum `1`. -/
@[simp] theorem normalizedEulerSum_empty : empty.normalizedEulerSum = 1 := by
  rw [← laurentEval_one_enhancedStateSum, enhancedStateSum_empty, map_one]

/-- The unknot has normalized Euler sum `2`. -/
@[simp] theorem normalizedEulerSum_unknot (o : Bool) : (unknot o).normalizedEulerSum = 2 := by
  rw [← laurentEval_one_enhancedStateSum, enhancedStateSum_unknot, map_add]
  simp

/-- Reversing all component orientations preserves `normalizedEulerSum`. -/
@[simp] theorem normalizedEulerSum_reverse (D : OrientedPDCode n) :
    D.reverse.normalizedEulerSum = D.normalizedEulerSum := by
  simp [normalizedEulerSum_def]

/-- Rotating the slot numbering at a crossing preserves `normalizedEulerSum`. -/
@[simp] theorem normalizedEulerSum_rotateCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.rotateCrossing i).normalizedEulerSum = D.normalizedEulerSum := by
  have hn : (D.rotateCrossing i).negativeCrossingCount = D.negativeCrossingCount := by
    simp [negativeCrossingCount_def]
  simp [normalizedEulerSum_def, hn]

/-- Relabelling half-edges and crossings preserves `normalizedEulerSum`. -/
@[simp] theorem normalizedEulerSum_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).normalizedEulerSum = D.normalizedEulerSum := by
  let e : (Fin n → Bool) ≃ (Fin m → Bool) := Equiv.arrowCongr cross (Equiv.refl Bool)
  rw [normalizedEulerSum_def, normalizedEulerSum_def, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hcard : #{j : Fin m | e s j = false} = #{i : Fin n | s i = false} := by
    rw [Finset.card_filter, Finset.card_filter, ← Equiv.sum_comp cross]
    simp [e]
  have hcomp : e s ∘ cross = s := by
    funext i
    simp [e]
  rw [hcard, negativeCrossingCount_relabel, relabel_toPDCode, PDCode.stateLoopCount_relabel, hcomp]

/-- Mirroring preserves `normalizedEulerSum`. -/
@[simp] theorem normalizedEulerSum_mirror (D : OrientedPDCode n) :
    D.mirror.normalizedEulerSum = D.normalizedEulerSum := by
  let negState : (Fin n → Bool) ≃ (Fin n → Bool) := Equiv.piCongrRight fun _ ↦ Equiv.boolNot
  rw [normalizedEulerSum_def, normalizedEulerSum_def, ← Equiv.sum_comp negState]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hnot : ({i : Fin n | negState s i = false} : Finset (Fin n)) =
      ({i : Fin n | ¬ (s i = false)} : Finset (Fin n)) := by
    ext i
    cases hs : s i <;> simp [negState, hs]
  have hcard : #{i : Fin n | s i = false} + #{i : Fin n | negState s i = false} = n := by
    rw [hnot, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hcross := D.positiveCrossingCount_add_negativeCrossingCount
  have hsign : (-1 : ℤ) ^ (#{i | negState s i = false} + D.mirror.negativeCrossingCount) =
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) := by
    rw [negativeCrossingCount_mirror]
    refine neg_one_pow_congr ?_
    rw [Nat.even_iff, Nat.even_iff]
    omega
  have hloop : D.mirror.stateLoopCount (negState s) = D.stateLoopCount s := by
    rw [mirror_toPDCode, PDCode.stateLoopCount_mirror]
    congr 1
    funext i
    simp [negState]
  rw [hsign, hloop]

/-- **Crossing-change invariance of the normalized Euler sum.** Switching any crossing leaves
`normalizedEulerSum` unchanged, without any planarity assumption. -/
@[simp] theorem normalizedEulerSum_changeCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.changeCrossing i).normalizedEulerSum = D.normalizedEulerSum := by
  -- Toggling each state at `i` preserves `stateLoopCount` and shifts `|S| + n₋` by an even integer.
  let toggle : Equiv.Perm (Fin n → Bool) := Bool.involutive_not.updatePerm i
  rw [normalizedEulerSum_def, normalizedEulerSum_def, ← Equiv.sum_comp toggle]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hloop : (D.changeCrossing i).stateLoopCount (toggle s) = D.stateLoopCount s := by
    rw [toPDCode_changeCrossing, PDCode.stateLoopCount_changeCrossing]
    simp only [toggle, Function.Involutive.updatePerm_apply]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hcard : #{j | toggle s j = false} + (if s i = false then 1 else 0) =
      #{j | s j = false} + (if (!s i) = false then 1 else 0) := by
    rw [Finset.card_filter, Finset.card_filter, Fintype.sum_eq_add_sum_compl i,
      Fintype.sum_eq_add_sum_compl i (fun j ↦ if s j = false then 1 else 0)]
    have hcompl : ∑ x ∈ ({i}ᶜ : Finset (Fin n)), (if toggle s x = false then 1 else 0) =
        ∑ x ∈ ({i}ᶜ : Finset (Fin n)), (if s x = false then 1 else 0) :=
      Finset.sum_congr rfl fun x hx ↦ by
        simp only [toggle, Function.Involutive.updatePerm_apply,
          Function.update_of_ne (by simpa using hx)]
    rw [hcompl]
    simp only [toggle, Function.Involutive.updatePerm_apply, Function.update_self]
    omega
  have hsign : (-1 : ℤ) ^ (#{j | toggle s j = false} +
        (D.changeCrossing i).negativeCrossingCount) =
      (-1 : ℤ) ^ (#{j | s j = false} + D.negativeCrossingCount) := by
    refine neg_one_pow_congr ?_
    rw [Nat.even_iff, Nat.even_iff]
    rcases D.crossingSign_eq_one_or_neg_one i with hi | hi
    · have hn := D.negativeCrossingCount_changeCrossing_of_crossingSign_eq_one i hi
      cases hs : s i <;>
        simp only [hs, Bool.not_false, Bool.not_true, Bool.true_eq_false, ↓reduceIte] at hcard <;>
        omega
    · have hn := D.negativeCrossingCount_changeCrossing_add_one_of_crossingSign_eq_neg_one i hi
      cases hs : s i <;>
        simp only [hs, Bool.not_false, Bool.not_true, Bool.true_eq_false, ↓reduceIte] at hcard <;>
        omega
  rw [hsign, hloop]

/-! ### Planar parity, orientation independence, skein recurrence, and evaluation `2 ^ c` -/

/-- For a planar oriented diagram `D`, the state sign `(-1) ^ (|S| + n₋)` equals
`(-1) ^ (c + k(s) + n)`, which depends only on the underlying unoriented code `D.toPDCode`. -/
theorem neg_one_pow_card_false_add_negativeCrossingCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) (s : Fin n → Bool) :
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) =
      (-1 : ℤ) ^ (D.componentCount + D.stateLoopCount s + n) := by
  have hp := D.stateQuantumShift_add_stateLoopCount_mod_two hD s
  rw [stateQuantumShift_def] at hp
  have hc := D.positiveCrossingCount_add_negativeCrossingCount
  refine neg_one_pow_congr ?_
  rw [Nat.even_iff, Nat.even_iff]
  omega

/-- **Reorientation independence.** Two planar oriented PD-codes with the same underlying
unoriented code have the same `normalizedEulerSum`. -/
theorem normalizedEulerSum_eq_of_toPDCode_eq {D E : OrientedPDCode n} (hD : D.toPDCode.IsPlanar)
    (h : D.toPDCode = E.toPDCode) :
    D.normalizedEulerSum = E.normalizedEulerSum := by
  have hE : E.toPDCode.IsPlanar := h ▸ hD
  rw [normalizedEulerSum_def, normalizedEulerSum_def]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [D.neg_one_pow_card_false_add_negativeCrossingCount hD s,
    E.neg_one_pow_card_false_add_negativeCrossingCount hE s, h]

private theorem normalizedEulerSum_insertNth_term (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) (t : Bool) {E : OrientedPDCode n}
    (hE : E.toPDCode.IsPlanar) (ht : E.toPDCode = D.toPDCode.resolveCrossing c t)
    (s : Fin n → Bool) :
    (-1 : ℤ) ^
        (#{i | c.insertNth (α := fun _ ↦ Bool) t s i = false} + D.negativeCrossingCount) *
        2 ^ D.stateLoopCount (c.insertNth (α := fun _ ↦ Bool) t s) =
      -(-1 : ℤ) ^ D.componentCount * ((-1 : ℤ) ^ E.componentCount *
        ((-1 : ℤ) ^ (#{i | s i = false} + E.negativeCrossingCount) *
          2 ^ E.stateLoopCount s)) := by
  rw [D.neg_one_pow_card_false_add_negativeCrossingCount hD
      (c.insertNth (α := fun _ ↦ Bool) t s),
    E.neg_one_pow_card_false_add_negativeCrossingCount hE s,
    D.toPDCode.stateLoopCount_insertNth c t s, ← ht]
  set cD := D.componentCount
  set cE := E.componentCount
  simp only [pow_add, pow_one]
  rcases neg_one_pow_eq_or ℤ cE with hcE | hcE <;> rw [hcE] <;> ring

/-- **Normalized skein recurrence for `normalizedEulerSum`.** Let `D` be a planar oriented code
with `n + 1` crossings, `c` one of its crossings, and `D_A`, `D_B` any oriented codes whose
underlying unoriented codes are the `A`- and `B`-resolutions of `D` at `c`. Then

`E(D) = -(-1) ^ c(D) * ((-1) ^ c(D_A) * E(D_A) + (-1) ^ c(D_B) * E(D_B))`. -/
theorem normalizedEulerSum_eq_resolveCrossing (D : OrientedPDCode (n + 1))
    (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) {D_A D_B : OrientedPDCode n}
    (hA : D_A.toPDCode = D.toPDCode.resolveCrossing c true)
    (hB : D_B.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.normalizedEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ D_A.componentCount * D_A.normalizedEulerSum +
          (-1 : ℤ) ^ D_B.componentCount * D_B.normalizedEulerSum) := by
  have hPA : D_A.toPDCode.IsPlanar := hA ▸ hD.resolveCrossing _ c true
  have hPB : D_B.toPDCode.IsPlanar := hB ▸ hD.resolveCrossing _ c false
  -- Split the state sum at `c` into its `A`- (`true`) and `B`- (`false`) faces via `insertNth`.
  rw [D.normalizedEulerSum_def, ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.insertNthEquiv_apply,
    D_A.normalizedEulerSum_def, D_B.normalizedEulerSum_def, mul_add, Finset.mul_sum]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun s _ ↦ D.normalizedEulerSum_insertNth_term hD c true hPA hA s)
    (Finset.sum_congr rfl fun s _ ↦ D.normalizedEulerSum_insertNth_term hD c false hPB hB s)

/-- **The normalized enhanced-state Euler sum of a planar oriented PD-code with `c` components is
`2 ^ c`**, including crossing-free codes and the empty diagram (`c = 0`, `2 ^ 0 = 1`). -/
theorem normalizedEulerSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    D.normalizedEulerSum = 2 ^ D.componentCount := by
  induction n with
  | zero => exact D.normalizedEulerSum_eq_two_pow_of_zero_crossings
  | succ n ih =>
    obtain ⟨D_A, hA⟩ := (D.toPDCode.resolveCrossing 0 true).exists_orientedPDCode
    obtain ⟨D_B, hB⟩ := (D.toPDCode.resolveCrossing 0 false).exists_orientedPDCode
    have hPA : D_A.toPDCode.IsPlanar := hA ▸ hD.resolveCrossing _ 0 true
    have hPB : D_B.toPDCode.IsPlanar := hB ▸ hD.resolveCrossing _ 0 false
    rw [D.normalizedEulerSum_eq_resolveCrossing hD 0 hA hB, ih D_A hPA, ih D_B hPB]
    have hcA : D_A.componentCount = (D.toPDCode.resolveCrossing 0 true).componentCount := by
      rw [hA]
    have hcB : D_B.componentCount = (D.toPDCode.resolveCrossing 0 false).componentCount := by
      rw [hB]
    rw [hcA, hcB]
    rcases D.toPDCode.componentCount_resolveCrossing_alternatives 0 with
      ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · set k := (D.toPDCode.resolveCrossing 0 true).componentCount
      have hk : (D.toPDCode.resolveCrossing 0 false).componentCount = k := by omega
      have hDk : D.componentCount = k + 1 := by omega
      rw [hk, hDk, pow_succ (-1 : ℤ) k, pow_succ (2 : ℤ) k]
      rcases neg_one_pow_eq_or ℤ k with hk' | hk' <;> rw [hk'] <;> ring
    · set k := D.toPDCode.componentCount
      rw [h₁, h₂, pow_succ (-1 : ℤ) k, pow_succ (2 : ℤ) k]
      rcases neg_one_pow_eq_or ℤ k with hk' | hk' <;> rw [hk'] <;> ring
    · set k := D.toPDCode.componentCount
      rw [h₁, h₂, pow_succ (-1 : ℤ) k, pow_succ (2 : ℤ) k]
      rcases neg_one_pow_eq_or ℤ k with hk' | hk' <;> rw [hk'] <;> ring

/-! ### Consequences for the enhanced state sum, Jones polynomial, and Khovanov homology -/

section Planar

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
include hD

/-- Evaluating `D.enhancedStateSum` at `1` in `S` gives `2 ^ D.componentCount`. -/
theorem eval₂_one_enhancedStateSum_eq_two_pow {S : Type*} [CommRing S] :
    eval₂ (Int.castRingHom S) 1 D.enhancedStateSum = 2 ^ D.componentCount := by
  simp [D.eval₂_one_enhancedStateSum, D.normalizedEulerSum_eq_two_pow hD]

/-- Evaluating `D.enhancedStateSum` at `1 : ℤˣ` gives `2 ^ D.componentCount`. -/
theorem laurentEval_one_enhancedStateSum_eq_two_pow :
    laurentEval (1 : ℤˣ) D.enhancedStateSum = 2 ^ D.componentCount := by
  rw [laurentEval_one_enhancedStateSum, D.normalizedEulerSum_eq_two_pow hD]

/-- The enhanced state sum of any planar oriented diagram (including `empty`) is nonzero. -/
theorem enhancedStateSum_ne_zero : D.enhancedStateSum ≠ 0 := by
  intro h
  have h0 := congrArg (laurentEval (R := ℤ) (1 : ℤˣ)) h
  rw [D.laurentEval_one_enhancedStateSum_eq_two_pow hD, map_zero] at h0
  exact pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0) h0

/-- **Evaluating the Jones polynomial of a nonempty planar diagram at `t ^ (1/2) = -1`** gives
`2 ^ (c - 1)` (cf. Lickorish, Proposition 3.6, whose `(-2) ^ (c - 1)` at `t ^ (1/2) = 1` becomes
`2 ^ (c - 1)` at `t ^ (1/2) = -1` since the exponents of `t ^ (1/2)` have the parity of
`c - 1`). -/
theorem laurentEval_neg_one_jonesPolynomial (hc : 0 < D.componentCount) :
    laurentEval (-1 : ℤˣ) D.jonesPolynomial = 2 ^ (D.componentCount - 1) := by
  let g : ℤ[T;T⁻¹] →ₐ[ℤ] ℤ := laurentEval (1 : ℤˣ)
  have hsub : eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial =
      laurentEval (-genericUnit ℤ) D.jonesPolynomial := by
    rw [laurentEval_eq_eval₂, Subsingleton.elim (algebraMap ℤ ℤ[T;T⁻¹]) (Int.castRingHom ℤ[T;T⁻¹])]
  have hu : Units.map (g : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) = (-1 : ℤˣ) := by
    ext
    simp [g]
  have hgD : g D.enhancedStateSum = 2 ^ D.componentCount :=
    D.laurentEval_one_enhancedStateSum_eq_two_pow hD
  have hg1 : g (T 1) = 1 := by simp [g]
  have hgm1 : g (T (-1)) = 1 := by simp [g]
  have heval := congrArg g (D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hc)
  rw [hgD, hsub, map_mul, map_add, hg1, hgm1, one_add_one_eq_two, ← AlgHom.comp_apply,
    comp_laurentEval, hu] at heval
  have hpow : (2 : ℤ) ^ D.componentCount = 2 * 2 ^ (D.componentCount - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hc), pow_succ']
  rw [hpow] at heval
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) heval.symm

/-- Evaluating `D.jonesPolynomial` at `-1` in any commutative ring `S` gives `2 ^ (c - 1)`. -/
theorem eval₂_neg_one_jonesPolynomial {S : Type*} [CommRing S] (hc : 0 < D.componentCount) :
    eval₂ (Int.castRingHom S) (-1) D.jonesPolynomial = 2 ^ (D.componentCount - 1) := by
  let φ : ℤ →ₐ[ℤ] S := Algebra.ofId ℤ S
  have h := congrArg φ (D.laurentEval_neg_one_jonesPolynomial hD hc)
  have hu : Units.map (φ : ℤ →* S) (-1 : ℤˣ) = (-1 : Sˣ) := by
    ext
    simp [φ]
  rw [← AlgHom.comp_apply, comp_laurentEval, hu, laurentEval_eq_eval₂,
    Subsingleton.elim (algebraMap ℤ S) (Int.castRingHom S)] at h
  simpa [φ] using h

/-- The Jones polynomial of any nonempty planar oriented diagram is nonzero. -/
theorem jonesPolynomial_ne_zero (hc : 0 < D.componentCount) : D.jonesPolynomial ≠ 0 := by
  intro h
  have h0 := congrArg (laurentEval (R := ℤ) (-1 : ℤˣ)) h
  rw [D.laurentEval_neg_one_jonesPolynomial hD hc, map_zero] at h0
  exact pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0) h0

section Homology

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- Evaluating `χ_q Kh(D; R)` at `1 : ℤˣ` gives `2 ^ D.componentCount`. -/
theorem laurentEval_one_khovanovEulerChar :
    laurentEval (1 : ℤˣ) (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R,
    D.laurentEval_one_enhancedStateSum_eq_two_pow hD]

/-- Evaluating `χ_q Kh(D; R)` at `1` in `S` gives `2 ^ D.componentCount`. -/
theorem eval₂_one_khovanovEulerChar {S : Type*} [CommRing S] :
    eval₂ (Int.castRingHom S) 1 (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R,
    D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- The graded Euler characteristic `χ_q Kh(D; R)` is nonzero for every planar oriented code `D`,
including `empty`. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R]
  exact D.enhancedStateSum_ne_zero hD

/-- Total homology rank lower bound: the sum of `Module.finrank R (Khⁱʲ(D; R))` over the active
quantum support and normalized cochain interval `[-n₋, n₊]` is at least `2 ^ D.componentCount`. -/
theorem two_pow_componentCount_le_sum_finrank_khovanovHomology :
    2 ^ D.componentCount ≤
      ∑ j ∈ (D.khovanovEulerChar hD R).coeff.support,
        ∑ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
          Module.finrank R (D.khovanovHomology hD R i j) := by
  have heval := D.laurentEval_one_khovanovEulerChar hD R
  rw [laurentEval_one_eq_sum, Finsupp.sum] at heval
  have hle : ∑ j ∈ (D.khovanovEulerChar hD R).coeff.support, (D.khovanovEulerChar hD R).coeff j ≤
      ∑ j ∈ (D.khovanovEulerChar hD R).coeff.support,
        ∑ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
          (Module.finrank R (D.khovanovHomology hD R i j) : ℤ) := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hsign : (i.negOnePow : ℤ) ≤ 1 := by
      have habs := Int.abs_negOnePow i
      exact le_of_abs_le (by omega)
    simpa using mul_le_mul_of_nonneg_right hsign
      (Nat.cast_nonneg (Module.finrank R (D.khovanovHomology hD R i j)))
  rw [heval] at hle
  exact_mod_cast hle

/-- **Nonvanishing of Khovanov homology (with cochain support bound).** Over a Noetherian
commutative ring `R` with the rank-nullity property, every planar oriented diagram `D` (including
`empty`) has a cochain degree `i ∈ [-n₋, n₊]` and a quantum degree `j ≡ c (mod 2)` in which
`Khⁱʲ(D; R)` has positive rank. -/
theorem exists_mem_Icc_finrank_khovanovHomology_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  have hne := D.khovanovEulerChar_ne_zero hD R
  have hexJ : ∃ j : ℤ, (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
    by_contra! hall
    exact hne (AddMonoidAlgebra.coeff_injective (Finsupp.ext fun j ↦ by simpa using hall j))
  obtain ⟨j, hj⟩ := hexJ
  have hmod : j % 2 = (D.componentCount : ℤ) % 2 := by
    by_contra hmod
    rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.coeff_enhancedStateSum R j] at hj
    refine hj (Finset.sum_eq_zero fun s _ ↦ ?_)
    rw [D.circleQuantumGrading_piece_eq_bot_of_mod_two_ne hD R s hmod,
      finrank_bot, Nat.cast_zero, smul_zero]
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j] at hj
  obtain ⟨i, hi, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  have hpos : 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
    by_contra h0
    simp [Nat.eq_zero_of_not_pos h0] at hterm
  exact ⟨i, hi, j, hmod, hpos⟩

/-- **Nonvanishing of Khovanov homology (rank form)** over any Noetherian commutative ring `R`
with the rank-nullity property, including the empty diagram. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i j : ℤ, 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  obtain ⟨i, -, j, -, hpos⟩ := D.exists_mem_Icc_finrank_khovanovHomology_pos hD R
  exact ⟨i, j, hpos⟩

/-- **Nonvanishing of Khovanov homology** over any Noetherian commutative ring `R` with the
rank-nullity property, including the empty diagram. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i j : ℤ, ¬ IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, j, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  refine ⟨i, j, fun hz ↦ ?_⟩
  rw [ModuleCat.finrank_eq_zero_of_isZero hz] at hpos
  exact lt_irrefl 0 hpos

end Homology

/-- **Integral Khovanov homology is nonzero** for every planar oriented diagram `D`, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_int :
    ∃ i j : ℤ, ¬ IsZero (D.khovanovHomology hD ℤ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℤ

/-- **Rational Khovanov homology is nonzero** for every planar oriented diagram `D`, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_rat :
    ∃ i j : ℤ, ¬ IsZero (D.khovanovHomology hD ℚ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℚ

end Planar

end TauCeti.OrientedPDCode
