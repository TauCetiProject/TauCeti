/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EnhancedState.Parity
public import TauCeti.KnotTheory.PDCode.ChangeCrossing
public import TauCeti.KnotTheory.PDCode.Oriented.VertexResolution
import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar

/-!
# Invariance and smoothing recurrences of the enhanced-state Euler sum

This file proves crossing-change invariance, planar reorientation invariance, and the normalized
parity smoothing recurrence for the normalized enhanced-state Euler sum
`TauCeti.OrientedPDCode.enhancedStateEulerSum` (defined in
`TauCeti.KnotTheory.Khovanov.EnhancedState.Basic`), without any homology dependencies.

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

## Main results

* `TauCeti.OrientedPDCode.enhancedStateEulerSum_changeCrossing`: crossing-change invariance of
  `E(D)`.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_congr_toPDCode`: reorientation invariance of `E(D)`
  for planar diagrams.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing` and
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_resolveCrossingOriented`: the normalized parity
  recurrence across arbitrary oriented smoothings of a crossing.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
-/

public section

open Finset

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-! ### Crossing-change invariance -/

/-- **Crossing-change invariance of `E(D)`.** Switching crossing `i` between over and under leaves
`E(D)` unchanged, without any planarity assumption. -/
@[simp] theorem enhancedStateEulerSum_changeCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.changeCrossing i).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def,
    ← Equiv.sum_comp (PDCode.flipStateEquiv i)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hmod := D.card_false_flipStateEquiv_add_negativeCrossingCount_changeCrossing_mod_two i s
  rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two, toPDCode_changeCrossing,
    D.toPDCode.stateLoopCount_changeCrossing_flipStateEquiv i s]

/-! ### Planar parity, reorientation invariance, and the normalized recurrence -/

/-- **Reorientation invariance of `E(D)` for planar diagrams.** Two oriented PD-codes sharing the
same underlying planar PD-code have the same enhanced-state Euler sum. -/
theorem enhancedStateEulerSum_congr_toPDCode {D₁ D₂ : OrientedPDCode n}
    (hD₁ : D₁.toPDCode.IsPlanar) (h : D₁.toPDCode = D₂.toPDCode) :
    D₁.enhancedStateEulerSum = D₂.enhancedStateEulerSum := by
  have hmod := negativeCrossingCount_mod_two_congr_toPDCode hD₁ h
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [h]
  congr 1
  exact neg_one_pow_congr (by simp only [Nat.even_iff]; omega)

/-- At a single smoothing branch `t : Bool` of crossing `c` of a planar diagram `D`, the signed
state sum over states sending `c ↦ t` equals
`-(-1) ^ D.componentCount * (-1) ^ E.componentCount * E.enhancedStateEulerSum` for **any**
orientation `E` of `D.toPDCode.resolveCrossing c t`. -/
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
        (#{j | s j = false} + E.negativeCrossingCount)) :=
    neg_one_pow_congr (by simp only [Nat.even_iff]; omega)
  rw [hsign, hloop, pow_add, pow_add, pow_add, pow_one]
  ring

/-- **Normalized parity recurrence for `E(D)` across arbitrary oriented smoothings.** For any
planar oriented diagram `D` with `n + 1` crossings, any crossing `c`, and any oriented diagrams
`D_A` and `D_B` whose underlying unoriented codes are the `A`- and `B`-resolutions of `c`
(regardless of how their components are reoriented),
`E(D) = -(-1) ^ D.componentCount * ((-1) ^ D_A.componentCount * E(D_A) +`
`(-1) ^ D_B.componentCount * E(D_B))`. -/
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
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
    (detachedA : Multiset Bool) (hA : detachedA.card = D.toPDCode.detachedCircleCount c true)
    (detachedB : Multiset Bool) (hB : detachedB.card = D.toPDCode.detachedCircleCount c false) :
    D.enhancedStateEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ (D.resolveCrossingOriented c true detachedA hA).componentCount *
            (D.resolveCrossingOriented c true detachedA hA).enhancedStateEulerSum +
          (-1 : ℤ) ^ (D.resolveCrossingOriented c false detachedB hB).componentCount *
            (D.resolveCrossingOriented c false detachedB hB).enhancedStateEulerSum) :=
  D.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing hD c
    (D.toPDCode_resolveCrossingOriented c true detachedA hA)
    (D.toPDCode_resolveCrossingOriented c false detachedB hB)

end TauCeti.OrientedPDCode
