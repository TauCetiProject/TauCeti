/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Relations
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the binary Montgomery-ladder invariant

Three true bits starting from `(3, 1)` on `y² = x³ + x` over `𝔽₇` give representatives
of `[7]P` and `[8]P`. The invariant certifies that the second is infinity without
assuming the order of `P`. Leading zero bits are also allowed. A distinguished
two-torsion input gives a zero pair after one true bit, illustrating why it is excluded
from `LadderRel.coordinates` while `LadderRel.cross_coordinates` still holds. Finally,
`LadderRel.map` transports composite-modulus derivations to prime-field derivations.
-/

namespace TauCeti.Montgomery

open WeierstrassCurve

-- Three bits, with the actual unnormalized raw outputs retained at each stage.
example [Fact (Nat.Prime 7)] :
    let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 (by
      rw [Affine.nonsingular_iff, Affine.equation_iff]
      norm_num
      decide +revert)
    (Pair.mk (2 : ZMod 7) 3).cross (coordinates 0 1 (7 • P)) = 0 ∧ 8 • P = 0 := by
  intro P
  have hP : P ≠ 0 := Affine.Point.some_ne_zero _
  have hPT : P ≠ twoTorsionPoint 0 (by simp) := by
    simpa [P, twoTorsionPoint_def] using
      (ZMod.natCast_eq_zero_iff 3 7).not.mpr (by decide)
  have h₁ : LadderRel (2 : ZMod 7) 4 ⟨3, 1⟩ 1 ⟨1, 5⟩ ⟨4, 4⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 7)) (D := 4) (S := ⟨3, 1⟩)).bit true
      using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;>
      (clear hPT hP P; decide +revert)
  have h₃ : LadderRel (2 : ZMod 7) 4 ⟨3, 1⟩ 3 ⟨2, 6⟩ ⟨0, 2⟩ := by
    convert h₁.bit true using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;>
      (clear hPT hP P h₁; decide +revert)
  have h₇ : LadderRel (2 : ZMod 7) 4 ⟨3, 1⟩ 7 ⟨2, 3⟩ ⟨1, 0⟩ := by
    convert h₃.bit true using 1 <;> norm_num <;> ext <;>
      norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def] <;>
      (clear hPT hP P h₃ h₁; decide +revert)
  have hinv := h₇.coordinates (A := 0) (B := 1) (P := P)
    ((ZMod.natCast_eq_zero_iff 2 7).not.mpr (by decide)) (by simp)
    ((ZMod.natCast_eq_zero_iff 4 7).not.mpr (by decide)) (by norm_num)
    (by simp [Pair.ne_zero_iff]) (by simp [P]) hP hPT
  refine ⟨hinv.2.1, (coordinates_z_eq_zero_iff (by simp)).mp ?_⟩
  simpa [Pair.cross_def] using hinv.2.2.2

-- The relation is meaningful over composite residue rings, and commutes with reduction.
example : ∃ U V, LadderRel (2 : ZMod 35) 4 ⟨22, 1⟩ 100 U V ∧
    LadderRel (2 : ZMod 5) 4 ⟨2, 1⟩ 100
      (U.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)))
      (V.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))) := by
  obtain ⟨U, V, h⟩ := LadderRel.exists_pairs (2 : ZMod 35) 4 ⟨22, 1⟩ 100
  refine ⟨U, V, h, ?_⟩
  let φ := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
  have h2 : φ 2 = 2 := by decide
  have h4 : φ 4 = 4 := by decide
  have hS : (⟨22, 1⟩ : Pair (ZMod 35)).map φ = ⟨2, 1⟩ := by
    ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide
  simpa only [h2, h4, hS] using h.map φ

-- Leading zeros preserve the index but can change the raw representatives.
example {K : Type*} [Field K] [DecidableEq K] {A B N D : K}
    (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hND : 4 * N = (A + 2) * D)
    {P : (model A B).toAffine.Point} (hP : P ≠ 0) (hPT : P ≠ twoTorsionPoint A hB) :
    double N D ⟨1, 0⟩ ≠ 0 ∧
      (diffAdd (coordinates A B P) ⟨1, 0⟩ (coordinates A B P)).cross
        (coordinates A B P) = 0 := by
  have h := (LadderRel.zero (N := N) (D := D) (S := coordinates A B P)).bit false
  have hinv := h.coordinates h₂ hB hD hND (coordinates_ne_zero hB P) (by simp) hP hPT
  simpa using And.intro hinv.1 hinv.2.2.2

-- Every index is reachable from an arbitrary nonzero scaling of the starting coordinates.
example {K : Type*} [Field K] [DecidableEq K] {A B N D c : K}
    (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hND : 4 * N = (A + 2) * D)
    (hc : c ≠ 0) {P : (model A B).toAffine.Point}
    (hP : P ≠ 0) (hPT : P ≠ twoTorsionPoint A hB) (n : ℕ) :
    ∃ U V, LadderRel N D (c • coordinates A B P) n U V ∧ U ≠ 0 ∧
      U.cross (coordinates A B (n • P)) = 0 ∧ V ≠ 0 ∧
      V.cross (coordinates A B ((n + 1) • P)) = 0 := by
  obtain ⟨U, V, h⟩ := LadderRel.exists_pairs N D (c • coordinates A B P) n
  exact ⟨U, V, h, h.coordinates h₂ hB hD hND
    (by simp [hc, coordinates_ne_zero hB P]) (by simp) hP hPT⟩

-- At the distinguished point, a one-bit derivation has a zero first output, yet
-- LadderRel.cross_coordinates still applies unconditionally.
example [Fact (Nat.Prime 7)] : LadderRel (2 : ZMod 7) 4 ⟨0, 1⟩ 1 0 ⟨4, 0⟩ ∧
    (0 : Pair (ZMod 7)).cross
      (coordinates 0 1 ((1 : ℕ) • twoTorsionPoint (0 : ZMod 7) one_ne_zero)) = 0 ∧
    (⟨4, 0⟩ : Pair (ZMod 7)).cross
      (coordinates 0 1 ((2 : ℕ) • twoTorsionPoint (0 : ZMod 7) one_ne_zero)) = 0 := by
  have h₁ : LadderRel (2 : ZMod 7) 4 ⟨0, 1⟩ 1 0 ⟨4, 0⟩ := by
    convert (LadderRel.zero (N := (2 : ZMod 7)) (D := 4) (S := ⟨0, 1⟩)).bit true
      using 1 <;> norm_num
    ext <;> norm_num [double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def]
  exact ⟨h₁, h₁.cross_coordinates (by norm_num) (by simp)⟩

-- Away from twoTorsionPoint (including at P = 0), vanishing of U.z characterizes addOrderOf P ∣ n.
example {K : Type*} [Field K] [DecidableEq K] {A B N D : K} {S U V : Pair K} {n : ℕ}
    (h : LadderRel N D S n U V) (h₂ : (2 : K) ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hND : 4 * N = (A + 2) * D) (hS : S ≠ 0) (hSP : S.cross (coordinates A B 0) = 0) :
    U.z = 0 := by
  rw [h.z_eq_zero_iff_addOrderOf_dvd h₂ hB hD hND hS hSP (twoTorsionPoint_ne_zero A hB).symm]
  simp

end TauCeti.Montgomery
