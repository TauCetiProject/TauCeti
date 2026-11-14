/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the odd Montgomery-ladder step and scalar-multiple sequences

On `y² = x³ + x` over `𝔽₇`, starting from `P = (3, 3)` of order `8`, the even and odd ladder
relations (`double` and `diffAdd`) certify that `[1..8]P` have projective `x`-coordinates
`(3 : 1), (1 : 1), (5 : 1), (0 : 1), (5 : 1), (1 : 1), (3 : 1), (1 : 0)`, and differential
addition of the coordinate pairs of `[2]P`, `P` and `P` is nonzero and represents `5`. Modulo
`35`, applying `diffAdd` to `(21, 25)`, `(22, 1)` and `(22, 1)` produces `(1, 8)` with
`gcd(8, 35) = 1`; its reductions modulo `5` and `7` represent `[3](2, 0) = (2, 0)` over `𝔽₅` and
`[3](1, 3) = (1, 4)` over `𝔽₇`.

On `y² = x³ + x` over `𝔽₅`, the point `(2, 0)` is a non-distinguished point of order two.
The odd step is nonzero for every index at this base point, not just at points of odd order.
In contrast, at the distinguished point `(0, 0)` it is always zero; its multiples alternate
between that point and infinity. The alternation remains valid in characteristic two.
-/

namespace TauCeti.Montgomery

open WeierstrassCurve

section Exceptional

variable [Fact (Nat.Prime 2)] [Fact (Nat.Prime 5)] [Fact (Nat.Prime 7)]

-- Use three independently scaled representatives of the non-distinguished point of order two.
example (k : ℕ) :
    let T : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 (by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert)
    let R := diffAdd ((2 : ZMod 5) • coordinates (0 : ZMod 5) 1 ((k + 1) • T))
      ((3 : ZMod 5) • coordinates (0 : ZMod 5) 1 (k • T))
      ((4 : ZMod 5) • coordinates (0 : ZMod 5) 1 T)
    R.cross (coordinates (0 : ZMod 5) 1 ((2 * k + 1) • T)) = 0 ∧ R ≠ 0 := by
  dsimp only
  have hB : (1 : ZMod 5) ≠ 0 := one_ne_zero
  have h₂ : (2 : ZMod 5) ≠ 0 := by decide +revert
  have h₃ : (3 : ZMod 5) ≠ 0 := by decide +revert
  have h₄ : (4 : ZMod 5) ≠ 0 := by decide +revert
  have nonsingular_two_zero : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  have hscale (a : ZMod 5) (ha : a ≠ 0) (Q : (model (0 : ZMod 5) 1).toAffine.Point) :
      a • coordinates 0 1 Q ≠ 0 := by
    rw [Ne, Pair.smul_eq_zero, not_or]
    exact ⟨ha, coordinates_ne_zero hB Q⟩
  refine ⟨diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero
    (.some 2 0 nonsingular_two_zero) k (by simp) (by simp) (by simp), ?_⟩
  have h := diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero h₂ hB
    (A := 0) (.some 2 0 nonsingular_two_zero) k
    (SNext := (2 : ZMod 5) • coordinates 0 1 ((k + 1) • .some 2 0 nonsingular_two_zero))
    (SCurrent := (3 : ZMod 5) • coordinates 0 1 (k • .some 2 0 nonsingular_two_zero))
    (SBase := (4 : ZMod 5) • coordinates 0 1 (.some 2 0 nonsingular_two_zero))
    (hscale 2 h₂ _) (hscale 3 h₃ _) (hscale 4 h₄ _)
    (by simp) (by simp) (by simp)
  apply h.mpr ⟨Affine.Point.some_ne_zero _, ?_⟩
  exact (some_eq_twoTorsionPoint_iff hB nonsingular_two_zero).not.mpr h₂

-- The distinguished point alternates, while its odd differential-addition step degenerates.
example (k : ℕ) :
    coordinates (0 : ZMod 7) 1 ((2 * k) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)) =
      ⟨1, 0⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

example (k : ℕ) :
    coordinates (0 : ZMod 7) 1 ((2 * k + 1) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)) =
      ⟨0, 1⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

example (k : ℕ) :
    diffAdd
      (coordinates (0 : ZMod 7) 1 ((k + 1) • twoTorsionPoint (0 : ZMod 7) (by decide +revert)))
      (coordinates (0 : ZMod 7) 1 (k • twoTorsionPoint (0 : ZMod 7) (by decide +revert)))
      (coordinates (0 : ZMod 7) 1 (twoTorsionPoint (0 : ZMod 7) (by decide +revert))) = 0 := by
  simp

-- Characteristic two is not excluded from the alternation theorem.
example (k : ℕ) :
    coordinates (0 : ZMod 2) 1 ((2 * k + 1) • twoTorsionPoint (0 : ZMod 2) (by decide +revert)) =
      ⟨0, 1⟩ := by
  simp [coordinates_nsmul_twoTorsionPoint]

-- Infinity is also an exceptional fixed difference, even though the input pairs are nonzero.
example (k : ℕ) :
    diffAdd (coordinates (0 : ZMod 7) 1 ((k + 1) • (0 : (model (0 : ZMod 7) 1).toAffine.Point)))
      (coordinates (0 : ZMod 7) 1 (k • 0)) (coordinates (0 : ZMod 7) 1 0) = 0 := by
  ext <;> simp

end Exceptional

section Seven

variable [Fact (Nat.Prime 7)]

-- Over `𝔽₇` with `(A, B) = (0, 1)` and `P = (3, 3)`, the even and odd ladder relations give the
-- projective `x`-coordinates `(3 : 1), (1 : 1), (5 : 1), (0 : 1), (5 : 1), (1 : 1), (3 : 1),
-- (1 : 0)` of `[1..8]P`.
example :
    let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 (by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert)
    let proj (x z : ZMod 7) (h : Pair.mk x z ≠ 0) := (Pair.mk x z).toProj h
    projectiveX 0 one_ne_zero (1 • P) = proj 3 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (2 • P) = proj 1 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (3 • P) = proj 5 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (4 • P) = proj 0 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (5 • P) = proj 5 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (6 • P) = proj 1 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (7 • P) = proj 3 1 (Pair.ne_zero_iff.mpr (by decide +revert)) ∧
      projectiveX 0 one_ne_zero (8 • P) = proj 1 0 (Pair.ne_zero_iff.mpr (by decide +revert)) := by
  dsimp only
  obtain ⟨hD, hND, ⟨hnz₁, hnz₂, hnz₃, hnz₄, hnz₅, hnz₆, hnz₇, hnz₈⟩, ⟨hd₂, hd₄, hd₆, hd₈⟩,
      ⟨hd₃, hd₅, hd₇⟩, ⟨hc₂, hc₃, hc₄, hc₅, hc₆, hc₇⟩, hns⟩ :
      (4 : ZMod 7) ≠ 0 ∧ (4 : ZMod 7) * 2 = (0 + 2) * 4 ∧
      ((⟨3, 1⟩ : Pair (ZMod 7)) ≠ 0 ∧ (⟨4, 4⟩ : Pair (ZMod 7)) ≠ 0 ∧
        (⟨4, 5⟩ : Pair (ZMod 7)) ≠ 0 ∧ (⟨0, 2⟩ : Pair (ZMod 7)) ≠ 0 ∧
        (⟨1, 3⟩ : Pair (ZMod 7)) ≠ 0 ∧ (⟨2, 2⟩ : Pair (ZMod 7)) ≠ 0 ∧
        (⟨1, 5⟩ : Pair (ZMod 7)) ≠ 0 ∧ (⟨1, 0⟩ : Pair (ZMod 7)) ≠ 0) ∧
      (double (2 : ZMod 7) 4 ⟨3, 1⟩ = ⟨4, 4⟩ ∧ double (2 : ZMod 7) 4 ⟨4, 4⟩ = ⟨0, 2⟩ ∧
        double (2 : ZMod 7) 4 ⟨4, 5⟩ = ⟨2, 2⟩ ∧ double (2 : ZMod 7) 4 ⟨0, 2⟩ = ⟨1, 0⟩) ∧
      (diffAdd (⟨4, 4⟩ : Pair (ZMod 7)) ⟨3, 1⟩ ⟨3, 1⟩ = ⟨4, 5⟩ ∧
        diffAdd (⟨4, 5⟩ : Pair (ZMod 7)) ⟨4, 4⟩ ⟨3, 1⟩ = ⟨1, 3⟩ ∧
        diffAdd (⟨0, 2⟩ : Pair (ZMod 7)) ⟨4, 5⟩ ⟨3, 1⟩ = ⟨1, 5⟩) ∧
      ((⟨4, 4⟩ : Pair (ZMod 7)).cross ⟨1, 1⟩ = 0 ∧ (⟨4, 5⟩ : Pair (ZMod 7)).cross ⟨5, 1⟩ = 0 ∧
        (⟨0, 2⟩ : Pair (ZMod 7)).cross ⟨0, 1⟩ = 0 ∧ (⟨1, 3⟩ : Pair (ZMod 7)).cross ⟨5, 1⟩ = 0 ∧
        (⟨2, 2⟩ : Pair (ZMod 7)).cross ⟨1, 1⟩ = 0 ∧ (⟨1, 5⟩ : Pair (ZMod 7)).cross ⟨3, 1⟩ = 0) ∧
      (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
    simp only [Pair.ne_zero_iff, Pair.ext_iff, double_x, double_z, diffAdd_x, diffAdd_z,
      Pair.cross_def, Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 hns
  have heven (k : ℕ) {S T : Pair (ZMod 7)} (hS : S ≠ 0) (hT : double 2 4 S = T)
      (hc : S.cross (coordinates 0 1 (k • P)) = 0) :
      T.cross (coordinates 0 1 ((2 * k) • P)) = 0 := by
    rw [← hT]
    simpa only [mul_nsmul, two_nsmul, nsmul_add] using
      (double_coordinates_of_cross_eq_zero hD hND hS hc).2
  have hodd (k : ℕ) {S₂ S₁ T : Pair (ZMod 7)} (hT : diffAdd S₂ S₁ ⟨3, 1⟩ = T)
      (hc₂ : S₂.cross (coordinates 0 1 ((k + 1) • P)) = 0)
      (hc₁ : S₁.cross (coordinates 0 1 (k • P)) = 0) :
      T.cross (coordinates 0 1 ((2 * k + 1) • P)) = 0 :=
    hT ▸ diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P k hc₂ hc₁ (by simp [P])
  have hproj (k : ℕ) {S R : Pair (ZMod 7)} (hS : S ≠ 0) (hR : R ≠ 0)
      (hc : S.cross (coordinates 0 1 (k • P)) = 0) (hSR : S.cross R = 0) :
      projectiveX 0 one_ne_zero (k • P) = R.toProj hR :=
    (projectiveX_def ..).trans <| (Pair.toProj_eq_toProj_iff ..).mpr
      (Pair.cross_eq_zero_trans hS (Pair.cross_eq_zero_comm.mp hc) hSR)
  have h₁ : (Pair.mk (3 : ZMod 7) 1).cross (coordinates 0 1 (1 • P)) = 0 := by simp [P]
  have h₂ : (Pair.mk (4 : ZMod 7) 4).cross (coordinates 0 1 (2 • P)) = 0 := heven 1 hnz₁ hd₂ h₁
  have h₃ : (Pair.mk (4 : ZMod 7) 5).cross (coordinates 0 1 (3 • P)) = 0 := hodd 1 hd₃ h₂ h₁
  have h₄ : (Pair.mk (0 : ZMod 7) 2).cross (coordinates 0 1 (4 • P)) = 0 := heven 2 hnz₂ hd₄ h₂
  have h₅ : (Pair.mk (1 : ZMod 7) 3).cross (coordinates 0 1 (5 • P)) = 0 := hodd 2 hd₅ h₃ h₂
  have h₆ : (Pair.mk (2 : ZMod 7) 2).cross (coordinates 0 1 (6 • P)) = 0 := heven 3 hnz₃ hd₆ h₃
  have h₇ : (Pair.mk (1 : ZMod 7) 5).cross (coordinates 0 1 (7 • P)) = 0 := hodd 3 hd₇ h₄ h₃
  have h₈ : (Pair.mk (1 : ZMod 7) 0).cross (coordinates 0 1 (8 • P)) = 0 := heven 4 hnz₄ hd₈ h₄
  exact ⟨hproj 1 hnz₁ _ h₁ (Pair.cross_self _),
    hproj 2 hnz₂ _ h₂ hc₂, hproj 3 hnz₃ _ h₃ hc₃, hproj 4 hnz₄ _ h₄ hc₄,
    hproj 5 hnz₅ _ h₅ hc₅, hproj 6 hnz₆ _ h₆ hc₆, hproj 7 hnz₇ _ h₇ hc₇,
    hproj 8 hnz₈ _ h₈ (Pair.cross_self _)⟩

-- Differential addition of the coordinate pairs of `[2]P`, `P` and `P` is nonzero and
-- represents `5`, the `x`-coordinate of `[3]P`.
example :
    let hP : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert
    let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 hP
    let R := diffAdd (coordinates 0 1 (2 • P)) (coordinates 0 1 P) (coordinates 0 1 P)
    R ≠ 0 ∧ R.cross ⟨5, 1⟩ = 0 := by
  dsimp only
  obtain ⟨h₂, h₃, h₄, hND, hd, hc₄₅, hP⟩ :
      (2 : ZMod 7) ≠ 0 ∧ (3 : ZMod 7) ≠ 0 ∧ (4 : ZMod 7) ≠ 0 ∧
      (4 : ZMod 7) * 2 = (0 + 2) * 4 ∧
      diffAdd (double (2 : ZMod 7) 4 ⟨3, 1⟩) ⟨3, 1⟩ ⟨3, 1⟩ = ⟨4, 5⟩ ∧
      (⟨4, 5⟩ : Pair (ZMod 7)).cross ⟨5, 1⟩ = 0 ∧
      (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
    simp only [Pair.ext_iff, double_x, double_z, diffAdd_x, diffAdd_z, Pair.cross_def,
      Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  have h₃₁ : (⟨3, 1⟩ : Pair (ZMod 7)) ≠ 0 := Pair.ne_zero_iff.mpr (.inl h₃)
  have h₄₅ : (⟨4, 5⟩ : Pair (ZMod 7)) ≠ 0 := Pair.ne_zero_iff.mpr (.inl h₄)
  let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 hP
  have hPT : P ≠ twoTorsionPoint 0 one_ne_zero :=
    (some_eq_twoTorsionPoint_iff one_ne_zero hP).not.mpr h₃
  have hne : diffAdd (coordinates 0 1 (2 • P)) (coordinates 0 1 P) (coordinates 0 1 P) ≠ 0 :=
    (diffAdd_nsmul_ne_zero_iff_of_cross_eq_zero h₂ one_ne_zero P 1
      (coordinates_ne_zero one_ne_zero _) (coordinates_ne_zero one_ne_zero _)
      (coordinates_ne_zero one_ne_zero _) (Pair.cross_self _) (by simp) (Pair.cross_self _)).mpr
      ⟨Affine.Point.some_ne_zero _, hPT⟩
  have hR₃ :
      (diffAdd (coordinates 0 1 (2 • P)) (coordinates 0 1 P) (coordinates 0 1 P)).cross
        (coordinates (0 : ZMod 7) 1 (3 • P)) = 0 :=
    diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P 1
      (Pair.cross_self _) (by simp) (Pair.cross_self _)
  have hS₂ : (double (2 : ZMod 7) 4 ⟨3, 1⟩).cross (coordinates 0 1 (2 • P)) = 0 := by
    simpa only [two_nsmul] using
      (double_coordinates_of_cross_eq_zero h₄ hND h₃₁ (by simp [P])).2
  have hS₃ :
      (diffAdd (double (2 : ZMod 7) 4 ⟨3, 1⟩) ⟨3, 1⟩ ⟨3, 1⟩).cross
        (coordinates (0 : ZMod 7) 1 (3 • P)) = 0 :=
    diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P 1 hS₂ (by simp [P])
      (by simp [P])
  rw [hd] at hS₃
  have hc₃ : (coordinates (0 : ZMod 7) 1 (3 • P)).cross ⟨5, 1⟩ = 0 :=
    Pair.cross_eq_zero_trans h₄₅ (Pair.cross_eq_zero_comm.mp hS₃) hc₄₅
  exact ⟨hne, Pair.cross_eq_zero_trans (coordinates_ne_zero one_ne_zero _) hR₃ hc₃⟩

end Seven

section ModThirtyFive

-- Modulo `35`, the odd step `diffAdd (21, 25) (22, 1) (22, 1) = (1, 8)` has `gcd(8, 35) = 1`;
-- modulo `5` it represents `[3](2, 0) = (2, 0)`.
example [Fact (Nat.Prime 5)] :
    let R := diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩
    let P₅ : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 (by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert)
    R = ⟨1, 8⟩ ∧ Nat.gcd R.z.val 35 = 1 ∧ 3 • P₅ = P₅ ∧
      (R.map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        (coordinates 0 1 (3 • P₅)) = 0 := by
  dsimp only
  obtain ⟨hc₀, hc₁, hns⟩ :
      ((⟨21, 25⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        ⟨1, 0⟩ = 0 ∧
      ((⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5))).cross
        ⟨2, 1⟩ = 0 ∧
      (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
    simp only [Pair.cross_def, Pair.map_x, Pair.map_z, Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  have hR : diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ := by
    ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide
  let P₅ : (model (0 : ZMod 5) 1).toAffine.Point := .some 2 0 hns
  have h2 : 2 • P₅ = 0 := by
    rw [two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])
  have h3 : 3 • P₅ = P₅ := by
    have h3eq : (3 : ℕ) = 2 + 1 := rfl
    rw [h3eq, add_nsmul, h2, zero_add, one_nsmul]
  refine ⟨hR, by rw [hR]; decide, h3, ?_⟩
  rw [map_diffAdd]
  refine diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P₅ 1 ?_ ?_ ?_
  · rw [h2, coordinates_zero]
    exact hc₀
  · rw [one_nsmul, coordinates_some]
    exact hc₁
  · rw [coordinates_some]
    exact hc₁

-- Modulo `7`, the same odd-step output `(1, 8)` represents `[3](1, 3) = (1, 4)`.
example [Fact (Nat.Prime 7)] :
    let R := diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩
    let h₁₃ : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert
    let h₁₄ : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
      simp only [Affine.nonsingular_iff, Affine.equation_iff,
        model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
      decide +revert
    let P₇ : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 h₁₃
    3 • P₇ = .some 1 4 h₁₄ ∧
      (R.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 (3 • P₇)) = 0 := by
  dsimp only
  obtain ⟨hneg, hc₀, hc₁, h₁₃, h₁₄⟩ :
      (-(3 : ZMod 7) - 0 * 1 - 0 : ZMod 7) = 4 ∧
      ((⟨21, 25⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        ⟨0, 1⟩ = 0 ∧
      ((⟨22, 1⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        ⟨1, 1⟩ = 0 ∧
      (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 ∧
      (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
    simp only [Pair.cross_def, Pair.map_x, Pair.map_z, Affine.nonsingular_iff, Affine.equation_iff,
      model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
    decide +revert
  let P₇ : (model (0 : ZMod 7) 1).toAffine.Point := .some 1 3 h₁₃
  have h2 : 2 • P₇ = twoTorsionPoint 0 one_ne_zero := by
    rw [two_nsmul]
    exact (add_self_eq_twoTorsionPoint_iff one_ne_zero h₁₃).mpr rfl
  have h4 : 3 • P₇ + P₇ = 0 := by
    have h4eq : 3 • P₇ + P₇ = 2 • P₇ + 2 • P₇ := by
      rw [← succ_nsmul, ← add_nsmul]
    rw [h4eq, h2, twoTorsionPoint_add_self]
  have h3 : 3 • P₇ = .some 1 4 h₁₄ := by
    rw [eq_neg_of_add_eq_zero_left h4]
    simp only [P₇, Affine.Point.neg_some, Affine.negY, model_a₁, model_a₃,
      Affine.Point.some.injEq]
    exact ⟨trivial, hneg⟩
  refine ⟨h3, ?_⟩
  rw [map_diffAdd]
  refine diffAdd_cross_two_mul_add_one_nsmul_eq_zero_of_cross_eq_zero P₇ 1 ?_ ?_ ?_
  · rw [h2, coordinates_twoTorsionPoint]
    exact hc₀
  · rw [one_nsmul, coordinates_some]
    exact hc₁
  · rw [coordinates_some]
    exact hc₁

end ModThirtyFive

end TauCeti.Montgomery
