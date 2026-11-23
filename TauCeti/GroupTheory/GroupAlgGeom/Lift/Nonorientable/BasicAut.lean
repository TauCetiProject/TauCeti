/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicAut
import TauCeti.Data.List.ProdOfFn
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Tactic.Group

/-!
# Basic automorphisms of a non-orientable quadratic word

Let `G` be a group and `X` a set of variables containing pairwise distinct variables `xᵢ`, `yᵢ`
(`i = 1, …, n`), `zⱼ` (`j = 1, …, m`) and `uₖ` (`k = 1, …, r`), and let `cⱼ ∈ G`. [IFT], §7.5,
writes a non-orientable quadratic equation in a mixed form with commutators and one or two
squares, (113) and (114), whose left side is the word
`S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²` (`basicMixedWord`), where `[x, y] = x⁻¹ y⁻¹ x y`. This file
defines the `G`-automorphisms of the free `G`-group `G[X]` that [IFT], §7.5, adds to the
orientable basic automorphisms of `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]`
(`TauCeti.GroupAlgGeom.Lift.basicWord`). Writing `w^A = A⁻¹ w A`, they are
* `basicLinkSq`: `zⱼ ↦ zⱼ A`, `uₖ ↦ uₖ^A` with `A = zⱼ⁻¹ cⱼ zⱼ uₖ²`;
* `basicCommSq`: `xᵢ ↦ A⁻¹ xᵢ`, `yᵢ ↦ yᵢ^A`, `uₖ ↦ uₖ^A` with `A = yᵢ uₖ²`;
* `basicSqMul`: `uₖ ↦ uₖ A`, `uₖ' ↦ A⁻¹ uₖ'` with `A = uₖ uₖ'`;
* `basicSqConj`: `uₖ ↦ uₖ^A`, `uₖ' ↦ uₖ'^A` with `A = uₖ² uₖ'²`.

Each multiplies or conjugates the variables of two atoms of `S₁` by a word `A` that it fixes, so
it is a twist (`TauCeti.GroupAlgGeom.twist`), and it fixes `S₁` when the two atoms are adjacent:
`basicLinkSq` when there is no commutator and it links the last coefficient atom with the first
square, `basicCommSq` when it links the last commutator with the first square, and `basicSqMul`,
`basicSqConj` for two consecutive squares. In [IFT], §7.5, they are the automorphisms `γₘ`,
`γₘ₊₁`, `γₘ₊₂` (no commutator) and `γₘ₊₄ₙ`, `γₘ₊₄ₙ₊₁`, `γₘ₊₄ₙ₊₂` (at least one commutator) of
equation (114). In `γₘ₊₁` and `γₘ₊₄ₙ₊₁` the image `uₖ (uₖ uₖ')` of `uₖ` is a product, not a
conjugate: only the product makes these maps automorphisms fixing `uₖ² uₖ'²`.

Being twists, their powers are given by the same formulas with `A ^ p` in place of `A`, for
every integer `p`, as [IFT], Lemma 41, computes the positive powers of the orientable basic
automorphisms.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.sqAtom`: the square `uₖ²` of a variable.
* `TauCeti.GroupAlgGeom.Lift.basicMixedWord`: the word `S₁`.
* `TauCeti.GroupAlgGeom.Lift.basicLinkSq`, `basicCommSq`, `basicSqMul`, `basicSqConj`: the basic
  automorphisms of the squares.

## Main results

* `TauCeti.GroupAlgGeom.Lift.basicLinkSq_basicMixedWord`,
  `TauCeti.GroupAlgGeom.Lift.basicCommSq_basicMixedWord`,
  `TauCeti.GroupAlgGeom.Lift.basicSqMul_basicMixedWord`,
  `TauCeti.GroupAlgGeom.Lift.basicSqConj_basicMixedWord`: the basic automorphisms of the squares
  fix `S₁`; so do their inverses and their natural and integer powers
  (`basicLinkSq_symm_basicMixedWord`, `basicLinkSq_pow_basicMixedWord`,
  `basicLinkSq_zpow_basicMixedWord`, and the same for the other three).
* `TauCeti.GroupAlgGeom.Lift.basicLinkSq_inl`, `basicLinkSq_inr_of_z` and the lemmas after them:
  the basic automorphisms of the squares, their inverses and their natural and integer powers on
  the coefficients and on the variables.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.5, (113), (114) and the automorphisms `γₘ, …, γₘ₊₄ₙ₊₂`; §7.1, Lemma 41.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G X : Type*} [Group G] {n m r : ℕ}

/-! ### The word `S₁` -/

section Word

variable (x y : Fin n → X) (z : Fin m → X) (u : Fin r → X) (c : Fin m → G)

/-- The square `uₖ²` of a variable. -/
def sqAtom (k : Fin r) : GX G X :=
  inr (.of (u k)) ^ 2

/-- The word `S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²`, the left side of [IFT], §7.5, (113) and
(114) without its constant. -/
def basicMixedWord : GX G X :=
  basicWord x y z c * (List.ofFn (sqAtom (G := G) u)).prod

theorem sqAtom_def (k : Fin r) : sqAtom (G := G) u k = inr (.of (u k)) ^ 2 := (rfl)

theorem basicMixedWord_def :
    basicMixedWord x y z u c = basicWord x y z c * (List.ofFn (sqAtom (G := G) u)).prod := (rfl)

variable {H : Type*} [Group H] (ι : G →* H) (v : X → H)

@[simp]
theorem eval_sqAtom (k : Fin r) : eval ι v (sqAtom (G := G) u k) = v (u k) ^ 2 := by
  simp [sqAtom_def]

/-- The value of the word `S₁` at a point `v`: the value of `S₀` times `∏ₖ v(uₖ)²`. -/
@[simp]
theorem eval_basicMixedWord :
    eval ι v (basicMixedWord x y z u c) =
      eval ι v (basicWord x y z c) * (List.ofFn fun k => v (u k) ^ 2).prod := by
  simp [basicMixedWord_def, map_list_prod, List.map_ofFn, Function.comp_def]

end Word

/-! ### Twists fixing the squares -/

/-- A twist whose exponents vanish at `uₖ` fixes the square `uₖ²`. -/
theorem twistHom_sqAtom_of_eq_zero {u : Fin r → X} {B : GX G X} {e : X → ℤ × ℤ} (k : Fin r)
    (hk : e (u k) = 0) : twistHom B e (sqAtom u k) = sqAtom u k := by
  simp [sqAtom_def, hk]

/-! ### Exponents at the variables of `S₁` -/

section BlockExp

variable {x y : Fin n → X} {z : Fin m → X} {u : Fin r → X}
  {e : ((Fin n ⊕ Fin n) ⊕ Fin m) ⊕ Fin r → ℤ × ℤ}
  (inj : (Sum.elim (Sum.elim (Sum.elim x y) z) u).Injective)
include inj

private theorem blockExp_x (i : Fin n) :
    blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u) e (x i) = e (.inl (.inl (.inl i))) :=
  blockExp_apply inj (.inl (.inl (.inl i)))

private theorem blockExp_y (i : Fin n) :
    blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u) e (y i) = e (.inl (.inl (.inr i))) :=
  blockExp_apply inj (.inl (.inl (.inr i)))

private theorem blockExp_z (j : Fin m) :
    blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u) e (z j) = e (.inl (.inr j)) :=
  blockExp_apply inj (.inl (.inr j))

private theorem blockExp_u (k : Fin r) :
    blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u) e (u k) = e (.inr k) :=
  blockExp_apply inj (.inr k)

end BlockExp

/-! ### The basic automorphisms of the squares -/

section Families

variable {x y : Fin n → X} {z : Fin m → X} {u : Fin r → X}
  (inj : (Sum.elim (Sum.elim (Sum.elim x y) z) u).Injective) (c : Fin m → G)
include inj

section LinkSq

variable (j : Fin m) (k : Fin r)

private theorem twistHom_linkSqTerm {B : GX G X} (hB : Commute B (coeffAtom z c j * sqAtom u k)) :
    twistHom B (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
        (Sum.elim (Sum.elim 0 (Pi.single j (0, 1))) (Pi.single k (-1, 1))))
      (coeffAtom z c j * sqAtom u k) = coeffAtom z c j * sqAtom u k := by
  calc _ = B⁻¹ * (coeffAtom z c j * sqAtom u k) * B := by
        simp only [coeffAtom_def, sqAtom_def, map_mul, map_inv, twistHom_inl, twistHom_inr_of,
          blockExp_z inj, blockExp_u inj, Sum.elim_inl, Sum.elim_inr, Pi.single_eq_same, zpow_zero,
          zpow_one, zpow_neg, one_mul, sq]
        group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism `zⱼ ↦ zⱼ A`, `uₖ ↦ A⁻¹ uₖ A` of `G[X]`, where `A = zⱼ⁻¹ cⱼ zⱼ uₖ²`;
the other variables are fixed. For the last coefficient atom and the first square of an equation
without commutators it is the automorphism `γₘ` of [IFT], §7.5. -/
noncomputable def basicLinkSq : MulAut (GX G X) :=
  twist (coeffAtom z c j * sqAtom u k)
    (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
      (Sum.elim (Sum.elim 0 (Pi.single j (0, 1))) (Pi.single k (-1, 1))))
    (twistHom_linkSqTerm inj c j k (Commute.refl _))
    (twistHom_linkSqTerm inj c j k (Commute.refl _).inv_left)

@[simp]
theorem basicLinkSq_inl (g : G) : basicLinkSq inj c j k (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_symm_inl (g : G) : (basicLinkSq inj c j k).symm (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_pow_inl (p : ℕ) (g : G) : (basicLinkSq inj c j k ^ p) (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_zpow_inl (p : ℤ) (g : G) : (basicLinkSq inj c j k ^ p) (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_inr_of_z :
    basicLinkSq inj c j k (inr (.of (z j))) = inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) := by
  simp [basicLinkSq, blockExp_z inj]

@[simp]
theorem basicLinkSq_symm_inr_of_z :
    (basicLinkSq inj c j k).symm (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k)⁻¹ := by
  simp [basicLinkSq, blockExp_z inj]

@[simp]
theorem basicLinkSq_pow_inr_of_z (p : ℕ) :
    (basicLinkSq inj c j k ^ p) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, blockExp_z inj]

@[simp]
theorem basicLinkSq_zpow_inr_of_z (p : ℤ) :
    (basicLinkSq inj c j k ^ p) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, blockExp_z inj]

@[simp]
theorem basicLinkSq_inr_of_u :
    basicLinkSq inj c j k (inr (.of (u k))) =
      (coeffAtom z c j * sqAtom u k)⁻¹ * inr (.of (u k)) * (coeffAtom z c j * sqAtom u k) := by
  simp [basicLinkSq, blockExp_u inj]

@[simp]
theorem basicLinkSq_symm_inr_of_u :
    (basicLinkSq inj c j k).symm (inr (.of (u k))) =
      (coeffAtom z c j * sqAtom u k) * inr (.of (u k)) * (coeffAtom z c j * sqAtom u k)⁻¹ := by
  simp [basicLinkSq, blockExp_u inj]

@[simp]
theorem basicLinkSq_pow_inr_of_u (p : ℕ) :
    (basicLinkSq inj c j k ^ p) (inr (.of (u k))) =
      ((coeffAtom z c j * sqAtom u k) ^ p)⁻¹ * inr (.of (u k)) *
        (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, blockExp_u inj]

@[simp]
theorem basicLinkSq_zpow_inr_of_u (p : ℤ) :
    (basicLinkSq inj c j k ^ p) (inr (.of (u k))) =
      ((coeffAtom z c j * sqAtom u k) ^ p)⁻¹ * inr (.of (u k)) *
        (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, blockExp_u inj]

theorem basicLinkSq_zpow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) (p : ℤ) :
    (basicLinkSq inj c j k ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicLinkSq, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero (by
    rintro (((l | l) | l) | l) rfl
    · rfl
    · rfl
    · exact Pi.single_eq_of_ne (fun h => hz (congrArg z h)) _
    · exact Pi.single_eq_of_ne (fun h => hu (congrArg u h)) _)]
  simp

theorem basicLinkSq_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) :
    basicLinkSq inj c j k (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne inj c j k hz hu 1

theorem basicLinkSq_symm_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) :
    (basicLinkSq inj c j k).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne inj c j k hz hu (-1)

theorem basicLinkSq_pow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) (p : ℕ) :
    (basicLinkSq inj c j k ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne inj c j k hz hu p

/-- For an equation without commutators, the basic automorphism of the last coefficient atom and
the first square fixes the word `S₁`. -/
theorem basicLinkSq_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0) :
    basicLinkSq inj c j k (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  subst hn
  have hS : basicMixedWord x y z u c =
      (List.ofFn (Fin.append (coeffAtom z c) (sqAtom u))).prod := by
    simp [basicMixedWord_def, basicWord_def, List.ofFn_fin_append]
  rw [basicLinkSq, twist_apply, hS]
  refine List.map_prod_ofFn_of_adjacent _ _ (i := Fin.castAdd r j) (i' := Fin.natAdd m k)
    (by simp [hj, hk]) (fun l hl hl' => ?_) ?_
  · induction l using Fin.addCases with
    | left l =>
      have hlj : l ≠ j := fun h => hl (h ▸ rfl)
      simpa using twistHom_coeffAtom_of_eq_zero c l (by simp [blockExp_z inj, hlj])
    | right l =>
      have hlk : l ≠ k := fun h => hl' (h ▸ rfl)
      simpa using twistHom_sqAtom_of_eq_zero l (by simp [blockExp_u inj, hlk])
  · rw [Fin.append_left, Fin.append_right]
    exact twistHom_linkSqTerm inj c j k (.refl _)

theorem basicLinkSq_zpow_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0)
    (p : ℤ) :
    (basicLinkSq inj c j k ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicLinkSq_basicMixedWord inj c j k hn hj hk)) p

theorem basicLinkSq_symm_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0) :
    (basicLinkSq inj c j k).symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicLinkSq_zpow_basicMixedWord inj c j k hn hj hk (-1)

theorem basicLinkSq_pow_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0)
    (p : ℕ) :
    (basicLinkSq inj c j k ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicLinkSq_zpow_basicMixedWord inj c j k hn hj hk p

end LinkSq

section CommSq

variable (i : Fin n) (k : Fin r)

private theorem twistHom_commSqTerm {B : GX G X} (hB : Commute B (inr (.of (y i)) * sqAtom u k)) :
    twistHom B (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
        (Sum.elim (Sum.elim (Sum.elim (Pi.single i (-1, 0)) (Pi.single i (-1, 1))) 0)
          (Pi.single k (-1, 1))))
      (inr (.of (y i)) * sqAtom u k) = inr (.of (y i)) * sqAtom u k := by
  calc _ = B⁻¹ * (inr (.of (y i)) * sqAtom u k) * B := by
        simp only [sqAtom_def, map_mul, twistHom_inr_of, blockExp_y inj, blockExp_u inj,
          Sum.elim_inl, Sum.elim_inr, Pi.single_eq_same, zpow_one, zpow_neg, sq]
        group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism `xᵢ ↦ A⁻¹ xᵢ`, `yᵢ ↦ A⁻¹ yᵢ A`, `uₖ ↦ A⁻¹ uₖ A` of `G[X]`, where
`A = yᵢ uₖ²`; the other variables are fixed. For the last commutator and the first square it is
the automorphism `γₘ₊₄ₙ` of [IFT], §7.5. -/
noncomputable def basicCommSq : MulAut (GX G X) :=
  twist (inr (.of (y i)) * sqAtom u k)
    (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
      (Sum.elim (Sum.elim (Sum.elim (Pi.single i (-1, 0)) (Pi.single i (-1, 1))) 0)
        (Pi.single k (-1, 1))))
    (twistHom_commSqTerm inj i k (Commute.refl _))
    (twistHom_commSqTerm inj i k (Commute.refl _).inv_left)

@[simp]
theorem basicCommSq_inl (g : G) : basicCommSq inj i k (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_symm_inl (g : G) : (basicCommSq inj i k).symm (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_pow_inl (p : ℕ) (g : G) : (basicCommSq inj i k ^ p) (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_zpow_inl (p : ℤ) (g : G) : (basicCommSq inj i k ^ p) (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_inr_of_x :
    basicCommSq inj i k (inr (.of (x i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq, blockExp_x inj]

@[simp]
theorem basicCommSq_symm_inr_of_x :
    (basicCommSq inj i k).symm (inr (.of (x i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (x i)) := by
  simp [basicCommSq, blockExp_x inj]

@[simp]
theorem basicCommSq_pow_inr_of_x (p : ℕ) :
    (basicCommSq inj i k ^ p) (inr (.of (x i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq, blockExp_x inj]

@[simp]
theorem basicCommSq_zpow_inr_of_x (p : ℤ) :
    (basicCommSq inj i k ^ p) (inr (.of (x i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq, blockExp_x inj]

@[simp]
theorem basicCommSq_inr_of_y :
    basicCommSq inj i k (inr (.of (y i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) := by
  simp [basicCommSq, blockExp_y inj]

@[simp]
theorem basicCommSq_symm_inr_of_y :
    (basicCommSq inj i k).symm (inr (.of (y i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k)⁻¹ := by
  simp [basicCommSq, blockExp_y inj]

@[simp]
theorem basicCommSq_pow_inr_of_y (p : ℕ) :
    (basicCommSq inj i k ^ p) (inr (.of (y i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, blockExp_y inj]

@[simp]
theorem basicCommSq_zpow_inr_of_y (p : ℤ) :
    (basicCommSq inj i k ^ p) (inr (.of (y i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, blockExp_y inj]

@[simp]
theorem basicCommSq_inr_of_u :
    basicCommSq inj i k (inr (.of (u k))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) := by
  simp [basicCommSq, blockExp_u inj]

@[simp]
theorem basicCommSq_symm_inr_of_u :
    (basicCommSq inj i k).symm (inr (.of (u k))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k)⁻¹ := by
  simp [basicCommSq, blockExp_u inj]

@[simp]
theorem basicCommSq_pow_inr_of_u (p : ℕ) :
    (basicCommSq inj i k ^ p) (inr (.of (u k))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, blockExp_u inj]

@[simp]
theorem basicCommSq_zpow_inr_of_u (p : ℤ) :
    (basicCommSq inj i k ^ p) (inr (.of (u k))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, blockExp_u inj]

theorem basicCommSq_zpow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) (p : ℤ) :
    (basicCommSq inj i k ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicCommSq, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero (by
    rintro (((l | l) | l) | l) rfl
    · exact Pi.single_eq_of_ne (fun h => hx (congrArg x h)) _
    · exact Pi.single_eq_of_ne (fun h => hy (congrArg y h)) _
    · rfl
    · exact Pi.single_eq_of_ne (fun h => hu (congrArg u h)) _)]
  simp

theorem basicCommSq_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) :
    basicCommSq inj i k (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne inj i k hx hy hu 1

theorem basicCommSq_symm_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) :
    (basicCommSq inj i k).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne inj i k hx hy hu (-1)

theorem basicCommSq_pow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) (p : ℕ) :
    (basicCommSq inj i k ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne inj i k hx hy hu p

private theorem basicCommSq_commAtom_mul_sqAtom :
    basicCommSq inj i k (commAtom (G := G) x y i * sqAtom u k) = commAtom x y i * sqAtom u k := by
  simp only [basicCommSq, twist_apply, commAtom_def, sqAtom_def, map_mul,
    map_inv, twistHom_inr_of, blockExp_x inj, blockExp_y inj, blockExp_u inj, Sum.elim_inl,
    Sum.elim_inr, Pi.single_eq_same, zpow_one, zpow_neg, zpow_zero, mul_one, sq,
    commutatorElement_def]
  group

/-- The basic automorphism of the last commutator and the first square fixes the word `S₁`. -/
theorem basicCommSq_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) :
    basicCommSq inj i k (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  have hS : basicMixedWord x y z u c = (List.ofFn (coeffAtom z c)).prod *
      (List.ofFn (Fin.append (commAtom x y) (sqAtom u))).prod := by
    simp [basicMixedWord_def, basicWord_def, List.ofFn_fin_append, mul_assoc]
  rw [hS, map_mul]
  congr 1
  · refine List.map_prod_ofFn_of_forall _ _ fun l => ?_
    rw [basicCommSq, twist_apply]
    exact twistHom_coeffAtom_of_eq_zero c l (by simp [blockExp_z inj])
  refine List.map_prod_ofFn_of_adjacent _ _ (i := Fin.castAdd r i) (i' := Fin.natAdd n k)
    (by simp [hi, hk]) (fun l hl hl' => ?_) ?_
  · rw [basicCommSq, twist_apply]
    induction l using Fin.addCases with
    | left l =>
      have hli : l ≠ i := fun h => hl (h ▸ rfl)
      simpa using twistHom_commAtom_of_eq_zero l (by simp [blockExp_x inj, hli])
        (by simp [blockExp_y inj, hli])
    | right l =>
      have hlk : l ≠ k := fun h => hl' (h ▸ rfl)
      simpa using twistHom_sqAtom_of_eq_zero l (by simp [blockExp_u inj, hlk])
  · rw [Fin.append_left, Fin.append_right]
    exact basicCommSq_commAtom_mul_sqAtom inj i k

theorem basicCommSq_zpow_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) (p : ℤ) :
    (basicCommSq inj i k ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicCommSq_basicMixedWord inj c i k hi hk)) p

theorem basicCommSq_symm_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) :
    (basicCommSq inj i k).symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicCommSq_zpow_basicMixedWord inj c i k hi hk (-1)

theorem basicCommSq_pow_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) (p : ℕ) :
    (basicCommSq inj i k ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicCommSq_zpow_basicMixedWord inj c i k hi hk p

end CommSq

section SqMul

variable (k k' : Fin r)

private theorem twistHom_sqMulTerm {B : GX G X}
    (hB : Commute B (inr (.of (u k)) * inr (.of (u k')))) :
    twistHom B (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
        (Sum.elim 0 (Pi.single k (0, 1) + Pi.single k' (-1, 0))))
      (inr (.of (u k)) * inr (.of (u k'))) = inr (.of (u k)) * inr (.of (u k')) := by
  rw [map_mul, twistHom_inr_of, twistHom_inr_of, blockExp_u inj, blockExp_u inj, Sum.elim_inr,
    Sum.elim_inr]
  by_cases hkk : k = k'
  · subst hkk
    simp only [Pi.add_apply, Pi.single_eq_same, Prod.mk_add_mk, zero_add, add_zero, zpow_one,
      zpow_neg]
    calc _ = B⁻¹ * (inr (.of (u k)) * inr (.of (u k))) * B := by group
      _ = _ := hB.inv_mul_cancel
  · simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkk,
      Pi.single_eq_of_ne (Ne.symm hkk), add_zero, zero_add, zpow_zero, zpow_one, zpow_neg]
    group

/-- The basic automorphism `uₖ ↦ uₖ A`, `uₖ' ↦ A⁻¹ uₖ'` of `G[X]`, where `A = uₖ uₖ'`, for
`k ≠ k'` (for `k = k'` it conjugates `uₖ` by `A = uₖ²`, which fixes it); the other variables are
fixed. For the two squares of [IFT], (114), it is the automorphism `γₘ₊₁`, respectively
`γₘ₊₄ₙ₊₁`, of [IFT], §7.5. -/
noncomputable def basicSqMul : MulAut (GX G X) :=
  twist (inr (.of (u k)) * inr (.of (u k')))
    (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
      (Sum.elim 0 (Pi.single k (0, 1) + Pi.single k' (-1, 0))))
    (twistHom_sqMulTerm inj k k' (Commute.refl _))
    (twistHom_sqMulTerm inj k k' (Commute.refl _).inv_left)

@[simp]
theorem basicSqMul_inl (g : G) : basicSqMul inj k k' (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_symm_inl (g : G) : (basicSqMul inj k k').symm (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_pow_inl (p : ℕ) (g : G) : (basicSqMul inj k k' ^ p) (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_zpow_inl (p : ℤ) (g : G) : (basicSqMul inj k k' ^ p) (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_inr_of_left (h : k ≠ k') :
    basicSqMul inj k k' (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) := by
  simp [basicSqMul, blockExp_u inj, h]

@[simp]
theorem basicSqMul_symm_inr_of_left (h : k ≠ k') :
    (basicSqMul inj k k').symm (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k')))⁻¹ := by
  simp [basicSqMul, blockExp_u inj, h]

@[simp]
theorem basicSqMul_pow_inr_of_left (h : k ≠ k') (p : ℕ) :
    (basicSqMul inj k k' ^ p) (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) ^ p := by
  simp [basicSqMul, blockExp_u inj, h]

@[simp]
theorem basicSqMul_zpow_inr_of_left (h : k ≠ k') (p : ℤ) :
    (basicSqMul inj k k' ^ p) (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) ^ p := by
  simp [basicSqMul, blockExp_u inj, h]

@[simp]
theorem basicSqMul_inr_of_right (h : k ≠ k') :
    basicSqMul inj k k' (inr (.of (u k'))) =
      ((inr (.of (u k)) : GX G X) * inr (.of (u k')))⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, blockExp_u inj, Ne.symm h]

@[simp]
theorem basicSqMul_symm_inr_of_right (h : k ≠ k') :
    (basicSqMul inj k k').symm (inr (.of (u k'))) =
      ((inr (.of (u k)) : GX G X) * inr (.of (u k'))) * inr (.of (u k')) := by
  simp [basicSqMul, blockExp_u inj, Ne.symm h]

@[simp]
theorem basicSqMul_pow_inr_of_right (h : k ≠ k') (p : ℕ) :
    (basicSqMul inj k k' ^ p) (inr (.of (u k'))) =
      (((inr (.of (u k)) : GX G X) * inr (.of (u k'))) ^ p)⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, blockExp_u inj, Ne.symm h]

@[simp]
theorem basicSqMul_zpow_inr_of_right (h : k ≠ k') (p : ℤ) :
    (basicSqMul inj k k' ^ p) (inr (.of (u k'))) =
      (((inr (.of (u k)) : GX G X) * inr (.of (u k'))) ^ p)⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, blockExp_u inj, Ne.symm h]

theorem basicSqMul_zpow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℤ) :
    (basicSqMul inj k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicSqMul, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero (by
    rintro (l | l) rfl
    · rfl
    · simp [show l ≠ k from fun h => hk (congrArg u h),
        show l ≠ k' from fun h => hk' (congrArg u h)])]
  simp

theorem basicSqMul_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    basicSqMul inj k k' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne inj k k' hk hk' 1

theorem basicSqMul_symm_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    (basicSqMul inj k k').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne inj k k' hk hk' (-1)

theorem basicSqMul_pow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℕ) :
    (basicSqMul inj k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne inj k k' hk hk' p

private theorem basicSqMul_sqAtom_mul_sqAtom (h : k ≠ k') :
    basicSqMul (G := G) inj k k' (sqAtom u k * sqAtom u k') = sqAtom u k * sqAtom u k' := by
  simp only [basicSqMul, twist_apply, sqAtom_def, map_mul, twistHom_inr_of, blockExp_u inj,
    Sum.elim_inr, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h,
    Pi.single_eq_of_ne (Ne.symm h), add_zero, zero_add, zpow_zero, zpow_one, zpow_neg, one_mul,
    mul_one, sq]
  group

/-- The basic automorphism `uₖ ↦ uₖ (uₖ uₖ₊₁)`, `uₖ₊₁ ↦ (uₖ uₖ₊₁)⁻¹ uₖ₊₁` of two consecutive
squares fixes the word `S₁`. -/
theorem basicSqMul_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    basicSqMul inj k k' (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  have hne : k ≠ k' := fun h => by simp [h] at hk
  rw [basicMixedWord_def, map_mul]
  congr 1
  · rw [basicSqMul, twist_apply]
    exact twistHom_basicWord c (fun _ => by simp [blockExp_x inj])
      (fun _ => by simp [blockExp_y inj]) fun _ => by simp [blockExp_z inj]
  refine List.map_prod_ofFn_of_adjacent _ _ hk (fun l hl hl' => ?_)
    (basicSqMul_sqAtom_mul_sqAtom inj k k' hne)
  rw [basicSqMul, twist_apply]
  exact twistHom_sqAtom_of_eq_zero l (by simp [blockExp_u inj, hl, hl'])

theorem basicSqMul_zpow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℤ) :
    (basicSqMul inj k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicSqMul_basicMixedWord inj c k k' hk)) p

theorem basicSqMul_symm_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    (basicSqMul inj k k').symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqMul_zpow_basicMixedWord inj c k k' hk (-1)

theorem basicSqMul_pow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℕ) :
    (basicSqMul inj k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqMul_zpow_basicMixedWord inj c k k' hk p

end SqMul

section SqConj

variable (k k' : Fin r)

private theorem twistHom_sqConjTerm {B : GX G X} (hB : Commute B (sqAtom u k * sqAtom u k')) :
    twistHom B (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
        (Sum.elim 0 fun l => if l = k ∨ l = k' then (-1, 1) else 0))
      (sqAtom u k * sqAtom u k') = sqAtom u k * sqAtom u k' := by
  calc _ = B⁻¹ * (sqAtom u k * sqAtom u k') * B := by
        simp only [sqAtom_def, map_mul, twistHom_inr_of, blockExp_u inj, Sum.elim_inr, true_or,
          or_true,
          ite_true, zpow_one, zpow_neg, sq]
        group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism `uₖ ↦ A⁻¹ uₖ A`, `uₖ' ↦ A⁻¹ uₖ' A` of `G[X]`, where `A = uₖ² uₖ'²`;
the other variables are fixed. For the two squares of [IFT], (114), it is the automorphism
`γₘ₊₂`, respectively `γₘ₊₄ₙ₊₂`, of [IFT], §7.5. -/
noncomputable def basicSqConj : MulAut (GX G X) :=
  twist (sqAtom u k * sqAtom u k')
    (blockExp (Sum.elim (Sum.elim (Sum.elim x y) z) u)
      (Sum.elim 0 fun l => if l = k ∨ l = k' then (-1, 1) else 0))
    (twistHom_sqConjTerm inj k k' (Commute.refl _))
    (twistHom_sqConjTerm inj k k' (Commute.refl _).inv_left)

@[simp]
theorem basicSqConj_inl (g : G) : basicSqConj inj k k' (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_symm_inl (g : G) : (basicSqConj inj k k').symm (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_pow_inl (p : ℕ) (g : G) : (basicSqConj inj k k' ^ p) (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_zpow_inl (p : ℤ) (g : G) : (basicSqConj inj k k' ^ p) (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_inr_of_left :
    basicSqConj inj k k' (inr (.of (u k))) =
      (sqAtom (G := G) u k * sqAtom u k')⁻¹ * inr (.of (u k)) * (sqAtom u k * sqAtom u k') := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_symm_inr_of_left :
    (basicSqConj inj k k').symm (inr (.of (u k))) =
      (sqAtom (G := G) u k * sqAtom u k') * inr (.of (u k)) * (sqAtom u k * sqAtom u k')⁻¹ := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_pow_inr_of_left (p : ℕ) :
    (basicSqConj inj k k' ^ p) (inr (.of (u k))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k)) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_zpow_inr_of_left (p : ℤ) :
    (basicSqConj inj k k' ^ p) (inr (.of (u k))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k)) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_inr_of_right :
    basicSqConj inj k k' (inr (.of (u k'))) =
      (sqAtom (G := G) u k * sqAtom u k')⁻¹ * inr (.of (u k')) * (sqAtom u k * sqAtom u k') := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_symm_inr_of_right :
    (basicSqConj inj k k').symm (inr (.of (u k'))) =
      (sqAtom (G := G) u k * sqAtom u k') * inr (.of (u k')) * (sqAtom u k * sqAtom u k')⁻¹ := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_pow_inr_of_right (p : ℕ) :
    (basicSqConj inj k k' ^ p) (inr (.of (u k'))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k')) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj, blockExp_u inj]

@[simp]
theorem basicSqConj_zpow_inr_of_right (p : ℤ) :
    (basicSqConj inj k k' ^ p) (inr (.of (u k'))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k')) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj, blockExp_u inj]

theorem basicSqConj_zpow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℤ) :
    (basicSqConj inj k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicSqConj, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero (by
    rintro (l | l) rfl
    · rfl
    · simp [show l ≠ k from fun h => hk (congrArg u h),
        show l ≠ k' from fun h => hk' (congrArg u h)])]
  simp

theorem basicSqConj_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    basicSqConj inj k k' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne inj k k' hk hk' 1

theorem basicSqConj_symm_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    (basicSqConj inj k k').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne inj k k' hk hk' (-1)

theorem basicSqConj_pow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℕ) :
    (basicSqConj inj k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne inj k k' hk hk' p

/-- The basic automorphism conjugating two consecutive square variables by the product of their
squares fixes the word `S₁`. -/
theorem basicSqConj_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    basicSqConj inj k k' (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [basicSqConj, twist_apply, basicMixedWord_def, map_mul, twistHom_basicWord c
    (fun _ => by simp [blockExp_x inj]) (fun _ => by simp [blockExp_y inj])
    fun _ => by simp [blockExp_z inj]]
  congr 1
  exact List.map_prod_ofFn_of_adjacent _ _ hk (fun l hl hl' =>
    twistHom_sqAtom_of_eq_zero l (by simp [blockExp_u inj, hl, hl']))
    (twistHom_sqConjTerm inj k k' (.refl _))

theorem basicSqConj_zpow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℤ) :
    (basicSqConj inj k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicSqConj_basicMixedWord inj c k k' hk)) p

theorem basicSqConj_symm_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    (basicSqConj inj k k').symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqConj_zpow_basicMixedWord inj c k k' hk (-1)

theorem basicSqConj_pow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℕ) :
    (basicSqConj inj k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqConj_zpow_basicMixedWord inj c k k' hk p

end SqConj

end Families

end TauCeti.GroupAlgGeom.Lift
