/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Twist
import TauCeti.Data.List.ProdOfFn
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Tactic.Group

/-!
# Basic automorphisms of a non-orientable quadratic word

Let `G` be a group, `X` a set of variables, `xᵢ`, `yᵢ` (`i = 1, …, n`), `zⱼ` (`j = 1, …, m`) and
`uₖ` (`k = 1, …, r`) variables, and `cⱼ ∈ G`. [IFT], §7.5, writes a non-orientable quadratic
equation in a mixed form with commutators and one or two squares, (113) and (114). Its left side
is `S₁ d` with a constant `d ∈ G`, where
`S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²` (`TauCeti.GroupAlgGeom.Quadratic.basicMixedWord`) is the
product of the atoms that carry variables, and `[x, y] = x⁻¹ y⁻¹ x y`. This file defines the
`G`-automorphisms of the free `G`-group `G[X]` that [IFT], §7.5, adds to the orientable basic
automorphisms of `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` (`TauCeti.GroupAlgGeom.Lift.basicCoeff` and the
others). Writing `w^A = A⁻¹ w A`, they are
* `basicLinkSq`: `zⱼ ↦ zⱼ A`, `uₖ ↦ uₖ^A` with `A = zⱼ⁻¹ cⱼ zⱼ uₖ²`;
* `basicCommSq`: `xᵢ ↦ A⁻¹ xᵢ`, `yᵢ ↦ yᵢ^A`, `uₖ ↦ uₖ^A` with `A = yᵢ uₖ²`;
* `basicSqMul`: `uₖ ↦ uₖ A`, `uₖ' ↦ A⁻¹ uₖ'` with `A = uₖ uₖ'`;
* `basicSqConj`: `uₖ ↦ uₖ^A`, `uₖ' ↦ uₖ'^A` with `A = uₖ² uₖ'²`.

Each multiplies or conjugates the variables of two atoms of `S₁` by a word `A` that it fixes, so
it is a twist (`TauCeti.GroupAlgGeom.twist`). Defining it needs `zⱼ ≠ uₖ` for `basicLinkSq`,
`xᵢ ≠ yᵢ` and `xᵢ ≠ uₖ` for `basicCommSq`, and no condition for `basicSqMul` and `basicSqConj`,
which are the identity when `uₖ = uₖ'`. It fixes `S₁` when the two atoms are adjacent and the
other atoms do not contain the variables it moves:
`basicLinkSq` when there is no commutator and it links the last coefficient atom with the first
square, `basicCommSq` when it links the last commutator with the first square, and `basicSqMul`,
`basicSqConj` for two consecutive squares. Since it also fixes the coefficients, it then fixes
the left side `S₁ d` of the equation. In [IFT], §7.5, where the variables are pairwise distinct,
they are the automorphisms `γₘ`, `γₘ₊₁`, `γₘ₊₂` (no commutator) and `γₘ₊₄ₙ`, `γₘ₊₄ₙ₊₁`,
`γₘ₊₄ₙ₊₂` (at least one commutator) of equation (114). In `γₘ₊₁` and `γₘ₊₄ₙ₊₁` the image
`uₖ (uₖ uₖ')` of `uₖ` is a product, not a conjugate: only the product makes these maps
automorphisms fixing `uₖ² uₖ'²`.

Being twists, their powers are given by the same formulas with `A ^ p` in place of `A`, for
every integer `p`, as [IFT], Lemma 41, computes the positive powers of the orientable basic
automorphisms.

## Main definitions

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
* `TauCeti.GroupAlgGeom.Lift.basicSqMul_eq_one`, `basicSqConj_eq_one`: the automorphisms of two
  squares of the same variable are the identity.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.5, (113), (114) and the automorphisms `γₘ, …, γₘ₊₄ₙ₊₂`; §7.1, Lemma 41.
-/

public section

open Monoid.Coprod TauCeti.GroupAlgGeom.Quadratic
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G X : Type*} [Group G] {n m r : ℕ}

/-! ### The basic automorphisms of the squares -/

section Families

variable {x y : Fin n → X} {z : Fin m → X} {u : Fin r → X} (c : Fin m → G)

section LinkSq

variable (j : Fin m) (k : Fin r) (hzu : z j ≠ u k)
include hzu

open scoped Classical in
private theorem twistHom_linkSqTerm {B : GX G X} (hB : Commute B (coeffAtom z c j * sqAtom u k)) :
    twistHom B (Pi.single (z j) (0, 1) + Pi.single (u k) (-1, 1))
      (coeffAtom z c j * sqAtom u k) = coeffAtom z c j * sqAtom u k := by
  calc _ = B⁻¹ * (coeffAtom z c j * sqAtom u k) * B := by
        simp only [coeffAtom_def, sqAtom_def, map_mul, map_inv, twistHom_inl, twistHom_inr_of,
          Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hzu, Pi.single_eq_of_ne' hzu,
          add_zero, zero_add, zpow_zero, zpow_one, zpow_neg, one_mul, sq]
        group
    _ = _ := hB.inv_mul_cancel

open scoped Classical in
/-- The basic automorphism `zⱼ ↦ zⱼ A`, `uₖ ↦ A⁻¹ uₖ A` of `G[X]`, where `A = zⱼ⁻¹ cⱼ zⱼ uₖ²`,
for distinct variables `zⱼ` and `uₖ`; the other variables are fixed. For the last coefficient
atom and the first square of an equation without commutators it is the automorphism `γₘ` of
[IFT], §7.5. -/
noncomputable def basicLinkSq : MulAut (GX G X) :=
  twist (coeffAtom z c j * sqAtom u k) (Pi.single (z j) (0, 1) + Pi.single (u k) (-1, 1))
    (twistHom_linkSqTerm c j k hzu (Commute.refl _))
    (twistHom_linkSqTerm c j k hzu (Commute.refl _).inv_left)

@[simp]
theorem basicLinkSq_inl (g : G) : basicLinkSq c j k hzu (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_symm_inl (g : G) : (basicLinkSq c j k hzu).symm (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_pow_inl (p : ℕ) (g : G) : (basicLinkSq c j k hzu ^ p) (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_zpow_inl (p : ℤ) (g : G) : (basicLinkSq c j k hzu ^ p) (inl g) = inl g := by
  simp [basicLinkSq]

@[simp]
theorem basicLinkSq_inr_of_z :
    basicLinkSq c j k hzu (inr (.of (z j))) = inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_symm_inr_of_z :
    (basicLinkSq c j k hzu).symm (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k)⁻¹ := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_pow_inr_of_z (p : ℕ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_zpow_inr_of_z (p : ℤ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_inr_of_u :
    basicLinkSq c j k hzu (inr (.of (u k))) =
      (coeffAtom z c j * sqAtom u k)⁻¹ * inr (.of (u k)) * (coeffAtom z c j * sqAtom u k) := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_symm_inr_of_u :
    (basicLinkSq c j k hzu).symm (inr (.of (u k))) =
      (coeffAtom z c j * sqAtom u k) * inr (.of (u k)) * (coeffAtom z c j * sqAtom u k)⁻¹ := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_pow_inr_of_u (p : ℕ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of (u k))) =
      ((coeffAtom z c j * sqAtom u k) ^ p)⁻¹ * inr (.of (u k)) *
        (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_zpow_inr_of_u (p : ℤ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of (u k))) =
      ((coeffAtom z c j * sqAtom u k) ^ p)⁻¹ * inr (.of (u k)) *
        (coeffAtom z c j * sqAtom u k) ^ p := by
  simp [basicLinkSq, hzu]

@[simp]
theorem basicLinkSq_zpow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) (p : ℤ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicLinkSq, twist_zpow_apply, twistHom_inr_of]
  simp [hz, hu]

@[simp]
theorem basicLinkSq_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) :
    basicLinkSq c j k hzu (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne c j k hzu hz hu 1

@[simp]
theorem basicLinkSq_symm_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) :
    (basicLinkSq c j k hzu).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne c j k hzu hz hu (-1)

@[simp]
theorem basicLinkSq_pow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hu : v ≠ u k) (p : ℕ) :
    (basicLinkSq c j k hzu ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLinkSq_zpow_inr_of_of_ne c j k hzu hz hu p

variable (hz : ∀ l ≠ j, z l ≠ z j ∧ z l ≠ u k) (hu : ∀ l ≠ k, u l ≠ z j ∧ u l ≠ u k)
include hz hu

/-- For an equation without commutators, the basic automorphism of the last coefficient atom and
the first square fixes the word `S₁` when no other atom contains `zⱼ` or `uₖ`. -/
theorem basicLinkSq_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0) :
    basicLinkSq c j k hzu (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  subst hn
  have hS : basicMixedWord x y z u c =
      (List.ofFn (Fin.append (coeffAtom z c) (sqAtom u))).prod := by
    simp [basicMixedWord_def, basicMixedAtoms_def, List.ofFn_fin_append]
  rw [hS]
  refine List.map_prod_ofFn_of_adjacent _ _ (i := Fin.castAdd r j) (i' := Fin.natAdd m k)
    (by simp [hj, hk]) (fun l hl hl' => ?_) ?_
  · induction l using Fin.addCases with
    | left l =>
      have hlj : l ≠ j := fun h => hl (h ▸ rfl)
      simp [coeffAtom_def, hz l hlj]
    | right l =>
      have hlk : l ≠ k := fun h => hl' (h ▸ rfl)
      simp [sqAtom_def, hu l hlk]
  · rw [Fin.append_left, Fin.append_right, basicLinkSq, twist_apply]
    exact twistHom_linkSqTerm c j k hzu (.refl _)

theorem basicLinkSq_zpow_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0)
    (p : ℤ) :
    (basicLinkSq c j k hzu ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicLinkSq_basicMixedWord c j k hzu hz hu hn hj hk)) p

theorem basicLinkSq_symm_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0) :
    (basicLinkSq c j k hzu).symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicLinkSq_zpow_basicMixedWord c j k hzu hz hu hn hj hk (-1)

theorem basicLinkSq_pow_basicMixedWord (hn : n = 0) (hj : (j : ℕ) + 1 = m) (hk : (k : ℕ) = 0)
    (p : ℕ) :
    (basicLinkSq c j k hzu ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicLinkSq_zpow_basicMixedWord c j k hzu hz hu hn hj hk p

end LinkSq

section CommSq

variable (i : Fin n) (k : Fin r) (hxy : x i ≠ y i) (hxu : x i ≠ u k)
include hxy hxu

open scoped Classical in
private theorem twistHom_commSqTerm {B : GX G X} (hB : Commute B (inr (.of (y i)) * sqAtom u k)) :
    twistHom B (fun v => if v = x i then (-1, 0) else if v = y i ∨ v = u k then (-1, 1) else 0)
      (inr (.of (y i)) * sqAtom u k) = inr (.of (y i)) * sqAtom u k := by
  calc _ = B⁻¹ * (inr (.of (y i)) * sqAtom u k) * B := by
        simp only [sqAtom_def, map_mul, twistHom_inr_of, hxy.symm, hxu.symm, true_or, or_true,
          ite_true, ite_false, zpow_one, zpow_neg, sq]
        group
    _ = _ := hB.inv_mul_cancel

open scoped Classical in
/-- The basic automorphism `xᵢ ↦ A⁻¹ xᵢ`, `yᵢ ↦ A⁻¹ yᵢ A`, `uₖ ↦ A⁻¹ uₖ A` of `G[X]`, where
`A = yᵢ uₖ²`, for a variable `xᵢ` distinct from `yᵢ` and `uₖ`; the other variables are fixed.
For the last commutator and the first square it is the automorphism `γₘ₊₄ₙ` of [IFT], §7.5. -/
noncomputable def basicCommSq : MulAut (GX G X) :=
  twist (inr (.of (y i)) * sqAtom u k)
    (fun v => if v = x i then (-1, 0) else if v = y i ∨ v = u k then (-1, 1) else 0)
    (twistHom_commSqTerm i k hxy hxu (Commute.refl _))
    (twistHom_commSqTerm i k hxy hxu (Commute.refl _).inv_left)

@[simp]
theorem basicCommSq_inl (g : G) : basicCommSq i k hxy hxu (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_symm_inl (g : G) : (basicCommSq i k hxy hxu).symm (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_pow_inl (p : ℕ) (g : G) : (basicCommSq i k hxy hxu ^ p) (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_zpow_inl (p : ℤ) (g : G) :
    (basicCommSq i k hxy hxu ^ p) (inl g) = inl g := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_inr_of_x :
    basicCommSq i k hxy hxu (inr (.of (x i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_symm_inr_of_x :
    (basicCommSq i k hxy hxu).symm (inr (.of (x i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (x i)) := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_pow_inr_of_x (p : ℕ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (x i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_zpow_inr_of_x (p : ℤ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (x i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (x i)) := by
  simp [basicCommSq]

@[simp]
theorem basicCommSq_inr_of_y :
    basicCommSq i k hxy hxu (inr (.of (y i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) := by
  simp [basicCommSq, hxy.symm]

@[simp]
theorem basicCommSq_symm_inr_of_y :
    (basicCommSq i k hxy hxu).symm (inr (.of (y i))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k)⁻¹ := by
  simp [basicCommSq, hxy.symm]

@[simp]
theorem basicCommSq_pow_inr_of_y (p : ℕ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (y i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, hxy.symm]

@[simp]
theorem basicCommSq_zpow_inr_of_y (p : ℤ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (y i))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, hxy.symm]

@[simp]
theorem basicCommSq_inr_of_u :
    basicCommSq i k hxy hxu (inr (.of (u k))) =
      (inr (.of (y i)) * sqAtom (G := G) u k)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) := by
  simp [basicCommSq, hxu.symm]

@[simp]
theorem basicCommSq_symm_inr_of_u :
    (basicCommSq i k hxy hxu).symm (inr (.of (u k))) =
      (inr (.of (y i)) * sqAtom (G := G) u k) * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k)⁻¹ := by
  simp [basicCommSq, hxu.symm]

@[simp]
theorem basicCommSq_pow_inr_of_u (p : ℕ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (u k))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, hxu.symm]

@[simp]
theorem basicCommSq_zpow_inr_of_u (p : ℤ) :
    (basicCommSq i k hxy hxu ^ p) (inr (.of (u k))) =
      ((inr (.of (y i)) * sqAtom (G := G) u k) ^ p)⁻¹ * inr (.of (u k)) *
        (inr (.of (y i)) * sqAtom u k) ^ p := by
  simp [basicCommSq, hxu.symm]

@[simp]
theorem basicCommSq_zpow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k)
    (p : ℤ) : (basicCommSq i k hxy hxu ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicCommSq, twist_zpow_apply, twistHom_inr_of]
  simp [hx, hy, hu]

@[simp]
theorem basicCommSq_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) :
    basicCommSq i k hxy hxu (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne i k hxy hxu hx hy hu 1

@[simp]
theorem basicCommSq_symm_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k) :
    (basicCommSq i k hxy hxu).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne i k hxy hxu hx hy hu (-1)

@[simp]
theorem basicCommSq_pow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hu : v ≠ u k)
    (p : ℕ) : (basicCommSq i k hxy hxu ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCommSq_zpow_inr_of_of_ne i k hxy hxu hx hy hu p

private theorem basicCommSq_commAtom_mul_sqAtom :
    basicCommSq i k hxy hxu (commAtom (G := G) x y i * sqAtom u k) =
      commAtom x y i * sqAtom u k := by
  simp only [commAtom_def, commutatorElement_def, sqAtom_def, sq, map_mul, map_inv,
    basicCommSq_inr_of_x, basicCommSq_inr_of_y, basicCommSq_inr_of_u]
  group

variable (hz : ∀ l, z l ≠ x i ∧ z l ≠ y i ∧ z l ≠ u k)
  (hx : ∀ l ≠ i, x l ≠ x i ∧ x l ≠ y i ∧ x l ≠ u k)
  (hy : ∀ l ≠ i, y l ≠ x i ∧ y l ≠ y i ∧ y l ≠ u k)
  (hu : ∀ l ≠ k, u l ≠ x i ∧ u l ≠ y i ∧ u l ≠ u k)
include hz hx hy hu

/-- The basic automorphism of the last commutator and the first square fixes the word `S₁` when
no other atom contains `xᵢ`, `yᵢ` or `uₖ`. -/
theorem basicCommSq_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) :
    basicCommSq i k hxy hxu (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  have hS : basicMixedWord x y z u c = (List.ofFn (coeffAtom z c)).prod *
      (List.ofFn (Fin.append (commAtom x y) (sqAtom u))).prod := by
    simp [basicMixedWord_def, basicMixedAtoms_def, List.ofFn_fin_append]
  rw [hS, map_mul]
  congr 1
  · exact List.map_prod_ofFn_of_forall _ _ fun l => by simp [coeffAtom_def, hz l]
  refine List.map_prod_ofFn_of_adjacent _ _ (i := Fin.castAdd r i) (i' := Fin.natAdd n k)
    (by simp [hi, hk]) (fun l hl hl' => ?_) ?_
  · induction l using Fin.addCases with
    | left l =>
      have hli : l ≠ i := fun h => hl (h ▸ rfl)
      simp [commAtom_def, commutatorElement_def, hx l hli, hy l hli]
    | right l =>
      have hlk : l ≠ k := fun h => hl' (h ▸ rfl)
      simp [sqAtom_def, hu l hlk]
  · rw [Fin.append_left, Fin.append_right]
    exact basicCommSq_commAtom_mul_sqAtom i k hxy hxu

theorem basicCommSq_zpow_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) (p : ℤ) :
    (basicCommSq i k hxy hxu ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow ((MulAut.smul_def _ _).trans
    (basicCommSq_basicMixedWord c i k hxy hxu hz hx hy hu hi hk)) p

theorem basicCommSq_symm_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) :
    (basicCommSq i k hxy hxu).symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicCommSq_zpow_basicMixedWord c i k hxy hxu hz hx hy hu hi hk (-1)

theorem basicCommSq_pow_basicMixedWord (hi : (i : ℕ) + 1 = n) (hk : (k : ℕ) = 0) (p : ℕ) :
    (basicCommSq i k hxy hxu ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicCommSq_zpow_basicMixedWord c i k hxy hxu hz hx hy hu hi hk p

end CommSq

section SqMul

variable (u) (k k' : Fin r)

open scoped Classical in
private theorem twistHom_sqMulTerm {B : GX G X}
    (hB : Commute B (inr (.of (u k)) * inr (.of (u k')))) :
    twistHom B (Pi.single (u k) (0, 1) + Pi.single (u k') (-1, 0))
      (inr (.of (u k)) * inr (.of (u k'))) = inr (.of (u k)) * inr (.of (u k')) := by
  rw [map_mul, twistHom_inr_of, twistHom_inr_of]
  by_cases huk : u k = u k'
  · rw [← huk] at hB ⊢
    simp only [Pi.add_apply, Pi.single_eq_same, Prod.mk_add_mk, zero_add, add_zero, zpow_one,
      zpow_neg]
    calc _ = B⁻¹ * (inr (.of (u k)) * inr (.of (u k))) * B := by group
      _ = _ := hB.inv_mul_cancel
  · simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne huk, Pi.single_eq_of_ne' huk,
      add_zero, zero_add, zpow_zero, zpow_one, zpow_neg]
    group

open scoped Classical in
/-- The basic automorphism `uₖ ↦ uₖ A`, `uₖ' ↦ A⁻¹ uₖ'` of `G[X]`, where `A = uₖ uₖ'`, for
distinct variables `uₖ` and `uₖ'` (when `uₖ = uₖ'` it conjugates `uₖ` by `A = uₖ²`, which fixes
it); the other variables are fixed. For the two squares of [IFT], (114), it is the automorphism
`γₘ₊₁`, respectively `γₘ₊₄ₙ₊₁`, of [IFT], §7.5. -/
noncomputable def basicSqMul : MulAut (GX G X) :=
  twist (inr (.of (u k)) * inr (.of (u k'))) (Pi.single (u k) (0, 1) + Pi.single (u k') (-1, 0))
    (twistHom_sqMulTerm u k k' (Commute.refl _))
    (twistHom_sqMulTerm u k k' (Commute.refl _).inv_left)

@[simp]
theorem basicSqMul_inl (g : G) : basicSqMul u k k' (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_symm_inl (g : G) : (basicSqMul u k k').symm (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_pow_inl (p : ℕ) (g : G) : (basicSqMul u k k' ^ p) (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_zpow_inl (p : ℤ) (g : G) : (basicSqMul u k k' ^ p) (inl g) = inl g := by
  simp [basicSqMul]

@[simp]
theorem basicSqMul_inr_of_left (h : u k ≠ u k') :
    basicSqMul u k k' (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_symm_inr_of_left (h : u k ≠ u k') :
    (basicSqMul u k k').symm (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k')))⁻¹ := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_pow_inr_of_left (h : u k ≠ u k') (p : ℕ) :
    (basicSqMul u k k' ^ p) (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) ^ p := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_zpow_inr_of_left (h : u k ≠ u k') (p : ℤ) :
    (basicSqMul u k k' ^ p) (inr (.of (u k))) =
      (inr (.of (u k)) : GX G X) * (inr (.of (u k)) * inr (.of (u k'))) ^ p := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_inr_of_right (h : u k ≠ u k') :
    basicSqMul u k k' (inr (.of (u k'))) =
      ((inr (.of (u k)) : GX G X) * inr (.of (u k')))⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_symm_inr_of_right (h : u k ≠ u k') :
    (basicSqMul u k k').symm (inr (.of (u k'))) =
      ((inr (.of (u k)) : GX G X) * inr (.of (u k'))) * inr (.of (u k')) := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_pow_inr_of_right (h : u k ≠ u k') (p : ℕ) :
    (basicSqMul u k k' ^ p) (inr (.of (u k'))) =
      (((inr (.of (u k)) : GX G X) * inr (.of (u k'))) ^ p)⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_zpow_inr_of_right (h : u k ≠ u k') (p : ℤ) :
    (basicSqMul u k k' ^ p) (inr (.of (u k'))) =
      (((inr (.of (u k)) : GX G X) * inr (.of (u k'))) ^ p)⁻¹ * inr (.of (u k')) := by
  simp [basicSqMul, h]

@[simp]
theorem basicSqMul_zpow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℤ) :
    (basicSqMul u k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicSqMul, twist_zpow_apply, twistHom_inr_of]
  simp [hk, hk']

@[simp]
theorem basicSqMul_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    basicSqMul u k k' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne u k k' hk hk' 1

@[simp]
theorem basicSqMul_symm_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    (basicSqMul u k k').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne u k k' hk hk' (-1)

@[simp]
theorem basicSqMul_pow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℕ) :
    (basicSqMul u k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqMul_zpow_inr_of_of_ne u k k' hk hk' p

open scoped Classical in
/-- When `uₖ = uₖ'`, the automorphism `basicSqMul u k k'` conjugates `uₖ` by `uₖ²`: it is the
identity. -/
@[simp]
theorem basicSqMul_eq_one (h : u k = u k') : basicSqMul (G := G) u k k' = 1 := by
  ext w
  rw [basicSqMul, twist_apply, MulAut.one_apply]
  refine DFunLike.congr_fun (?_ : _ = MonoidHom.id (GX G X)) w
  refine Monoid.Coprod.hom_ext (by simp) (FreeGroup.ext_hom _ _ fun v => ?_)
  simp only [MonoidHom.comp_apply, twistHom_inr_of, MonoidHom.id_apply, ← h]
  obtain rfl | hv := eq_or_ne v (u k)
  · simp only [Pi.add_apply, Pi.single_eq_same, Prod.mk_add_mk, zero_add, add_zero, zpow_one,
      zpow_neg]
    group
  · simp [hv]

private theorem basicSqMul_sqAtom_mul_sqAtom (h : u k ≠ u k') :
    basicSqMul (G := G) u k k' (sqAtom u k * sqAtom u k') = sqAtom u k * sqAtom u k' := by
  simp only [sqAtom_def, sq, map_mul, basicSqMul_inr_of_left u k k' h,
    basicSqMul_inr_of_right u k k' h]
  group

variable {u} (hx : ∀ l, x l ≠ u k ∧ x l ≠ u k') (hy : ∀ l, y l ≠ u k ∧ y l ≠ u k')
  (hz : ∀ l, z l ≠ u k ∧ z l ≠ u k') (hu : ∀ l, l ≠ k → l ≠ k' → u l ≠ u k ∧ u l ≠ u k')
include hx hy hz hu

/-- The basic automorphism `uₖ ↦ uₖ (uₖ uₖ₊₁)`, `uₖ₊₁ ↦ (uₖ uₖ₊₁)⁻¹ uₖ₊₁` of two consecutive
squares fixes the word `S₁` when no other atom contains `uₖ` or `uₖ₊₁`. -/
theorem basicSqMul_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    basicSqMul u k k' (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  obtain h | h := eq_or_ne (u k) (u k')
  · rw [basicSqMul_eq_one u k k' h, MulAut.one_apply]
  rw [basicMixedWord_eq_basicWord_mul, map_mul]
  congr 1
  · rw [basicSqMul, twist_apply]
    exact twistHom_basicWord c (fun l => by simp [hx l]) (fun l => by simp [hy l])
      fun l => by simp [hz l]
  exact List.map_prod_ofFn_of_adjacent _ _ hk (fun l hl hl' => by simp [sqAtom_def, hu l hl hl'])
    (basicSqMul_sqAtom_mul_sqAtom u k k' h)

theorem basicSqMul_zpow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℤ) :
    (basicSqMul u k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicSqMul_basicMixedWord c k k' hx hy hz hu hk)) p

theorem basicSqMul_symm_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    (basicSqMul u k k').symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqMul_zpow_basicMixedWord c k k' hx hy hz hu hk (-1)

theorem basicSqMul_pow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℕ) :
    (basicSqMul u k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqMul_zpow_basicMixedWord c k k' hx hy hz hu hk p

end SqMul

section SqConj

variable (u) (k k' : Fin r)

open scoped Classical in
private theorem twistHom_sqConjTerm {B : GX G X} (hB : Commute B (sqAtom u k * sqAtom u k')) :
    twistHom B (fun v => if v = u k ∨ v = u k' then (-1, 1) else 0)
      (sqAtom u k * sqAtom u k') = sqAtom u k * sqAtom u k' := by
  calc _ = B⁻¹ * (sqAtom u k * sqAtom u k') * B := by
        simp only [sqAtom_def, map_mul, twistHom_inr_of, true_or, or_true, ite_true, zpow_one,
          zpow_neg, sq]
        group
    _ = _ := hB.inv_mul_cancel

open scoped Classical in
/-- The basic automorphism `uₖ ↦ A⁻¹ uₖ A`, `uₖ' ↦ A⁻¹ uₖ' A` of `G[X]`, where `A = uₖ² uₖ'²`;
the other variables are fixed. For the two squares of [IFT], (114), it is the automorphism
`γₘ₊₂`, respectively `γₘ₊₄ₙ₊₂`, of [IFT], §7.5. -/
noncomputable def basicSqConj : MulAut (GX G X) :=
  twist (sqAtom u k * sqAtom u k') (fun v => if v = u k ∨ v = u k' then (-1, 1) else 0)
    (twistHom_sqConjTerm u k k' (Commute.refl _))
    (twistHom_sqConjTerm u k k' (Commute.refl _).inv_left)

@[simp]
theorem basicSqConj_inl (g : G) : basicSqConj u k k' (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_symm_inl (g : G) : (basicSqConj u k k').symm (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_pow_inl (p : ℕ) (g : G) : (basicSqConj u k k' ^ p) (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_zpow_inl (p : ℤ) (g : G) : (basicSqConj u k k' ^ p) (inl g) = inl g := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_inr_of_left :
    basicSqConj u k k' (inr (.of (u k))) =
      (sqAtom (G := G) u k * sqAtom u k')⁻¹ * inr (.of (u k)) * (sqAtom u k * sqAtom u k') := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_symm_inr_of_left :
    (basicSqConj u k k').symm (inr (.of (u k))) =
      (sqAtom (G := G) u k * sqAtom u k') * inr (.of (u k)) * (sqAtom u k * sqAtom u k')⁻¹ := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_pow_inr_of_left (p : ℕ) :
    (basicSqConj u k k' ^ p) (inr (.of (u k))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k)) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_zpow_inr_of_left (p : ℤ) :
    (basicSqConj u k k' ^ p) (inr (.of (u k))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k)) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_inr_of_right :
    basicSqConj u k k' (inr (.of (u k'))) =
      (sqAtom (G := G) u k * sqAtom u k')⁻¹ * inr (.of (u k')) * (sqAtom u k * sqAtom u k') := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_symm_inr_of_right :
    (basicSqConj u k k').symm (inr (.of (u k'))) =
      (sqAtom (G := G) u k * sqAtom u k') * inr (.of (u k')) * (sqAtom u k * sqAtom u k')⁻¹ := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_pow_inr_of_right (p : ℕ) :
    (basicSqConj u k k' ^ p) (inr (.of (u k'))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k')) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_zpow_inr_of_right (p : ℤ) :
    (basicSqConj u k k' ^ p) (inr (.of (u k'))) =
      ((sqAtom (G := G) u k * sqAtom u k') ^ p)⁻¹ * inr (.of (u k')) *
        (sqAtom u k * sqAtom u k') ^ p := by
  simp [basicSqConj]

@[simp]
theorem basicSqConj_zpow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℤ) :
    (basicSqConj u k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicSqConj, twist_zpow_apply, twistHom_inr_of]
  simp [hk, hk']

@[simp]
theorem basicSqConj_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    basicSqConj u k k' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne u k k' hk hk' 1

@[simp]
theorem basicSqConj_symm_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') :
    (basicSqConj u k k').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne u k k' hk hk' (-1)

@[simp]
theorem basicSqConj_pow_inr_of_of_ne {v : X} (hk : v ≠ u k) (hk' : v ≠ u k') (p : ℕ) :
    (basicSqConj u k k' ^ p) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicSqConj_zpow_inr_of_of_ne u k k' hk hk' p

open scoped Classical in
/-- When `uₖ = uₖ'`, the automorphism `basicSqConj u k k'` conjugates `uₖ` by `uₖ⁴`: it is the
identity. -/
@[simp]
theorem basicSqConj_eq_one (h : u k = u k') : basicSqConj (G := G) u k k' = 1 := by
  ext w
  rw [basicSqConj, twist_apply, MulAut.one_apply]
  refine DFunLike.congr_fun (?_ : _ = MonoidHom.id (GX G X)) w
  refine Monoid.Coprod.hom_ext (by simp) (FreeGroup.ext_hom _ _ fun v => ?_)
  simp only [MonoidHom.comp_apply, twistHom_inr_of, MonoidHom.id_apply, ← h, or_self]
  obtain rfl | hv := eq_or_ne v (u k)
  · simp only [sqAtom_def, ← h, ite_true, zpow_one, zpow_neg]
    group
  · simp [hv]

variable {u} (hx : ∀ l, x l ≠ u k ∧ x l ≠ u k') (hy : ∀ l, y l ≠ u k ∧ y l ≠ u k')
  (hz : ∀ l, z l ≠ u k ∧ z l ≠ u k') (hu : ∀ l, l ≠ k → l ≠ k' → u l ≠ u k ∧ u l ≠ u k')
include hx hy hz hu

/-- The basic automorphism conjugating two consecutive square variables by the product of their
squares fixes the word `S₁` when no other atom contains `uₖ` or `uₖ₊₁`. -/
theorem basicSqConj_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    basicSqConj u k k' (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [basicMixedWord_eq_basicWord_mul, map_mul]
  congr 1
  · rw [basicSqConj, twist_apply]
    exact twistHom_basicWord c (fun l => by simp [hx l]) (fun l => by simp [hy l])
      fun l => by simp [hz l]
  exact List.map_prod_ofFn_of_adjacent _ _ hk (fun l hl hl' => by simp [sqAtom_def, hu l hl hl'])
    (by rw [basicSqConj, twist_apply]; exact twistHom_sqConjTerm u k k' (.refl _))

theorem basicSqConj_zpow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℤ) :
    (basicSqConj u k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicSqConj_basicMixedWord c k k' hx hy hz hu hk)) p

theorem basicSqConj_symm_basicMixedWord (hk : (k : ℕ) + 1 = k') :
    (basicSqConj u k k').symm (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqConj_zpow_basicMixedWord c k k' hx hy hz hu hk (-1)

theorem basicSqConj_pow_basicMixedWord (hk : (k : ℕ) + 1 = k') (p : ℕ) :
    (basicSqConj u k k' ^ p) (basicMixedWord x y z u c) = basicMixedWord x y z u c := by
  simpa using basicSqConj_zpow_basicMixedWord c k k' hx hy hz hu hk p

end SqConj

end Families

end TauCeti.GroupAlgGeom.Lift
