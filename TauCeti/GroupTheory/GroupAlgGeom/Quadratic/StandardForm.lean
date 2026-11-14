/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import Mathlib.Algebra.Group.Commutator

/-!
# The rewriting rules of the standard form

By [IFT], §2.7, Lemma 1, a strictly quadratic word of `G[X]` is brought to a standard quadratic
word, or to a coefficient, by a `G`-automorphism of `G[X]` and a conjugation. The automorphism is
a product of elementary ones (`GX.elementaryAut`): the substitutions `x ↦ a x b`, for words `a`
and `b` in which `x` does not occur, and the inversions `x ↦ x⁻¹`. This file proves the rewriting
rules of the reduction, which follows the normal form of polygonal words in the classification of
compact surfaces, with the coefficients in the role of boundary edges.

## Main results

* `GX.transvection_crossCap`: the cross-cap rule `x U x V ↦ x² U⁻¹ V`.
* `GX.transvection_rotate`: the rotation rule `x U V x⁻¹ W ↦ x V U x⁻¹ W`.
* `GX.exists_mem_elementaryAut_handle`: the handle rule, carrying `x U y V x⁻¹ W y⁻¹ Z`, up to
  conjugation, to `x⁻¹ y⁻¹ x y Z W V U`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Lemma 1.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 6.
* J. Gallier, D. Xu, *A guide to the classification theorem for compact surfaces*, Springer
  (2013), Chapter 6, Lemma 6.1.
-/

public section

open Monoid.Coprod Subgroup
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.GX

variable {G X : Type*} [Group G] [DecidableEq X] {x y : X} {U V W Z : GX G X}

/-- The cross-cap rule: `x ↦ x U⁻¹` turns `x U x V` into `x² U⁻¹ V`. -/
theorem transvection_crossCap (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * inr (FreeGroup.of x) * V) =
      inr (FreeGroup.of x) ^ 2 * (U⁻¹ * V) := by
  simp [hU, hV, mul_assoc, pow_two]

/-- The rotation rule: `x ↦ x U⁻¹` turns `x U V x⁻¹ W` into `x V U x⁻¹ W`. -/
theorem transvection_rotate (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) (hW : W ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * V * (inr (FreeGroup.of x))⁻¹ * W) =
      inr (FreeGroup.of x) * V * U * (inr (FreeGroup.of x))⁻¹ * W := by
  simp [hU, hV, hW, mul_assoc]

/-- The handle rule: an elementary automorphism and a conjugation turn `x U y V x⁻¹ W y⁻¹ Z`
into `[x, y] Z W V U`, where `[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_handle (hxy : x ≠ y) (hU : U ∈ avoiding x ⊓ avoiding y)
    (hV : V ∈ avoiding x ⊓ avoiding y) (hW : W ∈ avoiding x ⊓ avoiding y)
    (hZ : Z ∈ avoiding x ⊓ avoiding y) : ∃ f ∈ elementaryAut G X, ∃ u : GX G X,
      u * f (inr (FreeGroup.of x) * U * inr (FreeGroup.of y) * V * (inr (FreeGroup.of x))⁻¹ * W *
          (inr (FreeGroup.of y))⁻¹ * Z) * u⁻¹ =
        ⁅(inr (FreeGroup.of x) : GX G X)⁻¹, (inr (FreeGroup.of y))⁻¹⁆ * (Z * W * V * U) := by
  rw [mem_inf] at hU hV hW hZ
  -- `x ↦ x U⁻¹`, then `y ↦ y (V U)⁻¹`, then `x ↦ (W V U) x` give `(W V U) x y x⁻¹ y⁻¹ Z`;
  -- inverting `x` and `y` and conjugating by `(W V U)⁻¹` give `x⁻¹ y⁻¹ x y Z W V U`.
  refine ⟨invertVar G y * invertVar G x *
      transvection x (W * V * U) 1 (mul_mem (mul_mem hW.1 hV.1) hU.1) (one_mem _) *
      transvection y 1 (V * U)⁻¹ (one_mem _) (inv_mem (mul_mem hV.2 hU.2)) *
      transvection x 1 U⁻¹ (one_mem _) (inv_mem hU.1), ?_, (W * V * U)⁻¹, ?_⟩
  · refine mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_ <;> simp
  · simp [hU.1, hU.2, hV.1, hV.2, hW.1, hW.2, hZ.1, hZ.2, hxy, hxy.symm, commutatorElement_def,
      mul_assoc]

end TauCeti.GroupAlgGeom.GX
