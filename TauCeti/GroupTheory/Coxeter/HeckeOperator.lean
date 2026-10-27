/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.GroupTheory.Coxeter.Matsumoto
public import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# The regular operators of an Iwahori–Hecke algebra

Let `cs : CoxeterSystem M W` be a Coxeter system and `c` an element of a commutative semiring `R`.
On the free `R`-module `W →₀ R`, with basis vectors `e w = Finsupp.single w 1`, this file defines
for every simple reflection `s = cs.simple i` the two operators

* `CoxeterSystem.heckeLeftMul cs c i`, with `e w ↦ e (s * w)` if `ℓ (s * w) > ℓ w` and
  `e w ↦ c • e w + e (s * w)` if `ℓ (s * w) < ℓ w`, and
* `CoxeterSystem.heckeRightMul cs c i`, the same rule for `w * s`.

These are left and right multiplication by the generator `T s` in the regular representation of
the Iwahori–Hecke algebra with quadratic relation `T s ^ 2 = c • T s + 1`, written in the basis
`T w`. They are the device by which one proves that the `T w` are linearly independent: the
operators can be written down without knowing the algebra, and they satisfy its defining relations.

The key point is that **left and right operators commute**
(`CoxeterSystem.commute_heckeLeftMul_heckeRightMul`); the one non-formal case of this is
the length lemma `CoxeterSystem.simple_mul_eq_mul_simple_of_length_eq`. Consequently an operator
commuting with all right operators is determined by its value on `e 1`
(`CoxeterSystem.ext_of_commute_heckeRightMul`). Since a product of left operators along a reduced
word sends `e 1` to the basis vector of the element it spells
(`CoxeterSystem.prod_map_heckeLeftMul_apply_single_one`), and braid words are reduced, the left
operators satisfy the braid relations (`CoxeterSystem.prod_map_heckeLeftMul_braidWord`). Together
with the quadratic relation (`CoxeterSystem.heckeLeftMul_mul_self`) these are the relations of the
Iwahori–Hecke algebra.

## Main definitions

* `CoxeterSystem.heckeLeftMul`, `CoxeterSystem.heckeRightMul`: the left and right regular
  operators of a simple reflection.

## Main results

* `CoxeterSystem.commute_heckeLeftMul_heckeRightMul`: left and right operators commute.
* `CoxeterSystem.heckeLeftMul_mul_self`: the quadratic relation.
* `CoxeterSystem.ext_of_commute_heckeRightMul`: an operator commuting with the right operators is
  determined by its value on `e 1`.
* `CoxeterSystem.prod_map_heckeLeftMul_apply_single_one`: left operators along a reduced word.
* `CoxeterSystem.prod_map_heckeLeftMul_braidWord`: the braid relations.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Chapter 7, whose
  construction of the generic algebra this follows.
-/

public section

namespace CoxeterSystem

open Finsupp

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R : Type*} [CommSemiring R] (c : R)

local prefix:100 "ℓ " => cs.length
local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

open scoped Classical in
/-- Left multiplication by the Hecke generator `T (s i)` in the basis `T w`, with quadratic
relation `T (s i) ^ 2 = c • T (s i) + 1`: the basis vector of `w` goes to that of `s i * w` when
`i` is not a left descent of `w`, and to `c` times itself plus that of `s i * w` when it is. -/
noncomputable def heckeLeftMul (i : B) : Module.End R (W →₀ R) :=
  linearCombination R fun w ↦
    (if cs.IsLeftDescent w i then single w c else 0) + single (s i * w) 1

open scoped Classical in
/-- Right multiplication by the Hecke generator `T (s i)` in the basis `T w`, with quadratic
relation `T (s i) ^ 2 = c • T (s i) + 1`: the basis vector of `w` goes to that of `w * s i` when
`i` is not a right descent of `w`, and to `c` times itself plus that of `w * s i` when it is. -/
noncomputable def heckeRightMul (i : B) : Module.End R (W →₀ R) :=
  linearCombination R fun w ↦
    (if cs.IsRightDescent w i then single w c else 0) + single (w * s i) 1

variable {cs c}

/-- **Left multiplication, length increase.** -/
theorem heckeLeftMul_single_of_not_isLeftDescent {w : W} {i : B} (h : ¬cs.IsLeftDescent w i)
    (r : R) : cs.heckeLeftMul c i (single w r) = single (s i * w) r := by
  simp [heckeLeftMul, h]

/-- **Left multiplication, length decrease.** -/
theorem heckeLeftMul_single_of_isLeftDescent {w : W} {i : B} (h : cs.IsLeftDescent w i)
    (r : R) : cs.heckeLeftMul c i (single w r) = c • single w r + single (s i * w) r := by
  simp [heckeLeftMul, h, mul_comm]

/-- **Right multiplication, length increase.** -/
theorem heckeRightMul_single_of_not_isRightDescent {w : W} {i : B} (h : ¬cs.IsRightDescent w i)
    (r : R) : cs.heckeRightMul c i (single w r) = single (w * s i) r := by
  simp [heckeRightMul, h]

/-- **Right multiplication, length decrease.** -/
theorem heckeRightMul_single_of_isRightDescent {w : W} {i : B} (h : cs.IsRightDescent w i)
    (r : R) : cs.heckeRightMul c i (single w r) = c • single w r + single (w * s i) r := by
  simp [heckeRightMul, h, mul_comm]

variable (cs c)

/-- **The quadratic relation** for the left operators:
`heckeLeftMul cs c i ^ 2 = c • heckeLeftMul cs c i + 1`. -/
theorem heckeLeftMul_mul_self (i : B) :
    cs.heckeLeftMul c i * cs.heckeLeftMul c i = c • cs.heckeLeftMul c i + 1 := by
  refine Finsupp.lhom_ext fun w r ↦ ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  by_cases h : cs.IsLeftDescent w i
  · have h' : ¬cs.IsLeftDescent (s i * w) i := cs.isLeftDescent_iff_not_isLeftDescent_mul.mp h
    simp only [heckeLeftMul_single_of_isLeftDescent h, heckeLeftMul_single_of_not_isLeftDescent h',
      map_add, map_smul, cs.simple_mul_simple_cancel_left]
  · have h' : cs.IsLeftDescent (s i * w) i := by
      rwa [cs.isLeftDescent_iff_not_isLeftDescent_mul, cs.simple_mul_simple_cancel_left]
    simp only [heckeLeftMul_single_of_not_isLeftDescent h, heckeLeftMul_single_of_isLeftDescent h',
      cs.simple_mul_simple_cancel_left]

/-- **Left and right operators commute**: `heckeLeftMul cs c i` and `heckeRightMul cs c j`
commute for all `i` and `j`. -/
theorem commute_heckeLeftMul_heckeRightMul (i j : B) :
    Commute (cs.heckeLeftMul c i) (cs.heckeRightMul c j) := by
  -- On a basis vector `e w` this is a case analysis on the lengths of `w`, `s i * w`, `w * s j`
  -- and `s i * w * s j`; in the two cases where lengths cannot tell `s i * w` and `w * s j`
  -- apart, they are equal by `CoxeterSystem.simple_mul_eq_mul_simple_of_length_eq`.
  refine Finsupp.lhom_ext fun w r ↦ ?_
  simp only [Module.End.mul_apply]
  have hl := cs.length_simple_mul w i
  have hr := cs.length_mul_simple w j
  have hlr := cs.length_simple_mul (w * s j) i
  have hrl := cs.length_mul_simple (s i * w) j
  have hkey := cs.simple_mul_eq_mul_simple_of_length_eq (i := i) (j := j) (w := w)
  rw [mul_assoc] at hrl hkey
  -- Split on the four descents involved, apply both sides, and discard the impossible cases.
  by_cases h₁ : cs.IsLeftDescent w i <;> by_cases h₂ : cs.IsRightDescent w j <;>
    by_cases h₃ : cs.IsLeftDescent (w * s j) i <;> by_cases h₄ : cs.IsRightDescent (s i * w) j <;>
    simp only [heckeLeftMul_single_of_isLeftDescent, heckeLeftMul_single_of_not_isLeftDescent,
      heckeRightMul_single_of_isRightDescent, heckeRightMul_single_of_not_isRightDescent, h₁, h₂,
      h₃, h₄, not_false_eq_true, map_add, map_smul, smul_add, mul_assoc] <;>
    simp only [isLeftDescent_iff, isRightDescent_iff, mul_assoc] at h₁ h₂ h₃ h₄
  all_goals first
    | omega
    | rw [hkey (by omega) (by omega)]
    | abel1

variable {c} in
/-- **An operator commuting with the right operators is determined by its value on `e 1`.** -/
theorem ext_of_commute_heckeRightMul {f g : Module.End R (W →₀ R)}
    (hf : ∀ j, Commute f (cs.heckeRightMul c j)) (hg : ∀ j, Commute g (cs.heckeRightMul c j))
    (h : f (single 1 1) = g (single 1 1)) : f = g := by
  -- Every basis vector `e w` is obtained from `e 1` by right operators along a reduced word for
  -- `w`; induct on the length of `w`, peeling off a right descent.
  refine Finsupp.lhom_ext' fun w ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  induction hn : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : w = 1
    · rw [hw, h]
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    have hj' : ¬cs.IsRightDescent (w * s j) j :=
      cs.isRightDescent_iff_not_isRightDescent_mul.mp hj
    have hsingle : single w (1 : R) = cs.heckeRightMul c j (single (w * s j) 1) := by
      rw [heckeRightMul_single_of_not_isRightDescent hj', cs.simple_mul_simple_cancel_right]
    have hlt : ℓ (w * s j) < n := hn ▸ hj
    rw [hsingle, ← Module.End.mul_apply, (hf j).eq, Module.End.mul_apply, ih _ hlt _ rfl,
      ← Module.End.mul_apply, ← (hg j).eq, Module.End.mul_apply]

/-- Left operators along a reduced word `ω` send `e 1` to the basis vector of the element `ω`
spells. -/
theorem prod_map_heckeLeftMul_apply_single_one {ω : List B} (hω : cs.IsReduced ω) :
    (ω.map (cs.heckeLeftMul c)).prod (single 1 1) = single (π ω) 1 := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hi : ¬cs.IsLeftDescent (π ω) i := by
      rw [cs.not_isLeftDescent_iff, ← cs.wordProd_cons, hω.eq, hω'.eq, List.length_cons]
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hω',
      heckeLeftMul_single_of_not_isLeftDescent hi, cs.wordProd_cons]

/-- **The braid relations** for the left operators: the two braid words at `(i, i')` give the
same operator. -/
theorem prod_map_heckeLeftMul_braidWord (i i' : B) :
    ((braidWord M i i').map (cs.heckeLeftMul c)).prod =
      ((braidWord M i' i).map (cs.heckeLeftMul c)).prod := by
  -- Both sides commute with the right operators and send `e 1` to the basis vector of the same
  -- element, since braid words are reduced (`CoxeterSystem.isReduced_braidWord`).
  have hcomm (ω : List B) (j : B) :
      Commute (ω.map (cs.heckeLeftMul c)).prod (cs.heckeRightMul c j) :=
    Commute.list_prod_left _ _ fun f hf ↦ by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hf
      exact cs.commute_heckeLeftMul_heckeRightMul c k j
  refine cs.ext_of_commute_heckeRightMul (hcomm _) (hcomm _) ?_
  rw [cs.prod_map_heckeLeftMul_apply_single_one c (cs.isReduced_braidWord i i'),
    cs.prod_map_heckeLeftMul_apply_single_one c (cs.isReduced_braidWord i' i),
    cs.wordProd_braidWord_eq]

end CoxeterSystem
