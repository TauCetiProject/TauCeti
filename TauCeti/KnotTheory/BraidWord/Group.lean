/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence

/-!
# The group of braid words modulo moves

Braid words modulo Artin relations and free cancellation (`TauCeti.BraidWord.WordEquiv`) form a
group `TauCeti.BraidWordGroup n` under concatenation: the relation is a congruence for
concatenation (`TauCeti.BraidWord.WordEquiv.append`), the empty word is the identity, and the
inverse of a word is its reverse with every sign negated. The represented braid
`TauCeti.BraidWord.toBraid` descends to a multiplicative equivalence
`TauCeti.BraidWordGroup.toBraidMulEquiv` with the braid group `TauCeti.BraidGroup n`. It is
multiplicative by `TauCeti.BraidWord.toBraid_append`, injective by the completeness of the moves
(`TauCeti.BraidWord.toBraid_eq_iff_wordEquiv`) and surjective by
`TauCeti.BraidWord.toBraid_surjective`. A closure invariant which respects the moves is therefore
a function on the braid group.

Free cancellation is needed: Artin steps preserve the length of a word, so the one-letter-pair
word `[(0, 1), (0, -1)]` and the empty word, which both represent `1` in `B₂`, are not related by
Artin steps alone (`TauCeti.BraidWord.not_artinEquiv_cancel_nil`).

## Main definitions

* `TauCeti.BraidWordGroup n`: braid words on `n` strands modulo `WordEquiv`, as a group, with
  `TauCeti.BraidWordGroup.lift` for functions invariant under the moves.
* `TauCeti.BraidWordGroup.toBraidMulEquiv`: **braid words modulo moves are the braid group.**

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 1 (the Artin presentation).
-/

public section

namespace TauCeti

open BraidGroup

/-- Braid words modulo Artin relations and free cancellation, a group under concatenation. -/
-- Exposed because the bodies of the `Mul` and `Inv` instances below are exposed, and they are
-- maps of this quotient. Downstream code uses `mk`, `lift` and `induction_on`.
@[expose] def BraidWordGroup (n : ℕ) : Type :=
  Quotient (BraidWord.wordSetoid n)

namespace BraidWordGroup

variable {n : ℕ}

/-- The class of a braid word. -/
def mk (w : BraidWord n) : BraidWordGroup n :=
  Quotient.mk (BraidWord.wordSetoid n) w

theorem mk_surjective : Function.Surjective (mk (n := n)) :=
  Quotient.mk_surjective

@[elab_as_elim]
theorem induction_on {motive : BraidWordGroup n → Prop} (x : BraidWordGroup n)
    (h : ∀ w, motive (mk w)) : motive x :=
  Quotient.inductionOn x h

/-- A function on braid words which is invariant under the moves, as a function on their
classes. -/
def lift {α : Sort*} (f : BraidWord n → α) (hf : ∀ w w', BraidWord.WordEquiv w w' → f w = f w') :
    BraidWordGroup n → α :=
  Quotient.lift (s := BraidWord.wordSetoid n) f hf

/-- The lift of `f` takes the class of `w` to `f w`. -/
@[simp]
theorem lift_mk {α : Sort*} (f : BraidWord n → α)
    (hf : ∀ w w', BraidWord.WordEquiv w w' → f w = f w') (w : BraidWord n) :
    lift f hf (mk w) = f w :=
  (rfl)

/-- Two words have the same class exactly when they are related by the moves. -/
theorem mk_eq_mk_iff {w w' : BraidWord n} : mk w = mk w' ↔ BraidWord.WordEquiv w w' :=
  Quotient.eq

/-- Two words have the same class exactly when they represent the same braid. -/
theorem mk_eq_mk_iff_toBraid_eq {w w' : BraidWord n} :
    mk w = mk w' ↔ w.toBraid = w'.toBraid :=
  mk_eq_mk_iff.trans BraidWord.toBraid_eq_iff_wordEquiv.symm

instance : One (BraidWordGroup n) := ⟨mk []⟩

instance : Mul (BraidWordGroup n) where
  mul := Quotient.map₂ (sa := BraidWord.wordSetoid n) (sb := BraidWord.wordSetoid n)
    (sc := BraidWord.wordSetoid n) (· ++ ·) fun _ _ hu _ _ hw ↦ BraidWord.WordEquiv.append hu hw

instance : Inv (BraidWordGroup n) where
  inv := Quotient.map (sa := BraidWord.wordSetoid n) (sb := BraidWord.wordSetoid n)
    (fun w : BraidWord n ↦ w.reverse.map fun x ↦ (x.1, -x.2)) fun _ _ h ↦ by
    -- Both inverse words represent the inverse braid, so they are related by the moves.
    refine BraidWord.toBraid_eq_iff_wordEquiv.mp ?_
    rw [BraidWord.toBraid_reverse_map_neg, BraidWord.toBraid_reverse_map_neg, h.toBraid_eq]

@[simp] theorem mk_nil : mk ([] : BraidWord n) = 1 := (rfl)

@[simp] theorem mk_append (w w' : BraidWord n) : mk (w ++ w') = mk w * mk w' := (rfl)

@[simp] theorem inv_mk (w : BraidWord n) : (mk w)⁻¹ = mk (w.reverse.map fun x ↦ (x.1, -x.2)) :=
  (rfl)

instance : Group (BraidWordGroup n) where
  mul_assoc x y z := by
    induction x using induction_on with | h u =>
    induction y using induction_on with | h v =>
    induction z using induction_on with | h w =>
    rw [← mk_append, ← mk_append, ← mk_append, ← mk_append, List.append_assoc]
  one_mul x := by
    induction x using induction_on with | h w => rw [← mk_nil, ← mk_append, List.nil_append]
  mul_one x := by
    induction x using induction_on with | h w => rw [← mk_nil, ← mk_append, List.append_nil]
  inv_mul_cancel x := by
    induction x using induction_on with | h w =>
    rw [inv_mk, ← mk_append, ← mk_nil, mk_eq_mk_iff_toBraid_eq, BraidWord.toBraid_append,
      BraidWord.toBraid_reverse_map_neg, inv_mul_cancel, BraidWord.toBraid_nil]

/-- The braid represented by a class of words. -/
def toBraid : BraidWordGroup n →* BraidGroup n where
  toFun := lift BraidWord.toBraid fun _ _ h ↦ BraidWord.WordEquiv.toBraid_eq h
  map_one' := BraidWord.toBraid_nil
  map_mul' x y := by
    induction x using induction_on with | h u =>
    induction y using induction_on with | h v =>
    rw [← mk_append]
    exact BraidWord.toBraid_append u v

@[simp] theorem toBraid_mk (w : BraidWord n) : toBraid (mk w) = w.toBraid := (rfl)

/-- **Braid words modulo moves are the braid group**: the represented braid is a multiplicative
equivalence from classes of braid words modulo Artin relations and free cancellation to the braid
group. -/
noncomputable def toBraidMulEquiv : BraidWordGroup n ≃* BraidGroup n :=
  MulEquiv.ofBijective toBraid
    ⟨fun x y h ↦ by
      induction x using induction_on with | h u =>
      induction y using induction_on with | h v =>
      exact mk_eq_mk_iff_toBraid_eq.mpr h,
    fun b ↦ (BraidWord.toBraid_surjective b).elim fun w hw ↦ ⟨mk w, hw⟩⟩

@[simp] theorem toBraidMulEquiv_mk (w : BraidWord n) : toBraidMulEquiv (mk w) = w.toBraid :=
  (rfl)

/-- The equivalence is the represented braid. -/
@[simp] theorem coe_toBraidMulEquiv : ⇑(toBraidMulEquiv (n := n)) = ⇑toBraid :=
  (rfl)

/-- The inverse equivalence sends the braid represented by a word to the class of that word. -/
@[simp] theorem toBraidMulEquiv_symm_toBraid (w : BraidWord n) :
    toBraidMulEquiv.symm w.toBraid = mk w :=
  toBraidMulEquiv.symm_apply_eq.mpr rfl

end BraidWordGroup

end TauCeti
