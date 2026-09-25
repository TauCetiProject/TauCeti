/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import TauCeti.GroupTheory.PresentedGroup

/-!
# Index-two Reidemeister--Schreier rewriting for presentations by involutions

Let `G = ⟨X | R⟩` be a group presented by involutions: every generator squares to the identity in
`G`, and every relator of `R` other than those squares is a word of even length. Sending every
generator to the nontrivial element of `C₂` then defines the **parity homomorphism**
`G →* C₂`, and its kernel is a subgroup of index at most two. The Reidemeister--Schreier method
presents that kernel on the Schreier generators of the transversal `{1, a}` for a distinguished
generator `a`: the generator attached to `x ≠ a` is `a x`, the one attached to `a` is trivial, and
a source word `x₁ x₂ x₃ ⋯` of even length rewrites as `(a x₁)⁻¹ (a x₂) (a x₃)⁻¹ ⋯`, the sign of
each letter alternating with its position. The rewrite of a relator `r` and of its conjugate
`a r a` together present the kernel.

This file proves that theorem for such presentations. `TauCeti.schreierWord` is the rewrite,
`TauCeti.schreierRelators` is the rewritten relator set, `TauCeti.IsSchreierIndexTwoSource`
records the hypotheses on the source presentation, and
`TauCeti.IsSchreierIndexTwoSource.mulEquivKerParityHom` is the identification of the rewritten
presented group with the kernel of the parity homomorphism. The kernel is the commutator subgroup
as soon as all generators agree in the abelianization,
`TauCeti.IsSchreierIndexTwoSource.commutator_eq_ker_parityHom`.

The generator index type of the rewritten presentation is left free, as an equivalence `e` between
the source generators other than `a` and a type `β`, so that a transcription indexed by `Fin n` is
a direct instance.

## Main definitions

* `TauCeti.lengthParity`: the homomorphism from the free group to `C₂` sending every generator to
  the nontrivial element.
* `TauCeti.schreierWord` and `TauCeti.schreierRelators`: the Reidemeister--Schreier rewrite of a
  word and of a set of words for the transversal `{1, a}`.
* `TauCeti.IsSchreierIndexTwoSource`: the hypotheses on a source presentation `R` and the set `W`
  of words to rewrite.
* `TauCeti.IsSchreierIndexTwoSource.parityHom`: the parity homomorphism of the source presented
  group.
* `TauCeti.IsSchreierIndexTwoSource.toPresentedGroup`: the homomorphism from the rewritten
  presented group to the source presented group, sending the Schreier generator of `x` to `a x`.
* `TauCeti.IsSchreierIndexTwoSource.mulEquivKerParityHom` and
  `TauCeti.IsSchreierIndexTwoSource.mulEquivCommutator`: the rewritten presented group is the
  kernel of the parity homomorphism, and the commutator subgroup when all generators agree in the
  abelianization.
* `TauCeti.GroupPresentation.mulEquivCommutator`: the same identification for a transcribed
  presentation row whose relations are the rewritten relators.

## Main results

* `TauCeti.IsSchreierIndexTwoSource.range_toPresentedGroup_eq_ker_parityHom`: the rewritten
  presented group maps onto the kernel of the parity homomorphism.
* `TauCeti.IsSchreierIndexTwoSource.toPresentedGroup_injective`: that map is injective.
* `TauCeti.IsSchreierIndexTwoSource.commutator_eq_ker_parityHom`: the kernel of the parity
  homomorphism is the commutator subgroup when all generators agree in the abelianization.

## References

* W. Magnus, A. Karrass and D. Solitar, *Combinatorial Group Theory*, §2.3, for the
  Reidemeister--Schreier method.
* D. L. Johnson, *Presentations of Groups*, 2nd ed., Chapter 9.
-/

public section

namespace TauCeti

open Multiplicative

variable {α β : Type*}

/-! ## The length parity -/

/-- **The length parity of a word**: the homomorphism from the free group on `α` to `C₂` sending
every generator to the nontrivial element. On the word `L` it is the parity of the length of `L`,
`TauCeti.lengthParity_mk`. -/
def lengthParity (α : Type*) : FreeGroup α →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun _ => ofAdd 1

/-- Every generator has odd length parity. -/
@[simp]
theorem lengthParity_of (x : α) : lengthParity α (FreeGroup.of x) = ofAdd 1 :=
  FreeGroup.lift_apply_of

/-- The inverse of a generator has odd length parity. -/
theorem lengthParity_mk_singleton_false (x : α) :
    lengthParity α (FreeGroup.mk [(x, false)]) = ofAdd 1 := by
  simp only [MonoidHom.apply_freeGroup_mk, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Bool.cond_false, mul_one, lengthParity_of]
  decide

/-- **The length parity of a word is the parity of its length.** -/
theorem lengthParity_mk (L : PresentationWord α) :
    lengthParity α (FreeGroup.mk L) = ofAdd (L.length : ZMod 2) := by
  induction L with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons p L ih =>
    obtain ⟨x, b⟩ := p
    conv_lhs => rw [← List.singleton_append]
    rw [← FreeGroup.mul_mk (L₁ := [(x, b)]) (L₂ := L), map_mul, ih, List.length_cons,
      Nat.cast_succ, ofAdd_add, mul_comm]
    congr 1
    cases b
    · exact lengthParity_mk_singleton_false x
    · exact lengthParity_of x

/-! ## The rewrite -/

section Rewrite

variable [DecidableEq α] (a : α) (e : {x : α // x ≠ a} ≃ β)

/-- **The Reidemeister--Schreier rewrite of a word** for the transversal `{1, a}`, on the Schreier
generators indexed by `β` through `e`. The Boolean `positive` records whether the current
transversal representative is `a`: a source letter `x ≠ a` read at representative `a` contributes
the generator `a x` and read at representative `1` contributes its inverse, the letter `a`
contributes nothing, and every letter switches the representative. The sign of a source letter is
ignored, the source generators being involutions.

Starting from `false` rewrites the word itself, starting from `true` rewrites its conjugate by
`a`. -/
def schreierWord : Bool → PresentationWord α → PresentationWord β
  | _, [] => []
  | positive, (x, _) :: w =>
      (if h : x = a then [] else [(e ⟨x, h⟩, positive)]) ++ schreierWord (!positive) w

/-- The empty word rewrites to the empty word. -/
@[simp]
theorem schreierWord_nil (positive : Bool) : schreierWord a e positive [] = [] := by
  simp only [schreierWord]

/-- One step of the rewrite: the letter `a` contributes nothing and any other letter contributes
its Schreier generator, inverted exactly when the current representative is `1`; the representative
then switches. -/
@[simp]
theorem schreierWord_cons (positive : Bool) (x : α) (s : Bool) (w : PresentationWord α) :
    schreierWord a e positive ((x, s) :: w) =
      (if h : x = a then [] else [(e ⟨x, h⟩, positive)]) ++ schreierWord a e (!positive) w := by
  simp only [schreierWord]

/-- Starting the rewrite from the other representative flips every sign. -/
theorem schreierWord_not (positive : Bool) (w : PresentationWord α) :
    schreierWord a e (!positive) w = (schreierWord a e positive w).map fun p => (p.1, !p.2) := by
  induction w generalizing positive with
  | nil => simp
  | cons p w ih =>
    obtain ⟨x, s⟩ := p
    rw [schreierWord_cons, schreierWord_cons, List.map_append, ih (!positive)]
    congr 1
    split_ifs <;> simp

/-- The rewrite of a word is the rewrite of its first letter followed by the rewrite of the rest
from the other representative. -/
theorem schreierWord_cons_eq_append (positive : Bool) (x : α) (s : Bool) (w : PresentationWord α) :
    schreierWord a e positive ((x, s) :: w) =
      schreierWord a e positive [(x, s)] ++ schreierWord a e (!positive) w := by
  simp [schreierWord_cons]

/-- **The Reidemeister--Schreier relators** of a set `W` of source words: the rewrites of every
word of `W` from both transversal representatives, that is, the rewrites of `w` and of
`a w a` for every `w ∈ W`. -/
def schreierRelators (W : Set (PresentationWord α)) : Set (FreeGroup β) :=
  {r | ∃ (positive : Bool) (w : PresentationWord α),
    w ∈ W ∧ FreeGroup.mk (schreierWord a e positive w) = r}

variable {W : Set (PresentationWord α)}

@[simp]
theorem mem_schreierRelators {r : FreeGroup β} :
    r ∈ schreierRelators a e W ↔
      ∃ (positive : Bool) (w : PresentationWord α),
        w ∈ W ∧ FreeGroup.mk (schreierWord a e positive w) = r :=
  Iff.rfl

theorem mk_schreierWord_mem_schreierRelators (positive : Bool) {w : PresentationWord α}
    (hw : w ∈ W) : FreeGroup.mk (schreierWord a e positive w) ∈ schreierRelators a e W :=
  ⟨positive, w, hw, rfl⟩

variable (W)

/-- **The Schreier generator of a source generator** in the rewritten presented group: the class of
the generator indexed by `x` for `x ≠ a`, and the identity for `x = a`. It stands for the element
`a x` of the source group, `TauCeti.IsSchreierIndexTwoSource.toPresentedGroup_schreierGenerator`. -/
def schreierGenerator (x : α) : PresentedGroup (schreierRelators a e W) :=
  if hx : x = a then 1 else PresentedGroup.of (e ⟨x, hx⟩)

@[simp]
theorem schreierGenerator_self : schreierGenerator a e W a = 1 := by
  simp [schreierGenerator]

theorem schreierGenerator_of_ne {x : α} (hx : x ≠ a) :
    schreierGenerator a e W x = PresentedGroup.of (e ⟨x, hx⟩) := by
  simp [schreierGenerator, hx]

/-- The Schreier generator of the source generator indexed by `y` is the generator `y`. -/
@[simp]
theorem schreierGenerator_symm (y : β) :
    schreierGenerator a e W (e.symm y).1 = PresentedGroup.of y := by
  rw [schreierGenerator_of_ne a e W (e.symm y).2, Subtype.coe_eta, Equiv.apply_symm_apply]

/-- The class of the singleton rewrite of a source letter read at representative `1` is the inverse
of its Schreier generator. -/
theorem mk_mk_schreierWord_singleton (x : α) (s : Bool) :
    PresentedGroup.mk (schreierRelators a e W) (FreeGroup.mk (schreierWord a e false [(x, s)])) =
      (schreierGenerator a e W x)⁻¹ := by
  rw [schreierWord_cons, schreierWord_nil, List.append_nil]
  split_ifs with hx
  · rw [hx, schreierGenerator_self, inv_one, ← FreeGroup.one_eq_mk, map_one]
  · rw [schreierGenerator_of_ne a e W hx, PresentedGroup.mk_mk]
    simp

/-! ## Conjugation by the transversal element -/

/-- **Inverting every Schreier generator**, as an endomorphism of the rewritten presented group. It
is the action of conjugation by `a` on the kernel, since `a (a x) a⁻¹ = x a = (a x)⁻¹` for
involutions; it is an automorphism, `TauCeti.schreierInvAut`. -/
def schreierInvHom :
    PresentedGroup (schreierRelators a e W) →* PresentedGroup (schreierRelators a e W) :=
  PresentedGroup.toGroup (f := fun y => (PresentedGroup.of y)⁻¹) (by
    rintro r ⟨positive, w, hw, rfl⟩
    rw [PresentedGroup.lift_inv_of_mk, ← schreierWord_not]
    exact PresentedGroup.one_of_mem (mk_schreierWord_mem_schreierRelators a e (!positive) hw))

@[simp]
theorem schreierInvHom_of (y : β) :
    schreierInvHom a e W (PresentedGroup.of y) = (PresentedGroup.of y)⁻¹ :=
  PresentedGroup.toGroup.of _

/-- Inverting every generator is an involution. -/
@[simp]
theorem schreierInvHom_apply_apply (g : PresentedGroup (schreierRelators a e W)) :
    schreierInvHom a e W (schreierInvHom a e W g) = g := by
  have h : (schreierInvHom a e W).comp (schreierInvHom a e W) = MonoidHom.id _ := by
    ext y
    simp
  exact DFunLike.congr_fun h g

/-- Inverting every generator inverts every Schreier generator. -/
@[simp]
theorem schreierInvHom_schreierGenerator (x : α) :
    schreierInvHom a e W (schreierGenerator a e W x) = (schreierGenerator a e W x)⁻¹ := by
  unfold schreierGenerator
  split_ifs
  · simp
  · exact schreierInvHom_of a e W _

/-- **Inverting every Schreier generator**, as an automorphism of the rewritten presented group. -/
def schreierInvAut : MulAut (PresentedGroup (schreierRelators a e W)) :=
  MonoidHom.toMulEquiv (schreierInvHom a e W) (schreierInvHom a e W)
    (by ext y; simp) (by ext y; simp)

@[simp]
theorem schreierInvAut_apply (g : PresentedGroup (schreierRelators a e W)) :
    schreierInvAut a e W g = schreierInvHom a e W g :=
  (rfl)

/-- The inverting automorphism has order dividing two. -/
theorem schreierInvAut_sq : schreierInvAut a e W ^ 2 = 1 := by
  ext g
  simp [sq]

/-- **The action of `C₂` on the rewritten presented group** through the inverting automorphism:
the nontrivial element acts by `TauCeti.schreierInvAut`. -/
def schreierConjAction :
    Multiplicative (ZMod 2) →* MulAut (PresentedGroup (schreierRelators a e W)) where
  toFun g := schreierInvAut a e W ^ g.toAdd.val
  map_one' := by simp
  map_mul' g h := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (schreierInvAut_sq a e W), pow_add]

theorem schreierConjAction_apply (g : Multiplicative (ZMod 2)) :
    schreierConjAction a e W g = schreierInvAut a e W ^ g.toAdd.val :=
  (rfl)

/-- The nontrivial element of `C₂` acts by inverting every Schreier generator. -/
theorem schreierConjAction_ofAdd_one :
    schreierConjAction a e W (ofAdd 1) = schreierInvAut a e W := by
  simp [schreierConjAction_apply, ZMod.val_one_eq_one_mod]

end Rewrite

/-! ## The source presentation -/

/-- **The hypotheses of index-two Reidemeister--Schreier rewriting on a source presentation.** The
group is `PresentedGroup R`; `W` is the set of source words to rewrite. Every generator is an
involution in the presented group, every word of `W` has even length and is a relation of the
presented group, and every relator of `R` is either the class of a word of `W` or the square of a
generator. The squares are what the rewrite leaves out: they rewrite to words that are trivial in
the free group. -/
structure IsSchreierIndexTwoSource (R : Set (FreeGroup α)) (W : Set (PresentationWord α)) :
    Prop where
  /-- Every generator is an involution in the presented group. -/
  of_mul_of : ∀ x : α, (PresentedGroup.of x : PresentedGroup R) * PresentedGroup.of x = 1
  /-- Every source word has even length. -/
  even_length : ∀ w ∈ W, Even w.length
  /-- Every source word is a relation of the presented group. -/
  mk_mk_eq_one : ∀ w ∈ W, PresentedGroup.mk R (FreeGroup.mk w) = 1
  /-- Every relator is the class of a source word or the square of a generator. -/
  eq_mk_or_eq_of_mul_of : ∀ r ∈ R,
    (∃ w ∈ W, FreeGroup.mk w = r) ∨ ∃ x : α, FreeGroup.of x * FreeGroup.of x = r

namespace IsSchreierIndexTwoSource

variable {R : Set (FreeGroup α)} {W : Set (PresentationWord α)} (h : IsSchreierIndexTwoSource R W)
include h

theorem inv_of (x : α) : (PresentedGroup.of x : PresentedGroup R)⁻¹ = PresentedGroup.of x :=
  inv_eq_of_mul_eq_one_right (h.of_mul_of x)

/-- Reading one letter of a word in the source presented group, whichever sign it carries. -/
theorem mk_mk_cons (x : α) (s : Bool) (L : PresentationWord α) :
    PresentedGroup.mk R (FreeGroup.mk ((x, s) :: L)) =
      PresentedGroup.of x * PresentedGroup.mk R (FreeGroup.mk L) := by
  simp only [PresentedGroup.mk_mk, List.map_cons, List.prod_cons]
  congr 1
  cases s
  · exact h.inv_of x
  · rfl

/-! ### The parity homomorphism -/

theorem lengthParity_eq_one : ∀ r ∈ R, lengthParity α r = 1 := by
  intro r hr
  rcases h.eq_mk_or_eq_of_mul_of r hr with ⟨w, hw, rfl⟩ | ⟨x, rfl⟩
  · rw [lengthParity_mk, ofAdd_eq_one, ZMod.natCast_eq_zero_iff_even]
    exact h.even_length w hw
  · rw [map_mul, lengthParity_of, ← ofAdd_add]
    decide

/-- **The parity homomorphism of the source presented group**: every generator goes to the
nontrivial element of `C₂`. -/
def parityHom : PresentedGroup R →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ => ofAdd 1) h.lengthParity_eq_one

@[simp]
theorem parityHom_of (x : α) : h.parityHom (PresentedGroup.of x) = ofAdd 1 :=
  PresentedGroup.toGroup.of _

/-- The parity homomorphism reads the parity of the length of a word. -/
theorem parityHom_mk_mk (L : PresentationWord α) :
    h.parityHom (PresentedGroup.mk R (FreeGroup.mk L)) = ofAdd (L.length : ZMod 2) := by
  have hcomp : h.parityHom.comp (PresentedGroup.mk R) = lengthParity α := by
    ext x
    rw [MonoidHom.comp_apply, lengthParity_of]
    exact h.parityHom_of x
  have key := DFunLike.congr_fun hcomp (FreeGroup.mk L)
  rwa [MonoidHom.comp_apply, lengthParity_mk] at key

/-- The class of a word lies in the kernel of the parity homomorphism exactly when the word has
even length. -/
theorem mk_mk_mem_ker_parityHom_iff (L : PresentationWord α) :
    PresentedGroup.mk R (FreeGroup.mk L) ∈ h.parityHom.ker ↔ Even L.length := by
  rw [MonoidHom.mem_ker, h.parityHom_mk_mk, ofAdd_eq_one, ZMod.natCast_eq_zero_iff_even]

/-! ### The map from the rewritten presentation -/

variable [DecidableEq α] (a : α) (e : {x : α // x ≠ a} ≃ β)

/-- The lift of `y ↦ a x_y` to the free group evaluates a rewritten word against the source word,
up to the transversal representatives at the two ends. Writing `t true = a` and `t false = 1`,
the rewrite of `w` from representative `t` satisfies `ρ(w) · t' = t · w`, where `t'` is the
representative reached after reading `w`. -/
theorem lift_mk_schreierWord (positive : Bool) (w : PresentationWord α) :
    FreeGroup.lift (fun y : β =>
        (PresentedGroup.of a : PresentedGroup R) * PresentedGroup.of (e.symm y).1)
        (FreeGroup.mk (schreierWord a e positive w)) *
      cond (positive ^^ decide (Odd w.length)) (PresentedGroup.of a) 1 =
    cond positive (PresentedGroup.of a) 1 * PresentedGroup.mk R (FreeGroup.mk w) := by
  induction w generalizing positive with
  | nil =>
    have hodd : decide (Odd ([] : PresentationWord α).length) = false := by
      rw [List.length_nil]
      decide
    rw [hodd, Bool.xor_false]
    cases positive <;> simp [← FreeGroup.one_eq_mk]
  | cons p w ih =>
    obtain ⟨x, s⟩ := p
    have hodd : (positive ^^ decide (Odd ((x, s) :: w).length)) =
        (!positive ^^ decide (Odd w.length)) := by
      rw [List.length_cons, Bool.not_xor, ← Bool.xor_not]
      congr 1
      simp only [Nat.odd_add_one, decide_not]
    rw [hodd, schreierWord_cons, ← FreeGroup.mul_mk, map_mul, mul_assoc, ih (!positive),
      h.mk_mk_cons, ← mul_assoc, ← mul_assoc]
    congr 1
    split_ifs with hx
    · rw [hx]
      cases positive <;> simp [← FreeGroup.one_eq_mk, h.of_mul_of]
    · cases positive
      · simp [FreeGroup.lift_mk, mul_inv_rev, h.inv_of, mul_assoc, h.of_mul_of]
      · simp [FreeGroup.lift_mk]

theorem lift_mk_schreierWord_of_mem {w : PresentationWord α} (hw : w ∈ W) (positive : Bool) :
    FreeGroup.lift (fun y : β =>
        (PresentedGroup.of a : PresentedGroup R) * PresentedGroup.of (e.symm y).1)
      (FreeGroup.mk (schreierWord a e positive w)) = 1 := by
  have key := h.lift_mk_schreierWord a e positive w
  have hodd : decide (Odd w.length) = false := by
    simpa [Nat.not_odd_iff_even] using h.even_length w hw
  rw [hodd, Bool.xor_false, h.mk_mk_eq_one w hw, mul_one] at key
  exact mul_right_cancel (key.trans (one_mul _).symm)

/-- **The homomorphism from the rewritten presented group to the source presented group**, sending
the Schreier generator indexed by `y` to `a x_y`, for `x_y` the source generator it names. It is
injective, `TauCeti.IsSchreierIndexTwoSource.toPresentedGroup_injective`, with range the kernel of
the parity homomorphism,
`TauCeti.IsSchreierIndexTwoSource.range_toPresentedGroup_eq_ker_parityHom`. -/
def toPresentedGroup : PresentedGroup (schreierRelators a e W) →* PresentedGroup R :=
  PresentedGroup.toGroup
    (f := fun y => (PresentedGroup.of a : PresentedGroup R) * PresentedGroup.of (e.symm y).1) (by
      rintro r ⟨positive, w, hw, rfl⟩
      exact h.lift_mk_schreierWord_of_mem a e hw positive)

@[simp]
theorem toPresentedGroup_of (y : β) :
    h.toPresentedGroup a e (PresentedGroup.of y) =
      PresentedGroup.of a * PresentedGroup.of (e.symm y).1 :=
  PresentedGroup.toGroup.of _

theorem toPresentedGroup_mk (z : FreeGroup β) :
    h.toPresentedGroup a e (PresentedGroup.mk _ z) =
      FreeGroup.lift (fun y : β =>
        (PresentedGroup.of a : PresentedGroup R) * PresentedGroup.of (e.symm y).1) z :=
  (rfl)

/-- The Schreier generator of `x` goes to `a x`. -/
@[simp]
theorem toPresentedGroup_schreierGenerator (x : α) :
    h.toPresentedGroup a e (schreierGenerator a e W x) =
      PresentedGroup.of a * PresentedGroup.of x := by
  unfold schreierGenerator
  split_ifs with hx
  · rw [hx, map_one, h.of_mul_of]
  · rw [toPresentedGroup_of, Equiv.symm_apply_apply]

/-- **The rewrite of an even-length word from representative `1` goes to the word itself.** -/
theorem toPresentedGroup_mk_mk_schreierWord {w : PresentationWord α} (hw : Even w.length) :
    h.toPresentedGroup a e (PresentedGroup.mk _ (FreeGroup.mk (schreierWord a e false w))) =
      PresentedGroup.mk R (FreeGroup.mk w) := by
  have key := h.lift_mk_schreierWord a e false w
  have hodd : decide (Odd w.length) = false := by simpa [Nat.not_odd_iff_even] using hw
  rw [hodd] at key
  simpa [toPresentedGroup_mk] using key

theorem parityHom_toPresentedGroup (g : PresentedGroup (schreierRelators a e W)) :
    h.parityHom (h.toPresentedGroup a e g) = 1 := by
  have hcomp : h.parityHom.comp (h.toPresentedGroup a e) = 1 := by
    ext y
    rw [MonoidHom.comp_apply, toPresentedGroup_of, map_mul, parityHom_of, parityHom_of,
      MonoidHom.one_apply]
    decide
  exact DFunLike.congr_fun hcomp g

/-- **The rewritten presented group maps onto the kernel of the parity homomorphism.** -/
theorem range_toPresentedGroup_eq_ker_parityHom :
    (h.toPresentedGroup a e).range = h.parityHom.ker := by
  ext g
  constructor
  · intro hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
    exact MonoidHom.mem_ker.mpr (h.parityHom_toPresentedGroup a e y)
  · intro hg
    obtain ⟨z, rfl⟩ := PresentedGroup.mk_surjective R g
    obtain ⟨L, rfl⟩ : ∃ L, FreeGroup.mk L = z := Quot.exists_rep z
    rw [h.mk_mk_mem_ker_parityHom_iff] at hg
    exact MonoidHom.mem_range.mpr ⟨_, h.toPresentedGroup_mk_mk_schreierWord a e hg⟩

/-! ### Injectivity, through the semidirect product `H ⋊ C₂` -/

omit h in
/-- The letter map of the source generators into `H ⋊ C₂`: `x ↦ ((a x)⁻¹, t)`, for `t` the
nontrivial element of `C₂`. -/
private def semidirectLetter (x : α) :
    PresentedGroup (schreierRelators a e W) ⋊[schreierConjAction a e W] Multiplicative (ZMod 2) :=
  ⟨(schreierGenerator a e W x)⁻¹, ofAdd 1⟩

omit h in
private theorem semidirectLetter_mul_self (x : α) :
    semidirectLetter a e (W := W) x * semidirectLetter a e (W := W) x = 1 := by
  ext1
  · simp [semidirectLetter, SemidirectProduct.mul_left, schreierConjAction_ofAdd_one]
  · simp only [semidirectLetter, SemidirectProduct.mul_right, SemidirectProduct.one_right]
    decide

omit h in
/-- Reading a source word letter by letter in `H ⋊ C₂` produces its rewrite from representative
`1` together with its length parity. -/
private theorem lift_semidirectLetter_mk (L : PresentationWord α) :
    FreeGroup.lift (semidirectLetter a e (W := W)) (FreeGroup.mk L) =
      ⟨PresentedGroup.mk _ (FreeGroup.mk (schreierWord a e false L)),
        ofAdd (L.length : ZMod 2)⟩ := by
  induction L with
  | nil =>
    ext1
    · simp [← FreeGroup.one_eq_mk]
    · simp [← FreeGroup.one_eq_mk]
  | cons p L ih =>
    obtain ⟨x, s⟩ := p
    have hletter : FreeGroup.lift (semidirectLetter a e (W := W)) (FreeGroup.mk [(x, s)]) =
        semidirectLetter a e (W := W) x := by
      cases s
      · rw [FreeGroup.lift_mk]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Bool.cond_false]
        exact inv_eq_of_mul_eq_one_right (semidirectLetter_mul_self a e (W := W) x)
      · rw [FreeGroup.lift_mk]
        simp
    conv_lhs => rw [← List.singleton_append]
    rw [← FreeGroup.mul_mk (L₁ := [(x, s)]) (L₂ := L), map_mul, hletter, ih]
    ext1
    · rw [SemidirectProduct.mul_left]
      simp only [semidirectLetter, schreierConjAction_ofAdd_one, schreierInvAut_apply]
      rw [schreierWord_cons_eq_append, ← FreeGroup.mul_mk, map_mul, mk_mk_schreierWord_singleton,
        Bool.not_false]
      congr 1
      calc
        _ = FreeGroup.lift
            (fun y => (PresentedGroup.of y : PresentedGroup (schreierRelators a e W))⁻¹)
            (FreeGroup.mk (schreierWord a e false L)) := rfl
        _ = _ := by
          simpa only [← schreierWord_not, Bool.not_false] using
            PresentedGroup.lift_inv_of_mk (schreierRelators a e W) (schreierWord a e false L)
    · simp only [semidirectLetter, SemidirectProduct.mul_right, List.length_cons, Nat.cast_succ,
        ofAdd_add]
      exact mul_comm _ _

/-- The homomorphism from the source presented group to `H ⋊ C₂`. -/
private def toSemidirectProduct :
    PresentedGroup R →*
      PresentedGroup (schreierRelators a e W) ⋊[schreierConjAction a e W] Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := semidirectLetter a e (W := W)) (by
    intro r hr
    rcases h.eq_mk_or_eq_of_mul_of r hr with ⟨w, hw, rfl⟩ | ⟨x, rfl⟩
    · rw [lift_semidirectLetter_mk]
      ext1
      · exact PresentedGroup.one_of_mem (mk_schreierWord_mem_schreierRelators a e false hw)
      · simpa [ofAdd_eq_one, ZMod.natCast_eq_zero_iff_even] using h.even_length w hw
    · simp only [map_mul, FreeGroup.lift_apply_of]
      exact semidirectLetter_mul_self a e (W := W) x)

private theorem toSemidirectProduct_comp_toPresentedGroup :
    (toSemidirectProduct h a e).comp (h.toPresentedGroup a e) = SemidirectProduct.inl := by
  refine PresentedGroup.ext fun y => ?_
  rw [MonoidHom.comp_apply, toPresentedGroup_of, map_mul]
  simp only [toSemidirectProduct, PresentedGroup.toGroup.of]
  ext1
  · simp [semidirectLetter, SemidirectProduct.mul_left, schreierConjAction_ofAdd_one]
  · simp only [semidirectLetter, SemidirectProduct.mul_right, SemidirectProduct.right_inl]
    decide

/-- **The map from the rewritten presented group is injective**: composed with the map of the
source presented group into `H ⋊ C₂` it is the inclusion of `H`. -/
theorem toPresentedGroup_injective : Function.Injective (h.toPresentedGroup a e) := by
  intro g₁ g₂ hg
  have key := congrArg (toSemidirectProduct h a e) hg
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    toSemidirectProduct_comp_toPresentedGroup h a e] at key
  exact SemidirectProduct.inl_injective key

/-! ### The identification -/

/-- **Index-two Reidemeister--Schreier rewriting.** The group presented by the rewrites of the
source words is the kernel of the parity homomorphism of the source presented group, the Schreier
generator indexed by `y` going to `a x_y`. -/
noncomputable def mulEquivKerParityHom :
    PresentedGroup (schreierRelators a e W) ≃* ↥h.parityHom.ker :=
  (MonoidHom.ofInjective (h.toPresentedGroup_injective a e)).trans
    (MulEquiv.subgroupCongr (h.range_toPresentedGroup_eq_ker_parityHom a e))

@[simp]
theorem coe_mulEquivKerParityHom_apply (g : PresentedGroup (schreierRelators a e W)) :
    (h.mulEquivKerParityHom a e g : PresentedGroup R) = h.toPresentedGroup a e g := by
  simp [mulEquivKerParityHom, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

omit [DecidableEq α] in
/-- **The kernel of the parity homomorphism is the commutator subgroup** as soon as all generators
agree in the abelianization: an even-length word is then an even power of one element of order at
most two there. -/
theorem commutator_eq_ker_parityHom
    (habel : ∀ x : α, Abelianization.of (PresentedGroup.of x : PresentedGroup R) =
      Abelianization.of (PresentedGroup.of a)) :
    commutator (PresentedGroup R) = h.parityHom.ker := by
  refine le_antisymm (Abelianization.commutator_subset_ker _) fun g hg => ?_
  obtain ⟨z, rfl⟩ := PresentedGroup.mk_surjective R g
  obtain ⟨L, rfl⟩ : ∃ L, FreeGroup.mk L = z := Quot.exists_rep z
  rw [h.mk_mk_mem_ker_parityHom_iff] at hg
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  have key : ∀ L : PresentationWord α,
      Abelianization.of (PresentedGroup.mk R (FreeGroup.mk L)) =
        Abelianization.of (PresentedGroup.of a : PresentedGroup R) ^ L.length := by
    intro L
    induction L with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons p L ih =>
      obtain ⟨x, s⟩ := p
      rw [h.mk_mk_cons, map_mul, ih, habel, List.length_cons, pow_succ']
  obtain ⟨k, hk⟩ := hg
  rw [key, hk, ← two_mul, pow_mul, ← map_pow, sq, h.of_mul_of, map_one, one_pow]

/-- **Index-two Reidemeister--Schreier rewriting onto the commutator subgroup.** When all
generators agree in the abelianization, the group presented by the rewrites of the source words is
the commutator subgroup of the source presented group. -/
noncomputable def mulEquivCommutator
    (habel : ∀ x : α, Abelianization.of (PresentedGroup.of x : PresentedGroup R) =
      Abelianization.of (PresentedGroup.of a)) :
    PresentedGroup (schreierRelators a e W) ≃* ↥(commutator (PresentedGroup R)) :=
  (h.mulEquivKerParityHom a e).trans
    (MulEquiv.subgroupCongr (h.commutator_eq_ker_parityHom a habel).symm)

@[simp]
theorem coe_mulEquivCommutator_apply
    (habel : ∀ x : α, Abelianization.of (PresentedGroup.of x : PresentedGroup R) =
      Abelianization.of (PresentedGroup.of a))
    (g : PresentedGroup (schreierRelators a e W)) :
    (h.mulEquivCommutator a e habel g : PresentedGroup R) = h.toPresentedGroup a e g := by
  simp [mulEquivCommutator, MulEquiv.subgroupCongr_apply]

end IsSchreierIndexTwoSource

/-! ## Presentation rows -/

section Row

variable [DecidableEq α] {R : Set (FreeGroup α)} {W : Set (PresentationWord α)}

/-- **A transcribed presentation row presents the commutator subgroup of a source presentation**
when its relations have the same normal closure as the Reidemeister--Schreier relators of the
source words, indexed by the row's generators through `e`, and the source generators agree in the
abelianization. This is `TauCeti.IsSchreierIndexTwoSource.mulEquivCommutator` for a row in the
auditable format, so that a transcription can be identified with the subgroup its source
describes. -/
noncomputable def GroupPresentation.mulEquivCommutator (P : GroupPresentation)
    (h : IsSchreierIndexTwoSource R W) (a : α) (e : {x : α // x ≠ a} ≃ Fin P.generatorCount)
    (habel : ∀ x : α, Abelianization.of (PresentedGroup.of x : PresentedGroup R) =
      Abelianization.of (PresentedGroup.of a))
    (hrel : Subgroup.normalClosure (Relator.relatorSet P.transcribed) =
      Subgroup.normalClosure (schreierRelators a e W)) :
    P.Group ≃* ↥(commutator (PresentedGroup R)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [P.relatorSet_eq_relatorSet_transcribed]
    exact hrel)).trans (h.mulEquivCommutator a e habel)

/-- The row generator indexed by `i` goes to `a x`, for `x` the source generator it names. -/
@[simp]
theorem GroupPresentation.coe_mulEquivCommutator_of (P : GroupPresentation)
    (h : IsSchreierIndexTwoSource R W) (a : α) (e : {x : α // x ≠ a} ≃ Fin P.generatorCount)
    (habel : ∀ x : α, Abelianization.of (PresentedGroup.of x : PresentedGroup R) =
      Abelianization.of (PresentedGroup.of a))
    (hrel : Subgroup.normalClosure (Relator.relatorSet P.transcribed) =
      Subgroup.normalClosure (schreierRelators a e W)) (i : Fin P.generatorCount) :
    (P.mulEquivCommutator h a e habel hrel (PresentedGroup.of i) : PresentedGroup R) =
      PresentedGroup.of a * PresentedGroup.of (e.symm i).1 := by
  unfold GroupPresentation.mulEquivCommutator
  -- The two group instances on the middle quotient agree only up to unfolding, so the
  -- composite is evaluated by terms rather than by rewriting.
  refine (congrArg Subtype.val (MulEquiv.trans_apply _ _ _)).trans ?_
  refine (congrArg (fun g => ((h.mulEquivCommutator a e habel g :
      ↥(commutator (PresentedGroup R))) : PresentedGroup R))
    (QuotientGroup.quotientMulEquivOfEq_mk _ (FreeGroup.of i))).trans ?_
  exact (h.coe_mulEquivCommutator_apply a e habel (PresentedGroup.of i)).trans
    (h.toPresentedGroup_of a e i)

end Row

end TauCeti
