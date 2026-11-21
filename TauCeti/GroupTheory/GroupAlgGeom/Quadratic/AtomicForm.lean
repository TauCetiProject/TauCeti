/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardForm
import Mathlib.Algebra.Group.Submonoid.BigOperators
import TauCeti.Data.List.OfFn

/-!
# Quadratic words in atomic form

A word over `G` is in atomic form when it is a product
`∏ [xᵢ, yᵢ] · ∏ sₖ² · ∏ zⱼ⁻¹ cⱼ zⱼ · d` of commutators, squares and conjugates of coefficients,
followed by a coefficient `d`; it is quadratic when its variables are pairwise distinct, which is
the separate hypothesis `P.vars.Nodup` on the data `P : AtomicForm G X` of such a word. Unlike the
standard quadratic words of [IFT], Definition 3, commutators and squares may both occur and the
coefficients `cⱼ`, `d` may be trivial. It is the intermediate form between a strictly quadratic
word and its standard form ([IFT], Lemma 1).

An elementary automorphism of `G[X]` and a conjugation bring a word in atomic form in pairwise
distinct variables to a coefficient or to a standard quadratic word: conjugates of the trivial
coefficient are deleted, a commutator next to a square becomes three squares, and if `d = 1` the
last conjugate `z⁻¹ c z` is conjugated to the new coefficient `d = c`, its variable `z`
disappearing.

## Main definitions

* `Quadratic.AtomicForm G X`: the data of a word in atomic form, with `AtomicForm.toWord` and the
  list `AtomicForm.vars` of its variables.

## Main results

* `AtomicForm.exists_mem_elementaryAut_apply_toWord_eq_conj`: conjugation of a word in atomic form
  without constant by a word in other variables is induced by an elementary automorphism.
* `AtomicForm.exists_mem_elementaryAut_apply_toWord_eq_squares`: in the presence of a square, an
  elementary automorphism maps the whole word to the word obtained by replacing each commutator
  factor with two square factors.
* `AtomicForm.exists_mem_elementaryAut_conj_toWord_concat`: the last conjugate becomes the constant.
* `AtomicForm.exists_standard_toWord_eq`: the atomic forms that are standard quadratic words.
* `AtomicForm.exists_standardForm`: every word in atomic form is brought to a coefficient or to a
  standard quadratic word.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 3, 4 and Lemma 1.
* [GaXu] J. Gallier, D. Xu, *A guide to the classification theorem for compact surfaces*, Springer
  (2013), Chapter 6, Lemma 6.1, Steps 4 and 5.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G X : Type*}

/-- The data of a quadratic word in atomic form `∏ [xᵢ, yᵢ] · ∏ sₖ² · ∏ zⱼ⁻¹ cⱼ zⱼ · d`: the pairs
`(xᵢ, yᵢ)` of the commutators, the variables `sₖ` of the squares, the pairs `(zⱼ, cⱼ)` of the
conjugates of coefficients, and the constant `d`. -/
structure AtomicForm (G X : Type*) where
  /-- The pairs `(xᵢ, yᵢ)` of variables of the commutators `[xᵢ, yᵢ]`. -/
  comms : List (X × X)
  /-- The variables `sₖ` of the squares `sₖ²`. -/
  squares : List X
  /-- The pairs `(zⱼ, cⱼ)` of the conjugates `zⱼ⁻¹ cⱼ zⱼ`. -/
  conjs : List (X × G)
  /-- The constant `d`. -/
  const : G

namespace AtomicForm

/-- The variables of a word in atomic form, in order of occurrence. -/
def vars (P : AtomicForm G X) : List X :=
  P.comms.flatMap (fun p => [p.1, p.2]) ++ P.squares ++ P.conjs.map Prod.fst

theorem vars_def (P : AtomicForm G X) :
    P.vars = P.comms.flatMap (fun p => [p.1, p.2]) ++ P.squares ++ P.conjs.map Prod.fst := (rfl)

private theorem vars_perm (P : AtomicForm G X) : P.vars.Perm
    (P.comms.map Prod.fst ++ P.comms.map Prod.snd ++ P.squares ++ P.conjs.map Prod.fst) := by
  -- the first variables `xᵢ` of the commutators, followed by their second variables `yᵢ`
  simpa only [vars_def, ← List.map_eq_flatMap, List.append_assoc] using
    (List.map_append_flatMap_perm P.comms Prod.fst fun p => [p.2]).symm.append_right
      (P.squares ++ P.conjs.map Prod.fst)

section DropTrivial

variable [One G]

open scoped Classical in
/-- Delete the conjugates `z⁻¹ c z` with `c = 1` from the data of a word in atomic form. -/
noncomputable def dropTrivial (P : AtomicForm G X) : AtomicForm G X :=
  { P with conjs := P.conjs.filter fun p => p.2 ≠ 1 }

@[simp]
theorem comms_dropTrivial (P : AtomicForm G X) : P.dropTrivial.comms = P.comms := (rfl)

@[simp]
theorem squares_dropTrivial (P : AtomicForm G X) : P.dropTrivial.squares = P.squares := (rfl)

@[simp]
theorem const_dropTrivial (P : AtomicForm G X) : P.dropTrivial.const = P.const := (rfl)

@[simp]
theorem conjs_dropTrivial [DecidableEq G] (P : AtomicForm G X) :
    P.dropTrivial.conjs = P.conjs.filter fun p => p.2 ≠ 1 := by
  simp only [dropTrivial]
  congr!

@[simp]
theorem mem_conjs_dropTrivial {P : AtomicForm G X} {p : X × G} :
    p ∈ P.dropTrivial.conjs ↔ p ∈ P.conjs ∧ p.2 ≠ 1 := by
  simp [dropTrivial]

theorem vars_dropTrivial_sublist (P : AtomicForm G X) : P.dropTrivial.vars.Sublist P.vars :=
  (List.filter_sublist.map _).append_left _

end DropTrivial

end AtomicForm

section Avoiding

variable [Group G] [DecidableEq X]

theorem commWord_mem_avoiding {p : X × X} {v : X}
    (h₁ : p.1 ≠ v) (h₂ : p.2 ≠ v) : commWord (G := G) p ∈ GX.avoiding v := by
  have ha : (inr (FreeGroup.of p.1) : GX G X) ∈ GX.avoiding v := GX.inr_of_mem_avoiding h₁
  have hb : (inr (FreeGroup.of p.2) : GX G X) ∈ GX.avoiding v := GX.inr_of_mem_avoiding h₂
  rw [commWord_def, commutatorElement_def, inv_inv, inv_inv]
  exact mul_mem (mul_mem (mul_mem (inv_mem ha) (inv_mem hb)) ha) hb

theorem sqWord_mem_avoiding {x v : X} (hx : x ≠ v) :
    sqWord (G := G) x ∈ GX.avoiding v := by
  rw [sqWord_def]
  exact pow_mem (GX.inr_of_mem_avoiding hx) 2

theorem conjWord_mem_avoiding {p : X × G} {v : X} (hp : p.1 ≠ v) :
    conjWord p ∈ GX.avoiding v := by
  rw [conjWord_def]
  exact mul_mem (mul_mem (inv_mem (GX.inr_of_mem_avoiding hp)) (GX.inl_mem_avoiding _ _))
    (GX.inr_of_mem_avoiding hp)

end Avoiding

namespace AtomicForm

variable [Group G]

/-- The product `∏ [xᵢ, yᵢ]` of the commutator atoms of `P`. -/
def commsProd (P : AtomicForm G X) : GX G X :=
  (P.comms.map commWord).prod

theorem commsProd_def (P : AtomicForm G X) : P.commsProd = (P.comms.map commWord).prod := (rfl)

@[simp]
theorem commsProd_nil (S : List X) (Z : List (X × G)) (d : G) :
    (⟨[], S, Z, d⟩ : AtomicForm G X).commsProd = 1 := by
  simp [commsProd_def]

@[simp]
theorem commsProd_cons (p : X × X) (C : List (X × X)) (S : List X) (Z : List (X × G)) (d : G) :
    (⟨p :: C, S, Z, d⟩ : AtomicForm G X).commsProd =
      commWord p * (⟨C, S, Z, d⟩ : AtomicForm G X).commsProd := by
  simp [commsProd_def]

/-- The product `∏ sₖ²` of the square atoms of `P`. -/
def squaresProd (P : AtomicForm G X) : GX G X :=
  (P.squares.map sqWord).prod

theorem squaresProd_def (P : AtomicForm G X) : P.squaresProd = (P.squares.map sqWord).prod := (rfl)

@[simp]
theorem squaresProd_nil (C : List (X × X)) (Z : List (X × G)) (d : G) :
    (⟨C, [], Z, d⟩ : AtomicForm G X).squaresProd = 1 := by
  simp [squaresProd_def]

@[simp]
theorem squaresProd_cons (s : X) (C : List (X × X)) (S : List X) (Z : List (X × G)) (d : G) :
    (⟨C, s :: S, Z, d⟩ : AtomicForm G X).squaresProd =
      sqWord s * (⟨C, S, Z, d⟩ : AtomicForm G X).squaresProd := by
  simp [squaresProd_def]

/-- The product `∏ zⱼ⁻¹ cⱼ zⱼ` of the conjugate atoms of `P`. -/
def conjsProd (P : AtomicForm G X) : GX G X :=
  (P.conjs.map conjWord).prod

theorem conjsProd_def (P : AtomicForm G X) : P.conjsProd = (P.conjs.map conjWord).prod := (rfl)

@[simp]
theorem conjsProd_nil (C : List (X × X)) (S : List X) (d : G) :
    (⟨C, S, [], d⟩ : AtomicForm G X).conjsProd = 1 := by
  simp [conjsProd_def]

@[simp]
theorem conjsProd_cons (p : X × G) (C : List (X × X)) (S : List X) (Z : List (X × G)) (d : G) :
    (⟨C, S, p :: Z, d⟩ : AtomicForm G X).conjsProd =
      conjWord p * (⟨C, S, Z, d⟩ : AtomicForm G X).conjsProd := by
  simp [conjsProd_def]

/-- The word `∏ [xᵢ, yᵢ] · ∏ sₖ² · ∏ zⱼ⁻¹ cⱼ zⱼ · d` of `G[X]`, with `[x, y] = x⁻¹ y⁻¹ x y`. -/
def toWord (P : AtomicForm G X) : GX G X :=
  P.commsProd * P.squaresProd * P.conjsProd * inl P.const

theorem toWord_def (P : AtomicForm G X) :
    P.toWord = P.commsProd * P.squaresProd * P.conjsProd * inl P.const := (rfl)

@[simp]
theorem toWord_dropTrivial (P : AtomicForm G X) : P.dropTrivial.toWord = P.toWord := by
  obtain ⟨C, S, Z, d⟩ := P
  simp only [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, dropTrivial]
  congr 2
  -- the deleted conjugates `z⁻¹ * inl 1 * z` are trivial
  induction Z with
  | nil => rfl
  | cons p Z ih =>
    by_cases hp : p.2 = 1
    · rw [List.filter_cons_of_neg (by simpa using hp), ih]
      simp [conjWord_def, hp]
    · rw [List.filter_cons_of_pos (by simpa using hp)]
      simp only [List.map_cons, List.prod_cons, ih]

/-- A variable outside the commutator pairs of `P` does not occur in the commutator product of
`P`. -/
theorem commsProd_mem_avoiding [DecidableEq X] {P : AtomicForm G X} {x : X}
    (hx : x ∉ P.comms.flatMap fun p => [p.1, p.2]) :
    P.commsProd ∈ GX.avoiding x := by
  refine list_prod_mem fun _ hr => ?_
  rcases List.mem_map.1 hr with ⟨p, hp, rfl⟩
  exact commWord_mem_avoiding
    (by rintro rfl; exact hx (List.mem_flatMap.2 ⟨p, hp, by simp⟩))
    (by rintro rfl; exact hx (List.mem_flatMap.2 ⟨p, hp, by simp⟩))

/-- A variable outside `P.squares` does not occur in the square product of `P`. -/
theorem squaresProd_mem_avoiding [DecidableEq X] {P : AtomicForm G X} {x : X}
    (hx : x ∉ P.squares) :
    P.squaresProd ∈ GX.avoiding x := by
  refine list_prod_mem fun _ hr => ?_
  rcases List.mem_map.1 hr with ⟨s, hs, rfl⟩
  exact sqWord_mem_avoiding (by rintro rfl; exact hx hs)

/-- A variable outside `P.conjs.map Prod.fst` does not occur in the conjugate product of `P`. -/
theorem conjsProd_mem_avoiding [DecidableEq X] {P : AtomicForm G X} {x : X}
    (hx : x ∉ P.conjs.map Prod.fst) :
    P.conjsProd ∈ GX.avoiding x := by
  refine list_prod_mem fun _ hr => ?_
  rcases List.mem_map.1 hr with ⟨p, hp, rfl⟩
  exact conjWord_mem_avoiding (by rintro rfl; exact hx (List.mem_map.2 ⟨p, hp, rfl⟩))

/-- A variable outside `P.vars` is avoided by each of the three atom products `P.commsProd`,
`P.squaresProd`, and `P.conjsProd`. -/
theorem commsProd_squaresProd_conjsProd_mem_avoiding [DecidableEq X] {P : AtomicForm G X} {x : X}
    (hx : x ∉ P.vars) :
    P.commsProd ∈ GX.avoiding x ∧ P.squaresProd ∈ GX.avoiding x ∧ P.conjsProd ∈ GX.avoiding x := by
  simp only [vars_def, List.mem_append, not_or] at hx
  exact ⟨commsProd_mem_avoiding hx.1.1, squaresProd_mem_avoiding hx.1.2,
    conjsProd_mem_avoiding hx.2⟩

/-- A variable which is not a variable of a word in atomic form does not occur in it. -/
theorem toWord_mem_avoiding [DecidableEq X] {P : AtomicForm G X} {x : X} (hx : x ∉ P.vars) :
    P.toWord ∈ GX.avoiding x := by
  obtain ⟨hC, hSq, hCj⟩ := P.commsProd_squaresProd_conjsProd_mem_avoiding hx
  exact mul_mem (mul_mem (mul_mem hC hSq) hCj) (GX.inl_mem_avoiding _ _)

private theorem apply_toWord_eq_conj (P : AtomicForm G X) (hc : P.const = 1)
    {f : MulAut (GX G X)} {t : GX G X} (hf : ∀ g, f (inl g) = inl g)
    (hA : ∀ y ∈ P.comms.flatMap (fun p => [p.1, p.2]) ++ P.squares,
      f (inr (FreeGroup.of y)) = MulAut.conj t⁻¹ (inr (FreeGroup.of y)))
    (hZ : ∀ z ∈ P.conjs.map Prod.fst, f (inr (FreeGroup.of z)) = inr (FreeGroup.of z) * t) :
    f P.toWord = t⁻¹ * P.toWord * t := by
  -- `f` conjugates every atom by `t`
  suffices f P.toWord = MulAut.conj t⁻¹ P.toWord by simpa using this
  rw [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, hc]
  simp only [map_mul, map_list_prod, List.map_map]
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) (congr_arg₂ (· * ·)
    (congr_arg _ (List.map_congr_left fun p hp => ?_)) (congr_arg _ (List.map_congr_left
      fun p hp => ?_))) (congr_arg _ (List.map_congr_left fun p hp => ?_))) (by simp)
  · have h₁ := hA p.1 (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩))
    have h₂ := hA p.2 (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩))
    simp only [Function.comp_apply, commWord_def, map_commutatorElement, map_inv, h₁, h₂]
  · simp only [Function.comp_apply, sqWord_def, map_pow, hA p (List.mem_append_right _ hp)]
  · simp only [Function.comp_apply, conjWord_def, map_mul, map_inv, hZ p.1 (List.mem_map_of_mem hp),
      hf]
    simp [mul_assoc]

/-- Conjugation of a word in atomic form without constant by a word `t` in other variables is
induced by an elementary automorphism which fixes every word in other variables, provided that no
variable of a conjugate `z⁻¹ c z` is also a variable of a commutator or of a square. -/
theorem exists_mem_elementaryAut_apply_toWord_eq_conj [DecidableEq X] (P : AtomicForm G X)
    (hP : (P.comms.flatMap (fun p => [p.1, p.2]) ++ P.squares).Disjoint (P.conjs.map Prod.fst))
    (hc : P.const = 1) (t : GX G X) (ht : ∀ y ∈ P.vars, t ∈ GX.avoiding y) :
    ∃ f ∈ GX.elementaryAut G X, f P.toWord = t⁻¹ * P.toWord * t ∧
      ∀ w : GX G X, (∀ y ∈ P.vars, w ∈ GX.avoiding y) → f w = w := by
  -- `y ↦ t⁻¹ y t` on the variables of the commutators and squares, `z ↦ z t` on those of the
  -- conjugates
  obtain ⟨f, hf, hfv, hfw⟩ := GX.exists_mem_elementaryAut_forall_apply_inr_of P.vars.toFinset
    (fun y => if y ∈ P.conjs.map Prod.fst then 1 else t⁻¹) (fun _ => t)
    (fun y _ y' hy' => by
      split_ifs
      · exact one_mem _
      · exact inv_mem (ht y' (List.mem_toFinset.1 hy')))
    (fun _ _ y' hy' => ht y' (List.mem_toFinset.1 hy'))
  refine ⟨f, hf, P.apply_toWord_eq_conj hc (GX.apply_inl_of_mem_elementaryAut hf)
    (fun y hy => ?_) (fun z hz => ?_), fun w hw => hfw w fun y hy => hw y (List.mem_toFinset.1 hy)⟩
  · have hyZ : y ∉ P.conjs.map Prod.fst := fun h => hP hy h
    simp [hfv y (List.mem_toFinset.2 (List.mem_append_left _ hy)), hyZ]
  · simp [hfv z (List.mem_toFinset.2 (List.mem_append_right _ hz)), hz]

private theorem exists_mem_elementaryAut_apply_toWord_append_singleton [DecidableEq X]
    (C : List (X × X)) (x y s : X) (S : List X) (Z : List (X × G)) (d : G)
    (h : (⟨C ++ [(x, y)], s :: S, Z, d⟩ : AtomicForm G X).vars.Nodup) :
    ∃ f ∈ GX.elementaryAut G X,
      f (⟨C ++ [(x, y)], s :: S, Z, d⟩ : AtomicForm G X).toWord =
        (⟨C, x :: y :: s :: S, Z, d⟩ : AtomicForm G X).toWord ∧
      ∀ a, (∀ v ∈ (⟨C ++ [(x, y)], s :: S, Z, d⟩ : AtomicForm G X).vars, a ∈ GX.avoiding v) →
        f a = a := by
  simp only [vars_def, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.nodup_middle, List.nodup_cons,
    List.mem_append, List.mem_cons, not_or] at h
  obtain ⟨⟨hxC, hxy, hxs, hxS, hxZ⟩, ⟨hyC, hys, hyS, hyZ⟩, ⟨hsC, hsS, hsZ⟩, -⟩ := h
  obtain ⟨f, hf, hfe, hfw⟩ :=
    GX.exists_mem_elementaryAut_apply_commutator_mul_sq (G := G) hxy hxs hys
  refine ⟨f, hf, ?_, fun a ha => hfw a ⟨⟨ha x (by simp [vars_def]), ha y (by simp [vars_def])⟩,
    ha s (by simp [vars_def])⟩⟩
  -- the rule fixes the commutators before `[x, y]` and the atoms after `s²`
  have hav : ∀ Q : AtomicForm G X, x ∉ Q.vars → y ∉ Q.vars → s ∉ Q.vars →
      Q.toWord ∈ GX.avoiding x ⊓ GX.avoiding y ⊓ GX.avoiding s := fun Q hx hy hs =>
    ⟨⟨toWord_mem_avoiding hx, toWord_mem_avoiding hy⟩, toWord_mem_avoiding hs⟩
  have e₁ : (⟨C ++ [(x, y)], s :: S, Z, d⟩ : AtomicForm G X).toWord =
      (⟨C, [], [], 1⟩ : AtomicForm G X).toWord * (commWord (x, y) * sqWord s) *
      (⟨[], S, Z, d⟩ : AtomicForm G X).toWord := by
    simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, mul_assoc]
  have e₂ : (⟨C, x :: y :: s :: S, Z, d⟩ : AtomicForm G X).toWord =
      (⟨C, [], [], 1⟩ : AtomicForm G X).toWord * (sqWord x * sqWord y * sqWord s) *
      (⟨[], S, Z, d⟩ : AtomicForm G X).toWord := by
    simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, mul_assoc]
  rw [e₁, e₂, map_mul, map_mul, commWord_def, sqWord_def, sqWord_def, sqWord_def, hfe,
    hfw _ (hav _ (by simpa [vars_def] using hxC) (by simpa [vars_def] using hyC)
      (by simpa [vars_def] using hsC)),
    hfw _ (hav _ (by simp [vars_def, hxS, hxZ]) (by simp [vars_def, hyS, hyZ])
      (by simp [vars_def, hsS, hsZ]))]

/-- In the presence of a square, an elementary automorphism fixing every word avoiding `P.vars`
maps a word `P` in atomic form in pairwise distinct variables to the word obtained by replacing each
commutator factor `[x, y]` with the two square factors `x² y²`. -/
theorem exists_mem_elementaryAut_apply_toWord_eq_squares [DecidableEq X] (P : AtomicForm G X)
    (hP : P.vars.Nodup) (hs : P.squares ≠ []) :
    ∃ f ∈ GX.elementaryAut G X,
      f P.toWord =
        (⟨[], P.comms.flatMap (fun p => [p.1, p.2]) ++ P.squares, P.conjs, P.const⟩ :
          AtomicForm G X).toWord ∧
      ∀ a, (∀ v ∈ P.vars, a ∈ GX.avoiding v) → f a = a := by
  obtain ⟨C, S, Z, d⟩ := P
  dsimp only at hs ⊢
  induction C using List.reverseRecOn generalizing S with
  | nil => exact ⟨1, one_mem _, by simp, fun _ _ => rfl⟩
  | append_singleton C p ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨s, S, rfl⟩ := List.exists_cons_of_ne_nil hs
    obtain ⟨f, hf, hfe, hffix⟩ :=
      exists_mem_elementaryAut_apply_toWord_append_singleton C x y s S Z d hP
    obtain ⟨g, hg, hge, hgfix⟩ :=
      ih (x :: y :: s :: S) (by simpa [vars_def] using hP) (List.cons_ne_nil _ _)
    refine ⟨g * f, mul_mem hg hf, ?_, fun a ha => ?_⟩
    · rw [MulAut.mul_apply, hfe, hge]
      simp
    · rw [MulAut.mul_apply, hffix a ha, hgfix a fun v hv => ha v (by simpa [vars_def] using hv)]

/-- A word `W` in atomic form in pairwise distinct variables, without constant, whose last atom is
the conjugate `z⁻¹ c z`: for some elementary automorphism `f` fixing every word avoiding the
variables of `W`, the conjugate `z * f W * z⁻¹` is the word in which this atom is replaced by the
constant `c`. -/
theorem exists_mem_elementaryAut_conj_toWord_concat [DecidableEq X]
    (C : List (X × X)) (S : List X) (Z : List (X × G)) (z : X) (c : G)
    (h : (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).vars.Nodup) :
    ∃ f ∈ GX.elementaryAut G X,
      inr (FreeGroup.of z) * f (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).toWord *
        (inr (FreeGroup.of z))⁻¹ = (⟨C, S, Z, c⟩ : AtomicForm G X).toWord ∧
      ∀ a, (∀ v ∈ (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).vars, a ∈ GX.avoiding v) →
        f a = a := by
  have hsub : (⟨C, S, Z, 1⟩ : AtomicForm G X).vars.Sublist
      (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).vars := by
    simp only [vars_def, List.map_append]
    exact (List.sublist_append_left _ _).append_left _
  replace h : ((⟨C, S, Z, 1⟩ : AtomicForm G X).vars ++ [z]).Nodup := by simpa [vars_def] using h
  have hzy : ∀ y ∈ (⟨C, S, Z, 1⟩ : AtomicForm G X).vars,
      (inr (FreeGroup.of z) : GX G X) ∈ GX.avoiding y := fun y hy =>
    GX.inr_of_mem_avoiding fun hzy => List.disjoint_of_nodup_append h (hzy ▸ hy) (.head _)
  -- conjugating the other atoms by `z` is induced by an automorphism which fixes `z⁻¹ c z`
  obtain ⟨f, hf, hfP, hfw⟩ := exists_mem_elementaryAut_apply_toWord_eq_conj ⟨C, S, Z, 1⟩
    (List.disjoint_of_nodup_append h.of_append_left) rfl _ hzy
  have e : (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).toWord =
      (⟨C, S, Z, 1⟩ : AtomicForm G X).toWord * conjWord (z, c) := by
    simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, mul_assoc]
  refine ⟨f, hf, ?_, fun a ha => hfw a fun v hv => ha v (hsub.subset hv)⟩
  rw [e, map_mul, hfP, hfw _ fun y hy => conjWord_mem_avoiding (p := (z, c))
    (fun (hzy' : z = y) => List.disjoint_of_nodup_append h (hzy' ▸ hy) (.head _))]
  simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, conjWord_def, mul_assoc]

/-! ### Atomic forms that are standard quadratic words -/

private theorem exists_standard_orientable {C : List (X × X)}
    (hP : (⟨C, [], [], 1⟩ : AtomicForm G X).vars.Nodup)
    (hne : (⟨C, [], [], 1⟩ : AtomicForm G X).vars ≠ []) :
    ∃ S : Standard G X, S.toWord = (⟨C, [], [], 1⟩ : AtomicForm G X).toWord ∧
      S.vars = {x | x ∈ (⟨C, [], [], 1⟩ : AtomicForm G X).vars} := by
  have hC := vars_perm (⟨C, [], [], 1⟩ : AtomicForm G X)
  simp only [vars_def, List.map_nil, List.append_nil] at hC hP hne ⊢
  refine ⟨.orientable C.length (List.length_pos_of_ne_nil (by rintro rfl; simp at hne))
    (fun i : Fin C.length => C[(i : ℕ)].1) (fun i : Fin C.length => C[(i : ℕ)].2)
    (List.nodup_ofFn_append_ofFn.1 (by simpa using hC.nodup_iff.1 hP)), ?_, ?_⟩
  · simp [Standard.toWord_def, toWord_def, commsProd_def, squaresProd_def, conjsProd_def,
      funext fun p => commWord_def (G := G) p, List.ofFn_getElem_eq_map C
        fun p => ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2))⁻¹⁆]
  · ext v
    simp only [Standard.vars_orientable, Set.Sum.elim_range, Set.mem_union, ← List.mem_ofFn',
      List.ofFn_getElem_eq_map, Set.mem_ofPred_eq, hC.mem_iff, List.mem_append]

private theorem exists_standard_orientableCoeff {C : List (X × X)} {Z : List (X × G)} {d : G}
    (hP : (⟨C, [], Z, d⟩ : AtomicForm G X).vars.Nodup)
    (hne : (⟨C, [], Z, d⟩ : AtomicForm G X).vars ≠ []) (hc : ∀ p ∈ Z, p.2 ≠ 1) (hd : d ≠ 1) :
    ∃ S : Standard G X, S.toWord = (⟨C, [], Z, d⟩ : AtomicForm G X).toWord ∧
      S.vars = {x | x ∈ (⟨C, [], Z, d⟩ : AtomicForm G X).vars} := by
  have hC := vars_perm (⟨C, [], Z, d⟩ : AtomicForm G X)
  simp only [vars_def, List.append_nil] at hC hP hne ⊢
  have hnm : 0 < C.length + Z.length := by
    rcases C with _ | _ <;> rcases Z with _ | _ <;> simp_all
  refine ⟨.orientableCoeff C.length Z.length hnm (fun i : Fin C.length => C[(i : ℕ)].1)
    (fun i : Fin C.length => C[(i : ℕ)].2) (fun j : Fin Z.length => Z[(j : ℕ)].1)
    (List.nodup_ofFn_append_ofFn_append_ofFn.1 (by simpa using hC.nodup_iff.1 hP))
    (fun j : Fin Z.length => Z[(j : ℕ)].2) (fun j => hc _ (List.getElem_mem _)) d hd, ?_, ?_⟩
  · simp [Standard.toWord_def, toWord_def, commsProd_def, squaresProd_def, conjsProd_def,
      funext fun p => commWord_def (G := G) p, funext fun p => conjWord_def (G := G) p, mul_assoc,
      List.ofFn_getElem_eq_map C
        fun p => ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2))⁻¹⁆,
      List.ofFn_getElem_eq_map Z
        fun p => (inr (FreeGroup.of p.1) : GX G X)⁻¹ * (inl p.2 * inr (FreeGroup.of p.1))]
  · ext v
    simp only [Standard.vars_orientableCoeff, Set.Sum.elim_range, Set.mem_union,
      ← List.mem_ofFn', List.ofFn_getElem_eq_map, Set.mem_ofPred_eq, hC.mem_iff, List.mem_append]

private theorem exists_standard_nonorientable {S : List X}
    (hP : (⟨[], S, [], 1⟩ : AtomicForm G X).vars.Nodup)
    (hne : (⟨[], S, [], 1⟩ : AtomicForm G X).vars ≠ []) :
    ∃ T : Standard G X, T.toWord = (⟨[], S, [], 1⟩ : AtomicForm G X).toWord ∧
      T.vars = {x | x ∈ (⟨[], S, [], 1⟩ : AtomicForm G X).vars} := by
  simp only [vars_def, List.flatMap_nil, List.nil_append, List.map_nil, List.append_nil] at hP hne ⊢
  refine ⟨.nonorientable S.length (List.length_pos_of_ne_nil hne)
    (fun i : Fin S.length => S[(i : ℕ)]) (List.nodup_ofFn.1 (by simpa using hP)), ?_, ?_⟩
  · simp [Standard.toWord_def, toWord_def, commsProd_def, squaresProd_def, conjsProd_def,
      funext fun x => sqWord_def (G := G) x,
      List.ofFn_getElem_eq_map S fun x => (inr (FreeGroup.of x) : GX G X) ^ 2]
  · ext v
    simp only [Standard.vars_nonorientable, ← List.mem_ofFn', List.ofFn_getElem, Set.mem_ofPred_eq]

private theorem exists_standard_nonorientableCoeff {S : List X} {Z : List (X × G)} {d : G}
    (hP : (⟨[], S, Z, d⟩ : AtomicForm G X).vars.Nodup) (hS : S ≠ []) (hc : ∀ p ∈ Z, p.2 ≠ 1)
    (hd : d ≠ 1) :
    ∃ T : Standard G X, T.toWord = (⟨[], S, Z, d⟩ : AtomicForm G X).toWord ∧
      T.vars = {x | x ∈ (⟨[], S, Z, d⟩ : AtomicForm G X).vars} := by
  simp only [vars_def, List.flatMap_nil, List.nil_append] at hP ⊢
  refine ⟨.nonorientableCoeff S.length Z.length (List.length_pos_of_ne_nil hS)
    (fun i : Fin S.length => S[(i : ℕ)]) (fun j : Fin Z.length => Z[(j : ℕ)].1)
    (List.nodup_ofFn_append_ofFn.1 (by simpa using hP)) (fun j : Fin Z.length => Z[(j : ℕ)].2)
    (fun j => hc _ (List.getElem_mem _)) d hd, ?_, ?_⟩
  · simp [Standard.toWord_def, toWord_def, commsProd_def, squaresProd_def, conjsProd_def,
      funext fun x => sqWord_def (G := G) x, funext fun p => conjWord_def (G := G) p, mul_assoc,
      List.ofFn_getElem_eq_map S fun x => (inr (FreeGroup.of x) : GX G X) ^ 2,
      List.ofFn_getElem_eq_map Z
        fun p => (inr (FreeGroup.of p.1) : GX G X)⁻¹ * (inl p.2 * inr (FreeGroup.of p.1))]
  · ext v
    simp only [Standard.vars_nonorientableCoeff, Set.Sum.elim_range, Set.mem_union,
      ← List.mem_ofFn', List.ofFn_getElem, List.ofFn_getElem_eq_map, Set.mem_ofPred_eq,
      List.mem_append]

/-- A word in atomic form in pairwise distinct variables, with at least one atom, without
commutators or without squares, whose conjugated coefficients are nontrivial and whose constant is
nontrivial unless there is no conjugate, is a standard quadratic word in the same variables. -/
theorem exists_standard_toWord_eq (P : AtomicForm G X) (hP : P.vars.Nodup)
    (hcs : P.comms = [] ∨ P.squares = []) (hc : ∀ p ∈ P.conjs, p.2 ≠ 1)
    (hd : P.const = 1 → P.conjs = []) (hne : P.vars ≠ []) :
    ∃ S : Standard G X, S.toWord = P.toWord ∧ S.vars = {x | x ∈ P.vars} := by
  obtain ⟨C, S, Z, d⟩ := P
  dsimp only at hcs hc hd
  rcases eq_or_ne S [] with rfl | hS
  · -- no squares: types (1) and (2)
    rcases eq_or_ne d 1 with rfl | hd'
    · obtain rfl := hd rfl
      exact exists_standard_orientable hP hne
    · exact exists_standard_orientableCoeff hP hne hc hd'
  · -- squares and no commutators: types (3) and (4)
    obtain rfl := hcs.resolve_right hS
    rcases eq_or_ne d 1 with rfl | hd'
    · obtain rfl := hd rfl
      exact exists_standard_nonorientable hP hne
    · exact exists_standard_nonorientableCoeff hP hS hc hd'

/-! ### Normalisation of a word in atomic form -/

private theorem coeff_or_standard (Q : AtomicForm G X) (hQ : Q.vars.Nodup)
    (hcs : Q.comms = [] ∨ Q.squares = []) (hc : ∀ p ∈ Q.conjs, p.2 ≠ 1)
    (hd : Q.const = 1 → Q.conjs = []) : (∃ c : G, Q.toWord = inl c) ∨
      ∃ S : Standard G X, Q.toWord = S.toWord ∧ S.vars ⊆ {x | x ∈ Q.vars} := by
  rcases eq_or_ne Q.vars [] with h | h
  · left
    obtain ⟨_ | ⟨p, C⟩, S, Z, d⟩ := Q
    · obtain ⟨rfl, rfl⟩ : S = [] ∧ Z = [] := by simpa [vars_def] using h
      exact ⟨d, by simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def]⟩
    · simp [vars_def] at h
  · obtain ⟨S, hS, hSv⟩ := exists_standard_toWord_eq Q hQ hcs hc hd h
    exact .inr ⟨S, hS.symm, hSv.le⟩

private theorem exists_standardForm_of_ne_one [DecidableEq X] (P : AtomicForm G X)
    (hP : P.vars.Nodup) (hcs : P.comms = [] ∨ P.squares = []) (hc : ∀ p ∈ P.conjs, p.2 ≠ 1) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∀ a, (∀ v ∈ P.vars, a ∈ GX.avoiding v) → f a = a) ∧
      ((∃ c : G, u * f P.toWord * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f P.toWord * u⁻¹ = S.toWord ∧ S.vars ⊆ {x | x ∈ P.vars}) := by
  obtain ⟨C, S, Z, d⟩ := P
  by_cases h : d = 1 ∧ Z ≠ []
  · -- no constant and a last conjugate `z⁻¹ c z`: conjugating by `z` makes `c` the constant
    obtain ⟨rfl, hZ⟩ := h
    obtain ⟨Z, ⟨z, c⟩, rfl⟩ : ∃ Z' p, Z = Z' ++ [p] :=
      ⟨_, _, (List.dropLast_append_getLast hZ).symm⟩
    obtain ⟨f, hf, hfe, hffix⟩ := exists_mem_elementaryAut_conj_toWord_concat C S Z z c hP
    have hQ : (⟨C, S, Z, c⟩ : AtomicForm G X).vars.Sublist
        (⟨C, S, Z ++ [(z, c)], 1⟩ : AtomicForm G X).vars := by
      rw [vars_def, vars_def, List.map_append]
      exact (List.sublist_append_left _ _).append_left _
    refine ⟨f, hf, inr (FreeGroup.of z), hffix, ?_⟩
    rw [hfe]
    exact (coeff_or_standard _ (hP.sublist hQ) hcs (fun p hp => hc p (by simp [hp]))
      fun h => absurd h (hc (z, c) (by simp))).imp_right
        fun ⟨T, hT, hTv⟩ => ⟨T, hT, hTv.trans fun x hx => hQ.subset hx⟩
  · -- otherwise the word is already a coefficient or a standard word
    refine ⟨1, one_mem _, 1, fun _ _ => rfl, ?_⟩
    simpa using coeff_or_standard _ hP hcs hc fun hd => not_not.1 (not_and.1 h hd)

private theorem exists_comms_eq_nil_or_squares_eq_nil [DecidableEq X] (P : AtomicForm G X)
    (hP : P.vars.Nodup) :
    ∃ f ∈ GX.elementaryAut G X, ∃ Q : AtomicForm G X, f P.toWord = Q.toWord ∧ Q.vars = P.vars ∧
      Q.conjs = P.conjs ∧ (Q.comms = [] ∨ Q.squares = []) ∧
      ∀ a, (∀ v ∈ P.vars, a ∈ GX.avoiding v) → f a = a := by
  rcases eq_or_ne P.squares [] with hs | hs
  · exact ⟨1, one_mem _, P, rfl, rfl, rfl, .inr hs, fun _ _ => rfl⟩
  · obtain ⟨f, hf, hfe, hffix⟩ := exists_mem_elementaryAut_apply_toWord_eq_squares P hP hs
    exact ⟨f, hf, _, hfe, by simp [vars_def], rfl, .inl rfl, hffix⟩

/-- A word in atomic form in pairwise distinct variables is carried by an elementary automorphism
fixing every word avoiding `P.vars` and a conjugation to a coefficient or to a standard quadratic
word in some of its variables. -/
theorem exists_standardForm [DecidableEq X] (P : AtomicForm G X) (hP : P.vars.Nodup) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∀ a, (∀ v ∈ P.vars, a ∈ GX.avoiding v) → f a = a) ∧
      ((∃ c : G, u * f P.toWord * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f P.toWord * u⁻¹ = S.toWord ∧ S.vars ⊆ {x | x ∈ P.vars}) := by
  -- delete the conjugates of `1`, then turn the commutators into squares if there is a square
  have hP' := hP.sublist P.vars_dropTrivial_sublist
  obtain ⟨f₁, hf₁, Q, hQ, hQv, hQc, hcs, hf₁fix⟩ := exists_comms_eq_nil_or_squares_eq_nil _ hP'
  obtain ⟨f₂, hf₂, u, hf₂fix, h⟩ := exists_standardForm_of_ne_one Q (hQv ▸ hP') hcs
    fun p hp => (mem_conjs_dropTrivial.1 (hQc ▸ hp)).2
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, u, fun a ha => ?_, ?_⟩
  · have ha' : ∀ v ∈ P.dropTrivial.vars, a ∈ GX.avoiding v :=
      fun v hv => ha v (P.vars_dropTrivial_sublist.subset hv)
    rw [MulAut.mul_apply, hf₁fix a ha', hf₂fix a fun v hv => ha' v (hQv ▸ hv)]
  · rw [MulAut.mul_apply, ← toWord_dropTrivial, hQ]
    exact h.imp_right fun ⟨S, hS, hSv⟩ =>
      ⟨S, hS, hSv.trans fun x hx => P.vars_dropTrivial_sublist.subset (hQv ▸ hx)⟩

/-! ### Examples -/

section Examples

/-- The word `[x, y] s²` in atomic form, with a commutator and a square, is carried by an
elementary automorphism to a standard quadratic word of type (3), non-orientable of genus `3`. -/
theorem exists_standard_commutator_mul_sq : ∃ f ∈ GX.elementaryAut G (Fin 3),
    ∃ S : Standard G (Fin 3), f (⟨[(0, 1)], [2], [], 1⟩ : AtomicForm G (Fin 3)).toWord = S.toWord ∧
      ¬S.IsOrientable ∧ S.genus = 3 ∧ S.coeffs = [] := by
  obtain ⟨f, hf, hfe, -⟩ := exists_mem_elementaryAut_apply_toWord_eq_squares
    (⟨[(0, 1)], [2], [], 1⟩ : AtomicForm G (Fin 3)) (by simp [vars_def]) (by simp)
  refine ⟨f, hf, .nonorientable 3 (by omega) id Function.injective_id, ?_, by simp, by simp,
    by simp⟩
  rw [hfe]
  simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, sqWord_def, Standard.toWord_def,
    List.ofFn_succ]

/-- The word `[x, y] s² z⁻¹ c z` in atomic form, with `c ≠ 1`, is carried by an elementary
automorphism and a conjugation to a standard quadratic word of type (4) in the variables `x`, `y`,
`s`, non-orientable of genus `3` with the single coefficient `c`: the conjugate `z⁻¹ c z` becomes
the constant and its variable `z` disappears. -/
theorem exists_standard_commutator_mul_sq_mul_conj {c : G} (hc : c ≠ 1) :
    ∃ f ∈ GX.elementaryAut G (Fin 4), ∃ u : GX G (Fin 4), ∃ S : Standard G (Fin 4),
      u * f (⟨[(0, 1)], [2], [(3, c)], 1⟩ : AtomicForm G (Fin 4)).toWord * u⁻¹ = S.toWord ∧
        ¬S.IsOrientable ∧ S.genus = 3 ∧ S.coeffs = [c] ∧ S.vars = {0, 1, 2} := by
  obtain ⟨f₁, hf₁, h₁, -⟩ := exists_mem_elementaryAut_apply_toWord_eq_squares
    (⟨[(0, 1)], [2], [(3, c)], 1⟩ : AtomicForm G (Fin 4)) (by simp [vars_def]) (by simp)
  obtain ⟨f₂, hf₂, h₂, -⟩ :=
    exists_mem_elementaryAut_conj_toWord_concat (X := Fin 4) [] [0, 1, 2] [] 3 c
      (by simp [vars_def])
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, inr (.of 3), .nonorientableCoeff 3 0 (by omega) ![0, 1, 2]
    Fin.elim0 (by decide) Fin.elim0 (fun j => j.elim0) c hc, ?_, by simp, by simp, by simp, ?_⟩
  · rw [MulAut.mul_apply, h₁]
    refine h₂.trans ?_
    simp [toWord_def, commsProd_def, squaresProd_def, conjsProd_def, sqWord_def,
      Standard.toWord_def, List.ofFn_succ, mul_assoc]
  · ext i
    simp only [Standard.vars_nonorientableCoeff, Set.Sum.elim_range, Matrix.range_cons,
      Set.range_eq_empty, Set.union_empty, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_insert_iff]

end Examples

end AtomicForm

end TauCeti.GroupAlgGeom.Quadratic
