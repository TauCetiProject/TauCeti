/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Elementary automorphisms of the free `G`-group

A `G`-automorphism of the free `G`-group `G[X] = G ∗ F(X)` is an automorphism fixing the
coefficients. It is determined by the words it substitutes for the variables, and a substitution
`x ↦ w x` is an automorphism as soon as there is a substitution `y ↦ w' y` such that each of the
two undoes the other (`GX.substEquiv`).

This file constructs the elementary `G`-automorphisms of Nielsen type from which the changes of
variables of the theory of equations over `G` are composed:

* `GX.transvection x a b`: `x ↦ a x b`, the other variables being fixed, for words `a` and `b` in
  which `x` does not occur. This covers the substitutions `x ↦ x y` and `x ↦ y x` for another
  variable `y`, the conjugation `x ↦ y⁻¹ x y`, and the substitutions `x ↦ x g` and `x ↦ g x` for a
  coefficient `g`.
* `GX.invertVar x`: `x ↦ x⁻¹`, the other variables being fixed.

They generate the group `GX.elementaryAut` of elementary automorphisms, whose elements fix the
coefficients (`GX.apply_inl_of_mem_elementaryAut`). The file also constructs `GX.renameEquiv e`,
the renaming of the variables along a bijection, in particular a permutation of the variables;
the renamings are not among the generators of `GX.elementaryAut`.

Each comes with its values on coefficients and variables, its inverse, and its effect on
evaluation: the value of `φ w` at a point `v` is the value of `w` at the point obtained from `v`
by the corresponding substitution. The words in which `x` does not occur form the subgroup
`GX.avoiding x`: they are the words unchanged by the substitution `x ↦ 1`, and their values do
not depend on the coordinate `x` of a point. Transvections of finitely many variables, by words in
which none of these variables occurs, are carried out at once by one elementary automorphism,
which fixes the words in which none of them occurs
(`GX.exists_mem_elementaryAut_forall_apply_inr_of`).

These are the automorphisms by which a strictly quadratic word is normalized: a product of
elementary `G`-automorphisms followed by a conjugation in `G[X]` brings it either to a coefficient
or to a standard quadratic word. This corrects [IFT], §2.7, Lemma 1 (and [VAR-I], §1, Lemma 6),
which asserts a `G`-automorphism alone and has no coefficient case; a coefficient `g ≠ 1` is
strictly quadratic and is not a standard quadratic word.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Lemma 1.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 6.
-/

public section

open Monoid.Coprod Function

namespace TauCeti.GroupAlgGeom.GX

variable {G H X Y Z : Type*} [Group G] [Group H] (ι : G →* H)

/-! ### Automorphisms given by substitutions -/

section SubstEquiv

variable (w : X → GX G Y) (w' : Y → GX G X)
  (h₁ : ∀ x, eval inl w' (w x) = inr (FreeGroup.of x))
  (h₂ : ∀ y, eval inl w (w' y) = inr (FreeGroup.of y))

/-- The isomorphism `G[X] ≃* G[Y]` fixing the coefficients and substituting the word `w x` for
every variable `x`, given words `w' y` such that the substitutions `x ↦ w x` and `y ↦ w' y` are
mutually inverse. -/
def substEquiv : GX G X ≃* GX G Y :=
  MonoidHom.toMulEquiv (eval inl w) (eval inl w')
    (by rw [eval_comp_eval, ← eval_inl_inr_of]; exact congrArg _ (funext fun x => by simp [h₁]))
    (by rw [eval_comp_eval, ← eval_inl_inr_of]; exact congrArg _ (funext fun y => by simp [h₂]))

@[simp]
theorem substEquiv_apply (u : GX G X) : substEquiv w w' h₁ h₂ u = eval inl w u := (rfl)

@[simp]
theorem substEquiv_symm : (substEquiv w w' h₁ h₂).symm = substEquiv w' w h₂ h₁ := (rfl)

/-- Evaluating a substituted word at `v` evaluates the word at the tuple of the values at `v` of
the substituted words. -/
theorem eval_substEquiv (v : Y → H) (u : GX G X) :
    eval ι v (substEquiv w w' h₁ h₂ u) = eval ι (wordMap ι w v) u := by
  rw [← eval_comp_eval]
  simp

end SubstEquiv

/-! ### Words in which a variable does not occur -/

section Avoiding

variable [DecidableEq X] {x y : X} {a b : GX G X}

/-- The subgroup of `G[X]` of the words in which the variable `x` does not occur: the words
unchanged by the substitution `x ↦ 1`. -/
def avoiding (x : X) : Subgroup (GX G X) :=
  (eval inl (update (fun y => inr (FreeGroup.of y)) x 1)).eqLocus (MonoidHom.id (GX G X))

theorem mem_avoiding :
    a ∈ avoiding x ↔ eval inl (update (fun y => inr (FreeGroup.of y)) x 1) a = a := Iff.rfl

@[simp]
theorem inl_mem_avoiding (x : X) (g : G) : (inl g : GX G X) ∈ avoiding x := by
  simp [mem_avoiding]

/-- A variable does not occur in another variable, and occurs in itself. -/
@[simp]
theorem inr_of_mem_avoiding_iff : (inr (FreeGroup.of y) : GX G X) ∈ avoiding x ↔ y ≠ x := by
  by_cases h : y = x
  · subst h
    simpa [mem_avoiding] using fun h : (1 : GX G X) = inr (FreeGroup.of y) =>
      FreeGroup.of_ne_one y (inr_injective (h.symm.trans (map_one inr).symm))
  · simp [mem_avoiding, h]

theorem inr_of_mem_avoiding (h : y ≠ x) : (inr (FreeGroup.of y) : GX G X) ∈ avoiding x :=
  inr_of_mem_avoiding_iff.2 h

/-- Substituting the word `c` for `x` in a word and evaluating at `v` evaluates the word at the
point obtained from `v` by replacing its coordinate `x` by the value of `c` at `v`. -/
theorem eval_eval_update (v : X → H) (x : X) (c u : GX G X) :
    eval ι v (eval inl (update (fun y => inr (FreeGroup.of y)) x c) u) =
      eval ι (update v x (eval ι v c)) u := by
  rw [← MonoidHom.comp_apply, eval_comp_eval, wordMap_update, wordMap_id]

/-- The value of a word in which `x` does not occur does not depend on the coordinate `x` of the
point. -/
theorem eval_congr_of_mem_avoiding (ha : a ∈ avoiding x) {v v' : X → H}
    (h : ∀ y, y ≠ x → v y = v' y) : eval ι v a = eval ι v' a := by
  have key : update v x 1 = update v' x 1 := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, h y hy]
  rw [← mem_avoiding.1 ha]
  simp only [eval_eval_update, map_one, key]

/-- The value of a word in which `x` does not occur is unchanged by a change of the coordinate
`x` of the point. -/
@[simp]
theorem eval_update_of_mem_avoiding (ha : a ∈ avoiding x) (v : X → H) (c : H) :
    eval ι (update v x c) a = eval ι v a :=
  eval_congr_of_mem_avoiding ι ha fun y hy => by simp [hy]

end Avoiding

/-! ### Transvections -/

section Transvection

variable [DecidableEq X] {x y : X} {a b c d : GX G X}

private theorem eval_update_mul_update (ha : a ∈ avoiding x) (hb : b ∈ avoiding x) (z : X) :
    eval inl (update (fun y => inr (FreeGroup.of y)) x (a * inr (FreeGroup.of x) * b))
      (update (fun y => inr (FreeGroup.of y)) x (a⁻¹ * inr (FreeGroup.of x) * b⁻¹) z) =
      inr (FreeGroup.of z) := by
  by_cases hz : z = x
  · subst hz; simp [ha, hb, mul_assoc]
  · simp [hz]

/-- The `G`-automorphism `x ↦ a x b` of `G[X]` fixing the other variables, for words `a` and `b`
in which `x` does not occur. For `a = 1` and `b` a variable or a coefficient this is the Nielsen
transformation `x ↦ x y` or the substitution `x ↦ x g`, and for `a = b⁻¹` it conjugates `x`. -/
def transvection (x : X) (a b : GX G X) (ha : a ∈ avoiding x) (hb : b ∈ avoiding x) :
    MulAut (GX G X) :=
  substEquiv (update (fun y => inr (FreeGroup.of y)) x (a * inr (FreeGroup.of x) * b))
    (update (fun y => inr (FreeGroup.of y)) x (a⁻¹ * inr (FreeGroup.of x) * b⁻¹))
    (by simpa using eval_update_mul_update (inv_mem ha) (inv_mem hb))
    (eval_update_mul_update ha hb)

variable (ha : a ∈ avoiding x) (hb : b ∈ avoiding x)

theorem transvection_apply (u : GX G X) :
    transvection x a b ha hb u =
      eval inl (update (fun y => inr (FreeGroup.of y)) x (a * inr (FreeGroup.of x) * b)) u :=
  (rfl)

theorem transvection_inl (g : G) : transvection x a b ha hb (inl g) = inl g := by
  simp [transvection_apply]

@[simp]
theorem transvection_inr_of_self :
    transvection x a b ha hb (inr (FreeGroup.of x)) = a * inr (FreeGroup.of x) * b := by
  simp [transvection_apply]

theorem transvection_inr_of_of_ne (h : y ≠ x) :
    transvection x a b ha hb (inr (FreeGroup.of y)) = inr (FreeGroup.of y) := by
  simp [transvection_apply, h]

/-- A transvection of the variable `x` fixes the words in which `x` does not occur. -/
@[simp]
theorem transvection_apply_of_mem_avoiding (hc : c ∈ avoiding x) :
    transvection x a b ha hb c = c := by
  simp [transvection_apply, hc]

/-- The inverse of `x ↦ a x b` is `x ↦ a⁻¹ x b⁻¹`. -/
@[simp]
theorem transvection_symm :
    (transvection x a b ha hb).symm = transvection x a⁻¹ b⁻¹ (inv_mem ha) (inv_mem hb) := by
  refine ext_hom (fun g => by simp [transvection]) fun z => ?_
  by_cases hz : z = x
  · subst hz; simp [transvection]
  · simp [transvection, hz]

/-- The inverse of `x ↦ a x b` is `x ↦ a⁻¹ x b⁻¹`. -/
@[simp]
theorem transvection_inv :
    (transvection x a b ha hb)⁻¹ = transvection x a⁻¹ b⁻¹ (inv_mem ha) (inv_mem hb) := by
  rw [MulAut.inv_def, transvection_symm]

/-- Transvections of the same variable compose by multiplying their words. -/
theorem transvection_mul_transvection (hc : c ∈ avoiding x) (hd : d ∈ avoiding x) :
    transvection x a b ha hb * transvection x c d hc hd =
      transvection x (c * a) (b * d) (mul_mem hc ha) (mul_mem hb hd) := by
  refine ext_hom (fun g => by simp) fun z => ?_
  by_cases hz : z = x
  · subst hz; simp [hc, hd, mul_assoc]
  · simp [hz]

@[simp]
theorem transvection_one_one (x : X) :
    transvection x (1 : GX G X) 1 (one_mem _) (one_mem _) = 1 := by
  refine ext_hom (fun g => by simp) fun z => ?_
  by_cases hz : z = x
  · subst hz; simp
  · simp [hz]

/-- The value at `v` of the image of `u` under `x ↦ a x b` is the value of `u` at the point
obtained from `v` by replacing its coordinate `x` by `a(v) v_x b(v)`. -/
@[simp]
theorem eval_transvection (v : X → H) (u : GX G X) :
    eval ι v (transvection x a b ha hb u) =
      eval ι (update v x (eval ι v a * v x * eval ι v b)) u := by
  rw [transvection_apply, eval_eval_update]
  simp

end Transvection

/-! ### Inversion of a variable -/

section InvertVar

variable [DecidableEq X] {x y : X} {a : GX G X}

private theorem eval_update_inv_update_inv (x z : X) :
    eval (inl : G →* GX G X) (update (fun y => inr (FreeGroup.of y)) x (inr (FreeGroup.of x))⁻¹)
      (update (fun y => inr (FreeGroup.of y)) x (inr (FreeGroup.of x))⁻¹ z) =
      inr (FreeGroup.of z) := by
  by_cases hz : z = x
  · subst hz; simp
  · simp [hz]

variable (G) in
/-- The `G`-automorphism `x ↦ x⁻¹` of `G[X]` fixing the other variables. -/
def invertVar (x : X) : MulAut (GX G X) :=
  substEquiv (update (fun y => inr (FreeGroup.of y)) x (inr (FreeGroup.of x))⁻¹)
    (update (fun y => inr (FreeGroup.of y)) x (inr (FreeGroup.of x))⁻¹)
    (eval_update_inv_update_inv x) (eval_update_inv_update_inv x)

theorem invertVar_apply (x : X) (u : GX G X) :
    invertVar G x u =
      eval inl (update (fun y => inr (FreeGroup.of y)) x (inr (FreeGroup.of x))⁻¹) u := (rfl)

theorem invertVar_inl (x : X) (g : G) : invertVar G x (inl g) = inl g := by
  simp [invertVar_apply]

@[simp]
theorem invertVar_inr_of_self (x : X) :
    invertVar G x (inr (FreeGroup.of x)) = (inr (FreeGroup.of x))⁻¹ := by
  simp [invertVar_apply]

theorem invertVar_inr_of_of_ne (h : y ≠ x) :
    invertVar G x (inr (FreeGroup.of y)) = inr (FreeGroup.of y) := by
  simp [invertVar_apply, h]

/-- Inverting the variable `x` fixes the words in which `x` does not occur. -/
@[simp]
theorem invertVar_apply_of_mem_avoiding (ha : a ∈ avoiding x) : invertVar G x a = a := by
  simp [invertVar_apply, ha]

/-- Inverting a variable is an involution. -/
@[simp]
theorem invertVar_symm (x : X) : (invertVar G x).symm = invertVar G x := (rfl)

/-- Inverting a variable is an involution. -/
@[simp]
theorem invertVar_inv (x : X) : (invertVar G x)⁻¹ = invertVar G x := by
  rw [MulAut.inv_def, invertVar_symm]

/-- Inverting a variable is an involution. -/
@[simp]
theorem invertVar_mul_self (x : X) : invertVar G x * invertVar G x = 1 := by
  rw [← eq_inv_iff_mul_eq_one, invertVar_inv]

/-- The value at `v` of the image of `u` under `x ↦ x⁻¹` is the value of `u` at the point
obtained from `v` by inverting its coordinate `x`. -/
@[simp]
theorem eval_invertVar (v : X → H) (x : X) (u : GX G X) :
    eval ι v (invertVar G x u) = eval ι (update v x (v x)⁻¹) u := by
  rw [invertVar_apply, eval_eval_update]
  simp

end InvertVar

/-! ### Renaming the variables -/

section RenameEquiv

variable (G) in
/-- The `G`-isomorphism `G[X] ≃* G[Y]` renaming the variables along a bijection `e : X ≃ Y`. For
a permutation of `X` it is the `G`-automorphism of `G[X]` permuting the variables. -/
def renameEquiv (e : X ≃ Y) : GX G X ≃* GX G Y :=
  MulEquiv.coprodCongr (.refl G) (FreeGroup.freeGroupCongr e)

theorem renameEquiv_apply (e : X ≃ Y) (u : GX G X) :
    renameEquiv G e u = Monoid.Coprod.map (.id G) (FreeGroup.map e) u := (rfl)

@[simp]
theorem renameEquiv_inl (e : X ≃ Y) (g : G) : renameEquiv G e (inl g) = inl g := by
  simp [renameEquiv_apply]

@[simp]
theorem renameEquiv_inr_of (e : X ≃ Y) (x : X) :
    renameEquiv G e (inr (FreeGroup.of x)) = inr (FreeGroup.of (e x)) := by
  simp [renameEquiv_apply]

@[simp]
theorem renameEquiv_symm (e : X ≃ Y) : (renameEquiv G e).symm = renameEquiv G e.symm := (rfl)

@[simp]
theorem renameEquiv_refl : renameEquiv G (Equiv.refl X) = MulEquiv.refl _ :=
  ext_hom (fun g => by simp) fun x => by simp

@[simp]
theorem renameEquiv_trans (e : X ≃ Y) (f : Y ≃ Z) :
    (renameEquiv G e).trans (renameEquiv G f) = renameEquiv G (e.trans f) :=
  ext_hom (fun g => by simp) fun x => by simp

/-- The value at `v` of a renamed word is the value of the word at the renamed point `v ∘ e`. -/
@[simp]
theorem eval_renameEquiv (v : Y → H) (e : X ≃ Y) (u : GX G X) :
    eval ι v (renameEquiv G e u) = eval ι (v ∘ e) u := by
  simp [renameEquiv_apply]

end RenameEquiv

/-! ### The group of elementary automorphisms -/

section Elementary

open scoped Classical in
variable (G X) in
/-- The group of elementary automorphisms of `G[X]`: the subgroup of the automorphism group
generated by the substitutions `x ↦ a x b`, for words `a` and `b` in which `x` does not occur, and
the inversions `x ↦ x⁻¹`. The renamings `GX.renameEquiv` of the variables are not among the
generators. -/
noncomputable def elementaryAut : Subgroup (MulAut (GX G X)) :=
  Subgroup.closure ({φ | ∃ (x : X) (a b : GX G X) (ha : a ∈ avoiding x) (hb : b ∈ avoiding x),
      φ = transvection x a b ha hb} ∪ Set.range (invertVar G))

variable [DecidableEq X]

/-- `elementaryAut G X` is generated by the transvections and the inversions of the variables, for
any decidable equality on `X`. -/
theorem elementaryAut_eq_closure :
    elementaryAut G X = Subgroup.closure ({φ | ∃ (x : X) (a b : GX G X) (ha : a ∈ avoiding x)
      (hb : b ∈ avoiding x), φ = transvection x a b ha hb} ∪ Set.range (invertVar G)) := by
  -- the two sides differ only in the instance of `DecidableEq X`
  rw [elementaryAut]
  congr!

@[simp]
theorem transvection_mem_elementaryAut (x : X) {a b : GX G X} (ha : a ∈ avoiding x)
    (hb : b ∈ avoiding x) : transvection x a b ha hb ∈ elementaryAut G X := by
  rw [elementaryAut_eq_closure]
  exact Subgroup.subset_closure (.inl ⟨x, a, b, ha, hb, rfl⟩)

@[simp]
theorem invertVar_mem_elementaryAut (x : X) : invertVar G x ∈ elementaryAut G X := by
  rw [elementaryAut_eq_closure]
  exact Subgroup.subset_closure (.inr ⟨x, rfl⟩)

omit [DecidableEq X] in
/-- Elementary automorphisms fix the coefficients. -/
theorem apply_inl_of_mem_elementaryAut {f : MulAut (GX G X)} (hf : f ∈ elementaryAut G X) (g : G) :
    f (inl g) = inl g := by
  classical
  rw [elementaryAut_eq_closure] at hf
  induction hf using Subgroup.closure_induction with
  | mem f hf => obtain ⟨x, a, b, ha, hb, rfl⟩ | ⟨x, rfl⟩ := hf <;> simp
  | one => rfl
  | mul f f' _ _ hf hf' => simp [hf, hf']
  | inv f _ hf => simpa [MulEquiv.symm_apply_eq] using hf.symm

/-- Simultaneous transvections: for a finite set `Y` of variables and words `a y`, `b y` in which
no variable of `Y` occurs, there is an elementary automorphism with `y ↦ a y * y * b y` for every
`y ∈ Y` which fixes every word in which no variable of `Y` occurs. -/
theorem exists_mem_elementaryAut_forall_apply_inr_of (Y : Finset X) (a b : X → GX G X)
    (ha : ∀ y ∈ Y, ∀ y' ∈ Y, a y ∈ avoiding y') (hb : ∀ y ∈ Y, ∀ y' ∈ Y, b y ∈ avoiding y') :
    ∃ f ∈ elementaryAut G X,
      (∀ y ∈ Y, f (inr (FreeGroup.of y)) = a y * inr (FreeGroup.of y) * b y) ∧
      ∀ w : GX G X, (∀ y ∈ Y, w ∈ avoiding y) → f w = w := by
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun w _ => rfl⟩
  | insert y₀ Y hy₀ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at ha hb ⊢
    obtain ⟨f, hf, hfY, hfw⟩ :=
      ih (fun y hy y' hy' => (ha.2 y hy).2 y' hy') (fun y hy y' hy' => (hb.2 y hy).2 y' hy')
    -- first the transvections of the variables of `Y`, then the one of `y₀`
    refine ⟨transvection y₀ (a y₀) (b y₀) ha.1.1 hb.1.1 * f,
      mul_mem (transvection_mem_elementaryAut _ _ _) hf, ⟨?_, fun y hy => ?_⟩, fun w hw => ?_⟩
    · rw [MulAut.mul_apply,
        hfw _ fun y hy => inr_of_mem_avoiding (ne_of_mem_of_not_mem hy hy₀).symm,
        transvection_inr_of_self]
    · rw [MulAut.mul_apply, hfY y hy]
      simp [(ha.2 y hy).1, (hb.2 y hy).1, ne_of_mem_of_not_mem hy hy₀]
    · rw [MulAut.mul_apply, hfw w hw.2, transvection_apply_of_mem_avoiding _ _ hw.1]

end Elementary

end TauCeti.GroupAlgGeom.GX
