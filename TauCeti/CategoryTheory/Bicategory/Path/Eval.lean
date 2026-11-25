/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Coherent evaluation of paths of `1`-morphisms in a bicategory

A path `p : Quiver.Path a b` in the underlying quiver of a bicategory `B` is a finite string of
composable `1`-morphisms. This file evaluates such a path to a single `1`-morphism
`p.eval : a ⟶ b` of `B`, and compares the evaluation of a concatenation of paths with the
composite of the evaluations.

The evaluation is chosen so that short paths evaluate to what one expects: the empty path
evaluates to `𝟙 a`, the path `[f]` to `f` (by definition, not merely up to a unitor), and a longer
path `[f₁, …, fₙ]` to the left-associated composite `(⋯(f₁ ≫ f₂) ≫ ⋯) ≫ fₙ`.

Since composition in `B` is associative and unital only up to the associators and unitors, the
evaluation of `p.comp q` is in general not equal to `p.eval ≫ q.eval`. Instead there is a
canonical isomorphism `Quiver.Path.evalComp p q : (p.comp q).eval ≅ p.eval ≫ q.eval`, built from
associators and unitors. An empty right factor gives the inverse right unitor, an empty left
factor gives the inverse left unitor, and on three paths the comparisons agree with the
associator of `B` (`Quiver.Path.evalComp_assoc_hom`); since the paths `(p.comp q).comp r` and
`p.comp (q.comp r)` are equal but not definitionally so, this is stated with an `eqToHom`.

Conjugating by these comparisons, a `2`-morphism `θ : q.eval ⟶ q'.eval` of `B` is whiskered by a
path `p` on the left (`Quiver.Path.whiskerLeftEval`) and on the right
(`Quiver.Path.whiskerRightEval`). These whiskerings satisfy the laws of a strict `2`-category on
paths, in which composition of `1`-morphisms is concatenation of paths and the associators and
unitors are the `eqToHom`s along `Quiver.Path.comp_assoc`, `Quiver.Path.nil_comp` and
`Quiver.Path.comp_nil`. `TauCeti.Bicategory.Paths` packages them as a strict bicategory.

## Main definitions and results

* `Quiver.Path.eval`: the left-associated evaluation of a path.
* `Quiver.Path.evalCons`, `Quiver.Path.evalComp`: the comparisons
  `(p.cons f).eval ≅ p.eval ≫ f` and `(p.comp q).eval ≅ p.eval ≫ q.eval`.
* `Quiver.Path.nil_evalComp_hom`, `Quiver.Path.evalComp_nil`: the comparison with an empty
  factor is a unitor.
* `Quiver.Path.evalComp_assoc_hom`: compatibility of the comparisons with the associator.
* `Quiver.Path.whiskerLeftEval`, `Quiver.Path.whiskerRightEval`: whiskering of `2`-morphisms
  between evaluations by paths, with the laws of a strict `2`-category
  (`Quiver.Path.comp_whiskerLeftEval`, `Quiver.Path.whiskerRightEval_comp`,
  `Quiver.Path.whiskerRightEval_whiskerLeftEval`, …).

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651. Proposition 2.5 constructs the
  implicit `2`-category of a bicategory, whose `1`-morphisms are paths.
-/

public section

namespace Quiver.Path

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}

/-- The evaluation of a path of `1`-morphisms in a bicategory: `𝟙 a` for the empty path, `f` for
the path `[f]`, and the left-associated composite `(⋯(f₁ ≫ f₂) ≫ ⋯) ≫ fₙ` for longer paths. -/
@[expose]
def eval : ∀ {b : B}, Path a b → (a ⟶ b)
  | _, nil => 𝟙 a
  | _, cons nil f => f
  | _, cons (cons p g) f => (p.cons g).eval ≫ f

@[simp]
lemma eval_nil : (nil : Path a a).eval = 𝟙 a := rfl

@[simp]
lemma eval_cons_nil (f : a ⟶ b) : (nil.cons f).eval = f := rfl

@[simp]
lemma eval_toPath (f : a ⟶ b) : f.toPath.eval = f := rfl

@[simp]
lemma eval_cons_cons (p : Path a b) (g : b ⟶ c) (f : c ⟶ d) :
    ((p.cons g).cons f).eval = (p.cons g).eval ≫ f := rfl

example (f : a ⟶ b) (g : b ⟶ c) : (f.toPath.cons g).eval = f ≫ g := rfl

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    ((f.toPath.cons g).cons h).eval = (f ≫ g) ≫ h := rfl

/-- The comparison `(p.cons f).eval ≅ p.eval ≫ f`: the inverse left unitor of `f` when `p` is
empty, and the identity otherwise. -/
def evalCons : ∀ {b c : B} (p : Path a b) (f : b ⟶ c), (p.cons f).eval ≅ p.eval ≫ f
  | _, _, nil, f => (λ_ f).symm
  | _, _, cons _ _, _ => Iso.refl _

lemma evalCons_nil (f : a ⟶ b) : evalCons nil f = (λ_ f).symm := (rfl)

@[simp]
lemma evalCons_nil_hom (f : a ⟶ b) : (evalCons nil f).hom = (λ_ f).inv := (rfl)

@[simp]
lemma evalCons_nil_inv (f : a ⟶ b) : (evalCons nil f).inv = (λ_ f).hom := (rfl)

@[simp]
lemma evalCons_cons (p : Path a b) (g : b ⟶ c) (f : c ⟶ d) :
    evalCons (p.cons g) f = Iso.refl _ := (rfl)

/-- `Quiver.Path.evalCons` is compatible with equalities of paths. -/
private lemma evalCons_hom_congr {P P' : Path a b} (h : P = P') (f : b ⟶ c) :
    (evalCons P f).hom = eqToHom (congrArg (fun P => (P.cons f).eval) h) ≫ (evalCons P' f).hom ≫
      eqToHom (congrArg eval h.symm) ▷ f := by
  subst h; simp

/-- The comparison `(p.comp q).eval ≅ p.eval ≫ q.eval` between the evaluation of a
concatenation and the composite of the evaluations, by recursion on `q`. -/
def evalComp (p : Path a b) : ∀ {c : B} (q : Path b c), (p.comp q).eval ≅ p.eval ≫ q.eval
  | _, nil => (ρ_ p.eval).symm
  | _, cons q f => evalCons (p.comp q) f ≪≫ whiskerRightIso (evalComp p q) f ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso p.eval (evalCons q f).symm

/-- With an empty right factor, the comparison is the inverse right unitor. -/
@[simp]
lemma evalComp_nil (p : Path a b) : evalComp p nil = (ρ_ p.eval).symm := (rfl)

lemma evalComp_cons (p : Path a b) (q : Path b c) (f : c ⟶ d) :
    evalComp p (q.cons f) = evalCons (p.comp q) f ≪≫ whiskerRightIso (evalComp p q) f ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso p.eval (evalCons q f).symm := (rfl)

/-- With a right factor of length one, the comparison is `Quiver.Path.evalCons`. -/
@[simp]
lemma evalComp_toPath (p : Path a b) (f : b ⟶ c) : evalComp p f.toPath = evalCons p f := by
  ext
  simp only [Quiver.Hom.toPath, evalComp_cons, Iso.trans_hom, Iso.symm_hom, evalCons_nil_inv,
    whiskerLeftIso_hom, evalComp_nil]
  dsimp only [eval_cons_nil]
  simp

/-- With an empty left factor, the comparison is the inverse left unitor, after identifying
`nil.comp q` with `q`. -/
lemma nil_evalComp_hom (q : Path a b) :
    (evalComp nil q).hom = eqToHom (congrArg eval (nil_comp q)) ≫ (λ_ q.eval).inv := by
  induction q with
  | nil =>
    -- `nil.comp nil` is `nil` by definition, so the `eqToHom` is an identity.
    exact unitors_inv_equal.symm.trans (Category.id_comp _).symm
  | cons q f ih =>
    rw [evalComp_cons]
    simp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, Iso.symm_hom, ih,
      evalCons_hom_congr (nil_comp q) f]
    dsimp only [eval_nil]
    simp

lemma nil_evalComp_inv (q : Path a b) :
    (evalComp nil q).inv = (λ_ q.eval).hom ≫ eqToHom (congrArg eval (nil_comp q)).symm :=
  Iso.inv_ext (by simp [nil_evalComp_hom])

/-- The comparisons are compatible with the associator: the two ways of comparing the evaluation
of a concatenation of three paths with `p.eval ≫ (q.eval ≫ r.eval)`, through
`(p.comp q).comp r` and through `p.comp (q.comp r)`, agree. -/
@[reassoc]
lemma evalComp_assoc_hom (p : Path a b) (q : Path b c) : ∀ {d : B} (r : Path c d),
    (evalComp (p.comp q) r).hom ≫ (evalComp p q).hom ▷ r.eval ≫ (α_ _ _ _).hom =
      eqToHom (congrArg eval (comp_assoc p q r)) ≫ (evalComp p (q.comp r)).hom ≫
        p.eval ◁ (evalComp q r).hom
  | _, nil => by
    simp only [comp_nil, evalComp_nil, Iso.symm_hom]
    -- `(p.comp q).comp nil` and `p.comp (q.comp nil)` are both `p.comp q` by definition.
    exact ((Category.id_comp _).trans (by simp)).symm
  | _, cons r f => by
    -- The inductive hypothesis, solved for `((p.comp q).evalComp r).hom`.
    have ih : (evalComp (p.comp q) r).hom = eqToHom (congrArg eval (comp_assoc p q r)) ≫
        (evalComp p (q.comp r)).hom ≫ p.eval ◁ (evalComp q r).hom ≫ (α_ _ _ _).inv ≫
          (evalComp p q).inv ▷ r.eval := by
      rw [← cancel_mono ((evalComp p q).hom ▷ r.eval ≫ (α_ _ _ _).hom), evalComp_assoc_hom p q r]
      simp
    simp [evalComp_cons, whisker_exchange_assoc, ih, evalCons_hom_congr (comp_assoc p q r) f]

/-- The comparison for `(p.comp q).comp r`, expressed through those for `p.comp (q.comp r)`. -/
lemma comp_evalComp_hom (p : Path a b) (q : Path b c) (r : Path c d) :
    (evalComp (p.comp q) r).hom = eqToHom (congrArg eval (comp_assoc p q r)) ≫
      (evalComp p (q.comp r)).hom ≫ p.eval ◁ (evalComp q r).hom ≫ (α_ _ _ _).inv ≫
        (evalComp p q).inv ▷ r.eval := by
  rw [← cancel_mono ((evalComp p q).hom ▷ r.eval ≫ (α_ _ _ _).hom), evalComp_assoc_hom]
  simp

lemma comp_evalComp_inv (p : Path a b) (q : Path b c) (r : Path c d) :
    (evalComp (p.comp q) r).inv = (evalComp p q).hom ▷ r.eval ≫ (α_ _ _ _).hom ≫
      p.eval ◁ (evalComp q r).inv ≫ (evalComp p (q.comp r)).inv ≫
        eqToHom (congrArg eval (comp_assoc p q r)).symm :=
  Iso.inv_ext (by simp [comp_evalComp_hom])

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (evalComp f.toPath (g.toPath.cons h)).hom = (α_ f g h).hom := by
  simp only [evalComp_cons, evalComp_toPath, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom]
  dsimp only [Quiver.Hom.toPath, eval_cons_nil, comp_cons, comp_nil]
  simp

/-- Left whiskering of a `2`-morphism between evaluations by a path, conjugated by the
comparisons `Quiver.Path.evalComp`. -/
def whiskerLeftEval (p : Path a b) {q q' : Path b c} (θ : q.eval ⟶ q'.eval) :
    (p.comp q).eval ⟶ (p.comp q').eval :=
  (evalComp p q).hom ≫ p.eval ◁ θ ≫ (evalComp p q').inv

/-- Right whiskering of a `2`-morphism between evaluations by a path, conjugated by the
comparisons `Quiver.Path.evalComp`. -/
def whiskerRightEval {p p' : Path a b} (θ : p.eval ⟶ p'.eval) (q : Path b c) :
    (p.comp q).eval ⟶ (p'.comp q).eval :=
  (evalComp p q).hom ≫ θ ▷ q.eval ≫ (evalComp p' q).inv

lemma whiskerLeftEval_def (p : Path a b) {q q' : Path b c} (θ : q.eval ⟶ q'.eval) :
    p.whiskerLeftEval θ = (evalComp p q).hom ≫ p.eval ◁ θ ≫ (evalComp p q').inv := (rfl)

lemma whiskerRightEval_def {p p' : Path a b} (θ : p.eval ⟶ p'.eval) (q : Path b c) :
    whiskerRightEval θ q = (evalComp p q).hom ≫ θ ▷ q.eval ≫ (evalComp p' q).inv := (rfl)

@[simp]
lemma whiskerLeftEval_id (p : Path a b) (q : Path b c) :
    p.whiskerLeftEval (𝟙 q.eval) = 𝟙 _ := by
  simp [whiskerLeftEval]

@[simp]
lemma whiskerLeftEval_comp (p : Path a b) {q q' q'' : Path b c} (η : q.eval ⟶ q'.eval)
    (θ : q'.eval ⟶ q''.eval) :
    p.whiskerLeftEval (η ≫ θ) = p.whiskerLeftEval η ≫ p.whiskerLeftEval θ := by
  simp [whiskerLeftEval]

@[simp]
lemma id_whiskerRightEval (p : Path a b) (q : Path b c) :
    whiskerRightEval (𝟙 p.eval) q = 𝟙 _ := by
  simp [whiskerRightEval]

@[simp]
lemma comp_whiskerRightEval {p p' p'' : Path a b} (η : p.eval ⟶ p'.eval)
    (θ : p'.eval ⟶ p''.eval) (q : Path b c) :
    whiskerRightEval (η ≫ θ) q = whiskerRightEval η q ≫ whiskerRightEval θ q := by
  simp [whiskerRightEval]

/-- The interchange law for whiskering by paths. -/
lemma whiskerLeftEval_comp_whiskerRightEval {p p' : Path a b} {q q' : Path b c}
    (η : p.eval ⟶ p'.eval) (θ : q.eval ⟶ q'.eval) :
    p.whiskerLeftEval θ ≫ whiskerRightEval η q' = whiskerRightEval η q ≫ p'.whiskerLeftEval θ := by
  simp [whiskerLeftEval, whiskerRightEval, whisker_exchange_assoc]

@[simp]
lemma whiskerLeftEval_eqToHom (p : Path a b) {q q' : Path b c} (h : q = q') :
    p.whiskerLeftEval (eqToHom (congrArg eval h)) =
      eqToHom (congrArg (fun q => (p.comp q).eval) h) := by
  subst h; simp

@[simp]
lemma eqToHom_whiskerRightEval {p p' : Path a b} (h : p = p') (q : Path b c) :
    whiskerRightEval (eqToHom (congrArg eval h)) q =
      eqToHom (congrArg (fun p => (p.comp q).eval) h) := by
  subst h; simp

/-- Whiskering on the left by the empty path is the identity, after identifying `nil.comp q`
with `q`. -/
lemma nil_whiskerLeftEval {q q' : Path a b} (θ : q.eval ⟶ q'.eval) :
    nil.whiskerLeftEval θ =
      eqToHom (congrArg eval (nil_comp q)) ≫ θ ≫ eqToHom (congrArg eval (nil_comp q')).symm := by
  simp only [whiskerLeftEval, nil_evalComp_hom, nil_evalComp_inv]
  dsimp only [eval_nil]
  simp

/-- Whiskering on the right by the empty path is the identity. Both `eqToHom`s are identities,
since `p.comp nil` is `p` by definition; they are kept so that the statement has the shape of
`CategoryTheory.Bicategory.whiskerRight_id`. -/
lemma whiskerRightEval_nil {p p' : Path a b} (θ : p.eval ⟶ p'.eval) :
    whiskerRightEval θ nil =
      eqToHom (congrArg eval (comp_nil p)) ≫ θ ≫ eqToHom (congrArg eval (comp_nil p')).symm := by
  have h : whiskerRightEval θ nil = 𝟙 _ ≫ θ ≫ 𝟙 _ := by
    simp only [whiskerRightEval, evalComp_nil, Iso.symm_hom, Iso.symm_inv]
    dsimp only [eval_nil]
    simp
  exact h

/-- Whiskering on the left by a concatenation is whiskering by each factor in turn, after
reassociating the paths. -/
lemma comp_whiskerLeftEval (p : Path a b) (q : Path b c) {r r' : Path c d}
    (θ : r.eval ⟶ r'.eval) :
    (p.comp q).whiskerLeftEval θ =
      eqToHom (congrArg eval (comp_assoc p q r)) ≫ p.whiskerLeftEval (q.whiskerLeftEval θ) ≫
        eqToHom (congrArg eval (comp_assoc p q r')).symm := by
  simp only [whiskerLeftEval, comp_evalComp_hom, comp_evalComp_inv, Category.assoc]
  rw [← whisker_exchange_assoc, inv_hom_whiskerRight_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  bicategory

/-- Whiskering on the right by a concatenation is whiskering by each factor in turn, after
reassociating the paths. -/
lemma whiskerRightEval_comp {p p' : Path a b} (θ : p.eval ⟶ p'.eval) (q : Path b c)
    (r : Path c d) :
    whiskerRightEval θ (q.comp r) =
      eqToHom (congrArg eval (comp_assoc p q r)).symm ≫
        whiskerRightEval (whiskerRightEval θ q) r ≫
          eqToHom (congrArg eval (comp_assoc p' q r)) := by
  simp only [whiskerRightEval, comp_evalComp_hom, comp_evalComp_inv, Category.assoc,
    comp_whiskerRight, inv_hom_whiskerRight_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, eqToHom_trans, Category.comp_id]
  have h : θ ▷ (q.comp r).eval =
      p.eval ◁ (evalComp q r).hom ≫ θ ▷ (q.eval ≫ r.eval) ≫ p'.eval ◁ (evalComp q r).inv := by
    rw [whisker_exchange_assoc, whiskerLeft_hom_inv, Category.comp_id]
  rw [h]
  bicategory

/-- Whiskering on the left and on the right commute, after reassociating the paths. -/
lemma whiskerRightEval_whiskerLeftEval (p : Path a b) {q q' : Path b c}
    (θ : q.eval ⟶ q'.eval) (r : Path c d) :
    whiskerRightEval (p.whiskerLeftEval θ) r =
      eqToHom (congrArg eval (comp_assoc p q r)) ≫ p.whiskerLeftEval (whiskerRightEval θ r) ≫
        eqToHom (congrArg eval (comp_assoc p q' r)).symm := by
  simp only [whiskerLeftEval, whiskerRightEval, comp_evalComp_hom, comp_evalComp_inv,
    Category.assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc, whiskerLeft_comp]
  bicategory

end Quiver.Path
