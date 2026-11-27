/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Path.Eval

/-!
# The strict bicategory of paths in a bicategory

For a bicategory `B`, `TauCeti.Bicategory.Paths B` is the strict bicategory whose objects are
those of `B`, whose `1`-morphisms `a ⟶ b` are the paths `Quiver.Path a.as b.as` of
`1`-morphisms of `B`, and whose `2`-morphisms `p ⟶ q` are the `2`-morphisms
`p.eval ⟶ q.eval` of `B` between the evaluations of `Quiver.Path.eval`. No quotient of the
`2`-morphisms of `B` is taken.

Composition of `1`-morphisms is concatenation of paths, which is strictly associative and
unital, and the associators and unitors are the `eqToIso`s along `Quiver.Path.comp_assoc`,
`Quiver.Path.nil_comp` and `Quiver.Path.comp_nil`, so `Paths B` is a strict bicategory. The weak
associativity and unitality of `B` is absorbed into whiskering: whiskering a `2`-morphism by a
path conjugates the whiskering of `B` by the comparisons
`Quiver.Path.evalComp p q : (p.comp q).eval ≅ p.eval ≫ q.eval`, as in
`Quiver.Path.whiskerLeftEval` and `Quiver.Path.whiskerRightEval`, whose laws are proved in
`TauCeti.CategoryTheory.Bicategory.Path.Eval`.

Since `Quiver.Path.eval` sends a path `[f]` of length one to `f` by definition, the
`2`-morphisms `[f] ⟶ [g]` of `Paths B` are exactly the `2`-morphisms `f ⟶ g` of `B`.

## Main definitions

* `TauCeti.Bicategory.Paths B`: a copy of the objects of `B`, carrying the bicategory of paths.
* `TauCeti.Bicategory.Paths.instBicategory`, `TauCeti.Bicategory.Paths.instStrict`: the strict
  bicategory structure.
* `TauCeti.Bicategory.Paths.comp₂_def`, `TauCeti.Bicategory.Paths.whiskerLeft_def`, … : the
  `2`-categorical operations of `Paths B` expressed in `B`.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651. Proposition 2.5 constructs this
  strict `2`-category of paths from a bicategory.
-/

public section

namespace TauCeti.Bicategory

open CategoryTheory Bicategory Quiver

universe w v u

/-- A copy of the objects of a bicategory `B`, carrying the strict bicategory whose
`1`-morphisms are paths of `1`-morphisms of `B` and whose `2`-morphisms are the `2`-morphisms of
`B` between their evaluations. -/
structure Paths (B : Type u) where
  /-- The underlying object of `B`. -/
  as : B

namespace Paths

variable {B : Type u} [Bicategory.{w, v} B]

/-- The `1`-morphisms of `Paths B` are the paths of `1`-morphisms of `B`, composed by
concatenation. -/
instance : CategoryStruct.{max u v} (Paths B) where
  Hom x y := Path x.as y.as
  id x := Path.nil (a := x.as)
  comp p q := p.comp q

/-- The `2`-morphisms `p ⟶ q` of `Paths B` are the `2`-morphisms `p.eval ⟶ q.eval` of `B`. -/
instance homCategory (a b : Paths B) : Category.{w} (a ⟶ b) where
  Hom p q := Path.eval p ⟶ Path.eval q
  id p := 𝟙 (Path.eval p)
  comp θ θ' := θ ≫ θ'
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- The bicategory of paths: whiskering conjugates the whiskering of `B` by the comparisons
`Quiver.Path.evalComp`, and the associators and unitors are `eqToIso`s. -/
instance instBicategory : Bicategory.{w, max u v} (Paths B) where
  whiskerLeft p _ _ θ := Path.whiskerLeftEval p θ
  whiskerRight θ q := Path.whiskerRightEval θ q
  associator p q r := eqToIso (Path.comp_assoc p q r)
  leftUnitor p := eqToIso (Path.nil_comp p)
  rightUnitor p := eqToIso (Path.comp_nil p)
  -- The `2`-morphisms of `Paths B` are those of `B`, and `eqToHom` in `Paths B` unfolds to
  -- `eqToHom` in `B` along `congrArg Path.eval`, so the laws below are those of `Eval.lean`.
  whiskerLeft_id p q := Path.whiskerLeftEval_id p q
  whiskerLeft_comp p _ _ _ η θ := Path.whiskerLeftEval_comp p η θ
  id_whiskerLeft θ := Path.nil_whiskerLeftEval θ
  comp_whiskerLeft p q _ _ θ := Path.comp_whiskerLeftEval p q θ
  id_whiskerRight p q := Path.id_whiskerRightEval p q
  comp_whiskerRight η θ q := Path.comp_whiskerRightEval η θ q
  whiskerRight_id θ := Path.whiskerRightEval_nil θ
  whiskerRight_comp θ q r := Path.whiskerRightEval_comp θ q r
  whisker_assoc p _ _ θ r := Path.whiskerRightEval_whiskerLeftEval p θ r
  whisker_exchange η θ := Path.whiskerLeftEval_comp_whiskerRightEval η θ
  pentagon p q r s := by
    have h : Path.whiskerRightEval (eqToHom (congrArg Path.eval (Path.comp_assoc p q r))) s ≫
        eqToHom (congrArg Path.eval (Path.comp_assoc p (q.comp r) s)) ≫
          p.whiskerLeftEval (eqToHom (congrArg Path.eval (Path.comp_assoc q r s))) =
        eqToHom (congrArg Path.eval (Path.comp_assoc (p.comp q) r s)) ≫
          eqToHom (congrArg Path.eval (Path.comp_assoc p q (r.comp s))) := by
      simp
    exact h
  triangle p q := by
    have h : eqToHom (congrArg Path.eval (Path.comp_assoc p .nil q)) ≫
        p.whiskerLeftEval (eqToHom (congrArg Path.eval (Path.nil_comp q))) =
        Path.whiskerRightEval (eqToHom (congrArg Path.eval (Path.comp_nil p))) q := by
      -- `p.comp nil` is `p` by definition, so both sides are `eqToHom`s between the same paths.
      rw [Path.eqToHom_whiskerRightEval (Path.comp_nil p),
        Path.whiskerLeftEval_eqToHom _ (Path.nil_comp q), eqToHom_trans]
    exact h

/-- The bicategory of paths is strict: concatenation of paths is strictly associative and
unital, and the associators and unitors are `eqToIso`s. -/
instance instStrict : Bicategory.Strict (Paths B) where
  id_comp := Path.nil_comp
  comp_id := Path.comp_nil
  assoc := Path.comp_assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

variable {a b c : Paths B}

lemma id_def (a : Paths B) : 𝟙 a = (Path.nil : Path a.as a.as) := rfl

lemma comp_def (p : a ⟶ b) (q : b ⟶ c) : p ≫ q = Path.comp p q := rfl

lemma id₂_def (p : a ⟶ b) : 𝟙 p = 𝟙 (Path.eval p) := rfl

lemma comp₂_def {p q r : a ⟶ b} (θ : p ⟶ q) (θ' : q ⟶ r) :
    θ ≫ θ' = (θ ≫ θ' : Path.eval p ⟶ Path.eval r) := rfl

lemma whiskerLeft_def (p : a ⟶ b) {q q' : b ⟶ c} (θ : q ⟶ q') :
    p ◁ θ = Path.whiskerLeftEval p θ := rfl

lemma whiskerRight_def {p p' : a ⟶ b} (θ : p ⟶ p') (q : b ⟶ c) :
    θ ▷ q = Path.whiskerRightEval θ q := rfl

lemma eqToHom_def {p q : a ⟶ b} (h : p = q) :
    eqToHom h = eqToHom (congrArg Path.eval h) := by
  subst h; rfl

/-- The `2`-morphisms of `Paths B` between paths of length one are exactly the `2`-morphisms of
`B`. -/
example {x y : B} (f g : x ⟶ y) :
    Quiver.Hom (V := (⟨x⟩ : Paths B) ⟶ ⟨y⟩) f.toPath g.toPath = (f ⟶ g) := rfl

end Paths

end TauCeti.Bicategory
