/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Total Ext groups and the Yoneda product

For objects `X` and `Y` of an abelian category, the *total Ext group*
`CategoryTheory.Abelian.TotalExt X Y` is the direct sum `⨁ n, Extⁿ(X, Y)`. The Yoneda composition
of homogeneous classes extends biadditively to a product
`TotalExt X Y →+ TotalExt Y Z →+ TotalExt X Z` (`CategoryTheory.Abelian.TotalExt.comp`), written in
diagram order: `comp x y` is `x` followed by `y`. It is associative and unital, and a morphism
`f : X ⟶ Y` gives the class `TotalExt.mk₀ f` of degree zero, so that pull-back and push-forward
become products with classes of degree zero and degrees need no tracking.

An exact functor `G` acts on total Ext groups (`CategoryTheory.Abelian.TotalExt.map`) compatibly
with products (`CategoryTheory.Abelian.TotalExt.map_comp`), with composition of functors, and with
natural transformations (`CategoryTheory.Abelian.TotalExt.comp_map_mk₀`).

The long exact sequence of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in the first variable
becomes, in all degrees at once, an exact triangle
`TotalExt X₃ Y ⟶ TotalExt X₂ Y ⟶ TotalExt X₁ Y ⟶ TotalExt X₃ Y` of the two pull-backs and of the
product with the extension class (`CategoryTheory.Abelian.TotalExt.exact_triangle`).

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (declarations `New.Variety.TotalH`,
  `New.Variety.TotalH.comp`, `New.Variety.TotalH.comp_assoc`, `New.Variety.TotalH.map`,
  `New.Variety.TotalH.map_comp`, `New.Variety.TotalH.naturality`,
  `New.Variety.TotalH.exact_precomp`, `New.Variety.TotalH.exact_triangle`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The definitions and results are adapted from these declarations,
  stated here for an arbitrary abelian category.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Section 3.4 (Yoneda Ext and its products).
-/

public section

open CategoryTheory Limits DirectSum

universe w w' w'' v u v' u'

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The total Ext group `⨁ n, Extⁿ(X, Y)`. -/
abbrev TotalExt (X Y : C) : Type w := ⨁ n : ℕ, Ext.{w} X Y n

namespace TotalExt

variable {X Y Z T : C}

/-- The Yoneda product of total Ext groups, in diagram order: the biadditive extension of the
compositions `Extᵃ(X, Y) × Extᵇ(Y, Z) ⟶ Extᵃ⁺ᵇ(X, Z)`. -/
noncomputable def comp : TotalExt X Y →+ TotalExt Y Z →+ TotalExt X Z :=
  toAddMonoid fun a ↦ (toAddMonoid fun b ↦
    ((Ext.bilinearComp X Y Z a b (a + b) rfl).compr₂
      (of (fun n ↦ Ext.{w} X Z n) (a + b))).flip).flip

/-- On homogeneous classes the product is the Yoneda composition. -/
@[simp]
lemma comp_of_of {a b c : ℕ} (x : Ext.{w} X Y a) (y : Ext.{w} Y Z b) (h : a + b = c) :
    comp (of _ a x) (of _ b y) = of _ c (x.comp y h) := by
  subst h
  simp [comp]

/-- The Yoneda product of total Ext groups is associative. -/
lemma comp_assoc (x : TotalExt X Y) (y : TotalExt Y Z) (z : TotalExt Z T) :
    comp (comp x y) z = comp x (comp y z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp_all
  | of c z =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp_all
    | of b y =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | add x x' hx hx' => simp_all
      | of a x =>
        simp only [comp_of_of x y rfl, comp_of_of y z rfl, comp_of_of _ z rfl,
          comp_of_of x _ (add_assoc a b c).symm]
        exact congrArg _ (Ext.comp_assoc x y z rfl rfl rfl)

/-- The class of degree zero of a morphism. -/
noncomputable abbrev mk₀ (f : X ⟶ Y) : TotalExt X Y := of _ 0 (Ext.mk₀ f)

/-- The class of a composite is the product of the classes. -/
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk₀ f) (mk₀ g) = mk₀ (f ≫ g) := by
  simp

/-- The class of the identity is a right unit for the product. -/
@[simp]
lemma comp_mk₀_id (x : TotalExt X Y) : comp x (mk₀ (𝟙 Y)) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp [Ext.comp_mk₀_id]

/-- The class of the identity is a left unit for the product. -/
@[simp]
lemma mk₀_id_comp (x : TotalExt X Y) : comp (mk₀ (𝟙 X)) x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp [Ext.mk₀_id_comp]

/-- The product with the class of a morphism on the left is precomposition in every degree. -/
lemma mk₀_comp (f : X ⟶ Y) (x : TotalExt Y Z) :
    comp (mk₀ f) x = DirectSum.map (fun n ↦ (Ext.mk₀ f).precomp Z (zero_add n)) x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp

/-! ### Exact functors -/

section Map

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {E : Type*} [Category* E] [Abelian E] [HasExt.{w''} E]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An exact functor acts on total Ext groups, degree by degree. The total Ext groups of the
source and of the target may live in different universes. -/
noncomputable def map : TotalExt.{w} X Y →+ TotalExt.{w'} (G.obj X) (G.obj Y) :=
  DirectSum.map (G.mapExtAddHom X Y)

/-- On homogeneous classes `map G` is the image of the class under `G`. -/
@[simp]
lemma map_of {a : ℕ} (x : Ext.{w} X Y a) : map G (of _ a x) = of _ a (x.mapExactFunctor G) := by
  simp [map]

/-- An exact functor sends the class of a morphism to the class of its image. -/
lemma map_mk₀ (f : X ⟶ Y) : map G (mk₀ f) = mk₀ (G.map f) := by
  simp [Ext.mapExactFunctor_mk₀]

/-- An exact functor respects Yoneda products. -/
lemma map_comp (x : TotalExt X Y) (y : TotalExt Y Z) :
    map G (comp x y) = comp (map G x) (map G y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp_all
    | of b y => simp [Ext.mapExactFunctor_comp]

/-- The identity functor acts trivially on total Ext groups. Not a `simp` lemma, unlike
Mathlib's `Ext.id_mapExactFunctor`: `TotalExt.map` is a bundled additive map, so `simp` first
rewrites the type of the coercion through `Functor.id_obj`, and the simpNF linter rejects the
left-hand side. -/
lemma map_id (x : TotalExt X Y) : map (𝟭 C) x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x =>
    rw [map_of, Ext.id_mapExactFunctor]
    -- `(𝟭 C).obj X` and `(𝟭 C).obj Y` are `X` and `Y` by definition.
    rfl

/-- The action of a composite of exact functors is the composite of the actions. -/
lemma map_map (G' : D ⥤ E) [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (x : TotalExt X Y) : map G' (map G x) = map (G ⋙ G') x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp [Ext.comp_mapExactFunctor]

/-- Naturality in the functor: for a natural transformation `τ : G ⟶ G'` of exact functors,
pushing `G x` forward along `τ` equals pulling `G' x` back along `τ`. -/
lemma comp_map_mk₀ {G' : C ⥤ D} [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] (τ : G ⟶ G') (x : TotalExt X Y) :
    comp (map G x) (mk₀ (τ.app Y)) = comp (mk₀ (τ.app X)) (map G' x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all
  | of a x => simp [Ext.mapExactFunctor_comp_mk₀_natTransApp]

end Map

/-! ### The exact triangle -/

section Triangle

variable {M N F G : C}

/-- The degree-`m` component of a product `comp (of e ξ) y` with a homogeneous class on the left
is the composite of `ξ` with the degree-`n` component of `y`, where `e + n = m`. -/
lemma comp_of_apply {e n m : ℕ} (ξ : Ext.{w} G M e) (y : TotalExt M F) (h : e + n = m) :
    comp (of _ e ξ) y m = ξ.comp (y n) h := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
  | of i w =>
    rw [comp_of_of ξ w rfl]
    obtain rfl | hi := eq_or_ne i n
    · subst h
      simp
    · rw [of_eq_of_ne _ _ _ (show m ≠ e + i by lia), of_eq_of_ne _ _ _ (Ne.symm hi),
        Ext.comp_zero]

/-- Exactness of products with homogeneous classes is tested degree by degree. Let `ξ` be a class
in `Extᵉ(M, N)` and `ζ` a class in `Extᵇ(G, M)` with `ζ · ξ = 0`, and suppose that every
homogeneous class `y` in `Ext(M, F)` with `ζ · y = 0` is zero or of the form `ξ · x`. Then the
product with `ξ` followed by the product with `ζ` is exact at `TotalExt M F`. -/
lemma exact_comp_of_of {e b : ℕ} {ξ : Ext.{w} M N e} {ζ : Ext.{w} G M b}
    (hξζ : ζ.comp ξ rfl = 0)
    (hker : ∀ (n m : ℕ) (hm : b + n = m) (y : Ext.{w} M F n), ζ.comp y hm = 0 →
      y = 0 ∨ ∃ (a : ℕ) (ha : e + a = n) (x : Ext.{w} N F a), ξ.comp x ha = y) :
    Function.Exact (comp (Z := F) (of _ e ξ)) (comp (of _ b ζ)) := by
  classical
  refine Function.Exact.of_comp_of_mem_range (funext fun x ↦ ?_) fun y hy ↦ ?_
  · simp [← comp_assoc, comp_of_of ζ ξ rfl, hξζ]
  rw [← sum_support_of y]
  refine (comp (of _ e ξ)).range.sum_mem fun n _ ↦ ?_
  rcases hker n _ rfl (y n) (by rw [← comp_of_apply ζ y rfl, hy]; rfl) with h | ⟨a, ha, x, hx⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨of _ a x, by rw [← hx, comp_of_of]⟩

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
include hS

/-- **The exact triangle.** For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with extension class
`e ∈ Ext¹(X₃, X₁)`, the sequence
`TotalExt X₃ Y ⟶ TotalExt X₂ Y ⟶ TotalExt X₁ Y ⟶ TotalExt X₃ Y` of the pull-backs along `X₂ ⟶ X₃`
and `X₁ ⟶ X₂` and of the product with `e` is exact at each of its three places. -/
theorem exact_triangle :
    Function.Exact (comp (Z := Y) (mk₀ S.g)) (comp (mk₀ S.f)) ∧
    Function.Exact (comp (Z := Y) (mk₀ S.f)) (comp (of _ 1 hS.extClass)) ∧
    Function.Exact (comp (Z := Y) (of _ 1 hS.extClass)) (comp (mk₀ S.g)) := by
  refine ⟨exact_comp_of_of (by simp) fun n m hm y hy ↦ ?_,
    exact_comp_of_of (by simp) fun n m hm y hy ↦ ?_,
    exact_comp_of_of (by simp) fun n m hm y hy ↦ ?_⟩
  · obtain rfl : n = m := by lia
    exact .inr ⟨n, zero_add n, Ext.contravariant_sequence_exact₂ hS Y y hy⟩
  · obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS Y y hm hy
    exact .inr ⟨n, zero_add n, x, hx⟩
  · obtain rfl : n = m := by lia
    cases n with
    | zero =>
      have := hS.epi_g
      exact .inl (Ext.precomp_mk₀_injective_of_epi Y S.g (by simpa using hy))
    | succ n =>
      obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y y hy (add_comm 1 n)
      exact .inr ⟨n, add_comm 1 n, x, hx⟩

end Triangle

end TotalExt

end CategoryTheory.Abelian
