/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Comparison
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

/-!
# Functors on `C × Bℕ` and lines

Let `C` be a category and `Bℕ = SingleObj (Multiplicative ℕ)` the one-object category of the
monoid `ℕ`. A functor on `C × Bℕ` is a functor on `C` together with an endomorphism, the action of
`1 ∈ ℕ`; a functor on `C` is read on `C × Bℕ` through `Prod.fst`, with `ℕ` acting trivially. A map
`a : Y ⟶ U` from a functor `Y` on `C × Bℕ` to a functor `U` on `C` is a *line* for coefficients
`F : C ⥤ AddCommGrpCat` (`CategoryTheory.IsLineFor F a`) if pulling back along `a` identifies the
cohomology `Extⁿ(ℤ[U], F)` of `U` on `C` with the cohomology `Extⁿ(ℤ[Y], F ∘ Prod.fst)` of `Y` on
`C × Bℕ`. Lines replace, one coordinate and one endomorphism at a time, the continuous cohomology
of `ℤ_p^d` in toric towers: the cohomology of the monoid `ℕ` acting through one endomorphism is
computed by the two-term Wang sequence (`CategoryTheory.Functor.wangSequence`).

The basic line is the projection `X × ℕ ⟶ X` (`CategoryTheory.isLineFor_prodNatFst`). It comes
from Shapiro's lemma for the monoid `ℕ`: the functor `N ↦ (ℕ →₀ N)` from functors on `C` to
functors on `C × Bℕ`, with `ℕ` translating the index, is exact and left adjoint to restriction
along `c ↦ (c, ⋆)`, so Mathlib's `CategoryTheory.Adjunction.extEquiv` identifies
`Extⁿ(ℕ →₀ N, F ∘ Prod.fst)` with `Extⁿ(N, F)`; and `ℤ[X × ℕ]` is `ℕ →₀ ℤ[X]`.

## Main definitions

* `CategoryTheory.prodNat C`: the functor `X ↦ X × ℕ` from functors on `C` to functors on
  `C × Bℕ`, and `CategoryTheory.Functor.prodNatFst X : X × ℕ ⟶ X`.
* `CategoryTheory.finsuppNat C`: the functor `N ↦ (ℕ →₀ N)`, left adjoint to restriction along
  `c ↦ (c, ⋆)` (`CategoryTheory.finsuppNatAdjunction`), with its augmentation
  `CategoryTheory.Functor.finsuppNatAugmentation N : (ℕ →₀ N) ⟶ N`.
* `CategoryTheory.IsLineFor F a`: `a` is a line for the coefficients `F`.

## Main results

* `CategoryTheory.Functor.isExtComparisonBijective_finsuppNatAugmentation`: Shapiro's lemma,
  `Extⁿ(N, F) ≃ Extⁿ(ℕ →₀ N, F ∘ Prod.fst)`.
* `CategoryTheory.isLineFor_prodNatFst`: the projection `X × ℕ ⟶ X` is a line for every
  coefficient functor.

## References

* G. Faltings, *p-adic Hodge theory*, J. Amer. Math. Soc. 1 (1988), and P. Scholze, *p-adic Hodge
  theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), Lemmas 4.5 and 5.5: the toric
  towers whose cohomology lines compute.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/ToricTower.lean` (declarations `New.Variety.TimesBNat`,
  `New.Variety.IsLine`, `New.Variety.TimesBNat.isLine_fst`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The definitions and the statement that the projection is a line are adapted from
  these declarations.
-/

public section

open CategoryTheory Limits Abelian
open scoped CategoryTheory.Prod

universe t t' w v u

local notation "Bℕ" => SingleObj (Multiplicative ℕ)
local notation "⋆" => SingleObj.star (Multiplicative ℕ)

namespace CategoryTheory

/-- The element of `ℕ` given by a morphism of `Bℕ` is additive along composition. -/
private lemma toAdd_comp {a b c : Bℕ} (f : a ⟶ b) (g : b ⟶ c) :
    Multiplicative.toAdd (α := ℕ) (f ≫ g) =
      Multiplicative.toAdd (α := ℕ) f + Multiplicative.toAdd (α := ℕ) g :=
  (toAdd_mul (α := ℕ) g f).trans (add_comm _ _)

/-- The identity of `Bℕ` is the element `0` of `ℕ`. -/
private lemma toAdd_id (a : Bℕ) : Multiplicative.toAdd (α := ℕ) (𝟙 a) = 0 := rfl

variable (C : Type u) [Category.{v} C]

/-- The functor `X ↦ X × ℕ` from functors on `C` to functors on `C × Bℕ`: `(X × ℕ)(c, ⋆)` is
`X(c) × ℕ`, a morphism `f` of `C` acting on the first factor through `X(f)` and `k ∈ ℕ` acting on
the second factor by translation `n ↦ n + k`. -/
@[expose]
def prodNat : (C ⥤ Type w) ⥤ C × Bℕ ⥤ Type w where
  obj X :=
    { obj c := X.obj c.1 × ℕ
      map {c d} f := ↾fun p ↦ (X.map f.1 p.1, p.2 + Multiplicative.toAdd f.2)
      map_id c := by
        ext p
        · simp
        · simp [toAdd_id]
      map_comp f g := by
        ext p
        · simp
        · simp [toAdd_comp, add_assoc] }
  map φ :=
    { app c := ↾fun p ↦ (φ.app c.1 p.1, p.2)
      naturality c d f := by
        ext p
        · simp [NatTrans.naturality_apply]
        · simp }

@[simp]
lemma prodNat_obj_obj (X : C ⥤ Type w) (c : C × Bℕ) :
    ((prodNat C).obj X).obj c = (X.obj c.1 × ℕ) :=
  rfl

variable {C} in
/-- `X × ℕ` acts on `(x, k)` through `X` and by translation of `k`. Not a `simp` lemma, as are none
of the lemmas below evaluating maps of `X × ℕ` and of `ℕ →₀ N` on elements: `simp` rewrites the
types in their left-hand sides. -/
lemma prodNat_obj_map_apply (X : C ⥤ Type w) {c d : C × Bℕ} (f : c ⟶ d) (x : X.obj c.1) (k : ℕ) :
    ((prodNat C).obj X).map f ((x, k) : ((prodNat C).obj X).obj c) =
      ((X.map f.1 x, k + Multiplicative.toAdd (α := ℕ) f.2) : ((prodNat C).obj X).obj d) :=
  rfl

variable {C} in
/-- `φ × ℕ` acts on `(x, k)` through `φ`. -/
lemma prodNat_map_app_apply {X X' : C ⥤ Type w} (φ : X ⟶ X') (c : C × Bℕ) (x : X.obj c.1)
    (k : ℕ) :
    ((prodNat C).map φ).app c ((x, k) : ((prodNat C).obj X).obj c) =
      ((φ.app c.1 x, k) : ((prodNat C).obj X').obj c) :=
  rfl

/-- The functor `N ↦ (ℕ →₀ N)` from functors on `C` to functors on `C × Bℕ`: `(ℕ →₀ N)(c, ⋆)` is
the group of finitely supported functions `ℕ → N(c)`, a morphism `f` of `C` acting through `N(f)`
and `k ∈ ℕ` by translation `n ↦ n + k` of the index. It is left adjoint to restriction along
`c ↦ (c, ⋆)` (`CategoryTheory.finsuppNatAdjunction`), and `ℤ[X × ℕ]` is `ℕ →₀ ℤ[X]`
(`CategoryTheory.Functor.prodNatCompFreeIso`). -/
@[expose]
noncomputable def finsuppNat : (C ⥤ AddCommGrpCat.{w}) ⥤ C × Bℕ ⥤ AddCommGrpCat.{w} where
  obj N :=
    { obj c := AddCommGrpCat.of (ℕ →₀ N.obj c.1)
      map {c d} f := AddCommGrpCat.ofHom ((Finsupp.mapRange.addMonoidHom (N.map f.1).hom).comp
        (Finsupp.mapDomain.addMonoidHom (· + Multiplicative.toAdd f.2)))
      map_id c := by
        ext : 1
        refine Finsupp.addHom_ext fun k a ↦ ?_
        simp [toAdd_id]
      map_comp f g := by
        ext : 1
        refine Finsupp.addHom_ext fun k a ↦ ?_
        simp [toAdd_comp, add_assoc] }
  map φ :=
    { app c := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom (φ.app c.1).hom)
      naturality c d f := by
        ext : 1
        refine Finsupp.addHom_ext fun k a ↦ ?_
        simp [NatTrans.naturality_apply] }

variable {C}

/-- `(ℕ →₀ N)` acts on a coefficient `single k a` through `N` and by translation of `k`. -/
@[simp]
lemma finsuppNat_obj_map_single (N : C ⥤ AddCommGrpCat.{w}) {c d : C × Bℕ} (f : c ⟶ d) (k : ℕ)
    (a : N.obj c.1) :
    ((finsuppNat C).obj N).map f (Finsupp.single k a : ((finsuppNat C).obj N).obj c) =
      (Finsupp.single (k + Multiplicative.toAdd (α := ℕ) f.2) (N.map f.1 a) :
        ((finsuppNat C).obj N).obj d) :=
  (congrArg (Finsupp.mapRange.addMonoidHom (N.map f.1).hom) Finsupp.mapDomain_single).trans
    (Finsupp.mapRange_single (hf := map_zero _))

@[simp]
lemma finsuppNat_map_app_single {N N' : C ⥤ AddCommGrpCat.{w}} (φ : N ⟶ N') (c : C × Bℕ)
    (k : ℕ) (a : N.obj c.1) :
    ((finsuppNat C).map φ).app c (Finsupp.single k a : ((finsuppNat C).obj N).obj c) =
      (Finsupp.single k (φ.app c.1 a) : ((finsuppNat C).obj N').obj c) :=
  Finsupp.mapRange_single (hf := map_zero _)

/-- Two maps out of `ℕ →₀ N` agree if they agree on the coefficients `single k a`. -/
lemma finsuppNat_hom_ext {N : C ⥤ AddCommGrpCat.{w}} {M : C × Bℕ ⥤ AddCommGrpCat.{w}}
    {f g : (finsuppNat C).obj N ⟶ M}
    (h : ∀ (c : C × Bℕ) (k : ℕ) (a : N.obj c.1),
      f.app c (Finsupp.single k a : ((finsuppNat C).obj N).obj c) =
        g.app c (Finsupp.single k a : ((finsuppNat C).obj N).obj c)) :
    f = g :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext (Finsupp.addHom_ext (h c)))

/-- The functor `N ↦ (ℕ →₀ N)` is additive. -/
instance : (finsuppNat C).Additive where
  map_add {N N' φ ψ} := NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
    -- The components are, by definition, homomorphisms of finitely supported functions; `show`
    -- states the identity on these types, where `simp` applies.
    (show Finsupp.mapRange.addMonoidHom ((φ.app c.1).hom + (ψ.app c.1).hom) =
        Finsupp.mapRange.addMonoidHom (φ.app c.1).hom +
          Finsupp.mapRange.addMonoidHom (ψ.app c.1).hom from
      Finsupp.addHom_ext fun k a ↦ by simp [Finsupp.single_add]))

/-- The functor `N ↦ (ℕ →₀ N)` is exact: at every object it is `A ↦ (ℕ →₀ A)`, which preserves
exactness of sequences of abelian groups. -/
private lemma finsuppNat_exact :
    PreservesFiniteLimits (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) ∧
      PreservesFiniteColimits (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) :=
  Functor.preservesFiniteLimits_and_preservesFiniteColimits_of_function_exact _
    fun (S : ShortComplex (C ⥤ AddCommGrpCat.{w})) hS (c : C × Bℕ) y ↦ by
      have h := (ShortComplex.exact_iff_forall_function_exact S).1 hS c.1
      -- At `c`, the two maps are, by definition, `Finsupp.mapRange` of the components of `S` at
      -- `c.1`.
      change Finsupp.mapRange (S.g.app c.1) (map_zero _) y = 0 ↔
        y ∈ Set.range (Finsupp.mapRange (S.f.app c.1) (map_zero _))
      rw [Finsupp.range_mapRange, Finsupp.ext_iff]
      exact forall_congr' fun k ↦ h _

instance : PreservesFiniteLimits (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) :=
  finsuppNat_exact.1

instance : PreservesFiniteColimits (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) :=
  finsuppNat_exact.2

/-- A functor on `C × Bℕ` sends `𝟙 c ×ₘ 𝟙 a` to the identity. -/
private lemma map_id_prod_id_apply (M : C × Bℕ ⥤ AddCommGrpCat.{w}) (c : C) (a : Bℕ)
    (x : M.obj (c, a)) : M.map (𝟙 c ×ₘ 𝟙 a) x = x := by
  rw [← prod_id, M.map_id]
  rfl

/-- Naturality of the counit of `finsuppNatAdjunction`, on the underlying group homomorphisms:
sending the coefficient of `k` through the action of `k` commutes with the action of `f`. -/
private lemma liftAddHom_comp_finsuppNat_map (M : C × Bℕ ⥤ AddCommGrpCat.{w}) {c d : C × Bℕ}
    (f : c ⟶ d) :
    (Finsupp.liftAddHom fun k ↦ (M.map (𝟙 d.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ d.2))).hom).comp
        ((Finsupp.mapRange.addMonoidHom (M.map (f.1 ×ₘ 𝟙 ⋆)).hom).comp
          (Finsupp.mapDomain.addMonoidHom (· + Multiplicative.toAdd f.2))) =
      (M.map f).hom.comp
        (Finsupp.liftAddHom fun k ↦ (M.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2))).hom) :=
  Finsupp.addHom_ext fun k a ↦ by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      Finsupp.liftAddHom_apply_single]
    have h : (f.1 ×ₘ 𝟙 ⋆) ≫
        (𝟙 d.1 ×ₘ (Multiplicative.ofAdd (k + Multiplicative.toAdd f.2) : ⋆ ⟶ d.2)) =
        (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2)) ≫ f :=
      Prod.hom_ext (by simp) (Multiplicative.toAdd.injective (by simp [toAdd_comp]))
    rw [← ConcreteCategory.comp_apply, ← M.map_comp, h, M.map_comp, ConcreteCategory.comp_apply]

variable (C) in
/-- The functor `N ↦ (ℕ →₀ N)` is left adjoint to restriction along `c ↦ (c, ⋆)`: the unit puts an
element in the coefficient of `0`, and the counit sends the coefficient of `k` through the action
of `k`. -/
noncomputable def finsuppNatAdjunction :
    (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) ⊣
      (Functor.whiskeringLeft C (C × Bℕ) AddCommGrpCat.{w}).obj
        (Prod.sectL C ⋆) where
  -- The naturality conditions and triangle identities are checked on the underlying homomorphisms
  -- of finitely supported functions, which the components are by definition: `show` states them
  -- on these types, where `simp` applies.
  unit :=
    { app N :=
        { app c := AddCommGrpCat.ofHom (Finsupp.singleAddHom 0)
          naturality c d f := AddCommGrpCat.ext fun a ↦
            (finsuppNat_obj_map_single N (c := (c, ⋆)) (f ×ₘ 𝟙 _) 0 a).symm }
      naturality N N' φ := NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
        (show (Finsupp.singleAddHom 0).comp (φ.app c).hom =
            (Finsupp.mapRange.addMonoidHom (φ.app c).hom).comp (Finsupp.singleAddHom 0) from
          AddMonoidHom.ext fun a ↦ by simp)) }
  counit :=
    { app M :=
        { app c := AddCommGrpCat.ofHom (Finsupp.liftAddHom fun k ↦
            (M.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2))).hom)
          naturality c d f := AddCommGrpCat.hom_ext (liftAddHom_comp_finsuppNat_map M f) }
      naturality M M' φ := NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
        (show (Finsupp.liftAddHom fun k ↦
              (M'.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2))).hom).comp
            (Finsupp.mapRange.addMonoidHom (φ.app (c.1, ⋆)).hom) =
          (φ.app c).hom.comp (Finsupp.liftAddHom fun k ↦
            (M.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2))).hom) from
          Finsupp.addHom_ext fun k a ↦ by simp [NatTrans.naturality_apply])) }
  left_triangle_components N := NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
    (show (Finsupp.liftAddHom fun k ↦ (Finsupp.mapRange.addMonoidHom (N.map (𝟙 c.1)).hom).comp
          (Finsupp.mapDomain.addMonoidHom (· + k))).comp
        (Finsupp.mapRange.addMonoidHom (Finsupp.singleAddHom 0)) = AddMonoidHom.id _ from
      Finsupp.addHom_ext fun k a ↦ by simp))
  right_triangle_components M := NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
    (show (Finsupp.liftAddHom fun k ↦
          (M.map (𝟙 c ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ ⋆))).hom).comp
        (Finsupp.singleAddHom 0) = AddMonoidHom.id _ from
      AddMonoidHom.ext fun a ↦ (Finsupp.liftAddHom_apply_single _ _ _).trans
        (map_id_prod_id_apply M c _ a)))

/-- The unit of `finsuppNatAdjunction` puts an element in the coefficient of `0`. -/
lemma finsuppNatAdjunction_unit_app_app_apply (N : C ⥤ AddCommGrpCat.{w}) (c : C) (a : N.obj c) :
    ((finsuppNatAdjunction C).unit.app N).app c a =
      (Finsupp.single 0 a : ((finsuppNat C).obj N).obj (c, ⋆)) :=
  (rfl)

/-- The counit of `finsuppNatAdjunction` sends the coefficient of `k` through the action of `k`. -/
lemma finsuppNatAdjunction_counit_app_app_single (M : C × Bℕ ⥤ AddCommGrpCat.{w}) (c : C × Bℕ)
    (k : ℕ) (a : M.obj (c.1, ⋆)) :
    ((finsuppNatAdjunction C).counit.app M).app c
        (Finsupp.single k a :
          ((finsuppNat C).obj (Prod.sectL C ⋆ ⋙ M)).obj c) =
      M.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2)) a :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The *augmentation* `(ℕ →₀ N) ⟶ N`, which adds up the coefficients, to `N` read on `C × Bℕ`
with `ℕ` acting trivially. -/
@[expose]
noncomputable def Functor.finsuppNatAugmentation (N : C ⥤ AddCommGrpCat.{w}) :
    (finsuppNat C).obj N ⟶ Prod.fst C Bℕ ⋙ N where
  app _ := AddCommGrpCat.ofHom (Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id _)
  naturality c d f := AddCommGrpCat.hom_ext (Finsupp.addHom_ext fun k a ↦
    (congrArg (Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id (N.obj d.1))
      (finsuppNat_obj_map_single N f k a)).trans ((Finsupp.liftAddHom_apply_single _ _ _).trans
        (congrArg (N.map f.1) (Finsupp.liftAddHom_apply_single
          (fun _ ↦ AddMonoidHom.id (N.obj c.1)) k a)).symm))

/-- The augmentation sends the coefficient `single k a` to `a`. -/
lemma Functor.finsuppNatAugmentation_app_single (N : C ⥤ AddCommGrpCat.{w}) (c : C × Bℕ)
    (k : ℕ) (a : N.obj c.1) :
    N.finsuppNatAugmentation.app c (Finsupp.single k a : ((finsuppNat C).obj N).obj c) = a :=
  Finsupp.liftAddHom_apply_single (fun _ ↦ AddMonoidHom.id (N.obj c.1)) k a

/-- The unit of `finsuppNatAdjunction` followed by the augmentation is the identity. -/
lemma finsuppNatAdjunction_unit_app_comp_finsuppNatAugmentation
    (N : C ⥤ AddCommGrpCat.{w}) :
    (finsuppNatAdjunction C).unit.app N ≫
      (Prod.sectL C ⋆).whiskerLeft N.finsuppNatAugmentation = 𝟙 N :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.ext fun a ↦
    Finsupp.liftAddHom_apply_single (fun _ ↦ AddMonoidHom.id (N.obj c)) 0 a)

/-- The projection `X × ℕ ⟶ X` from the functor `X × ℕ` on `C × Bℕ` to `X` read on `C × Bℕ` with
`ℕ` acting trivially. -/
@[expose]
def Functor.prodNatFst (X : C ⥤ Type w) : (prodNat C).obj X ⟶ Prod.fst C Bℕ ⋙ X where
  app _ := ↾fun p ↦ p.1

/-- The projection sends `(x, k)` to `x`. -/
lemma Functor.prodNatFst_app_apply (X : C ⥤ Type w) (c : C × Bℕ) (x : X.obj c.1) (k : ℕ) :
    X.prodNatFst.app c ((x, k) : ((prodNat C).obj X).obj c) = x :=
  rfl

/-- The free abelian functor on `X × ℕ` is `ℕ →₀ ℤ[X]`, the generator of `(x, k)` corresponding to
the coefficient `single k x`. -/
noncomputable def Functor.prodNatCompFreeIso (X : C ⥤ Type w) :
    (prodNat C).obj X ⋙ AddCommGrpCat.free ≅ (finsuppNat C).obj (X ⋙ AddCommGrpCat.free) :=
  NatIso.ofComponents (fun c ↦ AddEquiv.toAddCommGrpIso
    (AddMonoidHom.toAddEquiv (M := FreeAddCommGroup (X.obj c.1 × ℕ))
      (N := ℕ →₀ FreeAddCommGroup (X.obj c.1))
      (FreeAddCommGroup.lift fun p : X.obj c.1 × ℕ ↦ Finsupp.single p.2 (FreeAddCommGroup.of p.1))
      (Finsupp.liftAddHom fun k ↦ FreeAddCommGroup.map (·, k))
      (by ext; simp) (Finsupp.addHom_ext' fun k ↦ by ext; simp)))
    (fun {c d} f ↦ AddCommGrpCat.hom_ext
      -- The components are, by definition, homomorphisms of free abelian groups and finitely
      -- supported functions; `show` states naturality on these types, where `simp` applies.
      (show (FreeAddCommGroup.lift fun p : X.obj d.1 × ℕ ↦
            Finsupp.single p.2 (FreeAddCommGroup.of p.1)).comp
          (FreeAddCommGroup.map fun p : X.obj c.1 × ℕ ↦
            (X.map f.1 p.1, p.2 + Multiplicative.toAdd f.2)) =
        ((Finsupp.mapRange.addMonoidHom (FreeAddCommGroup.map (X.map f.1))).comp
          (Finsupp.mapDomain.addMonoidHom (· + Multiplicative.toAdd f.2))).comp
          (FreeAddCommGroup.lift fun p : X.obj c.1 × ℕ ↦
            Finsupp.single p.2 (FreeAddCommGroup.of p.1)) from by ext; simp))

/-- The generator of `(x, k)` corresponds to the coefficient `single k x`. -/
lemma Functor.prodNatCompFreeIso_hom_app_of (X : C ⥤ Type w) (c : C × Bℕ) (x : X.obj c.1)
    (k : ℕ) :
    X.prodNatCompFreeIso.hom.app c (FreeAddCommGroup.of (x, k)) =
      (Finsupp.single k (FreeAddCommGroup.of x) :
        ((finsuppNat C).obj (X ⋙ AddCommGrpCat.free)).obj c) :=
  FreeAddCommGroup.lift_apply_of _ _

/-- Under `prodNatCompFreeIso`, the augmentation becomes the projection `X × ℕ ⟶ X`. -/
lemma Functor.prodNatCompFreeIso_hom_comp_finsuppNatAugmentation (X : C ⥤ Type w) :
    X.prodNatCompFreeIso.hom ≫ (X ⋙ AddCommGrpCat.free).finsuppNatAugmentation =
      Functor.whiskerRight X.prodNatFst AddCommGrpCat.free :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext
    -- The components are, by definition, homomorphisms of free abelian groups and finitely
    -- supported functions; `show` states the identity on these types, where `simp` applies.
    (show (Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id (FreeAddCommGroup (X.obj c.1))).comp
        (FreeAddCommGroup.lift fun p : X.obj c.1 × ℕ ↦
          Finsupp.single p.2 (FreeAddCommGroup.of p.1)) =
      FreeAddCommGroup.map fun p : X.obj c.1 × ℕ ↦ p.1 from by ext; simp))

section Ext

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})]

/-- **Shapiro's lemma for `ℕ`.** For functors `N, F : C ⥤ AddCommGrpCat`, restriction along
`Prod.fst : C × Bℕ ⥤ C` followed by pull-back along the augmentation `(ℕ →₀ N) ⟶ N` is a
bijection `Extⁿ(N, F) ≃ Extⁿ(ℕ →₀ N, F)`, the right side computed on `C × Bℕ`. -/
theorem Functor.isExtComparisonBijective_finsuppNatAugmentation
    (N F : C ⥤ AddCommGrpCat.{w}) :
    Functor.IsExtComparisonBijective.{t, t'} (Prod.fst C Bℕ) (𝟙 (Prod.fst C Bℕ ⋙ F))
      N.finsuppNatAugmentation := (Functor.isExtComparisonBijective_iff _ _ _).2 fun n ↦ by
  let adj : (finsuppNat C : (C ⥤ AddCommGrpCat.{w}) ⥤ _) ⊣ _ := finsuppNatAdjunction C
  -- The bijection `adj.extEquiv` is the comparison map along `c ↦ (c, ⋆)` with the unit.
  have h₁ (y : Ext.{t'} ((finsuppNat C).obj N) (Prod.fst C Bℕ ⋙ F) n) :
      adj.extEquiv y = Functor.extComparison (Prod.sectL C ⋆) (𝟙 _)
        (adj.unit.app N) n y := by
    rw [Adjunction.extEquiv_apply, Functor.extComparison_apply]
    congr 1
    exact (Ext.comp_mk₀_id _).symm
  -- Composed with it, the comparison map along `Prod.fst` is the identity.
  have h (x : Ext.{t} N F n) :
      adj.extEquiv (Functor.extComparison (Prod.fst C Bℕ) (𝟙 _) N.finsuppNatAugmentation n x) =
        x := by
    rw [h₁, Functor.extComparison_extComparison,
      finsuppNatAdjunction_unit_app_comp_finsuppNatAugmentation]
    exact (Functor.extComparison_id_apply (𝟙 F) (𝟙 N) x).trans (by simp)
  refine (adj.extEquiv.bijective.of_comp_iff' _).1 ?_
  exact ⟨fun x y hxy ↦ (h x).symm.trans (hxy.trans (h y)), fun y ↦ ⟨y, h y⟩⟩

/-- A map `a : Y ⟶ U` from a functor on `C × Bℕ` to a functor `U` on `C`, read on `C × Bℕ` with `ℕ`
acting trivially, is a *line* for the coefficients `F : C ⥤ AddCommGrpCat` if restriction along
`Prod.fst : C × Bℕ ⥤ C` followed by pull-back along `ℤ[a]`,
`Extⁿ(ℤ[U], F) ⟶ Extⁿ(ℤ[Y], F ∘ Prod.fst)`, is bijective for every `n`, the left side computed on
`C` and the right side on `C × Bℕ`. -/
def IsLineFor (F : C ⥤ AddCommGrpCat.{w}) {Y : C × Bℕ ⥤ Type w} {U : C ⥤ Type w}
    (a : Y ⟶ Prod.fst C Bℕ ⋙ U) : Prop :=
  Functor.IsExtComparisonBijective.{t, t'} (N := U ⋙ AddCommGrpCat.free) (Prod.fst C Bℕ)
    (𝟙 (Prod.fst C Bℕ ⋙ F)) (Functor.whiskerRight a AddCommGrpCat.free)

/-- `a` is a line for `F` exactly when its comparison maps are bijective in every degree. -/
lemma isLineFor_iff (F : C ⥤ AddCommGrpCat.{w}) {Y : C × Bℕ ⥤ Type w} {U : C ⥤ Type w}
    (a : Y ⟶ Prod.fst C Bℕ ⋙ U) :
    IsLineFor.{t, t'} F a ↔ ∀ n, Function.Bijective (Functor.extComparison.{t, t'}
      (N := U ⋙ AddCommGrpCat.free) (Prod.fst C Bℕ) (𝟙 (Prod.fst C Bℕ ⋙ F))
      (Functor.whiskerRight a AddCommGrpCat.free) n) :=
  Functor.isExtComparisonBijective_iff _ _ _

/-- **The projection `X × ℕ ⟶ X` is a line** for every coefficient functor. -/
theorem isLineFor_prodNatFst (F : C ⥤ AddCommGrpCat.{w}) (X : C ⥤ Type w) :
    IsLineFor.{t, t'} F X.prodNatFst := by
  refine (isLineFor_iff F _).2 fun n ↦ ?_
  let e := X.prodNatCompFreeIso
  -- The comparison map along the projection is the one along the augmentation, followed by
  -- pull-back along the isomorphism `e`.
  have hcomm : e.hom ≫ (X ⋙ AddCommGrpCat.free).finsuppNatAugmentation =
      Functor.whiskerRight X.prodNatFst AddCommGrpCat.free ≫
        (Prod.fst C Bℕ).whiskerLeft (𝟙 (X ⋙ AddCommGrpCat.free)) := by
    rw [Functor.prodNatCompFreeIso_hom_comp_finsuppNatAugmentation, Functor.whiskerLeft_id']
    exact (Category.comp_id _).symm
  have h (x : Ext.{t} (X ⋙ AddCommGrpCat.free) F n) :
      Functor.extComparison (N := X ⋙ AddCommGrpCat.free) (Prod.fst C Bℕ)
        (𝟙 (Prod.fst C Bℕ ⋙ F)) (Functor.whiskerRight X.prodNatFst AddCommGrpCat.free) n x =
      (Ext.mk₀ e.hom).comp (Functor.extComparison.{t, t'} (Prod.fst C Bℕ) (𝟙 _)
        (X ⋙ AddCommGrpCat.free).finsuppNatAugmentation n x) (zero_add n) := by
    rw [Functor.mk₀_comp_extComparison _ _ hcomm, Ext.mk₀_id_comp]
  have hb : Function.Bijective fun y : Ext.{t'} ((finsuppNat C).obj (X ⋙ AddCommGrpCat.free))
      (Prod.fst C Bℕ ⋙ F) n ↦ (Ext.mk₀ e.hom).comp y (zero_add n) :=
    Function.bijective_iff_has_inverse.2 ⟨fun y ↦ (Ext.mk₀ e.inv).comp y (zero_add n),
      fun y ↦ by simp [Ext.mk₀_comp_mk₀_assoc], fun y ↦ by simp [Ext.mk₀_comp_mk₀_assoc]⟩
  rw [show ⇑(Functor.extComparison (N := X ⋙ AddCommGrpCat.free) (Prod.fst C Bℕ)
      (𝟙 (Prod.fst C Bℕ ⋙ F)) (Functor.whiskerRight X.prodNatFst AddCommGrpCat.free) n) =
      _ ∘ _ from funext h]
  exact hb.comp ((Functor.isExtComparisonBijective_iff _ _ _).1
    (Functor.isExtComparisonBijective_finsuppNatAugmentation _ _) n)

end Ext

end CategoryTheory
