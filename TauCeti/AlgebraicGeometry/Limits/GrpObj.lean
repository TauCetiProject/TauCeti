/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Descent
public import TauCeti.AlgebraicGeometry.Morphisms.QuasiCompact.Over
public import TauCeti.CategoryTheory.Filtered.Basic
public import TauCeti.CategoryTheory.Monoidal.Grp.OfMap

/-!
# Spreading out group schemes along cofiltered limits

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps. A scheme `X` of finite presentation over `S` is the base change of a scheme
of finite presentation over some member `Dᵢ`
(`CategoryTheory.Limits.IsLimit.exists_isPullback_of_finitePresentation`, Stacks 01ZM). This file
shows that a group law spreads out along with the scheme: a group scheme of finite presentation over
`S` is the base change of a group scheme of finite presentation over some member of the diagram, by
an isomorphism of group schemes.

Group schemes over a base are group objects in the cartesian monoidal category of schemes over it,
and base change is the monoidal functor `Over.pullback`. The unit, the multiplication and the
inverse of a group law over `S` descend to morphisms over some member `Dⱼ`
(`CategoryTheory.Limits.IsLimit.exists_overPullback_map_comp_eq`), and each group axiom, an
equality of morphisms over `Dⱼ` which holds over `S`, holds over some later member `Dₖ`
(`CategoryTheory.Limits.IsLimit.exists_overPullback_map_eq_map`). Over `Dₖ` the base changes of the
descended morphisms are then a group law (`CategoryTheory.Functor.grpObjObjOfMap`) whose base
change to `S` is the given one.

Homomorphisms spread out in the same way. A morphism `f` of monoid objects is a homomorphism when
it is compatible with the units and with the multiplications, two equalities of morphisms, and its
image under a monoidal functor is a homomorphism exactly when the images of these equalities hold
(`CategoryTheory.Functor.isMonHom_map_iff_map_eq`). If the base change of `f` to `S` is a
homomorphism, these equalities therefore hold over some member. Together with the spreading out of
group laws, this spreads out a group law on the base change to `S` of a finitely presented scheme
`H` over a member along with the homomorphism property of a morphism `H ⟶ G` over that member.
When `H ⟶ G` is a monomorphism, for instance the inclusion of a closed subscheme, this spreads out
a subgroup of the base change of `G` to `S` which is the base change of a subscheme over a member.

## Main results

* `CategoryTheory.Limits.IsLimit.exists_grpObj_overPullback`: a group law on the base change to
  `S` of a finitely presented scheme `X` over `Dᵢ` is, after replacing `Dᵢ` by some `Dⱼ`, the base
  change of a group law on the base change of `X` to `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_grpObj_pullback_iso`: **spreading out group schemes**. A
  group scheme of finite presentation over `S` is isomorphic, as a group scheme, to the base change
  of a group scheme of finite presentation over some `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_isMonHom_overPullback_map`: a morphism of monoid objects
  over `Dᵢ` whose base change to `S` is a homomorphism has a homomorphism as base change to some
  `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_grpObj_isMonHom_overPullback`: a group law on the base
  change to `S` of a finitely presented scheme `H` over `Dᵢ`, for which the base change of a
  morphism `H ⟶ G` to a monoid object over `Dᵢ` is a homomorphism, is the base change of a group
  law over some `Dⱼ` for which the base change of `H ⟶ G` is a homomorphism.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.8.
* The Stacks Project, [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM) and
  [Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Obj

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

section GrpObj

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- The unit, the multiplication and the inverse of a group law on the base change of `X` to the
cone point lift to candidate structure morphisms on the base change of `X` to some member of the
diagram. -/
private theorem exists_lifts {i : I} (X : Over (D.obj i)) [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [GrpObj ((Over.pullback (c.π.app i)).obj X)] :
    ∃ (j : I) (g : j ⟶ i) (one : 𝟙_ _ ⟶ (Over.pullback (D.map g)).obj X)
      (mul : (Over.pullback (D.map g)).obj X ⊗ (Over.pullback (D.map g)).obj X ⟶
        (Over.pullback (D.map g)).obj X)
      (inv : (Over.pullback (D.map g)).obj X ⟶ (Over.pullback (D.map g)).obj X),
      (Over.pullback (c.π.app j)).map one ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          toUnit _ ≫ η[(Over.pullback (c.π.app i)).obj X] ∧
        (Over.pullback (c.π.app j)).map mul ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          δ (Over.pullback (c.π.app j)) ((Over.pullback (D.map g)).obj X)
            ((Over.pullback (D.map g)).obj X) ≫
            ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X ⊗ₘ
              (Over.pullbackCompIsoOfEq (c.w g)).hom.app X) ≫
              μ[(Over.pullback (c.π.app i)).obj X] ∧
        (Over.pullback (c.π.app j)).map inv ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app X =
          (Over.pullbackCompIsoOfEq (c.w g)).hom.app X ≫
            ι[(Over.pullback (c.π.app i)).obj X] := by
  -- Lift the three structure morphisms, each along some morphism to `i`, then along a common one.
  let R : Fin 3 → ∀ {k : I}, (k ⟶ i) → Prop := ![
    c.LiftsAlong (Functor.OplaxMonoidal.η (Over.pullback (c.π.app i)) ≫
      η[(Over.pullback (c.π.app i)).obj X]),
    c.LiftsAlong (δ (Over.pullback (c.π.app i)) X X ≫ μ[(Over.pullback (c.π.app i)).obj X]),
    c.LiftsAlong ι[(Over.pullback (c.π.app i)).obj X]]
  obtain ⟨j, g, hg⟩ := IsCofiltered.exists_forall_of_stable (R := R)
    (by intro n; fin_cases n <;> exact fun h hg ↦ hg.precomp h)
    (by intro n; fin_cases n <;> exact hc.exists_overPullback_map_comp_eq _)
  obtain ⟨vo, hvo⟩ := (Cone.liftsAlong_iff _ _).mp (hg 0)
  obtain ⟨vm, hvm⟩ := (Cone.liftsAlong_iff _ _).mp (hg 1)
  obtain ⟨vi, hvi⟩ := (Cone.liftsAlong_iff _ _).mp (hg 2)
  refine ⟨j, g, ε _ ≫ vo, Functor.LaxMonoidal.μ _ X X ≫ vm, vi, ?_, ?_, hvi⟩
  · rw [Functor.map_comp, Category.assoc, hvo, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ η[(Over.pullback (c.π.app i)).obj X]) (toUnit_unique _ _)
  · rw [Functor.map_comp, Category.assoc, hvm]
    have ht := NatTrans.IsMonoidal.tensor
      (τ := (Over.pullbackCompIsoOfEq (c.w g)).hom) X X
    dsimp only [Functor.LaxMonoidal.comp_μ] at ht
    rw [← cancel_epi (Functor.LaxMonoidal.μ (Over.pullback (c.π.app j))
      ((Over.pullback (D.map g)).obj X) ((Over.pullback (D.map g)).obj X))]
    simpa only [Category.assoc, Functor.Monoidal.μ_δ_assoc] using
      congrArg (· ≫ δ (Over.pullback (c.π.app i)) X X ≫
        μ[(Over.pullback (c.π.app i)).obj X]) ht

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- Candidate group structure morphisms on a scheme of finite type over a member of the diagram
which satisfy the group axioms after base change to the cone point satisfy them after base change
to some later member. -/
private theorem exists_map_axioms {j : I} (Y : Over (D.obj j)) [QuasiCompact Y.hom]
    [LocallyOfFiniteType Y.hom] (one : 𝟙_ _ ⟶ Y) (mul : Y ⊗ Y ⟶ Y) (inv : Y ⟶ Y)
    (h_one_mul : (Over.pullback (c.π.app j)).map (one ▷ Y ≫ mul) =
      (Over.pullback (c.π.app j)).map (λ_ Y).hom)
    (h_mul_one : (Over.pullback (c.π.app j)).map (Y ◁ one ≫ mul) =
      (Over.pullback (c.π.app j)).map (ρ_ Y).hom)
    (h_mul_assoc : (Over.pullback (c.π.app j)).map (mul ▷ Y ≫ mul) =
      (Over.pullback (c.π.app j)).map ((α_ Y Y Y).hom ≫ Y ◁ mul ≫ mul))
    (h_left_inv : (Over.pullback (c.π.app j)).map
      (CartesianMonoidalCategory.lift inv (𝟙 Y) ≫ mul) =
        (Over.pullback (c.π.app j)).map (toUnit Y ≫ one))
    (h_right_inv : (Over.pullback (c.π.app j)).map
      (CartesianMonoidalCategory.lift (𝟙 Y) inv ≫ mul) =
        (Over.pullback (c.π.app j)).map (toUnit Y ≫ one)) :
    ∃ (k : I) (h : k ⟶ j),
      (Over.pullback (D.map h)).map (one ▷ Y ≫ mul) = (Over.pullback (D.map h)).map (λ_ Y).hom ∧
      (Over.pullback (D.map h)).map (Y ◁ one ≫ mul) = (Over.pullback (D.map h)).map (ρ_ Y).hom ∧
      (Over.pullback (D.map h)).map (mul ▷ Y ≫ mul) =
        (Over.pullback (D.map h)).map ((α_ Y Y Y).hom ≫ Y ◁ mul ≫ mul) ∧
      (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift inv (𝟙 Y) ≫ mul) =
        (Over.pullback (D.map h)).map (toUnit Y ≫ one) ∧
      (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift (𝟙 Y) inv ≫ mul) =
        (Over.pullback (D.map h)).map (toUnit Y ≫ one) := by
  -- Equality after base change along `g` persists after base change along `h ≫ g`.
  have stable {A B : Over (D.obj j)} {u v : A ⟶ B} {k l : I} {g : k ⟶ j} (h : l ⟶ k)
      (e : (Over.pullback (D.map g)).map u = (Over.pullback (D.map g)).map v) :
      (Over.pullback (D.map (h ≫ g))).map u = (Over.pullback (D.map (h ≫ g))).map v :=
    Over.pullback_map_eq_map_of_comp_eq (D.map_comp h g).symm e
  -- Each axiom holds along some morphism to `j`; combine them along a common one.
  let R : Fin 5 → ∀ {k : I}, (k ⟶ j) → Prop := ![
    fun h ↦ (Over.pullback (D.map h)).map (one ▷ Y ≫ mul) =
      (Over.pullback (D.map h)).map (λ_ Y).hom,
    fun h ↦ (Over.pullback (D.map h)).map (Y ◁ one ≫ mul) =
      (Over.pullback (D.map h)).map (ρ_ Y).hom,
    fun h ↦ (Over.pullback (D.map h)).map (mul ▷ Y ≫ mul) =
      (Over.pullback (D.map h)).map ((α_ Y Y Y).hom ≫ Y ◁ mul ≫ mul),
    fun h ↦ (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift inv (𝟙 Y) ≫ mul) =
      (Over.pullback (D.map h)).map (toUnit Y ≫ one),
    fun h ↦ (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift (𝟙 Y) inv ≫ mul) =
      (Over.pullback (D.map h)).map (toUnit Y ≫ one)]
  obtain ⟨k, h, hh⟩ := IsCofiltered.exists_forall_of_stable (R := R)
    (by intro n; fin_cases n <;> exact fun h e ↦ stable h e)
    (by
      intro n
      fin_cases n
      · exact hc.exists_overPullback_map_eq_map _ _ h_one_mul
      · exact hc.exists_overPullback_map_eq_map _ _ h_mul_one
      · exact hc.exists_overPullback_map_eq_map _ _ h_mul_assoc
      · exact hc.exists_overPullback_map_eq_map _ _ h_left_inv
      · exact hc.exists_overPullback_map_eq_map _ _ h_right_inv)
  exact ⟨k, h, hh 0, hh 1, hh 2, hh 3, hh 4⟩

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Let `Y = X ×_{Dᵢ} Dⱼ` carry candidate unit and multiplication morphisms `one` and `mul`. Let
`T` be a monoid structure on the base change of `Y` to the cone point with the base changes of
`one` and `mul` as unit and multiplication, for which the identification with the base change of
`X` is a homomorphism to a given monoid structure, and let `S` be a monoid structure on the base
change of `Y` along `h : k ⟶ j` with the same property. Transported to `X ×_{Dᵢ} Dₖ`, the base
change of `S` to the cone point is identified with the base change of `X` by a homomorphism. -/
private theorem isMonHom_pullbackCompIsoOfEq_hom_app_ofIso {i j k : I} (X : Over (D.obj i))
    [MonObj ((Over.pullback (c.π.app i)).obj X)] (g : j ⟶ i) (h : k ⟶ j)
    (one : 𝟙_ _ ⟶ (Over.pullback (D.map g)).obj X)
    (mul : (Over.pullback (D.map g)).obj X ⊗ (Over.pullback (D.map g)).obj X ⟶
      (Over.pullback (D.map g)).obj X)
    [S : MonObj ((Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X))]
    (hS_one : η[(Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)] =
      ε _ ≫ (Over.pullback (D.map h)).map one)
    (hS_mul : μ[(Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)] =
      Functor.LaxMonoidal.μ _ _ _ ≫ (Over.pullback (D.map h)).map mul)
    [T : MonObj ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))]
    (hT_one : η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      ε _ ≫ (Over.pullback (c.π.app j)).map one)
    (hT_mul : μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      Functor.LaxMonoidal.μ _ _ _ ≫ (Over.pullback (c.π.app j)).map mul)
    (hT : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X)) :
    letI : MonObj ((Over.pullback (D.map (h ≫ g))).obj X) :=
      .ofIso (M := (Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X))
        ((Over.pullbackCompIsoOfEq (D.map_comp h g).symm).app X)
    IsMonHom (M := (Over.pullback (c.π.app k)).obj ((Over.pullback (D.map (h ≫ g))).obj X))
      ((Over.pullbackCompIsoOfEq (c.w (h ≫ g))).hom.app X) := by
  -- The structures are restated on the objects written as images under composite functors, as
  -- which they occur in the sources of the comparison isomorphisms.
  let S' : MonObj ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) := S
  let T' : MonObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  let : MonObj ((Over.pullback (D.map (h ≫ g))).obj X) :=
    .ofIso (M := (Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)) (C.app X)
  -- The comparison to the cone point factors through the comparisons along `h` and along `g`.
  rw [Over.pullbackCompIsoOfEq_hom_app_eq (c.w h) (D.map_comp h g).symm (c.w g) (c.w (h ≫ g)) X]
  have : IsMonHom (M := (Over.pullback (D.map (h ≫ g))).obj X)
      (N := (Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) (C.inv.app X) :=
    inferInstanceAs (IsMonHom (C.app X).inv)
  have : IsMonHom (M := (Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X)
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X) := hT
  have : IsMonHom (M := (Over.pullback (c.π.app k)).obj
        ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X))
      (N := (Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X)
      ((Over.pullbackCompIsoOfEq (c.w h)).hom.app ((Over.pullback (D.map g)).obj X)) := by
    refine NatTrans.isMonHom_app (F := Over.pullback (D.map h) ⋙ Over.pullback (c.π.app k))
      (G := Over.pullback (c.π.app j)) (X := (Over.pullback (D.map g)).obj X)
      (hF := Functor.monObjObj (F := Over.pullback (c.π.app k))
        ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X)) (hG := T')
      (one := one) (mul := mul) _ ?_ ?_ hT_one hT_mul <;> simp [S', hS_one, hS_mul]
  infer_instance

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Let `Y = X ×_{Dᵢ} Dⱼ` carry candidate group structure morphisms, and let its base change to the
cone point carry a group law whose unit and multiplication are their base changes, such that the
identification with the base change of `X` is a homomorphism to a given group law. If the group
axioms hold for the candidates after base change along `h : k ⟶ j`, then their base changes are a
group law on `X ×_{Dᵢ} Dₖ` whose base change to the cone point is the given one. -/
private theorem exists_grpObj_of_map_axioms {i j k : I} (X : Over (D.obj i))
    [GrpObj ((Over.pullback (c.π.app i)).obj X)] (g : j ⟶ i) (h : k ⟶ j)
    (one : 𝟙_ _ ⟶ (Over.pullback (D.map g)).obj X)
    (mul : (Over.pullback (D.map g)).obj X ⊗ (Over.pullback (D.map g)).obj X ⟶
      (Over.pullback (D.map g)).obj X)
    (inv : (Over.pullback (D.map g)).obj X ⟶ (Over.pullback (D.map g)).obj X)
    [T : GrpObj ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))]
    (h_one : η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      ε _ ≫ (Over.pullback (c.π.app j)).map one)
    (h_mul : μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] =
      Functor.LaxMonoidal.μ _ _ _ ≫ (Over.pullback (c.π.app j)).map mul)
    [hT : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X)]
    (e₁ : (Over.pullback (D.map h)).map (one ▷ _ ≫ mul) =
      (Over.pullback (D.map h)).map (λ_ _).hom)
    (e₂ : (Over.pullback (D.map h)).map (_ ◁ one ≫ mul) =
      (Over.pullback (D.map h)).map (ρ_ _).hom)
    (e₃ : (Over.pullback (D.map h)).map (mul ▷ _ ≫ mul) =
      (Over.pullback (D.map h)).map ((α_ _ _ _).hom ≫ _ ◁ mul ≫ mul))
    (e₄ : (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift inv (𝟙 _) ≫ mul) =
      (Over.pullback (D.map h)).map (toUnit _ ≫ one))
    (e₅ : (Over.pullback (D.map h)).map (CartesianMonoidalCategory.lift (𝟙 _) inv ≫ mul) =
      (Over.pullback (D.map h)).map (toUnit _ ≫ one)) :
    ∃ (_ : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X)),
      IsMonHom (M := (Over.pullback (c.π.app k)).obj ((Over.pullback (D.map (h ≫ g))).obj X))
        ((Over.pullbackCompIsoOfEq (c.w (h ≫ g))).hom.app X) := by
  -- The group law over `Dₖ`, on the iterated base change and transported to the direct one.
  let S : GrpObj ((Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)) :=
    (Over.pullback (D.map h)).grpObjObjOfMap one mul inv e₁ e₂ e₃ e₄ e₅
  exact ⟨.ofIso (G := (Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (D.map_comp h g).symm).app X),
    isMonHom_pullbackCompIsoOfEq_hom_app_ofIso X g h one mul (S := S.toMonObj) (by simp [S])
      (by simp [S]) (T := T.toMonObj) h_one h_mul hT⟩

include hc in
/-- **Spreading out a group law.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, and let `X` be a scheme of finite presentation,
quasi-compact and quasi-separated over a member `Dᵢ`. A group law on the base change `X ×_{Dᵢ} S`
over `S` is the base change of a group law on `X ×_{Dᵢ} Dⱼ` over some `Dⱼ`: the identification
`(X ×_{Dᵢ} Dⱼ) ×_{Dⱼ} S ≅ X ×_{Dᵢ} S` is an isomorphism of group schemes. -/
theorem exists_grpObj_overPullback {i : I} (X : Over (D.obj i))
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [GrpObj ((Over.pullback (c.π.app i)).obj X)] :
    ∃ (j : I) (f : j ⟶ i) (_ : GrpObj ((Over.pullback (D.map f)).obj X)),
      IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map f)).obj X))
        ((Over.pullbackCompIsoOfEq (c.w f)).hom.app X) := by
  obtain ⟨j, g, one, mul, inv, h_one, h_mul, h_inv⟩ := hc.exists_lifts X
  -- The given group law, transported to the base change to the cone point of `X ×_{Dᵢ} Dⱼ`.
  let T : GrpObj ((Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)) :=
    .ofIso ((Over.pullbackCompIsoOfEq (c.w g)).app X).symm
  -- The transported law, restated on the source of the comparison isomorphism.
  let T' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  -- The comparison is a homomorphism for the transported law; cancel it in each lift equation.
  have : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X) :=
    inferInstanceAs (IsMonHom ((Over.pullbackCompIsoOfEq (c.w g)).app X).symm.inv)
  have h_one' : (Over.pullback (c.π.app j)).map one = Functor.OplaxMonoidal.η _ ≫
      η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_one, Category.assoc,
      IsMonHom.one_hom, toUnit_unique (toUnit _) (Functor.OplaxMonoidal.η _)]
  have h_mul' : (Over.pullback (c.π.app j)).map mul =
      δ _ _ _ ≫ μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_mul, Category.assoc,
      IsMonHom.mul_hom]
  have h_inv' : (Over.pullback (c.π.app j)).map inv =
      ι[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [← cancel_mono ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X), h_inv, GrpObj.inv_hom]
  have : QuasiCompact ((Over.pullback (D.map g)).obj X).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (QuasiCompact (pullback.snd X.hom (D.map g))))
  have : LocallyOfFiniteType ((Over.pullback (D.map g)).obj X).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom (D.map g))))
  obtain ⟨k, h, e₁, e₂, e₃, e₄, e₅⟩ := hc.exists_map_axioms ((Over.pullback (D.map g)).obj X)
    one mul inv ((Over.pullback (c.π.app j)).map_one_mul h_one' h_mul')
    ((Over.pullback (c.π.app j)).map_mul_one h_one' h_mul')
    ((Over.pullback (c.π.app j)).map_mul_assoc h_mul')
    ((Over.pullback (c.π.app j)).map_left_inv h_one' h_mul' h_inv')
    ((Over.pullback (c.π.app j)).map_right_inv h_one' h_mul' h_inv')
  exact ⟨k, h ≫ g, exists_grpObj_of_map_axioms X g h one mul inv
    (by rw [h_one', Functor.Monoidal.ε_η_assoc]) (by rw [h_mul', Functor.Monoidal.μ_δ_assoc])
    e₁ e₂ e₃ e₄ e₅⟩

include hc in
/-- **Spreading out group schemes.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps. A group scheme `G` over `S` which is of finite
presentation, quasi-compact and quasi-separated over `S` is isomorphic, as a group scheme over `S`,
to the base change of a group scheme of finite presentation, quasi-compact and quasi-separated over
some member `Dⱼ`. -/
theorem exists_grpObj_pullback_iso (G : Over c.pt) [GrpObj G]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom] [QuasiSeparated G.hom] :
    ∃ (j : I) (Y : Over (D.obj j)) (_ : GrpObj Y) (e : (Over.pullback (c.π.app j)).obj Y ≅ G),
      LocallyOfFinitePresentation Y.hom ∧ QuasiCompact Y.hom ∧ QuasiSeparated Y.hom ∧
        IsMonHom e.hom := by
  obtain ⟨i, X, p, _, _, _, a, sq⟩ :=
    hc.exists_isPullback_of_finitePresentation (IsCofiltered.nonempty (C := I)).some G.hom
  let e₀ : (Over.pullback (c.π.app i)).obj (Over.mk p) ≅ G :=
    Over.isoMk sq.isoPullback.symm (by simp)
  let : GrpObj ((Over.pullback (c.π.app i)).obj (Over.mk p)) := .ofIso e₀.symm
  have : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e₀.symm.inv)
  have : LocallyOfFinitePresentation (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹LocallyOfFinitePresentation p›
  have : QuasiCompact (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹QuasiCompact p›
  have : QuasiSeparated (Over.mk p).hom := by
    simpa only [Over.mk_hom] using ‹QuasiSeparated p›
  obtain ⟨j, f, _, hf⟩ := hc.exists_grpObj_overPullback (Over.mk p)
  have : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map f)).obj (Over.mk p)))
      ((Over.pullbackCompIsoOfEq (c.w f)).app (Over.mk p)).hom := hf
  exact ⟨j, (Over.pullback (D.map f)).obj (Over.mk p), inferInstance,
    (Over.pullbackCompIsoOfEq (c.w f)).app (Over.mk p) ≪≫ e₀,
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p (D.map f))))),
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (QuasiCompact (pullback.snd p (D.map f))))),
    (by simpa only [Over.pullback_obj_hom, Over.mk_hom] using
      (inferInstanceAs (QuasiSeparated (pullback.snd p (D.map f))))),
    inferInstanceAs (IsMonHom (M := (Over.pullback (c.π.app j)).obj
      ((Over.pullback (D.map f)).obj (Over.mk p))) (_ ≫ e₀.hom))⟩

include hc in
omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- **Spreading out homomorphisms.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, and let `f : X ⟶ Y` be a morphism of monoid
objects over a member `Dᵢ`, with `X` quasi-compact and `Y` locally of finite type over `Dᵢ`. If the
base change of `f` to `S` is a homomorphism, then so is its base change to some `Dⱼ`. -/
theorem exists_isMonHom_overPullback_map {i : I} {X Y : Over (D.obj i)} [MonObj X] [MonObj Y]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [IsMonHom ((Over.pullback (c.π.app i)).map f)] :
    ∃ (j : I) (g : j ⟶ i), IsMonHom ((Over.pullback (D.map g)).map f) := by
  obtain ⟨h_one, h_mul⟩ := ((Over.pullback (c.π.app i)).isMonHom_map_iff_map_eq f).mp inferInstance
  -- Each homomorphism equation holds after base change to some member; combine them.
  obtain ⟨j, g, e_one, e_mul⟩ := IsCofiltered.exists_and_of_stable
    (R₁ := fun g ↦ (Over.pullback (D.map g)).map (η[X] ≫ f) = (Over.pullback (D.map g)).map η[Y])
    (R₂ := fun g ↦ (Over.pullback (D.map g)).map (μ[X] ≫ f) =
      (Over.pullback (D.map g)).map ((f ⊗ₘ f) ≫ μ[Y]))
    (fun h e ↦ Over.pullback_map_eq_map_of_comp_eq (D.map_comp h _).symm e)
    (fun h e ↦ Over.pullback_map_eq_map_of_comp_eq (D.map_comp h _).symm e)
    (hc.exists_overPullback_map_eq_map _ _ h_one) (hc.exists_overPullback_map_eq_map _ _ h_mul)
  exact ⟨j, g, ((Over.pullback (D.map g)).isMonHom_map_iff_map_eq f).mpr ⟨e_one, e_mul⟩⟩

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Let `X ×_{Dᵢ} Dⱼ` carry a group law whose base change to the cone point is a given group law,
and let `f : X ⟶ G` be a morphism to a monoid object over `Dᵢ` whose base change to `Dⱼ` becomes
a homomorphism after further base change along `h : k ⟶ j`. Then `X ×_{Dᵢ} Dₖ` carries a group law
whose base change to the cone point is the given one, and for which the base change of `f` is a
homomorphism. -/
private theorem exists_grpObj_isMonHom_of_isMonHom_overPullback_map {i j k : I}
    {X G : Over (D.obj i)} [MonObj G] (f : X ⟶ G) (g : j ⟶ i) (h : k ⟶ j)
    [GrpObj ((Over.pullback (c.π.app i)).obj X)] [T : GrpObj ((Over.pullback (D.map g)).obj X)]
    (hT : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X))
    (hf : IsMonHom ((Over.pullback (D.map h)).map ((Over.pullback (D.map g)).map f))) :
    ∃ (_ : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X)),
      IsMonHom ((Over.pullback (D.map (h ≫ g))).map f) ∧
        IsMonHom (M := (Over.pullback (c.π.app k)).obj ((Over.pullback (D.map (h ≫ g))).obj X))
          ((Over.pullbackCompIsoOfEq (c.w (h ≫ g))).hom.app X) := by
  -- The group law over `Dₖ`: the base change of `T`, transported to the direct base change.
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  let S : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) :=
    Functor.grpObjObj (F := Over.pullback (D.map h)) (G := (Over.pullback (D.map g)).obj X)
  let G' : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X) := .ofIso (C.app X)
  refine ⟨G', ?_, ?_⟩
  · -- The base change of `f` along `h ≫ g` is that along `g` and `h`, up to the comparisons.
    have : IsMonHom (M := (Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj G))
        (C.app G).hom :=
      NatTrans.isMonHom_app (F := Over.pullback (D.map g) ⋙ Over.pullback (D.map h))
        (G := Over.pullback (D.map (h ≫ g))) (X := G)
        (hF := Functor.monObjObj (F := Over.pullback (D.map h)) ((Over.pullback (D.map g)).obj G))
        (one := η[G]) (mul := μ[G]) C.hom (by simp) (by simp) (by simp) (by simp)
    have e : (Over.pullback (D.map (h ≫ g))).map f =
        (C.app X).inv ≫ (Over.pullback (D.map h)).map ((Over.pullback (D.map g)).map f) ≫
          (C.app G).hom := by
      rw [Iso.app_inv, Iso.app_hom, ← Functor.comp_map, C.hom.naturality,
        Iso.inv_hom_id_app_assoc]
    rw [e]
    infer_instance
  · exact isMonHom_pullbackCompIsoOfEq_hom_app_ofIso X g h η[(Over.pullback (D.map g)).obj X]
      μ[(Over.pullback (D.map g)).obj X] (S := S.toMonObj) (by simp [S]) (by simp [S])
      (T := (Functor.grpObjObj (F := Over.pullback (c.π.app j))).toMonObj) (by simp) (by simp) hT

include hc in
/-- **Spreading out homomorphisms from a group scheme over the limit.** Let `S = lim Dⱼ` be a
cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps, let `H` be a
scheme of finite presentation, quasi-compact and quasi-separated over a member `Dᵢ`, and let
`f : H ⟶ G` be a morphism to a monoid object `G` locally of finite type over `Dᵢ`. If the base
change `H ×_{Dᵢ} S` carries a group law for which the base change of `f` is a homomorphism, then
over some `Dⱼ` the base change `H ×_{Dᵢ} Dⱼ` carries a group law whose base change to `S` is the
given one, and for which the base change of `f` is a homomorphism. For a monomorphism `f` this
spreads out a subgroup of `G ×_{Dᵢ} S`. -/
theorem exists_grpObj_isMonHom_overPullback {i : I} {H G : Over (D.obj i)}
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom] [QuasiSeparated H.hom]
    [LocallyOfFiniteType G.hom] [MonObj G] (f : H ⟶ G)
    [GrpObj ((Over.pullback (c.π.app i)).obj H)] [IsMonHom ((Over.pullback (c.π.app i)).map f)] :
    ∃ (j : I) (g : j ⟶ i) (_ : GrpObj ((Over.pullback (D.map g)).obj H)),
      IsMonHom ((Over.pullback (D.map g)).map f) ∧
        IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj H))
          ((Over.pullbackCompIsoOfEq (c.w g)).hom.app H) := by
  obtain ⟨j, g, T, hT⟩ := hc.exists_grpObj_overPullback H
  let C := Over.pullbackCompIsoOfEq (c.w g)
  -- The comparison of the two base changes of `G` to `S` is a homomorphism.
  have hCG : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj G))
      (C.app G).hom :=
    NatTrans.isMonHom_app (F := Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j))
      (G := Over.pullback (c.π.app i)) (X := G)
      (hF := Functor.monObjObj (F := Over.pullback (c.π.app j)) ((Over.pullback (D.map g)).obj G))
      (one := η[G]) (mul := μ[G]) C.hom (by simp) (by simp) (by simp) (by simp)
  -- So the base change to `S` of the base change of `f` to `Dⱼ` is a homomorphism.
  have : IsMonHom ((Over.pullback (c.π.app j)).map ((Over.pullback (D.map g)).map f)) := by
    have e : (Over.pullback (c.π.app j)).map ((Over.pullback (D.map g)).map f) =
        C.hom.app H ≫ (Over.pullback (c.π.app i)).map f ≫ (C.app G).inv := by
      rw [Iso.app_inv, ← Functor.comp_map, ← Category.assoc, ← C.hom.naturality,
        Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [e]
    infer_instance
  have : QuasiCompact ((Over.pullback (D.map g)).obj H).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (QuasiCompact (pullback.snd H.hom (D.map g))))
  have : LocallyOfFiniteType ((Over.pullback (D.map g)).obj G).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (D.map g))))
  obtain ⟨k, h, hh⟩ := hc.exists_isMonHom_overPullback_map ((Over.pullback (D.map g)).map f)
  exact ⟨k, h ≫ g, exists_grpObj_isMonHom_of_isMonHom_overPullback_map f g h hT hh⟩

end GrpObj

end CategoryTheory.Limits.IsLimit
