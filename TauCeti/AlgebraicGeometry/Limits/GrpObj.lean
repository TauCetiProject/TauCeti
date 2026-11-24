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

## Main results

* `CategoryTheory.Limits.IsLimit.exists_grpObj_overPullback`: a group law on the base change to
  `S` of a finitely presented scheme `X` over `Dᵢ` is, after replacing `Dᵢ` by some `Dⱼ`, the base
  change of a group law on the base change of `X` to `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_grpObj_pullback_iso`: **spreading out group schemes**. A
  group scheme of finite presentation over `S` is isomorphic, as a group scheme, to the base change
  of a group scheme of finite presentation over some `Dⱼ`.

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
    LiftsAlong c (Functor.OplaxMonoidal.η (Over.pullback (c.π.app i)) ≫
      η[(Over.pullback (c.π.app i)).obj X]),
    LiftsAlong c (δ (Over.pullback (c.π.app i)) X X ≫ μ[(Over.pullback (c.π.app i)).obj X]),
    LiftsAlong c ι[(Over.pullback (c.π.app i)).obj X]]
  obtain ⟨j, g, hg⟩ := IsCofiltered.exists_forall_of_stable (R := R)
    (by intro n; fin_cases n <;> exact fun h hg ↦ hg.comp h)
    (by intro n; fin_cases n <;> exact hc.exists_overPullback_map_comp_eq _)
  obtain ⟨vo, hvo⟩ := (liftsAlong_iff _ _).mp (hg 0)
  obtain ⟨vm, hvm⟩ := (liftsAlong_iff _ _).mp (hg 1)
  obtain ⟨vi, hvi⟩ := (liftsAlong_iff _ _).mp (hg 2)
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
  -- The group law over `Dₖ`, on the iterated base change and transported to the direct one. The
  -- structures are restated on the objects written as images under composite functors, as which
  -- they occur in the sources of the comparison isomorphisms.
  let S : GrpObj ((Over.pullback (D.map h)).obj ((Over.pullback (D.map g)).obj X)) :=
    (Over.pullback (D.map h)).grpObjObjOfMap one mul inv e₁ e₂ e₃ e₄ e₅
  let S' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X) := S
  let T' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  let G : GrpObj ((Over.pullback (D.map (h ≫ g))).obj X) := .ofIso (C.app X)
  refine ⟨G, ?_⟩
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
        ((Over.pullback (D.map g) ⋙ Over.pullback (D.map h)).obj X)) (hG := T'.toMonObj)
      (one := one) (mul := mul) _ ?_ ?_ h_one h_mul <;> simp [S', S]
  infer_instance

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
  have h_one' : (Over.pullback (c.π.app j)).map one = Functor.OplaxMonoidal.η _ ≫
      η[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    rw [toUnit_unique (Functor.OplaxMonoidal.η _) (toUnit _), MonObj.ofIso_one, ← Category.assoc,
      ← h_one]
    simp
  have h_mul' : (Over.pullback (c.π.app j)).map mul =
      δ _ _ _ ≫ μ[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    simp only [T, MonObj.ofIso_mul, Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    rw [← reassoc_of% h_mul]
    simp
  have h_inv' : (Over.pullback (c.π.app j)).map inv =
      ι[(Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X)] := by
    simp only [T, GrpObj.ofIso_inv, Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    rw [← Category.assoc, ← h_inv]
    simp
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
  let T' : GrpObj ((Over.pullback (D.map g) ⋙ Over.pullback (c.π.app j)).obj X) := T
  have : IsMonHom (M := (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj X))
      ((Over.pullbackCompIsoOfEq (c.w g)).hom.app X) :=
    inferInstanceAs (IsMonHom ((Over.pullbackCompIsoOfEq (c.w g)).app X).symm.inv)
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

end GrpObj

end CategoryTheory.Limits.IsLimit
