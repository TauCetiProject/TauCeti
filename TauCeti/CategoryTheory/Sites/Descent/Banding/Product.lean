/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.Pi
public import TauCeti.CategoryTheory.Pi.Basic
public import TauCeti.CategoryTheory.Sites.Descent.Banding
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Products of bandings

Let `F i`, for `i : I`, be a family of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` on a site
`(C, J)` and `TauCeti.Stack.pi F` their product, whose fibre over `U` is the product of the fibres
of the `F i`. If `b i` is an `A i`-banding of `F i` and `hc` exhibits a fan `c` as a limit of the
sheaves of abelian groups `A i` (for instance `limit.isLimit` for the product `∏ᶜ A`, or, for two
factors indexed by `WalkingPair`, for `A ⨯ B`), then the product carries the `c.pt`-banding
`CategoryTheory.Pseudofunctor.AbelianBanding.pi b hc`: the band automorphism of a section `a` of
`c.pt` at a family `x` of objects is the family of the band automorphisms of the projections of `a`
at the `x i`. With it:

* the projections `π F i : pi F ⟶ F i` are compatible with the projections `c.proj i` of the fan
  (`TauCeti.Stack.pi.bandCompatible_π`), and a transformation into the product is compatible with
  a morphism into `c.pt` if and only if its projections are compatible with the projections of the
  morphism (`TauCeti.Stack.pi.bandCompatible_iff_comp_π`);
* the strong transformation into the product induced by transformations `a i : K ⟶ F i`
  compatible with morphisms `φ i : B ⟶ A i` is compatible with the induced morphism `B ⟶ c.pt`
  (`TauCeti.Stack.pi.bandCompatible_lift`);
* the product of band-preserving transformations preserves the product bands
  (`TauCeti.Stack.pi.bandPreserving_piMap`), and more generally the product of transformations
  compatible with morphisms `φ i : A i ⟶ A' i` is compatible with the product of the `φ i`
  (`TauCeti.Stack.pi.bandCompatible_piMap`).

When `I` is finite and the `F i` are gerbes, the product is a gerbe
(`TauCeti.Stack.pi.isGerbe`, in `TauCeti.CategoryTheory.Sites.Descent.Gerbe.Product`).

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding.pi`: the product banding.
* `TauCeti.Stack.pi.bandCompatible_π`, `TauCeti.Stack.pi.bandCompatible_iff_comp_π`,
  `TauCeti.Stack.pi.bandCompatible_lift`, `TauCeti.Stack.pi.bandCompatible_piMap`,
  `TauCeti.Stack.pi.bandPreserving_piMap`: compatibility of the projections, of transformations
  into the product, of induced transformations and of products of transformations with the bands.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1
-/

public section

universe w t v u v' u'

open CategoryTheory Limits Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open TauCeti.Stack

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {I : Type w}
  {F : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
  {A : I → Sheaf J AddCommGrpCat.{max w t}} (b : ∀ i, (F i).AbelianBanding J (A i))
  {c : Fan A} (hc : IsLimit c)

/-- The band isomorphisms of the product banding: sections of `c.pt` are families of sections of
the `A i`, which the `b i` identify with families of automorphisms of the components. -/
private noncomputable def piMulEquiv (U : C) (x : (TauCeti.Stack.pi F).obj (.mk (op U))) :
    Multiplicative (c.pt.obj.obj (op U)) ≃* Aut x :=
  -- Viewing `x` as a family makes the product structure of `Aut x` available to elaboration.
  let x' : pi.Fiber F (op U) := x
  ((Sheaf.fanSectionsAddEquiv hc (op U)).toMultiplicative.trans
    (MulEquiv.piMultiplicative _)).trans
    ((MulEquiv.piCongrRight fun i ↦ (b i).mulEquiv U (x' i)).trans (Pi.autMulEquiv x').symm)

private lemma piMulEquiv_asIso_hom (U : C) (x : (TauCeti.Stack.pi F).obj (.mk (op U)))
    (a : Multiplicative (c.pt.obj.obj (op U))) (i : I) :
    (piMulEquiv b hc U x a).asIso.hom i =
      ((b i).mulEquiv U (x i) (.ofAdd ((c.proj i).hom.app (op U) a.toAdd))).asIso.hom :=
  let x' : pi.Fiber F (op U) := x
  -- Unfolding the composite of multiplicative equivalences leaves the inverse of
  -- `Pi.autMulEquiv` applied to the family of band automorphisms of the sections of the factors.
  (congrArg (fun e : x' ≅ x' ↦ e.hom i) (Pi.autMulEquiv_symm_apply_asIso x' fun i ↦
    (b i).mulEquiv U (x' i) (.ofAdd (Sheaf.fanSectionsAddEquiv hc (op U) a.toAdd i)))).trans
    (congrArg (fun s ↦ ((b i).mulEquiv U (x i) (.ofAdd s)).asIso.hom)
      (Sheaf.fanSectionsAddEquiv_apply hc (op U) a.toAdd i))

/-- The product of bandings: for `A i`-bandings `b i` of the `F i` and a limit fan `c` of the
`A i`, the `c.pt`-banding of the product `pi F` whose band automorphism of a section `a` at a
family `x` has as components the band automorphisms of the projections of `a` at the `x i`. -/
noncomputable def pi : (TauCeti.Stack.pi F).AbelianBanding J c.pt where
  mulEquiv := piMulEquiv b hc
  mapAut_mulEquiv f x a := Aut.ext <| Iso.ext <| funext fun i ↦ by
    rw [Functor.mapAut_apply_asIso]
    simp only [Functor.mapIso_hom, pi.map_map_apply, piMulEquiv_asIso_hom, map_mulEquiv_hom,
      toAdd_ofAdd, NatTrans.naturality_apply]
    -- The two sides differ only by `pi.map_obj_apply`, which holds by definition; it cannot be
    -- rewritten since the band automorphisms depend on the object.
    rfl
  autMulEquivOfIso_mulEquiv e a := Aut.ext <| Iso.ext <| funext fun i ↦ by
    simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom, pi.comp_apply',
      piMulEquiv_asIso_hom]
    exact (b i).inv_comp_mulEquiv_hom_comp (Pi.isoApp e i) _

/-- The components of the band automorphisms of the product banding are the band automorphisms of
the projections. -/
@[simp]
lemma pi_mulEquiv_asIso_hom (U : C) (x : (TauCeti.Stack.pi F).obj (.mk (op U)))
    (a : Multiplicative (c.pt.obj.obj (op U))) (i : I) :
    ((pi b hc).mulEquiv U x a).asIso.hom i =
      ((b i).mulEquiv U (x i) (.ofAdd ((c.proj i).hom.app (op U) a.toAdd))).asIso.hom :=
  piMulEquiv_asIso_hom b hc U x a i

end CategoryTheory.Pseudofunctor.AbelianBanding

namespace TauCeti.Stack.pi

open CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {I : Type w}
  {F : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
  {A : I → Sheaf J AddCommGrpCat.{max w t}} (b : ∀ i, (F i).AbelianBanding J (A i))
  {c : Fan A} (hc : IsLimit c)

/-- The projections of the product are compatible with the projections of the fan. -/
instance bandCompatible_π (i : I) :
    BandCompatible (c.proj i) (AbelianBanding.pi b hc) (b i) (π F i) :=
  (bandCompatible_iff_map_mulEquiv_hom (b i) _ _).2 fun U x a ↦
    AbelianBanding.pi_mulEquiv_asIso_hom b hc U x a i

/-- A strong transformation `η : K ⟶ pi F` is compatible with a morphism `u : B ⟶ c.pt` if and
only if each of its projections `η ≫ π F i` is compatible with the projection `u ≫ c.proj i`. -/
theorem bandCompatible_iff_comp_π
    {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
    {B : Sheaf J AddCommGrpCat.{max w t}} (bK : K.AbelianBanding J B) (u : B ⟶ c.pt)
    (η : K ⟶ TauCeti.Stack.pi F) :
    BandCompatible u bK (AbelianBanding.pi b hc) η ↔
      ∀ i, BandCompatible (u ≫ c.proj i) bK (b i) (η ≫ π F i) :=
  ⟨fun _ i ↦ BandCompatible.comp (AbelianBanding.pi b hc) u (c.proj i) η (π F i),
    fun h ↦ (bandCompatible_iff_map_mulEquiv_hom _ _ _).2 fun U x s ↦ funext fun i ↦ by
      rw [AbelianBanding.pi_mulEquiv_asIso_hom]
      -- The `i`-th component of the image under `η` is by definition the image under
      -- `η ≫ π F i`, and the section of `u ≫ c.proj i` is by definition the projection of the
      -- section of `u`.
      exact BandCompatible.map_mulEquiv_hom (b i) (u ≫ c.proj i) (η ≫ π F i) U x s⟩

/-- The strong transformation `lift a : K ⟶ pi F` induced by transformations `a i : K ⟶ F i`
compatible with morphisms `φ i : B ⟶ A i` is compatible with the morphism `B ⟶ c.pt` induced by
the `φ i`. -/
theorem bandCompatible_lift {K : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}
    {B : Sheaf J AddCommGrpCat.{max w t}} (bK : K.AbelianBanding J B) (φ : ∀ i, B ⟶ A i)
    (a : ∀ i, K ⟶ F i) [∀ i, BandCompatible (φ i) bK (b i) (a i)] :
    BandCompatible (Fan.IsLimit.lift hc φ) bK (AbelianBanding.pi b hc) (lift a) :=
  (bandCompatible_iff_comp_π b hc bK _ _).2 fun i ↦ by
    rw [Fan.IsLimit.fac]
    exact .of_iso (liftCompπ a i).symm

variable {G : I → Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w u'}}

/-- The product of transformations `η i : F i ⟶ G i` compatible with morphisms
`φ i : A i ⟶ A' i` is compatible with the product of the `φ i`, the morphism between the points
of limit fans of the `A i` and of the `A' i` induced by the `c.proj i ≫ φ i`. -/
theorem bandCompatible_piMap {A' : I → Sheaf J AddCommGrpCat.{max w t}}
    (bG : ∀ i, (G i).AbelianBanding J (A' i)) {c' : Fan A'} (hc' : IsLimit c')
    (φ : ∀ i, A i ⟶ A' i) (η : ∀ i, F i ⟶ G i) [∀ i, BandCompatible (φ i) (b i) (bG i) (η i)] :
    BandCompatible (Fan.IsLimit.lift hc' fun i ↦ c.proj i ≫ φ i) (AbelianBanding.pi b hc)
      (AbelianBanding.pi bG hc') (piMap η) :=
  have (i : I) : BandCompatible (c.proj i ≫ φ i) (AbelianBanding.pi b hc) (bG i) (π F i ≫ η i) :=
    BandCompatible.comp (b i) _ _ _ _
  bandCompatible_lift bG hc' (AbelianBanding.pi b hc) _ _

/-- The product of band-preserving transformations preserves the product bands. -/
instance bandPreserving_piMap (bG : ∀ i, (G i).AbelianBanding J (A i)) (η : ∀ i, F i ⟶ G i)
    [∀ i, BandPreserving (b i) (bG i) (η i)] :
    BandPreserving (AbelianBanding.pi b hc) (AbelianBanding.pi bG hc) (piMap η) := by
  have h := bandCompatible_piMap b hc bG hc (fun i ↦ 𝟙 (A i)) η
  rwa [Fan.IsLimit.hom_ext hc (Fan.IsLimit.lift hc fun i ↦ c.proj i ≫ 𝟙 (A i)) (𝟙 c.pt)
    fun i ↦ by simp [Fan.IsLimit.fac],
    bandCompatible_id_iff] at h

end TauCeti.Stack.pi

end
