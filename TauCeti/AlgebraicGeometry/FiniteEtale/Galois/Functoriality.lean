/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.CategoryTheory.Galois.Topology

/-!
# Functoriality of étale paths and étale fundamental groups

For a geometric point `x : Spec Ω ⟶ T` of a scheme `T`, with `Ω` separably closed, the étale
fundamental group `π₁(T, x)` is the profinite group `Aut (FiniteEtaleScheme.fiber x)` of
automorphisms of the geometric fibre functor at `x`, and an étale path from `x` to another
geometric point `x'` is a natural isomorphism `fiber x ≅ fiber x'`. This file makes both
functorial in the scheme.

Let `f : T ⟶ S` be a morphism of schemes and `y = x ≫ f` the image of `x` in `S`. Base change
along `f` followed by the geometric fibre at `x` is the geometric fibre at `y`
(`TauCeti.FiniteEtaleScheme.pullbackCompFiberIso`). Whiskering with base change therefore carries
an étale path `γ` from `x` to `x'` in `T` to an étale path `mapFiberIso f hx hx' γ` from `y` to
`y'` in `S`, whose component at a finite étale `S`-scheme `X` is the component of `γ` at
`X ×_S T`. On loops this is a homomorphism of fundamental groups, which is continuous
(`TauCeti.FiniteEtaleScheme.mapAutFiber`):

`π₁(T, x) →ₜ* π₁(S, y)`.

To avoid identifying `x ≫ 𝟙 S` with `x` or `x ≫ (f ≫ g)` with `(x ≫ f) ≫ g` definitionally, the
image point is an arbitrary `y` with a proof of `x ≫ f = y`. The constructions satisfy the
groupoid laws in the path (`mapFiberIso_refl`, `mapFiberIso_trans`, `mapFiberIso_symm`) and the
functor laws in the morphism of schemes (`mapFiberIso_id`, `mapFiberIso_comp`, `mapAutFiber_id`,
`mapAutFiber_comp`). The latter rest on the coherence of base change with identities and
composites (`pullbackCompFiberIso_id_hom_app`, `pullbackCompFiberIso_comp_hom_app`).

Changing the base point along a path `γ` identifies `π₁(T, x)` with `π₁(T, x')` by conjugation
(`CategoryTheory.Iso.continuousConjAut`). The homomorphisms `mapAutFiber` are compatible with
these identifications (`mapAutFiber_conjAut`): `mapAutFiber` intertwines conjugation by `γ` with
conjugation by its image path. Consequently the homomorphism induced by `f` depends on the
base point only up to conjugation by étale paths.

A point of a geometric fibre is a lift of the geometric point (`fiberCompInclIso`), and the image
under `pullbackCompFiberIso` of a lift to `X ×_S T` is its composite with the projection to `X`
(`fiberCompInclIso_hom_app_pullbackCompFiberIso_hom_app_left`, in
`TauCeti/AlgebraicGeometry/FiniteEtale/Fiber.lean`). Hence étale paths in `T` and in `S` that
both act on lifts by precomposition with one morphism `Spec Ω' ⟶ Spec Ω` correspond under
`mapFiberIso` (`mapFiberIso_eq_of_fiberCompInclIso_left`), and likewise for loops under
`mapAutFiber` (`mapAutFiber_eq_of_fiberCompInclIso_left`); this is how the homomorphism induced by
a morphism of spectra of fields is identified with restriction of Galois automorphisms.

## Main definitions

* `TauCeti.FiniteEtaleScheme.mapFiberIso f hx hx' γ`: the image under `f : T ⟶ S` of an étale
  path `γ : fiber x ≅ fiber x'` in `T`, an étale path in `S`.
* `TauCeti.FiniteEtaleScheme.mapAutFiber f h`: the continuous homomorphism
  `π₁(T, x) →ₜ* π₁(S, y)` induced by `f : T ⟶ S`, where `h : x ≫ f = y`.

## Main results

* `TauCeti.FiniteEtaleScheme.mapFiberIso_id`, `TauCeti.FiniteEtaleScheme.mapFiberIso_comp`:
  functoriality of the image of étale paths.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_id`, `TauCeti.FiniteEtaleScheme.mapAutFiber_comp`:
  functoriality of the induced homomorphisms of étale fundamental groups.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_eq_conjAut`: `mapAutFiber f h` is precomposition with
  base change, conjugated by `pullbackCompFiberIso`.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_conjAut`: compatibility with change of base point.
* `TauCeti.FiniteEtaleScheme.mapFiberIso_eq_of_fiberCompInclIso_left`,
  `TauCeti.FiniteEtaleScheme.mapAutFiber_eq_of_fiberCompInclIso_left`: étale paths (and loops)
  acting on lifts of geometric points by precomposition with the same morphism
  `Spec Ω' ⟶ Spec Ω` correspond under `mapFiberIso` (and `mapAutFiber`).

## References

* A. Grothendieck, *SGA 1*, Exposé V, §7 and Exposé IX, §6.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.6 (tag 0BND), *Fundamental groups of schemes*.
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T U : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] [Field Ω''] [IsSepClosed Ω'']

/-- The image under `f : T ⟶ S` of an étale path `γ` from `x` to `x'` in `T`: the étale path
from `y = x ≫ f` to `y' = x' ≫ f` in `S` whose component at a finite étale `S`-scheme `X` is
the component of `γ` at the base change `X ×_S T`, transported along `pullbackCompFiberIso`. -/
noncomputable def mapFiberIso (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {x' : Spec (.of Ω') ⟶ T}
    {y : Spec (.of Ω) ⟶ S} {y' : Spec (.of Ω') ⟶ S} (hx : x ≫ f = y) (hx' : x' ≫ f = y')
    (γ : fiber x ≅ fiber x') : fiber y ≅ fiber y' :=
  (pullbackCompFiberIso f x ≪≫ eqToIso (congrArg fiber hx)).symm ≪≫
    Functor.isoWhiskerLeft (pullback f) γ ≪≫ pullbackCompFiberIso f x' ≪≫
      eqToIso (congrArg fiber hx')

/-- The components of the image of an étale path `γ` are the components of `γ` at base changes,
transported along `pullbackCompFiberIso`. -/
@[simp]
theorem mapFiberIso_hom_app (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {x' : Spec (.of Ω') ⟶ T}
    (γ : fiber x ≅ fiber x') (X : FiniteEtaleScheme S) :
    (mapFiberIso f (y := x ≫ f) (y' := x' ≫ f) rfl rfl γ).hom.app X =
      (pullbackCompFiberIso f x).inv.app X ≫ γ.hom.app ((pullback f).obj X) ≫
        (pullbackCompFiberIso f x').hom.app X := by
  simp [mapFiberIso, -pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]

section Groupoid

variable (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {x' : Spec (.of Ω') ⟶ T} {x'' : Spec (.of Ω'') ⟶ T}
  {y : Spec (.of Ω) ⟶ S} {y' : Spec (.of Ω') ⟶ S} {y'' : Spec (.of Ω'') ⟶ S}
  (hx : x ≫ f = y) (hx' : x' ≫ f = y') (hx'' : x'' ≫ f = y'')

/-- The image of the constant path is the constant path. -/
@[simp]
theorem mapFiberIso_refl : mapFiberIso f hx hx (Iso.refl (fiber x)) = Iso.refl (fiber y) := by
  subst hx
  ext X : 3
  simp [-pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]

/-- The image of a composite path is the composite of the images. -/
theorem mapFiberIso_trans (γ : fiber x ≅ fiber x') (δ : fiber x' ≅ fiber x'') :
    mapFiberIso f hx hx'' (γ ≪≫ δ) = mapFiberIso f hx hx' γ ≪≫ mapFiberIso f hx' hx'' δ := by
  subst hx hx' hx''
  ext X : 3
  simp [-pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]

/-- The image of the inverse path is the inverse of the image. -/
@[simp]
theorem mapFiberIso_symm (γ : fiber x ≅ fiber x') :
    mapFiberIso f hx' hx γ.symm = (mapFiberIso f hx hx' γ).symm := by
  ext1
  rw [Iso.symm_hom, eq_comm]
  apply Iso.inv_ext
  rw [← Iso.trans_hom, ← mapFiberIso_trans, Iso.self_symm_id, mapFiberIso_refl, Iso.refl_hom]

end Groupoid

/-- The image of an étale path under the identity is the path itself. -/
@[simp]
theorem mapFiberIso_id {x : Spec (.of Ω) ⟶ S} {x' : Spec (.of Ω') ⟶ S} (hx : x ≫ 𝟙 S = x)
    (hx' : x' ≫ 𝟙 S = x') (γ : fiber x ≅ fiber x') : mapFiberIso (𝟙 S) hx hx' γ = γ := by
  ext X : 3
  have h := pullbackCompFiberIso_id_hom_app x X
  have h' := pullbackCompFiberIso_id_hom_app x' X
  simp only [mapFiberIso, Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    eqToIso.inv, Functor.isoWhiskerLeft_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
    Functor.comp_obj, Functor.whiskerLeft_app]
  rw [h', ← γ.hom.naturality, ← reassoc_of% h]
  simp [-pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]

/-- The image of an étale path under a composite `f ≫ g` is the image under `g` of its image
under `f`. -/
theorem mapFiberIso_comp (f : T ⟶ S) (g : S ⟶ U) {x : Spec (.of Ω) ⟶ T}
    {x' : Spec (.of Ω') ⟶ T} {y : Spec (.of Ω) ⟶ S} {y' : Spec (.of Ω') ⟶ S}
    {z : Spec (.of Ω) ⟶ U} {z' : Spec (.of Ω') ⟶ U} (hx : x ≫ f = y) (hx' : x' ≫ f = y')
    (hy : y ≫ g = z) (hy' : y' ≫ g = z') (hxz : x ≫ f ≫ g = z) (hxz' : x' ≫ f ≫ g = z')
    (γ : fiber x ≅ fiber x') :
    mapFiberIso (f ≫ g) hxz hxz' γ = mapFiberIso g hy hy' (mapFiberIso f hx hx' γ) := by
  subst hx hx' hy hy'
  ext X : 3
  have h := pullbackCompFiberIso_comp_hom_app f g x X
  have h' := pullbackCompFiberIso_comp_hom_app f g x' X
  -- The base-point side of `h`, solved for the inverses of the comparison isomorphisms.
  have key : eqToHom (congrArg (fun x ↦ (fiber x).obj X) hxz.symm) ≫
      (pullbackCompFiberIso (f ≫ g) x).inv.app X ≫ (fiber x).map ((pullbackComp f g).hom.app X) =
        (pullbackCompFiberIso g (x ≫ f)).inv.app X ≫
          (pullbackCompFiberIso f x).inv.app ((pullback g).obj X) := by
    rw [← cancel_mono ((pullbackCompFiberIso f x).hom.app ((pullback g).obj X) ≫
      (pullbackCompFiberIso g (x ≫ f)).hom.app X)]
    simp only [Category.assoc, ← h]
    simp [-pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]
  simp only [mapFiberIso, Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    eqToIso.inv, Functor.isoWhiskerLeft_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
    Functor.comp_obj, Functor.whiskerLeft_app, eqToIso_refl, Iso.trans_refl,
    Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_twice, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp]
  rw [h', ← γ.hom.naturality_assoc, reassoc_of% key]
  -- The two sides differ only in writing `(pullback g ⋙ pullback f).obj X` (`Functor.comp_obj`).
  rfl

/-- The image of a loop `σ` at `x` is `σ` precomposed with base change along `f`, conjugated by
the identification of base change followed by the fibre at `x` with the fibre at `y`. -/
private theorem mapFiberIso_asIso_eq_conjAut (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T}
    {y : Spec (.of Ω) ⟶ S} (h : x ≫ f = y) (σ : Aut (fiber x)) :
    mapFiberIso f h h σ.asIso = ((pullbackCompFiberIso f x ≪≫ eqToIso (congrArg fiber h)).conjAut
      (((Functor.whiskeringLeft _ _ _).obj (pullback f)).mapAut (fiber x) σ)).asIso := by
  rw [Iso.conjAut_apply, Functor.mapAut_apply_asIso]
  ext X : 3
  simp [mapFiberIso, -pullbackCompFiberIso_hom_app, -pullbackCompFiberIso_inv_app]

/-- The continuous homomorphism of étale fundamental groups `π₁(T, x) →ₜ* π₁(S, y)` induced by
`f : T ⟶ S`, where `h : x ≫ f = y`: a loop `σ` at `x` goes to its image `mapFiberIso f h h σ`,
whose component at a finite étale `S`-scheme `X` is the component of `σ` at `X ×_S T`. -/
noncomputable def mapAutFiber (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S}
    (h : x ≫ f = y) : Aut (fiber x) →ₜ* Aut (fiber y) where
  toFun σ := .of (mapFiberIso f h h σ.asIso)
  map_one' := by
    ext1
    simp
  map_mul' σ τ := by
    ext1
    simp only [Aut.mul_asIso]
    exact mapFiberIso_trans f h h h τ.asIso σ.asIso
  continuous_toFun := by
    -- The map is conjugation by the identification of base change followed by the fibre at `x`
    -- with the fibre at `y`, after precomposition with base change along `f`.
    refine ((pullbackCompFiberIso f x ≪≫ eqToIso (congrArg fiber h)).continuous_conjAut.comp
      (continuous_mapAut_whiskeringLeft (pullback f) (fiber x))).congr
        fun σ ↦ Aut.ext (mapFiberIso_asIso_eq_conjAut f h σ).symm

/-- The loop `mapAutFiber f h σ` is the image of the loop `σ` under `f`. -/
@[simp]
theorem mapAutFiber_apply_asIso (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S}
    (h : x ≫ f = y) (σ : Aut (fiber x)) :
    (mapAutFiber f h σ).asIso = mapFiberIso f h h σ.asIso :=
  (rfl)

/-- The homomorphism of étale fundamental groups induced by `f : T ⟶ S` is precomposition with
base change along `f`, conjugated by the identification of base change followed by the fibre at
`x` with the fibre at `y`. -/
theorem mapAutFiber_eq_conjAut (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S}
    (h : x ≫ f = y) (σ : Aut (fiber x)) :
    mapAutFiber f h σ = (pullbackCompFiberIso f x ≪≫ eqToIso (congrArg fiber h)).conjAut
      (((Functor.whiskeringLeft _ _ _).obj (pullback f)).mapAut (fiber x) σ) :=
  Aut.ext (mapFiberIso_asIso_eq_conjAut f h σ)

/-- The identity of `S` induces the identity of `π₁(S, x)`. -/
@[simp]
theorem mapAutFiber_id {x : Spec (.of Ω) ⟶ S} (h : x ≫ 𝟙 S = x) :
    mapAutFiber (𝟙 S) h = ContinuousMonoidHom.id _ := by
  ext σ : 2
  simp

/-- The homomorphism of fundamental groups induced by a composite `f ≫ g` is the composite of the
induced homomorphisms. -/
theorem mapAutFiber_comp (f : T ⟶ S) (g : S ⟶ U) {x : Spec (.of Ω) ⟶ T}
    {y : Spec (.of Ω) ⟶ S} {z : Spec (.of Ω) ⟶ U} (hx : x ≫ f = y) (hy : y ≫ g = z)
    (hxz : x ≫ f ≫ g = z) :
    mapAutFiber (f ≫ g) hxz = (mapAutFiber g hy).comp (mapAutFiber f hx) := by
  ext σ : 2
  simp [mapFiberIso_comp f g hx hx hy hy hxz hxz]

/-- Functoriality of fundamental groups is compatible with change of base point: conjugating by an
étale path `γ` from `x` to `x'` and then mapping along `f` is mapping along `f` and then
conjugating by the image path. -/
theorem mapAutFiber_conjAut (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {x' : Spec (.of Ω') ⟶ T}
    {y : Spec (.of Ω) ⟶ S} {y' : Spec (.of Ω') ⟶ S} (hx : x ≫ f = y) (hx' : x' ≫ f = y')
    (γ : fiber x ≅ fiber x') (σ : Aut (fiber x)) :
    mapAutFiber f hx' (γ.conjAut σ) = (mapFiberIso f hx hx' γ).conjAut (mapAutFiber f hx σ) := by
  ext1
  rw [mapAutFiber_apply_asIso, Iso.conjAut_apply, Iso.conjAut_apply, mapAutFiber_apply_asIso,
    mapFiberIso_trans f hx' hx hx', mapFiberIso_trans f hx hx hx', mapFiberIso_symm]

/-- **Recognizing the image of an étale path by its action on lifts.** Let
`φ : Spec Ω' ⟶ Spec Ω`. If an étale path `γ` from `x` to `x'` sends each lift of `x` to a finite
étale `T`-scheme to its precomposition with `φ`, and an étale path `δ` from `y` to `y'` does the
same on lifts of `y`, then `δ` is the image `mapFiberIso f hx hx' γ`. -/
theorem mapFiberIso_eq_of_fiberCompInclIso_left (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T}
    {x' : Spec (.of Ω') ⟶ T} {y : Spec (.of Ω) ⟶ S} {y' : Spec (.of Ω') ⟶ S} (hx : x ≫ f = y)
    (hx' : x' ≫ f = y') (γ : fiber x ≅ fiber x') (δ : fiber y ≅ fiber y')
    (φ : Spec (.of Ω') ⟶ Spec (.of Ω))
    (hγ : ∀ (Z : FiniteEtaleScheme T) (z : (fiber x).obj Z),
      ((fiberCompInclIso x').hom.app Z (γ.hom.app Z z)).left =
        φ ≫ ((fiberCompInclIso x).hom.app Z z).left)
    (hδ : ∀ (X : FiniteEtaleScheme S) (w : (fiber y).obj X),
      ((fiberCompInclIso y').hom.app X (δ.hom.app X w)).left =
        φ ≫ ((fiberCompInclIso y).hom.app X w).left) :
    mapFiberIso f hx hx' γ = δ := by
  subst hx hx'
  ext X : 3
  ext w
  obtain ⟨z, rfl⟩ : ∃ z, (pullbackCompFiberIso f x).hom.app X z = w :=
    ⟨_, FintypeCat.inv_hom_id_apply ((pullbackCompFiberIso f x).app X) w⟩
  -- A point of the fibre is determined by the underlying morphism of schemes of its lift.
  refine (ConcreteCategory.bijective_of_isIso ((fiberCompInclIso (x' ≫ f)).hom.app X)).1
    (Over.OverMorphism.ext ?_)
  rw [hδ, mapFiberIso_hom_app]
  -- Evaluate the composite and cancel `pullbackCompFiberIso` against its inverse.
  simp only [FintypeCat.comp_apply, ← Iso.app_hom, ← Iso.app_inv, FintypeCat.hom_inv_id_apply]
  simp only [Iso.app_hom]
  -- Both sides are lifts to `X ×_S T` composed with the projection to `X`; there `γ` acts by `φ`.
  rw [fiberCompInclIso_hom_app_pullbackCompFiberIso_hom_app_left,
    fiberCompInclIso_hom_app_pullbackCompFiberIso_hom_app_left, hγ]
  exact Category.assoc _ _ _

/-- **Recognizing the image of a loop by its action on lifts.** Let `φ` be an endomorphism of
`Spec Ω`. If a loop `σ` at `x` acts on the lifts of `x` to every finite étale `T`-scheme by
precomposition with `φ`, and a loop `τ` at `y` does the same on the lifts of `y`, then
`mapAutFiber f h σ = τ`. -/
theorem mapAutFiber_eq_of_fiberCompInclIso_left (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T}
    {y : Spec (.of Ω) ⟶ S} (h : x ≫ f = y) (σ : Aut (fiber x)) (τ : Aut (fiber y))
    (φ : Spec (.of Ω) ⟶ Spec (.of Ω))
    (hσ : ∀ (Z : FiniteEtaleScheme T) (z : (fiber x).obj Z),
      ((fiberCompInclIso x).hom.app Z (σ.asIso.hom.app Z z)).left =
        φ ≫ ((fiberCompInclIso x).hom.app Z z).left)
    (hτ : ∀ (X : FiniteEtaleScheme S) (w : (fiber y).obj X),
      ((fiberCompInclIso y).hom.app X (τ.asIso.hom.app X w)).left =
        φ ≫ ((fiberCompInclIso y).hom.app X w).left) :
    mapAutFiber f h σ = τ := by
  ext1
  exact mapFiberIso_eq_of_fiberCompInclIso_left f h h σ.asIso τ.asIso φ hσ hτ

end TauCeti.FiniteEtaleScheme
