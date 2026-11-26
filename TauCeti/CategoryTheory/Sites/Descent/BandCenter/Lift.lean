/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Local
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.AutTransport
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.LocalCovers

/-!
# Lifting automorphisms to central sections of a gerbe with abelian inertia

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a gerbe for a Grothendieck topology `J` all of whose
automorphism groups are commutative, and `ZF(U)` its group of intrinsic central sections over `U`
(`CategoryTheory.Pseudofunctor.IntrinsicBandSections`).

Any two objects `x y` over `V` are isomorphic on their isomorphism cover, a covering sieve
(`GerbeLocalCovers.isomCover_mem`), so transport of automorphisms along local isomorphisms
(`GerbeAutTransport.conjugateCoverAut`) gives a homomorphism `Aut x →* Aut y`
(`IntrinsicBandSections.transport`), independent of the covering sieve and of the local
isomorphisms used (`IntrinsicBandSections.transport_eq_conjugateCoverAut`).

For an object `x` over `U` and `a ∈ Aut x`, the transports of `f^* a` to all objects `y` over `V`,
for all `f : V ⟶ U`, form a central section `L_x(a) ∈ ZF(U)` (`IntrinsicBandSections.lift`):
naturality in `y` comes from naturality of transport, and compatibility with pullback from its
base change and the composition isomorphisms of `F`. The evaluation of `L_x(a)` at `(𝟙, x)` is
`a` (`IntrinsicBandSections.evaluation_lift_id`), so evaluation at an object of a gerbe with
abelian inertia is surjective, and with the injectivity of main's `evaluation_injective` it is a
group isomorphism `ZF(U) ≃* Aut x` (`IntrinsicBandSections.evaluationMulEquiv`). This is the
local-conjugation step of the Stacks Project, Lemma 8.11.8 (tag 0CJY), with the varying-base
verification.

## Main definitions

* `IntrinsicBandSections.transport`: transport `Aut x →* Aut y` between objects over one base.
* `IntrinsicBandSections.lift`: the homomorphism `L_x : Aut x →* ZF(U)`.
* `IntrinsicBandSections.evaluationMulEquiv`: evaluation `ZF(U) ≃* Aut x`, with inverse `L_x`.

## Main results

* `IntrinsicBandSections.transport_of_iso`, `IntrinsicBandSections.transport_naturality`,
  `IntrinsicBandSections.mapAut_transport`, `IntrinsicBandSections.transport_comp`.
* `IntrinsicBandSections.evaluation_lift`: the evaluation at `(f, y)` is the transport of `f^* a`;
  `IntrinsicBandSections.evaluation_lift_of_iso` for a global isomorphism `f^* x ≅ y`.
* `IntrinsicBandSections.evaluation_lift_id`, `IntrinsicBandSections.lift_injective`,
  `IntrinsicBandSections.restrict_lift`, `IntrinsicBandSections.evaluation_surjective`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

open GerbeAutTransport GerbeLocalCovers

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (J : GrothendieckTopology C) [F.IsGerbe J]
  (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)

/-! ### Transport between objects over one base -/

/-- Chosen isomorphisms `i^* x ≅ i^* y` on the arrows `i` of the isomorphism cover of `x` and
`y`. -/
noncomputable def isomCoverIsos {V : C} (x y : F.obj (.mk (op V))) :
    LocalIsos (isomCover F x y) x y :=
  fun i ↦ ((mem_isomCover_iff x y i.obj.hom).1 i.property).some

/-- **Transport** of automorphisms from `x` to `y` over the same base: transport along chosen local
isomorphisms on the isomorphism cover of `x` and `y`. -/
noncomputable def transport {V : C} (x y : F.obj (.mk (op V))) : Aut x →* Aut y :=
  conjugateCoverHom hF (isomCover_mem (J := J) x y) (isomCoverIsos x y)

/-- Unfolding of `IntrinsicBandSections.transport`. -/
theorem transport_apply {V : C} (x y : F.obj (.mk (op V))) (a : Aut x) :
    transport J hF x y a =
      conjugateCoverAut hF (isomCover_mem (J := J) x y) (isomCoverIsos x y) a :=
  conjugateCoverHom_apply hF _ _ a

/-- Transport is transport along any local isomorphisms on any covering sieve. -/
theorem transport_eq_conjugateCoverAut {V : C} {x y : F.obj (.mk (op V))} {R : Sieve V}
    (hR : R ∈ J V) (e : LocalIsos R x y) (a : Aut x) :
    transport J hF x y a = conjugateCoverAut hF hR e a := by
  rw [transport_apply]
  exact conjugateCoverAut_cover_independent hF _ hR _ e a

/-- Transport along a global isomorphism `d : x ≅ y` is conjugation along `d`. -/
theorem transport_of_iso {V : C} {x y : F.obj (.mk (op V))} (d : x ≅ y) (a : Aut x) :
    transport J hF x y a = Aut.autMulEquivOfIso d a := by
  rw [transport_apply]
  exact conjugateCoverAut_of_iso hF _ _ d a

/-- **Naturality of transport.** For `c : x₁ ≅ x₂`, `d : y₁ ≅ y₂` and automorphisms `a₁`, `a₂`
related by `c`, the transports are related by `d`. -/
theorem transport_naturality {V : C} {x₁ x₂ y₁ y₂ : F.obj (.mk (op V))} (c : x₁ ≅ x₂)
    (d : y₁ ≅ y₂) (a₁ : Aut x₁) (a₂ : Aut x₂)
    (ha : a₁.asIso.hom ≫ c.hom = c.hom ≫ a₂.asIso.hom) :
    (transport J hF x₁ y₁ a₁).asIso.hom ≫ d.hom = d.hom ≫ (transport J hF x₂ y₂ a₂).asIso.hom := by
  rw [transport_apply, transport_apply]
  exact conjugateCoverAut_naturality hF _ _ _ _ c d a₁ a₂ ha

/-- **Base change of transport.** Pullback along `g : W ⟶ V` carries the transport from `x` to `y`
to the transport from `g^* x` to `g^* y`. -/
theorem mapAut_transport {V W : C} (g : W ⟶ V) (x y : F.obj (.mk (op V))) (a : Aut x) :
    (F.map g.op.toLoc).toFunctor.mapAut y (transport J hF x y a) =
      transport J hF ((F.map g.op.toLoc).toFunctor.obj x) ((F.map g.op.toLoc).toFunctor.obj y)
        ((F.map g.op.toLoc).toFunctor.mapAut x a) := by
  rw [transport_apply, transport_apply]
  exact conjugateCoverAut_baseChange hF g _ _ _ _ a

/-- **Transport across a composite pullback.** Transporting `(g ≫ f)^* a` from `(g ≫ f)^* x` and
`g^* (f^* a)` from `g^* (f^* x)` to the same object `y` gives the same automorphism. -/
theorem transport_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op U)))
    (y : F.obj (.mk (op W))) (a : Aut x) :
    transport J hF ((F.map (g ≫ f).op.toLoc).toFunctor.obj x) y
        ((F.map (g ≫ f).op.toLoc).toFunctor.mapAut x a) =
      transport J hF ((F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x)) y
        ((F.map g.op.toLoc).toFunctor.mapAut _ ((F.map f.op.toLoc).toFunctor.mapAut x a)) := by
  have hfg : f.op.toLoc ≫ g.op.toLoc = (g ≫ f).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  refine Aut.ext (Iso.ext ?_)
  simpa using transport_naturality J hF
    ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc hfg)).app x)
    (Iso.refl y) _ _ (F.mapComp'_hom_naturality f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc hfg
      a.asIso.hom)

/-! ### The lift of an automorphism -/

variable {U : C}

/-- The component of the lift of `a ∈ Aut x` at `f : V ⟶ U` and `y` over `V`: the transport of
`f^* a` from `f^* x` to `y`. -/
noncomputable abbrev liftAut (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    (y : F.obj (.mk (op V))) : Aut y :=
  transport J hF ((F.map f.op.toLoc).toFunctor.obj x) y ((F.map f.op.toLoc).toFunctor.mapAut x a)

/-- The components of the lift are natural in `y`. -/
theorem liftAut_naturality (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    {y y' : F.obj (.mk (op V))} (φ : y ⟶ y') :
    φ ≫ (liftAut J hF x a f y').asIso.hom = (liftAut J hF x a f y).asIso.hom ≫ φ :=
  (transport_naturality J hF (Iso.refl _) (asIso φ) _ _ (by simp)).symm

/-- The unit of the categorical centre of the fibre over `V` with components `liftAut x a f y`. -/
noncomputable def liftCenter (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U) :
    (CatCenter (F.obj (.mk (op V))))ˣ :=
  (Aut.unitsEndEquivAut (𝟭 _)).symm
    (.of (NatIso.ofComponents (fun y ↦ (liftAut J hF x a f y).asIso)
      fun φ ↦ liftAut_naturality J hF x a f φ))

@[simp]
theorem liftCenter_app (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    (y : F.obj (.mk (op V))) :
    (liftCenter J hF x a f).val.app y = (liftAut J hF x a f y).asIso.hom :=
  (rfl)

/-- The units `liftCenter x a f` are compatible with pullback. -/
theorem isPullbackCompatible_liftCenter (x : F.obj (.mk (op U))) (a : Aut x) :
    F.IsPullbackCompatible fun _ f ↦ liftCenter J hF x a f := by
  refine (isPullbackCompatible_iff _).2 fun V W f g y ↦ ?_
  rw [liftCenter_app, liftCenter_app, liftAut, liftAut, transport_comp J hF f g x _ a]
  have h := congrArg (fun b : Aut _ ↦ b.asIso.hom) (mapAut_transport J hF g _ y
    ((F.map f.op.toLoc).toFunctor.mapAut x a))
  simpa using h

/-- **The lift** `L_x : Aut x →* ZF(U)` of a gerbe with abelian inertia: the component of `L_x(a)`
at `f : V ⟶ U` and `y` over `V` is the transport of `f^* a` from `f^* x` to `y`. -/
noncomputable def lift (x : F.obj (.mk (op U))) : Aut x →* IntrinsicBandSections F U where
  toFun a :=
    ofCompatible (fun _ f ↦ liftCenter J hF x a f) (isPullbackCompatible_liftCenter J hF x a)
  map_one' := ext fun V f y ↦ by simp [liftAut]
  map_mul' a b := ext fun V f y ↦ by simp [liftAut, CatCenter.mul_app']

/-- The component of `L_x(a)` at `f` is `liftCenter x a f`. -/
@[simp]
theorem val_lift (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U) :
    (lift J hF x a).val V f = liftCenter J hF x a f :=
  val_ofCompatible _ _ V f

/-- The evaluation of `L_x(a)` at `f : V ⟶ U` and `y` is the transport of `f^* a` from `f^* x` to
`y`. -/
theorem evaluation_lift (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    (y : F.obj (.mk (op V))) :
    evaluation f y (lift J hF x a) =
      transport J hF ((F.map f.op.toLoc).toFunctor.obj x) y
        ((F.map f.op.toLoc).toFunctor.mapAut x a) :=
  Aut.ext (Iso.ext (by rw [evaluation_asIso_hom, val_lift, liftCenter_app]))

/-- Given a global isomorphism `d : f^* x ≅ y`, the evaluation of `L_x(a)` at `(f, y)` is the
conjugate of `f^* a` along `d`. -/
theorem evaluation_lift_of_iso (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    {y : F.obj (.mk (op V))} (d : (F.map f.op.toLoc).toFunctor.obj x ≅ y) :
    evaluation f y (lift J hF x a) =
      Aut.autMulEquivOfIso d ((F.map f.op.toLoc).toFunctor.mapAut x a) := by
  rw [evaluation_lift, transport_of_iso J hF d]

/-- **Evaluation of the lift at the identity**: `ev_(𝟙, x)(L_x(a)) = a`. -/
@[simp]
theorem evaluation_lift_id (x : F.obj (.mk (op U))) (a : Aut x) :
    evaluation (𝟙 U) x (lift J hF x a) = a := by
  let α := Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc (by simp))
  let d : (F.map (𝟙 U).op.toLoc).toFunctor.obj x ≅ x := α.app x
  rw [evaluation_lift_of_iso J hF x a (𝟙 U) d]
  exact (Functor.mapAut_eq_autMulEquivOfIso_app α x a).symm.trans (Aut.ext (Iso.ext (by
    rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom]; rfl)))

/-- The lift is injective. -/
theorem lift_injective (x : F.obj (.mk (op U))) : Function.Injective (lift J hF x) :=
  Function.LeftInverse.injective (g := evaluation (𝟙 U) x) (evaluation_lift_id J hF x)

/-- **Restriction of the lift**: `r_f(L_x(a)) = L_(f^* x)(f^* a)`. -/
theorem restrict_lift (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U) :
    restrict f (lift J hF x a) =
      lift J hF ((F.map f.op.toLoc).toFunctor.obj x) ((F.map f.op.toLoc).toFunctor.mapAut x a) :=
  ext_evaluation fun W g y ↦ by
    rw [evaluation_restrict, evaluation_lift, evaluation_lift, transport_comp]

include J hF in
/-- **Evaluation at an object of a gerbe with abelian inertia is surjective.** -/
theorem evaluation_surjective (x : F.obj (.mk (op U))) :
    Function.Surjective (evaluation (F := F) (𝟙 U) x) :=
  fun a ↦ ⟨lift J hF x a, evaluation_lift_id J hF x a⟩

/-- **Evaluation at an object `x` of a gerbe with abelian inertia is a group isomorphism**
`ZF(U) ≃* Aut x`, with inverse the lift `L_x`. -/
noncomputable def evaluationMulEquiv (x : F.obj (.mk (op U))) :
    IntrinsicBandSections F U ≃* Aut x where
  toFun := evaluation (𝟙 U) x
  invFun := lift J hF x
  left_inv s :=
    evaluation_injective (J := J) x (evaluation_lift_id J hF x (evaluation (𝟙 U) x s))
  right_inv := evaluation_lift_id J hF x
  map_mul' := map_mul _

@[simp]
theorem evaluationMulEquiv_apply (x : F.obj (.mk (op U))) (s : IntrinsicBandSections F U) :
    evaluationMulEquiv J hF x s = evaluation (𝟙 U) x s :=
  (rfl)

@[simp]
theorem evaluationMulEquiv_symm_apply (x : F.obj (.mk (op U))) (a : Aut x) :
    (evaluationMulEquiv J hF x).symm a = lift J hF x a :=
  (rfl)

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
