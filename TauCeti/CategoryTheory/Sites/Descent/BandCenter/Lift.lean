/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Local
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.Transport

/-!
# Lifting automorphisms to central sections of a gerbe with abelian inertia

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a gerbe for a Grothendieck topology `J` all of whose
automorphism groups are commutative, and `ZF(U)` its group of intrinsic central sections over `U`
(`CategoryTheory.Pseudofunctor.IntrinsicBandSections`).

Transport of automorphisms between objects over one base
(`GerbeAutTransport.isomCoverTransport`, `Gerbe/Transport.lean`) is canonical. For an object `x`
over `U` and `a ∈ Aut x`, the transports of `f^* a` to all objects `y` over `V`, for all
`f : V ⟶ U`, form a central section `L_x(a) ∈ ZF(U)` (`IntrinsicBandSections.lift`):
naturality in `y` comes from naturality of transport, and compatibility with pullback from its
base change and the composition isomorphisms of `F`. The evaluation of `L_x(a)` at `(𝟙, x)` is
`a` (`IntrinsicBandSections.evaluation_lift_id`), so evaluation at an object of a gerbe with
abelian inertia is surjective, and with the injectivity of
`IntrinsicBandSections.evaluation_injective` (`BandCenter/Local.lean`) it is a group isomorphism
`ZF(U) ≃* Aut x` (`IntrinsicBandSections.evaluationMulEquiv`). This is the local-conjugation step
of the Stacks Project, Lemma 8.11.8 (tag 0CJY), with the varying-base verification.

## Main definitions

* `IntrinsicBandSections.lift`: the homomorphism `L_x : Aut x →* ZF(U)`.
* `IntrinsicBandSections.evaluationMulEquiv`: evaluation `ZF(U) ≃* Aut x`, with inverse `L_x`.

## Main results

* `IntrinsicBandSections.evaluation_lift`: the evaluation at `(f, y)` is the transport of `f^* a`;
  `IntrinsicBandSections.evaluation_lift_of_iso` for a global isomorphism `f^* x ≅ y`.
* `IntrinsicBandSections.evaluation_lift_id`, `IntrinsicBandSections.lift_evaluation_id`: the
  two inverse laws; `IntrinsicBandSections.lift_injective`, `IntrinsicBandSections.lift_surjective`.
* `IntrinsicBandSections.restrict_lift`, `IntrinsicBandSections.lift_autMulEquivOfIso`: the lift
  commutes with pullback and with isomorphisms of objects.
* `IntrinsicBandSections.evaluation_surjective`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

open GerbeAutTransport

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (J : GrothendieckTopology C) [F.IsGerbe J]
  (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)

/-! ### The lift of an automorphism -/

variable {U : C}

/-- The unit of the categorical centre of the fibre over `V` whose component at `y` is the
transport of `f^* a` from `f^* x` to `y`. -/
noncomputable def liftCenter (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U) :
    (CatCenter (F.obj (.mk (op V))))ˣ :=
  (Aut.unitsEndEquivAut (𝟭 _)).symm
    (.of (NatIso.ofComponents (fun y ↦ (isomCoverTransport J hF
      ((F.map f.op.toLoc).toFunctor.obj x) y ((F.map f.op.toLoc).toFunctor.mapAut x a)).asIso)
      fun φ ↦ (isomCoverTransport_naturality J hF (Iso.refl _) (asIso φ) _ _ (by simp)).symm))

@[simp]
theorem liftCenter_app (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    (y : F.obj (.mk (op V))) :
    (liftCenter J hF x a f).val.app y =
      (isomCoverTransport J hF ((F.map f.op.toLoc).toFunctor.obj x) y
        ((F.map f.op.toLoc).toFunctor.mapAut x a)).asIso.hom :=
  (rfl)

/-- The units `liftCenter x a f` are compatible with pullback. -/
theorem isPullbackCompatible_liftCenter (x : F.obj (.mk (op U))) (a : Aut x) :
    F.IsPullbackCompatible fun _ f ↦ liftCenter J hF x a f := by
  refine (isPullbackCompatible_iff _).2 fun V W f g y ↦ ?_
  rw [liftCenter_app, liftCenter_app, isomCoverTransport_mapAut_comp J hF f g x _ a]
  have h := congrArg (fun b : Aut _ ↦ b.asIso.hom) (mapAut_isomCoverTransport J hF g _ y
    ((F.map f.op.toLoc).toFunctor.mapAut x a))
  simpa using h

/-- **The lift** `L_x : Aut x →* ZF(U)` of a gerbe with abelian inertia: the component of `L_x(a)`
at `f : V ⟶ U` and `y` over `V` is the transport of `f^* a` from `f^* x` to `y`. -/
noncomputable def lift (x : F.obj (.mk (op U))) : Aut x →* IntrinsicBandSections F U where
  toFun a :=
    ofCompatible (fun _ f ↦ liftCenter J hF x a f) (isPullbackCompatible_liftCenter J hF x a)
  map_one' := ext fun V f y ↦ by simp
  map_mul' a b := ext fun V f y ↦ by simp [CatCenter.mul_app']

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
      isomCoverTransport J hF ((F.map f.op.toLoc).toFunctor.obj x) y
        ((F.map f.op.toLoc).toFunctor.mapAut x a) :=
  Aut.ext (Iso.ext (by rw [evaluation_asIso_hom, val_lift, liftCenter_app]))

/-- Given a global isomorphism `d : f^* x ≅ y`, the evaluation of `L_x(a)` at `(f, y)` is the
conjugate of `f^* a` along `d`. -/
theorem evaluation_lift_of_iso (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U)
    {y : F.obj (.mk (op V))} (d : (F.map f.op.toLoc).toFunctor.obj x ≅ y) :
    evaluation f y (lift J hF x a) =
      Aut.autMulEquivOfIso d ((F.map f.op.toLoc).toFunctor.mapAut x a) := by
  rw [evaluation_lift, isomCoverTransport_of_iso J hF d]

/-- **Evaluation of the lift at the identity**: `ev_(𝟙, x)(L_x(a)) = a`. -/
@[simp]
theorem evaluation_lift_id (x : F.obj (.mk (op U))) (a : Aut x) :
    evaluation (𝟙 U) x (lift J hF x a) = a := by
  let α := Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc (by simp))
  let d : (F.map (𝟙 U).op.toLoc).toFunctor.obj x ≅ x := α.app x
  rw [evaluation_lift_of_iso J hF x a (𝟙 U) d]
  exact (Functor.mapAut_eq_autMulEquivOfIso_app α x a).symm.trans (Aut.ext (Iso.ext (by
    rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom, Cat.Hom.id_map])))

/-- **Lift of the evaluation at the identity**: `L_x(ev_(𝟙, x)(s)) = s`. -/
@[simp]
theorem lift_evaluation_id (x : F.obj (.mk (op U))) (s : IntrinsicBandSections F U) :
    lift J hF x (evaluation (𝟙 U) x s) = s :=
  evaluation_injective (J := J) x (evaluation_lift_id J hF x (evaluation (𝟙 U) x s))

/-- The lift is injective. -/
theorem lift_injective (x : F.obj (.mk (op U))) : Function.Injective (lift J hF x) :=
  Function.LeftInverse.injective (g := evaluation (𝟙 U) x) (evaluation_lift_id J hF x)

/-- The lift is surjective: every central section is the lift of its evaluation at `(𝟙, x)`. -/
theorem lift_surjective (x : F.obj (.mk (op U))) : Function.Surjective (lift J hF x) :=
  Function.LeftInverse.surjective (lift_evaluation_id J hF x)

/-- **Invariance of the lift under isomorphisms**: for `e : x ≅ x'`, `L_x'(e a e⁻¹) = L_x(a)`. -/
@[simp]
theorem lift_autMulEquivOfIso {x x' : F.obj (.mk (op U))} (e : x ≅ x') (a : Aut x) :
    lift J hF x' (Aut.autMulEquivOfIso e a) = lift J hF x a :=
  evaluation_injective (J := J) x' (by
    rw [evaluation_lift_id, ← autMulEquivOfIso_evaluation (𝟙 U) e, evaluation_lift_id])

/-- **Restriction of the lift**: `r_f(L_x(a)) = L_(f^* x)(f^* a)`. -/
theorem restrict_lift (x : F.obj (.mk (op U))) (a : Aut x) {V : C} (f : V ⟶ U) :
    restrict f (lift J hF x a) =
      lift J hF ((F.map f.op.toLoc).toFunctor.obj x) ((F.map f.op.toLoc).toFunctor.mapAut x a) :=
  ext_evaluation fun W g y ↦ by
    rw [evaluation_restrict, evaluation_lift, evaluation_lift, isomCoverTransport_mapAut_comp]

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
  left_inv := lift_evaluation_id J hF x
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
