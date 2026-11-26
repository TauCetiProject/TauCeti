/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import TauCeti.CategoryTheory.Endomorphism

/-!
# Intrinsic central sections of a fibred category

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `U` an object of `C`. The group
`ZF(U)` of **intrinsic central sections** over `U` (`IntrinsicBandSections F U`) consists of the
families `z = (z(V, f))`, indexed by the arrows `f : V ⟶ U`, of units `z(V, f)` of the categorical
centre `CatCenter (F V)` (invertible natural endomorphisms of the identity of the fibre over `V`),
that are compatible with pullback: for every `g : W ⟶ V` and every object `x` over `V`,
`F(g)(z(V, f)_x) = z(W, g ≫ f)_{F(g) x}`. These are pullback-compatible families of central
automorphisms of the fibres, defined without choosing objects; when `F` is a gerbe they give the
sections over `U` of the centre of its band (Stacks, Lemma 8.11.8 (06NY), the varying-`U` step).

`ZF(U)` is a subgroup of the product of the unit groups, with pointwise operations, and it is
commutative because each categorical centre is. Restriction along `f : V ⟶ U` reindexes a
section by composition with `f`; it is a group homomorphism `ZF(U) →* ZF(V)`, the identity for
`f = 𝟙` and compatible with composition.

Evaluating a section at `a : V ⟶ U` and an object `x` over `V` gives a group homomorphism
`ev_(a, x) : ZF(U) →* Aut x`. Conjugation by an isomorphism `x ≅ y` carries `ev_(a, x)` to
`ev_(a, y)`, and the pullback functor `F(g)` carries it to `ev_(g ≫ a, F(g) x)`. Sections are
determined by their evaluations. Evaluation is natural in `x`, so the automorphisms in the image
are central: they commute with every endomorphism of `x`.

## Main definitions

* `CategoryTheory.Pseudofunctor.IntrinsicBandSections F U`: the group `ZF(U)`.
* `CategoryTheory.Pseudofunctor.IntrinsicBandSections.ofCompatible`: the section with given
  compatible components.
* `CategoryTheory.Pseudofunctor.IntrinsicBandSections.restrict`: restriction `ZF(U) →* ZF(V)`
  along `f : V ⟶ U`.
* `CategoryTheory.Pseudofunctor.IntrinsicBandSections.evaluation`: evaluation
  `ZF(U) →* Aut x` at `a : V ⟶ U` and `x` over `V`.

## Main results

* `IntrinsicBandSections.map_app`: a section commutes with every pullback functor on every
  object.
* `IntrinsicBandSections.ext`: sections with the same component automorphisms are equal.
* `IntrinsicBandSections.mul_comm` and the `CommGroup` instance: `ZF(U)` is commutative.
* `IntrinsicBandSections.subsingleton_of_subsingleton_end`: when every object of every fibre has
  only the identity endomorphism (for instance thin fibres), the group of central sections is
  trivial.
* `IntrinsicBandSections.restrict_id` and `IntrinsicBandSections.restrict_comp`: restriction along
  the identity is the identity, and restriction is compatible with composition.
* `IntrinsicBandSections.autMulEquivOfIso_evaluation`: conjugation by `x ≅ y` carries evaluation
  at `x` to evaluation at `y`.
* `IntrinsicBandSections.mapAut_evaluation`: `F(g)` carries evaluation at `(a, x)` to evaluation
  at `(g ≫ a, F(g) x)`.
* `IntrinsicBandSections.ext_evaluation`: sections with the same evaluations are equal.
* `IntrinsicBandSections.evaluation_naturality`: morphisms `x ⟶ y` intertwine the evaluations.
* `IntrinsicBandSections.evaluation_comm`: evaluations commute with every endomorphism of `x`.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A family of units `z(V, f)` of the categorical centres of the fibres, indexed by the arrows
`f : V ⟶ U`, is **compatible with pullback** when `F(g)(z(V, f)_x) = z(W, g ≫ f)_{F(g) x}` for
every `g : W ⟶ V` and every object `x` over `V`. -/
def IsPullbackCompatible {U : C} (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    Prop :=
  ∀ ⦃V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op V))),
    (F.map g.op.toLoc).toFunctor.map ((z V f).val.app x) =
      (z W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x)

/-- The **intrinsic central sections** of `F` over `U`: the families of units `z(V, f)` of the
categorical centres `CatCenter (F V)`, for `f : V ⟶ U`, compatible with pullback
(`CategoryTheory.Pseudofunctor.IsPullbackCompatible`). -/
def IntrinsicBandSections (U : C) :
    Subgroup (∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) where
  carrier := {z | F.IsPullbackCompatible z}
  one_mem' := by
    intro V W f g x
    simp only [Pi.one_apply, Units.val_one, CatCenter.app_one, Functor.map_id]
  mul_mem' := by
    intro a b ha hb V W f g x
    simp only [Pi.mul_apply, Units.val_mul, CatCenter.mul_app, Functor.map_comp, ha f g x,
      hb f g x]
  inv_mem' := by
    intro a ha V W f g x
    simp only [Pi.inv_apply, NatTrans.inv_val_app, Functor.map_inv, ha f g x]

variable {F}

/-- Unfolding of `CategoryTheory.Pseudofunctor.IsPullbackCompatible`. -/
theorem isPullbackCompatible_iff {U : C}
    (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    F.IsPullbackCompatible z ↔ ∀ ⦃V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op V))),
      (F.map g.op.toLoc).toFunctor.map ((z V f).val.app x) =
        (z W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x) :=
  Iff.rfl

namespace IntrinsicBandSections

variable {U : C}

theorem mem_iff (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    z ∈ IntrinsicBandSections F U ↔ F.IsPullbackCompatible z :=
  Iff.rfl

/-- **Compatibility with pullback.** The component of a section at `g ≫ f` is the pullback along
`g` of its component at `f`. -/
theorem map_app (s : IntrinsicBandSections F U) {V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (.mk (op V))) :
    (F.map g.op.toLoc).toFunctor.map ((s.val V f).val.app x) =
      (s.val W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x) :=
  s.property f g x

/-- The section with components `z(V, f)`, given their compatibility with pullback. -/
def ofCompatible (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ)
    (hz : F.IsPullbackCompatible z) : IntrinsicBandSections F U :=
  ⟨z, hz⟩

@[simp]
theorem val_ofCompatible (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ)
    (hz : F.IsPullbackCompatible z) (V : C) (f : V ⟶ U) :
    (ofCompatible z hz).val V f = z V f :=
  (rfl)

@[simp]
theorem val_one (V : C) (f : V ⟶ U) : (1 : IntrinsicBandSections F U).val V f = 1 :=
  rfl

@[simp]
theorem val_mul (s t : IntrinsicBandSections F U) (V : C) (f : V ⟶ U) :
    (s * t).val V f = s.val V f * t.val V f :=
  rfl

@[simp]
theorem val_inv (s : IntrinsicBandSections F U) (V : C) (f : V ⟶ U) :
    s⁻¹.val V f = (s.val V f)⁻¹ :=
  rfl

/-- **Extensionality**: two sections with the same component automorphism at
every arrow `f : V ⟶ U` and every object `x` over `V` are equal. -/
@[ext]
theorem ext {s t : IntrinsicBandSections F U}
    (h : ∀ (V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))),
      (s.val V f).val.app x = (t.val V f).val.app x) :
    s = t :=
  Subtype.ext <| funext fun V ↦ funext fun f ↦ Units.ext <| CatCenter.ext _ _ (h V f)

/-- **Commutativity**: the intrinsic central sections commute, because the
categorical centre of each fibre is commutative. No commutativity of the automorphism groups of
`F` is needed. -/
protected theorem mul_comm (s t : IntrinsicBandSections F U) : s * t = t * s := by
  ext V f x
  simp only [val_mul, Units.val_mul]
  congr 1
  exact Std.Commutative.comm _ _

instance : CommGroup (IntrinsicBandSections F U) where
  mul_comm := IntrinsicBandSections.mul_comm

/-- **Restriction** along `f : V ⟶ U`: `(r_f s)(W, a) = s(W, a ≫ f)`. -/
def restrict {V : C} (f : V ⟶ U) : IntrinsicBandSections F U →* IntrinsicBandSections F V where
  toFun s := ofCompatible (fun W a ↦ s.val W (a ≫ f)) fun W T a g x ↦ by
    simp only [map_app, Category.assoc]
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem val_restrict {V : C} (f : V ⟶ U) (s : IntrinsicBandSections F U) (W : C) (a : W ⟶ V) :
    (restrict f s).val W a = s.val W (a ≫ f) :=
  (rfl)

/-- Restriction along the identity is the identity. -/
@[simp]
theorem restrict_id (s : IntrinsicBandSections F U) : restrict (𝟙 U) s = s := by
  ext W a x
  rw [val_restrict, Category.comp_id]

/-- Restriction is compatible with composition: `r_g (r_f s) = r_{g ≫ f} s`. -/
@[simp]
theorem restrict_comp {V W : C} (f : V ⟶ U) (g : W ⟶ V) (s : IntrinsicBandSections F U) :
    restrict g (restrict f s) = restrict (g ≫ f) s := by
  ext T a x
  rw [val_restrict, val_restrict, val_restrict, Category.assoc]

/-- If every object of every fibre has only the identity endomorphism, for instance when the
fibres are thin, the only intrinsic central section is the identity. -/
theorem subsingleton_of_subsingleton_end
    (h : ∀ (V : C) (x : F.obj (.mk (op V))), Subsingleton (x ⟶ x)) :
    Subsingleton (IntrinsicBandSections F U) :=
  ⟨fun _ _ ↦ ext fun V _ x ↦ (h V x).elim _ _⟩

/-! ### Evaluation -/

/-- **Evaluation** of the central sections at `a : V ⟶ U` and an object `x` over `V`: the
automorphism `z(V, a)_x` of `x`, as a group homomorphism `ZF(U) →* Aut x`. It is Mathlib's
`Aut.unitsEndEquivAut` at the identity functor of the fibre, followed by the component at `x`. -/
def evaluation {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V))) : IntrinsicBandSections F U →* Aut x :=
  (NatTrans.unitsEndEval (𝟭 (F.obj (.mk (op V)))) x).comp
    ((Pi.evalMonoidHom (fun _ : V ⟶ U ↦ (CatCenter (F.obj (.mk (op V))))ˣ) a).comp
      ((Pi.evalMonoidHom (fun V : C ↦ ∀ _ : V ⟶ U, (CatCenter (F.obj (.mk (op V))))ˣ) V).comp
        (IntrinsicBandSections F U).subtype))

/-- The evaluated automorphism is the component of the section. -/
@[simp]
theorem evaluation_asIso_hom {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V)))
    (s : IntrinsicBandSections F U) :
    (evaluation a x s).asIso.hom = (s.val V a).val.app x := by
  simp only [evaluation, MonoidHom.comp_apply, Subgroup.coe_subtype, Pi.evalMonoidHom_apply]
  exact NatTrans.unitsEndEval_asIso_hom x _

/-- The inverse of the evaluated automorphism is the component of the inverse section. -/
@[simp]
theorem evaluation_asIso_inv {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V)))
    (s : IntrinsicBandSections F U) :
    (evaluation a x s).asIso.inv = (s⁻¹.val V a).val.app x := by
  simp only [evaluation, MonoidHom.comp_apply, Subgroup.coe_subtype, Pi.evalMonoidHom_apply]
  exact NatTrans.unitsEndEval_asIso_inv x _

/-- **Sections are determined by their evaluations.** -/
theorem ext_evaluation {s t : IntrinsicBandSections F U}
    (h : ∀ (V : C) (a : V ⟶ U) (x : F.obj (.mk (op V))), evaluation a x s = evaluation a x t) :
    s = t :=
  ext fun V a x ↦ by simpa using congrArg (fun g : Aut x ↦ g.asIso.hom) (h V a x)

/-- **Naturality of evaluation.** Every morphism `h : x ⟶ y` over `V` intertwines the
evaluations at `x` and at `y`. -/
@[reassoc]
theorem evaluation_naturality {V : C} (a : V ⟶ U) {x y : F.obj (.mk (op V))} (h : x ⟶ y)
    (s : IntrinsicBandSections F U) :
    h ≫ (evaluation a y s).asIso.hom = (evaluation a x s).asIso.hom ≫ h := by
  simpa using CatCenter.naturality (s.val V a).val h

/-- **Evaluations are central.** The evaluated automorphism commutes with every endomorphism of
`x`. -/
@[reassoc]
theorem evaluation_comm {V : C} (a : V ⟶ U) (x : F.obj (.mk (op V)))
    (s : IntrinsicBandSections F U) (h : x ⟶ x) :
    h ≫ (evaluation a x s).asIso.hom = (evaluation a x s).asIso.hom ≫ h :=
  evaluation_naturality a h s

/-- **Transport along an isomorphism.** Conjugation by `e : x ≅ y` carries the evaluation at `x`
to the evaluation at `y`. -/
@[simp]
theorem autMulEquivOfIso_evaluation {V : C} (a : V ⟶ U) {x y : F.obj (.mk (op V))} (e : x ≅ y)
    (s : IntrinsicBandSections F U) :
    Aut.autMulEquivOfIso e (evaluation a x s) = evaluation a y s := by
  ext
  -- Conjugation by `e` is `e.inv ≫ _ ≫ e.hom`, and naturality along `e.hom` moves `e.hom` past
  -- the evaluation at `x`, where it cancels against `e.inv`.
  rw [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← evaluation_naturality, Iso.inv_hom_id_assoc]

/-- **Compatibility with pullback.** The pullback functor `F(g)` carries the evaluation at
`(a, x)` to the evaluation at `(g ≫ a, F(g) x)`. -/
@[simp]
theorem mapAut_evaluation {V W : C} (a : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op V)))
    (s : IntrinsicBandSections F U) :
    (F.map g.op.toLoc).toFunctor.mapAut x (evaluation a x s) =
      evaluation (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x) s := by
  ext
  simpa using map_app s a g x

/-- Evaluating a restricted section is evaluating at the composite arrow. -/
@[simp]
theorem evaluation_restrict {V W : C} (f : V ⟶ U) (b : W ⟶ V) (x : F.obj (.mk (op W)))
    (s : IntrinsicBandSections F U) :
    evaluation b x (restrict f s) = evaluation (b ≫ f) x s := by
  ext
  simp

end IntrinsicBandSections

end CategoryTheory.Pseudofunctor
