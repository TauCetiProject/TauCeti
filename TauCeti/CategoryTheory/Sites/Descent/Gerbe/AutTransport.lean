/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Aut.Conjugation

/-!
# Transport of automorphisms along local isomorphisms

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor all of whose fibre objects have
commutative automorphism groups, for instance a gerbe with abelian inertia. Let `x y` be objects
of the fibre over `U`, `R` a sieve on `U`, and `e_i : i^* x ≅ i^* y` an isomorphism for every arrow
`i : V_i ⟶ U` of `R`. The `e_i` are arbitrary: they need not form an isomorphism of descent data,
and `x`, `y` need not be isomorphic over `U`.

An automorphism `a` of `x` gives the automorphisms `conj(e_i)(i^* a)` of the `i^* y`. Because
conjugation along isomorphisms between objects with commutative automorphism groups does not
depend on the isomorphism (`Aut.autMulEquivOfIso_eq_of_commute`), these form an automorphism of
the canonical descent datum of `y` on `R` (`GerbeAutTransport.conjugateDescentIso`). When `R`
covers `U` and `F` is a prestack, the canonical descent functor is fully faithful, and lifting
through it gives an automorphism of `y` (`GerbeAutTransport.conjugateCoverAut`). It is the unique
automorphism of `y` restricting to `conj(e_i)(i^* a)` along every `i` of `R`
(`conjugateCoverAut_mapIso`, `conjugateCoverAut_unique`), it does not depend on the `e_i`
(`conjugateCoverAut_independent`) nor on the covering sieve (`conjugateCoverAut_cover_independent`),
and when `x ≅ y` globally it is conjugation along any global isomorphism
(`conjugateCoverAut_of_iso`). It is a group isomorphism `Aut x ≃* Aut y`
(`conjugateCoverEquiv`) whose inverse is transport along the `e_i⁻¹`, and transports compose
(`conjugateCoverAut_comp`). This is the choice independence and local gluing step in the Stacks
Project, Lemma 8.11.8 (tag 0CJY), which identifies all automorphism groups of a gerbe with abelian
inertia with each other.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeAutTransport`:

* `conjugateDescentIso`: the automorphism of the canonical descent datum of `y`.
* `conjugateCoverAut`: the descended automorphism of `y`, with `conjugateCoverAut_mapIso` and
  `conjugateCoverAut_unique`.
* `conjugateCoverAut_independent`, `conjugateCoverAut_refinement`,
  `conjugateCoverAut_cover_independent`: independence of the local isomorphisms and of the cover.
* `conjugateCoverAut_of_iso`: agreement with conjugation along a global isomorphism.
* `conjugateCoverHom`, `conjugateCoverAut_comp`, `conjugateCoverAut_reverse`,
  `conjugateCoverEquiv`, `conjugateCoverEquiv_of_iso`: the group isomorphism `Aut x ≃* Aut y`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeAutTransport

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)
  {U : C} {x y z : F.obj (.mk (op U))}

/-- The conjugate `conj(e_i)(i^* a)` of the pullback of `a` along `i`. -/
abbrev localConjugate {V : C} (i : V ⟶ U)
    (e : (F.map i.op.toLoc).toFunctor.obj x ≅ (F.map i.op.toLoc).toFunctor.obj y) (a : Aut x) :
    Aut ((F.map i.op.toLoc).toFunctor.obj y) :=
  Aut.autMulEquivOfIso e ((F.map i.op.toLoc).toFunctor.mapAut x a)

include hF in
/-- The local conjugate does not depend on the local isomorphism. -/
theorem localConjugate_eq {V : C} (i : V ⟶ U)
    (e e' : (F.map i.op.toLoc).toFunctor.obj x ≅ (F.map i.op.toLoc).toFunctor.obj y)
    (a : Aut x) : localConjugate i e a = localConjugate i e' a := by
  rw [localConjugate, localConjugate, Aut.autMulEquivOfIso_eq_of_commute (hF _ _) e e']

variable (R : Sieve U)

/-- A family of local isomorphisms `e_i : i^* x ≅ i^* y`, one for every arrow `i` of `R`. -/
abbrev LocalIsos (x y : F.obj (.mk (op U))) :=
  ∀ i : R.arrows.category,
    (F.map i.obj.hom.op.toLoc).toFunctor.obj x ≅ (F.map i.obj.hom.op.toLoc).toFunctor.obj y

variable {R}

include hF in
/-- The local conjugates `conj(e_i)(i^* a)` commute with the gluing isomorphisms of the canonical
descent datum of `y`. -/
theorem localConjugate_comm (e : LocalIsos R x y) (a : Aut x) ⦃Y : C⦄ (q : Y ⟶ U)
    ⦃i₁ i₂ : R.arrows.category⦄ (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (F.map f₁.op.toLoc).toFunctor.map (localConjugate i₁.obj.hom (e i₁) a).asIso.hom ≫
        ((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj y).hom q f₁ f₂ =
      ((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj y).hom q f₁ f₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (localConjugate i₂.obj.hom (e i₂) a).asIso.hom := by
  have h := Aut.autMulEquivOfIso_hom_comp_of_commute (hF _ _)
    (((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj x).iso q f₁ f₂ hf₁ hf₂)
    (((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj y).iso q f₁ f₂ hf₁ hf₂)
    ((F.map f₁.op.toLoc).toFunctor.mapIso (e i₁)) ((F.map f₂.op.toLoc).toFunctor.mapIso (e i₂))
    ((F.map f₁.op.toLoc).toFunctor.mapAut _ ((F.map i₁.obj.hom.op.toLoc).toFunctor.mapAut x a))
    ((F.map f₂.op.toLoc).toFunctor.mapAut _ ((F.map i₂.obj.hom.op.toLoc).toFunctor.mapAut x a))
    (((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).map a.asIso.hom).comm q f₁ f₂
      hf₁ hf₂)
  exact (eq_whisker congr($(Functor.mapAut_autMulEquivOfIso _ (e i₁) _).asIso.hom) _).trans
    (h.trans (whisker_eq _ congr($(Functor.mapAut_autMulEquivOfIso _ (e i₂) _).asIso.hom).symm))

/-- The automorphism of the canonical descent datum of `y` on `R` with components the local
conjugates `conj(e_i)(i^* a)`. -/
def conjugateDescentIso (e : LocalIsos R x y) (a : Aut x) :
    (F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj y ≅
      (F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj y :=
  DescentData.isoMk (fun i ↦ (localConjugate i.obj.hom (e i) a).asIso)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ localConjugate_comm hF e a q f₁ f₂ hf₁ hf₂)

@[simp]
theorem conjugateDescentIso_hom_hom (e : LocalIsos R x y) (a : Aut x) (i : R.arrows.category) :
    (conjugateDescentIso hF e a).hom.hom i = (localConjugate i.obj.hom (e i) a).asIso.hom :=
  (rfl)

@[simp]
theorem conjugateDescentIso_inv_hom (e : LocalIsos R x y) (a : Aut x) (i : R.arrows.category) :
    (conjugateDescentIso hF e a).inv.hom i = (localConjugate i.obj.hom (e i) a).asIso.inv :=
  (rfl)

/-- The descent automorphism of `a = 1` is the identity. -/
@[simp]
theorem conjugateDescentIso_one (e : LocalIsos R x y) :
    conjugateDescentIso hF e 1 = Iso.refl _ := by
  ext1
  refine DescentData.hom_ext fun i ↦ ?_
  rw [conjugateDescentIso_hom_hom, Iso.refl_hom, DescentData.id_hom]
  -- The component `((F.toDescentData _).obj y).obj i` of the descent datum is `i^* y` by
  -- definition (`DescentData.ofObj_obj`), so the identity on either object is the same morphism.
  exact (by simp : (localConjugate i.obj.hom (e i) 1).asIso.hom = 𝟙 _)

/-- The descent automorphism of `a⁻¹` is the inverse of the descent automorphism of `a`. -/
@[simp]
theorem conjugateDescentIso_inv (e : LocalIsos R x y) (a : Aut x) :
    conjugateDescentIso hF e a⁻¹ = (conjugateDescentIso hF e a).symm := by
  ext1
  refine DescentData.hom_ext fun i ↦ ?_
  rw [conjugateDescentIso_hom_hom, Iso.symm_hom, conjugateDescentIso_inv_hom]
  -- As in `conjugateDescentIso_one`, both sides are endomorphisms of `i^* y`, which is the
  -- component `((F.toDescentData _).obj y).obj i` by definition (`DescentData.ofObj_obj`).
  exact (by simp : (localConjugate i.obj.hom (e i) a⁻¹).asIso.hom =
    (localConjugate i.obj.hom (e i) a).asIso.inv)

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- **Transport of an automorphism along local isomorphisms.** For a covering sieve `R` of a
prestack, the automorphism of `y` obtained by lifting `conjugateDescentIso` through the fully
faithful canonical descent functor. -/
noncomputable def conjugateCoverAut (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) : Aut y :=
  .of ((F.isPrestackFor' R hR).fullyFaithful.preimageIso (conjugateDescentIso hF e a))

/-- Restricting the underlying morphism of the transported automorphism along any arrow `i` of
`R` gives that of the local conjugate `conj(e_i)(i^* a)`. -/
@[simp]
theorem map_conjugateCoverAut_hom (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x)
    (i : R.arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.map (conjugateCoverAut hF hR e a).asIso.hom =
      (localConjugate i.obj.hom (e i) a).asIso.hom := by
  have h := congrArg (fun φ ↦ DescentData.Hom.hom φ i)
    ((F.isPrestackFor' R hR).fullyFaithful.map_preimage (conjugateDescentIso hF e a).hom)
  rw [toDescentData_map_hom, conjugateDescentIso_hom_hom] at h
  exact h

/-- Restricting the transported automorphism along any arrow `i` of `R` gives the local conjugate
`conj(e_i)(i^* a)`, as an automorphism. -/
theorem conjugateCoverAut_mapIso (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x)
    (i : R.arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.mapAut y (conjugateCoverAut hF hR e a) =
      localConjugate i.obj.hom (e i) a :=
  Aut.ext (Iso.ext (map_conjugateCoverAut_hom hF hR e a i))

/-- **Uniqueness.** An automorphism of `y` restricting to the local conjugates along every arrow of
`R` is the transported automorphism. -/
theorem conjugateCoverAut_unique (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) (b : Aut y)
    (hb : ∀ i : R.arrows.category,
      (F.map i.obj.hom.op.toLoc).toFunctor.mapAut y b = localConjugate i.obj.hom (e i) a) :
    b = conjugateCoverAut hF hR e a := by
  refine Aut.ext (Iso.ext ((F.isPrestackFor' R hR).fullyFaithful.map_injective ?_))
  refine DescentData.hom_ext fun i ↦ ?_
  have h := congrArg (fun c : Aut _ ↦ c.asIso.hom) (hb i)
  rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom] at h
  rw [toDescentData_map_hom, toDescentData_map_hom, h, map_conjugateCoverAut_hom]

/-- **Independence of the local isomorphisms.** Two families of local isomorphisms on the same
covering sieve transport `a` to the same automorphism. -/
theorem conjugateCoverAut_independent (hR : R ∈ J U) (e e' : LocalIsos R x y) (a : Aut x) :
    conjugateCoverAut hF hR e a = conjugateCoverAut hF hR e' a :=
  conjugateCoverAut_unique hF hR e' a _ fun i ↦ by
    rw [conjugateCoverAut_mapIso, localConjugate_eq hF]

/-- **Refinement.** For covering sieves `R ≤ S` and arbitrary local isomorphisms on each, the
transported automorphisms agree. -/
theorem conjugateCoverAut_refinement {S : Sieve U} (hRS : R ≤ S) (hR : R ∈ J U) (hS : S ∈ J U)
    (e : LocalIsos R x y) (d : LocalIsos S x y) (a : Aut x) :
    conjugateCoverAut hF hR e a = conjugateCoverAut hF hS d a := by
  refine (conjugateCoverAut_unique hF hR e a _ fun i ↦ ?_).symm
  rw [conjugateCoverAut_mapIso hF hS d a ⟨i.obj, hRS _ i.property⟩, localConjugate_eq hF]

/-- **Independence of the cover.** Arbitrary covering sieves with arbitrary local isomorphisms
transport `a` to the same automorphism. -/
theorem conjugateCoverAut_cover_independent {S : Sieve U} (hR : R ∈ J U) (hS : S ∈ J U)
    (e : LocalIsos R x y) (d : LocalIsos S x y) (a : Aut x) :
    conjugateCoverAut hF hR e a = conjugateCoverAut hF hS d a := by
  let e' : LocalIsos (R ⊓ S) x y := fun i ↦ e ⟨i.obj, i.property.1⟩
  rw [← conjugateCoverAut_refinement hF inf_le_left (J.intersection_covering hR hS) hR e' e,
    conjugateCoverAut_refinement hF inf_le_right (J.intersection_covering hR hS) hS e' d]

/-- **Agreement with a global isomorphism.** If `d : x ≅ y`, transport along any local
isomorphisms is conjugation along `d`. -/
theorem conjugateCoverAut_of_iso (hR : R ∈ J U) (e : LocalIsos R x y) (d : x ≅ y) (a : Aut x) :
    conjugateCoverAut hF hR e a = Aut.autMulEquivOfIso d a :=
  (conjugateCoverAut_unique hF hR e a _ fun i ↦ by
    rw [Functor.mapAut_autMulEquivOfIso, localConjugate_eq hF]).symm

/-- Transport along local automorphisms of `x` is the identity. -/
@[simp]
theorem conjugateCoverAut_self (hR : R ∈ J U) (e : LocalIsos R x x) (a : Aut x) :
    conjugateCoverAut hF hR e a = a := by
  simp [conjugateCoverAut_of_iso hF hR e (Iso.refl x)]

/-- **Transport as a group homomorphism** `Aut x →* Aut y`. -/
noncomputable def conjugateCoverHom (hR : R ∈ J U) (e : LocalIsos R x y) : Aut x →* Aut y where
  toFun := conjugateCoverAut hF hR e
  map_one' := (conjugateCoverAut_unique hF hR e 1 1 fun i ↦ by simp [localConjugate]).symm
  map_mul' a b := (conjugateCoverAut_unique hF hR e (a * b) _ fun i ↦ by
    simp only [map_mul, conjugateCoverAut_mapIso, localConjugate]).symm

@[simp]
theorem conjugateCoverHom_apply (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) :
    conjugateCoverHom hF hR e a = conjugateCoverAut hF hR e a :=
  (rfl)

@[simp]
theorem conjugateCoverAut_one (hR : R ∈ J U) (e : LocalIsos R x y) :
    conjugateCoverAut hF hR e 1 = 1 :=
  map_one (conjugateCoverHom hF hR e)

@[simp]
theorem conjugateCoverAut_mul (hR : R ∈ J U) (e : LocalIsos R x y) (a b : Aut x) :
    conjugateCoverAut hF hR e (a * b) = conjugateCoverAut hF hR e a * conjugateCoverAut hF hR e b :=
  map_mul (conjugateCoverHom hF hR e) a b

@[simp]
theorem conjugateCoverAut_inv (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) :
    conjugateCoverAut hF hR e a⁻¹ = (conjugateCoverAut hF hR e a)⁻¹ :=
  map_inv (conjugateCoverHom hF hR e) a

/-- **Composition.** Transport along local isomorphisms `x ≅ y` and then `y ≅ z` is transport along
any local isomorphisms `x ≅ z`. -/
theorem conjugateCoverAut_comp (hR : R ∈ J U) (e : LocalIsos R x y) (d : LocalIsos R y z)
    (c : LocalIsos R x z) (a : Aut x) :
    conjugateCoverAut hF hR d (conjugateCoverAut hF hR e a) = conjugateCoverAut hF hR c a := by
  refine conjugateCoverAut_unique hF hR c a _ fun i ↦ ?_
  rw [conjugateCoverAut_mapIso, localConjugate, conjugateCoverAut_mapIso, localConjugate,
    ← MulEquiv.trans_apply, ← Aut.autMulEquivOfIso_trans]
  exact localConjugate_eq hF _ _ (c i) a

/-- **Reversal.** Transport along the inverse local isomorphisms undoes transport. -/
theorem conjugateCoverAut_reverse (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) :
    conjugateCoverAut hF hR (fun i ↦ (e i).symm) (conjugateCoverAut hF hR e a) = a := by
  rw [conjugateCoverAut_comp hF hR e _ (fun i ↦ Iso.refl _), conjugateCoverAut_self]

/-- **Transport as a group isomorphism** `Aut x ≃* Aut y`, with inverse transport along the inverse
local isomorphisms. -/
noncomputable def conjugateCoverEquiv (hR : R ∈ J U) (e : LocalIsos R x y) : Aut x ≃* Aut y where
  __ := conjugateCoverHom hF hR e
  invFun := conjugateCoverAut hF hR fun i ↦ (e i).symm
  left_inv := conjugateCoverAut_reverse hF hR e
  right_inv b := by
    simpa using conjugateCoverAut_reverse hF hR (fun i ↦ (e i).symm) b

@[simp]
theorem conjugateCoverEquiv_apply (hR : R ∈ J U) (e : LocalIsos R x y) (a : Aut x) :
    conjugateCoverEquiv hF hR e a = conjugateCoverAut hF hR e a :=
  (rfl)

@[simp]
theorem conjugateCoverEquiv_symm_apply (hR : R ∈ J U) (e : LocalIsos R x y) (b : Aut y) :
    (conjugateCoverEquiv hF hR e).symm b = conjugateCoverAut hF hR (fun i ↦ (e i).symm) b :=
  (rfl)

/-- The equivalences from two covering sieves with arbitrary local isomorphisms are equal. -/
theorem conjugateCoverEquiv_cover_independent {S : Sieve U} (hR : R ∈ J U) (hS : S ∈ J U)
    (e : LocalIsos R x y) (d : LocalIsos S x y) :
    conjugateCoverEquiv hF hR e = conjugateCoverEquiv hF hS d :=
  MulEquiv.ext fun a ↦ conjugateCoverAut_cover_independent hF hR hS e d a

/-- If `d : x ≅ y`, the equivalence from any local isomorphisms is conjugation along `d`. -/
theorem conjugateCoverEquiv_of_iso (hR : R ∈ J U) (e : LocalIsos R x y) (d : x ≅ y) :
    conjugateCoverEquiv hF hR e = Aut.autMulEquivOfIso d :=
  MulEquiv.ext (conjugateCoverAut_of_iso hF hR e d)

end CategoryTheory.Pseudofunctor.GerbeAutTransport
