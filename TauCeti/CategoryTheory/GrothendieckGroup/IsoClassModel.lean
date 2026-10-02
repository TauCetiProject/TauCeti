/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Presentation

/-!
# Choice independence of the small presentation of `K₀`

A categorical Grothendieck group is a quotient of a free abelian group whose generators index the
isomorphism classes of objects. `TauCeti.PresentedK0` takes those generators to be
`TauCeti.ObjectCode C = Shrink (Skeleton C)`, but this is only one small type in bijection with
the isomorphism classes: the skeleton of Mathlib's chosen small model `SmallModel C`, or the
codes `ObjectCode C` formed in another universe, serve as well. This file shows that the choice
does not matter, canonically.

A *model* `m : TauCeti.IsoClassModel C I` of the isomorphism classes of `C` is a surjective map
`m.code : C → I` under which two objects have the same code exactly when they are isomorphic.
Relations are given at the level of objects, as a set `ρ` of integral combinations of objects,
so that they make sense over every model at once, and `m.K0 ρ` is the free abelian group on `I`
modulo the codes of the relations. Over two models `m` and `m'` the groups `m.K0 ρ` and
`m'.K0 ρ` are related by a canonical isomorphism `TauCeti.IsoClassModel.K0.equiv m m' ρ`, the
unique homomorphism sending the class of each object to its class. These isomorphisms satisfy
the cocycle laws, and they commute with the maps induced by functors. The public group
`TauCeti.PresentedK0` of the codes of `ρ` is identified with `m.K0 ρ` for every model `m` by
`TauCeti.IsoClassModel.K0.presentedK0Equiv`, compatibly with these isomorphisms.

## Main definitions

* `TauCeti.IsoClassModel C I`: a model of the isomorphism classes of objects of `C` in `I`, with
  the instances `TauCeti.IsoClassModel.objectCode`, `TauCeti.IsoClassModel.skeleton` and
  `TauCeti.IsoClassModel.smallModel`, and the transports `TauCeti.IsoClassModel.ofEquiv` and
  `TauCeti.IsoClassModel.ofEquivalence`.
* `TauCeti.IsoClassModel.equiv m m'`: the bijection between the index types of two models which
  sends the code of an object to its code.
* `TauCeti.IsoClassModel.K0 m ρ`: the Grothendieck group presented by the object-level relations
  `ρ` over the model `m`, with its class map `TauCeti.IsoClassModel.K0.of`, its universal property
  `TauCeti.IsoClassModel.K0.lift` and its functoriality `TauCeti.IsoClassModel.K0.map`.
* `TauCeti.IsoClassModel.K0.equiv m m' ρ`: the canonical isomorphism `m.K0 ρ ≃+ m'.K0 ρ`.
* `TauCeti.IsoClassModel.K0.presentedK0Equiv m ρ`: the canonical isomorphism from the public
  presentation `TauCeti.PresentedK0` of the codes of `ρ` to `m.K0 ρ`.

## Main results

* `TauCeti.IsoClassModel.K0.equiv_of` and `TauCeti.IsoClassModel.K0.equiv_unique`: the canonical
  isomorphism preserves the class of every object, and is the only homomorphism doing so.
* `TauCeti.IsoClassModel.K0.equiv_refl`, `TauCeti.IsoClassModel.K0.equiv_symm` and
  `TauCeti.IsoClassModel.K0.equiv_trans`: the cocycle laws.
* `TauCeti.IsoClassModel.K0.equiv_map`: naturality of the canonical isomorphisms with respect to
  the maps induced by functors.
* `TauCeti.IsoClassModel.K0.presentedK0Equiv_trans_equiv`: the identification with the public
  presentation is compatible with the canonical isomorphisms.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  where `K₀` of an essentially small category is presented on a set of representatives of the
  isomorphism classes, and the universal property of an additive invariant removes the
  dependence on that set.
-/

public section

namespace TauCeti

open CategoryTheory

universe w w' w'' v v' v'' u u' u''

/-- A model of the isomorphism classes of objects of `C` in a type `I`: a surjective map from the
objects of `C` to `I` under which two objects have the same image exactly when they are
isomorphic. -/
@[ext]
structure IsoClassModel (C : Type u) [Category.{v} C] (I : Type w) where
  /-- The element of `I` coding the isomorphism class of an object. -/
  code : C → I
  /-- Every element of `I` codes some object. -/
  code_surjective : Function.Surjective code
  /-- Two objects have the same code exactly when they are isomorphic. -/
  code_eq_code_iff {X Y : C} : code X = code Y ↔ Nonempty (X ≅ Y)

namespace IsoClassModel

variable {C : Type u} [Category.{v} C] {I : Type w} {J : Type w'} {K : Type w''}

lemma code_congr (m : IsoClassModel C I) {X Y : C} (e : X ≅ Y) : m.code X = m.code Y :=
  m.code_eq_code_iff.2 ⟨e⟩

section Instances

variable (C) in
/-- The isomorphism classes of `C` modelled by the objects of its skeleton. -/
def skeleton : IsoClassModel C (Skeleton C) where
  code := toSkeleton
  code_surjective x := ⟨(fromSkeleton C).obj x, toSkeleton_fromSkeleton_obj x⟩
  code_eq_code_iff := toSkeleton_eq_toSkeleton_iff

variable (C) in
/-- The model underlying `TauCeti.PresentedK0`: the codes `TauCeti.ObjectCode C`. -/
noncomputable def objectCode [EssentiallySmall.{w} C] : IsoClassModel C (ObjectCode.{w} C) where
  code := TauCeti.objectCode
  code_surjective := objectCode_surjective
  code_eq_code_iff := objectCode_eq_objectCode_iff

/-- A model transported along a bijection of its index type. -/
def ofEquiv (m : IsoClassModel C I) (e : I ≃ J) : IsoClassModel C J where
  code X := e (m.code X)
  code_surjective := e.surjective.comp m.code_surjective
  code_eq_code_iff := e.apply_eq_iff_eq.trans m.code_eq_code_iff

/-- A model of the isomorphism classes of `D` pulled back along an equivalence `C ≌ D`. -/
def ofEquivalence {D : Type u'} [Category.{v'} D] (m : IsoClassModel D I) (e : C ≌ D) :
    IsoClassModel C I where
  code X := m.code (e.functor.obj X)
  code_surjective i := by
    obtain ⟨Y, rfl⟩ := m.code_surjective i
    exact ⟨e.inverse.obj Y, m.code_congr (e.counitIso.app Y)⟩
  code_eq_code_iff := m.code_eq_code_iff.trans
    ⟨fun ⟨f⟩ => ⟨e.functor.preimageIso f⟩, fun ⟨f⟩ => ⟨e.functor.mapIso f⟩⟩

variable (C) in
/-- The isomorphism classes of `C` modelled by the skeleton of Mathlib's chosen small model
`SmallModel C`. -/
noncomputable def smallModel [EssentiallySmall.{w} C] :
    IsoClassModel C (Skeleton (SmallModel.{w} C)) :=
  (skeleton (SmallModel.{w} C)).ofEquivalence (equivSmallModel C)

@[simp] lemma skeleton_code (X : C) : (skeleton C).code X = toSkeleton X := (rfl)

@[simp] lemma objectCode_code [EssentiallySmall.{w} C] (X : C) :
    (objectCode.{w} C).code X = TauCeti.objectCode X := (rfl)

@[simp] lemma ofEquiv_code (m : IsoClassModel C I) (e : I ≃ J) (X : C) :
    (m.ofEquiv e).code X = e (m.code X) := (rfl)

@[simp] lemma ofEquivalence_code {D : Type u'} [Category.{v'} D] (m : IsoClassModel D I)
    (e : C ≌ D) (X : C) : (m.ofEquivalence e).code X = m.code (e.functor.obj X) := (rfl)

@[simp] lemma smallModel_code [EssentiallySmall.{w} C] (X : C) :
    (smallModel.{w} C).code X = toSkeleton ((equivSmallModel.{w} C).functor.obj X) := (rfl)

end Instances

section Equiv

variable (m : IsoClassModel C I) (m' : IsoClassModel C J) (m'' : IsoClassModel C K)

private lemma code_surjInv_code (X : C) :
    m'.code (Function.surjInv m.code_surjective (m.code X)) = m'.code X :=
  m'.code_eq_code_iff.2 (m.code_eq_code_iff.1 (Function.surjInv_eq m.code_surjective _))

/-- The bijection between the index types of two models of the isomorphism classes of `C` which
sends the code of an object in the first model to its code in the second. -/
noncomputable def equiv : I ≃ J where
  toFun i := m'.code (Function.surjInv m.code_surjective i)
  invFun j := m.code (Function.surjInv m'.code_surjective j)
  left_inv i := by
    obtain ⟨X, rfl⟩ := m.code_surjective i
    simp only [code_surjInv_code]
  right_inv j := by
    obtain ⟨X, rfl⟩ := m'.code_surjective j
    simp only [code_surjInv_code]

@[simp]
lemma equiv_code (X : C) : m.equiv m' (m.code X) = m'.code X :=
  code_surjInv_code m m' X

/-- The bijection between two models is the only map compatible with the codes. -/
lemma equiv_unique (f : I → J) (hf : ∀ X : C, f (m.code X) = m'.code X) : ⇑(m.equiv m') = f := by
  funext i
  obtain ⟨X, rfl⟩ := m.code_surjective i
  rw [equiv_code, hf]

@[simp]
lemma equiv_refl : m.equiv m = Equiv.refl I :=
  Equiv.coe_inj.1 (equiv_unique m m _ fun _ => rfl)

@[simp]
lemma equiv_symm : (m.equiv m').symm = m'.equiv m :=
  Equiv.coe_inj.1 (equiv_unique m' m _ fun X => by rw [Equiv.symm_apply_eq, equiv_code]).symm

@[simp]
lemma equiv_trans : (m.equiv m').trans (m'.equiv m'') = m.equiv m'' :=
  Equiv.coe_inj.1 (equiv_unique m m'' _ fun X => by simp).symm

end Equiv

section K0

variable (m : IsoClassModel C I)

/-- The Grothendieck group presented by the object-level relations `ρ` over the model `m`: the
free abelian group on `I` modulo the subgroup generated by the codes of the relations. -/
def K0 (ρ : Set (FreeAbelianGroup C)) : Type w :=
  FreeAbelianGroup I ⧸ AddSubgroup.closure (FreeAbelianGroup.map m.code '' ρ)

instance (ρ : Set (FreeAbelianGroup C)) : AddCommGroup (m.K0 ρ) :=
  inferInstanceAs
    (AddCommGroup (FreeAbelianGroup I ⧸ AddSubgroup.closure (FreeAbelianGroup.map m.code '' ρ)))

namespace K0

variable {m} {ρ : Set (FreeAbelianGroup C)}

/-- The quotient map presenting `TauCeti.IsoClassModel.K0 m ρ`. -/
def mk : FreeAbelianGroup I →+ m.K0 ρ :=
  QuotientAddGroup.mk' _

lemma mk_surjective : Function.Surjective (mk : FreeAbelianGroup I →+ m.K0 ρ) :=
  QuotientAddGroup.mk'_surjective _

lemma mk_eq_zero_iff (r : FreeAbelianGroup I) :
    (mk r : m.K0 ρ) = 0 ↔ r ∈ AddSubgroup.closure (FreeAbelianGroup.map m.code '' ρ) :=
  QuotientAddGroup.eq_zero_iff r

/-- The class of an object of `C`. -/
noncomputable def of (X : C) : m.K0 ρ :=
  mk (FreeAbelianGroup.of (m.code X))

@[simp]
lemma mk_of_code (X : C) : (mk (FreeAbelianGroup.of (m.code X)) : m.K0 ρ) = of X := (rfl)

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : m.K0 ρ) = of Y := by
  rw [of, of, m.code_congr e]

/-- The class map, extended additively to integral combinations of objects, is the quotient map
applied to their codes. -/
lemma mk_map_code (r : FreeAbelianGroup C) :
    (mk (FreeAbelianGroup.map m.code r) : m.K0 ρ) = FreeAbelianGroup.lift of r := by
  rw [← AddMonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeAbelianGroup.lift_ext _ _ fun X => by simp) r

/-- The class map satisfies every relation in the subgroup generated by `ρ`. -/
lemma lift_of_eq_zero {r : FreeAbelianGroup C} (hr : r ∈ AddSubgroup.closure ρ) :
    FreeAbelianGroup.lift (of : C → m.K0 ρ) r = 0 := by
  rw [← mk_map_code, mk_eq_zero_iff, ← AddMonoidHom.map_closure]
  exact AddSubgroup.mem_map_of_mem _ hr

/-- The classes of objects generate the presented Grothendieck group. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → m.K0 ρ)) = ⊤ := by
  refine eq_top_iff.2 fun x hx => ?_
  clear hx
  obtain ⟨y, rfl⟩ := mk_surjective x
  induction y using FreeAbelianGroup.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | of i =>
      obtain ⟨X, rfl⟩ := m.code_surjective i
      exact AddSubgroup.subset_closure ⟨X, rfl⟩
  | neg a ha => rw [map_neg]; exact neg_mem ha
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- Two homomorphisms out of `m.K0 ρ` agreeing on the classes of objects are equal. -/
@[ext]
theorem hom_ext {G : Type*} [AddMonoid G] {f g : m.K0 ρ →+ G}
    (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  AddMonoidHom.eq_of_eqOn_dense closure_range_of (by rintro _ ⟨X, rfl⟩; exact h X)

section Lift

variable {G : Type*} [AddCommGroup G]

/-- The universal property: an isomorphism-invariant function on objects whose additive
extension annihilates every relation induces a homomorphism out of `m.K0 ρ`. -/
noncomputable def lift (f : C → G) (hf : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hρ : ∀ r ∈ ρ, FreeAbelianGroup.lift f r = 0) : m.K0 ρ →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift (f ∘ Function.surjInv m.code_surjective)) (by
    have hcomp : (f ∘ Function.surjInv m.code_surjective) ∘ m.code = f := funext fun X =>
      hf (m.code_eq_code_iff.1 (Function.surjInv_eq m.code_surjective (m.code X))).some
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, ← FreeAbelianGroup.lift_comp, hcomp, hρ r hr])

private lemma lift_mk (f : C → G) (hf : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hρ : ∀ r ∈ ρ, FreeAbelianGroup.lift f r = 0) (x : FreeAbelianGroup I) :
    lift (m := m) f hf hρ (mk x) =
      FreeAbelianGroup.lift (f ∘ Function.surjInv m.code_surjective) x :=
  QuotientAddGroup.lift_mk' _ _ _

@[simp]
lemma lift_of (f : C → G) (hf : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hρ : ∀ r ∈ ρ, FreeAbelianGroup.lift f r = 0) (X : C) :
    lift (m := m) f hf hρ (of X) = f X := by
  rw [← mk_of_code, lift_mk, FreeAbelianGroup.lift_apply_of]
  exact hf (m.code_eq_code_iff.1 (Function.surjInv_eq m.code_surjective (m.code X))).some

lemma lift_unique (f : C → G) (hf : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hρ : ∀ r ∈ ρ, FreeAbelianGroup.lift f r = 0) (g : m.K0 ρ →+ G)
    (hg : ∀ X : C, g (of X) = f X) : g = lift f hf hρ :=
  hom_ext fun X => by rw [hg, lift_of]

end Lift

section Map

variable {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  {σ : Set (FreeAbelianGroup D)} {τ : Set (FreeAbelianGroup E)}

variable (m) in
/-- Functoriality: a functor carrying every relation of `ρ` into the subgroup generated by `σ`
induces a homomorphism between the presented Grothendieck groups, over any two models. -/
noncomputable def map (n : IsoClassModel D J) (F : C ⥤ D)
    (h : ∀ r ∈ ρ, FreeAbelianGroup.map F.obj r ∈ AddSubgroup.closure σ) :
    m.K0 ρ →+ n.K0 σ :=
  lift (fun X => of (F.obj X)) (fun _ _ e => of_congr (F.mapIso e)) fun r hr => by
    refine (FreeAbelianGroup.lift_comp F.obj of r).trans ?_
    exact lift_of_eq_zero (h r hr)

@[simp]
lemma map_of (n : IsoClassModel D J) (F : C ⥤ D)
    (h : ∀ r ∈ ρ, FreeAbelianGroup.map F.obj r ∈ AddSubgroup.closure σ) (X : C) :
    map m n F h (of X) = of (F.obj X) :=
  lift_of _ _ _ X

lemma map_comp (n : IsoClassModel D J) (p : IsoClassModel E K) (F : C ⥤ D) (G : D ⥤ E)
    (hF : ∀ r ∈ ρ, FreeAbelianGroup.map F.obj r ∈ AddSubgroup.closure σ)
    (hG : ∀ r ∈ σ, FreeAbelianGroup.map G.obj r ∈ AddSubgroup.closure τ)
    (hFG : ∀ r ∈ ρ, FreeAbelianGroup.map (F ⋙ G).obj r ∈ AddSubgroup.closure τ) :
    map m p (F ⋙ G) hFG = (map n p G hG).comp (map m n F hF) :=
  hom_ext fun X => by simp

end Map

section Equiv

variable (m' : IsoClassModel C J) (m'' : IsoClassModel C K)

private lemma map_id_mem_closure :
    ∀ r ∈ ρ, FreeAbelianGroup.map (𝟭 C).obj r ∈ AddSubgroup.closure ρ := fun r hr =>
  (FreeAbelianGroup.map_id_apply r).symm ▸ AddSubgroup.subset_closure hr

/-- The canonical isomorphism between the Grothendieck groups presented by the same relations
over two models of the isomorphism classes of `C`. It sends the class of every object to its
class; see `TauCeti.IsoClassModel.K0.equiv_of` and `TauCeti.IsoClassModel.K0.equiv_unique`. -/
noncomputable def equiv (m : IsoClassModel C I) (m' : IsoClassModel C J)
    (ρ : Set (FreeAbelianGroup C)) : m.K0 ρ ≃+ m'.K0 ρ :=
  (map m m' (𝟭 C) map_id_mem_closure).toAddEquiv (map m' m (𝟭 C) map_id_mem_closure)
    (hom_ext fun X => by simp) (hom_ext fun X => by simp)

@[simp]
lemma equiv_of (X : C) : equiv m m' ρ (of X) = of X := by
  simp [equiv]

/-- The map induced by the identity functor between two models is the canonical isomorphism. -/
lemma map_id (h : ∀ r ∈ ρ, FreeAbelianGroup.map (𝟭 C).obj r ∈ AddSubgroup.closure ρ) :
    map m m' (𝟭 C) h = (equiv m m' ρ : m.K0 ρ →+ m'.K0 ρ) :=
  hom_ext fun X => by simp

/-- The canonical isomorphism is the only homomorphism preserving the class of every object. -/
lemma equiv_unique (f : m.K0 ρ →+ m'.K0 ρ) (hf : ∀ X : C, f (of X) = of X) :
    f = (equiv m m' ρ : m.K0 ρ →+ m'.K0 ρ) :=
  hom_ext fun X => by simp [hf]

@[simp]
lemma equiv_refl : equiv m m ρ = AddEquiv.refl (m.K0 ρ) :=
  AddEquiv.toAddMonoidHom_injective (hom_ext fun X => by simp)

@[simp]
lemma equiv_symm : (equiv m m' ρ).symm = equiv m' m ρ :=
  AddEquiv.toAddMonoidHom_injective
    (hom_ext fun X => by rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_eq]; simp)

/-- The cocycle law for the canonical isomorphisms. -/
@[simp]
lemma equiv_trans : (equiv m m' ρ).trans (equiv m' m'' ρ) = equiv m m'' ρ :=
  AddEquiv.toAddMonoidHom_injective (hom_ext fun X => by simp)

/-- Naturality of the canonical isomorphisms: they commute with the maps induced by a functor. -/
lemma equiv_map {D : Type u'} [Category.{v'} D] {J' : Type*} {K' : Type*}
    {σ : Set (FreeAbelianGroup D)} (n : IsoClassModel D J') (n' : IsoClassModel D K')
    (F : C ⥤ D) (h : ∀ r ∈ ρ, FreeAbelianGroup.map F.obj r ∈ AddSubgroup.closure σ)
    (x : m.K0 ρ) : equiv n n' σ (map m n F h x) = map m' n' F h (equiv m m' ρ x) :=
  DFunLike.congr_fun (hom_ext (f := (equiv n n' σ : n.K0 σ →+ n'.K0 σ).comp (map m n F h))
    (g := (map m' n' F h).comp (equiv m m' ρ : m.K0 ρ →+ m'.K0 ρ)) fun X => by simp) x

end Equiv

section PresentedK0

variable [EssentiallySmall.{w'} C]

private lemma freeLift_map_objectCode {G : Type*} [AddCommGroup G] {f : C → G}
    (hf : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y) (r : FreeAbelianGroup C) :
    freeLift f (FreeAbelianGroup.map TauCeti.objectCode r) = FreeAbelianGroup.lift f r := by
  rw [← AddMonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeAbelianGroup.lift_ext _ _ fun X => by
    rw [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply, ← freeOf_def,
      freeLift_freeOf hf, FreeAbelianGroup.lift_apply_of]) r

private lemma lift_presentedK0Of (r : FreeAbelianGroup C) :
    FreeAbelianGroup.lift (PresentedK0.of :
        C → PresentedK0 (FreeAbelianGroup.map (TauCeti.objectCode (C := C)) '' ρ)) r =
      PresentedK0.mk (FreeAbelianGroup.map TauCeti.objectCode r) := by
  rw [← AddMonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeAbelianGroup.lift_ext _ _ fun X => by
    rw [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply, ← freeOf_def,
      PresentedK0.mk_freeOf, FreeAbelianGroup.lift_apply_of]) r

variable (m ρ) in
/-- The public presentation `TauCeti.PresentedK0` of the codes of the object-level relations `ρ`
is canonically isomorphic to the presentation of `ρ` over any model `m`, by the isomorphism
preserving the class of every object. -/
noncomputable def presentedK0Equiv :
    PresentedK0 (FreeAbelianGroup.map (TauCeti.objectCode (C := C)) '' ρ) ≃+ m.K0 ρ :=
  AddMonoidHom.toAddEquiv
    (PresentedK0.lift
      { obj := of
        map_iso := fun _ _ e => of_congr e
        map_rel := by
          rintro _ ⟨r, hr, rfl⟩
          rw [freeLift_map_objectCode fun _ _ e => of_congr e]
          exact lift_of_eq_zero (AddSubgroup.subset_closure hr) })
    (lift PresentedK0.of (fun _ _ e => PresentedK0.of_congr e) fun r hr => by
      rw [lift_presentedK0Of]
      exact PresentedK0.mk_eq_zero_of_mem ⟨r, hr, rfl⟩)
    (PresentedK0.hom_ext fun X => by simp) (hom_ext fun X => by simp)

@[simp]
lemma presentedK0Equiv_of (X : C) : presentedK0Equiv m ρ (PresentedK0.of X) = of X := by
  simp [presentedK0Equiv]

@[simp]
lemma presentedK0Equiv_symm_of (X : C) :
    (presentedK0Equiv m ρ).symm (of X) = PresentedK0.of X :=
  (presentedK0Equiv m ρ).symm_apply_eq.2 (presentedK0Equiv_of X).symm

/-- The identification with the public presentation is compatible with the canonical
isomorphisms between models. -/
@[simp]
lemma presentedK0Equiv_trans_equiv (m' : IsoClassModel C J) :
    (presentedK0Equiv m ρ).trans (equiv m m' ρ) = presentedK0Equiv m' ρ :=
  AddEquiv.toAddMonoidHom_injective (PresentedK0.hom_ext fun X => by simp)

end PresentedK0

end K0

end K0

end IsoClassModel

end TauCeti
