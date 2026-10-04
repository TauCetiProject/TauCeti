/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Monoidal
public import TauCeti.CategoryTheory.GrothendieckGroup.Exact
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic

/-!
# The tensor product makes exact `K₀` a ring

Let `E` be an exact structure on an essentially small monoidal additive category `C` whose tensor
product is biexact (`TauCeti.ExactStructure.IsMonoidal`). Then `(X, Y) ↦ [X ⊗ Y]` is additive on
`E`-conflations in each variable, so it descends to a biadditive multiplication on the exact
Grothendieck group `TauCeti.ExactK0 E`, which makes it a ring with unit the class of the tensor
unit, commutative as soon as `C` is braided.

This is the ring structure of the Grothendieck ring `G₀(k[G])` of all finite-dimensional
representations of a finite group over a field, where the relations come from every short exact
sequence rather than only the split ones. Biexactness is exactly what is needed: over a field the
tensor product is exact in each variable, even when short exact sequences of representations do
not split.

The construction parallels `TauCeti/CategoryTheory/GrothendieckGroup/Monoidal/Basic.lean` for
split `K₀`, with the biproduct relations replaced by conflations: the multiplication is the
two-variable descent `TauCeti.ExactK0.BiadditiveInvariant.bilift` of `(X, Y) ↦ [X ⊗ Y]`. The
canonical comparison `TauCeti.ExactK0.fromSplit` from split `K₀` is a ring homomorphism,
`TauCeti.ExactK0.fromSplitRingHom`.

## Main definitions

* `TauCeti.ExactK0.mulHom E`: multiplication on exact `K₀`, as a biadditive map.
* `TauCeti.ExactK0.instRing` and `TauCeti.ExactK0.instCommRing`: the ring structure, commutative
  for a braided category.
* `TauCeti.ExactK0.liftRingHom`: the ring homomorphism induced by a multiplicative, unit-preserving
  conflation-additive invariant.
* `TauCeti.ExactK0.mapRingHom`: the ring homomorphism induced by a conflation-exact monoidal
  additive functor.
* `TauCeti.ExactK0.fromSplitRingHom`: the comparison from split `K₀` as a ring homomorphism.
* `TauCeti.ExactK0.fromSplitRingEquiv`: the comparison as a ring equivalence when every
  conflation splits.

## Main results

* `TauCeti.ExactK0.of_mul_of`: the computation rule `[X] * [Y] = [X ⊗ Y]`, and
  `TauCeti.ExactK0.one_def`: the unit is the class of the tensor unit.
* `TauCeti.ExactK0.ringHom_ext`: two ring homomorphisms out of exact `K₀` agreeing on the classes
  of objects are equal.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  for exact `K₀` and the products induced on it by biexact pairings, and Section 4 for the ring
  structure on `K₀` of a symmetric monoidal category.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §14.1, for the
  ring `R_k(G)` of a finite group over a field of arbitrary characteristic.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w w' w'' v v' v'' u u' u''

namespace ExactK0

section Ring

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [EssentiallySmall.{w} C]
  (E : ExactStructure C) [E.IsMonoidal]

/-- The class of a tensor product, as an invariant additive on conflations in each variable: this
is the datum that descends the tensor product to a multiplication on exact `K₀`. -/
private noncomputable def mulInvariant : BiadditiveInvariant E E (ExactK0 E) where
  obj X Y := of (X ⊗ Y)
  map_iso₁ e Y := of_congr (whiskerRightIso e Y)
  map_conflation₂ X _ hS :=
    of_conflation ((ExactStructure.IsMonoidal.isConflationExact_tensorLeft X).map_conflation hS)
  map_conflation₁ hS Y :=
    of_conflation ((ExactStructure.IsMonoidal.isConflationExact_tensorRight Y).map_conflation hS)

/-- Multiplication on exact `K₀`, as a biadditive map. -/
noncomputable def mulHom : ExactK0 E →+ ExactK0 E →+ ExactK0 E :=
  (mulInvariant E).bilift

variable {E}

/-- Multiplication evaluates on classes of objects as the class of their tensor product. -/
private lemma mulHom_of_of (X Y : C) : mulHom E (of X) (of Y) = of (X ⊗ Y) :=
  (mulInvariant E).bilift_of_of X Y

/-- The multiplication on exact `K₀` induced by the tensor product. -/
noncomputable instance instMul : Mul (ExactK0 E) where
  mul a b := mulHom E a b

/-- The multiplication on exact `K₀` is `TauCeti.ExactK0.mulHom`. -/
lemma mul_def (a b : ExactK0 E) : a * b = mulHom E a b := (rfl)

/-- The unit of exact `K₀` is the class of the tensor unit. -/
noncomputable instance instOne : One (ExactK0 E) where
  one := of (𝟙_ C)

omit [MonoidalPreadditive C] [E.IsMonoidal] in
/-- The unit of exact `K₀` is the class of the tensor unit. -/
lemma one_def : (1 : ExactK0 E) = of (𝟙_ C) := (rfl)

/-- The computation rule for the product: the class of a tensor product is the product of the
classes. -/
@[simp]
theorem of_mul_of (X Y : C) : (of X : ExactK0 E) * of Y = of (X ⊗ Y) :=
  mulHom_of_of X Y

-- This structure makes Mathlib's bundled multiplications `AddMonoidHom.mulLeft₃` and
-- `AddMonoidHom.mulRight₃` available for the associativity proof; it is private, so the `Ring`
-- instance below repeats its one-line fields rather than extending it.
/-- Exact `K₀` with the multiplication descended from the tensor product is a non-unital,
non-associative ring: the multiplication distributes over addition on both sides. -/
@[reducible]
private noncomputable def nonUnitalNonAssocRing : NonUnitalNonAssocRing (ExactK0 E) where
  left_distrib a b c := map_add (mulHom E a) b c
  right_distrib a b c := by rw [mul_def, mul_def, mul_def, map_add, AddMonoidHom.add_apply]
  zero_mul a := by rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero a := map_zero (mulHom E a)

section Associativity

attribute [local instance] nonUnitalNonAssocRing

/-- Associativity of the tensor multiplication, as the equality of the two bundled triple
products: this is the associator of `C`. -/
private theorem mulLeft₃_eq_mulRight₃ :
    (AddMonoidHom.mulLeft₃ : ExactK0 E →+ _) = AddMonoidHom.mulRight₃ := by
  refine hom_ext fun X => hom_ext fun Y => hom_ext fun Z => ?_
  simp only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply, of_mul_of]
  exact of_congr (α_ X Y Z)

end Associativity

-- Associativity comes from the associator of `C`, and the unit laws from its unitors.
/-- The tensor product makes the exact Grothendieck group of a monoidal exact category a ring, with
`[X] * [Y] = [X ⊗ Y]` and unit the class of the tensor unit. -/
noncomputable instance instRing : Ring (ExactK0 E) where
  __ := (inferInstance : AddCommGroup (ExactK0 E))
  left_distrib a b c := map_add (mulHom E a) b c
  right_distrib a b c := by rw [mul_def, mul_def, mul_def, map_add, AddMonoidHom.add_apply]
  zero_mul a := by rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero a := map_zero (mulHom E a)
  mul_assoc a b c := by
    simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun mulLeft₃_eq_mulRight₃ a) b) c
  one_mul a := by
    suffices h : mulHom E 1 = AddMonoidHom.id (ExactK0 E) by
      rw [mul_def, h, AddMonoidHom.id_apply]
    refine hom_ext fun X => ?_
    rw [one_def, mulHom_of_of, AddMonoidHom.id_apply]
    exact of_congr (λ_ X)
  mul_one a := by
    suffices h : (mulHom E).flip 1 = AddMonoidHom.id (ExactK0 E) by
      rw [mul_def, ← AddMonoidHom.flip_apply, h, AddMonoidHom.id_apply]
    refine hom_ext fun X => ?_
    rw [AddMonoidHom.flip_apply, one_def, mulHom_of_of, AddMonoidHom.id_apply]
    exact of_congr (ρ_ X)

/-- Two ring homomorphisms out of exact `K₀` agreeing on the classes of objects are equal. -/
@[ext]
theorem ringHom_ext {R : Type*} [NonAssocRing R] {f g : ExactK0 E →+* R}
    (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  RingHom.toAddMonoidHom_injective (hom_ext h)

section Lift

variable {R : Type*} [NonAssocRing R] (a : AdditiveInvariant E R) (hone : a.obj (𝟙_ C) = 1)
  (hmul : ∀ X Y : C, a.obj (X ⊗ Y) = a.obj X * a.obj Y)

/-- The ring homomorphism out of exact `K₀` induced by a conflation-additive invariant which sends
the tensor unit to `1` and is multiplicative on tensor products. With
`TauCeti.ExactK0.ringHom_ext` for uniqueness, this is the universal property of exact `K₀` as a
ring. -/
noncomputable def liftRingHom : ExactK0 E →+* R where
  toFun := lift a
  map_zero' := map_zero (lift a)
  map_add' := map_add (lift a)
  map_one' := by
    rw [one_def, lift_of]
    exact hone
  map_mul' := by
    rw [AddMonoidHom.map_mul_iff]
    refine hom_ext fun X => hom_ext fun Y => ?_
    simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, AddMonoidHom.compl₂_apply,
      AddMonoidHom.comp_apply, of_mul_of, lift_of]
    exact hmul X Y

/-- The induced ring homomorphism takes the class of an object to the value of the invariant. -/
@[simp]
lemma liftRingHom_of (X : C) : liftRingHom a hone hmul (of X) = a.obj X :=
  lift_of a X

/-- The additive homomorphism underlying `TauCeti.ExactK0.liftRingHom` is the additive lift of the
invariant. -/
@[simp]
lemma liftRingHom_toAddMonoidHom :
    ((liftRingHom a hone hmul : ExactK0 E →+* R) : ExactK0 E →+ R) = lift a :=
  hom_ext fun X => by rw [AddMonoidHom.coe_ofClass, liftRingHom_of, lift_of]

end Lift

variable (E) in
/-- **The comparison from split `K₀` is a ring homomorphism.** The canonical surjection
`TauCeti.ExactK0.fromSplit` from the split Grothendieck ring onto the exact one preserves the unit
and the product, since both are given by the tensor product on classes of objects. -/
noncomputable def fromSplitRingHom : SplitK0 C →+* ExactK0 E :=
  SplitK0.liftRingHom
    { obj := fun X => of X
      map_iso := fun _ _ e => of_congr e
      map_biprod := of_biprod }
    (one_def (E := E)).symm fun X Y => (of_mul_of X Y).symm

/-- The comparison ring homomorphism takes the class of an object to its class. -/
@[simp]
lemma fromSplitRingHom_of (X : C) : fromSplitRingHom E (SplitK0.of X) = of X :=
  SplitK0.liftRingHom_of _ _ _ X

/-- The additive homomorphism underlying `TauCeti.ExactK0.fromSplitRingHom` is
`TauCeti.ExactK0.fromSplit`. -/
@[simp]
lemma fromSplitRingHom_toAddMonoidHom :
    ((fromSplitRingHom E : SplitK0 C →+* ExactK0 E) : SplitK0 C →+ ExactK0 E) = fromSplit E :=
  fromSplit_unique _ fun X => by rw [AddMonoidHom.coe_ofClass, fromSplitRingHom_of]

/-- The comparison from split to exact Grothendieck rings is bijective when every
conflation splits. -/
theorem fromSplitRingHom_bijective
    (hsplit : ∀ {S : ShortComplex C}, E.Conflation S → Nonempty S.Splitting) :
    Function.Bijective (fromSplitRingHom E : SplitK0 C →+* ExactK0 E) := by
  have heq : ⇑(fromSplitEquiv hsplit) = ⇑(fromSplitRingHom E) := by
    funext x
    rw [fromSplitEquiv_apply]
    exact (congrArg (fun f : SplitK0 C →+ ExactK0 E ↦ f x)
      (fromSplitRingHom_toAddMonoidHom (E := E))).symm
  exact heq ▸ (fromSplitEquiv hsplit).bijective

/-- The split and exact Grothendieck rings are canonically isomorphic when every
conflation splits. -/
noncomputable def fromSplitRingEquiv
    (hsplit : ∀ {S : ShortComplex C}, E.Conflation S → Nonempty S.Splitting) :
    SplitK0 C ≃+* ExactK0 E :=
  RingEquiv.ofBijective (fromSplitRingHom E) (fromSplitRingHom_bijective hsplit)

/-- The ring equivalence acts by the canonical split-to-exact comparison. -/
@[simp]
lemma fromSplitRingEquiv_apply
    (hsplit : ∀ {S : ShortComplex C}, E.Conflation S → Nonempty S.Splitting) (x : SplitK0 C) :
    fromSplitRingEquiv hsplit x = fromSplit E x := by
  exact congrArg (fun f : SplitK0 C →+ ExactK0 E ↦ f x)
    (fromSplitRingHom_toAddMonoidHom (E := E))

/-- The inverse ring equivalence sends an exact object class to its split class. -/
@[simp]
lemma fromSplitRingEquiv_symm_apply_of
    (hsplit : ∀ {S : ShortComplex C}, E.Conflation S → Nonempty S.Splitting) (X : C) :
    (fromSplitRingEquiv hsplit).symm (of X) = SplitK0.of X := by
  apply (fromSplitRingEquiv hsplit).injective
  simp

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [EssentiallySmall.{w} C]
  {E : ExactStructure C} [E.IsMonoidal]

/-- For a braided monoidal exact category the ring structure on exact `K₀` is commutative:
`[X] * [Y] = [X ⊗ Y] = [Y ⊗ X] = [Y] * [X]` by the braiding of `C`. -/
noncomputable instance instCommRing : CommRing (ExactK0 E) where
  __ := instRing
  mul_comm a b := by
    suffices h : (AddMonoidHom.mul : ExactK0 E →+ ExactK0 E →+ ExactK0 E) = AddMonoidHom.mul.flip by
      simpa only [AddMonoidHom.flip_apply, AddMonoidHom.mul_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun h a) b
    refine hom_ext fun X => hom_ext fun Y => ?_
    rw [AddMonoidHom.flip_apply, AddMonoidHom.mul_apply, AddMonoidHom.mul_apply, of_mul_of,
      of_mul_of]
    exact of_congr (β_ X Y)

end CommRing

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [EssentiallySmall.{w'} D]
  {E : ExactStructure C} [E.IsMonoidal] {E' : ExactStructure D} [E'.IsMonoidal]

/-- The ring homomorphism of exact Grothendieck groups induced by a conflation-exact monoidal
additive functor: the functorial map `TauCeti.ExactK0.map`, which the comparison isomorphisms of
`F` make unit-preserving and multiplicative on tensor products. -/
noncomputable def mapRingHom (F : C ⥤ D) [F.Additive] [F.Monoidal]
    (hF : E.IsConflationExact E' F) : ExactK0 E →+* ExactK0 E' :=
  liftRingHom ((liftEquiv (E := E) (G := ExactK0 E')).symm (map F hF))
    (by
      simp only [liftEquiv_symm_apply_obj, one_def, map_of]
      exact of_congr (Functor.Monoidal.εIso F).symm)
    fun X Y => by
      simp only [liftEquiv_symm_apply_obj, map_of, of_mul_of]
      exact of_congr (Functor.Monoidal.μIso F X Y).symm

/-- The additive homomorphism underlying `TauCeti.ExactK0.mapRingHom` is the functorial map. -/
@[simp]
lemma mapRingHom_toAddMonoidHom (F : C ⥤ D) [F.Additive] [F.Monoidal]
    (hF : E.IsConflationExact E' F) :
    ((mapRingHom F hF : ExactK0 E →+* ExactK0 E') : ExactK0 E →+ ExactK0 E') = map F hF := by
  rw [mapRingHom, liftRingHom_toAddMonoidHom, ← liftEquiv_apply, Equiv.apply_symm_apply]

/-- The induced ring homomorphism takes the class of an object to the class of its image. -/
@[simp]
lemma mapRingHom_of (F : C ⥤ D) [F.Additive] [F.Monoidal] (hF : E.IsConflationExact E' F)
    (X : C) : mapRingHom F hF (of X : ExactK0 E) = of (F.obj X) := by
  rw [← AddMonoidHom.coe_ofClass, mapRingHom_toAddMonoidHom, map_of]

/-- `TauCeti.ExactK0.mapRingHom` sends the identity functor to the identity ring homomorphism. -/
@[simp]
lemma mapRingHom_id :
    mapRingHom (𝟭 C) ExactStructure.IsConflationExact.id = RingHom.id (ExactK0 E) :=
  ringHom_ext fun X => by rw [mapRingHom_of, RingHom.id_apply, Functor.id_obj]

/-- `TauCeti.ExactK0.mapRingHom` sends a composite of conflation-exact monoidal additive functors
to the composite ring homomorphism. -/
lemma mapRingHom_comp {K : Type u''} [Category.{v''} K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] [MonoidalCategory K] [MonoidalPreadditive K] [EssentiallySmall.{w''} K]
    {E'' : ExactStructure K} [E''.IsMonoidal] (F : C ⥤ D) (G : D ⥤ K) [F.Additive] [G.Additive]
    [F.Monoidal] [G.Monoidal] (hF : E.IsConflationExact E' F) (hG : E'.IsConflationExact E'' G) :
    mapRingHom (F ⋙ G) (hF.comp hG) = (mapRingHom G hG).comp (mapRingHom F hF) :=
  ringHom_ext fun X => by
    rw [mapRingHom_of, RingHom.coe_comp, Function.comp_apply, mapRingHom_of, mapRingHom_of,
      Functor.comp_obj]

end Functoriality

end ExactK0

end TauCeti
