/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import TauCeti.CategoryTheory.Category.QuiverTotal

/-!
# Universal property and base-change equivalences of weak fiber products

For functors `L : A ⥤ T` and `R : B ⥤ T`, the comma category `CategoryTheory.Comma L R` has
objects `(a, b, h)` with `h : L.obj a ⟶ R.obj b` and commuting pairs of arrows as morphisms. Over
a groupoid `T`, every structure arrow `h` is invertible, so `Comma L R` is canonically equivalent
to the categorical pullback `L ⊡ R` (`CategoryTheory.Comma.equivCategoricalPullback`) while
retaining a single morphism `h` in its object carrier.

This module develops the 2-categorical universal property and base-change calculus of `Comma L R`:
`objectEquiv` identifies objects with the fiber product of `Prod.map L.obj R.obj` and
`(left, right) : Quiver.Total T → T × T`; `Comma.lift`, `natTransMk`, `natIsoMk`, and `liftNatIso`
establish the 2-categorical universal property up to unique natural isomorphism; and
`flipEquivalence`, `idLeftEquivalence`, `idRightEquivalence`, `assocEquivalence`,
`pastingRightEquivalence`, and `pastingLeftEquivalence` supply symmetry, identity pullbacks,
associativity, and pasting of weak pullback squares.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

namespace CategoryTheory.Comma

open Category Limits

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

section ObjectEquiv

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]

/-- Objects of `Comma L R` correspond to pairs `((a, b), w)` in `(A × B) × Quiver.Total T` whose
endpoints match `(L.obj a, R.obj b)`. -/
def objectEquiv (L : A ⥤ T) (R : B ⥤ T) :
    Comma L R ≃
      {p : (A × B) × Quiver.Total T // Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} where
  toFun X := ⟨((X.left, X.right), ⟨L.obj X.left, R.obj X.right, X.hom⟩), rfl⟩
  invFun p := ⟨p.val.1.1, p.val.1.2,
    Quiver.homOfEq p.val.2.hom (Prod.mk.inj p.property).1.symm (Prod.mk.inj p.property).2.symm⟩
  left_inv X := by cases X; rfl
  right_inv := by
    rintro ⟨⟨⟨a, b⟩, ⟨t₁, t₂, h⟩⟩, hp⟩
    obtain ⟨hl, hr⟩ := Prod.mk.inj hp
    dsimp only [Prod.map_apply] at hl hr
    subst hl hr; rfl

@[simp] theorem objectEquiv_apply_coe (L : A ⥤ T) (R : B ⥤ T) (X : Comma L R) :
    (objectEquiv L R X : (A × B) × Quiver.Total T) =
      ((X.left, X.right), ⟨L.obj X.left, R.obj X.right, X.hom⟩) := (rfl)

@[simp] theorem objectEquiv_symm_apply_left (L : A ⥤ T) (R : B ⥤ T)
    (p : {p : (A × B) × Quiver.Total T // Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)}) :
    ((objectEquiv L R).symm p).left = p.val.1.1 := (rfl)

@[simp] theorem objectEquiv_symm_apply_right (L : A ⥤ T) (R : B ⥤ T)
    (p : {p : (A × B) × Quiver.Total T // Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)}) :
    ((objectEquiv L R).symm p).right = p.val.1.2 := (rfl)

@[simp] theorem objectEquiv_symm_apply_totalHom (L : A ⥤ T) (R : B ⥤ T)
    (p : {p : (A × B) × Quiver.Total T // Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)}) :
    (⟨_, _, ((objectEquiv L R).symm p).hom⟩ : Quiver.Total T) = p.val.2 :=
  Quiver.Total.mk_homOfEq p.val.2 (Prod.mk.inj p.property).1.symm (Prod.mk.inj p.property).2.symm

end ObjectEquiv

section UniversalProperty

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T] {D : Type u₄} [Category.{v₄} D]
  {L : A ⥤ T} {R : B ⥤ T}

/-- The universal functor `D ⥤ Comma L R` induced by `F : D ⥤ A`, `G : D ⥤ B`, and a natural
transformation `α : F ⋙ L ⟶ G ⋙ R`. -/
@[expose, implicit_reducible, simps!]
protected def lift (F : D ⥤ A) (G : D ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) : D ⥤ Comma L R where
  obj d := ⟨F.obj d, G.obj d, α.app d⟩
  map f := ⟨F.map f, G.map f, α.naturality f⟩

@[simp] theorem lift_fst (F : D ⥤ A) (G : D ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) :
    Comma.lift F G α ⋙ fst L R = F := (rfl)

@[simp] theorem lift_snd (F : D ⥤ A) (G : D ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) :
    Comma.lift F G α ⋙ snd L R = G := (rfl)

@[simp] theorem whiskerLeft_lift_natTrans (F : D ⥤ A) (G : D ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) :
    Functor.whiskerLeft (Comma.lift F G α) (natTrans L R) = α := by ext; rfl

@[simp] theorem lift_whiskerLeft_natTrans (H : D ⥤ Comma L R) :
    Comma.lift (H ⋙ fst L R) (H ⋙ snd L R) (Functor.whiskerLeft H (natTrans L R)) = H := (rfl)

/-- Two natural transformations into `Comma L R` are equal when their left and right projections
are equal. -/
theorem natTrans_ext {H₁ H₂ : D ⥤ Comma L R} {η θ : H₁ ⟶ H₂}
    (hl : Functor.whiskerRight η (fst L R) = Functor.whiskerRight θ (fst L R))
    (hr : Functor.whiskerRight η (snd L R) = Functor.whiskerRight θ (snd L R)) :
    η = θ := by
  ext d
  · exact NatTrans.congr_app hl d
  · exact NatTrans.congr_app hr d

section NatTransMk

variable {H₁ H₂ : D ⥤ Comma L R}
  (φ : H₁ ⋙ fst L R ⟶ H₂ ⋙ fst L R) (ψ : H₁ ⋙ snd L R ⟶ H₂ ⋙ snd L R)
  (hw : ∀ d, L.map (φ.app d) ≫ (H₂.obj d).hom = (H₁.obj d).hom ≫ R.map (ψ.app d))

/-- Construct a natural transformation between functors into `Comma L R` from compatible natural
transformations on the two projections. -/
def natTransMk : H₁ ⟶ H₂ where
  app d := ⟨φ.app d, ψ.app d, hw d⟩
  naturality _ _ f := hom_ext _ _ (φ.naturality f) (ψ.naturality f)

@[simp] theorem natTransMk_app_left (d : D) : ((natTransMk φ ψ hw).app d).left = φ.app d := (rfl)

@[simp] theorem natTransMk_app_right (d : D) : ((natTransMk φ ψ hw).app d).right = ψ.app d := (rfl)

@[simp] theorem whiskerRight_natTransMk_fst :
    Functor.whiskerRight (natTransMk φ ψ hw) (fst L R) = φ := (rfl)

@[simp] theorem whiskerRight_natTransMk_snd :
    Functor.whiskerRight (natTransMk φ ψ hw) (snd L R) = ψ := (rfl)

end NatTransMk

section NatIsoMk

variable {H₁ H₂ : D ⥤ Comma L R}
  (φ : H₁ ⋙ fst L R ≅ H₂ ⋙ fst L R) (ψ : H₁ ⋙ snd L R ≅ H₂ ⋙ snd L R)
  (hw : ∀ d, L.map (φ.hom.app d) ≫ (H₂.obj d).hom = (H₁.obj d).hom ≫ R.map (ψ.hom.app d))

/-- Construct a natural isomorphism between functors into `Comma L R` from compatible natural
isomorphisms on the two projections. -/
def natIsoMk : H₁ ≅ H₂ :=
  NatIso.ofComponents (fun d ↦ isoMk (φ.app d) (ψ.app d) (hw d)) fun f ↦
    hom_ext _ _ (φ.hom.naturality f) (ψ.hom.naturality f)

@[simp] theorem natIsoMk_hom_app_left (d : D) :
    ((natIsoMk φ ψ hw).hom.app d).left = φ.hom.app d := (rfl)

@[simp] theorem natIsoMk_hom_app_right (d : D) :
    ((natIsoMk φ ψ hw).hom.app d).right = ψ.hom.app d := (rfl)

@[simp] theorem natIsoMk_inv_app_left (d : D) :
    ((natIsoMk φ ψ hw).inv.app d).left = φ.inv.app d := (rfl)

@[simp] theorem natIsoMk_inv_app_right (d : D) :
    ((natIsoMk φ ψ hw).inv.app d).right = ψ.inv.app d := (rfl)

@[simp] theorem whiskerRight_natIsoMk_hom_fst :
    Functor.whiskerRight (natIsoMk φ ψ hw).hom (fst L R) = φ.hom := by ext; rfl

@[simp] theorem whiskerRight_natIsoMk_hom_snd :
    Functor.whiskerRight (natIsoMk φ ψ hw).hom (snd L R) = ψ.hom := by ext; rfl

end NatIsoMk

section LiftNatIso

variable {F : D ⥤ A} {G : D ⥤ B} (α : F ⋙ L ⟶ G ⋙ R) (H : D ⥤ Comma L R)
  (e₁ : H ⋙ fst L R ≅ F) (e₂ : H ⋙ snd L R ≅ G)
  (hw : ∀ d, L.map (e₁.hom.app d) ≫ α.app d = (H.obj d).hom ≫ R.map (e₂.hom.app d))

/-- **2-categorical uniqueness of lifts up to natural isomorphism.** Any functor `H : D ⥤ Comma L R`
equipped with natural isomorphisms `e₁ : H ⋙ fst L R ≅ F` and `e₂ : H ⋙ snd L R ≅ G` compatible
with `α : F ⋙ L ⟶ G ⋙ R` is naturally isomorphic to `Comma.lift F G α`. -/
def liftNatIso : H ≅ Comma.lift F G α :=
  natIsoMk e₁ e₂ hw

@[simp] theorem liftNatIso_hom_app_left (d : D) :
    ((liftNatIso α H e₁ e₂ hw).hom.app d).left = e₁.hom.app d := (rfl)

@[simp] theorem liftNatIso_hom_app_right (d : D) :
    ((liftNatIso α H e₁ e₂ hw).hom.app d).right = e₂.hom.app d := (rfl)

/-- The natural isomorphism `liftNatIso` is the unique natural isomorphism `H ≅ Comma.lift F G α`
inducing `e₁` and `e₂` on the two projections. -/
theorem eq_liftNatIso (e : H ≅ Comma.lift F G α)
    (h₁ : Functor.whiskerRight e.hom (fst L R) = e₁.hom)
    (h₂ : Functor.whiskerRight e.hom (snd L R) = e₂.hom) :
    e = liftNatIso α H e₁ e₂ hw := by
  ext d
  · exact NatTrans.congr_app h₁ d
  · exact NatTrans.congr_app h₂ d

end LiftNatIso

end UniversalProperty

section CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]

open scoped CategoricalPullback

/-- Forgetting the inverse of the structural isomorphism embeds the categorical pullback `L ⊡ R`
fully and faithfully into `Comma L R`. -/
@[expose, implicit_reducible, simps!]
def fromCategoricalPullback (L : A ⥤ T) (R : B ⥤ T) : (L ⊡ R) ⥤ Comma L R where
  obj X := ⟨X.fst, X.snd, X.iso.hom⟩
  map f := ⟨f.fst, f.snd, f.w⟩

/-- Over a groupoid `T`, every structure arrow of `Comma L R` is an isomorphism, giving the inverse
functor `Comma L R ⥤ L ⊡ R`. -/
@[expose, implicit_reducible, simps!]
noncomputable def toCategoricalPullback (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    Comma L R ⥤ (L ⊡ R) where
  obj X := ⟨X.left, X.right, asIso X.hom⟩
  map f := ⟨f.left, f.right, f.w⟩

/-- Over a groupoid `T`, the comma category `Comma L R` is canonically equivalent to the
categorical pullback `L ⊡ R`. -/
noncomputable def equivCategoricalPullback (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    Comma L R ≌ (L ⊡ R) where
  functor := toCategoricalPullback L R
  inverse := fromCategoricalPullback L R
  unitIso := NatIso.ofComponents
    (fun X ↦ isoMk (Iso.refl X.left) (Iso.refl X.right) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  counitIso := NatIso.ofComponents
    (fun X ↦ CategoricalPullback.mkIso (Iso.refl X.fst) (Iso.refl X.snd) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  functor_unitIso_comp _ := by dsimp; ext <;> simp

@[simp] theorem equivCategoricalPullback_functor (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    (equivCategoricalPullback L R).functor = toCategoricalPullback L R := (rfl)

@[simp] theorem equivCategoricalPullback_inverse (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    (equivCategoricalPullback L R).inverse = fromCategoricalPullback L R := (rfl)

end CategoricalPullback

section SymmetryAndIdentity

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]

/-- Over a groupoid `T`, swapping the left and right components and inverting the structure arrow
gives a functor `Comma L R ⥤ Comma R L`. -/
@[expose, implicit_reducible, simps!]
noncomputable def flipFunctor (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    Comma L R ⥤ Comma R L where
  obj X := ⟨X.right, X.left, inv X.hom⟩
  map f := ⟨f.right, f.left, by
    dsimp only; rw [IsIso.comp_inv_eq, assoc, f.w, IsIso.inv_hom_id_assoc]⟩

/-- Over a groupoid `T`, weak fiber products are symmetric up to canonical equivalence:
`Comma L R ≌ Comma R L`. -/
noncomputable def flipEquivalence (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    Comma L R ≌ Comma R L where
  functor := flipFunctor L R
  inverse := flipFunctor R L
  unitIso := NatIso.ofComponents
    (fun X ↦ isoMk (Iso.refl X.left) (Iso.refl X.right) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  counitIso := NatIso.ofComponents
    (fun X ↦ isoMk (Iso.refl X.left) (Iso.refl X.right) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  functor_unitIso_comp _ := by dsimp; ext <;> simp

@[simp] theorem flipEquivalence_functor (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    (flipEquivalence L R).functor = flipFunctor L R := (rfl)

@[simp] theorem flipEquivalence_inverse (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T] :
    (flipEquivalence L R).inverse = flipFunctor R L := (rfl)

/-- The canonical section `B ⥤ Comma (𝟭 T) R` sending `b` to `(R.obj b, b, 𝟙 (R.obj b))`. -/
@[expose, implicit_reducible, simps!]
def fromRight (R : B ⥤ T) : B ⥤ Comma (𝟭 T) R where
  obj b := ⟨R.obj b, b, 𝟙 (R.obj b)⟩
  map f := { left := R.map f, right := f }

/-- Over a groupoid `T`, pulling back along the identity functor `𝟭 T` on the left recovers `B`:
`Comma (𝟭 T) R ≌ B`. -/
noncomputable def idLeftEquivalence (R : B ⥤ T) [IsGroupoid T] :
    Comma (𝟭 T) R ≌ B where
  functor := snd (𝟭 T) R
  inverse := fromRight R
  unitIso := NatIso.ofComponents
    (fun X ↦ isoMk (asIso X.hom) (Iso.refl X.right) (by dsimp; simp))
    (fun f ↦ by
      dsimp; ext
      · simpa using f.w
      · simp)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by dsimp; simp)
  functor_unitIso_comp _ := by dsimp; simp

@[simp] theorem idLeftEquivalence_functor (R : B ⥤ T) [IsGroupoid T] :
    (idLeftEquivalence R).functor = snd (𝟭 T) R := (rfl)

@[simp] theorem idLeftEquivalence_inverse (R : B ⥤ T) [IsGroupoid T] :
    (idLeftEquivalence R).inverse = fromRight R := (rfl)

/-- The canonical section `A ⥤ Comma L (𝟭 T)` sending `a` to `(a, L.obj a, 𝟙 (L.obj a))`. -/
@[expose, implicit_reducible, simps!]
def fromLeft (L : A ⥤ T) : A ⥤ Comma L (𝟭 T) where
  obj a := ⟨a, L.obj a, 𝟙 (L.obj a)⟩
  map f := { left := f, right := L.map f }

/-- Over a groupoid `T`, pulling back along the identity functor `𝟭 T` on the right recovers `A`:
`Comma L (𝟭 T) ≌ A`. -/
noncomputable def idRightEquivalence (L : A ⥤ T) [IsGroupoid T] :
    Comma L (𝟭 T) ≌ A where
  functor := fst L (𝟭 T)
  inverse := fromLeft L
  unitIso := NatIso.ofComponents
    (fun X ↦ isoMk (Iso.refl X.left) (asIso X.hom).symm (by dsimp; simp))
    (fun {X Y} f ↦ by
      dsimp; ext
      · simp
      · simp only [comp_right, isoMk_hom_right, Iso.symm_hom, asIso_inv, fromLeft_map_right]
        have hw : L.map f.left ≫ Y.hom = X.hom ≫ f.right := f.w
        rw [IsIso.comp_inv_eq, assoc, hw, IsIso.inv_hom_id_assoc])
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by dsimp; simp)
  functor_unitIso_comp _ := by dsimp; simp

@[simp] theorem idRightEquivalence_functor (L : A ⥤ T) [IsGroupoid T] :
    (idRightEquivalence L).functor = fst L (𝟭 T) := (rfl)

@[simp] theorem idRightEquivalence_inverse (L : A ⥤ T) [IsGroupoid T] :
    (idRightEquivalence L).inverse = fromLeft L := (rfl)

end SymmetryAndIdentity

section BaseChangeAndPasting

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₄} [Category.{v₄} C] {T : Type u₃} [Category.{v₃} T]
  {S : Type u₅} [Category.{v₅} S]

/-- Reassociating an iterated comma category `(A ×_T B) ×_S C` into `A ×_T (B ×_S C)`. -/
@[expose, implicit_reducible, simps!]
def assocFunctor (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : C ⥤ S) :
    Comma (snd L F ⋙ G) M ⥤ Comma L (fst G M ⋙ F) where
  obj P := ⟨P.left.left, ⟨P.left.right, P.right, P.hom⟩, P.left.hom⟩
  map φ := ⟨φ.left.left, ⟨φ.left.right, φ.right, φ.w⟩, φ.left.w⟩

/-- Inverse reassociation `A ×_T (B ×_S C) ⥤ (A ×_T B) ×_S C`. -/
@[expose, implicit_reducible, simps!]
def assocInverse (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : C ⥤ S) :
    Comma L (fst G M ⋙ F) ⥤ Comma (snd L F ⋙ G) M where
  obj Q := ⟨⟨Q.left, Q.right.left, Q.hom⟩, Q.right.right, Q.right.hom⟩
  map ψ := ⟨⟨ψ.left, ψ.right.left, ψ.w⟩, ψ.right.right, ψ.right.w⟩

/-- Iterated comma categories are associative:
`Comma (snd L F ⋙ G) M ≌ Comma L (fst G M ⋙ F)`. -/
def assocEquivalence (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : C ⥤ S) :
    Comma (snd L F ⋙ G) M ≌ Comma L (fst G M ⋙ F) where
  functor := assocFunctor L F G M
  inverse := assocInverse L F G M
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by dsimp; ext <;> simp)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by dsimp; ext <;> simp)
  functor_unitIso_comp _ := by dsimp; ext <;> simp

@[simp] theorem assocEquivalence_functor (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : C ⥤ S) :
    (assocEquivalence L F G M).functor = assocFunctor L F G M := (rfl)

@[simp] theorem assocEquivalence_inverse (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : C ⥤ S) :
    (assocEquivalence L F G M).inverse = assocInverse L F G M := (rfl)

/-- Pasting two comma squares on the right, sending `((a, b, h), c, k)` to `(a, c, h ≫ R.map k)`. -/
@[expose, implicit_reducible, simps!]
def pastingRightFunctor (L : A ⥤ T) (R : B ⥤ T) (M : C ⥤ B) :
    Comma (snd L R) M ⥤ Comma L (M ⋙ R) where
  obj P := ⟨P.left.left, P.right, P.left.hom ≫ R.map P.hom⟩
  map {P P'} φ := ⟨φ.left.left, φ.right, by
    dsimp only
    have hw : φ.left.right ≫ P'.hom = P.hom ≫ M.map φ.right := φ.w
    rw [← assoc, φ.left.w, assoc, ← R.map_comp, hw, R.map_comp, Functor.comp_map, assoc]⟩

/-- The canonical section `Comma L (M ⋙ R) ⥤ Comma (snd L R) M` inserting an identity morphism in
`B`. -/
@[expose, implicit_reducible, simps!]
def pastingRightInverse (L : A ⥤ T) (R : B ⥤ T) (M : C ⥤ B) :
    Comma L (M ⋙ R) ⥤ Comma (snd L R) M where
  obj Q := ⟨⟨Q.left, M.obj Q.right, Q.hom⟩, Q.right, 𝟙 (M.obj Q.right)⟩
  map ψ := { left := ⟨ψ.left, M.map ψ.right, ψ.w⟩, right := ψ.right }

/-- **Right pasting law for weak fiber products.** When `B` is a groupoid, pulling `L : A ⥤ T` back
along `R : B ⥤ T` and then along `M : C ⥤ B` is canonically equivalent to pulling `L` back along
the composite `M ⋙ R`: `Comma (snd L R) M ≌ Comma L (M ⋙ R)`. -/
noncomputable def pastingRightEquivalence (L : A ⥤ T) (R : B ⥤ T) (M : C ⥤ B) [IsGroupoid B] :
    Comma (snd L R) M ≌ Comma L (M ⋙ R) where
  functor := pastingRightFunctor L R M
  inverse := pastingRightInverse L R M
  unitIso := NatIso.ofComponents
    (fun P ↦ isoMk (isoMk (Iso.refl P.left.left) (asIso P.hom) (by dsimp; simp))
      (Iso.refl P.right) (by dsimp; simp))
    (fun φ ↦ by
      dsimp; ext
      · simp
      · simpa using φ.w
      · simp)
  counitIso := NatIso.ofComponents
    (fun Q ↦ isoMk (Iso.refl Q.left) (Iso.refl Q.right) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  functor_unitIso_comp _ := by dsimp; ext <;> simp

@[simp] theorem pastingRightEquivalence_functor (L : A ⥤ T) (R : B ⥤ T) (M : C ⥤ B)
    [IsGroupoid B] : (pastingRightEquivalence L R M).functor = pastingRightFunctor L R M := (rfl)

@[simp] theorem pastingRightEquivalence_inverse (L : A ⥤ T) (R : B ⥤ T) (M : C ⥤ B)
    [IsGroupoid B] : (pastingRightEquivalence L R M).inverse = pastingRightInverse L R M := (rfl)

/-- Pasting two comma squares on the left, sending `(c, (a, b, h), k)` to `(c, b, L.map k ≫ h)`. -/
@[expose, implicit_reducible, simps!]
def pastingLeftFunctor (N : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    Comma N (fst L R) ⥤ Comma (N ⋙ L) R where
  obj P := ⟨P.left, P.right.right, L.map P.hom ≫ P.right.hom⟩
  map φ := ⟨φ.left, φ.right.right, by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← assoc, ← L.map_comp, φ.w, fst_map, L.map_comp, assoc, φ.right.w, assoc]⟩

/-- The canonical section `Comma (N ⋙ L) R ⥤ Comma N (fst L R)` inserting an identity morphism in
`A`. -/
@[expose, implicit_reducible, simps!]
def pastingLeftInverse (N : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    Comma (N ⋙ L) R ⥤ Comma N (fst L R) where
  obj Q := ⟨Q.left, ⟨N.obj Q.left, Q.right, Q.hom⟩, 𝟙 (N.obj Q.left)⟩
  map ψ := { left := ψ.left, right := ⟨N.map ψ.left, ψ.right, ψ.w⟩ }

/-- **Left pasting law for weak fiber products.** When `A` is a groupoid, pulling `fst L R` back
along `N : C ⥤ A` is canonically equivalent to pulling `R` back along `N ⋙ L`:
`Comma N (fst L R) ≌ Comma (N ⋙ L) R`. -/
noncomputable def pastingLeftEquivalence (N : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid A] :
    Comma N (fst L R) ≌ Comma (N ⋙ L) R where
  functor := pastingLeftFunctor N L R
  inverse := pastingLeftInverse N L R
  unitIso := NatIso.ofComponents
    (fun P ↦ isoMk (Iso.refl P.left)
      (isoMk (asIso P.hom).symm (Iso.refl P.right.right) (by
        dsimp
        rw [Functor.map_id, comp_id, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
          Functor.map_id, id_comp]))
      (by dsimp; simp))
    (fun {P P'} φ ↦ by
      dsimp; ext
      · simp
      · simp only [comp_right, comp_left, isoMk_hom_right, isoMk_hom_left, Iso.symm_hom, asIso_inv,
          pastingLeftInverse_map_right_left, pastingLeftFunctor_map_left]
        have hw : N.map φ.left ≫ P'.hom = P.hom ≫ φ.right.left := φ.w
        rw [IsIso.comp_inv_eq, assoc, hw, IsIso.inv_hom_id_assoc]
      · simp)
  counitIso := NatIso.ofComponents
    (fun Q ↦ isoMk (Iso.refl Q.left) (Iso.refl Q.right) (by dsimp; simp))
    (fun _ ↦ by dsimp; ext <;> simp)
  functor_unitIso_comp _ := by dsimp; ext <;> simp

@[simp] theorem pastingLeftEquivalence_functor (N : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
    [IsGroupoid A] : (pastingLeftEquivalence N L R).functor = pastingLeftFunctor N L R := (rfl)

@[simp] theorem pastingLeftEquivalence_inverse (N : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
    [IsGroupoid A] : (pastingLeftEquivalence N L R).inverse = pastingLeftInverse N L R := (rfl)

end BaseChangeAndPasting

end CategoryTheory.Comma
