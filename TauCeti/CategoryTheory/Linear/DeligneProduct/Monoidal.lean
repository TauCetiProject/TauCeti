/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import TauCeti.CategoryTheory.Linear.DeligneProduct.Basic
public import TauCeti.CategoryTheory.Monoidal.Envelope.Mat.Linear

/-!
# The monoidal structure on the Deligne tensor product

For two monoidal linear categories over a commutative semiring, the tensor product of pairs
in `LinearTensor k C D` is componentwise, as are the associator and unitors. On morphisms the
tensor product is the bilinear extension of `(f ⊗ g) ⊗ₘ (f' ⊗ g') = (f ⊗ₘ f') ⊗ (g ⊗ₘ g')`.
The Deligne product inherits its tensor product from the matrix category, so the tensor product
of two finite families is indexed by the product of their index types.

The canonical functor from the ordinary product category to the Deligne product is strong
monoidal. Its tensorator identifies the tensor product of two one-term families with the
one-term family on their componentwise tensor product.

## Main declarations

* `LinearTensor.instMonoidalCategory`, `LinearTensor.instMonoidalPreadditive` and
  `LinearTensor.instMonoidalLinear` equip pairs with their componentwise tensor.
  `LinearTensor.tmul_tensorHom_tmul` computes the tensor of two pure morphisms.
* `DeligneProduct.uncurryBifunctorMonoidal` makes the inclusion of pairs strong monoidal.
  `DeligneProduct.uncurry_bifunctor_ε` and `DeligneProduct.uncurry_bifunctor_μ`
  identify its comparison morphisms with those of the matrix embedding.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*][egno15], §4.6.
-/

public section

open CategoryTheory MonoidalCategory Preadditive TensorProduct

universe w v₁ v₂ u₁ u₂

namespace TauCeti.LinearTensor

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

section Monoidal

local notation "tensorHomMap" =>
  TensorProduct.map₂ MonoidalCategory.tensorHomLinear MonoidalCategory.tensorHomLinear

/-- Tensor and coherence data on the linear tensor product are componentwise on pure tensors. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (LinearTensor k C D) where
  tensorObj P Q := ⟨P.fst ⊗ Q.fst, P.snd ⊗ Q.snd⟩
  tensorUnit := ⟨𝟙_ C, 𝟙_ D⟩
  tensorHom f g := tensorHomMap f g
  whiskerLeft P _ _ f := tensorHomMap (𝟙 P) f
  whiskerRight f P := tensorHomMap f (𝟙 P)
  associator P Q R := isoMk (α_ P.fst Q.fst R.fst) (α_ P.snd Q.snd R.snd)
  leftUnitor P := isoMk (λ_ P.fst) (λ_ P.snd)
  rightUnitor P := isoMk (ρ_ P.fst) (ρ_ P.snd)

/-- The tensor product of pairs is the pair of tensor products. -/
theorem tensorObj_def (P Q : LinearTensor k C D) :
    P ⊗ Q = ⟨P.fst ⊗ Q.fst, P.snd ⊗ Q.snd⟩ :=
  rfl

/-- The tensor unit is the pair of tensor units. -/
theorem tensorUnit_def : 𝟙_ (LinearTensor k C D) = ⟨𝟙_ C, 𝟙_ D⟩ :=
  rfl

/-- The first component of the tensor product is the tensor product of the first components. -/
@[simp]
theorem tensorObj_fst (P Q : LinearTensor k C D) : (P ⊗ Q).fst = P.fst ⊗ Q.fst :=
  (rfl)

/-- The second component of the tensor product is the tensor product of the second components. -/
@[simp]
theorem tensorObj_snd (P Q : LinearTensor k C D) : (P ⊗ Q).snd = P.snd ⊗ Q.snd :=
  (rfl)

/-- The first component of the tensor unit is the tensor unit of the first factor. -/
@[simp]
theorem tensorUnit_fst : (𝟙_ (LinearTensor k C D)).fst = 𝟙_ C :=
  (rfl)

/-- The second component of the tensor unit is the tensor unit of the second factor. -/
@[simp]
theorem tensorUnit_snd : (𝟙_ (LinearTensor k C D)).snd = 𝟙_ D :=
  (rfl)

/-- Tensoring pure morphisms uses the tensor product in each factor category. -/
@[simp]
theorem tmul_tensorHom_tmul {X Y X' Y' : C} {U V U' V' : D}
    (f : X ⟶ Y) (g : U ⟶ V) (f' : X' ⟶ Y') (g' : U' ⟶ V') :
    tmul (k := k) f g ⊗ₘ tmul f' g' = tmul (f ⊗ₘ f') (g ⊗ₘ g') := by
  -- Unfold the morphism tensor to apply the computation lemmas for tensor products of modules.
  change tensorHomMap (f ⊗ₜ[k] g) (f' ⊗ₜ[k] g') = (f ⊗ₘ f') ⊗ₜ[k] (g ⊗ₘ g')
  simp only [TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul, tensorHomLinear_apply]

/-- The associator is built from the two associators. -/
@[simp]
theorem associator_def (P Q R : LinearTensor k C D) :
    α_ P Q R = isoMk (α_ P.fst Q.fst R.fst) (α_ P.snd Q.snd R.snd) :=
  (rfl)

/-- The left unitor is built from the two left unitors. -/
@[simp]
theorem leftUnitor_def (P : LinearTensor k C D) :
    λ_ P = isoMk (λ_ P.fst) (λ_ P.snd) :=
  (rfl)

/-- The right unitor is built from the two right unitors. -/
@[simp]
theorem rightUnitor_def (P : LinearTensor k C D) :
    ρ_ P = isoMk (ρ_ P.fst) (ρ_ P.snd) :=
  (rfl)

/-- Tensoring in the linear tensor product preserves addition in the first variable. -/
private theorem add_tensorHom {P Q P' Q' : LinearTensor k C D} (f g : P ⟶ Q) (h : P' ⟶ Q') :
    (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h :=
  LinearMap.map_add₂ tensorHomMap f g h

/-- Tensoring in the linear tensor product preserves addition in the second variable. -/
private theorem tensorHom_add {P Q P' Q' : LinearTensor k C D} (f : P ⟶ Q) (g h : P' ⟶ Q') :
    f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h :=
  map_add (tensorHomMap f) g h

/-- The interchange law extends from pure tensors by additivity in the four morphisms. -/
private theorem tensorHom_comp {P₁ Q₁ R₁ P₂ Q₂ R₂ : LinearTensor k C D}
    (f₁ : P₁ ⟶ Q₁) (f₂ : P₂ ⟶ Q₂) (g₁ : Q₁ ⟶ R₁) (g₂ : Q₂ ⟶ R₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  obtain ⟨_, _⟩ := P₁
  obtain ⟨_, _⟩ := Q₁
  obtain ⟨_, _⟩ := R₁
  obtain ⟨_, _⟩ := P₂
  obtain ⟨_, _⟩ := Q₂
  obtain ⟨_, _⟩ := R₂
  induction f₁ using hom_induction_on with
  | add _ _ h₁ h₂ => simp only [add_tensorHom, add_comp, h₁, h₂]
  | tmul f₁ f₁' =>
    induction f₂ using hom_induction_on with
    | add _ _ h₁ h₂ => simp only [tensorHom_add, add_comp, h₁, h₂]
    | tmul f₂ f₂' =>
      induction g₁ using hom_induction_on with
      | add _ _ h₁ h₂ => simp only [add_tensorHom, comp_add, h₁, h₂]
      | tmul g₁ g₁' =>
        induction g₂ using hom_induction_on with
        | add _ _ h₁ h₂ => simp only [tensorHom_add, comp_add, h₁, h₂]
        | tmul g₂ g₂' =>
          simp only [tmul_tensorHom_tmul, tmul_comp_tmul, tensorHom_comp_tensorHom]

/-- Naturality of the componentwise associator extends from pure tensors by additivity. -/
private theorem associator_naturality_aux {P₁ P₂ P₃ Q₁ Q₂ Q₃ : LinearTensor k C D}
    (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) (h : P₃ ⟶ Q₃) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ Q₁ Q₂ Q₃).hom = (α_ P₁ P₂ P₃).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  obtain ⟨_, _⟩ := P₁
  obtain ⟨_, _⟩ := P₂
  obtain ⟨_, _⟩ := P₃
  obtain ⟨_, _⟩ := Q₁
  obtain ⟨_, _⟩ := Q₂
  obtain ⟨_, _⟩ := Q₃
  induction f using hom_induction_on with
  | add _ _ h₁ h₂ => simp only [add_tensorHom, add_comp, comp_add, h₁, h₂]
  | tmul f f' =>
    induction g using hom_induction_on with
    | add _ _ h₁ h₂ => simp only [tensorHom_add, add_tensorHom, add_comp, comp_add, h₁, h₂]
    | tmul g g' =>
      induction h using hom_induction_on with
      | add _ _ h₁ h₂ => simp only [tensorHom_add, add_comp, comp_add, h₁, h₂]
      | tmul h h' =>
        simp only [associator_def, isoMk_hom, tmul_tensorHom_tmul, tmul_comp_tmul,
          associator_naturality]

/-- The linear tensor product of two monoidal linear categories is monoidal. -/
instance instMonoidalCategory : MonoidalCategory (LinearTensor k C D) :=
  -- State the identity at the tensor unit so both unitor rewrites match it directly.
  have tmul_id_tensorUnit : tmul (𝟙 (𝟙_ C)) (𝟙 (𝟙_ D)) = 𝟙 (𝟙_ (LinearTensor k C D)) :=
    tmul_id_id _ _
  .ofTensorHom
    (id_tensorHom_id := fun P Q ↦ by
      rw [← tmul_id_id P.fst P.snd, ← tmul_id_id Q.fst Q.snd, tmul_tensorHom_tmul]
      simp only [id_tensorHom_id, tmul_id_id, tensorObj_def])
    (id_tensorHom := fun _ {_ _} _ ↦ rfl)
    (tensorHom_id := fun {_ _} _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := by exact tensorHom_comp)
    (associator_naturality := by exact associator_naturality_aux)
    (leftUnitor_naturality := fun {P Q} f ↦ by
      obtain ⟨_, _⟩ := P
      obtain ⟨_, _⟩ := Q
      induction f using hom_induction_on with
      | add _ _ h₁ h₂ => simp only [tensorHom_add, add_comp, comp_add, h₁, h₂]
      | tmul f g =>
        rw [← tmul_id_tensorUnit]
        simp only [leftUnitor_def, isoMk_hom, tmul_tensorHom_tmul, tmul_comp_tmul, id_tensorHom,
          leftUnitor_naturality])
    (rightUnitor_naturality := fun {P Q} f ↦ by
      obtain ⟨_, _⟩ := P
      obtain ⟨_, _⟩ := Q
      induction f using hom_induction_on with
      | add _ _ h₁ h₂ => simp only [add_tensorHom, add_comp, comp_add, h₁, h₂]
      | tmul f g =>
        rw [← tmul_id_tensorUnit]
        simp only [rightUnitor_def, isoMk_hom, tmul_tensorHom_tmul, tmul_comp_tmul, tensorHom_id,
          rightUnitor_naturality])
    (pentagon := fun W X Y Z ↦ by
      rw [← tmul_id_id W.fst W.snd, ← tmul_id_id Z.fst Z.snd]
      simp only [associator_def, isoMk_hom, tmul_tensorHom_tmul, tmul_comp_tmul,
        id_tensorHom, tensorHom_id, tensorObj_def, pentagon])
    (triangle := fun X Y ↦ by
      rw [← tmul_id_id X.fst X.snd, ← tmul_id_id Y.fst Y.snd]
      simp only [associator_def, leftUnitor_def, rightUnitor_def, isoMk_hom, tmul_tensorHom_tmul,
        tmul_comp_tmul, id_tensorHom, tensorHom_id, tensorUnit_def, triangle])

/-- Whiskering a pure tensor on the left is componentwise. -/
@[simp]
theorem whiskerLeft_tmul (P : LinearTensor k C D) {X Y : C} {U V : D}
    (f : X ⟶ Y) (g : U ⟶ V) :
    P ◁ tmul f g = tmul (P.fst ◁ f) (P.snd ◁ g) := by
  rw [← id_tensorHom, ← tmul_id_id P.fst P.snd, tmul_tensorHom_tmul]
  simp

/-- Whiskering a pure tensor on the right is componentwise. -/
@[simp]
theorem tmul_whiskerRight {X Y : C} {U V : D} (f : X ⟶ Y) (g : U ⟶ V)
    (P : LinearTensor k C D) :
    tmul f g ▷ P = tmul (f ▷ P.fst) (g ▷ P.snd) := by
  rw [← tensorHom_id, ← tmul_id_id P.fst P.snd, tmul_tensorHom_tmul]
  simp

/-- Tensoring in the linear tensor product is additive in each variable. -/
instance instMonoidalPreadditive : MonoidalPreadditive (LinearTensor k C D) where
  whiskerLeft_zero := fun {P _ _} ↦ map_zero (tensorHomMap (𝟙 P))
  zero_whiskerRight := fun {P _ _} ↦ LinearMap.map_zero₂ tensorHomMap (𝟙 P)
  whiskerLeft_add := fun {P _ _} f g ↦ map_add (tensorHomMap (𝟙 P)) f g
  add_whiskerRight := fun {P _ _} f g ↦ LinearMap.map_add₂ tensorHomMap f g (𝟙 P)

/-- Tensoring in the linear tensor product is linear in each variable. -/
instance instMonoidalLinear : MonoidalLinear k (LinearTensor k C D) where
  whiskerLeft_smul P {_ _} r f := map_smul (tensorHomMap (𝟙 P)) r f
  smul_whiskerRight r {_ _} f P := LinearMap.map_smul₂ tensorHomMap r f (𝟙 P)

end Monoidal

/-- The canonical functor from the ordinary product to the linear tensor product is
strong monoidal with identity comparison maps. -/
instance uncurryBifunctorMonoidal : (Functor.uncurry.obj (bifunctor k C D)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun f P ↦ by simp
      μIso_hom_natural_right := fun P f ↦ by simp
      associativity := fun X Y Z ↦ by simp
      left_unitality := fun X ↦ by simp
      right_unitality := fun X ↦ by simp }

/-- The canonical functor preserves the tensor unit with identity comparison. -/
@[simp]
theorem uncurry_bifunctor_ε :
    Functor.LaxMonoidal.ε (Functor.uncurry.obj (bifunctor k C D)) = 𝟙 _ :=
  (rfl)

/-- The canonical functor preserves tensor products with identity comparison. -/
@[simp]
theorem uncurry_bifunctor_μ (P Q : C × D) :
    Functor.LaxMonoidal.μ (Functor.uncurry.obj (bifunctor k C D)) P Q = 𝟙 _ :=
  (rfl)

/-- The inverse unit comparison is the identity. -/
@[simp]
theorem uncurry_bifunctor_η :
    Functor.OplaxMonoidal.η (Functor.uncurry.obj (bifunctor k C D)) = 𝟙 _ :=
  (rfl)

/-- The inverse tensor comparison is the identity. -/
@[simp]
theorem uncurry_bifunctor_δ (P Q : C × D) :
    Functor.OplaxMonoidal.δ (Functor.uncurry.obj (bifunctor k C D)) P Q = 𝟙 _ :=
  (rfl)

end TauCeti.LinearTensor

namespace TauCeti.DeligneProduct

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

/-- The canonical functor from the ordinary product to the Deligne product is strong monoidal. -/
noncomputable instance uncurryBifunctorMonoidal :
    (Functor.uncurry.obj (bifunctor k C D)).Monoidal :=
  -- Uncurrying the Deligne bifunctor commutes definitionally with postcomposition by the
  -- matrix embedding, so the monoidal structure is the one on this composite.
  inferInstanceAs
    ((Functor.uncurry.obj (LinearTensor.bifunctor k C D)) ⋙
      Mat_.embedding (LinearTensor k C D)).Monoidal

/-- The unit comparison identifies the two presentations of the one-term family on the
pair of tensor units. -/
@[simp]
theorem uncurry_bifunctor_ε :
    Functor.LaxMonoidal.ε (Functor.uncurry.obj (bifunctor k C D)) =
      (Mat_.embeddingUnitIso (C := LinearTensor k C D)).hom := by
  -- Uncurrying the Deligne bifunctor commutes definitionally with postcomposition by the
  -- matrix embedding. Spell out that composite to use the comparison formula.
  change Functor.LaxMonoidal.ε
    (Functor.uncurry.obj (LinearTensor.bifunctor k C D) ⋙ Mat_.embedding _) = _
  simp

/-- The tensor comparison sends the tensor product of one-term families to the one-term
family on their componentwise tensor product. -/
@[simp]
theorem uncurry_bifunctor_μ (P Q : C × D) :
    Functor.LaxMonoidal.μ (Functor.uncurry.obj (bifunctor k C D)) P Q =
      (Mat_.embeddingTensorIso (⟨P.1, P.2⟩ : LinearTensor k C D) ⟨Q.1, Q.2⟩).hom := by
  -- Spell out the composite to use the tensor comparison formula for composed functors.
  change Functor.LaxMonoidal.μ
    (Functor.uncurry.obj (LinearTensor.bifunctor k C D) ⋙ Mat_.embedding _) P Q = _
  simp

/-- The inverse unit comparison is the inverse of the matrix embedding's unit comparison. -/
@[simp]
theorem uncurry_bifunctor_η :
    Functor.OplaxMonoidal.η (Functor.uncurry.obj (bifunctor k C D)) =
      (Mat_.embeddingUnitIso (C := LinearTensor k C D)).inv := by
  -- Spell out the composite to use the inverse comparison formula for composed functors.
  change Functor.OplaxMonoidal.η
    (Functor.uncurry.obj (LinearTensor.bifunctor k C D) ⋙ Mat_.embedding _) = _
  simp

/-- The inverse tensor comparison is the inverse of the matrix embedding's tensor comparison. -/
@[simp]
theorem uncurry_bifunctor_δ (P Q : C × D) :
    Functor.OplaxMonoidal.δ (Functor.uncurry.obj (bifunctor k C D)) P Q =
      (Mat_.embeddingTensorIso (⟨P.1, P.2⟩ : LinearTensor k C D) ⟨Q.1, Q.2⟩).inv := by
  -- Spell out the composite to use the inverse comparison formula for composed functors.
  change Functor.OplaxMonoidal.δ
    (Functor.uncurry.obj (LinearTensor.bifunctor k C D) ⋙ Mat_.embedding _) P Q = _
  simp

end TauCeti.DeligneProduct
