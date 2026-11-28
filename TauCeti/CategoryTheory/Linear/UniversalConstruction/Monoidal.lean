/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.UniversalConstruction.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Tensor products of states

When the distinguished object is the tensor unit, disjoint placement of fillings induces
natural maps from the tensor product of their state modules to the state module of their
tensor product. The radical is stable under placement in either factor: a test on a tensor
product gives a test on one factor after inserting a filling in the other.

Together with the empty filling these maps make the state functor lax monoidal, and lax
braided when the source is braided. Invertibility requires additional decomposition
results and is not asserted here. No multiplicativity assumption on the evaluation is
needed for these maps or their coherence.

The associativity comparison reuses Mathlib's lax monoidal structure on
`CategoryTheory.coyoneda.obj (Opposite.op (𝟙_ C))`. The quotient construction follows the
universal construction of Blanchet–Habegger–Masbaum–Vogel and its foam version in
Goertz–Marino–Wedrich, *Monoidal 2-categories from foam evaluation*, Lemmas 3.18–3.19.
-/

public section

namespace TauCeti.UniversalConstruction

open CategoryTheory MonoidalCategory TensorProduct

universe u v

variable {R : Type v} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [MonoidalCategory C]
  (ev : (𝟙_ C ⟶ 𝟙_ C) →ₗ[R] R)

/-- Placing a radical filling beside any other filling gives a radical filling. -/
theorem tensor_mem_radical_left {X Y : C} {a : 𝟙_ C ⟶ X}
    (ha : a ∈ radical (𝟙_ C) ev X) (b : 𝟙_ C ⟶ Y) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ∈ radical (𝟙_ C) ev (X ⊗ Y) := by
  rw [mem_radical_iff] at ha ⊢
  intro t
  simpa only [unitors_inv_equal, rightUnitor_inv_comp_tensorHom, Category.assoc] using
    ha ((ρ_ X).inv ≫ X ◁ b ≫ t)

/-- Placing any filling beside a radical filling gives a radical filling. -/
theorem tensor_mem_radical_right {X Y : C} (a : 𝟙_ C ⟶ X) {b : 𝟙_ C ⟶ Y}
    (hb : b ∈ radical (𝟙_ C) ev Y) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ∈ radical (𝟙_ C) ev (X ⊗ Y) := by
  rw [mem_radical_iff] at hb ⊢
  intro t
  simpa only [leftUnitor_inv_comp_tensorHom, Category.assoc] using
    hb ((λ_ Y).inv ≫ a ▷ Y ≫ t)

variable [MonoidalPreadditive C] [MonoidalLinear R C]

private def placement (X Y : C) :
    (𝟙_ C ⟶ X) →ₗ[R] (𝟙_ C ⟶ Y) →ₗ[R] State (𝟙_ C) ev (X ⊗ Y) where
  toFun a :=
    { toFun := fun b ↦ Submodule.Quotient.mk ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b))
      map_add' := by intro b c; simp [MonoidalPreadditive.tensor_add]
      map_smul' := by intro r b; simp [tensorHom_def] }
  map_add' := by intro a b; ext c; simp [MonoidalPreadditive.add_tensor]
  map_smul' := by intro r a; ext b; simp [tensorHom_def]

/-- The bilinear placement of two states. -/
def stateTensor (X Y : C) :
    State (𝟙_ C) ev X →ₗ[R] State (𝟙_ C) ev Y →ₗ[R] State (𝟙_ C) ev (X ⊗ Y) :=
  (placement ev X Y).liftQ₂ (radical (𝟙_ C) ev X) (radical (𝟙_ C) ev Y)
    (by
      intro a ha
      apply LinearMap.ext
      intro b
      exact (Submodule.Quotient.mk_eq_zero _).mpr (tensor_mem_radical_left ev ha b))
    (by
      intro b hb
      apply LinearMap.ext
      intro a
      exact (Submodule.Quotient.mk_eq_zero _).mpr (tensor_mem_radical_right ev a hb))

@[simp]
theorem stateTensor_mk {X Y : C} (a : 𝟙_ C ⟶ X) (b : 𝟙_ C ⟶ Y) :
    stateTensor ev X Y (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)) := (rfl)

/-- The tensor comparison on state modules, induced by disjoint placement. -/
def tensorComparison (X Y : C) :
    (State (𝟙_ C) ev X ⊗[R] State (𝟙_ C) ev Y) →ₗ[R] State (𝟙_ C) ev (X ⊗ Y) :=
  TensorProduct.lift (stateTensor ev X Y)

@[simp]
theorem tensorComparison_tmul (X Y : C) (x : State (𝟙_ C) ev X) (y : State (𝟙_ C) ev Y) :
    tensorComparison ev X Y (x ⊗ₜ[R] y) = stateTensor ev X Y x y := (rfl)

/-- Placing states commutes with the maps induced by both factors. -/
theorem stateTensor_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : State (𝟙_ C) ev X) (y : State (𝟙_ C) ev Y) :
    stateTensor ev X' Y' (stateMap (𝟙_ C) ev f x) (stateMap (𝟙_ C) ev g y) =
      stateMap (𝟙_ C) ev (f ⊗ₘ g) (stateTensor ev X Y x y) := by
  obtain ⟨a, rfl⟩ := (radical (𝟙_ C) ev X).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (radical (𝟙_ C) ev Y).mkQ_surjective y
  simp only [Submodule.mkQ_apply, stateMap_mk, stateTensor_mk, Category.assoc,
    tensorHom_comp_tensorHom]

/-- The empty filling, used as the unit comparison. -/
def unitComparison : R →ₗ[R] State (𝟙_ C) ev (𝟙_ C) :=
  LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk (𝟙 _))

omit [MonoidalPreadditive C] [MonoidalLinear R C] in
@[simp]
theorem unitComparison_apply (r : R) :
    unitComparison ev r = r • Submodule.Quotient.mk (𝟙 _) := (rfl)

/-- Associativity of state placement, with the source associator retained. -/
theorem stateTensor_assoc {X Y Z : C} (x : State (𝟙_ C) ev X)
    (y : State (𝟙_ C) ev Y) (z : State (𝟙_ C) ev Z) :
    stateMap (𝟙_ C) ev (α_ X Y Z).hom
        (stateTensor ev (X ⊗ Y) Z (stateTensor ev X Y x y) z) =
      stateTensor ev X (Y ⊗ Z) x (stateTensor ev Y Z y z) := by
  obtain ⟨a, rfl⟩ := (radical (𝟙_ C) ev X).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (radical (𝟙_ C) ev Y).mkQ_surjective y
  obtain ⟨c, rfl⟩ := (radical (𝟙_ C) ev Z).mkQ_surjective z
  simp only [Submodule.mkQ_apply, stateTensor_mk, stateMap_mk]
  -- Coyoneda supplies the coherence equation for the underlying fillings.
  have h := congrArg (fun k ↦ k ((a, b), c))
    (Functor.LaxMonoidal.associativity (coyoneda.obj (Opposite.op (𝟙_ C))) X Y Z)
  exact congrArg (Submodule.Quotient.mk) h

/-- The empty filling is the left unit for state placement. -/
theorem stateTensor_unit_left {X : C} (x : State (𝟙_ C) ev X) :
    stateMap (𝟙_ C) ev (λ_ X).hom
        (stateTensor ev (𝟙_ C) X (Submodule.Quotient.mk (𝟙 _)) x) = x := by
  obtain ⟨a, rfl⟩ := (radical (𝟙_ C) ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateTensor_mk, stateMap_mk]
  simp

/-- The empty filling is the right unit for state placement. -/
theorem stateTensor_unit_right {X : C} (x : State (𝟙_ C) ev X) :
    stateMap (𝟙_ C) ev (ρ_ X).hom
        (stateTensor ev X (𝟙_ C) x (Submodule.Quotient.mk (𝟙 _))) = x := by
  obtain ⟨a, rfl⟩ := (radical (𝟙_ C) ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateTensor_mk, stateMap_mk]
  simp [unitors_inv_equal]

/-- Disjoint placement and the empty filling make states a lax monoidal functor. -/
instance stateFunctorLaxMonoidal : (stateFunctor (𝟙_ C) ev).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ModuleCat.ofHom (unitComparison ev))
    (μ := fun X Y ↦ ModuleCat.ofHom (tensorComparison ev X Y))
    (μ_natural := by
      intro X X' Y Y' f g
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      exact stateTensor_naturality ev f g x y)
    (associativity := by
      intro X Y Z
      apply ModuleCat.MonoidalCategory.tensor_ext₃'
      intro x y z
      exact stateTensor_assoc ev x y z)
    (left_unitality := by
      intro X
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro r x
      -- Normalize the concrete ModuleCat coercions to expose the linear maps on states.
      change r • x = stateMap (𝟙_ C) ev (λ_ X).hom
        (stateTensor ev (𝟙_ C) X (unitComparison ev r) x)
      rw [unitComparison_apply]
      simp only [map_smul, LinearMap.smul_apply]
      exact congrArg (r • ·) (stateTensor_unit_left ev x).symm)
    (right_unitality := by
      intro X
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x r
      -- Normalize the concrete ModuleCat coercions to expose the linear maps on states.
      change r • x = stateMap (𝟙_ C) ev (ρ_ X).hom
        (stateTensor ev X (𝟙_ C) x (unitComparison ev r))
      rw [unitComparison_apply]
      simp only [map_smul]
      exact congrArg (r • ·) (stateTensor_unit_right ev x).symm)

@[simp]
theorem stateFunctor_μ (X Y : C) :
    (Functor.LaxMonoidal.μ (stateFunctor (𝟙_ C) ev) X Y).hom = tensorComparison ev X Y :=
  (rfl)

@[simp]
theorem stateFunctor_ε :
    (Functor.LaxMonoidal.ε (stateFunctor (𝟙_ C) ev)).hom = unitComparison ev := (rfl)

/-- Braiding exchanges the two state factors without a sign. -/
theorem stateTensor_braiding [BraidedCategory C] {X Y : C}
    (x : State (𝟙_ C) ev X) (y : State (𝟙_ C) ev Y) :
    stateMap (𝟙_ C) ev (β_ X Y).hom (stateTensor ev X Y x y) = stateTensor ev Y X y x := by
  obtain ⟨a, rfl⟩ := (radical (𝟙_ C) ev X).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (radical (𝟙_ C) ev Y).mkQ_surjective y
  simp only [Submodule.mkQ_apply, stateTensor_mk, stateMap_mk]
  congr 1
  rw [Category.assoc, BraidedCategory.braiding_naturality, ← Category.assoc,
    leftUnitor_inv_braiding, ← unitors_inv_equal]

/-- In a braided source category the state functor is lax braided. -/
instance stateFunctorLaxBraided [BraidedCategory C] :
    (stateFunctor (𝟙_ C) ev).LaxBraided where
  braided X Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact stateTensor_braiding ev x y

end TauCeti.UniversalConstruction

