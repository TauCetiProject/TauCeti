/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import TauCeti.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Tensor products of curved duplexes

Let `C` be an `R`-linear monoidal category with binary biproducts, in which the tensor product
is additive and `R`-linear in each variable. For curved duplexes `X` of curvature `v` and `Y` of
curvature `w`, the tensor product `X ⊗ Y` has components

`(X ⊗ Y)₀ = X₀ ⊗ Y₀ ⊞ X₁ ⊗ Y₁`,    `(X ⊗ Y)₁ = X₁ ⊗ Y₀ ⊞ X₀ ⊗ Y₁`,

and differential `d_X ⊗ 1 + ε ⊗ d_Y`, where `ε` is the parity sign `(-1)^|x|` of the Koszul
rule. The cross terms of its square cancel by the interchange law, and the diagonal terms are
`v • 𝟙` and `w • 𝟙`; thus `X ⊗ Y` is a curved duplex of curvature `v + w`. The curvatures add,
so this is not an operation on duplexes of one fixed curvature.

Even closed maps tensor componentwise, giving a bifunctor
`CurvedDuplex C v ⥤ CurvedDuplex C w ⥤ CurvedDuplex C (v + w)` that is `R`-linear in each
variable. Tensoring with any closed map preserves null-homotopic maps on either side: if
`f = d h + h d`, then `f ⊗ g = d (h ⊗ g) + (h ⊗ g) d`, and dually with the Koszul sign for an
odd map in the second variable. This is what lets the tensor product descend to homotopy
categories, and in particular to homotopy categories of matrix factorizations.

## Main definitions

* `TauCeti.CurvedDuplex.tensorObj`: the tensor product of curved duplexes, of summed curvature.
* `TauCeti.CurvedDuplex.tensorHom`: the tensor product of closed even maps.
* `TauCeti.CurvedDuplex.tensor`: the tensor-product bifunctor.

## Main results

* `TauCeti.CurvedDuplex.tensorHom_nullHomotopicMap_left` and
  `TauCeti.CurvedDuplex.tensorHom_nullHomotopicMap_right`: explicit homotopies for the tensor
  product of a null-homotopic map with a closed map.
* `TauCeti.CurvedDuplex.tensorHom_mem_nullHomotopic_left` and
  `TauCeti.CurvedDuplex.tensorHom_mem_nullHomotopic_right`: hence the tensor product with a
  null-homotopic map, on either side, is null-homotopic.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), 35–64, Section 5.
* H. Knörrer, *Cohen–Macaulay modules on hypersurface singularities I*, Invent. Math. **88**
  (1987), 153–164, Section 2 (the tensor product of matrix factorizations of `f` and `g` is a
  matrix factorization of `f + g`).
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]
  [MonoidalCategory C] [HasBinaryBiproducts C] {v w : R}

/-- The even-to-odd differential of the tensor product, from `X₀ ⊗ Y₀ ⊞ X₁ ⊗ Y₁` to
`X₁ ⊗ Y₀ ⊞ X₀ ⊗ Y₁`: on `X₀ ⊗ Y₀` it is `d₀ ⊗ 1 + 1 ⊗ d₀`, and on `X₁ ⊗ Y₁` it is
`d₁ ⊗ 1 - 1 ⊗ d₁`. -/
noncomputable def tensorD₀ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    X.X₀ ⊗ Y.X₀ ⊞ X.X₁ ⊗ Y.X₁ ⟶ X.X₁ ⊗ Y.X₀ ⊞ X.X₀ ⊗ Y.X₁ :=
  Biprod.ofComponents (X.d₀ ▷ Y.X₀) (X.X₀ ◁ Y.d₀) (-(X.X₁ ◁ Y.d₁)) (X.d₁ ▷ Y.X₁)

/-- The odd-to-even differential of the tensor product, from `X₁ ⊗ Y₀ ⊞ X₀ ⊗ Y₁` to
`X₀ ⊗ Y₀ ⊞ X₁ ⊗ Y₁`: on `X₁ ⊗ Y₀` it is `d₁ ⊗ 1 - 1 ⊗ d₀`, and on `X₀ ⊗ Y₁` it is
`d₀ ⊗ 1 + 1 ⊗ d₁`. -/
noncomputable def tensorD₁ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    X.X₁ ⊗ Y.X₀ ⊞ X.X₀ ⊗ Y.X₁ ⟶ X.X₀ ⊗ Y.X₀ ⊞ X.X₁ ⊗ Y.X₁ :=
  Biprod.ofComponents (X.d₁ ▷ Y.X₀) (-(X.X₁ ◁ Y.d₀)) (X.X₀ ◁ Y.d₁) (X.d₀ ▷ Y.X₁)

@[reassoc (attr := simp)]
theorem biprod_inl_comp_tensorD₀ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    biprod.inl ≫ tensorD₀ X Y = X.d₀ ▷ Y.X₀ ≫ biprod.inl + X.X₀ ◁ Y.d₀ ≫ biprod.inr := by
  simp [tensorD₀]

@[reassoc (attr := simp)]
theorem biprod_inr_comp_tensorD₀ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    biprod.inr ≫ tensorD₀ X Y = -(X.X₁ ◁ Y.d₁ ≫ biprod.inl) + X.d₁ ▷ Y.X₁ ≫ biprod.inr := by
  simp [tensorD₀]

@[reassoc (attr := simp)]
theorem biprod_inl_comp_tensorD₁ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    biprod.inl ≫ tensorD₁ X Y = X.d₁ ▷ Y.X₀ ≫ biprod.inl + -(X.X₁ ◁ Y.d₀ ≫ biprod.inr) := by
  simp [tensorD₁]

@[reassoc (attr := simp)]
theorem biprod_inr_comp_tensorD₁ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    biprod.inr ≫ tensorD₁ X Y = X.X₀ ◁ Y.d₁ ≫ biprod.inl + X.d₀ ▷ Y.X₁ ≫ biprod.inr := by
  simp [tensorD₁]

variable [MonoidalPreadditive C] [MonoidalLinear R C]

/-- The **tensor product** of a curved duplex `X` of curvature `v` and a curved duplex `Y` of
curvature `w`: the curved duplex of curvature `v + w` with components `X₀ ⊗ Y₀ ⊞ X₁ ⊗ Y₁` and
`X₁ ⊗ Y₀ ⊞ X₀ ⊗ Y₁` and the Koszul-signed differential `d_X ⊗ 1 + ε ⊗ d_Y`. -/
-- The object is exposed because its biproduct components occur in the types of the morphism
-- formulas and homotopies below.
@[expose, implicit_reducible] noncomputable def tensorObj (X : CurvedDuplex C v)
    (Y : CurvedDuplex C w) : CurvedDuplex C (v + w) where
  X₀ := X.X₀ ⊗ Y.X₀ ⊞ X.X₁ ⊗ Y.X₁
  X₁ := X.X₁ ⊗ Y.X₀ ⊞ X.X₀ ⊗ Y.X₁
  d₀ := tensorD₀ X Y
  d₁ := tensorD₁ X Y
  d₀_comp_d₁ := by
    ext <;> simp [add_smul, add_comm, whisker_exchange, ← whiskerLeft_comp,
      ← comp_whiskerRight]
  d₁_comp_d₀ := by
    ext <;> simp [add_smul, add_comm, whisker_exchange, ← whiskerLeft_comp,
      ← comp_whiskerRight]

@[simp] theorem tensorObj_X₀ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    (tensorObj X Y).X₀ = (X.X₀ ⊗ Y.X₀ ⊞ X.X₁ ⊗ Y.X₁) := rfl

@[simp] theorem tensorObj_X₁ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    (tensorObj X Y).X₁ = (X.X₁ ⊗ Y.X₀ ⊞ X.X₀ ⊗ Y.X₁) := rfl

@[simp] theorem tensorObj_d₀ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    (tensorObj X Y).d₀ = tensorD₀ X Y := rfl

@[simp] theorem tensorObj_d₁ (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    (tensorObj X Y).d₁ = tensorD₁ X Y := rfl

variable {X X' X'' : CurvedDuplex C v} {Y Y' Y'' : CurvedDuplex C w}

/-- The **tensor product of closed even maps** of curved duplexes, acting componentwise on the
four summands. -/
noncomputable def tensorHom (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' where
  f₀ := biprod.map (f.f₀ ⊗ₘ g.f₀) (f.f₁ ⊗ₘ g.f₁)
  f₁ := biprod.map (f.f₁ ⊗ₘ g.f₀) (f.f₀ ⊗ₘ g.f₁)
  comm₀ := by
    dsimp only [tensorObj]
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [← id_tensorHom, ← MonoidalCategory.tensorHom_id, f.comm₀, f.comm₁, g.comm₀,
        g.comm₁]
  comm₁ := by
    dsimp only [tensorObj]
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [← id_tensorHom, ← MonoidalCategory.tensorHom_id, f.comm₀, f.comm₁, g.comm₀,
        g.comm₁]

@[simp] theorem tensorHom_f₀ (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorHom f g).f₀ = biprod.map (f.f₀ ⊗ₘ g.f₀) (f.f₁ ⊗ₘ g.f₁) := by
  simp only [tensorHom]

@[simp] theorem tensorHom_f₁ (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorHom f g).f₁ = biprod.map (f.f₁ ⊗ₘ g.f₀) (f.f₀ ⊗ₘ g.f₁) := by
  simp only [tensorHom]

@[simp] theorem id_tensorHom_id (X : CurvedDuplex C v) (Y : CurvedDuplex C w) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem tensorHom_comp_tensorHom (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorHom f g ≫ tensorHom f' g' = tensorHom (f ≫ f') (g ≫ g') := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

@[simp] theorem add_tensorHom (f f' : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [MonoidalPreadditive.add_tensor]

@[simp] theorem tensorHom_add (f : X ⟶ X') (g g' : Y ⟶ Y') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [MonoidalPreadditive.tensor_add]

@[simp] theorem zero_tensorHom (g : Y ⟶ Y') : tensorHom (0 : X ⟶ X') g = 0 := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

@[simp] theorem tensorHom_zero (f : X ⟶ X') : tensorHom f (0 : Y ⟶ Y') = 0 := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

@[simp] theorem smul_tensorHom (r : R) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom (r • f) g = r • tensorHom f g := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

@[simp] theorem tensorHom_smul (r : R) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom f (r • g) = r • tensorHom f g := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- The tensor product of a null-homotopic map with a closed map is null-homotopic: if
`f = d h + h d` for the odd map `h = (h₀, h₁)`, then `f ⊗ g` is the boundary of `h ⊗ g`. -/
theorem tensorHom_nullHomotopicMap_left (h₀ : X.X₀ ⟶ X'.X₁) (h₁ : X.X₁ ⟶ X'.X₀) (g : Y ⟶ Y') :
    tensorHom (nullHomotopicMap h₀ h₁) g =
      nullHomotopicMap (biprod.map (h₀ ⊗ₘ g.f₀) (h₁ ⊗ₘ g.f₁))
        (biprod.map (h₁ ⊗ₘ g.f₀) (h₀ ⊗ₘ g.f₁)) := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [← id_tensorHom, ← MonoidalCategory.tensorHom_id, MonoidalPreadditive.add_tensor,
      g.comm₀, g.comm₁]

/-- The tensor product of a closed map with a null-homotopic map is null-homotopic: if
`g = d k + k d` for the odd map `k = (k₀, k₁)`, then `f ⊗ g` is the boundary of the odd map
`f ⊗ k`, which carries the Koszul sign `(-1)^|x|` on `x ⊗ y`. -/
theorem tensorHom_nullHomotopicMap_right (f : X ⟶ X') (k₀ : Y.X₀ ⟶ Y'.X₁)
    (k₁ : Y.X₁ ⟶ Y'.X₀) :
    tensorHom f (nullHomotopicMap k₀ k₁) =
      nullHomotopicMap (Biprod.ofComponents 0 (f.f₀ ⊗ₘ k₀) (-(f.f₁ ⊗ₘ k₁)) 0)
        (Biprod.ofComponents 0 (-(f.f₁ ⊗ₘ k₀)) (f.f₀ ⊗ₘ k₁) 0) := by
  ext <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [← id_tensorHom, ← MonoidalCategory.tensorHom_id, MonoidalPreadditive.tensor_add,
      reassoc_of% Biprod.inl_ofComponents, reassoc_of% Biprod.inr_ofComponents, f.comm₀, f.comm₁]

/-- The tensor product of a null-homotopic map with any closed map is null-homotopic. -/
theorem tensorHom_mem_nullHomotopic_left {f : X ⟶ X'} (hf : f ∈ (nullHomotopic C v).hom X X')
    (g : Y ⟶ Y') : tensorHom f g ∈ (nullHomotopic C (v + w)).hom _ _ := by
  obtain ⟨h₀, h₁, rfl⟩ := mem_nullHomotopic_iff.1 hf
  rw [tensorHom_nullHomotopicMap_left]
  exact nullHomotopicMap_mem_nullHomotopic _ _

/-- The tensor product of any closed map with a null-homotopic map is null-homotopic. -/
theorem tensorHom_mem_nullHomotopic_right (f : X ⟶ X') {g : Y ⟶ Y'}
    (hg : g ∈ (nullHomotopic C w).hom Y Y') :
    tensorHom f g ∈ (nullHomotopic C (v + w)).hom _ _ := by
  obtain ⟨k₀, k₁, rfl⟩ := mem_nullHomotopic_iff.1 hg
  rw [tensorHom_nullHomotopicMap_right]
  exact nullHomotopicMap_mem_nullHomotopic _ _

variable (C v w) in
/-- The **tensor-product bifunctor** from curved duplexes of curvatures `v` and `w` to curved
duplexes of curvature `v + w`. -/
-- Exposed so that its objects and maps unfold to `tensorObj` and `tensorHom`.
@[expose, simps]
noncomputable def tensor : CurvedDuplex C v ⥤ CurvedDuplex C w ⥤ CurvedDuplex C (v + w) where
  obj X :=
    { obj Y := tensorObj X Y
      map g := tensorHom (𝟙 X) g
      map_id Y := id_tensorHom_id X Y
      map_comp g g' := by simp }
  map f :=
    { app Y := tensorHom f (𝟙 Y)
      naturality _ _ g := by simp }
  map_id X := by ext Y : 2; exact id_tensorHom_id X Y
  map_comp f f' := by ext Y : 2; simp

instance (X : CurvedDuplex C v) : ((tensor C v w).obj X).Additive where
  map_add {_ _ f g} := tensorHom_add (𝟙 X) f g

instance : (tensor C v w).Additive where
  map_add {_ _ f g} := NatTrans.ext (funext fun Y ↦ add_tensorHom f g (𝟙 Y))

instance (Y : CurvedDuplex C w) : ((tensor C v w).flip.obj Y).Additive where
  map_add {_ _ f g} := add_tensorHom f g (𝟙 Y)

instance (X : CurvedDuplex C v) : ((tensor C v w).obj X).Linear R where
  map_smul {_ _} g r := tensorHom_smul r (𝟙 X) g

instance : (tensor C v w).Linear R where
  map_smul {_ _} f r := NatTrans.ext (funext fun Y ↦ smul_tensorHom r f (𝟙 Y))

instance (Y : CurvedDuplex C w) : ((tensor C v w).flip.obj Y).Linear R where
  map_smul {_ _} f r := smul_tensorHom r f (𝟙 Y)

/-- Tensoring on the left with a fixed curved duplex preserves null-homotopic maps. -/
theorem nullHomotopic_le_comap_tensor_obj (X : CurvedDuplex C v) :
    nullHomotopic C w ≤ (nullHomotopic C (v + w)).comap ((tensor C v w).obj X) :=
  fun _ _ g hg ↦ by
    rw [MorphismIdeal.mem_comap_hom, tensor_obj_map]
    exact tensorHom_mem_nullHomotopic_right _ hg

/-- Tensoring on the right with a fixed curved duplex preserves null-homotopic maps. -/
theorem nullHomotopic_le_comap_tensor_flip_obj (Y : CurvedDuplex C w) :
    nullHomotopic C v ≤ (nullHomotopic C (v + w)).comap ((tensor C v w).flip.obj Y) :=
  fun _ _ f hf ↦ by
    rw [MorphismIdeal.mem_comap_hom, Functor.flip_obj_map, tensor_map_app]
    exact tensorHom_mem_nullHomotopic_left hf _

end CurvedDuplex

end TauCeti
