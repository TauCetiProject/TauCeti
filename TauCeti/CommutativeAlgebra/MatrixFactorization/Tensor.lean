/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import TauCeti.Algebra.Homology.Curved.Tensor
public import TauCeti.Algebra.Category.FGModuleCat.Projective

/-!
# Tensor products of matrix factorizations

For matrix factorizations `X` of `v` and `Y` of `w` over a commutative ring `S`, the tensor
product of their underlying curved duplexes has components `X₀ ⊗ Y₀ ⊕ X₁ ⊗ Y₁` and
`X₁ ⊗ Y₀ ⊕ X₀ ⊗ Y₁`, which are again finitely generated and projective. It is therefore a
matrix factorization of the summed potential `v + w`. Closed maps tensor componentwise, which
gives a bifunctor `S`-linear in each variable, and tensoring with any map preserves
null-homotopic maps on either side.

## Main definitions

* `TauCeti.MatrixFactorization.tensorObj`: the tensor product of matrix factorizations, a
  matrix factorization of the summed potential.
* `TauCeti.MatrixFactorization.tensor`: the tensor-product bifunctor.

## Main results

* `TauCeti.MatrixFactorization.tensorHom_mem_nullHomotopic_left` and
  `TauCeti.MatrixFactorization.tensorHom_mem_nullHomotopic_right`: the tensor product of a
  null-homotopic map with any closed map, on either side, is null-homotopic.
* `TauCeti.MatrixFactorization.nullHomotopic_le_comap_tensor_obj` and
  `TauCeti.MatrixFactorization.nullHomotopic_le_comap_tensor_flip_obj`: tensoring with a fixed
  factorization, on either side, preserves null-homotopic maps.

## References

* H. Knörrer, *Cohen–Macaulay modules on hypersurface singularities I*, Invent. Math. **88**
  (1987), 153–164, Section 2.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Sections 1.2 and 3.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {S : Type u} [CommRing S] {v w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The **tensor product** of a matrix factorization of `v` and a matrix factorization of `w`: the
matrix factorization of `v + w` whose underlying curved duplex is the tensor product of curved
duplexes. -/
-- The constructor is exposed so that the underlying curved duplex unfolds to the tensor product
-- of curved duplexes, whose components occur in the types of the morphism formulas.
@[expose] noncomputable def tensorObj (X : MatrixFactorization S v)
    (Y : MatrixFactorization S w) : MatrixFactorization S (v + w) :=
  ofCurvedDuplex (CurvedDuplex.tensorObj X.obj Y.obj)
    (FGModuleCat.projective_biprod S _ _) (FGModuleCat.projective_biprod S _ _)

@[simp] theorem tensorObj_obj (X : MatrixFactorization S v) (Y : MatrixFactorization S w) :
    (tensorObj X Y).obj = CurvedDuplex.tensorObj X.obj Y.obj := rfl

variable {X X' X'' : MatrixFactorization S v} {Y Y' Y'' : MatrixFactorization S w}

/-- The tensor product of closed maps of matrix factorizations: the tensor product of the
underlying maps of curved duplexes. -/
noncomputable def tensorHom (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' :=
  ⟨CurvedDuplex.tensorHom f.hom g.hom⟩

@[simp] theorem tensorHom_hom (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorHom f g).hom = CurvedDuplex.tensorHom f.hom g.hom := by
  unfold tensorHom; rfl

@[simp] theorem id_tensorHom_id (X : MatrixFactorization S v) (Y : MatrixFactorization S w) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  ext : 1
  simp

@[reassoc (attr := simp)]
theorem tensorHom_comp_tensorHom (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorHom f g ≫ tensorHom f' g' = tensorHom (f ≫ f') (g ≫ g') := by
  ext : 1
  simp

-- In the six lemmas below, `simp` reduces both sides to the same curved-duplex expression but
-- cannot close the goal: the two sides remain indexed by `(tensorObj X Y).obj` and
-- `CurvedDuplex.tensorObj X.obj Y.obj`, which `tensorObj_obj` cannot rewrite inside the hom types.
-- Those agree definitionally, so the curved-duplex lemma is applied to the underlying maps.
@[simp] theorem add_tensorHom (f f' : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  ext : 1
  exact CurvedDuplex.add_tensorHom f.hom f'.hom g.hom

@[simp] theorem tensorHom_add (f : X ⟶ X') (g g' : Y ⟶ Y') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  ext : 1
  exact CurvedDuplex.tensorHom_add f.hom g.hom g'.hom

@[simp] theorem zero_tensorHom (g : Y ⟶ Y') : tensorHom (0 : X ⟶ X') g = 0 := by
  ext : 1
  exact CurvedDuplex.zero_tensorHom g.hom

@[simp] theorem tensorHom_zero (f : X ⟶ X') : tensorHom f (0 : Y ⟶ Y') = 0 := by
  ext : 1
  exact CurvedDuplex.tensorHom_zero f.hom

@[simp] theorem smul_tensorHom (r : S) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom (r • f) g = r • tensorHom f g := by
  ext : 1
  exact CurvedDuplex.smul_tensorHom r f.hom g.hom

@[simp] theorem tensorHom_smul (r : S) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom f (r • g) = r • tensorHom f g := by
  ext : 1
  exact CurvedDuplex.tensorHom_smul r f.hom g.hom

variable (S v w) in
/-- The **tensor-product bifunctor** from matrix factorizations of `v` and of `w` to matrix
factorizations of `v + w`. -/
-- Exposed so that its objects and maps unfold to `tensorObj` and `tensorHom`.
@[expose, simps]
noncomputable def tensor :
    MatrixFactorization S v ⥤ MatrixFactorization S w ⥤ MatrixFactorization S (v + w) where
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

instance (X : MatrixFactorization S v) : ((tensor S v w).obj X).Additive where
  map_add {_ _ f g} := tensorHom_add (𝟙 X) f g

instance : (tensor S v w).Additive where
  map_add {_ _ f g} := NatTrans.ext (funext fun Y ↦ add_tensorHom f g (𝟙 Y))

instance (Y : MatrixFactorization S w) : ((tensor S v w).flip.obj Y).Additive where
  map_add {_ _ f g} := add_tensorHom f g (𝟙 Y)

instance (X : MatrixFactorization S v) : ((tensor S v w).obj X).Linear S where
  map_smul {_ _} g r := tensorHom_smul r (𝟙 X) g

instance : (tensor S v w).Linear S where
  map_smul {_ _} f r := NatTrans.ext (funext fun Y ↦ smul_tensorHom r f (𝟙 Y))

instance (Y : MatrixFactorization S w) : ((tensor S v w).flip.obj Y).Linear S where
  map_smul {_ _} f r := smul_tensorHom r f (𝟙 Y)

/-- The tensor product of a null-homotopic map with any closed map is null-homotopic. -/
theorem tensorHom_mem_nullHomotopic_left {f : X ⟶ X'}
    (hf : f ∈ (nullHomotopic (S := S) (w := v)).hom X X') (g : Y ⟶ Y') :
    tensorHom f g ∈ (nullHomotopic (S := S) (w := v + w)).hom _ _ := by
  rw [mem_nullHomotopic_iff, ← CurvedDuplex.mem_nullHomotopic_iff] at hf ⊢
  -- The underlying map is `CurvedDuplex.tensorHom f.hom g.hom` (`tensorHom_hom`); rewriting by it
  -- would also change the objects indexing its hom type, so the identification is left to
  -- definitional unfolding.
  exact CurvedDuplex.tensorHom_mem_nullHomotopic_left hf g.hom

/-- The tensor product of any closed map with a null-homotopic map is null-homotopic. -/
theorem tensorHom_mem_nullHomotopic_right (f : X ⟶ X') {g : Y ⟶ Y'}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom Y Y') :
    tensorHom f g ∈ (nullHomotopic (S := S) (w := v + w)).hom _ _ := by
  rw [mem_nullHomotopic_iff, ← CurvedDuplex.mem_nullHomotopic_iff] at hg ⊢
  -- As above, the underlying map is identified with `CurvedDuplex.tensorHom f.hom g.hom` by
  -- definitional unfolding.
  exact CurvedDuplex.tensorHom_mem_nullHomotopic_right f.hom hg

/-- Tensoring on the left with a fixed matrix factorization preserves null-homotopic maps. -/
theorem nullHomotopic_le_comap_tensor_obj (X : MatrixFactorization S v) :
    nullHomotopic (S := S) (w := w) ≤
      (nullHomotopic (S := S) (w := v + w)).comap ((tensor S v w).obj X) :=
  fun _ _ g hg ↦ by
    rw [MorphismIdeal.mem_comap_hom, tensor_obj_map]
    exact tensorHom_mem_nullHomotopic_right _ hg

/-- Tensoring on the right with a fixed matrix factorization preserves null-homotopic maps. -/
theorem nullHomotopic_le_comap_tensor_flip_obj (Y : MatrixFactorization S w) :
    nullHomotopic (S := S) (w := v) ≤
      (nullHomotopic (S := S) (w := v + w)).comap ((tensor S v w).flip.obj Y) :=
  fun _ _ f hf ↦ by
    rw [MorphismIdeal.mem_comap_hom, Functor.flip_obj_map, tensor_map_app]
    exact tensorHom_mem_nullHomotopic_left hf _

end TauCeti.MatrixFactorization
