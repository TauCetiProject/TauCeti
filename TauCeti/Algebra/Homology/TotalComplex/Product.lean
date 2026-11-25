/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import TauCeti.Algebra.Homology.ComplexShape.Signs

/-!
# Product total complexes

Mathlib's total complex `K.total c₁₂` of a bicomplex `K : HomologicalComplex₂ C c₁ c₂` has in
degree `n` the coproduct of the terms `(K.X p).X q` with `ComplexShape.π c₁ c₂ c₁₂ (p, q) = n`.
This file constructs the product total complex `K.totalProduct c₁₂`, whose term in degree `n` is
the product of these terms. For a double complex of cochain complexes indexed by `ℤ`, the
component of its differential with target `(K.X p).X q` is `d₁ ∘ π_{p - 1, q}` plus
`(-1) ^ p • d₂ ∘ π_{p, q - 1}` (`HomologicalComplex₂.totalProduct_d_πTotalProduct_up_int`), with
the signs of `K.total`.

The two totalisations differ when an antidiagonal has infinitely many nonzero terms, and they
have different convergence properties: the column filtration is exhaustive on the direct sum
total complex and complete on the product total complex. For instance, for the double complex
with `(K.X p).X (-p) = (K.X (p + 1)).X (-p) = ℤ` for `p ≥ 0`, all other terms zero and the
nonzero differentials the identity, the total complex has `H⁰ = 0` while the product total complex
has `H⁰ = ℤ`.

## Construction

A bicomplex `K` in `C` gives a bicomplex `(HomologicalComplex₂.opFunctor C c₁ c₂).obj (op K)` in
`Cᵒᵖ` with the same terms, the opposite differentials and the opposite shapes `c₁.symm`,
`c₂.symm`. Products in `C` are coproducts in `Cᵒᵖ`, and `K.totalProduct c₁₂` is the opposite of
the total complex of this bicomplex for the shape `c₁₂.symm`. Its signs are those of an instance
`TotalComplexShape c₁.symm c₂.symm c₁₂.symm`; for a shape `c` with tensor signs, such as
`ComplexShape.up ℤ`, the shape `c.symm` inherits the tensor signs of `c`
(`TauCeti.Algebra.Homology.ComplexShape.Signs`).

## Main definitions and results

* `HomologicalComplex₂.totalProduct`: the product total complex, with the projections
  `HomologicalComplex₂.πTotalProduct`, the constructor `HomologicalComplex₂.totalProductLift`
  and the extensionality lemma `HomologicalComplex₂.totalProduct.hom_ext`.
* `HomologicalComplex₂.totalProduct_d_πTotalProduct`: the components of its differential.
* `HomologicalComplex₂.totalProductFunctor`: the product total complex as an additive functor.
* `HomologicalComplex₂.totalProductFlipIso`: the isomorphism between the product total complexes
  of a bicomplex and of its flip, given by the signs of a `TotalComplexShapeSymmetry`.
* `HomologicalComplex₂.hasTotal_of_hasCountableCoproducts`,
  `HomologicalComplex₂.hasTotalProduct_of_hasCountableProducts`: existence of both totalisations
  of a bicomplex indexed by countable types in a category with countable coproducts or products.
* `HomologicalComplex₂.totalToTotalProduct`: for a shape `c` with tensor signs, the natural chain
  map from the total complex to the product total complex which is the identity on each term.
  It commutes with the flip isomorphisms
  (`HomologicalComplex₂.totalFlipIso_hom_totalToTotalProduct`), and it is an isomorphism when
  every antidiagonal has only finitely many nonzero terms
  (`HomologicalComplex₂.isIso_totalToTotalProduct`).

## References

* The Stacks Project, Tag 09J0 (the complex `Tot_π` in its proof).
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 1.2.
-/

public section

open CategoryTheory Limits Opposite

namespace HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- The functor sending a bicomplex in `C` to the bicomplex in `Cᵒᵖ` with the same terms and the
opposite differentials. -/
@[expose, implicit_reducible]
noncomputable def opFunctor :
    (HomologicalComplex₂ C c₁ c₂)ᵒᵖ ⥤ HomologicalComplex₂ Cᵒᵖ c₁.symm c₂.symm :=
  HomologicalComplex.opFunctor (HomologicalComplex C c₂) c₁ ⋙
    (HomologicalComplex.opFunctor C c₂).mapHomologicalComplex c₁.symm

variable {C c₁ c₂}

@[simp]
lemma opFunctor_obj_X_X (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) :
    (((opFunctor C c₁ c₂).obj (op K)).X i₁).X i₂ = op ((K.X i₁).X i₂) := (rfl)

@[simp]
lemma opFunctor_obj_d_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ : I₂) :
    (((opFunctor C c₁ c₂).obj (op K)).d i₁ i₁').f i₂ = ((K.d i₁' i₁).f i₂).op := (rfl)

@[simp]
lemma opFunctor_obj_X_d (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ i₂' : I₂) :
    (((opFunctor C c₁ c₂).obj (op K)).X i₁).d i₂ i₂' = ((K.X i₁).d i₂' i₂).op := (rfl)

@[simp]
lemma opFunctor_map_f_f {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    (((opFunctor C c₁ c₂).map φ.op).f i₁).f i₂ = ((φ.f i₁).f i₂).op := (rfl)

variable (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁.symm c₂.symm c₁₂.symm]

/-- A bicomplex has a product total complex for `c₁₂` if for every `i₁₂ : I₁₂` the product of
the terms `(K.X i₁).X i₂` with `ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂` exists,
that is, if the bicomplex with the opposite differentials in `Cᵒᵖ` has a total complex. -/
abbrev HasTotalProduct := ((opFunctor C c₁ c₂).obj (op K)).HasTotal c₁₂.symm

variable [DecidableEq I₁₂]

section

variable [K.HasTotalProduct c₁₂]

/-- The product total complex of a bicomplex: its term in degree `i₁₂` is the product of the
terms `(K.X i₁).X i₂` over the indices with `π (i₁, i₂) = i₁₂`. It is the opposite of the total
complex of the bicomplex in `Cᵒᵖ` with the opposite differentials. -/
@[implicit_reducible]
noncomputable def totalProduct : HomologicalComplex C c₁₂ :=
  (((opFunctor C c₁ c₂).obj (op K)).total c₁₂.symm).unop

/-- The projection from the product total complex onto one of its factors. -/
noncomputable def πTotalProduct (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂) :
    (K.totalProduct c₁₂).X i₁₂ ⟶ (K.X i₁).X i₂ :=
  (((opFunctor C c₁ c₂).obj (op K)).ιTotal c₁₂.symm i₁ i₂ i₁₂ h).unop

/-- The projection from the product total complex onto one of its factors, or zero if the
degrees do not match. -/
noncomputable def πTotalProductOrZero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    (K.totalProduct c₁₂).X i₁₂ ⟶ (K.X i₁).X i₂ :=
  (((opFunctor C c₁ c₂).obj (op K)).ιTotalOrZero c₁₂.symm i₁ i₂ i₁₂).unop

lemma πTotalProductOrZero_eq (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂) :
    K.πTotalProductOrZero c₁₂ i₁ i₂ i₁₂ = K.πTotalProduct c₁₂ i₁ i₂ i₁₂ h := by
  rw [πTotalProductOrZero, ιTotalOrZero_eq _ _ _ _ _ h, πTotalProduct]

lemma πTotalProductOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) ≠ i₁₂) :
    K.πTotalProductOrZero c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [πTotalProductOrZero, ιTotalOrZero_eq_zero _ _ _ _ _ h, unop_zero]

section

variable {K c₁₂} {A : C} {i₁₂ : I₁₂}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂),
    A ⟶ (K.X i₁).X i₂)

/-- A constructor for morphisms to `(K.totalProduct c₁₂).X i₁₂`. -/
noncomputable def totalProductLift : A ⟶ (K.totalProduct c₁₂).X i₁₂ :=
  (((opFunctor C c₁ c₂).obj (op K)).totalDesc (fun i₁ i₂ h ↦ (f i₁ i₂ h).op)).unop

@[reassoc (attr := simp)]
lemma totalProductLift_πTotalProduct (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂) :
    totalProductLift f ≫ K.πTotalProduct c₁₂ i₁ i₂ i₁₂ h = f i₁ i₂ h :=
  by rw [totalProductLift, πTotalProduct, ← unop_comp, ι_totalDesc, Quiver.Hom.unop_op]

end

namespace totalProduct

variable {K L M c₁₂}

/-- A morphism to a term of the product total complex is determined by its composites with the
projections. -/
@[ext]
lemma hom_ext {A : C} {i₁₂ : I₁₂} {f g : A ⟶ (K.totalProduct c₁₂).X i₁₂}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂),
      f ≫ K.πTotalProduct c₁₂ i₁ i₂ i₁₂ hi = g ≫ K.πTotalProduct c₁₂ i₁ i₂ i₁₂ hi) :
    f = g :=
  Quiver.Hom.op_inj (total.hom_ext _ fun i₁ i₂ hi ↦ Quiver.Hom.unop_inj (h i₁ i₂ hi))

end totalProduct

/-- The differential of the product total complex, followed by a projection: the component with
target `(K.X i₁).X i₂` is the sum of the horizontal differential from `(K.X (c₁.prev i₁)).X i₂`
and the vertical differential from `(K.X i₁).X (c₂.prev i₂)`, with the signs of the total complex
shape `c₁.symm`, `c₂.symm`, `c₁₂.symm`. -/
@[reassoc]
lemma totalProduct_d_πTotalProduct (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂') :
    (K.totalProduct c₁₂).d i₁₂ i₁₂' ≫ K.πTotalProduct c₁₂ i₁ i₂ i₁₂' h =
      ComplexShape.ε₁ c₁.symm c₂.symm c₁₂.symm (i₁, i₂) •
          (K.πTotalProductOrZero c₁₂ (c₁.prev i₁) i₂ i₁₂ ≫ (K.d (c₁.prev i₁) i₁).f i₂) +
        ComplexShape.ε₂ c₁.symm c₂.symm c₁₂.symm (i₁, i₂) •
          (K.πTotalProductOrZero c₁₂ i₁ (c₂.prev i₂) i₁₂ ≫ (K.X i₁).d (c₂.prev i₂) i₂) := by
  apply Quiver.Hom.op_inj
  dsimp only [totalProduct, πTotalProduct, πTotalProductOrZero]
  simp only [op_add, op_comp, HomologicalComplex.unop_d, Quiver.Hom.op_unop, total_d,
    Preadditive.comp_add, ι_D₁, ι_D₂, d₁, d₂, opFunctor_obj_d_f, opFunctor_obj_X_d]
  -- `c.symm.next` is `c.prev`, and `ιMapObjOrZero` of the underlying graded object is
  -- `ιTotalOrZero`, both by definition
  rfl


namespace totalProduct

variable {K L M} [L.HasTotalProduct c₁₂] [M.HasTotalProduct c₁₂]

/-- The morphism of product total complexes induced by a morphism of bicomplexes. -/
noncomputable def map : K.totalProduct c₁₂ ⟶ L.totalProduct c₁₂ :=
  (HomologicalComplex.unopFunctor C c₁₂.symm).map
    (total.map ((opFunctor C c₁ c₂).map φ.op) c₁₂.symm).op

@[reassoc (attr := simp)]
lemma map_f_πTotalProduct (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂) :
    (map φ c₁₂).f i₁₂ ≫ L.πTotalProduct c₁₂ i₁ i₂ i₁₂ h =
      K.πTotalProduct c₁₂ i₁ i₂ i₁₂ h ≫ (φ.f i₁).f i₂ := by
  apply Quiver.Hom.op_inj
  dsimp only [map, πTotalProduct]
  simp only [op_comp, HomologicalComplex.unopFunctor_map_f, Quiver.Hom.op_unop, Quiver.Hom.unop_op,
    ιTotal_map, opFunctor_map_f_f]

variable (K) in
@[simp]
lemma map_id : map (𝟙 K) c₁₂ = 𝟙 _ := by
  ext
  simp

@[simp, reassoc]
lemma map_comp : map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂ := by
  ext
  simp

@[simp]
lemma map_add (φ φ' : K ⟶ L) : map (φ + φ') c₁₂ = map φ c₁₂ + map φ' c₁₂ := by
  ext
  simp

@[simp]
lemma map_zero : map (0 : K ⟶ L) c₁₂ = 0 := by
  ext
  simp

/-- The isomorphism of product total complexes induced by an isomorphism of bicomplexes. -/
noncomputable def mapIso (e : K ≅ L) : K.totalProduct c₁₂ ≅ L.totalProduct c₁₂ where
  hom := map e.hom c₁₂
  inv := map e.inv c₁₂
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

@[simp]
lemma mapIso_hom (e : K ≅ L) : (mapIso c₁₂ e).hom = map e.hom c₁₂ := (rfl)

@[simp]
lemma mapIso_inv (e : K ≅ L) : (mapIso c₁₂ e).inv = map e.inv c₁₂ := (rfl)

end totalProduct

end

variable (C c₁ c₂) in
/-- The functor which sends a bicomplex to its product total complex. -/
@[expose, simps]
noncomputable def totalProductFunctor [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotalProduct c₁₂] :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂ where
  obj K := K.totalProduct c₁₂
  map φ := totalProduct.map φ c₁₂

instance [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotalProduct c₁₂] :
    (totalProductFunctor C c₁ c₂ c₁₂).Additive where

section Flip

variable [TotalComplexShape c₂.symm c₁.symm c₁₂.symm]
  [TotalComplexShapeSymmetry c₁.symm c₂.symm c₁₂.symm] [K.HasTotalProduct c₁₂]

instance : K.flip.HasTotalProduct c₁₂ :=
  inferInstanceAs (((opFunctor C c₁ c₂).obj (op K)).flip.HasTotal c₁₂.symm)

/-- The isomorphism between the product total complexes of a bicomplex and of its flip. On the
factor `(K.X i₁).X i₂` it is the sign `ComplexShape.σ c₁.symm c₂.symm c₁₂.symm i₁ i₂`. -/
noncomputable def totalProductFlipIso : K.flip.totalProduct c₁₂ ≅ K.totalProduct c₁₂ :=
  ((HomologicalComplex.unopFunctor C c₁₂.symm).mapIso
    (((opFunctor C c₁ c₂).obj (op K)).totalFlipIso c₁₂.symm).op).symm

@[reassoc (attr := simp)]
lemma totalProductFlipIso_hom_f_πTotalProduct (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁.symm c₂.symm c₁₂.symm (i₁, i₂) = i₁₂) :
    (K.totalProductFlipIso c₁₂).hom.f i₁₂ ≫ K.πTotalProduct c₁₂ i₁ i₂ i₁₂ h =
      ComplexShape.σ c₁.symm c₂.symm c₁₂.symm i₁ i₂ • K.flip.πTotalProduct c₁₂ i₂ i₁ i₁₂
        (by rw [ComplexShape.π_symm c₁.symm c₂.symm c₁₂.symm i₁ i₂, h]) := by
  -- the product total complexes are the opposites of total complexes in `Cᵒᵖ`
  exact congrArg Quiver.Hom.unop
    (((opFunctor C c₁ c₂).obj (op K)).ιTotal_totalFlipIso_f_inv c₁₂.symm i₁ i₂ i₁₂ h)

@[reassoc (attr := simp)]
lemma totalProductFlipIso_inv_f_πTotalProduct (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₂.symm c₁.symm c₁₂.symm (i₂, i₁) = i₁₂) :
    (K.totalProductFlipIso c₁₂).inv.f i₁₂ ≫ K.flip.πTotalProduct c₁₂ i₂ i₁ i₁₂ h =
      ComplexShape.σ c₁.symm c₂.symm c₁₂.symm i₁ i₂ • K.πTotalProduct c₁₂ i₁ i₂ i₁₂
        (by rw [← ComplexShape.π_symm c₁.symm c₂.symm c₁₂.symm i₁ i₂, h]) := by
  -- the product total complexes are the opposites of total complexes in `Cᵒᵖ`
  exact congrArg Quiver.Hom.unop
    (((opFunctor C c₁ c₂).obj (op K)).ιTotal_totalFlipIso_f_hom c₁₂.symm i₁ i₂ i₁₂ h)

end Flip

section CochainComplex

variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotalProduct (ComplexShape.up ℤ)]

/-- For a double complex of cochain complexes indexed by `ℤ`, the component with target
`(K.X p).X q` of the differential of the product total complex is `d₁ ∘ π_{p - 1, q}` plus
`(-1) ^ p • d₂ ∘ π_{p, q - 1}`. -/
@[reassoc]
lemma totalProduct_d_πTotalProduct_up_int (n p q : ℤ) (h : p + q = n + 1) :
    (K.totalProduct (ComplexShape.up ℤ)).d n (n + 1) ≫
        K.πTotalProduct (ComplexShape.up ℤ) p q (n + 1) (by simpa using h) =
      K.πTotalProduct (ComplexShape.up ℤ) (p - 1) q n (by simp; omega) ≫ (K.d (p - 1) p).f q +
        p.negOnePow • (K.πTotalProduct (ComplexShape.up ℤ) p (q - 1) n (by simp; omega) ≫
          (K.X p).d (q - 1) q) := by
  rw [totalProduct_d_πTotalProduct, CochainComplex.prev, CochainComplex.prev,
    πTotalProductOrZero_eq _ _ _ _ _ (by simp; omega),
    πTotalProductOrZero_eq _ _ _ _ _ (by simp; omega)]
  simp

end CochainComplex

section Countable

variable [Countable I₁] [Countable I₂] (K : HomologicalComplex₂ C c₁ c₂)

/-- A bicomplex indexed by countable types has a total complex in a category with countable
coproducts. -/
instance hasTotal_of_hasCountableCoproducts [HasCountableCoproducts C]
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] : K.HasTotal c₁₂ :=
  fun _ ↦ inferInstance

/-- A bicomplex indexed by countable types has a product total complex in a category with
countable products. -/
instance hasTotalProduct_of_hasCountableProducts [HasCountableProducts C]
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁.symm c₂.symm c₁₂.symm] :
    K.HasTotalProduct c₁₂ :=
  fun _ ↦ inferInstance

end Countable

section TensorSigns

variable {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (K L : HomologicalComplex₂ C c c) (φ : K ⟶ L)
  [K.HasTotal c] [K.HasTotalProduct c] [L.HasTotal c] [L.HasTotalProduct c]

/-- The degreewise components of `totalToTotalProduct`. -/
private noncomputable def totalToTotalProductX (n : I) :
    (K.total c).X n ⟶ (K.totalProduct c).X n :=
  K.totalDesc fun p q _ ↦ totalProductLift fun p' q' _ ↦
    if h : p = p' ∧ q = q' then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0

private lemma ιTotal_totalToTotalProductX_πTotalProduct (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n) :
    K.ιTotal c p q n h ≫ K.totalToTotalProductX n ≫ K.πTotalProduct c p' q' n h' =
      if h : p = p' ∧ q = q' then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0 := by
  simp [totalToTotalProductX]

private lemma ιTotal_totalToTotalProductX_πTotalProductOrZero_of_ne (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (hne : (p, q) ≠ (p', q')) :
    K.ιTotal c p q n h ≫ K.totalToTotalProductX n ≫ K.πTotalProductOrZero c p' q' n = 0 := by
  by_cases h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n
  · rw [πTotalProductOrZero_eq _ _ _ _ _ h', ιTotal_totalToTotalProductX_πTotalProduct,
      dite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · rw [πTotalProductOrZero_eq_zero _ _ _ _ _ h', comp_zero, comp_zero]

private lemma ιTotalOrZero_totalToTotalProductX_πTotalProduct_of_ne (n p q p' q' : I)
    (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n) (hne : (p, q) ≠ (p', q')) :
    K.ιTotalOrZero c p q n ≫ K.totalToTotalProductX n ≫ K.πTotalProduct c p' q' n h' = 0 := by
  by_cases h : ComplexShape.π c c c (p, q) = n
  · rw [ιTotalOrZero_eq _ _ _ _ _ h, ιTotal_totalToTotalProductX_πTotalProduct, dite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · rw [ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp]

private lemma ιTotal_totalToTotalProductX_πTotalProduct_self (n p q : I)
    (h : ComplexShape.π c c c (p, q) = n) (h' : ComplexShape.π c.symm c.symm c.symm (p, q) = n) :
    K.ιTotal c p q n h ≫ K.totalToTotalProductX n ≫ K.πTotalProduct c p q n h' = 𝟙 _ := by
  simp [ιTotal_totalToTotalProductX_πTotalProduct]

/-- The horizontal part of the differential of `K.totalProduct c`, composed with the comparison
map, vanishes on the summand `(K.X p).X q` unless `(p', q')` is the horizontal successor. -/
private lemma ιTotal_totalToTotalProductX_dHorizontal (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (hpq : ¬ (c.Rel p p' ∧ q = q')) :
    K.ιTotal c p q n h ≫ K.totalToTotalProductX n ≫
      K.πTotalProductOrZero c (c.prev p') q' n ≫ (K.d (c.prev p') p').f q' = 0 := by
  by_cases hr : c.Rel (c.prev p') p'
  · rw [reassoc_of% (K.ιTotal_totalToTotalProductX_πTotalProductOrZero_of_ne n p q _ q' h ?_),
      zero_comp]
    rintro ⟨⟩
    exact hpq ⟨hr, rfl⟩
  · rw [K.shape_f _ _ hr, comp_zero, comp_zero, comp_zero]

private lemma ιTotal_totalToTotalProductX_dVertical (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (hpq : ¬ (p = p' ∧ c.Rel q q')) :
    K.ιTotal c p q n h ≫ K.totalToTotalProductX n ≫
      K.πTotalProductOrZero c p' (c.prev q') n ≫ (K.X p').d (c.prev q') q' = 0 := by
  by_cases hr : c.Rel (c.prev q') q'
  · rw [reassoc_of% (K.ιTotal_totalToTotalProductX_πTotalProductOrZero_of_ne n p q p' _ h ?_),
      zero_comp]
    rintro ⟨⟩
    exact hpq ⟨rfl, hr⟩
  · rw [HomologicalComplex.shape _ _ _ hr, comp_zero, comp_zero, comp_zero]

private lemma d₁_totalToTotalProductX_πTotalProduct (n p q p' q' : I)
    (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n) (hpq : ¬ (c.Rel p p' ∧ q = q')) :
    K.d₁ c p q n ≫ K.totalToTotalProductX n ≫ K.πTotalProduct c p' q' n h' = 0 := by
  by_cases hr : c.Rel p (c.next p)
  · rw [d₁_eq' _ _ hr, Linear.units_smul_comp, Category.assoc,
      K.ιTotalOrZero_totalToTotalProductX_πTotalProduct_of_ne n _ q p' q' h', comp_zero, smul_zero]
    rintro ⟨⟩
    exact hpq ⟨hr, rfl⟩
  · rw [d₁_eq_zero _ _ _ _ _ hr, zero_comp]

private lemma d₂_totalToTotalProductX_πTotalProduct (n p q p' q' : I)
    (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n) (hpq : ¬ (p = p' ∧ c.Rel q q')) :
    K.d₂ c p q n ≫ K.totalToTotalProductX n ≫ K.πTotalProduct c p' q' n h' = 0 := by
  by_cases hr : c.Rel q (c.next q)
  · rw [d₂_eq' _ _ _ hr, Linear.units_smul_comp, Category.assoc,
      K.ιTotalOrZero_totalToTotalProductX_πTotalProduct_of_ne n p _ p' q' h', comp_zero, smul_zero]
    rintro ⟨⟩
    exact hpq ⟨rfl, hr⟩
  · rw [d₂_eq_zero _ _ _ _ _ hr, zero_comp]

/-- The canonical map from the direct sum total complex to the product total complex of a
bicomplex: on the summand `(K.X p).X q` followed by the projection to the factor `(K.X p').X q'`
it is the identity if `(p, q) = (p', q')` and zero otherwise. -/
noncomputable def totalToTotalProduct : K.total c ⟶ K.totalProduct c where
  f n := K.totalToTotalProductX n
  comm' n n' _ := by
    ext p q h p' q' h'
    simp only [Category.assoc, totalProduct_d_πTotalProduct, total_d, Preadditive.add_comp,
      ι_D₁_assoc, ι_D₂_assoc, Preadditive.comp_add, Linear.comp_units_smul]
    by_cases h₁ : c.Rel p p' ∧ q = q'
    · obtain ⟨hp, rfl⟩ := h₁
      have h₂ : ¬ (p = p' ∧ c.Rel q q) := fun h ↦ c.not_rel_self _ (h.1 ▸ hp)
      rw [K.ιTotal_totalToTotalProductX_dVertical _ _ _ _ _ _ h₂,
        K.d₂_totalToTotalProductX_πTotalProduct _ _ _ _ _ _ h₂, c.prev_eq' hp,
        K.d₁_eq _ hp _ _ (by simpa using h'), πTotalProductOrZero_eq _ _ _ _ _ (by simpa using h),
        reassoc_of% (K.ιTotal_totalToTotalProductX_πTotalProduct_self n p q h)]
      simp [K.ιTotal_totalToTotalProductX_πTotalProduct_self n' p' q (by simpa using h') h']
    by_cases h₂ : p = p' ∧ c.Rel q q'
    · obtain ⟨rfl, hq⟩ := h₂
      rw [K.ιTotal_totalToTotalProductX_dHorizontal _ _ _ _ _ _ h₁,
        K.d₁_totalToTotalProductX_πTotalProduct _ _ _ _ _ _ h₁, c.prev_eq' hq,
        K.d₂_eq _ _ hq _ (by simpa using h'), πTotalProductOrZero_eq _ _ _ _ _ (by simpa using h),
        reassoc_of% (K.ιTotal_totalToTotalProductX_πTotalProduct_self n p q h)]
      simp [K.ιTotal_totalToTotalProductX_πTotalProduct_self n' p q' (by simpa using h') h']
    rw [K.ιTotal_totalToTotalProductX_dHorizontal _ _ _ _ _ _ h₁,
      K.ιTotal_totalToTotalProductX_dVertical _ _ _ _ _ _ h₂,
      K.d₁_totalToTotalProductX_πTotalProduct _ _ _ _ _ _ h₁,
      K.d₂_totalToTotalProductX_πTotalProduct _ _ _ _ _ _ h₂]
    simp

private lemma totalToTotalProduct_f (n : I) :
    (K.totalToTotalProduct).f n = K.totalToTotalProductX n := rfl

@[reassoc]
lemma ιTotal_totalToTotalProduct_f_πTotalProduct (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n) :
    K.ιTotal c p q n h ≫ (K.totalToTotalProduct).f n ≫ K.πTotalProduct c p' q' n h' =
      if h : p = p' ∧ q = q' then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0 :=
  K.ιTotal_totalToTotalProductX_πTotalProduct n p q p' q' h h'

@[reassoc (attr := simp)]
lemma ιTotal_totalToTotalProduct_f_πTotalProduct_self (n p q : I)
    (h : ComplexShape.π c c c (p, q) = n) (h' : ComplexShape.π c.symm c.symm c.symm (p, q) = n) :
    K.ιTotal c p q n h ≫ (K.totalToTotalProduct).f n ≫ K.πTotalProduct c p q n h' = 𝟙 _ :=
  K.ιTotal_totalToTotalProductX_πTotalProduct_self n p q h h'

@[reassoc]
lemma ιTotal_totalToTotalProduct_f_πTotalProduct_of_ne (n p q p' q' : I)
    (h : ComplexShape.π c c c (p, q) = n) (h' : ComplexShape.π c.symm c.symm c.symm (p', q') = n)
    (hne : (p, q) ≠ (p', q')) :
    K.ιTotal c p q n h ≫ (K.totalToTotalProduct).f n ≫ K.πTotalProduct c p' q' n h' = 0 := by
  rw [ιTotal_totalToTotalProduct_f_πTotalProduct, dite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact hne rfl

variable {K L} in
/-- The comparison map from the direct sum total complex to the product total complex is natural
in the bicomplex. -/
@[reassoc]
lemma totalToTotalProduct_naturality :
    total.map φ c ≫ L.totalToTotalProduct = K.totalToTotalProduct ≫ totalProduct.map φ c := by
  ext n p q h p' q' h'
  simp only [HomologicalComplex.comp_f, Category.assoc, ιTotal_map_assoc,
    totalProduct.map_f_πTotalProduct]
  by_cases hpq : (p, q) = (p', q')
  · obtain ⟨rfl, rfl⟩ := hpq
    simp
  · rw [L.ιTotal_totalToTotalProduct_f_πTotalProduct_of_ne _ _ _ _ _ h h' hpq,
      K.ιTotal_totalToTotalProduct_f_πTotalProduct_of_ne_assoc _ _ _ _ _ h h' hpq, comp_zero,
      zero_comp]

/-- In a degree `n` in which only finitely many terms `(K.X p).X q` with `p + q = n` are nonzero,
the comparison map from the direct sum total complex to the product total complex is an
isomorphism. -/
lemma isIso_totalToTotalProduct_f (n : I)
    (hn : {x : I × I | x.1 + x.2 = n ∧ ¬ IsZero ((K.X x.1).X x.2)}.Finite) :
    IsIso ((K.totalToTotalProduct).f n) := by
  refine ⟨∑ x ∈ hn.toFinset, K.πTotalProductOrZero c x.1 x.2 n ≫ K.ιTotalOrZero c x.1 x.2 n,
    ?_, ?_⟩
  · ext p q h
    by_cases hz : IsZero ((K.X p).X q)
    · exact hz.eq_of_src _ _
    rw [Preadditive.comp_sum, Preadditive.comp_sum, Finset.sum_eq_single (p, q)]
    · rw [πTotalProductOrZero_eq _ _ _ _ _ (by simpa using h),
        reassoc_of% (K.ιTotal_totalToTotalProduct_f_πTotalProduct_self n p q h),
        ιTotalOrZero_eq _ _ _ _ _ h, Category.comp_id]
    · intro x _ hx
      rw [totalToTotalProduct_f, reassoc_of%
        (K.ιTotal_totalToTotalProductX_πTotalProductOrZero_of_ne n p q x.1 x.2 h (Ne.symm hx)),
        zero_comp]
    · intro hx
      exact (hx (by simpa [hz] using h)).elim
  · ext p' q' h'
    by_cases hz : IsZero ((K.X p').X q')
    · exact hz.eq_of_tgt _ _
    rw [Preadditive.sum_comp, Preadditive.sum_comp, Finset.sum_eq_single (p', q')]
    · rw [Category.assoc, Category.assoc, ιTotalOrZero_eq _ _ _ _ _ (by simpa using h'),
        ιTotal_totalToTotalProduct_f_πTotalProduct_self, Category.comp_id,
        πTotalProductOrZero_eq _ _ _ _ _ h', Category.id_comp]
    · intro x _ hx
      rw [Category.assoc, Category.assoc, totalToTotalProduct_f,
        K.ιTotalOrZero_totalToTotalProductX_πTotalProduct_of_ne n x.1 x.2 p' q' h' hx, comp_zero]
    · intro hx
      exact (hx (by simpa [hz] using h')).elim

/-- When each antidiagonal has only finitely many nonzero terms, the comparison map from the
direct sum total complex to the product total complex is an isomorphism. -/
lemma isIso_totalToTotalProduct
    (h : ∀ n, {x : I × I | x.1 + x.2 = n ∧ ¬ IsZero ((K.X x.1).X x.2)}.Finite) :
    IsIso K.totalToTotalProduct := by
  have := fun n ↦ K.isIso_totalToTotalProduct_f n (h n)
  apply HomologicalComplex.Hom.isIso_of_components

variable [TotalComplexShapeSymmetry c c c]

/-- The comparison map from the direct sum total complex to the product total complex commutes
with the isomorphisms identifying the total complexes of a bicomplex and of its flip. -/
@[reassoc]
lemma totalFlipIso_hom_totalToTotalProduct :
    (K.totalFlipIso c).hom ≫ K.totalToTotalProduct =
      K.flip.totalToTotalProduct ≫ (K.totalProductFlipIso c).hom := by
  ext n q p h p' q' h'
  have h₁ : ComplexShape.π c c c (p, q) = n := (ComplexShape.π_symm c c c p q).symm.trans h
  have h₂ : ComplexShape.π c.symm c.symm c.symm (q', p') = n :=
    (ComplexShape.π_symm c.symm c.symm c.symm p' q').trans h'
  -- The terms of `K.flip` are those of `K` only up to unfolding `flip`, so the two sides are
  -- rewritten separately, each into a well-typed expression.
  have e₁ : K.flip.ιTotal c q p n h ≫ (K.totalFlipIso c).hom.f n ≫
      K.totalToTotalProduct.f n ≫ K.πTotalProduct c p' q' n h' =
        ComplexShape.σ c c c p q •
          (K.ιTotal c p q n h₁ ≫ K.totalToTotalProduct.f n ≫ K.πTotalProduct c p' q' n h') :=
    (K.ιTotal_totalFlipIso_f_hom_assoc c p q n h _).trans (Linear.units_smul_comp _ _ _)
  have e₂ : K.flip.ιTotal c q p n h ≫ K.flip.totalToTotalProduct.f n ≫
      (K.totalProductFlipIso c).hom.f n ≫ K.πTotalProduct c p' q' n h' =
        ComplexShape.σ c c c p' q' •
          (K.flip.ιTotal c q p n h ≫ K.flip.totalToTotalProduct.f n ≫
            K.flip.πTotalProduct c q' p' n h₂) :=
    (congrArg (fun g ↦ K.flip.ιTotal c q p n h ≫ K.flip.totalToTotalProduct.f n ≫ g)
      (K.totalProductFlipIso_hom_f_πTotalProduct c p' q' n h')).trans
      ((congrArg _ (Linear.comp_units_smul _ _ _)).trans (Linear.comp_units_smul _ _ _))
  simp only [HomologicalComplex.comp_f, Category.assoc]
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  by_cases hpq : (p, q) = (p', q')
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [ιTotal_totalToTotalProduct_f_πTotalProduct_self,
      ιTotal_totalToTotalProduct_f_πTotalProduct_self]
    rfl
  · rw [K.ιTotal_totalToTotalProduct_f_πTotalProduct_of_ne _ _ _ _ _ _ _ hpq,
      K.flip.ιTotal_totalToTotalProduct_f_πTotalProduct_of_ne _ _ _ _ _ _ _
        (fun h ↦ hpq (by simp_all)), smul_zero, smul_zero]

end TensorSigns

end HomologicalComplex₂
