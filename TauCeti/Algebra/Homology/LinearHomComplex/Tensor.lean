/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Composition
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The tensor product of cochains and of linear Hom complexes

Let `X₁`, `X₂`, `Y₁` and `Y₂` be cochain complexes of modules over a commutative ring `R`. A
cochain `z₁ : X₁ ⟶ Y₁` of degree `p` and a cochain `z₂ : X₂ ⟶ Y₂` of degree `q` have a tensor
product `z₁.tensor z₂ : X₁ ⊗ X₂ ⟶ Y₁ ⊗ Y₂` of degree `p + q`, given on homogeneous elements by
the Koszul rule

`(z₁ ⊗ z₂)(x ⊗ y) = (-1)^(q |x|) z₁(x) ⊗ z₂(y)`,

the sign coming from moving `z₂` past `x`. With Mathlib's differential
`δ z = d ∘ z - (-1)^|z| z ∘ d` on cochains and the Koszul differential of `X ⊗ Y`, it satisfies the
Leibniz rule `δ (z₁ ⊗ z₂) = δ z₁ ⊗ z₂ + (-1)^p z₁ ⊗ δ z₂`
(`CochainComplex.HomComplex.Cochain.δ_tensor`). So the tensor product is a morphism of complexes

`Hom(X₁, Y₁) ⊗ Hom(X₂, Y₂) ⟶ Hom(X₁ ⊗ X₂, Y₁ ⊗ Y₂)`

of `R`-linear Hom complexes (`TauCeti.linearHomComplexTensor`). On chain maps it is the tensor
product of morphisms of complexes (`CochainComplex.HomComplex.Cochain.ofHom_tensor_ofHom`), it obeys
the interchange law with composition, up to the Koszul sign of the two middle factors
(`CochainComplex.HomComplex.Cochain.tensor_comp_tensor`), and it is natural in all four complexes.

For duals `A∨ = Hom(A, R[0])`, with the dual differential `d f = (-1)^(|f| + 1) f ∘ d`, the tensor
product, the Koszul braiding and the unitor `R[0] ⊗ R[0] ≅ R[0]` give the comparison

`B∨ ⊗ A∨ ⟶ (A ⊗ B)∨`, `(g ⊗ f)(a ⊗ b) = f(a) g(b)`

(`TauCeti.linearHomComplexDualDistrib`), a complex-level form of `TensorProduct.dualDistrib` with
the factors in the reverse order. In this order, in which the inner factors `f` and `a` are paired
first, it carries no sign (`CochainComplex.HomComplex.Cochain.ιTensorObj_dualDistrib_v`). Applied to
`A` and `B∨` it is the comparison `B∨∨ ⊗ A∨ ⟶ (A ⊗ B∨)∨`, which sends tensors to functionals on
`A ⊗ B∨`; its inverse, which exists under finiteness hypotheses and is not constructed here,
converts such functionals back into tensors.

## Main definitions

* `CochainComplex.HomComplex.Cochain.tensor`: the tensor product of cochains.
* `TauCeti.linearHomComplexTensor`: the tensor product as a morphism of linear Hom complexes.
* `CochainComplex.HomComplex.Cochain.dualDistrib` and `TauCeti.linearHomComplexDualDistrib`: the
  pairing of dual cochains and the comparison `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨`.

## Main results

* `CochainComplex.HomComplex.Cochain.ιTensorObj_tensor_v`: the tensor product of cochains on a
  homogeneous summand.
* `CochainComplex.HomComplex.Cochain.δ_tensor`: the Leibniz rule.
* `CochainComplex.HomComplex.Cochain.tensor_comp_tensor`: the interchange law.
* `TauCeti.linearHomComplexTensor_naturality_source` and
  `TauCeti.linearHomComplexTensor_naturality_target`: naturality.
* `CochainComplex.leftUnitor_hom_f_zero_ιTensorObj_tmul`: on the degree-`0` summand of
  `R[0] ⊗ R[0]`, the unitor `R[0] ⊗ R[0] ≅ R[0]` is the multiplication of `R`.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. **27** (1994), Section 1, for
  the Koszul sign rule on tensor products of graded maps.
* Joël Riou's cochain and `δ` API in `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`
  and the totalized monoidal structure of Joël Riou and Kim Morrison in
  `Mathlib/Algebra/Homology/Monoidal.lean`, whose sign conventions this file inherits; the
  construction follows `TauCeti.linearHomComplexComp`.
-/

public section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe v

namespace CochainComplex.HomComplex.Cochain

variable {R : Type v} [CommRing R] {X₁ X₂ Y₁ Y₂ : CochainComplex (ModuleCat.{v} R) ℤ}

/-- The tensor product of a cochain `z₁ : X₁ ⟶ Y₁` of degree `p` and a cochain `z₂ : X₂ ⟶ Y₂` of
degree `q`, a cochain `X₁ ⊗ X₂ ⟶ Y₁ ⊗ Y₂` of degree `n = p + q`. On the summand `X₁.X a ⊗ X₂.X b`
it is `(-1)^(q a) (z₁ ⊗ z₂)` (`CochainComplex.HomComplex.Cochain.ιTensorObj_tensor_v`). -/
noncomputable def tensor {p q : ℤ} (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (n : ℤ)
    (h : p + q = n) : Cochain (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) n :=
  Cochain.mk fun i j hij ↦ mapBifunctorDesc fun a b hab ↦
    (q * a).negOnePow • ((z₁.v a (a + p) rfl ⊗ₘ z₂.v b (b + q) rfl) ≫
      ιTensorObj Y₁ Y₂ (a + p) (b + q) j (by dsimp at hab; omega))

/-- The tensor product of cochains on the summand `X₁.X a ⊗ X₂.X b`: the tensor product of the
components, with the Koszul sign `(-1)^(q a)`, followed by the inclusion of the summand
`Y₁.X a' ⊗ Y₂.X b'`. The target degrees `a' = a + p` and `b' = b + q` are passed as separate
variables so that callers need not rewrite them. -/
@[reassoc]
lemma ιTensorObj_tensor_v {p q n : ℤ} (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q)
    (h : p + q = n) (a b i j a' b' : ℤ) (hab : a + b = i) (hij : i + n = j) (ha : a + p = a')
    (hb : b + q = b') :
    ιTensorObj X₁ X₂ a b i hab ≫ (z₁.tensor z₂ n h).v i j hij =
      (q * a).negOnePow • ((z₁.v a a' ha ⊗ₘ z₂.v b b' hb) ≫
        ιTensorObj Y₁ Y₂ a' b' j (by omega)) := by
  subst ha hb
  simp [tensor]

/-- A cochain out of a tensor product of complexes is determined by its restrictions to the
homogeneous summands. -/
lemma ext_tensorObj {K : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}
    {z z' : Cochain (X₁ ⊗ X₂) K n}
    (h : ∀ a b i j (hab : a + b = i) (hij : i + n = j),
      ιTensorObj X₁ X₂ a b i hab ≫ z.v i j hij = ιTensorObj X₁ X₂ a b i hab ≫ z'.v i j hij) :
    z = z' :=
  Cochain.ext _ _ fun i j hij ↦ mapBifunctor.hom_ext fun a b hab ↦ h a b i j hab hij

/-- **The Leibniz rule for the tensor product of cochains.**
`δ (z₁ ⊗ z₂) = δ z₁ ⊗ z₂ + (-1)^p z₁ ⊗ δ z₂` for `z₁` of degree `p`. -/
lemma δ_tensor {p q n m : ℤ} (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q)
    (h : p + q = n) (hnm : n + 1 = m) :
    δ n m (z₁.tensor z₂ n h) =
      (δ p (p + 1) z₁).tensor z₂ m (by omega) +
        p.negOnePow • z₁.tensor (δ q (q + 1) z₂) m (by omega) := by
  subst h hnm
  refine ext_tensorObj fun a b i j hab hij ↦ ?_
  -- Expand `δ` of the tensor product on the summand `X₁.X a ⊗ X₂.X b`, and the right-hand side
  -- into its two summands.
  rw [δ_v (p + q) (p + q + 1) rfl _ i j hij (j - 1) (i + 1) rfl rfl, Preadditive.comp_add, add_v,
    units_smul_v, Preadditive.comp_add, Linear.comp_units_smul, Linear.comp_units_smul]
  -- Push the summand inclusion through `z₁.tensor z₂` and through the differentials of
  -- `Y₁ ⊗ Y₂` and `X₁ ⊗ X₂`; each of the latter splits into two summand terms.
  rw [ιTensorObj_tensor_v_assoc z₁ z₂ rfl a b i (j - 1) (a + p) (b + q) hab (by omega) rfl rfl,
    Linear.units_smul_comp, Category.assoc,
    ι_tensorObj_d' Y₁ Y₂ (by omega : a + p + (b + q) = j - 1) rfl rfl (by omega : j - 1 + 1 = j),
    ι_tensorObj_d'_assoc X₁ X₂ hab rfl rfl rfl, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc]
  -- Evaluate every remaining tensor product of cochains on its summand.
  rw [ιTensorObj_tensor_v z₁ z₂ rfl (a + 1) b (i + 1) j (a + p + 1) (b + q) _ _ (by omega) rfl,
    ιTensorObj_tensor_v z₁ z₂ rfl a (b + 1) (i + 1) j (a + p) (b + q + 1) _ _ rfl (by omega),
    ιTensorObj_tensor_v (δ p (p + 1) z₁) z₂ _ a b i j (a + p + 1) (b + q) hab _ (by omega) rfl,
    ιTensorObj_tensor_v z₁ (δ q (q + 1) z₂) _ a b i j (a + p) (b + q + 1) hab _ rfl (by omega)]
  -- Expand `δ z₁` and `δ z₂` on their components.
  rw [δ_v p (p + 1) rfl z₁ a (a + p + 1) _ (a + p) (a + 1) (by omega) rfl,
    δ_v q (q + 1) rfl z₂ b (b + q + 1) _ (b + q) (b + 1) (by omega) rfl]
  -- Distribute, collect the four terms on each side as signed tensor products of components,
  -- and match their Koszul signs.
  simp only [MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add, Units.smul_def,
    zsmul_tensorHom, tensorHom_zsmul, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_add, smul_smul, ← Units.val_mul,
    ← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, ← Int.negOnePow_add]
  have h₁ : (p + q + 1 + q * (a + 1)).negOnePow = (q * a + (p + 1)).negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨q, by ring⟩
  have h₂ : (p + q + 1 + (a + q * a)).negOnePow = (p + ((q + 1) * a + (q + 1))).negOnePow := by
    congr 1; ring
  rw [h₁, h₂, show q * a + (a + p) = p + (q + 1) * a by ring]
  abel

variable {p q n : ℤ}

/-- The tensor product of cochains is additive in the first factor. -/
@[simp]
lemma add_tensor (z₁ z₁' : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    (z₁ + z₁').tensor z₂ n h = z₁.tensor z₂ n h + z₁'.tensor z₂ n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [add_v, Preadditive.comp_add, ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl,
      MonoidalPreadditive.add_tensor, Preadditive.add_comp, smul_add]

/-- The tensor product of cochains is additive in the second factor. -/
@[simp]
lemma tensor_add (z₁ : Cochain X₁ Y₁ p) (z₂ z₂' : Cochain X₂ Y₂ q) (h : p + q = n) :
    z₁.tensor (z₂ + z₂') n h = z₁.tensor z₂ n h + z₁.tensor z₂' n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [add_v, Preadditive.comp_add, ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl,
      MonoidalPreadditive.tensor_add, Preadditive.add_comp, smul_add]

/-- The tensor product of cochains is `R`-linear in the first factor. -/
@[simp]
lemma smul_tensor (r : R) (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    (r • z₁).tensor z₂ n h = r • z₁.tensor z₂ n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [smul_v, Linear.comp_smul, ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl,
      tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, smul_comm r]

/-- The tensor product of cochains is `R`-linear in the second factor. -/
@[simp]
lemma tensor_smul (r : R) (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    z₁.tensor (r • z₂) n h = r • z₁.tensor z₂ n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [smul_v, Linear.comp_smul, ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl,
      tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul,
      smul_comm r]

/-- The tensor product of cochains commutes with signs in the first factor. -/
@[simp]
lemma units_smul_tensor (ε : ℤˣ) (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    (ε • z₁).tensor z₂ n h = ε • z₁.tensor z₂ n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [units_smul_v, Linear.comp_units_smul,
      ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl]
    simp only [Units.smul_def, zsmul_tensorHom, Preadditive.zsmul_comp, smul_comm (ε : ℤ)]

/-- The tensor product of cochains commutes with signs in the second factor. -/
@[simp]
lemma tensor_units_smul (ε : ℤˣ) (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    z₁.tensor (ε • z₂) n h = ε • z₁.tensor z₂ n h :=
  ext_tensorObj fun a b i j hab hij ↦ by
    simp only [units_smul_v, Linear.comp_units_smul,
      ιTensorObj_tensor_v _ _ h a b i j _ _ hab hij rfl rfl]
    simp only [Units.smul_def, tensorHom_zsmul, Preadditive.zsmul_comp, smul_comm (ε : ℤ)]

/-- The tensor product of cochains vanishes when the first factor does. -/
@[simp]
lemma zero_tensor (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    (0 : Cochain X₁ Y₁ p).tensor z₂ n h = 0 := by
  simpa using smul_tensor (0 : R) (0 : Cochain X₁ Y₁ p) z₂ h

/-- The tensor product of cochains vanishes when the second factor does. -/
@[simp]
lemma tensor_zero (z₁ : Cochain X₁ Y₁ p) (h : p + q = n) :
    z₁.tensor (0 : Cochain X₂ Y₂ q) n h = 0 := by
  simpa using tensor_smul (0 : R) z₁ (0 : Cochain X₂ Y₂ q) h

/-- The tensor product of cochains commutes with negation in the first factor. -/
@[simp]
lemma neg_tensor (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    (-z₁).tensor z₂ n h = -z₁.tensor z₂ n h :=
  eq_neg_of_add_eq_zero_left (by rw [← add_tensor, neg_add_cancel, zero_tensor])

/-- The tensor product of cochains commutes with negation in the second factor. -/
@[simp]
lemma tensor_neg (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (h : p + q = n) :
    z₁.tensor (-z₂) n h = -z₁.tensor z₂ n h :=
  eq_neg_of_add_eq_zero_left (by rw [← tensor_add, neg_add_cancel, tensor_zero])

/-- The tensor product of the cochains of two morphisms of complexes is the cochain of their
tensor product. -/
@[simp]
lemma ofHom_tensor_ofHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (ofHom f₁).tensor (ofHom f₂) 0 (add_zero 0) = ofHom (f₁ ⊗ₘ f₂) :=
  ext_tensorObj fun a b i j hab hij ↦ by
    obtain rfl : i = j := by omega
    rw [ιTensorObj_tensor_v _ _ _ a b i i a b hab hij (add_zero a) (add_zero b)]
    rw [ofHom_v, ofHom_v, ofHom_v, zero_mul, Int.negOnePow_zero, one_smul]
    exact (ι_tensorHom f₁ f₂ a b i hab).symm

/-- **The interchange law.** Composing tensor products of cochains is the tensor product of the
composites, up to the Koszul sign `(-1)^(q' p)` of moving `w₂`, of degree `q'`, past `z₁`, of
degree `p`. -/
lemma tensor_comp_tensor {Z₁ Z₂ : CochainComplex (ModuleCat.{v} R) ℤ} {p' q' n' m : ℤ}
    (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (w₁ : Cochain Y₁ Z₁ p')
    (w₂ : Cochain Y₂ Z₂ q') (h : p + q = n) (h' : p' + q' = n') (hm : n + n' = m) {r₁ r₂ : ℤ}
    (h₁ : p + p' = r₁) (h₂ : q + q' = r₂) :
    (z₁.tensor z₂ n h).comp (w₁.tensor w₂ n' h') hm =
      (q' * p).negOnePow • (z₁.comp w₁ h₁).tensor (z₂.comp w₂ h₂) m (by omega) :=
  ext_tensorObj fun a b i j hab hij ↦ by
    subst h₁ h₂
    -- Split the composite at degree `i + n`, and evaluate both tensor products on the summands
    -- `X₁.X a ⊗ X₂.X b` and `Y₁.X (a + p) ⊗ Y₂.X (b + q)` they pass through.
    rw [comp_v _ _ hm i (i + n) j rfl (by omega), units_smul_v, Linear.comp_units_smul,
      ιTensorObj_tensor_v_assoc _ _ h a b i (i + n) (a + p) (b + q) hab rfl rfl rfl,
      Linear.units_smul_comp, Category.assoc,
      ιTensorObj_tensor_v _ _ h' (a + p) (b + q) (i + n) j (a + p + p') (b + q + q') (by omega)
        (by omega) rfl rfl]
    -- Evaluate the right-hand side on the same summand, then gather the signs into one
    -- `negOnePow` and the components into one tensor product of composites.
    rw [ιTensorObj_tensor_v _ _ _ a b i j (a + p + p') (b + q + q') hab hij (by omega) (by omega),
      comp_v _ _ rfl a (a + p) (a + p + p') rfl rfl, comp_v _ _ rfl b (b + q) (b + q + q') rfl rfl,
      Linear.comp_units_smul, smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add,
      ← tensorHom_comp_tensorHom_assoc]
    -- The two Koszul exponents agree.
    congr 2
    ring

/-- The tensor product of cochains is natural in the targets. -/
lemma comp_ofHom_tensor_comp_ofHom {Z₁ Z₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂)
    (h : p + q = n) :
    (z₁.comp (ofHom g₁) (add_zero p)).tensor (z₂.comp (ofHom g₂) (add_zero q)) n h =
      (z₁.tensor z₂ n h).comp (ofHom (g₁ ⊗ₘ g₂)) (add_zero n) := by
  rw [← ofHom_tensor_ofHom, tensor_comp_tensor _ _ _ _ _ _ _ (add_zero p) (add_zero q), zero_mul,
    Int.negOnePow_zero, one_smul]

/-- The tensor product of cochains is natural in the sources. -/
lemma ofHom_comp_tensor_ofHom_comp {W₁ W₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (f₁ : W₁ ⟶ X₁) (f₂ : W₂ ⟶ X₂) (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q)
    (h : p + q = n) :
    ((ofHom f₁).comp z₁ (zero_add p)).tensor ((ofHom f₂).comp z₂ (zero_add q)) n h =
      (ofHom (f₁ ⊗ₘ f₂)).comp (z₁.tensor z₂ n h) (zero_add n) := by
  rw [← ofHom_tensor_ofHom, tensor_comp_tensor _ _ _ _ _ _ _ (zero_add p) (zero_add q), mul_zero,
    Int.negOnePow_zero, one_smul]

section Dual

variable {A B : CochainComplex (ModuleCat.{v} R) ℤ} {i j : ℤ}

/-- The pairing of a cochain `g : B ⟶ R[0]` of degree `i` and a cochain `f : A ⟶ R[0]` of degree
`j` into a cochain `A ⊗ B ⟶ R[0]` of degree `n = i + j`: on homogeneous elements it is
`a ⊗ b ↦ f(a) g(b)`, with no sign (`Cochain.ιTensorObj_dualDistrib_v`). It is the tensor product
`f.tensor g` followed by the unitor `R[0] ⊗ R[0] ≅ R[0]`, corrected by the Koszul sign
`(-1)^(i j)` of the reversed order of the factors. -/
noncomputable def dualDistrib (g : Cochain B (𝟙_ _) i) (f : Cochain A (𝟙_ _) j) (n : ℤ)
    (h : i + j = n) : Cochain (A ⊗ B) (𝟙_ _) n :=
  (i * j).negOnePow • (f.tensor g n (by omega)).comp (ofHom (λ_ _).hom) (add_zero n)

/-- `Cochain.dualDistrib` is the tensor product `f.tensor g` followed by the unitor
`R[0] ⊗ R[0] ≅ R[0]`, corrected by the Koszul sign `(-1)^(i j)`. -/
lemma dualDistrib_def (g : Cochain B (𝟙_ _) i) (f : Cochain A (𝟙_ _) j) (n : ℤ)
    (h : i + j = n) :
    g.dualDistrib f n h =
      (i * j).negOnePow • (f.tensor g n (by omega)).comp (ofHom (λ_ _).hom) (add_zero n) :=
  (rfl)

/-- **`Cochain.dualDistrib` has no sign.** On the summand `A.X a ⊗ B.X b`, the pairing of `g` and
`f` is `f ⊗ g` followed by the unitor of the tensor unit. -/
lemma ιTensorObj_dualDistrib_v (g : Cochain B (𝟙_ _) i) (f : Cochain A (𝟙_ _) j) {n : ℤ}
    (h : i + j = n) (a b k l a' b' : ℤ) (hab : a + b = k) (hkl : k + n = l) (ha : a + j = a')
    (hb : b + i = b') :
    ιTensorObj A B a b k hab ≫ (g.dualDistrib f n h).v k l hkl =
      (f.v a a' ha ⊗ₘ g.v b b' hb) ≫ ιTensorObj (𝟙_ _) (𝟙_ _) a' b' l (by omega) ≫
        ((λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).hom.f l) := by
  rw [dualDistrib_def, units_smul_v, comp_zero_cochain_v, ofHom_v, Linear.comp_units_smul,
    ιTensorObj_tensor_v_assoc _ _ _ a b k l a' b' hab hkl ha hb, Linear.units_smul_comp,
    smul_smul, ← Int.negOnePow_add]
  by_cases ha' : a' = 0
  · rw [show i * j + i * a = 0 by rw [← mul_add, add_comm, ha, ha', mul_zero],
      Int.negOnePow_zero, one_smul, Category.assoc]
  · have hf : f.v a a' ha = 0 :=
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ ha').eq_of_tgt _ _
    rw [hf, MonoidalPreadditive.zero_tensor, zero_comp, zero_comp, zero_comp, smul_zero]

end Dual

end CochainComplex.HomComplex.Cochain

namespace CochainComplex

open scoped TensorProduct

variable {R : Type v} [CommRing R]

/-- On the degree-`0` summand `R ⊗ R` of `R[0] ⊗ R[0]`, the left unitor of cochain complexes is
the multiplication of `R`, after identifying the degree-`0` term of `R[0]` with `R`. -/
lemma leftUnitor_hom_f_zero_ιTensorObj_tmul
    (u w : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).X 0) :
    ((λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).hom.f 0).hom
        ((HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (𝟙_ _) 0 0 0
          (zero_add 0)).hom (u ⊗ₜ w)) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom.hom u • w := by
  set e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))
  have hu : u = e.hom.hom u • e.inv.hom 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (congrArg (fun φ => φ.hom u) e.hom_inv_id).symm
  have hw : (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (𝟙_ _) 0 0 0
      (zero_add 0)).hom (e.inv.hom 1 ⊗ₜ w) =
        ((λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).inv.f 0).hom w := by
    rw [HomologicalComplex.leftUnitor_inv_f]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    -- `ConcreteCategory.hom` and `ModuleCat.Hom.hom` agree on `ModuleCat`.
    rfl
  conv_lhs => rw [hu, ← TensorProduct.smul_tmul', map_smul, map_smul, hw]
  exact congrArg _ <| Iso.inv_hom_id_apply
    (HomologicalComplex.Hom.isoApp (λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) 0) w

end CochainComplex

namespace TauCeti

open CochainComplex CochainComplex.HomComplex

variable (R : Type v) [CommRing R] (X₁ Y₁ X₂ Y₂ : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The tensor product of a degree-`p` cochain from `X₁` to `Y₁` with a degree-`q` cochain from
`X₂` to `Y₂`, as a map out of the tensor product of the two cochain modules. This is the
bidegree-`(p, q)` component of `TauCeti.linearHomComplexTensor`. -/
noncomputable def cochainTensorTensor (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    (linearHomComplex R X₁ Y₁).X p ⊗ (linearHomComplex R X₂ Y₂).X q ⟶
      (linearHomComplex R (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).X j :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (z₁ : Cochain X₁ Y₁ p) (z₂ : Cochain X₂ Y₂ q) => z₁.tensor z₂ j h)
    (fun _ _ _ => Cochain.add_tensor _ _ _ _)
    (fun _ _ _ => Cochain.smul_tensor _ _ _ _)
    (fun _ _ _ => Cochain.tensor_add _ _ _ _)
    (fun _ _ _ => Cochain.tensor_smul _ _ _ _)

/-- On a pure tensor, `cochainTensorTensor` sends `z₁ ⊗ₜ z₂` to the tensor product of cochains
`z₁.tensor z₂`. -/
@[simp]
lemma cochainTensorTensor_tmul (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j)
    (z₁ : ModuleCat.of R (Cochain X₁ Y₁ p)) (z₂ : ModuleCat.of R (Cochain X₂ Y₂ q)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom (cochainTensorTensor R X₁ Y₁ X₂ Y₂ p q j h) (z₁ ⊗ₜ z₂)) =
      (z₁.tensor z₂ j h : ModuleCat.of R (Cochain (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) j)) :=
  (rfl)

/- As in `TauCeti.linearHomComplexComp`, the totalized tensor differential of the two Hom
complexes is expanded on a summand by `HomologicalComplex.ι_tensorObj_d`, and the Leibniz rule
`Cochain.δ_tensor` closes the square. -/
private lemma cochainTensorTensor_d (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R X₁ Y₁) (linearHomComplex R X₂ Y₂)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
        (linearHomComplex R X₁ Y₁ ⊗ linearHomComplex R X₂ Y₂).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc (cochainTensorTensor R X₁ Y₁ X₂ Y₂ · · (j + 1) ·) =
      cochainTensorTensor R X₁ Y₁ X₂ Y₂ p q j h ≫
        (linearHomComplex R (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).d j (j + 1) := by
  -- `ComplexShape.π` is an abbreviation; Mathlib has no named specialization at
  -- `ComplexShape.up ℤ`.
  replace h : p + q = j := h
  rw [HomologicalComplex.ι_tensorObj_d_assoc _ _ p q j h, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₁ z₂
  let z₁' : ModuleCat.of R (Cochain X₁ Y₁ p) := z₁
  let z₂' : ModuleCat.of R (Cochain X₂ Y₂ q) := z₂
  simp only [curriedTensor_obj_obj, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    curriedTensor_map_app, curriedTensor_obj_map, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.add_apply, ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  -- Read the differential of the tensor product on this pure tensor in the degreewise cochain
  -- modules characterized by `linearHomComplex_X`.
  change ModuleCat.Hom.hom (cochainTensorTensor R X₁ Y₁ X₂ Y₂ (p + 1) q (j + 1)
        (show p + 1 + q = j + 1 by omega)) (
        ModuleCat.Hom.hom ((linearHomComplex R X₁ Y₁).d p (p + 1)) z₁' ⊗ₜ z₂') +
      p.negOnePow • ModuleCat.Hom.hom (cochainTensorTensor R X₁ Y₁ X₂ Y₂ p (q + 1) (j + 1)
        (show p + (q + 1) = j + 1 by omega))
        (z₁' ⊗ₜ ModuleCat.Hom.hom ((linearHomComplex R X₂ Y₂).d q (q + 1)) z₂') =
    ModuleCat.Hom.hom ((linearHomComplex R (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).d j (j + 1))
      (ModuleCat.Hom.hom (cochainTensorTensor R X₁ Y₁ X₂ Y₂ p q j h) (z₁' ⊗ₜ z₂'))
  rw [linearHomComplex_d_hom_apply, linearHomComplex_d_hom_apply, cochainTensorTensor_tmul,
    cochainTensorTensor_tmul, cochainTensorTensor_tmul, linearHomComplex_d_hom_apply]
  exact (Cochain.δ_tensor z₁' z₂' h (by omega)).symm

/-- **The tensor product of cochains is a closed degree-zero map.** It assembles into a morphism
of cochain complexes of `R`-modules
`Hom(X₁, Y₁) ⊗ Hom(X₂, Y₂) ⟶ Hom(X₁ ⊗ X₂, Y₁ ⊗ Y₂)`; the Leibniz rule `Cochain.δ_tensor` is
precisely the condition for this to be a chain map. -/
noncomputable def linearHomComplexTensor :
    linearHomComplex R X₁ Y₁ ⊗ linearHomComplex R X₂ Y₂ ⟶
      linearHomComplex R (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) where
  f j := HomologicalComplex.mapBifunctorDesc (cochainTensorTensor R X₁ Y₁ X₂ Y₂ · · j ·)
  comm' j j' hjj' := by
    -- `ComplexShape.Rel` for `ComplexShape.up ℤ` unfolds to `j + 1 = j'` by definition.
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact (cochainTensorTensor_d R X₁ Y₁ X₂ Y₂ p q j h).symm

/-- The degree-`j` component of `linearHomComplexTensor` is induced by its maps on the bidegree
summands of the totalized tensor product. -/
private lemma linearHomComplexTensor_f (j : ℤ) :
    (linearHomComplexTensor R X₁ Y₁ X₂ Y₂).f j =
      HomologicalComplex.mapBifunctorDesc (cochainTensorTensor R X₁ Y₁ X₂ Y₂ · · j ·) :=
  rfl

/-- The degree-`j` component of `linearHomComplexTensor` restricted to the bidegree-`(p, q)`
summand is `cochainTensorTensor`; see `cochainTensorTensor_tmul` for its value on pure
tensors. -/
@[reassoc (attr := simp)]
lemma ι_linearHomComplexTensor (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R X₁ Y₁) (linearHomComplex R X₂ Y₂)
        (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
      (linearHomComplexTensor R X₁ Y₁ X₂ Y₂).f j = cochainTensorTensor R X₁ Y₁ X₂ Y₂ p q j h :=
  by
  rw [linearHomComplexTensor_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- On a pure tensor `z₁ ⊗ₜ z₂` of the bidegree-`(p, q)` summand, the degree-`j` component of
`linearHomComplexTensor` is the tensor product of cochains `z₁.tensor z₂`. -/
lemma ι_linearHomComplexTensor_tmul (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j)
    (z₁ : ModuleCat.of R (Cochain X₁ Y₁ p)) (z₂ : ModuleCat.of R (Cochain X₂ Y₂ q)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexTensor R X₁ Y₁ X₂ Y₂).f j)
        (ModuleCat.Hom.hom (HomologicalComplex.ιMapBifunctor (linearHomComplex R X₁ Y₁)
          (linearHomComplex R X₂ Y₂) (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ)
            p q j h) (z₁ ⊗ₜ z₂))) =
      (z₁.tensor z₂ j h : ModuleCat.of R (Cochain (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) j)) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ι_linearHomComplexTensor,
    cochainTensorTensor_tmul]

variable {X₁ Y₁ X₂ Y₂}

/-- `TauCeti.linearHomComplexTensor` is natural in the targets. -/
@[reassoc]
lemma linearHomComplexTensor_naturality_target {Z₁ Z₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (linearHomComplexPostcomp R X₁ g₁ ⊗ₘ linearHomComplexPostcomp R X₂ g₂) ≫
        linearHomComplexTensor R X₁ Z₁ X₂ Z₂ =
      linearHomComplexTensor R X₁ Y₁ X₂ Y₂ ≫ linearHomComplexPostcomp R (X₁ ⊗ X₂) (g₁ ⊗ₘ g₂) := by
  apply linearHomComplex_tensor_hom_ext
  intro p q j h z₁ z₂
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ← Category.assoc]
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  rw [ι_linearHomComplexTensor_tmul, ι_linearHomComplexTensor_tmul,
    linearHomComplexPostcomp_f_apply, linearHomComplexPostcomp_f_apply,
    linearHomComplexPostcomp_f_apply]
  exact Cochain.comp_ofHom_tensor_comp_ofHom z₁ z₂ g₁ g₂ h

/-- `TauCeti.linearHomComplexTensor` is natural in the sources. -/
@[reassoc]
lemma linearHomComplexTensor_naturality_source {W₁ W₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (f₁ : W₁ ⟶ X₁) (f₂ : W₂ ⟶ X₂) :
    (linearHomComplexPrecomp R f₁ Y₁ ⊗ₘ linearHomComplexPrecomp R f₂ Y₂) ≫
        linearHomComplexTensor R W₁ Y₁ W₂ Y₂ =
      linearHomComplexTensor R X₁ Y₁ X₂ Y₂ ≫ linearHomComplexPrecomp R (f₁ ⊗ₘ f₂) (Y₁ ⊗ Y₂) := by
  apply linearHomComplex_tensor_hom_ext
  intro p q j h z₁ z₂
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ← Category.assoc]
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  rw [ι_linearHomComplexTensor_tmul, ι_linearHomComplexTensor_tmul,
    linearHomComplexPrecomp_f_apply, linearHomComplexPrecomp_f_apply,
    linearHomComplexPrecomp_f_apply]
  exact Cochain.ofHom_comp_tensor_ofHom_comp f₁ f₂ z₁ z₂ h

variable (X₁ Y₁ X₂ Y₂)

/-- The comparison `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨` between the tensor product of the dual complexes
`A∨ = Hom(A, R[0])` and the dual of a tensor product, in the order in which the pairing
`(g ⊗ f)(a ⊗ b) = f(a) g(b)` evaluates the inner factors first and carries no sign
(`CochainComplex.HomComplex.Cochain.ιTensorObj_dualDistrib_v`). This is the reverse of the order
of the factors in `TensorProduct.dualDistrib`. It is the Koszul braiding
followed by `TauCeti.linearHomComplexTensor` and the unitor `R[0] ⊗ R[0] ≅ R[0]`, so it is a
morphism of complexes for the dual differential `d f = (-1)^(|f| + 1) f ∘ d`. -/
noncomputable def linearHomComplexDualDistrib (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplex R B (𝟙_ _) ⊗ linearHomComplex R A (𝟙_ _) ⟶
      linearHomComplex R (A ⊗ B) (𝟙_ _) :=
  (HomologicalComplex.tensorBraiding _ _).hom ≫ linearHomComplexTensor R A (𝟙_ _) B (𝟙_ _) ≫
    linearHomComplexPostcomp R (A ⊗ B) (λ_ (𝟙_ _)).hom

/-- `TauCeti.linearHomComplexDualDistrib` is the Koszul braiding followed by
`TauCeti.linearHomComplexTensor` and postcomposition with the unitor `R[0] ⊗ R[0] ≅ R[0]`. -/
lemma linearHomComplexDualDistrib_def (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplexDualDistrib R A B =
      (HomologicalComplex.tensorBraiding _ _).hom ≫ linearHomComplexTensor R A (𝟙_ _) B (𝟙_ _) ≫
        linearHomComplexPostcomp R (A ⊗ B) (λ_ (𝟙_ _)).hom :=
  (rfl)

/-- On the bidegree-`(i, j)` summand, `TauCeti.linearHomComplexDualDistrib` sends `g ⊗ₜ f` to the
pairing `g.dualDistrib f`. -/
lemma ι_linearHomComplexDualDistrib_tmul (A B : CochainComplex (ModuleCat.{v} R) ℤ) (i j n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) = n)
    (g : ModuleCat.of R (Cochain B (𝟙_ _) i)) (f : ModuleCat.of R (Cochain A (𝟙_ _) j)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom (HomologicalComplex.ιMapBifunctor (linearHomComplex R B (𝟙_ _))
        (linearHomComplex R A (𝟙_ _)) (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ)
          i j n h ≫ (linearHomComplexDualDistrib R A B).f n) (g ⊗ₜ f)) =
      (g.dualDistrib f n h : ModuleCat.of R (Cochain (A ⊗ B) (𝟙_ _) n)) := by
  rw [linearHomComplexDualDistrib_def, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.ιTensorObj_tensorBraiding_hom_f_assoc, ComplexShape.σ_up_ℤ,
    Linear.units_smul_comp, Category.assoc,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply, ι_linearHomComplexTensor_tmul,
    linearHomComplexPostcomp_f_apply, Cochain.dualDistrib_def, Units.smul_def]

end TauCeti
