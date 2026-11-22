/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import TauCeti.Algebra.Homology.CochainComplex.SignedDifferential
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.Algebra.Homology.ParityComplex.Basic
import TauCeti.Algebra.Homology.Monoidal.Summand
import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
import TauCeti.CategoryTheory.Monoidal.Preadditive
import TauCeti.Data.ZMod.IntUnitsPower
import Mathlib.Tactic.Ring

/-!
# The super sign convention for tensor products of complexes with independent parity

For complexes whose terms carry a parity independent of their degree
(`TauCeti.ParityComplex`), tensor products use the *super* sign: for `x` of degree `p` and parity
`σ_x` and `y` of degree `r` and parity `σ_y`,

* the differential is `d (x ⊗ y) = d x ⊗ y + (-1)^(σ_x) x ⊗ d y`, and
* the symmetry sends `x ⊗ y` to `(-1)^(σ_x σ_y) y ⊗ x`.

The *native* convention of Mathlib's tensor product of cochain complexes
(`HomologicalComplex.monoidalCategory`) and of the Koszul braiding
(`TauCeti.koszulBraidedCategory`) uses the degrees `p` and `r` instead. For a factor `K` of
independent parity `τ`, so that `σ_x = p + τ`, the super differential on `K ⊗ L` is the native
differential of `K ⊗ L'`, where `L'` is `L` with its differential multiplied by `(-1)^τ`
(`CochainComplex.signedDifferential`). This is `TauCeti.ParityComplex.superTensorObj τ K L`.

* **The conjugation sign.** Multiplying the summand `K^p ⊗ L^r` by `(-1)^(τ r)` is an isomorphism
  from the super tensor product to the native one
  (`TauCeti.ParityComplex.superTensorObjIsoTensorObj`,
  `TauCeti.ParityComplex.ιTensorObj_superTensorObjIsoTensorObj_hom_f`).
* **The super symmetry.** Over braided coefficients, the native Koszul braiding conjugated by
  these signs and multiplied by `(-1)^(τ τ')` is an isomorphism
  `superTensorObj τ K L ≅ superTensorObj τ' L K` for `K` of independent parity `τ` and `L` of
  independent parity `τ'` (`TauCeti.ParityComplex.superBraiding`). On the summand `K^p ⊗ L^r` it
  is the coefficient braiding multiplied by `(-1)^((p + τ) (r + τ'))`, the product of the two
  parities (`TauCeti.ParityComplex.ιTensorObj_superBraiding_hom_f`), and over symmetric
  coefficients it is an involution
  (`TauCeti.ParityComplex.superBraiding_hom_comp_superBraiding_hom`).
* **Complexes with independent parity.** The super tensor product of two complexes with
  independent parity `A` and `B` is the complex with independent parity whose part of independent
  parity `τ` collects the summands `superTensorObj τ₁ (A τ₁) (B τ₂)` with `τ₁ + τ₂ = τ`
  (`TauCeti.ParityComplex.superTensor`). The conjugation signs identify it with the tensor product
  of the parts in Mathlib's monoidal structure on graded objects
  (`TauCeti.ParityComplex.superTensorIsoTensorObj`).

For instance, when `K` has odd independent parity and `L` is concentrated in degree `1`, the
conjugation sign is `-1`; when `K` has even independent parity it is `+1`, and the super and native
conventions agree.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. **20** (2016), 779–1034, Convention A.0.3.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

namespace ParityComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

section Conjugation

/-- The **super tensor product** of a cochain complex `K` of independent parity `τ` with a cochain
complex `L`: the tensor product `K ⊗ L` whose differential on `K^p ⊗ L^r` is
`d ⊗ 1 + (-1)^(p + τ) 1 ⊗ d`, with the sign of the parity `p + τ` of the first factor. It is the
native tensor product of `K` with `L` whose differential is multiplied by `(-1)^τ`; it is an
abbreviation, so that it can be computed as a native tensor product. -/
noncomputable abbrev superTensorObj (τ : ZMod 2) (K L : CochainComplex C ℤ) : CochainComplex C ℤ :=
  K ⊗ L.signedDifferential τ

/-- **The conjugation sign.** Multiplying the summand `K^p ⊗ L^r` by `(-1)^(τ r)` identifies the
super tensor product of `K`, of independent parity `τ`, and `L` with their native tensor
product. -/
noncomputable def superTensorObjIsoTensorObj (τ : ZMod 2) (K L : CochainComplex C ℤ) :
    superTensorObj τ K L ≅ K ⊗ L :=
  whiskerLeftIso K (L.signedDifferentialIso τ)

/-- On the summand `K^p ⊗ L^r`, the conjugation between the super and native tensor products is
multiplication by `(-1)^(τ r)`. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_superTensorObjIsoTensorObj_hom_f (τ : ZMod 2) (K L : CochainComplex C ℤ)
    (p r n : ℤ) (h : p + r = n) :
    HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r n h ≫
        (superTensorObjIsoTensorObj τ K L).hom.f n =
      (((-1 : ℤˣ) ^ (τ * r) : ℤˣ) : ℤ) •
        ((K.X p ◁ (L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r).hom) ≫
          HomologicalComplex.ιTensorObj K L p r n h) := by
  simp [superTensorObjIsoTensorObj]

/-- On the summand `K^p ⊗ L^r`, the inverse conjugation is again multiplication by
`(-1)^(τ r)`. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_superTensorObjIsoTensorObj_inv_f (τ : ZMod 2) (K L : CochainComplex C ℤ)
    (p r n : ℤ) (h : p + r = n) :
    HomologicalComplex.ιTensorObj K L p r n h ≫ (superTensorObjIsoTensorObj τ K L).inv.f n =
      (((-1 : ℤˣ) ^ (τ * r) : ℤˣ) : ℤ) •
        ((K.X p ◁ (L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r).inv) ≫
          HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r n h) := by
  simp [superTensorObjIsoTensorObj, whiskerLeft_zsmul]

end Conjugation

section Differential

universe u

variable {R : Type u} [CommRing R]

/-- **The super differential.** For complexes of modules, the differential of the super tensor
product `superTensorObj τ K L` on the summand `K^p ⊗ L^r` is `d ⊗ 1 + (-1)^(p + τ) 1 ⊗ d`: the
sign of the second term is that of the parity `p + τ` of the first factor, not of its degree. -/
theorem ιTensorObj_superTensorObj_d (τ : ZMod 2) (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {p r n p' r' n' : ℤ} (h : p + r = n) (hp : p + 1 = p') (hr : r + 1 = r') (hn : n + 1 = n') :
    HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r n h ≫
        (superTensorObj τ K L).d n n' =
      (K.d p p' ▷ (L.signedDifferential τ).X r) ≫
          HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p' r n' (by omega) +
        (((-1 : ℤˣ) ^ ((p : ZMod 2) + τ) : ℤˣ) : ℤ) •
          ((K.X p ◁ ((L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r).hom ≫ L.d r r' ≫
              (L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r').inv)) ≫
            HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r' n' (by omega)) := by
  simp only [HomologicalComplex.ιTensorObj_tensor_d' K (L.signedDifferential τ) h hp hr hn,
    CochainComplex.scaleDifferential_d_eq, whiskerLeft_zsmul, Preadditive.zsmul_comp,
    Units.smul_def, smul_smul, ← Units.val_mul, negOnePow_mul_uzpow]

end Differential

section Symmetry

variable [BraidedCategory C]

/-- **The super symmetry.** For `K` of independent parity `τ` and `L` of independent parity `τ'`,
the Koszul braiding of the native tensor products, conjugated by the signs
`TauCeti.ParityComplex.superTensorObjIsoTensorObj` and multiplied by `(-1)^(τ τ')`. On the summand
`K^p ⊗ L^r` it is the coefficient braiding with the sign `(-1)^((p + τ) (r + τ'))` of the two
parities (`TauCeti.ParityComplex.ιTensorObj_superBraiding_hom_f`). -/
noncomputable def superBraiding (τ τ' : ZMod 2) (K L : CochainComplex C ℤ) :
    superTensorObj τ K L ≅ superTensorObj τ' L K where
  hom := (((-1 : ℤˣ) ^ (τ * τ') : ℤˣ) : ℤ) •
    ((superTensorObjIsoTensorObj τ K L).hom ≫ (β_ K L).hom ≫
      (superTensorObjIsoTensorObj τ' L K).inv)
  inv := (((-1 : ℤˣ) ^ (τ * τ') : ℤˣ) : ℤ) •
    ((superTensorObjIsoTensorObj τ' L K).hom ≫ (β_ K L).inv ≫
      (superTensorObjIsoTensorObj τ K L).inv)
  hom_inv_id := by simp [smul_smul]
  inv_hom_id := by simp [smul_smul]

/-- The sign of the super symmetry on the summand `K^p ⊗ L^r` is the product of the two
parities. -/
private theorem uzpow_superBraiding (τ τ' : ZMod 2) (p r : ℤ) :
    (((-1 : ℤˣ) ^ (τ * τ') : ℤˣ) : ℤ) *
        ((((-1 : ℤˣ) ^ (τ * r) : ℤˣ) : ℤ) * ((((p * r).negOnePow : ℤˣ) : ℤ) *
          (((-1 : ℤˣ) ^ (τ' * p) : ℤˣ) : ℤ))) =
      (((-1 : ℤˣ) ^ ((p + τ) * (r + τ')) : ℤˣ) : ℤ) := by
  rw [← uzpow_intCast_eq_negOnePow, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
    ← uzpow_add, ← uzpow_add, ← uzpow_add]
  congr 2
  push_cast
  ring

/-- **The super sign of the symmetry.** On the summand `K^p ⊗ L^r`, the super symmetry is the
coefficient braiding of `K^p` and `L^r`, multiplied by `(-1)^((p + τ) (r + τ'))`, the product of
the parities of the two factors. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_superBraiding_hom_f (τ τ' : ZMod 2) (K L : CochainComplex C ℤ)
    (p r n : ℤ) (h : p + r = n) :
    HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r n h ≫
        (superBraiding τ τ' K L).hom.f n =
      (((-1 : ℤˣ) ^ ((p + τ) * (r + τ')) : ℤˣ) : ℤ) •
        ((K.X p ◁ (L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r).hom) ≫
          (β_ (K.X p) (L.X r)).hom ≫
          (L.X r ◁ (K.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ') p).inv) ≫
          HomologicalComplex.ιTensorObj L (K.signedDifferential τ') r p n (by omega)) := by
  simp only [superBraiding, braiding_eq_koszulBraiding, ι_koszulBraiding_hom_assoc,
    koszulBraidingSummand_def,
    ιTensorObj_superTensorObjIsoTensorObj_hom_f_assoc,
    ιTensorObj_superTensorObjIsoTensorObj_inv_f, HomologicalComplex.zsmul_f_apply,
    HomologicalComplex.comp_f, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    Units.smul_def, smul_smul, uzpow_superBraiding]

/-- On the summand `L^r ⊗ K^p`, the inverse of the super symmetry is the inverse coefficient
braiding of `K^p` and `L^r`, multiplied by the same sign `(-1)^((p + τ) (r + τ'))`. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_superBraiding_inv_f (τ τ' : ZMod 2) (K L : CochainComplex C ℤ)
    (r p n : ℤ) (h : r + p = n) :
    HomologicalComplex.ιTensorObj L (K.signedDifferential τ') r p n h ≫
        (superBraiding τ τ' K L).inv.f n =
      (((-1 : ℤˣ) ^ ((p + τ) * (r + τ')) : ℤˣ) : ℤ) •
        ((L.X r ◁ (K.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ') p).hom) ≫
          (β_ (K.X p) (L.X r)).inv ≫
          (K.X p ◁ (L.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) r).inv) ≫
          HomologicalComplex.ιTensorObj K (L.signedDifferential τ) p r n (by omega)) := by
  simp only [superBraiding, braiding_eq_koszulBraiding, ι_koszulBraiding_inv_assoc,
    ιTensorObj_superTensorObjIsoTensorObj_hom_f_assoc,
    ιTensorObj_superTensorObjIsoTensorObj_inv_f, HomologicalComplex.zsmul_f_apply,
    HomologicalComplex.comp_f, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    Units.smul_def, smul_smul]
  -- The sign is that of the `hom` summand formula, with its factors in another order.
  rw [← uzpow_superBraiding τ τ' p r, mul_comm r p]
  congr 1
  ring

end Symmetry

section Involution

variable [SymmetricCategory C]

/-- Over symmetric coefficients, the super symmetry is an involution. -/
@[reassoc (attr := simp)]
theorem superBraiding_hom_comp_superBraiding_hom (τ τ' : ZMod 2) (K L : CochainComplex C ℤ) :
    (superBraiding τ τ' K L).hom ≫ (superBraiding τ' τ L K).hom = 𝟙 _ := by
  simp only [superBraiding, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    Iso.inv_hom_id_assoc, SymmetricCategory.symmetry_assoc, Iso.hom_inv_id, smul_smul,
    mul_comm τ' τ, Int.units_coe_mul_self, one_smul]

end Involution

section Parts

/-- The summands of the super tensor product of two complexes with independent parity, graded by
the pair `(τ₁, τ₂)` of independent parities of the factors: the super tensor product of the parts
`A τ₁` and `B τ₂`. The body is exposed so that the summands reduce to super tensor products, as
the statements of `TauCeti.ParityComplex.superTensorSummandsIso_hom_apply` and its inverse need. -/
@[expose]
noncomputable def superTensorSummands (A B : ParityComplex C) :
    GradedObject (ZMod 2 × ZMod 2) (CochainComplex C ℤ) :=
  fun τ ↦ superTensorObj τ.1 (A τ.1) (B τ.2)

omit [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z] in
@[simp]
theorem superTensorSummands_apply (A B : ParityComplex C) (τ : ZMod 2 × ZMod 2) :
    superTensorSummands A B τ = superTensorObj τ.1 (A τ.1) (B τ.2) := (rfl)

/-- The conjugation signs on the summands of the super tensor product. -/
noncomputable def superTensorSummandsIso (A B : ParityComplex C) :
    superTensorSummands A B ≅
      ((GradedObject.mapBifunctor (curriedTensor (CochainComplex C ℤ)) (ZMod 2) (ZMod 2)).obj
        A).obj B :=
  GradedObject.isoMk _ _ fun τ ↦ superTensorObjIsoTensorObj τ.1 (A τ.1) (B τ.2)

/-- On the summand indexed by `τ`, the conjugation signs are the conjugation of
`superTensorObj τ.1 (A τ.1) (B τ.2)`. -/
@[simp]
theorem superTensorSummandsIso_hom_apply (A B : ParityComplex C) (τ : ZMod 2 × ZMod 2) :
    (superTensorSummandsIso A B).hom τ = (superTensorObjIsoTensorObj τ.1 (A τ.1) (B τ.2)).hom :=
  (rfl)

/-- On the summand indexed by `τ`, the inverse conjugation signs are the inverse conjugation of
`superTensorObj τ.1 (A τ.1) (B τ.2)`. -/
@[simp]
theorem superTensorSummandsIso_inv_apply (A B : ParityComplex C) (τ : ZMod 2 × ZMod 2) :
    (superTensorSummandsIso A B).inv τ = (superTensorObjIsoTensorObj τ.1 (A τ.1) (B τ.2)).inv :=
  (rfl)

instance (A B : ParityComplex C) [GradedObject.HasTensor A B] :
    (superTensorSummands A B).HasMap (fun τ ↦ τ.1 + τ.2) :=
  GradedObject.hasMap_of_iso (superTensorSummandsIso A B).symm _

/-- The **super tensor product** of two complexes with independent parity: its part of
independent parity `τ` collects the super tensor products `superTensorObj τ₁ (A τ₁) (B τ₂)` of the
parts with `τ₁ + τ₂ = τ`. -/
noncomputable def superTensor (A B : ParityComplex C) [GradedObject.HasTensor A B] :
    ParityComplex C :=
  (superTensorSummands A B).mapObj (fun τ ↦ τ.1 + τ.2)

/-- The inclusion of the super tensor product of the parts `A τ₁` and `B τ₂` into the part of
independent parity `τ₁ + τ₂` of the super tensor product. -/
noncomputable def ιSuperTensor (A B : ParityComplex C) [GradedObject.HasTensor A B]
    (τ₁ τ₂ τ : ZMod 2) (h : τ₁ + τ₂ = τ) :
    superTensorObj τ₁ (A τ₁) (B τ₂) ⟶ superTensor A B τ :=
  (superTensorSummands A B).ιMapObj (fun τ ↦ τ.1 + τ.2) (τ₁, τ₂) τ h

/-- Two morphisms out of a part of the super tensor product agree when they agree on every
summand. -/
@[ext]
theorem superTensor_ext {A B : ParityComplex C} [GradedObject.HasTensor A B] {τ : ZMod 2}
    {Z : CochainComplex C ℤ} {f g : superTensor A B τ ⟶ Z}
    (hfg : ∀ τ₁ τ₂ (h : τ₁ + τ₂ = τ),
      ιSuperTensor A B τ₁ τ₂ τ h ≫ f = ιSuperTensor A B τ₁ τ₂ τ h ≫ g) :
    f = g :=
  GradedObject.mapObj_ext _ _ _ _ fun x hx ↦ hfg x.1 x.2 hx

/-- **The conjugation sign for complexes with independent parity.** The signs `(-1)^(τ₁ r)` on the
summands identify the super tensor product with the tensor product of graded objects of the parts,
`(A ⊗ B) τ = ∐_{τ₁ + τ₂ = τ} A τ₁ ⊗ B τ₂`. -/
noncomputable def superTensorIsoTensorObj (A B : ParityComplex C) [GradedObject.HasTensor A B] :
    superTensor A B ≅ GradedObject.Monoidal.tensorObj A B :=
  GradedObject.mapIso (superTensorSummandsIso A B) _

/-- On the summand indexed by `(τ₁, τ₂)`, the conjugation of the super tensor product is the
conjugation of `superTensorObj τ₁ (A τ₁) (B τ₂)`. -/
@[reassoc (attr := simp)]
theorem ιSuperTensor_superTensorIsoTensorObj_hom (A B : ParityComplex C)
    [GradedObject.HasTensor A B] (τ₁ τ₂ τ : ZMod 2) (h : τ₁ + τ₂ = τ) :
    ιSuperTensor A B τ₁ τ₂ τ h ≫ (superTensorIsoTensorObj A B).hom τ =
      (superTensorObjIsoTensorObj τ₁ (A τ₁) (B τ₂)).hom ≫
        GradedObject.Monoidal.ιTensorObj A B τ₁ τ₂ τ h :=
  GradedObject.ι_mapMap _ _ _ _ _

/-- On the summand indexed by `(τ₁, τ₂)`, the inverse conjugation of the super tensor product is
the inverse conjugation of `superTensorObj τ₁ (A τ₁) (B τ₂)`. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_superTensorIsoTensorObj_inv (A B : ParityComplex C)
    [GradedObject.HasTensor A B] (τ₁ τ₂ τ : ZMod 2) (h : τ₁ + τ₂ = τ) :
    GradedObject.Monoidal.ιTensorObj A B τ₁ τ₂ τ h ≫ (superTensorIsoTensorObj A B).inv τ =
      (superTensorObjIsoTensorObj τ₁ (A τ₁) (B τ₂)).inv ≫ ιSuperTensor A B τ₁ τ₂ τ h :=
  GradedObject.ι_mapMap _ _ _ _ _

end Parts

end ParityComplex

end TauCeti
