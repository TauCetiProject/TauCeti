/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.Algebra.Lie.UniversalEnveloping.Prod
import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Kostant forms of products of Lie algebras

The Kostant form on the disjoint unions of two specified root and Cartan families in
`L × M` is the tensor product over `ℤ` of the two individual Kostant forms. The equivalence
`TauCeti.UniversalEnvelopingAlgebra.kostantFormProdEquivTensor` restricts the rational
product-to-tensor equivalence, and its inverse sends `a ⊗ b` to the product of the two
canonical inclusions. Thus integral constructions can be assembled componentwise, without
assuming an integral PBW basis first.

No independence, finiteness, commutativity of the Cartan families, or Lie-generation
hypothesis is needed. In particular the construction retains empty families and central
toral directions. Injectivity uses torsion-freeness of subrings of rational algebras, hence
flatness over `ℤ`; surjectivity uses the specified divided-power and binomial generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2, no. 2, Proposition 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The rational comparison is `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor`.
The integral tensor-embedding argument follows `Subring.tensorSquareMap_injective`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
variable {ι κ η θ : Type*} (e : ι → L) (h : κ → L) (f : η → M) (k : θ → M)

local notation "UL" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "UM" => _root_.UniversalEnvelopingAlgebra ℚ M
local notation "UP" => _root_.UniversalEnvelopingAlgebra ℚ (L × M)
local notation "ep" => Sum.elim (fun i => (e i, (0 : M))) (fun j => ((0 : L), f j))
local notation "hp" => Sum.elim (fun i => (h i, (0 : M))) (fun j => ((0 : L), k j))

attribute [local instance] TauCeti.moduleNNRat

-- First include the integral factors in the integer tensor product of the rational algebras.
-- Rational balancing adds no new relations there, and the rational product equivalence
-- then returns to the enveloping algebra of the product.
private noncomputable def productTensorMap :
    kostantForm e h ⊗[ℤ] kostantForm f k →ₐ[ℤ] UP :=
  ((prodEquivTensor ℚ L M).symm.toAlgHom.restrictScalars ℤ).comp
    ((((Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ UL UM).symm.toAlgHom).restrictScalars
      ℤ).comp
      (Algebra.TensorProduct.map (kostantForm e h).subtype.toIntAlgHom
        (kostantForm f k).subtype.toIntAlgHom))

private theorem productTensorMap_tmul (a : kostantForm e h) (b : kostantForm f k) :
    productTensorMap e h f k (a ⊗ₜ[ℤ] b) =
      map ℚ (LieHom.inl ℚ L M) a * map ℚ (LieHom.inr ℚ L M) b := by
  have hrat (a : UL) (b : UM) :
      (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ UL UM).symm (a ⊗ₜ[ℤ] b) =
        a ⊗ₜ[ℚ] b := by
    apply (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ UL UM).injective
    exact (Algebra.TensorProduct.mapOfCompatibleSMul_tmul
      (R := ℤ) (S := ℚ) (T := ℚ) (A := UL) (B := UM) a b).symm
  simp only [productTensorMap, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.map_tmul, RingHom.toIntAlgHom_apply,
    Subring.coe_subtype, hrat, prodEquivTensor_symm_tmul]

private theorem productTensorMap_injective : Function.Injective (productTensorMap e h f k) := by
  let : HasUniqueDiv UL := .of_module_rat UL
  let : HasUniqueDiv UM := .of_module_rat UM
  let : HasUniqueDiv (kostantForm e h) := Function.Injective.hasUniqueDiv
    (kostantForm e h).subtype.toAddMonoidHom (kostantForm e h).subtype_injective
  let : HasUniqueDiv (kostantForm f k) := Function.Injective.hasUniqueDiv
    (kostantForm f k).subtype.toAddMonoidHom (kostantForm f k).subtype_injective
  have hinj := TensorProduct.map_injective_of_flat_flat_of_isDomain (R := ℤ)
    (kostantForm e h).subtype.toIntAlgHom.toLinearMap
    (kostantForm f k).subtype.toIntAlgHom.toLinearMap
    (kostantForm e h).subtype_injective (kostantForm f k).subtype_injective
  have halg : Function.Injective (Algebra.TensorProduct.map (R := ℤ) (S := ℤ)
      (kostantForm e h).subtype.toIntAlgHom (kostantForm f k).subtype.toIntAlgHom) := by
    intro x y hxy
    apply hinj
    rw [← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq] at hxy
    exact hxy
  exact (prodEquivTensor ℚ L M).symm.injective.comp
    ((Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ UL UM).symm.injective.comp halg)

private theorem map_inl_mem_productForm {a : UL} (ha : a ∈ kostantForm e h) :
    map ℚ (LieHom.inl ℚ L M) a ∈ kostantForm ep hp := by
  have hle : kostantForm e h ≤ (kostantForm ep hp).comap (map ℚ (LieHom.inl ℚ L M)).toRingHom := by
    rw [kostantForm_le_iff]
    constructor
    · intro i n
      simpa only [Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Associative.map_dividedPower, map_ι, LieHom.inl_apply, Sum.elim_inl] using
        dividedPower_mem_kostantForm ep hp (Sum.inl i) n
    · intro i n
      simpa only [Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ring.map_choose, map_ι, LieHom.inl_apply, Sum.elim_inl] using
        ringChoose_mem_kostantForm ep hp (Sum.inl i) n
  exact hle ha

private theorem map_inr_mem_productForm {b : UM} (hb : b ∈ kostantForm f k) :
    map ℚ (LieHom.inr ℚ L M) b ∈ kostantForm ep hp := by
  have hle : kostantForm f k ≤ (kostantForm ep hp).comap (map ℚ (LieHom.inr ℚ L M)).toRingHom := by
    rw [kostantForm_le_iff]
    constructor
    · intro i n
      simpa only [Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Associative.map_dividedPower, map_ι, LieHom.inr_apply, Sum.elim_inr] using
        dividedPower_mem_kostantForm ep hp (Sum.inr i) n
    · intro i n
      simpa only [Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ring.map_choose, map_ι, LieHom.inr_apply, Sum.elim_inr] using
        ringChoose_mem_kostantForm ep hp (Sum.inr i) n
  exact hle hb

private theorem range_productTensorMap :
    (productTensorMap e h f k).toRingHom.range = kostantForm ep hp := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productTensorMap_tmul]
        exact Subring.mul_mem _ (map_inl_mem_productForm e h f k a.property)
          (map_inr_mem_productForm e h f k b.property)
    | add a b ha hb => simpa only [map_add] using Subring.add_mem _ ha hb
  · rw [kostantForm_le_iff]
    constructor
    · rintro (i | j) n
      · refine ⟨(⟨_, dividedPower_mem_kostantForm e h i n⟩ : kostantForm e h) ⊗ₜ[ℤ] 1, ?_⟩
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productTensorMap_tmul,
          OneMemClass.coe_one, map_one, mul_one, Associative.map_dividedPower, map_ι,
          LieHom.inl_apply, Sum.elim_inl]
      · refine ⟨(1 : kostantForm e h) ⊗ₜ[ℤ]
          (⟨_, dividedPower_mem_kostantForm f k j n⟩ : kostantForm f k), ?_⟩
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productTensorMap_tmul,
          OneMemClass.coe_one, map_one, one_mul, Associative.map_dividedPower, map_ι,
          LieHom.inr_apply, Sum.elim_inr]
    · rintro (i | j) n
      · refine ⟨(⟨_, ringChoose_mem_kostantForm e h i n⟩ : kostantForm e h) ⊗ₜ[ℤ] 1, ?_⟩
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productTensorMap_tmul,
          OneMemClass.coe_one, map_one, mul_one, Ring.map_choose, map_ι,
          LieHom.inl_apply, Sum.elim_inl]
      · refine ⟨(1 : kostantForm e h) ⊗ₜ[ℤ]
          (⟨_, ringChoose_mem_kostantForm f k j n⟩ : kostantForm f k), ?_⟩
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productTensorMap_tmul,
          OneMemClass.coe_one, map_one, one_mul, Ring.map_choose, map_ι,
          LieHom.inr_apply, Sum.elim_inr]

/-- The Kostant form of a product, on the disjoint root and Cartan families, is the
integer tensor product of the individual Kostant forms. -/
noncomputable def kostantFormProdEquivTensor :
    kostantForm ep hp ≃ₐ[ℤ] kostantForm e h ⊗[ℤ] kostantForm f k :=
  ((AlgEquiv.ofInjective (productTensorMap e h f k)
    (productTensorMap_injective e h f k)).trans
      (RingEquiv.subringCongr (range_productTensorMap e h f k)).toIntAlgEquiv).symm

/-- The inverse integral product equivalence multiplies the two canonical inclusions. -/
@[simp]
theorem coe_kostantFormProdEquivTensor_symm_tmul (a : kostantForm e h) (b : kostantForm f k) :
    ((kostantFormProdEquivTensor e h f k).symm (a ⊗ₜ[ℤ] b) : UP) =
      map ℚ (LieHom.inl ℚ L M) a * map ℚ (LieHom.inr ℚ L M) b := by
  -- Both equivalences onto the range preserve the underlying element; only the
  -- tensor-map computation is left after projecting their subtype values.
  simp only [kostantFormProdEquivTensor, AlgEquiv.symm_symm]
  exact productTensorMap_tmul e h f k a b

/-- An integral product element has pure tensor coordinates precisely when its underlying
rational element is the product of the corresponding canonical factor inclusions. -/
@[simp]
theorem kostantFormProdEquivTensor_apply_eq_tmul_iff
    (u : kostantForm ep hp) (a : kostantForm e h) (b : kostantForm f k) :
    kostantFormProdEquivTensor e h f k u = a ⊗ₜ[ℤ] b ↔
      (u : UP) = map ℚ (LieHom.inl ℚ L M) a * map ℚ (LieHom.inr ℚ L M) b := by
  rw [← coe_kostantFormProdEquivTensor_symm_tmul e h f k a b, Subtype.coe_inj]
  exact (kostantFormProdEquivTensor e h f k).toEquiv.eq_symm_apply.symm

end TauCeti.UniversalEnvelopingAlgebra
