/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Centralizer
public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Prod
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import Mathlib.RingTheory.Flat.Basic

/-!
# The enveloping algebra and center of a product with an abelian factor

Let `Z` be an abelian Lie algebra and `S` any Lie algebra over a commutative ring `R`. The
enveloping algebra of `Z × S` is `Sym(Z) ⊗ U(S)`: compose the product comparison
`U(Z × S) ≃ U(Z) ⊗ U(S)` with the inverse of the abelian comparison `Sym(Z) ≃ U(Z)` on the left
factor. A canonical generator `(z, s)` goes to `z ⊗ 1 + 1 ⊗ s`, and a pure tensor `a ⊗ u` comes
back as the product of the images of `a` and `u` under the two factor inclusions.

When `Z` is a free module, for instance over a field, the center of `U(Z × S)` is then
`Sym(Z) ⊗ Z(U(S))`. The left factor of `Sym(Z) ⊗ U(S)` is commutative, so an element is central
exactly when it commutes with the right factor `1 ⊗ U(S)`, and
`Subalgebra.center_tensorProduct_eq_range_of_free` identifies the center with the range of
`id ⊗ (Z(U(S)) ↪ U(S))`. This map is injective because `Sym(Z)` is free, hence flat. The
resulting algebra equivalence commutes with the actual inclusions. No finite-dimensionality or
characteristic hypothesis is used: in characteristic `p`, the center of `U(S)` contains `p`-th
power elements, and they are retained.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping`: the algebra equivalence
  `U(Z × S) ≃ₐ[R] Sym(Z) ⊗[R] U(S)`.
* `TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv`: for `Z` free, the algebra equivalence
  `Z(U(Z × S)) ≃ₐ[R] Sym(Z) ⊗[R] Z(U(S))`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_ι`: the value `z ⊗ 1 + 1 ⊗ s` on a
  canonical generator `(z, s)`.
* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_symm_tmul`: the inverse on a pure tensor
  is the product of the two factor inclusions.
* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_naturality`: naturality in maps of both
  factors.
* `TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv_inclusion`: the inclusion square
  `(id ⊗ val) ∘ productCenterEquiv = productEnveloping ∘ val`.
* `TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv_symm_tmul`: the inverse on a pure
  tensor `a ⊗ c` with `c` central.
* `TauCeti.UniversalEnvelopingAlgebra.injective_map_id_center_val`: for `Z` free, `id ⊗ val` is
  injective, so the inclusion square determines `productCenterEquiv`.
* `TauCeti.UniversalEnvelopingAlgebra.exists_productCenterEquiv`: the center comparison with its
  inclusion square, as an existence statement.

## References

* J. Dixmier, *Enveloping Algebras*, §1.6, for the enveloping algebra of a product and the
  reductive splitting of its center.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2, no. 2, Proposition 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section Product

variable (R : Type u) [CommRing R]
variable (Z : Type v) [LieRing Z] [LieAlgebra R Z] [IsLieAbelian Z]
variable (S : Type w) [LieRing S] [LieAlgebra R S]

local notation "UZ" => _root_.UniversalEnvelopingAlgebra R Z
local notation "US" => _root_.UniversalEnvelopingAlgebra R S
local notation "UP" => _root_.UniversalEnvelopingAlgebra R (Z × S)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The enveloping algebra of a product with an abelian first factor: the product comparison
`U(Z × S) ≃ U(Z) ⊗ U(S)` followed by the inverse abelian comparison `U(Z) ≃ Sym(Z)` on the left
factor. The order of the factors is fixed. -/
noncomputable def productEnveloping : UP ≃ₐ[R] SymmetricAlgebra R Z ⊗[R] US :=
  (prodEquivTensor R Z S).trans
    (Algebra.TensorProduct.congr (symmetricAlgebraEquiv R Z).symm AlgEquiv.refl)

/-- The definition of `productEnveloping`, for use outside this module. -/
theorem productEnveloping_def :
    productEnveloping R Z S =
      (prodEquivTensor R Z S).trans
        (Algebra.TensorProduct.congr (symmetricAlgebraEquiv R Z).symm AlgEquiv.refl) :=
  (rfl)

/-- `productEnveloping` sends a canonical generator `(z, s)` to `z ⊗ 1 + 1 ⊗ s`. -/
theorem productEnveloping_ι (x : Z × S) :
    productEnveloping R Z S (_root_.UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R Z x.1 ⊗ₜ[R] (1 : US) +
        (1 : SymmetricAlgebra R Z) ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x.2 := by
  rw [productEnveloping, AlgEquiv.trans_apply, prodEquivTensor_ι, map_add,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  exact congrArg₂ (· + ·)
    (congrArg (· ⊗ₜ[R] (1 : US)) (symmetricAlgebraEquiv_symm_ι R Z x.1)) (by simp)

/-- The `simp`-normal form of `productEnveloping_ι`, stated for the canonical generators as `simp`
writes them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem productEnveloping_ι' (x : Z × S) :
    productEnveloping R Z S
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R (Z × S) (TensorAlgebra.ι R x)) =
      SymmetricAlgebra.ι R Z x.1 ⊗ₜ[R] (1 : US) +
        (1 : SymmetricAlgebra R Z) ⊗ₜ[R]
          _root_.UniversalEnvelopingAlgebra.mkAlgHom R S (TensorAlgebra.ι R x.2) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using productEnveloping_ι R Z S x

/-- On the abelian factor inclusion, `productEnveloping` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem productEnveloping_map_inl (a : UZ) :
    productEnveloping R Z S (map R (LieHom.inl R Z S) a) =
      (symmetricAlgebraEquiv R Z).symm a ⊗ₜ[R] (1 : US) := by
  rw [productEnveloping, AlgEquiv.trans_apply, prodEquivTensor_map_inl,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

/-- On the second factor inclusion, `productEnveloping` is one tensored with the element. -/
@[simp]
theorem productEnveloping_map_inr (u : US) :
    productEnveloping R Z S (map R (LieHom.inr R Z S) u) =
      (1 : SymmetricAlgebra R Z) ⊗ₜ[R] u := by
  rw [productEnveloping, AlgEquiv.trans_apply, prodEquivTensor_map_inr,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

/-- The inverse of `productEnveloping` sends a pure tensor `a ⊗ u` to the product of the images
of `a` and `u` under the two factor inclusions. -/
@[simp]
theorem productEnveloping_symm_tmul (a : SymmetricAlgebra R Z) (u : US) :
    (productEnveloping R Z S).symm (a ⊗ₜ[R] u) =
      map R (LieHom.inl R Z S) (symmetricAlgebraEquiv R Z a) * map R (LieHom.inr R Z S) u := by
  rw [productEnveloping, AlgEquiv.symm_trans_apply, Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  simp

/-- `productEnveloping` is natural in maps of both factors: a linear map of the abelian factor
acts on `Sym(Z)` and a Lie map of the second factor acts on `U(S)`. -/
theorem productEnveloping_naturality
    {Z' : Type*} [LieRing Z'] [LieAlgebra R Z'] [IsLieAbelian Z']
    {S' : Type*} [LieRing S'] [LieAlgebra R S']
    (f : Z →ₗ⁅R⁆ Z') (g : S →ₗ⁅R⁆ S') :
    (Algebra.TensorProduct.map (SymmetricAlgebra.map R (f : Z →ₗ[R] Z')) (map R g)).comp
        (productEnveloping R Z S).toAlgHom =
      (productEnveloping R Z' S').toAlgHom.comp (map R (f.prodMap g)) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  rintro ⟨z, s⟩
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [productEnveloping_ι, map_ι, productEnveloping_ι, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  simp only [SymmetricAlgebra.map_apply_ι, map_one, map_ι, LieHom.prodMap_apply,
    LieHom.coe_toLinearMap]

end Product

section Center

variable (K : Type u) [CommRing K]
variable (Z : Type v) [LieRing Z] [LieAlgebra K Z] [IsLieAbelian Z] [Module.Free K Z]
variable (S : Type w) [LieRing S] [LieAlgebra K S]

local notation "US" => _root_.UniversalEnvelopingAlgebra K S
local notation "UP" => _root_.UniversalEnvelopingAlgebra K (Z × S)
local notation "ZS" => Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K S)

/-- The inclusion `Sym(Z) ⊗ Z(U(S)) → Sym(Z) ⊗ U(S)`, `id ⊗ val`. -/
private noncomputable abbrev centerInclusion :
    SymmetricAlgebra K Z ⊗[K] ZS →ₐ[K] SymmetricAlgebra K Z ⊗[K] US :=
  Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K Z)) (ZS).val

omit [IsLieAbelian Z] in
/-- For `Z` free, the inclusion `id ⊗ val : Sym(Z) ⊗ Z(U(S)) → Sym(Z) ⊗ U(S)` is injective, so
`productCenterEquiv` is determined by its inclusion square `productCenterEquiv_inclusion`. -/
theorem injective_map_id_center_val :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K Z)) (ZS).val) :=
  haveI : Module.Flat K (SymmetricAlgebra K Z) := Module.Flat.of_free
  Module.Flat.lTensor_preserves_injective_linearMap (M := SymmetricAlgebra K Z)
    (ZS).val.toLinearMap Subtype.val_injective

private theorem map_center_productEnveloping :
    (Subalgebra.center K UP).map (productEnveloping K Z S : UP →ₐ[K] _) =
      (centerInclusion K Z S).range := by
  rw [Subalgebra.map_center_eq, Subalgebra.center_tensorProduct_eq_range_of_free]

/-- For `Z` free, the center of the enveloping algebra of a product with an abelian first factor
is `Sym(Z) ⊗ Z(U(S))`. This is `productEnveloping` restricted to the centers; see
`productCenterEquiv_inclusion` for the inclusion square. -/
noncomputable def productCenterEquiv :
    Subalgebra.center K UP ≃ₐ[K] SymmetricAlgebra K Z ⊗[K] ZS :=
  ((AlgEquiv.subalgebraMap (productEnveloping K Z S) (Subalgebra.center K UP)).trans
    (Subalgebra.equivOfEq _ _ (map_center_productEnveloping K Z S))).trans
    (AlgEquiv.ofInjective (centerInclusion K Z S) (injective_map_id_center_val K Z S)).symm

/-- The inclusion square of `productCenterEquiv`: followed by `id ⊗ val`, it is
`productEnveloping` on the underlying central element. -/
@[simp]
theorem productCenterEquiv_inclusion (z : Subalgebra.center K UP) :
    Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K Z)) (ZS).val
        (productCenterEquiv K Z S z) =
      productEnveloping K Z S (z : UP) := by
  set e := AlgEquiv.ofInjective (centerInclusion K Z S) (injective_map_id_center_val K Z S)
  set y := Subalgebra.equivOfEq _ _ (map_center_productEnveloping K Z S)
    (AlgEquiv.subalgebraMap (productEnveloping K Z S) (Subalgebra.center K UP) z)
  have h : (e (e.symm y) : SymmetricAlgebra K Z ⊗[K] US) = y := by rw [e.apply_symm_apply]
  rw [AlgEquiv.ofInjective_apply] at h
  exact h

/-- The inverse of `productCenterEquiv` on a pure tensor `a ⊗ c` is the product of the images of
`a` and of the central element `c` under the two factor inclusions. -/
@[simp]
theorem productCenterEquiv_symm_tmul (a : SymmetricAlgebra K Z) (c : ZS) :
    ((productCenterEquiv K Z S).symm (a ⊗ₜ[K] c) : UP) =
      map K (LieHom.inl K Z S) (symmetricAlgebraEquiv K Z a) *
        map K (LieHom.inr K Z S) (c : US) := by
  apply (productEnveloping K Z S).injective
  rw [← productCenterEquiv_inclusion, AlgEquiv.apply_symm_apply, map_mul,
    productEnveloping_map_inl, productEnveloping_map_inr, AlgEquiv.symm_apply_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

/-- **The center of the enveloping algebra of a product with an abelian factor.** For `Z` free,
there is an algebra equivalence `Z(U(Z × S)) ≃ Sym(Z) ⊗ Z(U(S))` which, followed by
`id ⊗ val`, is `productEnveloping` on the underlying central element. -/
theorem exists_productCenterEquiv :
    ∃ e : Subalgebra.center K UP ≃ₐ[K] SymmetricAlgebra K Z ⊗[K] ZS,
      ∀ z, Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K Z)) (ZS).val (e z) =
        productEnveloping K Z S (z : UP) :=
  ⟨productCenterEquiv K Z S, productCenterEquiv_inclusion K Z S⟩

end Center

end TauCeti.UniversalEnvelopingAlgebra
