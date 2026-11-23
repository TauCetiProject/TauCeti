/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Equalizer
public import TauCeti.RingTheory.Localization.Away.MayerVietoris

/-!
# Exact squares of commutative rings

A square of commutative rings

```
R  ⟶ R₁
↓     ↓
R₂ ⟶ L
```

is *exact* when the sequence of `R`-modules
`0 → R → R₁ × R₂ → L → 0`, whose first map is the diagonal `r ↦ (r, r)` and whose last map is
the difference `(a, b) ↦ a - b` of the images in `L`, is exact at all three places.
Exact squares replace a descent datum over `R₁ ⊗[R] R₁` by a single overlap ring `L`: they are
the algebraic setting of the patching theorems of Kedlaya–Liu for finite projective modules and
finite étale algebras, of Zariski gluing along two basic opens, and of Beauville–Laszlo gluing.
Neither `R → R₁` nor `R → R₂` is assumed to be flat.

## Main definitions

* `TauCeti.ExactSquare R R₁ R₂ L`: the square of `R`, `R₁`, `R₂`, `L` is exact.
* `TauCeti.patchingDiagonal R R₁ R₂ M`: the map `m ↦ (1 ⊗ m, 1 ⊗ m)` from an `R`-module `M`
  to its two scalar extensions.
* `TauCeti.patchingDifference R R₁ R₂ L M`: the difference of the two scalar extension maps
  `(R₁ ⊗[R] M) × (R₂ ⊗[R] M) → L ⊗[R] M`.

## Main results

* `TauCeti.exactSquare_self`: the identity square of a ring is exact.
* `TauCeti.exactSquare_of_isCoprime`: for coprime `f g : R`, the Zariski square
  `R → R[1/f]`, `R[1/g] → R[1/(fg)]` is exact. This is the sheaf condition of the structure
  sheaf for the cover of `Spec R` by `D(f)` and `D(g)`.
* `TauCeti.ExactSquare.isScalarTower_right`, `TauCeti.ExactSquare.isScalarTower_left`: an
  `R`-algebra structure on the overlap compatible with one corner is compatible with both.
* `TauCeti.exact_patchingDiagonal_of_exact`, `TauCeti.surjective_of_comp_prodLeft_eq_rTensor`,
  `TauCeti.injective_patchingDiagonal_of_exact_of_flat`: tensoring an exact sequence
  `R → R₁ × R₂ → P → 0`, for any linear map `R₁ × R₂ → P`, with a module. These only use the
  ring-level exactness and surjectivity, so they also apply to Laurent covers.
* `TauCeti.ExactSquare.surjective_patchingDifference`: the patching sequence of any module is
  exact on the right.
* `TauCeti.ExactSquare.exact_patchingDiagonal_patchingDifference`: the patching sequence of any
  module is exact in the middle, again by right exactness of tensor products.
* `TauCeti.ExactSquare.injective_patchingDiagonal`: for a flat module `M` the diagonal is also
  injective, so tensoring an exact square with `M` gives the short exact sequence
  `0 → M → (R₁ ⊗[R] M) × (R₂ ⊗[R] M) → L ⊗[R] M → 0`.
* `TauCeti.ExactSquare.injective_patchingDiagonal_of_flat_overlap`: when the overlap `L` is flat
  over `R`, the diagonal is injective for every module `M`.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 1.3.7 ([arXiv:1301.0792](https://arxiv.org/abs/1301.0792)).
* [The Stacks Project, Section 15.92](https://stacks.math.columbia.edu/tag/0BNI), glueing pairs.
-/

public section

open TensorProduct

namespace TauCeti

section Definition

variable (R R₁ R₂ L : Type*) [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ L] [Algebra R₂ L]

/-- A square of commutative rings `R → R₁, R₂ → L` is *exact* when
`0 → R → R₁ × R₂ → L → 0` is exact, where the first map is `r ↦ (r, r)` and the last map is
`(a, b) ↦ a - b`. Exactness in the middle says that a pair lies in the image of `R` if and only
if its two images in `L` agree; in particular the square commutes. -/
structure ExactSquare : Prop where
  /-- The diagonal map `R → R₁ × R₂` is injective. -/
  injective : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)
  /-- A pair comes from `R` if and only if its two images in `L` agree. -/
  exact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    fun x : R₁ × R₂ ↦ algebraMap R₁ L x.1 - algebraMap R₂ L x.2
  /-- Every element of `L` is a difference of images of elements of `R₁` and `R₂`. -/
  surjective : Function.Surjective fun x : R₁ × R₂ ↦ algebraMap R₁ L x.1 - algebraMap R₂ L x.2

end Definition

variable {R R₁ R₂ L : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ L] [Algebra R₂ L]

/-- An exact square commutes. -/
theorem ExactSquare.algebraMap_eq (h : ExactSquare R R₁ R₂ L) (r : R) :
    algebraMap R₁ L (algebraMap R R₁ r) = algebraMap R₂ L (algebraMap R R₂ r) :=
  sub_eq_zero.mp <| h.exact.apply_apply_eq_zero r

/-- In an exact square, a pair `(a, b)` comes from `R` if and only if `a` and `b` have the same
image in `L`. -/
theorem ExactSquare.exists_algebraMap_eq_iff (h : ExactSquare R R₁ R₂ L) (a : R₁) (b : R₂) :
    (∃ r : R, algebraMap R R₁ r = a ∧ algebraMap R R₂ r = b) ↔
      algebraMap R₁ L a = algebraMap R₂ L b := by
  rw [← sub_eq_zero, h.exact (a, b)]
  simp [Prod.ext_iff]

variable (R) in
/-- The identity square of a commutative ring is exact. -/
theorem exactSquare_self : ExactSquare R R R R where
  injective _ _ h := congr_arg Prod.fst h
  exact x := by
    obtain ⟨a, b⟩ := x
    simp [sub_eq_zero, Prod.ext_iff, eq_comm]
  surjective y := ⟨(y, 0), by simp⟩

section Zariski

variable [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L]

/-- For coprime `f` and `g`, the Zariski square `R → R[1/f], R[1/g] → R[1/(f * g)]` is exact.
This is the sheaf condition of the structure sheaf of `Spec R` for the cover by the basic opens
`D(f)` and `D(g)`. -/
theorem exactSquare_of_isCoprime {f g : R} (hfg : IsCoprime f g) [IsLocalization.Away f R₁]
    [IsLocalization.Away g R₂] [IsLocalization.Away (f * g) L] :
    ExactSquare R R₁ R₂ L where
  injective := IsLocalization.Away.mayerVietoris_injective hfg
  exact := IsLocalization.Away.mayerVietoris_exact hfg
    (fun b ↦ (IsScalarTower.algebraMap_apply R R₁ L b).symm)
    (fun b ↦ (IsScalarTower.algebraMap_apply R R₂ L b).symm)
  surjective := IsLocalization.Away.mayerVietoris_surjective hfg
    (fun b ↦ (IsScalarTower.algebraMap_apply R R₁ L b).symm)
    (fun b ↦ (IsScalarTower.algebraMap_apply R R₂ L b).symm)

end Zariski

section Modules

variable (R R₁ R₂ L M : Type*) [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R L] [Algebra R₁ L] [Algebra R₂ L]
  [IsScalarTower R R₁ L] [IsScalarTower R R₂ L] [AddCommGroup M] [Module R M]

/-- The canonical map `m ↦ (1 ⊗ m, 1 ⊗ m)` from a module to its two scalar extensions. -/
def patchingDiagonal : M →ₗ[R] (R₁ ⊗[R] M) × (R₂ ⊗[R] M) :=
  (TensorProduct.mk R R₁ M 1).prod (TensorProduct.mk R R₂ M 1)

/-- The difference `(x₁, x₂) ↦ x₁ - x₂` of the two scalar extension maps to the overlap
`L ⊗[R] M`, with the first piece taken positively. -/
def patchingDifference : (R₁ ⊗[R] M) × (R₂ ⊗[R] M) →ₗ[R] L ⊗[R] M :=
  ((IsScalarTower.toAlgHom R R₁ L).toLinearMap.rTensor M).coprod
    (-(IsScalarTower.toAlgHom R R₂ L).toLinearMap.rTensor M)

variable {R R₁ R₂ L M}

@[simp]
theorem patchingDiagonal_apply (m : M) :
    patchingDiagonal R R₁ R₂ M m = (1 ⊗ₜ m, 1 ⊗ₜ m) :=
  (rfl)

theorem patchingDifference_apply (x : (R₁ ⊗[R] M) × (R₂ ⊗[R] M)) :
    patchingDifference R R₁ R₂ L M x =
      (IsScalarTower.toAlgHom R R₁ L).toLinearMap.rTensor M x.1 -
        (IsScalarTower.toAlgHom R R₂ L).toLinearMap.rTensor M x.2 :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem patchingDifference_tmul (a : R₁) (b : R₂) (m n : M) :
    patchingDifference R R₁ R₂ L M (a ⊗ₜ m, b ⊗ₜ n) =
      algebraMap R₁ L a ⊗ₜ m - algebraMap R₂ L b ⊗ₜ n :=
  patchingDifference_apply _

@[simp]
theorem patchingDifference_comp_patchingDiagonal :
    patchingDifference R R₁ R₂ L M ∘ₗ patchingDiagonal R R₁ R₂ M = 0 := by
  ext m
  simp

end Modules

section Tensor

/-! ### Tensoring the sequence `R → R₁ × R₂ → P` with a module

The results of this section only use the exactness of `R → R₁ × R₂ → P` and the surjectivity of
its second map, for an arbitrary `R`-linear map `R₁ × R₂ → P`. They apply to exact squares, and
equally to squares whose maps to the overlap are algebra homomorphisms rather than algebra
structures, such as the Laurent covers of affinoid algebras. -/

variable {R R₁ R₂ P : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [Algebra R R₁]
  [Algebra R R₂] [AddCommGroup P] [Module R P] (M : Type*) [AddCommGroup M] [Module R M]

/-- The diagonal map of `M` is the diagonal `R → R₁ × R₂` tensored with `M`. -/
theorem patchingDiagonal_comp_lid :
    patchingDiagonal R R₁ R₂ M ∘ₗ (TensorProduct.lid R M).toLinearMap =
      (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap ∘ₗ
        (Algebra.linearMap R (R₁ × R₂)).rTensor M := by
  refine TensorProduct.ext' fun r m ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    patchingDiagonal_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
    Prod.algebraMap_apply, TensorProduct.prodLeft_tmul]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

/-- The diagonal map of `M` is injective as soon as the diagonal `R → R₁ × R₂` stays injective
after tensoring with `M`. -/
private theorem injective_patchingDiagonal_of_injective_rTensor
    (hM : Function.Injective ((Algebra.linearMap R (R₁ × R₂)).rTensor M)) :
    Function.Injective (patchingDiagonal R R₁ R₂ M) := by
  apply (EquivLike.injective_comp (TensorProduct.lid R M) _).mp
  rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp, patchingDiagonal_comp_lid]
  exact (TensorProduct.prodLeft R R R₁ R₂ M).injective.comp hM

variable {M}

/-- Tensoring with `M` preserves the surjectivity of a map `d : R₁ × R₂ → P`: a map `δ` out of
`(R₁ ⊗[R] M) × (R₂ ⊗[R] M)` that is `d ⊗ M` up to `TensorProduct.prodLeft` is surjective. -/
theorem surjective_of_comp_prodLeft_eq_rTensor {d : R₁ × R₂ →ₗ[R] P}
    {δ : (R₁ ⊗[R] M) × (R₂ ⊗[R] M) →ₗ[R] P ⊗[R] M}
    (hδ : δ ∘ₗ (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap = d.rTensor M)
    (hs : Function.Surjective d) : Function.Surjective δ := by
  apply Function.Surjective.of_comp (g := TensorProduct.prodLeft R R R₁ R₂ M)
  rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp, hδ]
  exact LinearMap.rTensor_surjective M hs

/-- If `R → R₁ × R₂ → P → 0` is exact, then so is its tensor product
`M → (R₁ ⊗[R] M) × (R₂ ⊗[R] M) → P ⊗[R] M → 0` with any module `M`, where the second map `δ`
is `d ⊗ M` up to `TensorProduct.prodLeft`: tensor products are right exact. -/
theorem exact_patchingDiagonal_of_exact {d : R₁ × R₂ →ₗ[R] P}
    {δ : (R₁ ⊗[R] M) × (R₂ ⊗[R] M) →ₗ[R] P ⊗[R] M}
    (hδ : δ ∘ₗ (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap = d.rTensor M)
    (he : Function.Exact (algebraMap R (R₁ × R₂)) d) (hs : Function.Surjective d) :
    Function.Exact (patchingDiagonal R R₁ R₂ M) δ :=
  Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := TensorProduct.lid R M)
    (e₂ := TensorProduct.prodLeft R R R₁ R₂ M) (e₃ := LinearEquiv.refl R (P ⊗[R] M))
    (patchingDiagonal_comp_lid M) (by simpa using hδ) (rTensor_exact M he hs)

variable (M) in
/-- If `0 → R → R₁ × R₂ → P → 0` is exact and `P` is flat over `R`, then the diagonal map of
every module `M` is injective. -/
theorem injective_patchingDiagonal_of_exact_of_flat [Module.Flat R P] {d : R₁ × R₂ →ₗ[R] P}
    (hi : Function.Injective (algebraMap R (R₁ × R₂)))
    (he : Function.Exact (algebraMap R (R₁ × R₂)) d) (hs : Function.Surjective d) :
    Function.Injective (patchingDiagonal R R₁ R₂ M) :=
  injective_patchingDiagonal_of_injective_rTensor M <|
    ((Algebra.linearMap R (R₁ × R₂)).lTensor_inj_iff_rTensor_inj M).mp <|
      LinearMap.lTensor_injective_of_exact_of_flat d hs _ hi he M

end Tensor

namespace ExactSquare

variable {R R₁ R₂ L : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ L] [Algebra R₂ L] (h : ExactSquare R R₁ R₂ L)
include h

/-- In an exact square, an `R`-algebra structure on the overlap that is compatible with `R₁` is
also compatible with `R₂`. For instance `Algebra.compHom L (algebraMap R R₁)` is compatible with
`R₁` by `IsScalarTower.of_algebraMap_eq'`, hence with both corners. -/
theorem isScalarTower_right [Algebra R L] [IsScalarTower R R₁ L] : IsScalarTower R R₂ L :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [← h.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R₁ L]

/-- In an exact square, an `R`-algebra structure on the overlap that is compatible with `R₂` is
also compatible with `R₁`. -/
theorem isScalarTower_left [Algebra R L] [IsScalarTower R R₂ L] : IsScalarTower R R₁ L :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [h.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R₂ L]

omit h in
/-- The diagonal `r ↦ (r, r)` of a square is the algebra map `R → R₁ × R₂`. -/
private theorem coe_algebraMap_prod :
    ⇑(algebraMap R (R₁ × R₂)) = fun r ↦ (algebraMap R R₁ r, algebraMap R R₂ r) :=
  funext Prod.algebraMap_apply

private theorem injective_algebraMap : Function.Injective (algebraMap R (R₁ × R₂)) := by
  rw [coe_algebraMap_prod]
  exact h.injective

variable [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L]

/-- The difference map `R₁ × R₂ → L` of a square, as a linear map. -/
private def squareDifference : R₁ × R₂ →ₗ[R] L :=
  (IsScalarTower.toAlgHom R R₁ L).toLinearMap.coprod (-(IsScalarTower.toAlgHom R R₂ L).toLinearMap)

omit h in
private theorem coe_squareDifference :
    ⇑(squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) =
      fun x ↦ algebraMap R₁ L x.1 - algebraMap R₂ L x.2 :=
  funext fun x ↦ by simp [squareDifference, sub_eq_add_neg]

private theorem exact_squareDifference :
    Function.Exact (algebraMap R (R₁ × R₂))
      (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) := by
  rw [coe_algebraMap_prod, coe_squareDifference]
  exact h.exact

private theorem surjective_squareDifference :
    Function.Surjective (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) := by
  rw [coe_squareDifference]
  exact h.surjective

variable (M : Type*) [AddCommGroup M] [Module R M]

omit h in
/-- The patching difference of `M` is the difference map of the square tensored with `M`. -/
private theorem patchingDifference_comp_prodLeft :
    patchingDifference R R₁ R₂ L M ∘ₗ (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap =
      (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)).rTensor M := by
  ext x m <;> simp [squareDifference, patchingDifference_apply, neg_tmul]

/-- The patching sequence of every module is exact on the right: tensor products are right
exact. -/
theorem surjective_patchingDifference :
    Function.Surjective (patchingDifference R R₁ R₂ L M) :=
  surjective_of_comp_prodLeft_eq_rTensor (patchingDifference_comp_prodLeft M)
    h.surjective_squareDifference

omit [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L] in
/-- Tensoring an exact square with a flat module gives an injective diagonal map. -/
theorem injective_patchingDiagonal [Module.Flat R M] :
    Function.Injective (patchingDiagonal R R₁ R₂ M) :=
  injective_patchingDiagonal_of_injective_rTensor M <|
    Module.Flat.rTensor_preserves_injective_linearMap _ h.injective_algebraMap

/-- When the overlap `L` of an exact square is flat over `R`, for instance for the Zariski square
`exactSquare_of_isCoprime`, the diagonal map of every module is injective. -/
theorem injective_patchingDiagonal_of_flat_overlap [Module.Flat R L] :
    Function.Injective (patchingDiagonal R R₁ R₂ M) :=
  injective_patchingDiagonal_of_exact_of_flat M h.injective_algebraMap h.exact_squareDifference
    h.surjective_squareDifference

/-- The patching sequence of every module is exact in the middle, by right exactness of tensor
products: a pair of elements of the two scalar extensions comes from `M` if and only if the two
pieces agree in the scalar extension to the overlap. Flatness of `M` or of the overlap is only
needed for injectivity on the left (`ExactSquare.injective_patchingDiagonal`,
`ExactSquare.injective_patchingDiagonal_of_flat_overlap`). -/
theorem exact_patchingDiagonal_patchingDifference :
    Function.Exact (patchingDiagonal R R₁ R₂ M) (patchingDifference R R₁ R₂ L M) :=
  exact_patchingDiagonal_of_exact (patchingDifference_comp_prodLeft M) h.exact_squareDifference
    h.surjective_squareDifference

end ExactSquare

end TauCeti
