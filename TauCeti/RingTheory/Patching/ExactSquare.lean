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

theorem patchingDifference_comp_patchingDiagonal :
    patchingDifference R R₁ R₂ L M ∘ₗ patchingDiagonal R R₁ R₂ M = 0 := by
  ext m
  simp

/-- The diagonal `R → R₁ × R₂` of a square, as a linear map. -/
private def squareDiagonal : R →ₗ[R] R₁ × R₂ :=
  (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)

/-- The difference `R₁ × R₂ → L` of a square, as a linear map. -/
private def squareDifference : R₁ × R₂ →ₗ[R] L :=
  (IsScalarTower.toAlgHom R R₁ L).toLinearMap ∘ₗ LinearMap.fst R _ _ -
    (IsScalarTower.toAlgHom R R₂ L).toLinearMap ∘ₗ LinearMap.snd R _ _

/-- The patching maps of `M` are the maps of the square tensored with `M`. -/
private theorem patchingDiagonal_comp_lid :
    patchingDiagonal R R₁ R₂ M ∘ₗ (TensorProduct.lid R M).toLinearMap =
      (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap ∘ₗ
        (squareDiagonal (R₁ := R₁) (R₂ := R₂)).rTensor M := by
  refine TensorProduct.ext' fun r m ↦ ?_
  simp [squareDiagonal, Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem patchingDifference_comp_prodLeft :
    patchingDifference R R₁ R₂ L M ∘ₗ (TensorProduct.prodLeft R R R₁ R₂ M).toLinearMap =
      (LinearEquiv.refl R (L ⊗[R] M)).toLinearMap ∘ₗ
        (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)).rTensor M := by
  ext x m <;> simp [squareDifference, patchingDifference_apply]

variable (M) in
/-- The diagonal map of `M` is injective as soon as the diagonal `R → R₁ × R₂` of the square
stays injective after tensoring with `M`. -/
private theorem injective_patchingDiagonal_of_injective_rTensor
    (hM : Function.Injective ((squareDiagonal (R := R) (R₁ := R₁) (R₂ := R₂)).rTensor M)) :
    Function.Injective (patchingDiagonal R R₁ R₂ M) := by
  have := patchingDiagonal_comp_lid (R := R) (R₁ := R₁) (R₂ := R₂) (M := M)
  have hd : ⇑(patchingDiagonal R R₁ R₂ M) = TensorProduct.prodLeft R R R₁ R₂ M ∘
      squareDiagonal.rTensor M ∘ (TensorProduct.lid R M).symm := by
    ext1 x
    simpa using congr($this ((TensorProduct.lid R M).symm x))
  rw [hd]
  exact (TensorProduct.prodLeft R R R₁ R₂ M).injective.comp <|
    hM.comp (TensorProduct.lid R M).symm.injective

end Modules

namespace ExactSquare

variable {R R₁ R₂ L : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R L] [Algebra R₁ L] [Algebra R₂ L]
  [IsScalarTower R R₁ L] [IsScalarTower R R₂ L] (h : ExactSquare R R₁ R₂ L)
  (M : Type*) [AddCommGroup M] [Module R M]
include h

/-- The patching sequence of every module is exact on the right: tensor products are right
exact. -/
theorem surjective_patchingDifference :
    Function.Surjective (patchingDifference R R₁ R₂ L M) := by
  have hs : Function.Surjective (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) :=
    h.surjective
  have := patchingDifference_comp_prodLeft (R := R) (R₁ := R₁) (R₂ := R₂) (L := L) (M := M)
  have hc := (LinearMap.rTensor_surjective M hs)
  intro y
  obtain ⟨x, rfl⟩ := hc y
  exact ⟨TensorProduct.prodLeft R R R₁ R₂ M x, by simpa using congr($this x)⟩

omit [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L] in
/-- Tensoring an exact square with a flat module gives an injective diagonal map. -/
theorem injective_patchingDiagonal [Module.Flat R M] :
    Function.Injective (patchingDiagonal R R₁ R₂ M) :=
  injective_patchingDiagonal_of_injective_rTensor M <|
    Module.Flat.rTensor_preserves_injective_linearMap _ h.injective

/-- When the overlap `L` of an exact square is flat over `R`, for instance for the Zariski square
`exactSquare_of_isCoprime`, the diagonal map of every module is injective. -/
theorem injective_patchingDiagonal_of_flat_overlap [Module.Flat R L] :
    Function.Injective (patchingDiagonal R R₁ R₂ M) :=
  injective_patchingDiagonal_of_injective_rTensor M <|
    (LinearMap.lTensor_inj_iff_rTensor_inj M squareDiagonal).mp <|
      LinearMap.lTensor_injective_of_exact_of_flat
        (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) h.surjective
        (squareDiagonal (R := R) (R₁ := R₁) (R₂ := R₂)) h.injective h.exact M

/-- The patching sequence of every module is exact in the middle, by right exactness of tensor
products: a pair of elements of the two scalar extensions comes from `M` if and only if the two
pieces agree in the scalar extension to the overlap. Flatness of `M` or of the overlap is only
needed for injectivity on the left (`ExactSquare.injective_patchingDiagonal`,
`ExactSquare.injective_patchingDiagonal_of_flat_overlap`). -/
theorem exact_patchingDiagonal_patchingDifference :
    Function.Exact (patchingDiagonal R R₁ R₂ M) (patchingDifference R R₁ R₂ L M) := by
  have he : Function.Exact (squareDiagonal (R := R) (R₁ := R₁) (R₂ := R₂))
      (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) := h.exact
  have hs : Function.Surjective (squareDifference (R := R) (R₁ := R₁) (R₂ := R₂) (L := L)) :=
    h.surjective
  exact (Function.Exact.iff_of_ladder_linearEquiv patchingDiagonal_comp_lid
    patchingDifference_comp_prodLeft).mpr (rTensor_exact M he hs)

end ExactSquare

end TauCeti
