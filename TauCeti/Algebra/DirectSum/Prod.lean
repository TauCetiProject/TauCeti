/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct sums of products of modules

The direct sum of a family of products of modules is the product of the two direct sums:
`⨁ᵢ (Mᵢ × Nᵢ) ≃ₗ (⨁ᵢ Mᵢ) × (⨁ᵢ Nᵢ)`, taking the two components summand by summand. A pair of
maps out of `⨁ᵢ Mᵢ` and `⨁ᵢ Nᵢ` thus gives a map out of `⨁ᵢ (Mᵢ × Nᵢ)`, which is how a direct sum
of Mayer–Vietoris sequences, whose middle terms are products, is compared with a single one.

## Main definitions and results

* `DirectSum.prodLinearEquiv`: the linear equivalence `⨁ᵢ (Mᵢ × Nᵢ) ≃ₗ (⨁ᵢ Mᵢ) × (⨁ᵢ Nᵢ)`.
* `DirectSum.prodLinearEquiv_lof`: it sends the summand `x` at `i` to the pair of summands
  `x.1` and `x.2` at `i`.
* `DirectSum.prodLinearEquiv_symm_apply`, `DirectSum.prodLinearEquiv_symm_lof`,
  `DirectSum.prodLinearEquiv_symm_lof_zero`, `DirectSum.prodLinearEquiv_symm_zero_lof`: its
  inverse pairs up the summands of two direct sums.
-/

public section

universe uR uι uM uN

namespace DirectSum

variable (R : Type uR) [Semiring R] {ι : Type uι} (M : ι → Type uM) (N : ι → Type uN)
  [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (M i)]
  [∀ i, Module R (N i)]

/-- The direct sum of a family of products of modules is the product of the two direct sums,
`⨁ᵢ (Mᵢ × Nᵢ) ≃ₗ (⨁ᵢ Mᵢ) × (⨁ᵢ Nᵢ)`. -/
def prodLinearEquiv : (⨁ i, M i × N i) ≃ₗ[R] (⨁ i, M i) × (⨁ i, N i) :=
  LinearEquiv.ofLinearMap
    ((lmap fun i ↦ LinearMap.fst R (M i) (N i)).prod (lmap fun i ↦ LinearMap.snd R (M i) (N i)))
    ((lmap fun i ↦ LinearMap.inl R (M i) (N i)).coprod (lmap fun i ↦ LinearMap.inr R (M i) (N i)))
    (LinearMap.ext fun _ ↦ Prod.ext (DFinsupp.ext fun _ ↦ by simp)
      (DFinsupp.ext fun _ ↦ by simp))
    (LinearMap.ext fun _ ↦ DFinsupp.ext fun _ ↦ by simp)

variable {R M N}

/-- The first component of `DirectSum.prodLinearEquiv x` takes the first component of every
summand of `x`. -/
@[simp]
lemma fst_prodLinearEquiv_apply (x : ⨁ i, M i × N i) (i : ι) :
    (prodLinearEquiv R M N x).1 i = (x i).1 := by
  simp [prodLinearEquiv]

/-- The second component of `DirectSum.prodLinearEquiv x` takes the second component of every
summand of `x`. -/
@[simp]
lemma snd_prodLinearEquiv_apply (x : ⨁ i, M i × N i) (i : ι) :
    (prodLinearEquiv R M N x).2 i = (x i).2 := by
  simp [prodLinearEquiv]

/-- `DirectSum.prodLinearEquiv` sends the summand `x` at `i` to the pair of summands `x.1` and
`x.2` at `i`. -/
@[simp]
lemma prodLinearEquiv_lof [DecidableEq ι] (i : ι) (x : M i × N i) :
    prodLinearEquiv R M N (lof R ι (fun i ↦ M i × N i) i x) =
      (lof R ι M i x.1, lof R ι N i x.2) := by
  simp [prodLinearEquiv]

/-- The inverse of `DirectSum.prodLinearEquiv` pairs up the summands of `x.1` and `x.2` at every
`i`. -/
@[simp]
lemma prodLinearEquiv_symm_apply (x : (⨁ i, M i) × (⨁ i, N i)) (i : ι) :
    (prodLinearEquiv R M N).symm x i = (x.1 i, x.2 i) := by
  simp [prodLinearEquiv]

/-- The inverse of `DirectSum.prodLinearEquiv` sends the pair of summands `y` and `z` at `i` to the
summand `(y, z)` at `i`. -/
@[simp]
lemma prodLinearEquiv_symm_lof [DecidableEq ι] (i : ι) (y : M i) (z : N i) :
    (prodLinearEquiv R M N).symm (lof R ι M i y, lof R ι N i z) =
      lof R ι (fun i ↦ M i × N i) i (y, z) := by
  rw [LinearEquiv.symm_apply_eq, prodLinearEquiv_lof]

/-- The inverse of `DirectSum.prodLinearEquiv` sends the summand `y` at `i`, paired with `0`, to
the summand `(y, 0)` at `i`. -/
@[simp]
lemma prodLinearEquiv_symm_lof_zero [DecidableEq ι] (i : ι) (y : M i) :
    (prodLinearEquiv R M N).symm (lof R ι M i y, 0) = lof R ι (fun i ↦ M i × N i) i (y, 0) := by
  rw [← prodLinearEquiv_symm_lof, map_zero]

/-- The inverse of `DirectSum.prodLinearEquiv` sends `0`, paired with the summand `z` at `i`, to
the summand `(0, z)` at `i`. -/
@[simp]
lemma prodLinearEquiv_symm_zero_lof [DecidableEq ι] (i : ι) (z : N i) :
    (prodLinearEquiv R M N).symm (0, lof R ι N i z) = lof R ι (fun i ↦ M i × N i) i (0, z) := by
  rw [← prodLinearEquiv_symm_lof, map_zero]

end DirectSum
