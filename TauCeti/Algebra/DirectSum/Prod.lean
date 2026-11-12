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

* `DirectSum.lequivProd`: the linear equivalence `⨁ᵢ (Mᵢ × Nᵢ) ≃ₗ (⨁ᵢ Mᵢ) × (⨁ᵢ Nᵢ)`.
* `DirectSum.lequivProd_lof`: it sends the summand `(y, z)` at `i` to the pair of summands at `i`.
* `DirectSum.lequivProd_symm_apply`, `DirectSum.lequivProd_symm_lof`: its inverse pairs up the
  summands of two direct sums.
-/

public section

universe uR uι uM uN

namespace DirectSum

variable (R : Type uR) [Semiring R] {ι : Type uι} (M : ι → Type uM) (N : ι → Type uN)
  [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (M i)]
  [∀ i, Module R (N i)]

/-- The direct sum of a family of products of modules is the product of the two direct sums,
`⨁ᵢ (Mᵢ × Nᵢ) ≃ₗ (⨁ᵢ Mᵢ) × (⨁ᵢ Nᵢ)`. -/
def lequivProd : (⨁ i, M i × N i) ≃ₗ[R] (⨁ i, M i) × (⨁ i, N i) :=
  LinearEquiv.ofLinearMap
    ((lmap fun i ↦ LinearMap.fst R (M i) (N i)).prod (lmap fun i ↦ LinearMap.snd R (M i) (N i)))
    ((lmap fun i ↦ LinearMap.inl R (M i) (N i)).coprod (lmap fun i ↦ LinearMap.inr R (M i) (N i)))
    (LinearMap.ext fun _ ↦ Prod.ext (DFinsupp.ext fun _ ↦ by simp)
      (DFinsupp.ext fun _ ↦ by simp))
    (LinearMap.ext fun _ ↦ DFinsupp.ext fun _ ↦ by simp)

variable {R M N}

/-- The first component of `DirectSum.lequivProd x` takes the first component of every summand
of `x`. -/
@[simp]
lemma fst_lequivProd_apply (x : ⨁ i, M i × N i) (i : ι) : (lequivProd R M N x).1 i = (x i).1 := by
  simp [lequivProd]

/-- The second component of `DirectSum.lequivProd x` takes the second component of every summand
of `x`. -/
@[simp]
lemma snd_lequivProd_apply (x : ⨁ i, M i × N i) (i : ι) : (lequivProd R M N x).2 i = (x i).2 := by
  simp [lequivProd]

/-- `DirectSum.lequivProd` sends the summand `(y, z)` at `i` to the pair of summands `y` and `z`
at `i`. -/
@[simp]
lemma lequivProd_lof [DecidableEq ι] (i : ι) (y : M i) (z : N i) :
    lequivProd R M N (lof R ι (fun i ↦ M i × N i) i (y, z)) = (lof R ι M i y, lof R ι N i z) := by
  simp [lequivProd]

/-- The inverse of `DirectSum.lequivProd` pairs up the summands of `x` and `y` at every `i`. -/
@[simp]
lemma lequivProd_symm_apply (x : ⨁ i, M i) (y : ⨁ i, N i) (i : ι) :
    (lequivProd R M N).symm (x, y) i = (x i, y i) := by
  simp [lequivProd]

/-- The inverse of `DirectSum.lequivProd` sends the pair of summands `y` and `z` at `i` to the
summand `(y, z)` at `i`. -/
@[simp]
lemma lequivProd_symm_lof [DecidableEq ι] (i : ι) (y : M i) (z : N i) :
    (lequivProd R M N).symm (lof R ι M i y, lof R ι N i z) =
      lof R ι (fun i ↦ M i × N i) i (y, z) := by
  rw [LinearEquiv.symm_apply_eq, lequivProd_lof]

end DirectSum
