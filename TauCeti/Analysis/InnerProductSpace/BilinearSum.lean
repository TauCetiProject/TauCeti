/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.LinearAlgebra.BilinearMap.Sum

/-!
# Bilinear forms on finite linear combinations and Euclidean inner products

A scalar-valued bilinear form evaluated on the finite linear combinations `∑ k, f i k • φ k` and
`∑ l, g i l • ψ l`, summed over `i`, is the matrix sum `∑ k, ∑ l, B (φ k) (ψ l) * ⟪u k, v l⟫`
for the Euclidean vectors `u k = (conj (f i k))ᵢ` and `v l = (g i l)ᵢ`.

## Main results

* `LinearMap.sum_apply_sum_smul_sum_smul_eq`: the identity.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

/-- Expanding the finite linear combinations `∑ k, f i k • φ k` and `∑ l, g i l • ψ l` in a
bilinear form turns `∑ i, B (∑ k, f i k • φ k) (∑ l, g i l • ψ l)` into the matrix sum
`∑ k, ∑ l, B (φ k) (ψ l) * ⟪u k, v l⟫` for the Euclidean vectors `u k = (conj (f i k))ᵢ` and
`v l = (g i l)ᵢ`. -/
theorem sum_apply_sum_smul_sum_smul_eq {M N : Type*} [AddCommMonoid M] [Module 𝕜 M]
    [AddCommMonoid N] [Module 𝕜 N] {s : Type*} {t : Type*} [Fintype s] [Fintype t]
    (B : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (φ : s → M) (ψ : t → N) (f : ι → s → 𝕜) (g : ι → t → 𝕜) :
    ∑ k : s, ∑ l : t, B (φ k) (ψ l) * ⟪(WithLp.toLp 2 fun i ↦ star (f i k) :
      EuclideanSpace 𝕜 ι), WithLp.toLp 2 fun i ↦ g i l⟫_𝕜 =
    ∑ i, B (∑ k : s, f i k • φ k) (∑ l : t, g i l • ψ l) := by
  simp only [apply_sum_smul_sum_smul, smul_eq_mul, EuclideanSpace.inner_toLp_toLp,
    dotProduct, Pi.star_apply, star_star, Finset.mul_sum]
  calc _ = ∑ k : s, ∑ l : t, ∑ i, B (φ k) (ψ l) * f i k * g i l :=
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦
          Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ k : s, ∑ i, ∑ l : t, B (φ k) (ψ l) * f i k * g i l :=
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k : s, ∑ l : t, B (φ k) (ψ l) * f i k * g i l := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
        Finset.sum_congr rfl fun l _ ↦ by ring

end LinearMap
