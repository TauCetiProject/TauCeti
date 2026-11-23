/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The kernel of the exterior-square action

An endomorphism of a free module with at least three basis vectors acts trivially on its exterior
square exactly when it is scalar multiplication by a scalar whose square is one; in particular it
is then an automorphism. This holds over any commutative ring, including in characteristic two.
Without zero divisors the scalars are `±1`. The rank restriction is essential: in rank two the
exterior square detects only the determinant.

This criterion identifies the kernel of the exterior-square realization of the six-dimensional
orthogonal representation of the four-dimensional special linear group.
-/

public section

open exteriorPower

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace TauCeti

/-- If an automorphism acts trivially on the exterior square, applying it to one factor of
an exterior product is equivalent to applying its inverse to the other factor. -/
theorem exteriorPower_ιMulti_apply_eq_of_map_eq_id {f : M ≃ₗ[R] M}
    (hf : exteriorPower.map 2 f.toLinearMap = LinearMap.id) (x y : M) :
    ιMulti R 2 ![f x, y] = ιMulti R 2 ![x, f.symm y] := by
  have h := LinearMap.congr_fun hf (ιMulti R 2 ![x, f.symm y])
  have hv : f ∘ ![x, f.symm y] = ![f x, y] := by
    ext i
    fin_cases i <;> simp
  simpa only [map_apply_ιMulti, LinearEquiv.coe_coe, hv, LinearMap.id_apply] using h

/-- If an endomorphism acts trivially on the exterior square, it preserves every `2 × 2` minor
cut out by a pair of linear functionals. -/
theorem exteriorPower_pairing_eq_of_map_eq_id {f : M →ₗ[R] M}
    (hf : exteriorPower.map 2 f = LinearMap.id) (φ ψ : Module.Dual R M) (x y : M) :
    φ (f x) * ψ (f y) - ψ (f x) * φ (f y) = φ x * ψ y - ψ x * φ y := by
  have h := congrArg (pairingDual R M 2 (ιMulti R 2 ![φ, ψ]))
    (LinearMap.congr_fun hf (ιMulti R 2 ![x, y]))
  simpa [pairingDual_ιMulti_ιMulti, Matrix.det_fin_two] using h

end TauCeti

/-- With at least three basis vectors, an endomorphism acts trivially on the exterior square
exactly when it is scalar multiplication by a scalar whose square is one. -/
theorem Module.Basis.exteriorPower_map_eq_id_iff (b : Module.Basis ι R M)
    (hι : 3 ≤ ENat.card ι) (f : M →ₗ[R] M) :
    exteriorPower.map 2 f = LinearMap.id ↔ ∃ c : R, c ^ 2 = 1 ∧ f = c • LinearMap.id := by
  classical
  have hthird (i j : ι) : ∃ k : ι, k ≠ i ∧ k ≠ j :=
    ENat.exists_ne_ne_of_three_le hι i j
  constructor
  · intro hf
    -- `b.repr (f (b i)) k` is the `(k, i)` entry of the matrix of `f`, and the `2 × 2` minors
    -- of this matrix are those of the identity matrix.
    have hminor (k l i j : ι) :
        b.repr (f (b i)) k * b.repr (f (b j)) l - b.repr (f (b i)) l * b.repr (f (b j)) k =
          Finsupp.single i 1 k * Finsupp.single j 1 l -
            Finsupp.single i 1 l * Finsupp.single j 1 k := by
      simpa only [Module.Basis.coord_apply, Module.Basis.repr_self] using
        TauCeti.exteriorPower_pairing_eq_of_map_eq_id hf (b.coord k) (b.coord l) (b i) (b j)
    -- The minors on the columns `i` and `j`, for a third index `j`, kill the entry `(k, i)`.
    have hoff (i k : ι) (hik : i ≠ k) : b.repr (f (b i)) k = 0 := by
      obtain ⟨j, hji, hjk⟩ := hthird i k
      have e₁ := hminor k i i j
      have e₂ := hminor k j i j
      have e₃ := hminor i j i j
      simp only [Finsupp.single_apply, hik, hji, hjk, hji.symm, ite_true, ite_false]
        at e₁ e₂ e₃
      linear_combination (-(b.repr (f (b i)) k)) * e₃ + b.repr (f (b i)) i * e₂ -
        b.repr (f (b i)) j * e₁
    -- Hence the product of any two distinct diagonal entries is one.
    have hdiag (i j : ι) (hij : i ≠ j) : b.repr (f (b i)) i * b.repr (f (b j)) j = 1 := by
      simpa [hoff j i hij.symm, hij, hij.symm] using hminor i j i j
    -- A third index then makes all diagonal entries equal.
    obtain ⟨i₀⟩ := (ENat.card_pos_iff_nonempty ι).mp (lt_of_lt_of_le (by norm_num) hι)
    set c := b.repr (f (b i₀)) i₀
    have hsame (i : ι) : b.repr (f (b i)) i = c := by
      obtain ⟨j, hji, hji₀⟩ := hthird i i₀
      linear_combination c * hdiag i j hji.symm - b.repr (f (b i)) i * hdiag i₀ j hji₀.symm
    -- The coordinate identities identify the endomorphism with scalar multiplication.
    refine ⟨c, ?_, b.ext fun i ↦ b.repr.injective ?_⟩
    · obtain ⟨j, hji₀, -⟩ := hthird i₀ i₀
      simpa [pow_two, hsame j] using hdiag i₀ j hji₀.symm
    ext k
    by_cases hik : i = k
    · subst k
      simpa using hsame i
    · simp [hoff i k hik, Ne.symm hik]
  · rintro ⟨c, hc, rfl⟩
    ext v
    simp [AlternatingMap.map_smul_univ, hc]

/-- Over a ring without zero divisors, an endomorphism of a free module with at least three basis
vectors acts trivially on the exterior square exactly when it is `±1`. In characteristic two
these coincide. -/
theorem Module.Basis.exteriorPower_map_eq_id_iff_eq_or_eq_neg_id
    [NoZeroDivisors R] (b : Module.Basis ι R M) (hι : 3 ≤ ENat.card ι) (f : M →ₗ[R] M) :
    exteriorPower.map 2 f = LinearMap.id ↔ f = LinearMap.id ∨ f = -LinearMap.id := by
  rw [b.exteriorPower_map_eq_id_iff hι f]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases sq_eq_one_iff.mp hc with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩
