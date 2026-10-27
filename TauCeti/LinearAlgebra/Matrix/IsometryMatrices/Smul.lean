/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Matrices preserving a scaled Gram matrix

Let `f : R →+* S` be a surjective ring homomorphism and `c ∈ R` an element whose annihilator is
the kernel of `f`: `c * z = 0` exactly when `f z = 0`. Then `Xᵀ (c • A) X = c • A` says exactly
that the reduction of `X` along `f` preserves the reduction of `A`. So the matrices preserving
`c • A` are the full preimage of the matrices preserving `A.map f`, and there are
`Nat.card (ker f) ^ (k ^ 2)` times as many of them, for `k` the size of the index type.

The case of interest is `R = ℤ/p^{r+k}`, `S = ℤ/pʳ` and `c` the image of a `p`-adic integer of
valuation `k`. This is how the count behind the local density of a quadratic lattice changes when
the lattice is rescaled.

## Main results

* `Matrix.isometryMatrices_smul_eq_comap`: the matrices preserving `c • A` are the preimage of
  the matrices preserving `A.map f`.
* `Matrix.natCard_isometryMatrices_smul`: the count of matrices preserving `c • A`.
-/

public section

namespace Matrix

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- **Matrices preserving a scaled Gram matrix.** If `c * z = 0` exactly when `f z = 0`, then `X`
preserves `c • A` exactly when its reduction along `f` preserves the reduction of `A`. -/
theorem isometryMatrices_smul_eq_comap (f : R →+* S) {c : R} (hc : ∀ z, c * z = 0 ↔ f z = 0)
    (A : Matrix n n R) :
    isometryMatrices (c • A) = (isometryMatrices (A.map f)).comap f.mapMatrix := by
  ext X
  rw [Submonoid.mem_comap, mem_isometryMatrices, mem_isometryMatrices, RingHom.mapMatrix_apply,
    ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← sub_eq_zero, ← smul_sub, ← sub_eq_zero (a := (Xᵀ * A * X).map f),
    ← Matrix.map_sub f (map_sub f)]
  simp only [← Matrix.ext_iff, smul_apply, smul_eq_mul, zero_apply, map_apply, hc]

/-- **Counting matrices preserving a scaled Gram matrix.** Let `f` be surjective and let `c` have
annihilator `ker f`. Then the `Nat.card` of the matrices preserving `c • A` is
`Nat.card (ker f) ^ (k ^ 2)` times that of the matrices preserving `A.map f`, for `k` the size of
the index type: they are the preimage of the latter under reduction, whose fibers are the
matrices with entries in `ker f`. -/
theorem natCard_isometryMatrices_smul (f : R →+* S) (hf : Function.Surjective f) {c : R}
    (hc : ∀ z, c * z = 0 ↔ f z = 0) (A : Matrix n n R) :
    Nat.card (isometryMatrices (c • A)) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n ^ 2) * Nat.card (isometryMatrices (A.map f)) := by
  let φ : Matrix n n R →+ Matrix n n S := (f : R →+ S).mapMatrix
  have hφ : Function.Surjective φ := fun Y ↦ by
    choose g hg using hf
    exact ⟨Y.map g, Matrix.ext fun i j ↦ hg (Y i j)⟩
  -- the kernel of the reduction is the matrices with entries in `ker f`
  have hker : Nat.card φ.ker = Nat.card (RingHom.ker f) ^ (Fintype.card n ^ 2) := by
    have e : φ.ker ≃ (n → n → RingHom.ker f) :=
      { toFun X i j := ⟨X.1 i j, by
          rw [RingHom.mem_ker]
          exact congrFun (congrFun (φ.mem_ker.mp X.2) i) j⟩
        invFun K := ⟨fun i j ↦ K i j, φ.mem_ker.mpr <| Matrix.ext fun i j ↦
          RingHom.mem_ker.mp (K i j).2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.card_eq_fintype_card (α := n),
      sq]
  have hpre : (isometryMatrices (c • A) : Set (Matrix n n R)) =
      φ ⁻¹' (isometryMatrices (A.map f) : Set (Matrix n n S)) := by
    rw [isometryMatrices_smul_eq_comap f hc]
    -- `φ` is `f.mapMatrix` viewed as an additive homomorphism; the two coercions agree
    rfl
  rw [← hker, mul_comm]
  exact (Nat.card_congr (Set.equivOfEq hpre)).trans (φ.natCard_preimage_of_surjective hφ _)

end Matrix
