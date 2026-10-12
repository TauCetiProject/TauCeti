/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis

/-!
# Quaternion bases: anticommutators and commuting generators

Mathlib's `QuaternionAlgebra.Basis A c₁ c₂ c₃` records elements `i j k` of an `R`-algebra `A`
satisfying the relations of `ℍ[R,c₁,c₂,c₃]`, and `QuaternionAlgebra.Basis.liftHom` is the
algebra map `ℍ[R,c₁,c₂,c₃] →ₐ[R] A` they induce. This file computes the anticommutators of the
generators `i j k`, which vanish when `c₂ = 0`, and shows that two such bases of the same
algebra whose generators commute pairwise induce algebra maps with commuting images. That is the
hypothesis `Algebra.TensorProduct.lift` needs to assemble the two maps into one out of the tensor
product, as `TauCeti/Algebra/Quaternion/TensorProduct.lean` does for the common slot lemma.

## Main results

* `QuaternionAlgebra.Basis.i_mul_j_add_j_mul_i`, `QuaternionAlgebra.Basis.i_mul_k_add_k_mul_i`,
  and `QuaternionAlgebra.Basis.j_mul_k_add_k_mul_j`: the anticommutators of the generators.
* `QuaternionAlgebra.Basis.commute_liftHom`: two quaternion bases of one algebra whose generators
  commute pairwise induce commuting algebra maps.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra.Basis

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {c₁ c₂ c₃ d₁ d₂ d₃ : R}

/-- The anticommutator of the generators `i` and `j` of a quaternion basis. -/
theorem i_mul_j_add_j_mul_i (q : Basis A c₁ c₂ c₃) : q.i * q.j + q.j * q.i = c₂ • q.j := by
  rw [q.i_mul_j, q.j_mul_i, add_sub_cancel]

/-- The anticommutator of the generators `i` and `k` of a quaternion basis. -/
theorem i_mul_k_add_k_mul_i (q : Basis A c₁ c₂ c₃) : q.i * q.k + q.k * q.i = c₂ • q.k := by
  rw [q.i_mul_k, q.k_mul_i, neg_smul, add_neg_cancel_comm]

/-- The anticommutator of the generators `j` and `k` of a quaternion basis. -/
theorem j_mul_k_add_k_mul_j (q : Basis A c₁ c₂ c₃) :
    q.j * q.k + q.k * q.j = (c₂ * c₃) • 1 := by
  rw [q.j_mul_k, q.k_mul_j, sub_add_cancel]

/-- Two quaternion bases of the same algebra whose generators `i` and `j` commute pairwise induce
commuting algebra maps out of the corresponding quaternion algebras. -/
theorem commute_liftHom (B₁ : Basis A c₁ c₂ c₃) (B₂ : Basis A d₁ d₂ d₃)
    (hii : Commute B₁.i B₂.i) (hij : Commute B₁.i B₂.j) (hji : Commute B₁.j B₂.i)
    (hjj : Commute B₁.j B₂.j) (x : ℍ[R,c₁,c₂,c₃]) (y : ℍ[R,d₁,d₂,d₃]) :
    Commute (B₁.liftHom x) (B₂.liftHom y) := by
  have hik : Commute B₁.i B₂.k := B₂.i_mul_j ▸ hii.mul_right hij
  have hjk : Commute B₁.j B₂.k := B₂.i_mul_j ▸ hji.mul_right hjj
  have hi : Commute B₁.i (B₂.liftHom y) := by
    simp only [liftHom_apply, lift]
    exact (((Algebra.commute_algebraMap_right _ _).add_right (hii.smul_right _)).add_right
      (hij.smul_right _)).add_right (hik.smul_right _)
  have hj : Commute B₁.j (B₂.liftHom y) := by
    simp only [liftHom_apply, lift]
    exact (((Algebra.commute_algebraMap_right _ _).add_right (hji.smul_right _)).add_right
      (hjj.smul_right _)).add_right (hjk.smul_right _)
  have hk : Commute B₁.k (B₂.liftHom y) := B₁.i_mul_j ▸ hi.mul_left hj
  simp only [liftHom_apply, lift]
  exact (((Algebra.commute_algebraMap_left _ _).add_left (hi.smul_left _)).add_left
    (hj.smul_left _)).add_left (hk.smul_left _)

end QuaternionAlgebra.Basis
