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
generators `i j k`, which vanish when `c₂ = 0`, and shows that an element commuting with the
generators `i j` commutes with the whole image of the induced map. Consequently two quaternion
bases of the same algebra, possibly over different base rings, whose generators commute pairwise
induce algebra maps with commuting images. That is the hypothesis `Algebra.TensorProduct.lift`
needs to assemble the two maps into one out of the tensor product, as
`TauCeti/Algebra/Quaternion/TensorProduct.lean` does for the common slot lemma.

## Main results

* `QuaternionAlgebra.Basis.i_mul_j_add_j_mul_i`, `QuaternionAlgebra.Basis.i_mul_k_add_k_mul_i`,
  and `QuaternionAlgebra.Basis.j_mul_k_add_k_mul_j`: the anticommutators of the generators.
* `QuaternionAlgebra.Basis.commute_liftHom_of_commute`: an element commuting with the generators
  `i` and `j` commutes with the image of `liftHom`.
* `QuaternionAlgebra.Basis.commute_liftHom`: two quaternion bases of one algebra whose generators
  commute pairwise induce commuting algebra maps.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra.Basis

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A] [Algebra R A] [Algebra S A]
  {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}

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

/-- An element commuting with the generators `i` and `j` of a quaternion basis commutes with every
element in the image of the induced algebra map. -/
theorem commute_liftHom_of_commute {a : A} (q : Basis A c₁ c₂ c₃) (hi : Commute a q.i)
    (hj : Commute a q.j) (x : ℍ[R,c₁,c₂,c₃]) : Commute a (q.liftHom x) :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (q.range_liftHom ▸ q.liftHom.mem_range_self x)
    (by simpa using ⟨hi, hj, q.i_mul_j ▸ hi.mul_right hj⟩)

/-- Two quaternion bases of the same algebra whose generators `i` and `j` commute pairwise induce
commuting algebra maps out of the corresponding quaternion algebras. The two bases may be over
different base rings. -/
theorem commute_liftHom (B₁ : Basis A c₁ c₂ c₃) (B₂ : Basis A d₁ d₂ d₃)
    (hii : Commute B₁.i B₂.i) (hij : Commute B₁.i B₂.j) (hji : Commute B₁.j B₂.i)
    (hjj : Commute B₁.j B₂.j) (x : ℍ[R,c₁,c₂,c₃]) (y : ℍ[S,d₁,d₂,d₃]) :
    Commute (B₁.liftHom x) (B₂.liftHom y) :=
  B₂.commute_liftHom_of_commute (B₁.commute_liftHom_of_commute hii.symm hji.symm x).symm
    (B₁.commute_liftHom_of_commute hij.symm hjj.symm x).symm y

end QuaternionAlgebra.Basis
