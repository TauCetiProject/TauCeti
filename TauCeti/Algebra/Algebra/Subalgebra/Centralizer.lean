/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Central.TensorProduct
import TauCeti.Algebra.Group.Center

/-!
# Centralizers under algebra homomorphisms and isomorphisms

* `AlgEquiv.map_centralizer`: an algebra isomorphism `e : A ≃ₐ[R] B` carries the centralizer of a
  set `s ⊆ A` onto the centralizer of its image `e '' s`. Together with `AlgEquiv.subalgebraMap`,
  this transports centralizers, and in particular their dimensions, between isomorphic algebras such
  as matrices and endomorphisms.
* `Subalgebra.apply_mem_centralizer_range`: every value of a multiplicative homomorphism from a
  commutative magma into an `R`-algebra lies in the subalgebra centralizer of its range.
* `Subalgebra.center_tensorProduct_eq_range_of_free`: for a commutative algebra `A` that is free as
  a module, the center of `A ⊗ B` is the range of `id ⊗ (Z(B) ↪ B)`.
-/

public section

open scoped TensorProduct

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- **Transport of centralizers.** An algebra isomorphism carries the centralizer of a set onto
the centralizer of its image. -/
theorem map_centralizer (e : A ≃ₐ[R] B) (s : Set A) :
    (Subalgebra.centralizer R s).map (e : A →ₐ[R] B) = Subalgebra.centralizer R (e '' s) := by
  ext b
  simp only [Subalgebra.mem_map, Subalgebra.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩ x hx
    simp [← map_mul, ha x hx]
  · intro h
    exact ⟨e.symm b, fun x hx => e.injective (by simpa using h hx), by simp⟩

end AlgEquiv

namespace Subalgebra

/-- If `A` is commutative and free, the center of `A ⊗ B` is `A ⊗ Z(B)`, embedded by
`id ⊗ (Z(B) ↪ B)`. -/
theorem center_tensorProduct_eq_range_of_free (R A B : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [Module.Free R A] :
    Subalgebra.center R (A ⊗[R] B) =
      (Algebra.TensorProduct.map (AlgHom.id R A) (Subalgebra.center R B).val).range := by
  apply le_antisymm
  · rw [← centralizer_range_includeRight_eq_center_tensorProduct, ← centralizer_univ]
    exact centralizer_le R _ _ (Set.subset_univ _)
  · rw [Algebra.TensorProduct.map_range, AlgHom.range_comp, AlgHom.range_comp, Algebra.range_id,
      range_val, ← center_eq_top R A]
    exact sup_le (Algebra.TensorProduct.includeLeft_map_center_le R A B)
      (Algebra.TensorProduct.includeRight_map_center_le R A B)

/-- Every value of a multiplicative homomorphism from a commutative magma into an `R`-algebra lies
in the subalgebra centralizer of its range. -/
@[simp]
theorem apply_mem_centralizer_range (R : Type*) {A B F : Type*} [CommSemiring R]
    [Semiring B] [Algebra R B] [Mul A] [IsMulCommutative A] [FunLike F A B]
    [MulHomClass F A B] (f : F) (a : A) :
    f a ∈ centralizer R (Set.range f) := by
  rw [← SetLike.mem_coe, coe_centralizer]
  exact Set.apply_mem_centralizer_range f a

end Subalgebra
