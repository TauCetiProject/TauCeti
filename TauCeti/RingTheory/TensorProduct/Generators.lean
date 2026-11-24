/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra generators of tensor products

Pure tensors of two algebra-generating families generate their tensor product when each
family contains one. The distinguished unit generators recover both canonical inclusions.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B ι κ : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- If each of two generating families contains one, their pure tensors generate the tensor
product as an algebra. No finiteness or commutativity of the factors is needed. -/
theorem adjoin_range_tmul_eq_top {f : ι → A} {g : κ → B}
    (hf : Algebra.adjoin R (Set.range f) = ⊤)
    (hg : Algebra.adjoin R (Set.range g) = ⊤)
    {i : ι} (hi : f i = 1) {j : κ} (hj : g j = 1) :
    Algebra.adjoin R (Set.range fun s : ι × κ ↦ f s.1 ⊗ₜ[R] g s.2) = ⊤ := by
  let C := Algebra.adjoin R (Set.range fun s : ι × κ ↦ f s.1 ⊗ₜ[R] g s.2)
  have hleft : ∀ a : A, a ⊗ₜ[R] (1 : B) ∈ C := by
    have hmap : (Algebra.adjoin R (Set.range f)).map includeLeft ≤ C := by
      rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact Algebra.subset_adjoin ⟨(k, j), by simp [hj]⟩
    rw [hf, Algebra.map_top] at hmap
    exact fun a ↦ hmap ⟨a, rfl⟩
  have hright : ∀ b : B, (1 : A) ⊗ₜ[R] b ∈ C := by
    have hmap : (Algebra.adjoin R (Set.range g)).map includeRight ≤ C := by
      rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact Algebra.subset_adjoin ⟨(i, k), by simp [hi]⟩
    rw [hg, Algebra.map_top] at hmap
    exact fun b ↦ hmap ⟨b, rfl⟩
  apply top_unique
  rw [← Algebra.TensorProduct.adjoin_tmul_eq_top, Algebra.adjoin_le_iff]
  rintro _ ⟨a, b, rfl⟩
  -- Name the target subalgebra so its multiplication closure applies to the two pure tensors.
  change a ⊗ₜ[R] b ∈ C
  have hmul := C.mul_mem (hleft a) (hright b)
  simpa only [tmul_mul_tmul, mul_one, one_mul] using hmul

end Algebra.TensorProduct
