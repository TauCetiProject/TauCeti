/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Pointwise

/-!
# Pointwise multiplication of commuting subalgebras

Mathlib's `Subalgebra.mul_toSubmodule` proves that the underlying submodule of `S ⊔ T` is the
submodule product `S.toSubmodule * T.toSubmodule` when the ambient algebra `A` is commutative. In
noncommutative algebras—such as `H →L[ℂ] H`, where a von Neumann algebra `M` and its commutant
`M.commutant` commute elementwise without `H →L[ℂ] H` being commutative—the same equality holds
whenever every element of `S` commutes with every element of `T`.

## Main results

* `Subalgebra.mul_toSubmodule_of_commute`: if `∀ a ∈ S, ∀ b ∈ T, Commute a b`, then
  `toSubmodule S * toSubmodule T = toSubmodule (S ⊔ T)`.
-/

public section

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- If every element of `S` commutes with every element of `T`, the product of their underlying
submodules equals the underlying submodule of their subalgebra join `S ⊔ T`. This generalizes
`Subalgebra.mul_toSubmodule` from `[CommSemiring A]` to `[Semiring A]`. -/
theorem mul_toSubmodule_of_commute (S T : Subalgebra R A)
    (h : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    toSubmodule S * toSubmodule T = toSubmodule (S ⊔ T) := by
  refine le_antisymm (mul_toSubmodule_le S T) ?_
  have hTS : toSubmodule T * toSubmodule S ≤ toSubmodule S * toSubmodule T :=
    Submodule.mul_le.mpr fun b hb a ha => (h a ha b hb).symm.eq ▸ Submodule.mul_mem_mul ha hb
  have hmul : (toSubmodule S * toSubmodule T) * (toSubmodule S * toSubmodule T) ≤
      toSubmodule S * toSubmodule T :=
    calc
      (toSubmodule S * toSubmodule T) * (toSubmodule S * toSubmodule T)
          = toSubmodule S * (toSubmodule T * toSubmodule S) * toSubmodule T := by
            simp only [mul_assoc]
      _ ≤ toSubmodule S * (toSubmodule S * toSubmodule T) * toSubmodule T := by gcongr
      _ = (toSubmodule S * toSubmodule S) * (toSubmodule T * toSubmodule T) := by
            simp only [mul_assoc]
      _ = toSubmodule S * toSubmodule T := by
            rw [S.isIdempotentElem_toSubmodule.eq, T.isIdempotentElem_toSubmodule.eq]
  intro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  refine Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_)
    (fun _ _ _ _ => Submodule.add_mem _)
    (fun _ _ _ _ hx hy => hmul (Submodule.mul_mem_mul hx hy)) hx
  · rcases hx with hxS | hxT
    · exact mul_one x ▸ Submodule.mul_mem_mul hxS T.one_mem
    · exact one_mul x ▸ Submodule.mul_mem_mul S.one_mem hxT
  · exact one_mul (algebraMap R A r) ▸ Submodule.mul_mem_mul S.one_mem (T.algebraMap_mem r)

end Subalgebra
