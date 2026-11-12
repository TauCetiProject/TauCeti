/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Tensor products of local algebras over a local ring

For local homomorphisms `R → A` and `R → B` of local rings, the maximal ideals of `A` and `B`
generate a proper ideal of `A ⊗[R] B`
(`Algebra.TensorProduct.map_maximalIdeal_sup_map_maximalIdeal_ne_top`). Modulo this ideal the
tensor product becomes `κ(A) ⊗[κ(R)] κ(B)`, which is nonzero as a tensor product of nonzero vector
spaces over the field `κ(R)`. Hence `A ⊗[R] B` has a prime lying over the maximal ideals of both
factors, as used when amalgamating valuation rings.
-/

public section

open scoped TensorProduct

open IsLocalRing

namespace Algebra.TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A]
  [IsLocalRing B] [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R A)]
  [IsLocalHom (algebraMap R B)]

/-- For local homomorphisms `R → A` and `R → B` of local rings, the extensions of the maximal
ideals of `A` and `B` to `A ⊗[R] B` together generate a proper ideal. -/
theorem map_maximalIdeal_sup_map_maximalIdeal_ne_top :
    (maximalIdeal A).map (includeLeftRingHom : A →+* A ⊗[R] B) ⊔
      (maximalIdeal B).map (includeRight : B →ₐ[R] A ⊗[R] B).toRingHom ≠ ⊤ := by
  have := nontrivial_of_algebraMap_injective_of_isDomain (ResidueField R) (ResidueField A)
    (ResidueField B) (RingHom.injective _) (RingHom.injective _)
  let χ := mapRingHom (residue R) (residue A) (residue B) (RingHom.ext fun _ ↦ rfl)
    (RingHom.ext fun _ ↦ rfl)
  refine ne_top_of_le_ne_top (RingHom.ker_ne_top χ) (sup_le ?_ ?_) <;>
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp [χ, (residue_eq_zero_iff x).mpr hx]

end Algebra.TensorProduct
