/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Basic

/-!
# Linearity and root-congruence of the Hall algebra eigenvalue sum

Let `k` be a field and `K` a field containing `k`. In `TauCeti.HallAlgebra`, the eigenvalue sum
`β_η = TauCeti.HallAlgebra.eigenvalueSum K η` sends an endomorphism `g` to the sum of `η` over the
roots of `g.charpoly` in `K`, counted with multiplicity.

This file records the linearity of `η ↦ eigenvalueSum K η` and its root-congruence property:

* `TauCeti.HallAlgebra.eigenvalueSum_zero`, `TauCeti.HallAlgebra.eigenvalueSum_add`,
  `TauCeti.HallAlgebra.eigenvalueSum_smul`, `TauCeti.HallAlgebra.eigenvalueSum_neg`,
  `TauCeti.HallAlgebra.eigenvalueSum_sub`: `η ↦ β_η` is `ℂ`-linear.
* `TauCeti.HallAlgebra.eigenvalueSum_ofEnd_congr`: if `η` and `η'` agree on every root of
  `g.charpoly` in `K`, then `β_η(g) = β_{η'}(g)`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` and
  `src/Lib/LocalGL/Green/TauFunctions.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

namespace TauCeti.HallAlgebra

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The eigenvalue sum of the zero function is `0`. -/
@[simp]
theorem eigenvalueSum_zero : (eigenvalueSum K (0 : K → ℂ) : HallAlgebra k) = 0 :=
  ext_ofEnd fun _ g ↦ by simp [eigenvalueSum_ofEnd]

/-- The eigenvalue sum is additive in `η : K → ℂ`. -/
@[simp]
theorem eigenvalueSum_add (η₁ η₂ : K → ℂ) :
    (eigenvalueSum K (η₁ + η₂) : HallAlgebra k) = eigenvalueSum K η₁ + eigenvalueSum K η₂ :=
  ext_ofEnd fun _ g ↦ by simp [eigenvalueSum_ofEnd]

/-- The eigenvalue sum commutes with complex scalar multiplication in `η : K → ℂ`. -/
@[simp]
theorem eigenvalueSum_smul (c : ℂ) (η : K → ℂ) :
    (eigenvalueSum K (c • η) : HallAlgebra k) = c • eigenvalueSum K η :=
  ext_ofEnd fun _ g ↦ by
    simp only [eigenvalueSum_ofEnd, smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Multiset.sum_map_mul_left]

/-- The eigenvalue sum commutes with negation in `η : K → ℂ`. -/
@[simp]
theorem eigenvalueSum_neg (η : K → ℂ) :
    (eigenvalueSum K (-η) : HallAlgebra k) = -eigenvalueSum K η := by
  have h : (-η : K → ℂ) = (-1 : ℂ) • η := by ext x; simp
  rw [h, eigenvalueSum_smul, neg_one_smul]

/-- The eigenvalue sum commutes with subtraction in `η : K → ℂ`. -/
@[simp]
theorem eigenvalueSum_sub (η₁ η₂ : K → ℂ) :
    (eigenvalueSum K (η₁ - η₂) : HallAlgebra k) = eigenvalueSum K η₁ - eigenvalueSum K η₂ := by
  rw [sub_eq_add_neg, eigenvalueSum_add, eigenvalueSum_neg, sub_eq_add_neg]

/-- If `η₁` and `η₂` agree on every root of `g.charpoly` in `K`, then they have the same
eigenvalue sum at `g`. -/
theorem eigenvalueSum_ofEnd_congr {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {g : Module.End k V} {η₁ η₂ : K → ℂ}
    (h : ∀ x ∈ g.charpoly.aroots K, η₁ x = η₂ x) :
    (eigenvalueSum K η₁ : HallAlgebra k) (SimilarityClass.ofEnd g) =
      eigenvalueSum K η₂ (SimilarityClass.ofEnd g) := by
  rw [eigenvalueSum_ofEnd, eigenvalueSum_ofEnd]
  exact congrArg Multiset.sum (Multiset.map_congr rfl h)

end TauCeti.HallAlgebra
