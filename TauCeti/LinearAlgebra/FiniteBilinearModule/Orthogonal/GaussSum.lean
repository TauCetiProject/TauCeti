/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum

/-!
# Gauss sums under isotropic reduction

For a quadratic-isotropic subgroup `H` of a finite quadratic module `A`, the Gauss sum
satisfies `G(A) = |H| G(H⊥ / H)`. Averaging translations by `H` cancels the contributions
outside `H⊥`, and each class in the quotient has `|H|` representatives. This identity
requires isotropy for the quadratic form itself, rather than just for its polar pairing.
It holds for degenerate modules too.

For nondegenerate `A`, the order identity `|H⊥ / H| |H|² = |A|` shows that the normalized
Gauss sums agree, so isotropic reduction preserves the Gauss-sum invariant. This permits
recursive calculations of Gauss sums of finite quadratic forms by reducing their exponents.

## References

* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public noncomputable section

open scoped Real

namespace TauCeti.FiniteQuadraticModule

variable (A : FiniteQuadraticModule) {H : AddSubgroup A}

/-- **Gauss sums under isotropic reduction.** For a quadratic-isotropic subgroup `H`,
`G(A) = |H| G(H⊥ / H)`. Nondegeneracy is unnecessary. -/
theorem gaussSum_eq_card_mul_gaussSum_orthogonalQuotient (hH : A.IsIsotropic H) :
    A.gaussSum = Nat.card H * (A.orthogonalQuotient H hH).gaussSum := by
  rw [← A.gaussSum_restrict_orthogonalComplement hH]
  have hle : H ≤ A.toFiniteBilinearModule.orthogonalComplement H :=
    (A.toFiniteBilinearModule.isIsotropic_iff_le_orthogonalComplement H).mp
      (hH.toFiniteBilinearModule A)
  have hsub : A.subgroupInOrthogonalComplement H =
      H.addSubgroupOf (A.toFiniteBilinearModule.orthogonalComplement H) := by
    ext x
    rw [A.mem_subgroupInOrthogonalComplement_iff, AddSubgroup.mem_addSubgroupOf]
  have hc : Nat.card (A.subgroupInOrthogonalComplement H) = Nat.card H := by
    rw [hsub]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  have h := gaussSum_eq_card_mul_gaussSum_quotientOfLeQuadraticRadical
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)
  -- The quotient is the same construction; only the order of the copy of H changes.
  convert h using 1
  congr 1
  exact_mod_cast hc.symm

/-- **Isotropic reduction preserves the Gauss-sum invariant** of a nondegenerate finite
quadratic module. -/
@[simp]
theorem gaussSign_orthogonalQuotient (hA : A.IsNondegenerate) (hH : A.IsIsotropic H) :
    (A.orthogonalQuotient H hH).gaussSign = A.gaussSign := by
  let Q := A.orthogonalQuotient H hH
  have hc := IsNondegenerate.card_orthogonalQuotient_mul_card_sq A hA hH
  have hs : (√(Nat.card A) : ℂ) = Nat.card H * √(Nat.card Q) := by
    rw [← hc, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_mul]
    push_cast
    ring
  have hQ := IsNondegenerate.isNondegenerate_orthogonalQuotient A hA hH
  have heq := hQ.gaussSum_eq
  have hG := A.gaussSum_eq_card_mul_gaussSum_orthogonalQuotient hH
  have : A.gaussSign = Q.gaussSign := A.gaussSign_eq_of_gaussSum_eq (by
    rw [hG, heq, hs, mul_assoc])
  exact this.symm

end TauCeti.FiniteQuadraticModule
