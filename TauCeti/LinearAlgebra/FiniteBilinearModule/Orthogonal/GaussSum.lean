/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
import TauCeti.GroupTheory.Coset.Fiber

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

The reduction is most often applied to the `n`-torsion `A[n]`, whose orthogonal complement in a
nondegenerate module is `nA`. When `A[n]` is quadratic-isotropic this gives
`|A[n]| G(A) = ∑_y e^{2πi q(n y)}`, with no quotient module to identify: if moreover
`q_A(n y) = q_B(r y)` for a surjective homomorphism `r : A → B` onto a nondegenerate module `B`,
then `A` and `B` have the same Gauss-sum invariant. For Nikulin's cyclic generators on
`ℤ/p^{k+2}`, with `k ≥ 1` when `p = 2`, taking `n = p` and `r` the reduction to `ℤ/p^k` lowers the
exponent by two.

## Main declarations

* `TauCeti.FiniteQuadraticModule.gaussSum_eq_card_mul_gaussSum_orthogonalQuotient`:
  `G(A) = |H| G(H⊥ / H)` for a quadratic-isotropic `H`.
* `TauCeti.FiniteQuadraticModule.gaussSign_orthogonalQuotient`: isotropic reduction preserves the
  Gauss-sum invariant.
* `TauCeti.FiniteQuadraticModule.IsNondegenerate.natCard_ker_zsmul_mul_gaussSum`:
  `|A[n]| G(A) = ∑_y e^{2πi q(n y)}` when `A[n]` is quadratic-isotropic.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_of_quadratic_zsmul_eq`: the Gauss-sum invariant is
  unchanged along multiplication by `n` followed by a reduction.

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

variable {A} in
/-- **Gauss sums under multiplication by `n`.** If the `n`-torsion `A[n]` of a nondegenerate
module is quadratic-isotropic, then `|A[n]| G(A) = ∑_y e^{2πi q(n y)}`. The orthogonal complement
of `A[n]` is `nA`, so `G(A)` is the sum over `nA`, and `y ↦ n y` covers `nA` exactly `|A[n]|`
times. -/
theorem IsNondegenerate.natCard_ker_zsmul_mul_gaussSum [Fintype A] (hA : A.IsNondegenerate)
    (n : ℤ) (hH : A.IsIsotropic (zsmulAddGroupHom (α := A) n).ker) :
    Nat.card (zsmulAddGroupHom (α := A) n).ker * A.gaussSum =
      ∑ y : A, expCircle (A.quadratic (n • y)) := by
  classical
  set f := zsmulAddGroupHom (α := A) n
  let : Fintype (A.restrict f.range) := inferInstanceAs (Fintype f.range)
  have hG : A.gaussSum = ∑ x : f.range, expCircle (A.quadratic x) := by
    rw [← A.gaussSum_restrict_orthogonalComplement hH,
      FiniteBilinearModule.IsNondegenerate.orthogonalComplement_ker_zsmul _ hA n, gaussSum_eq_sum]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ fun x ↦ congrArg expCircle (A.restrict_quadratic _ x)
  have hsum := AddMonoidHom.sum_comp_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    fun x : f.range ↦ expCircle (A.quadratic x)
  rw [AddMonoidHom.ker_rangeRestrict] at hsum
  rw [hG, ← nsmul_eq_mul, ← hsum]
  simp [f]

variable {A} in
/-- **The Gauss-sum invariant along multiplication by `n`.** Let `A` and `B` be nondegenerate,
let the `n`-torsion of `A` be quadratic-isotropic, and let `r : A → B` be a surjective
homomorphism with `q_A(n y) = q_B(r y)`. Then `sign A = sign B`, because both
`|A[n]| G(A)` and `|ker r| G(B)` equal `∑_y e^{2πi q_A(n y)}`.

For Nikulin's cyclic generators on `A = ℤ/p^{k+2}`, with `k ≥ 1` when `p = 2`, taking `n = p` and
`r` the reduction to `B = ℤ/p^k` lowers the exponent by two. -/
theorem gaussSign_eq_of_quadratic_zsmul_eq {B : FiniteQuadraticModule} (hA : A.IsNondegenerate)
    (hB : B.IsNondegenerate) (n : ℤ) (hH : A.IsIsotropic (zsmulAddGroupHom (α := A) n).ker)
    (r : A →+ B) (hr : Function.Surjective r) (hq : ∀ y, A.quadratic (n • y) = B.quadratic (r y)) :
    A.gaussSign = B.gaussSign := by
  obtain ⟨_⟩ := nonempty_fintype A
  obtain ⟨_⟩ := nonempty_fintype B
  have hm : (Nat.card (zsmulAddGroupHom (α := A) n).ker : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h : (Nat.card (zsmulAddGroupHom (α := A) n).ker : ℂ) * A.gaussSum =
      Nat.card r.ker * B.gaussSum := by
    rw [hA.natCard_ker_zsmul_mul_gaussSum n hH, gaussSum_eq_sum, ← nsmul_eq_mul,
      ← AddMonoidHom.sum_comp_of_surjective r hr]
    simp_rw [hq]
  refine gaussSign_eq_of_gaussSum_eq_mul hA hB (c := Nat.card r.ker /
    Nat.card (zsmulAddGroupHom (α := A) n).ker) (by positivity) ?_
  rw [← mul_right_inj' hm, h]
  push_cast
  field_simp

end TauCeti.FiniteQuadraticModule
