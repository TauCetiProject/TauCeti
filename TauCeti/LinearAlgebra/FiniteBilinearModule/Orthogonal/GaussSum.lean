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

/-- Restricting to the orthogonal complement of a quadratic-isotropic subgroup leaves the
Gauss sum unchanged, even when the ambient quadratic module is degenerate. -/
@[simp]
theorem gaussSum_restrict_orthogonalComplement (hH : A.IsIsotropic H) :
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).gaussSum = A.gaussSum := by
  classical
  obtain ⟨_⟩ := nonempty_fintype A
  -- Use the subgroup enumeration on the restricted carrier.
  let : Fintype (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)) :=
    inferInstanceAs (Fintype (A.toFiniteBilinearModule.orthogonalComplement H))
  have hq := (A.isIsotropic_def).mp hH
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- The character sum over H detects membership in its orthogonal complement.
  have hinner (a : A) :
      ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing a h) =
        if a ∈ A.toFiniteBilinearModule.orthogonalComplement H then (Nat.card H : ℂ) else 0 := by
    have h := CharacterModule.sum_expCircle (A.toFiniteBilinearModule.pairingRestrict H a)
    simp only [FiniteBilinearModule.pairingRestrict_apply] at h
    rw [h, Nat.card_eq_fintype_card]
    refine if_congr ?_ rfl rfl
    rw [← AddMonoidHom.mem_ker, FiniteBilinearModule.pairingRestrict_ker]
  have hshift (h : H) : ∑ a, expCircle (A.quadratic (a + h)) = A.gaussSum := by
    rw [gaussSum_eq_sum]
    exact Equiv.sum_comp (Equiv.addRight (h : A)) (fun a ↦ expCircle (A.quadratic a))
  -- Average all translates by H, then sum over the surviving subgroup.
  apply mul_left_cancel₀ hcard
  symm
  calc (Nat.card H : ℂ) * A.gaussSum
      = ∑ h : H, ∑ a, expCircle (A.quadratic (a + h)) := by
        simp [hshift, Nat.card_eq_fintype_card]
    _ = ∑ a, expCircle (A.quadratic a) *
          ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing a h) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [← AddChar.map_add_eq_mul, ← polar_eq_pairing, QuadraticMap.polar, hq h h.2]
        congr 1
        abel
    _ = (Nat.card H : ℂ) * (A.restrict
          (A.toFiniteBilinearModule.orthogonalComplement H)).gaussSum := by
        have hs : (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).gaussSum =
            ∑ x : A.toFiniteBilinearModule.orthogonalComplement H,
              expCircle (A.quadratic x) := by
          rw [gaussSum_eq_sum]
          exact Fintype.sum_equiv (Equiv.refl _) _ _
            (fun x ↦ congrArg expCircle (A.restrict_quadratic _ x))
        simp_rw [hinner]
        rw [hs, Finset.mul_sum]
        have ht := Finset.sum_subtype
          (F := inferInstanceAs (Fintype (A.toFiniteBilinearModule.orthogonalComplement H)))
          (p := fun a : A ↦ a ∈ A.toFiniteBilinearModule.orthogonalComplement H)
          (Finset.univ.filter (fun a : A ↦ a ∈ A.toFiniteBilinearModule.orthogonalComplement H))
          (by simp) (fun a : A ↦ (Nat.card H : ℂ) * expCircle (A.quadratic a))
        rw [← ht, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp [mul_comm]

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
