/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Metabolic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.ZModStandard

/-!
# Gauss sums of finite quadratic modules

The Gauss sum of a finite quadratic module `(A, q)` is

```text
G(q) = ∑_{a ∈ A} e^{2πi q(a)},
```

the sum of the standard character `TauCeti.expCircle` of `ℚ/ℤ` over the values of `q`. In the
half-norm convention of discriminant forms, `q(x) = B(x, x) / 2` modulo `ℤ`, the factor in the
exponent is `2πi`.

This file proves the properties of `G(q)` that hold for every finite quadratic module, before any
classification is available:

* it is an isometry invariant, it is multiplicative over orthogonal sums, and negating `q`
  conjugates it;
* for nondegenerate `q`, `G(q) · conj G(q) = #A`, so `|G(q)| = √#A`. Expanding the product and
  substituting `a = b + c` turns it into `∑_c e(q(c)) ∑_b e(b(c, b))`, and nondegeneracy kills
  every inner sum except the one at `c = 0`;
* for a Lagrangian subgroup `H` (isotropic for `q` itself, and equal to its orthogonal complement)
  `G(q) = #H`, so a nondegenerate metabolic module has `G(q) = √#A`.

The normalized Gauss sum `G(q) / √#A` of a nondegenerate module is therefore a complex number of
absolute value one, equal to `1` on metabolic modules. That it is an eighth root of unity, whose
exponent is the Gauss-sum invariant `sign q ∈ ℤ/8` that Milgram's theorem compares with the
signature of an even lattice, rests on the classification of nondegenerate finite quadratic
modules and is not proved here.

Quadratic isotropy is needed in the Lagrangian statement, not merely isotropy for the polar
pairing: the discriminant form of `A₁ ⊕ A₁`, the orthogonal sum of two copies of
`q(x) = x² / 4` on `ℤ/2`, has a subgroup equal to its own orthogonal complement on which the
pairing vanishes, while its Gauss sum is `(1 + i)² = 2i ≠ 2`, so it is not metabolic.

## Main declarations

* `TauCeti.FiniteQuadraticModule.gaussSum`: the Gauss sum `∑_{a ∈ A} e^{2πi q(a)}`.
* `TauCeti.FiniteQuadraticModule.gaussSum_prod`: multiplicativity over orthogonal sums.
* `TauCeti.FiniteQuadraticModule.IsNondegenerate.gaussSum_mul_conj` and
  `TauCeti.FiniteQuadraticModule.IsNondegenerate.norm_gaussSum`: `|G(q)|² = #A`.
* `TauCeti.FiniteQuadraticModule.gaussSum_eq_natCard_of_isLagrangian` and
  `TauCeti.FiniteQuadraticModule.gaussSum_eq_sqrt_natCard_of_isMetabolic`: the value on modules
  with a Lagrangian subgroup.
* `TauCeti.FiniteQuadraticModule.gaussSum_zmodStandard_two` and
  `TauCeti.FiniteQuadraticModule.isLagrangian_zmultiples_and_not_isMetabolic_zmodStandard_two_prod`:
  the discriminant forms of `A₁` and of `A₁ ⊕ A₁`.

## References

* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.11.
-/

public section

open Complex ComplexConjugate
open scoped Real

namespace TauCeti.FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- **The Gauss sum** `∑_{a ∈ A} e^{2πi q(a)}` of a finite quadratic module. -/
noncomputable def gaussSum : ℂ :=
  ∑ᶠ a : A, expCircle (A.quadratic a)

/-- The Gauss sum as a finite sum over the elements of the module. -/
theorem gaussSum_eq_sum [Fintype A] : A.gaussSum = ∑ a, expCircle (A.quadratic a) :=
  finsum_eq_sum_of_fintype _

variable {A} in
/-- The Gauss sum is an isometry invariant. -/
theorem Isometry.gaussSum_eq {B : FiniteQuadraticModule} (f : Isometry A B) :
    A.gaussSum = B.gaussSum := by
  obtain ⟨_⟩ := nonempty_fintype A
  obtain ⟨_⟩ := nonempty_fintype B
  rw [gaussSum_eq_sum, gaussSum_eq_sum]
  exact Fintype.sum_equiv f.toLinearEquiv.toEquiv _ _ fun x ↦
    congrArg expCircle (f.map_app x).symm

/-- **The Gauss sum is multiplicative** over orthogonal sums. -/
@[simp]
theorem gaussSum_prod (B : FiniteQuadraticModule) :
    (A.prod B).gaussSum = A.gaussSum * B.gaussSum := by
  obtain ⟨_⟩ := nonempty_fintype A
  obtain ⟨_⟩ := nonempty_fintype B
  rw [gaussSum_eq_sum, gaussSum_eq_sum, gaussSum_eq_sum, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  simp only [QuadraticMap.prod_apply, AddChar.map_add_eq_mul]

/-- Negating the quadratic form conjugates the Gauss sum. -/
@[simp]
theorem gaussSum_neg : A.neg.gaussSum = conj A.gaussSum := by
  obtain ⟨_⟩ := nonempty_fintype A
  rw [gaussSum_eq_sum A, map_sum]
  -- The carrier of `A.neg` is the carrier of `A`.
  let : Fintype A.neg := ‹Fintype A›
  rw [gaussSum_eq_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by
    rw [← expCircle_neg]
    exact congrArg expCircle (A.neg_quadratic a)

/-- Expanding `G(q) · conj G(q)` and substituting `a = b + c` gives
`∑_c e(q(c)) ∑_b e(b(c, b))`, and each inner sum is a character sum. -/
private theorem gaussSum_mul_conj_eq_sum [Fintype A] [DecidableEq (CharacterModule A)] :
    A.gaussSum * conj A.gaussSum =
      ∑ c, expCircle (A.quadratic c) *
        if A.toFiniteBilinearModule.pairing c = 0 then (Fintype.card A : ℂ) else 0 := by
  have hshift : ∀ b, ∑ a, expCircle (A.quadratic a) * conj (expCircle (A.quadratic b)) =
      ∑ c, expCircle (A.quadratic c) * expCircle (A.toFiniteBilinearModule.pairing c b) := by
    intro b
    rw [← Equiv.sum_comp (Equiv.addLeft b)]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have hq : A.quadratic (b + c) =
        A.quadratic b + (A.quadratic c + A.toFiniteBilinearModule.pairing c b) := by
      rw [← polar_eq_pairing, QuadraticMap.polar, add_comm c b]
      abel
    rw [Equiv.coe_addLeft, hq, ← expCircle_neg, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, add_neg_cancel_comm]
  rw [gaussSum_eq_sum, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [hshift]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← Finset.mul_sum, CharacterModule.sum_expCircle]

variable {A} in
/-- **The Gauss sum of a nondegenerate module has squared absolute value `#A`.** -/
theorem IsNondegenerate.gaussSum_mul_conj (hA : A.IsNondegenerate) :
    A.gaussSum * conj A.gaussSum = Nat.card A := by
  classical
  obtain ⟨_⟩ := nonempty_fintype A
  rw [gaussSum_mul_conj_eq_sum, Finset.sum_eq_single 0]
  · simp [Nat.card_eq_fintype_card]
  · intro c _ hc
    have hpc : A.toFiniteBilinearModule.pairing c ≠ 0 := fun h ↦
      hc (FiniteBilinearModule.IsNondegenerate.injective _ hA (h.trans (map_zero _).symm))
    simp [hpc]
  · simp

variable {A} in
/-- **The Gauss sum of a nondegenerate module has absolute value `√#A`.** -/
theorem IsNondegenerate.norm_gaussSum (hA : A.IsNondegenerate) :
    ‖A.gaussSum‖ = √(Nat.card A) := by
  have h := hA.gaussSum_mul_conj
  rw [mul_conj, normSq_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg A.gaussSum)]
  exact congrArg Real.sqrt (by exact_mod_cast h)

variable {A} in
/-- **The Gauss sum of a module with a Lagrangian subgroup `H` is `#H`.** -/
theorem gaussSum_eq_natCard_of_isLagrangian {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    A.gaussSum = Nat.card H := by
  classical
  obtain ⟨_⟩ := nonempty_fintype A
  have hq : ∀ x ∈ H, A.quadratic x = 0 := (isIsotropic_def A).1 (IsLagrangian.isIsotropic A hH)
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hcard ?_
  -- The inner character sum over `H`, with the character `b(a, ·)` restricted to `H`.
  have hinner : ∀ a, ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing a h) =
      if a ∈ H then (Nat.card H : ℂ) else 0 := fun a ↦ by
    have h := CharacterModule.sum_expCircle (A.toFiniteBilinearModule.pairingRestrict H a)
    simp only [FiniteBilinearModule.pairingRestrict_apply] at h
    rw [h, Nat.card_eq_fintype_card]
    refine if_congr ?_ rfl rfl
    rw [← AddMonoidHom.mem_ker, FiniteBilinearModule.pairingRestrict_ker,
      ← IsLagrangian.eq_orthogonalComplement A hH]
  have hshift : ∀ h : H, ∑ a, expCircle (A.quadratic (a + h)) = A.gaussSum := fun h ↦ by
    rw [gaussSum_eq_sum]
    exact Equiv.sum_comp (Equiv.addRight (h : A)) fun a ↦ expCircle (A.quadratic a)
  calc (Nat.card H : ℂ) * A.gaussSum
      = ∑ h : H, ∑ a, expCircle (A.quadratic (a + h)) := by
        simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]
    _ = ∑ a, expCircle (A.quadratic a) *
          ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing a h) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [← AddChar.map_add_eq_mul, ← polar_eq_pairing, QuadraticMap.polar, hq h h.2]
        congr 1
        abel
    _ = ∑ a, if a ∈ H then (Nat.card H : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [hinner]
        split_ifs with ha
        · rw [hq a ha, AddChar.map_zero_eq_one, one_mul]
        · rw [mul_zero]
    _ = (Nat.card H : ℂ) * Nat.card H := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm,
          Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {A} in
/-- **The Gauss sum of a nondegenerate metabolic module is `√#A`**, the value that makes the
Gauss-sum invariant vanish. Nondegeneracy is what makes `#H² = #A` for a Lagrangian `H`. -/
theorem gaussSum_eq_sqrt_natCard_of_isMetabolic (hA : A.IsNondegenerate) (h : A.IsMetabolic) :
    A.gaussSum = √(Nat.card A) := by
  obtain ⟨H, hH⟩ := (isMetabolic_def A).1 h
  rw [gaussSum_eq_natCard_of_isLagrangian hH,
    ← FiniteBilinearModule.IsLagrangian.card_sq A.toFiniteBilinearModule
      (IsLagrangian.toFiniteBilinearModule A hH) hA, Nat.cast_pow,
    Real.sqrt_sq (Nat.cast_nonneg _), ofReal_natCast]

/-! ## The discriminant forms of `A₁` and `A₁ ⊕ A₁` -/

/-- The discriminant form of `A₁`, the quadratic form `q(x) = x² / 4` on `ℤ/2`, has Gauss sum
`1 + i = √2 · e^{2πi/8}`. -/
theorem gaussSum_zmodStandard_two : (zmodStandard 2 even_two).gaussSum = 1 + I := by
  rw [gaussSum_eq_sum, Fintype.sum_eq_add 0 1 zero_ne_one (by decide), zmodStandard_quadratic,
    map_zero, AddChar.map_zero_eq_one, zmodStandard_quadratic, zmodStandardMap_val, ZMod.val_one,
    expCircle_coe]
  have h : 2 * (π : ℂ) * I * ((((1 : ℕ) : ℚ) ^ 2 / (2 * (2 : ℕ)) : ℚ) : ℂ) = π / 2 * I := by
    push_cast
    ring
  rw [h, exp_pi_div_two_mul_I]

/-- **Bilinear Lagrangians do not make a module metabolic.** In the discriminant form of
`A₁ ⊕ A₁`, the orthogonal sum of two copies of `q(x) = x² / 4` on `ℤ/2`, the subgroup generated
by `(1, 1)` is Lagrangian for the polar pairing, but the module is not metabolic: its Gauss sum
is `(1 + i)² = 2i`, not `√4`. The quadratic form takes the value `1/2` on `(1, 1)`. -/
theorem isLagrangian_zmultiples_and_not_isMetabolic_zmodStandard_two_prod :
    ((zmodStandard 2 even_two).prod (zmodStandard 2 even_two)).toFiniteBilinearModule.IsLagrangian
        (AddSubgroup.zmultiples ((1, 1) : ZMod 2 × ZMod 2)) ∧
      ¬ ((zmodStandard 2 even_two).prod (zmodStandard 2 even_two)).IsMetabolic := by
  have hA : ((zmodStandard 2 even_two).prod (zmodStandard 2 even_two)).IsNondegenerate :=
    (isNondegenerate_prod _ _).2
      ⟨isNondegenerate_zmodStandard 2 even_two, isNondegenerate_zmodStandard 2 even_two⟩
  have hcardA : Nat.card (ZMod 2 × ZMod 2) = 4 := by simp
  refine ⟨FiniteBilinearModule.IsIsotropic.isLagrangian_of_card_sq_eq _ ?_ hA ?_, fun h ↦ ?_⟩
  · rw [FiniteBilinearModule.isIsotropic_zmultiples_iff, FiniteBilinearModule.isIsotropicElem_def]
    -- Both factors carry the standard pairing `b(x, y) = xy / 2`, reducibly.
    have h : (FiniteBilinearModule.zmodStandard 2).pairing 1 1 +
        (FiniteBilinearModule.zmodStandard 2).pairing 1 1 = 0 := by
      rw [FiniteBilinearModule.zmodStandard_pairing, ← map_add]
      exact (map_eq_zero_iff _ (ZMod.toRatAddCircle_injective 2)).2 (by decide)
    rw [prod_pairing]
    exact h
  · rw [Nat.card_zmultiples, addOrderOf_eq_prime (p := 2) (by decide) (by decide)]
    exact hcardA.symm
  · have hG := gaussSum_eq_sqrt_natCard_of_isMetabolic hA h
    rw [gaussSum_prod, gaussSum_zmodStandard_two] at hG
    have him := congrArg Complex.im hG
    simp at him

end TauCeti.FiniteQuadraticModule
