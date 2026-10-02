/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Metabolic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.ZModStandard
import Mathlib.NumberTheory.SumFourSquares
import TauCeti.LinearAlgebra.QuadraticForm.FourSquares

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
absolute value one, equal to `1` on metabolic modules. It is moreover an eighth root of unity, and
this needs no classification of finite quadratic modules. Write `2#A - 1 = a² + b² + c² + d²` by
Lagrange's four-square theorem. Multiplication by the quaternion `a + bi + cj + dk` is a bijection
of `A⁴`, because composing it with multiplication by the conjugate quaternion is multiplication by
`2#A - 1`, which is `-1` on `A`. By Euler's four-square identity for quadratic maps it carries
`q(x₁) + ⋯ + q(x₄)` to `(2#A - 1)(q(x₁) + ⋯ + q(x₄)) = -(q(x₁) + ⋯ + q(x₄))`, since `2#A` kills
every value of `q`. Reindexing the sum that defines `G(q)⁴` along it gives
`G(q)⁴ = conj (G(q)⁴)`, so `G(q)⁸ = (G(q) · conj G(q))⁴ = #A⁴`.

The exponent of that root of unity is the **Gauss-sum invariant** `sign q ∈ ℤ/8`, defined by

```text
G(q) = √#A · e^{2πi sign(q) / 8},
```

the invariant that Milgram's theorem compares with the signature of an even lattice. It is an
isometry invariant, additive over orthogonal sums, negated by negating `q`, and zero on metabolic
modules; the discriminant form of `A₁` has invariant `1`.

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
* `TauCeti.FiniteQuadraticModule.conj_gaussSum_pow_four` and
  `TauCeti.FiniteQuadraticModule.IsNondegenerate.gaussSum_pow_eight`: `G(q)⁴` is real, and
  `G(q)⁸ = #A⁴` for nondegenerate `q`.
* `TauCeti.FiniteQuadraticModule.gaussSign`: the Gauss-sum invariant `sign q ∈ ℤ/8`, with its
  defining property `TauCeti.FiniteQuadraticModule.IsNondegenerate.gaussSum_eq` and its
  uniqueness `TauCeti.FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq`.
* `TauCeti.FiniteQuadraticModule.gaussSign_prod`, `TauCeti.FiniteQuadraticModule.gaussSign_neg`
  and `TauCeti.FiniteQuadraticModule.gaussSign_eq_zero_of_isMetabolic`: additivity, behaviour under
  negation, and vanishing on metabolic modules.

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

/-! ## The eighth power of the Gauss sum -/

/-- `2#A` kills every value of the quadratic map, because `2 q(x) = b(x, x)` and `#A` kills `x`. -/
private theorem two_mul_natCard_nsmul_quadratic (x : A) :
    (2 * Nat.card A) • A.quadratic x = 0 := by
  rw [mul_nsmul, ← QuadraticMap.polar_self, polar_eq_pairing, ← map_nsmul, card_nsmul_eq_zero',
    map_zero]

/-- Multiplication by a quaternion `a + bi + cj + dk` of norm `2#A - 1` is a bijection of `A⁴`
which negates `q(x₁) + ⋯ + q(x₄)`. Its composite with multiplication by the conjugate quaternion
is multiplication by `2#A - 1`, which is `-1` on `A`. -/
private theorem exists_bijective_sum_quadratic_eq_neg :
    ∃ Φ : (Fin 4 → A) → (Fin 4 → A), Function.Bijective Φ ∧
      ∀ y, ∑ i, A.quadratic (Φ y i) = -∑ i, A.quadratic (y i) := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (2 * Nat.card A - 1)
  have hcard : 1 ≤ 2 * Nat.card A := by have := Nat.card_pos (α := A); omega
  have hN : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 =
      (2 * Nat.card A - 1 : ℕ) := by
    rw [← habcd]
    push_cast
    ring
  have hnegA (x : A) : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • x = -x := by
    rw [hN, natCast_zsmul, eq_neg_iff_add_eq_zero, ← succ_nsmul, Nat.sub_add_cancel hcard,
      mul_nsmul', card_nsmul_eq_zero', nsmul_zero]
  have hnegq (x : A) : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • A.quadratic x =
      -A.quadratic x := by
    rw [hN, natCast_zsmul, eq_neg_iff_add_eq_zero, ← succ_nsmul, Nat.sub_add_cancel hcard,
      two_mul_natCard_nsmul_quadratic]
  let Φ : (Fin 4 → A) → (Fin 4 → A) := fun y ↦
    ![(a : ℤ) • y 0 - (b : ℤ) • y 1 - (c : ℤ) • y 2 - (d : ℤ) • y 3,
      (a : ℤ) • y 1 + (b : ℤ) • y 0 + (c : ℤ) • y 3 - (d : ℤ) • y 2,
      (a : ℤ) • y 2 - (b : ℤ) • y 3 + (c : ℤ) • y 0 + (d : ℤ) • y 1,
      (a : ℤ) • y 3 + (b : ℤ) • y 2 - (c : ℤ) • y 1 + (d : ℤ) • y 0]
  let Ψ : (Fin 4 → A) → (Fin 4 → A) := fun u ↦
    ![(a : ℤ) • u 0 + (b : ℤ) • u 1 + (c : ℤ) • u 2 + (d : ℤ) • u 3,
      (a : ℤ) • u 1 - (b : ℤ) • u 0 - (c : ℤ) • u 3 + (d : ℤ) • u 2,
      (a : ℤ) • u 2 + (b : ℤ) • u 3 - (c : ℤ) • u 0 - (d : ℤ) • u 1,
      (a : ℤ) • u 3 - (b : ℤ) • u 2 + (c : ℤ) • u 1 - (d : ℤ) • u 0]
  have hΨΦ (y : Fin 4 → A) : Ψ (Φ y) = -y := by
    ext i
    rw [Pi.neg_apply, ← hnegA]
    fin_cases i <;> simp [Φ, Ψ] <;> module
  refine ⟨Φ, Finite.injective_iff_bijective.1 fun y y' h ↦
    neg_injective ((hΨΦ y).symm.trans ((congrArg Ψ h).trans (hΨΦ y'))), fun y ↦ ?_⟩
  simp only [Fin.sum_univ_four, Φ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [QuadraticMap.euler_four_squares, smul_add, smul_add, smul_add, hnegq, hnegq, hnegq, hnegq]
  abel

/-- **The fourth power of the Gauss sum is real**, for every finite quadratic module. -/
theorem conj_gaussSum_pow_four : conj (A.gaussSum ^ 4) = A.gaussSum ^ 4 := by
  obtain ⟨_⟩ := nonempty_fintype A
  obtain ⟨Φ, hΦ, hq⟩ := A.exists_bijective_sum_quadratic_eq_neg
  -- Both sides are sums over `A⁴`; reindex the left one along `Φ`.
  rw [gaussSum_eq_sum, map_pow, map_sum, ← Fin.prod_const, ← Fin.prod_const, Fintype.prod_sum,
    Fintype.prod_sum]
  calc ∑ y : Fin 4 → A, ∏ i, conj (expCircle (A.quadratic (y i)))
      = ∑ y : Fin 4 → A, expCircle (∑ i, A.quadratic (Φ y i)) := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp only [hq, Fin.sum_univ_four, Fin.prod_univ_four, neg_add, ← expCircle_neg,
          AddChar.map_add_eq_mul]
    _ = ∑ y : Fin 4 → A, ∏ i, expCircle (A.quadratic (y i)) := by
        rw [hΦ.sum_comp fun u ↦ expCircle (∑ i, A.quadratic (u i))]
        simp only [Fin.sum_univ_four, Fin.prod_univ_four, AddChar.map_add_eq_mul]

variable {A} in
/-- **The eighth power of the Gauss sum of a nondegenerate module is `#A⁴`**, so the normalized
Gauss sum `G(q) / √#A` is an eighth root of unity. -/
theorem IsNondegenerate.gaussSum_pow_eight (hA : A.IsNondegenerate) :
    A.gaussSum ^ 8 = (Nat.card A : ℂ) ^ 4 := by
  rw [← hA.gaussSum_mul_conj, mul_pow, ← map_pow, conj_gaussSum_pow_four, ← pow_two, ← pow_mul]

/-! ## The Gauss-sum invariant -/

/-- `√#A` is a nonzero complex number. -/
private theorem sqrt_natCard_ne_zero : (√(Nat.card A) : ℂ) ≠ 0 :=
  ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 Nat.card_pos))

/-- The generator of `ℤ/8` corresponds to `1/8` in `ℚ/ℤ`. -/
private theorem toRatAddCircle_eight_one :
    ZMod.toRatAddCircle 8 1 = ((1 / 8 : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using ZMod.toRatAddCircle_natCast 8 1

variable {A} in
/-- The normalized Gauss sum of a nondegenerate module is a power of `e^{2πi/8}`. -/
private theorem IsNondegenerate.exists_gaussSum_eq (hA : A.IsNondegenerate) :
    ∃ k : ZMod 8, A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k) := by
  have hpow : (A.gaussSum / √(Nat.card A)) ^ 8 = 1 := by
    rw [div_pow, hA.gaussSum_pow_eight, show 8 = 2 * 4 from rfl, pow_mul, ← ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ofReal_natCast,
      div_self (pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))]
  obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_expCircle 8 (by norm_num)).eq_pow_of_pow_eq_one hpow
  refine ⟨i, ?_⟩
  rw [← nsmul_one (i : ℕ) (A := ZMod 8), map_nsmul, AddChar.map_nsmul_eq_pow,
    toRatAddCircle_eight_one, ← Nat.cast_ofNat (R := ℚ) (n := 8), hi,
    mul_div_cancel₀ _ (sqrt_natCard_ne_zero A)]

open Classical in
/-- **The Gauss-sum invariant** `sign q ∈ ℤ/8` of a finite quadratic module: the class `k` with
`G(q) = √#A · e^{2πi k/8}`. Such a class is always unique (`gaussSign_eq_of_gaussSum_eq`), and it
exists for a nondegenerate module (`IsNondegenerate.gaussSum_eq`). When there is none, which can
only happen for a degenerate module, the value is `0`. -/
noncomputable def gaussSign : ZMod 8 :=
  if h : ∃ k : ZMod 8, A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k) then
    h.choose
  else 0

/-- **The Gauss-sum invariant is determined by the Gauss sum**: if `G(q) = √#A · e^{2πi k/8}`,
then `sign q = k`. No nondegeneracy is needed, since `√#A ≠ 0` and `k ↦ e^{2πi k/8}` is
injective on `ℤ/8`. -/
theorem gaussSign_eq_of_gaussSum_eq {k : ZMod 8}
    (h : A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k)) :
    A.gaussSign = k := by
  have hex : ∃ k : ZMod 8, A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k) :=
    ⟨k, h⟩
  have hspec : A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 A.gaussSign) := by
    rw [gaussSign, dite_eq_left hex]
    exact hex.choose_spec
  refine ZMod.toRatAddCircle_injective 8 ?_
  refine AddChar.injective_iff.2 (fun _ ↦ expCircle_eq_one_iff.1) ?_
  exact mul_left_cancel₀ (sqrt_natCard_ne_zero A) (hspec.symm.trans h)

variable {A} in
/-- **The Gauss sum of a nondegenerate module** is `√#A · e^{2πi sign(q)/8}`. -/
theorem IsNondegenerate.gaussSum_eq (hA : A.IsNondegenerate) :
    A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 A.gaussSign) := by
  obtain ⟨k, hk⟩ := hA.exists_gaussSum_eq
  rwa [gaussSign_eq_of_gaussSum_eq A hk]

variable {A} in
/-- The Gauss-sum invariant is an isometry invariant. -/
theorem Isometry.gaussSign_eq {B : FiniteQuadraticModule} (f : Isometry A B) :
    A.gaussSign = B.gaussSign := by
  simp only [gaussSign, f.gaussSum_eq, Nat.card_congr f.toLinearEquiv.toEquiv]

variable {A} in
/-- **The Gauss-sum invariant is additive** over orthogonal sums of nondegenerate modules. -/
theorem gaussSign_prod {B : FiniteQuadraticModule} (hA : A.IsNondegenerate)
    (hB : B.IsNondegenerate) : (A.prod B).gaussSign = A.gaussSign + B.gaussSign := by
  refine gaussSign_eq_of_gaussSum_eq _ ?_
  rw [gaussSum_prod, hA.gaussSum_eq, hB.gaussSum_eq, map_add, AddChar.map_add_eq_mul, Nat.card_prod,
    Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ofReal_mul]
  ring

/-- Negating the quadratic form negates the Gauss-sum invariant. -/
@[simp]
theorem gaussSign_neg : A.neg.gaussSign = -A.gaussSign := by
  -- `A.neg` has the carrier of `A`, so the two Gauss sums are normalized by the same `√#A`.
  have hcard : Nat.card A.neg = Nat.card A := rfl
  have hconj (k : ZMod 8) :
      conj (√(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k)) =
        √(Nat.card A.neg) * expCircle (ZMod.toRatAddCircle 8 (-k)) := by
    rw [map_mul, conj_ofReal, map_neg, expCircle_neg, hcard]
  by_cases h : ∃ k : ZMod 8, A.gaussSum = √(Nat.card A) * expCircle (ZMod.toRatAddCircle 8 k)
  · obtain ⟨k, hk⟩ := h
    rw [gaussSign_eq_of_gaussSum_eq A hk]
    exact gaussSign_eq_of_gaussSum_eq _ (by rw [gaussSum_neg, hk, hconj])
  · have h' : ¬∃ k : ZMod 8,
        A.neg.gaussSum = √(Nat.card A.neg) * expCircle (ZMod.toRatAddCircle 8 k) := by
      rintro ⟨k, hk⟩
      refine h ⟨-k, ?_⟩
      have hk' := congrArg conj hk
      rw [gaussSum_neg, conj_conj] at hk'
      rw [hk', map_mul, conj_ofReal, ← expCircle_neg, ← map_neg, hcard]
    rw [gaussSign, gaussSign, dite_eq_right h, dite_eq_right h', neg_zero]

variable {A} in
/-- **The Gauss-sum invariant of a nondegenerate metabolic module vanishes.** -/
theorem gaussSign_eq_zero_of_isMetabolic (hA : A.IsNondegenerate) (h : A.IsMetabolic) :
    A.gaussSign = 0 := by
  refine gaussSign_eq_of_gaussSum_eq A ?_
  rw [map_zero, AddChar.map_zero_eq_one, mul_one]
  exact gaussSum_eq_sqrt_natCard_of_isMetabolic hA h

/-- The discriminant form of `A₁`, the quadratic form `q(x) = x² / 4` on `ℤ/2`, has Gauss-sum
invariant `1`, since `1 + i = √2 · e^{2πi/8}`. -/
@[simp]
theorem gaussSign_zmodStandard_two : (zmodStandard 2 even_two).gaussSign = 1 := by
  refine gaussSign_eq_of_gaussSum_eq _ ?_
  rw [gaussSum_zmodStandard_two, toRatAddCircle_eight_one, expCircle_coe, Nat.card_zmod]
  have h : 2 * (π : ℂ) * I * ((1 / 8 : ℚ) : ℂ) = (π / 4 : ℝ) * I := by
    push_cast
    ring
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt zero_le_two, ofReal_ofNat]
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  linear_combination (-(1 + I) / 2) * h2

end TauCeti.FiniteQuadraticModule
