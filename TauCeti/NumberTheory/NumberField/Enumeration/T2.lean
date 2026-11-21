/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
import TauCeti.FieldTheory.Minpoly.SumAlgHom
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# The `T₂` norm of a polynomial and of an algebraic integer

The `T₂` norm of a complex polynomial `P` is the sum `∑ ‖α‖ ^ 2` of the squared absolute values
of its complex roots, counted with multiplicity. For an integer polynomial it is computed after
mapping the coefficients to `ℂ`. This is the size measure used to enumerate number fields: a
monic integer polynomial of fixed degree and bounded `T₂` has bounded roots, hence bounded
coefficients, and there are only finitely many such polynomials. Among the defining polynomials of
a number field one chooses a canonical one minimizing `T₂` (PARI's `polredabs`), and Hunter's
theorem bounds `T₂` of a well-chosen algebraic integer in terms of the discriminant.

`T₂` is the sum of squared absolute values, not the power sum `∑ α ^ 2`: for `X ^ 2 + 1` the
former is `2` and the latter is `-2`. The two agree exactly when every root is real; then
`T₂ = a₁ ^ 2 - 2 a₂` for `P = Xⁿ + a₁ Xⁿ⁻¹ + a₂ Xⁿ⁻² + ⋯` (with `a_k = 0` for `k > n`).

For an algebraic integer `θ` of a number field `K`, `∑_σ ‖σ θ‖ ^ 2` over the complex embeddings
`σ` of `K` is `[K : ℚ(θ)]` times `T₂` of the minimal polynomial of `θ`, because each root of that
polynomial is the image of `θ` under exactly `[K : ℚ(θ)]` embeddings.

## Main definitions

* `Polynomial.complexT2 P`: the `T₂` norm of `P : ℂ[X]`.
* `Polynomial.t2 P`: the `T₂` norm of `P : ℤ[X]`, that of its image in `ℂ[X]`.
* `TauCeti.NumberField.candidates n B`: the monic integer polynomials of degree `n` with
  `T₂ ≤ B`.

## Main results

* `Polynomial.complexT2_mul`, `Polynomial.complexT2_C_mul`: `T₂` is additive on products of
  nonzero polynomials and invariant under nonzero scalars.
* `Polynomial.complexT2_eq_of_forall_im_eq_zero`, `Polynomial.t2_eq_of_forall_im_eq_zero`: for a
  monic polynomial with only real roots, `T₂ = a₁ ^ 2 - 2 a₂`.
* `TauCeti.NumberField.candidates_finite`: there are finitely many monic integer polynomials of
  given degree and bounded `T₂`.
* `NumberField.RingOfIntegers.sum_norm_sq_embeddings_eq_finrank_div_mul_t2`: for `θ ∈ 𝓞 K`,
  `∑_σ ‖σ θ‖ ^ 2 = ([K : ℚ] / deg (minpoly ℤ θ)) * T₂ (minpoly ℤ θ)`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, Springer 1993, §4.4
  (the `T₂` norm and `polredabs`).
* The LMFDB Collaboration, knowl `nf.polredabs`.
-/

public section

open Polynomial Module
open scoped IntermediateField

namespace Polynomial

/-! ### The `T₂` norm of a complex polynomial -/

/-- The `T₂` norm of a complex polynomial: the sum of the squared absolute values `‖α‖ ^ 2` of
its complex roots, counted with multiplicity. By convention the zero polynomial, which has no
roots in Mathlib's sense, has `T₂` norm `0`. -/
noncomputable def complexT2 (P : ℂ[X]) : ℝ :=
  (P.roots.map fun z : ℂ => ‖z‖ ^ 2).sum

theorem complexT2_def (P : ℂ[X]) : complexT2 P = (P.roots.map fun z : ℂ => ‖z‖ ^ 2).sum :=
  (rfl)

theorem complexT2_nonneg (P : ℂ[X]) : 0 ≤ complexT2 P :=
  Multiset.sum_nonneg fun _ hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    positivity

/-- The squared absolute value of each complex root is at most the `T₂` norm. -/
theorem norm_sq_le_complexT2 {P : ℂ[X]} {z : ℂ} (hz : z ∈ P.roots) : ‖z‖ ^ 2 ≤ complexT2 P :=
  Multiset.single_le_sum (fun _ hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    positivity) _ (Multiset.mem_map_of_mem _ hz)

/-- The `T₂` norm of a product of linear factors `∏ (X - C a)` is `∑ ‖a‖ ^ 2`. -/
@[simp]
theorem complexT2_multiset_prod_X_sub_C (s : Multiset ℂ) :
    complexT2 (s.map fun a => X - C a).prod = (s.map fun a : ℂ => ‖a‖ ^ 2).sum := by
  rw [complexT2_def, roots_multiset_prod_X_sub_C]

@[simp]
theorem complexT2_X_sub_C (a : ℂ) : complexT2 (X - C a) = ‖a‖ ^ 2 := by
  simp [complexT2_def]

@[simp]
theorem complexT2_X : complexT2 X = 0 := by
  simp [complexT2_def]

@[simp]
theorem complexT2_C (a : ℂ) : complexT2 (C a) = 0 := by
  simp [complexT2_def]

@[simp]
theorem complexT2_zero : complexT2 0 = 0 := by
  simp [complexT2_def]

@[simp]
theorem complexT2_one : complexT2 1 = 0 := by
  simp [complexT2_def]

/-- `T₂` is additive on products of nonzero polynomials. -/
theorem complexT2_mul {P Q : ℂ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    complexT2 (P * Q) = complexT2 P + complexT2 Q := by
  rw [complexT2_def, roots_mul (mul_ne_zero hP hQ), Multiset.map_add, Multiset.sum_add,
    complexT2_def, complexT2_def]

/-- `T₂` is invariant under multiplication by a nonzero scalar. -/
@[simp]
theorem complexT2_C_mul (P : ℂ[X]) {a : ℂ} (ha : a ≠ 0) : complexT2 (C a * P) = complexT2 P := by
  rw [complexT2_def, roots_C_mul _ ha, complexT2_def]

/-- `T₂` is invariant under multiplication by a nonzero scalar. -/
@[simp]
theorem complexT2_smul (P : ℂ[X]) {a : ℂ} (ha : a ≠ 0) : complexT2 (a • P) = complexT2 P := by
  rw [smul_eq_C_mul, complexT2_C_mul _ ha]

/-- **`T₂` of a polynomial with real roots.** If `P = Xⁿ + a₁ Xⁿ⁻¹ + a₂ Xⁿ⁻² + ⋯` is monic and
all its complex roots are real, then `T₂(P) = a₁ ^ 2 - 2 a₂`. Here `a_k = P.reverse.coeff k`,
which is `P.coeff (n - k)` for `k ≤ n` and `0` for `k > n`, so the formula holds in every
degree. The right side is always the power sum `∑ α ^ 2` of the roots; the reality hypothesis
is what makes it equal to `∑ ‖α‖ ^ 2`. -/
theorem complexT2_eq_of_forall_im_eq_zero {P : ℂ[X]} (hP : P.Monic)
    (hreal : ∀ z ∈ P.roots, z.im = 0) :
    (complexT2 P : ℂ) = P.reverse.coeff 1 ^ 2 - 2 * P.reverse.coeff 2 := by
  have hcard : Multiset.card P.roots = P.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hsq : ((P.roots.map fun z : ℂ => ‖z‖ ^ 2).sum : ℂ) = (P.roots.map (· ^ 2)).sum := by
    rw [← Complex.ofRealHom_eq_coe, map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_pow, ← Complex.mul_conj',
      Complex.conj_eq_iff_im.mpr (hreal z hz), sq]
  rw [complexT2_def, hsq, Multiset.sum_map_pow_two_eq_esymm,
    coeff_reverse_eq_esymm_roots_of_card hcard, coeff_reverse_eq_esymm_roots_of_card hcard,
    hP.leadingCoeff]
  ring

/-! ### The `T₂` norm of an integer polynomial -/

/-- The `T₂` norm of an integer polynomial: the sum of the squared absolute values of its complex
roots, counted with multiplicity, i.e. `complexT2` of its image in `ℂ[X]`. -/
noncomputable def t2 (P : ℤ[X]) : ℝ :=
  complexT2 (P.map (Int.castRingHom ℂ))

/-- The integer `T₂` norm is the complex one after mapping the coefficients to `ℂ`. -/
@[simp]
theorem complexT2_map_intCast (P : ℤ[X]) : complexT2 (P.map (Int.castRingHom ℂ)) = t2 P :=
  (rfl)

theorem t2_nonneg (P : ℤ[X]) : 0 ≤ t2 P :=
  complexT2_nonneg _

/-- The squared absolute value of each complex root is at most the `T₂` norm. -/
theorem norm_sq_le_t2 {P : ℤ[X]} {z : ℂ} (hz : z ∈ (P.map (Int.castRingHom ℂ)).roots) :
    ‖z‖ ^ 2 ≤ t2 P :=
  norm_sq_le_complexT2 hz

/-- `T₂` is additive on products of nonzero integer polynomials. -/
theorem t2_mul {P Q : ℤ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) : t2 (P * Q) = t2 P + t2 Q := by
  rw [t2, Polynomial.map_mul, complexT2_mul ((Polynomial.map_ne_zero_iff
    (RingHom.injective_int _)).mpr hP) ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr
    hQ), t2, t2]

/-- `T₂` of an integer polynomial is invariant under multiplication by a nonzero integer. -/
@[simp]
theorem t2_intCast_mul (P : ℤ[X]) {a : ℤ} (ha : a ≠ 0) : t2 ((a : ℤ[X]) * P) = t2 P := by
  rw [← C_eq_intCast, t2, Polynomial.map_mul, map_C, complexT2_C_mul _ (by simpa using ha), t2]

/-- `T₂` of an integer polynomial is invariant under multiplication by a nonzero integer. Not a
simp lemma: simp rewrites `a • P` to `(a : ℤ[X]) * P`, where `t2_intCast_mul` applies. -/
theorem t2_smul (P : ℤ[X]) {a : ℤ} (ha : a ≠ 0) : t2 (a • P) = t2 P := by
  rw [zsmul_eq_mul, t2_intCast_mul _ ha]

@[simp]
theorem t2_X_sub_intCast (a : ℤ) : t2 (X - (a : ℤ[X])) = (a : ℝ) ^ 2 := by
  rw [← C_eq_intCast, ← complexT2_map_intCast, Polynomial.map_sub, map_X, map_C,
    complexT2_X_sub_C, eq_intCast, Complex.norm_intCast, sq_abs]
  norm_cast

@[simp]
theorem t2_intCast (a : ℤ) : t2 (a : ℤ[X]) = 0 := by
  rw [← C_eq_intCast, ← complexT2_map_intCast, map_C, complexT2_C]

@[simp]
theorem t2_zero : t2 0 = 0 := by
  rw [t2, Polynomial.map_zero, complexT2_zero]

@[simp]
theorem t2_one : t2 1 = 0 := by
  rw [← complexT2_map_intCast]
  simp

@[simp]
theorem t2_X : t2 X = 0 := by
  rw [← complexT2_map_intCast]
  simp

/-- **`T₂` of an integer polynomial with real roots.** If `P = Xⁿ + a₁ Xⁿ⁻¹ + a₂ Xⁿ⁻² + ⋯` is a
monic integer polynomial all of whose complex roots are real, then `T₂(P) = a₁ ^ 2 - 2 a₂`, with
`a_k = P.reverse.coeff k` (so `a_k = 0` for `k` beyond the degree). -/
theorem t2_eq_of_forall_im_eq_zero {P : ℤ[X]} (hP : P.Monic)
    (hreal : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, z.im = 0) :
    t2 P = ((P.reverse.coeff 1 ^ 2 - 2 * P.reverse.coeff 2 : ℤ) : ℝ) := by
  have h := complexT2_eq_of_forall_im_eq_zero (hP.map (Int.castRingHom ℂ)) hreal
  simp only [coeff_reverse, coeff_map, eq_intCast, complexT2_map_intCast,
    natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ))] at h
  rw [coeff_reverse, coeff_reverse]
  exact_mod_cast h

end Polynomial

namespace TauCeti.NumberField

/-! ### Monic integer polynomials of bounded `T₂` -/

/-- The candidate polynomials of degree `n` and `T₂` norm at most `B`: the monic integer
polynomials `P` with `P.natDegree = n` and `t2 P ≤ B`. -/
def candidates (n : ℕ) (B : ℝ) : Set ℤ[X] :=
  {P | P.Monic ∧ P.natDegree = n ∧ t2 P ≤ B}

@[simp]
theorem mem_candidates {n : ℕ} {B : ℝ} {P : ℤ[X]} :
    P ∈ candidates n B ↔ P.Monic ∧ P.natDegree = n ∧ t2 P ≤ B :=
  Iff.rfl

/-- The candidate sets increase with the bound. -/
theorem candidates_mono (n : ℕ) : Monotone (candidates n) :=
  fun _ _ hB _ hP => ⟨hP.1, hP.2.1, hP.2.2.trans hB⟩

/-- Candidate sets of distinct degrees are disjoint. -/
theorem disjoint_candidates {n m : ℕ} (h : n ≠ m) (B B' : ℝ) :
    Disjoint (candidates n B) (candidates m B') :=
  Set.disjoint_left.mpr fun _ hP hQ => h (hP.2.1.symm.trans hQ.2.1)

/-- There are no candidates with a negative bound, since `T₂ ≥ 0`. -/
theorem candidates_eq_empty_of_neg {B : ℝ} (hB : B < 0) (n : ℕ) : candidates n B = ∅ :=
  Set.eq_empty_of_forall_notMem fun P hP => (hB.trans_le (t2_nonneg P)).not_ge hP.2.2

/-- The only candidate of degree `0` is the constant `1`, provided the bound is nonnegative. -/
theorem candidates_zero {B : ℝ} (hB : 0 ≤ B) : candidates 0 B = {1} := by
  ext P
  simp only [mem_candidates, Set.mem_singleton_iff]
  refine ⟨fun h => Polynomial.eq_one_of_monic_natDegree_zero h.1 h.2.1, ?_⟩
  rintro rfl
  exact ⟨monic_one, natDegree_one, by rwa [t2_one]⟩

/-- **Finiteness of the candidate sets.** There are only finitely many monic integer polynomials
of a given degree and bounded `T₂` norm: each complex root has absolute value at most `√B`, which
bounds every coefficient. -/
theorem candidates_finite (n : ℕ) (B : ℝ) : (candidates n B).Finite := by
  set C : ℝ := max √B 1 ^ n * n.choose (n / 2)
  -- every candidate has degree at most `n` and coefficients in `[-⌈C⌉, ⌈C⌉]`
  have hsub : candidates n B ⊆
      {P : ℤ[X] | P.natDegree ≤ n ∧ ∀ i, P.coeff i ∈ Set.Icc (-⌈C⌉) ⌈C⌉} := by
    intro P ⟨hmon, hdeg, hB⟩
    refine ⟨hdeg.le, fun i => ?_⟩
    have hroot : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ √B := fun z hz =>
      Real.le_sqrt_of_sq_le ((norm_sq_le_t2 hz).trans hB)
    have h := coeff_bdd_of_roots_le (Int.castRingHom ℂ) hmon (IsAlgClosed.splits _) hdeg.le
      hroot i
    rw [coeff_map, eq_intCast, Complex.norm_intCast] at h
    rw [Set.mem_Icc, ← abs_le]
    exact_mod_cast h.trans (Int.le_ceil C)
  exact (TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem n (Set.finite_Icc _ _)).subset hsub

end TauCeti.NumberField

/-! ### `T₂` of an algebraic integer -/

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The minimal polynomial over `ℚ` of an algebraic integer `θ` is the image of its minimal
polynomial over `ℤ`. -/
theorem minpoly_rat_coe_eq_map (θ : 𝓞 K) :
    minpoly ℚ (θ : K) = (minpoly ℤ θ).map (Int.castRingHom ℚ) := by
  rw [← minpoly_coe, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe,
    algebraMap_int_eq]

/-- For `θ ∈ 𝓞 K`, the sum of `‖σ θ‖ ^ 2` over the complex embeddings `σ` of `K` is
`[K : ℚ(θ)]` times the `T₂` norm of the minimal polynomial of `θ` over `ℤ`: every complex root of
that polynomial is `σ θ` for exactly `[K : ℚ(θ)]` embeddings `σ`. -/
theorem sum_norm_sq_embeddings_eq_finrank_mul_t2 (θ : 𝓞 K) :
    ∑ σ : K →+* ℂ, ‖σ θ‖ ^ 2 =
      finrank ℚ⟮(θ : K)⟯ K * t2 (minpoly ℤ θ) := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ (θ : K)‖ ^ 2)
      (fun σ => ‖σ (θ : K)‖ ^ 2) (fun _ => by simp [RingHom.equivRatAlgHom_apply]),
    TauCeti.sum_algHom_apply_eq_finrank_nsmul_sum_map_aroots (fun z : ℂ => ‖z‖ ^ 2),
    nsmul_eq_mul, ← complexT2_map_intCast, complexT2_def, minpoly_rat_coe_eq_map, aroots_def,
    Polynomial.map_map, RingHom.ext_int ((algebraMap ℚ ℂ).comp _) (Int.castRingHom ℂ)]

/-- For `θ ∈ 𝓞 K`, `∑_σ ‖σ θ‖ ^ 2 = ([K : ℚ] / deg (minpoly ℤ θ)) * T₂ (minpoly ℤ θ)`, the sum
running over the complex embeddings `σ` of `K`. -/
theorem sum_norm_sq_embeddings_eq_finrank_div_mul_t2 (θ : 𝓞 K) :
    ∑ σ : K →+* ℂ, ‖σ θ‖ ^ 2 =
      (finrank ℚ K / (minpoly ℤ θ).natDegree : ℝ) * t2 (minpoly ℤ θ) := by
  have hdeg : finrank ℚ ℚ⟮(θ : K)⟯ = (minpoly ℤ θ).natDegree := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
      minpoly_rat_coe_eq_map, (minpoly.monic θ.isIntegral).natDegree_map]
  have hpos : (0 : ℝ) < finrank ℚ ℚ⟮(θ : K)⟯ := mod_cast finrank_pos
  rw [sum_norm_sq_embeddings_eq_finrank_mul_t2, ← hdeg,
    ← finrank_mul_finrank ℚ ℚ⟮(θ : K)⟯ K, Nat.cast_mul, mul_div_cancel_left₀ _ hpos.ne']

end NumberField.RingOfIntegers
