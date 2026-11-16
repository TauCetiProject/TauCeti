/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.NthProduct
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# State–field `n`-th products, the Borcherds identity, and skew-symmetry

Over a `ℚ`-algebra `R`, the state–field map `Y` of a formal vertex algebra
`A : TauCeti.FormalVertexAxioms R V` intertwines all integer `n`-th products on states with
field-level `n`-th products: `Y(a₍ₙ₎ b, z) = Y(a, z)_{(n)} Y(b, z)`. Combined with the delta
expansion of local commutators, this yields the mode commutator formula, the mode iterate formula,
the full Borcherds (Jacobi) identity for all `m, n, r : ℤ`, and skew-symmetry.

## Main results

* `TauCeti.FormalVertexAxioms.eq_field_of_lie_translation_ncoeff`: uniqueness of a local
  translation-covariant field from its `(-1)`-mode on `|0⟩`.
* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: `Y(a₍ₙ₎ b, z) = Y(a, z)_{(n)} Y(b, z)`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field`: the mode commutator formula.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`: the mode iterate formula (`m = 0` case).
* `TauCeti.FormalVertexAxioms.borcherds_finsum`, `TauCeti.FormalVertexAxioms.borcherds`: the full
  Borcherds identity in `finsum` and finite-cutoff forms.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry`: skew-symmetry of vertex modes.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.2, §4.5, §4.6 and §4.8.
* R. E. Borcherds, *Vertex algebras, Kac–Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2–3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti.FormalVertexAxioms

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

private theorem finsum_eq_sum_range_of_zero {M : Type*} [AddCommMonoid M] {f : ℕ → M} {N : ℕ}
    (h : ∀ i, N ≤ i → f i = 0) : ∑ᶠ i : ℕ, f i = ∑ i ∈ range N, f i :=
  finsum_eq_sum_of_support_subset _ fun i hi ↦ by
    simpa only [mem_coe, mem_range] using not_le.mp fun hle ↦ hi (h i hle)

/-- The field associated to the vacuum vector is the identity vertex operator. -/
@[simp] theorem field_vacuum : A.field A.vacuum = VertexOperator.id R V :=
  ext_ncoeff fun n ↦ by rw [A.ncoeff_field_vacuum, ncoeff_id]

/-- Iterated translation intertwines with iterated formal differentiation of fields. -/
theorem field_pow_translation (a : V) (k : ℕ) :
    A.field ((A.translation ^ k) a) = (derivative^[k]) (A.field a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply', mul_apply_eq_comp, A.field_translation, ih]

/-- Without division, `k!` times the `k`-th Hasse derivative of `Y(a, z)` is `Y(Tᵏ a, z)`. -/
theorem factorial_smul_hasseDerivative_field (a : V) (k : ℕ) :
    k.factorial • hasseDerivative k (A.field a) = A.field ((A.translation ^ k) a) := by
  rw [factorial_smul_hasseDerivative, A.field_pow_translation]

private theorem neg_one_pow_mul_choose_neg_succ (k i : ℕ) :
    (-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i = ((k + i).choose k : ℤ) := by
  rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Ring.choose_neg, Units.smul_def,
    Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_id,
    show (k : ℤ) + 1 + i - 1 = ((k + i : ℕ) : ℤ) by omega, Ring.choose_natCast,
    Nat.choose_symm_add, ← mul_assoc, ← mul_pow, show (-1 : ℤ) * -1 = 1 by ring, one_pow, one_mul]

private theorem hasseDerivative_normalOrder_right_sum (a b c : V) (k M : ℕ) (r : ℤ) :
    (∑ j ∈ range (k + M), ((A.field b)[[r - j - 1]])
        (((hasseDerivative k (A.field a))[[(j : ℤ)]]) c)) =
    -∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        (((-(k : ℤ) - 1).negOnePow : ℤ) •
          ((A.field b)[[(-(k : ℤ) - 1) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  have hsign : -(((-(k : ℤ) - 1).negOnePow : ℤ)) = (-1 : ℤ) ^ k := by
    rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Int.negOnePow_neg, Int.negOnePow_succ,
      Units.val_neg, neg_neg, Int.coe_negOnePow_natCast]
  rw [sum_range_add, sum_eq_zero fun j hj ↦ by
      rw [ncoeff_hasseDerivative, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (mem_range.mp hj)]; simp,
    zero_add, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [ncoeff_hasseDerivative, LinearMap.smul_apply, map_zsmul, Ring.choose_natCast,
    neg_one_pow_mul_choose_neg_succ k i, show ((k + i : ℕ) : ℤ) - k = (i : ℤ) by omega,
    show r - ((k + i : ℕ) : ℤ) - 1 = (-(k : ℤ) - 1) + r - i by omega, smul_smul, ← neg_smul]
  congr 1; linear_combination -(((k + i).choose k : ℤ)) * hsign

end CommRing

section RatAlgebra

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- The `ℚ`-algebra form of `FormalVertexAxioms.factorial_smul_ncoeff_field_apply_vacuum`
(cf. `ncoeff_field_apply_vacuum_neg`), `a₍₋ₖ₋₁₎|0⟩ = (k!)⁻¹ • Tᵏ a`. -/
theorem ncoeff_field_neg_succ_apply_vacuum (a : V) (k : ℕ) :
    ((A.field a)[[-(k : ℤ) - 1]]) A.vacuum =
      algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (A.translation ^ k) a := by
  simpa using ncoeff_neg_succ_apply_of_lie A.translation_vacuum (A.lie_translation_ncoeff a) k

/-- Over a `ℚ`-algebra, a translation-covariant field `B` that is mutually local with every field
`Y(c, z)` is uniquely determined by `b = B₍₋₁₎|0⟩` as `B = Y(b, z)`, without assuming separately
that nonnegative modes annihilate the vacuum. -/
theorem eq_field_of_lie_translation_ncoeff {B : VertexOperator R V} {b : V}
    (hloc : ∀ c : V, ∃ N : ℕ, B.IsLocalOfOrder (A.field c) N)
    (hcov : ∀ m : ℤ, ⁅A.translation, B[[m]]⁆ = (derivative B)[[m]])
    (hb : (B[[-1]]) A.vacuum = b) : B = A.field b := by
  refine A.eq_field_of_ncoeff_apply_vacuum_eq hloc fun n ↦ ?_
  rcases le_or_gt 0 n with hn | hn
  · rw [ncoeff_apply_eq_zero_of_nonneg_of_lie A.translation_vacuum hcov hn,
      A.ncoeff_field_apply_vacuum_of_nonneg b n hn]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [ncoeff_neg_succ_apply_of_lie A.translation_vacuum hcov k, hb,
      A.ncoeff_field_neg_succ_apply_vacuum b k]

/-- The field of `a₍₋ₖ₋₁₎|0⟩` is the `k`-th Hasse derivative of `Y(a, z)`. -/
@[simp] theorem field_ncoeff_neg_succ_apply_vacuum (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) = hasseDerivative k (A.field a) :=
  (A.eq_field_of_lie_translation_ncoeff
    (fun c ↦ let ⟨N, hN⟩ := A.exists_isLocalOfOrder a c; ⟨N + k, hN.hasseDerivative_left k⟩)
    (lie_ncoeff_hasseDerivative (A.lie_translation_ncoeff a) k)
    (ncoeff_neg_one_hasseDerivative k (A.field a) ▸ rfl)).symm

/-! ### State–field `n`-th product -/

/-- **State–field `n`-th product identity.** Over a `ℚ`-algebra, the field of `a₍ₙ₎ b` is the
`n`-th field product `Y(a, z)_{(n)} Y(b, z)` for every integer `n`. -/
theorem field_ncoeff_apply (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm; refine A.eq_field_of_lie_translation_ncoeff (fun c ↦ ?_)
    (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n) ?_
  · obtain ⟨_, h₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨_, h₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨_, h₃⟩ := A.exists_isLocalOfOrder b c
    exact ⟨_, h₁.nthProduct_left h₃ h₂ n⟩
  · rw [ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
      (A.ncoeff_field_apply_vacuum_of_nonneg b) n, A.ncoeff_neg_one_field_apply_vacuum]

/-- For `k : ℕ`, `Y(a₍ₖ₎ b, z)` is the `k`-th nonnegative residue product of `Y(a, z)` and
`Y(b, z)`. -/
theorem field_ncoeff_natCast_apply (a b : V) (k : ℕ) :
    A.field (((A.field a)[[(k : ℤ)]]) b) = nonnegResidueProduct k (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- `Y(a₍₋₁₎ b, z)` is the normal-ordered product `:Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_one]

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDerivative k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_succ]

/-! ### Mode commutator formula -/

/-- If `Y(a, z)` and `Y(b, z)` are local of order `N`, then `a₍ᵢ₎ b = 0` for all `i ≥ N`. -/
theorem ncoeff_field_apply_eq_zero_of_isLocalOfOrder {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) {i : ℕ} (hi : N ≤ i) :
    ((A.field a)[[(i : ℤ)]]) b = 0 := by
  rw [← A.ncoeff_neg_one_field_apply_vacuum (((A.field a)[[(i : ℤ)]]) b),
    A.field_ncoeff_natCast_apply, h.nonnegResidueProduct_eq_zero hi]; simp

/-- **Borcherds commutator formula** for fields local of order `N`:
`[a₍ₘ₎, b₍ₙ₎] = ∑_{i < N} (m choose i) (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`. -/
theorem lie_ncoeff_field {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ i ∈ range N, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  rw [h.lie_ncoeff]; exact sum_congr rfl fun i _ ↦ by rw [A.field_ncoeff_natCast_apply]

/-- **Borcherds commutator formula** in `finsum` form, independent of a chosen locality bound. -/
theorem lie_ncoeff_field_finsum (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ i : ℕ, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  obtain ⟨N, h⟩ := A.exists_isLocalOfOrder a b
  rw [A.lie_ncoeff_field h m n, eq_comm]
  exact finsum_eq_sum_range_of_zero fun i hi ↦ by
    simp [A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h hi]

/-! ### Mode iterate formula (`m = 0` case of Borcherds) -/

private theorem borcherds_zero_left_nonneg (a b c : V) (k : ℕ) (r : ℤ) :
    ((A.field (((A.field a)[[(k : ℤ)]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (k : ℤ) i) •
        (((A.field a)[[(k : ℤ) - i]]) (((A.field b)[[r + i]]) c) -
          (((k : ℤ).negOnePow : ℤ)) •
            ((A.field b)[[(k : ℤ) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rw [finsum_eq_sum_range_of_zero (N := k + 1) fun i hi ↦ by
      simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hi],
    A.field_ncoeff_natCast_apply, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, smul_sub,
    sum_sub_distrib, Int.coe_negOnePow_natCast, Ring.choose_natCast]
  congr 1
  · rw [← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun i hi ↦ ?_
    have hle : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm hle,
      show ((k - i : ℕ) : ℤ) = (k : ℤ) - i by omega, ← natCast_zsmul, smul_smul, mul_comm]
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun i hi ↦ ?_
    have hle : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hpow : (-1 : ℤ) ^ (k - i) = (-1 : ℤ) ^ i * (-1 : ℤ) ^ k := by
      have hk : (-1 : ℤ) ^ k = (-1 : ℤ) ^ (k - i) * (-1 : ℤ) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [hk, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]; norm_num
    rw [show r + ((k - i : ℕ) : ℤ) = (k : ℤ) + r - i by omega, hpow,
      ← natCast_zsmul, smul_smul, smul_smul]; congr 1; ring

private theorem borcherds_zero_left_neg (a b c : V) (k : ℕ) (r : ℤ) :
    ((A.field (((A.field a)[[-(k : ℤ) - 1]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        (((A.field a)[[(-(k : ℤ) - 1) - i]]) (((A.field b)[[r + i]]) c) -
          (((-(k : ℤ) - 1).negOnePow : ℤ)) •
            ((A.field b)[[(-(k : ℤ) - 1) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  obtain ⟨P₀, hP₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨Q₀, hQ₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let M := max ((P₀ : ℤ) - r).toNat Q₀
  rw [finsum_eq_sum_range_of_zero (N := M) fun i hi ↦ by
      simp [hP₀ (r + i) (by omega), hQ₀ i (by omega)],
    A.field_ncoeff_neg_succ_apply, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum _ _ r c (P := M) (Q := k + M) (fun _ _ ↦ hP₀ _ (by omega))
      (fun j _ ↦ by rw [ncoeff_hasseDerivative, LinearMap.smul_apply,
        show (j : ℤ) - k = ((j - k : ℕ) : ℤ) by omega, hQ₀ _ (by omega), smul_zero]),
    A.hasseDerivative_normalOrder_right_sum a b c k M r, ← sub_eq_add_neg]
  simp only [smul_sub, sum_sub_distrib]
  congr 1; exact sum_congr rfl fun i _ ↦ by
    rw [ncoeff_hasseDerivative, LinearMap.smul_apply, neg_one_pow_mul_choose_neg_succ i k,
      neg_one_pow_mul_choose_neg_succ k i, Nat.add_comm i k, Nat.choose_symm_add,
      show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by omega]

/-- **Mode iterate / associativity formula** (`m = 0` case of the Borcherds identity):
`((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`
for all `a, b, c : V` and all integers `n, r : ℤ`. -/
theorem ncoeff_field_ncoeff_apply (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn; exact A.borcherds_zero_left_nonneg a b c n r
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    exact A.borcherds_zero_left_neg a b c k r

end RatAlgebra

/-! ### The Borcherds identity -/

section PascalAux

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

private def borcherdsLHS (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c

private def borcherdsRHS (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
      (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c))

private theorem borcherdsLHS_eq_sum {a b c : V} {m n r : ℤ} {M : ℕ}
    (hM : ∀ i : ℕ, M ≤ i → ((A.field a)[[n + i]]) b = 0) :
    A.borcherdsLHS a b c m n r =
      ∑ i ∈ range M, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c :=
  finsum_eq_sum_range_of_zero fun i hi ↦ by simp [hM i hi]

private theorem borcherdsRHS_eq_sum {a b c : V} {m n r : ℤ} {M : ℕ}
    (hB : ∀ i : ℕ, M ≤ i → ((A.field b)[[r + i]]) c = 0)
    (hA : ∀ i : ℕ, M ≤ i → ((A.field a)[[m + i]]) c = 0) :
    A.borcherdsRHS a b c m n r =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  finsum_eq_sum_range_of_zero fun i hi ↦ by simp [hB i hi, hA i hi]

private theorem sum_choose_add_one {M : ℕ} (m : ℤ) (u : ℕ → V) :
    (∑ i ∈ range (M + 1), Ring.choose (m + 1) i • u i) =
      (∑ i ∈ range (M + 1), Ring.choose m i • u i) +
        ∑ i ∈ range M, Ring.choose m i • u (i + 1) := by
  rw [sum_range_succ' _ M, sum_range_succ' _ M]
  simp only [Ring.choose_zero_right, one_smul, Ring.choose_succ_succ, add_smul, sum_add_distrib]
  abel

private theorem sum_alt_choose_add_one {M : ℕ} (n : ℤ) (u : ℕ → V) :
    (∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose n i) • u i) =
      (∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) • u (i + 1)) +
        ∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) • u i := by
  rw [sum_range_succ' _ M, sum_range_succ' _ M]
  simp only [pow_zero, Ring.choose_zero_right, one_mul, one_smul]
  rw [← add_assoc, ← sum_add_distrib]; congr 1
  exact sum_congr rfl fun i _ ↦ by
    rw [← add_smul, Ring.choose_succ_succ, pow_succ]; congr 1; ring

private theorem borcherdsLHS_add_one (a b c : V) (m n r : ℤ) :
    A.borcherdsLHS a b c (m + 1) n r =
      A.borcherdsLHS a b c m n (r + 1) + A.borcherdsLHS a b c m (n + 1) r := by
  obtain ⟨N₀, hN₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let M := ((N₀ : ℤ) - n).toNat
  rw [A.borcherdsLHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₀ _ (by omega)),
    A.borcherdsLHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₀ _ (by omega)),
    A.borcherdsLHS_eq_sum (M := M) (fun _ _ ↦ hN₀ _ (by omega)),
    sum_choose_add_one (u := fun i ↦ ((A.field (((A.field a)[[n + i]]) b))[[m + 1 + r - i]]) c)]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by rw [show m + 1 + r - (i : ℤ) = m + (r + 1) - i by omega]
  · exact sum_congr rfl fun i _ ↦ by
      rw [show n + ((i + 1 : ℕ) : ℤ) = n + 1 + i by omega,
        show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + r - i by omega]

private theorem borcherdsRHS_add_one (a b c : V) (m n r : ℤ) :
    A.borcherdsRHS a b c (m + 1) n r =
      A.borcherdsRHS a b c m n (r + 1) + A.borcherdsRHS a b c m (n + 1) r := by
  obtain ⟨N₂, hN₂⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨N₃, hN₃⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let M := max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat
  rw [A.borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    A.borcherdsRHS_eq_sum (M := M) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    A.borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  simp only [smul_sub, sum_sub_distrib]
  let S (k : ℕ) (p : ℤ) (u : ℕ → V) := ∑ i ∈ range k, ((-1 : ℤ) ^ i * Ring.choose p i) • u i
  let u₁ (i : ℕ) := ((A.field a)[[m + 1 + n - i]]) (((A.field b)[[r + i]]) c)
  let u₂ (i : ℕ) := (n.negOnePow : ℤ) • ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c)
  have e1a : S M n (fun i ↦ ((A.field a)[[m + n - i]]) (((A.field b)[[r + 1 + i]]) c)) =
      S M n (fun i ↦ u₁ (i + 1)) := sum_congr rfl fun i _ ↦ by
    simp only [u₁, show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by omega,
      show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by omega]
  have e1b : S (M + 1) (n + 1) (fun i ↦ ((A.field a)[[m + (n + 1) - i]]) (((A.field b)[[r + i]]) c))
      = S (M + 1) (n + 1) u₁ := sum_congr rfl fun i _ ↦ by
    simp only [u₁, show m + 1 + n - (i : ℤ) = m + (n + 1) - i by omega]
  have e2a : S (M + 1) n (fun i ↦ (n.negOnePow : ℤ) •
      ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c)) = S M n (fun i ↦ u₂ (i + 1)) := by
    dsimp only [S]; rw [sum_range_succ, hN₃ (m + 1 + M) (by omega), map_zero, smul_zero, smul_zero,
      add_zero]
    exact sum_congr rfl fun i _ ↦ by simp only [u₂,
      show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by omega,
      show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by omega]
  have e2c : S (M + 1) (n + 1) (fun i ↦ ((n + 1).negOnePow : ℤ) •
      ((A.field b)[[n + 1 + r - i]]) (((A.field a)[[m + i]]) c)) = -S (M + 1) (n + 1) u₂ := by
    dsimp only [S]; rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ ↦ by simp only [u₂, Int.negOnePow_succ, Units.val_neg, neg_smul,
      smul_neg, show n + 1 + r - (i : ℤ) = n + (r + 1) - i by omega]
  change S (M + 1) n u₁ - S (M + 1) n _ =
    (S M n _ - S M n u₂) + (S (M + 1) (n + 1) _ - S (M + 1) (n + 1) _)
  rw [e1a, e1b, e2a, e2c, show S (M + 1) n u₁ = _ from sum_alt_choose_add_one n u₁,
    show S M n u₂ = S (M + 1) n u₂ by
      dsimp only [S]; rw [sum_range_succ]; simp [u₂, hN₃ (m + M) (by omega)],
    show S (M + 1) n u₂ = _ from sum_alt_choose_add_one n u₂]; abel

private theorem borcherds_eq_of_zero {a b c : V}
    (h0n : ∀ q s : ℤ, A.borcherdsLHS a b c 0 q s = A.borcherdsRHS a b c 0 q s)
    (hm0 : ∀ p s : ℤ, A.borcherdsLHS a b c p 0 s = A.borcherdsRHS a b c p 0 s)
    (m n r : ℤ) : A.borcherdsLHS a b c m n r = A.borcherdsRHS a b c m n r := by
  let D (p q s : ℤ) := A.borcherdsLHS a b c p q s - A.borcherdsRHS a b c p q s
  have hrec (p q s : ℤ) : D (p + 1) q s = D p q (s + 1) + D p (q + 1) s := by
    simp only [D, A.borcherdsLHS_add_one, A.borcherdsRHS_add_one]; abel
  have hm_nonneg (k : ℕ) : ∀ q s : ℤ, D k q s = 0 := by
    induction k with
    | zero => exact fun q s ↦ sub_eq_zero.mpr (h0n q s)
    | succ k ih => exact fun q s ↦ by rw [Nat.cast_succ, hrec, ih, ih, add_zero]
  have hn_nonneg (l : ℕ) : ∀ p s : ℤ, D p l s = 0 := by
    induction l with
    | zero => exact fun p s ↦ sub_eq_zero.mpr (hm0 p s)
    | succ l ih =>
      intro p s; have h := hrec p l s
      rw [ih (p + 1) s, ih p (s + 1), zero_add, eq_comm] at h; simpa [Nat.cast_succ] using h
  have hmn_neg (k : ℕ) : ∀ (l : ℕ) (s : ℤ), D (-(k : ℤ)) (-(l : ℤ)) s = 0 := by
    induction k with
    | zero => exact fun l s ↦ by simpa [D] using sub_eq_zero.mpr (h0n _ s)
    | succ k ihk =>
      intro l; induction l with
      | zero => exact fun s ↦ by simpa [D] using sub_eq_zero.mpr (hm0 _ s)
      | succ l ihl =>
        intro s; have h := hrec (-((k + 1 : ℕ) : ℤ)) (-((l + 1 : ℕ) : ℤ)) (s - 1)
        rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by omega,
          show -((l + 1 : ℕ) : ℤ) + 1 = -(l : ℤ) by omega, sub_add_cancel,
          ihk (l + 1) (s - 1), ihl (s - 1), add_zero] at h
        exact h.symm
  suffices hD : D m n r = 0 from sub_eq_zero.mp hD
  rcases le_or_gt 0 m with hm | hm; · lift m to ℕ using hm; exact hm_nonneg m n r
  rcases le_or_gt 0 n with hn | hn; · lift n to ℕ using hn; exact hn_nonneg n m r
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, n = -(l : ℤ) := ⟨(-n).toNat, by omega⟩
  exact hmn_neg k l r

end PascalAux

section Borcherds

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

private theorem borcherds_zero_left (a b c : V) (n r : ℤ) :
    A.borcherdsLHS a b c 0 n r = A.borcherdsRHS a b c 0 n r := by
  rw [borcherdsLHS, finsum_eq_single _ 0]
  · simpa [borcherdsRHS] using A.ncoeff_field_ncoeff_apply a b c n r
  · intro i hi; simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem borcherds_zero_mid (a b c : V) (m r : ℤ) :
    A.borcherdsLHS a b c m 0 r = A.borcherdsRHS a b c m 0 r := by
  obtain ⟨N, hloc⟩ := A.exists_isLocalOfOrder a b
  have hL : A.borcherdsLHS a b c m 0 r = (⁅(A.field a)[[m]], (A.field b)[[r]]⁆) c := by
    rw [A.lie_ncoeff_field hloc m r, LinearMap.sum_apply,
      A.borcherdsLHS_eq_sum (M := N) fun i hi ↦ by
        simpa using A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder hloc hi]
    exact sum_congr rfl fun i _ ↦ by simp
  have hR : A.borcherdsRHS a b c m 0 r = (⁅(A.field a)[[m]], (A.field b)[[r]]⁆) c := by
    rw [borcherdsRHS, finsum_eq_single _ 0]
    · simp [Ring.lie_def, mul_apply_eq_comp]
    · intro i hi; simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  exact hL.trans hR.symm

/-- **The Borcherds identity** in `finsum` form: for all states `a, b, c : V` and all integers
`m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`. -/
theorem borcherds_finsum (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  A.borcherds_eq_of_zero (A.borcherds_zero_left a b c) (A.borcherds_zero_mid a b c) m n r

/-- **The Borcherds identity** with explicit finite cutoff `N`: all three mode expressions vanish
for `i ≥ N`, and the finite sums over `Finset.range N` agree. -/
theorem borcherds (a b c : V) (m n r : ℤ) :
    ∃ N : ℕ,
      (∀ i : ℕ, N ≤ i → ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c = 0) ∧
      (∀ i : ℕ, N ≤ i →
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) = 0 ∧
        ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c) = 0) ∧
      (∑ i ∈ range N, Ring.choose m i •
          ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
        ∑ i ∈ range N, ((-1 : ℤ) ^ i * Ring.choose n i) •
          (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
            (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  obtain ⟨N₁, hN₁⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  obtain ⟨N₂, hN₂⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨N₃, hN₃⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let N := max ((N₁ : ℤ) - n).toNat (max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat)
  refine ⟨N, fun i hi ↦ by simp [hN₁ (n + i) (by omega)],
    fun i hi ↦ ⟨by simp [hN₂ (r + i) (by omega)], by simp [hN₃ (m + i) (by omega)]⟩, ?_⟩
  rw [← A.borcherdsLHS_eq_sum (fun _ _ ↦ hN₁ _ (by omega)),
    ← A.borcherdsRHS_eq_sum (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  exact A.borcherds_finsum a b c m n r

/-! ### Skew-symmetry -/

/-- **Skew-symmetry of formal vertex algebra modes**:
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)` for all `a, b : V` and `n : ℤ`. -/
theorem ncoeff_field_apply_skewSymmetry (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a)) := by
  have hbor := A.borcherds_finsum b a A.vacuum (-1) n 0
  have hR : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
      (((A.field b)[[-1 + n - i]]) (((A.field a)[[(0 : ℤ) + i]]) A.vacuum) -
        (n.negOnePow : ℤ) • ((A.field a)[[n + 0 - i]]) (((A.field b)[[-1 + i]]) A.vacuum))) =
      -((n.negOnePow : ℤ) • (((A.field a)[[n]]) b)) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi; simp [A.ncoeff_field_apply_vacuum_of_nonneg b (-1 + i) (by omega)]
  obtain ⟨N₀, hN₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := ((N₀ : ℤ) - n).toNat
  rw [hR, finsum_eq_sum_range_of_zero (N := M)
    (fun i hi ↦ by simp [hN₀ (n + i) (by omega)])] at hbor
  rw [finsum_eq_sum_range_of_zero (N := M) (fun i hi ↦ by simp [hN₀ (n + i) (by omega)])]
  have hsq : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one]
  have hmul := congrArg ((-(n.negOnePow : ℤ)) • ·) hbor.symm
  rw [smul_neg, ← neg_smul, neg_neg, smul_smul, hsq, one_smul, smul_sum] at hmul
  rw [hmul]
  refine sum_congr rfl fun i _ ↦ ?_
  have hch : Ring.choose (-1 : ℤ) i = (-1 : ℤ) ^ i := by
    simpa [show (1 : ℤ) + i - 1 = i by omega, Int.negOnePow_def, Units.smul_def,
      Ring.choose_natCast, Nat.choose_self] using Ring.choose_neg (1 : ℤ) i
  rw [hch, show -1 + (0 : ℤ) - i = -(i : ℤ) - 1 by omega, A.ncoeff_field_neg_succ_apply_vacuum,
    smul_smul]
  congr 1; rw [Int.negOnePow_add, Units.val_mul, Int.coe_negOnePow_natCast, neg_mul]

end Borcherds

end TauCeti.FormalVertexAxioms
