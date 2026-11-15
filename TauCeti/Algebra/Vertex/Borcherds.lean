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
`A : TauCeti.FormalVertexAxioms R V` intertwines all integer `n`-th products on states with the
field-level `n`-th products (`VertexOperator.nthProduct`):

`Y(a₍ₙ₎ b, z) = Y(a, z)_{(n)} Y(b, z)`.

In particular, `Y(a₍₋₁₎ b, z) = :Y(a, z) Y(b, z):` recovers normal ordering and
`Y(a₍ₖ₎ b, z)` (`k : ℕ`) recovers the nonnegative residue products controlling singular operator
product terms. Combining this state–field product identity with the delta expansion of local
commutators yields the algebraic identities governing vertex algebra modes and representations:

* **Mode commutator formula** (`TauCeti.FormalVertexAxioms.lie_ncoeff_field`):
  `[a₍ₘ₎, b₍ₙ₎] = ∑_{i < N} (m choose i) (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`.
* **Mode iterate / associativity formula** (`TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`):
  `((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`.
* **The Borcherds (Jacobi) identity** (`TauCeti.FormalVertexAxioms.borcherds_finsum` and
  `TauCeti.FormalVertexAxioms.borcherds`), unifying commutativity and associativity of modes for all
  integers `m, n, r : ℤ`.
* **Skew-symmetry** (`TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry`):
  `a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)`.

## Main results

* `TauCeti.FormalVertexAxioms.eq_field_of_lie_translation_ncoeff`: over a `ℚ`-algebra, a
  translation-covariant field local to all `Y(c, z)` is `Y(B₍₋₁₎|0⟩, z)`.
* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: `Y(a₍ₙ₎ b, z) = Y(a, z)_{(n)} Y(b, z)`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field`: the mode commutator formula.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`: the mode iterate formula (`m = 0` case of
  Borcherds).
* `TauCeti.FormalVertexAxioms.borcherds_finsum`, `TauCeti.FormalVertexAxioms.borcherds`: the full
  Borcherds identity in `finsum` and explicit finite-cutoff forms.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry`: Borcherds skew-symmetry of modes.

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

/-- The field associated to the vacuum vector is the identity vertex operator. -/
@[simp]
theorem field_vacuum : A.field A.vacuum = VertexOperator.id R V :=
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
  have hneg : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by omega
  have harg : (k : ℤ) + 1 + i - 1 = ((k + i : ℕ) : ℤ) := by omega
  rw [hneg, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_id,
    harg, Ring.choose_natCast, Nat.choose_symm_add, ← mul_assoc, ← mul_pow,
    show (-1 : ℤ) * -1 = 1 by ring, one_pow, one_mul]

private theorem hasseDerivative_normalOrder_right_sum (a b c : V) (k M : ℕ) (r : ℤ) :
    (∑ j ∈ range (k + M), ((A.field b)[[r - j - 1]])
        (((hasseDerivative k (A.field a))[[(j : ℤ)]]) c)) =
    -∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        (((-(k : ℤ) - 1).negOnePow : ℤ) •
          ((A.field b)[[(-(k : ℤ) - 1) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  have hinit :
      (∑ j ∈ range k, ((A.field b)[[r - j - 1]])
          (((hasseDerivative k (A.field a))[[(j : ℤ)]]) c)) = 0 := by
    refine sum_eq_zero fun j hj ↦ ?_
    rw [ncoeff_hasseDerivative, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
    simp
  have hsign : -(((-(k : ℤ) - 1).negOnePow : ℤ)) = (-1 : ℤ) ^ k := by
    have e : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by omega
    rw [e, Int.negOnePow_neg, Int.negOnePow_succ, Units.val_neg, neg_neg,
      Int.coe_negOnePow_natCast]
  rw [sum_range_add, hinit, zero_add, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [ncoeff_hasseDerivative, LinearMap.smul_apply, map_zsmul,
    Ring.choose_natCast, neg_one_pow_mul_choose_neg_succ k i,
    show ((k + i : ℕ) : ℤ) - k = (i : ℤ) by omega,
    show r - ((k + i : ℕ) : ℤ) - 1 = (-(k : ℤ) - 1) + r - i by omega,
    smul_smul, ← neg_smul]
  congr 1
  linear_combination -(((k + i).choose k : ℤ)) * hsign

end CommRing

section RatAlgebra

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- The `ℚ`-algebra form of `FormalVertexAxioms.factorial_smul_ncoeff_field_apply_vacuum`
(cf. `ncoeff_field_apply_vacuum_neg`), `a₍₋ₖ₋₁₎|0⟩ = (k!)⁻¹ • Tᵏ a`. -/
theorem ncoeff_field_neg_succ_apply_vacuum (a : V) (k : ℕ) :
    ((A.field a)[[-(k : ℤ) - 1]]) A.vacuum =
      algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (A.translation ^ k) a := by
  rw [← A.factorial_smul_ncoeff_field_apply_vacuum, ← Nat.cast_smul_eq_nsmul R,
    ← map_natCast (algebraMap ℚ R), smul_smul, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast k.factorial_ne_zero), map_one, one_smul]

/-- Over a `ℚ`-algebra, a translation-covariant field `B` that is mutually local with every field
`Y(c, z)` is uniquely determined by `b = B₍₋₁₎|0⟩` as `B = Y(b, z)`, without assuming separately
that nonnegative modes annihilate the vacuum. -/
theorem eq_field_of_lie_translation_ncoeff {B : VertexOperator R V} {b : V}
    (hloc : ∀ c : V, ∃ N : ℕ, B.IsLocalOfOrder (A.field c) N)
    (hcov : ∀ m : ℤ, ⁅A.translation, B[[m]]⁆ = (derivative B)[[m]])
    (hb : (B[[-1]]) A.vacuum = b) :
    B = A.field b := by
  refine A.eq_field_of_ncoeff_apply_vacuum_eq hloc fun n ↦ ?_
  rcases le_or_gt 0 n with hn | hn
  · rw [ncoeff_apply_eq_zero_of_nonneg_of_lie A.translation_vacuum hcov hn,
      A.ncoeff_field_apply_vacuum_of_nonneg b n hn]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [ncoeff_neg_succ_apply_of_lie A.translation_vacuum hcov k, hb,
      A.ncoeff_field_neg_succ_apply_vacuum b k]

/-- The field of `a₍₋ₖ₋₁₎|0⟩` is the `k`-th Hasse derivative of `Y(a, z)`. -/
@[simp]
theorem field_ncoeff_neg_succ_apply_vacuum (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) = hasseDerivative k (A.field a) := by
  symm
  refine A.eq_field_of_lie_translation_ncoeff
    (fun c ↦ let ⟨N, hN⟩ := A.exists_isLocalOfOrder a c; ⟨N + k, hN.hasseDerivative_left k⟩)
    (lie_ncoeff_hasseDerivative (A.lie_translation_ncoeff a) k) ?_
  rw [ncoeff_neg_one_hasseDerivative]

/-! ### State–field `n`-th product -/

/-- **State–field `n`-th product identity.** Over a `ℚ`-algebra, the field of `a₍ₙ₎ b` is the
`n`-th field product `Y(a, z)_{(n)} Y(b, z)` for every integer `n`. -/
theorem field_ncoeff_apply (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_lie_translation_ncoeff (fun c ↦ ?_)
    (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n) ?_
  · obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨N₃, h₃⟩ := A.exists_isLocalOfOrder b c
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
    A.field_ncoeff_natCast_apply, h.nonnegResidueProduct_eq_zero hi,
    map_zero, Pi.zero_apply, LinearMap.zero_apply]

/-- **Borcherds commutator formula** for fields local of order `N`:
`[a₍ₘ₎, b₍ₙ₎] = ∑_{i < N} (m choose i) (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`. -/
theorem lie_ncoeff_field {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ i ∈ range N, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  rw [h.lie_ncoeff]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [A.field_ncoeff_natCast_apply]

/-- **Borcherds commutator formula** in `finsum` form, independent of a chosen locality bound. -/
theorem lie_ncoeff_field_finsum (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ i : ℕ, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  obtain ⟨N, h⟩ := A.exists_isLocalOfOrder a b
  rw [A.lie_ncoeff_field h m n, eq_comm]
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h hle])

/-! ### Mode iterate formula (`m = 0` case of Borcherds) -/

private theorem borcherds_zero_left_nonneg (a b c : V) (k : ℕ) (r : ℤ) :
    ((A.field (((A.field a)[[(k : ℤ)]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (k : ℤ) i) •
        (((A.field a)[[(k : ℤ) - i]]) (((A.field b)[[r + i]]) c) -
          (((k : ℤ).negOnePow : ℤ)) •
            ((A.field b)[[(k : ℤ) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  have hsupp : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose (k : ℤ) i) •
        (((A.field a)[[(k : ℤ) - i]]) (((A.field b)[[r + i]]) c) -
          (((k : ℤ).negOnePow : ℤ)) •
            ((A.field b)[[(k : ℤ) + r - i]]) (((A.field a)[[(i : ℤ)]]) c))) ⊆
      range (k + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hle])
  rw [finsum_eq_sum_of_support_subset _ hsupp, A.field_ncoeff_natCast_apply,
    ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
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
      have h₁ : (-1 : ℤ) ^ k = (-1 : ℤ) ^ (k - i) * (-1 : ℤ) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [h₁, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow,
        show (-1 : ℤ) * -1 = 1 by ring, one_pow, mul_one]
    rw [show r + ((k - i : ℕ) : ℤ) = (k : ℤ) + r - i by omega, hpow,
      ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    ring

private theorem borcherds_zero_left_neg (a b c : V) (k : ℕ) (r : ℤ) :
    ((A.field (((A.field a)[[-(k : ℤ) - 1]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        (((A.field a)[[(-(k : ℤ) - 1) - i]]) (((A.field b)[[r + i]]) c) -
          (((-(k : ℤ) - 1).negOnePow : ℤ)) •
            ((A.field b)[[(-(k : ℤ) - 1) + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  obtain ⟨P₀, hP₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨Q₀, hQ₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let M := max ((P₀ : ℤ) - r).toNat Q₀
  have cutB (i : ℕ) (hi : M ≤ i) : ((A.field b)[[r + i]]) c = 0 := hP₀ _ (by omega)
  have cutA (i : ℕ) (hi : M ≤ i) : ((A.field a)[[(i : ℤ)]]) c = 0 := hQ₀ _ (by omega)
  have cutdA (j : ℕ) (hj : k + M ≤ j) : ((hasseDerivative k (A.field a))[[(j : ℤ)]]) c = 0 := by
    rw [ncoeff_hasseDerivative, LinearMap.smul_apply,
      show (j : ℤ) - k = ((j - k : ℕ) : ℤ) by omega, cutA (j - k) (by omega), smul_zero]
  have hsupp : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        (((A.field a)[[(-(k : ℤ) - 1) - i]]) (((A.field b)[[r + i]]) c) -
          (((-(k : ℤ) - 1).negOnePow : ℤ)) •
            ((A.field b)[[(-(k : ℤ) - 1) + r - i]]) (((A.field a)[[(i : ℤ)]]) c))) ⊆
      range M := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [cutB i hle, cutA i hle])
  rw [finsum_eq_sum_of_support_subset _ hsupp, A.field_ncoeff_neg_succ_apply,
    ncoeff_normalOrder, normalOrderCoeff_eq_sum _ _ r c cutB cutdA]
  have hleft :
      (∑ i ∈ range M, ((hasseDerivative k (A.field a))[[-(i : ℤ) - 1]])
          (((A.field b)[[r + i]]) c)) =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i) •
        ((A.field a)[[(-(k : ℤ) - 1) - i]]) (((A.field b)[[r + i]]) c) := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [ncoeff_hasseDerivative, LinearMap.smul_apply, neg_one_pow_mul_choose_neg_succ i k,
      neg_one_pow_mul_choose_neg_succ k i, Nat.add_comm i k, Nat.choose_symm_add,
      show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by omega]
  rw [hleft, A.hasseDerivative_normalOrder_right_sum a b c k M r, ← sub_eq_add_neg]
  simp only [smul_sub, sum_sub_distrib]

/-- **Mode iterate / associativity formula** (`m = 0` case of the Borcherds identity):
`((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`
for all `a, b, c : V` and all integers `n, r : ℤ`. -/
theorem ncoeff_field_ncoeff_apply (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    exact A.borcherds_zero_left_nonneg a b c n r
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
      ∑ i ∈ range M, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hM i hle])

private theorem borcherdsRHS_eq_sum {a b c : V} {m n r : ℤ} {M : ℕ}
    (hB : ∀ i : ℕ, M ≤ i → ((A.field b)[[r + i]]) c = 0)
    (hA : ∀ i : ℕ, M ≤ i → ((A.field a)[[m + i]]) c = 0) :
    A.borcherdsRHS a b c m n r =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hB i hle, hA i hle])

private theorem borcherdsLHS_add_one (a b c : V) (m n r : ℤ) :
    A.borcherdsLHS a b c (m + 1) n r =
      A.borcherdsLHS a b c m n (r + 1) + A.borcherdsLHS a b c m (n + 1) r := by
  obtain ⟨N₀, hN₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let M := ((N₀ : ℤ) - n).toNat
  rw [A.borcherdsLHS_eq_sum (M := M + 1) (fun i hi ↦ hN₀ _ (by omega)),
    A.borcherdsLHS_eq_sum (M := M + 1) (fun i hi ↦ hN₀ _ (by omega)),
    A.borcherdsLHS_eq_sum (M := M) (fun i hi ↦ hN₀ _ (by omega)),
    sum_range_succ', sum_range_succ' _ M]
  simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero, sub_zero,
    Ring.choose_succ_succ, add_smul, sum_add_distrib]
  have e₁ : ∀ i ∈ range M,
      Ring.choose m i • ((A.field (((A.field a)[[n + ((i + 1 : ℕ) : ℤ)]]) b))
        [[m + 1 + r - ((i + 1 : ℕ) : ℤ)]]) c =
      Ring.choose m i • ((A.field (((A.field a)[[n + 1 + i]]) b))[[m + r - i]]) c := by
    intro i _
    rw [show n + ((i + 1 : ℕ) : ℤ) = n + 1 + i by omega,
      show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + r - i by omega]
  have e₂ : ∀ i ∈ range M,
      Ring.choose m (i + 1) • ((A.field (((A.field a)[[n + ((i + 1 : ℕ) : ℤ)]]) b))
        [[m + 1 + r - ((i + 1 : ℕ) : ℤ)]]) c =
      Ring.choose m (i + 1) •
        ((A.field (((A.field a)[[n + ((i + 1 : ℕ) : ℤ)]]) b))
          [[m + (r + 1) - ((i + 1 : ℕ) : ℤ)]]) c := by
    intro i _
    rw [show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + (r + 1) - ((i + 1 : ℕ) : ℤ) by omega]
  rw [sum_congr rfl e₁, sum_congr rfl e₂, show m + 1 + r = m + (r + 1) by omega]
  abel

private theorem borcherdsRHS_add_one_first (a b c : V) (m n r : ℤ) (M : ℕ) :
    (∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A.field a)[[m + 1 + n - i]]) (((A.field b)[[r + i]]) c)) =
    (∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + 1 + i]]) c)) +
      ∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) •
        ((A.field a)[[m + (n + 1) - i]]) (((A.field b)[[r + i]]) c) := by
  rw [sum_range_succ' _ M, sum_range_succ' _ M]
  simp only [pow_zero, Ring.choose_zero_right, one_mul, one_smul, Nat.cast_zero, sub_zero,
    add_zero, show m + (n + 1) = m + 1 + n by omega]
  have hcomb :
      (∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A.field a)[[m + n - i]]) (((A.field b)[[r + 1 + i]]) c)) +
        (∑ i ∈ range M, ((-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1)) •
          ((A.field a)[[m + 1 + n - ((i + 1 : ℕ) : ℤ)]])
            (((A.field b)[[r + ((i + 1 : ℕ) : ℤ)]]) c)) =
      ∑ i ∈ range M, ((-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1)) •
        ((A.field a)[[m + 1 + n - ((i + 1 : ℕ) : ℤ)]])
          (((A.field b)[[r + ((i + 1 : ℕ) : ℤ)]]) c) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by omega,
      show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by omega, ← add_smul, Ring.choose_succ_succ, pow_succ]
    congr 1
    ring
  rw [← add_assoc, hcomb]

private theorem borcherdsRHS_add_one_second (a b c : V) (m n r : ℤ) (M : ℕ)
    (hAM : ((A.field a)[[m + M]]) c = 0) (hAM1 : ((A.field a)[[m + 1 + M]]) c = 0) :
    (∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
        ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c)) =
    (∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
        ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c)) +
      ∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose (n + 1) i) • ((n + 1).negOnePow : ℤ) •
        ((A.field b)[[n + 1 + r - i]]) (((A.field a)[[m + i]]) c) := by
  have hpad1 :
      (∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c)) =
      ∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c) := by
    rw [sum_range_succ, hAM, map_zero, smul_zero, smul_zero, add_zero]
  have hpad0 :
      (∑ i ∈ range (M + 1), ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c)) =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c) := by
    rw [sum_range_succ, hAM1, map_zero, smul_zero, smul_zero, add_zero]
  rw [hpad1, hpad0, sum_range_succ' _ M, sum_range_succ' _ M]
  simp only [pow_zero, Ring.choose_zero_right, one_mul, one_smul, Nat.cast_zero, sub_zero,
    add_zero, Int.negOnePow_succ, Units.val_neg, neg_smul,
    show n + 1 + r = n + (r + 1) by omega]
  have hcomb :
      (∑ i ∈ range M, ((-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1)) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]])
            (((A.field a)[[m + ((i + 1 : ℕ) : ℤ)]]) c)) +
        (∑ i ∈ range M, ((-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1)) •
          -((n.negOnePow : ℤ) • ((A.field b)[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]])
            (((A.field a)[[m + ((i + 1 : ℕ) : ℤ)]]) c))) =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by omega,
      show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by omega,
      smul_neg, ← neg_smul, smul_smul, smul_smul, smul_smul, ← add_smul,
      Ring.choose_succ_succ, pow_succ]
    congr 1
    ring
  rw [← hcomb]
  abel

private theorem borcherdsRHS_add_one (a b c : V) (m n r : ℤ) :
    A.borcherdsRHS a b c (m + 1) n r =
      A.borcherdsRHS a b c m n (r + 1) + A.borcherdsRHS a b c m (n + 1) r := by
  obtain ⟨N₂, hN₂⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨N₃, hN₃⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let M := max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat
  rw [A.borcherdsRHS_eq_sum (M := M + 1)
      (fun i hi ↦ hN₂ _ (by omega)) (fun i hi ↦ hN₃ _ (by omega)),
    A.borcherdsRHS_eq_sum (M := M)
      (fun i hi ↦ hN₂ _ (by omega)) (fun i hi ↦ hN₃ _ (by omega)),
    A.borcherdsRHS_eq_sum (M := M + 1)
      (fun i hi ↦ hN₂ _ (by omega)) (fun i hi ↦ hN₃ _ (by omega))]
  simp only [smul_sub, sum_sub_distrib]
  rw [A.borcherdsRHS_add_one_first a b c m n r M,
    A.borcherdsRHS_add_one_second a b c m n r M (hN₃ _ (by omega)) (hN₃ _ (by omega))]
  abel

private theorem borcherds_eq_of_zero {a b c : V}
    (h0n : ∀ q s : ℤ, A.borcherdsLHS a b c 0 q s = A.borcherdsRHS a b c 0 q s)
    (hm0 : ∀ p s : ℤ, A.borcherdsLHS a b c p 0 s = A.borcherdsRHS a b c p 0 s)
    (m n r : ℤ) : A.borcherdsLHS a b c m n r = A.borcherdsRHS a b c m n r := by
  let D : ℤ → ℤ → ℤ → V := fun p q s ↦ A.borcherdsLHS a b c p q s - A.borcherdsRHS a b c p q s
  have h0n' (q s : ℤ) : D 0 q s = 0 := sub_eq_zero.mpr (h0n q s)
  have hm0' (p s : ℤ) : D p 0 s = 0 := sub_eq_zero.mpr (hm0 p s)
  have hrec (p q s : ℤ) : D (p + 1) q s = D p q (s + 1) + D p (q + 1) s := by
    simp only [D, A.borcherdsLHS_add_one, A.borcherdsRHS_add_one]
    abel
  have hm_nonneg (k : ℕ) : ∀ q s : ℤ, D k q s = 0 := by
    induction k with
    | zero => exact h0n'
    | succ k ih =>
      intro q s
      rw [Nat.cast_succ, hrec, ih, ih, add_zero]
  have hn_nonneg (l : ℕ) : ∀ p s : ℤ, D p l s = 0 := by
    induction l with
    | zero => exact hm0'
    | succ l ih =>
      intro p s
      have h := hrec p l s
      rw [ih (p + 1) s, ih p (s + 1), zero_add, eq_comm] at h
      simpa [Nat.cast_succ] using h
  have hmn_neg (t : ℕ) : ∀ k l : ℕ, k + l = t → ∀ s : ℤ, D (-(k : ℤ)) (-(l : ℤ)) s = 0 := by
    induction t with
    | zero =>
      intro k l hkl s
      obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
      simpa using h0n' 0 s
    | succ t ih =>
      intro k l hkl s
      rcases eq_or_ne k 0 with rfl | hk
      · simpa using h0n' _ s
      · rcases eq_or_ne l 0 with rfl | hl
        · simpa using hm0' _ s
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          have h := hrec (-((k' + 1 : ℕ) : ℤ)) (-((l' + 1 : ℕ) : ℤ)) (s - 1)
          rw [show -((k' + 1 : ℕ) : ℤ) + 1 = -(k' : ℤ) by omega,
            show -((l' + 1 : ℕ) : ℤ) + 1 = -(l' : ℤ) by omega, sub_add_cancel,
            ih k' (l' + 1) (by omega) (s - 1), ih (k' + 1) l' (by omega) (s - 1), add_zero] at h
          exact h.symm
  suffices hD : D m n r = 0 from sub_eq_zero.mp hD
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    exact hm_nonneg m n r
  · rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      exact hn_nonneg n m r
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l : ℕ, n = -(l : ℤ) := ⟨(-n).toNat, by omega⟩
      exact hmn_neg (k + l) k l rfl r

end PascalAux

section Borcherds

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

private theorem borcherds_zero_left (a b c : V) (n r : ℤ) :
    A.borcherdsLHS a b c 0 n r = A.borcherdsRHS a b c 0 n r := by
  rw [borcherdsLHS, finsum_eq_single _ 0]
  · simpa [borcherdsRHS] using A.ncoeff_field_ncoeff_apply a b c n r
  · intro i hi
    simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem borcherds_zero_mid (a b c : V) (m r : ℤ) :
    A.borcherdsLHS a b c m 0 r = A.borcherdsRHS a b c m 0 r := by
  obtain ⟨N, hloc⟩ := A.exists_isLocalOfOrder a b
  have hL : A.borcherdsLHS a b c m 0 r =
      (⁅(A.field a)[[m]], (A.field b)[[r]]⁆) c := by
    rw [A.lie_ncoeff_field hloc m r, LinearMap.sum_apply,
      A.borcherdsLHS_eq_sum (M := N) fun i hi ↦ by
        simpa using A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder hloc hi]
    refine sum_congr rfl fun i _ ↦ ?_
    simp
  have hR : A.borcherdsRHS a b c m 0 r =
      (⁅(A.field a)[[m]], (A.field b)[[r]]⁆) c := by
    rw [borcherdsRHS, finsum_eq_single _ 0]
    · simp [Ring.lie_def, mul_apply_eq_comp]
    · intro i hi
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
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
  have cut1 (i : ℕ) (hi : N ≤ i) : ((A.field a)[[n + i]]) b = 0 := hN₁ _ (by omega)
  have cut2 (i : ℕ) (hi : N ≤ i) : ((A.field b)[[r + i]]) c = 0 := hN₂ _ (by omega)
  have cut3 (i : ℕ) (hi : N ≤ i) : ((A.field a)[[m + i]]) c = 0 := hN₃ _ (by omega)
  refine ⟨N, fun i hi ↦ by simp [cut1 i hi], fun i hi ↦ ⟨by simp [cut2 i hi], by simp [cut3 i hi]⟩,
    ?_⟩
  rw [← A.borcherdsLHS_eq_sum cut1, ← A.borcherdsRHS_eq_sum cut2 cut3]
  exact A.borcherds_finsum a b c m n r

/-! ### Skew-symmetry -/

/-- **Skew-symmetry of formal vertex algebra modes**:
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)` for all `a, b : V` and `n : ℤ`. -/
theorem ncoeff_field_apply_skewSymmetry (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a)) := by
  have hbor := A.borcherds_finsum b a A.vacuum (-1) n 0
  have hR :
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field b)[[-1 + n - i]]) (((A.field a)[[(0 : ℤ) + i]]) A.vacuum) -
          (n.negOnePow : ℤ) • ((A.field a)[[n + 0 - i]]) (((A.field b)[[-1 + i]]) A.vacuum))) =
      -((n.negOnePow : ℤ) • (((A.field a)[[n]]) b)) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi
      have h₂ : ((A.field b)[[-1 + (i : ℤ)]]) A.vacuum = 0 :=
        A.ncoeff_field_apply_vacuum_of_nonneg b _ (by omega)
      simp [h₂]
  obtain ⟨N₀, hN₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := ((N₀ : ℤ) - n).toNat
  have hsuppL : (Function.support fun i : ℕ ↦
      Ring.choose (-1 : ℤ) i •
        ((A.field (((A.field b)[[n + i]]) a))[[-1 + (0 : ℤ) - i]]) A.vacuum) ⊆ range M := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [hN₀ (n + i) (by omega)])
  have hsuppR : (Function.support fun i : ℕ ↦
      (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ •
          (A.translation ^ i) (((A.field b)[[n + i]]) a))) ⊆ range M := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [hN₀ (n + i) (by omega)])
  rw [hR, finsum_eq_sum_of_support_subset _ hsuppL] at hbor
  rw [finsum_eq_sum_of_support_subset _ hsuppR]
  have hsq : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one]
  have hmul := congrArg ((-(n.negOnePow : ℤ)) • ·) hbor.symm
  rw [smul_neg, ← neg_smul, neg_neg, smul_smul, hsq, one_smul, smul_sum] at hmul
  rw [hmul]
  refine sum_congr rfl fun i _ ↦ ?_
  have hch : Ring.choose (-1 : ℤ) i = (-1 : ℤ) ^ i := by
    rw [show (-1 : ℤ) = -(1 : ℤ) by ring, Ring.choose_neg, Units.smul_def,
      Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_id,
      show (1 : ℤ) + i - 1 = (i : ℤ) by omega,
      Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one]
  have hidx : -1 + (0 : ℤ) - i = -(i : ℤ) - 1 := by omega
  rw [hch, hidx, A.ncoeff_field_neg_succ_apply_vacuum, smul_smul]
  congr 1
  rw [Int.negOnePow_add, Units.val_mul, Int.coe_negOnePow_natCast, neg_mul]

end Borcherds

end TauCeti.FormalVertexAxioms
