/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.Dong
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.RingTheory.Binomial
import Mathlib.Algebra.Module.Rat

/-!
# Integer field products, skew symmetry, and the Borcherds identity

Let `A : FormalVertexAxioms R V` be a formal vertex algebra over a commutative ring `R`. While the
axioms of `FormalVertexAxioms` are division-free, recovering the negative modes of a field on the
vacuum from powers of the translation operator `T` via `k! • a₍₋ₖ₋₁₎|0⟩ = Tᵏ a` requires cancelling
`k!`, i.e. unique divisibility `[HasUniqueDiv V]` (satisfied in particular by every `ℚ`-module).

Under `[HasUniqueDiv V]`, Dong's lemma (`VertexOperator.IsLocalOfOrder.nthProduct_left`) and
Goddard's uniqueness theorem (`FormalVertexAxioms.eq_field_of_ncoeff_apply_vacuum_eq`) identify the
state–field map on every integer mode product `(a₍ₙ₎ b)` (`n : ℤ`) with the `n`-th field product
`VertexOperator.nthProduct n (A.field a) (A.field b)`. From this we deduce the Borcherds commutator
and iterate formulas, the full three-parameter Borcherds identity, and skew symmetry.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: state–field correspondence
  `Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for all `n : ℤ` under `[HasUniqueDiv V]`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field_eq_sum`: the Borcherds commutator formula
  `⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`, its `m = 0` specialization
  `TauCeti.FormalVertexAxioms.lie_ncoeff_zero_field` (`⁅a₍₀₎, b₍ₙ₎⁆ = (a₍₀₎ b)₍ₙ₎`), and the
  derivation identity `TauCeti.FormalVertexAxioms.ncoeff_zero_field_ncoeff_apply`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply_apply_eq_sum`: the Borcherds iterate formula
  for `((a₍ₙ₎ b)₍q₎) c`.
* `TauCeti.FormalVertexAxioms.borcherds` and `TauCeti.FormalVertexAxioms.exists_borcherds`: the full
  three-parameter Borcherds identity for all `m, n, q : ℤ` under `[HasUniqueDiv V]`, proved by
  two-way Pascal induction on `m` combined with locality vanishing for large `n`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_vacuum` and
  `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_translation_pow`: skew symmetry of `a₍ₙ₎ b`
  in division-free form and in Kac's exponential form over `ℚ`, together with
  `TauCeti.FormalVertexAxioms.ncoeff_zero_field_apply_add_mem_range_translation`
  (`a₍₀₎ b + b₍₀₎ a ∈ LinearMap.range T`).

## References

* R. E. Borcherds, *Vertex algebras, Kac-Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071, §4.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.2 (skew symmetry), §4.5 (Theorem 4.5,
  state–field correspondence for `n`-th products), and §4.8 (Theorem 4.8, the Borcherds identity).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), 143–195, Proposition 3.2.7.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2–3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-! ### State–field correspondence for integer products -/

/-- **State–field correspondence for integer products.** When `V` has unique divisibility
(in particular over any `ℚ`-module), the field of every `n`-th product `a₍ₙ₎ b` (`n : ℤ`) is the
`n`-th field product `nthProduct n (Y(a, z)) (Y(b, z))`. -/
theorem field_ncoeff_apply [HasUniqueDiv V] (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_ncoeff_apply_vacuum_eq (fun c ↦ ?_) fun m ↦ ?_
  · obtain ⟨r₀, h₀⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨r₁, h₁⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨r₂, h₂⟩ := A.exists_isLocalOfOrder b c
    exact ⟨_, h₀.nthProduct_left h₁ h₂ n⟩
  · by_cases hm : 0 ≤ m
    · rw [ncoeff_nthProduct_apply_of_nonneg (A.ncoeff_field_apply_vacuum_of_nonneg a)
        (A.ncoeff_field_apply_vacuum_of_nonneg b) n hm,
        A.ncoeff_field_apply_vacuum_of_nonneg _ m hm]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
      rw [← nsmul_right_inj k.factorial_ne_zero,
        factorial_smul_ncoeff_apply A.translation_vacuum
          (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n) k,
        A.factorial_smul_ncoeff_field_apply_vacuum,
        ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
          (A.ncoeff_field_apply_vacuum_of_nonneg b) n,
        A.ncoeff_neg_one_field_apply_vacuum]

/-- The field of the `(-1)`-st product `a₍₋₁₎ b` is the normal-ordered product `:Y(a,z) Y(b,z):`. -/
theorem field_ncoeff_neg_one_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  simp [A.field_ncoeff_apply]

/-- For `n : ℕ`, the field of `a₍ₙ₎ b` is `nonnegResidueProduct n (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_natCast_apply [HasUniqueDiv V] (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- The field of the `0`-th product `a₍₀₎ b` is `nonnegResidueProduct 0 (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_zero_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[0]]) b) = nonnegResidueProduct 0 (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_zero]

/-! ### Borcherds commutator and iterate formulas -/

/-- **Borcherds commutator formula.** For any cutoff `N : ℕ` above which `a₍ⱼ₎ b = 0`,
`⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`. -/
theorem lie_ncoeff_field_eq_sum [HasUniqueDiv V] (a b : V) (m n : ℤ) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → ((A.field a)[[(j : ℤ)]]) b = 0) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + n - j]] := by
  obtain ⟨L, hL⟩ := A.exists_isLocalOfOrder a b
  rw [(hL.mono (le_max_right N L)).lie_ncoeff_eq_sum_nthProduct m n]
  simp_rw [← A.field_ncoeff_apply]
  symm
  refine sum_subset (range_mono (le_max_left N L)) fun j _ hj ↦ ?_
  simp [hN j (by simp only [mem_range] at hj; omega)]

/-- The `0`-th mode `a₍₀₎` commutes with `Y(b, z)` by `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`. -/
@[simp]
theorem lie_ncoeff_zero_field [HasUniqueDiv V] (a b : V) (n : ℤ) :
    ⁅(A.field a)[[0]], (A.field b)[[n]]⁆ = (A.field (((A.field a)[[0]]) b))[[n]] := by
  obtain ⟨N, hN⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  rw [A.lie_ncoeff_field_eq_sum a b 0 n (N := N + 1) (fun j hj ↦ hN j (by omega)), sum_range_succ']
  simp

/-- The `0`-th mode `a₍₀₎` is a derivation of every `n`-th product (`n : ℤ`):
`a₍₀₎ (b₍ₙ₎ c) = (a₍₀₎ b)₍ₙ₎ c + b₍ₙ₎ (a₍₀₎ c)`. At `n = 0` this is the Leibniz identity for
`₍₀₎`. -/
theorem ncoeff_zero_field_ncoeff_apply [HasUniqueDiv V] (a b c : V) (n : ℤ) :
    ((A.field a)[[0]]) (((A.field b)[[n]]) c) =
      ((A.field (((A.field a)[[0]]) b))[[n]]) c +
        ((A.field b)[[n]]) (((A.field a)[[0]]) c) := by
  have h := LinearMap.congr_fun (A.lie_ncoeff_zero_field a b n) c
  rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    sub_eq_iff_eq_add] at h

/-- **Borcherds iterate formula.** Mode expansion of `((a₍ₙ₎ b)₍q₎) c` for any `n, q : ℤ`. -/
theorem ncoeff_field_ncoeff_apply_apply_eq_sum [HasUniqueDiv V] (a b c : V) (n q : ℤ) {K : ℕ}
    (ha : ∀ j : ℕ, K ≤ j → ((A.field a)[[(j : ℤ)]]) c = 0)
    (hb : ∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0) :
    ((A.field (((A.field a)[[n]]) b))[[q]]) c =
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        (((A.field a)[[n - j]]) (((A.field b)[[q + j]]) c) -
          Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[(j : ℤ)]]) c)) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply_eq_sum n (A.field a) (A.field b) q c ha hb]

/-! ### The full Borcherds identity -/

private def borcherdsLhs₁ (a b c : V) (m n q : ℤ) : V :=
  ∑ᶠ j : ℕ, (-1 : ℤ) ^ j • Ring.choose n j •
    ((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c)

private def borcherdsLhs₂ (a b c : V) (m n q : ℤ) : V :=
  ∑ᶠ j : ℕ, (-1 : ℤ) ^ j • Ring.choose n j •
    (Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c))

private def borcherdsRhs (a b c : V) (m n q : ℤ) : V :=
  ∑ᶠ j : ℕ, Ring.choose m j • ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c

private def borcherdsDelta (a b c : V) (m n q : ℤ) : V :=
  (A.borcherdsLhs₁ a b c m n q - A.borcherdsLhs₂ a b c m n q) - A.borcherdsRhs a b c m n q

private theorem borcherdsLhs₁_eq_sum (a b c : V) (m n q : ℤ) {K : ℕ}
    (hb : ∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0) :
    A.borcherdsLhs₁ a b c m n q =
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        ((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c) :=
  finsum_eq_sum_range_of_forall_eq_zero fun j hj ↦ by simp [hb j hj]

private theorem borcherdsLhs₂_eq_sum (a b c : V) (m n q : ℤ) {K : ℕ}
    (ha : ∀ j : ℕ, K ≤ j → ((A.field a)[[m + j]]) c = 0) :
    A.borcherdsLhs₂ a b c m n q =
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        (Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c)) :=
  finsum_eq_sum_range_of_forall_eq_zero fun j hj ↦ by simp [ha j hj]

private theorem borcherdsRhs_eq_sum (a b c : V) (m n q : ℤ) {K : ℕ}
    (hab : ∀ j : ℕ, K ≤ j → ((A.field a)[[n + j]]) b = 0) :
    A.borcherdsRhs a b c m n q =
      ∑ j ∈ range K, Ring.choose m j •
        ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c :=
  finsum_eq_sum_range_of_forall_eq_zero fun j hj ↦ by simp [hab j hj]

private theorem borcherdsLhs₁_succ (a b c : V) (m n q : ℤ) :
    A.borcherdsLhs₁ a b c (m + 1) n q =
      A.borcherdsLhs₁ a b c m (n + 1) q + A.borcherdsLhs₁ a b c m n (q + 1) := by
  obtain ⟨P, hP⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  let K := P + q.natAbs
  have hb₀ (j : ℕ) (hj : K ≤ j) : ((A.field b)[[q + j]]) c = 0 := hP _ (by omega)
  have hb₁ (j : ℕ) (hj : K + 1 ≤ j) : ((A.field b)[[q + j]]) c = 0 := hb₀ j (by omega)
  have hb₂ (j : ℕ) (hj : K ≤ j) : ((A.field b)[[(q + 1) + j]]) c = 0 := by
    simpa only [show (q + 1) + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by push_cast; ring] using
      hb₀ (j + 1) (by omega)
  rw [A.borcherdsLhs₁_eq_sum a b c (m + 1) n q hb₁,
    A.borcherdsLhs₁_eq_sum a b c m (n + 1) q hb₁,
    A.borcherdsLhs₁_eq_sum a b c m n (q + 1) hb₂,
    sum_range_succ' _ K, sum_range_succ' _ K]
  simp only [Nat.cast_zero, pow_zero, Ring.choose_zero_right, one_smul, sub_zero, add_zero]
  rw [show m + (n + 1) = (m + 1) + n by ring, add_right_comm _ _ (∑ k ∈ range K, _),
    ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  have hidx₁ : (m + 1) + n - ((j + 1 : ℕ) : ℤ) = m + n - j := by push_cast; ring
  have hidx₃ : (q + 1) + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hidx₁, hidx₃]
  simp only [Ring.choose_succ_succ n j, pow_succ' (-1 : ℤ) j, mul_smul, neg_one_smul, add_smul,
    smul_add]
  abel

private theorem borcherdsLhs₂_succ (a b c : V) (m n q : ℤ) :
    A.borcherdsLhs₂ a b c (m + 1) n q =
      A.borcherdsLhs₂ a b c m (n + 1) q + A.borcherdsLhs₂ a b c m n (q + 1) := by
  obtain ⟨P, hP⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let K := P + m.natAbs
  have ha₀ (j : ℕ) (hj : K ≤ j) : ((A.field a)[[m + j]]) c = 0 := hP _ (by omega)
  have ha₁ (j : ℕ) (hj : K + 1 ≤ j) : ((A.field a)[[m + j]]) c = 0 := ha₀ j (by omega)
  have ha₂ (j : ℕ) (hj : K ≤ j) : ((A.field a)[[(m + 1) + j]]) c = 0 := by
    simpa only [show (m + 1) + (j : ℤ) = m + ((j + 1 : ℕ) : ℤ) by push_cast; ring] using
      ha₀ (j + 1) (by omega)
  rw [A.borcherdsLhs₂_eq_sum a b c (m + 1) n q ha₂,
    A.borcherdsLhs₂_eq_sum a b c m (n + 1) q ha₁,
    A.borcherdsLhs₂_eq_sum a b c m n (q + 1) ha₁,
    sum_range_succ' _ K, sum_range_succ' _ K]
  simp only [Int.negOnePow_succ, Units.neg_smul, smul_neg, Nat.cast_zero, pow_zero,
    Ring.choose_zero_right, one_smul, sub_zero, add_zero]
  have hcancel (x y z : V) : (x + -z) + (y + z) = x + y := by abel
  rw [show (n + 1) + q = n + (q + 1) by ring, hcancel, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  have hidx₁ : (m + 1) + (j : ℤ) = m + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  have hidx₃ : n + (q + 1) - ((j + 1 : ℕ) : ℤ) = n + q - j := by push_cast; ring
  rw [hidx₁, hidx₃]
  simp only [Ring.choose_succ_succ n j, pow_succ' (-1 : ℤ) j, mul_smul, neg_one_smul, add_smul,
    smul_add]
  abel

private theorem borcherdsRhs_succ (a b c : V) (m n q : ℤ) :
    A.borcherdsRhs a b c (m + 1) n q =
      A.borcherdsRhs a b c m (n + 1) q + A.borcherdsRhs a b c m n (q + 1) := by
  obtain ⟨P, hP⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let K := P + n.natAbs
  have hab₀ (j : ℕ) (hj : K ≤ j) : ((A.field a)[[n + j]]) b = 0 := hP _ (by omega)
  have hab₁ (j : ℕ) (hj : K + 1 ≤ j) : ((A.field a)[[n + j]]) b = 0 := hab₀ j (by omega)
  have hab₂ (j : ℕ) (hj : K ≤ j) : ((A.field a)[[(n + 1) + j]]) b = 0 := by
    simpa only [show (n + 1) + (j : ℤ) = n + ((j + 1 : ℕ) : ℤ) by push_cast; ring] using
      hab₀ (j + 1) (by omega)
  rw [A.borcherdsRhs_eq_sum a b c (m + 1) n q hab₁,
    A.borcherdsRhs_eq_sum a b c m (n + 1) q hab₂,
    A.borcherdsRhs_eq_sum a b c m n (q + 1) hab₁,
    sum_range_succ' _ K, sum_range_succ' _ K]
  simp only [Nat.cast_zero, Ring.choose_zero_right, one_smul, sub_zero, add_zero]
  rw [show (m + 1) + q = m + (q + 1) by ring, ← add_assoc (∑ j ∈ range K, _), ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  have hidx₁ : (n + 1) + (j : ℤ) = n + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  have hidx₃ : m + (q + 1) - ((j + 1 : ℕ) : ℤ) = m + q - j := by push_cast; ring
  rw [hidx₁, hidx₃, Ring.choose_succ_succ m j, add_smul]

private theorem borcherdsDelta_succ (a b c : V) (m n q : ℤ) :
    A.borcherdsDelta a b c (m + 1) n q =
      A.borcherdsDelta a b c m (n + 1) q + A.borcherdsDelta a b c m n (q + 1) := by
  simp only [borcherdsDelta, borcherdsLhs₁_succ, borcherdsLhs₂_succ, borcherdsRhs_succ]
  abel

private theorem borcherdsDelta_zero_left [HasUniqueDiv V] (a b c : V) (n q : ℤ) :
    A.borcherdsDelta a b c 0 n q = 0 := by
  obtain ⟨Pₐ, hPₐ⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_b, hPb⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_ab, hPab⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let K := max Pₐ (max P_b P_ab) + q.natAbs + n.natAbs
  have ha (j : ℕ) (hj : K + 1 ≤ j) : ((A.field a)[[(j : ℤ)]]) c = 0 := hPₐ _ (by omega)
  have hb (j : ℕ) (hj : K + 1 ≤ j) : ((A.field b)[[q + j]]) c = 0 := hPb _ (by omega)
  have hab (j : ℕ) (hj : K + 1 ≤ j) : ((A.field a)[[n + j]]) b = 0 := hPab _ (by omega)
  have hrhs : A.borcherdsRhs a b c 0 n q = ((A.field (((A.field a)[[n]]) b))[[q]]) c := by
    rw [A.borcherdsRhs_eq_sum a b c 0 n q hab, sum_range_succ']
    simp
  rw [borcherdsDelta, A.borcherdsLhs₁_eq_sum a b c 0 n q hb,
    A.borcherdsLhs₂_eq_sum a b c 0 n q (by simpa only [zero_add] using ha),
    hrhs, A.ncoeff_field_ncoeff_apply_apply_eq_sum a b c n q ha hb, ← sum_sub_distrib]
  refine sub_eq_zero.mpr (sum_congr rfl fun j _ ↦ ?_)
  rw [zero_add, zero_add, ← smul_sub, ← smul_sub]

private theorem borcherdsLhs₁_natCast (a b c : V) (m q : ℤ) (M : ℕ) :
    A.borcherdsLhs₁ a b c m (M : ℤ) q =
      ∑ x ∈ antidiagonal M, M.choose x.1 • (-1 : ℤ) ^ x.2 •
        ((A.field a)[[m + x.1]]) (((A.field b)[[q + x.2]]) c) := by
  rw [borcherdsLhs₁, finsum_eq_sum_range_of_forall_eq_zero (K := M + 1) fun j hj ↦ by
      simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hj],
    ← FormalDistribution.sum_antidiagonal_choose_eq_sum_range_succ_left M
      (fun x y ↦ ((A.field a)[[x]]) (((A.field b)[[y]]) c)) m q]

private theorem borcherdsLhs₂_natCast (a b c : V) (m q : ℤ) (M : ℕ) :
    A.borcherdsLhs₂ a b c m (M : ℤ) q =
      ∑ x ∈ antidiagonal M, M.choose x.1 • (-1 : ℤ) ^ x.2 •
        ((A.field b)[[q + x.2]]) (((A.field a)[[m + x.1]]) c) := by
  rw [borcherdsLhs₂, finsum_eq_sum_range_of_forall_eq_zero (K := M + 1) fun j hj ↦ by
      simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hj],
    ← FormalDistribution.sum_antidiagonal_choose_eq_sum_range_succ_right M
      (fun x y ↦ ((A.field b)[[y]]) (((A.field a)[[x]]) c)) m q]

private theorem borcherdsDelta_natCast_mid (a b c : V) (m q : ℤ) {M : ℕ}
    (hloc : (A.field a).IsLocalOfOrder (A.field b) M)
    (hab : ∀ j : ℕ, ((A.field a)[[(M : ℤ) + j]]) b = 0) :
    A.borcherdsDelta a b c m (M : ℤ) q = 0 := by
  have hrhs : A.borcherdsRhs a b c m (M : ℤ) q = 0 := by
    rw [A.borcherdsRhs_eq_sum a b c m (M : ℤ) q (K := 0) (fun j _ ↦ hab j), sum_range_zero]
  have hlhs : A.borcherdsLhs₁ a b c m (M : ℤ) q - A.borcherdsLhs₂ a b c m (M : ℤ) q = 0 := by
    have h₀ := LinearMap.congr_fun (isLocalOfOrder_iff.mp hloc m q) c
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, LinearMap.zero_apply, smul_sub, sum_sub_distrib] at h₀
    rwa [A.borcherdsLhs₁_natCast, A.borcherdsLhs₂_natCast]
  rw [borcherdsDelta, hlhs, hrhs, sub_zero]

private theorem borcherdsDelta_eq_zero [HasUniqueDiv V] (a b c : V) (m n q : ℤ) :
    A.borcherdsDelta a b c m n q = 0 := by
  obtain ⟨N₁, hN₁⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨N₂, hN₂⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let N₀ := max N₁ N₂
  have hlarge (m' q' : ℤ) {M : ℕ} (hM : N₀ ≤ M) : A.borcherdsDelta a b c m' (M : ℤ) q' = 0 :=
    A.borcherdsDelta_natCast_mid a b c m' q' (hN₁.mono (le_trans (le_max_left N₁ N₂) hM))
      fun j ↦ hN₂ _ (by have := le_trans (le_max_right N₁ N₂) hM; omega)
  suffices ∀ m' n' q' : ℤ, A.borcherdsDelta a b c m' n' q' = 0 from this m n q
  intro m'
  induction m' using Int.induction_on with
  | zero => exact A.borcherdsDelta_zero_left a b c
  | succ k ih =>
    intro n' q'
    rw [A.borcherdsDelta_succ, ih, ih, add_zero]
  | pred k ih =>
    have hshift (s : ℕ) : ∀ n' q' : ℤ,
        A.borcherdsDelta a b c (-(k : ℤ) - 1) n' q' =
          (-1 : ℤ) ^ s • A.borcherdsDelta a b c (-(k : ℤ) - 1) (n' + s) (q' - s) := by
      induction s with
      | zero => intro n' q'; simp
      | succ s ihs =>
        intro n' q'
        have hstep := A.borcherdsDelta_succ a b c (-(k : ℤ) - 1) n' (q' - 1)
        rw [sub_add_cancel, ih n' (q' - 1), sub_add_cancel] at hstep
        rw [eq_neg_of_add_eq_zero_right hstep.symm, ihs (n' + 1) (q' - 1), pow_succ', mul_smul,
          neg_one_smul]
        push_cast
        rw [show n' + 1 + (s : ℤ) = n' + ((s : ℤ) + 1) by ring,
          show q' - 1 - (s : ℤ) = q' - ((s : ℤ) + 1) by ring]
    intro n' q'
    let s : ℕ := ((N₀ : ℤ) - n').toNat
    let M : ℕ := (n' + (s : ℤ)).toNat
    rw [hshift s n' q', show n' + (s : ℤ) = (M : ℤ) by omega, hlarge _ _ (by omega), smul_zero]

/-- **The Borcherds identity.** For any states `a, b, c : V`, any modes `m, n, q : ℤ`, and any
cutoffs `K, L : ℕ` with `a₍ₘ₊ⱼ₎ c = 0` and `b₍q₊ⱼ₎ c = 0` for `K ≤ j` and `a₍ₙ₊ⱼ₎ b = 0` for
`L ≤ j`,
`∑_{j < K} (-1)ʲ (n choose j) (a₍ₘ₊ₙ₋ⱼ₎ (b₍q₊ⱼ₎ c) - (-1)ⁿ b₍ₙ₊q₋ⱼ₎ (a₍ₘ₊ⱼ₎ c)) =
  ∑_{j < L} (m choose j) ((a₍ₙ₊ⱼ₎ b)₍ₘ₊q₋ⱼ₎ c)`. -/
theorem borcherds [HasUniqueDiv V] (a b c : V) (m n q : ℤ) {K L : ℕ}
    (ha : ∀ j : ℕ, K ≤ j → ((A.field a)[[m + j]]) c = 0)
    (hb : ∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0)
    (hab : ∀ j : ℕ, L ≤ j → ((A.field a)[[n + j]]) b = 0) :
    ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        (((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c) -
          Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c)) =
      ∑ j ∈ range L, Ring.choose m j •
        ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c := by
  have h := sub_eq_zero.mp (A.borcherdsDelta_eq_zero a b c m n q)
  rw [A.borcherdsLhs₁_eq_sum a b c m n q hb, A.borcherdsLhs₂_eq_sum a b c m n q ha,
    A.borcherdsRhs_eq_sum a b c m n q hab, ← sum_sub_distrib] at h
  rw [← h]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← smul_sub, ← smul_sub]

/-- **Existence form of the Borcherds identity**, producing a common finite cutoff `K : ℕ` for all
three mode sequences from field truncation. -/
theorem exists_borcherds [HasUniqueDiv V] (a b c : V) (m n q : ℤ) :
    ∃ K : ℕ,
      (∀ j : ℕ, K ≤ j → ((A.field a)[[m + j]]) c = 0) ∧
      (∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0) ∧
      (∀ j : ℕ, K ≤ j → ((A.field a)[[n + j]]) b = 0) ∧
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
          (((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c) -
            Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c)) =
        ∑ j ∈ range K, Ring.choose m j •
          ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c := by
  obtain ⟨Pₐ, hPₐ⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_b, hPb⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_ab, hPab⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  have ha : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field a)[[m + j]]) c = 0 := fun j hj ↦ hPₐ _ (by omega)
  have hb : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field b)[[q + j]]) c = 0 := fun j hj ↦ hPb _ (by omega)
  have hab : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field a)[[n + j]]) b = 0 := fun j hj ↦ hPab _ (by omega)
  exact ⟨_, ha, hb, hab, A.borcherds a b c m n q ha hb hab⟩

/-! ### Skew symmetry -/

/-- **Skew symmetry (division-free form).** Over any module with unique divisibility, for any
cutoff `K : ℕ` above which `b₍ₙ₊ⱼ₎ a = 0`,
`a₍ₙ₎ b = ∑_{j < K} (-1)^{n + j + 1} (b₍ₙ₊ⱼ₎ a)₍₋ⱼ₋₁₎|0⟩`. -/
theorem ncoeff_field_apply_eq_sum_vacuum [HasUniqueDiv V] (a b : V) (n : ℤ) {K : ℕ}
    (hba : ∀ j : ℕ, K ≤ j → ((A.field b)[[n + j]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ j ∈ range K, Int.negOnePow (n + j + 1) •
        ((A.field (((A.field b)[[n + j]]) a))[[-j - 1]]) A.vacuum := by
  have h := A.borcherds b a A.vacuum (-1) n 0 (K := 1) (L := K)
    (fun j hj ↦ A.ncoeff_field_apply_vacuum_of_nonneg b _ (by omega))
    (fun j _ ↦ A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega)) hba
  simp only [range_one, sum_singleton, Nat.cast_zero, pow_zero, Ring.choose_zero_right, one_smul,
    sub_zero, add_zero, A.ncoeff_field_apply_vacuum_of_nonneg a 0 le_rfl, map_zero,
    A.ncoeff_neg_one_field_apply_vacuum, zero_sub] at h
  have hinv := congrArg (fun x : V ↦ -(Int.negOnePow n • x)) h
  simp only [smul_neg, neg_neg, smul_smul, Int.units_mul_self, one_smul, smul_sum,
    ← sum_neg_distrib] at hinv
  rw [hinv]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [Ring.choose_neg_one, ← Int.coe_negOnePow_natCast, ← Units.smul_def,
    show (-1 : ℤ) - j = -(j : ℤ) - 1 by ring, Int.negOnePow_succ, Units.neg_smul,
    Int.negOnePow_add, mul_smul]

/-- **Skew symmetry (`e^{zT}` form).** Over a `ℚ`-module, for any cutoff `K : ℕ` above which
`b₍ₙ₊ⱼ₎ a = 0`, `a₍ₙ₎ b = ∑_{j < K} (-1)^{n + j + 1} (j!)⁻¹ • Tʲ (b₍ₙ₊ⱼ₎ a)`. -/
theorem ncoeff_field_apply_eq_sum_translation_pow [Module ℚ V] (a b : V) (n : ℤ) {K : ℕ}
    (hba : ∀ j : ℕ, K ≤ j → ((A.field b)[[n + j]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ j ∈ range K, Int.negOnePow (n + j + 1) • (j.factorial : ℚ)⁻¹ •
        (A.translation ^ j) (((A.field b)[[n + j]]) a) := by
  have : HasUniqueDiv V := .of_module_rat V
  rw [A.ncoeff_field_apply_eq_sum_vacuum a b n hba]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [A.ncoeff_field_apply_vacuum_neg]

/-- Over a `ℚ`-module, the `0`-th product is skew-symmetric modulo `T(V)`:
`a₍₀₎ b + b₍₀₎ a ∈ LinearMap.range A.translation`. Together with `ncoeff_zero_field_ncoeff_apply`,
`ncoeff_field_translation`, and `translation_ncoeff_apply`, this supplies the identities needed for
the induced Lie bracket on `V / T(V)`. -/
theorem ncoeff_zero_field_apply_add_mem_range_translation [Module ℚ V] (a b : V) :
    ((A.field a)[[0]]) b + ((A.field b)[[0]]) a ∈ LinearMap.range A.translation := by
  obtain ⟨P, hP⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  rw [A.ncoeff_field_apply_eq_sum_translation_pow a b 0 (K := P + 1)
      (fun j hj ↦ by simpa using hP j (by omega)),
    sum_range_succ']
  simp only [Nat.cast_zero, add_zero, zero_add, Int.negOnePow_one, Units.neg_smul, one_smul,
    Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_apply_eq_self, neg_add_cancel_right]
  refine Submodule.sum_mem (LinearMap.range A.translation) fun j _ ↦ ?_
  refine ⟨Int.negOnePow (((j + 1 : ℕ) : ℤ) + 1) • ((j + 1).factorial : ℚ)⁻¹ •
      (A.translation ^ j) (((A.field b)[[(j + 1 : ℕ)]]) a), ?_⟩
  simp only [Units.smul_def]
  rw [map_zsmul, map_rat_smul, pow_succ', mul_apply_eq_comp]

end FormalVertexAxioms

end TauCeti
