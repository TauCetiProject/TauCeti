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

/-- Without division, `k!` times the `k`-th Hasse derivative of `Y(a, z)` is `Y(Tᵏ a, z)`. -/
theorem factorial_smul_hasseDeriv_field (a : V) (k : ℕ) :
    k.factorial • hasseDeriv k (A.field a) = A.field ((A.translation ^ k) a) := by
  rw [← iterate_derivative_eq_factorial_smul_hasseDeriv, A.field_pow_translation]

/-- The field of `a₍₋ₖ₋₁₎|0⟩` is the `k`-th Hasse derivative of `Y(a, z)`. -/
@[simp]
theorem field_ncoeff_neg_succ_apply_vacuum [HasUniqueDiv V] (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) = hasseDeriv k (A.field a) :=
  (A.eq_field_of_lie_translation_ncoeff
    (fun c ↦ let ⟨N, hN⟩ := A.exists_isLocalOfOrder a c; ⟨N + k, hN.hasseDeriv_left k⟩)
    (lie_ncoeff_hasseDeriv (A.lie_translation_ncoeff a) k)
    (ncoeff_neg_one_hasseDeriv k (A.field a) ▸ rfl)).symm

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply [HasUniqueDiv V] (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_natCast_sub_one]

/-- **Borcherds commutator formula** in `finsum` form, independent of a chosen locality bound. -/
theorem lie_ncoeff_field_finsum [HasUniqueDiv V] (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ i : ℕ, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  obtain ⟨N, h⟩ := A.exists_isLocalOfOrder a b
  have hN (j : ℕ) (hj : N ≤ j) : ((A.field a)[[(j : ℤ)]]) b = 0 :=
    A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h hj
  rw [A.lie_ncoeff_field_eq_sum a b m n hN, eq_comm]
  exact TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hN i hi]

/-- **Mode iterate / associativity formula** (`m = 0` case of the Borcherds identity) in `finsum`
form: `((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`
for all `a, b, c : V` and all integers `n, r : ℤ`. -/
theorem ncoeff_field_ncoeff_apply [HasUniqueDiv V] (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply]

/-- **Skew symmetry (division-free `finsum` form):**
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (b₍ₙ₊ᵢ₎ a)₍₋ᵢ₋₁₎|0⟩`. -/
theorem ncoeff_field_apply_skewSymmetry_vacuum [HasUniqueDiv V] (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        ((A.field (((A.field b)[[n + i]]) a))[[-(i : ℤ) - 1]]) A.vacuum := by
  obtain ⟨K, hK⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := ((K : ℤ) - n).toNat
  have hba (j : ℕ) (hj : M ≤ j) : ((A.field b)[[n + j]]) a = 0 := hK (n + j) (by omega)
  rw [TauCeti.finsum_eq_sum_range_of_forall_eq_zero (K := M) fun i hi ↦ by
      simp [hba i hi],
    A.ncoeff_field_apply_eq_sum_vacuum a b n hba]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Int.negOnePow_add, Int.negOnePow_add, Units.smul_def, Units.val_mul, Units.val_mul,
    Int.negOnePow_one, Units.val_neg, Units.val_one, mul_neg_one,
    show -(i : ℤ) - 1 = -i - 1 by omega]

/-- **Skew symmetry (`ℚ`-algebra `finsum` form):**
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)`. -/
theorem ncoeff_field_apply_skewSymmetry [Algebra ℚ R] (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a)) := by
  let : Module ℚ V := Module.compHom V (algebraMap ℚ R)
  have : HasUniqueDiv V := .of_module_rat V
  rw [A.ncoeff_field_apply_skewSymmetry_vacuum a b n]
  exact finsum_congr fun i ↦ by rw [A.ncoeff_field_neg_succ_apply_vacuum]

end FormalVertexAxioms

end TauCeti

/-! ### Field-level Borcherds identity over a commutative ring -/

namespace VertexOperator

section BorcherdsField

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private def borcherdsLHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v

private def borcherdsRHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    ((A[[m + n - i]]) ((B[[r + i]]) v) -
      (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v))

private theorem borcherdsLHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hM : ∀ i : ℕ, M ≤ i → nthProduct (n + i) A B = 0) :
    borcherdsLHS A B v m n r =
      ∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v :=
  TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hM i hi]

private theorem borcherdsRHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hB : ∀ i : ℕ, M ≤ i → (B[[r + i]]) v = 0) (hA : ∀ i : ℕ, M ≤ i → (A[[m + i]]) v = 0) :
    borcherdsRHS A B v m n r =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) :=
  TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hB i hi, hA i hi]

private theorem borcherdsLHS_add_one {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    borcherdsLHS A B v (m + 1) n r =
      borcherdsLHS A B v m n (r + 1) + borcherdsLHS A B v m (n + 1) r := by
  let M := ((N : ℤ) - n).toNat
  have hcut (q : ℤ) (hq : n ≤ q) (K : ℕ) (hK : M ≤ K) :
      ∀ i : ℕ, K ≤ i → nthProduct (q + i) A B = 0 := fun i hi ↦ by
    rw [nthProduct_of_nonneg (by omega)]; exact h.nonnegResidueProduct_eq_zero (by omega)
  rw [borcherdsLHS_eq_sum (M := M + 1) (hcut n le_rfl (M + 1) (by omega)),
    borcherdsLHS_eq_sum (M := M + 1) (hcut n le_rfl (M + 1) (by omega)),
    borcherdsLHS_eq_sum (M := M) (hcut (n + 1) (by omega) M le_rfl),
    TauCeti.Ring.sum_range_choose_add_one_smul (R := ℤ) M m
      (fun i ↦ ((nthProduct (n + i) A B)[[m + 1 + r - i]]) v)]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by rw [show m + 1 + r - (i : ℤ) = m + (r + 1) - i by omega]
  · exact sum_congr rfl fun i _ ↦ by
      rw [show n + ((i + 1 : ℕ) : ℤ) = n + 1 + i by omega,
        show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + r - i by omega]

private theorem borcherdsRHS_add_one (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v (m + 1) n r =
      borcherdsRHS A B v m n (r + 1) + borcherdsRHS A B v m (n + 1) r := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M := max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat
  rw [borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    borcherdsRHS_eq_sum (M := M) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  simp only [smul_sub, sum_sub_distrib]; rw [← add_sub_add_comm]; congr 1
  · rw [TauCeti.Ring.sum_range_neg_one_pow_mul_choose_smul (R := ℤ) M n
      (fun i ↦ (A[[m + 1 + n - i]]) ((B[[r + i]]) v))]
    congr 1
    · exact sum_congr rfl fun i _ ↦ by
        rw [show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by omega,
          show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by omega]
    · exact sum_congr rfl fun i _ ↦ by rw [show m + 1 + n - (i : ℤ) = m + (n + 1) - i by omega]
  · have h₂ := eq_sub_of_add_eq (TauCeti.Ring.sum_range_neg_one_pow_mul_choose_smul (R := ℤ) M n
      (fun i ↦ (n.negOnePow : ℤ) • (B[[n + (r + 1) - i]]) ((A[[m + i]]) v))).symm
    rw [sum_range_succ _ M, hN₃ (m + M) (by omega), map_zero, smul_zero, smul_zero, add_zero] at h₂
    rw [sum_range_succ _ M, hN₃ (m + 1 + M) (by omega), map_zero, smul_zero, smul_zero, add_zero,
      sum_congr rfl fun i _ ↦ show _ = ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          (B[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]]) ((A[[m + ((i + 1 : ℕ) : ℤ)]]) v) by
        rw [show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by omega,
          show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by omega],
      h₂, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1; exact sum_congr rfl fun i _ ↦ by
      simp only [Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg,
        show n + 1 + r - (i : ℤ) = n + (r + 1) - i by omega]

private theorem borcherds_eq_of_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {v : V}
    (h0n : ∀ q s : ℤ, borcherdsLHS A B v 0 q s = borcherdsRHS A B v 0 q s)
    (hm0 : ∀ p s : ℤ, borcherdsLHS A B v p 0 s = borcherdsRHS A B v p 0 s)
    (m n r : ℤ) : borcherdsLHS A B v m n r = borcherdsRHS A B v m n r := by
  let D (p q s : ℤ) := borcherdsLHS A B v p q s - borcherdsRHS A B v p q s
  have hrec (p q s : ℤ) : D (p + 1) q s = D p q (s + 1) + D p (q + 1) s := by
    simp only [D, borcherdsLHS_add_one h, borcherdsRHS_add_one]; abel
  have hm0' (k : ℕ) : ∀ q s : ℤ, D k q s = 0 := by
    induction k with
    | zero => exact fun q s ↦ sub_eq_zero.mpr (h0n q s)
    | succ k ih => exact fun q s ↦ by rw [Nat.cast_succ, hrec, ih, ih, add_zero]
  have hn0' (l : ℕ) : ∀ p s : ℤ, D p l s = 0 := by
    induction l with
    | zero => exact fun p s ↦ sub_eq_zero.mpr (hm0 p s)
    | succ l ih =>
      intro p s
      have h' := hrec p l s; rw [ih (p + 1) s, ih p (s + 1), zero_add, eq_comm] at h'
      simpa [Nat.cast_succ] using h'
  have hneg (k : ℕ) : ∀ (l : ℕ) (s : ℤ), D (-(k : ℤ)) (-(l : ℤ)) s = 0 := by
    induction k with
    | zero => exact fun l s ↦ by simpa [D] using sub_eq_zero.mpr (h0n _ s)
    | succ k ihk =>
      intro l; induction l with
      | zero => exact fun s ↦ by simpa [D] using sub_eq_zero.mpr (hm0 _ s)
      | succ l ihl =>
        intro s
        have h' := hrec (-((k + 1 : ℕ) : ℤ)) (-((l + 1 : ℕ) : ℤ)) (s - 1)
        rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by omega,
          show -((l + 1 : ℕ) : ℤ) + 1 = -(l : ℤ) by omega, sub_add_cancel,
          ihk (l + 1) (s - 1), ihl (s - 1), add_zero] at h'; exact h'.symm
  suffices hD : D m n r = 0 from sub_eq_zero.mp hD
  rcases le_or_gt 0 m with hm | hm; · lift m to ℕ using hm; exact hm0' m n r
  rcases le_or_gt 0 n with hn | hn; · lift n to ℕ using hn; exact hn0' n m r
  simpa only [show -((-m).toNat : ℤ) = m by omega, show -((-n).toNat : ℤ) = n by omega] using
    hneg (-m).toNat (-n).toNat r

/-- **Field-level Borcherds identity** in `finsum` form, over any commutative ring: for mutually
local fields `A, B` (local of order `N`), any `v : V`, and all integers `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) ((A_{(n+i)} B)_{(m+r-i)}) v =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (A₍ₘ₊ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ v) - (-1)ⁿ B₍ₙ₊ᵣ₋ᵢ₎ (A₍ₘ₊ᵢ₎ v))`. -/
theorem IsLocalOfOrder.borcherds_finsum {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  refine borcherds_eq_of_zero h (fun q s ↦ ?_) (fun p s ↦ ?_) m n r
  · rw [borcherdsLHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    simpa [borcherdsRHS] using ncoeff_nthProduct_apply A B q s v
  · rw [borcherdsRHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    have hL : borcherdsLHS A B v p 0 s = (⁅A[[p]], B[[s]]⁆) v := by
      rw [h.lie_ncoeff p s, LinearMap.sum_apply,
        borcherdsLHS_eq_sum (M := N) fun i hi ↦ by simpa using h.nonnegResidueProduct_eq_zero hi]
      exact sum_congr rfl fun i _ ↦ by
        simp only [zero_add, nthProduct_natCast, LinearMap.smul_apply]
    simpa [Ring.lie_def, mul_apply_eq_comp] using hL

/-- **Field-level Borcherds identity** with explicit finite cutoff `M`, over any commutative ring:
all three mode expressions vanish for `i ≥ M`, and the finite sums over `Finset.range M` agree. -/
theorem IsLocalOfOrder.borcherds {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    ∃ M : ℕ,
      (∀ i : ℕ, M ≤ i → ((nthProduct (n + i) A B)[[m + r - i]]) v = 0) ∧
      (∀ i : ℕ, M ≤ i →
        (A[[m + n - i]]) ((B[[r + i]]) v) = 0 ∧ (B[[n + r - i]]) ((A[[m + i]]) v) = 0) ∧
      (∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
        ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A[[m + n - i]]) ((B[[r + i]]) v) -
            (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M := max ((N : ℤ) - n).toNat (max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat)
  have hcut (i : ℕ) (hi : M ≤ i) : nthProduct (n + i) A B = 0 := by
    rw [nthProduct_of_nonneg (by omega)]; exact h.nonnegResidueProduct_eq_zero (by omega)
  refine ⟨M, fun i hi ↦ by simp [hcut i hi],
    fun i hi ↦ ⟨by simp [hN₂ (r + i) (by omega)], by simp [hN₃ (m + i) (by omega)]⟩, ?_⟩
  rw [← borcherdsLHS_eq_sum hcut,
    ← borcherdsRHS_eq_sum (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  exact h.borcherds_finsum v m n r

end BorcherdsField

end VertexOperator

namespace TauCeti.FormalVertexAxioms

open VertexOperator

/-- **The Borcherds identity** in `finsum` form: for all states `a, b, c : V` and `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`. -/
theorem borcherds_finsum {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [HasUniqueDiv V] (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  let ⟨_, h⟩ := A.exists_isLocalOfOrder a b
  by simpa only [A.field_ncoeff_apply] using h.borcherds_finsum c m n r

end TauCeti.FormalVertexAxioms
