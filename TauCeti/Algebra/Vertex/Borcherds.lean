/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.NthProduct
-- Proof-only: delta expansions of local commutators, ℚ-linearity, binomial sums, and module tactic.
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Duality, skew symmetry, and the Borcherds identity for formal vertex algebras

In a formal vertex algebra `A : FormalVertexAxioms R V` whose underlying additive group is
torsion-free (`HasUniqueDiv V`), Dong's lemma and Goddard's uniqueness theorem force the
state–field correspondence to intertwine every integer `n`-th product of states with the `n`-th
product of fields:
`Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)`.

From this state–field `n`-th product identity we deduce the fundamental identities of vertex
algebra theory:

* **Singular pole bound from locality**: if `Y(a, z)` and `Y(b, w)` are mutually local of order
  `N`, then `a₍ₘ₎ b = 0` for all `m ≥ N` (`ncoeff_field_apply_eq_zero_of_isLocalOfOrder`).
* **State–field `n`-th product identity** (`field_ncoeff_apply`), specializing to nonnegative
  residue products (`field_ncoeff_natCast_apply`), normal ordering (`field_ncoeff_neg_one_apply`),
  and divided-power derivatives (`field_ncoeff_neg_succ_apply`).
* **Iterate / associativity formula** (`ncoeff_field_ncoeff_apply`): expansion of `(a₍ₙ₎ b)₍ᵣ₎ c`.
* **Mode commutator formula** (`lie_ncoeff_field_of_isLocalOfOrder` and
  `lie_ncoeff_field_apply_eq_sum`):
  `⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑ i ∈ range N, choose m i • (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`.
* **Borcherds (Jacobi) identity** in both cutoff-free `finsum` form (`borcherds_finsum`) and
  uniform-cutoff finite-sum form (`borcherds`), valid for all `a b c : V` and `m n r : ℤ` without
  any division over `ℚ`.
* **Skew symmetry** (`ncoeff_field_apply_skewSymmetry` and
  `ncoeff_field_apply_skewSymmetry_finsum`): over a `ℚ`-module `V`,
  `a₍ₙ₎ b = ∑ₖ (-1)^|n + k + 1| • (k!)⁻¹ • Tᵏ (b₍ₙ₊ₖ₎ a)`, the mode form of
  `Y(a, z) b = e^{zT} Y(b, -z) a`.

## References

* R. E. Borcherds, *Vertex algebras, Kac-Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.2 (Proposition 4.2, skew symmetry), §4.5
  (Theorem 4.5, `n`-th product identity), §4.6 (commutator formula), and §4.8 (Theorem 4.8,
  Borcherds identity).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.3.5 and Theorem 2.3.7.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2 and §3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti.FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-! ### Consequences of locality on the vacuum -/

private theorem ncoeff_add_apply_eq_sum_vacuum {B : VertexOperator R V} {a : V} {N : ℕ}
    (h : B.IsLocalOfOrder (A.field a) N) (m : ℤ) :
    (B[[m + N]]) a = ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      ((A.field a)[[-1 + ij.2]]) ((B[[m + ij.1]]) A.vacuum) := by
  have h₀ := LinearMap.congr_fun (isLocalOfOrder_iff.mp h m (-1)) A.vacuum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, LinearMap.zero_apply, smul_sub, sum_sub_distrib] at h₀
  rw [sum_eq_single (N, 0) (fun ij hij hne ↦ ?_) (by simp), sub_eq_zero] at h₀
  · simpa using h₀
  · have hj : ij.2 ≠ 0 :=
      fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
    rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega), map_zero, smul_zero, smul_zero]

/-- If `Y(a, z)` and `Y(b, w)` are mutually local of order `N`, then `a₍ₘ₎ b = 0` for all
`m ≥ N`. -/
theorem ncoeff_field_apply_eq_zero_of_isLocalOfOrder {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) {m : ℤ} (hm : (N : ℤ) ≤ m) :
    ((A.field a)[[m]]) b = 0 := by
  have hm' : m = m - N + N := by ring
  rw [hm', A.ncoeff_add_apply_eq_sum_vacuum h]
  refine sum_eq_zero fun ij _ ↦ ?_
  rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega), map_zero, smul_zero, smul_zero]

/-! ### State–field correspondence for `n`-th products -/

/-- Without division, the negative modes of `nthProduct n (A.field a) (A.field b)` on the vacuum
match the Taylor coefficients of `e^{zT} (a₍ₙ₎ b)`. -/
theorem factorial_smul_ncoeff_nthProduct_field_apply_vacuum (a b : V) (n : ℤ) (k : ℕ) :
    k.factorial • ((nthProduct n (A.field a) (A.field b))[[-k - 1]]) A.vacuum =
      (A.translation ^ k) (((A.field a)[[n]]) b) := by
  induction k with
  | zero =>
    rw [Nat.factorial_zero, one_smul, Nat.cast_zero, neg_zero, zero_sub,
      ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
        (A.ncoeff_field_apply_vacuum_of_nonneg b),
      A.ncoeff_neg_one_field_apply_vacuum, pow_zero, one_apply_eq_self]
  | succ k ih =>
    have hlie := LinearMap.congr_fun
      (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b)
        n (-k - 1)) A.vacuum
    rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      A.translation_vacuum, map_zero, sub_zero, ncoeff_derivative, LinearMap.smul_apply] at hlie
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [h₁, h₂, natCast_zsmul] at hlie
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, hlie, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- **State–field `n`-th product identity** (duality): in a torsion-free formal vertex algebra,
`Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for every `n : ℤ`. -/
theorem field_ncoeff_apply [HasUniqueDiv V] (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_ncoeff_apply_vacuum_eq (fun c ↦ ?_) (fun m ↦ ?_)
  · obtain ⟨r₁, hr₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨r₂, hr₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨r₃, hr₃⟩ := A.exists_isLocalOfOrder b c
    let r := max r₁ (max r₂ r₃)
    exact ⟨3 * r + n.natAbs, (hr₁.mono (le_max_left _ _)).nthProduct
      (hr₂.mono ((le_max_left _ _).trans (le_max_right _ _)))
      (hr₃.mono ((le_max_right _ _).trans (le_max_right _ _))) n⟩
  · rcases le_or_gt 0 m with hm | hm
    · rw [ncoeff_nthProduct_apply_of_nonneg (A.ncoeff_field_apply_vacuum_of_nonneg a)
        (A.ncoeff_field_apply_vacuum_of_nonneg b) n hm,
        A.ncoeff_field_apply_vacuum_of_nonneg _ m hm]
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
      rw [hk]
      exact nsmul_right_injective k.factorial_ne_zero
        ((A.factorial_smul_ncoeff_nthProduct_field_apply_vacuum a b n k).trans
          (A.factorial_smul_ncoeff_field_apply_vacuum _ k).symm)

/-- For `n : ℕ`, the field of `a₍ₙ₎ b` is the nonnegative residue product of `Y(a, z)` and
`Y(b, z)`. -/
theorem field_ncoeff_natCast_apply [HasUniqueDiv V] (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- The field of `a₍₋₁₎ b` is the normal-ordered product `:Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_one]

/-- For `k : ℕ`, the field of `a₍₋ₖ₋₁₎ b` is `:∂_z^(k) Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply [HasUniqueDiv V] (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_succ]

/-- **Iterate (associativity) formula** for modes: expansion of `(a₍ₙ₎ b)₍ᵣ₎ c` in terms of modes
of `a` and `b`. -/
theorem ncoeff_field_ncoeff_apply [HasUniqueDiv V] (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c)) -
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct, nthProductCoeff_apply]

/-! ### Mode commutator formula -/

/-- **Borcherds commutator formula** for fields local of order `N`:
`⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑ i ∈ range N, choose m i • (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`. -/
theorem lie_ncoeff_field_of_isLocalOfOrder [HasUniqueDiv V] {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ i ∈ range N, Ring.choose m i •
        (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  have hexp := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm m) n
  simp only [commutatorDistribution_apply, Finset.sum_apply,
    FormalDistribution.deltaTerm_apply, FormalDistribution.residue_apply,
    FormalDistribution.mulSub_pow_apply, zero_add] at hexp
  rw [Ring.lie_def, hexp]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [A.field_ncoeff_natCast_apply, ncoeff_nonnegResidueProduct]

/-- **Borcherds commutator formula** with an arbitrary singular truncation bound `N` for `a` on
`b`. -/
theorem lie_ncoeff_field_apply_eq_sum [HasUniqueDiv V] (a b c : V) (m n : ℤ) {N : ℕ}
    (hN : ∀ i : ℕ, N ≤ i → ((A.field a)[[(i : ℤ)]]) b = 0) :
    (⁅(A.field a)[[m]], (A.field b)[[n]]⁆) c =
      ∑ i ∈ range N, Ring.choose m i •
        ((A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]]) c := by
  obtain ⟨L, hL⟩ := A.exists_isLocalOfOrder a b
  rw [A.lie_ncoeff_field_of_isLocalOfOrder (hL.mono (le_max_right N L)), LinearMap.sum_apply]
  symm
  refine sum_subset (range_mono (le_max_left N L)) fun i _ hi ↦ ?_
  have hge : N ≤ i := by simp only [mem_range, not_lt] at hi; exact hi
  simp [hN i hge]

/-! ### The Borcherds identity -/

section BorcherdsIdentity

private def borcherdsLHS (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c

private def borcherdsRHS (a b c : V) (m n r : ℤ) : V :=
  (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i •
      ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)) -
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
      ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)

private theorem borcherdsLHS_eq_sum (a b c : V) (m n r : ℤ) {P : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → ((A.field a)[[n + i]]) b = 0) :
    A.borcherdsLHS a b c m n r =
      ∑ i ∈ range P, Ring.choose m i •
        ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c := by
  have hs : (Function.support fun i : ℕ ↦
      Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) ⊆ range P := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h; exact hi (by simp [hP i h])
  exact finsum_eq_sum_of_support_subset _ hs

private theorem borcherdsRHS_eq_sum (a b c : V) (m n r : ℤ) {P Q : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → ((A.field b)[[r + i]]) c = 0)
    (hQ : ∀ i : ℕ, Q ≤ i → ((A.field a)[[m + i]]) c = 0) :
    A.borcherdsRHS a b c m n r =
      (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)) -
        ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c) := by
  have hs₁ : (Function.support fun i : ℕ ↦ (-1 : ℤ) ^ i • Ring.choose n i •
      ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)) ⊆ range P := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h; exact hi (by simp [hP i h])
  have hs₂ : (Function.support fun i : ℕ ↦ (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
      ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) ⊆ range Q := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h; exact hi (by simp [hQ i h])
  rw [borcherdsRHS, finsum_eq_sum_of_support_subset _ hs₁, finsum_eq_sum_of_support_subset _ hs₂]

private theorem borcherds_zero [HasUniqueDiv V] (a b c : V) (n r : ℤ) :
    A.borcherdsLHS a b c 0 n r = A.borcherdsRHS a b c 0 n r := by
  obtain ⟨P₀, hP₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let P := P₀ + n.natAbs + 1
  rw [A.borcherdsLHS_eq_sum a b c 0 n r (P := P) (fun i hi ↦ hP₀ _ (by omega)),
    sum_eq_single 0 (fun i _ hi ↦ by
      rw [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi), zero_smul])
      (fun h0 ↦ (h0 (mem_range.mpr (by omega))).elim)]
  simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero, zero_add, sub_zero,
    A.ncoeff_field_ncoeff_apply, borcherdsRHS]

private theorem neg_one_pow_sub_nat {k i : ℕ} (hi : i ≤ k) :
    (-1 : ℤ) ^ k * (-1 : ℤ) ^ i = (-1 : ℤ) ^ (k - i) := by
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  conv_lhs => rw [hk, pow_add, mul_assoc, ← mul_pow]
  simp

private theorem borcherds_of_isLocalOfOrder (a b c : V) (m r : ℤ) {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    A.borcherdsLHS a b c m n r = A.borcherdsRHS a b c m n r := by
  have hLHS : A.borcherdsLHS a b c m n r = 0 := by
    rw [A.borcherdsLHS_eq_sum a b c m n r (P := 0)
      (fun i _ ↦ A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h (by omega)),
      range_zero, sum_empty]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
  have hNk : N ≤ k := by omega
  have hs₁ : (Function.support fun i : ℕ ↦ (-1 : ℤ) ^ i • Ring.choose (k : ℤ) i •
      ((A.field a)[[m + k - i]]) (((A.field b)[[r + i]]) c)) ⊆ range (k + 1) := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! hlt
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : k < i)])
  have hs₂ : (Function.support fun i : ℕ ↦ (-1 : ℤ) ^ (k : ℤ).natAbs • (-1 : ℤ) ^ i •
      Ring.choose (k : ℤ) i • ((A.field b)[[k + r - i]]) (((A.field a)[[m + i]]) c)) ⊆
      range (k + 1) := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! hlt
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : k < i)])
  have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.mp (h.mono hNk) m r) c
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
    LinearMap.zero_apply, Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_sub,
    sum_sub_distrib] at hloc
  rw [hLHS, eq_comm, borcherdsRHS, finsum_eq_sum_of_support_subset _ hs₁,
    finsum_eq_sum_of_support_subset _ hs₂,
    ← sum_range_reflect (fun i ↦ (-1 : ℤ) ^ i • Ring.choose (k : ℤ) i •
      ((A.field a)[[m + k - i]]) (((A.field b)[[r + i]]) c)) (k + 1), ← hloc]
  simp only [Nat.add_sub_cancel, Int.natAbs_natCast, Ring.choose_natCast]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : m + (k : ℤ) - ↑(k - i) = m + i := by omega
    rw [hidx, Nat.choose_symm hi', natCast_zsmul]
    module
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : (k : ℤ) + r - i = r + ↑(k - i) := by omega
    rw [hidx, ← mul_smul ((-1 : ℤ) ^ k), neg_one_pow_sub_nat hi', natCast_zsmul]
    module

private theorem borcherdsLHS_succ (a b c : V) (m n r : ℤ) :
    A.borcherdsLHS a b c (m + 1) n r =
      A.borcherdsLHS a b c m n (r + 1) + A.borcherdsLHS a b c m (n + 1) r := by
  obtain ⟨P₀, hP₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let P := P₀ + n.natAbs + 2
  rw [A.borcherdsLHS_eq_sum a b c (m + 1) n r (P := P + 1) (fun _ hi ↦ hP₀ _ (by omega)),
    A.borcherdsLHS_eq_sum a b c m n (r + 1) (P := P + 1) (fun _ hi ↦ hP₀ _ (by omega)),
    A.borcherdsLHS_eq_sum a b c m (n + 1) r (P := P) (fun _ hi ↦ hP₀ _ (by omega)),
    sum_range_succ' _ P, sum_range_succ' _ P]
  have h₀ : m + 1 + r - (0 : ℤ) = m + (r + 1) - 0 := by omega
  simp only [Ring.choose_succ_succ m, add_smul, sum_add_distrib, Ring.choose_zero_right,
    Nat.cast_zero, h₀]
  have h₁ : ∑ j ∈ range P, Ring.choose m (j + 1) •
      ((A.field (((A.field a)[[n + ↑(j + 1)]]) b))[[m + 1 + r - ↑(j + 1)]]) c =
      ∑ j ∈ range P, Ring.choose m (j + 1) •
        ((A.field (((A.field a)[[n + ↑(j + 1)]]) b))[[m + (r + 1) - ↑(j + 1)]]) c :=
    sum_congr rfl fun j _ ↦ by
      have heq : m + 1 + r - ↑(j + 1) = m + (r + 1) - ↑(j + 1) := by omega
      rw [heq]
  have h₂ : ∑ j ∈ range P, Ring.choose m j •
      ((A.field (((A.field a)[[n + ↑(j + 1)]]) b))[[m + 1 + r - ↑(j + 1)]]) c =
      ∑ j ∈ range P, Ring.choose m j •
        ((A.field (((A.field a)[[n + 1 + j]]) b))[[m + r - j]]) c :=
    sum_congr rfl fun j _ ↦ by
      have ha : n + ↑(j + 1) = n + 1 + (j : ℤ) := by omega
      have hb : m + 1 + r - ↑(j + 1) = m + r - (j : ℤ) := by omega
      rw [ha, hb]
  rw [h₁, h₂]
  abel

private theorem borcherdsRHS_succ_left (a b c : V) (m n r : ℤ) {P : ℕ}
    (hP0 : P ≠ 0) (hBP : ((A.field b)[[r + 1 + ↑(P - 1)]]) c = 0) :
    ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field a)[[m + 1 + n - i]]) (((A.field b)[[r + i]]) c) -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + 1 + i]]) c) -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
        ((A.field a)[[m + (n + 1) - i]]) (((A.field b)[[r + i]]) c) = 0 := by
  let h₁ : ℕ → V := fun i ↦
    if i = 0 then 0
    else -((-1 : ℤ) ^ (i - 1) • Ring.choose n (i - 1) •
      ((A.field a)[[m + n - ↑(i - 1)]]) (((A.field b)[[r + 1 + ↑(i - 1)]]) c))
  have htel : (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field a)[[m + 1 + n - i]]) (((A.field b)[[r + i]]) c) -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + 1 + i]]) c) -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
        ((A.field a)[[m + (n + 1) - i]]) (((A.field b)[[r + i]]) c)) =
      ∑ i ∈ range P, (h₁ (i + 1) - h₁ i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    cases i with
    | zero =>
      have ha : m + 1 + n - (0 : ℤ) = m + (n + 1) - 0 := by omega
      simp only [h₁, zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.cast_zero, pow_zero,
        Ring.choose_zero_right, one_smul, add_zero, sub_zero, ha]
      abel
    | succ j =>
      simp only [h₁, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, Ring.choose_succ_succ n j, add_smul, smul_add]
      have ha : m + 1 + n - ↑(j + 1) = m + n - (j : ℤ) := by omega
      have hb : m + (n + 1) - ↑(j + 1) = m + n - (j : ℤ) := by omega
      have hc : r + ↑(j + 1) = r + 1 + (j : ℤ) := by omega
      rw [ha, hb, hc, pow_succ (-1 : ℤ) j]
      simp only [mul_neg, mul_one, neg_smul, neg_neg]
      abel
  rw [htel, sum_range_sub]
  simp [h₁, hP0, hBP]

private theorem borcherdsRHS_succ_right (a b c : V) (m n r : ℤ) {Q : ℕ}
    (hQ0 : Q ≠ 0) (hAQ : ((A.field a)[[m + 1 + ↑(Q - 1)]]) c = 0) :
    ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c) -
      ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c) -
      ∑ i ∈ range Q, (-1 : ℤ) ^ (n + 1).natAbs • (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
        ((A.field b)[[n + 1 + r - i]]) (((A.field a)[[m + i]]) c) = 0 := by
  have hsign : (-1 : ℤ) ^ (n + 1).natAbs = -((-1 : ℤ) ^ n.natAbs) := by
    rw [← Int.coe_negOnePow ℤ (n + 1), ← Int.coe_negOnePow ℤ n, Int.negOnePow_succ]
    simp
  let h₂ : ℕ → V := fun i ↦
    if i = 0 then 0
    else (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ (i - 1) • Ring.choose n (i - 1) •
      ((A.field b)[[n + r - ↑(i - 1)]]) (((A.field a)[[m + 1 + ↑(i - 1)]]) c)
  have htel : (∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field b)[[n + r - i]]) (((A.field a)[[m + 1 + i]]) c) -
      ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        ((A.field b)[[n + (r + 1) - i]]) (((A.field a)[[m + i]]) c) -
      ∑ i ∈ range Q, (-1 : ℤ) ^ (n + 1).natAbs • (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
        ((A.field b)[[n + 1 + r - i]]) (((A.field a)[[m + i]]) c)) =
      ∑ i ∈ range Q, (h₂ (i + 1) - h₂ i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    cases i with
    | zero =>
      have ha : n + (r + 1) - (0 : ℤ) = n + 1 + r - 0 := by omega
      simp only [h₂, zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.cast_zero, pow_zero,
        Ring.choose_zero_right, one_smul, add_zero, sub_zero, hsign, neg_smul, ha]
      abel
    | succ j =>
      simp only [h₂, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, Ring.choose_succ_succ n j, hsign, add_smul, smul_add, neg_smul]
      have ha : n + (r + 1) - ↑(j + 1) = n + r - (j : ℤ) := by omega
      have hb : n + 1 + r - ↑(j + 1) = n + r - (j : ℤ) := by omega
      have hc : m + ↑(j + 1) = m + 1 + (j : ℤ) := by omega
      rw [ha, hb, hc, pow_succ (-1 : ℤ) j]
      simp only [mul_neg, mul_one, neg_smul, smul_neg, neg_neg]
      abel
  rw [htel, sum_range_sub]
  simp [h₂, hQ0, hAQ]

private theorem borcherdsRHS_succ (a b c : V) (m n r : ℤ) :
    A.borcherdsRHS a b c (m + 1) n r =
      A.borcherdsRHS a b c m n (r + 1) + A.borcherdsRHS a b c m (n + 1) r := by
  obtain ⟨P₀, hP₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨Q₀, hQ₀⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let P := P₀ + r.natAbs + 2
  let Q := Q₀ + m.natAbs + 2
  rw [A.borcherdsRHS_eq_sum a b c (m + 1) n r (P := P) (Q := Q)
      (fun _ hi ↦ hP₀ _ (by omega)) (fun _ hi ↦ hQ₀ _ (by omega)),
    A.borcherdsRHS_eq_sum a b c m n (r + 1) (P := P) (Q := Q)
      (fun _ hi ↦ hP₀ _ (by omega)) (fun _ hi ↦ hQ₀ _ (by omega)),
    A.borcherdsRHS_eq_sum a b c m (n + 1) r (P := P) (Q := Q)
      (fun _ hi ↦ hP₀ _ (by omega)) (fun _ hi ↦ hQ₀ _ (by omega)),
    ← sub_eq_zero]
  have hcomb : ∀ a₁ a₂ b₁ b₂ c₁ c₂ : V,
      (a₁ - a₂) - ((b₁ - b₂) + (c₁ - c₂)) = (a₁ - b₁ - c₁) - (a₂ - b₂ - c₂) := by intros; abel
  rw [hcomb,
    A.borcherdsRHS_succ_left a b c m n r (by omega) (hP₀ _ (by omega)),
    A.borcherdsRHS_succ_right a b c m n r (by omega) (hQ₀ _ (by omega)),
    sub_zero]

private theorem borcherdsLHS_eq_borcherdsRHS [HasUniqueDiv V] (a b c : V) (m n r : ℤ) :
    A.borcherdsLHS a b c m n r = A.borcherdsRHS a b c m n r := by
  rw [← sub_eq_zero]
  let D : ℤ → ℤ → ℤ → V := fun m' n' r' ↦
    A.borcherdsLHS a b c m' n' r' - A.borcherdsRHS a b c m' n' r'
  have hD0 (n' r' : ℤ) : D 0 n' r' = 0 := sub_eq_zero.mpr (A.borcherds_zero a b c n' r')
  have hDsucc (m' n' r' : ℤ) : D (m' + 1) n' r' = D m' n' (r' + 1) + D m' (n' + 1) r' := by
    simp only [D, A.borcherdsLHS_succ, A.borcherdsRHS_succ]; abel
  obtain ⟨N₀, hN₀⟩ := A.exists_isLocalOfOrder a b
  have hDlarge (m' n' r' : ℤ) (hn : (N₀ : ℤ) ≤ n') : D m' n' r' = 0 :=
    sub_eq_zero.mpr (A.borcherds_of_isLocalOfOrder a b c m' r' hN₀ hn)
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    have hpos : ∀ (j : ℕ) (n' r' : ℤ), D j n' r' = 0 := by
      intro j; induction j with
      | zero => exact hD0
      | succ j ih => intro n' r'; rw [Nat.cast_succ, hDsucc, ih, ih, add_zero]
    exact hpos k n r
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [hk]
    have hneg : ∀ (j : ℕ) (n' r' : ℤ), D (-(j : ℤ)) n' r' = 0 := by
      intro j; induction j with
      | zero => simpa using hD0
      | succ j ih =>
        have hstep (n' s : ℤ) :
            D (-((j + 1 : ℕ) : ℤ)) n' s = -D (-((j + 1 : ℕ) : ℤ)) (n' + 1) (s - 1) := by
          have h := hDsucc (-((j + 1 : ℕ) : ℤ)) n' (s - 1)
          have h₁ : -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) := by omega
          rw [h₁, sub_add_cancel, ih] at h
          exact eq_neg_of_add_eq_zero_left h.symm
        have hiter : ∀ (d : ℕ) (n' s : ℤ),
            D (-((j + 1 : ℕ) : ℤ)) n' s =
              (-1 : ℤ) ^ d • D (-((j + 1 : ℕ) : ℤ)) (n' + d) (s - d) := by
          intro d; induction d with
          | zero => simp
          | succ d ihd =>
            intro n' s; rw [hstep, ihd]
            have ha : n' + 1 + (d : ℤ) = n' + ↑(d + 1) := by omega
            have hb : s - 1 - (d : ℤ) = s - ↑(d + 1) := by omega
            rw [ha, hb, pow_succ (-1 : ℤ) d]; module
        intro n' r'
        rw [hiter (N₀ + n'.natAbs) n' r',
          hDlarge _ _ _ (by omega : (N₀ : ℤ) ≤ n' + ↑(N₀ + n'.natAbs)), smul_zero]
    exact hneg k n r

/-- **The Borcherds (Jacobi) identity** in cutoff-free `finsum` form, valid over any commutative
ring on a torsion-free `V`. -/
theorem borcherds_finsum [HasUniqueDiv V] (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i •
        ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)) -
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c) :=
  A.borcherdsLHS_eq_borcherdsRHS a b c m n r

/-- **The Borcherds (Jacobi) identity** with a uniform truncation cutoff `N`: for all `a b c : V`
and `m n r : ℤ`, all three tails vanish beyond `N` and the finite sums over `range N` agree. -/
theorem borcherds [HasUniqueDiv V] (a b c : V) (m n r : ℤ) :
    ∃ N : ℕ,
      (∀ i : ℕ, N ≤ i → ((A.field a)[[n + i]]) b = 0) ∧
      (∀ i : ℕ, N ≤ i → ((A.field b)[[r + i]]) c = 0) ∧
      (∀ i : ℕ, N ≤ i → ((A.field a)[[m + i]]) c = 0) ∧
      (∑ i ∈ range N, Ring.choose m i •
          ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
        ∑ i ∈ range N, (-1 : ℤ) ^ i • Ring.choose n i •
          (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
            (-1 : ℤ) ^ n.natAbs • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  obtain ⟨N₁, hN₁⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  obtain ⟨N₂, hN₂⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨N₃, hN₃⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let N := max (N₁ + n.natAbs) (max (N₂ + r.natAbs) (N₃ + m.natAbs))
  have h₁ : ∀ i : ℕ, N ≤ i → ((A.field a)[[n + i]]) b = 0 := fun _ hi ↦ hN₁ _ (by omega)
  have h₂ : ∀ i : ℕ, N ≤ i → ((A.field b)[[r + i]]) c = 0 := fun _ hi ↦ hN₂ _ (by omega)
  have h₃ : ∀ i : ℕ, N ≤ i → ((A.field a)[[m + i]]) c = 0 := fun _ hi ↦ hN₃ _ (by omega)
  refine ⟨N, h₁, h₂, h₃, ?_⟩
  have hfin := A.borcherdsLHS_eq_borcherdsRHS a b c m n r
  rw [A.borcherdsLHS_eq_sum a b c m n r h₁, A.borcherdsRHS_eq_sum a b c m n r h₂ h₃] at hfin
  rw [hfin, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  module

end BorcherdsIdentity

/-! ### Skew symmetry -/

section SkewSymmetry

private theorem succ_mul_choose_succ_int (q : ℤ) (l : ℕ) :
    ((l : ℤ) + 1) * Ring.choose q (l + 1) = (q - l) * Ring.choose q l := by
  have h := Ring.choose_smul_choose q (Nat.le_succ l)
  rw [Nat.succ_eq_add_one, Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
    Ring.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    mul_comm (Ring.choose q l)] at h
  exact h

/-- Action of a mode `b₍q₎` on a translated vector `Tʳ a`. -/
theorem ncoeff_field_translation_pow_apply (b a : V) (q : ℤ) (r : ℕ) :
    ((A.field b)[[q]]) ((A.translation ^ r) a) =
      ∑ kl ∈ antidiagonal r, r.choose kl.1 • kl.2.factorial • Ring.choose q kl.2 •
        (A.translation ^ kl.1) (((A.field b)[[q - kl.2]]) a) := by
  induction r generalizing a q with
  | zero => simp
  | succ r ih =>
    have hstep (p : ℤ) (x : V) :
        ((A.field b)[[p]]) (A.translation x) =
          A.translation (((A.field b)[[p]]) x) + p • ((A.field b)[[p - 1]]) x := by
      have h := A.translation_ncoeff_apply b x p
      rw [A.ncoeff_field_translation, LinearMap.smul_apply, neg_smul] at h
      rw [← sub_eq_zero, h]
      abel
    rw [pow_succ, mul_apply_eq_comp, ih,
      sum_antidiagonal_choose_succ_nsmul
        (fun k l ↦ l.factorial • Ring.choose q l •
          (A.translation ^ k) (((A.field b)[[q - l]]) a)) r]
    simp only [hstep, map_add, smul_add, sum_add_distrib]
    conv_lhs => rw [add_comm]
    congr 1
    · refine sum_congr rfl fun kl _ ↦ ?_
      have hidx : q - (kl.2 : ℤ) - 1 = q - ↑(kl.2 + 1) := by omega
      have hc := succ_mul_choose_succ_int q kl.2
      rw [hidx, map_zsmul (A.translation ^ kl.1), Nat.factorial_succ]
      simp only [← natCast_zsmul, ← mul_smul]
      refine congrArg (fun c : ℤ ↦ c •
        (A.translation ^ kl.1) (((A.field b)[[q - ↑(kl.2 + 1)]]) a)) ?_
      push_cast
      linear_combination -(r.choose kl.1 : ℤ) * (kl.2.factorial : ℤ) * hc
    · refine sum_congr rfl fun kl hkl ↦ ?_
      have hsum : r = kl.2 + kl.1 := by have := mem_antidiagonal.mp hkl; omega
      have hc : r.choose kl.2 = r.choose kl.1 := Nat.choose_symm_of_eq_add hsum
      rw [hc, pow_succ, mul_apply_eq_comp]

private theorem sum_range_choose_mul_choose_eq_one (m d : ℕ) :
    (∑ i ∈ range (d + 1),
        (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + 1 + i)) * ↑((m + i).choose m)) = 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hsplit : ∀ i ∈ range (d + 2),
        (-1 : ℤ) ^ i * ↑((m + 1 + (d + 1)).choose (m + 1 + i)) * ↑((m + i).choose m) =
          (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + i)) * ↑((m + i).choose m) +
            (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + 1 + i)) * ↑((m + i).choose m) := by
      intro i _
      have ha : m + 1 + (d + 1) = (m + 1 + d) + 1 := by omega
      have hb : m + 1 + i = (m + i) + 1 := by omega
      rw [ha, hb, Nat.choose_succ_succ, Nat.cast_add]
      ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    have hfirst : (∑ i ∈ range (d + 2),
        (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + i)) * ↑((m + i).choose m)) = 0 := by
      have hmul : ∀ i ∈ range (d + 2),
          (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + i)) * ↑((m + i).choose m) =
            ↑((m + 1 + d).choose m) * ((-1 : ℤ) ^ i * ↑((d + 1).choose i)) := by
        intro i _
        have hc := Nat.choose_mul (n := m + 1 + d) (k := m + i) (s := m) (Nat.le_add_right m i)
        have hsub₁ : m + 1 + d - m = d + 1 := by omega
        have hsub₂ : m + i - m = i := by omega
        rw [hsub₁, hsub₂] at hc
        rw [mul_assoc, ← Nat.cast_mul, hc, Nat.cast_mul]
        ring
      rw [sum_congr rfl hmul, ← mul_sum,
        Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero d), mul_zero]
    have hsecond : (∑ i ∈ range (d + 2),
        (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + 1 + i)) * ↑((m + i).choose m)) = 1 := by
      rw [sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega : m + 1 + d < m + 1 + (d + 1))]
      simp
    rw [hfirst, hsecond, zero_add]

private theorem alternating_sum_skew_coeff (N : ℕ) {p : ℤ} (hpN : p ≤ N) :
    (∑ j ∈ range (N + 1),
        if p ≤ (j : ℤ) then
          (-1 : ℤ) ^ j * ↑(N.choose j) * Ring.choose ((j : ℤ) - 1) ((j : ℤ) - p).toNat
        else 0) = (-1 : ℤ) ^ p.natAbs := by
  rcases le_or_gt p 0 with hp0 | hppos
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, p = -(s : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [sum_eq_single 0 (fun j _ hj0 ↦ ?_) (by simp)]
    · have h0 : ((0 : ℤ) - -(s : ℤ)).toNat = s := by omega
      have h1 : (0 : ℤ) - 1 = -(1 : ℤ) := by omega
      have h2 : (1 : ℤ) + s - 1 = (s : ℤ) := by omega
      have hneg : (-(s : ℤ)).natAbs = s := by omega
      simp only [Nat.cast_zero, Left.neg_nonpos_iff, Nat.cast_nonneg, ↓reduceIte, pow_zero,
        Nat.choose_zero_right, Nat.cast_one, one_mul, h0, h1, Ring.choose_neg, h2,
        Ring.choose_natCast, Nat.choose_self, Units.smul_def, Int.coe_negOnePow_natCast,
        smul_eq_mul, mul_one, hneg]
    · obtain ⟨u, rfl⟩ : ∃ u : ℕ, j = u + 1 := ⟨j - 1, by omega⟩
      have hu₁ : ((u + 1 : ℕ) : ℤ) - 1 = (u : ℤ) := by omega
      have hu₂ : (((u + 1 : ℕ) : ℤ) - -(s : ℤ)).toNat = u + 1 + s := by omega
      simp only [hu₁, hu₂, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega : u < u + 1 + s), Nat.cast_zero, mul_zero, ite_self]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = ↑(m + 1) := ⟨(p - 1).toNat, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, N = m + 1 + d := ⟨N - (m + 1), by omega⟩
    have hsplit : m + 1 + d + 1 = (m + 1) + (d + 1) := by omega
    rw [hsplit, sum_range_add]
    have hzero : (∑ j ∈ range (m + 1),
        if ((m + 1 : ℕ) : ℤ) ≤ (j : ℤ) then
          (-1 : ℤ) ^ j * ↑((m + 1 + d).choose j) *
            Ring.choose ((j : ℤ) - 1) ((j : ℤ) - ↑(m + 1)).toNat
        else 0) = 0 :=
      sum_eq_zero fun j hj ↦ ite_eq_right (by have := mem_range.mp hj; omega)
    have htail : (∑ i ∈ range (d + 1),
        if ((m + 1 : ℕ) : ℤ) ≤ ↑(m + 1 + i) then
          (-1 : ℤ) ^ (m + 1 + i) * ↑((m + 1 + d).choose (m + 1 + i)) *
            Ring.choose (((m + 1 + i : ℕ) : ℤ) - 1) (↑(m + 1 + i) - ((m + 1 : ℕ) : ℤ)).toNat
        else 0) =
        (-1 : ℤ) ^ (m + 1) * ∑ i ∈ range (d + 1),
          (-1 : ℤ) ^ i * ↑((m + 1 + d).choose (m + 1 + i)) * ↑((m + i).choose m) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      have hle : ((m + 1 : ℕ) : ℤ) ≤ ↑(m + 1 + i) := by omega
      have h₁ : ((m + 1 + i : ℕ) : ℤ) - 1 = ↑(m + i) := by omega
      have h₂ : (((m + 1 + i : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)).toNat = i := by omega
      rw [ite_eq_left hle, h₁, h₂, Ring.choose_natCast, Nat.choose_symm_add, pow_add]
      ring
    rw [hzero, zero_add, htail, sum_range_choose_mul_choose_eq_one, mul_one, Int.natAbs_natCast]

private theorem skew_vacuum_term_eq_sum [Module ℚ V] (a b : V) (n : ℤ) {N K : ℕ}
    (hNK : N + n.natAbs + 1 ≤ K) {j : ℕ} (hj : j ∈ range (N + 1)) :
    N.choose j • (-1 : ℤ) ^ j • ((A.field b)[[(j : ℤ) - 1]]) (((A.field a)[[n - j]]) A.vacuum) =
      ∑ k ∈ range K,
        if n + 1 + (k : ℤ) ≤ (j : ℤ) then
          ((-1 : ℤ) ^ j * ↑(N.choose j) *
              Ring.choose ((j : ℤ) - 1) ((j : ℤ) - (n + 1 + k)).toNat) •
            (k.factorial : ℚ)⁻¹ • (A.translation ^ k) (((A.field b)[[n + k]]) a)
        else 0 := by
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rcases le_or_gt (j : ℤ) n with hle | hgt
  · rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega), map_zero, smul_zero, smul_zero]
    symm
    exact sum_eq_zero fun k _ ↦ ite_eq_right (by omega)
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, (j : ℤ) = n + 1 + r := ⟨((j : ℤ) - n - 1).toNat, by omega⟩
    have hnj : n - (j : ℤ) = -(r : ℤ) - 1 := by omega
    have hrK : r + 1 ≤ K := by omega
    rw [hnj, A.ncoeff_field_apply_vacuum_neg, map_rat_smul, A.ncoeff_field_translation_pow_apply,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_sum, smul_sum, smul_sum]
    symm
    refine (sum_subset (range_mono hrK) fun k _ hk ↦ ?_).symm.trans ?_
    · rw [mem_range, not_lt] at hk
      exact ite_eq_right (by omega)
    · refine sum_congr rfl fun k hk ↦ ?_
      have hkr : k ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hcond : n + 1 + (k : ℤ) ≤ (j : ℤ) := by omega
      have hsub : ((j : ℤ) - (n + 1 + k)).toNat = r - k := by omega
      have hmode : (j : ℤ) - 1 - ↑(r - k) = n + k := by omega
      rw [ite_eq_left hcond, hsub, hmode]
      have hrat : (r.factorial : ℚ)⁻¹ * (r.choose k * (r - k).factorial : ℚ) =
          (k.factorial : ℚ)⁻¹ := by
        have hfac : (r.choose k * (r - k).factorial : ℚ) * k.factorial = r.factorial := by
          have h₀ : (r.choose k * k.factorial * (r - k).factorial : ℚ) = r.factorial := by
            exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkr
          linear_combination h₀
        have hk0 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
        have hr0 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
        apply mul_right_cancel₀ hk0
        rw [mul_assoc, hfac, inv_mul_cancel₀ hr0, inv_mul_cancel₀ hk0]
      rw [← Nat.cast_smul_eq_nsmul ℚ (r.choose k), ← Nat.cast_smul_eq_nsmul ℚ (r - k).factorial,
        ← Nat.cast_smul_eq_nsmul ℤ (N.choose j)]
      simp only [smul_comm (_ : ℚ) (_ : ℤ), ← mul_smul]
      rw [hrat]
      exact congrArg (· • (k.factorial : ℚ)⁻¹ • (A.translation ^ k) (((A.field b)[[n + k]]) a))
        (by ring)

/-- **Skew symmetry** for fields mutually local of order `N`, over a `ℚ`-module `V`:
`a₍ₙ₎ b = ∑ k ∈ range M, (-1)^|n + k + 1| • (k!)⁻¹ • Tᵏ (b₍ₙ₊ₖ₎ a)` for any cutoff `M` beyond
which `b₍ₙ₊ₖ₎ a = 0`. -/
theorem ncoeff_field_apply_skewSymmetry [Module ℚ V] (a b : V) (n : ℤ) {M : ℕ}
    (hM : ∀ k : ℕ, M ≤ k → ((A.field b)[[n + k]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ k ∈ range M, (-1 : ℤ) ^ (n + k + 1).natAbs • (k.factorial : ℚ)⁻¹ •
        (A.translation ^ k) (((A.field b)[[n + k]]) a) := by
  obtain ⟨N, hN⟩ := A.exists_isLocalOfOrder a b
  let K := max M (N + n.natAbs + 1)
  have hNK : N + n.natAbs + 1 ≤ K := le_max_right _ _
  have hn : n = n - N + N := by ring
  conv_lhs => rw [hn, A.ncoeff_add_apply_eq_sum_vacuum hN,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hrew : ∑ j ∈ range (N + 1), N.choose j • (-1 : ℤ) ^ (N - j) •
      ((A.field b)[[-1 + ↑(N - j)]]) (((A.field a)[[n - N + j]]) A.vacuum) =
      ∑ j ∈ range (N + 1), N.choose j • (-1 : ℤ) ^ j •
        ((A.field b)[[(j : ℤ) - 1]]) (((A.field a)[[n - j]]) A.vacuum) := by
    rw [← sum_range_reflect (fun j ↦ N.choose j • (-1 : ℤ) ^ (N - j) •
      ((A.field b)[[-1 + ↑(N - j)]]) (((A.field a)[[n - N + j]]) A.vacuum)) (N + 1)]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h₂ : (-1 : ℤ) + (j : ℤ) = (j : ℤ) - 1 := by omega
    have h₃ : n - (N : ℤ) + ↑(N - j) = n - j := by omega
    rw [Nat.add_sub_cancel, Nat.choose_symm hj', Nat.sub_sub_self hj', h₂, h₃]
  rw [hrew, sum_congr rfl fun j hj ↦ A.skew_vacuum_term_eq_sum a b n hNK hj, sum_comm]
  refine (sum_congr rfl fun k _ ↦ ?_).trans
    (sum_subset (range_mono (le_max_left M _)) fun k _ hk ↦ by
      rw [mem_range, not_lt] at hk; simp [hM k hk]).symm
  rcases le_or_gt (n + 1 + (k : ℤ)) N with hkN | hkN
  · have hpull : ∀ j ∈ range (N + 1),
        (if n + 1 + (k : ℤ) ≤ (j : ℤ) then
          ((-1 : ℤ) ^ j * ↑(N.choose j) *
              Ring.choose ((j : ℤ) - 1) ((j : ℤ) - (n + 1 + k)).toNat) •
            (k.factorial : ℚ)⁻¹ • (A.translation ^ k) (((A.field b)[[n + k]]) a)
        else 0) =
        (if n + 1 + (k : ℤ) ≤ (j : ℤ) then
          (-1 : ℤ) ^ j * ↑(N.choose j) *
            Ring.choose ((j : ℤ) - 1) ((j : ℤ) - (n + 1 + k)).toNat
        else 0) • (k.factorial : ℚ)⁻¹ • (A.translation ^ k) (((A.field b)[[n + k]]) a) :=
      fun _ _ ↦ by split_ifs <;> simp
    have habs : (n + 1 + (k : ℤ)).natAbs = (n + k + 1).natAbs := by omega
    rw [sum_congr rfl hpull, ← sum_smul, alternating_sum_skew_coeff N hkN, habs]
  · simp [A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder hN.symm (by omega : (N : ℤ) ≤ n + k)]

/-- **Skew symmetry** (`Y(a, z) b = e^{zT} Y(b, -z) a`) in cutoff-free `finsum` form over a
`ℚ`-module `V`. -/
theorem ncoeff_field_apply_skewSymmetry_finsum [Module ℚ V] (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ k : ℕ, (-1 : ℤ) ^ (n + k + 1).natAbs • (k.factorial : ℚ)⁻¹ •
        (A.translation ^ k) (((A.field b)[[n + k]]) a) := by
  obtain ⟨M₀, hM₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := M₀ + n.natAbs
  have hM : ∀ k : ℕ, M ≤ k → ((A.field b)[[n + k]]) a = 0 := fun _ hk ↦ hM₀ _ (by omega)
  have hs : (Function.support fun k : ℕ ↦
      (-1 : ℤ) ^ (n + k + 1).natAbs • (k.factorial : ℚ)⁻¹ •
        (A.translation ^ k) (((A.field b)[[n + k]]) a)) ⊆ range M := by
    intro k hk; simp only [mem_coe, mem_range]; by_contra! h; exact hk (by simp [hM k h])
  rw [finsum_eq_sum_of_support_subset _ hs, A.ncoeff_field_apply_skewSymmetry a b n hM]

end SkewSymmetry

end TauCeti.FormalVertexAxioms
