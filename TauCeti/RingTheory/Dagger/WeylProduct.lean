/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.Ring.Commutator
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Products of overconvergent differential operators

A differential operator `∑ a_{ij} x^i ∂^j` in one variable, written in normal order, is recorded by
its coefficient array, which we store as the two-variable power series `∑ a_{ij} X₀^i X₁^j`. In the
Weyl algebra with `∂ x - x ∂ = c`, the product of `x^i ∂^j` and `x^k ∂^l` is
`∑_s (j choose s) (k choose s) s! c^s x^{i+k-s} ∂^{j+l-s}`, so the product of two arrays `a` and `b`
has the coefficients

```text
c_{mn} = ∑_{s ≥ 0} ∑_{i ≤ m} ∑_{j ≤ n}
          a_{i,j+s} b_{m-i+s,n-j} ((j+s) choose s) ((m-i+s) choose s) s! c^s.
```

For polynomial arrays this is a finite sum and computes the product in every algebra in which
`∂ x - x ∂ = c` (`TauCeti.Dagger.sum_mul_sum_eq_sum_coeff_weylMul`). For infinite arrays the sum
over `s` is infinite.

Over a complete field with an ultrametric norm, take `c = π⁻¹` with `π ^ (p - 1) = -p`. The
coefficient arrays of Kedlaya's overconvergent Weyl algebra `D†` are those with
`liminf v_p(a_{ij}) / (i + j) > 0`, which are exactly the overconvergent series of the
Monsky–Washnitzer algebra `K⟨X₀, X₁⟩†` (`TauCeti.Dagger.mem_washnitzerAlgebra_iff_norm_coeff_le`).
For two such arrays the sums defining `c_{mn}` converge, and the product array is again
overconvergent. The factor `s! c^s` grows only polynomially in `s`, because the `p`-adic valuation
of `s!` falls short of `s / (p - 1)` by at most the number of base-`p` digits of `s`
(`TauCeti.norm_factorial_mul_pow_le`), so it is absorbed by the geometric decay of the
coefficients. The same estimate holds for every constant `c` with `‖c‖ ^ (p - 1) ≤ ‖p‖⁻¹`, over
every complete normed commutative ring with an ultrametric norm and `‖1‖ = 1`.

## Main definitions

* `TauCeti.Dagger.weylMulTerm`: the contribution of a fixed `s` to `c_{mn}`.
* `TauCeti.Dagger.weylMul`: the product array `∑_{mn} c_{mn} X₀^m X₁^n`.

## Main results

* `TauCeti.Dagger.coeff_weylMul_eq_sum_range`: on polynomial arrays, the series defining the
  coefficients of `weylMul` are finite sums.
* `TauCeti.Dagger.sum_mul_sum_eq_sum_coeff_weylMul`: on polynomial arrays, `weylMul` computes the
  product in any algebra with `∂ x = x ∂ + c`.
* `TauCeti.Dagger.norm_weylMulTerm_le`, `TauCeti.Dagger.norm_coeff_weylMul_le`: if both arrays
  are bounded by `C η^{|ν|}`, then `‖weylMulTerm c f g m n s‖ ≤ C² ‖s! c^s‖ η^{2s} η^{m+n}`, and
  the coefficients of `weylMul c f g` are bounded by `C² M η^{|ν|}` for every bound `M` of
  `‖s! c^s‖ η^{2s}`.
* `TauCeti.Dagger.summable_weylMulTerm`: for overconvergent arrays the series over `s` converges.
* `TauCeti.Dagger.weylMul_mem_washnitzerAlgebra`: the product array `weylMul c f g` of two
  overconvergent arrays is overconvergent; `TauCeti.Dagger.weylMul_inv_mem_washnitzerAlgebra` is
  the case `c = π⁻¹` with `π ^ (p - 1) = -p`.

## References

* K. S. Kedlaya, *Fourier transforms and p-adic 'Weil II'*, Compos. Math. 142 (2006), §4.1,
  Lemma 4.1.1, Lemma 4.1.2 and Proposition 4.1.3.
-/

public section

namespace TauCeti.Dagger

open Finset Filter Topology Nat _root_.MvPowerSeries
open Finsupp (single)

section Algebraic

variable {K : Type*} [CommSemiring K]

/-- The contribution of `s` contractions to the coefficient of `x^m ∂^n` in the product of the
operators with coefficient arrays `f` and `g`, in the Weyl algebra with `∂ x - x ∂ = c`:

```text
∑_{i ≤ m} ∑_{j ≤ n} f_{i,j+s} g_{m-i+s,n-j} ((j+s) choose s) ((m-i+s) choose s) s! c^s.
```

It collects the products `(x^i ∂^{j+s}) (x^{m-i+s} ∂^{n-j})` in which `s` copies of `∂` pass
across `s` copies of `x`. -/
noncomputable def weylMulTerm (c : K) (f g : MvPowerSeries (Fin 2) K) (m n s : ℕ) : K :=
  ∑ i ∈ range (m + 1), ∑ j ∈ range (n + 1),
    coeff (single 0 i + single 1 (j + s)) f * coeff (single 0 (m - i + s) + single 1 (n - j)) g *
      ((((j + s).choose s * (m - i + s).choose s * s ! : ℕ) : K) * c ^ s)

/-- The defining double sum of `weylMulTerm`. -/
theorem weylMulTerm_def (c : K) (f g : MvPowerSeries (Fin 2) K) (m n s : ℕ) :
    weylMulTerm c f g m n s = ∑ i ∈ range (m + 1), ∑ j ∈ range (n + 1),
      coeff (single 0 i + single 1 (j + s)) f * coeff (single 0 (m - i + s) + single 1 (n - j)) g *
        ((((j + s).choose s * (m - i + s).choose s * s ! : ℕ) : K) * c ^ s) :=
  (rfl)

/-- **Reindexing the contractions of a product.** Fix the number `s` of contractions. The products
`(x^i ∂^J) (x^k ∂^l)` with `J, k ≥ s` and all indices below `N` are in bijection with the data
`m < 2N`, `n < 2N`, `i ≤ m`, `j ≤ n`, via `J = j + s`, `k = m - i + s` and `l = n - j`, so that
`m = i + (k - s)` and `n = (J - s) + l` are the exponents of the result. -/
private theorem sum_range_four_eq_sum_range_four {M : Type*} [AddCommMonoid M] {N : ℕ} (s : ℕ)
    {F : ℕ → ℕ → ℕ → ℕ → M}
    (hF : ∀ i J k l, N ≤ i ∨ N ≤ J ∨ N ≤ k ∨ N ≤ l ∨ J < s ∨ k < s → F i J k l = 0) :
    ∑ i ∈ range N, ∑ J ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N, F i J k l =
      ∑ m ∈ range (2 * N), ∑ n ∈ range (2 * N), ∑ i ∈ range (m + 1), ∑ j ∈ range (n + 1),
        F i (j + s) (m - i + s) (n - j) := by
  calc ∑ i ∈ range N, ∑ J ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N, F i J k l
      = ∑ i ∈ range N, ∑ j ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N, F i (j + s) (k + s) l :=
        sum_congr rfl fun i _ ↦ (sum_range_eq_sum_range_add_of_eq_zero s fun J hJ ↦
          sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ hF _ _ _ _ (by omega)).trans <|
            sum_congr rfl fun j _ ↦ sum_range_eq_sum_range_add_of_eq_zero s fun k hk ↦
              sum_eq_zero fun l _ ↦ hF _ _ _ _ (by omega)
    _ = ∑ i ∈ range N, ∑ k ∈ range N, ∑ j ∈ range N, ∑ l ∈ range N, F i (j + s) (k + s) l :=
        sum_congr rfl fun _ _ ↦ sum_comm
    _ = ∑ m ∈ range (2 * N), ∑ i ∈ range (m + 1), ∑ j ∈ range N, ∑ l ∈ range N,
          F i (j + s) (m - i + s) l :=
        (sum_range_add_antidiagonal_of_support N N
          (fun q ↦ ∑ j ∈ range N, ∑ l ∈ range N, F q.1 (j + s) (q.2 + s) l)
          fun i k hik ↦ sum_eq_zero fun j _ ↦ sum_eq_zero fun l _ ↦
            hF _ _ _ _ (by omega)).symm.trans
          (by rw [two_mul]; simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk])
    _ = ∑ m ∈ range (2 * N), ∑ i ∈ range (m + 1), ∑ n ∈ range (2 * N), ∑ j ∈ range (n + 1),
          F i (j + s) (m - i + s) (n - j) :=
        sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦
          (sum_range_add_antidiagonal_of_support N N (fun q ↦ F i (q.1 + s) (m - i + s) q.2)
            fun j l hjl ↦ hF _ _ _ _ (by omega)).symm.trans
            (by rw [two_mul]; simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk])
    _ = _ := sum_congr rfl fun _ _ ↦ sum_comm

/-- A coefficient array supported in `[0, N) × [0, N)` vanishes at `(i, j)` once `i` or `j`
reaches `N`. -/
private theorem coeff_single_add_single_eq_zero {f : MvPowerSeries (Fin 2) K} {N : ℕ}
    (hf : ∀ ν, coeff ν f ≠ 0 → ν 0 < N ∧ ν 1 < N) {i j : ℕ} (h : N ≤ i ∨ N ≤ j) :
    coeff (single 0 i + single 1 j) f = 0 := by
  by_contra hne
  have := hf _ hne
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, ne_eq, zero_ne_one,
    not_false_eq_true, Finsupp.single_eq_of_ne, add_zero, one_ne_zero, zero_add] at this
  omega

variable {A : Type*} [Semiring A] [Algebra K A]

/-- The product of two normal-ordered monomials in an algebra with `∂ x = x ∂ + c`, written as a
sum over the number `s < N` of contractions: `x^i ∂^J x^k ∂^l` is the sum of
`(J choose s) (k choose s) s! c^s x^{i+(k-s)} ∂^{(J-s)+l}`. -/
private theorem pow_mul_pow_mul_pow_mul_pow_eq_sum {c : K} {x d : A}
    (hdx : d * x = x * d + algebraMap K A c) {N i J k l : ℕ} (hJ : J < N) :
    x ^ i * d ^ J * (x ^ k * d ^ l) = ∑ s ∈ range N,
      (((J.choose s * k.choose s * s ! : ℕ) : K) * c ^ s) •
        (x ^ (i + (k - s)) * d ^ (J - s + l)) := by
  have hcomm (a : A) : Commute a (algebraMap K A c) := (Algebra.commutes c a).symm
  rw [mul_assoc, ← mul_assoc (d ^ J),
    Associative.pow_mul_pow_eq_sum_of_commutator_eq hdx (hcomm d) (hcomm x),
    ← sum_subset (range_subset_range.2 (by omega : min J k + 1 ≤ N)) fun s _ hs ↦ by
      rw [mem_range, not_lt, Nat.succ_le_iff, min_lt_iff] at hs
      rcases hs with hs | hs <;> simp [Nat.choose_eq_zero_of_lt hs],
    sum_mul, mul_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [← map_pow, ← Nat.cast_smul_eq_nsmul K, mul_smul, Algebra.algebraMap_eq_smul_one]
  simp only [smul_mul_assoc, mul_smul_comm, mul_one, pow_add, mul_assoc]

variable [TopologicalSpace K]

/-- The **product of differential operators in normal order**, on coefficient arrays: the
coefficient of `x^m ∂^n` in `weylMul c f g` is defined as the sum `∑' s, weylMulTerm c f g m n s`.
When these series converge, it is the coefficient of `x^m ∂^n` in the product of
`∑ f_{ij} x^i ∂^j` and `∑ g_{kl} x^k ∂^l` in the Weyl algebra with `∂ x - x ∂ = c`: for instance
for polynomial arrays (`TauCeti.Dagger.sum_mul_sum_eq_sum_coeff_weylMul`), or for overconvergent
arrays over a complete ring (`TauCeti.Dagger.summable_weylMulTerm`). Where a series diverges,
`tsum` returns `0`. -/
noncomputable def weylMul (c : K) (f g : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  fun ν ↦ ∑' s, weylMulTerm c f g (ν 0) (ν 1) s

@[simp]
theorem coeff_weylMul (c : K) (f g : MvPowerSeries (Fin 2) K) (ν : Fin 2 →₀ ℕ) :
    coeff ν (weylMul c f g) = ∑' s, weylMulTerm c f g (ν 0) (ν 1) s :=
  coeff_apply _ _

/-- **`weylMul` on polynomial arrays is a finite sum.** If `f` is supported in `[0, N) × [0, N)`,
only the terms `s < N` contribute to the coefficients of `weylMul c f g`, since `f_{i,j+s} = 0`
once `j + s ≥ N`. -/
theorem coeff_weylMul_eq_sum_range {c : K} {f g : MvPowerSeries (Fin 2) K} {N : ℕ}
    (hf : ∀ ν, coeff ν f ≠ 0 → ν 0 < N ∧ ν 1 < N) (ν : Fin 2 →₀ ℕ) :
    coeff ν (weylMul c f g) = ∑ s ∈ range N, weylMulTerm c f g (ν 0) (ν 1) s := by
  have hvan : ∀ s ∉ range N, weylMulTerm c f g (ν 0) (ν 1) s = 0 := fun s hs ↦
    sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ by
      rw [coeff_single_add_single_eq_zero hf (.inr (by simp only [mem_range, not_lt] at hs; omega))]
      simp
  rw [coeff_weylMul, tsum_eq_sum hvan]

/-- **`weylMul` computes products of polynomial operators.** Let `x` and `d` be elements of a
`K`-algebra with `d * x = x * d + c`, and let `f`, `g` be coefficient arrays supported in
`[0, N) × [0, N)`. Then the product of the operators `∑ f_{ij} x^i d^j` and `∑ g_{kl} x^k d^l` is
the operator `∑ c_{mn} x^m d^n` with coefficient array `weylMul c f g`. -/
theorem sum_mul_sum_eq_sum_coeff_weylMul {c : K} {x d : A}
    (hdx : d * x = x * d + algebraMap K A c) {f g : MvPowerSeries (Fin 2) K} {N : ℕ}
    (hf : ∀ ν, coeff ν f ≠ 0 → ν 0 < N ∧ ν 1 < N) (hg : ∀ ν, coeff ν g ≠ 0 → ν 0 < N ∧ ν 1 < N) :
    (∑ i ∈ range N, ∑ j ∈ range N, coeff (single 0 i + single 1 j) f • (x ^ i * d ^ j)) *
        (∑ k ∈ range N, ∑ l ∈ range N, coeff (single 0 k + single 1 l) g • (x ^ k * d ^ l)) =
      ∑ m ∈ range (2 * N), ∑ n ∈ range (2 * N),
        coeff (single 0 m + single 1 n) (weylMul c f g) • (x ^ m * d ^ n) := by
  have ha (i j : ℕ) (h : N ≤ i ∨ N ≤ j) := coeff_single_add_single_eq_zero hf h
  have hb (k l : ℕ) (h : N ≤ k ∨ N ≤ l) := coeff_single_add_single_eq_zero hg h
  -- `T s i J k l` is the part of `(f_{iJ} x^i ∂^J) (g_{kl} x^k ∂^l)` with `s` contractions.
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℕ → ℕ → ℕ → A, ∀ s i J k l, T s i J k l =
      (coeff (single 0 i + single 1 J) f * coeff (single 0 k + single 1 l) g *
        (((J.choose s * k.choose s * s ! : ℕ) : K) * c ^ s)) •
          (x ^ (i + (k - s)) * d ^ (J - s + l)) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  calc _ = ∑ i ∈ range N, ∑ J ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N, ∑ s ∈ range N,
          T s i J k l := by
        simp only [sum_mul]
        simp only [mul_sum]
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun J hJ ↦ sum_congr rfl fun k _ ↦
          sum_congr rfl fun l _ ↦ ?_
        rw [smul_mul_smul_comm, pow_mul_pow_mul_pow_mul_pow_eq_sum hdx (mem_range.1 hJ), smul_sum]
        simp only [smul_smul, hT]
    -- Move the sum over the number `s` of contractions to the outside.
    _ = ∑ i ∈ range N, ∑ J ∈ range N, ∑ s ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N,
          T s i J k l :=
        sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦
          (sum_congr rfl fun _ _ ↦ sum_comm).trans sum_comm
    _ = ∑ s ∈ range N, ∑ i ∈ range N, ∑ J ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N,
          T s i J k l := (sum_congr rfl fun _ _ ↦ sum_comm).trans sum_comm
    _ = ∑ s ∈ range N, ∑ m ∈ range (2 * N), ∑ n ∈ range (2 * N), ∑ i ∈ range (m + 1),
          ∑ j ∈ range (n + 1), T s i (j + s) (m - i + s) (n - j) :=
        sum_congr rfl fun s _ ↦ sum_range_four_eq_sum_range_four s fun i J k l h ↦ by
          rw [hT]
          rcases h with h | h | h | h | h | h
          · simp [ha i J (.inl h)]
          · simp [ha i J (.inr h)]
          · simp [hb k l (.inl h)]
          · simp [hb k l (.inr h)]
          · simp [Nat.choose_eq_zero_of_lt h]
          · simp [Nat.choose_eq_zero_of_lt h]
    _ = ∑ m ∈ range (2 * N), ∑ n ∈ range (2 * N), ∑ s ∈ range N, ∑ i ∈ range (m + 1),
          ∑ j ∈ range (n + 1), T s i (j + s) (m - i + s) (n - j) :=
        sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm)
    _ = _ := by
        refine sum_congr rfl fun m _ ↦ sum_congr rfl fun n _ ↦ ?_
        have h0 : (single 0 m + single 1 n : Fin 2 →₀ ℕ) 0 = m := by simp
        have h1 : (single 0 m + single 1 n : Fin 2 →₀ ℕ) 1 = n := by simp
        rw [coeff_weylMul_eq_sum_range hf, h0, h1, sum_smul]
        refine sum_congr rfl fun s _ ↦ ?_
        simp only [weylMulTerm, sum_smul]
        refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
        rw [mem_range] at hi hj
        rw [hT, show i + (m - i + s - s) = m by omega, show j + s - s + (n - j) = n by omega]

end Algebraic

section Analytic

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K] {f g : MvPowerSeries (Fin 2) K}

/-- The total degree of the exponent `single 0 i + single 1 j` is `i + j`. -/
private theorem degree_single_add_single (i j : ℕ) :
    (single 0 i + single 1 j : Fin 2 →₀ ℕ).degree = i + j := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

omit [IsUltrametricDist K] in
/-- A coefficient bound `‖a_ν‖ ≤ C η^{|ν|}` forces `0 ≤ C`, and `0 ≤ η` unless `C = 0`. -/
private theorem nonneg_and_nonneg_or_eq_zero_of_norm_coeff_le {η C : ℝ}
    (h : ∀ ν : Fin 2 →₀ ℕ, ‖coeff ν f‖ ≤ C * η ^ ν.degree) : 0 ≤ C ∧ (0 ≤ η ∨ C = 0) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (h 0)
  refine ⟨hC, or_iff_not_imp_left.2 fun hη ↦ ?_⟩
  have h1 := (norm_nonneg _).trans (h (single 0 1))
  rw [Finsupp.degree_single, pow_one] at h1
  nlinarith

variable [NormOneClass K] (p : ℕ) [Fact p.Prime] {c : K}

/-- **The basic estimate.** If both coefficient arrays are bounded by `C η^{|ν|}`, then the
`s`-th term of the coefficient of `x^m ∂^n` is bounded by `C² ‖s! c^s‖ η^{2s} η^{m+n}`: each of
its summands is a product of two coefficients of total degree `m + n + 2s` with an integer
multiple of `s! c^s`. -/
theorem norm_weylMulTerm_le {η C : ℝ}
    (hfg : ∀ ν : Fin 2 →₀ ℕ, ‖coeff ν f‖ ≤ C * η ^ ν.degree ∧ ‖coeff ν g‖ ≤ C * η ^ ν.degree)
    (m n s : ℕ) :
    ‖weylMulTerm c f g m n s‖ ≤ C ^ 2 * (‖(s ! : K) * c ^ s‖ * (η ^ 2) ^ s) * η ^ (m + n) := by
  obtain ⟨hC, hη | rfl⟩ := nonneg_and_nonneg_or_eq_zero_of_norm_coeff_le fun ν ↦ (hfg ν).1
  swap
  · -- If `C = 0`, both arrays vanish.
    have h0 (ν : Fin 2 →₀ ℕ) : coeff ν f = 0 ∧ coeff ν g = 0 := by simpa using hfg ν
    simp [weylMulTerm, h0]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj ↦ ?_
  rw [mem_range, Nat.lt_succ_iff] at hi hj
  have hint : ‖(((j + s).choose s * (m - i + s).choose s : ℕ) : K)‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one K _
  have hdeg : i + (j + s) + (m - i + s + (n - j)) = 2 * s + (m + n) := by omega
  rw [Nat.cast_mul (_ * _), mul_assoc (((_ * _ : ℕ)) : K)]
  refine (norm_mul_le _ _).trans <| (mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _) (norm_nonneg _)
    (by positivity)).trans ?_
  calc ‖coeff (single 0 i + single 1 (j + s)) f‖ *
        ‖coeff (single 0 (m - i + s) + single 1 (n - j)) g‖ *
        (‖(((j + s).choose s * (m - i + s).choose s : ℕ) : K)‖ * ‖(s ! : K) * c ^ s‖)
      ≤ (C * η ^ (i + (j + s))) * (C * η ^ (m - i + s + (n - j))) *
          (1 * ‖(s ! : K) * c ^ s‖) := by
        gcongr
        · have h := (hfg (single 0 i + single 1 (j + s))).1
          rwa [degree_single_add_single] at h
        · have h := (hfg (single 0 (m - i + s) + single 1 (n - j))).2
          rwa [degree_single_add_single] at h
    _ = C ^ 2 * ‖(s ! : K) * c ^ s‖ * η ^ (i + (j + s) + (m - i + s + (n - j))) := by ring
    _ = C ^ 2 * (‖(s ! : K) * c ^ s‖ * (η ^ 2) ^ s) * η ^ (m + n) := by rw [hdeg]; ring

/-- **The coefficient bound of a product** (Kedlaya, Proposition 4.1.3). If both coefficient
arrays are bounded by `C η^{|ν|}` and `‖s! c^s‖ η^{2s} ≤ M` for every `s`, then the coefficients
of `weylMul c f g` are bounded by `C² M η^{|ν|}`: the product keeps the decay rate `η`. When
`‖c‖ ^ (p - 1) ≤ ‖p‖⁻¹` and `0 ≤ η < 1`, such an `M` exists, because `‖s! c^s‖ η^{2s} → 0`
(`TauCeti.tendsto_norm_factorial_mul_pow_mul_pow`). -/
theorem norm_coeff_weylMul_le {η C M : ℝ}
    (hfg : ∀ ν : Fin 2 →₀ ℕ, ‖coeff ν f‖ ≤ C * η ^ ν.degree ∧ ‖coeff ν g‖ ≤ C * η ^ ν.degree)
    (hM : ∀ s : ℕ, ‖(s ! : K) * c ^ s‖ * (η ^ 2) ^ s ≤ M) (ν : Fin 2 →₀ ℕ) :
    ‖coeff ν (weylMul c f g)‖ ≤ C ^ 2 * M * η ^ ν.degree := by
  obtain ⟨hC, hη | rfl⟩ := nonneg_and_nonneg_or_eq_zero_of_norm_coeff_le fun ν ↦ (hfg ν).1
  swap
  · -- If `C = 0`, both arrays vanish.
    have h0 (ν : Fin 2 →₀ ℕ) : coeff ν f = 0 ∧ coeff ν g = 0 := by simpa using hfg ν
    simp [weylMulTerm, h0]
  have hM0 : 0 ≤ M :=
    (by positivity : (0 : ℝ) ≤ ‖((0 ! : ℕ) : K) * c ^ 0‖ * (η ^ 2) ^ 0).trans (hM 0)
  rw [coeff_weylMul, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun s ↦ ?_
  refine (norm_weylMulTerm_le hfg _ _ s).trans ?_
  gcongr
  exact hM s

/-- **The product of two overconvergent operators is overconvergent** (Kedlaya,
Proposition 4.1.3). If `‖c‖ ^ (p - 1) ≤ ‖p‖⁻¹` and `f`, `g` are overconvergent coefficient
arrays, then so is the coefficient array `weylMul c f g`. Its coefficients are the sums
`∑' s, weylMulTerm c f g m n s`, so it is the coefficient array of the product when these series
converge, for instance when `K` is complete (`TauCeti.Dagger.summable_weylMulTerm`). -/
theorem weylMul_mem_washnitzerAlgebra (hc : ‖c‖ ^ (p - 1) ≤ ‖(p : K)‖⁻¹)
    (hf : f ∈ washnitzerAlgebra (Fin 2) K) (hg : g ∈ washnitzerAlgebra (Fin 2) K) :
    weylMul c f g ∈ washnitzerAlgebra (Fin 2) K := by
  obtain ⟨η, hη0, hη1, C, hfg⟩ := exists_norm_coeff_le_of_mem_washnitzerAlgebra hf hg
  have hη2 : |η ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ hη0.le hη1 two_ne_zero
  -- `‖s! c^s‖ η^{2s}` tends to zero, so it is bounded by some `M`.
  obtain ⟨M, hM⟩ := (tendsto_norm_factorial_mul_pow_mul_pow p hc hη2).bddAbove_range
  refine mem_washnitzerAlgebra_iff_norm_coeff_le.2 ⟨η⁻¹, one_lt_inv₀ hη0 |>.2 hη1, C ^ 2 * M,
    fun ν ↦ ?_⟩
  rw [inv_pow, inv_inv]
  exact norm_coeff_weylMul_le hfg (fun s ↦ hM ⟨s, rfl⟩) ν

variable [CompleteSpace K]

/-- **The coefficients of a product of overconvergent operators converge** (Kedlaya,
Proposition 4.1.3). If `‖c‖ ^ (p - 1) ≤ ‖p‖⁻¹`, for instance `c = π⁻¹` with `π ^ (p - 1) = -p`,
and `f`, `g` are overconvergent coefficient arrays, then for every `m` and `n` the series
`∑_s weylMulTerm c f g m n s` defining the coefficient of `x^m ∂^n` in their product converges. -/
theorem summable_weylMulTerm (hc : ‖c‖ ^ (p - 1) ≤ ‖(p : K)‖⁻¹)
    (hf : f ∈ washnitzerAlgebra (Fin 2) K) (hg : g ∈ washnitzerAlgebra (Fin 2) K) (m n : ℕ) :
    Summable (weylMulTerm c f g m n) := by
  obtain ⟨η, hη0, hη1, C, hfg⟩ := exists_norm_coeff_le_of_mem_washnitzerAlgebra hf hg
  have hη2 : |η ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ hη0.le hη1 two_ne_zero
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (norm_weylMulTerm_le hfg m n) ?_
  simpa using ((tendsto_norm_factorial_mul_pow_mul_pow p hc hη2).const_mul (C ^ 2)).mul_const
    (η ^ (m + n))

end Analytic

/-- **Kedlaya's overconvergent product.** Let `π ∈ K` satisfy `π ^ (p - 1) = -p`, the
normalisation of Dwork's `π`. In the Weyl algebra with `∂ x - x ∂ = π⁻¹`, the coefficient array
`weylMul π⁻¹ f g` of two overconvergent coefficient arrays is overconvergent. It is the
coefficient array of their product when the series defining it converge, for instance when `K` is
complete (`TauCeti.Dagger.summable_weylMulTerm`). -/
theorem weylMul_inv_mem_washnitzerAlgebra {K : Type*} [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] {f g : MvPowerSeries (Fin 2) K} {π : K} (hπ : π ^ (p - 1) = -p)
    (hf : f ∈ washnitzerAlgebra (Fin 2) K) (hg : g ∈ washnitzerAlgebra (Fin 2) K) :
    weylMul π⁻¹ f g ∈ washnitzerAlgebra (Fin 2) K :=
  weylMul_mem_washnitzerAlgebra p (by rw [norm_inv, inv_pow, ← norm_pow, hπ, norm_neg]) hf hg

end TauCeti.Dagger
