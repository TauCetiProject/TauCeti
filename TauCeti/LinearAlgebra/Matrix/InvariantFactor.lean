/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.LinearAlgebra.Matrix.Divisibility
public import TauCeti.LinearAlgebra.Matrix.Minor
public import TauCeti.RingTheory.Valuation.AddValuation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Invariant factors and the valuations of minors

Let `L * A * Q = diagonal s` with `L`, `Q` of unit determinant and `s₀ ∣ s₁ ∣ ⋯ ∣ sₙ₋₁` a
divisibility chain, a Smith normal form of the square matrix `A` with invariant factors `s`.
Over any commutative ring, the product `s₀ ⋯ sₖ₋₁` of the first `k` invariant factors divides
every `k × k` minor of `A`, on arbitrary rows and columns, and every common divisor of these
minors divides it: it is a greatest common divisor of the `k × k` minors. For an additive
valuation `v` which is nonnegative on the whole ring, such as the valuation of a discrete
valuation ring, the least valuation of a `k × k` minor of `A` is therefore
`v s₀ + ⋯ + v sₖ₋₁`, and `v (det A)` is the sum of all the `v sᵢ`. All row and column choices
are needed here; the principal minors alone need not attain the minimum.

Over a discrete valuation ring, every square matrix has such a Smith
normal form: `Matrix.exists_smith_normal_form_of_isDiscreteValuationRing` in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic`. Comparing these least valuations shows that
a Smith normal form `diagonal (ϖ ^ α)` by powers of a uniformizer `ϖ`, with monotone exponents
`α`, is unique.

These valuations are the slopes of the Hodge polygon of the endomorphism `A` of the lattice
`Rⁿ`, and the minor bounds are the input to the comparison of this Hodge polygon with the Newton
polygon of `det (1 - X A)` in `TauCeti.NumberTheory.NewtonPolygon.Lattice`.

## Main results

* `Matrix.le_valuation_det_submatrix_mul_mul`: a lower bound for the valuations of the minors of
  `A` of a given size persists for those of `P * A * Q`, for a nonnegative valuation.
* `Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal`,
  `Matrix.dvd_prod_of_mul_mul_eq_diagonal`: the product of the first `k` invariant factors is a
  greatest common divisor of the `k × k` minors.
* `Matrix.prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal`,
  `Matrix.exists_valuation_det_submatrix_eq_prefixSum_of_mul_mul_eq_diagonal`: its valuation
  `v s₀ + ⋯ + v sₖ₋₁` is the least valuation of a `k × k` minor.
* `Matrix.prefixSum_le_valuation_principalMinor_of_mul_mul_eq_diagonal`: in particular it bounds
  the valuations of the principal `k × k` minors from below.
* `Matrix.valuation_det_eq_sum_of_mul_mul_eq_diagonal`: `v (det A) = ∑ i, v (s i)`.
* `Matrix.eq_of_mul_mul_eq_diagonal_pow`: over a discrete valuation ring, a Smith normal form
  `diagonal (ϖ ^ α)` with monotone exponents is unique.

## References

* K. S. Kedlaya, [*A little p-adic numerical analysis*](https://kskedlaya.org/18.787/numerical.pdf),
  MIT 18.787 notes (2007), §3.
* N. Jacobson, *Basic Algebra I*, second edition, W. H. Freeman, 1985, §3.9.
-/

public section

open Finset TauCeti

namespace Matrix

/-! ### Valuations of minors of products -/

section Valuation

variable {ι l m n o R Γ₀ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]
  {v : AddValuation R Γ₀}

/-- **A lower bound for the valuations of the minors survives left multiplication.** For a
valuation which is nonnegative on the whole ring, if every `ι`-minor of `B` has valuation at least
`c`, then so does every `ι`-minor of `A * B`, which is an `R`-combination of minors of `B`. -/
theorem le_valuation_det_submatrix_mul_left [Fintype ι] [DecidableEq ι] [Fintype m]
    (hv : ∀ x, 0 ≤ v x) {B : Matrix m n R} {c : Γ₀}
    (hc : ∀ (f : ι → m) (g : ι → n), c ≤ v (B.submatrix f g).det)
    (A : Matrix l m R) (f : ι → l) (g : ι → n) : c ≤ v ((A * B).submatrix f g).det := by
  rw [submatrix_mul A B f id g Function.bijective_id, det_mul_eq_sum_prod_mul_det_submatrix]
  refine AddValuation.map_le_sum v fun r _ ↦ ?_
  rw [v.map_mul]
  exact le_add_of_nonneg_of_le (hv _) (hc r g)

/-- **A lower bound for the valuations of the minors survives two-sided multiplication.** For a
valuation which is nonnegative on the whole ring, if every `ι`-minor of `A` has valuation at least
`c`, then so does every `ι`-minor of `P * A * Q`. -/
theorem le_valuation_det_submatrix_mul_mul [Fintype ι] [DecidableEq ι] [Fintype m] [Fintype n]
    (hv : ∀ x, 0 ≤ v x) {A : Matrix m n R} {c : Γ₀}
    (hc : ∀ (f : ι → m) (g : ι → n), c ≤ v (A.submatrix f g).det)
    (P : Matrix l m R) (Q : Matrix n o R) (f : ι → l) (g : ι → o) :
    c ≤ v ((P * A * Q).submatrix f g).det := by
  -- the right factor is handled by transposing it into a left factor
  have hAQ : ∀ (f' : ι → m) (g' : ι → o), c ≤ v ((A * Q).submatrix f' g').det := by
    intro f' g'
    rw [← det_transpose, transpose_submatrix, transpose_mul]
    exact le_valuation_det_submatrix_mul_left hv
      (fun g'' f'' ↦ by rw [← transpose_submatrix, det_transpose]; exact hc f'' g'') _ g' f'
  rw [Matrix.mul_assoc]
  exact le_valuation_det_submatrix_mul_left hv hAQ P f g

end Valuation

/-! ### Minors and invariant factors -/

section InvariantFactor

variable {R : Type*} [CommRing R] {n : ℕ} {A L Q : Matrix (Fin n) (Fin n) R} {s : Fin n → R}

/-- **The leading invariant factors divide the minors.** If `L * A * Q = diagonal s` with `L`, `Q`
of unit determinant and `s` a divisibility chain, then the product of the first `k` entries of `s`
divides every `k × k` minor of `A`, on arbitrary rows and columns. -/
theorem prod_dvd_det_submatrix_of_mul_mul_eq_diagonal (hL : IsUnit L.det) (hQ : IsUnit Q.det)
    (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j) (h : L * A * Q = diagonal s) {k : ℕ} (hk : k ≤ n)
    (f g : Fin k → Fin n) : ∏ j : Fin k, s (Fin.castLE hk j) ∣ (A.submatrix f g).det := by
  rw [← (GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq (nonsingInvUnit L hL)
    (nonsingInvUnit Q hQ)).2 h]
  refine dvd_det_submatrix_mul_mul (fun f' g' ↦ ?_) _ _ f g
  simpa using prod_castLE_mul_prod_castLE_dvd_det_submatrix_diagonal_mul_diagonal hs
    (c₂ := 1) (fun _ _ _ ↦ dvd_rfl) 1 hk f' g'

/-- **Common divisors of the minors divide the leading invariant factors.** If
`L * A * Q = diagonal s` and `c` divides every `k × k` minor of `A`, then `c` divides the product
of the first `k` entries of `s`. Together with
`Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal`, this product is a greatest common divisor
of the `k × k` minors of `A`. -/
theorem dvd_prod_of_mul_mul_eq_diagonal (h : L * A * Q = diagonal s) {k : ℕ} (hk : k ≤ n)
    {c : R} (hc : ∀ f g : Fin k → Fin n, c ∣ (A.submatrix f g).det) :
    c ∣ ∏ j : Fin k, s (Fin.castLE hk j) := by
  rw [← det_submatrix_diagonal s (Fin.castLE_injective hk), ← h]
  exact dvd_det_submatrix_mul_mul hc L Q _ _

variable {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀] {v : AddValuation R Γ₀}

/-- **Lower bound for the valuations of the minors.** For a valuation which is nonnegative on the
whole ring and a Smith normal form `L * A * Q = diagonal s`, every `k × k` minor of `A` has
valuation at least `v s₀ + ⋯ + v sₖ₋₁`. -/
theorem prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j)
    (h : L * A * Q = diagonal s) {k : ℕ} (hk : k ≤ n) (f g : Fin k → Fin n) :
    (prefixSum k fun i ↦ v (s i)) ≤ v (A.submatrix f g).det := by
  rw [← v.map_prod_castLE hk]
  exact AddValuation.map_le_map_of_dvd hv
    (prod_dvd_det_submatrix_of_mul_mul_eq_diagonal hL hQ hs h hk f g)

/-- **The least valuation of a minor.** For a valuation which is nonnegative on the whole ring and
a Smith normal form `L * A * Q = diagonal s`, some `k × k` minor of `A` has valuation exactly
`v s₀ + ⋯ + v sₖ₋₁`, which is therefore the least valuation of a `k × k` minor of `A`. -/
theorem exists_valuation_det_submatrix_eq_prefixSum_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j)
    (h : L * A * Q = diagonal s) {k : ℕ} (hk : k ≤ n) :
    ∃ f g : Fin k → Fin n, v (A.submatrix f g).det = prefixSum k fun i ↦ v (s i) := by
  -- a minor of least valuation exists among the finitely many `k × k` minors
  obtain ⟨p, -, hp⟩ := exists_min_image univ (fun p : (Fin k → Fin n) × (Fin k → Fin n) ↦
    v (A.submatrix p.1 p.2).det) ⟨(Fin.castLE hk, Fin.castLE hk), mem_univ _⟩
  refine ⟨p.1, p.2, le_antisymm ?_
    (prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal hv hL hQ hs h hk _ _)⟩
  rw [← v.map_prod_castLE hk, ← det_submatrix_diagonal s (Fin.castLE_injective hk), ← h]
  exact le_valuation_det_submatrix_mul_mul hv (fun f g ↦ hp (f, g) (mem_univ _)) L Q _ _

/-- **Lower bound for the valuations of the principal minors.** For a valuation which is
nonnegative on the whole ring and a Smith normal form `L * A * Q = diagonal s`, the principal minor
of `A` on a set `t` of indices has valuation at least the sum of the valuations of the first `#t`
entries of `s`. -/
theorem prefixSum_le_valuation_principalMinor_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j)
    (h : L * A * Q = diagonal s) (t : Finset (Fin n)) :
    (prefixSum #t fun i ↦ v (s i)) ≤ v (A.principalMinor t) := by
  -- enumerate `t` by `Fin #t` to view the principal minor as a `#t × #t` minor
  set e := t.equivFin.symm
  rw [principalMinor_def, ← det_submatrix_equiv_self e, submatrix_submatrix]
  exact prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal hv hL hQ hs h
    (t.card_le_univ.trans_eq (Fintype.card_fin n)) _ _

/-- For a valuation which is nonnegative on the whole ring and `L * A * Q = diagonal s` with `L`,
`Q` of unit determinant, the valuation of `det A` is the sum of the valuations of the entries
of `s`. -/
theorem valuation_det_eq_sum_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x) (hL : IsUnit L.det)
    (hQ : IsUnit Q.det) (h : L * A * Q = diagonal s) : v A.det = ∑ i, v (s i) := by
  have hdet := congrArg (fun M ↦ v M.det) h
  simp only [det_mul, det_diagonal, v.map_mul, AddValuation.map_prod,
    AddValuation.map_eq_zero_of_isUnit hv hL, AddValuation.map_eq_zero_of_isUnit hv hQ, zero_add,
    add_zero] at hdet
  exact hdet

end InvariantFactor

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  {A L Q L' Q' : Matrix (Fin n) (Fin n) R} {ϖ : R} {α β : Fin n → ℕ}

/-- **Uniqueness of the Smith normal form over a discrete valuation ring.** If
`L * A * Q = diagonal (ϖ ^ α)` and `L' * A * Q' = diagonal (ϖ ^ β)` for a uniformizer `ϖ`,
monotone exponents `α`, `β` and `L`, `Q`, `L'`, `Q'` of unit determinant, then `α = β`. -/
theorem eq_of_mul_mul_eq_diagonal_pow (hϖ : Irreducible ϖ) (hα : Monotone α) (hβ : Monotone β)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hL' : IsUnit L'.det) (hQ' : IsUnit Q'.det)
    (h : L * A * Q = diagonal fun i ↦ ϖ ^ α i) (h' : L' * A * Q' = diagonal fun i ↦ ϖ ^ β i) :
    α = β := by
  set v := IsDiscreteValuationRing.addVal R
  have hv : ∀ x, 0 ≤ v x := fun _ ↦ zero_le
  have hval (γ : Fin n → ℕ) : (fun i ↦ v (ϖ ^ γ i)) = fun i ↦ ((γ i : ℕ) : ℕ∞) := by
    simp [v, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  -- the least valuation of a `k × k` minor of `A` is the prefix sum of either exponent vector
  have hprefix (k : ℕ) (hk : k ≤ n) : prefixSum k α = prefixSum k β := by
    have key {γ δ : Fin n → ℕ} (hγ : Monotone γ) (hδ : Monotone δ) {L₁ Q₁ L₂ Q₂ : Matrix _ _ R}
        (hL₁ : IsUnit L₁.det) (hQ₁ : IsUnit Q₁.det) (hL₂ : IsUnit L₂.det) (hQ₂ : IsUnit Q₂.det)
        (h₁ : L₁ * A * Q₁ = diagonal fun i ↦ ϖ ^ γ i)
        (h₂ : L₂ * A * Q₂ = diagonal fun i ↦ ϖ ^ δ i) : prefixSum k γ ≤ prefixSum k δ := by
      obtain ⟨f, g, hfg⟩ := exists_valuation_det_submatrix_eq_prefixSum_of_mul_mul_eq_diagonal
        hv hL₂ hQ₂ (fun _ _ hij ↦ pow_dvd_pow ϖ (hδ hij)) h₂ hk
      have hle := prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal
        hv hL₁ hQ₁ (fun _ _ hij ↦ pow_dvd_pow ϖ (hγ hij)) h₁ hk f g
      rw [hval] at hfg hle
      have hcast (ε : Fin n → ℕ) : (prefixSum k fun i ↦ ((ε i : ℕ) : ℕ∞)) = prefixSum k ε := by
        simp [prefixSum_def]
      rw [hcast] at hle hfg
      exact_mod_cast hle.trans hfg.le
    exact le_antisymm (key hα hβ hL hQ hL' hQ' h h') (key hβ hα hL' hQ' hL hQ h' h)
  funext i
  have h₁ := hprefix (i + 1) i.isLt
  rw [prefixSum_succ i.isLt, prefixSum_succ i.isLt, hprefix i i.isLt.le] at h₁
  exact Nat.add_left_cancel h₁

end DiscreteValuationRing

end Matrix
