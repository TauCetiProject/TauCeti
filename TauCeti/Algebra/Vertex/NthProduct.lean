/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.HasseDeriv
public import TauCeti.Algebra.Vertex.ResidueProduct
public import TauCeti.Algebra.Vertex.NormalOrder
public import Mathlib.Algebra.Lie.OfAssociative
-- Proof-only: formal distributions for binomial difference powers and module normalization.
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Tactic.Module

/-!
# The `n`-th products of vertex operators and Dong's lemma

For fields `A(z)` and `B(w)` and any integer `n : ℤ`, the `n`-th product `A(w)₍ₙ₎ B(w)` is the
residue field `Res_z (i_{z,w} (z - w)ⁿ A(z) B(w) - i_{w,z} (z - w)ⁿ B(w) A(z))`. In normalized
modes its action on a vector `v` is

`((A₍ₙ₎ B)[[m]]) v = ∑ᶠ i : ℕ, (-1)ⁱ • choose n i • A[[n - i]] (B[[m + i]] v)`
`                    - ∑ᶠ i : ℕ, (-1)^|n| • (-1)ⁱ • choose n i • B[[n + m - i]] (A[[i]] v)`.

Both infinite sums are finite on every vector without any locality assumption, and their
coefficients again define a field (`VertexOperator.nthProduct`).

This single family unifies the singular and nonsingular field operations:
* for `n : ℕ`, `nthProduct n A B` is the singular commutator residue
  `VertexOperator.nonnegResidueProduct n A B`;
* for `n = -1`, `nthProduct (-1) A B` is the normal-ordered product
  `VertexOperator.normalOrder A B`;
* for `n = -k - 1`, `nthProduct (-k - 1) A B = normalOrder (hasseDeriv k A) B`.

Finally we prove **Dong's lemma** (`VertexOperator.IsLocalOfOrder.nthProduct`) over an arbitrary
commutative ring: if `(A, B)`, `(A, C)` and `(B, C)` are mutually local of order `r`, then
`nthProduct n A B` and `C` are mutually local of order `3 * r + n.natAbs`.

## Main definitions

* `VertexOperator.nthProductCoeff`: the `m`-th normalized mode of the `n`-th product of two fields.
* `VertexOperator.nthProduct`: the `n`-th product of fields as an `R`-bilinear map.

## Main results

* `VertexOperator.nthProduct_natCast`: `nthProduct (n : ℤ) A B = nonnegResidueProduct n A B`.
* `VertexOperator.nthProduct_neg_one`: `nthProduct (-1) A B = normalOrder A B`.
* `VertexOperator.nthProduct_neg_succ`:
  `nthProduct (-k - 1) A B = normalOrder (hasseDeriv k A) B`.
* `VertexOperator.nthProduct_derivative_left`:
  `nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B`.
* `VertexOperator.lie_ncoeff_nthProduct`: translation covariance passes to `nthProduct`.
* `VertexOperator.IsLocalOfOrder.nthProduct`: **Dong's lemma** for all integer `n`-th products,
  with corollaries `IsLocalOfOrder.nonnegResidueProduct` and `IsLocalOfOrder.normalOrder`.

## References

* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Lemma 2.3.1 (Dong's lemma) and Proposition 2.3.5.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.1 and §3.2 (Lemma 3.2, Dong's lemma).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.1 and §3.2.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Construction of the `n`-th product -/

private theorem support_nthProduct_left_subset (A B : VertexOperator R V) (n m : ℤ) (v : V)
    {P : ℕ} (hP : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0) :
    (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) ⊆ range P := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp [hP i h])

private theorem support_nthProduct_right_subset (A B : VertexOperator R V) (n m : ℤ) (v : V)
    {Q : ℕ} (hQ : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0) :
    (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)) ⊆ range Q := by
  intro i hi
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (by simp [hQ i h])

private theorem finite_support_nthProduct_left (A B : VertexOperator R V) (n m : ℤ) (v : V) :
    (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)).Finite := by
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  exact (finite_toSet (range (N + m.natAbs))).subset
    (support_nthProduct_left_subset A B n m v fun _ hi ↦ hN _ (by omega))

private theorem finite_support_nthProduct_right (A B : VertexOperator R V) (n m : ℤ) (v : V) :
    (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)).Finite := by
  obtain ⟨N, hN⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  exact (finite_toSet (range N)).subset
    (support_nthProduct_right_subset A B n m v fun _ hi ↦ hN _ (by omega))

private theorem nthProduct_sums_add (A B C D : VertexOperator R V) (n m : ℤ) (v w : V) :
    (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v) +
        (-1 : ℤ) ^ i • Ring.choose n i • (C[[n - i]]) ((D[[m + i]]) w))) -
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + m - i]]) ((A[[(i : ℤ)]]) v) +
        (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (D[[n + m - i]]) ((C[[(i : ℤ)]]) w))) =
    ((∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)) +
    ((∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • (C[[n - i]]) ((D[[m + i]]) w)) -
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (D[[n + m - i]]) ((C[[(i : ℤ)]]) w)) := by
  rw [finsum_add_distrib (finite_support_nthProduct_left A B n m v)
      (finite_support_nthProduct_left C D n m w),
    finsum_add_distrib (finite_support_nthProduct_right A B n m v)
      (finite_support_nthProduct_right C D n m w)]
  abel

private theorem nthProduct_sums_smul (r : R) (A B : VertexOperator R V) (n m : ℤ) (v : V) :
    (∑ᶠ i : ℕ, r • ((-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v))) -
      (∑ᶠ i : ℕ, r • ((-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v))) =
    r • ((∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)) := by
  rw [← smul_finsum' r (finite_support_nthProduct_left A B n m v),
    ← smul_finsum' r (finite_support_nthProduct_right A B n m v), smul_sub]

/-- The `m`-th normalized mode `(A₍ₙ₎ B)[[m]]` of the `n`-th product of fields `A` and `B`. -/
def nthProductCoeff (A B : VertexOperator R V) (n m : ℤ) : Module.End R V where
  toFun v :=
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)
  map_add' v w := by
    simpa only [map_add, smul_add] using nthProduct_sums_add A B A B n m v w
  map_smul' r v := by
    simpa only [map_smul, RingHom.id_apply, smul_comm r] using
      nthProduct_sums_smul r A B n m v

/-- Pointwise formula for the `m`-th normalized mode of the `n`-th product. -/
@[simp]
theorem nthProductCoeff_apply (A B : VertexOperator R V) (n m : ℤ) (v : V) :
    nthProductCoeff A B n m v =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + m - i]]) ((A[[(i : ℤ)]]) v) := (rfl)

/-- Additivity of `nthProductCoeff` in the first field. -/
@[simp]
theorem nthProductCoeff_add_left (A B C : VertexOperator R V) (n m : ℤ) :
    nthProductCoeff (A + B) C n m = nthProductCoeff A C n m + nthProductCoeff B C n m := by
  ext v
  simpa only [map_add, Pi.add_apply, LinearMap.add_apply, nthProductCoeff_apply, smul_add] using
    nthProduct_sums_add A C B C n m v v

/-- Additivity of `nthProductCoeff` in the second field. -/
@[simp]
theorem nthProductCoeff_add_right (A B C : VertexOperator R V) (n m : ℤ) :
    nthProductCoeff A (B + C) n m = nthProductCoeff A B n m + nthProductCoeff A C n m := by
  ext v
  simpa only [map_add, Pi.add_apply, LinearMap.add_apply, nthProductCoeff_apply, smul_add] using
    nthProduct_sums_add A B A C n m v v

/-- Scalar linearity of `nthProductCoeff` in the first field. -/
@[simp]
theorem nthProductCoeff_smul_left (r : R) (A B : VertexOperator R V) (n m : ℤ) :
    nthProductCoeff (r • A) B n m = r • nthProductCoeff A B n m := by
  ext v
  simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply, nthProductCoeff_apply,
    smul_comm r] using nthProduct_sums_smul r A B n m v

/-- Scalar linearity of `nthProductCoeff` in the second field. -/
@[simp]
theorem nthProductCoeff_smul_right (r : R) (A B : VertexOperator R V) (n m : ℤ) :
    nthProductCoeff A (r • B) n m = r • nthProductCoeff A B n m := by
  ext v
  simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply, nthProductCoeff_apply,
    smul_comm r] using nthProduct_sums_smul r A B n m v

/-- Explicit finite-sum evaluation of `nthProductCoeff` given truncation cutoffs for `B` and `A`
on `v`. -/
theorem nthProductCoeff_eq_sum (A B : VertexOperator R V) (n m : ℤ) (v : V)
    {P Q : ℕ} (hP : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0)
    (hQ : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0) :
    nthProductCoeff A B n m v =
      (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
        ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + m - i]]) ((A[[(i : ℤ)]]) v) := by
  rw [nthProductCoeff_apply,
    finsum_eq_sum_of_support_subset _ (support_nthProduct_left_subset A B n m v hP),
    finsum_eq_sum_of_support_subset _ (support_nthProduct_right_subset A B n m v hQ)]

private theorem exists_forall_nthProductCoeff_eq_zero (A B : VertexOperator R V) (n : ℤ) (v : V) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → nthProductCoeff A B n m v = 0 := by
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  choose C hC using fun i : ℕ ↦ B.exists_forall_ncoeff_apply_eq_zero ((A[[(i : ℤ)]]) v)
  refine ⟨max P (n.natAbs + Q + ∑ i ∈ range Q, C i), fun m hm ↦ ?_⟩
  rw [nthProductCoeff_eq_sum A B n m v (P := 0) (Q := Q)
    (fun _ _ ↦ hP _ (by omega)) (fun _ hi ↦ hQ _ (by omega))]
  simp only [range_zero, sum_empty, zero_sub, neg_eq_zero]
  refine sum_eq_zero fun i hi ↦ ?_
  have hle := single_le_sum (f := C) (fun j _ ↦ Nat.zero_le (C j)) hi
  have hi' := mem_range.mp hi
  rw [hC i _ (by omega), smul_zero, smul_zero, smul_zero]

/-- The `n`-th product `(A, B) ↦ A₍ₙ₎ B` of fields as an `R`-bilinear map, defined for all
integers `n : ℤ` without any locality hypothesis. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A :=
    { toFun B := of_coeff (fun k ↦ nthProductCoeff A B n (-k - 1)) fun v ↦ by
        obtain ⟨N, hN⟩ := exists_forall_nthProductCoeff_eq_zero A B n v
        refine ⟨-(N : ℤ), fun k hk ↦ ?_⟩
        by_contra! h
        exact hk (hN _ (by omega))
      map_add' B C := ext_ncoeff fun m ↦ by simp
      map_smul' r B := ext_ncoeff fun m ↦ by simp }
  map_add' A B := LinearMap.ext fun C ↦ ext_ncoeff fun m ↦ by simp
  map_smul' r A := LinearMap.ext fun B ↦ ext_ncoeff fun m ↦ by simp

/-- The normalized modes of `nthProduct n A B` are `nthProductCoeff A B n`. -/
@[simp]
theorem ncoeff_nthProduct (n : ℤ) (A B : VertexOperator R V) (m : ℤ) :
    (nthProduct n A B)[[m]] = nthProductCoeff A B n m := by
  simp [nthProduct]

/-! ### Comparison with nonnegative residue products and normal ordering -/

private theorem neg_one_pow_sub {n i : ℕ} (hi : i ≤ n) :
    (-1 : ℤ) ^ n * (-1 : ℤ) ^ i = (-1 : ℤ) ^ (n - i) := by
  have hn : n = n - i + i := (Nat.sub_add_cancel hi).symm
  conv_lhs => rw [hn, pow_add, mul_assoc, ← mul_pow]
  simp

/-- For `n : ℕ`, the `n`-th product coincides with the nonnegative residue product
`Res_z (z - w)ⁿ [A(z), B(w)]`. -/
@[simp]
theorem nthProduct_natCast (n : ℕ) (A B : VertexOperator R V) :
    nthProduct (n : ℤ) A B = nonnegResidueProduct n A B := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  rw [ncoeff_nthProduct, nthProductCoeff_apply, ncoeff_nonnegResidueProduct]
  have hsupp₁ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ i • Ring.choose (n : ℤ) i • (A[[(n : ℤ) - i]]) ((B[[m + i]]) v)) ⊆
      range (n + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : n < i)])
  have hsupp₂ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ (n : ℤ).natAbs • (-1 : ℤ) ^ i • Ring.choose (n : ℤ) i •
        (B[[(n : ℤ) + m - i]]) ((A[[(i : ℤ)]]) v)) ⊆ range (n + 1) := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : n < i)])
  rw [finsum_eq_sum_of_support_subset _ hsupp₁, finsum_eq_sum_of_support_subset _ hsupp₂,
    ← sum_range_reflect (fun i ↦ (-1 : ℤ) ^ i • Ring.choose (n : ℤ) i •
      (A[[(n : ℤ) - i]]) ((B[[m + i]]) v)) (n + 1)]
  simp only [Nat.add_sub_cancel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_sub, sum_sub_distrib,
    Int.natAbs_natCast, Ring.choose_natCast]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : (n : ℤ) - ↑(n - i) = (i : ℤ) := by omega
    rw [hidx, Nat.choose_symm hi', natCast_zsmul]
    module
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : (n : ℤ) + m - i = m + ↑(n - i) := by omega
    rw [hidx, ← mul_smul ((-1 : ℤ) ^ n), neg_one_pow_sub hi', natCast_zsmul]
    module

private theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← mul_pow]
  simp

private theorem nthProduct_neg_succ_left_sum (k : ℕ) (A B : VertexOperator R V) (m : ℤ) (v : V)
    (P : ℕ) :
    ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose (-(k : ℤ) - 1) i •
        (A[[-(k : ℤ) - 1 - i]]) ((B[[m + i]]) v) =
      ∑ i ∈ range P, ((hasseDeriv k A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v) := by
  refine sum_congr rfl fun i _ ↦ ?_
  have h₁ : -(k : ℤ) - 1 = -(k + 1 : ℤ) := by omega
  have h₂ : -(i : ℤ) - 1 = -(i + 1 : ℤ) := by omega
  have h₃ : (k : ℤ) + 1 + i - 1 = ↑(k + i) := by omega
  have h₄ : (i : ℤ) + 1 + k - 1 = ↑(i + k) := by omega
  have h₅ : -(k : ℤ) - 1 - i = -(i : ℤ) - 1 - k := by omega
  rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, h₅, h₁, h₂,
    Ring.choose_neg, Ring.choose_neg, h₃, h₄, Units.smul_def, Units.smul_def,
    Int.coe_negOnePow_natCast, Int.coe_negOnePow_natCast, Ring.choose_natCast,
    Ring.choose_natCast, add_comm i k, Nat.choose_symm_add]
  simp only [smul_eq_mul, ← mul_smul, ← mul_assoc, neg_one_pow_mul_self, one_mul]

/-- Negative `n`-th products are normal-ordered products with Hasse derivatives:
`A₍₋ₖ₋₁₎ B = :(∂_z^(k) A) B:`. -/
theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDeriv k A) B := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := P₀ + m.natAbs
  have hP : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0 := fun _ hi ↦ hP₀ _ (by omega)
  have hQ₁ : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0 := fun _ hi ↦ hQ _ (by omega)
  have hQ' : ∀ j : ℕ, k + Q ≤ j → ((hasseDeriv k A)[[(j : ℤ)]]) v = 0 := fun j hj ↦ by
    rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, hQ _ (by omega),
      smul_zero, smul_zero]
  rw [ncoeff_nthProduct, nthProductCoeff_eq_sum A B _ m v hP hQ₁,
    ncoeff_normalOrder, normalOrderCoeff_eq_sum _ B m v hP hQ']
  have hneg : (-(k : ℤ) - 1).natAbs = k + 1 := by omega
  have hright_split : ∑ j ∈ range (k + Q), (B[[m - j - 1]]) (((hasseDeriv k A)[[(j : ℤ)]]) v) =
      ∑ i ∈ range Q, (B[[m - ↑(k + i) - 1]]) (((hasseDeriv k A)[[↑(k + i)]]) v) := by
    rw [sum_range_add, sum_eq_zero (fun j hj ↦ by
      simp [ncoeff_hasseDeriv, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (mem_range.mp hj)]),
      zero_add]
  rw [nthProduct_neg_succ_left_sum, sub_eq_add_neg, ← sum_neg_distrib, hright_split]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  have h₁ : -(k : ℤ) - 1 = -(k + 1 : ℤ) := by omega
  have h₂ : (k : ℤ) + 1 + i - 1 = ↑(k + i) := by omega
  have h₃ : -(k : ℤ) - 1 + m - i = m - ↑(k + i) - 1 := by omega
  have h₄ : ((k + i : ℕ) : ℤ) - k = (i : ℤ) := by omega
  rw [hneg, h₃, h₁, Ring.choose_neg, h₂, ncoeff_hasseDeriv, h₄, Units.smul_def,
    Int.coe_negOnePow_natCast, Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm_add]
  simp only [LinearMap.smul_apply, map_zsmul, smul_eq_mul, ← mul_smul, pow_succ (-1 : ℤ) k,
    mul_neg, mul_one, ← neg_smul]
  refine congrArg (· • (B[[m - ↑(k + i) - 1]]) ((A[[(i : ℤ)]]) v)) ?_
  linear_combination (-1 : ℤ) ^ k * ↑((k + i).choose i) * neg_one_pow_mul_self i

/-- The `(-1)`-st product of fields is their normal-ordered product. -/
@[simp]
theorem nthProduct_neg_one (A B : VertexOperator R V) :
    nthProduct (-1) A B = normalOrder A B := by
  simpa using nthProduct_neg_succ 0 A B

/-! ### Vacuum evaluation and formal derivatives -/

/-- If `A` and `B` have no negative powers on a vector `vac`, neither does `nthProduct n A B`. -/
theorem ncoeff_nthProduct_apply_of_nonneg {A B : VertexOperator R V} {vac : V}
    (hA : ∀ k : ℤ, 0 ≤ k → (A[[k]]) vac = 0) (hB : ∀ k : ℤ, 0 ≤ k → (B[[k]]) vac = 0)
    (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) vac = 0 := by
  rw [ncoeff_nthProduct, nthProductCoeff_eq_sum A B n m vac (P := 0) (Q := 0)
    (fun _ _ ↦ hB _ (by omega)) (fun _ _ ↦ hA _ (by omega))]
  simp

/-- If `A` and `B` have no negative powers on `vac`, the constant term of `(A₍ₙ₎ B)(z) vac` is
`A[[n]] (B[[-1]] vac)`. -/
theorem ncoeff_neg_one_nthProduct_apply {A B : VertexOperator R V} {vac : V}
    (hA : ∀ k : ℤ, 0 ≤ k → (A[[k]]) vac = 0) (hB : ∀ k : ℤ, 0 ≤ k → (B[[k]]) vac = 0)
    (n : ℤ) :
    ((nthProduct n A B)[[-1]]) vac = (A[[n]]) ((B[[-1]]) vac) := by
  rw [ncoeff_nthProduct, nthProductCoeff_eq_sum A B n (-1) vac (P := 1) (Q := 0)
    (fun _ hi ↦ hB _ (by omega)) (fun _ _ ↦ hA _ (by omega))]
  simp

private theorem succ_mul_choose_succ (n : ℤ) (i : ℕ) :
    ((i : ℤ) + 1) * Ring.choose n (i + 1) = (n - i) * Ring.choose n i := by
  have h := Ring.choose_smul_choose n (Nat.le_succ i)
  rw [Nat.succ_eq_add_one, Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
    Ring.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    mul_comm (Ring.choose n i)] at h
  exact h

private theorem mul_choose_sub_one (n : ℤ) (i : ℕ) :
    (n - i) * Ring.choose n i = n * Ring.choose (n - 1) i := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    have h₁ := succ_mul_choose_succ n i
    have h₂ := succ_mul_choose_succ (n - 1) i
    have hsub : n - 1 - (i : ℤ) = n - ↑(i + 1) := by omega
    rw [hsub] at h₂
    apply mul_left_cancel₀ (by positivity : ((i : ℤ) + 1) ≠ 0)
    calc
      ((i : ℤ) + 1) * ((n - ↑(i + 1)) * Ring.choose n (i + 1))
          = (n - ↑(i + 1)) * (((i : ℤ) + 1) * Ring.choose n (i + 1)) := by ring
      _ = (n - ↑(i + 1)) * (n * Ring.choose (n - 1) i) := by rw [h₁, ih n]
      _ = n * ((n - ↑(i + 1)) * Ring.choose (n - 1) i) := by ring
      _ = n * (((i : ℤ) + 1) * Ring.choose (n - 1) (i + 1)) := by rw [h₂]
      _ = ((i : ℤ) + 1) * (n * Ring.choose (n - 1) (i + 1)) := by ring

/-- Differentiating the first field in an `n`-th product lowers `n` by one:
`(∂_z A)₍ₙ₎ B = (-n) • A₍ₙ₋₁₎ B`. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₀, hQ₀⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := P₀ + m.natAbs
  have hP : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0 := fun _ hi ↦ hP₀ _ (by omega)
  have hQ₁ : ∀ i : ℕ, Q₀ + 1 ≤ i → ((derivative A)[[(i : ℤ)]]) v = 0 := fun i hi ↦ by
    rw [ncoeff_derivative, LinearMap.smul_apply, hQ₀ _ (by omega), smul_zero]
  have hQ₂ : ∀ i : ℕ, Q₀ ≤ i → (A[[(i : ℤ)]]) v = 0 := fun _ hi ↦ hQ₀ _ (by omega)
  rw [map_zsmul, Pi.smul_apply, LinearMap.smul_apply, ncoeff_nthProduct, ncoeff_nthProduct,
    nthProductCoeff_eq_sum (derivative A) B n m v hP hQ₁,
    nthProductCoeff_eq_sum A B (n - 1) m v hP hQ₂, smul_sub, smul_sum, smul_sum]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [ncoeff_derivative, LinearMap.smul_apply]
    have hidx : n - (i : ℤ) - 1 = n - 1 - i := by omega
    have hc := mul_choose_sub_one n i
    rw [hidx]
    simp only [← mul_smul]
    exact congrArg (· • (A[[n - 1 - i]]) ((B[[m + i]]) v))
      (by linear_combination -((-1 : ℤ) ^ i) * hc)
  · rw [sum_range_succ']
    simp only [Nat.cast_zero, ncoeff_derivative, neg_zero, zero_smul, LinearMap.zero_apply,
      map_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ ↦ ?_
    have hsign : (-1 : ℤ) ^ n.natAbs = -((-1 : ℤ) ^ (n - 1).natAbs) := by
      rw [← Int.coe_negOnePow ℤ n, ← Int.coe_negOnePow ℤ (n - 1)]
      have hn : n = n - 1 + 1 := by omega
      conv_lhs => rw [hn, Int.negOnePow_succ]
      simp
    have hc : ((i : ℤ) + 1) * Ring.choose n (i + 1) = n * Ring.choose (n - 1) i :=
      (succ_mul_choose_succ n i).trans (mul_choose_sub_one n i)
    have hidx₁ : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by omega
    have hidx₂ : n + m - ↑(i + 1) = n - 1 + m - i := by omega
    rw [hidx₁, hidx₂, hsign, pow_succ (-1 : ℤ) i]
    simp only [LinearMap.smul_apply, map_zsmul, ← mul_smul]
    refine congrArg (· • (B[[n - 1 + m - i]]) ((A[[(i : ℤ)]]) v)) ?_
    push_cast
    linear_combination -((-1 : ℤ) ^ (n - 1).natAbs * (-1 : ℤ) ^ i) * hc

private theorem lie_nthProduct_left_term {T : Module.End R V} {A B : VertexOperator R V}
    (hTA : ∀ (p : ℤ) (w : V), T ((A[[p]]) w) = (-p) • (A[[p - 1]]) w + (A[[p]]) (T w))
    (hTB : ∀ (p : ℤ) (w : V), T ((B[[p]]) w) = (-p) • (B[[p - 1]]) w + (B[[p]]) (T w))
    (n m : ℤ) (v : V) (i : ℕ) :
    T ((-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) v)) -
        (-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m + i]]) (T v)) -
        (-m) • ((-1 : ℤ) ^ i • Ring.choose n i • (A[[n - i]]) ((B[[m - 1 + i]]) v)) =
      (-1 : ℤ) ^ (i + 1) • ((↑(i + 1) : ℤ) * Ring.choose n (i + 1)) •
          (A[[n - ↑(i + 1)]]) ((B[[m - 1 + ↑(i + 1)]]) v) -
        (-1 : ℤ) ^ i • ((i : ℤ) * Ring.choose n i) • (A[[n - i]]) ((B[[m - 1 + i]]) v) := by
  simp only [map_zsmul, hTA, hTB, map_add, smul_add]
  have hc := succ_mul_choose_succ n i
  have h₁ : n - (i : ℤ) - 1 = n - ↑(i + 1) := by omega
  have h₂ : m + (i : ℤ) - 1 = m - 1 + i := by omega
  have h₃ : m + (i : ℤ) = m - 1 + ↑(i + 1) := by omega
  rw [h₁, h₂, h₃, pow_succ (-1 : ℤ) i]
  simp only [← mul_smul, ← mul_assoc]
  have hcancel : (-1 : ℤ) ^ i * Ring.choose n i * (-(n - (i : ℤ))) =
      (-1 : ℤ) ^ i * -1 * ↑(i + 1) * Ring.choose n (i + 1) := by
    push_cast; linear_combination ((-1 : ℤ) ^ i) * hc
  have hm : (-1 : ℤ) ^ i * Ring.choose n i * (-(m - 1 + ↑(i + 1))) =
      (-m) * (-1 : ℤ) ^ i * Ring.choose n i - (-1 : ℤ) ^ i * (i : ℤ) * Ring.choose n i := by
    push_cast; ring
  rw [hcancel, hm, sub_smul]
  abel

private theorem lie_nthProduct_right_term {T : Module.End R V} {A B : VertexOperator R V}
    (hTA : ∀ (p : ℤ) (w : V), T ((A[[p]]) w) = (-p) • (A[[p - 1]]) w + (A[[p]]) (T w))
    (hTB : ∀ (p : ℤ) (w : V), T ((B[[p]]) w) = (-p) • (B[[p - 1]]) w + (B[[p]]) (T w))
    (n m : ℤ) (v : V) (i : ℕ) :
    T ((-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + m - i]]) ((A[[(i : ℤ)]]) v)) -
        (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + m - i]]) ((A[[(i : ℤ)]]) (T v)) -
        (-m) • ((-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (B[[n + (m - 1) - i]]) ((A[[(i : ℤ)]]) v)) =
      (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ (i + 1) • ((↑(i + 1) : ℤ) * Ring.choose n (i + 1)) •
          (B[[n + m - ↑(i + 1)]]) ((A[[((i + 1 : ℕ) : ℤ) - 1]]) v) -
        (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • ((i : ℤ) * Ring.choose n i) •
          (B[[n + m - i]]) ((A[[(i : ℤ) - 1]]) v) := by
  simp only [map_zsmul, hTA, hTB, map_add, smul_add]
  have hc := succ_mul_choose_succ n i
  have h₁ : n + m - (i : ℤ) - 1 = n + m - ↑(i + 1) := by omega
  have h₂ : n + (m - 1) - (i : ℤ) = n + m - ↑(i + 1) := by omega
  have h₃ : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by omega
  rw [h₁, h₂, h₃, pow_succ (-1 : ℤ) i]
  simp only [← mul_smul, ← mul_assoc]
  have hBcoeff : (-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i * Ring.choose n i * (-(n + m - (i : ℤ))) =
      (-m) * (-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i * Ring.choose n i +
        (-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i * -1 * ↑(i + 1) * Ring.choose n (i + 1) := by
    push_cast; linear_combination ((-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i) * hc
  have hAcoeff : (-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i * Ring.choose n i * (-(i : ℤ)) =
      -((-1 : ℤ) ^ n.natAbs * (-1 : ℤ) ^ i * (i : ℤ) * Ring.choose n i) := by ring
  rw [hBcoeff, hAcoeff, add_smul, neg_smul]
  abel

/-- Translation covariance passes to all integer `n`-th products: if `[T, A[[k]]] = (∂A)[[k]]`
and `[T, B[[k]]] = (∂B)[[k]]`, then `[T, (nthProduct n A B)[[m]]] = (∂(nthProduct n A B))[[m]]`. -/
theorem lie_ncoeff_nthProduct {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ k : ℤ, ⁅T, A[[k]]⁆ = (derivative A)[[k]])
    (hB : ∀ k : ℤ, ⁅T, B[[k]]⁆ = (derivative B)[[k]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  ext v
  have hderiv {C : VertexOperator R V} (hC : ∀ k : ℤ, ⁅T, C[[k]]⁆ = (derivative C)[[k]])
      (p : ℤ) (w : V) : T ((C[[p]]) w) = (-p) • (C[[p - 1]]) w + (C[[p]]) (T w) := by
    have h := LinearMap.congr_fun (hC p) w
    rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      ncoeff_derivative, LinearMap.smul_apply, sub_eq_iff_eq_add] at h
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let P := max P₁ P₂ + m.natAbs + 2
  let Q := max Q₁ Q₂ + 1
  have hPv : ∀ i : ℕ, P ≤ i → (B[[m + i]]) v = 0 := fun _ hi ↦ hP₁ _ (by omega)
  have hPv' : ∀ i : ℕ, P ≤ i → (B[[m - 1 + i]]) v = 0 := fun _ hi ↦ hP₁ _ (by omega)
  have hPTv : ∀ i : ℕ, P ≤ i → (B[[m + i]]) (T v) = 0 := fun _ hi ↦ hP₂ _ (by omega)
  have hQv : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) v = 0 := fun _ hi ↦ hQ₁ _ (by omega)
  have hQTv : ∀ i : ℕ, Q ≤ i → (A[[(i : ℤ)]]) (T v) = 0 := fun _ hi ↦ hQ₂ _ (by omega)
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    ncoeff_derivative, LinearMap.smul_apply, ncoeff_nthProduct, ncoeff_nthProduct,
    nthProductCoeff_eq_sum A B n m v hPv hQv, nthProductCoeff_eq_sum A B n m (T v) hPTv hQTv,
    nthProductCoeff_eq_sum A B n (m - 1) v hPv' hQv, map_sub, map_sum, map_sum, smul_sub,
    ← sub_eq_zero]
  let g₁ : ℕ → V := fun i ↦
    (-1 : ℤ) ^ i • ((i : ℤ) * Ring.choose n i) • (A[[n - i]]) ((B[[m - 1 + i]]) v)
  let g₂ : ℕ → V := fun i ↦
    (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • ((i : ℤ) * Ring.choose n i) •
      (B[[n + m - i]]) ((A[[(i : ℤ) - 1]]) v)
  have hcomb : ∀ a₁ a₂ b₁ b₂ c₁ c₂ : V,
      (a₁ - a₂) - (b₁ - b₂) - (c₁ - c₂) = (a₁ - b₁ - c₁) - (a₂ - b₂ - c₂) := by intros; abel
  rw [hcomb, smul_sum, smul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_sub_distrib,
    sum_congr rfl fun i _ ↦ lie_nthProduct_left_term (hderiv hA) (hderiv hB) n m v i,
    sum_congr rfl fun i _ ↦ lie_nthProduct_right_term (hderiv hA) (hderiv hB) n m v i,
    sum_range_sub g₁ P, sum_range_sub g₂ Q]
  have hQ' : (A[[(Q : ℤ) - 1]]) v = 0 := hQ₁ _ (by omega)
  simp [g₁, g₂, hPv' P le_rfl, hQ']

/-! ### Dong's lemma -/

section Dong

/-- Difference operator in `(z, x)` on three-variable `V`-valued distributions `F p l q`. -/
private def mulSubZX (V : Type*) [AddCommGroup V] : AddMonoid.End (ℤ → ℤ → ℤ → V) where
  toFun F p l q := F (p + 1) l q - F p l (q + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSubZX_apply (F : ℤ → ℤ → ℤ → V) (p l q : ℤ) :
    mulSubZX V F p l q = F (p + 1) l q - F p l (q + 1) := (rfl)

/-- Difference operator in `(w, x)` on three-variable `V`-valued distributions `F p l q`. -/
private def mulSubWX (V : Type*) [AddCommGroup V] : AddMonoid.End (ℤ → ℤ → ℤ → V) where
  toFun F p l q := F p (l + 1) q - F p l (q + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSubWX_apply (F : ℤ → ℤ → ℤ → V) (p l q : ℤ) :
    mulSubWX V F p l q = F p (l + 1) q - F p l (q + 1) := (rfl)

private theorem commute_mulSubZX_mulSubWX :
    Commute (mulSubZX V) (mulSubWX V) := by
  ext F p l q
  simp only [AddMonoid.End.coe_mul, Function.comp_apply, mulSubZX_apply, mulSubWX_apply]
  abel

private theorem mulSubZX_pow_apply (N : ℕ) (F : ℤ → ℤ → ℤ → V) (p l q : ℤ) :
    ((mulSubZX V ^ N) F) p l q = ∑ ij ∈ antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • F (p + ij.1) l (q + ij.2) := by
  let c : TauCeti.FormalDistribution V := fun p' q' ↦ F p' l q'
  have h : ∀ k p' q', ((mulSubZX V ^ k) F) p' l q' =
      ((TauCeti.FormalDistribution.mulSub ^ k) c) p' q' := by
    intro k
    induction k with
    | zero => intro p' q'; rfl
    | succ k ih =>
      intro p' q'
      rw [pow_succ', pow_succ', AddMonoid.End.coe_mul, AddMonoid.End.coe_mul,
        Function.comp_apply, Function.comp_apply, mulSubZX_apply,
        TauCeti.FormalDistribution.mulSub_apply, ih, ih]
  rw [h N p q, TauCeti.FormalDistribution.mulSub_pow_apply]

private theorem mulSubWX_pow_apply (N : ℕ) (F : ℤ → ℤ → ℤ → V) (p l q : ℤ) :
    ((mulSubWX V ^ N) F) p l q = ∑ ij ∈ antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • F p (l + ij.1) (q + ij.2) := by
  let c : TauCeti.FormalDistribution V := fun l' q' ↦ F p l' q'
  have h : ∀ k l' q', ((mulSubWX V ^ k) F) p l' q' =
      ((TauCeti.FormalDistribution.mulSub ^ k) c) l' q' := by
    intro k
    induction k with
    | zero => intro l' q'; rfl
    | succ k ih =>
      intro l' q'
      rw [pow_succ', pow_succ', AddMonoid.End.coe_mul, AddMonoid.End.coe_mul,
        Function.comp_apply, Function.comp_apply, mulSubWX_apply,
        TauCeti.FormalDistribution.mulSub_apply, ih, ih]
  rw [h N l q, TauCeti.FormalDistribution.mulSub_pow_apply]

private def HasMiddleCutoff (F : ℤ → ℤ → ℤ → V) : Prop :=
  ∀ q : ℤ, ∃ P : ℕ, ∀ p l : ℤ, (P : ℤ) ≤ l → F p l q = 0

private def HasFirstCutoff (G : ℤ → ℤ → ℤ → V) : Prop :=
  ∀ q : ℤ, ∃ Q : ℕ, ∀ p l : ℤ, (Q : ℤ) ≤ p → G p l q = 0

private theorem HasMiddleCutoff.of_mulSubZX {F : ℤ → ℤ → ℤ → V} (hF : HasMiddleCutoff F) :
    HasMiddleCutoff (mulSubZX V F) := fun q ↦ by
  obtain ⟨P₁, h₁⟩ := hF q
  obtain ⟨P₂, h₂⟩ := hF (q + 1)
  refine ⟨max P₁ P₂, fun p l hl ↦ ?_⟩
  rw [mulSubZX_apply, h₁ (p + 1) l (by omega), h₂ p l (by omega), sub_zero]

private theorem HasMiddleCutoff.of_mulSubWX {F : ℤ → ℤ → ℤ → V} (hF : HasMiddleCutoff F) :
    HasMiddleCutoff (mulSubWX V F) := fun q ↦ by
  obtain ⟨P₁, h₁⟩ := hF q
  obtain ⟨P₂, h₂⟩ := hF (q + 1)
  refine ⟨max P₁ P₂, fun p l hl ↦ ?_⟩
  rw [mulSubWX_apply, h₁ p (l + 1) (by omega), h₂ p l (by omega), sub_zero]

private theorem HasMiddleCutoff.of_mulSubZX_pow {F : ℤ → ℤ → ℤ → V} (hF : HasMiddleCutoff F)
    (k : ℕ) : HasMiddleCutoff ((mulSubZX V ^ k) F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact ih.of_mulSubZX

private theorem HasMiddleCutoff.of_mulSubWX_pow {F : ℤ → ℤ → ℤ → V} (hF : HasMiddleCutoff F)
    (k : ℕ) : HasMiddleCutoff ((mulSubWX V ^ k) F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact ih.of_mulSubWX

private theorem HasFirstCutoff.of_mulSubZX {G : ℤ → ℤ → ℤ → V} (hG : HasFirstCutoff G) :
    HasFirstCutoff (mulSubZX V G) := fun q ↦ by
  obtain ⟨Q₁, h₁⟩ := hG q
  obtain ⟨Q₂, h₂⟩ := hG (q + 1)
  refine ⟨max Q₁ Q₂, fun p l hp ↦ ?_⟩
  rw [mulSubZX_apply, h₁ (p + 1) l (by omega), h₂ p l (by omega), sub_zero]

private theorem HasFirstCutoff.of_mulSubWX {G : ℤ → ℤ → ℤ → V} (hG : HasFirstCutoff G) :
    HasFirstCutoff (mulSubWX V G) := fun q ↦ by
  obtain ⟨Q₁, h₁⟩ := hG q
  obtain ⟨Q₂, h₂⟩ := hG (q + 1)
  refine ⟨max Q₁ Q₂, fun p l hp ↦ ?_⟩
  rw [mulSubWX_apply, h₁ p (l + 1) (by omega), h₂ p l (by omega), sub_zero]

private theorem HasFirstCutoff.of_mulSubZX_pow {G : ℤ → ℤ → ℤ → V} (hG : HasFirstCutoff G)
    (k : ℕ) : HasFirstCutoff ((mulSubZX V ^ k) G) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact ih.of_mulSubZX

private theorem HasFirstCutoff.of_mulSubWX_pow {G : ℤ → ℤ → ℤ → V} (hG : HasFirstCutoff G)
    (k : ℕ) : HasFirstCutoff ((mulSubWX V ^ k) G) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply]
    exact ih.of_mulSubWX

/-- The formal `n`-th residue functional combining `F` (expanded in `|z| > |w|`) and `G`
(expanded in `|w| > |z|`). -/
private def dongResidue (n : ℤ) (F G : ℤ → ℤ → ℤ → V) (m q : ℤ) : V :=
  (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + i) q) -
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i • G (i : ℤ) (n + m - i) q

private theorem dongResidue_eq_sum (n : ℤ) {F G : ℤ → ℤ → ℤ → V} (m q : ℤ) {P Q : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → F (n - i) (m + i) q = 0)
    (hQ : ∀ i : ℕ, Q ≤ i → G (i : ℤ) (n + m - i) q = 0) :
    dongResidue n F G m q =
      (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + i) q) -
        ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          G (i : ℤ) (n + m - i) q := by
  have hs₁ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + i) q) ⊆ range P := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h; exact hi (by simp [hP i h])
  have hs₂ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i • G (i : ℤ) (n + m - i) q) ⊆
      range Q := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h; exact hi (by simp [hQ i h])
  rw [dongResidue, finsum_eq_sum_of_support_subset _ hs₁, finsum_eq_sum_of_support_subset _ hs₂]

/-- Multiplying `dongResidue` by `w - x` commutes directly into `F` and `G`. -/
private theorem mulSub_dongResidue_eq_mulSubWX (n : ℤ) {F G : ℤ → ℤ → ℤ → V}
    (hF : HasMiddleCutoff F) (hG : HasFirstCutoff G) :
    TauCeti.FormalDistribution.mulSub (dongResidue n F G) =
      dongResidue n (mulSubWX V F) (mulSubWX V G) := by
  ext m q
  obtain ⟨P₁, hP₁⟩ := hF q
  obtain ⟨P₂, hP₂⟩ := hF (q + 1)
  obtain ⟨Q₁, hQ₁⟩ := hG q
  obtain ⟨Q₂, hQ₂⟩ := hG (q + 1)
  let P := max P₁ P₂ + m.natAbs + 1
  let Q := max Q₁ Q₂
  rw [TauCeti.FormalDistribution.mulSub_apply,
    dongResidue_eq_sum n (m + 1) q (P := P) (Q := Q)
      (fun i hi ↦ hP₁ (n - i) (m + 1 + i) (by omega))
      (fun i hi ↦ hQ₁ i (n + (m + 1) - i) (by omega)),
    dongResidue_eq_sum n m (q + 1) (P := P) (Q := Q)
      (fun i hi ↦ hP₂ (n - i) (m + i) (by omega))
      (fun i hi ↦ hQ₂ i (n + m - i) (by omega)),
    dongResidue_eq_sum n m q (P := P) (Q := Q)
      (fun i hi ↦ by
        rw [mulSubWX_apply, hP₁ (n - i) (m + i + 1) (by omega),
          hP₂ (n - i) (m + i) (by omega), sub_zero])
      (fun i hi ↦ by
        rw [mulSubWX_apply, hQ₁ i (n + m - i + 1) (by omega),
          hQ₂ i (n + m - i) (by omega), sub_zero])]
  have hcomb : ∀ a₁ a₂ b₁ b₂ : V, (a₁ - a₂) - (b₁ - b₂) = (a₁ - b₁) - (a₂ - b₂) := by
    intros; abel
  rw [hcomb, ← sum_sub_distrib, ← sum_sub_distrib]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i _ ↦ ?_
    have hidx : m + 1 + (i : ℤ) = m + i + 1 := by omega
    rw [mulSubWX_apply, hidx, smul_sub, smul_sub]
  · refine sum_congr rfl fun i _ ↦ ?_
    have hidx : n + (m + 1) - (i : ℤ) = n + m - i + 1 := by omega
    rw [mulSubWX_apply, hidx, smul_sub, smul_sub, smul_sub]

private theorem mulSub_pow_dongResidue_eq_mulSubWX_pow (k : ℕ) (n : ℤ) {F G : ℤ → ℤ → ℤ → V}
    (hF : HasMiddleCutoff F) (hG : HasFirstCutoff G) :
    (TauCeti.FormalDistribution.mulSub ^ k) (dongResidue n F G) =
      dongResidue n ((mulSubWX V ^ k) F) ((mulSubWX V ^ k) G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih,
      mulSub_dongResidue_eq_mulSubWX n (hF.of_mulSubWX_pow k) (hG.of_mulSubWX_pow k),
      ← Function.comp_apply (f := ⇑(mulSubWX V)), ← AddMonoid.End.coe_mul, ← pow_succ',
      ← Function.comp_apply (f := ⇑(mulSubWX V)), ← AddMonoid.End.coe_mul, ← pow_succ']

private theorem mulSub_dongResidue_left_sum (n m q : ℤ) (F : ℤ → ℤ → ℤ → V) {P : ℕ}
    (hP0 : P ≠ 0) (hFP : F (n - ↑(P - 1)) (m + 1 + ↑(P - 1)) q = 0) :
    ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + 1 + i) q -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + i) (q + 1) -
      (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • (mulSubZX V F) (n - i) (m + i) q -
        ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose (n + 1) i • F (n + 1 - i) (m + i) q) = 0 := by
  let h₁ : ℕ → V := fun i ↦
    if i = 0 then 0
    else (-1 : ℤ) ^ (i - 1) • Ring.choose n (i - 1) • F (n - ↑(i - 1)) (m + 1 + ↑(i - 1)) q
  have htel : (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + 1 + i) q -
      ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • F (n - i) (m + i) (q + 1) -
      (∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose n i • (mulSubZX V F) (n - i) (m + i) q -
        ∑ i ∈ range P, (-1 : ℤ) ^ i • Ring.choose (n + 1) i • F (n + 1 - i) (m + i) q)) =
      ∑ i ∈ range P, (h₁ (i + 1) - h₁ i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    cases i with
    | zero =>
      simp only [h₁, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.sub_self,
        Nat.cast_zero, pow_zero, Ring.choose_zero_right, one_smul, mulSubZX_apply, sub_zero,
        add_zero]
      abel
    | succ j =>
      simp only [h₁, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, mulSubZX_apply, Ring.choose_succ_succ n j, add_smul, smul_add, smul_sub]
      have ha : n - ↑(j + 1) + 1 = n - (j : ℤ) := by omega
      have hb : n + 1 - ↑(j + 1) = n - (j : ℤ) := by omega
      have hc : m + 1 + ↑(j + 1) = m + 1 + (j : ℤ) + 1 := by omega
      have hd : m + ↑(j + 1) = m + 1 + (j : ℤ) := by omega
      rw [ha, hb, hc, hd, pow_succ (-1 : ℤ) j]
      simp only [mul_neg, mul_one, neg_smul]
      abel
  rw [htel, sum_range_sub]
  simp [h₁, hP0, hFP]

private theorem mulSub_dongResidue_right_sum (n m q : ℤ) (G : ℤ → ℤ → ℤ → V) {Q : ℕ}
    (hQ0 : Q ≠ 0) (hGQ : G (↑(Q - 1) + 1) (n + m - ↑(Q - 1)) q = 0) :
    ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        G (i : ℤ) (n + (m + 1) - i) q -
      ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        G (i : ℤ) (n + m - i) (q + 1) -
      (∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (mulSubZX V G) (i : ℤ) (n + m - i) q -
        ∑ i ∈ range Q, (-1 : ℤ) ^ (n + 1).natAbs • (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
          G (i : ℤ) (n + 1 + m - i) q) = 0 := by
  have hsign : (-1 : ℤ) ^ (n + 1).natAbs = -((-1 : ℤ) ^ n.natAbs) := by
    rw [← Int.coe_negOnePow ℤ (n + 1), ← Int.coe_negOnePow ℤ n, Int.negOnePow_succ]
    simp
  let h₂ : ℕ → V := fun i ↦
    if i = 0 then 0
    else -((-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ (i - 1) • Ring.choose n (i - 1) •
      G (↑(i - 1) + 1) (n + m - ↑(i - 1)) q)
  have htel : (∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        G (i : ℤ) (n + (m + 1) - i) q -
      ∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
        G (i : ℤ) (n + m - i) (q + 1) -
      (∑ i ∈ range Q, (-1 : ℤ) ^ n.natAbs • (-1 : ℤ) ^ i • Ring.choose n i •
          (mulSubZX V G) (i : ℤ) (n + m - i) q -
        ∑ i ∈ range Q, (-1 : ℤ) ^ (n + 1).natAbs • (-1 : ℤ) ^ i • Ring.choose (n + 1) i •
          G (i : ℤ) (n + 1 + m - i) q)) = ∑ i ∈ range Q, (h₂ (i + 1) - h₂ i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    cases i with
    | zero =>
      have ha : n + (m + 1) - (0 : ℤ) = n + 1 + m - 0 := by omega
      simp only [h₂, one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.cast_zero, pow_zero,
        Ring.choose_zero_right, one_smul, mulSubZX_apply, smul_sub, hsign, neg_smul, zero_add,
        ha, sub_zero]
      abel
    | succ j =>
      simp only [h₂, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, mulSubZX_apply,
        Ring.choose_succ_succ n j, hsign, add_smul, smul_add, smul_sub, neg_smul]
      have ha : n + (m + 1) - ↑(j + 1) = n + m - (j : ℤ) := by omega
      have hb : n + 1 + m - ↑(j + 1) = n + m - (j : ℤ) := by omega
      have hc : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
      rw [ha, hb, hc, pow_succ (-1 : ℤ) j]
      simp only [mul_neg, mul_one, neg_smul, smul_neg, neg_neg]
      abel
  rw [htel, sum_range_sub]
  simp [h₂, hQ0, hGQ]

/-- Decomposition `(w - x) = (z - x) - (z - w)` inside `dongResidue`: applying `mulSub` splits
into `mulSubZX` at `n` minus the shifted residue at `n + 1`. -/
private theorem mulSub_dongResidue_eq_sub (n : ℤ) {F G : ℤ → ℤ → ℤ → V}
    (hF : HasMiddleCutoff F) (hG : HasFirstCutoff G) :
    TauCeti.FormalDistribution.mulSub (dongResidue n F G) =
      dongResidue n (mulSubZX V F) (mulSubZX V G) - dongResidue (n + 1) F G := by
  ext m q
  obtain ⟨P₁, hP₁⟩ := hF q
  obtain ⟨P₂, hP₂⟩ := hF (q + 1)
  obtain ⟨Q₁, hQ₁⟩ := hG q
  obtain ⟨Q₂, hQ₂⟩ := hG (q + 1)
  let P := max P₁ P₂ + m.natAbs + 2
  let Q := max Q₁ Q₂ + 1
  rw [TauCeti.FormalDistribution.mulSub_apply, Pi.sub_apply, Pi.sub_apply,
    dongResidue_eq_sum n (m + 1) q (P := P) (Q := Q)
      (fun i hi ↦ hP₁ (n - i) (m + 1 + i) (by omega))
      (fun i hi ↦ hQ₁ i (n + (m + 1) - i) (by omega)),
    dongResidue_eq_sum n m (q + 1) (P := P) (Q := Q)
      (fun i hi ↦ hP₂ (n - i) (m + i) (by omega))
      (fun i hi ↦ hQ₂ i (n + m - i) (by omega)),
    dongResidue_eq_sum n m q (P := P) (Q := Q)
      (fun i hi ↦ by
        rw [mulSubZX_apply, hP₁ (n - i + 1) (m + i) (by omega),
          hP₂ (n - i) (m + i) (by omega), sub_zero])
      (fun i hi ↦ by
        rw [mulSubZX_apply, hQ₁ (i + 1) (n + m - i) (by omega),
          hQ₂ i (n + m - i) (by omega), sub_zero]),
    dongResidue_eq_sum (n + 1) m q (P := P) (Q := Q)
      (fun i hi ↦ hP₁ (n + 1 - i) (m + i) (by omega))
      (fun i hi ↦ hQ₁ i (n + 1 + m - i) (by omega)),
    ← sub_eq_zero]
  have hcomb : ∀ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V,
      (a₁ - a₂) - (b₁ - b₂) - ((c₁ - c₂) - (d₁ - d₂)) =
        (a₁ - b₁ - (c₁ - d₁)) - (a₂ - b₂ - (c₂ - d₂)) := by intros; abel
  rw [hcomb,
    mulSub_dongResidue_left_sum n m q F (by omega)
      (hP₁ (n - ↑(P - 1)) (m + 1 + ↑(P - 1)) (by omega)),
    mulSub_dongResidue_right_sum n m q G (by omega)
      (hQ₁ (↑(Q - 1) + 1) (n + m - ↑(Q - 1)) (by omega)),
    sub_zero]

private theorem mulSub_pow_dongResidue (K : ℕ) (n : ℤ) {F G : ℤ → ℤ → ℤ → V}
    (hF : HasMiddleCutoff F) (hG : HasFirstCutoff G) :
    (TauCeti.FormalDistribution.mulSub ^ K) (dongResidue n F G) =
      ∑ st ∈ antidiagonal K, K.choose st.1 • (-1 : ℤ) ^ st.2 •
        dongResidue (n + st.2) ((mulSubZX V ^ st.1) F) ((mulSubZX V ^ st.1) G) := by
  induction K generalizing n F G with
  | zero => simp
  | succ K ih =>
    rw [pow_succ, AddMonoid.End.coe_mul, Function.comp_apply,
      mulSub_dongResidue_eq_sub n hF hG, map_sub,
      ih n hF.of_mulSubZX hG.of_mulSubZX, ih (n + 1) hF hG,
      sum_antidiagonal_choose_succ_nsmul
        (fun s t ↦ (-1 : ℤ) ^ t •
          dongResidue (n + t) ((mulSubZX V ^ s) F) ((mulSubZX V ^ s) G)) K]
    have e₁ : ∀ st ∈ antidiagonal K,
        K.choose st.2 • (-1 : ℤ) ^ st.2 •
          dongResidue (n + st.2) ((mulSubZX V ^ (st.1 + 1)) F) ((mulSubZX V ^ (st.1 + 1)) G) =
        K.choose st.1 • (-1 : ℤ) ^ st.2 •
          dongResidue (n + st.2) ((mulSubZX V ^ st.1) (mulSubZX V F))
            ((mulSubZX V ^ st.1) (mulSubZX V G)) := by
      intro st hst
      have hsum : K = st.2 + st.1 := by have := mem_antidiagonal.mp hst; omega
      have hc : K.choose st.2 = K.choose st.1 := Nat.choose_symm_of_eq_add hsum
      rw [hc, pow_succ, AddMonoid.End.coe_mul, Function.comp_apply, Function.comp_apply]
    have e₂ : ∀ st ∈ antidiagonal K,
        K.choose st.1 • (-1 : ℤ) ^ (st.2 + 1) •
          dongResidue (n + ↑(st.2 + 1)) ((mulSubZX V ^ st.1) F) ((mulSubZX V ^ st.1) G) =
        -(K.choose st.1 • (-1 : ℤ) ^ st.2 •
          dongResidue (n + 1 + st.2) ((mulSubZX V ^ st.1) F) ((mulSubZX V ^ st.1) G)) := by
      intro st _
      have hidx : n + ↑(st.2 + 1) = n + 1 + st.2 := by omega
      rw [hidx, pow_succ (-1 : ℤ) st.2]
      module
    rw [sum_congr rfl e₁, sum_congr rfl e₂, sum_neg_distrib, sub_eq_add_neg, add_comm]

/-- For `k : ℕ`, `dongResidue (k : ℤ) F G` is the finite binomial sum of `F - G`. -/
private theorem dongResidue_natCast (k : ℕ) (F G : ℤ → ℤ → ℤ → V) (m q : ℤ) :
    dongResidue (k : ℤ) F G m q =
      ∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (F ij.1 (m + ij.2) q - G ij.1 (m + ij.2) q) := by
  have hs₁ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ i • Ring.choose (k : ℤ) i • F ((k : ℤ) - i) (m + i) q) ⊆ range (k + 1) := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : k < i)])
  have hs₂ : (Function.support fun i : ℕ ↦
      (-1 : ℤ) ^ (k : ℤ).natAbs • (-1 : ℤ) ^ i • Ring.choose (k : ℤ) i •
        G (i : ℤ) ((k : ℤ) + m - i) q) ⊆ range (k + 1) := by
    intro i hi; simp only [mem_coe, mem_range]; by_contra! h
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : k < i)])
  rw [dongResidue, finsum_eq_sum_of_support_subset _ hs₁, finsum_eq_sum_of_support_subset _ hs₂,
    ← sum_range_reflect (fun i ↦ (-1 : ℤ) ^ i • Ring.choose (k : ℤ) i •
      F ((k : ℤ) - i) (m + i) q) (k + 1)]
  simp only [Nat.add_sub_cancel, Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_sub,
    sum_sub_distrib, Int.natAbs_natCast, Ring.choose_natCast]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : (k : ℤ) - ↑(k - i) = (i : ℤ) := by omega
    rw [hidx, Nat.choose_symm hi', natCast_zsmul]
    module
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hidx : (k : ℤ) + m - i = m + ↑(k - i) := by omega
    rw [hidx, ← mul_smul ((-1 : ℤ) ^ k), neg_one_pow_sub hi', natCast_zsmul]
    module

private def dongF (A B C : VertexOperator R V) (v : V) (p l q : ℤ) : V :=
  (A[[p]]) ((B[[l]]) ((C[[q]]) v)) - (C[[q]]) ((A[[p]]) ((B[[l]]) v))

private def dongG (A B C : VertexOperator R V) (v : V) (p l q : ℤ) : V :=
  (B[[l]]) ((A[[p]]) ((C[[q]]) v)) - (C[[q]]) ((B[[l]]) ((A[[p]]) v))

private theorem hasMiddleCutoff_dongF (A B C : VertexOperator R V) (v : V) :
    HasMiddleCutoff (dongF A B C v) := fun q ↦ by
  obtain ⟨P₁, h₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[q]]) v)
  obtain ⟨P₂, h₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  refine ⟨max P₁ P₂, fun p l hl ↦ ?_⟩
  simp only [dongF, h₁ l (by omega), h₂ l (by omega), map_zero, sub_self]

private theorem hasFirstCutoff_dongG (A B C : VertexOperator R V) (v : V) :
    HasFirstCutoff (dongG A B C v) := fun q ↦ by
  obtain ⟨Q₁, h₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[q]]) v)
  obtain ⟨Q₂, h₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  refine ⟨max Q₁ Q₂, fun p l hp ↦ ?_⟩
  simp only [dongG, h₁ p (by omega), h₂ p (by omega), map_zero, sub_self]

private theorem comm_nthProduct_eq_dongResidue (A B C : VertexOperator R V) (v : V)
    (n m q : ℤ) :
    (((nthProduct n A B)[[m]] * C[[q]] - C[[q]] * (nthProduct n A B)[[m]]) v) =
      dongResidue n (dongF A B C v) (dongG A B C v) m q := by
  obtain ⟨P, hP⟩ := hasMiddleCutoff_dongF A B C v q
  obtain ⟨Q, hQ⟩ := hasFirstCutoff_dongG A B C v q
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[q]]) v)
  obtain ⟨P₂, h₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[q]]) v)
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P' := max P (max P₁ P₂) + m.natAbs
  let Q' := max Q (max Q₁ Q₂)
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, ncoeff_nthProduct]
  rw [nthProductCoeff_eq_sum A B n m ((C[[q]]) v) (P := P') (Q := Q')
      (fun i hi ↦ hP₁ (m + i) (by omega)) (fun i hi ↦ hQ₁ i (by omega)),
    nthProductCoeff_eq_sum A B n m v (P := P') (Q := Q')
      (fun i hi ↦ h₂ (m + i) (by omega)) (fun i hi ↦ hQ₂ i (by omega)),
    dongResidue_eq_sum n m q (P := P') (Q := Q')
      (fun i hi ↦ hP (n - i) (m + i) (by omega)) (fun i hi ↦ hQ i (n + m - i) (by omega)),
    map_sub, map_sum, map_sum]
  have hcomb : ∀ a₁ a₂ b₁ b₂ : V, (a₁ - a₂) - (b₁ - b₂) = (a₁ - b₁) - (a₂ - b₂) := by
    intros; abel
  rw [hcomb, ← sum_sub_distrib, ← sum_sub_distrib]
  refine congrArg₂ Sub.sub ?_ ?_
  · refine sum_congr rfl fun i _ ↦ ?_
    simp [dongF, map_zsmul, smul_sub]
  · refine sum_congr rfl fun i _ ↦ ?_
    simp [dongG, map_zsmul, smul_sub]

private theorem dongResidue_mulSubZX_pow_eq_zero {A B C : VertexOperator R V} {r k : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hrk : r ≤ k) (v : V) (s : ℕ) :
    dongResidue (k : ℤ) ((mulSubZX V ^ s) (dongF A B C v))
      ((mulSubZX V ^ s) (dongG A B C v)) = 0 := by
  ext m q
  rw [dongResidue_natCast]
  simp only [Pi.zero_apply, mulSubZX_pow_apply, ← sum_sub_distrib, smul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun ab _ ↦ ?_
  have hpull : ∑ ij ∈ antidiagonal k,
      k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (s.choose ab.1 • (-1 : ℤ) ^ ab.2 •
          dongF A B C v (↑ij.1 + ↑ab.1) (m + ↑ij.2) (q + ↑ab.2) -
        s.choose ab.1 • (-1 : ℤ) ^ ab.2 •
          dongG A B C v (↑ij.1 + ↑ab.1) (m + ↑ij.2) (q + ↑ab.2)) =
      s.choose ab.1 • (-1 : ℤ) ^ ab.2 •
        (((∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
            (A[[(ab.1 : ℤ) + ij.1]] * B[[m + ij.2]] -
              B[[m + ij.2]] * A[[(ab.1 : ℤ) + ij.1]])) ((C[[q + ab.2]]) v)) -
          (C[[q + ab.2]]) ((∑ ij ∈ antidiagonal k, k.choose ij.1 • (-1 : ℤ) ^ ij.2 •
            (A[[(ab.1 : ℤ) + ij.1]] * B[[m + ij.2]] -
              B[[m + ij.2]] * A[[(ab.1 : ℤ) + ij.1]])) v)) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, map_sum, map_nsmul, map_zsmul, map_sub, smul_sub, smul_sum,
      ← sum_sub_distrib, dongF, dongG]
    refine sum_congr rfl fun ij _ ↦ ?_
    rw [add_comm (ab.1 : ℤ)]
    module
  rw [hpull, isLocalOfOrder_iff.mp (hAB.mono hrk) ab.1 m]
  simp

private theorem mulSubWX_pow_mulSubZX_pow_dongF_eq_zero {A B C : VertexOperator R V} {r s : ℕ}
    (hAC : A.IsLocalOfOrder C r) (hBC : B.IsLocalOfOrder C r) (hrs : r ≤ s) (v : V) :
    (mulSubWX V ^ r) ((mulSubZX V ^ s) (dongF A B C v)) = 0 := by
  let F₁ : ℤ → ℤ → ℤ → V := fun p l q ↦ (A[[p]]) (((B[[l]] * C[[q]] - C[[q]] * B[[l]]) v))
  let F₂ : ℤ → ℤ → ℤ → V := fun p l q ↦ ((A[[p]] * C[[q]] - C[[q]] * A[[p]]) ((B[[l]]) v))
  have hFdecomp : dongF A B C v = F₁ + F₂ := by
    ext p l q
    simp only [dongF, F₁, F₂, Pi.add_apply, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  have hF₁ : (mulSubWX V ^ r) F₁ = 0 := by
    ext p l q
    have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.mp hBC l q) v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hloc
    have hpull : ∑ ij ∈ antidiagonal r,
        r.choose ij.1 • (-1 : ℤ) ^ ij.2 • F₁ p (l + ij.1) (q + ij.2) =
        (A[[p]]) (∑ ij ∈ antidiagonal r, r.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (B[[l + ij.1]] * C[[q + ij.2]] - C[[q + ij.2]] * B[[l + ij.1]]) v) := by
      simp [F₁, map_sum, map_nsmul, map_zsmul]
    rw [mulSubWX_pow_apply, hpull, hloc, map_zero]
    rfl
  have hF₂ : (mulSubZX V ^ s) F₂ = 0 := by
    ext p l q
    simp only [mulSubZX_pow_apply, F₂, Pi.zero_apply]
    have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.mp (hAC.mono hrs) p q) ((B[[l]]) v)
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using hloc
  rw [hFdecomp, map_add, map_add, hF₂, map_zero, add_zero,
    ← Function.comp_apply (f := ⇑(mulSubWX V ^ r)), ← AddMonoid.End.coe_mul,
    (commute_mulSubZX_mulSubWX.pow_pow s r).symm.eq,
    AddMonoid.End.coe_mul, Function.comp_apply, hF₁, map_zero]

private theorem mulSubWX_pow_mulSubZX_pow_dongG_eq_zero {A B C : VertexOperator R V} {r s : ℕ}
    (hAC : A.IsLocalOfOrder C r) (hBC : B.IsLocalOfOrder C r) (hrs : r ≤ s) (v : V) :
    (mulSubWX V ^ r) ((mulSubZX V ^ s) (dongG A B C v)) = 0 := by
  let G₁ : ℤ → ℤ → ℤ → V := fun p l q ↦ (B[[l]]) (((A[[p]] * C[[q]] - C[[q]] * A[[p]]) v))
  let G₂ : ℤ → ℤ → ℤ → V := fun p l q ↦ ((B[[l]] * C[[q]] - C[[q]] * B[[l]]) ((A[[p]]) v))
  have hGdecomp : dongG A B C v = G₁ + G₂ := by
    ext p l q
    simp only [dongG, G₁, G₂, Pi.add_apply, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  have hG₁ : (mulSubZX V ^ s) G₁ = 0 := by
    ext p l q
    have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.mp (hAC.mono hrs) p q) v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hloc
    have hpull : ∑ ij ∈ antidiagonal s,
        s.choose ij.1 • (-1 : ℤ) ^ ij.2 • G₁ (p + ij.1) l (q + ij.2) =
        (B[[l]]) (∑ ij ∈ antidiagonal s, s.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[p + ij.1]] * C[[q + ij.2]] - C[[q + ij.2]] * A[[p + ij.1]]) v) := by
      simp [G₁, map_sum, map_nsmul, map_zsmul]
    rw [mulSubZX_pow_apply, hpull, hloc, map_zero]
    rfl
  have hG₂ : (mulSubWX V ^ r) G₂ = 0 := by
    ext p l q
    simp only [mulSubWX_pow_apply, G₂, Pi.zero_apply]
    have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.mp hBC l q) ((A[[p]]) v)
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using hloc
  rw [hGdecomp, map_add, map_add, hG₁, map_zero, zero_add,
    ← Function.comp_apply (f := ⇑(mulSubWX V ^ r)), ← AddMonoid.End.coe_mul,
    (commute_mulSubZX_mulSubWX.pow_pow s r).symm.eq,
    AddMonoid.End.coe_mul, Function.comp_apply, hG₂, map_zero]

/-- **Dong's lemma.** If `(A, B)`, `(A, C)` and `(B, C)` are mutually local of order `r`, then
`nthProduct n A B` and `C` are mutually local of order `3 * r + n.natAbs`. -/
theorem IsLocalOfOrder.nthProduct {A B C : VertexOperator R V} {r : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C r) (hBC : B.IsLocalOfOrder C r)
    (n : ℤ) :
    (VertexOperator.nthProduct n A B).IsLocalOfOrder C (3 * r + n.natAbs) := by
  rw [isLocalOfOrder_iff]
  intro m₀ q₀
  ext v
  have hF := hasMiddleCutoff_dongF A B C v
  have hG := hasFirstCutoff_dongG A B C v
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    comm_nthProduct_eq_dongResidue, ← TauCeti.FormalDistribution.mulSub_pow_apply]
  have hsplit : 3 * r + n.natAbs = r + (2 * r + n.natAbs) := by omega
  have hexp : ((TauCeti.FormalDistribution.mulSub ^ (3 * r + n.natAbs))
        (dongResidue n (dongF A B C v) (dongG A B C v))) =
      (TauCeti.FormalDistribution.mulSub ^ r)
        ((TauCeti.FormalDistribution.mulSub ^ (2 * r + n.natAbs))
          (dongResidue n (dongF A B C v) (dongG A B C v))) := by
    rw [hsplit, pow_add, AddMonoid.End.coe_mul, Function.comp_apply]
  rw [hexp, mulSub_pow_dongResidue _ n hF hG, map_sum, Finset.sum_apply, Finset.sum_apply]
  refine sum_eq_zero fun st hst ↦ ?_
  have hsum := mem_antidiagonal.mp hst
  rw [map_nsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
  rcases le_or_gt (r + n.natAbs) st.2 with ht | hs
  · -- When `st.2 ≥ r + |n|`, `n + st.2 ≥ r ≥ 0` so `(A, B)` locality kills `dongResidue` directly.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n + st.2 = k := ⟨(n + st.2).toNat, by omega⟩
    rw [hk, dongResidue_mulSubZX_pow_eq_zero hAB (by omega) v st.1, map_zero]
    simp
  · -- Otherwise `st.1 ≥ r`, so `(z - x)^st.1` kills `[A, C]` while `(w - x)^r` kills `[B, C]`.
    have hrs : r ≤ st.1 := by omega
    rw [mulSub_pow_dongResidue_eq_mulSubWX_pow r _ (hF.of_mulSubZX_pow st.1)
        (hG.of_mulSubZX_pow st.1),
      mulSubWX_pow_mulSubZX_pow_dongF_eq_zero hAC hBC hrs v,
      mulSubWX_pow_mulSubZX_pow_dongG_eq_zero hAC hBC hrs v]
    simp [dongResidue]

/-- **Dong's lemma** for nonnegative residue products. -/
theorem IsLocalOfOrder.nonnegResidueProduct {A B C : VertexOperator R V} {r : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C r) (hBC : B.IsLocalOfOrder C r)
    (n : ℕ) :
    (VertexOperator.nonnegResidueProduct n A B).IsLocalOfOrder C (3 * r + n) := by
  simpa using hAB.nthProduct hAC hBC (n : ℤ)

/-- **Dong's lemma** for normal-ordered products: if `(A, B)`, `(A, C)` and `(B, C)` are mutually
local of order `r`, then `normalOrder A B` and `C` are mutually local of order `3 * r + 1`. -/
theorem IsLocalOfOrder.normalOrder {A B C : VertexOperator R V} {r : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C r) (hBC : B.IsLocalOfOrder C r) :
    (VertexOperator.normalOrder A B).IsLocalOfOrder C (3 * r + 1) := by
  simpa using hAB.nthProduct hAC hBC (-1)

end Dong

end VertexOperator
