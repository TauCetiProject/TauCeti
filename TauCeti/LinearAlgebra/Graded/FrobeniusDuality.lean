/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Charpoly.Pairing
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.Prod

/-!
# Graded Frobenius duality

The cohomology `H^i = H^i(X, ℚ_ℓ)` of a smooth proper variety `X₀` of pure dimension `d` over a
finite field `𝔽_q` carries the geometric Frobenius `F_i`, and Poincaré duality pairs `H^i`
perfectly with `H^(2d - i)`. Frobenius multiplies the pairing by `q ^ d`, and graded commutativity
of the cup product gives it the Koszul sign `(-1) ^ i`. This file isolates that linear algebra
(Deligne, *Weil I*, (2.3)–(2.6)): a *graded Frobenius duality datum of weight `(2d, q ^ d)`*
(`TauCeti.GradedFrobeniusDuality`) is a `ℤ`-indexed family of vector spaces `H i` over a field
`E` with automorphisms `frob i` and perfect pairings `H i × H j → E` for `i + j = 2d`, subject to
these two laws. No semisimplicity of Frobenius is assumed, and finite-dimensionality is not
assumed either: it follows from perfectness.

The numerical invariants read the degrees `0 ≤ i ≤ 2d`: the Euler characteristic
`TauCeti.gradedEulerChar d b = ∑ (-1) ^ i b i` of the Betti numbers `b i`, and the alternating
product `TauCeti.gradedDelta H d F = ∏ det (F i) ^ (-1) ^ i` of the Frobenius determinants. For
the cohomology of a variety, `H i` vanishes outside these degrees, so these are the Euler
characteristic and the determinant of Frobenius on all of the cohomology; none of the statements
below needs the vanishing.

## Main results

For a datum `D` of weight `(2d, q ^ d)` and complementary degrees `i + j = 2d`:

* `TauCeti.GradedFrobeniusDuality.finrank_eq`: `b i = b j`.
* `TauCeti.GradedFrobeniusDuality.C_det_mul_reverse_charpoly`: reciprocity of the Frobenius
  polynomials `P_i(t) = det (1 - t F_i)`, as the polynomial identity
  `det F_i * P_j(t) = (-1) ^ (b i) * det (q ^ d t - F_i)`, that is,
  `P_j(t) * det F_i = (-q ^ d t) ^ (b i) * P_i (1 / (q ^ d t))`.
* `TauCeti.GradedFrobeniusDuality.det_mul_det`: `det F_i * det F_j = q ^ (d * b i)`.
* `TauCeti.GradedFrobeniusDuality.isSymm_pairing_self`,
  `TauCeti.GradedFrobeniusDuality.isAlt_pairing_self`: the middle form on `H d` is symmetric for
  even `d` and alternating for odd `d` (in characteristic not `2`), so for odd `d` the middle
  Betti number is even (`TauCeti.GradedFrobeniusDuality.even_finrank_self`).
* `TauCeti.GradedFrobeniusDuality.gradedDelta_sq`: `Δ ^ 2 = q ^ (d χ)`.
* `TauCeti.GradedFrobeniusDuality.even_mul_gradedEulerChar`: `d χ` is even, in characteristic
  not `2`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (2.3)–(2.6).
* J. S. Milne, *Lectures on Étale Cohomology*, Remark 27.13 and Summary 27.14.
-/

public section

open Module Polynomial

namespace TauCeti

section Invariants

/-- The **Euler characteristic** `∑_{0 ≤ i ≤ 2d} (-1) ^ i b i` of the Betti numbers `b` in the
degrees `0` to `2d`. -/
def gradedEulerChar (d : ℕ) (b : ℤ → ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 0 (2 * (d : ℤ)), (i.negOnePow : ℤ) * b i

/-- Unfolds the Euler characteristic. -/
theorem gradedEulerChar_def (d : ℕ) (b : ℤ → ℕ) :
    gradedEulerChar d b = ∑ i ∈ Finset.Icc 0 (2 * (d : ℤ)), (i.negOnePow : ℤ) * b i :=
  (rfl)

/-- The Euler characteristic is additive in the Betti numbers, for instance under direct sums. -/
@[simp]
theorem gradedEulerChar_add (d : ℕ) (b b' : ℤ → ℕ) :
    gradedEulerChar d (b + b') = gradedEulerChar d b + gradedEulerChar d b' := by
  simp [gradedEulerChar_def, mul_add, Finset.sum_add_distrib]

variable {R : Type*} [CommRing R] (H : ℤ → Type*) [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]

/-- The **alternating determinant** `∏_{0 ≤ i ≤ 2d} det (F i) ^ (-1) ^ i` of a family of
automorphisms `F i` in the degrees `0` to `2d`, a unit of the coefficient ring. -/
noncomputable def gradedDelta (d : ℕ) (F : ∀ i, H i ≃ₗ[R] H i) : Rˣ :=
  ∏ i ∈ Finset.Icc 0 (2 * (d : ℤ)), LinearEquiv.det (F i) ^ (i.negOnePow : ℤ)

/-- Unfolds the alternating determinant. -/
theorem gradedDelta_def (d : ℕ) (F : ∀ i, H i ≃ₗ[R] H i) :
    gradedDelta H d F =
      ∏ i ∈ Finset.Icc 0 (2 * (d : ℤ)), LinearEquiv.det (F i) ^ (i.negOnePow : ℤ) :=
  (rfl)

/-- The alternating determinant of the identity automorphisms is `1`. -/
@[simp]
theorem gradedDelta_refl (d : ℕ) : gradedDelta H d (fun i ↦ LinearEquiv.refl R (H i)) = 1 := by
  simp [gradedDelta_def]

variable {H}

/-- The alternating determinant is invariant under a degreewise linear equivalence. -/
@[simp]
theorem gradedDelta_conj {H' : ℤ → Type*} [∀ i, AddCommGroup (H' i)] [∀ i, Module R (H' i)]
    (d : ℕ) (F : ∀ i, H i ≃ₗ[R] H i) (e : ∀ i, H i ≃ₗ[R] H' i) :
    gradedDelta H' d (fun i ↦ ((e i).symm.trans (F i)).trans (e i)) = gradedDelta H d F := by
  simp [gradedDelta_def]

/-- The alternating determinant is multiplicative under degreewise direct sums of finite free
modules. -/
@[simp]
theorem gradedDelta_prodCongr {H' : ℤ → Type*} [∀ i, AddCommGroup (H' i)]
    [∀ i, Module R (H' i)] [∀ i, Module.Free R (H i)] [∀ i, Module.Finite R (H i)]
    [∀ i, Module.Free R (H' i)] [∀ i, Module.Finite R (H' i)] (d : ℕ) (F : ∀ i, H i ≃ₗ[R] H i)
    (F' : ∀ i, H' i ≃ₗ[R] H' i) :
    gradedDelta (fun i ↦ H i × H' i) d (fun i ↦ (F i).prodCongr (F' i)) =
      gradedDelta H d F * gradedDelta H' d F' := by
  simp [gradedDelta_def, mul_zpow, Finset.prod_mul_distrib]

end Invariants

/-- A **graded Frobenius duality datum of weight `(2d, q ^ d)`** on a `ℤ`-indexed family `H` of
vector spaces over `E`: automorphisms `frob i` of `H i` and pairings `pairing i j` of `H i` with
`H j` for `i + j = 2d`, which are perfect, are multiplied by `q ^ d` under Frobenius, and satisfy
the Koszul sign rule `⟨x, y⟩ = (-1) ^ i ⟨y, x⟩` for `x ∈ H i`.

The motivating example is the `ℓ`-adic cohomology of a smooth proper variety of pure dimension `d`
over `𝔽_q`, with the geometric Frobenius and the cup-product pairing. Each `H i` is
finite-dimensional (`TauCeti.GradedFrobeniusDuality.finiteDimensional`). -/
@[ext]
structure GradedFrobeniusDuality (E : Type*) [Field E] (H : ℤ → Type*) [∀ i, AddCommGroup (H i)]
    [∀ i, Module E (H i)] (d : ℕ) (q : Eˣ) where
  /-- The Frobenius automorphism in each degree. -/
  frob : ∀ i, H i ≃ₗ[E] H i
  /-- The pairing of complementary degrees `i + j = 2d`. -/
  pairing : ∀ i j, i + j = 2 * (d : ℤ) → H i →ₗ[E] H j →ₗ[E] E
  /-- The pairings are perfect. -/
  isPerfPair : ∀ i j (hij : i + j = 2 * (d : ℤ)), (pairing i j hij).IsPerfPair
  /-- Frobenius multiplies the pairing by `q ^ d`. -/
  pairing_frob_frob : ∀ i j (hij : i + j = 2 * (d : ℤ)) (x : H i) (y : H j),
    pairing i j hij (frob i x) (frob j y) = (q : E) ^ d * pairing i j hij x y
  /-- The Koszul sign rule. -/
  pairing_comm : ∀ i j (hij : i + j = 2 * (d : ℤ)) (x : H i) (y : H j),
    pairing i j hij x y = (-1 : E) ^ i * pairing j i (by rw [add_comm, hij]) y x

namespace GradedFrobeniusDuality

variable {E : Type*} [Field E] {H : ℤ → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module E (H i)]
  {d : ℕ} {q : Eˣ} (D : GradedFrobeniusDuality E H d q)

include D in
/-- Every space of a graded Frobenius duality datum is finite-dimensional, since it is perfectly
paired with another. -/
theorem finiteDimensional (i : ℤ) : FiniteDimensional E (H i) :=
  have := D.isPerfPair i (2 * d - i) (by ring)
  have : IsReflexive E (H i) := .of_isPerfPair (D.pairing i (2 * d - i) _)
  inferInstance

/-- Frobenius multiplies the pairing by `q ^ d`, as an identity of bilinear maps. -/
theorem compl₁₂_pairing_frob_frob {i j : ℤ} (hij : i + j = 2 * (d : ℤ)) :
    (D.pairing i j hij).compl₁₂ (D.frob i).toLinearMap (D.frob j).toLinearMap =
      ((q : E) ^ d) • D.pairing i j hij := by
  ext x y
  simp [D.pairing_frob_frob]

include D in
/-- **Poincaré duality of Betti numbers**: complementary degrees have the same dimension. -/
theorem finrank_eq {i j : ℤ} (hij : i + j = 2 * (d : ℤ)) :
    finrank E (H i) = finrank E (H j) :=
  have := D.finiteDimensional i
  have := D.isPerfPair i j hij
  finrank_of_isPerfPair (D.pairing i j hij)

/-- **Determinants of Frobenius in complementary degrees**: `det F_i * det F_j = q ^ (d b_i)`. -/
theorem det_mul_det {i j : ℤ} (hij : i + j = 2 * (d : ℤ)) :
    LinearEquiv.det (D.frob i) * LinearEquiv.det (D.frob j) = q ^ (d * finrank E (H i)) := by
  have := D.finiteDimensional i
  ext
  simpa [LinearEquiv.coe_det, pow_mul] using
    LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul _ (D.isPerfPair i j hij).bijective_right
      (D.compl₁₂_pairing_frob_frob hij)

/-- **Reciprocity of Frobenius polynomials.** In complementary degrees `i + j = 2d`,
`det F_i * det (1 - X F_j) = (-1) ^ b_i * det (q ^ d X - F_i)`. Since `q` is a
unit, this is the identity `P_j(t) * det F_i = (-q ^ d t) ^ b_i * P_i (1 / (q ^ d t))` of rational
functions for `P_i(t) = det (1 - t F_i)`. -/
theorem C_det_mul_reverse_charpoly {i j : ℤ} [FiniteDimensional E (H i)]
    [FiniteDimensional E (H j)] (hij : i + j = 2 * (d : ℤ)) :
    C (LinearEquiv.det (D.frob i) : E) * (D.frob j).toLinearMap.charpoly.reverse =
      (-1) ^ finrank E (H i) * (D.frob i).toLinearMap.charpoly.comp (C ((q : E) ^ d) * X) := by
  rw [LinearEquiv.coe_det]
  exact LinearMap.C_det_mul_reverse_charpoly_of_compl₁₂_eq_smul _
    (D.isPerfPair i j hij).bijective_right (D.compl₁₂_pairing_frob_frob hij)

/-- The middle form on `H d` is `(-1) ^ d`-symmetric. -/
theorem pairing_self_comm (x y : H d) :
    D.pairing d d (two_mul (d : ℤ)).symm x y =
      (-1) ^ d * D.pairing d d (two_mul (d : ℤ)).symm y x := by
  rw [D.pairing_comm, zpow_natCast]

/-- For even `d`, the middle form on `H d` is symmetric. -/
theorem isSymm_pairing_self (hd : Even d) :
    LinearMap.BilinForm.IsSymm (D.pairing d d (two_mul (d : ℤ)).symm) :=
  ⟨fun x y ↦ by rw [D.pairing_self_comm, hd.neg_one_pow, one_mul]⟩

/-- For odd `d`, in characteristic not `2`, the middle form on `H d` is alternating. -/
theorem isAlt_pairing_self (h2 : (2 : E) ≠ 0) (hd : Odd d) :
    LinearMap.BilinForm.IsAlt (D.pairing d d (two_mul (d : ℤ)).symm) := fun x ↦ by
  have h := D.pairing_self_comm x x
  rw [hd.neg_one_pow, neg_one_mul, eq_neg_iff_add_eq_zero, ← two_mul] at h
  exact (mul_eq_zero.1 h).resolve_left h2

include D in
/-- For odd `d`, in characteristic not `2`, the middle Betti number `b_d` is even, since the
middle form is alternating and perfect. -/
theorem even_finrank_self (h2 : (2 : E) ≠ 0) (hd : Odd d) : Even (finrank E (H d)) :=
  have := D.finiteDimensional d
  LinearMap.BilinForm.IsAlt.even_finrank (D.isAlt_pairing_self h2 hd)
    (D.isPerfPair d d _).nondegenerate

/-- **The determinant relation** `Δ ^ 2 = q ^ (d χ)`: pairing the degrees `i` and `2d - i`, which
have the same sign, each pair contributes `(det F_i * det F_(2d - i)) ^ (-1) ^ i`, that is,
`q ^ (d * (-1) ^ i * b_i)`. -/
theorem gradedDelta_sq :
    gradedDelta H d D.frob ^ 2 = q ^ ((d : ℤ) * gradedEulerChar d (fun i ↦ finrank E (H i))) := by
  have hrefl : gradedDelta H d D.frob =
      ∏ i ∈ Finset.Icc 0 (2 * (d : ℤ)), LinearEquiv.det (D.frob (2 * d - i)) ^ (i.negOnePow : ℤ) :=
    Finset.prod_nbij' (fun i ↦ 2 * d - i) (fun i ↦ 2 * d - i)
      (fun i hi ↦ by simp only [Finset.mem_Icc] at hi ⊢; omega)
      (fun i hi ↦ by simp only [Finset.mem_Icc] at hi ⊢; omega)
      (fun i _ ↦ by ring) (fun i _ ↦ by ring)
      (fun i _ ↦ by rw [sub_sub_cancel, Int.negOnePow_sub, Int.negOnePow_two_mul, one_mul])
  rw [sq]
  nth_rw 2 [hrefl]
  rw [gradedDelta_def, ← Finset.prod_mul_distrib, gradedEulerChar_def, Finset.mul_sum,
    ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← mul_zpow, D.det_mul_det (by ring), ← zpow_natCast, ← zpow_mul]
  push_cast
  ring_nf

include D in
/-- In characteristic not `2`, `d χ` is even. For odd `d`, the degrees other than `d` pair off
with equal Betti numbers, and the middle Betti number is even (`even_finrank_self`). -/
theorem even_mul_gradedEulerChar (h2 : (2 : E) ≠ 0) :
    Even ((d : ℤ) * gradedEulerChar d (fun i ↦ finrank E (H i))) := by
  rcases Nat.even_or_odd d with hd | hd
  · exact (Int.even_natCast d).2 hd |>.mul_right _
  refine Even.mul_left ?_ _
  rw [even_iff_two_dvd]
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 ?_
  rw [gradedEulerChar_def]
  push_cast
  refine Finset.sum_involution (fun i _ ↦ 2 * d - i) (fun i hi ↦ ?_) (fun i _ hi h ↦ ?_)
    (fun i hi ↦ by simp only [Finset.mem_Icc] at hi ⊢; omega) (fun i _ ↦ by ring)
  · rw [Int.negOnePow_sub, Int.negOnePow_two_mul, one_mul,
      ← D.finrank_eq (i := i) (j := 2 * d - i) (by ring), ← two_mul]
    exact mul_eq_zero_of_left (by decide) _
  · obtain rfl : i = d := by omega
    obtain ⟨k, hk⟩ := D.even_finrank_self h2 hd
    refine hi ?_
    rw [hk]
    push_cast
    rw [← two_mul]
    exact mul_eq_zero_of_right _ (mul_eq_zero_of_left (by decide) _)

end GradedFrobeniusDuality

end TauCeti
