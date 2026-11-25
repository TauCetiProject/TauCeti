/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Product
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# The discriminant of a binary form of fixed degree

A polynomial `G` of degree at most `n` is the dehomogenisation of the binary form
`Σ Gᵢ Xⁱ Yⁿ⁻ⁱ` of degree `n`. The discriminant of that binary form is not `Polynomial.discr G`:
when `G` has degree `n - 1` the form has a simple root at infinity, and when `G` has degree at
most `n - 2` the form has a multiple root at infinity and its discriminant vanishes, while
`Polynomial.discr G` only sees the degree of `G`. This file defines the discriminant of `G` as a
binary form of degree `n` by specialising one universal integer polynomial, so that it depends
only on the coefficients `G₀, …, Gₙ`, is compatible with every ring homomorphism, and is defined
in every characteristic. It is the discriminant used for the equation `y² = G(x)` of a
hyperelliptic curve, where `G` has formal degree `2g + 2` but may have actual degree `2g + 1`.

## Main definitions

* `TauCeti.universalPoly n`: the universal polynomial `Σ aᵢ Tⁱ` of formal degree `n` over
  `ℤ[a₀, …, aₙ]`.
* `TauCeti.universalDiscr n`: its discriminant, an integer polynomial in `a₀, …, aₙ`.
* `Polynomial.formDiscr n G`: the discriminant of `G` as a binary form of degree `n`, obtained by
  evaluating `universalDiscr n` at the coefficients of `G`.

## Main results

* `Polynomial.formDiscr_map`: compatibility with ring homomorphisms.
* `Polynomial.formDiscr_of_natDegree_eq`: in the generic degree it is `Polynomial.discr`.
* `Polynomial.formDiscr_zero`, `Polynomial.formDiscr_one`: for `n ≤ 1` it is `1`.
* `Polynomial.formDiscr_succ`, `Polynomial.formDiscr_succ_eq_coeff_sq_mul_discr`: the
  degree-drop formula `formDiscr (n + 1) G = Gₙ² · formDiscr n G = Gₙ² · discr G` for `G` of
  degree at most `n ≥ 1`.
* `Polynomial.formDiscr_of_natDegree_eq_pred`, `Polynomial.formDiscr_eq_zero_of_natDegree_le`:
  a simple root at infinity contributes the square of the leading coefficient, a multiple root at
  infinity makes the discriminant vanish.
* `Polynomial.formDiscr_C_mul`: homogeneity of degree `2n - 2` in the coefficients.
* `Polynomial.formDiscr_reflect`: invariance under the inversion `x ↦ 1/x` of the binary form.
* `Polynomial.formDiscr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq_of_natDegree_eq`,
  `Polynomial.formDiscr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq_of_natDegree_eq_pred`: the
  root-product formula `formDiscr n G = lc ^ (2n - 2) · ∏_{i < j} (rᵢ - rⱼ)²` in both degrees.

## Implementation notes

The degree-drop formula is proved universally: over `ℤ[a₀, …, aₙ]` the polynomial of formal
degree `n + 1` with vanishing top coefficient is turned, by reversal at the formal degree, into
`X` times the reversal of the universal polynomial of degree `n`, whose constant coefficient `aₙ`
is nonzero. The general case follows by specialisation. At `n = 1` the convention of Mathlib's
`Polynomial.discr_of_degree_eq_one` gives `formDiscr 1 G = 1` for every `G`, so the degree-drop
formula needs `n ≥ 1` and its corollaries need `n ≥ 2`.

## References

* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.
* P. Lockhart, *On the discriminant of a hyperelliptic curve*, Trans. Amer. Math. Soc. 342
  (1994), §1.
-/

public section

open Finset

namespace TauCeti

open Polynomial

/-! ### The universal polynomial -/

/-- The universal polynomial `Σ aᵢ Tⁱ` of formal degree `n`, whose coefficients are the variables
of `ℤ[a₀, …, aₙ]`. Every polynomial of degree at most `n` is a specialisation of it
(`TauCeti.map_universalPoly_of_natDegree_le`). -/
noncomputable def universalPoly (n : ℕ) : (MvPolynomial (Fin (n + 1)) ℤ)[X] :=
  ∑ i : Fin (n + 1), C (MvPolynomial.X i) * X ^ (i : ℕ)

/-- The `i`-th coefficient of the universal polynomial is the variable `aᵢ`. -/
@[simp]
theorem coeff_universalPoly (n : ℕ) (i : Fin (n + 1)) :
    (universalPoly n).coeff i = MvPolynomial.X i := by
  simp [universalPoly, Fin.val_inj]

@[simp]
theorem coeff_zero_universalPoly (n : ℕ) : (universalPoly n).coeff 0 = MvPolynomial.X 0 :=
  coeff_universalPoly n 0

/-- The `k`-th coefficient of the universal polynomial of formal degree `n ≥ k` is the variable
`aₖ`. -/
theorem coeff_universalPoly_of_le {n k : ℕ} (hk : k ≤ n) :
    (universalPoly n).coeff k = MvPolynomial.X ⟨k, Nat.lt_succ_of_le hk⟩ :=
  coeff_universalPoly n ⟨k, Nat.lt_succ_of_le hk⟩

/-- The universal polynomial of formal degree `n` has no coefficients beyond degree `n`. -/
theorem coeff_universalPoly_of_lt {n k : ℕ} (hk : n < k) : (universalPoly n).coeff k = 0 := by
  simp only [universalPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)

@[simp]
theorem natDegree_universalPoly (n : ℕ) : (universalPoly n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦
      coeff_universalPoly_of_lt (by exact_mod_cast hk)
  · rw [coeff_universalPoly_of_le le_rfl]
    exact MvPolynomial.X_ne_zero _

@[simp]
theorem leadingCoeff_universalPoly (n : ℕ) :
    (universalPoly n).leadingCoeff = MvPolynomial.X (Fin.last n) := by
  rw [leadingCoeff, natDegree_universalPoly]
  exact coeff_universalPoly n (Fin.last n)

/-- Specialising the coefficients of the universal polynomial to `a`. -/
theorem map_universalPoly {R : Type*} [CommRing R] (n : ℕ) (a : Fin (n + 1) → R) :
    (universalPoly n).map (MvPolynomial.aeval a).toRingHom =
      ∑ i : Fin (n + 1), C (a i) * X ^ (i : ℕ) := by
  simp [universalPoly, Polynomial.map_sum]

/-- A polynomial of degree at most `n` is the specialisation of the universal polynomial of formal
degree `n` at its coefficients. -/
theorem map_universalPoly_of_natDegree_le {R : Type*} [CommRing R] {n : ℕ} {G : R[X]}
    (hG : G.natDegree ≤ n) :
    (universalPoly n).map (MvPolynomial.aeval fun i : Fin (n + 1) ↦ G.coeff i).toRingHom =
      G := by
  rw [map_universalPoly, Fin.sum_univ_eq_sum_range (fun i ↦ C (G.coeff i) * X ^ i) (n + 1)]
  exact (as_sum_range_C_mul_X_pow' G (Nat.lt_succ_of_le hG)).symm

/-! ### The discriminant of a binary form -/

/-- The universal discriminant of a binary form of degree `n`: the discriminant of the universal
polynomial `Σ aᵢ Tⁱ`, an integer polynomial in `a₀, …, aₙ`. -/
noncomputable def universalDiscr (n : ℕ) : MvPolynomial (Fin (n + 1)) ℤ :=
  (universalPoly n).discr

/-- Unfolding `TauCeti.universalDiscr` outside this module. -/
theorem universalDiscr_def (n : ℕ) : universalDiscr n = (universalPoly n).discr :=
  (rfl)

end TauCeti

namespace Polynomial

open TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The discriminant of `G` viewed as a binary form `Σ Gᵢ Xⁱ Yⁿ⁻ⁱ` of degree `n`: the universal
discriminant `universalDiscr n` evaluated at the coefficients `G₀, …, Gₙ`. It is
`Polynomial.discr G` when `G` has degree `n` (`Polynomial.formDiscr_of_natDegree_eq`), it is
`lc(G)² · Polynomial.discr G` when `G` has degree `n - 1 ≥ 1`
(`Polynomial.formDiscr_of_natDegree_eq_pred`), and it vanishes when `G` has degree at most
`n - 2` with `n ≥ 2` (`Polynomial.formDiscr_eq_zero_of_natDegree_le`). For `n ≤ 1` it is `1`. -/
noncomputable def formDiscr (n : ℕ) (G : R[X]) : R :=
  MvPolynomial.aeval (fun i : Fin (n + 1) ↦ G.coeff i) (universalDiscr n)

/-- Unfolding `Polynomial.formDiscr` outside this module: the universal discriminant evaluated at
the coefficients of `G`. -/
theorem formDiscr_def (n : ℕ) (G : R[X]) :
    G.formDiscr n = MvPolynomial.aeval (fun i : Fin (n + 1) ↦ G.coeff i) (universalDiscr n) :=
  (rfl)

/-- The binary-form discriminant only depends on the coefficients `G₀, …, Gₙ`. -/
theorem formDiscr_congr {n : ℕ} {G H : R[X]} (h : ∀ i ≤ n, G.coeff i = H.coeff i) :
    G.formDiscr n = H.formDiscr n := by
  have hGH : (fun i : Fin (n + 1) ↦ G.coeff i) = fun i : Fin (n + 1) ↦ H.coeff i :=
    _root_.funext fun i : Fin (n + 1) ↦ h i (Nat.lt_succ_iff.mp i.isLt)
  rw [formDiscr, formDiscr, hGH]

@[simp]
theorem formDiscr_universalPoly (n : ℕ) : (universalPoly n).formDiscr n = universalDiscr n := by
  simp only [formDiscr, coeff_universalPoly]
  exact MvPolynomial.aeval_X_left_apply _

/-- The binary-form discriminant commutes with every ring homomorphism, whether or not it
preserves the degree. -/
@[simp]
theorem formDiscr_map (n : ℕ) (G : R[X]) (φ : R →+* S) :
    (G.map φ).formDiscr n = φ (G.formDiscr n) := by
  simp only [formDiscr, coeff_map]
  exact (MvPolynomial.comp_aeval_apply _ φ.toIntAlgHom _).symm

/-- In the generic degree the binary-form discriminant is Mathlib's `Polynomial.discr`. -/
theorem formDiscr_of_natDegree_eq {n : ℕ} {G : R[X]} (hG : G.natDegree = n) :
    G.formDiscr n = G.discr := by
  have hmap := map_universalPoly_of_natDegree_le hG.le
  have hdeg : ((universalPoly n).map
      (MvPolynomial.aeval fun i : Fin (n + 1) ↦ G.coeff i).toRingHom).natDegree =
      (universalPoly n).natDegree := by
    rw [hmap, hG, natDegree_universalPoly]
  rw [← hmap, discr_map_of_natDegree_eq _ hdeg, formDiscr_map, formDiscr_universalPoly,
    universalDiscr]

@[simp]
theorem formDiscr_zero (G : R[X]) : G.formDiscr 0 = 1 := by
  rw [formDiscr, universalDiscr, eq_C_of_natDegree_eq_zero (natDegree_universalPoly 0), discr_C,
    map_one]

@[simp]
theorem formDiscr_one (G : R[X]) : G.formDiscr 1 = 1 := by
  have hdeg : (universalPoly 1).degree = 1 := by
    rw [degree_eq_natDegree, natDegree_universalPoly, Nat.cast_one]
    rw [← leadingCoeff_ne_zero, leadingCoeff_universalPoly]
    exact MvPolynomial.X_ne_zero _
  rw [formDiscr, universalDiscr, discr_of_degree_eq_one hdeg, map_one]

/-- The universal form of the degree-drop formula: the polynomial `Σ_{i ≤ n} aᵢ Tⁱ`, viewed as a
binary form of degree `n + 1`, has discriminant `aₙ² · universalDiscr n`. -/
private theorem formDiscr_succ_universalPoly {n : ℕ} (hn : 1 ≤ n) :
    (universalPoly n).formDiscr (n + 1) =
      MvPolynomial.X (Fin.last n) ^ 2 * universalDiscr n := by
  set V := universalPoly n
  set ρ : MvPolynomial (Fin (n + 2)) ℤ →+* MvPolynomial (Fin (n + 1)) ℤ :=
    (MvPolynomial.aeval fun i : Fin (n + 2) ↦ V.coeff i).toRingHom
  have hV0 : V.coeff 0 ≠ 0 := by
    rw [coeff_zero_universalPoly]
    exact MvPolynomial.X_ne_zero _
  have h0 : ρ ((universalPoly (n + 1)).coeff 0) ≠ 0 := by
    simpa [ρ, coeff_zero_universalPoly] using hV0
  have hmap : (universalPoly (n + 1)).map ρ = V :=
    map_universalPoly_of_natDegree_le (by simp [V])
  have hrev : ((universalPoly (n + 1)).reverse).map ρ = X * V.reverse := by
    have h := reflect_mul V 1 (natDegree_universalPoly n).le (natDegree_one.trans_le zero_le_one)
    rw [mul_one, reflect_one, pow_one] at h
    rw [reverse, natDegree_universalPoly, ← reflect_map, hmap, h, reverse, natDegree_universalPoly,
      mul_comm]
  have hVrev : V.reverse.natDegree = n := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr hV0), Nat.sub_zero,
      natDegree_universalPoly]
  have key := discr_map_reverse (universalPoly (n + 1)) ρ h0
  rw [hrev, discr_X_mul _ (by omega), discr_reverse _ hV0, coeff_zero_reverse,
    leadingCoeff_universalPoly] at key
  simp only [formDiscr, universalDiscr]
  rw [mul_comm]
  exact key.symm

/-- **The degree-drop formula.** A polynomial of degree at most `n ≥ 1`, viewed as a binary form
of degree `n + 1`, has discriminant `Gₙ²` times its discriminant as a binary form of degree
`n`. -/
theorem formDiscr_succ {n : ℕ} (hn : 1 ≤ n) {G : R[X]} (hG : G.natDegree ≤ n) :
    G.formDiscr (n + 1) = G.coeff n ^ 2 * G.formDiscr n := by
  rw [← map_universalPoly_of_natDegree_le hG, formDiscr_map, formDiscr_map,
    formDiscr_succ_universalPoly hn, coeff_map, ← formDiscr_universalPoly, map_mul, map_pow]
  congr 2
  simpa using (congrArg (MvPolynomial.aeval fun i : Fin (n + 1) ↦ G.coeff i)
    (coeff_universalPoly n (Fin.last n))).symm

/-- The degree-drop formula read against `Polynomial.discr`: for `G` of degree at most `n ≥ 1`,
the binary form of degree `n + 1` has discriminant `Gₙ² · discr G`. When `Gₙ = 0` both sides
vanish, so no hypothesis on the actual degree is needed. -/
theorem formDiscr_succ_eq_coeff_sq_mul_discr {n : ℕ} (hn : 1 ≤ n) {G : R[X]}
    (hG : G.natDegree ≤ n) : G.formDiscr (n + 1) = G.coeff n ^ 2 * G.discr := by
  rw [formDiscr_succ hn hG]
  by_cases h : G.coeff n = 0
  · simp [h]
  · rw [formDiscr_of_natDegree_eq (le_antisymm hG (le_natDegree_of_ne_zero h))]

/-- **A simple root at infinity.** For `n ≥ 2` and `G` of degree `n - 1`, the binary form of
degree `n` has discriminant `lc(G)² · discr G`. -/
theorem formDiscr_of_natDegree_eq_pred {n : ℕ} (hn : 2 ≤ n) {G : R[X]}
    (hG : G.natDegree = n - 1) : G.formDiscr n = G.leadingCoeff ^ 2 * G.discr := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hG
  rw [formDiscr_succ_eq_coeff_sq_mul_discr (by omega) hG.le, leadingCoeff, hG]

/-- **A multiple root at infinity.** For `n ≥ 2` and `G` of degree at most `n - 2`, the binary
form of degree `n` has discriminant `0`. -/
theorem formDiscr_eq_zero_of_natDegree_le {n : ℕ} (hn : 2 ≤ n) {G : R[X]}
    (hG : G.natDegree ≤ n - 2) : G.formDiscr n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [formDiscr_succ (by omega) (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
    zero_pow two_ne_zero, zero_mul]

/-- The universal form of homogeneity: over the domain `ℤ[a₀, …, aₙ][Y]`, scaling the universal
polynomial by `Y` scales its discriminant by `Y ^ (2n - 2)`. -/
private theorem formDiscr_C_X_mul_map_universalPoly (n : ℕ) :
    (C (X : (MvPolynomial (Fin (n + 1)) ℤ)[X]) * (universalPoly n).map C).formDiscr n =
      X ^ (2 * n - 2) * ((universalPoly n).map C).formDiscr n := by
  have hdeg : ((universalPoly n).map (C : MvPolynomial (Fin (n + 1)) ℤ →+* _)).natDegree = n := by
    rw [natDegree_map_eq_of_injective C_injective, natDegree_universalPoly]
  rw [formDiscr_of_natDegree_eq hdeg,
    formDiscr_of_natDegree_eq (by rw [natDegree_C_mul X_ne_zero, hdeg]),
    TauCeti.discr_C_mul _ X_ne_zero, hdeg]

/-- **Homogeneity.** The binary-form discriminant of degree `n` is homogeneous of degree `2n - 2`
in the coefficients. No hypothesis on `c` or on the degree of `G` is needed. -/
theorem formDiscr_C_mul (n : ℕ) (c : R) (G : R[X]) :
    (C c * G).formDiscr n = c ^ (2 * n - 2) * G.formDiscr n := by
  set a : Fin (n + 1) → R := fun i ↦ G.coeff i
  set ψ : (MvPolynomial (Fin (n + 1)) ℤ)[X] →+* R :=
    eval₂RingHom (MvPolynomial.aeval a).toRingHom c
  have hψC : ψ.comp C = (MvPolynomial.aeval a).toRingHom := RingHom.ext fun x ↦ eval₂_C _ _
  have hmap : ((universalPoly n).map C).map ψ =
      (universalPoly n).map (MvPolynomial.aeval a).toRingHom := by
    rw [map_map, hψC]
  have hcoeff (i : ℕ) (hi : i ≤ n) :
      G.coeff i = ((universalPoly n).map (MvPolynomial.aeval a).toRingHom).coeff i := by
    rw [coeff_map, coeff_universalPoly_of_le hi]
    simp [a]
  have hG : G.formDiscr n = (((universalPoly n).map C).map ψ).formDiscr n :=
    formDiscr_congr fun i hi ↦ by rw [hmap]; exact hcoeff i hi
  have hCG : (C c * G).formDiscr n =
      ((C (X : (MvPolynomial (Fin (n + 1)) ℤ)[X]) * (universalPoly n).map C).map ψ).formDiscr
        n := by
    refine formDiscr_congr fun i hi ↦ ?_
    rw [Polynomial.map_mul, map_C, coeff_C_mul, coeff_C_mul, hmap]
    congr 1
    · simp [ψ]
    exact hcoeff i hi
  rw [hCG, hG, formDiscr_map, formDiscr_map, formDiscr_C_X_mul_map_universalPoly, map_mul,
    map_pow]
  simp [ψ]

/-- Reversing the coefficients of the universal polynomial is the reversal of the polynomial. -/
private theorem map_rename_rev_universalPoly (n : ℕ) :
    (universalPoly n).map (MvPolynomial.rename Fin.rev).toRingHom = (universalPoly n).reverse := by
  ext k : 2
  rw [coeff_reverse, natDegree_universalPoly, coeff_map]
  rcases le_or_gt k n with hk | hk
  · rw [revAt_le hk, coeff_universalPoly_of_le hk, coeff_universalPoly_of_le (Nat.sub_le n k)]
    simp [Fin.ext_iff, Fin.val_rev]
  · rw [coeff_universalPoly_of_lt hk, revAt_eq_self_of_lt hk, coeff_universalPoly_of_lt hk,
      map_zero]

/-- The universal discriminant is invariant under reversing the order of the coefficients. -/
private theorem rename_rev_universalDiscr (n : ℕ) :
    MvPolynomial.rename Fin.rev (universalDiscr n) = universalDiscr n := by
  have hdeg : ((universalPoly n).map (MvPolynomial.rename Fin.rev).toRingHom).natDegree =
      (universalPoly n).natDegree :=
    natDegree_map_eq_of_injective (MvPolynomial.rename_injective _ Fin.rev_injective) _
  have h0 : (universalPoly n).coeff 0 ≠ 0 := by
    rw [coeff_zero_universalPoly]
    exact MvPolynomial.X_ne_zero _
  have key := discr_map_of_natDegree_eq _ hdeg
  rw [map_rename_rev_universalPoly, discr_reverse _ h0] at key
  exact key.symm

/-- **Invariance under inversion.** Reflecting `G` at the formal degree `n`, which is the
substitution `(x : y) ↦ (y : x)` of the binary form of degree `n`, preserves the binary-form
discriminant. No hypothesis on the degree of `G` is needed: a root at infinity of one form is a
root at `0` of the other. -/
@[simp]
theorem formDiscr_reflect (n : ℕ) (G : R[X]) : (G.reflect n).formDiscr n = G.formDiscr n := by
  conv_rhs => rw [formDiscr, ← rename_rev_universalDiscr, MvPolynomial.aeval_rename]
  have hcoeff : (fun i : Fin (n + 1) ↦ (G.reflect n).coeff i) =
      (fun i : Fin (n + 1) ↦ G.coeff i) ∘ Fin.rev := _root_.funext fun i ↦ by
    rw [coeff_reflect, revAt_le (Nat.lt_succ_iff.mp i.isLt), Function.comp_apply, Fin.val_rev]
    congr 1
    omega
  rw [formDiscr, hcoeff]

/-- **The root-product formula in the generic degree.** If `G` has degree `n` and `r` enumerates
its roots in a domain `L`, then `formDiscr n G = lc(G) ^ (2n - 2) · ∏_{i < j} (rᵢ - rⱼ)²`. -/
theorem formDiscr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq_of_natDegree_eq {L : Type*}
    [CommRing L] [IsDomain L] [Algebra R L] {n : ℕ} {G : R[X]} (hG : G.natDegree = n)
    {r : Fin G.natDegree → L} (hr : IsRootEnumeration G r) :
    algebraMap R L (G.formDiscr n) = algebraMap R L G.leadingCoeff ^ (2 * n - 2) *
      ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  subst hG
  rw [formDiscr_of_natDegree_eq rfl, discr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq hr]

/-- **The root-product formula with a root at infinity.** If `G` has degree `n - 1` and `r`
enumerates its finite roots in a domain `L`, then
`formDiscr n G = lc(G) ^ (2n - 2) · ∏_{i < j} (rᵢ - rⱼ)²`, the formula of the generic degree
with the exponent of degree `n`. In projective coordinates the root at infinity `(1 : 0)` has
determinant `±1` against each finite root `(rᵢ : 1)`, so it adds no factor to the product. -/
theorem formDiscr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq_of_natDegree_eq_pred {L : Type*}
    [CommRing L] [IsDomain L] [Algebra R L] {n : ℕ} {G : R[X]} (hG : G.natDegree = n - 1)
    {r : Fin G.natDegree → L} (hr : IsRootEnumeration G r) :
    algebraMap R L (G.formDiscr n) = algebraMap R L G.leadingCoeff ^ (2 * n - 2) *
      ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · -- For `n ≤ 1` both sides are `1`: `G` is constant and the root product is empty.
    have h0 : G.natDegree = 0 := by omega
    have : IsEmpty (Fin G.natDegree) := by rw [h0]; infer_instance
    interval_cases n <;> simp [Finset.univ_eq_empty]
  rw [formDiscr_of_natDegree_eq_pred hn hG, map_mul, map_pow,
    discr_eq_leadingCoeff_pow_mul_prod_roots_sub_sq hr, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-! ### Examples -/

/-- The binary quadratic `X² - Y²` has discriminant `4`. -/
example : (X ^ 2 - 1 : ℤ[X]).formDiscr 2 = 4 := by
  rw [formDiscr_of_natDegree_eq (by compute_degree!), discr_of_degree_eq_two (by compute_degree!)]
  norm_num [coeff_one, coeff_X_pow]

/-- Doubling the form multiplies the discriminant by `2 ^ (2 · 2 - 2) = 4`, giving `16`. -/
example : (C 2 * (X ^ 2 - 1) : ℤ[X]).formDiscr 2 = 16 := by
  rw [formDiscr_C_mul, formDiscr_of_natDegree_eq (by compute_degree!),
    discr_of_degree_eq_two (by compute_degree!)]
  norm_num [coeff_one, coeff_X_pow]

/-- The constant `2`, as a binary form of degree `2`, has a double root at infinity. -/
example : (C 2 : ℤ[X]).formDiscr 2 = 0 :=
  formDiscr_eq_zero_of_natDegree_le le_rfl (by simp)

/-- As a binary form of degree `1`, the same constant has discriminant `1`, not `2² · 1`. -/
example : (C 2 : ℤ[X]).formDiscr 1 = 1 :=
  formDiscr_one _

/-- The cubic `4X³ + b₂X² + 2b₄X + b₆` of a Weierstrass curve, viewed as a quartic binary form, has
a root at infinity, and its discriminant is `16` times that of the cubic, in every
characteristic. -/
example (b₂ b₄ b₆ : R) :
    (C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X + C b₆ : R[X]).formDiscr 4 =
      16 * (C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X + C b₆ : R[X]).discr := by
  rw [formDiscr_succ_eq_coeff_sq_mul_discr (n := 3) (by norm_num) (by compute_degree)]
  norm_num [coeff_X, coeff_C, coeff_X_pow]

end Polynomial
