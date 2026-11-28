/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.NewtonPolynomial
public import TauCeti.RingTheory.PowerSeries.Expand

import Mathlib.Data.Multiset.Fintype
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.Algebra.MvPolynomial.Coeff
import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# The multiplicative sequence of a power series

Let `Q(t) = ∑ qₖ tᵏ` be a power series over a commutative ring `R`. For `n` variables
`x₁, …, xₙ`, the coefficient of `tᵏ` in `∏ᵢ Q(xᵢ t)` is a symmetric polynomial in the `xᵢ`, so
by the fundamental theorem of symmetric polynomials it is a unique polynomial
`Kₖ(e₁, …, eₙ)` in the elementary symmetric polynomials. When `Q(0) = 1`, the family `(Kₖ)` is
Hirzebruch's *multiplicative sequence* belonging to `Q`.

In characteristic class theory the `xᵢ` are the formal roots of a vector bundle and the `eᵢ` its
Chern classes: for `Q(t) = t / (1 - e⁻ᵗ)` the value `Kₖ(c₁, …, cₙ)` is the degree-`2k` part of
the Todd class of a complex bundle of rank `n`. The `L` and `Â` classes come from even series
`Q(z)`: one first writes `Q(z) = P(z²)` and then applies the construction to `P`, whose roots are
the squares `xᵢ²`, so that the `eᵢ` are the elementary symmetric polynomials in the `xᵢ²`, that
is, the Pontryagin classes. This file develops the algebra that such definitions rest on: the
root description of `Kₖ` in any commutative `R`-algebra, the Whitney (product) formula for roots,
the normalization on a single root, stability under adjoining a zero root, the root description
for even series, and the explicit polynomials `K₁`, `K₂` and `K₃`.

## Main definitions

* `PowerSeries.multiplicativeSequence Q n k`: the polynomial `Kₖ` in `n` variables, where the
  variable `j : Fin n` stands for the elementary symmetric polynomial `e_{j+1}`.

## Main results

* `PowerSeries.aeval_esymm_multiplicativeSequence` and
  `PowerSeries.eq_multiplicativeSequence_iff`: `Kₖ` is the unique polynomial whose value at
  `e₁, …, eₙ` is the coefficient of `tᵏ` in `∏ᵢ Q(xᵢ t)`.
* `PowerSeries.mk_aeval_multiplicativeSequence`: for `n` roots `xᵢ` in any commutative
  `R`-algebra, `∑ₖ Kₖ(e₁(x), …, eₙ(x)) tᵏ = ∏ᵢ Q(xᵢ t)`.
* `PowerSeries.aeval_multiset_esymm_multiplicativeSequence`: the same, coefficientwise.
* `PowerSeries.aeval_multiset_esymm_add_multiplicativeSequence`: the Whitney formula: on the
  union of two families of roots, `Kₖ` is the convolution of the values of `K` on each family.
* `PowerSeries.multiplicativeSequence_one_left`: on a single root, `Kₖ(e₁) = qₖ e₁ᵏ`.
* `PowerSeries.multiplicativeSequence_zero_right`: `K₀ = Q(0) ^ n`.
* `PowerSeries.aeval_snoc_zero_multiplicativeSequence`: setting `eₙ₊₁ = 0` in the polynomial for
  `n + 1` roots gives `Q(0)` times the polynomial for `n` roots.
* `PowerSeries.aeval_pi_single_zero_multiplicativeSequence`: evaluating at `e₁ = x` and `eⱼ = 0`
  for `j ≥ 2` gives `Q(0) ^ n qₖ xᵏ`; when `Q(0) = 1`, the total class `1 + x` goes to `Q(x)`.
* `PowerSeries.expand_mk_aeval_multiplicativeSequence`,
  `PowerSeries.aeval_multiset_esymm_sq_multiplicativeSequence`: for the even series `Q(t²)`,
  `∏_{x ∈ s} Q(x² t²)` is `∑ₖ Kₖ(e₁(s²), …, eₙ(s²)) t²ᵏ`, where `s²` is the multiset of squares.
* `PowerSeries.map_multiplicativeSequence`: the multiplicative sequence is compatible with change
  of coefficients.
* `PowerSeries.multiplicativeSequence_one_add_X`: the multiplicative sequence of `1 + X` is
  `Kₖ = eₖ`.
* `PowerSeries.constantCoeff_multiplicativeSequence`: in positive degree `Kₖ` has no constant
  term.
* `PowerSeries.natCast_mul_multiplicativeSequence`: the Newton-type recursion
  `m Kₘ = ∑_{a + b = m} Kₐ g_b s_b` when `Q G = X Q'`, where `s_b` is the Newton polynomial.
* `TauCeti.coeff_single_newtonMvPolynomial`: the coefficient of `eₖ` in the Newton polynomial
  `sₖ` is `(-1)ᵏ⁻¹ k`.
* `PowerSeries.coeff_single_multiplicativeSequence`: for `Q(0) = 1`, the coefficient of `eₖ` in
  `Kₖ` is `(-1)ᵏ⁻¹` times the coefficient of `tᵏ` in `t Q'(t) / Q(t)`.
* `PowerSeries.multiplicativeSequence_one_right`, `PowerSeries.multiplicativeSequence_two_right`,
  `PowerSeries.multiplicativeSequence_three_right`: for `Q(0) = 1`, `K₁ = q₁ e₁`,
  `K₂ = q₂ e₁² + (q₁² - 2 q₂) e₂` and
  `K₃ = q₃ e₁³ + (q₁ q₂ - 3 q₃) e₁ e₂ + (q₁³ - 3 q₁ q₂ + 3 q₃) e₃`.

## References

* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, §1.
* J. Milnor and J. Stasheff, *Characteristic Classes*, §19.
-/

public section

open Finset

namespace PowerSeries

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Pushing `∏ᵢ Q(xᵢ t)` forward along an algebra homomorphism `φ` out of `R[x]` replaces each
root `xᵢ` by `φ xᵢ`. -/
theorem map_prod_rescale_X {σ S : Type*} [Fintype σ] [CommSemiring S] [Algebra R S]
    (Q : PowerSeries R) (φ : MvPolynomial σ R →ₐ[R] S) :
    map (φ : MvPolynomial σ R →+* S)
        (∏ i : σ, rescale (MvPolynomial.X i) (Q.map (algebraMap R _))) =
      ∏ i : σ, rescale (φ (MvPolynomial.X i)) (Q.map (algebraMap R S)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← rescale_map, ← RingHom.comp_apply (map _), ← map_comp, AlgHom.comp_algebraMap,
    RingHom.coe_coe]

/-- The coefficient of `tᵏ` in `∏ᵢ Q(xᵢ t)` is a symmetric polynomial in the `xᵢ`. -/
theorem isSymmetric_coeff_prod_rescale_X {σ : Type*} [Fintype σ] (Q : PowerSeries R)
    (k : ℕ) :
    (coeff k (∏ i : σ, rescale (MvPolynomial.X i)
      (Q.map (algebraMap R (MvPolynomial σ R))))).IsSymmetric := by
  intro e
  have h := congrArg (coeff k) (map_prod_rescale_X Q (MvPolynomial.rename e))
  rw [coeff_map, RingHom.coe_coe] at h
  simp only [h, MvPolynomial.rename_X]
  exact congrArg (coeff k) (Equiv.prod_comp e fun i => rescale (MvPolynomial.X i) _)

end CommSemiring

variable {R : Type*} [CommRing R]

/-- The **multiplicative sequence** belonging to the power series `Q`, in `n` variables:
`Q.multiplicativeSequence n k` is the unique polynomial `Kₖ` such that substituting the
elementary symmetric polynomials `e₁, …, eₙ` of `x₁, …, xₙ` gives the coefficient of `tᵏ` in
`∏ᵢ Q(xᵢ t)`. The variable `j : Fin n` stands for `e_{j+1}`, following
`MvPolynomial.esymmAlgHom`. -/
noncomputable def multiplicativeSequence (Q : PowerSeries R) (n k : ℕ) :
    MvPolynomial (Fin n) R :=
  (MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).symm
    ⟨coeff k (∏ i : Fin n, rescale (MvPolynomial.X i) (Q.map (algebraMap R _))),
      isSymmetric_coeff_prod_rescale_X Q k⟩

variable (Q : PowerSeries R) (n k : ℕ)

/-- The defining property of `PowerSeries.multiplicativeSequence`: its value at the elementary
symmetric polynomials `e₁, …, eₙ` is the coefficient of `tᵏ` in `∏ᵢ Q(xᵢ t)`. -/
theorem aeval_esymm_multiplicativeSequence :
    MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1))
        (Q.multiplicativeSequence n k) =
      coeff k (∏ i : Fin n, rescale (MvPolynomial.X i) (Q.map (algebraMap R _))) := by
  rw [← MvPolynomial.esymmAlgHom_apply,
    ← MvPolynomial.esymmAlgEquiv_apply (Fin n) R (Fintype.card_fin n), multiplicativeSequence,
    AlgEquiv.apply_symm_apply]

variable {Q n k} in
/-- `PowerSeries.multiplicativeSequence` is characterized by its value at the elementary
symmetric polynomials. -/
theorem eq_multiplicativeSequence_iff {p : MvPolynomial (Fin n) R} :
    p = Q.multiplicativeSequence n k ↔
      MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1)) p =
        coeff k (∏ i : Fin n, rescale (MvPolynomial.X i) (Q.map (algebraMap R _))) := by
  refine ⟨fun h => h ▸ aeval_esymm_multiplicativeSequence Q n k, fun h => ?_⟩
  refine MvPolynomial.esymmAlgHom_injective R (Fintype.card_fin n).ge (Subtype.ext ?_)
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply,
    aeval_esymm_multiplicativeSequence, h]

section Roots

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- **Root description of the multiplicative sequence**, for an indexed family of roots: for
`x : Fin n → S`, `∑ₖ Kₖ(e₁(x), …, eₙ(x)) tᵏ = ∏ᵢ Q(xᵢ t)`. -/
private theorem mk_aeval_multiplicativeSequence_fin (x : Fin n → S) :
    mk (fun k => MvPolynomial.aeval (fun j : Fin n => (univ.val.map x).esymm (j + 1))
        (Q.multiplicativeSequence n k)) =
      ∏ i : Fin n, rescale (x i) (Q.map (algebraMap R S)) := by
  ext k
  have h : (fun j : Fin n => (univ.val.map x).esymm (j + 1)) =
      fun j : Fin n => MvPolynomial.aeval x (MvPolynomial.esymm (Fin n) R (j + 1)) := by
    simp [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  rw [coeff_mk, h, ← MvPolynomial.comp_aeval_apply, aeval_esymm_multiplicativeSequence,
    ← RingHom.coe_coe, ← coeff_map, map_prod_rescale_X]
  simp only [MvPolynomial.aeval_X]

/-- **Root description of the multiplicative sequence**: for a multiset `s` of `n` roots in a
commutative `R`-algebra, `∑ₖ Kₖ(e₁(s), …, eₙ(s)) tᵏ = ∏_{x ∈ s} Q(x t)`. -/
theorem mk_aeval_multiplicativeSequence (s : Multiset S) (hs : s.card = n) :
    mk (fun k => MvPolynomial.aeval (fun j : Fin n => s.esymm (j + 1))
        (Q.multiplicativeSequence n k)) =
      (s.map fun x => rescale x (Q.map (algebraMap R S))).prod := by
  classical
  let e : Fin n ≃ s.ToType := Fintype.equivOfCardEq (by simp [hs])
  have hx : (univ.val.map fun i => (e i : S)) = s := by
    conv_rhs => rw [← Multiset.map_univ_coe s, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
    rw [Function.comp_def]
  rw [← hx, mk_aeval_multiplicativeSequence_fin, Finset.prod_eq_multiset_prod, Multiset.map_map,
    Function.comp_def]

/-- **Root description of the multiplicative sequence**, coefficientwise: for a multiset `s` of
`n` roots, `Kₖ(e₁(s), …, eₙ(s))` is the coefficient of `tᵏ` in `∏_{x ∈ s} Q(x t)`. -/
theorem aeval_multiset_esymm_multiplicativeSequence (s : Multiset S) (hs : s.card = n) :
    MvPolynomial.aeval (fun j : Fin n => s.esymm (j + 1)) (Q.multiplicativeSequence n k) =
      coeff k (s.map fun x => rescale x (Q.map (algebraMap R S))).prod := by
  rw [← mk_aeval_multiplicativeSequence Q n s hs, coeff_mk]

/-- **The Whitney formula for roots**: on the union of a family `s` of `n` roots and a family `t`
of `m` roots, `Kₖ` is the convolution of the values of the multiplicative sequence on `s` and
on `t`. -/
theorem aeval_multiset_esymm_add_multiplicativeSequence {m : ℕ} (s t : Multiset S)
    (hs : s.card = n) (ht : t.card = m) :
    MvPolynomial.aeval (fun j : Fin (n + m) => (s + t).esymm (j + 1))
        (Q.multiplicativeSequence (n + m) k) =
      ∑ p ∈ antidiagonal k,
        MvPolynomial.aeval (fun j : Fin n => s.esymm (j + 1)) (Q.multiplicativeSequence n p.1) *
          MvPolynomial.aeval (fun j : Fin m => t.esymm (j + 1))
            (Q.multiplicativeSequence m p.2) := by
  rw [aeval_multiset_esymm_multiplicativeSequence Q (n + m) k (s + t) (by simp [hs, ht]),
    Multiset.map_add, Multiset.prod_add, coeff_mul]
  simp_rw [aeval_multiset_esymm_multiplicativeSequence Q _ _ _ hs,
    aeval_multiset_esymm_multiplicativeSequence Q _ _ _ ht]

end Roots

section Normalization

/-- In a single variable, `e₁` is the root itself, so `Kₖ(e₁) = qₖ e₁ᵏ`. -/
@[simp]
theorem multiplicativeSequence_one_left :
    Q.multiplicativeSequence 1 k = MvPolynomial.C (coeff k Q) * MvPolynomial.X 0 ^ k := by
  refine (eq_multiplicativeSequence_iff.2 ?_).symm
  simp [coeff_rescale, mul_comm]

variable {Q}

/-- The degree-zero term of the multiplicative sequence is `Q(0) ^ n`; in particular it is `1`
when `Q(0) = 1`. -/
@[simp]
theorem multiplicativeSequence_zero_right :
    Q.multiplicativeSequence n 0 = MvPolynomial.C (constantCoeff Q ^ n) := by
  refine (eq_multiplicativeSequence_iff.2 ?_).symm
  rw [MvPolynomial.aeval_C, coeff_zero_eq_constantCoeff_apply, map_prod]
  simp [← coeff_zero_eq_constantCoeff_apply (rescale _ _), coeff_rescale]

/-- Setting the last variable to zero in the polynomial for `n + 1` roots gives `Q(0)` times the
polynomial for `n` roots, as a statement in `R[x₁, …, xₙ]`. -/
private theorem aeval_snoc_X_zero_multiplicativeSequence :
    MvPolynomial.aeval (Fin.snoc MvPolynomial.X 0 : Fin (n + 1) → MvPolynomial (Fin n) R)
        (Q.multiplicativeSequence (n + 1) k) =
      MvPolynomial.C (constantCoeff Q) * Q.multiplicativeSequence n k := by
  refine MvPolynomial.esymmAlgHom_injective R (Fintype.card_fin n).ge (Subtype.ext ?_)
  -- The elementary symmetric polynomials of `x₁, …, xₙ, 0` are those of `x₁, …, xₙ`, then `0`.
  have h := Fin.comp_snoc
    (MvPolynomial.aeval (R := R) fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1))
    MvPolynomial.X 0
  simp only [map_zero, Function.comp_def, MvPolynomial.aeval_X] at h
  rw [MvPolynomial.esymm_eq_multiset_esymm, ← Multiset.esymm_cons_zero_eq_snoc _ (by simp),
    ← MvPolynomial.esymm_eq_multiset_esymm] at h
  -- Both sides are now coefficients of `∏ᵢ Q(xᵢ t)`, with an extra factor `Q(0 t)` on the left.
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply,
    MvPolynomial.comp_aeval_apply, h,
    aeval_multiset_esymm_multiplicativeSequence Q (n + 1) k _ (by simp), map_mul,
    MvPolynomial.aeval_C, aeval_esymm_multiplicativeSequence]
  simp [Finset.prod_eq_multiset_prod, Function.comp_def,
    ← coeff_zero_eq_constantCoeff_apply (map _ Q), MvPolynomial.algebraMap_eq]

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- **Stability of the multiplicative sequence**: setting `eₙ₊₁ = 0` in the polynomial for
`n + 1` roots gives `Q(0)` times the polynomial for `n` roots. When `Q(0) = 1`, the
multiplicative sequence is therefore unchanged by adjoining a zero root. -/
@[simp]
theorem aeval_snoc_zero_multiplicativeSequence (c : Fin n → S) :
    MvPolynomial.aeval (Fin.snoc c 0) (Q.multiplicativeSequence (n + 1) k) =
      algebraMap R S (constantCoeff Q) * MvPolynomial.aeval c (Q.multiplicativeSequence n k) := by
  rw [← MvPolynomial.aeval_C c, ← map_mul, ← aeval_snoc_X_zero_multiplicativeSequence,
    MvPolynomial.comp_aeval_apply]
  refine congrArg (fun f => MvPolynomial.aeval f _) (funext fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

/-- **Normalization of the multiplicative sequence**: evaluating at `e₁ = x` and `eⱼ = 0` for
`j ≥ 2` gives `Q(0) ^ n qₖ xᵏ`. When `Q(0) = 1`, the multiplicative sequence therefore sends the
total class `1 + x` to `Q(x)`. -/
@[simp]
theorem aeval_pi_single_zero_multiplicativeSequence (x : S) :
    MvPolynomial.aeval (Pi.single 0 x : Fin (n + 1) → S) (Q.multiplicativeSequence (n + 1) k) =
      algebraMap R S (constantCoeff Q ^ n * coeff k Q) * x ^ k := by
  induction n with
  | zero => simp [multiplicativeSequence_one_left]
  | succ n ih =>
    have h : (Pi.single 0 x : Fin (n + 2) → S) = Fin.snoc (Pi.single 0 x : Fin (n + 1) → S) 0 := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [Fin.ext_iff]
      · simp [Pi.single_apply]
    rw [h, aeval_snoc_zero_multiplicativeSequence, ih]
    simp only [map_mul, map_pow]
    ring

end Normalization

section Even

variable {S : Type*} [CommRing S] [Algebra R S]

/-- **Multiplicative sequences of even series**: for a multiset `s` of `n` roots,
`∏_{x ∈ s} Q(x² t²)` is obtained from `∑ₖ Kₖ(e₁(s²), …, eₙ(s²)) tᵏ`, where `Kₖ` is the
multiplicative sequence of `Q` and `s²` is the multiset of squares of the roots, by substituting
`t²` for `t`. An even characteristic series is of the form `Q(t²)`; for the `L` and `Â` classes the
roots are one degree-two root per oriented real 2-plane, and the `eᵢ(s²)` are the Pontryagin
classes. -/
theorem expand_mk_aeval_multiplicativeSequence (s : Multiset S) (hs : s.card = n) :
    expand 2 two_ne_zero (mk fun k => MvPolynomial.aeval
        (fun j : Fin n => (s.map (· ^ 2)).esymm (j + 1)) (Q.multiplicativeSequence n k)) =
      (s.map fun x => rescale x ((expand 2 two_ne_zero Q).map (algebraMap R S))).prod := by
  rw [mk_aeval_multiplicativeSequence Q n _ (by simpa using hs), map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  simp [Function.comp_def, rescale_expand]

/-- **Multiplicative sequences of even series**, coefficientwise: for a multiset `s` of `n` roots,
`Kₖ(e₁(s²), …, eₙ(s²))` is the coefficient of `t²ᵏ` in `∏_{x ∈ s} Q(x² t²)`, where `Kₖ` is the
multiplicative sequence of `Q`. -/
theorem aeval_multiset_esymm_sq_multiplicativeSequence (s : Multiset S) (hs : s.card = n) :
    MvPolynomial.aeval (fun j : Fin n => (s.map (· ^ 2)).esymm (j + 1))
        (Q.multiplicativeSequence n k) =
      coeff (2 * k)
        (s.map fun x => rescale x ((expand 2 two_ne_zero Q).map (algebraMap R S))).prod := by
  have h := congrArg (coeff (2 * k)) (expand_mk_aeval_multiplicativeSequence Q n s hs)
  rwa [coeff_expand_mul, coeff_mk] at h

end Even

section LowDegree

variable {Q} {S : Type*} [CommRing S] [Algebra R S]

/-- The coefficients of `∏_{x ∈ s} Q(x t)` in degrees `0` to `3`, for `Q(0) = 1`, as polynomials in
the elementary symmetric functions of the roots. -/
private theorem coeff_multiset_prod_rescale_le_three (hQ : constantCoeff Q = 1)
    (s : Multiset S) :
    coeff 0 (s.map fun x => rescale x (Q.map (algebraMap R S))).prod = 1 ∧
    coeff 1 (s.map fun x => rescale x (Q.map (algebraMap R S))).prod =
      algebraMap R S (coeff 1 Q) * s.esymm 1 ∧
    coeff 2 (s.map fun x => rescale x (Q.map (algebraMap R S))).prod =
      algebraMap R S (coeff 2 Q) * s.esymm 1 ^ 2 +
        algebraMap R S (coeff 1 Q ^ 2 - 2 * coeff 2 Q) * s.esymm 2 ∧
    coeff 3 (s.map fun x => rescale x (Q.map (algebraMap R S))).prod =
      algebraMap R S (coeff 3 Q) * s.esymm 1 ^ 3 +
        algebraMap R S (coeff 1 Q * coeff 2 Q - 3 * coeff 3 Q) * s.esymm 1 * s.esymm 2 +
        algebraMap R S (coeff 1 Q ^ 3 - 3 * coeff 1 Q * coeff 2 Q + 3 * coeff 3 Q) *
          s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons x s ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have hq0 : algebraMap R S (coeff 0 Q) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, hQ, map_one]
    simp only [Multiset.map_cons, Multiset.prod_cons, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, coeff_rescale, coeff_map, Nat.reduceAdd,
      Multiset.esymm_cons, Multiset.esymm_zero, hq0, h0, h1, h2, h3, map_add, map_sub, map_mul,
      map_pow, map_ofNat]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

variable {n k} in
/-- To identify `Kₖ` in `n` variables, it suffices to compute the value of a polynomial at the
elementary symmetric polynomials of the variables, viewed as a multiset of roots. -/
private theorem eq_multiplicativeSequence_of_aeval {p : MvPolynomial (Fin n) R}
    (h : MvPolynomial.aeval
        (fun j : Fin n => (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))).esymm (j + 1)) p =
      coeff k ((univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))).map
        fun x => rescale x (Q.map (algebraMap R _))).prod) :
    p = Q.multiplicativeSequence n k := by
  rw [eq_multiplicativeSequence_iff]
  simpa [MvPolynomial.esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod, Multiset.map_map,
    Function.comp_def] using h

/-- **The linear term of a multiplicative sequence**: for `Q(0) = 1`, `K₁ = q₁ e₁`. -/
theorem multiplicativeSequence_one_right (hQ : constantCoeff Q = 1) :
    Q.multiplicativeSequence (n + 1) 1 = MvPolynomial.C (coeff 1 Q) * MvPolynomial.X 0 := by
  refine (eq_multiplicativeSequence_of_aeval ?_).symm
  rw [(coeff_multiset_prod_rescale_le_three hQ _).2.1]
  simp [MvPolynomial.algebraMap_eq]

/-- **The quadratic term of a multiplicative sequence**: for `Q(0) = 1` and at least two variables,
`K₂ = q₂ e₁² + (q₁² - 2 q₂) e₂`. -/
theorem multiplicativeSequence_two_right (hQ : constantCoeff Q = 1) :
    Q.multiplicativeSequence (n + 2) 2 =
      MvPolynomial.C (coeff 2 Q) * MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C (coeff 1 Q ^ 2 - 2 * coeff 2 Q) * MvPolynomial.X 1 := by
  refine (eq_multiplicativeSequence_of_aeval ?_).symm
  rw [(coeff_multiset_prod_rescale_le_three hQ _).2.2.1]
  simp [MvPolynomial.algebraMap_eq]

/-- **The cubic term of a multiplicative sequence**: for `Q(0) = 1` and at least three variables,
`K₃ = q₃ e₁³ + (q₁ q₂ - 3 q₃) e₁ e₂ + (q₁³ - 3 q₁ q₂ + 3 q₃) e₃`. -/
theorem multiplicativeSequence_three_right (hQ : constantCoeff Q = 1) :
    Q.multiplicativeSequence (n + 3) 3 =
      MvPolynomial.C (coeff 3 Q) * MvPolynomial.X 0 ^ 3 +
        MvPolynomial.C (coeff 1 Q * coeff 2 Q - 3 * coeff 3 Q) * MvPolynomial.X 0 *
          MvPolynomial.X 1 +
        MvPolynomial.C (coeff 1 Q ^ 3 - 3 * coeff 1 Q * coeff 2 Q + 3 * coeff 3 Q) *
          MvPolynomial.X 2 := by
  refine (eq_multiplicativeSequence_of_aeval ?_).symm
  rw [(coeff_multiset_prod_rescale_le_three hQ _).2.2.2]
  simp [MvPolynomial.algebraMap_eq, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]

end LowDegree

section Map

variable {S : Type*} [CommRing S]

/-- **Change of coefficients**: changing the coefficients of the multiplicative sequence of `Q`
along a ring homomorphism `f` gives the multiplicative sequence of the image of `Q`. -/
@[simp]
theorem map_multiplicativeSequence (f : R →+* S) :
    MvPolynomial.map f (Q.multiplicativeSequence n k) = (Q.map f).multiplicativeSequence n k := by
  refine eq_multiplicativeSequence_iff.2 ?_
  have h : (MvPolynomial.aeval fun j : Fin n => MvPolynomial.esymm (Fin n) S (j + 1)).toRingHom.comp
      (MvPolynomial.map f) =
      (MvPolynomial.map f).comp
        (MvPolynomial.aeval fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1)).toRingHom := by
    ext <;> simp [MvPolynomial.map_esymm]
  have h' := congrArg (fun φ => φ (Q.multiplicativeSequence n k)) h
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h'
  rw [h', aeval_esymm_multiplicativeSequence, ← coeff_map, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  ext m
  simp [coeff_rescale, MvPolynomial.algebraMap_eq]

end Map

section Elementary

variable {n}

/-- **The multiplicative sequence of `1 + X`** is the sequence of elementary symmetric
polynomials: since `∏ᵢ (1 + xᵢ t) = ∑ₖ eₖ tᵏ`, the polynomial `K_{i+1}` is the variable `i`, which
stands for `e_{i+1}`. -/
theorem multiplicativeSequence_one_add_X (i : Fin n) :
    (1 + X : R⟦X⟧).multiplicativeSequence n (i + 1) = MvPolynomial.X i := by
  refine (eq_multiplicativeSequence_iff.2 ?_).symm
  have h : ∏ j : Fin n, rescale (MvPolynomial.X j)
      ((1 + X : R⟦X⟧).map (algebraMap R (MvPolynomial (Fin n) R))) =
      ∏ j : Fin n, (1 + C (MvPolynomial.X j) * X) :=
    Finset.prod_congr rfl fun j _ => by simp
  rw [MvPolynomial.aeval_X, h, ← TauCeti.mk_esymm_eq_prod_one_add_X (σ := Fin n) R, coeff_mk]

end Elementary

section Indecomposable

/-! ### The indecomposable coefficient

For `Q(0) = 1` write `t Q'(t) / Q(t) = ∑ₘ gₘ tᵐ`. Then `t F' = F · ∑ₘ gₘ pₘ tᵐ` for
`F = ∏ᵢ Q(xᵢ t)`, where `pₘ` is the `m`-th power sum of the roots, so `m Kₘ = ∑ₐ Kₐ g_{m-a} N_{m-a}`
with `N_b` the Newton polynomial. Taking the coefficient of the monomial `eₖ`, which is a
derivation at `0` and kills all products of polynomials without constant term, gives
`k c = gₖ d`, where `c` and `d` are the coefficients of `eₖ` in `Kₖ` and `Nₖ`. Applying this to
`Q = 1 + X`, whose multiplicative sequence is `Kₖ = eₖ`, gives `d = (-1)ᵏ⁻¹ k`. The factor `k` is
cancelled for the universal series over `ℤ[q₀, q₁, …]`, and the result is then specialized to
any commutative ring. -/

variable {Q n} {G : R⟦X⟧}

/-- **Newton-type identity for the multiplicative sequence**: if `Q G = X Q'`, then
`m Kₘ = ∑_{a + b = m} Kₐ g_b s_b`, where `s_b` is the Newton polynomial. -/
theorem natCast_mul_multiplicativeSequence (hG : Q * G = X * d⁄dX Q) (m : ℕ) :
    (m : MvPolynomial (Fin n) R) * Q.multiplicativeSequence n m =
      ∑ p ∈ antidiagonal m, Q.multiplicativeSequence n p.1 *
        (MvPolynomial.C (coeff p.2 G) * TauCeti.newtonMvPolynomial R n p.2) := by
  have hs : (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))).card = n := by simp
  refine MvPolynomial.aeval_multiset_esymm_X_injective R (Fintype.card_fin n).ge ?_
  have h := congrArg (coeff m) (X_mul_derivative_multiset_prod_rescale hG
    (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))))
  rw [coeff_X_mul_derivative, coeff_mul] at h
  have hK (k : ℕ) := aeval_multiset_esymm_multiplicativeSequence Q n k
    (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))) hs
  have hN (k : ℕ) := Multiset.aeval_esymm_newtonMvPolynomial (R := R) (k := k)
    (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))) hs
  simp only [map_mul, map_natCast, map_sum, MvPolynomial.aeval_C, hK, hN]
  simpa only [coeff_mk] using h

/-- In positive degree, the multiplicative sequence has no constant term. -/
theorem constantCoeff_multiplicativeSequence {m : ℕ} (hm : m ≠ 0) :
    MvPolynomial.constantCoeff (Q.multiplicativeSequence n m) = 0 := by
  have h := aeval_multiset_esymm_multiplicativeSequence Q n m (Multiset.replicate n (0 : R))
    (by simp)
  simp only [Multiset.esymm_replicate_zero, Multiset.map_replicate, Multiset.prod_replicate,
    rescale_zero_apply, ← map_pow, coeff_C, hm, ite_false] at h
  simpa [← Pi.zero_def, MvPolynomial.aeval_zero] using h

/-- If `Q(0) = 1` and `Q G = X Q'`, then `k` times the coefficient of `eₖ` in `Kₖ` is `gₖ` times
the coefficient of `eₖ` in the Newton polynomial `sₖ`. -/
private theorem natCast_mul_coeff_single_multiplicativeSequence (hQ : constantCoeff Q = 1)
    (hG : Q * G = X * d⁄dX Q) (i : Fin n) :
    ((i + 1 : ℕ) : R) * (Q.multiplicativeSequence n (i + 1)).coeff (Finsupp.single i 1) =
      coeff (i + 1) G * (TauCeti.newtonMvPolynomial R n (i + 1)).coeff (Finsupp.single i 1) := by
  have hG₀ : coeff 0 G = 0 := by
    simpa [hQ] using congrArg constantCoeff hG
  -- Every term `g_b s_b` has zero constant term.
  have hcc (b : ℕ) : MvPolynomial.constantCoeff
      (MvPolynomial.C (coeff b G) * TauCeti.newtonMvPolynomial R n b) = 0 := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp [hG₀]
    · simp [TauCeti.constantCoeff_newtonMvPolynomial hb]
  have h := congrArg (fun p : MvPolynomial (Fin n) R => p.coeff (Finsupp.single i 1))
    (natCast_mul_multiplicativeSequence hG (i + 1))
  simp only [MvPolynomial.coeff_single_one_mul, MvPolynomial.coeff_sum, hcc, mul_zero,
    zero_add] at h
  rw [Finset.sum_eq_single ((0 : ℕ), (i : ℕ) + 1)] at h
  · have h0 : (0 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    simpa [hQ, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_one, h0] using h
  · rintro ⟨a, b⟩ hab hne
    have ha : a ≠ 0 := by
      rintro rfl
      exact hne (by simpa [eq_comm] using hab)
    rw [constantCoeff_multiplicativeSequence ha, zero_mul]
  · simp

/-- The coefficient of `eₖ` in the Newton polynomial `sₖ` is `(-1)ᵏ⁻¹ k`. -/
theorem _root_.TauCeti.coeff_single_newtonMvPolynomial (i : Fin n) :
    (TauCeti.newtonMvPolynomial R n (i + 1)).coeff (Finsupp.single i 1) =
      (-1) ^ (i : ℕ) * ((i + 1 : ℕ) : R) := by
  -- `t (1 + t)' / (1 + t) = ∑_{m ≥ 1} (-1)ᵐ⁻¹ tᵐ`.
  have hG : (1 + X : R⟦X⟧) * (X * rescale (-1) (mk 1)) = X * d⁄dX (1 + X : R⟦X⟧) := by
    have h := congrArg (rescale (-1 : R)) (mk_one_mul_one_sub_eq_one (S := R))
    simp only [map_mul, map_sub, map_one, rescale_X, map_neg, neg_mul, one_mul, sub_neg_eq_add] at h
    rw [map_add, derivative_X, derivative_one, zero_add, mul_one]
    linear_combination X * h
  have h := natCast_mul_coeff_single_multiplicativeSequence (by simp) hG i
  rw [multiplicativeSequence_one_add_X] at h
  simp only [MvPolynomial.coeff_X, ↓reduceIte, mul_one] at h
  rw [coeff_succ_X_mul, coeff_rescale, coeff_mk, Pi.one_apply, mul_one] at h
  rw [h, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **The indecomposable coefficient of a multiplicative sequence**: let `Q(0) = 1` and let
`G = X Q' / Q` be the logarithmic derivative series, characterized by `Q G = X Q'`. Then, for
`k = i + 1 ≤ n`, the coefficient of the monomial `eₖ` in `Kₖ` is `(-1)ᵏ⁻¹` times the coefficient
of `Xᵏ` in `G`. Modulo products of lower elementary symmetric polynomials, `Kₖ` is therefore
`(-1)ᵏ⁻¹ gₖ eₖ`. For an even characteristic series `L(X) = P(X²)`, the theorem is applied to `P`,
not to `L`: the variable `i` then stands for `eₖ` of the squared roots, which is the Pontryagin
class `pₖ`, so this computes Hirzebruch's coefficient `sₖ` of `pₖ`. -/
theorem coeff_single_multiplicativeSequence (hQ : constantCoeff Q = 1) (hG : Q * G = X * d⁄dX Q)
    (i : Fin n) :
    (Q.multiplicativeSequence n (i + 1)).coeff (Finsupp.single i 1) =
      (-1) ^ (i : ℕ) * coeff (i + 1) G := by
  -- The universal series `1 + ∑ₘ qₘ Xᵐ⁺¹` over `ℤ[q₀, q₁, …]`, where `k` can be cancelled.
  set Q₀ : (MvPolynomial ℕ ℤ)⟦X⟧ := 1 + X * mk MvPolynomial.X
  have hQ₀ : constantCoeff Q₀ = 1 := by simp [Q₀]
  set G₀ := X * d⁄dX Q₀ * invOfUnit Q₀ 1
  have hG₀ : Q₀ * G₀ = X * d⁄dX Q₀ := by
    rw [mul_comm, mul_assoc, mul_comm (invOfUnit Q₀ 1), mul_invOfUnit Q₀ 1 (by simp [hQ₀]),
      mul_one]
  have h₀ : (Q₀.multiplicativeSequence n (i + 1)).coeff (Finsupp.single i 1) =
      (-1) ^ (i : ℕ) * coeff (i + 1) G₀ := by
    have h := natCast_mul_coeff_single_multiplicativeSequence hQ₀ hG₀ i
    rw [TauCeti.coeff_single_newtonMvPolynomial] at h
    refine mul_left_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero (i : ℕ))) ?_
    rw [h]
    ring
  -- Specialize the universal series to `Q`.
  set f : MvPolynomial ℕ ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) fun m => coeff (m + 1) Q
  have hf : Q₀.map f = Q := by
    ext m
    rcases m with _ | m
    · simp [Q₀, hQ]
    · simp [Q₀, f, coeff_succ_X_mul]
  have hGf : G₀.map f = G := by
    refine (isUnit_iff_constantCoeff.2 (hQ ▸ isUnit_one)).mul_left_cancel ?_
    rw [hG, ← hf, ← map_mul, hG₀, map_mul, map_X, derivative_map]
  have h := congrArg f h₀
  rw [← MvPolynomial.coeff_map, map_multiplicativeSequence, hf, map_mul, map_pow, map_neg,
    map_one, ← coeff_map, hGf] at h
  exact h

end Indecomposable

end PowerSeries
