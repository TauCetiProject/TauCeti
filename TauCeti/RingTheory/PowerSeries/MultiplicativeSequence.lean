/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

import Mathlib.Data.Multiset.Fintype

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
the normalization on a single root, and stability under adjoining a zero root.

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
  have h : (fun j : Fin (n + 1) => MvPolynomial.aeval
      (fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1))
      (Fin.snoc (α := fun _ => MvPolynomial (Fin n) R) MvPolynomial.X 0 j)) =
      fun j : Fin (n + 1) =>
        (0 ::ₘ univ.val.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)).esymm (j + 1) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, map_zero, Fin.val_last, Multiset.esymm_cons_zero,
        Multiset.esymm_of_card_lt (by simp)]
    · rw [Fin.snoc_castSucc, MvPolynomial.aeval_X, Fin.val_castSucc, Multiset.esymm_cons_zero,
        MvPolynomial.esymm_eq_multiset_esymm]
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

end PowerSeries
