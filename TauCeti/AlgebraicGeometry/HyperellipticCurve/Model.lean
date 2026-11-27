/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.FormDiscriminant
-- Proof-only: the algebraic closure, integral closedness of `ℤ[a₀, …]`, primality of `2` there,
-- clearing denominators at roots, and reversal for the examples. The statements only need the
-- public import above.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Weierstrass models of hyperelliptic curves and their discriminant

In every characteristic, a curve of genus `g` with a separable degree-two map to the projective
line has a *Weierstrass model* `y² + h(x) y = f(x)` with `deg f ≤ 2g + 2` and `deg h ≤ g + 1`.
This file defines the carrier `Model R g` of such equations over a commutative ring `R`, parallel
to Mathlib's `WeierstrassCurve`, together with its base change, its *Weierstrass form*
`4f + h²` (the right-hand side after completing the square), and its discriminant
`Δ = 2^{-4(g+1)} · disc_{2g+2}(4f + h²)`, where `disc_n` is the discriminant of a binary form of
degree `n` (`Polynomial.formDiscr`).

The division by `2^{4(g+1)}` is the point. The discriminant is defined as one integer polynomial
`universalΔ g` in the coefficients `f₀, …, f_{2g+2}, h₀, …, h_{g+1}`, evaluated at the
coefficients of a model, so that it is defined over every ring and commutes with every ring
homomorphism. In characteristic `2` the Weierstrass form is `h²`, its discriminant vanishes, and
`Δ` is still meaningful: for `y² + y = x³` it is `-27`, a unit modulo `2`. That
`disc_{2g+2}(4f + h²)` is divisible by `2^{4(g+1)}` in `ℤ[f₀, …, h_{g+1}]` is the theorem
`two_pow_mul_universalΔ`. This normalisation is Lockhart's in every genus and Liu's in genus `2`.
For `h = 0` it is `Δ = 2^{4g} · disc_{2g+2}(f)` (`Model.Δ_of_h_eq_zero`).

## Main definitions

* `TauCeti.HyperellipticCurve.Model R g`: a pair `(f, h)` of polynomials over `R` with
  `natDegree f ≤ 2g + 2` and `natDegree h ≤ g + 1`.
* `Model.map`, `Model.baseChange`: applying a ring homomorphism to the coefficients.
* `Model.weierstrassForm`: the polynomial `4f + h²` of degree at most `2g + 2`.
* `Model.universal g`: the model over `ℤ[f₀, …, f_{2g+2}, h₀, …, h_{g+1}]` whose coefficients
  are the variables; every model is its image under a unique ring homomorphism
  (`Model.map_universal_eq_iff`).
* `universalΔ g`: the integer polynomial with `2^{4(g+1)} · universalΔ g = disc_{2g+2}(4f + h²)`.
* `Model.Δ`: the discriminant of a model, `universalΔ g` evaluated at its coefficients.

## Main results

* `two_pow_mul_universalΔ`: the integrality of the discriminant.
* `Model.two_pow_mul_Δ`: `2^{4(g+1)} · Δ = disc_{2g+2}(4f + h²)` over every commutative ring.
* `Model.map_Δ`: compatibility with ring homomorphisms.
* `Model.Δ_of_h_eq_zero`: `Δ(f, 0) = 2^{4g} · disc_{2g+2}(f)`.

## Implementation notes

It suffices to prove the integrality over the universal coefficient ring `A = ℤ[f₀, …, h_{g+1}]`,
an integrally closed domain in which `2` is prime. Write `G = 4f + h²` and `n = 2g + 2`. Over an
algebraic closure of the fraction field of `A`, the discriminant of `G` is, up to sign and powers
of the leading coefficient `c` of `G`, the product of `G'(r)` over the roots `r` of `G`. At a root,
`h(r)² = -4 f(r)`, so `θ = h(r) / 2` satisfies `θ² = -f(r)`; hence `cᵍ⁺¹ θ` is integral over
`A`, and `G'(r) = 4 f'(r) + 2 h(r) h'(r) = 4 (f'(r) + θ h'(r))` is `4` times an element made
integral by a power of `c`. The product over the `n` roots therefore exhibits
`c^N · disc(G)` as `4ⁿ = 2^{4(g+1)}` times an element of `A`, since `A` is integrally closed.
The leading coefficient `c = 4 f_n + h_{g+1}²` is not divisible by the prime `2`, so `2^{4(g+1)}`
divides `disc(G)` itself.

## References

* P. Lockhart, *On the discriminant of a hyperelliptic curve*, Trans. Amer. Math. Soc. 342
  (1994).
* Q. Liu, *Conducteur et discriminant minimal de courbes de genre 2*, Compositio Math. 94 (1994),
  51–79, §1.2.
-/

public section

open Polynomial

namespace TauCeti.HyperellipticCurve

/-- A **Weierstrass model** `y² + h(x) y = f(x)` of a curve of genus `g` over a commutative ring
`R`: a pair of polynomials with `natDegree f ≤ 2g + 2` and `natDegree h ≤ g + 1`. No condition on
the actual degrees or on the discriminant `Model.Δ` is imposed. Mathlib's `WeierstrassCurve`
corresponds to the genus-one models with `f` monic of degree `3` and `natDegree h ≤ 1`. -/
@[ext]
structure Model (R : Type*) [CommRing R] (g : ℕ) where
  /-- The right-hand side `f` of the equation `y² + h(x) y = f(x)`. -/
  f : R[X]
  /-- The cross term `h` of the equation `y² + h(x) y = f(x)`. -/
  h : R[X]
  natDegree_f_le : f.natDegree ≤ 2 * g + 2
  natDegree_h_le : h.natDegree ≤ g + 1

namespace Model

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] {g : ℕ}

/-! ### Base change -/

/-- The model obtained by applying a ring homomorphism to the coefficients of `f` and `h`. -/
noncomputable def map (W : Model R g) (φ : R →+* S) : Model S g where
  f := W.f.map φ
  h := W.h.map φ
  natDegree_f_le := natDegree_map_le.trans W.natDegree_f_le
  natDegree_h_le := natDegree_map_le.trans W.natDegree_h_le

@[simp]
theorem map_f (W : Model R g) (φ : R →+* S) : (W.map φ).f = W.f.map φ :=
  (rfl)

@[simp]
theorem map_h (W : Model R g) (φ : R →+* S) : (W.map φ).h = W.h.map φ :=
  (rfl)

@[simp]
theorem map_id (W : Model R g) : W.map (RingHom.id R) = W := by
  ext <;> simp

theorem map_map (W : Model R g) (φ : R →+* S) (ψ : S →+* A) :
    (W.map φ).map ψ = W.map (ψ.comp φ) := by
  ext <;> simp [Polynomial.map_map]

/-- The base change of a model to an `R`-algebra `A`. -/
noncomputable abbrev baseChange (W : Model R g) (A : Type*) [CommRing A] [Algebra R A] :
    Model A g :=
  W.map (algebraMap R A)

/-! ### The Weierstrass form -/

/-- The **Weierstrass form** `4f + h²` of a model, of degree at most `2g + 2`. The substitution
`w = 2y + h` turns `y² + hy = f` into `w² = 4f + h²`; away from characteristic `2` the roots of
the Weierstrass form are the `x`-coordinates of the finite Weierstrass points. -/
noncomputable def weierstrassForm (W : Model R g) : R[X] :=
  4 * W.f + W.h ^ 2

theorem weierstrassForm_def (W : Model R g) : W.weierstrassForm = 4 * W.f + W.h ^ 2 :=
  (rfl)

theorem natDegree_weierstrassForm_le (W : Model R g) :
    W.weierstrassForm.natDegree ≤ 2 * g + 2 := by
  rw [weierstrassForm_def]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_mul_le.trans (by simpa using W.natDegree_f_le)
  · exact natDegree_pow_le.trans (by linarith [W.natDegree_h_le])

/-- The coefficient of `x ^ (2g + 2)` in the Weierstrass form `4f + h²` is
`4 f_{2g+2} + h_{g+1}²`; it is the leading coefficient when nonzero. -/
theorem coeff_weierstrassForm_two_mul_add_two (W : Model R g) :
    W.weierstrassForm.coeff (2 * g + 2) = 4 * W.f.coeff (2 * g + 2) + W.h.coeff (g + 1) ^ 2 := by
  have hh := coeff_pow_of_natDegree_le (m := 2) W.natDegree_h_le
  rw [show 2 * (g + 1) = 2 * g + 2 by ring] at hh
  rw [weierstrassForm_def, coeff_add, hh, coeff_ofNat_mul]

@[simp]
theorem map_weierstrassForm (W : Model R g) (φ : R →+* S) :
    (W.map φ).weierstrassForm = W.weierstrassForm.map φ := by
  simp [weierstrassForm_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-! ### The universal model -/

/-- The coefficients `f₀, …, f_{2g+2}, h₀, …, h_{g+1}` of a model, indexed by
`Fin (2g + 3) ⊕ Fin (g + 2)` as the variables of the universal model. -/
def coeffs (W : Model R g) : Fin (2 * g + 3) ⊕ Fin (g + 2) → R :=
  Sum.elim (fun i ↦ W.f.coeff i) (fun j ↦ W.h.coeff j)

@[simp]
theorem coeffs_inl (W : Model R g) (i : Fin (2 * g + 3)) : W.coeffs (.inl i) = W.f.coeff i :=
  (rfl)

@[simp]
theorem coeffs_inr (W : Model R g) (j : Fin (g + 2)) : W.coeffs (.inr j) = W.h.coeff j :=
  (rfl)

@[simp]
theorem map_coeffs (W : Model R g) (φ : R →+* S) : (W.map φ).coeffs = φ ∘ W.coeffs := by
  ext (i | j) <;> simp

/-- The **universal model** of genus `g`, over `ℤ[f₀, …, f_{2g+2}, h₀, …, h_{g+1}]`, whose
coefficients are the variables. Every model over a commutative ring is its image under the
evaluation at its coefficients (`Model.map_universal`), and under no other ring homomorphism
(`Model.map_universal_eq_iff`). -/
noncomputable def universal (g : ℕ) : Model (MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) ℤ) g where
  f := (universalPoly (2 * g + 2)).map (MvPolynomial.rename Sum.inl).toRingHom
  h := (universalPoly (g + 1)).map (MvPolynomial.rename Sum.inr).toRingHom
  natDegree_f_le := natDegree_map_le.trans (natDegree_universalPoly _).le
  natDegree_h_le := natDegree_map_le.trans (natDegree_universalPoly _).le

@[simp]
theorem coeffs_universal (g : ℕ) : (universal g).coeffs = MvPolynomial.X := by
  ext (i | j) <;> simp [universal]

@[simp]
theorem coeff_universal_f (i : Fin (2 * g + 3)) :
    (universal g).f.coeff i = MvPolynomial.X (.inl i) :=
  congr_fun (coeffs_universal g) (.inl i)

@[simp]
theorem coeff_universal_h (j : Fin (g + 2)) :
    (universal g).h.coeff j = MvPolynomial.X (.inr j) :=
  congr_fun (coeffs_universal g) (.inr j)

/-- Every model is the specialisation of the universal model at its coefficients. -/
@[simp]
theorem map_universal (W : Model R g) :
    (universal g).map (MvPolynomial.aeval (R := ℤ) W.coeffs : _ →+* R) = W := by
  ext : 1
  · simp only [map_f, universal, Polynomial.map_map]
    convert map_universalPoly_of_natDegree_le W.natDegree_f_le using 2
    exact MvPolynomial.ringHom_ext (by simp) (by simp)
  · simp only [map_h, universal, Polynomial.map_map]
    convert map_universalPoly_of_natDegree_le W.natDegree_h_le using 2
    exact MvPolynomial.ringHom_ext (by simp) (by simp)

/-- **The universal property of the universal model.** A ring homomorphism specialises the
universal model to `W` if and only if it is the evaluation at the coefficients of `W`. -/
theorem map_universal_eq_iff {W : Model R g}
    {φ : MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) ℤ →+* R} :
    (universal g).map φ = W ↔ φ = MvPolynomial.aeval (R := ℤ) W.coeffs := by
  refine ⟨fun hφ ↦ MvPolynomial.ringHom_ext (fun _ ↦ by simp) fun v ↦ ?_, fun hφ ↦ ?_⟩
  · simp only [RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [← hφ, map_coeffs, Function.comp_apply, coeffs_universal]
  · rw [hφ, map_universal]

/-! ### The integrality of the discriminant -/

section Integrality

/-- At a root `r` of `G = 4f + h²` in a field where `2 ≠ 0`, the value `G'(r) / 4` becomes integral
after multiplication by `lc(G) ^ (2k + 1)`, when `natDegree f ≤ 2k + 2` and `natDegree h ≤ k + 1`.
Indeed `G'(r) / 4 = f'(r) + θ h'(r)` with `θ = h(r) / 2`, and `θ² = -f(r)` because `G(r) = 0`. -/
private theorem isIntegral_leadingCoeff_pow_mul_aeval_derivative_div_four {D L : Type*}
    [CommRing D] [Field L] [Algebra D L] (h2 : (2 : L) ≠ 0) {k : ℕ} {f h : D[X]}
    (hf : f.natDegree ≤ 2 * k + 2) (hh : h.natDegree ≤ k + 1) {r : L}
    (hr : aeval r (4 * f + h ^ 2) = 0) :
    IsIntegral D (algebraMap D L (4 * f + h ^ 2).leadingCoeff ^ (2 * k + 1) *
      (aeval r (derivative (4 * f + h ^ 2)) / 4)) := by
  set c := algebraMap D L (4 * f + h ^ 2).leadingCoeff
  have h4 : (4 : L) ≠ 0 := by
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hf' : IsIntegral D (c ^ (2 * k + 1) * aeval r (derivative f)) :=
    isIntegral_leadingCoeff_pow_mul_aeval hr ((natDegree_derivative_le f).trans (by omega))
  have hh' : IsIntegral D (c ^ k * aeval r (derivative h)) :=
    isIntegral_leadingCoeff_pow_mul_aeval hr ((natDegree_derivative_le h).trans (by omega))
  have hθ : IsIntegral D (c ^ (k + 1) * (aeval r h / 2)) := by
    refine .of_pow two_pos ?_
    have hr' : 4 * aeval r f + aeval r h ^ 2 = 0 := by
      rwa [map_add, map_mul, map_pow, map_ofNat] at hr
    convert (isIntegral_leadingCoeff_pow_mul_aeval hr hf).neg using 1
    field_simp
    linear_combination c ^ (2 * k + 2) * hr'
  have hθh' := hθ.pow_add_mul_mul hh'
  rw [show k + 1 + k = 2 * k + 1 by omega] at hθh'
  convert hf'.pow_mul_add hθh' using 2
  simp only [derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_sq, map_add,
    map_mul, map_ofNat]
  field_simp
  ring

/-- Over an algebraically closed field `L` containing `D`, with `G = 4f + h²` as in
`two_pow_dvd_leadingCoeff_pow_mul_discr`, a power of `lc(G)` times `discr G` is `2 ^ (4(k + 1))`
times an element of `L` integral over `D`. Up to sign and powers of `lc(G)`, `discr G` is the
product of `G'` over the `2k + 2` roots of `G`, and each factor is `4` times an element made
integral by `lc(G) ^ (2k + 1)`. -/
private theorem exists_isIntegral_algebraMap_leadingCoeff_pow_mul_discr {D L : Type*}
    [CommRing D] [Field L] [IsAlgClosed L] [Algebra D L]
    (hinj : Function.Injective (algebraMap D L)) (h2 : (2 : D) ≠ 0) {k : ℕ} {f h : D[X]}
    (hf : f.natDegree ≤ 2 * k + 2) (hh : h.natDegree ≤ k + 1)
    (hG : (4 * f + h ^ 2).natDegree = 2 * k + 2) :
    ∃ y : L, IsIntegral D y ∧ algebraMap D L ((4 * f + h ^ 2).leadingCoeff ^
      ((2 * k + 2) * (2 * k + 1)) * (4 * f + h ^ 2).discr) = 2 ^ (4 * (k + 1)) * y := by
  set G := 4 * f + h ^ 2
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap D L) 2]
    exact (map_ne_zero_iff _ hinj).mpr h2
  have h4L : (4 : L) ≠ 0 := by
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact mul_ne_zero h2L h2L
  have hG0 : G ≠ 0 := fun h0 ↦ by simp [h0] at hG
  set c := algebraMap D L G.leadingCoeff with hc_def
  have hc : c ≠ 0 := (map_ne_zero_iff _ hinj).mpr (leadingCoeff_ne_zero.mpr hG0)
  set GK := G.map (algebraMap D L) with hGK_def
  have hGK : GK.natDegree = 2 * k + 2 := by rw [natDegree_map_eq_of_injective hinj, hG]
  have hsplit : GK.Splits := IsAlgClosed.splits GK
  -- Up to the sign `s` and powers of `c`, `discr G` is the product `P` of `G'` over the roots.
  set P := (GK.roots.map GK.derivative.eval).prod
  set s : L := (-1) ^ ((2 * k + 2) * (2 * k + 1) / 2)
  have hres : s * c * algebraMap D L G.discr = c ^ (2 * k + 1) * P := by
    have h := leadingCoeff_pow_mul_prod_roots_eval_derivative
      (natDegree_pos_iff_degree_pos.mp (by omega)) hsplit
    rw [hGK, show 2 * k + 2 - 1 = 2 * k + 1 by omega, leadingCoeff_map_of_injective hinj,
      discr_map_of_natDegree_eq _ (by rw [hGK, hG])] at h
    exact h.symm
  -- Each of the `2k + 2` factors of `P` is `4` times an element made integral by `c ^ (2k + 1)`.
  set Q := (GK.roots.map fun r ↦ c ^ (2 * k + 1) * (GK.derivative.eval r / 4)).prod
  have hPQ : c ^ ((2 * k + 2) * (2 * k + 1)) * P = 2 ^ (4 * (k + 1)) * Q := by
    have hconst (a : L) : (GK.roots.map fun _ ↦ a).prod = a ^ (2 * k + 2) := by
      rw [Multiset.map_const', Multiset.prod_replicate, ← hsplit.natDegree_eq_card_roots, hGK]
    rw [pow_mul', show (2 : L) ^ (4 * (k + 1)) = 4 ^ (2 * k + 2) by
      rw [show (4 : L) = 2 ^ 2 by norm_num, ← pow_mul]; ring, ← hconst, ← hconst,
      ← Multiset.prod_map_mul, ← Multiset.prod_map_mul]
    exact congrArg _ (Multiset.map_congr rfl fun r _ ↦ by field_simp)
  have hQ : IsIntegral D Q := IsIntegral.multiset_prod fun x hx ↦ by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    have hr' : aeval r G = 0 := by rw [← eval_map_algebraMap]; exact isRoot_of_mem_roots hr
    rw [hGK_def, derivative_map, eval_map_algebraMap]
    exact isIntegral_leadingCoeff_pow_mul_aeval_derivative_div_four h2L hf hh hr'
  refine ⟨s * c ^ (2 * k) * Q,
    ((isIntegral_one.neg.pow _).mul (isIntegral_algebraMap.pow _)).mul hQ, ?_⟩
  have hs : s ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [map_mul, map_pow, ← hc_def]
  refine mul_left_cancel₀ hc ?_
  linear_combination (s * c ^ ((2 * k + 2) * (2 * k + 1))) * hres +
    (s * c ^ (2 * k + 1)) * hPQ -
    (c * c ^ ((2 * k + 2) * (2 * k + 1)) * algebraMap D L G.discr) * hs

/-- **The integrality of the discriminant, up to the leading coefficient.** Over an integrally
closed domain in which `2 ≠ 0`, let `G = 4f + h²` with `natDegree f ≤ 2k + 2`,
`natDegree h ≤ k + 1` and `natDegree G = 2k + 2`. Then `2 ^ (4(k + 1))` divides a power of the
leading coefficient of `G` times `discr G`. -/
private theorem two_pow_dvd_leadingCoeff_pow_mul_discr {D : Type*} [CommRing D] [IsDomain D]
    [IsIntegrallyClosed D] (h2 : (2 : D) ≠ 0) {k : ℕ} {f h : D[X]}
    (hf : f.natDegree ≤ 2 * k + 2) (hh : h.natDegree ≤ k + 1)
    (hG : (4 * f + h ^ 2).natDegree = 2 * k + 2) :
    2 ^ (4 * (k + 1)) ∣
      (4 * f + h ^ 2).leadingCoeff ^ ((2 * k + 2) * (2 * k + 1)) * (4 * f + h ^ 2).discr := by
  let L := AlgebraicClosure (FractionRing D)
  have hinj : Function.Injective (algebraMap D L) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) L]
    exact (algebraMap (FractionRing D) L).injective.comp (IsFractionRing.injective D _)
  have : FaithfulSMul D L := (faithfulSMul_iff_algebraMap_injective D L).mpr hinj
  obtain ⟨y, hy, hkey⟩ :=
    exists_isIntegral_algebraMap_leadingCoeff_pow_mul_discr (L := L) hinj h2 hf hh hG
  refine dvd_of_isIntegral_div (L := L) (pow_ne_zero _ h2) ?_
  rwa [hkey, ← map_ofNat (algebraMap D L) 2, ← map_pow,
    mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ h2))]

/-- The leading coefficient of the universal Weierstrass form is not divisible by `2`: modulo `2`
it is the square of a variable. -/
private theorem not_two_dvd_coeff_weierstrassForm_universal (g : ℕ) :
    ¬ 2 ∣ (universal g).weierstrassForm.coeff (2 * g + 2) := by
  rintro ⟨q, hq⟩
  have h := congrArg (MvPolynomial.map (Int.castRingHom (ZMod 2))) hq
  rw [coeff_weierstrassForm_two_mul_add_two, ← Fin.val_last (2 * g + 2), coeff_universal_f,
    ← Fin.val_last (g + 1), coeff_universal_h] at h
  have hC (n : ℕ) [n.AtLeastTwo] (hn : (OfNat.ofNat n : ZMod 2) = 0) :
      (OfNat.ofNat n : MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) (ZMod 2)) = 0 := by
    rw [← map_ofNat MvPolynomial.C, hn, map_zero]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.map_X, hC 4 (by decide),
    hC 2 (by decide), zero_mul, zero_add] at h
  exact pow_ne_zero 2 (MvPolynomial.X_ne_zero _) h

private theorem two_pow_dvd_formDiscr_weierstrassForm_universal (g : ℕ) :
    2 ^ (4 * (g + 1)) ∣ (universal g).weierstrassForm.formDiscr (2 * g + 2) := by
  have hnd := not_two_dvd_coeff_weierstrassForm_universal g
  have hdeg : (universal g).weierstrassForm.natDegree = 2 * g + 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_weierstrassForm_le _)
      fun h0 ↦ hnd (h0 ▸ dvd_zero 2)
  have hprime : Prime (2 : MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) ℤ) := by
    simpa using (MvPolynomial.prime_C_iff _).mpr Int.prime_two
  have hdvd := two_pow_dvd_leadingCoeff_pow_mul_discr two_ne_zero (universal g).natDegree_f_le
    (universal g).natDegree_h_le hdeg
  rw [← weierstrassForm_def, leadingCoeff, hdeg] at hdvd
  rw [formDiscr_of_natDegree_eq hdeg]
  exact hprime.pow_dvd_of_dvd_mul_left _ (fun h ↦ hnd (hprime.dvd_of_dvd_pow h)) hdvd

end Integrality

end Model

/-! ### The discriminant -/

/-- The **universal discriminant** of a genus-`g` model: the integer polynomial in
`f₀, …, f_{2g+2}, h₀, …, h_{g+1}` obtained by dividing every coefficient of
`disc_{2g+2}(4f + h²)` by `2 ^ (4(g + 1))`. The division is exact (`two_pow_mul_universalΔ`),
and `universalΔ g` is the unique polynomial with this property (`eq_universalΔ_iff`). -/
noncomputable def universalΔ (g : ℕ) : MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) ℤ :=
  ∑ μ ∈ ((Model.universal g).weierstrassForm.formDiscr (2 * g + 2)).support,
    MvPolynomial.monomial μ
      (((Model.universal g).weierstrassForm.formDiscr (2 * g + 2)).coeff μ / 2 ^ (4 * (g + 1)))

/-- **The integrality of the discriminant of a hyperelliptic Weierstrass model.** The binary-form
discriminant `disc_{2g+2}(4f + h²)` of the universal model is `2 ^ (4(g + 1))` times the integer
polynomial `universalΔ g`. -/
theorem two_pow_mul_universalΔ (g : ℕ) :
    2 ^ (4 * (g + 1)) * universalΔ g =
      (Model.universal g).weierstrassForm.formDiscr (2 * g + 2) := by
  set D := (Model.universal g).weierstrassForm.formDiscr (2 * g + 2)
  have hdvd : ∀ μ, (2 : ℤ) ^ (4 * (g + 1)) ∣ D.coeff μ := by
    rw [← MvPolynomial.C_dvd_iff_dvd_coeff]
    simpa using Model.two_pow_dvd_formDiscr_weierstrassForm_universal g
  rw [universalΔ, Finset.mul_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff D]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [← map_ofNat MvPolynomial.C 2, ← map_pow, MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hdvd μ)]

/-- `universalΔ g` is the only polynomial whose product with `2 ^ (4(g + 1))` is the binary-form
discriminant of the universal Weierstrass form. -/
theorem eq_universalΔ_iff {P : MvPolynomial (Fin (2 * g + 3) ⊕ Fin (g + 2)) ℤ} :
    P = universalΔ g ↔
      2 ^ (4 * (g + 1)) * P = (Model.universal g).weierstrassForm.formDiscr (2 * g + 2) := by
  rw [← two_pow_mul_universalΔ]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) h⟩

namespace Model

variable {R S : Type*} [CommRing R] [CommRing S] {g : ℕ}

/-- The **discriminant** of a model `y² + h(x) y = f(x)`: the universal discriminant
`universalΔ g` evaluated at the coefficients of `f` and `h`. It satisfies
`2 ^ (4(g + 1)) · Δ = disc_{2g+2}(4f + h²)` (`Model.two_pow_mul_Δ`), which determines it when
`2` is not a zero divisor, and it is defined in every characteristic. -/
noncomputable def Δ (W : Model R g) : R :=
  MvPolynomial.aeval W.coeffs (universalΔ g)

theorem Δ_def (W : Model R g) : W.Δ = MvPolynomial.aeval W.coeffs (universalΔ g) :=
  (rfl)

@[simp]
theorem Δ_universal (g : ℕ) : (universal g).Δ = universalΔ g := by
  rw [Δ_def, coeffs_universal]
  -- `MvPolynomial.aeval_X_left_apply` is stated for the `ℤ`-algebra structure of a polynomial
  -- ring, `Model.Δ` uses the one of an arbitrary ring; the two agree.
  convert MvPolynomial.aeval_X_left_apply (universalΔ g) <;> exact Subsingleton.elim _ _

/-- The discriminant commutes with every ring homomorphism. -/
@[simp]
theorem map_Δ (W : Model R g) (φ : R →+* S) : (W.map φ).Δ = φ W.Δ := by
  rw [Δ_def, Δ_def, map_coeffs]
  exact (MvPolynomial.comp_aeval_apply _ φ.toIntAlgHom _).symm

/-- The discriminant of a model is `2 ^ (-4(g + 1))` times the binary-form discriminant of its
Weierstrass form, in the division-free form valid over every commutative ring. -/
theorem two_pow_mul_Δ (W : Model R g) :
    2 ^ (4 * (g + 1)) * W.Δ = W.weierstrassForm.formDiscr (2 * g + 2) := by
  have h := congrArg (MvPolynomial.aeval W.coeffs) (two_pow_mul_universalΔ g)
  rw [map_mul, map_pow, map_ofNat, ← Δ_def] at h
  rw [h]
  conv_rhs => rw [← W.map_universal]
  rw [map_weierstrassForm, formDiscr_map, RingHom.coe_coe]

/-- **The discriminant of `y² = f(x)`** is `2 ^ (4g)` times the binary-form discriminant of `f` of
degree `2g + 2`. -/
theorem Δ_of_h_eq_zero {W : Model R g} (hW : W.h = 0) :
    W.Δ = 2 ^ (4 * g) * W.f.formDiscr (2 * g + 2) := by
  -- The model `y² = Σ aᵢ xⁱ` over the domain `ℤ[a₀, …, a_{2g+2}]`, where `2` may be cancelled.
  let V : Model (MvPolynomial (Fin (2 * g + 3)) ℤ) g :=
    ⟨universalPoly (2 * g + 2), 0, (natDegree_universalPoly _).le, by simp⟩
  have hV : V.Δ = 2 ^ (4 * g) * V.f.formDiscr (2 * g + 2) := by
    -- The cross term of `V` is the literal `0` in its definition.
    have hV0 : V.h = 0 := rfl
    refine mul_left_cancel₀ (pow_ne_zero (4 * (g + 1)) two_ne_zero) ?_
    rw [two_pow_mul_Δ, weierstrassForm_def, hV0, zero_pow two_ne_zero, add_zero, ← C_ofNat,
      formDiscr_C_mul, ← mul_assoc, ← pow_add,
      show (4 : MvPolynomial (Fin (2 * g + 3)) ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 2
    omega
  have hW' : V.map (MvPolynomial.aeval fun i : Fin (2 * g + 3) ↦ W.f.coeff i).toRingHom = W := by
    ext : 1
    · exact map_universalPoly_of_natDegree_le W.natDegree_f_le
    · simp [V, hW]
  rw [← hW', map_Δ, hV, map_mul, map_pow, map_ofNat, map_f, formDiscr_map]

end Model

/-! ### Examples -/

section Examples

open Model

/-- The genus-one model `y² = x³ - x` has discriminant `64`. -/
example : (⟨X ^ 3 - X, 0, by compute_degree!, by simp⟩ : Model ℤ 1).Δ = 64 := by
  have h3 : (X ^ 3 - X : ℤ[X]).natDegree ≤ 3 := by compute_degree
  have h3' : (X ^ 3 - X : ℤ[X]).degree = 3 := by compute_degree!
  rw [Δ_of_h_eq_zero rfl, formDiscr_succ_eq_coeff_sq_mul_discr (n := 3) (by norm_num) h3,
    discr_of_degree_eq_three h3']
  norm_num [coeff_X, coeff_X_pow]

/-- The genus-one model `y² + y = x³` has discriminant `-27`. -/
private theorem Δ_X_pow_three_one :
    (⟨X ^ 3, 1, by compute_degree!, by simp⟩ : Model ℤ 1).Δ = -27 := by
  have h := two_pow_mul_Δ (⟨X ^ 3, 1, by compute_degree!, by simp⟩ : Model ℤ 1)
  have h3 : (4 * X ^ 3 + 1 ^ 2 : ℤ[X]).natDegree ≤ 3 := by compute_degree
  have h3' : (4 * X ^ 3 + 1 ^ 2 : ℤ[X]).degree = 3 := by compute_degree!
  rw [weierstrassForm_def, formDiscr_succ_eq_coeff_sq_mul_discr (n := 3) (by norm_num) h3,
    discr_of_degree_eq_three h3'] at h
  norm_num [coeff_X, coeff_X_pow, coeff_one] at h
  linarith

/-- Modulo `2` the Weierstrass form of `y² + y = x³` is the constant `1`, whose binary-form
discriminant of degree `4` vanishes, but the discriminant of the model is `1`: the curve has good
reduction at `2`. -/
example : ((⟨X ^ 3, 1, by compute_degree!, by simp⟩ : Model ℤ 1).map
    (Int.castRingHom (ZMod 2))).Δ = 1 := by
  rw [map_Δ, Δ_X_pow_three_one]
  decide

/-- The genus-two model `y² + y = x⁵` has discriminant `3125 = 5⁵`. Its Weierstrass form
`4x⁵ + 1` has degree `5`, so as a binary sextic it has a simple root at infinity. -/
private theorem Δ_X_pow_five_one :
    (⟨X ^ 5, 1, by compute_degree!, by simp⟩ : Model ℤ 2).Δ = 3125 := by
  have h := two_pow_mul_Δ (⟨X ^ 5, 1, by compute_degree!, by simp⟩ : Model ℤ 2)
  have h5 : (4 * X ^ 5 + 1 ^ 2 : ℤ[X]).natDegree = 6 - 1 := by compute_degree!
  -- Reversing the coefficients turns `4x⁵ + 1` into the binomial `x⁵ + 4`.
  have hrev : (4 * X ^ 5 + 1 ^ 2 : ℤ[X]).reverse = X ^ 5 - C (-4) := by
    have h5' : (4 * X ^ 5 + 1 ^ 2 : ℤ[X]).natDegree = 5 := by omega
    rw [reverse, h5']
    ext i
    simp only [coeff_reflect, coeff_add, coeff_sub, coeff_X_pow, coeff_C]
    rcases le_or_gt i 5 with hi | hi
    · rw [revAt_le hi]
      interval_cases i <;> simp [coeff_X_pow, coeff_one]
    · have hi0 : i ≠ 0 := by omega
      rw [revAt_eq_self_of_lt hi]
      simp [coeff_X_pow, coeff_one, hi.ne', hi0]
  rw [weierstrassForm_def, formDiscr_of_natDegree_eq_pred (by norm_num) h5,
    ← discr_reverse _ (by simp), hrev, discr_X_pow_sub_C, leadingCoeff, h5] at h
  norm_num [coeff_X_pow, coeff_one] at h
  linarith

/-- Modulo `2` the Weierstrass form of `y² + y = x⁵` is again the constant `1`, and the discriminant
of the model is `1`: the curve stays smooth modulo `2`. -/
example : ((⟨X ^ 5, 1, by compute_degree!, by simp⟩ : Model ℤ 2).map
    (Int.castRingHom (ZMod 2))).Δ = 1 := by
  rw [map_Δ, Δ_X_pow_five_one]
  decide

end Examples

end TauCeti.HyperellipticCurve
