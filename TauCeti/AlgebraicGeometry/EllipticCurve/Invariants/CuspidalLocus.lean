/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.RingTheory.Ideal.Height

/-!
# The cuspidal locus of the universal Weierstrass equation

A Weierstrass equation over a field is smooth or nodal exactly when `c₄` and `Δ` do not both
vanish: the excluded locus `V(c₄, Δ)` of `Spec ℤ[a₁, a₂, a₃, a₄, a₆]` is the cuspidal locus. Its
complement `D(c₄) ∪ D(Δ)` is the open subscheme of the Weierstrass atlas whose quotient by the
coordinate-change group is the compactified moduli stack of stable one-pointed genus-one curves,
while `D(Δ)` alone gives the smooth locus.

This file shows that the cuspidal locus has codimension two in the atlas, whereas the
discriminant divisor `V(Δ)` has codimension one. The key input is that `c₄` is irreducible: it
is linear in `a₄`, with coefficient `-48`, and the remaining part
`(a₁² + 4a₂)² - 24a₁a₃` is not divisible by `2` or `3`. Since `y² = x³ + 1` has `c₄ = 0` and
`Δ = -432`, the invariant `c₄` does not divide `Δ`, so `c₄` and `Δ` are relatively prime in the
unique factorization domain `ℤ[a₁, a₂, a₃, a₄, a₆]`.

Relative primality is also the depth-two extension property of the cuspidal locus: a function
on `D(c₄)`, written `a / c₄ᵐ`, and a function on `D(Δ)`, written `b / Δⁿ`, which agree on the
overlap come from a polynomial in the Weierstrass coefficients. So a regular function on
the compactified locus `D(c₄) ∪ D(Δ)` extends over the whole atlas. Every change of variables
multiplies `c₄` and `Δ` by units, so the ideal `(c₄, Δ)` and hence the cuspidal locus are
stable under the coordinate-change group (`WeierstrassCurve.span_variableChange_c₄_Δ`, proved
over any commutative ring in `TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic`).

## Main results

* `WeierstrassCurve.Universal.irreducible_c₄`: the invariant `c₄` of the universal Weierstrass
  curve is irreducible.
* `WeierstrassCurve.Universal.isRelPrime_c₄_Δ`: `c₄` and `Δ` are relatively prime.
* `WeierstrassCurve.Universal.height_span_c₄_Δ`: the cuspidal locus `V(c₄, Δ)` has codimension
  two.
* `WeierstrassCurve.Universal.height_span_Δ`: the discriminant divisor `V(Δ)` has codimension
  one.
* `WeierstrassCurve.Universal.exists_eq_c₄_pow_mul_and_eq_Δ_pow_mul`: functions on `D(c₄)` and
  on `D(Δ)` which agree on the overlap extend over the whole atlas.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3.
* P. Goerss, *Topological modular forms [after Hopkins, Miller, and Lurie]*, Séminaire Bourbaki
  1005 (2009), §3.1.
-/

public section

noncomputable section

namespace WeierstrassCurve

namespace Universal

open MvPolynomial

/-- The part `(a₁² + 4a₂)² - 24a₁a₃` of `c₄` not involving `a₄`, as a polynomial in the other
coefficients. -/
private def c₄Rest : MvPolynomial {i : Coeff // i ≠ .A₄} ℤ :=
  (X ⟨.A₁, nofun⟩ ^ 2 + 4 * X ⟨.A₂, nofun⟩) ^ 2 -
    24 * X ⟨.A₁, nofun⟩ * X ⟨.A₃, nofun⟩

private lemma c₄_eq : curve.c₄ = C (-48) * X .A₄ + rename Subtype.val c₄Rest := by
  simp only [c₄Rest, c₄, b₂, b₄, curve_a₁, curve_a₂, curve_a₃, curve_a₄, map_sub, map_add,
    map_mul, map_pow, map_ofNat, rename_X, map_neg]
  ring

/-- The part of `c₄` not involving `a₄` is divisible by no prime number. -/
private lemma isRelPrime_C_c₄Rest {p : ℤ} (hp : Prime p) :
    IsRelPrime (C p) (rename Subtype.val c₄Rest) := by
  refine (((prime_C_iff _).mpr hp).irreducible.isRelPrime_iff_not_dvd).mpr fun h ↦ ?_
  -- At `a₁ = 1` and `a₂ = a₃ = a₄ = a₆ = 0` this part takes the value `1`.
  have : p ∣ 1 := by
    simpa [c₄Rest] using map_dvd (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve ℤ).specialize h
  exact hp.not_isUnit (isUnit_of_dvd_one this)

/-- The invariant `c₄` of the universal Weierstrass curve is irreducible in
`ℤ[a₁, a₂, a₃, a₄, a₆]`. -/
theorem irreducible_c₄ : Irreducible curve.c₄ := by
  classical
  rw [c₄_eq]
  refine irreducible_mul_X_add _ _ _ (by simp) (by rw [vars_C]; simp) (fun h ↦ ?_) ?_
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (vars_rename _ _ h)
    exact i.2 hi
  · -- The coefficient `-48 = -3 · 2⁴` of `a₄` is coprime to the rest of `c₄`.
    have h48 : (C (-48) : MvPolynomial Coeff ℤ) = -(C 3 * C 2 ^ 4) := by
      simp only [← map_pow, ← map_mul, ← map_neg]
      norm_num
    rw [h48]
    exact ((isRelPrime_C_c₄Rest Int.prime_three).mul_left
      (isRelPrime_C_c₄Rest Int.prime_two).pow_left).neg_left

/-- The invariants `c₄` and `Δ` of the universal Weierstrass curve are relatively prime. -/
theorem isRelPrime_c₄_Δ : IsRelPrime curve.c₄ curve.Δ := by
  refine irreducible_c₄.isRelPrime_iff_not_dvd.mpr fun h ↦ ?_
  -- The curve `y² = x³ + 1` has `c₄ = 0` and `Δ = -432`.
  have := map_dvd (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).specialize h
  rw [specialize_c₄, specialize_Δ] at this
  norm_num [c₄, Δ, b₂, b₄, b₆, b₈] at this

/-- The ideal `(c₄, Δ)` is proper: the cuspidal cubic `y² = x³` lies in the cuspidal locus. -/
private lemma span_c₄_Δ_ne_top : Ideal.span {curve.c₄, curve.Δ} ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (RingHom.ker_ne_top (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℤ).specialize) ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl) <;> simp [c₄, Δ, b₂, b₄, b₆, b₈]

/-- The cuspidal locus `V(c₄, Δ)` of the universal Weierstrass curve has codimension two in
`Spec ℤ[a₁, a₂, a₃, a₄, a₆]`. -/
theorem height_span_c₄_Δ : (Ideal.span {curve.c₄, curve.Δ}).height = 2 :=
  Ideal.height_span_pair_eq_two_of_isRelPrime isRelPrime_c₄_Δ span_c₄_Δ_ne_top

/-- The discriminant divisor `V(Δ)` of the universal Weierstrass curve has codimension one in
`Spec ℤ[a₁, a₂, a₃, a₄, a₆]`. -/
theorem height_span_Δ : (Ideal.span {curve.Δ}).height = 1 := by
  refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero curve_Δ_ne_zero) fun h ↦ ?_
  -- The cuspidal cubic `y² = x³` has `Δ = 0`.
  have := h.map (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℤ).specialize
  rw [specialize_Δ] at this
  simp [Δ, b₂, b₄, b₆, b₈] at this

/-- **Extension across the cuspidal locus.** If a function `a / c₄ᵐ` on `D(c₄)` and a function
`b / Δⁿ` on `D(Δ)` agree on the overlap, that is `Δⁿ a = c₄ᵐ b`, then both are restrictions of a
single polynomial `c` in the Weierstrass coefficients. Thus regular functions on the compactified
locus `D(c₄) ∪ D(Δ)` extend over the whole Weierstrass atlas. -/
theorem exists_eq_c₄_pow_mul_and_eq_Δ_pow_mul {m n : ℕ} {a b : MvPolynomial Coeff ℤ}
    (h : curve.Δ ^ n * a = curve.c₄ ^ m * b) :
    ∃ c, a = curve.c₄ ^ m * c ∧ b = curve.Δ ^ n * c := by
  obtain ⟨c, rfl⟩ := isRelPrime_c₄_Δ.pow.dvd_of_dvd_mul_left ⟨b, h⟩
  refine ⟨c, rfl, mul_left_cancel₀ (pow_ne_zero m irreducible_c₄.ne_zero) ?_⟩
  rw [← h]
  ring

end Universal

end WeierstrassCurve
