/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.RationalSubfield
-- Proof-only: ramification indices and different exponents of `y ^ 2 = f`.
import TauCeti.FieldTheory.FunctionField.Different.Radical
-- Proof-only: the order of `X` at the finite places of `k(x)`.
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# The regular differentials of a function field with a rational subfield of index two

Let `F / k` be a function field with exact constant field `k` and genus `g`, and let `x ∈ F` be
transcendental with `[F : k(x)] = 2`. The divisor `(g - 1) · (x)_∞` is canonical
(`TauCeti.divisorClass_sub_one_zsmul_poles_eq_canonicalClass`), so it is the divisor of a Weil
differential `ω₀`. By the duality theorem the regular differentials `Ω_F(0)` are the multiples
`z · ω₀` with `z ∈ L((g - 1) · (x)_∞)`, and that space is spanned by `1, x, …, x^{g-1}`. Hence
`ω₀, x ω₀, …, x^{g-1} ω₀` is a `k`-basis of `Ω_F(0)`, and the quotient of two regular
differentials always lies in `k(x)`. For `g ≥ 2` the quotient of `x ω₀` by `ω₀` is `x` itself, so
these quotients generate `k(x)`: the regular differentials single out the rational subfield of
index two.

For the model `y ^ 2 = f(x)` with `f` squarefree of degree `m ≥ 1`, away from characteristic two,
the differential `ω₀` is explicit: `dx / y` has divisor `(g - 1) · (x)_∞`. Indeed
`(dx) = -2 (x)_∞ + Diff(F / k(x))`, and at a place `Q` above a place `P` of `k(x)` with
ramification index `e` the three terms contribute as follows.

* Above a zero of `f`: `e = 2`, the different exponent is `1` and `ord_Q y = 1`.
* Above any other finite place: `e = 1` and both the different exponent and `ord_Q y` vanish.
* Above infinity, for `m` odd: `e = 2`, the different exponent is `1`, `ord_Q y = -m` and
  `ord_Q x = -2`, so the coefficient is `m - 3 = 2 (g - 1)`.
* Above infinity, for `m` even: `e = 1`, the different exponent is `0`, `ord_Q y = -m / 2` and
  `ord_Q x = -1`, so the coefficient is `m / 2 - 2 = g - 1`.

So the regular differentials of `y ^ 2 = f(x)` are exactly `p(x) dx / y` with `deg p < g`.

## Main results

* `TauCeti.weilDifferentialFiltration_zero_eq_span_pow`: if `(ω₀) = (g - 1) · (x)_∞`, then
  `Ω_F(0)` is spanned by `x ^ i · ω₀` for `i < g`; these are linearly independent by
  `TauCeti.linearIndependent_repartitionDualMul_pow`.
* `TauCeti.mem_adjoin_of_repartitionDualMul_eq`: the quotient of two regular differentials lies
  in `k(x)`.
* `TauCeti.adjoin_setOf_repartitionDualMul_eq_adjoin`: for `g ≥ 2`, these quotients generate
  `k(x)`.
* `TauCeti.weilDifferentialDivisor_repartitionDualMul_inv_weilDifferentialCotrace_of_sq_eq`:
  for `y ^ 2 = f(x)`, the differential `dx / y` has divisor `(g - 1) · (x)_∞`.
* `TauCeti.weilDifferentialFiltration_zero_eq_span_of_sq_eq`: the regular differentials of
  `y ^ 2 = f(x)` are spanned by `x ^ i dx / y` for `i < g`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section VI.2.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### A rational subfield of index two -/

section IndexTwo

variable {x : F}

/-- **The regular differentials over a rational subfield of index two**: if `[F : k(x)] = 2` and
the Weil differential `ω` has divisor `(g - 1) · (x)_∞`, then the regular differentials are
spanned by `ω, x ω, …, x^{g-1} ω`. These are linearly independent
(`TauCeti.linearIndependent_repartitionDualMul_pow`), so they form a basis of `Ω_F(0)`. -/
theorem weilDifferentialFiltration_zero_eq_span_pow (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D}
      ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero))) :
    weilDifferentialFiltration (0 : Divisor k F) =
      Submodule.span k
        (Set.range fun i : Fin (genus k F) ↦ repartitionDualMul hF (x ^ (i : ℕ)) ω) := by
  rw [← map_riemannRochSpace_repartitionDualMulRight hF hex hω hW, sub_zero,
    riemannRochSpace_sub_one_zsmul_poles_eq_span hF hex hx hdeg, Submodule.map_span,
    ← Set.range_comp]
  simp only [Function.comp_def, repartitionDualMulRight_apply]

/-- **Quotients of regular differentials lie in the rational subfield of index two**: if
`[F : k(x)] = 2` and `z · η = ω` for regular Weil differentials `ω` and `η ≠ 0`, then `z ∈ k(x)`.
-/
theorem mem_adjoin_of_repartitionDualMul_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) {ω η : Module.Dual k ↥(repartitionSpace k F)}
    (hωmem : ω ∈ weilDifferentialFiltration (0 : Divisor k F))
    (hηmem : η ∈ weilDifferentialFiltration (0 : Divisor k F)) (hη : η ≠ 0) {z : F}
    (hz : repartitionDualMul hF z η = ω) : z ∈ k⟮x⟯ := by
  -- Write `ω = a · ω₀` and `η = b · ω₀` for a differential `ω₀` with divisor `(g - 1) (x)_∞`;
  -- then `a, b ∈ L((g - 1) (x)_∞) ⊆ k(x)`, `b ≠ 0`, and `z b = a`.
  obtain ⟨ω₀, -, hω₀, hW⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hF hex
    (divisorClass_sub_one_zsmul_poles_eq_canonicalClass hF hex hx hdeg)
  have hmap := map_riemannRochSpace_repartitionDualMulRight hF hex hω₀ hW 0
  rw [sub_zero] at hmap
  obtain ⟨a, ha, rfl⟩ := hmap ▸ hωmem
  obtain ⟨b, hb, rfl⟩ := hmap ▸ hηmem
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hη (map_zero _)
  have hzb : z * b = a := repartitionDualMulRight_injective hF hω₀ (by
    simpa only [repartitionDualMulRight_apply, repartitionDualMul_repartitionDualMul] using hz)
  rw [← mul_div_cancel_right₀ z hb0, hzb]
  exact div_mem (mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles hF hex hx hdeg ha)
    (mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles hF hex hx hdeg hb)

/-- **Quotients of regular differentials generate the rational subfield of index two**: if
`[F : k(x)] = 2` and `g ≥ 2`, then the quotients `z` of regular Weil differentials, `z · η = ω` with
`η ≠ 0`, generate `k(x)`. Each such quotient lies in `k(x)`
(`TauCeti.mem_adjoin_of_repartitionDualMul_eq`), and `x` is the quotient of `x ω₀` by `ω₀`. -/
theorem adjoin_setOf_repartitionDualMul_eq_adjoin (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) (hg : 2 ≤ genus k F) :
    IntermediateField.adjoin k {z : F | ∃ ω ∈ weilDifferentialFiltration (0 : Divisor k F),
      ∃ η ∈ weilDifferentialFiltration (0 : Divisor k F), η ≠ 0 ∧
        repartitionDualMul hF z η = ω} = k⟮x⟯ := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) ?_
  · rintro z ⟨ω, hωmem, η, hηmem, hη, hz⟩
    exact mem_adjoin_of_repartitionDualMul_eq hF hex hx hdeg hωmem hηmem hη hz
  · -- `x` is the quotient of `x ω₀` by `ω₀`, both regular since `1, x` lie among `1, …, x^{g-1}`.
    obtain ⟨ω₀, -, hω₀, hW⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hF hex
      (divisorClass_sub_one_zsmul_poles_eq_canonicalClass hF hex hx hdeg)
    have hspan := weilDifferentialFiltration_zero_eq_span_pow hF hex hx hdeg hω₀ hW
    have hmem (i : ℕ) (hi : i < genus k F) :
        repartitionDualMul hF (x ^ i) ω₀ ∈ weilDifferentialFiltration (0 : Divisor k F) :=
      hspan ▸ Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    refine IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ ?_)
    refine ⟨_, hmem 1 (by omega), ω₀, ?_, hω₀, by rw [pow_one]⟩
    simpa only [pow_zero, map_one, Module.End.one_apply] using hmem 0 (by omega)

end IndexTwo

/-! ### The model `y ^ 2 = f(x)` -/

section SqEq

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- **The divisor of `dx / y`**: away from characteristic two, if `F = k(x, y)` with
`y ^ 2 = f(x)` for a squarefree polynomial `f` of degree `m ≥ 1`, then the Weil differential
`dx / y` has divisor `(g - 1) · (x)_∞`, where `g = ⌊(m - 1) / 2⌋` is the genus of `F` and `dx` is
the cotrace of the normalized differential of `k(x)`. -/
theorem weilDifferentialDivisor_repartitionDualMul_inv_weilDifferentialCotrace_of_sq_eq
    (h2 : (2 : k) ≠ 0) {f : k[X]} (hf : Squarefree f) (hdeg : 0 < f.natDegree) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) :
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy).1
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy).2
    letI hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
    weilDifferentialDivisor hF (isIntegrallyClosedIn_of_sq_eq h2 hf hdeg hgen hy)
        (repartitionDualMul_mem_weilDifferentialSpace hF ((y⁻¹ : Fˣ) : F)
          (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
            ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩).2)
        (repartitionDualMul_ne_zero hF (Units.ne_zero _)
          (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF)) =
      (genus k F - 1 : ℤ) • Divisor.poles hF (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
        (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) := by
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  have hex := isIntegrallyClosedIn_of_sq_eq h2 hf hdeg hgen hy
  rw [weilDifferentialDivisor_repartitionDualMul hF hex
      (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩).2
      (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF),
    weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential,
    genus_eq_of_sq_eq h2 hf hdeg hgen hy]
  refine WeilDivisor.ext fun Q ↦ ?_
  simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, Divisor.coeff_principal,
    Divisor.coeff_poles, Divisor.coeff_different, Units.val_inv_eq_inv_val, Place.ord_inv,
    Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0]
  -- the orders of `y` and `x` at `Q` in terms of those of `f` and `X` at the place below
  have hord := congrArg Q.ord hy
  rw [Q.ord_pow, Place.ord_algebraMap_restrict k (RatFunc k)] at hord
  have hx := Place.ord_algebraMap_restrict k (RatFunc k) Q RatFunc.X
  have he := Place.ramificationIdx_eq_of_pow_eq_of_prime k (RatFunc k) (P' := Q)
    Nat.prime_two hgen hy (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)
  have hd := Place.differentExponent_eq_of_pow_eq_of_prime k (RatFunc k) (P' := Q)
    Nat.prime_two hgen hy (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)
  -- Case on the place below `Q`, and then on the parities deciding `e` and the different
  -- exponent: in each case every term is an explicit multiple of `ord_Q y` or of `deg f`.
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with
    hQ | ⟨q, hq, hQ⟩
  · rw [hQ, Place.ord_infty, RatFunc.intDegree_polynomial] at hord he hd
    rw [hQ, Place.ord_infty, RatFunc.intDegree_X] at hx
    split_ifs at he hd with h <;> rw [he] at hord hx <;> rw [hd, hx] <;> norm_num at hord ⊢ <;>
      omega
  · rw [hQ, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf] at hord he hd
    rw [hQ, Place.ord_adicOfIrreducible_X] at hx
    split_ifs at he hd hx hord <;> rw [he] at hord hx <;> rw [hd, hx] <;>
      norm_num at hord ⊢ <;> omega

/-- **The regular differentials of `y ^ 2 = f(x)`**: away from characteristic two, if
`F = k(x, y)` with `y ^ 2 = f(x)` for a squarefree polynomial `f` of degree `m ≥ 1`, then the
regular Weil differentials of `F` are spanned by `x ^ i dx / y` for `i < g`, where
`g = ⌊(m - 1) / 2⌋` is the genus of `F` and `dx` is the cotrace of the normalized differential of
`k(x)`. They are linearly independent (`TauCeti.linearIndependent_repartitionDualMul_pow`
applied to `dx / y`), so they form a basis of `Ω_F(0)`. -/
theorem weilDifferentialFiltration_zero_eq_span_of_sq_eq (h2 : (2 : k) ≠ 0) {f : k[X]}
    (hf : Squarefree f) (hdeg : 0 < f.natDegree) {y : Fˣ} (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) :
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy).1
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy).2
    letI hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
    weilDifferentialFiltration (0 : Divisor k F) =
      Submodule.span k (Set.range fun i : Fin (genus k F) ↦
        repartitionDualMul hF (algebraMap (RatFunc k) F RatFunc.X ^ (i : ℕ) / y)
          (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
            ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩)) := by
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  have hex := isIntegrallyClosedIn_of_sq_eq h2 hf hdeg hgen hy
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) := (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hrank : Module.finrank k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F = 2 := by
    rw [finrank_adjoin_algebraMap_X, finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy]
  have hW := isGreatest_weilDifferentialDivisor hF hex
    (repartitionDualMul_mem_weilDifferentialSpace hF ((y⁻¹ : Fˣ) : F)
      (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩).2)
    (repartitionDualMul_ne_zero hF (Units.ne_zero _)
      (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF))
  rw [weilDifferentialDivisor_repartitionDualMul_inv_weilDifferentialCotrace_of_sq_eq h2 hf hdeg
    hgen hy] at hW
  have hX : Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = Units.mk0 _ hx.ne_zero := Units.ext rfl
  rw [hX] at hW
  rw [weilDifferentialFiltration_zero_eq_span_pow hF hex hx hrank
    (repartitionDualMul_ne_zero hF (Units.ne_zero _)
      (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF)) hW]
  simp_rw [repartitionDualMul_repartitionDualMul, Units.val_inv_eq_inv_val, div_eq_mul_inv]

end SqEq

end TauCeti
