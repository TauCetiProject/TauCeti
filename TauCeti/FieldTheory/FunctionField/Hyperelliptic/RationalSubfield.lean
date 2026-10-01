/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Basic
-- Proof-only: the pole divisor of a transcendental element has degree `[F : k(x)]`.
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
-- Proof-only: the constants are the algebraic elements.
import TauCeti.FieldTheory.FunctionField.ConstantField

/-!
# The rational subfield of index two of a hyperelliptic function field

Let `F / k` be a function field with exact constant field `k` and genus `g`, and let `x ∈ F` be
transcendental with `[F : k(x)] = 2`. The divisor `(g - 1) · (x)_∞` has degree `2g - 2` and its
Riemann–Roch space contains `1, x, …, x^{g-1}`, so it is a canonical divisor, and its
Riemann–Roch space is exactly the polynomials in `x` of degree less than `g`. From this follows
Stichtenoth's Proposition 6.2.4(a): every `z ∈ F` with `[F : k(z)] ≤ g` lies in `k(x)`. Indeed,
with `B = (z)_∞` the Riemann–Roch theorem gives `ℓ((g - 1)(x)_∞ - B) ≥ 1`, so some nonzero `u`
has `u · L(B) ⊆ L((g - 1)(x)_∞) ⊆ k(x)`, and `z = (z u) / u`.

In particular, for a hyperelliptic function field, `g ≥ 2`, the rational subfield of index two is
unique: any `z` with `[F : k(z)] = 2` has `k(z) = k(x)`.

## Main results

* `TauCeti.divisorClass_sub_one_zsmul_poles_eq_canonicalClass`: `(g - 1) · (x)_∞` is canonical.
* `TauCeti.mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles`: `L((g - 1) · (x)_∞) ⊆ k(x)`.
* `TauCeti.mem_adjoin_of_finrank_adjoin_le_genus`: **`[F : k(z)] ≤ g` forces `z ∈ k(x)`**.
* `TauCeti.adjoin_eq_adjoin_of_finrank_adjoin_eq_two`: **the rational subfield of index two of a
  hyperelliptic function field is unique**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.2.4.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- An effective divisor is nonnegative. -/
theorem zero_le_of_isEffective {D : Divisor k F} (hD : WeilDivisor.IsEffective D) : 0 ≤ D :=
  WeilDivisor.le_iff.mpr fun P ↦ by
    rw [WeilDivisor.coeff_zero]
    exact (WeilDivisor.isEffective_iff D).mp hD P

/-- Multiples of an effective divisor are monotone in the multiplier. -/
theorem zsmul_le_zsmul_of_isEffective {D : Divisor k F} (hD : WeilDivisor.IsEffective D)
    {m n : ℤ} (h : m ≤ n) : m • D ≤ n • D :=
  WeilDivisor.le_iff.mpr fun P ↦ by
    rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_zsmul]
    exact mul_le_mul_of_nonneg_right h ((WeilDivisor.isEffective_iff D).mp hD P)

/-- A nonzero function lies in the Riemann–Roch space of its pole divisor. -/
theorem mem_riemannRochSpace_poles (hF : IsFunctionField k F) (z : Fˣ) :
    (z : F) ∈ riemannRochSpace (Divisor.poles hF z) := by
  rw [mem_riemannRochSpace_units_iff hF, ← Divisor.zeros_sub_poles, sub_add_cancel]
  exact zero_le_of_isEffective (Divisor.isEffective_zeros hF z)

/-- The `n`-th power of a nonzero function has poles bounded by `n` times its pole divisor. -/
theorem pow_mem_riemannRochSpace_zsmul_poles (hF : IsFunctionField k F) (z : Fˣ) (n : ℕ) :
    (z : F) ^ n ∈ riemannRochSpace ((n : ℤ) • Divisor.poles hF z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_smul, one_smul]
    exact mul_mem_riemannRochSpace_add ih (mem_riemannRochSpace_poles hF z)

/-- The powers `1, z, …, z^{n-1}` of a nonzero function lie in `L((n - 1) · (z)_∞)`; more
generally `z ^ i ∈ L(m · (z)_∞)` whenever `i ≤ m`. -/
theorem pow_mem_riemannRochSpace_zsmul_poles_of_le (hF : IsFunctionField k F) (z : Fˣ) {i : ℕ}
    {m : ℤ} (h : (i : ℤ) ≤ m) : (z : F) ^ i ∈ riemannRochSpace (m • Divisor.poles hF z) :=
  riemannRochSpace_mono (zsmul_le_zsmul_of_isEffective (Divisor.isEffective_poles hF z) h)
    (pow_mem_riemannRochSpace_zsmul_poles hF z i)

/-- The span of the powers `1, z, …, z^{n-1}` of a transcendental `z` has dimension `n`. -/
theorem finrank_span_range_pow {z : F} (hz : Transcendental k z) (n : ℕ) :
    Module.finrank k (Submodule.span k (Set.range fun i : Fin n ↦ z ^ (i : ℕ))) = n :=
  (finrank_span_eq_card (hz.linearIndependent_pow.comp _ Fin.val_injective)).trans
    (Fintype.card_fin n)

/-- **`(g - 1) · (x)_∞` is a canonical divisor** when `[F : k(x)] = 2`: it has degree `2g - 2`,
and its Riemann–Roch space contains the `g` independent functions `1, x, …, x^{g-1}`. -/
theorem divisorClass_sub_one_zsmul_poles_eq_canonicalClass (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) :
    (Place.orderSystem hF).divisorClass
        ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero)) =
      canonicalClass hF hex := by
  refine (divisorClass_eq_canonicalClass_iff hF hex _).mpr ⟨?_, ?_⟩
  · rw [Divisor.degree_zsmul, Divisor.degree_poles hF (Units.mk0 x hx.ne_zero) hx, Units.val_mk0,
      hdeg]
    ring
  · have := finiteDimensional_riemannRochSpace hF
      ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero))
    have hle : Submodule.span k (Set.range fun i : Fin (genus k F) ↦ x ^ (i : ℕ)) ≤
        riemannRochSpace ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero)) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        have := i.isLt
        exact pow_mem_riemannRochSpace_zsmul_poles_of_le hF _ (by omega))
    have h := Submodule.finrank_mono hle
    rwa [finrank_span_range_pow hx, ← Divisor.dim_def] at h

/-- **`L((g - 1) · (x)_∞)` is spanned by `1, x, …, x^{g-1}`** when `[F : k(x)] = 2`: the `g`
powers are independent, and `ℓ((g - 1) · (x)_∞) = g` since the divisor is canonical. -/
theorem riemannRochSpace_sub_one_zsmul_poles_eq_span (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) :
    riemannRochSpace ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero)) =
      Submodule.span k (Set.range fun i : Fin (genus k F) ↦ x ^ (i : ℕ)) := by
  have := finiteDimensional_riemannRochSpace hF
    ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero))
  refine (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_).symm
  · rintro _ ⟨i, rfl⟩
    have := i.isLt
    exact pow_mem_riemannRochSpace_zsmul_poles_of_le hF _ (by omega)
  · rw [finrank_span_range_pow hx, ← Divisor.dim_def,
      (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hF hex
        (divisorClass_sub_one_zsmul_poles_eq_canonicalClass hF hex hx hdeg)).dim_eq hF hex]

/-- **`L((g - 1) · (x)_∞) ⊆ k(x)`** when `[F : k(x)] = 2`. -/
theorem mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) {f : F}
    (hf : f ∈ riemannRochSpace ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero))) :
    f ∈ k⟮x⟯ := by
  rw [riemannRochSpace_sub_one_zsmul_poles_eq_span hF hex hx hdeg] at hf
  refine (Submodule.span_le (p := Subalgebra.toSubmodule k⟮x⟯.toSubalgebra)).mpr ?_ hf
  rintro _ ⟨i, rfl⟩
  exact pow_mem (IntermediateField.mem_adjoin_simple_self k x) _

/-- **Stichtenoth, Proposition 6.2.4(a)**: if `[F : k(x)] = 2` and `z ∈ F` has `[F : k(z)] ≤ g`,
then `z ∈ k(x)`. For a constant `z` this is exactness of `k`; otherwise, with `B = (z)_∞`, the
Riemann–Roch theorem at `B` with the canonical divisor `(g - 1) · (x)_∞` gives a nonzero `u` with
`u · L(B) ⊆ L((g - 1) · (x)_∞) ⊆ k(x)`, and `z = (z u) / u`. -/
theorem mem_adjoin_of_finrank_adjoin_le_genus (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) {z : F} (hz : Module.finrank k⟮z⟯ F ≤ genus k F) :
    z ∈ k⟮x⟯ := by
  by_cases halg : IsAlgebraic k z
  · obtain ⟨c, rfl⟩ := (hF.isAlgebraic_iff_mem_range_algebraMap hF hex).mp halg
    exact IntermediateField.algebraMap_mem _ c
  have hz0 : z ≠ 0 := fun h ↦ halg (h ▸ isAlgebraic_zero)
  -- `ℓ((z)_∞) ≥ 2`, from the independent functions `1` and `z`
  have hdimB : 2 ≤ Divisor.dim (Divisor.poles hF (Units.mk0 z hz0)) := by
    have := finiteDimensional_riemannRochSpace hF (Divisor.poles hF (Units.mk0 z hz0))
    rw [Divisor.dim_def, ← finrank_span_range_pow (k := k) halg 2]
    refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    simpa using pow_mem_riemannRochSpace_zsmul_poles_of_le hF (Units.mk0 z hz0)
      (m := 1) (by omega)
  -- Riemann–Roch at `(z)_∞` with the canonical divisor `(g - 1) · (x)_∞`: `ℓ(W - B) ≥ 1`
  have hRR := Divisor.isRiemannRochDivisor_iff.mp
    (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hF hex
      (divisorClass_sub_one_zsmul_poles_eq_canonicalClass hF hex hx hdeg))
    (Divisor.poles hF (Units.mk0 z hz0))
  have hdegB : Divisor.degree (Divisor.poles hF (Units.mk0 z hz0)) = Module.finrank k⟮z⟯ F :=
    Divisor.degree_poles hF (Units.mk0 z hz0) halg
  have hne : riemannRochSpace ((genus k F - 1 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero) -
      Divisor.poles hF (Units.mk0 z hz0)) ≠ ⊥ :=
    (Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF _).mp (by omega)
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hne
  -- `z u` and `u` lie in `L((g - 1) · (x)_∞) ⊆ k(x)`
  have hzu : z * u ∈ k⟮x⟯ := by
    have h := mul_mem_riemannRochSpace_add (mem_riemannRochSpace_poles hF (Units.mk0 z hz0)) hu
    rw [Units.val_mk0, add_sub_cancel] at h
    exact mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles hF hex hx hdeg h
  have hu' : u ∈ k⟮x⟯ := by
    have h := mul_mem_riemannRochSpace_add (one_mem_riemannRochSpace_iff.mpr
      (zero_le_of_isEffective (Divisor.isEffective_poles hF (Units.mk0 z hz0)))) hu
    rw [one_mul, add_sub_cancel] at h
    exact mem_adjoin_of_mem_riemannRochSpace_sub_one_zsmul_poles hF hex hx hdeg h
  have : z = z * u / u := by field_simp
  rw [this]
  exact div_mem hzu hu'

/-- **The rational subfield of index two of a hyperelliptic function field is unique**
(Stichtenoth, Proposition 6.2.4): if `g ≥ 2` and `x, z ∈ F` are transcendental with
`[F : k(x)] = [F : k(z)] = 2`, then `k(z) = k(x)`. -/
theorem adjoin_eq_adjoin_of_finrank_adjoin_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F) {x z : F} (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) (hdegz : Module.finrank k⟮z⟯ F = 2) : k⟮z⟯ = k⟮x⟯ := by
  have : FiniteDimensional k⟮z⟯ F := Module.finite_of_finrank_pos (by omega)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_ (by rw [hdeg, hdegz])
  exact IntermediateField.adjoin_simple_le_iff.mpr
    (mem_adjoin_of_finrank_adjoin_le_genus hF hex hx hdeg (by omega))

end TauCeti
