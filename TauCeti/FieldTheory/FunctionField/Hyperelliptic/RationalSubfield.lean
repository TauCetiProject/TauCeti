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
-- Proof-only: powers of a function lie in the multiples of its pole divisor.
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Principal
-- Proof-only: the span of the powers of a transcendental element has full dimension.
import TauCeti.RingTheory.Algebraic.LinearIndependent

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

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

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
    rwa [hx.finrank_span_range_pow, ← Divisor.dim_def] at h

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
  · rw [hx.finrank_span_range_pow, ← Divisor.dim_def,
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
    rw [Divisor.dim_def, ← (Transcendental.finrank_span_range_pow (K := k) halg 2)]
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
      (Divisor.isEffective_poles hF (Units.mk0 z hz0)).zero_le) hu
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
