/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.RamanujanFormula
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.NumberTheory.ModularForms.EllipticPoints

/-!
# The level-one modular invariant

The classical modular invariant is the quotient `E₄³ / Δ`.  The denominator has no zeros in
the upper half-plane, so the quotient is holomorphic there.  Its weight is zero: the weight
factors of its numerator and denominator cancel under the modular group.  The identity
`j - 1728 = E₆² / Δ` identifies the fibres above `0` and `1728` with the zero loci of
`E₄` and `E₆`, respectively.

At the two elliptic points `ρ = e^{2πi/3}` and `i` the orders are exact: `E₄` vanishes at `ρ`
and `E₆` at `i`, both to order one, so `j` vanishes to order `3` at `ρ` and `j - 1728` to order
`2` at `i`.  These are the ramification data of `j` over the elliptic points.  Orders are read
in the coordinate of `ℂ`, as the analytic order of the composite with `ofComplex`.

## Implementation notes

The vanishing comes from the stabilizers: `S` fixes `i` and `S * T` fixes `ρ`, with automorphy
factors `iᵏ` and `(ρ + 1)ᵏ` in weight `k`, so a form invariant under `S` vanishes at `i` unless
`4 ∣ k`, and one invariant under `S * T` vanishes at `ρ` unless `6 ∣ k`
(`TauCeti.NumberTheory.ModularForms.EllipticPoints`); in particular `E₆` vanishes at `i` and
`E₄` at `ρ`.  That the zeros are simple comes from Ramanujan's formulas
`D E₄ = (E₂ E₄ - E₆) / 3` and `D E₆ = (E₂ E₆ - E₄²) / 2`
(Mathlib's `Derivative.normalizedDerivOfComplex_E₄` and `Derivative.normalizedDerivOfComplex_E₆`):
at a zero of `E₄` the derivative is `-E₆ / 3`, and at a zero of `E₆` it is `-E₄² / 2`, neither
of which vanishes because `Δ = (E₄³ - E₆²) / 1728` has no zeros.

## Main results

* `TauCeti.ModularForm.j`, `TauCeti.ModularForm.j_smul`, `TauCeti.ModularForm.j_sub_1728`: the
  invariant, its modular invariance, and the identity `j - 1728 = E₆² / Δ`.
* `TauCeti.ModularForm.E₄_ρ`, `TauCeti.ModularForm.E₆_I`: the elliptic zeros of `E₄` and `E₆`.
* `TauCeti.ModularForm.j_ρ`, `TauCeti.ModularForm.j_I`: `j ρ = 0` and `j i = 1728`.
* `TauCeti.ModularForm.analyticOrderAt_j_comp_ofComplex_ρ`: `j` vanishes to order `3` at `ρ`.
* `TauCeti.ModularForm.analyticOrderAt_j_sub_1728_comp_ofComplex_I`: `j - 1728` vanishes to
  order `2` at `i`.

## References

* J.-P. Serre, *A Course in Arithmetic*, VII.3 — the normalization of `j` and the discriminant
  identity; the orders of `E₄`, `E₆` and `j` at the elliptic points.
* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  §5.2 — Ramanujan's differential equations for `E₂`, `E₄`, `E₆`.
-/

public noncomputable section

open UpperHalfPlane MatrixGroups ModularForm Matrix.SpecialLinearGroup
open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

/-- The normalized modular invariant `j = E₄³ / Δ` on the upper half-plane. -/
def j (z : ℍ) : ℂ := E₄ z ^ 3 / discriminant z

-- A simp attribute here would make the `j_smul` and fibre simp lemmas fail `simpNF`.
theorem j_apply (z : ℍ) : j z = E₄ z ^ 3 / discriminant z := by rfl

/-- The modular invariant is holomorphic on the upper half-plane. -/
theorem j_mdifferentiable : MDiff j := by
  exact (ModularForm.holo' E₄).pow 3 |>.div (CuspForm.discriminant.holo') discriminant_ne_zero

-- A direct-action `@[simp]` variant fails `simpNF`:
-- `ModularGroup.sl_moeb` simplifies its left side.
/-- The weight factors cancel, so `j` is invariant under `SL₂(ℤ)`. -/
@[simp]
theorem j_smul (γ : SL(2, ℤ)) (z : ℍ) :
    j ((map (Int.castRingHom ℝ) γ) • z) = j z := by
  have hγ : mapGL ℝ γ ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨γ, rfl⟩
  have hE : (⇑(E₄.pow 3) ∣[(12 : ℤ)] (mapGL ℝ γ)) = ⇑(E₄.pow 3) := by
    simpa using SlashInvariantForm.slash_action_eqn (E₄.pow 3) _ hγ
  have hΔ : (⇑CuspForm.discriminant ∣[(12 : ℤ)] (mapGL ℝ γ)) =
      ⇑CuspForm.discriminant := by
    simpa using SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ hγ
  have h : (⇑(E₄.pow 3) / ⇑CuspForm.discriminant) ∣[(12 : ℤ) - 12] γ =
      ⇑(E₄.pow 3) / ⇑CuspForm.discriminant := by
    rw [div_slash_SL2]
    -- The `SL₂` slash action uses `mapGL ℝ γ` definitionally, as in `hE` and `hΔ`.
    change (⇑(E₄.pow 3) ∣[(12 : ℤ)] (mapGL ℝ γ)) /
      (⇑CuspForm.discriminant ∣[(12 : ℤ)] (mapGL ℝ γ)) = _
    rw [hE, hΔ]
  have hpow (w : ℍ) : (E₄.pow 3) w = E₄ w ^ 3 := by
    exact congrFun (ModularForm.coe_pow E₄ 3) w
  have hz := congrFun h z
  have hinv : j (γ • z) = j z := by
    simpa [SL_slash_apply, j, hpow] using hz
  have hAction : (map (Int.castRingHom ℝ) γ) • z = γ • z := by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    have hMap : mapGL ℝ (map (Int.castRingHom ℝ) γ) = mapGL ℝ γ := by
      ext i j
      simp [mapGL_coe_matrix]
    exact congrArg (· • z) hMap
  rw [hAction]
  exact hinv

/-- The identity `j - 1728 = E₆² / Δ`. -/
theorem j_sub_1728 (z : ℍ) : j z - 1728 = E₆ z ^ 2 / discriminant z := by
  have hΔ : (1728 : ℂ) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [j_apply]
  field_simp [discriminant_ne_zero z]
  linear_combination -hΔ

/-- The zero fibre of `j` is exactly the zero locus of `E₄`. -/
@[simp]
theorem j_eq_zero_iff (z : ℍ) : j z = 0 ↔ E₄ z = 0 := by
  simp [j_apply, discriminant_ne_zero z]

/-- The fibre of `j` above `1728` is exactly the zero locus of `E₆`. -/
@[simp]
theorem j_eq_1728_iff (z : ℍ) : j z = 1728 ↔ E₆ z = 0 := by
  rw [← sub_eq_zero, j_sub_1728]
  simp [discriminant_ne_zero z]

/-! ### The elliptic points -/

open ModularGroup

/-- `E₄` vanishes at `ρ`. -/
@[simp]
theorem E₄_ρ : E₄ ρ = 0 :=
  apply_ρ_eq_zero_of_not_dvd (Γ := 𝒮ℒ) ⟨S * T, rfl⟩ E₄ (by decide)

/-- `E₆` vanishes at `i`. -/
@[simp]
theorem E₆_I : E₆ I = 0 :=
  apply_I_eq_zero_of_not_dvd (Γ := 𝒮ℒ) ⟨S, rfl⟩ E₆ (by decide)

/-- `E₆` does not vanish at `ρ`. -/
theorem E₆_ρ_ne_zero : E₆ ρ ≠ 0 := by
  intro h
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq ρ
  simp [E₄_ρ, h, discriminant_ne_zero] at hΔ

/-- `E₄` does not vanish at `i`. -/
theorem E₄_I_ne_zero : E₄ I ≠ 0 := by
  intro h
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq I
  simp [E₆_I, h, discriminant_ne_zero] at hΔ

/-- The value `j ρ = 0`. -/
@[simp]
theorem j_ρ : j ρ = 0 := by
  simp

/-- The value `j i = 1728`. -/
@[simp]
theorem j_I : j I = 1728 := by
  simp

/-- `E₄` has a simple zero at `ρ`. -/
@[simp]
theorem analyticOrderAt_E₄_comp_ofComplex_ρ :
    analyticOrderAt (E₄ ∘ ofComplex) (ρ : ℂ) = 1 := by
  refine (UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo E₄) ρ.im_pos)
    |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp [ofComplex_apply]) fun h ↦ E₆_ρ_ne_zero ?_
  have hD := congrFun Derivative.normalizedDerivOfComplex_E₄ ρ
  rw [Derivative.normalizedDerivOfComplex, h, mul_zero] at hD
  simpa using hD

/-- `E₆` has a simple zero at `i`. -/
@[simp]
theorem analyticOrderAt_E₆_comp_ofComplex_I :
    analyticOrderAt (E₆ ∘ ofComplex) Complex.I = 1 := by
  rw [← coe_I]
  refine (UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo E₆) I.im_pos)
    |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by rw [Function.comp_apply, ofComplex_apply]; exact E₆_I) fun h ↦ E₄_I_ne_zero ?_
  have hD := congrFun Derivative.normalizedDerivOfComplex_E₆ I
  rw [Derivative.normalizedDerivOfComplex, h, mul_zero] at hD
  simpa using hD

/-- The order of `fⁿ / Δ` is `n` times the order of `f`, as `Δ` has no zeros. -/
private lemma analyticOrderAt_pow_div_discriminant {f : ℍ → ℂ} (hf : MDiff f) (n : ℕ)
    (z : ℍ) :
    analyticOrderAt (fun w ↦ f (ofComplex w) ^ n / discriminant (ofComplex w)) z =
      n • analyticOrderAt (f ∘ ofComplex) z := by
  have hf' := UpperHalfPlane.analyticAt_comp_ofComplex hf z.im_pos
  have hΔ : (discriminant ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa [ofComplex_apply] using discriminant_ne_zero z
  have hΔinv : AnalyticAt ℂ (discriminant ∘ ofComplex)⁻¹ z :=
    (UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo CuspForm.discriminant)
      z.im_pos).inv hΔ
  have heq : (fun w ↦ f (ofComplex w) ^ n / discriminant (ofComplex w)) =
      (f ∘ ofComplex) ^ n * (discriminant ∘ ofComplex)⁻¹ := by
    funext w
    simp [div_eq_mul_inv]
  rw [heq, analyticOrderAt_mul (hf'.pow n) hΔinv, analyticOrderAt_pow hf',
    hΔinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hΔ), add_zero]

/-- The modular invariant vanishes to order exactly `3` at the elliptic point `ρ`. -/
@[simp]
theorem analyticOrderAt_j_comp_ofComplex_ρ : analyticOrderAt (j ∘ ofComplex) (ρ : ℂ) = 3 := by
  have heq : j ∘ ofComplex = fun w ↦ E₄ (ofComplex w) ^ 3 / discriminant (ofComplex w) := by
    funext w
    simp [j_apply]
  rw [heq, analyticOrderAt_pow_div_discriminant (ModularFormClass.holo E₄),
    analyticOrderAt_E₄_comp_ofComplex_ρ]
  simp

/-- The function `j - 1728` vanishes to order exactly `2` at the elliptic point `i`. -/
@[simp]
theorem analyticOrderAt_j_sub_1728_comp_ofComplex_I :
    analyticOrderAt ((j - 1728) ∘ ofComplex) Complex.I = 2 := by
  have heq : (j - 1728) ∘ ofComplex =
      fun w ↦ E₆ (ofComplex w) ^ 2 / discriminant (ofComplex w) := by
    funext w
    simp [j_sub_1728]
  rw [heq, ← coe_I, analyticOrderAt_pow_div_discriminant (ModularFormClass.holo E₆), coe_I,
    analyticOrderAt_E₆_comp_ofComplex_I]
  simp

end TauCeti.ModularForm
