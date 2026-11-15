/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# Separability of an isogeny and its dual

An isogeny and its dual are both separable exactly when their common degree is nonzero in
the base field. Thus an isogeny of degree prime to the characteristic and its dual both
admit the separable Kummer sequences. For a separable isogeny, this also characterizes
separability of its dual; separability of the original alone does not suffice in positive
characteristic.

Quantitatively, if `φ^*ω₂ = c ω₁` and `φ̂^*ω₁ = c' ω₂` for the invariant differentials `ω₁` and
`ω₂`, then `c c' = deg φ`, since `φ̂ ∘ φ = [deg φ]` pulls `ω₁` back to `deg φ · ω₁`. Over a
valued field this splits the valuation of `deg φ` between `φ` and its dual.

## Main results

* `TauCeti.Isogeny.isSeparable_dual_and_self_iff`: `φ` and `φ̂` are both separable exactly when
  `deg φ ≠ 0` in the base field.
* `TauCeti.Isogeny.mul_eq_degree_of_pullbackDifferential_eq_smul`: `c c' = deg φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2 and III.6.4.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)

/-- An isogeny and its dual are both separable exactly when the degree is nonzero in the
base field. -/
theorem isSeparable_dual_and_self_iff :
    (Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField ∧
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField) ↔
        (φ.degree : F) ≠ 0 := by
  rw [← isSeparable_comp_iff, dual_comp]
  simpa only [Int.cast_natCast] using
    isSeparable_mulByIntIsogeny_iff W₁
      (psiFunctionField_ne_zero_of_Δ_ne_zero W₁ W₁.isUnit_Δ.ne_zero
        (mod_cast φ.degree_ne_zero : (φ.degree : ℤ) ≠ 0))

/-- The dual of an isogeny whose degree is nonzero in the base field is separable. -/
theorem isSeparable_dual_of_degree_ne_zero (h : (φ.degree : F) ≠ 0) :
    Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField :=
  ((φ.isSeparable_dual_and_self_iff).2 h).1

/-- For a separable isogeny, its dual is separable exactly when the degree is nonzero in
the base field. -/
@[simp]
theorem isSeparable_dual_iff
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField ↔
      (φ.degree : F) ≠ 0 :=
  ⟨fun h ↦ φ.isSeparable_dual_and_self_iff.mp ⟨h, inferInstance⟩,
    φ.isSeparable_dual_of_degree_ne_zero⟩

/-- **The differential constants of an isogeny and its dual multiply to the degree**: if
`φ^*ω₂ = c ω₁` and `φ̂^*ω₁ = c' ω₂` for the invariant differentials `ω₁` and `ω₂`, then
`c c' = deg φ`. -/
theorem mul_eq_degree_of_pullbackDifferential_eq_smul {c c' : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    (hc' : φ.dual.pullbackDifferential (invariantDifferential W₁) =
      c' • invariantDifferential W₂) :
    c * c' = φ.degree := by
  -- `(φ̂ ∘ φ)^*ω₁ = φ^*(c' ω₂) = c' c ω₁`, while `φ̂ ∘ φ = [deg φ]` pulls `ω₁` back to `deg φ · ω₁`
  have h : (φ.dual.comp φ).pullbackDifferential (invariantDifferential W₁) =
      (φ.degree : ℤ) • invariantDifferential W₁ := by
    rw [dual_comp]
    exact pullbackDifferential_mulByIntIsogeny_invariantDifferential W₁ _
  rw [pullbackDifferential_comp, LinearMap.comp_apply,
    hc', map_smul, hc, smul_smul, ← Int.cast_smul_eq_zsmul F, Int.cast_natCast] at h
  rw [mul_comm]
  exact smul_left_injective F (invariantDifferential_ne_zero (E := W₁)) h

end TauCeti.Isogeny

end
