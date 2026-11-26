/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CompactRealForm.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Basic

/-!
# The Cartan involution of a real form compatible with a compact real form

Let `L` be a complex Lie algebra with a conjugation `σ`, whose fixed points form a real form
`𝔤₀ = Fix σ` (`TauCeti.IsLieConjugation.realForm`), and let `τ` be a compact conjugation
(`TauCeti.IsCompactConjugation`) commuting with `σ`. Then `τ` maps `𝔤₀` to itself, and its
restriction `θ = στ|_{𝔤₀}` (on `𝔤₀` the conjugation `σ` is the identity, so this is also
`τ|_{𝔤₀}`) is an involutive automorphism of the real Lie algebra `𝔤₀`. It is a **Cartan
involution**: for `X ∈ 𝔤₀`, the real Killing form of `𝔤₀` is the restriction of the complex
Killing form (`TauCeti.IsLieConjugation.killingForm_realForm`), so
`B_{𝔤₀}(X, θ X) = B(X, τ X) = -H_τ(X, X) < 0` for `X ≠ 0`, where `H_τ` is the positive definite
Hermitian Killing form of `τ`.

This is the construction of the Cartan involution of a real form from a compact real form
commuting with it. The existence of such a `τ` for an arbitrary real form, by conjugating a given
compact real form by an inner automorphism, is not proved here.

## Main declarations

* `TauCeti.IsLieConjugation.apply_mem_realForm_of_commute`: `τ` preserves `Fix σ`.
* `TauCeti.IsLieConjugation.restrictRealForm`: the restriction `θ` of `τ` to `Fix σ`, an
  automorphism of the real Lie algebra `Fix σ`.
* `TauCeti.IsLieConjugation.coe_restrictRealForm_apply_eq_apply_apply`: `θ = στ` on `Fix σ`.
* `TauCeti.IsCompactConjugation.isCartanInvolution_restrictRealForm`: `θ` is a Cartan involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Chapter VI, §2.
-/

public section

open scoped ComplexOrder

namespace TauCeti

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L]
  {σ τ : L →ₛₗ[starRingEnd ℂ] L}

namespace IsLieConjugation

/-- **A conjugation commuting with `σ` preserves the real form `Fix σ`.** -/
theorem apply_mem_realForm_of_commute (hσ : IsLieConjugation σ)
    (hcomm : ∀ x, σ (τ x) = τ (σ x)) {x : L} (hx : x ∈ hσ.realForm) : τ x ∈ hσ.realForm := by
  rw [mem_realForm] at hx ⊢
  rw [hcomm, hx]

/-- **The restriction of a conjugation `τ` commuting with `σ` to the real form `Fix σ`**, an
automorphism of the real Lie algebra `Fix σ`. On `Fix σ` it is `θ = στ`
(`TauCeti.IsLieConjugation.coe_restrictRealForm_apply_eq_apply_apply`). -/
def restrictRealForm (hσ : IsLieConjugation σ) (hτ : IsLieConjugation τ)
    (hcomm : ∀ x, σ (τ x) = τ (σ x)) : hσ.realForm ≃ₗ⁅ℝ⁆ hσ.realForm where
  toFun x := ⟨τ x, hσ.apply_mem_realForm_of_commute hcomm x.property⟩
  invFun x := ⟨τ x, hσ.apply_mem_realForm_of_commute hcomm x.property⟩
  map_add' x y := Subtype.ext (map_add τ (x : L) (y : L))
  map_smul' r x := Subtype.ext (τ.map_real_smul r (x : L))
  map_lie' {x y} := Subtype.ext (hτ.map_lie (x : L) (y : L))
  left_inv x := Subtype.ext (hτ.apply_apply (x : L))
  right_inv x := Subtype.ext (hτ.apply_apply (x : L))

variable (hσ : IsLieConjugation σ) (hτ : IsLieConjugation τ) (hcomm : ∀ x, σ (τ x) = τ (σ x))

/-- The restriction of `τ` to `Fix σ` is `τ`. -/
@[simp]
theorem coe_restrictRealForm_apply (x : hσ.realForm) :
    (hσ.restrictRealForm hτ hcomm x : L) = τ x :=
  (rfl)

/-- **On `Fix σ` the restriction of `τ` is `θ = στ`.** -/
theorem coe_restrictRealForm_apply_eq_apply_apply (x : hσ.realForm) :
    (hσ.restrictRealForm hτ hcomm x : L) = σ (τ x) := by
  rw [coe_restrictRealForm_apply, hcomm, apply_coe_realForm]

/-- Applying the restriction of `τ` to `Fix σ` twice gives the identity. -/
@[simp]
theorem restrictRealForm_restrictRealForm (x : hσ.realForm) :
    hσ.restrictRealForm hτ hcomm (hσ.restrictRealForm hτ hcomm x) = x :=
  Subtype.ext (hτ.apply_apply (x : L))

/-- The restriction of `τ` to `Fix σ` is an involution. -/
theorem restrictRealForm_involutive :
    Function.Involutive (hσ.restrictRealForm hτ hcomm) :=
  hσ.restrictRealForm_restrictRealForm hτ hcomm

/-- The restriction of `τ` to `Fix σ` is its own inverse. -/
@[simp]
theorem restrictRealForm_symm :
    (hσ.restrictRealForm hτ hcomm).symm = hσ.restrictRealForm hτ hcomm :=
  (rfl)

end IsLieConjugation

namespace IsCompactConjugation

/-- **The Cartan involution of a real form from a commuting compact real form.** If `τ` is a
compact conjugation commuting with the conjugation `σ`, then `θ = στ|_{Fix σ}` is a Cartan
involution of the real form `Fix σ`: `B(X, θ X) = -H_τ(X, X) < 0` for `X ≠ 0`. -/
theorem isCartanInvolution_restrictRealForm (hσ : IsLieConjugation σ)
    (hτ : IsCompactConjugation τ) (hcomm : ∀ x, σ (τ x) = τ (σ x)) :
    (hσ.restrictRealForm hτ.toIsLieConjugation hcomm).IsCartanInvolution :=
  LieEquiv.isCartanInvolution_iff.mpr
    ⟨hσ.restrictRealForm_involutive hτ.toIsLieConjugation hcomm, fun _ hx =>
      hτ.killingForm_realForm_neg hσ (hσ.coe_restrictRealForm_apply hτ.toIsLieConjugation hcomm _)
        hx⟩

end IsCompactConjugation

end TauCeti
