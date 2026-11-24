/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GammaOneThreeForm

/-!
# Strict `Γ₁(3)` Weierstrass variable changes

Over a commutative ring `R`, an admissible change of variables `C = (u, r, s, t)` is a **strict
`Γ₁(3)` arrow** out of `W = WeierstrassCurve.gammaOneThreeForm a₁ a₃` (`Y² + a₁XY + a₃Y = X³`) when
`C.u = 1` and `C • W` again has vanishing `a₂`, `a₄`, and `a₆` coefficients
(`WeierstrassCurve.IsStrictGammaOneThreeChange`). It then carries `W` to
`gammaOneThreeForm (a₁ + 2s) (a₃ + ra₁ + 2t)` (`IsStrictGammaOneThreeChange.smul_eq`).

This file establishes the groupoid and base-change closure of strict `Γ₁(3)` variable changes
(`.one`, `.mul`, `.inv`, `.inv_of_eq`, `.map`) together with the inverse-coordinate formulas used to
construct the groupoid shearing equivalence and Hopf-algebroid conjugation.

## Main definitions

* `WeierstrassCurve.IsStrictGammaOneThreeChange a₁ a₃ C`: `C` has `u = 1` and carries
  `gammaOneThreeForm a₁ a₃` to another curve in `Γ₁(3)` normal form.

## Main results

* `WeierstrassCurve.eq_gammaOneThreeForm_iff`: a Weierstrass curve equals `gammaOneThreeForm` of
  its own `a₁` and `a₃` if and only if `a₂ = a₄ = a₆ = 0`.
* `WeierstrassCurve.baseChange_gammaOneThreeForm`: compatibility of `gammaOneThreeForm` with
  `WeierstrassCurve.baseChange`.
* `WeierstrassCurve.IsStrictGammaOneThreeChange.smul_eq`: explicit target curve
  `gammaOneThreeForm (a₁ + 2 * C.s) (a₃ + C.r * a₁ + 2 * C.t)`.
* `WeierstrassCurve.IsStrictGammaOneThreeChange.one`, `.mul`, `.inv`, `.map`: groupoid and
  base-change closure of strict `Γ₁(3)` variable changes.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A,
  Proposition 1.3.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* Christian Carrick, J. Davies and S. van Nigtevecht, *The descent spectral sequence for topological
  modular forms*, arXiv:2412.01640v2, §4.2.
-/

public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A Weierstrass curve equals `gammaOneThreeForm` of its own `a₁` and `a₃` if and only if
`a₂ = a₄ = a₆ = 0`. -/
theorem eq_gammaOneThreeForm_iff (W : WeierstrassCurve R) :
    W = gammaOneThreeForm W.a₁ W.a₃ ↔ W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h₂, h₄, h₆⟩ ↦ by ext <;> simp [h₂, h₄, h₆]⟩

/-- Base change carries `gammaOneThreeForm` to `gammaOneThreeForm` on the algebra images of the
coefficients. Stated separately from `map_gammaOneThreeForm` because `simp` does not unfold
`baseChange`. -/
@[simp]
theorem baseChange_gammaOneThreeForm [Algebra R S] (a₁ a₃ : R) :
    (gammaOneThreeForm a₁ a₃).baseChange S =
      gammaOneThreeForm (algebraMap R S a₁) (algebraMap R S a₃) := by
  rw [baseChange, map_gammaOneThreeForm]

/-- A change of variables `C` is a **strict `Γ₁(3)` arrow** out of `gammaOneThreeForm a₁ a₃` when
`C.u = 1` and `C • gammaOneThreeForm a₁ a₃` again has `a₂ = a₄ = a₆ = 0`. -/
def IsStrictGammaOneThreeChange (a₁ a₃ : R) (C : VariableChange R) : Prop :=
  C.u = 1 ∧ (C • gammaOneThreeForm a₁ a₃).a₂ = 0 ∧
    (C • gammaOneThreeForm a₁ a₃).a₄ = 0 ∧ (C • gammaOneThreeForm a₁ a₃).a₆ = 0

/-- Explicit unfolding of `IsStrictGammaOneThreeChange`. -/
theorem isStrictGammaOneThreeChange_iff {a₁ a₃ : R} {C : VariableChange R} :
    IsStrictGammaOneThreeChange a₁ a₃ C ↔
      C.u = 1 ∧ (C • gammaOneThreeForm a₁ a₃).a₂ = 0 ∧
        (C • gammaOneThreeForm a₁ a₃).a₄ = 0 ∧ (C • gammaOneThreeForm a₁ a₃).a₆ = 0 :=
  Iff.rfl

/-- Characterization of `IsStrictGammaOneThreeChange a₁ a₃ ⟨1, r, s, t⟩` by the three defining
polynomial equations in `(r, s, t)`. -/
theorem isStrictGammaOneThreeChange_mk_iff {a₁ a₃ r s t : R} :
    IsStrictGammaOneThreeChange a₁ a₃ ⟨1, r, s, t⟩ ↔
      3 * r - s ^ 2 - s * a₁ = 0 ∧
        -(s * a₃) - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t = 0 ∧
        r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁ = 0 := by
  simp [IsStrictGammaOneThreeChange, variableChange_gammaOneThreeForm_a₂,
    variableChange_gammaOneThreeForm_a₄, variableChange_gammaOneThreeForm_a₆]

namespace IsStrictGammaOneThreeChange

/-- A strict `Γ₁(3)` arrow has `u = 1`. -/
theorem u_eq_one {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    C.u = 1 :=
  h.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₂`. -/
theorem a₂_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    (C • gammaOneThreeForm a₁ a₃).a₂ = 0 :=
  h.2.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₄`. -/
theorem a₄_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    (C • gammaOneThreeForm a₁ a₃).a₄ = 0 :=
  h.2.2.1

/-- Acting by a strict `Γ₁(3)` arrow annihilates `a₆`. -/
theorem a₆_eq_zero {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    (C • gammaOneThreeForm a₁ a₃).a₆ = 0 :=
  h.2.2.2

/-- A strict `Γ₁(3)` arrow `C` equals `⟨1, C.r, C.s, C.t⟩`. -/
theorem eq_mk {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    C = ⟨1, C.r, C.s, C.t⟩ :=
  VariableChange.ext h.1 rfl rfl rfl

/-- Acting by a strict `Γ₁(3)` arrow produces `gammaOneThreeForm (a₁ + 2s) (a₃ + ra₁ + 2t)`. -/
theorem smul_eq {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    C • gammaOneThreeForm a₁ a₃ =
      gammaOneThreeForm (a₁ + 2 * C.s) (a₃ + C.r * a₁ + 2 * C.t) := by
  have hW := (eq_gammaOneThreeForm_iff (C • gammaOneThreeForm a₁ a₃)).mpr ⟨h.2.1, h.2.2⟩
  conv_lhs => rw [hW]
  conv_lhs => rw [h.eq_mk]
  rw [variableChange_gammaOneThreeForm_a₁, variableChange_gammaOneThreeForm_a₃]

/-- The identity change of variables is a strict `Γ₁(3)` arrow. -/
theorem one (a₁ a₃ : R) : IsStrictGammaOneThreeChange a₁ a₃ 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp

/-- Strict `Γ₁(3)` arrows are closed under composition. -/
theorem mul {a₁ a₃ : R} {C₁ C₂ : VariableChange R}
    (h₁ : IsStrictGammaOneThreeChange a₁ a₃ C₁)
    (h₂ : IsStrictGammaOneThreeChange (a₁ + 2 * C₁.s) (a₃ + C₁.r * a₁ + 2 * C₁.t) C₂) :
    IsStrictGammaOneThreeChange a₁ a₃ (C₂ * C₁) := by
  refine ⟨by rw [VariableChange.mul_def, h₂.1, h₁.1, mul_one], ?_⟩
  rw [mul_smul, h₁.smul_eq]
  exact h₂.2

/-- The inverse of a strict `Γ₁(3)` arrow is a strict `Γ₁(3)` arrow from its target back to its
source. -/
theorem inv {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C) :
    IsStrictGammaOneThreeChange (a₁ + 2 * C.s) (a₃ + C.r * a₁ + 2 * C.t) C⁻¹ := by
  refine ⟨by simp [VariableChange.inv_def, h.1], ?_⟩
  rw [← h.smul_eq, inv_smul_smul]
  exact ⟨gammaOneThreeForm_a₂ a₁ a₃, gammaOneThreeForm_a₄ a₁ a₃, gammaOneThreeForm_a₆ a₁ a₃⟩

/-- Target-coefficient version of `inv`: if `C` carries `gammaOneThreeForm a₁ a₃` to
`gammaOneThreeForm a₁' a₃'`, then `C⁻¹` is a strict `Γ₁(3)` arrow out of
`gammaOneThreeForm a₁' a₃'`. -/
theorem inv_of_eq {a₁ a₃ a₁' a₃' : R} {C : VariableChange R}
    (h : IsStrictGammaOneThreeChange a₁ a₃ C)
    (ha₁ : a₁' = a₁ + 2 * C.s) (ha₃ : a₃' = a₃ + C.r * a₁ + 2 * C.t) :
    IsStrictGammaOneThreeChange a₁' a₃' C⁻¹ := by
  rw [ha₁, ha₃]
  exact h.inv

/-- Recovering `a₁` from the target coefficient `a₁' = a₁ + 2 * C.s` via `C⁻¹`. -/
theorem eq_add_two_mul_inv_s {a₁ a₃ a₁' : R} {C : VariableChange R}
    (h : IsStrictGammaOneThreeChange a₁ a₃ C) (ha₁ : a₁' = a₁ + 2 * C.s) :
    a₁ = a₁' + 2 * C⁻¹.s := by
  simp [ha₁, VariableChange.inv_def, h.u_eq_one]

/-- Recovering `a₃` from the target coefficients `(a₁', a₃')` via `C⁻¹`. -/
theorem eq_add_inv_r_mul_add_two_mul_inv_t {a₁ a₃ a₁' a₃' : R} {C : VariableChange R}
    (h : IsStrictGammaOneThreeChange a₁ a₃ C)
    (ha₁ : a₁' = a₁ + 2 * C.s) (ha₃ : a₃' = a₃ + C.r * a₁ + 2 * C.t) :
    a₃ = a₃' + C⁻¹.r * a₁' + 2 * C⁻¹.t := by
  simp only [ha₁, ha₃, VariableChange.inv_def, h.u_eq_one, inv_one, Units.val_one, one_pow, mul_one]
  ring

/-- Strict `Γ₁(3)` arrows are preserved along ring homomorphisms. -/
theorem map {a₁ a₃ : R} {C : VariableChange R} (h : IsStrictGammaOneThreeChange a₁ a₃ C)
    (f : R →+* S) : IsStrictGammaOneThreeChange (f a₁) (f a₃) (C.map f) := by
  refine ⟨by simp [h.1], ?_⟩
  have hsmul : C.map f • gammaOneThreeForm (f a₁) (f a₃) =
      (C • gammaOneThreeForm a₁ a₃).map f := by
    rw [← map_gammaOneThreeForm, map_variableChange]
  rw [hsmul]
  simp [h.2.1, h.2.2.1, h.2.2.2]

end IsStrictGammaOneThreeChange

end WeierstrassCurve

end
