/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere

/-!
# The lattice of a complex elliptic curve

For a period lattice `Λ`, the point map `z ↦ (℘(z), ℘'(z) / 2)` descends to a group isomorphism
`ℂ / Λ ≃+ E_Λ(ℂ)` onto the points of the Weierstrass curve `E_Λ : y² = x³ - (g₂ / 4) x - g₃ / 4`
(`PeriodPair.weierstrassPointEquiv`), and rescaling `Λ` by `c` changes `E_Λ` by the change of
variables with `u = c` (`PeriodPair.weierstrassCurve_eq_smul_of_lattice_eq`). This file proves the
converse: every complex elliptic curve arises from a lattice, unique up to homothety.

Every lattice is homothetic to `ℤ τ + ℤ` with `τ ∈ ℍ`, and the `j`-invariant of `E_{ℤ τ + ℤ}` is
the modular invariant `j(τ)`, which takes every complex value (`TauCeti.ModularForm.j_surjective`).
Over the algebraically closed field `ℂ`, elliptic curves with the same `j`-invariant are related by
a change of variables (`WeierstrassCurve.exists_variableChange_of_j_eq`), so every elliptic curve
`E` over `ℂ` is a change of variables of some `E_{ℤ τ + ℤ}`, and `E(ℂ) ≃+ ℂ / Λ` for a lattice `Λ`.
For a curve in the short form `y² = x³ - (a / 4) x - b / 4` the change of variables is a rescaling,
which gives the uniformization theorem: whenever `a³ - 27 b² ≠ 0` there is a lattice with `g₂ = a`
and `g₃ = b`.

The lattice is determined by the curve up to homothety: two lattices give isomorphic curves, or
just curves with the same `j`-invariant, exactly when they are homothetic. This follows from the
fact that `j(τ) = j(τ')` exactly when `τ' ∈ SL(2, ℤ) τ` (`TauCeti.ModularGroup.j_eq_j_iff`), since
the lattice of `γ τ` is `(c τ + d)⁻¹ (ℤ τ + ℤ)`.

## Main results

* `PeriodPair.weierstrassCurve_j_eq_iff`,
  `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq_iff`: `E_Λ` and `E_{Λ'}` have the same
  `j`-invariant, or are related by a change of variables, exactly when `Λ'` is homothetic to `Λ`.
* `WeierstrassCurve.exists_variableChange_smul_weierstrassCurve_periodPair_eq`: every elliptic curve
  over `ℂ` is a change of variables of the curve of some `ℤ τ + ℤ`.
* `WeierstrassCurve.exists_periodPair_nonempty_addEquiv`: every elliptic curve `E` over `ℂ` has
  `E(ℂ) ≃+ ℂ / Λ` for some lattice `Λ`.
* `PeriodPair.exists_g₂_g₃_eq`: **the uniformization theorem**, every pair `(a, b)` with
  `a³ - 27 b² ≠ 0` is `(g₂, g₃)` of some lattice.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.3, §VI.4 and Theorem VI.5.1.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.3.3.
-/

public noncomputable section

open Complex UpperHalfPlane WeierstrassCurve

/-! ### Homothetic lattices -/

namespace PeriodPair

variable {L L' : PeriodPair}

/-- **The `j`-invariant classifies lattices up to homothety**: `E_Λ` and `E_{Λ'}` have the same
`j`-invariant exactly when `Λ' = c Λ` for some `c ∈ ℂˣ`. -/
theorem weierstrassCurve_j_eq_iff :
    L.weierstrassCurve.j = L'.weierstrassCurve.j ↔ ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  refine ⟨fun hj ↦ ?_, fun ⟨c, h⟩ ↦ (weierstrassCurve_j_eq_of_lattice_eq_smul h).symm⟩
  -- Write `Λ = c₁ (ℤ τ + ℤ)` and `Λ' = c₂ (ℤ τ' + ℤ)`; then `j(τ) = j(τ')`, so `τ' = γ τ`.
  obtain ⟨c₁, τ, h₁⟩ := L.exists_lattice_eq_smul_periodPair
  obtain ⟨c₂, τ', h₂⟩ := L'.exists_lattice_eq_smul_periodPair
  rw [weierstrassCurve_j_eq_of_lattice_eq_smul h₁, weierstrassCurve_j_eq_of_lattice_eq_smul h₂,
    weierstrassCurve_j_periodPair, weierstrassCurve_j_periodPair,
    TauCeti.ModularGroup.j_eq_j_iff] at hj
  obtain ⟨γ, rfl⟩ := hj
  -- Then `Λ' = c₂ (c τ + d)⁻¹ (ℤ τ + ℤ) = c₂ (c τ + d)⁻¹ c₁⁻¹ Λ`.
  have h₁' : τ.periodPair.lattice = (c₁⁻¹ • L).lattice := by
    rw [lattice_smul_eq_of_lattice_eq c₁⁻¹ h₁, inv_smul_smul]
  refine ⟨c₂ * (Units.mk0 (denom γ τ) (denom_ne_zero γ τ))⁻¹ * c₁⁻¹, ?_⟩
  rw [h₂, lattice_smul_eq_of_lattice_eq c₂ (lattice_periodPair_smul γ τ), ← mul_smul,
    lattice_smul_eq_of_lattice_eq _ h₁', ← mul_smul]

/-- **Isomorphic curves come from homothetic lattices**: `E_{Λ'}` is a change of variables of
`E_Λ` exactly when `Λ' = c Λ` for some `c ∈ ℂˣ`. -/
theorem exists_variableChange_smul_weierstrassCurve_eq_iff :
    (∃ C : VariableChange ℂ, C • L.weierstrassCurve = L'.weierstrassCurve) ↔
      ∃ c : ℂˣ, L'.lattice = (c • L).lattice := by
  rw [← weierstrassCurve_j_eq_iff]
  refine ⟨fun ⟨C, hC⟩ ↦ ?_, exists_variableChange_of_j_eq _ _⟩
  simp only [← hC, variableChange_j]

end PeriodPair

/-! ### Every complex elliptic curve comes from a lattice -/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- **Every elliptic curve over `ℂ` comes from a lattice**: it is a change of variables of the
Weierstrass curve `y² = x³ - (g₂ / 4) x - g₃ / 4` of `ℤ τ + ℤ` for some `τ ∈ ℍ`, namely any `τ`
with `j(τ) = j(E)`. -/
theorem exists_variableChange_smul_weierstrassCurve_periodPair_eq :
    ∃ (τ : ℍ) (C : VariableChange ℂ), C • τ.periodPair.weierstrassCurve = E := by
  obtain ⟨τ, hτ⟩ := TauCeti.ModularForm.j_surjective E.j
  exact ⟨τ, exists_variableChange_of_j_eq _ _ (by rw [weierstrassCurve_j_periodPair, hτ])⟩

/-- **The complex points of every elliptic curve over `ℂ` are a quotient of `ℂ` by a lattice**: as
an additive group, `E(ℂ) ≃+ ℂ / Λ` for some period lattice `Λ`. -/
theorem exists_periodPair_nonempty_addEquiv :
    ∃ L : PeriodPair, Nonempty ((ℂ ⧸ L.lattice.toAddSubgroup) ≃+ E.toAffine.Point) := by
  obtain ⟨τ, C, hC⟩ := E.exists_variableChange_smul_weierstrassCurve_periodPair_eq
  have h : τ.periodPair.weierstrassCurve = C⁻¹ • E := by rw [← hC, inv_smul_smul]
  exact ⟨τ.periodPair, ⟨τ.periodPair.weierstrassPointEquiv.trans
    ((AddEquiv.cast (M := fun V : WeierstrassCurve ℂ ↦ V.toAffine.Point) h).trans
      (Affine.Point.addEquivVariableChange E C⁻¹))⟩⟩

end WeierstrassCurve

namespace PeriodPair

/-- **The uniformization theorem**: for all `a, b ∈ ℂ` with `a³ - 27 b² ≠ 0` there is a lattice `Λ`
with `g₂(Λ) = a` and `g₃(Λ) = b`. -/
theorem exists_g₂_g₃_eq {a b : ℂ} (hab : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  let E : WeierstrassCurve ℂ := ⟨0, 0, 0, -(a / 4), -(b / 4)⟩
  have hΔ : E.Δ = a ^ 3 - 27 * b ^ 2 := by
    simp only [E, Δ, b₂, b₄, b₆, b₈]
    ring
  have : E.IsElliptic := ⟨hΔ ▸ hab.isUnit⟩
  obtain ⟨τ, C, hC⟩ := E.exists_variableChange_smul_weierstrassCurve_periodPair_eq
  -- A change of variables between two short normal forms has `r = s = t = 0`.
  have : τ.periodPair.weierstrassCurve.IsShortNF := ⟨by simp, by simp, by simp⟩
  have : (C • τ.periodPair.weierstrassCurve).IsShortNF := hC ▸ ⟨rfl, rfl, rfl⟩
  have h2 : IsRegular (2 : ℂ) := .of_ne_zero two_ne_zero
  have hs := C.s_eq_zero_of_isShortNF τ.periodPair.weierstrassCurve h2
  have hr := C.r_eq_zero_of_isShortNF τ.periodPair.weierstrassCurve h2 (.of_ne_zero three_ne_zero)
  have ht := C.t_eq_zero_of_isShortNF τ.periodPair.weierstrassCurve h2
  have hE : (C.u • τ.periodPair).weierstrassCurve = E := by
    rw [weierstrassCurve_smul, ← hC]
    congr 1
    ext <;> simp [hr, hs, ht]
  refine ⟨C.u • τ.periodPair, ?_, ?_⟩
  · linear_combination -4 * (weierstrassCurve_a₄ _).symm.trans (congrArg a₄ hE)
  · linear_combination -4 * (weierstrassCurve_a₆ _).symm.trans (congrArg a₆ hE)

end PeriodPair
