/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho

/-!
# The lattice of a complex elliptic curve

For a period lattice `Λ`, the point map `z ↦ (℘(z), ℘'(z) / 2)` descends to a group isomorphism
`ℂ / Λ ≃+ E_Λ(ℂ)` onto the points of the Weierstrass curve `E_Λ : y² = x³ - (g₂ / 4) x - g₃ / 4`
(`PeriodPair.weierstrassPointEquiv`), and rescaling `Λ` by `c` changes `E_Λ` by the change of
variables with `u = c` (`PeriodPair.weierstrassCurve_eq_smul_of_lattice_eq`). This file proves the
converse: every complex elliptic curve arises from a lattice, unique up to homothety.
The pair of invariants `(g₂, g₃)`, or equivalently the Weierstrass curve itself, determines the
lattice exactly; a change of variables between lattice curves recovers the exact rescaling.

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

* `PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq`,
  `PeriodPair.weierstrassCurve_eq_iff_lattice_eq`: a lattice is determined by its invariants,
  equivalently by its Weierstrass curve.
* `PeriodPair.variableChange_eq_mk_of_smul_eq`: a change of variables between lattice curves is
  a scaling `(x, y) ↦ (u²x, u³y)`.
* `PeriodPair.lattice_eq_smul_of_variableChange_smul_eq`: a change of variables with scaling
  factor `u` between lattice curves rescales the lattice by `u`.
* `WeierstrassCurve.exists_periodPair_variableChange_smul_eq`: every elliptic curve over `ℂ`
  comes from a lattice by a change of variables with `u = 1`.

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

/-- **A lattice with `g₃ = 0` has complex multiplication by `i`**: it is preserved by every fourth
root of unity. Indeed `j = 1728`, so the lattice is homothetic to `ℤ i + ℤ`. -/
theorem lattice_smul_eq_self_of_g₃_eq_zero (h : L.g₃ = 0) {c : ℂˣ} (hc : (c : ℂ) ^ 4 = 1) :
    (c • L).lattice = L.lattice := by
  obtain ⟨d, hd⟩ := weierstrassCurve_j_eq_iff.mp
    ((UpperHalfPlane.weierstrassCurve_j_periodPair _).trans
      (TauCeti.ModularForm.j_I.trans (weierstrassCurve_j_eq_1728_iff.mpr h).symm))
  exact lattice_smul_eq_self_of_lattice_eq_smul hd
    (lattice_smul_eq_self_of_pow_eq_one (ζ := Units.mk0 Complex.I I_ne_zero)
      (by simpa using Complex.isPrimitiveRoot_I) UpperHalfPlane.lattice_I_smul_periodPair_I hc)

/-- **A lattice with `g₂ = 0` has complex multiplication by `ρ`**: it is preserved by every sixth
root of unity. Indeed `j = 0`, so the lattice is homothetic to `ℤ ρ + ℤ`. -/
theorem lattice_smul_eq_self_of_g₂_eq_zero (h : L.g₂ = 0) {c : ℂˣ} (hc : (c : ℂ) ^ 6 = 1) :
    (c • L).lattice = L.lattice := by
  obtain ⟨d, hd⟩ := weierstrassCurve_j_eq_iff.mp
    ((UpperHalfPlane.weierstrassCurve_j_periodPair _).trans
      (TauCeti.ModularForm.j_ρ.trans (weierstrassCurve_j_eq_zero_iff.mpr h).symm))
  -- `ρ` is a primitive cube root of unity, and `c` or `-c` is a cube root of unity.
  have hρ : IsPrimitiveRoot ((Units.mk0 (UpperHalfPlane.ρ : ℂ) UpperHalfPlane.ρ.ne_zero : ℂˣ) : ℂ)
      3 := by
    have hpow : ((UpperHalfPlane.ρ : ℂ) + 1) ^ 2 = (UpperHalfPlane.ρ : ℂ) := by
      linear_combination UpperHalfPlane.ρ_sq
    simpa only [Units.val_mk0, hpow] using
      UpperHalfPlane.isPrimitiveRoot_ρ_add_one.pow_of_dvd (p := 2) (by norm_num) (by norm_num)
  have hρL (c : ℂˣ) (hc : (c : ℂ) ^ 3 = 1) :
      (c • UpperHalfPlane.ρ.periodPair).lattice = UpperHalfPlane.ρ.periodPair.lattice :=
    lattice_smul_eq_self_of_pow_eq_one hρ UpperHalfPlane.lattice_ρ_smul_periodPair_ρ hc
  refine lattice_smul_eq_self_of_lattice_eq_smul hd ?_
  rcases mul_self_eq_one_iff.mp (by linear_combination hc : ((c : ℂ) ^ 3) * (c : ℂ) ^ 3 = 1)
    with h3 | h3
  · exact hρL c h3
  · have hneg : c = -1 * -c := by simp
    rw [hneg, mul_smul, lattice_neg_one_smul]
    exact hρL (-c) (by rw [Units.val_neg, neg_pow, h3]; norm_num)

/-- **Period-lattice recovery**: a lattice is determined by its invariants `g₂` and `g₃`. -/
theorem lattice_eq_iff_g₂_eq_and_g₃_eq : L.lattice = L'.lattice ↔ L.g₂ = L'.g₂ ∧ L.g₃ = L'.g₃ := by
  refine ⟨g₂_eq_and_g₃_eq_of_lattice_eq, fun ⟨h₂, h₃⟩ ↦ ?_⟩
  -- The curves agree, so `Λ' = c Λ` for some `c ∈ ℂˣ`; then `c⁴ g₂ = g₂` and `c⁶ g₃ = g₃`.
  obtain ⟨c, hc⟩ := (weierstrassCurve_j_eq_iff (L := L) (L' := L')).mp (by
    rw [weierstrassCurve_j, weierstrassCurve_j, h₂, h₃])
  rw [hc]
  have hc₀ : (c : ℂ) ≠ 0 := c.ne_zero
  obtain ⟨hg₂, hg₃⟩ := g₂_eq_and_g₃_eq_of_lattice_eq hc
  rw [g₂_smul, ← h₂, eq_div_iff (pow_ne_zero 4 hc₀)] at hg₂
  rw [g₃_smul, ← h₃, eq_div_iff (pow_ne_zero 6 hc₀)] at hg₃
  symm
  rcases eq_or_ne L.g₃ 0 with h0 | h₃0
  · have h₂0 : L.g₂ ≠ 0 := fun h' ↦ L.weierstrassCurve_Δ_ne_zero (by
      rw [weierstrassCurve_Δ, h', h0]; ring)
    exact lattice_smul_eq_self_of_g₃_eq_zero h0 ((mul_eq_left₀ h₂0).mp hg₂)
  rcases eq_or_ne L.g₂ 0 with h0 | h₂0
  · exact lattice_smul_eq_self_of_g₂_eq_zero h0 ((mul_eq_left₀ h₃0).mp hg₃)
  -- Otherwise `c⁴ = c⁶ = 1`, so `c² = 1`.
  have h4 := (mul_eq_left₀ h₂0).mp hg₂
  have h6 := (mul_eq_left₀ h₃0).mp hg₃
  exact lattice_smul_eq_self_of_sq_eq_one (by linear_combination h6 - (c : ℂ) ^ 2 * h4)

/-- A change of variables `C` taking `E_Λ` to `E_{Λ'}` is the scaling `(x, y) ↦ (u²x, u³y)`: it has
`r = s = t = 0`. -/
theorem variableChange_eq_mk_of_smul_eq {C : VariableChange ℂ}
    (h : C • L.weierstrassCurve = L'.weierstrassCurve) : C = ⟨C.u, 0, 0, 0⟩ :=
  have : (C • L.weierstrassCurve).IsShortNF := h ▸ inferInstance
  C.eq_mk_u_of_isShortNF L.weierstrassCurve (.of_ne_zero two_ne_zero) (.of_ne_zero three_ne_zero)

/-- **Changes of variables between lattice curves are rescalings**: if a change of variables `C`
takes `E_Λ` to `E_{Λ'}`, then `Λ' = u Λ` for the scaling factor `u` of `C`. -/
theorem lattice_eq_smul_of_variableChange_smul_eq {C : VariableChange ℂ}
    (h : C • L.weierstrassCurve = L'.weierstrassCurve) : L'.lattice = (C.u • L).lattice := by
  have : (C • L.weierstrassCurve).IsShortNF := h ▸ inferInstance
  have h2 : IsRegular (2 : ℂ) := .of_ne_zero two_ne_zero
  have h3 : IsRegular (3 : ℂ) := .of_ne_zero three_ne_zero
  have h₄ := variableChange_a₄_of_isShortNF L.weierstrassCurve C h2
  have h₆ := variableChange_a₆_of_isShortNF L.weierstrassCurve C h2 h3
  rw [h, weierstrassCurve_a₄, weierstrassCurve_a₄] at h₄
  rw [h, weierstrassCurve_a₆, weierstrassCurve_a₆] at h₆
  refine lattice_eq_iff_g₂_eq_and_g₃_eq.mpr ⟨?_, ?_⟩
  · rw [g₂_smul, div_eq_mul_inv, ← inv_pow, ← Units.val_inv_eq_inv_val]
    linear_combination -4 * h₄
  · rw [g₃_smul, div_eq_mul_inv, ← inv_pow, ← Units.val_inv_eq_inv_val]
    linear_combination -4 * h₆

/-- **A lattice is determined by its Weierstrass curve.** -/
theorem weierstrassCurve_eq_iff_lattice_eq :
    L.weierstrassCurve = L'.weierstrassCurve ↔ L.lattice = L'.lattice :=
  ⟨fun h ↦ by
    simpa [VariableChange.one_def] using
      (lattice_eq_smul_of_variableChange_smul_eq (C := 1) (L' := L') (by rw [one_smul, h])).symm,
    weierstrassCurve_eq_of_lattice_eq⟩

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

/-- Every elliptic curve over `ℂ` is the image of the Weierstrass curve of a lattice under a change
of variables with scaling factor `u = 1`. -/
theorem exists_periodPair_variableChange_smul_eq :
    ∃ (L : PeriodPair) (C : VariableChange ℂ), C.u = 1 ∧ C • L.weierstrassCurve = E := by
  obtain ⟨τ, C, hC⟩ := E.exists_variableChange_smul_weierstrassCurve_periodPair_eq
  refine ⟨C.u • τ.periodPair, C * ⟨C.u, 0, 0, 0⟩⁻¹, ?_, ?_⟩
  · simp [VariableChange.mul_def, VariableChange.inv_def]
  · rw [PeriodPair.weierstrassCurve_smul, mul_smul, inv_smul_smul, hC]

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
  have : (C • τ.periodPair.weierstrassCurve).IsShortNF := hC ▸ ⟨rfl, rfl, rfl⟩
  have hE : (C.u • τ.periodPair).weierstrassCurve = E := by
    rw [weierstrassCurve_smul, ← hC, ← C.eq_mk_u_of_isShortNF τ.periodPair.weierstrassCurve
      (.of_ne_zero two_ne_zero) (.of_ne_zero three_ne_zero)]
  refine ⟨C.u • τ.periodPair, ?_, ?_⟩
  · linear_combination -4 * (weierstrassCurve_a₄ _).symm.trans (congrArg a₄ hE)
  · linear_combination -4 * (weierstrassCurve_a₆ _).symm.trans (congrArg a₆ hE)

end PeriodPair
