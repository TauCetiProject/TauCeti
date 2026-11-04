/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere

/-!
# Complex uniformization: `ℂ / Λ ≃ E(ℂ)` and the lattice of a complex elliptic curve

For a period lattice `Λ`, the point map `z ↦ (℘(z), ℘'(z) / 2)` to the Weierstrass curve
`E_Λ : y² = x³ - (g₂ / 4) x - g₃ / 4` is a surjective group homomorphism with kernel `Λ`
(`PeriodPair.weierstrassPoint_surjective`, `PeriodPair.ker_weierstrassPointHom`), so it descends
to a group isomorphism `ℂ / Λ ≃+ E_Λ(ℂ)` (`PeriodPair.weierstrassPointEquiv`).

Rescaling a lattice by `c ∈ ℂˣ` changes `E_Λ` by the change of variables `(x, y) ↦ (c⁻² x, c⁻³ y)`,
and the induced isomorphism of point groups sends the point of `c z` on `E_{cΛ}` to the point of `z`
on `E_Λ` (`PeriodPair.pointAddEquivOfLatticeEq_weierstrassPoint`). Since the curve only depends on
the lattice, the same holds for any basis of `cΛ`.

Conversely, every complex elliptic curve arises from a lattice. Every lattice is homothetic to
`ℤ τ + ℤ` with `τ ∈ ℍ`, and the `j`-invariant of `E_{ℤ τ + ℤ}` is the modular invariant `j(τ)`,
which takes every complex value (`TauCeti.ModularForm.j_surjective`). Over the algebraically closed
field `ℂ`, elliptic curves with the same `j`-invariant are related by a change of variables
(`WeierstrassCurve.exists_variableChange_of_j_eq`), so every elliptic curve `E` over `ℂ` is a
change of variables of some `E_{ℤ τ + ℤ}`, and `E(ℂ) ≃+ ℂ / Λ` for a lattice `Λ`. For a curve in
the short form `y² = x³ - (a / 4) x - b / 4` the change of variables is a rescaling, which gives
the uniformization theorem: whenever `a³ - 27 b² ≠ 0` there is a lattice with `g₂ = a` and
`g₃ = b`.

The lattice is determined by the curve up to homothety: two lattices give isomorphic curves, or
just curves with the same `j`-invariant, exactly when they are homothetic. This follows from the
fact that `j(τ) = j(τ')` exactly when `τ' ∈ SL(2, ℤ) τ` (`TauCeti.ModularForm.j_eq_j_iff`), since
the lattice of `γ τ` is `(c τ + d)⁻¹ (ℤ τ + ℤ)`.

## Main definitions

* `PeriodPair.weierstrassPointEquiv`: the group isomorphism `ℂ / Λ ≃+ E_Λ(ℂ)`.
* `PeriodPair.pointAddEquivOfLatticeEq`: for `Λ' = c Λ`, the isomorphism `E_{Λ'}(ℂ) ≃+ E_Λ(ℂ)`
  given by the change of variables with `u = c`.

## Main results

* `PeriodPair.weierstrassPointEquiv_mk`, `PeriodPair.weierstrassPointEquiv_symm_weierstrassPoint`:
  the isomorphism and its inverse on the class of `z`.
* `PeriodPair.pointAddEquivOfLatticeEq_weierstrassPoint`,
  `PeriodPair.pointAddEquivOfLatticeEq_symm_weierstrassPoint`: rescaling naturality of the point
  map.
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

/-! ### The isomorphism `ℂ / Λ ≃+ E(ℂ)` -/

namespace PeriodPair

variable (L : PeriodPair)

/-- **The complex uniformization** `ℂ / Λ ≃+ E_Λ(ℂ)`, induced by the point map
`z ↦ (℘(z), ℘'(z) / 2)` (`PeriodPair.weierstrassPoint`), which is a surjective group homomorphism
with kernel `Λ`. -/
def weierstrassPointEquiv :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ L.weierstrassCurve.toAffine.Point :=
  QuotientAddGroup.liftEquiv _
    (fun P ↦ by simpa using L.weierstrassPoint_surjective P) L.ker_weierstrassPointHom.symm

@[simp]
lemma weierstrassPointEquiv_mk (z : ℂ) :
    L.weierstrassPointEquiv (QuotientAddGroup.mk z) = L.weierstrassPoint z := by
  exact (QuotientAddGroup.liftEquiv_mk _ _ _ z).trans (L.weierstrassPointHom_apply z)

@[simp]
lemma weierstrassPointEquiv_symm_weierstrassPoint (z : ℂ) :
    L.weierstrassPointEquiv.symm (L.weierstrassPoint z) = QuotientAddGroup.mk z := by
  rw [AddEquiv.symm_apply_eq, weierstrassPointEquiv_mk]

/-! ### Homothetic lattices -/

variable {L} {L' : PeriodPair} {c : ℂˣ}

/-- If `Λ' = c Λ`, the curve of `Λ'` is obtained from that of `Λ` by the change of variables
`(x, y) ↦ (c⁻² x, c⁻³ y)`, that is, with `u = c` and `r = s = t = 0`. -/
lemma weierstrassCurve_eq_smul_of_lattice_eq (h : L'.lattice = (c • L).lattice) :
    L'.weierstrassCurve = (⟨c, 0, 0, 0⟩ : VariableChange ℂ) • L.weierstrassCurve := by
  rw [weierstrassCurve_eq_of_lattice_eq h, weierstrassCurve_smul]

/-- Homothetic lattices have the same `j`-invariant. -/
lemma weierstrassCurve_j_eq_of_lattice_eq_smul (h : L'.lattice = (c • L).lattice) :
    L'.weierstrassCurve.j = L.weierstrassCurve.j := by
  simp only [weierstrassCurve_eq_smul_of_lattice_eq h, variableChange_j]

/-- For `Λ' = c Λ`, the isomorphism `E_{Λ'}(ℂ) ≃+ E_Λ(ℂ)` given by the change of variables
`(x, y) ↦ (c² x, c³ y)`. It sends the point of `c z` to the point of `z`
(`PeriodPair.pointAddEquivOfLatticeEq_weierstrassPoint`). -/
def pointAddEquivOfLatticeEq (h : L'.lattice = (c • L).lattice) :
    L'.weierstrassCurve.toAffine.Point ≃+ L.weierstrassCurve.toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve ℂ ↦ V.toAffine.Point)
    (weierstrassCurve_eq_smul_of_lattice_eq h)).trans
    (Affine.Point.addEquivVariableChange L.weierstrassCurve _)

/-- **Rescaling naturality of the point map.** If `Λ' = c Λ`, the change of variables from `E_{Λ'}`
to `E_Λ` sends the point `(℘(c z; Λ'), ℘'(c z; Λ') / 2)` to `(℘(z; Λ), ℘'(z; Λ) / 2)`. -/
@[simp]
theorem pointAddEquivOfLatticeEq_weierstrassPoint (h : L'.lattice = (c • L).lattice) (z : ℂ) :
    pointAddEquivOfLatticeEq h (L'.weierstrassPoint (c * z)) = L.weierstrassPoint z := by
  have hmem : (c : ℂ) * z ∈ L'.lattice ↔ z ∈ L.lattice := by
    rw [h, mul_mem_lattice_smul_iff]
  by_cases hz : z ∈ L.lattice
  · rw [L'.weierstrassPoint_of_mem (hmem.mpr hz), L.weierstrassPoint_of_mem hz, map_zero]
  rw [L'.weierstrassPoint_of_notMem (mt hmem.mp hz), L.weierstrassPoint_of_notMem hz,
    pointAddEquivOfLatticeEq, AddEquiv.trans_apply, AddEquiv.cast_apply,
    Affine.Point.cast_some (weierstrassCurve_eq_smul_of_lattice_eq h),
    Affine.Point.coe_addEquivVariableChange, Affine.Point.equivVariableChange_some,
    Affine.Point.some.injEq, weierstrassP_eq_of_lattice_eq h, derivWeierstrassP_eq_of_lattice_eq h,
    weierstrassP_smul, derivWeierstrassP_smul]
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  constructor <;> field_simp <;> ring

@[simp]
theorem pointAddEquivOfLatticeEq_symm_weierstrassPoint (h : L'.lattice = (c • L).lattice)
    (z : ℂ) : (pointAddEquivOfLatticeEq h).symm (L.weierstrassPoint z) =
      L'.weierstrassPoint (c * z) := by
  rw [AddEquiv.symm_apply_eq, pointAddEquivOfLatticeEq_weierstrassPoint]

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
    TauCeti.ModularForm.j_eq_j_iff] at hj
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

/-- **The complex points of every elliptic curve over `ℂ` form a complex torus**: `E(ℂ) ≃+ ℂ / Λ`
for some lattice `Λ`. -/
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
  -- A change of variables between two curves with `a₁ = a₂ = a₃ = 0` has `r = s = t = 0`.
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    have := congrArg a₁ hC
    simp only [variableChange_a₁, weierstrassCurve_a₁, E] at this
    simpa [hu] using this
  have hr : C.r = 0 := by
    have := congrArg a₂ hC
    simp only [variableChange_a₂, weierstrassCurve_a₁, weierstrassCurve_a₂, hs, E] at this
    simpa [hu] using this
  have ht : C.t = 0 := by
    have := congrArg a₃ hC
    simp only [variableChange_a₃, weierstrassCurve_a₁, weierstrassCurve_a₃, hr, E] at this
    simpa [hu] using this
  have hE : (C.u • τ.periodPair).weierstrassCurve = E := by
    rw [weierstrassCurve_smul, ← hC]
    congr 1
    ext <;> simp [hr, hs, ht]
  refine ⟨C.u • τ.periodPair, ?_, ?_⟩
  · linear_combination -4 * (weierstrassCurve_a₄ _).symm.trans (congrArg a₄ hE)
  · linear_combination -4 * (weierstrassCurve_a₆ _).symm.trans (congrArg a₆ hE)

end PeriodPair
