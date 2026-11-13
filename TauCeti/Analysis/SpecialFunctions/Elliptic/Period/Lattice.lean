/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Topology

/-!
# The period lattice of a complex elliptic curve

A period lattice `Λ` is recovered from its Weierstrass curve
`E_Λ : y² = x³ - (g₂ / 4) x - g₃ / 4`: two lattices with the same invariants `g₂` and `g₃` are
equal (`PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq`). Homothetic lattices `Λ' = c Λ` have
`g₂(Λ') = c⁻⁴ g₂(Λ)` and `g₃(Λ') = c⁻⁶ g₃(Λ)`, so the content is that a scalar `c` with
`c⁴ g₂ = g₂` and `c⁶ g₃ = g₃` preserves `Λ`. When `g₂ g₃ ≠ 0` this forces `c = ±1`. When
`g₃ = 0` the curve has `j = 1728`, so `Λ` is homothetic to `ℤ i + ℤ`, which is preserved by
multiplication by `i` and hence by every fourth root of unity; when `g₂ = 0` the curve has `j = 0`
and `Λ` is homothetic to `ℤ ρ + ℤ`, preserved by every sixth root of unity.

Consequently a change of variables between two lattice curves `E_Λ` and `E_{Λ'}` is a rescaling,
and `Λ' = u Λ` for its scaling factor `u` (`PeriodPair.lattice_eq_smul_of_variableChange_smul_eq`).
Every elliptic curve `E` over `ℂ` is the image of some `E_Λ` under a change of variables with
`u = 1`, and by the above this `Λ` is unique: it is the **period lattice** `E.periodLattice` of `E`.
The normalization `u = 1` is the one under which the invariant differential
`dx / (2y + a₁x + a₃)` of `E` pulls back to `dz` along the lattice point map
`z ↦ (℘(z), ℘'(z) / 2)` composed with the point isomorphism from `E_Λ` to `E` induced by
the chosen change of variables with `u = 1`, so
`E.periodLattice` is the lattice of periods of that differential; differentials themselves are not
used here. The period lattice scales by `u` under a change of variables with scaling factor `u`
(`WeierstrassCurve.variableChange_periodLattice`), and `E(ℂ)` is isomorphic as a topological
group to `ℂ / E.periodLattice`.

## Main definitions

* `WeierstrassCurve.periodLattice`: the period lattice of an elliptic curve over `ℂ`.

## Main results

* `PeriodPair.lattice_smul_eq_self_of_g₃_eq_zero`, `PeriodPair.lattice_smul_eq_self_of_g₂_eq_zero`:
  a lattice with `g₃ = 0` is preserved by the fourth roots of unity, one with `g₂ = 0` by the
  sixth roots of unity.
* `PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq`,
  `PeriodPair.weierstrassCurve_eq_iff_lattice_eq`: **period-lattice recovery**, a lattice is
  determined by `g₂` and `g₃`, equivalently by its Weierstrass curve.
* `PeriodPair.lattice_eq_smul_of_variableChange_smul_eq`: a change of variables `C` taking `E_Λ`
  to `E_{Λ'}` has `Λ' = C.u Λ`.
* `WeierstrassCurve.periodLattice_eq_iff`: `E.periodLattice = Λ` exactly when `E` is the image of
  `E_Λ` under a change of variables with `u = 1`.
* `WeierstrassCurve.variableChange_periodLattice`: rescaling naturality of the period
  lattice.
* `WeierstrassCurve.nonempty_continuousAddEquiv_periodLattice`: `E(ℂ) ≃ₜ+ ℂ / E.periodLattice`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.1, §VI.3 and §VI.5.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.3.
-/

public noncomputable section

open Complex WeierstrassCurve

/-! ### The period lattice of a complex elliptic curve -/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- The **period lattice** of an elliptic curve `E` over `ℂ`: the unique lattice `Λ` whose
Weierstrass curve `y² = x³ - (g₂(Λ) / 4) x - g₃(Λ) / 4` is taken to `E` by a change of variables
with scaling factor `u = 1` (`WeierstrassCurve.periodLattice_eq_iff`). The normalization `u = 1`
makes it the lattice of periods of the invariant differential `dx / (2y + a₁x + a₃)` of `E`, which
the lattice point map `z ↦ (℘(z), ℘'(z) / 2)`, composed with the point isomorphism from `E_Λ`
to `E` induced by the chosen change of variables with `u = 1`, pulls back to `dz`. -/
def periodLattice : Submodule ℤ ℂ :=
  E.exists_periodPair_variableChange_smul_eq.choose.lattice

variable {E}

/-- `E.periodLattice = Λ` exactly when `E` is the image of the Weierstrass curve of `Λ` under a
change of variables with scaling factor `u = 1`. -/
theorem periodLattice_eq_iff {L : PeriodPair} :
    E.periodLattice = L.lattice ↔
      ∃ C : VariableChange ℂ, C.u = 1 ∧ C • L.weierstrassCurve = E := by
  obtain ⟨C₀, hu₀, h₀⟩ := E.exists_periodPair_variableChange_smul_eq.choose_spec
  refine ⟨fun h ↦ ⟨C₀, hu₀, ?_⟩, fun ⟨C, hu, hC⟩ ↦ ?_⟩
  · rwa [← PeriodPair.weierstrassCurve_eq_of_lattice_eq h]
  · have := PeriodPair.lattice_eq_smul_of_variableChange_smul_eq (C := C⁻¹ * C₀)
      (L' := L) (by rw [mul_smul, h₀, ← hC, inv_smul_smul])
    rw [periodLattice, this]
    simp [VariableChange.mul_def, VariableChange.inv_def, hu, hu₀]

/-- Every complex elliptic curve has a period lattice spanned by a period pair. -/
theorem exists_periodPair_lattice_eq_periodLattice :
    ∃ L : PeriodPair, L.lattice = E.periodLattice :=
  ⟨E.exists_periodPair_variableChange_smul_eq.choose, by rw [periodLattice]⟩

/-- The period lattice of the Weierstrass curve of `Λ` is `Λ`. -/
@[simp]
theorem _root_.PeriodPair.periodLattice_weierstrassCurve (L : PeriodPair) :
    L.weierstrassCurve.periodLattice = L.lattice :=
  periodLattice_eq_iff.mpr ⟨1, rfl, one_smul _ _⟩

/-- **Rescaling naturality of the period lattice**: a change of variables with scaling factor `u`
multiplies the period lattice by `u`. -/
theorem variableChange_periodLattice (C : VariableChange ℂ) :
    (C • E).periodLattice = E.periodLattice.map (LinearMap.mulLeft ℤ (C.u : ℂ)) := by
  obtain ⟨L, hL⟩ := E.exists_periodPair_lattice_eq_periodLattice
  obtain ⟨C₀, hu₀, h₀⟩ := periodLattice_eq_iff.mp hL.symm
  rw [← hL, ← PeriodPair.lattice_smul, periodLattice_eq_iff]
  refine ⟨C * C₀ * ⟨C.u, 0, 0, 0⟩⁻¹, ?_, ?_⟩
  · simp [VariableChange.mul_def, VariableChange.inv_def, hu₀]
  · rw [PeriodPair.weierstrassCurve_smul, mul_smul, inv_smul_smul, mul_smul, h₀]

/-- **Uniformization of a complex elliptic curve by its period lattice**: the points of an elliptic
curve `E` over `ℂ` are isomorphic as a topological group to `ℂ / E.periodLattice`. -/
theorem nonempty_continuousAddEquiv_periodLattice :
    Nonempty (ℂ ⧸ E.periodLattice.toAddSubgroup ≃ₜ+ E.toProjective.Point) := by
  obtain ⟨L, C, hu, rfl⟩ := E.exists_periodPair_variableChange_smul_eq
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩]
  exact ⟨L.weierstrassPointContinuousAddEquiv.trans
    (Projective.Point.continuousAddEquivVariableChange _ C).symm⟩

end WeierstrassCurve
