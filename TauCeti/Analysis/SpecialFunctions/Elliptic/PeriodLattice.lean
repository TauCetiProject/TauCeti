/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Topology
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

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
`dx / (2y + a₁x + a₃)` of `E` pulls back to `dz` along the point map `z ↦ (℘(z), ℘'(z) / 2)`, so
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
* `PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq`, `PeriodPair.weierstrassCurve_inj`: **period-lattice
  recovery**, a lattice is determined by `g₂` and `g₃`, equivalently by its Weierstrass curve.
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

/-! ### Roots of unity preserving a lattice -/

namespace PeriodPair

variable {L L' : PeriodPair}

/-- The invariants `g₂` and `g₃` depend only on the lattice. -/
private lemma g₂_eq_and_g₃_eq_of_lattice_eq (h : L.lattice = L'.lattice) :
    L.g₂ = L'.g₂ ∧ L.g₃ = L'.g₃ := by
  simp [g₂, g₃, G_eq_of_lattice_eq h]

/-- If `Λ` is homothetic to a lattice preserved by multiplication by `c`, then `Λ` is preserved by
multiplication by `c`. -/
private lemma lattice_smul_eq_self_of_lattice_eq_smul {L₀ : PeriodPair} {c d : ℂˣ}
    (hd : L.lattice = (d • L₀).lattice) (hc : (c • L₀).lattice = L₀.lattice) :
    (c • L).lattice = L.lattice := by
  rw [lattice_smul_eq_of_lattice_eq c hd, ← mul_smul, mul_comm, mul_smul,
    lattice_smul_eq_of_lattice_eq d hc, hd]

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
    rw [Units.val_mk0, IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_prime (by linear_combination ((UpperHalfPlane.ρ : ℂ) - 1) *
      UpperHalfPlane.ρ_sq) fun h ↦ ?_
    simp [UpperHalfPlane.ρ, Complex.ext_iff] at h
  have hρL (c : ℂˣ) (hc : (c : ℂ) ^ 3 = 1) :
      (c • UpperHalfPlane.ρ.periodPair).lattice = UpperHalfPlane.ρ.periodPair.lattice :=
    lattice_smul_eq_self_of_pow_eq_one hρ UpperHalfPlane.lattice_ρ_smul_periodPair_ρ hc
  refine lattice_smul_eq_self_of_lattice_eq_smul hd ?_
  rcases mul_self_eq_one_iff.mp (by linear_combination hc : ((c : ℂ) ^ 3) * (c : ℂ) ^ 3 = 1)
    with h3 | h3
  · exact hρL c h3
  · rw [show c = -1 * -c by rw [neg_one_mul, neg_neg], mul_smul, lattice_neg_one_smul]
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

/-- **Changes of variables between lattice curves are rescalings**: if a change of variables `C`
takes `E_Λ` to `E_{Λ'}`, then `Λ' = u Λ` for the scaling factor `u` of `C`. -/
theorem lattice_eq_smul_of_variableChange_smul_eq {C : VariableChange ℂ}
    (h : C • L.weierstrassCurve = L'.weierstrassCurve) : L'.lattice = (C.u • L).lattice := by
  have : L.weierstrassCurve.IsShortNF := ⟨by simp, by simp, by simp⟩
  have : (C • L.weierstrassCurve).IsShortNF := h ▸ ⟨by simp, by simp, by simp⟩
  have h2 : IsRegular (2 : ℂ) := .of_ne_zero two_ne_zero
  have h3 : IsRegular (3 : ℂ) := .of_ne_zero three_ne_zero
  have h₄ := variableChange_a₄_of_isShortNF L.weierstrassCurve C h2 h3
  have h₆ := variableChange_a₆_of_isShortNF L.weierstrassCurve C h2 h3
  rw [h, weierstrassCurve_a₄, weierstrassCurve_a₄] at h₄
  rw [h, weierstrassCurve_a₆, weierstrassCurve_a₆] at h₆
  refine lattice_eq_iff_g₂_eq_and_g₃_eq.mpr ⟨?_, ?_⟩
  · rw [g₂_smul, div_eq_mul_inv, ← inv_pow, ← Units.val_inv_eq_inv_val]
    linear_combination -4 * h₄
  · rw [g₃_smul, div_eq_mul_inv, ← inv_pow, ← Units.val_inv_eq_inv_val]
    linear_combination -4 * h₆

/-- **A lattice is determined by its Weierstrass curve.** -/
theorem weierstrassCurve_inj : L.weierstrassCurve = L'.weierstrassCurve ↔ L.lattice = L'.lattice :=
  ⟨fun h ↦ by
    simpa [VariableChange.one_def] using
      (lattice_eq_smul_of_variableChange_smul_eq (C := 1) (L' := L') (by rw [one_smul, h])).symm,
    weierstrassCurve_eq_of_lattice_eq⟩

end PeriodPair

/-! ### The period lattice of a complex elliptic curve -/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- Every elliptic curve over `ℂ` is the image of the Weierstrass curve of a lattice under a change
of variables with scaling factor `u = 1`. -/
theorem exists_periodPair_variableChange_smul_eq :
    ∃ (L : PeriodPair) (C : VariableChange ℂ), C.u = 1 ∧ C • L.weierstrassCurve = E := by
  obtain ⟨τ, C, hC⟩ := E.exists_variableChange_smul_weierstrassCurve_periodPair_eq
  refine ⟨C.u • τ.periodPair, C * ⟨C.u, 0, 0, 0⟩⁻¹, ?_, ?_⟩
  · simp [VariableChange.mul_def, VariableChange.inv_def]
  · rw [PeriodPair.weierstrassCurve_smul, mul_smul, inv_smul_smul, hC]

/-- The **period lattice** of an elliptic curve `E` over `ℂ`: the unique lattice `Λ` whose
Weierstrass curve `y² = x³ - (g₂(Λ) / 4) x - g₃(Λ) / 4` is taken to `E` by a change of variables
with scaling factor `u = 1` (`WeierstrassCurve.periodLattice_eq_iff`). The normalization `u = 1`
makes it the lattice of periods of the invariant differential `dx / (2y + a₁x + a₃)` of `E`, which
the point map `z ↦ (℘(z), ℘'(z) / 2)` pulls back to `dz`. -/
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
