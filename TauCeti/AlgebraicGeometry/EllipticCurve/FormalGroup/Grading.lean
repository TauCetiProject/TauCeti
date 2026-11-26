/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.StrictVariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Weight
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Grading
public import TauCeti.RingTheory.PowerSeries.Coordinate.Graded

/-!
# Homological homogeneity of Weierstrass formal expansions and coordinate transitions

Building on the formal-group weight theorems in `FormalGroup.Weight` and the pure-scaling laws in
`FormalGroup.VariableChange` (`formalCoordinate_scaling_mul_mul_inv`,
`formalInvariantDifferentialDenom_mk_smul`, `formalW_mk_smul`), this file records `baseGrading`
membership for the universal Weierstrass formal group law, proves weighted and graded homogeneity
of `formalW` and `formalInvariantDifferentialDenom`, and proves gradedness of Weierstrass formal
coordinate transitions (`VariableChange.formalCoordinate_mem_gradedSubgroup`,
`strictFormalCoordinate_mem_gradedSubgroup`).

## Main definitions and results

* `WeierstrassCurve.Universal.coeff_formalGroup_mem_baseGrading`,
  `isWeightedHomogeneous_coeff_formalW`,
  `isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom`,
  `WeierstrassCurve.coeff_formalW_mem`, and
  `WeierstrassCurve.coeff_formalInvariantDifferentialDenom_mem`.
* `WeierstrassCurve.VariableChange.formalCoordinate_mem_gradedSubgroup`,
  `TauCeti.WeierstrassHopfAlgebroid.strictFormalCoordinate_mem_gradedSubgroup`, and
  `TauCeti.WeierstrassHopfAlgebroid.coeff_succ_strictFormalCoordinate_mem_strictArrowGrading`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section

noncomputable section

namespace WeierstrassCurve

/-! ### Homogeneity of Weierstrass formal expansions -/

namespace Universal

open TauCeti.WeierstrassHopfAlgebroid

/-- **Homological homogeneity of the universal Weierstrass formal group law**: the coefficient of
`X^(d 0) Y^(d 1)` lies in `baseGrading (2 * (d 0 + d 1 - 1))`. -/
theorem coeff_formalGroup_mem_baseGrading (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries ∈
      baseGrading (2 * (d.degree - 1)) :=
  mem_baseGrading_two_mul_iff.mpr (isWeightedHomogeneous_coeff_formalGroup d)

/-- The coefficient of `zⁿ` in `formalW Universal.curve` is weighted homogeneous of modular weight
`n - 3` (vanishing for `n < 3`). -/
theorem isWeightedHomogeneous_coeff_formalW (n : ℕ) :
    (PowerSeries.coeff n (formalW Universal.curve)).IsWeightedHomogeneous
      coefficientWeight (n - 3) := by
  rcases lt_or_ge n 3 with hn | hn
  · rw [coeff_formalW, formalWCoeff_eq_zero_of_lt _ hn]
    exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [Nat.add_sub_cancel]
    refine isWeightedHomogeneous_iff_forall_specialize_mk_smul.2 fun R _ W u ↦ ?_
    simp only [← PowerSeries.coeff_map, ← map_formalW, map_specialize, formalW_mk_smul,
      PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul, pow_add]
    linear_combination PowerSeries.coeff (m + 3) (formalW W) * (↑u⁻¹ : R) ^ m *
      pow_mul_pow_eq_one 3 u.mul_inv

/-- The coefficient of `zⁿ` in `Universal.curve.formalInvariantDifferentialDenom` is weighted
homogeneous of modular weight `n`. -/
theorem isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom (n : ℕ) :
    (PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom).IsWeightedHomogeneous
      coefficientWeight n :=
  isWeightedHomogeneous_iff_forall_specialize_mk_smul.2 fun _ _ W u ↦ by
    simp only [← PowerSeries.coeff_map, ← map_formalInvariantDifferentialDenom, map_specialize,
      formalInvariantDifferentialDenom_mk_smul, PowerSeries.coeff_rescale]

end Universal

section GradedWeierstrassCurve

variable {A ι σ : Type*} [CommRing A] [AddCommMonoid ι] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ι → σ} [SetLike.GradedMonoid 𝒜] {W : WeierstrassCurve A} {w : ι}
  (h₁ : W.a₁ ∈ 𝒜 w) (h₂ : W.a₂ ∈ 𝒜 (2 • w)) (h₃ : W.a₃ ∈ 𝒜 (3 • w))
  (h₄ : W.a₄ ∈ 𝒜 (4 • w)) (h₆ : W.a₆ ∈ 𝒜 (6 • w))
include h₁ h₂ h₃ h₄ h₆

/-- If the coefficient `aᵢ` of `W` has degree `i • w`, then the coefficient of `zⁿ` in `formalW W`
has degree `(n - 3) • w`. -/
theorem coeff_formalW_mem (n : ℕ) : PowerSeries.coeff n (formalW W) ∈ 𝒜 ((n - 3) • w) := by
  rw [← W.map_specialize, map_formalW, PowerSeries.coeff_map]
  exact W.specialize_mem h₁ h₂ h₃ h₄ h₆ (Universal.isWeightedHomogeneous_coeff_formalW n)

/-- If the coefficient `aᵢ` of `W` has degree `i • w`, then the coefficient of `zⁿ` in
`W.formalInvariantDifferentialDenom` has degree `n • w`. -/
theorem coeff_formalInvariantDifferentialDenom_mem (n : ℕ) :
    PowerSeries.coeff n W.formalInvariantDifferentialDenom ∈ 𝒜 (n • w) := by
  rw [← W.map_specialize, map_formalInvariantDifferentialDenom, PowerSeries.coeff_map]
  exact W.specialize_mem h₁ h₂ h₃ h₄ h₆
    (Universal.isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom n)

end GradedWeierstrassCurve

namespace VariableChange

/-- If `W` has homogeneous Weierstrass coefficients of degrees `w * i` and `C = (u, r, s, t)` has
`u ∈ 𝒜 0`, `r ∈ 𝒜 (w * 2)`, `s ∈ 𝒜 w`, `t ∈ 𝒜 (w * 3)`, then `C.formalCoordinate W` lies in
`FormalCoordinate.gradedSubgroup 𝒜 w`. -/
theorem formalCoordinate_mem_gradedSubgroup {B σ : Type*} [CommRing B] [SetLike σ B]
    [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ) {W : WeierstrassCurve B}
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i))
    {C : VariableChange B} (hu : (C.u : B) ∈ 𝒜 0) (hr : C.r ∈ 𝒜 (w * 2)) (hs : C.s ∈ 𝒜 w)
    (ht : C.t ∈ 𝒜 (w * 3)) :
    C.formalCoordinate W ∈ TauCeti.FormalCoordinate.gradedSubgroup 𝒜 w := by
  rw [TauCeti.FormalCoordinate.mem_gradedSubgroup,
    ← TauCeti.FormalCoordinate.map_toLaurent_eq_conjugate_iff, ← map_formalCoordinate,
    map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv 𝒜 w hu hr hs ht,
    WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling 𝒜 w hW,
    formalCoordinate_scaling_mul_mul_inv, map_formalCoordinate]
  simp

end VariableChange

end WeierstrassCurve

/-! ### The universal strict formal coordinate transition over `A[r, s, t]` -/

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve

/-- **Homological homogeneity of the universal strict Weierstrass formal coordinate**. -/
theorem strictFormalCoordinate_mem_gradedSubgroup :
    strictFormalCoordinate ∈ TauCeti.FormalCoordinate.gradedSubgroup strictArrowGrading 2 := by
  rw [strictFormalCoordinate_def]
  refine Subgroup.inv_mem _ (VariableChange.formalCoordinate_mem_gradedSubgroup strictArrowGrading 2
    (fun i ↦ ?_) (by simpa using SetLike.one_mem_graded strictArrowGrading)
    (by simp) (by simp) (by simp))
  rw [WeierstrassCurve.specialize_map, Universal.specialize_curve]
  exact strictLeftUnit_mem_strictArrowGrading (X_mem_baseGrading i)

/-- The coefficient of `z^(i + 1)` in `strictFormalCoordinate` lies in
`strictArrowGrading (2 * i)`. -/
theorem coeff_succ_strictFormalCoordinate_mem_strictArrowGrading (i : ℕ+) :
    PowerSeries.coeff (i + 1) strictFormalCoordinate.toPowerSeries ∈
      strictArrowGrading (2 * (i : ℕ)) := by
  simpa using
    (TauCeti.FormalCoordinate.mem_gradedSubgroup strictArrowGrading 2 strictFormalCoordinate).mp
      strictFormalCoordinate_mem_gradedSubgroup (i + 1)

end TauCeti.WeierstrassHopfAlgebroid
