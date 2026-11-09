/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The weak Cauchy–Riemann equation on planar domains

For a real normed space `V`, a field of real-linear endomorphisms `J : ℂ → V → V →L[ℝ] V` and an
inhomogeneous term `η : ℂ → V → V`, the planar nonlinear Cauchy–Riemann equation for `u : ℂ → V`
is `∂ₛu + J(z, u) ∂ₜu = η(z, u)`, in the coordinate `z = s + it`. Its weak form is

* `TauCeti.IsWeakCauchyRiemannOn p Ω J η u`, for an open set `Ω`: `u` is continuous on `Ω`, it is
  locally `Lᵖ` there, and it has a weak derivative `D` on `Ω`, locally `Lᵖ` as well, with
  `D z 1 + J z (u z) (D z I) = η z (u z)` for almost every `z ∈ Ω`;
* `TauCeti.IsWeakCauchyRiemannUpToBoundaryOn p U J η u`, for an arbitrary set `U`: the same,
  with the weak derivative and the equation taken on the interior of `U` and the `Lᵖ` bounds on
  the compact subsets of `U` itself, as in `TauCeti.MemWkpLoc`. The intended sets are half-discs,
  relatively open in the closed upper half-plane, where these bounds reach the real axis; no
  such hypothesis is imposed. On an open set the two predicates agree.

This is McDuff–Salamon's normalization: for a constant `J` the left-hand side is twice the
Cauchy–Riemann operator `\bar∂ = (∂ₛ + J ∂ₜ)/2`. No hypothesis on `J` is part of the predicates:
the square identity `J² = -1` and the regularity of `J` and `η` enter only the theorems that use
them, so the linear equations with arbitrary coefficient fields are special cases.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn`: the equation does not depend on
  which weak derivative is used, since weak derivatives agree almost everywhere.
* `TauCeti.isWeakCauchyRiemannOn_iff_of_contDiffOn`: for `u` of class `C¹` on `Ω`, with `J` and
  `η` continuous along `u`, the predicate is the pointwise equation on `Ω` for the classical
  derivative, for every exponent `p`.
* `TauCeti.IsWeakLinearCauchyRiemannOn`: the linear equation `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`, whose
  solutions form a real vector space.
* `TauCeti.isWeakCauchyRiemannOn_id` and `TauCeti.not_isWeakCauchyRiemannOn_conj`: for `J = i`
  the identity solves the homogeneous equation and conjugation does not. Two examples at the end
  of the file show that the swapped expression `D(i) + J D(1)` would reverse these verdicts.
* `TauCeti.isWeakCauchyRiemannOn_const_iff`: a constant `u₀` solves the equation exactly when
  `η(z, u₀) = 0` for almost every `z ∈ Ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p q : ENNReal} {Ω Ω' : Opens ℂ} {U U' : Set ℂ}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- The weak nonlinear Cauchy–Riemann equation `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on an open set `Ω`.
The map `u` is continuous on `Ω`, it and a weak derivative `D` of it on `Ω` are locally `Lᵖ`,
and `D z 1 + J z (u z) (D z I) = η z (u z)` for almost every `z ∈ Ω`. -/
def IsWeakCauchyRiemannOn (p : ENNReal) (Ω : Opens ℂ) (J : ℂ → V → V →L[ℝ] V)
    (η : ℂ → V → V) (u : ℂ → V) : Prop :=
  ContinuousOn u Ω ∧ MemLpLoc p Ω u ∧ ∃ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω u D ∧
    MemLpLoc p Ω D ∧ ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z)

/-- The weak nonlinear Cauchy–Riemann equation up to the boundary of a set `U`. The intended
sets are half-discs, relatively open in the closed upper half-plane, but none is required. The map
`u` is continuous on `U`, it is locally `Lᵖ` on `U`, and it has a weak derivative `D` on the
interior of `U` that is locally `Lᵖ` on `U` and satisfies `D z 1 + J z (u z) (D z I) = η z (u z)`
almost everywhere on that interior. The local `Lᵖ` bounds reach the boundary, as in
`TauCeti.MemWkpLoc`. -/
def IsWeakCauchyRiemannUpToBoundaryOn (p : ENNReal) (U : Set ℂ) (J : ℂ → V → V →L[ℝ] V)
    (η : ℂ → V → V) (u : ℂ → V) : Prop :=
  ContinuousOn u U ∧ MemLpLoc p U u ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
    HasWeakFDerivOn volume (Opens.interior U) u D ∧ MemLpLoc p U D ∧
      ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z)

/-- The open-set weak equation unfolded into its defining conditions. -/
theorem isWeakCauchyRiemannOn_iff : IsWeakCauchyRiemannOn p Ω J η u ↔
    ContinuousOn u Ω ∧ MemLpLoc p Ω u ∧ ∃ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω u D ∧
      MemLpLoc p Ω D ∧ ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z) :=
  Iff.rfl

/-- The weak equation up to the boundary unfolded into its defining conditions. -/
theorem isWeakCauchyRiemannUpToBoundaryOn_iff : IsWeakCauchyRiemannUpToBoundaryOn p U J η u ↔
    ContinuousOn u U ∧ MemLpLoc p U u ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) u D ∧ MemLpLoc p U D ∧
        ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) :=
  Iff.rfl

/-! ### Elementary properties -/

namespace IsWeakCauchyRiemannOn

/-- A weak solution is continuous on the domain. -/
theorem continuousOn (h : IsWeakCauchyRiemannOn p Ω J η u) : ContinuousOn u Ω := h.1

/-- A weak solution is locally `Lᵖ` on the domain. -/
theorem memLpLoc (h : IsWeakCauchyRiemannOn p Ω J η u) : MemLpLoc p Ω u := h.2.1

/-- A weak solution belongs to the local Sobolev class `W^{1,p}_loc` of the domain. -/
theorem memWkpLoc_one (h : IsWeakCauchyRiemannOn p Ω J η u) : MemWkpLoc p Ω 1 u := by
  obtain ⟨-, hu, D, hD, hDp, -⟩ := h
  exact memWkpLoc_succ_iff_of_isOpen.2 ⟨hu, D, hD, memWkpLoc_zero_iff.2 hDp⟩

/-- The codomain of a weak solution is complete, as for every weak derivative. -/
theorem completeSpace (h : IsWeakCauchyRiemannOn p Ω J η u) : CompleteSpace V := by
  obtain ⟨-, -, D, hD, -⟩ := h
  exact hD.completeSpace

/-- **Independence of the weak derivative.** The equation holds for every weak derivative of a
weak solution, since weak derivatives agree almost everywhere. -/
theorem ae_eq_of_hasWeakFDerivOn (h : IsWeakCauchyRiemannOn p Ω J η u)
    {D : ℂ → ℂ →L[ℝ] V} (hD : HasWeakFDerivOn volume Ω u D) :
    ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z) := by
  obtain ⟨-, -, D', hD', -, hae⟩ := h
  filter_upwards [hae, hD'.ae_eq hD] with z hz hDz
  rwa [← hDz]

/-- Restricting a weak solution to a smaller open set gives a weak solution. -/
theorem mono (h : IsWeakCauchyRiemannOn p Ω J η u) (hΩ : Ω' ≤ Ω) :
    IsWeakCauchyRiemannOn p Ω' J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc.mono hΩ, hu.mono_set hΩ, D, hD.mono hΩ, hDp.mono_set hΩ,
    ae_restrict_of_ae_restrict_of_subset hΩ hae⟩

/-- Decreasing the exponent preserves weak solutions, since compact sets have finite volume. -/
theorem mono_exponent (h : IsWeakCauchyRiemannOn p Ω J η u) (hqp : q ≤ p) :
    IsWeakCauchyRiemannOn q Ω J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc, hu.mono_exponent hqp, D, hD, hDp.mono_exponent hqp, hae⟩

/-- An open-set weak solution is a weak solution up to the boundary of the same set. -/
theorem isWeakCauchyRiemannUpToBoundaryOn (h : IsWeakCauchyRiemannOn p Ω J η u) :
    IsWeakCauchyRiemannUpToBoundaryOn p (Ω : Set ℂ) J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  refine ⟨hc, hu, D, ?_, hDp, ?_⟩
  · rwa [Opens.interior_coe]
  · rwa [Ω.isOpen.interior_eq]

end IsWeakCauchyRiemannOn

/-- A weak solution is a continuous `W^{1,p}_loc` map for which the equation holds with every
weak derivative. -/
theorem isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn :
    IsWeakCauchyRiemannOn p Ω J η u ↔ ContinuousOn u Ω ∧ MemWkpLoc p Ω 1 u ∧
      ∀ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω u D →
        ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z) := by
  refine ⟨fun h => ⟨h.continuousOn, h.memWkpLoc_one, fun D hD => h.ae_eq_of_hasWeakFDerivOn hD⟩,
    fun ⟨hc, hw, hall⟩ => ?_⟩
  obtain ⟨hu, D, hD, hDp⟩ := memWkpLoc_succ_iff_of_isOpen.1 hw
  exact ⟨hc, hu, D, hD, memWkpLoc_zero_iff.1 hDp, hall D hD⟩

namespace IsWeakCauchyRiemannUpToBoundaryOn

/-- A weak solution up to the boundary is continuous on `U`. -/
theorem continuousOn (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) : ContinuousOn u U := h.1

/-- A weak solution up to the boundary is locally `Lᵖ` on `U`. -/
theorem memLpLoc (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) : MemLpLoc p U u := h.2.1

/-- The codomain of a weak solution up to the boundary is complete. -/
theorem completeSpace (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) : CompleteSpace V := by
  obtain ⟨-, -, D, hD, -⟩ := h
  exact hD.completeSpace

/-- A weak solution up to the boundary belongs to `W^{1,p}_loc` up to the boundary. -/
theorem memWkpLoc_one (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) : MemWkpLoc p U 1 u := by
  obtain ⟨-, hu, D, hD, hDp, -⟩ := h
  exact memWkpLoc_succ_iff.2 ⟨hu, D, hD, memWkpLoc_zero_iff.2 hDp⟩

/-- **Independence of the weak derivative**, up to the boundary. -/
theorem ae_eq_of_hasWeakFDerivOn (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u)
    {D : ℂ → ℂ →L[ℝ] V} (hD : HasWeakFDerivOn volume (Opens.interior U) u D) :
    ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) := by
  obtain ⟨-, -, D', hD', -, hae⟩ := h
  filter_upwards [hae, hD'.ae_eq hD] with z hz hDz
  rwa [← hDz]

/-- Restricting a weak solution up to the boundary to a smaller set preserves it. -/
theorem mono (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) (hU : U' ⊆ U) :
    IsWeakCauchyRiemannUpToBoundaryOn p U' J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc.mono hU, hu.mono_set hU, D, hD.mono (interior_mono hU), hDp.mono_set hU,
    ae_restrict_of_ae_restrict_of_subset (interior_mono hU) hae⟩

/-- Decreasing the exponent preserves weak solutions up to the boundary. -/
theorem mono_exponent (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) (hqp : q ≤ p) :
    IsWeakCauchyRiemannUpToBoundaryOn q U J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc, hu.mono_exponent hqp, D, hD, hDp.mono_exponent hqp, hae⟩

/-- A weak solution up to the boundary of `U` is a weak solution on the interior of `U`. -/
theorem isWeakCauchyRiemannOn_interior (h : IsWeakCauchyRiemannUpToBoundaryOn p U J η u) :
    IsWeakCauchyRiemannOn p (Opens.interior U) J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc.mono interior_subset, hu.mono_set interior_subset, D, hD,
    hDp.mono_set interior_subset, hae⟩

end IsWeakCauchyRiemannUpToBoundaryOn

/-- A weak solution up to the boundary is a continuous map in `W^{1,p}_loc` up to the boundary
for which the equation holds with every weak derivative on the interior. -/
theorem isWeakCauchyRiemannUpToBoundaryOn_iff_forall_hasWeakFDerivOn :
    IsWeakCauchyRiemannUpToBoundaryOn p U J η u ↔ ContinuousOn u U ∧ MemWkpLoc p U 1 u ∧
      ∀ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume (Opens.interior U) u D →
        ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) := by
  refine ⟨fun h => ⟨h.continuousOn, h.memWkpLoc_one, fun D hD => h.ae_eq_of_hasWeakFDerivOn hD⟩,
    fun ⟨hc, hw, hall⟩ => ?_⟩
  obtain ⟨hu, D, hD, hDp⟩ := memWkpLoc_succ_iff.1 hw
  exact ⟨hc, hu, D, hD, memWkpLoc_zero_iff.1 hDp, hall D hD⟩

/-- On an open set, the weak equation up to the boundary is the open-set weak equation. -/
@[simp]
theorem isWeakCauchyRiemannUpToBoundaryOn_coe_iff :
    IsWeakCauchyRiemannUpToBoundaryOn p (Ω : Set ℂ) J η u ↔ IsWeakCauchyRiemannOn p Ω J η u :=
  ⟨fun h => by simpa only [Opens.interior_coe] using h.isWeakCauchyRiemannOn_interior,
    IsWeakCauchyRiemannOn.isWeakCauchyRiemannUpToBoundaryOn⟩

/-! ### Comparison with the classical equation -/

section Classical

variable [CompleteSpace V]

/-- **The `C¹` comparison.** For `u` of class `C¹` on `Ω`, with `J` and `η` continuous along `u`,
the weak equation for any exponent is the pointwise equation for the classical derivative at
every point of `Ω`. Continuity turns the almost-everywhere identity into an everywhere one. -/
theorem isWeakCauchyRiemannOn_iff_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    (hJ : ContinuousOn (fun z => J z (u z)) Ω) (hη : ContinuousOn (fun z => η z (u z)) Ω) :
    IsWeakCauchyRiemannOn p Ω J η u ↔
      ∀ z ∈ (Ω : Set ℂ), fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z) := by
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hdiff : ∀ z ∈ (Ω : Set ℂ), DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hweak : HasWeakFDerivOn volume Ω u (fderiv ℝ u) :=
    hasWeakFDerivOn_of_differentiableOn (hdu.locallyIntegrableOn Ω.isOpen.measurableSet) hdiff
  have hlhs : ContinuousOn (fun z => fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I)) Ω :=
    (hdu.clm_apply continuousOn_const).add (hJ.clm_apply (hdu.clm_apply continuousOn_const))
  constructor
  · intro h
    exact Measure.eqOn_open_of_ae_eq (h.ae_eq_of_hasWeakFDerivOn hweak) Ω.isOpen hlhs hη
  · intro h
    refine ⟨hu.continuousOn, hu.continuousOn.memLpLoc, fderiv ℝ u, hweak, hdu.memLpLoc, ?_⟩
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall h)

/-- A `C¹` map satisfying the classical equation on `Ω` is a weak solution for every exponent. -/
theorem isWeakCauchyRiemannOn_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    (hJ : ContinuousOn (fun z => J z (u z)) Ω) (hη : ContinuousOn (fun z => η z (u z)) Ω)
    (h : ∀ z ∈ (Ω : Set ℂ), fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z)) :
    IsWeakCauchyRiemannOn p Ω J η u :=
  (isWeakCauchyRiemannOn_iff_of_contDiffOn hu hJ hη).2 h

/-- **Constant maps.** A constant map is a weak solution exactly when the inhomogeneous term
vanishes at its value for almost every point of `Ω`. No hypothesis on `J` is needed, since the
weak derivative of a constant is zero. -/
@[simp]
theorem isWeakCauchyRiemannOn_const_iff (u₀ : V) :
    IsWeakCauchyRiemannOn p Ω J η (fun _ => u₀) ↔
      ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), η z u₀ = 0 := by
  have hweak : HasWeakFDerivOn volume Ω (fun _ : ℂ => u₀) 0 := hasWeakFDerivOn_iff.2 fun v => by
    simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := v) u₀
  constructor
  · intro h
    filter_upwards [h.ae_eq_of_hasWeakFDerivOn hweak] with z hz
    simpa using hz.symm
  · intro h
    refine ⟨continuousOn_const, memLpLoc_const u₀, 0, hweak, memLpLoc_zero, ?_⟩
    filter_upwards [h] with z hz
    simp [hz]

/-- Constant maps solve the homogeneous equation for every `J`. -/
theorem isWeakCauchyRiemannOn_const (u₀ : V) :
    IsWeakCauchyRiemannOn p Ω J (fun _ _ => 0) (fun _ => u₀) :=
  (isWeakCauchyRiemannOn_const_iff u₀).2 (Filter.Eventually.of_forall fun _ => rfl)

end Classical

/-! ### The linear equation -/

/-- The weak linear Cauchy–Riemann equation `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` on `Ω`, with
coefficient fields `J` and `C` that do not depend on the value of `ξ`. It is the nonlinear
equation with the field `J` and the inhomogeneous term `-C(z) x`. -/
abbrev IsWeakLinearCauchyRiemannOn (p : ENNReal) (Ω : Opens ℂ) (J C : ℂ → V →L[ℝ] V)
    (ξ : ℂ → V) : Prop :=
  IsWeakCauchyRiemannOn p Ω (fun z _ => J z) (fun z x => -C z x) ξ

variable {A C : ℂ → V →L[ℝ] V} {ξ ξ' : ℂ → V}

/-- The linear equation written out: `D z 1 + J z (D z I) + C z (ξ z) = 0` almost everywhere. -/
theorem isWeakLinearCauchyRiemannOn_iff :
    IsWeakLinearCauchyRiemannOn p Ω A C ξ ↔ ContinuousOn ξ Ω ∧ MemLpLoc p Ω ξ ∧
      ∃ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω ξ D ∧ MemLpLoc p Ω D ∧
        ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + A z (D z I) + C z (ξ z) = 0 := by
  simp only [IsWeakLinearCauchyRiemannOn, IsWeakCauchyRiemannOn, add_eq_zero_iff_eq_neg]

namespace IsWeakLinearCauchyRiemannOn

/-- Weak solutions of the linear equation are closed under addition. -/
theorem add (h : IsWeakLinearCauchyRiemannOn p Ω A C ξ)
    (h' : IsWeakLinearCauchyRiemannOn p Ω A C ξ') :
    IsWeakLinearCauchyRiemannOn p Ω A C (ξ + ξ') := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 h
  obtain ⟨hc', hu', D', hD', hDp', hae'⟩ := isWeakLinearCauchyRiemannOn_iff.1 h'
  refine isWeakLinearCauchyRiemannOn_iff.2
    ⟨hc.add hc', hu.add hu', D + D', hD.add hD', hDp.add hDp', ?_⟩
  filter_upwards [hae, hae'] with z hz hz'
  simp only [Pi.add_apply, add_apply, map_add]
  calc _ = (D z 1 + A z (D z I) + C z (ξ z)) + (D' z 1 + A z (D' z I) + C z (ξ' z)) := by abel
    _ = 0 := by rw [hz, hz', add_zero]

/-- Weak solutions of the linear equation are closed under real scalar multiplication. -/
theorem const_smul (h : IsWeakLinearCauchyRiemannOn p Ω A C ξ) (c : ℝ) :
    IsWeakLinearCauchyRiemannOn p Ω A C (c • ξ) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 h
  refine isWeakLinearCauchyRiemannOn_iff.2
    ⟨hc.const_smul c, hu.const_smul c, c • D, hD.const_smul c, hDp.const_smul c, ?_⟩
  filter_upwards [hae] with z hz
  simp only [Pi.smul_apply, FunLike.coe_smul, map_smul, ← smul_add, hz, smul_zero]

/-- The zero map solves the linear equation. -/
theorem zero [CompleteSpace V] : IsWeakLinearCauchyRiemannOn p Ω A C 0 := by
  exact (isWeakCauchyRiemannOn_const_iff (p := p) (Ω := Ω) (J := fun z _ => A z)
    (η := fun z x => -C z x) (0 : V)).2 (Filter.Eventually.of_forall fun z => by simp)

end IsWeakLinearCauchyRiemannOn

/-! ### Checks for the standard structure on `ℂ` -/

section Standard

/-- Conjugation is real-linear, so it is its own derivative. -/
private theorem fderiv_conj_eq (z : ℂ) : fderiv ℝ conj z = conjCLE.toContinuousLinearMap :=
  conjCLE.fderiv

/-- The identity solves the homogeneous equation for `J = i`: its derivative is the identity and
`1 + i·i = 0`. -/
theorem isWeakCauchyRiemannOn_id :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0) id :=
  isWeakCauchyRiemannOn_of_contDiffOn contDiff_id.contDiffOn continuousOn_const
    continuousOn_const fun z _ => by simp

/-- Conjugation does not solve the homogeneous equation for `J = i` on a nonempty open set: its
derivative is conjugation, and `1 + i·(-i) = 2 ≠ 0`. -/
theorem not_isWeakCauchyRiemannOn_conj (hΩ : (Ω : Set ℂ).Nonempty) :
    ¬IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
      conj := by
  have hc : ContDiffOn ℝ 1 (conj : ℂ → ℂ) Ω := conjCLE.contDiff.contDiffOn
  rw [isWeakCauchyRiemannOn_iff_of_contDiffOn hc continuousOn_const continuousOn_const]
  obtain ⟨z, hz⟩ := hΩ
  intro h
  have h2 := h z hz
  rw [fderiv_conj_eq] at h2
  norm_num [Complex.ext_iff] at h2

-- With the swapped expression `D(i) + J D(1)` in place of `D(1) + J D(i)`, the identity would
-- not be a solution, since `i + i·1 = 2i ≠ 0`.
example (z : ℂ) : fderiv ℝ id z I + (I • ContinuousLinearMap.id ℝ ℂ) (fderiv ℝ id z 1) ≠ 0 := by
  norm_num [Complex.ext_iff]

-- With the swapped expression, conjugation would be a solution, since `-i + i·1 = 0`.
example (z : ℂ) :
    fderiv ℝ conj z I + (I • ContinuousLinearMap.id ℝ ℂ) (fderiv ℝ conj z 1) = 0 := by
  rw [fderiv_conj_eq]
  norm_num [Complex.ext_iff]

end Standard

end TauCeti
