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
# The weak Cauchy–Riemann equation on planar domains and half-discs

For a real normed space `V`, a field of real-linear endomorphisms `J : ℂ → V → V →L[ℝ] V` and an
inhomogeneous term `η : ℂ → V → V`, the planar nonlinear Cauchy–Riemann equation for `u : ℂ → V`
is `∂ₛu + J(z, u) ∂ₜu = η(z, u)`, in the coordinate `z = s + it`. Its weak form on a set
`U ⊆ ℂ` is `TauCeti.IsWeakCauchyRiemannOn p U J η u`: `u` is continuous on `U`, it is locally
`Lᵖ` on `U`, and it has a weak derivative `D` on the interior of `U`, locally `Lᵖ` on `U` as
well, with `D z 1 + J z (u z) (D z I) = η z (u z)` for almost every `z` in the interior. As for
`TauCeti.MemWkpLoc`, the `Lᵖ` bounds are taken on the compact subsets of `U` itself, so on a
half-disc, relatively open in the closed upper half-plane, they reach the real axis while the
weak derivative is tested in the interior. On an open set `Ω` the predicate is the usual one
(`TauCeti.isWeakCauchyRiemannOn_iff_of_isOpen`).

This is McDuff–Salamon's normalization: for a constant `J` the left-hand side is twice the
Cauchy–Riemann operator `\bar∂ = (∂ₛ + J ∂ₜ)/2`. No hypothesis on `J` is part of the predicate:
the square identity `J² = -1` and the regularity of `J` and `η` enter only the theorems that use
them, so the linear equations with arbitrary coefficient fields are special cases.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn`: the equation does not depend on
  which weak derivative is used, since weak derivatives agree almost everywhere.
* `TauCeti.isWeakCauchyRiemannOn_iff_of_contDiffOn`: for `u` of class `C¹` on an open set `Ω`,
  with `J` and `η` continuous along `u`, the predicate is the pointwise equation on `Ω` for the
  classical derivative, for every exponent `p`.
* `TauCeti.IsWeakLinearCauchyRiemannOn`: the linear equation `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`, whose
  solutions on any set form a real vector space.
* `TauCeti.isWeakCauchyRiemannOn_id` and `TauCeti.not_isWeakCauchyRiemannOn_conj`: for `J = i`
  the identity solves the homogeneous equation and conjugation does not. Two examples at the end
  of the file show that the swapped expression `D(i) + J D(1)` would reverse these verdicts.
* `TauCeti.isWeakCauchyRiemannOn_const_iff`: a constant `u₀` solves the equation exactly when
  `η(z, u₀) = 0` for almost every `z` in the interior of `U`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p q : ENNReal} {Ω : Opens ℂ} {U U' : Set ℂ}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- The weak nonlinear Cauchy–Riemann equation `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on a set `U`. The
map `u` is continuous on `U`, it is locally `Lᵖ` on `U`, and it has a weak derivative `D` on the
interior of `U` that is locally `Lᵖ` on `U` and satisfies `D z 1 + J z (u z) (D z I) = η z (u z)`
almost everywhere on that interior. The local `Lᵖ` bounds reach the boundary of `U`, as in
`TauCeti.MemWkpLoc`; the intended non-open sets are half-discs, relatively open in the closed
upper half-plane. -/
def IsWeakCauchyRiemannOn (p : ENNReal) (U : Set ℂ) (J : ℂ → V → V →L[ℝ] V)
    (η : ℂ → V → V) (u : ℂ → V) : Prop :=
  ContinuousOn u U ∧ MemLpLoc p U u ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
    HasWeakFDerivOn volume (Opens.interior U) u D ∧ MemLpLoc p U D ∧
      ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z)

/-- The weak equation unfolded into its defining conditions. -/
theorem isWeakCauchyRiemannOn_iff : IsWeakCauchyRiemannOn p U J η u ↔
    ContinuousOn u U ∧ MemLpLoc p U u ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) u D ∧ MemLpLoc p U D ∧
        ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) :=
  Iff.rfl

/-- On an open set `Ω`, the weak derivative and the equation are taken on `Ω` itself. -/
theorem isWeakCauchyRiemannOn_iff_of_isOpen : IsWeakCauchyRiemannOn p (Ω : Set ℂ) J η u ↔
    ContinuousOn u Ω ∧ MemLpLoc p Ω u ∧ ∃ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω u D ∧
      MemLpLoc p Ω D ∧ ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z) :=
  by rw [isWeakCauchyRiemannOn_iff, Opens.interior_coe, Ω.isOpen.interior_eq]

/-! ### Elementary properties -/

namespace IsWeakCauchyRiemannOn

/-- A weak solution is continuous on `U`. -/
theorem continuousOn (h : IsWeakCauchyRiemannOn p U J η u) : ContinuousOn u U := h.1

/-- A weak solution is locally `Lᵖ` on `U`. -/
theorem memLpLoc (h : IsWeakCauchyRiemannOn p U J η u) : MemLpLoc p U u := h.2.1

/-- The codomain of a weak solution is complete, as for every weak derivative. -/
theorem completeSpace (h : IsWeakCauchyRiemannOn p U J η u) : CompleteSpace V := by
  obtain ⟨-, -, D, hD, -⟩ := h
  exact hD.completeSpace

/-- A weak solution belongs to the local Sobolev class `W^{1,p}_loc` of `U`. -/
theorem memWkpLoc_one (h : IsWeakCauchyRiemannOn p U J η u) : MemWkpLoc p U 1 u := by
  obtain ⟨-, hu, D, hD, hDp, -⟩ := h
  exact memWkpLoc_succ_iff.2 ⟨hu, D, hD, memWkpLoc_zero_iff.2 hDp⟩

/-- **Independence of the weak derivative.** The equation holds for every weak derivative of a
weak solution on the interior, since weak derivatives agree almost everywhere. -/
theorem ae_eq_of_hasWeakFDerivOn (h : IsWeakCauchyRiemannOn p U J η u)
    {D : ℂ → ℂ →L[ℝ] V} (hD : HasWeakFDerivOn volume (Opens.interior U) u D) :
    ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) := by
  obtain ⟨-, -, D', hD', -, hae⟩ := h
  filter_upwards [hae, hD'.ae_eq hD] with z hz hDz
  rwa [← hDz]

/-- **Independence of the weak derivative** on an open set. -/
theorem ae_eq_of_hasWeakFDerivOn_of_isOpen (h : IsWeakCauchyRiemannOn p (Ω : Set ℂ) J η u)
    {D : ℂ → ℂ →L[ℝ] V} (hD : HasWeakFDerivOn volume Ω u D) :
    ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 + J z (u z) (D z I) = η z (u z) := by
  have := h.ae_eq_of_hasWeakFDerivOn (D := D) (by rwa [Opens.interior_coe])
  rwa [Ω.isOpen.interior_eq] at this

/-- Restricting a weak solution to a smaller set gives a weak solution. -/
theorem mono (h : IsWeakCauchyRiemannOn p U J η u) (hU : U' ⊆ U) :
    IsWeakCauchyRiemannOn p U' J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc.mono hU, hu.mono_set hU, D, hD.mono (interior_mono hU), hDp.mono_set hU,
    ae_restrict_of_ae_restrict_of_subset (interior_mono hU) hae⟩

/-- Decreasing the exponent preserves weak solutions, since compact sets have finite volume. -/
theorem mono_exponent (h : IsWeakCauchyRiemannOn p U J η u) (hqp : q ≤ p) :
    IsWeakCauchyRiemannOn q U J η u := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := h
  exact ⟨hc, hu.mono_exponent hqp, D, hD, hDp.mono_exponent hqp, hae⟩

end IsWeakCauchyRiemannOn

/-- A weak solution is a continuous map in `W^{1,p}_loc` of `U` for which the equation holds with
every weak derivative on the interior. -/
theorem isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn :
    IsWeakCauchyRiemannOn p U J η u ↔ ContinuousOn u U ∧ MemWkpLoc p U 1 u ∧
      ∀ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume (Opens.interior U) u D →
        ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (u z) (D z I) = η z (u z) := by
  refine ⟨fun h => ⟨h.continuousOn, h.memWkpLoc_one, fun D hD => h.ae_eq_of_hasWeakFDerivOn hD⟩,
    fun ⟨hc, hw, hall⟩ => ?_⟩
  obtain ⟨hu, D, hD, hDp⟩ := memWkpLoc_succ_iff.1 hw
  exact ⟨hc, hu, D, hD, memWkpLoc_zero_iff.1 hDp, hall D hD⟩

/-! ### Comparison with the classical equation -/

section Classical

variable [CompleteSpace V]

/-- A `C¹` map satisfying the classical equation at every point of an open set `Ω` is a weak
solution on `Ω` for every exponent. No regularity of `J` or `η` is needed: the classical
derivative is a weak one. -/
theorem isWeakCauchyRiemannOn_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    (h : ∀ z ∈ (Ω : Set ℂ), fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z)) :
    IsWeakCauchyRiemannOn p Ω J η u := by
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  refine isWeakCauchyRiemannOn_iff_of_isOpen.2 ⟨hu.continuousOn, hu.continuousOn.memLpLoc,
    fderiv ℝ u, hasWeakFDerivOn_of_differentiableOn
      (hdu.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun z hz => (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz),
    hdu.memLpLoc, ?_⟩
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall h)

/-- **The `C¹` comparison.** For `u` of class `C¹` on an open set `Ω`, with `J` and `η`
continuous along `u`, the weak equation for any exponent is the pointwise equation for the
classical derivative at every point of `Ω`. Continuity turns the almost-everywhere identity into
an everywhere one. -/
theorem isWeakCauchyRiemannOn_iff_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    (hJ : ContinuousOn (fun z => J z (u z)) Ω) (hη : ContinuousOn (fun z => η z (u z)) Ω) :
    IsWeakCauchyRiemannOn p Ω J η u ↔
      ∀ z ∈ (Ω : Set ℂ), fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z) := by
  refine ⟨fun h => ?_, isWeakCauchyRiemannOn_of_contDiffOn hu⟩
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hweak : HasWeakFDerivOn volume Ω u (fderiv ℝ u) :=
    hasWeakFDerivOn_of_differentiableOn (hdu.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun z hz => (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hlhs : ContinuousOn (fun z => fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I)) Ω :=
    (hdu.clm_apply continuousOn_const).add (hJ.clm_apply (hdu.clm_apply continuousOn_const))
  exact Measure.eqOn_open_of_ae_eq (h.ae_eq_of_hasWeakFDerivOn_of_isOpen hweak) Ω.isOpen hlhs hη

/-- **Constant maps.** A constant map is a weak solution on `U` exactly when the inhomogeneous
term vanishes at its value for almost every point of the interior of `U`. No hypothesis on `J`
is needed, since the weak derivative of a constant is zero. -/
@[simp]
theorem isWeakCauchyRiemannOn_const_iff (u₀ : V) :
    IsWeakCauchyRiemannOn p U J η (fun _ => u₀) ↔
      ∀ᵐ z ∂volume.restrict (interior U), η z u₀ = 0 := by
  have hweak : HasWeakFDerivOn volume (Opens.interior U) (fun _ : ℂ => u₀) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by
      simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Opens.interior U) (v := v) u₀
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
    IsWeakCauchyRiemannOn p U J (fun _ _ => 0) (fun _ => u₀) :=
  (isWeakCauchyRiemannOn_const_iff u₀).2 (Filter.Eventually.of_forall fun _ => rfl)

end Classical

/-! ### The linear equation -/

/-- The weak linear Cauchy–Riemann equation `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` on `U`, with
coefficient fields `J` and `C` that do not depend on the value of `ξ`. It is the nonlinear
equation with the field `J` and the inhomogeneous term `-C(z) x`. -/
abbrev IsWeakLinearCauchyRiemannOn (p : ENNReal) (U : Set ℂ) (J C : ℂ → V →L[ℝ] V)
    (ξ : ℂ → V) : Prop :=
  IsWeakCauchyRiemannOn p U (fun z _ => J z) (fun z x => -C z x) ξ

variable {A C : ℂ → V →L[ℝ] V} {ξ ξ' : ℂ → V}

/-- The linear equation written out: `D z 1 + J z (D z I) + C z (ξ z) = 0` almost everywhere on
the interior of `U`. -/
theorem isWeakLinearCauchyRiemannOn_iff :
    IsWeakLinearCauchyRiemannOn p U A C ξ ↔ ContinuousOn ξ U ∧ MemLpLoc p U ξ ∧
      ∃ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume (Opens.interior U) ξ D ∧ MemLpLoc p U D ∧
        ∀ᵐ z ∂volume.restrict (interior U), D z 1 + A z (D z I) + C z (ξ z) = 0 := by
  simp only [IsWeakLinearCauchyRiemannOn, isWeakCauchyRiemannOn_iff, add_eq_zero_iff_eq_neg]

namespace IsWeakLinearCauchyRiemannOn

/-- Weak solutions of the linear equation are closed under addition. -/
theorem add (h : IsWeakLinearCauchyRiemannOn p U A C ξ)
    (h' : IsWeakLinearCauchyRiemannOn p U A C ξ') :
    IsWeakLinearCauchyRiemannOn p U A C (ξ + ξ') := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 h
  obtain ⟨hc', hu', D', hD', hDp', hae'⟩ := isWeakLinearCauchyRiemannOn_iff.1 h'
  refine isWeakLinearCauchyRiemannOn_iff.2
    ⟨hc.add hc', hu.add hu', D + D', hD.add hD', hDp.add hDp', ?_⟩
  filter_upwards [hae, hae'] with z hz hz'
  simp only [Pi.add_apply, add_apply, map_add]
  calc _ = (D z 1 + A z (D z I) + C z (ξ z)) + (D' z 1 + A z (D' z I) + C z (ξ' z)) := by abel
    _ = 0 := by rw [hz, hz', add_zero]

/-- Weak solutions of the linear equation are closed under real scalar multiplication. -/
theorem const_smul (h : IsWeakLinearCauchyRiemannOn p U A C ξ) (c : ℝ) :
    IsWeakLinearCauchyRiemannOn p U A C (c • ξ) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 h
  refine isWeakLinearCauchyRiemannOn_iff.2
    ⟨hc.const_smul c, hu.const_smul c, c • D, hD.const_smul c, hDp.const_smul c, ?_⟩
  filter_upwards [hae] with z hz
  simp only [Pi.smul_apply, FunLike.coe_smul, map_smul, ← smul_add, hz, smul_zero]

/-- The zero map solves the linear equation. -/
theorem zero [CompleteSpace V] : IsWeakLinearCauchyRiemannOn p U A C 0 :=
  (isWeakCauchyRiemannOn_const_iff (p := p) (U := U) (J := fun z _ => A z)
    (η := fun z x => -C z x) (0 : V)).2 (Filter.Eventually.of_forall fun z => by simp)

end IsWeakLinearCauchyRiemannOn

/-! ### Checks for the standard structure on `ℂ` -/

section Standard

/-- Conjugation is real-linear, so its derivative applies conjugation. This is the applied form
of `ContinuousLinearEquiv.fderiv` for `conjCLE`, with the coercion of `conjCLE` to `conj`
bridged by `Complex.conjCLE_apply`. -/
private theorem fderiv_conj_apply (z w : ℂ) : fderiv ℝ conj z w = conj w := by
  have hconj : (conj : ℂ → ℂ) = conjCLE := funext fun x => (conjCLE_apply x).symm
  rw [hconj, conjCLE.fderiv, ContinuousLinearEquiv.coe_coe, conjCLE_apply]

/-- The identity solves the homogeneous equation for `J = i`: its derivative is the identity and
`1 + i·i = 0`. -/
theorem isWeakCauchyRiemannOn_id :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0) id :=
  isWeakCauchyRiemannOn_of_contDiffOn contDiff_id.contDiffOn fun z _ => by simp

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
  rw [fderiv_conj_apply, fderiv_conj_apply] at h2
  norm_num [Complex.ext_iff] at h2

-- With the swapped expression `D(i) + J D(1)` in place of `D(1) + J D(i)`, the identity would
-- not be a solution, since `i + i·1 = 2i ≠ 0`.
example (z : ℂ) : fderiv ℝ id z I + (I • ContinuousLinearMap.id ℝ ℂ) (fderiv ℝ id z 1) ≠ 0 := by
  norm_num [Complex.ext_iff]

-- With the swapped expression, conjugation would be a solution, since `-i + i·1 = 0`.
example (z : ℂ) :
    fderiv ℝ conj z I + (I • ContinuousLinearMap.id ℝ ℂ) (fderiv ℝ conj z 1) = 0 := by
  rw [fderiv_conj_apply, fderiv_conj_apply]
  norm_num [Complex.ext_iff]

end Standard

end TauCeti
