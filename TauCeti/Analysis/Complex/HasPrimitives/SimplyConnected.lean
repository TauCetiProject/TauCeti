/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.Analysis.Complex.HasPrimitives.Local
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.SimplyConnected
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace

/-!
# Holomorphic functions on simply connected domains have primitives

Mathlib's `DifferentiableOn.isExactOn_ball` gives a holomorphic function on a disc, with values in
a complete complex normed space, a primitive there. This file extends it to every simply connected
open set `Ω ⊆ ℂ` (`DifferentiableOn.isExactOn_of_isSimplyConnected`), every open set whose
connected components are simply connected
(`DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`), and continuous
conservative functions (`Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`,
`Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn`).

The real `1`-form `v ↦ v • f z` on the open submanifold `Ω` of `ℂ` has a primitive on every disc
in `Ω`, a complex primitive of `f` there having real derivative `v ↦ v • f w` at `w`. A `1`-form
with local primitives on a simply connected manifold has a global primitive
(`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`); near each point of `Ω` this global
primitive differs by a constant from a disc primitive, so its extension to `ℂ` has complex
derivative `f` at every point of `Ω`.

## Main results

* `DifferentiableOn.isExactOn_of_isSimplyConnected`: a holomorphic function on a simply connected
  open subset of `ℂ`, with values in a complete complex normed space, has a primitive there.
* `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: a holomorphic function on
  an open subset of `ℂ` whose connected components are simply connected has a primitive there.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected` and
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: Morera's theorem
  on simply connected open sets and open sets with simply connected components.

## References

* Walter Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11 (a holomorphic function on a
  simply connected plane region has a primitive).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 8, Section 1 (monodromy and primitives on
  simply connected regions).
-/

public section

open Set Metric Filter TopologicalSpace
open scoped Manifold Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti

/-- A complex primitive `h` of `f` on an open set `B ⊆ ℂ` restricts to a primitive, on the part of
an open set `U` lying in `B`, of the real `1`-form `v ↦ v • f z` on `U`. -/
private theorem isPrimitiveOn_restrict_of_hasDerivAt {f h : ℂ → F} {U : Opens ℂ} {B : Set ℂ}
    (hB : IsOpen B) (hh : ∀ w ∈ B, HasDerivAt h (f w) w) :
    IsPrimitiveOn ((RoughForm.flatOneFormEquiv U).symm
        fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ)
      (fun y : U ↦ h y) (Subtype.val ⁻¹' B) := by
  refine ⟨hB.preimage continuous_subtypeVal, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · exact (Manifold.mdifferentiableAt_comp_subtype_val_iff.mpr
      ((hh y hy).hasFDerivAt.restrictScalars ℝ).differentiableAt.mdifferentiableAt)
        |>.mdifferentiableWithinAt
  · ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    have key := RoughForm.flatOneFormEquiv_apply
      (mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun y : U ↦ h y)) y (v 0)
    rw [RoughForm.flatOneFormEquiv_mextDeriv_ofFunction,
      ((hh y hy).hasFDerivAt.restrictScalars ℝ).fderiv] at key
    conv_lhs => rw [hv]
    exact key.symm.trans (RoughForm.flatOneFormEquiv_symm_apply
      (fun z : U ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) y v).symm

end TauCeti

open TauCeti in
/-- **Holomorphic functions on simply connected domains have primitives.** A holomorphic function
on a simply connected open set `Ω ⊆ ℂ`, with values in a complete complex normed space, has a
primitive on `Ω`. This extends `DifferentiableOn.isExactOn_ball` from discs to simply connected
domains. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected [CompleteSpace F] {f : ℂ → F}
    {Ω : Set ℂ} (hf : DifferentiableOn ℂ f Ω) (hΩ : IsOpen Ω) (hΩc : IsSimplyConnected Ω) :
    Complex.IsExactOn f Ω := by
  classical
  let U : Opens ℂ := ⟨Ω, hΩ⟩
  -- the subtype of the open set `U` is the subtype of `Ω`
  have : SimplyConnectedSpace U := hΩc.simplyConnectedSpace
  -- Every point of `Ω` is the centre of a disc in `Ω` carrying a complex primitive of `f`.
  have hdisc (z : ℂ) (hz : z ∈ Ω) :
      ∃ h : ℂ → F, ∃ r > 0, ∀ w ∈ ball z r, HasDerivAt h (f w) w := by
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ z hz
    obtain ⟨h, hh⟩ := (hf.mono hrΩ).isExactOn_ball
    exact ⟨h, r, hr, hh⟩
  choose h r hr hh using hdisc
  have hprim (z : ℂ) (hz : z ∈ Ω) := isPrimitiveOn_restrict_of_hasDerivAt (U := U) isOpen_ball
    (hh z hz)
  -- The real form `v ↦ v • f z` on `U` has a global primitive `G`.
  obtain ⟨G, hG⟩ := exists_isPrimitiveOn_univ_of_simplyConnectedSpace fun x : U ↦
    ⟨_, _, mem_ball_self (hr x x.property), hprim x x.property⟩
  refine ⟨fun z ↦ if hz : z ∈ Ω then G ⟨z, hz⟩ else 0, fun z hz ↦ ?_⟩
  -- Near `z`, the extension of `G` differs by a constant from the disc primitive at `z`.
  have hGz := hG.eventuallyEq_add_const (hprim z hz) (mem_univ ⟨z, hz⟩) (mem_ball_self (hr z hz))
  refine ((hh z hz z (mem_ball_self (hr z hz))).add_const (G ⟨z, hz⟩ - h z hz z))
    |>.congr_of_eventuallyEq ?_
  rw [← hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨z, hz⟩, eventuallyEq_map]
  filter_upwards [hGz] with y hy
  simp only [Function.comp_apply, Subtype.coe_prop, dite_true]
  exact hy

/-- Every holomorphic function on an open subset `s ⊆ ℂ` whose connected components are all simply
connected (with complete coefficients) has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ :=
    TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- **Morera's theorem on simply connected domains.** A continuous function on a simply connected
open subset `s ⊆ ℂ` whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s)
    (hs : IsOpen s) (hsc : IsSimplyConnected s) : Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected hs hsc

/-- A continuous function on an open subset `s ⊆ ℂ` whose connected components are simply connected
and whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    [CompleteSpace F] {f : ℂ → F} {s : Set ℂ} (hf : Complex.IsConservativeOn f s)
    (hfc : ContinuousOn f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected_connectedComponentIn hs hsc
