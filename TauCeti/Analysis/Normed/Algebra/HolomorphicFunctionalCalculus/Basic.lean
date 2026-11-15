/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ
public import TauCeti.Analysis.Contour.Cycle.Grid
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Cycle

/-!
# The holomorphic germ calculus

For an element `a` of a complex Banach algebra, `holomorphicCalculus a` is a unital
complex-algebra homomorphism from holomorphic germs near its spectrum to the algebra.
Its restrictions to open domains are continuous for the compact-open topology, with an
explicit contour norm bound. It sends the coordinate germ to `a`. Its value is the
normalized resolvent integral over any null-homologous cycle in the holomorphic domain
that avoids the spectrum and winds once around it. Thus it is independent of the
representative, the domain, and the cycle.

The construction first gives `holomorphicCalculusOn a U hU` on holomorphic functions
on an open neighbourhood `U` of the spectrum, then descends along restriction to germs.
Multiplicativity uses two nested grid cycles, not a connectedness assumption on the
spectrum. The zero algebra and its empty spectrum are included. No normalization of
the norm of the identity is assumed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.

The integral identities are those of `TauCeti.Contour.Cycle`; descent uses
`TauCeti.holomorphicGerms.lift`.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped Real Interval

namespace TauCeti

open Contour HolomorphicFunctions

/-- Fix the inherited additive group before using continuity of additive homomorphisms. -/
local instance (U : Opens ℂ) : AddCommGroup (holomorphicFunctions U) := inferInstance

/-- Linear maps use the additive monoid projection of the inherited additive group. -/
local instance (U : Opens ℂ) : AddCommMonoid (holomorphicFunctions U) :=
  (inferInstance : AddCommGroup (holomorphicFunctions U)).toAddCommMonoid

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

private def calculusValue (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) : A :=
  (2 * π * I)⁻¹ • Cycle.integral (fun z => extend f z • resolvent a z)
    ((spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha).choose

private theorem calculusValue_eq_integral (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) (Γ : Cycle)
    (hΓ : Γ.IsIn (U \ spectrum ℂ a)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1) :
    calculusValue a U ha f =
      (2 * π * I)⁻¹ • Cycle.integral (fun z => extend f z • resolvent a z) Γ := by
  obtain ⟨hΓ', hn', hw'⟩ :=
    ((spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha).choose_spec
  exact congrArg ((2 * π * I)⁻¹ • ·)
    (Cycle.integral_smul_resolvent_eq_of_windingNumber_eq U.isOpen
      (differentiableOn_extend f) hΓ' hΓ hn' hn fun z hz => (hw' z hz).trans (hw z hz).symm)

private theorem calculusValue_congr (a : A) {U V : Opens ℂ}
    (hU : spectrum ℂ a ⊆ U) (hV : spectrum ℂ a ⊆ V)
    (f : holomorphicFunctions U) (g : holomorphicFunctions V) (hVU : V ≤ U)
    (hfg : ∀ z : V, f.val (Set.inclusion hVU z) = g.val z) :
    calculusValue a U hU f = calculusValue a V hV g := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one V.isOpen hV
  rw [calculusValue_eq_integral a V hV g Γ hΓ hn hw,
    calculusValue_eq_integral a U hU f Γ
      (Cycle.isIn_iff.mpr fun z hz => ⟨hVU (Cycle.isIn_iff.mp hΓ hz).1,
        (Cycle.isIn_iff.mp hΓ hz).2⟩)
      (hn.mono hVU) hw]
  congr 1
  apply Cycle.integral_congr
  intro z hz
  have hzV := (Cycle.isIn_iff.mp hΓ hz).1
  simp only [extend_apply f ⟨z, hVU hzV⟩, extend_apply g ⟨z, hzV⟩, hfg ⟨z, hzV⟩]

omit [CompleteSpace A] in
private theorem isIn_resolventSet {a : A} {U : Set ℂ} {Γ : Cycle}
    (hΓ : Γ.IsIn (U \ spectrum ℂ a)) : Γ.IsIn (resolventSet ℂ a) :=
  Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2

private theorem continuousOn_calculusIntegrand {a : A} {U : Opens ℂ}
    (f : holomorphicFunctions U) {Γ : Cycle} (hΓ : Γ.IsIn (U \ spectrum ℂ a)) :
    ContinuousOn (fun z => extend f z • resolvent a z) (Cycle.trace Γ) :=
  ((differentiableOn_extend f).continuousOn.mono
    (fun _ hz => (Cycle.isIn_iff.mp hΓ hz).1)).smul
    (Cycle.continuousOn_resolvent (isIn_resolventSet hΓ))

private theorem calculusValue_add (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f g : holomorphicFunctions U) :
    calculusValue a U ha (f + g) = calculusValue a U ha f + calculusValue a U ha g := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [calculusValue_eq_integral a U ha (f + g) Γ hΓ hn hw,
    calculusValue_eq_integral a U ha f Γ hΓ hn hw,
    calculusValue_eq_integral a U ha g Γ hΓ hn hw]
  rw [Cycle.integral_congr (g := fun z => extend f z • resolvent a z +
    extend g z • resolvent a z) (fun z hz => by
      have hzU := (Cycle.isIn_iff.mp hΓ hz).1
      simp [extend_apply _ ⟨z, hzU⟩, add_smul]),
    Cycle.integral_add (continuousOn_calculusIntegrand f hΓ)
      (continuousOn_calculusIntegrand g hΓ), smul_add]

private theorem calculusValue_mul (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f g : holomorphicFunctions U) :
    calculusValue a U ha (f * g) = calculusValue a U ha f * calculusValue a U ha g := by
  obtain ⟨Γ₁, Γ₂, h₁, h₂, hn₁, hn₂, hw₁, hw₂, hd, hw₁₂, hw₂₁⟩ :=
    (spectrum.isCompact a).exists_nested_cycles_windingNumber_eq_one U.isOpen ha
  rw [calculusValue_eq_integral a U ha (f * g) Γ₁ h₁ hn₁ hw₁,
    calculusValue_eq_integral a U ha f Γ₁ h₁ hn₁ hw₁,
    calculusValue_eq_integral a U ha g Γ₂ h₂ hn₂ hw₂, smul_mul_smul_comm,
    Cycle.integral_smul_resolvent_mul_integral_smul_resolvent U.isOpen
      (differentiableOn_extend f) (differentiableOn_extend g)
      h₁ h₂ hn₁ hn₂ hd hw₁₂ hw₂₁, smul_smul]
  have hc : (2 * π * I)⁻¹ * (2 * π * I)⁻¹ * (2 * π * I) = (2 * π * I)⁻¹ := by
    field_simp
  rw [hc]
  congr 1
  apply Cycle.integral_congr
  intro z hz
  have hzU := (Cycle.isIn_iff.mp h₁ hz).1
  simp [extend_apply _ ⟨z, hzU⟩]

private theorem calculusValue_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p : Polynomial ℂ) :
    calculusValue a U ha (of U (fun z => p.eval z) p.differentiable.differentiableOn) =
      Polynomial.aeval a p := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [calculusValue_eq_integral a U ha _ Γ hΓ hn hw,
    Cycle.integral_congr (g := fun z => p.eval z • resolvent a z) (fun z hz => by
      rw [extend_apply _ ⟨z, (Cycle.isIn_iff.mp hΓ hz).1⟩, of_apply]),
    Cycle.integral_eval_smul_resolvent
      (isIn_resolventSet hΓ) hw,
    smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- The holomorphic calculus on an open neighbourhood of the spectrum. Its value is the
normalized resolvent integral; restriction to a smaller neighbourhood does not change it. -/
def holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) :
    holomorphicFunctions U →ₐ[ℂ] A where
  toFun := calculusValue a U ha
  map_zero' := by
    have h : of U (fun _ => 0) (differentiableOn_const _) = 0 := by ext z; simp
    simpa only [Polynomial.eval_zero, map_zero, h] using calculusValue_polynomial a U ha 0
  map_one' := by
    have h : of U (fun _ => 1) (differentiableOn_const _) = 1 := by ext z; simp
    simpa only [Polynomial.eval_one, map_one, h] using calculusValue_polynomial a U ha 1
  map_add' := calculusValue_add a U ha
  map_mul' := calculusValue_mul a U ha
  commutes' c := by
    convert calculusValue_polynomial a U ha (Polynomial.C c) using 1
    · congr 1
      ext z
      simp
    · simp

/-- The calculus on an open neighbourhood agrees with polynomial evaluation. -/
@[simp]
theorem holomorphicCalculusOn_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p : Polynomial ℂ) :
    holomorphicCalculusOn a U ha
      (of U (fun z => p.eval z) p.differentiable.differentiableOn) = Polynomial.aeval a p :=
  calculusValue_polynomial a U ha p

/-- The coordinate function on an open neighbourhood is sent to the specified element. -/
@[simp]
theorem holomorphicCalculusOn_id (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) :
    holomorphicCalculusOn a U ha (of U id differentiableOn_id) = a := by
  have hid : (fun z : ℂ => Polynomial.eval z Polynomial.X) = id := by ext z; simp
  simpa only [hid, Polynomial.aeval_X] using holomorphicCalculusOn_polynomial a U ha Polynomial.X

/-- Contour formula for the calculus on an open domain, for any admissible cycle. -/
theorem holomorphicCalculusOn_eq_integral (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (Γ : Cycle) (hΓ : Γ.IsIn (U \ spectrum ℂ a))
    (hn : Γ.IsNullHomologous U) (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1) :
    holomorphicCalculusOn a U ha f =
      (2 * π * I)⁻¹ • Cycle.integral (fun z => extend f z • resolvent a z) Γ :=
  calculusValue_eq_integral a U ha f Γ hΓ hn hw

/-- The contour bound for the holomorphic calculus. A bound `M` for the function and `R`
for the resolvent on the trace gives their product times the cycle length and `(2π)⁻¹`.
The cycle length is the sum of the generator lengths weighted by absolute coefficients. -/
theorem norm_holomorphicCalculusOn_le (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (Γ : Cycle) (hΓ : Γ.IsIn (U \ spectrum ℂ a))
    (hn : Γ.IsNullHomologous U) (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1)
    {M R : ℝ} (hM : ∀ z ∈ Cycle.trace Γ, ‖extend f z‖ ≤ M)
    (hR : ∀ z ∈ Cycle.trace Γ, ‖resolvent a z‖ ≤ R) :
    ‖holomorphicCalculusOn a U ha f‖ ≤ ‖(2 * π * I)⁻¹‖ *
      ((∑ γ ∈ FreeAbelianGroup.support Γ, |(FreeAbelianGroup.coeff γ Γ : ℝ)| *
        ∫ t in Ι γ.a γ.b, ‖deriv γ t‖) * (M * R)) := by
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw, norm_smul]
  gcongr
  apply Cycle.norm_integral_le_of_norm_le_const
  intro z hz
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hR z hz) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (hM z hz) ((norm_nonneg _).trans (hR z hz)))

/-- On every open neighbourhood of the spectrum the holomorphic calculus is continuous
for uniform convergence on compact subsets. -/
@[continuity]
theorem continuous_holomorphicCalculusOn (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) : Continuous (holomorphicCalculusOn a U ha) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  let := isCompact_iff_compactSpace.mp (Cycle.isCompact_trace Γ)
  let j : C(Cycle.trace Γ, U) :=
    ⟨fun z => ⟨z, (Cycle.isIn_iff.mp hΓ z.property).1⟩,
      continuous_subtype_val.subtype_mk _⟩
  let ρ : holomorphicFunctions U →ₐ[ℂ] C(Cycle.trace Γ, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ j).comp (holomorphicFunctions U).val
  have hρ : Continuous ρ :=
    (ContinuousMap.compRightAlgHom_continuous ℂ ℂ j).comp continuous_subtype_val
  have hρ_apply (f : holomorphicFunctions U) (z : Cycle.trace Γ) :
      ρ f z = f.val ⟨z, (Cycle.isIn_iff.mp hΓ z.property).1⟩ := rfl
  have hres := Cycle.continuousOn_resolvent (isIn_resolventSet hΓ)
  obtain ⟨R, hR⟩ := (Cycle.isCompact_trace Γ).exists_bound_of_continuousOn hres
  let C := ‖(2 * π * I)⁻¹‖ *
    (∑ γ ∈ FreeAbelianGroup.support Γ, |(FreeAbelianGroup.coeff γ Γ : ℝ)| *
      ∫ t in Ι γ.a γ.b, ‖deriv γ t‖) * R
  let : IsTopologicalAddGroup (holomorphicFunctions U) :=
    IsInducing.subtypeVal.isTopologicalAddGroup
      (holomorphicFunctions U).val.toLinearMap.toAddMonoidHom
  apply continuous_of_tendsto_nhds_zero (holomorphicCalculusOn a U ha).toLinearMap.toAddMonoidHom
  apply squeeze_zero_norm (a := fun f => C * ‖ρ f‖)
  · intro f
    have hM : ∀ z ∈ Cycle.trace Γ, ‖extend f z‖ ≤ ‖ρ f‖ := by
      intro z hz
      rw [extend_apply f ⟨z, (Cycle.isIn_iff.mp hΓ hz).1⟩, ← hρ_apply f ⟨z, hz⟩]
      exact (ρ f).norm_coe_le_norm ⟨z, hz⟩
    convert norm_holomorphicCalculusOn_le a U ha f Γ hΓ hn hw hM hR using 1 <;>
      dsimp [C]
    ring
  · simpa only [Function.comp_apply, map_zero, norm_zero, mul_zero] using
      ((continuous_norm.comp hρ).const_mul C).tendsto 0

/-- Shrinking the domain leaves the holomorphic calculus unchanged. -/
@[simp]
theorem holomorphicCalculusOn_restrict (a : A) {U V : Opens ℂ}
    (ha : spectrum ℂ a ⊆ V) (hVU : V ≤ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn a V ha (restrict hVU f) =
      holomorphicCalculusOn a U (ha.trans hVU) f :=
  (calculusValue_congr a (ha.trans hVU) ha f (restrict hVU f) hVU
    (fun z => (restrict_apply hVU f z).symm)).symm

/-- The unital complex-algebra homomorphism evaluating holomorphic germs near the spectrum
at a Banach-algebra element. -/
def holomorphicCalculus (a : A) : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A :=
  holomorphicGerms.lift (holomorphicCalculusOn a)
    (fun _ _ ha hVU f => holomorphicCalculusOn_restrict a ha hVU f)

/-- The germ calculus agrees with the calculus on every open neighbourhood. -/
@[simp]
theorem holomorphicCalculus_toGerm (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculus a (toGerm ha f) = holomorphicCalculusOn a U ha f :=
  holomorphicGerms.lift_toGerm _ _ U ha f

/-- Evaluate a holomorphic representative by integrating over any admissible cycle in its
domain. In particular, the formula depends only on the germ near the spectrum. -/
theorem holomorphicCalculus_ofFun_eq_integral (a : A) {U : Set ℂ} (hU : IsOpen U)
    (ha : spectrum ℂ a ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (Γ : Cycle) (hΓ : Γ.IsIn (U \ spectrum ℂ a)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1) :
    holomorphicCalculus a (holomorphicGerms.ofFun f ((hf.analyticOnNhd hU).mono ha)) =
      (2 * π * I)⁻¹ • Cycle.integral (fun z => f z • resolvent a z) Γ := by
  rw [← toGerm_of (U := ⟨U, hU⟩) ha f hf, holomorphicCalculus_toGerm,
    holomorphicCalculusOn_eq_integral a ⟨U, hU⟩ ha _ Γ hΓ hn hw]
  congr 1
  exact Cycle.integral_congr fun z hz => by
    rw [extend_apply _ ⟨z, (Cycle.isIn_iff.mp hΓ hz).1⟩, of_apply]

/-- The germ calculus agrees with polynomial evaluation. -/
@[simp]
theorem holomorphicCalculus_polynomial (a : A) (p : Polynomial ℂ) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => p.eval z)
        ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))) = Polynomial.aeval a p := by
  rw [← toGerm_of (U := ⊤) (subset_univ _) _ p.differentiable.differentiableOn,
    holomorphicCalculus_toGerm]
  exact holomorphicCalculusOn_polynomial a ⊤ (subset_univ _) p

/-- The coordinate germ is sent to the specified algebra element. -/
@[simp]
theorem holomorphicCalculus_id (a : A) :
    holomorphicCalculus a (holomorphicGerms.ofFun id analyticOnNhd_id) = a := by
  have hid : (fun z : ℂ => Polynomial.eval z Polynomial.X) = id := by ext z; simp
  simpa only [hid, Polynomial.aeval_X] using holomorphicCalculus_polynomial a Polynomial.X

end TauCeti
