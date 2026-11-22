/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

This file also establishes the core algebraic and functorial properties—commutation, naturality,
and scalar specialization from the contour definition, together with character evaluation and
resolvent/rational evaluation formulas as algebraic consequences of coordinate evaluation (via
`AlgHom.map_holomorphicGermsOfFun_*`):
* **Commutation**: every element commuting with `a` commutes with `f(a)`, and values of the
  calculus at commuting elements commute with one another.
* **Naturality**: continuous unital complex-algebra homomorphisms and equivalences commute with
  `holomorphicCalculusOn` and `holomorphicCalculus`.
* **Resolvent kernels and rational functions**: `holomorphicCalculus a` evaluates `(w - ·)⁻¹` to
  `resolvent a w` for `w ∉ spectrum ℂ a` (and `holomorphicCalculusOn a U ha` does so for `w ∉ U`),
  and sends reciprocals, quotients `f(z) / g(z)`, and rational functions `p(z) / q(z)` (with
  denominator nonvanishing on `spectrum ℂ a`) to `f(a)⁻¹`, `f(a) g(a)⁻¹`, and `p(a) q(a)⁻¹`.
* **Scalar specialization**: on `ℂ`, the calculus is point evaluation, so any complex character on
  a Banach algebra evaluates the calculus by point evaluation at the character value.

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
    ((spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha).choose

private theorem calculusValue_eq_integral (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) (Γ : Cycle)
    (hΓ : Γ.IsIn (U \ spectrum ℂ a)) (hn : Γ.IsNullHomologous U)
    (hw : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ = 1) :
    calculusValue a U ha f =
      (2 * π * I)⁻¹ • Cycle.integral (fun z => extend f z • resolvent a z) Γ := by
  obtain ⟨hΓ', hn', hw'⟩ :=
    ((spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha).choose_spec
  exact congrArg ((2 * π * I)⁻¹ • ·)
    (Cycle.integral_smul_resolvent_eq_of_windingNumber_eq U.isOpen
      (differentiableOn_extend f) hΓ' hΓ hn' hn fun z hz => (hw' z hz).trans (hw z hz).symm)

private theorem calculusValue_congr (a : A) {U V : Opens ℂ}
    (hU : spectrum ℂ a ⊆ U) (hV : spectrum ℂ a ⊆ V)
    (f : holomorphicFunctions U) (g : holomorphicFunctions V) (hVU : V ≤ U)
    (hfg : ∀ z : V, f.val (Set.inclusion hVU z) = g.val z) :
    calculusValue a U hU f = calculusValue a V hV g := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one V.isOpen hV
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
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha
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
    (spectrum.isCompact ℂ a).exists_nested_cycles_windingNumber_eq_one U.isOpen ha
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
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha
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
      ((∑ γ ∈ FreeAddCommGroup.support Γ, |(FreeAddCommGroup.coeff γ Γ : ℝ)| *
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
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha
  let := isCompact_iff_compactSpace.mp (Cycle.isCompact_trace Γ)
  let j : C(Cycle.trace Γ, U) :=
    ⟨fun z => ⟨z, (Cycle.isIn_iff.mp hΓ z.property).1⟩,
      continuous_subtypeVal.subtype_mk _⟩
  let ρ : holomorphicFunctions U →ₐ[ℂ] C(Cycle.trace Γ, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ j).comp (holomorphicFunctions U).val
  have hρ : Continuous ρ :=
    (ContinuousMap.compRightAlgHom_continuous ℂ ℂ j).comp continuous_subtypeVal
  have hρ_apply (f : holomorphicFunctions U) (z : Cycle.trace Γ) :
      ρ f z = f.val ⟨z, (Cycle.isIn_iff.mp hΓ z.property).1⟩ := rfl
  have hres := Cycle.continuousOn_resolvent (isIn_resolventSet hΓ)
  obtain ⟨R, hR⟩ := (Cycle.isCompact_trace Γ).exists_bound_of_continuousOn hres
  let C := ‖(2 * π * I)⁻¹‖ *
    (∑ γ ∈ FreeAddCommGroup.support Γ, |(FreeAddCommGroup.coeff γ Γ : ℝ)| *
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

/-- The coordinate germ is sent to the specified algebra element. -/
@[simp]
theorem holomorphicCalculus_id (a : A) :
    holomorphicCalculus a (holomorphicGerms.ofFun id analyticOnNhd_id) = a := by
  rw [← toGerm_of (U := ⊤) (subset_univ _) id differentiableOn_id, holomorphicCalculus_toGerm]
  exact holomorphicCalculusOn_id a ⊤ (subset_univ _)

/-- The germ calculus agrees with polynomial evaluation. -/
@[simp]
theorem holomorphicCalculus_polynomial (a : A) (p : Polynomial ℂ) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => p.eval z)
        ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))) = Polynomial.aeval a p :=
  (holomorphicCalculus a).map_holomorphicGermsOfFun_polynomial (holomorphicCalculus_id a) p

end TauCeti

section Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem Commute.holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  exact (hb.integral_smul_resolvent_right
    ((differentiableOn_extend f).continuousOn.mono fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1)
    (Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2)).smul_right _

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`. -/
theorem Commute.holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

/-- Functions of commuting Banach-algebra elements under the holomorphic calculus commute. -/
theorem Commute.holomorphicCalculus {a b : A} (hab : Commute a b)
    (f : holomorphicGerms (spectrum ℂ a)) (g : holomorphicGerms (spectrum ℂ b)) :
    Commute (holomorphicCalculus a f) (holomorphicCalculus b g) :=
  ((hab.holomorphicCalculus_right g).symm.holomorphicCalculus_right f).symm

end Commute

namespace AlgHom

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

/-- Continuous unital complex-algebra homomorphisms preserve `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    [FunLike F A B] [AlgHomClass F ℂ A B] (φ : F) (hφ : Continuous φ) (a : A)
    (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  let L : A →L[ℂ] B := { (AlgHom.ofClass φ).toLinearMap with cont := hφ }
  have hL : ∀ x, L x = φ x := fun _ ↦ rfl
  have hsub : spectrum ℂ (φ a) ⊆ spectrum ℂ a := AlgHom.spectrum_apply_subset φ a
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ a).exists_cycle_windingNumber_eq_one U.isOpen ha
  have hΓB : Γ.IsIn (U \ spectrum ℂ (φ a)) := Cycle.isIn_iff.mpr fun z hz ↦
    ⟨(Cycle.isIn_iff.mp hΓ hz).1, fun hzB ↦ (Cycle.isIn_iff.mp hΓ hz).2 (hsub hzB)⟩
  have hR : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  have hcont : ContinuousOn (fun z ↦ extend f z • resolvent a z) (Cycle.trace Γ) :=
    ((differentiableOn_extend f).continuousOn.mono
      fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1).smul (Cycle.continuousOn_resolvent hR)
  have hcomm := Cycle.integral_comp_comm (f := fun z ↦ extend f z • resolvent a z)
    (fun _ ↦ Cycle.intervalIntegrable_of_mem_support hcont) L
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓB hn
      (fun z hz ↦ hw z (hsub hz)),
    ← hL, L.map_smul, ← hcomm]
  congr 1
  refine Cycle.integral_congr fun z hz ↦ ?_
  rw [hL, map_smul, AlgHom.map_resolvent φ (Cycle.isIn_iff.mp hR hz)]

/-- Continuous unital complex-algebra homomorphisms preserve `holomorphicCalculus`, restricting the
germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    [FunLike F A B] [AlgHomClass F ℂ A B] (φ : F) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, restrict_toGerm, holomorphicCalculus_toGerm]
  exact AlgHom.map_holomorphicCalculusOn φ hφ a U ha f

end AlgHom

namespace ContinuousAlgHom

open TauCeti TauCeti.HolomorphicFunctions

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous unital algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : A →A[ℂ] B) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  AlgHom.map_holomorphicCalculusOn φ φ.continuous a U ha f

/-- Continuous unital algebra homomorphisms commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus (φ : A →A[ℂ] B) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  AlgHom.map_holomorphicCalculus φ φ.continuous a g

end ContinuousAlgHom

namespace ContinuousAlgEquiv

open TauCeti TauCeti.HolomorphicFunctions

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous unital algebra equivalences commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : A ≃A[ℂ] B) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  AlgHom.map_holomorphicCalculusOn φ φ.continuous a U ha f

/-- Continuous unital algebra equivalences commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus (φ : A ≃A[ℂ] B) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  AlgHom.map_holomorphicCalculus φ φ.continuous a g

end ContinuousAlgEquiv

namespace TauCeti

open Contour HolomorphicFunctions

section ResolventAndRational

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- For `w ∉ spectrum ℂ a` (witnessed by analyticity of `z ↦ (w - z)⁻¹` near `spectrum ℂ a`),
the holomorphic germ calculus maps `(w - ·)⁻¹` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculus_sub_inv (a : A) (w : ℂ)
    (hf : AnalyticOnNhd ℂ (fun z ↦ (w - z)⁻¹) (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) hf) = resolvent a w :=
  (holomorphicCalculus a).map_holomorphicGermsOfFun_sub_inv_eq_resolvent
    (holomorphicCalculus_id a) hf

/-- On an open neighbourhood `U` of `spectrum ℂ a` avoiding `w` (witnessed by differentiability of
`z ↦ (w - z)⁻¹` on `U`), `holomorphicCalculusOn` maps `(w - ·)⁻¹` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_sub_inv (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (w : ℂ) (hf : DifferentiableOn ℂ (fun z ↦ (w - z)⁻¹) U) :
    holomorphicCalculusOn a U ha (of U (fun z ↦ (w - z)⁻¹) hf) = resolvent a w := by
  rw [← holomorphicCalculus_toGerm, toGerm_of, holomorphicCalculus_sub_inv]

/-- The calculus sends the reciprocal of a function without zeros on the spectrum to the inverse
of its value. -/
theorem holomorphicCalculus_ofFun_inv (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hne : ∀ x ∈ spectrum ℂ a, f x ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (f z)⁻¹) (hf.inv hne)) =
      Ring.inverse (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) :=
  (holomorphicCalculus a).map_holomorphicGermsOfFun_inv hf hne

/-- The calculus sends a quotient by a function with no zero on the spectrum to the product with
the inverse of the denominator's value. -/
theorem holomorphicCalculus_ofFun_div (a : A) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hg : AnalyticOnNhd ℂ g (spectrum ℂ a))
    (hne : ∀ z ∈ spectrum ℂ a, g z ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ f z / g z) (hf.div hg hne)) =
      holomorphicCalculus a (holomorphicGerms.ofFun f hf) *
        Ring.inverse (holomorphicCalculus a (holomorphicGerms.ofFun g hg)) :=
  (holomorphicCalculus a).map_holomorphicGermsOfFun_div hf hg hne

/-- **Rational functions in the holomorphic calculus.** If `p, q : Polynomial ℂ` and `q` has no
zeros on `spectrum ℂ a`, then the holomorphic calculus sends `z ↦ p(z) / q(z)` to
`p(a) q(a)⁻¹`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z)
        (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
          ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  rw [(holomorphicCalculus a).map_holomorphicGermsOfFun_div
      ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))
      ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq,
    holomorphicCalculus_polynomial, holomorphicCalculus_polynomial]

/-- On an open neighbourhood `U` of `spectrum ℂ a` where `q` does not vanish, the calculus sends
`z ↦ p(z) / q(z)` to `p(a) q(a)⁻¹`. -/
theorem holomorphicCalculusOn_div_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p q : Polynomial ℂ) (hq : ∀ z ∈ U, q.eval z ≠ 0) :
    holomorphicCalculusOn a U ha
      (of U (fun z ↦ p.eval z / q.eval z)
        (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  rw [← holomorphicCalculus_toGerm, toGerm_of]
  exact holomorphicCalculus_div_polynomial a p q fun z hz ↦ hq z (ha hz)

end ResolventAndRational

section Scalar

/-- On `ℂ`, `holomorphicCalculusOn c` is point evaluation at `c`. -/
@[simp]
theorem holomorphicCalculusOn_complex (c : ℂ) (U : Opens ℂ) (hc : spectrum ℂ c ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn c U hc f = f.val ⟨c, hc (by simp [spectrum.mem_iff])⟩ := by
  have hc_mem : c ∈ spectrum ℂ c := by simp [spectrum.mem_iff]
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact ℂ c).exists_cycle_windingNumber_eq_one U.isOpen hc
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  have hoff : c ∉ Cycle.trace Γ := fun hcΓ ↦ (Cycle.isIn_iff.mp hΓ hcΓ).2 hc_mem
  rw [holomorphicCalculusOn_eq_integral c U hc f Γ hΓ hn hw,
    Cycle.integral_congr (g := fun z ↦ extend f z / (z - c)) fun z _ ↦ by
      rw [smul_eq_mul, resolvent, Algebra.algebraMap_self, RingHom.id_apply, Ring.inverse_eq_inv,
        ← div_eq_mul_inv],
    Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f) hΓU hn hoff,
    hw c hc_mem, mul_one, extend_apply f ⟨c, hc hc_mem⟩, smul_eq_mul,
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- On `ℂ`, `holomorphicCalculus c` evaluates germs at `c`. -/
@[simp]
theorem holomorphicCalculus_complex (c : ℂ) (g : holomorphicGerms (spectrum ℂ c)) :
    holomorphicCalculus c g = holomorphicGerms.eval c (by simp [spectrum.mem_iff]) g := by
  obtain ⟨U, hc, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, holomorphicCalculusOn_complex, eval_toGerm]

end Scalar

end TauCeti

namespace AlgHom

open TauCeti HolomorphicFunctions

/-- Any complex character on a unital complex Banach algebra `B` evaluates the holomorphic germ
calculus by point evaluation at `φ b`. -/
theorem map_holomorphicCalculus_eq_eval {F B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] [FunLike F B ℂ] [AlgHomClass F ℂ B ℂ] (φ : F) (b : B)
    (g : holomorphicGerms (spectrum ℂ b)) :
    φ (holomorphicCalculus b g) =
      holomorphicGerms.eval (φ b) (AlgHom.apply_mem_spectrum φ b) g := by
  rw [AlgHom.map_holomorphicCalculus φ (map_continuous φ), holomorphicCalculus_complex]
  obtain ⟨U, hbU, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  simp

end AlgHom
