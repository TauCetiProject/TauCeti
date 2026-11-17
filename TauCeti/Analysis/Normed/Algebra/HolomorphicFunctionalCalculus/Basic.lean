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
spectrum. We also record commutativity with elements commuting with `a`, along with
explicit evaluations on Cauchy kernels (resolvents), nonvanishing analytic quotients
and rational functions, and norm-convergent power series. The zero algebra and its
empty spectrum are included. No normalization of the norm of the identity is assumed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.

The integral identities are those of `TauCeti.Contour.Cycle`; descent uses
`TauCeti.holomorphicGerms.lift`.
-/

public noncomputable section

open Complex Filter Metric Set TopologicalSpace Topology
open scoped Real Interval NNReal ENNReal Ring

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

/-- `holomorphicCalculusOn` depends only on the element `a`, not on the proof `spectrum ℂ a ⊆ U`. -/
theorem holomorphicCalculusOn_congr {a b : A} (h : a = b) {U : Opens ℂ}
    {ha : spectrum ℂ a ⊆ U} {hb : spectrum ℂ b ⊆ U} :
    holomorphicCalculusOn a U ha = holomorphicCalculusOn b U hb := by
  subst h
  rfl

/-- Evaluating `holomorphicCalculus` on a restricted germ depends only on the element `a`, not on
the spectrum-inclusion proof. -/
theorem holomorphicCalculus_restrict_congr {s : Set ℂ} {a b : A} (h : a = b)
    {ha : spectrum ℂ a ⊆ s} {hb : spectrum ℂ b ⊆ s} (g : holomorphicGerms s) :
    holomorphicCalculus a (holomorphicGerms.restrict ha g) =
      holomorphicCalculus b (holomorphicGerms.restrict hb g) := by
  subst h
  rfl

/-- Evaluating `holomorphicCalculus` on a represented analytic function depends only on the element
`a` and function `f`, not on the analyticity proof. -/
theorem holomorphicCalculus_ofFun_congr {a b : A} (h : a = b) {f : ℂ → ℂ}
    {ha : AnalyticOnNhd ℂ f (spectrum ℂ a)} {hb : AnalyticOnNhd ℂ f (spectrum ℂ b)} :
    holomorphicCalculus a (holomorphicGerms.ofFun f ha) =
      holomorphicCalculus b (holomorphicGerms.ofFun f hb) := by
  subst h
  rfl

section Algebraic

/-- Any unital `ℂ`-algebra homomorphism on `holomorphicFunctions V` sending the coordinate
function to `b` sends each Cauchy kernel `z ↦ (w - z)⁻¹` (`w ∉ V`) to `resolvent b w`. -/
theorem algHom_cauchyKernel_eq_resolvent {B : Type*} [Ring B] [Algebra ℂ B]
    {V : Opens ℂ} {b : B} (Φ : holomorphicFunctions V →ₐ[ℂ] B)
    (hΦ : Φ (of V id differentiableOn_id) = b) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    Φ (cauchyKernel hw) = resolvent b w := by
  have hleft : (algebraMap ℂ B w - b) * Φ (cauchyKernel hw) = 1 := by
    rw [← Φ.commutes w, ← hΦ, ← map_sub, ← map_mul, sub_id_mul_cauchyKernel, map_one]
  have hright : Φ (cauchyKernel hw) * (algebraMap ℂ B w - b) = 1 := by
    rw [← Φ.commutes w, ← hΦ, ← map_sub, ← map_mul, cauchyKernel_mul_sub_id, map_one]
  rw [resolvent, ← Units.val_mk (algebraMap ℂ B w - b) (Φ (cauchyKernel hw)) hleft hright,
    Ring.inverse_unit, Units.inv_mk, Units.val_mk]

end Algebraic

/-- On an open neighbourhood `U` of `spectrum ℂ a`, the holomorphic calculus sends the Cauchy
kernel at `w ∉ U` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_cauchyKernel (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    {w : ℂ} (hw : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha (cauchyKernel hw) = resolvent a w :=
  algHom_cauchyKernel_eq_resolvent (holomorphicCalculusOn a U ha)
    (holomorphicCalculusOn_id a U ha) hw

/-- At a point `w` in the resolvent set of `a`, the holomorphic germ calculus sends
`z ↦ (w - z)⁻¹` to `resolvent a w`. -/
theorem holomorphicCalculus_inv_sub (a : A) {w : ℂ} (hw : w ∈ resolventSet ℂ a)
    (hf : AnalyticOnNhd ℂ (fun z ↦ (w - z)⁻¹) (spectrum ℂ a) :=
      (analyticOnNhd_const.sub analyticOnNhd_id).inv fun _ hz ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (spectrum.notMem_iff.mpr hw)).symm) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) hf) = resolvent a w := by
  let U : Opens ℂ := ⟨{w}ᶜ, isClosed_singleton.isOpen_compl⟩
  have ha : spectrum ℂ a ⊆ U := fun z hz hzw ↦
    spectrum.notMem_iff.mpr hw (mem_singleton_iff.mp hzw ▸ hz)
  have hwU : w ∉ (U : Set ℂ) := fun h ↦ h (mem_singleton w)
  have hgerm : holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) hf = toGerm ha (cauchyKernel hwU) :=
    (toGerm_eq_ofFun ha (cauchyKernel hwU) _ hf fun z ↦ cauchyKernel_apply hwU z).symm
  rw [hgerm, holomorphicCalculus_toGerm, holomorphicCalculusOn_cauchyKernel]

/-- For `g` analytic near `spectrum ℂ a` and nonvanishing on `spectrum ℂ a`, the holomorphic germ
calculus sends `z ↦ (g z)⁻¹` to `(holomorphicCalculus a (ofFun g hg))⁻¹ʳ`. -/
theorem holomorphicCalculus_ofFun_inv (a : A) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) (hg0 : ∀ z ∈ spectrum ℂ a, g z ≠ 0)
    (hinv : AnalyticOnNhd ℂ (fun z ↦ (g z)⁻¹) (spectrum ℂ a) := hg.inv hg0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (g z)⁻¹) hinv) =
      (holomorphicCalculus a (holomorphicGerms.ofFun g hg))⁻¹ʳ := by
  have hunit : IsUnit (holomorphicGerms.ofFun g hg) :=
    (holomorphicGerms.isUnit_iff _).mpr fun z hz ↦ by simpa using hg0 z hz
  have hmul : holomorphicGerms.ofFun (fun z ↦ (g z)⁻¹) hinv * holomorphicGerms.ofFun g hg = 1 := by
    rw [← holomorphicGerms.ofFun_mul, ← map_one (algebraMap ℂ (holomorphicGerms (spectrum ℂ a))),
      ← holomorphicGerms.ofFun_const 1, holomorphicGerms.ofFun_eq_iff]
    refine eventually_nhdsSet_iff_forall.mpr fun z hz ↦ ?_
    filter_upwards [(hg z hz).continuousAt.eventually_ne (hg0 z hz)] with w hw
    exact inv_mul_cancel₀ hw
  have hinv_eq :
      holomorphicGerms.ofFun (fun z ↦ (g z)⁻¹) hinv = (holomorphicGerms.ofFun g hg)⁻¹ʳ :=
    left_inv_eq_right_inv hmul (Ring.mul_inverse_cancel _ hunit)
  rw [hinv_eq, hunit.map_ringInverse (holomorphicCalculus a)]

/-- For `f` and `g` analytic near `spectrum ℂ a` with `g` nonvanishing on `spectrum ℂ a`, the
holomorphic germ calculus sends `z ↦ f z / g z` to
`holomorphicCalculus a (ofFun f hf) * (holomorphicCalculus a (ofFun g hg))⁻¹ʳ`. -/
theorem holomorphicCalculus_ofFun_div (a : A) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hg : AnalyticOnNhd ℂ g (spectrum ℂ a))
    (hg0 : ∀ z ∈ spectrum ℂ a, g z ≠ 0)
    (hdiv : AnalyticOnNhd ℂ (fun z ↦ f z / g z) (spectrum ℂ a) := hf.div hg hg0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ f z / g z) hdiv) =
      holomorphicCalculus a (holomorphicGerms.ofFun f hf) *
        (holomorphicCalculus a (holomorphicGerms.ofFun g hg))⁻¹ʳ := by
  have heq : holomorphicGerms.ofFun (fun z ↦ f z / g z) hdiv =
      holomorphicGerms.ofFun f hf * holomorphicGerms.ofFun (fun z ↦ (g z)⁻¹) (hg.inv hg0) := by
    rw [← holomorphicGerms.ofFun_mul, holomorphicGerms.ofFun_eq_iff]
    exact Eventually.of_forall fun z ↦ div_eq_mul_inv (f z) (g z)
  rw [heq, map_mul, holomorphicCalculus_ofFun_inv a hg hg0]

/-- **Rational functional calculus compatibility.** For polynomials `p` and `q` such that `q` has
no zeros on `spectrum ℂ a`, the holomorphic germ calculus sends `z ↦ p.eval z / q.eval z` to
`p(a) * q(a)⁻¹`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0)
    (hf : AnalyticOnNhd ℂ (fun z ↦ p.eval z / q.eval z) (spectrum ℂ a) :=
      ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
        ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf) =
      Polynomial.aeval a p * (Polynomial.aeval a q)⁻¹ʳ := by
  rw [holomorphicCalculus_ofFun_div a
    ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))
    ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq hf,
    holomorphicCalculus_polynomial, holomorphicCalculus_polynomial]

/-- When `spectralRadius ℂ b < p.radius`, the series `∑ p.coeff n • b ^ n` is absolutely norm
summable in `A`. -/
theorem _root_.FormalMultilinearSeries.summable_norm_coeff_smul_pow_of_spectralRadius_lt
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (b : A) (hb : spectralRadius ℂ b < p.radius) :
    Summable (fun n ↦ ‖p.coeff n • b ^ n‖) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact summable_zero.congr fun _ ↦ (norm_eq_zero.mpr (Subsingleton.elim _ _)).symm
  obtain ⟨r, hrb, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
  have hgelf : gelfandRadius b < (r : ℝ) :=
    (ENNReal.ofReal_lt_coe_iff (gelfandRadius_nonneg b)).mp
      (spectrum.spectralRadius_eq_gelfandRadius b ▸ hrb)
  obtain ⟨C, -, hpow⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hgelf
  have hsum_scalar : Summable (fun n ↦ ‖p.coeff n‖ * (r : ℝ) ^ n) := by
    simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef] using p.summable_norm_mul_pow hrp
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) (hsum_scalar.mul_left C)
  rw [norm_smul]
  calc ‖p.coeff n‖ * ‖b ^ n‖ ≤ ‖p.coeff n‖ * (C * (r : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (hpow n) (norm_nonneg _)
    _ = C * (‖p.coeff n‖ * (r : ℝ) ^ n) := by ring

/-- **Power-series evaluation of the holomorphic calculus.** If `f` has the formal power-series
expansion `p` on the open ball `Metric.eball z₀ R` containing `spectrum ℂ a`, then
`∑ p.coeff n • (a - z₀) ^ n` converges unconditionally in norm to `holomorphicCalculus a f`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ R)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ R)
    (hf_an : AnalyticOnNhd ℂ f (spectrum ℂ a) := hf.analyticOnNhd.mono ha) :
    HasSum (fun n ↦ p.coeff n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) 0]
    exact hasSum_zero.congr_fun fun _ ↦ Subsingleton.elim _ _
  let b : A := a - algebraMap ℂ A z₀
  have hspec_lt : spectralRadius ℂ b < p.radius := by
    refine lt_of_lt_of_le ?_ hf.r_le
    obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_nnNorm_eq_spectralRadius b
    rw [← hw_eq]
    have hw' : w + z₀ ∈ spectrum ℂ a := by
      rw [spectrum.add_mem_iff, neg_add_eq_sub]
      exact hw
    simpa only [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_right, eNorm_eq_nnNorm]
      using ha hw'
  have hsum : Summable (fun n ↦ p.coeff n • b ^ n) :=
    (p.summable_norm_coeff_smul_pow_of_spectralRadius_lt b hspec_lt).of_norm
  let U : Opens ℂ := ⟨Metric.eball z₀ R, Metric.isOpen_eball⟩
  have haU : spectrum ℂ a ⊆ U := ha
  let zU : holomorphicFunctions U :=
    of U id differentiableOn_id - algebraMap ℂ (holomorphicFunctions U) z₀
  let F : ℕ → holomorphicFunctions U := fun n ↦ ∑ k ∈ Finset.range n, p.coeff k • zU ^ k
  have hF_tendsto : Tendsto F atTop (𝓝 (of U f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn]
    refine (hf.tendstoLocallyUniformlyOn'.congr ?_).congr_right fun z hz ↦
      ((extend_apply (of U f hf.differentiableOn) ⟨z, hz⟩).trans (of_apply _ _ ⟨z, hz⟩)).symm
    intro n z hz
    rw [extend_apply (F n) ⟨z, hz⟩]
    simp [F, zU, FormalMultilinearSeries.partialSum, p.apply_eq_pow_smul_coeff, smul_eq_mul,
      mul_comm]
  have hcalc_tendsto :
      Tendsto (fun n ↦ holomorphicCalculusOn a U haU (F n)) atTop
        (𝓝 (holomorphicCalculusOn a U haU (of U f hf.differentiableOn))) :=
    (continuous_holomorphicCalculusOn a U haU).tendsto _ |>.comp hF_tendsto
  have hcalc_F (n : ℕ) :
      holomorphicCalculusOn a U haU (F n) = ∑ k ∈ Finset.range n, p.coeff k • b ^ k := by
    simp [F, zU, b, map_sum, map_smul, map_pow, map_sub]
  simp only [hcalc_F] at hcalc_tendsto
  have hgerm_eq :
      holomorphicCalculusOn a U haU (of U f hf.differentiableOn) =
        holomorphicCalculus a (holomorphicGerms.ofFun f hf_an) := by
    rw [← holomorphicCalculus_toGerm a U haU (of U f hf.differentiableOn), toGerm_of]
  rw [hgerm_eq] at hcalc_tendsto
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hcalc_tendsto ▸ hsum.hasSum

/-- Specialization of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus` centered at `0`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus_zero
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball 0 R)
    (hf_an : AnalyticOnNhd ℂ f (spectrum ℂ a) := hf.analyticOnNhd.mono ha) :
    HasSum (fun n ↦ p.coeff n • a ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) := by
  simpa only [map_zero, sub_zero] using hf.hasSum_holomorphicCalculus a ha hf_an

end TauCeti

section Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem Commute.holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  have hfΓ : ContinuousOn (extend f) (Cycle.trace Γ) :=
    (differentiableOn_extend f).continuousOn.mono fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  have hΓ_res : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  exact (hb.integral_smul_resolvent_right hfΓ hΓ_res).smul_right _

/-- `holomorphicCalculusOn a U ha f` commutes with every element commuting with `a`. -/
theorem Commute.holomorphicCalculusOn_left {a b : A} (hb : Commute a b) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute (holomorphicCalculusOn a U ha f) b :=
  (hb.symm.holomorphicCalculusOn_right U ha f).symm

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`. -/
theorem Commute.holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

/-- `holomorphicCalculus a g` commutes with every element commuting with `a`. -/
theorem Commute.holomorphicCalculus_left {a b : A} (hb : Commute a b)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute (holomorphicCalculus a g) b :=
  (hb.symm.holomorphicCalculus_right g).symm

end Commute
