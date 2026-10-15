/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Algebra.Category.ModuleCat.RatAddCircle
public import Mathlib.Algebra.Module.ULift

/-!
# Rational dimension shifting for integral continuous cohomology

For a compact group with trivial discrete coefficients, the connecting map of
`0 → ℤ → ℚ → ℚ/ℤ → 0` identifies `Hⁿ(G, ℚ/ℤ)` with `Hⁿ⁺¹(G, ℤ)` for `n > 0`.
In degree one this describes integral second cohomology by continuous rational characters.
It is the connecting-map half of the computation of second integral cohomology of the
profinite integers.

The integers and rationals are lifted to the universe of the group. The rational module must
carry a discrete topology. The quotient coefficient module is supplied through an additive
equivalence with `AddCircle (1 : ℚ)`, allowing any discrete model of the rational circle.
All caller-supplied actions are retained and assumed trivial. No new cohomology carrier is used.

The algebraic exactness is reused from `ModuleCat.ratAddCircleShortComplex_shortExact`;
the isomorphism uses the canonical connecting map and vanishing of positive-degree
continuous cohomology of discrete rational vector spaces.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Propositions 1–2.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*,
  2nd ed., (1.3.2) and (1.6.1).
-/

public section

namespace TauCeti.ContCohomology

open CategoryTheory
open TauCeti.ContinuousCohomology

universe u

variable (G : Type u) [Group G]
  [DistribMulAction G (ULift.{u} ℤ)] [DistribMulAction G (ULift.{u} ℚ)]
  [TopologicalSpace (ULift.{u} ℚ)] [DiscreteTopology (ULift.{u} ℚ)]
  (C : Type u) [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]
  (e : C ≃+ AddCircle (1 : ℚ))
  (hℤ : ∀ (g : G) (x : ULift.{u} ℤ), g • x = x)
  (hℚ : ∀ (g : G) (x : ULift.{u} ℚ), g • x = x)
  (hC : ∀ (g : G) (x : C), g • x = x)

/-- The discrete trivial coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`, with a supplied
model of the rational circle. The two small coefficient groups are universe-lifted. -/
def rationalIntegralShortExact : DiscreteShortExact G (ULift.{u} ℤ) (ULift.{u} ℚ) C where
  incl := AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((Int.castAddHom ℚ).comp AddEquiv.ulift.toAddMonoidHom)
  proj := e.symm.toAddMonoidHom.comp
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      AddEquiv.ulift.toAddMonoidHom)
  incl_equivariant g x := by simp only [hℤ, hℚ]
  proj_equivariant g x := by simp only [hℚ, hC]
  incl_injective := by
    intro x y h
    apply ULift.ext
    exact ModuleCat.ratAddCircleShortComplex_shortExact.moduleCat_injective_f
      (congrArg ULift.down h)
  proj_surjective := by
    intro c
    obtain ⟨q, hq⟩ :=
      ModuleCat.ratAddCircleShortComplex_shortExact.moduleCat_surjective_g (e c)
    exact ⟨ULift.up q, (congrArg e.symm hq).trans (e.symm_apply_apply c)⟩
  exact x := by
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      ModuleCat.ratAddCircleShortComplex).mp
      ModuleCat.ratAddCircleShortComplex_shortExact.exact x.down
    constructor
    · intro hx
      -- Unfold the projection's composite: first unlift the rational value, then reduce
      -- modulo one and transport it to C through e.symm.
      have hx' : e.symm (x.down : AddCircle (1 : ℚ)) = 0 := hx
      obtain ⟨n, hn⟩ := hex.mp (e.symm.injective (hx'.trans e.symm.map_zero.symm))
      exact ⟨ULift.up n, ULift.ext hn⟩
    · rintro ⟨n, rfl⟩
      exact e.symm.map_eq_zero_iff.mpr (hex.mpr ⟨n.down, rfl⟩)

/-- The inclusion sends a lifted integer to the same rational number. -/
@[simp]
theorem rationalIntegralShortExact_incl_apply (x : ULift.{u} ℤ) :
    (rationalIntegralShortExact G C e hℤ hℚ hC).incl x = ULift.up (x.down : ℚ) := (rfl)

/-- The projection is reduction of the rational value modulo `1`, read in the supplied model. -/
@[simp]
theorem rationalIntegralShortExact_proj_apply (x : ULift.{u} ℚ) :
    (rationalIntegralShortExact G C e hℤ hℚ hC).proj x =
      e.symm (x.down : AddCircle (1 : ℚ)) := (rfl)

/-- Restricting the rational coefficient sequence retains the same inclusion and projection. -/
@[simp]
theorem rationalIntegralShortExact_restrict (T : Subgroup G) :
    (rationalIntegralShortExact G C e hℤ hℚ hC).restrict T =
      rationalIntegralShortExact T C e (fun g ↦ hℤ g) (fun g ↦ hℚ g) (fun g ↦ hC g) := by
  apply DiscreteShortExact.ext <;>
    simp only [DiscreteShortExact.restrict_incl, DiscreteShortExact.restrict_proj,
      rationalIntegralShortExact]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [ContinuousSMul G (ULift.{u} ℚ)]

/-- Rational dimension shifting in every positive degree: the canonical connecting map
`Hⁿ⁺¹(G, ℚ/ℤ) → Hⁿ⁺²(G, ℤ)` is an isomorphism of topological integer modules. -/
noncomputable def rationalIntegralDeltaIso (n : ℕ) :
    continuousCohomology (n + 1) (ofDiscreteModule ℤ G C) ≅
      continuousCohomology (n + 1 + 1) (ofDiscreteModule ℤ G (ULift.{u} ℤ)) := by
  letI : Module ℚ (ofDiscreteModule ℤ G (ULift.{u} ℚ)).V :=
    inferInstanceAs (Module ℚ (ULift.{u} ℚ))
  have := subsingleton_continuousCohomology_of_module_rat
    (X := ofDiscreteModule ℤ G (ULift.{u} ℚ)) n
  have := subsingleton_continuousCohomology_of_module_rat
    (X := ofDiscreteModule ℤ G (ULift.{u} ℚ)) (n + 1)
  have := (rationalIntegralShortExact G C e hℤ hℚ hC).isIso_delta (n + 1)
  exact asIso ((rationalIntegralShortExact G C e hℤ hℚ hC).delta (n + 1))

/-- The forward map of rational dimension shifting is the canonical connecting map of the
named coefficient sequence. -/
@[simp]
theorem rationalIntegralDeltaIso_hom (n : ℕ) :
    (rationalIntegralDeltaIso G C e hℤ hℚ hC n).hom =
      (rationalIntegralShortExact G C e hℤ hℚ hC).delta (n + 1) := by
  simp [rationalIntegralDeltaIso]

/-- Rational dimension shifting commutes with restriction to a compact subgroup. -/
@[reassoc]
theorem rationalIntegralDeltaIso_hom_res (T : Subgroup G) [CompactSpace T] (n : ℕ) :
    (rationalIntegralDeltaIso G C e hℤ hℚ hC n).hom ≫
        res T (ofDiscreteModule ℤ G (ULift.{u} ℤ)) (n + 1 + 1) =
      res T (ofDiscreteModule ℤ G C) (n + 1) ≫
        (rationalIntegralDeltaIso T C e (fun g ↦ hℤ g) (fun g ↦ hℚ g)
          (fun g ↦ hC g) n).hom := by
  simpa only [rationalIntegralDeltaIso_hom, rationalIntegralShortExact_restrict] using
    (rationalIntegralShortExact G C e hℤ hℚ hC).delta_res T (n + 1)

variable [ContinuousSMul G C]

/-- Integral second continuous cohomology of a compact group is the additive group of
continuous rational-circle characters. -/
noncomputable def continuousCohomologyTwoIntEquivContinuousMonoidHom :
    continuousCohomology 2 (ofDiscreteModule ℤ G (ULift.{u} ℤ)) ≃+
      Additive (G →ₜ* Multiplicative C) :=
  (rationalIntegralDeltaIso G C e hℤ hℚ hC 0).symm.toContinuousLinearEquiv.toAddEquiv.trans
    ((explicitH1AddEquivContinuousCohomology G C).symm.trans (H1EquivOfSmulEqSelf hC))

/-- The inverse character identification takes the explicit class of the character to
canonical cohomology and then applies the connecting map. -/
@[simp]
theorem continuousCohomologyTwoIntEquivContinuousMonoidHom_symm_apply
    (χ : Additive (G →ₜ* Multiplicative C)) :
    (continuousCohomologyTwoIntEquivContinuousMonoidHom G C e hℤ hℚ hC).symm χ =
      (rationalIntegralShortExact G C e hℤ hℚ hC).delta 1
        (explicitH1AddEquivContinuousCohomology G C
          ((H1EquivOfSmulEqSelf hC).symm χ)) := by
  rw [continuousCohomologyTwoIntEquivContinuousMonoidHom, AddEquiv.symm_trans_apply,
    AddEquiv.symm_trans_apply, AddEquiv.symm_symm]
  -- Iso.toContinuousLinearEquiv has no inverse-application lemma: its defining invFun
  -- is the inverse morphism. Expose just that conversion after rewriting the composites.
  change (rationalIntegralDeltaIso G C e hℤ hℚ hC 0).symm.inv
    (explicitH1AddEquivContinuousCohomology G C ((H1EquivOfSmulEqSelf hC).symm χ)) = _
  rw [Iso.symm_inv, rationalIntegralDeltaIso_hom]

end TauCeti.ContCohomology
