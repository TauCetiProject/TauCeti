/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.SplitMultiplicative
public import TauCeti.NumberTheory.LocalField.Unramified.Quadratic
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# The unramified quadratic twist at multiplicative reduction

A nonsplit multiplicative elliptic curve over a nonarchimedean local field becomes split after
an unramified quadratic twist, including in residue characteristic two. The extension is generated
by a root of the monic node quadratic. Its discriminant is a unit, so the extension is unramified.
This identifies the splitting character needed to compare inertia representations of split and
nonsplit multiplicative curves.

The result concerns the minimal equation of the twist: the original equation is minimal by the
multiplicative-reduction hypothesis, but a chosen equation of its twist need not be minimal.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and X.2.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.5.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
-/

public section

open Polynomial ValuativeRel IsLocalRing TauCeti

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {E : WeierstrassCurve K} [E.HasMultiplicativeReduction 𝒪[K]]

/-- A quadratic local-field extension containing a generator satisfying the monic node quadratic
of a multiplicative equation is unramified. No restriction on the residue characteristic is
needed: the node quadratic has unit discriminant even in residue characteristic two. -/
theorem isUnramified_of_root_nodeQuadratic
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsQuadraticExtension K L] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L))
    (hroot : θ ^ 2 + algebraMap K L E.a₁ * θ +
      algebraMap K L (E.nodePolynomial.coeff 0 / E.c₄) = 0) :
    IsUnramified K L := by
  obtain ⟨-, n, -, hD, hn⟩ := exists_integral_nodeQuadratic 𝒪[K] (E := E)
  let I := E.integralModel 𝒪[K]
  have hroot' : θ ^ 2 + algebraMap K L (I.a₁ : K) * θ +
      algebraMap K L (n : K) = 0 := by
    rw [← integralModel_a₁_eq 𝒪[K] E, ← hn] at hroot
    exact hroot
  have hint : _root_.IsIntegral 𝒪[K] θ := by
    refine ⟨X ^ 2 + C I.a₁ * X + C n, by monicity!, ?_⟩
    simpa only [eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X,
      IsScalarTower.algebraMap_apply 𝒪[K] K L,
      Algebra.algebraMap_ofSubsemiring_apply] using hroot'
  let ω : 𝒪[L] := ⟨θ, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation K)) _).mp hint⟩
  have htr : Algebra.trace 𝒪[K] 𝒪[L] ω = -I.a₁ := by
    apply Subtype.ext
    rw [coe_trace_integerRing]
    exact _root_.Algebra.IsQuadraticExtension.trace_eq_neg_of_sq_add_mul_add_eq_zero hθ hroot'
  have hnorm : Algebra.norm 𝒪[K] ω = n := by
    apply Subtype.ext
    rw [coe_norm_integerRing]
    apply TauCeti.Algebra.norm_eq_of_mul_self_eq hθ (t := -(I.a₁ : K))
    rw [map_neg]
    linear_combination hroot'
  apply TauCeti.isUnramified_of_isUnit_discrim (ω := ω)
  simpa only [htr, hnorm, neg_sq] using hD

/-- A nonsplit multiplicative elliptic curve over a nonarchimedean local field admits an
unramified separable quadratic twist with split multiplicative reduction. The extension has its
compatible local-field valuation and topology; the conclusion uses a minimal equation of the
twist. This includes residue characteristic two and equal characteristic two. -/
theorem exists_unramified_quadraticTwist_hasSplitMultiplicativeReduction [E.IsElliptic]
    (h : ¬ E.HasSplitMultiplicativeReduction 𝒪[K]) :
    ∃ (L : Type u) (_ : Field L) (_ : ValuativeRel L) (_ : TopologicalSpace L)
      (_ : IsNonarchimedeanLocalField L) (_ : Algebra K L) (_ : ValuativeExtension K L)
      (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L)
      (_ : IsUnramified K L),
      ((E.quadraticTwist L).minimal 𝒪[K]).HasSplitMultiplicativeReduction 𝒪[K] := by
  obtain ⟨L, _, _, _, _, θ, hθ, hroot⟩ := exists_quadraticExtension_root_nodeQuadratic h
  let := algebraicExtensionValuativeRel K L
  let := algebraicExtensionNormedFieldTopology K L
  have := finiteExtension_isNonarchimedeanLocalField K L
  have := algebraicExtension_valuativeExtension K L
  have := isUnramified_of_root_nodeQuadratic hθ hroot
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root hθ hroot⟩

end WeierstrassCurve
