/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.SplitMultiplicative
public import TauCeti.NumberTheory.LocalField.Unramified.Quadratic
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.NumberTheory.LocalField.Unramified.Rigidity

/-!
# The unramified quadratic twist at multiplicative reduction

A nonsplit multiplicative elliptic curve over a nonarchimedean local field becomes split after
an unramified quadratic twist, including in residue characteristic two. The extension is generated
by a root of the monic node quadratic. Its discriminant is a unit, so the extension is unramified.
In fact, twisting by any unramified quadratic extension gives split multiplicative reduction.
This supplies a split twist over the original base field for comparing inertia representations.

The result concerns the minimal equation of the twist: the original equation is minimal by the
multiplicative-reduction hypothesis, but a chosen equation of its twist need not be minimal.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and X.2.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.5.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
-/

public section

open ValuativeRel IsLocalRing TauCeti

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
  obtain ⟨n, -, hD, hn⟩ := E.exists_algebraMap_eq_nodePolynomial_coeff_zero_div 𝒪[K]
  rw [← integralModel_a₁_eq 𝒪[K] E, ← hn] at hroot
  exact TauCeti.isUnramified_of_sq_add_mul_add_eq_zero hD hθ hroot

/-- At nonsplit multiplicative reduction the monic node quadratic has a generating root in any
unramified quadratic extension of the base field. -/
theorem exists_root_nodeQuadratic_of_isUnramified
    (h : ¬ E.HasSplitMultiplicativeReduction 𝒪[K])
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsQuadraticExtension K L] [IsUnramified K L] :
    ∃ θ : L, θ ∉ Set.range (algebraMap K L) ∧
      θ ^ 2 + algebraMap K L E.a₁ * θ +
        algebraMap K L (E.nodePolynomial.coeff 0 / E.c₄) = 0 := by
  obtain ⟨M, _, _, _, _, θ, hθ, hroot⟩ := exists_quadraticExtension_root_nodeQuadratic h
  let := algebraicExtensionValuativeRel K M
  let := algebraicExtensionNormedFieldTopology K M
  have := finiteExtension_isNonarchimedeanLocalField K M
  have := algebraicExtension_valuativeExtension K M
  have := isUnramified_of_root_nodeQuadratic hθ hroot
  -- Both residue extensions have degree two; lift a residue field embedding to local fields.
  obtain ⟨φ⟩ : Nonempty (𝓀[M] →ₐ[𝓀[K]] 𝓀[L]) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      simp only [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank,
        Algebra.IsQuadraticExtension.finrank_eq_two, dvd_refl])
  obtain ⟨f, -⟩ := (IsUnramified.residueFieldHom_bijective (L := M) (M := L)).surjective φ
  refine ⟨f θ, fun ⟨a, ha⟩ ↦ hθ ⟨a, f.injective ((f.commutes a).trans ha)⟩, ?_⟩
  simpa only [map_add, map_mul, map_pow, map_zero, AlgHom.commutes] using congrArg f hroot

/-- Twisting a nonsplit multiplicative elliptic curve by any unramified separable quadratic
extension gives split multiplicative reduction on the chosen minimal equation. -/
theorem hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_isUnramified [E.IsElliptic]
    (h : ¬ E.HasSplitMultiplicativeReduction 𝒪[K])
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] [IsUnramified K L] :
    ((E.quadraticTwist L).minimal 𝒪[K]).HasSplitMultiplicativeReduction 𝒪[K] := by
  obtain ⟨θ, hθ, hroot⟩ := exists_root_nodeQuadratic_of_isUnramified h L
  exact hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root_nodeQuadratic 𝒪[K] hθ hroot

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
    hasSplitMultiplicativeReduction_minimal_quadraticTwist_of_root_nodeQuadratic 𝒪[K] hθ hroot⟩

end WeierstrassCurve
