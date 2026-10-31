/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The genus of a smooth curve under every constant field extension

Let `X` be a smooth, proper, geometrically integral curve over a field `k`, with function field
`F = k(X)`. This file shows that the genus of `F` does not change under any algebraic extension
`k' / k` of the constants, separable or not:

`g(F · k' / k') = g(F / k)`.

Over a perfect field, or for separable `k' / k`, this is Stichtenoth's Theorem 3.6.3(b)
(`TauCeti.genus_eq_genus_of_constantCompositum_eq_top`). Without separability the genus can drop
(`TauCeti.GenusDrop.genus_lt_genus`, the curve `y² = x^p - t` over `𝔽_p(t)`, whose regular proper
model is therefore not smooth), and in general it never increases
(`TauCeti.genus_le_genus_of_constantCompositum_eq_top`). Smoothness of the curve is what rules out
the drop, over any constant field.

The proof compares both genera with cohomology. The base change `X_{k'} = X ×_k Spec k'` is again
smooth, proper and geometrically integral, its genus `dim H¹(X_{k'}, 𝒪)` is that of `X` by flat
base change (`TauCeti.AlgebraicGeometry.genus_eq_of_isPullback_of_smooth`), and on each of these
curves the cohomological genus is the genus of the function field
(`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.genus_eq_genus_functionField`). It remains to
identify the function field of `X_{k'}` with `F · k'`, which holds for every geometrically integral
`X` (`TauCeti.AlgebraicGeometry.nonempty_functionField_algEquiv_of_isPullback`): both are the
fraction field of `A ⊗[k] k'` for a nonempty affine open `U = Spec A` of `X`.

## Main results

* `AlgebraicGeometry.Scheme.genus_eq_genus_functionField_of_smooth`: the genus
  `dim H¹(X, 𝒪_X)` of a smooth proper geometrically integral curve is the genus of its function
  field.
* `TauCeti.AlgebraicGeometry.genus_functionField_eq_of_isPullback`: the function field of the
  base change of such a curve to any field extension `K / k` has the same genus.
* `TauCeti.AlgebraicGeometry.genus_eq_genus_functionField_of_constantCompositum_eq_top`:
  **the genus of the function field of a smooth proper geometrically integral curve is invariant
  under every algebraic constant field extension.**

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 3.6.3.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

/-- **The genus of a smooth curve is the genus of its function field.** For a smooth proper
geometrically integral curve `X` over `k`, the genus `dim_k H¹(X, 𝒪_X)` is the genus of the
function field `k(X)` defined through Riemann's theorem. -/
theorem _root_.AlgebraicGeometry.Scheme.genus_eq_genus_functionField_of_smooth (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    haveI := finiteDimensional_cohomology_one_trivial_of_smooth k X
    X.genus k = genus k X.functionField := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x ↦ inferInstance
  have : X.IsCurveOver k :=
    ⟨topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))⟩
  have : IsNoetherian X := Scheme.IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  exact SchemeWeilDivisor.genus_eq_genus_functionField
    (Scheme.IsCurveOver.valuativeCriterion_existence k X)
    (Scheme.IsCurveOver.coheight_le_one (k := k)) Scheme.IsCurveOver.isFunctionField
    (isIntegrallyClosedIn_functionField_of_geometricallyIntegral)

variable {K : Type u} [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- **The function field of a smooth curve keeps its genus under base change.** Let `X` be a
smooth proper geometrically integral curve over `k` and `Y = X ×_k Spec K` its base change to a
field extension `K / k`. Then the function field `K(Y)` has the genus of `k(X)`. -/
theorem genus_functionField_eq_of_isPullback [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    genus K Y.functionField = genus k X.functionField := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : IsProper (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) H inferInstance
  have : GeometricallyIntegral (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  rw [← Scheme.genus_eq_genus_functionField_of_smooth,
    ← Scheme.genus_eq_genus_functionField_of_smooth]
  exact genus_eq_of_isPullback_of_smooth H

omit [Algebra k K] [Y.Over (Spec (.of K))] in
/-- **The genus of a smooth curve is invariant under every constant field extension.** Let `X` be
a smooth proper geometrically integral curve over `k` with function field `F = k(X)`, and let
`F' = F · k'` for an algebraic extension `k' / k`, separable or not. Then `g(F' / k') = g(F / k)`.

Without smoothness the genus can drop under an inseparable `k' / k`
(`TauCeti.GenusDrop.genus_lt_genus`). -/
theorem genus_eq_genus_functionField_of_constantCompositum_eq_top [IsIntegral X]
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] {k' : Type u} [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] {F' : Type*} [Field F'] [Algebra k' F'] [Algebra X.functionField F']
    [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k X.functionField F']
    (h : constantCompositum X.functionField k' F' = ⊤) :
    genus k' F' = genus k X.functionField := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let _ : (pullback (X ↘ Spec (.of k)) s).Over (Spec (.of k')) := ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst _ _) (pullback (X ↘ Spec (.of k)) s ↘ Spec (.of k'))
      (X ↘ Spec (.of k)) s :=
    IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := nonempty_functionField_algEquiv_of_isPullback H h
  rw [← genus_functionField_eq_of_isPullback H]
  exact genus_eq_of_ringEquiv (RingEquiv.refl k') e.toRingEquiv e.commutes

end AlgebraicGeometry

end TauCeti
