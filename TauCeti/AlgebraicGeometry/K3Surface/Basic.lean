/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms

/-!
# K3 surfaces over a field

A K3 surface over a field `k` is a scheme `X` with a structure morphism `f : X ⟶ Spec k` that is
smooth of relative dimension two, proper and geometrically integral, whose canonical sheaf
`ω_{X/k} = Ω²_{X/k} = det Ω_{X/k}` is isomorphic to the structure sheaf, and with
`H¹(X, 𝒪_X) = 0`.

The predicate `IsK3 k f` is a proposition: it records only the existence of a trivialization of
the canonical sheaf, and no chosen volume form, polarization or projective embedding. The field
`k` is arbitrary; it need not be algebraically closed or perfect, and smoothness is relative to
`k` rather than absolute regularity. Projectivity is not part of the definition.

From the definition we derive the first consequences: a K3 surface is nonempty and integral, its
canonical line bundle has trivial class, its only global functions are the constants, so
`H⁰(X, 𝒪_X)` is one-dimensional over `k`, and it has no nonzero differential forms of degree
greater than two.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsK3`: the K3 property of a scheme over a field, and
  `TauCeti.AlgebraicGeometry.isK3_iff`, its unfolding into the five defining conditions;
* `TauCeti.AlgebraicGeometry.IsK3.nonempty` and `TauCeti.AlgebraicGeometry.IsK3.isIntegral`;
* `TauCeti.AlgebraicGeometry.IsK3.mk_determinant_relativeDifferentials_eq_one`: the canonical
  line bundle `det Ω_{X/k}` has trivial class;
* `TauCeti.AlgebraicGeometry.IsK3.finrank_cohomology_zero`: `h⁰(X, 𝒪_X) = 1`;
* `TauCeti.AlgebraicGeometry.IsK3.isZero_differentialForms`: `Ωᵖ_{X/k} = 0` for `p > 2`.

## References

* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Definition 1.1 and Remark 1.2.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

/-- A scheme `X` with structure morphism `f : X ⟶ Spec k` over a field `k` is a **K3 surface**
if `f` is smooth of relative dimension two, proper and geometrically integral, the canonical
sheaf `Ω²_{X/k}` is isomorphic to the structure sheaf `𝒪_X`, and `H¹(X, 𝒪_X) = 0`. Only the
existence of a trivialization of the canonical sheaf is required; none is chosen.
See Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Definition 1.1. -/
structure IsK3 (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop where
  /-- The structure morphism is smooth of relative dimension two. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension 2 f
  /-- The structure morphism is proper. -/
  isProper : IsProper f
  /-- The structure morphism is geometrically integral; in particular `X` is nonempty. -/
  geometricallyIntegral : GeometricallyIntegral f
  /-- The canonical sheaf `Ω²_{X/k}` is trivial. -/
  nonempty_differentialForms_two_iso :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    Nonempty (X.differentialForms k 2 ≅ 𝟙_ X.Modules)
  /-- The first cohomology of the structure sheaf vanishes. -/
  subsingleton_cohomology_one :
    Subsingleton (Scheme.Modules.Cohomology (𝟙_ X.Modules) 1)

/-- The K3 property is exactly the conjunction of its five defining conditions. -/
theorem isK3_iff (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsK3 k f ↔ SmoothOfRelativeDimension 2 f ∧ IsProper f ∧ GeometricallyIntegral f ∧
      (letI : X.Over (Spec (.of k)) := ⟨f⟩;
        Nonempty (X.differentialForms k 2 ≅ 𝟙_ X.Modules)) ∧
      Subsingleton (Scheme.Modules.Cohomology (𝟙_ X.Modules) 1) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

namespace IsK3

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (hX : IsK3 k (X ↘ Spec (.of k)))
include hX

/-- A K3 surface is nonempty. -/
theorem nonempty : Nonempty X :=
  have := hX.geometricallyIntegral
  (X ↘ Spec (.of k)).surjective.nonempty

/-- A K3 surface is an integral scheme. -/
theorem isIntegral : IsIntegral X :=
  have := hX.geometricallyIntegral
  GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))

/-- The canonical class of a K3 surface is trivial: the determinant `det Ω_{X/k}` of the cotangent
bundle has trivial line-bundle class. -/
theorem mk_determinant_relativeDifferentials_eq_one :
    haveI := hX.smoothOfRelativeDimension
    LineBundleClass.mk ((FiniteLocallyFreeSheaf.determinant X 2).obj
      (FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials k X 2)) = 1 := by
  have := hX.smoothOfRelativeDimension
  rw [LineBundleClass.mk_eq_one_iff,
    FiniteLocallyFreeSheaf.determinant_obj_relativeDifferentials_obj]
  exact hX.nonempty_differentialForms_two_iso

/-- The only global functions on a K3 surface over `k` are the constants:
`H⁰(X, 𝒪_X)` is one-dimensional over `k`. -/
theorem finrank_cohomology_zero :
    finrank k (Scheme.Modules.Cohomology (𝟙_ X.Modules) 0) = 1 := by
  have := hX.geometricallyIntegral
  have := hX.isProper
  have := hX.nonempty
  rw [← Scheme.Modules.finrank_cohomology_congr k (InvertibleSheaf.trivialObjIsoUnit X) 0]
  exact finrank_cohomology_zero_trivial_eq_one_of_surjective k
    (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).2

/-- A K3 surface has no nonzero differential forms of degree greater than two:
`Ωᵖ_{X/k} = 0` for `p > 2`. -/
theorem isZero_differentialForms {p : ℕ} (hp : 2 < p) : IsZero (X.differentialForms k p) :=
  have := hX.smoothOfRelativeDimension
  isZero_differentialForms_of_lt k hp

end IsK3

end TauCeti.AlgebraicGeometry
