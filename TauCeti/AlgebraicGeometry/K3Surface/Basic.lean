/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms

/-!
# K3 surfaces over a field

A **K3 surface** over a field `k` is a scheme `X` with a structure morphism `f : X ⟶ Spec k`
that is smooth of relative dimension two, proper and geometrically integral, whose canonical sheaf
`Ω²_{X/k}` is isomorphic to `𝒪_X`, and with `H¹(X, 𝒪_X) = 0`. The field is arbitrary: it need not
be algebraically closed or perfect, and smoothness is relative to `k`. The predicate `IsK3 k f`
is a proposition; it records only the existence of a trivialization of `Ω²_{X/k}`, and neither a
chosen trivialization, a polarization nor a projective embedding.

The consequences proved here are those of the defining conditions themselves: a K3 surface is
integral, so in particular nonempty, it has no differential forms of degree greater than two, and
its canonical class `det Ω_{X/k}` is trivial in the group of line-bundle classes, and its only
global functions are the constants.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsK3 k f`: `f : X ⟶ Spec k` is a K3 surface;
* `TauCeti.AlgebraicGeometry.isK3_iff`: `IsK3 k f` is equivalent to the five defining conditions;
* `IsK3.isIntegral` and `not_isK3_of_isEmpty`: a K3 surface is integral, and the empty scheme is
  not a K3 surface;
* `IsK3.isZero_differentialForms`: `Ωᵖ_{X/k} = 0` for `p > 2`;
* `IsK3.mk_det_relativeDifferentials_eq_one`: the canonical class of a K3 surface is trivial;
* `IsK3.finrank_cohomology_zero`: `H⁰(X, 𝒪_X)` is one-dimensional over `k`.

## References

* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Definition 1.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}

/-- A scheme `X` with structure morphism `f : X ⟶ Spec k` over a field `k` is a **K3 surface** if
`f` is smooth of relative dimension two, proper and geometrically integral, the sheaf `Ω²_{X/k}`
of differential `2`-forms is isomorphic to the structure sheaf, and `H¹(X, 𝒪_X) = 0`. Only the
existence of an isomorphism `Ω²_{X/k} ≅ 𝒪_X` is required; none is chosen.
Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Definition 1.1. -/
structure IsK3 (f : X ⟶ Spec (.of k)) : Prop where
  /-- A K3 surface is smooth of relative dimension two over `k`. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension 2 f
  /-- A K3 surface is proper over `k`. -/
  isProper : IsProper f
  /-- A K3 surface is geometrically integral over `k`. -/
  geometricallyIntegral : GeometricallyIntegral f
  /-- The canonical sheaf `Ω²_{X/k}` of a K3 surface is trivial. -/
  nonempty_differentialFormsIso :
    Nonempty (differentialForms k f 2 ≅ SheafOfModules.unit X.ringCatSheaf)
  /-- The first cohomology `H¹(X, 𝒪_X)` of a K3 surface vanishes. -/
  subsingleton_cohomology_one :
    Subsingleton (Scheme.Modules.Cohomology (SheafOfModules.unit X.ringCatSheaf) 1)

variable {k}

/-- A scheme over a field is a K3 surface exactly when it satisfies the five defining
conditions. -/
theorem isK3_iff (f : X ⟶ Spec (.of k)) :
    IsK3 k f ↔ SmoothOfRelativeDimension 2 f ∧ IsProper f ∧ GeometricallyIntegral f ∧
      Nonempty (differentialForms k f 2 ≅ SheafOfModules.unit X.ringCatSheaf) ∧
      Subsingleton (Scheme.Modules.Cohomology (SheafOfModules.unit X.ringCatSheaf) 1) :=
  ⟨fun h ↦ ⟨h.smoothOfRelativeDimension, h.isProper, h.geometricallyIntegral,
      h.nonempty_differentialFormsIso, h.subsingleton_cohomology_one⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

namespace IsK3

variable {f : X ⟶ Spec (.of k)}

/-- A K3 surface is an integral scheme. -/
theorem isIntegral (h : IsK3 k f) : IsIntegral X :=
  have := h.geometricallyIntegral
  GeometricallyIntegral.isIntegral_of_subsingleton f

/-- A K3 surface has no nonzero differential `p`-forms for `p > 2`. -/
theorem isZero_differentialForms (h : IsK3 k f) {p : ℕ} (hp : 2 < p) :
    IsZero (differentialForms k f p) :=
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k)) := h.smoothOfRelativeDimension
  TauCeti.AlgebraicGeometry.isZero_differentialForms k X hp

/-- The canonical class `det Ω_{X/k}` of a K3 surface is trivial in the group of line-bundle
classes. -/
theorem mk_det_relativeDifferentials_eq_one [X.Over (Spec (.of k))]
    (h : IsK3 k (X ↘ Spec (.of k))) :
    haveI := h.smoothOfRelativeDimension
    haveI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
    LineBundleClass.mk
      (FiniteLocallyFreeSheaf.det (FiniteLocallyFreeSheaf.relativeDifferentials k X)) = 1 := by
  have := h.smoothOfRelativeDimension
  obtain ⟨e⟩ := h.nonempty_differentialFormsIso
  exact LineBundleClass.mk_eq_one_iff.2 ⟨(differentialFormsIsoDet k X 2).symm ≪≫ e⟩

/-- A K3 surface has only constant global functions: `H⁰(X, 𝒪_X)` is one-dimensional over `k`.
No rational point is needed; this uses only properness and geometric integrality. -/
theorem finrank_cohomology_zero [X.Over (Spec (.of k))] (h : IsK3 k (X ↘ Spec (.of k))) :
    Module.finrank k (Scheme.Modules.Cohomology (𝟙_ X.Modules) 0) = 1 := by
  have := h.geometricallyIntegral
  have := h.isProper
  have := h.isIntegral
  rw [← Scheme.Modules.finrank_cohomology_congr k (InvertibleSheaf.trivialObjIsoUnit X) 0]
  exact finrank_cohomology_zero_trivial_eq_one_of_surjective k
    (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).2

end IsK3

/-- The empty scheme is not a K3 surface: geometric integrality includes nonemptiness. -/
theorem not_isK3_of_isEmpty [IsEmpty X] (f : X ⟶ Spec (.of k)) : ¬IsK3 k f := fun h ↦
  have := h.isIntegral
  IsEmpty.false (Classical.arbitrary X)

end TauCeti.AlgebraicGeometry
