/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.CyclicSubgroup.Basic
import TauCeti.AlgebraicGeometry.Descent.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.ClosedSubgroup
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Descent of cyclic subgroups of an elliptic curve

Cyclic subgroups of an elliptic curve (`EllipticCurveGeom.IsCyclicSubgroup`) are stable under
arbitrary base change (`EllipticCurveGeom.IsCyclicSubgroup.comap`). Conversely, being a cyclic
subgroup of order `N` descends along surjective fppf base changes
(`EllipticCurveGeom.isCyclicSubgroup_comap_iff`). Finiteness, flatness and finite presentation
descend by fppf descent. Being a subgroup scheme is reflected by flat surjective base change, with
no finiteness hypothesis on the subscheme
(`EllipticCurveGeom.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`). A generating fppf
covering of the new base composes with the base change to a generating fppf covering of the old
one.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isCyclicSubgroup_comap_iff`: cyclic subgroups
  descend along surjective fppf base changes.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.4 (`[Γ₀(N)]`-structures).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **Cyclic subgroups descend along surjective fppf morphisms** (Katz–Mazur, §3.4). Let
`g : E' ⟶ E` be a morphism of elliptic curves lying over a surjective, flat
morphism `f : S' ⟶ S` locally of finite presentation, forming a pullback square with the structure
morphisms and carrying the zero section of `E'` to that of `E`. Then the ideal sheaf `I` cuts out a
cyclic subgroup of `E` of order `N` exactly when its inverse image along `g` cuts out a cyclic
subgroup of `E'` of order `N`.

Finiteness, flatness and finite presentation of the subgroup descend along `f` by fppf descent of
finite locally free morphisms
(`AlgebraicGeometry.descendsAlong_isFinite_inf_flat_inf_locallyOfFinitePresentation`), assembled
from the fppf descent instances
`AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation`
and its namesakes for `Flat` and `LocallyOfFinitePresentation`. These come from the fpqc descent
of finiteness (`AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact`),
of flatness (`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_quasicompact`) and
Mathlib's fpqc descent of local finite presentation in
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`, through Mathlib's fpqc-to-fppf descent
instance in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`, which removes the
quasi-compactness hypothesis of fpqc descent for Zariski-local properties. -/
theorem isCyclicSubgroup_comap_iff [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] {I : E.carrier.IdealSheafData} {N : ℕ} :
    E'.IsCyclicSubgroup (I.comap g) N ↔ E.IsCyclicSubgroup I N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap hg h0⟩
  -- The closed subscheme of `I.comap g` is the base change of that of `I` along `f`, so finiteness,
  -- flatness and finite presentation descend along `f`.
  have hsub := (I.isPullback_subschemeMap_comap _ hg).flip
  have hf : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) f :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨⟨_, _⟩, _⟩ : (@IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) (I.subschemeι ≫ E.structureMap) :=
    MorphismProperty.of_isPullback_of_descendsAlong hsub hf
      ⟨⟨h.isFinite, h.flat⟩, h.locallyOfFinitePresentation⟩
  refine
    { exists_grpObj_isMonHom :=
        (exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective hg h0 I).mp
          h.exists_grpObj_isMonHom
      isFinite := inferInstance
      flat := inferInstance
      locallyOfFinitePresentation := inferInstance
      finrank_eq s := ?_
      exists_cover := ?_ }
  · obtain ⟨s', rfl⟩ := f.surjective s
    rw [← I.finrank_comap_of_isPullback _ g _ f hg, h.finrank_eq]
  -- Refine the singleton fppf covering by `f` by an fppf covering of `S'` on which the inverse
  -- image is generated.
  obtain ⟨𝒰, h𝒰⟩ := h.exists_cover
  refine ⟨Precoverage.ZeroHypercover.bind (J := Scheme.fppfPrecoverage)
    (f.cover (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      ⟨inferInstance, inferInstance⟩) fun _ ↦ 𝒰, fun ⟨_, i⟩ ↦ ?_⟩
  obtain ⟨E₁, g₁, hg₁, h0₁, P, hP, hI⟩ := h𝒰 i
  have h0₂ : E₁.zero ≫ g₁ ≫ g = (𝒰.f i ≫ f) ≫ E.zero := by
    rw [reassoc_of% h0₁, h0, Category.assoc]
  refine ⟨E₁, g₁ ≫ g, hg₁.paste_horiz hg, h0₂, P, hP, ?_⟩
  rw [Scheme.IdealSheafData.comap_comp]
  exact hI

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
