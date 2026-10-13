/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.GlobalSections
import Mathlib.AlgebraicGeometry.PullbackCarrier
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# The structure sheaf of an elliptic curve pushes forward to the structure sheaf of the base

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`. This file
shows that the unit `𝒪_S ⟶ π_* 𝒪_E` is an isomorphism: for every open `U` of `S`, the functions on
`π⁻¹(U)` are exactly the functions on `U`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_structureMap_app`). Since the base change of
an elliptic curve along any morphism `T ⟶ S` is again an elliptic curve, the same holds for
`π_T : E_T ⟶ T`, for every `T`.

Over the base of a pointed Weierstrass chart, `π` is the projective Weierstrass model of an
elliptic curve over a ring, whose global functions are the constants
(`WeierstrassCurve.isIso_appTop_projModelOver`); this gives the statement over the image of the
base of a chart (`TauCeti.AlgebraicGeometry.PointedWeierstrassChart.isIso_app_opensRange`). The
images of the restrictions of the charts of an atlas to the affine opens of their bases form a
basis of the topology of `S`, and a morphism of sheaves which is an isomorphism on a basis is an
isomorphism.

## Main results

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.isIso_app_opensRange`: over the image of the
  base of a pointed Weierstrass chart of `π`, the functions on the preimage under `π` are the
  functions on the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_structureMap_app`: for an elliptic curve
  `π : E ⟶ S` and every open `U` of `S`, `π` induces an isomorphism `Γ(S, U) ≅ Γ(E, π⁻¹(U))`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- Over the base of a pointed Weierstrass chart `c`, the restriction of `π` has only constant
global functions: it is the projective model of the equation of `c`. -/
instance isIso_appTop_toBase (c : PointedWeierstrassChart π zero) : IsIso c.toBase.appTop := by
  have h := congrArg Scheme.Hom.appTop c.modelIso_over
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  have : IsIso c.modelIso.hom.appTop := inferInstanceAs (IsIso (c.modelIso.hom.app ⊤))
  have : IsIso c.baseIso.hom.appTop := inferInstanceAs (IsIso (c.baseIso.hom.app ⊤))
  have : IsIso (c.baseIso.hom.appTop ≫ c.toBase.appTop) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left c.baseIso.hom.appTop c.toBase.appTop

/-- Over the image `U` of the base of a pointed Weierstrass chart of `π`, the functions on `π⁻¹(U)`
are the functions on `U`: `π` induces an isomorphism `Γ(S, U) ≅ Γ(X, π⁻¹(U))`. -/
theorem isIso_app_opensRange (c : PointedWeierstrassChart π zero) :
    IsIso (π.app c.baseMap.opensRange) := by
  have : IsOpenImmersion c.toTotal :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) c.isPullback.flip c.baseMap_open
  -- `π⁻¹(U)` is the image of the restriction of `X` to the base of `c`
  have hrange : π ⁻¹ᵁ c.baseMap.opensRange ≤ c.toTotal.opensRange := by
    intro x hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (pullback.fst π c.baseMap) := by
      rw [Scheme.Pullback.range_fst]
      exact hx
    exact ⟨c.isPullback.isoPullback.inv y, by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hy]⟩
  have : IsIso (c.toTotal.app (π ⁻¹ᵁ c.baseMap.opensRange)) := c.toTotal.isIso_app _ hrange
  have hb : IsIso (c.baseMap.app c.baseMap.opensRange) := c.baseMap.isIso_app _ le_rfl
  have htop : ∀ V, V = ⊤ → IsIso (c.toBase.app V) := by
    rintro _ rfl
    exact c.isIso_appTop_toBase
  -- read the pullback square `toTotal ≫ π = toBase ≫ baseMap` on sections over `U`
  have h := Scheme.Hom.congr_app c.isPullback.w c.baseMap.opensRange
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at h
  have : IsIso (π.app c.baseMap.opensRange ≫ c.toTotal.app (π ⁻¹ᵁ c.baseMap.opensRange)) := by
    rw [h]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' hb (htop _ c.baseMap.preimage_opensRange))
      (Functor.map_isIso _ _)
  exact IsIso.of_isIso_comp_right _ (c.toTotal.app (π ⁻¹ᵁ c.baseMap.opensRange))

end PointedWeierstrassChart

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The unit `𝒪_S ⟶ π_* 𝒪_E` of an elliptic curve is an isomorphism.** For an elliptic curve
`π : E ⟶ S` and every open `U` of `S`, `π` induces an isomorphism `Γ(S, U) ≅ Γ(E, π⁻¹(U))`: the
functions on `π⁻¹(U)` are the functions on `U`. Applied to the base change `E.baseChange f`, this
gives the same statement after any base change `f : T ⟶ S`. -/
instance isIso_structureMap_app (U : S.Opens) : IsIso (E.structureMap.app U) := by
  obtain ⟨A⟩ := E.localModel
  -- the images of the restrictions of the charts to affine opens of their bases
  let B : (Σ i : A.index, (A.chart i).base.affineOpens) → S.Opens :=
    fun p ↦ ((A.chart p.1).restrict p.2).baseMap.opensRange
  have hB : Opens.IsBasis (Set.range B) := by
    refine Opens.isBasis_iff_nbhd.mpr fun {V s} hs ↦ ?_
    obtain ⟨i, x, rfl⟩ := A.covers s
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      (A.chart i).base.isBasis_affineOpens.exists_subset_of_mem_open
        ((A.chart i).baseMap.mem_preimage.mpr hs) ((A.chart i).baseMap ⁻¹ᵁ V).isOpen
    -- the image of the restriction of the chart to `W` is the image of `W`
    have hrange (t : S) : t ∈ ((A.chart i).restrict ⟨W, hW⟩).baseMap.opensRange ↔
        t ∈ (A.chart i).baseMap '' W := by
      rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, ← PointedWeierstrassChart.restrictι_baseMap,
        Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        PointedWeierstrassChart.range_restrictι]
    refine ⟨B ⟨i, ⟨W, hW⟩⟩, ⟨_, rfl⟩, (hrange _).mpr ⟨x, hxW, rfl⟩, fun t ht ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := (hrange t).mp ht
    exact hWV hy
  -- `π` induces isomorphisms on sections over the basis `B`, hence over every open
  exact E.structureMap.isIso_app_of_isBasis hB
    (fun p ↦ ((A.chart p.1).restrict p.2).isIso_app_opensRange) U

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
