/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
# Toric fan schemes over the complex numbers

The structure morphisms of the affine toric charts descend to a structure morphism from the
scheme of a regular fan to `Spec ℂ`. The chart inclusions and the algebraic maps induced by fan
morphisms commute with these structure morphisms. Thus these schemes and maps can be used in
Mathlib's category of schemes over `Spec ℂ`, and their complex points can be expressed as
morphisms over `Spec ℂ`.

The affine structures are Mathlib's `AlgebraicGeometry.specOverSpec`; the global structure is
obtained from the existing colimit of affine toric charts. The construction also applies to the
empty fan. The integral lattices are in `Type`, so their spectra and `Spec ℂ` are schemes in the
same universe; the ambient real vector spaces need not be in `Type`.

## Main declarations

* `TauCeti.Toric.Fan.algebraicRealizationOver`: the canonical complex-scheme structure.
* `TauCeti.Toric.Fan.isOver_affineToricChartι`: affine chart inclusions are complex morphisms.
* `TauCeti.Toric.FanHom.isOver_algebraicMap`: toric maps are complex morphisms.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable (Φ : Fan i)

/-- The compatible structure morphisms of the affine toric charts. -/
private noncomputable def structureCocone : Cocone Φ.affineToricDiagram where
  pt := Spec (.of ℂ)
  ι :=
    { app := fun σ ↦ Φ.affineToricChart σ ↘ Spec (.of ℂ)
      naturality := by
        intro τ σ h
        -- Pin the affine and constant-functor carriers before using the categorical unit law.
        change faceAffineToricSchemeMap Φ.lattice
          (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom h)) ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, faceAffineToricSchemeMap_def]
        exact comp_over (Spec.map (CommRingCat.ofHom
          (faceAffineCoordinateRingMap Φ.lattice
            (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom h))).toRingHom)) (Spec (.of ℂ)) }

/-- The structure morphism to `Spec ℂ` of the scheme of a regular fan. -/
noncomputable def algebraicRealizationStructureMap (hΦ : Φ.IsRegular) :
    Φ.algebraicRealization hΦ ⟶ Spec (.of ℂ) :=
  (Φ.isColimitAffineToricCocone hΦ).desc (structureCocone Φ)

/-- The canonical structure over `Spec ℂ` on the scheme of a regular fan, induced by the
complex-algebra structures on its affine coordinate rings. -/
noncomputable instance algebraicRealizationOver (hΦ : Φ.IsRegular) :
    (Φ.algebraicRealization hΦ).Over (Spec (.of ℂ)) :=
  OverClass.ofHom (Φ.algebraicRealizationStructureMap hΦ)

/-- The canonical complex structure morphism is the descended structure morphism. -/
theorem algebraicRealization_over (hΦ : Φ.IsRegular) :
    Φ.algebraicRealization hΦ ↘ Spec (.of ℂ) = Φ.algebraicRealizationStructureMap hΦ :=
  (rfl)

/-- Each affine toric chart inclusion respects the complex-scheme structures. -/
instance isOver_affineToricChartι (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    (Φ.affineToricChartι hΦ σ).IsOver (Spec (.of ℂ)) where
  comp_over := by
    rw [algebraicRealization_over, specOverSpec_over]
    -- State the factorization on the chart carriers before rewriting their over-structures.
    have h : Φ.affineToricChartι hΦ σ ≫ Φ.algebraicRealizationStructureMap hΦ =
        Φ.affineToricChart σ ↘ Spec (.of ℂ) := by
      have h := (Φ.isColimitAffineToricCocone hΦ).fac (structureCocone Φ) σ
      rw [affineToricCocone_ι_app] at h
      exact h
    simpa only [specOverSpec_over] using h

end Fan

namespace FanHom

variable {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- The algebraic morphism induced by a fan morphism respects the complex-scheme structures. -/
instance isOver_algebraicMap (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) :
    (f.algebraicMap hΦ hΨ).IsOver (Spec (.of ℂ)) where
  comp_over := by
    apply Fan.algebraicRealization_hom_ext Φ hΦ
    intro σ
    simp only [affineToricChartι_comp_algebraicMap_assoc, comp_over]
    rw [affineToricChartMap_def, affineToricSchemeMap_def]
    exact comp_over (Spec.map (CommRingCat.ofHom
      (affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
        _).toRingHom)) (Spec (.of ℂ))

end FanHom

end TauCeti.Toric
