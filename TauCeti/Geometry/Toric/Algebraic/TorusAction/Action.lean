/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.CategoryTheory.Monoidal.Mod
public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Internal

/-!
# Internal torus actions on affine toric schemes

Each affine toric scheme is a module object for the dense torus in the category of schemes
over `Spec ℂ`. The action is obtained by applying Mathlib's monoidal spectrum functor
`AlgebraicGeometry.algSpec` to `affineCoordinateRingCoactionModObj`, using
`CategoryTheory.Functor.modObjObj`. Thus the coaction identities give the unit and
associativity laws on schemes, rather than just a morphism with the expected source and target.

The computation of the underlying scheme morphism identifies the action with the spectrum
of the grading coaction after the affine fibre-product comparison. Face maps are equivariant
module morphisms, so the actions are compatible with the open immersions used to glue fan
schemes. On the zero cone this is the regular action of the same dense torus on itself.
No regularity or rationality assumption on the cone is needed. As for Mathlib's affine
scheme structures over `Spec ℂ`, the lattice carrier lies in `Type`; the ambient real
vector space may lie in any universe.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj Opposite

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The dense torus acts on each affine toric scheme over `Spec ℂ`. This is the internal
action transported from the coordinate-ring coaction, with its unit and associativity laws. -/
noncomputable instance affineToricSchemeModObj (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    ModObj ((denseTorusScheme hi).asOver (Spec (.of ℂ)))
      ((affineToricScheme hi σ).asOver (Spec (.of ℂ))) := by
  letI : (algSpec (.of ℂ)).LaxMonoidal :=
    (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
  letI := affineCoordinateRingCoactionModObj hi σ
  exact (algSpec (.of ℂ)).modObjObj
    (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
    (op (CommAlgCat.of ℂ (affineCoordinateRing hi σ)))

/-- On underlying schemes, the action is the spectrum of the grading coaction, with its
source identified by the canonical affine fibre-product comparison. -/
@[simp]
theorem affineToricSchemeModObj_smul_left (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    γ[(denseTorusScheme hi).asOver (Spec (.of ℂ)),
        (affineToricScheme hi σ).asOver (Spec (.of ℂ))].left =
      (pullbackSpecIso ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
        (affineCoordinateRing hi σ)).hom ≫
      Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom) := by
  let : (algSpec (.of ℂ)).LaxMonoidal :=
    (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
  let := affineCoordinateRingCoactionModObj hi σ
  have h := (algSpec (.of ℂ)).modObjObj_smul
    (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
    (op (CommAlgCat.of ℂ (affineCoordinateRing hi σ)))
  rw [affineCoordinateRingCoactionModObj_smul] at h
  have hl := congrArg (fun f ↦ f.left) h
  simp only [Over.comp_left, algSpec_map_left] at hl
  exact hl

/-- The zero-cone chart carries the regular action of the dense torus on itself. -/
@[simp]
theorem affineToricSchemeModObj_bot (hi : IsIntegralLattice i) :
    affineToricSchemeModObj hi (⊥ : PointedCone ℝ V) =
      ModObj.regular ((denseTorusScheme hi).asOver (Spec (.of ℂ))) := by
  apply ModObj.ext
  apply Over.OverMorphism.ext
  rw [affineToricSchemeModObj_smul_left, affineCoordinateRingCoaction_bot]
  exact (mul_spec_asOver_spec_left (R := .of ℂ)
    (A := .of (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))).symm

/-- The spectrum of restriction to a face is an equivariant morphism for the internal
dense-torus actions. The morphism is bundled by the complex-algebra spectrum functor. -/
instance isModHom_spec_faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    IsModHom ((denseTorusScheme hi).asOver (Spec (.of ℂ)))
      ((Spec.map (CommRingCat.ofHom
        (faceAffineCoordinateRingMap hi hτσ).toRingHom)).asOver (Spec (.of ℂ))) := by
  let : (algSpec (.of ℂ)).LaxMonoidal :=
    (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
  let := affineCoordinateRingCoactionModObj hi τ
  let := affineCoordinateRingCoactionModObj hi σ
  let := isModHom_faceAffineCoordinateRingMap hi hτσ
  exact (algSpec (.of ℂ)).modObjObj_isModHom
    (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
    (CommAlgCat.ofHom (faceAffineCoordinateRingMap hi hτσ)).op

end TauCeti.Toric
