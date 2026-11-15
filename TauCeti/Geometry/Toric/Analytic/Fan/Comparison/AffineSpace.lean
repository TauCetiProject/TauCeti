/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Scheme
public import TauCeti.Geometry.Toric.Analytic.Fan.Affine.Space
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction

/-!
# Affine space and the algebraic–analytic toric comparison

Let `b` be an integral basis indexed by a finite type `ι`. The toric scheme of the fan of affine
space is identified with `𝔸(ι; Spec ℂ)` over `Spec ℂ` by
`TauCeti.Toric.Fan.affineSpaceAlgebraicIso`. A complex point of `𝔸(ι; Spec ℂ)`, a morphism from
`Spec ℂ` over `Spec ℂ`, is the same as the vector of complex numbers obtained by pulling back the
coordinates (Mathlib's `AlgebraicGeometry.AffineSpace.homOverEquiv`). So the complex points of
the toric scheme of the fan of affine space are identified with `ι → ℂ` through the algebraic
coordinates.

On the analytic side, `TauCeti.Toric.Fan.affineSpaceHomeomorph` identifies the analytic
realization of the same fan with `ι → ℂ` through the character functions of the coordinate
characters `b.coord j`. This file shows that the algebraic–analytic comparison
`TauCeti.Toric.Fan.algebraicAnalyticEquiv` carries the algebraic coordinates to the analytic
ones: the coordinate `j` of `𝔸(ι; Spec ℂ)` is the character function of `b.coord j` on complex
points. Consequently the algebraic identification of complex points with `ι → ℂ` is a
homeomorphism for the topology glued from the affine charts and a biholomorphism for the complex
structure pulled back from the analytic realization, and torus translation scales each algebraic
coordinate by the corresponding character value.

## Main declarations

* `TauCeti.Toric.Fan.affineSpaceAlgebraicComplexPointEquiv`: the complex points of the toric scheme
  of the fan of affine space are their coordinates in `𝔸(ι; Spec ℂ)`.
* `TauCeti.Toric.Fan.affineSpaceAlgebraicComplexPointEquiv_apply_eq_character`: the algebraic
  coordinate `j` is the character function of `b.coord j`.
* `TauCeti.Toric.Fan.affineSpaceHomeomorph_algebraicAnalyticEquiv`: the algebraic–analytic
  comparison commutes with the identifications of both sides with `ι → ℂ`.
* `TauCeti.Toric.Fan.affineSpaceAlgebraicComplexPointHomeomorph` and
  `TauCeti.Toric.Fan.affineSpaceAlgebraicComplexPointDiffeomorph`: the algebraic coordinates are a
  homeomorphism and a biholomorphism onto `ι → ℂ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1, 1.3 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1, 1.2 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N ι V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

open AlgebraicComplexPoint

/-- The complex points of the toric scheme of the fan of affine space are their coordinates in
`𝔸(ι; Spec ℂ)`: a complex point is sent through `affineSpaceAlgebraicIso` to a complex point of
affine space, whose coordinate `j` is the pullback of the coordinate function `j`. -/
noncomputable def affineSpaceAlgebraicComplexPointEquiv :
    (affineSpace b hi).AlgebraicComplexPoint ≃ (ι → ℂ) :=
  ({ toFun p := ⟨p.1 ≫ (affineSpaceAlgebraicIso b hi).hom, by have := p.2; infer_instance⟩
     invFun q := ⟨q.1 ≫ (affineSpaceAlgebraicIso b hi).inv, by have := q.2; infer_instance⟩
     left_inv p := by simp
     right_inv q := by simp } :
    (affineSpace b hi).AlgebraicComplexPoint ≃
      {q : Spec (.of ℂ) ⟶ 𝔸(ι; Spec (.of ℂ)) // q.IsOver (Spec (.of ℂ))}).trans <|
    (AffineSpace.homOverEquiv (S := Spec (.of ℂ))).trans <|
      Equiv.piCongrRight fun _ ↦ (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.toEquiv

/-- The coordinate `j` of a complex point of the toric scheme of the fan of affine space is the
pullback of the coordinate function `j` of `𝔸(ι; Spec ℂ)`, read in `ℂ`. -/
theorem affineSpaceAlgebraicComplexPointEquiv_apply (p : (affineSpace b hi).AlgebraicComplexPoint)
    (j : ι) :
    affineSpaceAlgebraicComplexPointEquiv b hi p j =
      (Scheme.ΓSpecIso (.of ℂ)).hom
        ((p.1 ≫ (affineSpaceAlgebraicIso b hi).hom).appTop (AffineSpace.coord _ j)) :=
  (rfl)

/-- The complex point of the toric scheme of the fan of affine space with coordinates `z` is the
morphism `Spec ℂ ⟶ 𝔸(ι; Spec ℂ)` with coordinate functions `z j`, followed by the inverse of
`affineSpaceAlgebraicIso`. -/
theorem coe_affineSpaceAlgebraicComplexPointEquiv_symm_apply (z : ι → ℂ) :
    ((affineSpaceAlgebraicComplexPointEquiv b hi).symm z).1 =
      AffineSpace.homOfVector (Spec (.of ℂ) ↘ Spec (.of ℂ))
          (fun j ↦ (Scheme.ΓSpecIso (.of ℂ)).inv (z j)) ≫
        (affineSpaceAlgebraicIso b hi).inv :=
  (rfl)

/-- On the chart of the orthant, the algebraic coordinate `j` of a complex point is its value at
the monomial of the coordinate character `b.coord j`. -/
private theorem affineSpaceAlgebraicComplexPointEquiv_ofAffinePoint
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (affineSpace b hi).lattice (affineSpaceMaximalCone b hi).1)) (j : ι) :
    affineSpaceAlgebraicComplexPointEquiv b hi (ofAffinePoint (affineSpaceMaximalCone b hi) x) j =
      x (MonoidAlgebra.single (ofAdd ⟨(b.coord j).toAddMonoidHom,
        coord_mem_dualSemigroup_affineSpace b hi j (affineSpaceMaximalCone b hi)⟩) 1) := by
  -- On the orthant chart the coordinate is the monomial of `b.coord j`; evaluating it at `x` is
  -- naturality of `Scheme.ΓSpecIso` for the ring map of `x`.
  rw [affineSpaceAlgebraicComplexPointEquiv_apply, coe_ofAffinePoint, Category.assoc,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineToricChartι_comp_affineSpaceAlgebraicIso_hom_appTop_coord,
    ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  simp

/-- The algebraic coordinate `j` of a complex point of the toric scheme of the fan of affine space
is the value of the character function of the coordinate character `b.coord j`. -/
@[simp]
theorem affineSpaceAlgebraicComplexPointEquiv_apply_eq_character
    (p : (affineSpace b hi).AlgebraicComplexPoint) (j : ι) :
    affineSpaceAlgebraicComplexPointEquiv b hi p j =
      character (affineSpace b hi) (b.coord j).toAddMonoidHom
        (coord_mem_dualSemigroup_affineSpace b hi j) p := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  -- Every cone of the fan of affine space is a face of the orthant.
  have hσ : σ.1.IsFaceOf (affineSpaceMaximalCone b hi).1 := (mem_ofCone_cones hi _).1 σ.2
  rw [← ofAffinePoint_faceAffinePointMap hσ, affineSpaceAlgebraicComplexPointEquiv_ofAffinePoint,
    character_ofAffinePoint]

/-- The character function of the coordinate character `b.coord j`, at the complex point of the
toric scheme of the fan of affine space with coordinates `z`, is `z j`. -/
@[simp]
theorem character_affineSpaceAlgebraicComplexPointEquiv_symm (z : ι → ℂ) (j : ι) :
    character (affineSpace b hi) (b.coord j).toAddMonoidHom
        (coord_mem_dualSemigroup_affineSpace b hi j)
        ((affineSpaceAlgebraicComplexPointEquiv b hi).symm z) =
      z j := by
  rw [← affineSpaceAlgebraicComplexPointEquiv_apply_eq_character, Equiv.apply_symm_apply]

/-- The algebraic–analytic comparison commutes with the identifications of both sides with
`ι → ℂ`: the analytic coordinates of the point corresponding to a complex point of the toric scheme
are its algebraic coordinates in `𝔸(ι; Spec ℂ)`. -/
theorem affineSpaceHomeomorph_algebraicAnalyticEquiv
    (p : (affineSpace b hi).AlgebraicComplexPoint) :
    affineSpaceHomeomorph b hi (algebraicAnalyticEquiv (isRegular_affineSpace b hi) p) =
      affineSpaceAlgebraicComplexPointEquiv b hi p := by
  funext j
  simp

/-- The inverse algebraic identification of complex points with `ι → ℂ` is the inverse analytic
identification, read through the algebraic–analytic comparison. -/
theorem affineSpaceAlgebraicComplexPointEquiv_symm_eq :
    ⇑(affineSpaceAlgebraicComplexPointEquiv b hi).symm =
      (algebraicAnalyticEquiv (isRegular_affineSpace b hi)).symm ∘
        (affineSpaceHomeomorph b hi).symm := by
  funext z
  rw [Function.comp_apply, Equiv.symm_apply_eq, ← affineSpaceHomeomorph_algebraicAnalyticEquiv,
    Equiv.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- Torus translation scales each algebraic coordinate of a complex point of the toric scheme of
the fan of affine space by the corresponding character value. -/
theorem affineSpaceAlgebraicComplexPointEquiv_smul (t : ComplexTorus N)
    (p : (affineSpace b hi).AlgebraicComplexPoint) (j : ι) :
    affineSpaceAlgebraicComplexPointEquiv b hi (t • p) j =
      (t (b.coord j).toAddMonoidHom : ℂ) * affineSpaceAlgebraicComplexPointEquiv b hi p j := by
  simp

/-- The algebraic coordinates of the complex points of the toric scheme of the fan of affine space
are a homeomorphism onto `ι → ℂ`, for the topology glued from the affine charts. -/
noncomputable def affineSpaceAlgebraicComplexPointHomeomorph :
    (affineSpace b hi).AlgebraicComplexPoint ≃ₜ (ι → ℂ) where
  toEquiv := affineSpaceAlgebraicComplexPointEquiv b hi
  continuous_toFun :=
    ((affineSpaceHomeomorph b hi).continuous.comp
      (algebraicAnalyticHomeomorph (isRegular_affineSpace b hi)).continuous).congr fun p ↦ by
        rw [Function.comp_apply, coe_algebraicAnalyticHomeomorph,
          affineSpaceHomeomorph_algebraicAnalyticEquiv, Equiv.toFun_as_coe]
  continuous_invFun := by
    simp only [Equiv.invFun_as_coe, affineSpaceAlgebraicComplexPointEquiv_symm_eq,
      ← coe_algebraicAnalyticHomeomorph_symm]
    fun_prop

/-- The homeomorphism is the identification `affineSpaceAlgebraicComplexPointEquiv`. -/
@[simp]
theorem coe_affineSpaceAlgebraicComplexPointHomeomorph :
    ⇑(affineSpaceAlgebraicComplexPointHomeomorph b hi) =
      affineSpaceAlgebraicComplexPointEquiv b hi :=
  (rfl)

/-- The inverse homeomorphism is the inverse identification. -/
@[simp]
theorem coe_affineSpaceAlgebraicComplexPointHomeomorph_symm :
    ⇑(affineSpaceAlgebraicComplexPointHomeomorph b hi).symm =
      (affineSpaceAlgebraicComplexPointEquiv b hi).symm :=
  (rfl)

/-- The algebraic coordinates of the complex points of the toric scheme of the fan of affine space
are a biholomorphism onto `ι → ℂ`, for the complex structure pulled back from the analytic
realization, at every smoothness order. -/
noncomputable def affineSpaceAlgebraicComplexPointDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (isRegular_affineSpace b hi)
    (affineSpace b hi).AlgebraicComplexPoint ≃ₘ^n⟮𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ),
      𝓘(ℂ, ι → ℂ)⟯ (ι → ℂ) :=
  letI := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
  letI := algebraicComplexPointChartedSpace (isRegular_affineSpace b hi)
  (algebraicAnalyticDiffeomorph (isRegular_affineSpace b hi) n).trans
    (affineSpaceDiffeomorph b hi n)

/-- The biholomorphism is the identification `affineSpaceAlgebraicComplexPointEquiv`. -/
@[simp]
theorem coe_affineSpaceAlgebraicComplexPointDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (isRegular_affineSpace b hi)
    ⇑(affineSpaceAlgebraicComplexPointDiffeomorph b hi n) =
      affineSpaceAlgebraicComplexPointEquiv b hi := by
  let := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
  let := algebraicComplexPointChartedSpace (isRegular_affineSpace b hi)
  funext p
  rw [affineSpaceAlgebraicComplexPointDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    coe_algebraicAnalyticDiffeomorph, affineSpaceDiffeomorph_apply,
    affineSpaceHomeomorph_algebraicAnalyticEquiv]

end TauCeti.Toric.Fan
