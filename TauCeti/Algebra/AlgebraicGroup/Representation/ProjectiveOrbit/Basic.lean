/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Unimodular
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Projective orbit morphisms of Hopf comodules

For a unimodular vector `m` in a finite projective comodule `M` over a commutative Hopf
algebra `H`, construct the scheme morphism

`Spec H ⟶ Proj(Sym(M∨))`

with homogeneous coordinates `φ ↦ c(φ, m)`. On points this sends `g` to the line through
`g · m`, using the original action on `M`, rather than its contragredient. The dual module
appears because its elements are the linear homogeneous coordinates of projective space.
Over a field, every nonzero vector is unimodular. Over a general ring, unimodularity
ensures that the vector generates a direct summand of rank one.

The matrix coefficients generate the unit ideal by
`Comodule.span_matrixCoefficient_eq_top_iff_isUnimodular`. The construction then uses
Mathlib's `Proj.fromOfGlobalSections`, including its chart and base-morphism formulas.
No smoothness, reducedness, or finite-type hypothesis on `H` is imposed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u v w

section Coordinates

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [CommSemiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The homogeneous coordinate map of the orbit of a vector: the linear coordinate `φ`
pulls back to the matrix coefficient `c(φ, m)`. -/
noncomputable def orbitCoordinates (m : M) : SymmetricAlgebra R (Module.Dual R M) →ₐ[R] H :=
  SymmetricAlgebra.lift ((matrixCoefficientBilinear (C := H)).flip m)

/-- Linear homogeneous coordinates pull back to their matrix coefficients. -/
@[simp]
theorem orbitCoordinates_ι (m : M) (φ : Module.Dual R M) :
    orbitCoordinates (H := H) m (SymmetricAlgebra.ι R (Module.Dual R M) φ) =
      matrixCoefficient (C := H) φ m := by
  simp [orbitCoordinates]

/-- At the identity point, orbit coordinates specialize to evaluation at the original vector. -/
@[simp]
theorem counitAlgHom_comp_orbitCoordinates (m : M) :
    (Bialgebra.counitAlgHom R H).comp (orbitCoordinates (H := H) m) =
      SymmetricAlgebra.lift (Module.Dual.eval R M m) := by
  ext φ
  simp [Bialgebra.counitAlgHom_apply]

end Coordinates

section Grading

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The images of the irrelevant ideal under orbit coordinates of a unimodular vector
generate the unit ideal. This defines a morphism on the whole group scheme. -/
theorem map_irrelevant_orbitCoordinates {m : M} (hm : Module.IsUnimodular R m) :
    (HomogeneousIdeal.irrelevant
      (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))).toIdeal.map
      (orbitCoordinates (H := H) m).toRingHom = ⊤ := by
  apply top_unique
  rw [← (span_matrixCoefficient_eq_top_iff_isUnimodular (H := H) m).mpr hm]
  refine Ideal.span_le.mpr (Set.range_subset_iff.mpr fun φ ↦ ?_)
  rw [← orbitCoordinates_ι m φ]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide)
    (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ))

end Grading

section Scheme

variable {R H M : Type u}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The projective orbit morphism of a unimodular vector in a finite projective Hopf comodule.
Its homogeneous coordinate functions are the vector's matrix coefficients. -/
noncomputable def projectiveOrbitMap (m : M) (hm : Module.IsUnimodular R m) :
    Spec (.of H) ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)) :=
  Proj.fromOfGlobalSections _
    ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (orbitCoordinates (H := H) m).toRingHom)
    (by rw [← Ideal.map_map, map_irrelevant_orbitCoordinates hm, Ideal.map_top])

/-- The orbit morphism is the morphism defined by its global homogeneous coordinate map. -/
theorem projectiveOrbitMap_def (m : M) (hm : Module.IsUnimodular R m) :
    projectiveOrbitMap (H := H) m hm =
      Proj.fromOfGlobalSections _
        ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (orbitCoordinates (H := H) m).toRingHom)
        (by rw [← Ideal.map_map, map_irrelevant_orbitCoordinates hm, Ideal.map_top]) := (rfl)

/-- The inverse image of a standard projective open is the principal open of its pulled-back
homogeneous coordinate function. -/
theorem projectiveOrbitMap_preimage_basicOpen (m : M) (hm : Module.IsUnimodular R m)
    {s : SymmetricAlgebra R (Module.Dual R M)} {n : ℕ} (hn : 0 < n)
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    projectiveOrbitMap (H := H) m hm ⁻¹ᵁ Proj.basicOpen _ s =
      (Spec (.of H)).basicOpen ((Scheme.ΓSpecIso (.of H)).inv (orbitCoordinates (H := H) m s)) := by
  rw [projectiveOrbitMap_def, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hs]
  rfl

/-- The standard open of a linear coordinate pulls back to the principal open of the
corresponding matrix coefficient. -/
@[simp]
theorem projectiveOrbitMap_preimage_basicOpen_ι (m : M) (hm : Module.IsUnimodular R m)
    (φ : Module.Dual R M) :
    projectiveOrbitMap (H := H) m hm ⁻¹ᵁ
        Proj.basicOpen _ (SymmetricAlgebra.ι R (Module.Dual R M) φ) =
      (Spec (.of H)).basicOpen ((Scheme.ΓSpecIso (.of H)).inv
        (matrixCoefficient (C := H) φ m)) := by
  simpa only [orbitCoordinates_ι] using projectiveOrbitMap_preimage_basicOpen m hm
    (by decide : 0 < 1) (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ)

/-- On every standard chart, the orbit morphism is obtained by localizing its matrix
coefficient coordinate map. -/
theorem projectiveOrbitMap_resLE (m : M) (hm : Module.IsUnimodular R m)
    {s : SymmetricAlgebra R (Module.Dual R M)} {n : ℕ} (hn : 0 < n)
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    (projectiveOrbitMap (H := H) m hm).resLE _ _
      (projectiveOrbitMap_preimage_basicOpen m hm hn hs).ge =
      Proj.toBasicOpenOfGlobalSections _
        ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (orbitCoordinates (H := H) m).toRingHom)
        rfl hn hs := by
  simp only [projectiveOrbitMap_def]
  exact Proj.fromOfGlobalSections_resLE _ _ _ hn hs

/-- The projective orbit morphism lies over the coordinate map on degree-zero elements. -/
@[reassoc]
theorem projectiveOrbitMap_toSpecZero (m : M) (hm : Module.IsUnimodular R m) :
    projectiveOrbitMap (H := H) m hm ≫
      Proj.toSpecZero (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)) =
      Spec.map (CommRingCat.ofHom ((orbitCoordinates (H := H) m).toRingHom.comp
        (algebraMap (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) 0)
          (SymmetricAlgebra R (Module.Dual R M))))) := by
  rw [projectiveOrbitMap_def, Proj.fromOfGlobalSections_toSpecZero]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    Category.assoc]
  rw [← Scheme.isoSpec_Spec_inv, Scheme.toSpecΓ_isoSpec_inv_assoc]

end Scheme

end TauCeti.Comodule
