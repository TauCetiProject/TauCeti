/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.MappingCone
public import TauCeti.Algebra.Homology.Periodic.Compression.MappingCone

/-!
# Compression is a triangle functor

The `n`-periodic compression `K^b(C) ⥤ K_n(C)` from the homotopy category of bounded cochain
complexes to the `n`-periodic homotopy category is a triangle functor
(`TauCeti.PeriodicComplex.homotopyCompressionFunctor_isTriangulated`), for every additive
category `C` and every period `n`.

Every distinguished triangle of `K^b(C)` is isomorphic to the image of the mapping-cone triangle
of a morphism `φ` of bounded complexes. The compression functor sends that image to the class of
the compression of the mapping-cone triangle of `φ`, with the shift datum descended from
`TauCeti.PeriodicComplex.compressionShiftIso`, and this compression is the periodic mapping-cone
triangle of the compression of `φ`, which is distinguished.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [HasFiniteCoproducts C] (n : ℕ)

/-- Compression of bounded complexes carries the mapping-cone triangle of `φ`, with the shift
datum `compressionFunctorShiftIso`, to the compression of the mapping-cone triangle of the
underlying morphism of cochain complexes. -/
@[expose, simps! hom_hom₁ hom_hom₂ hom_hom₃ inv_hom₁ inv_hom₂ inv_hom₃]
noncomputable def compressionFunctorMapTriangleMappingConeTriangleIso
    {K L : CochainComplex.Bounded C} (φ : K ⟶ L) :
    (compressionFunctor n).mapTriangle.obj (CochainComplex.Bounded.mappingConeTriangle φ) ≅
      compressionMappingConeTriangle n φ.hom :=
  Triangle.isoMk _ _ (eqToIso (compressionFunctor_obj n K)) (eqToIso (compressionFunctor_obj n L))
    (eqToIso (compressionFunctor_obj n _)) (by dsimp; simp) (by dsimp; simp) (by
      dsimp
      -- The shift datum of compression first undoes the comparison `(ι C).commShiftIso 1` used
      -- to type the third morphism of the bounded mapping-cone triangle.
      simp only [compressionFunctor_map, compressionFunctor_commShiftIso,
        compressionFunctorShiftIso_hom_app, ObjectProperty.homMk_hom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_map]
      rw [← compressionMap_comp_assoc, Category.assoc, Iso.inv_hom_id_app]
      simp)

/-- The compression functor `K^b(C) ⥤ K_n(C)` sends the image of the mapping-cone triangle of a
morphism `φ` of bounded complexes to the class of the compression of the mapping-cone triangle
of `φ`. -/
private noncomputable def homotopyCompressionFunctorMapTriangleIso
    {K L : CochainComplex.Bounded C} (φ : K ⟶ L) :
    (homotopyCompressionFunctor n).mapTriangle.obj
        ((HomotopyCategory.Bounded.quotient C).mapTriangle.obj
          (CochainComplex.Bounded.mappingConeTriangle φ)) ≅
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).mapTriangle.obj
        (compressionMappingConeTriangle n φ.hom) :=
  (Functor.mapTriangleCompIso (HomotopyCategory.Bounded.quotient C)
      (homotopyCompressionFunctor n)).symm.app _ ≪≫
    (Functor.mapTriangleIso (quotientCompHomotopyCompressionFunctorIso n)).app _ ≪≫
    (Functor.mapTriangleCompIso (compressionFunctor n)
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n)))).app _ ≪≫
    (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).mapTriangle.mapIso
      (compressionFunctorMapTriangleMappingConeTriangleIso n φ)

/-- **Compression is a triangle functor.** The `n`-periodic compression functor from the
homotopy category of bounded cochain complexes to the `n`-periodic homotopy category sends
distinguished triangles to distinguished triangles. -/
instance homotopyCompressionFunctor_isTriangulated [HasZeroObject C] :
    (homotopyCompressionFunctor (C := C) n).IsTriangulated :=
  HomotopyCategory.Bounded.isTriangulated_of_mappingConeTriangle _ fun φ ↦
    isomorphic_distinguished _ (compressionMappingConeTriangle_mem_distTriang n φ.hom) _
      (homotopyCompressionFunctorMapTriangleIso n φ)

end TauCeti.PeriodicComplex
