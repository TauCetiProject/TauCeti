/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Flat
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Lifting
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Fppf-local lifts of projective orbit points

For a reduced finite-type affine group over an algebraically closed field, every
algebra-valued point of a projective orbit lifts to a group point after one faithfully
flat, finitely presented extension of the value algebra. No reducedness assumption is
made on the value algebra. Thus the geometric orbit map supplies the local lifts needed
to identify the orbit with the fppf homogeneous quotient by the line stabilizer.

The orbit map is affine because its source is affine and its target is separated.
Combine its flatness with `Scheme.Hom.exists_faithfullyFlat_lift`; the compatibility of
the orbit map with the base field lets Mathlib's `Spec.mapMulEquiv` recover an
algebra-valued group point from the lifted scheme morphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

variable [_root_.IsReduced H]

/-- Every algebra-valued point of the projective orbit lifts to a group point after a
faithfully flat, finitely presented extension of the value algebra. The value algebra
may be nonreduced, and no global lift over it is asserted. -/
theorem exists_faithfullyFlat_lift_toProjectiveOrbit
    (m : M) (hm : Module.IsUnimodular k m) (A : CommAlgCat.{u} k)
    (y : Spec (.of A) ⟶ projectiveOrbitScheme (H := H) m hm)
    (hy : y ≫ projectiveOrbitToSpec (H := H) m hm =
      Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (B : CommAlgCat.{u} k) (φ : A ⟶ B) (g : WithConv (H →ₐ[k] B)),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.toRingHom.FinitePresentation ∧
        Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫
            toProjectiveOrbit (H := H) m hm =
          Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ y := by
  obtain ⟨B, φ, z, hflat, hfp, hz⟩ :=
    (toProjectiveOrbit (H := H) m hm).exists_faithfullyFlat_lift y
  let : Algebra k B := (φ.hom.comp (algebraMap k A)).toAlgebra
  have hbase : z ≫ Spec.map (CommRingCat.ofHom (algebraMap k H)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    -- The algebra structure on `B` is induced by the composite `k → A → B`.
    have hscalar : CommRingCat.ofHom (algebraMap k B) =
        CommRingCat.ofHom (algebraMap k A) ≫ φ := rfl
    rw [hscalar]
    simpa [Category.assoc, hy, ← Spec.map_comp] using
      congrArg (fun t ↦ t ≫ projectiveOrbitToSpec (H := H) m hm) hz
  let z' : (Spec (.of B)).asOver (Spec (.of k)) ⟶
      (Spec (.of H)).asOver (Spec (.of k)) :=
    Over.homMk z (by
      simpa only [Scheme.asOver, OverClass.asOver, Over.mk_hom, specOverSpec_over] using hbase)
  let g : WithConv (H →ₐ[k] B) := Spec.mapMulEquiv.symm z'
  have hg : Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) = z := by
    -- The forward spectrum-points equivalence is `Spec.map`; project its round trip
    -- to the underlying scheme morphism.
    exact congrArg Over.Hom.left (Spec.mapMulEquiv.apply_symm_apply z')
  let φ' : A →ₐ[k] B := { φ.hom with commutes' := fun _ ↦ rfl }
  refine ⟨CommAlgCat.of k B, CommAlgCat.ofHom φ', g,
    hflat, hfp, ?_⟩
  simpa only [CommAlgCat.hom_ofHom, φ', CommRingCat.ofHom_hom, hg] using hz

end TauCeti.Comodule
