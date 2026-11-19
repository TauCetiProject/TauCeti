/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# Kernels of dual isogenies and degree torsion

For an isogeny `φ : W₁ → W₂`, the identity `φ̂ ∘ φ = [deg φ]` gives an exact sequence
`ker φ → W₁[deg φ] → ker φ̂`. The first map is inclusion and the second is induced by `φ`.
Over a separably closed field, if `φ` is separable, the second map is surjective.
If `φ̂` is separable, applying this to the dual lifts every point of `ker φ` through `φ̂`
on degree torsion.

These are the native-point counterparts of `TauCeti.Isogeny.kerCoeffToTorsionCoeff` and
`TauCeti.Isogeny.torsionCoeffToDualKerCoeff` in
`TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion`.
There `TauCeti.Isogeny.torsionShortExact` packages the same sequence over a separable closure
as discrete Galois modules. Here the maps are defined over any field, without coefficient
or cohomology imports; surjectivity only needs separability of the relevant isogeny.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.6 and III.8.
-/

public section

noncomputable section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂)

/-- A point killed by an isogeny is killed by its degree. -/
theorem nsmul_eq_zero_of_mem_ker_pointMapHom {P : W₁.Point}
    (hP : P ∈ (Hom.ofIsogeny φ).pointMapHom.ker) : φ.degree • P = 0 := by
  rw [← φ.pointMap_dual_pointMap, (Hom.mem_ker_pointMapHom_iff _ _).mp hP]
  exact (Hom.ofIsogeny φ.dual).pointMap_zero

/-- The inclusion of an isogeny's kernel in the torsion subgroup at its degree. -/
def kerToTorsion : (Hom.ofIsogeny φ).pointMapHom.ker →+
    Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ) :=
  AddSubgroup.inclusion (K := (Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)).toAddSubgroup)
    fun P hP ↦ by
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul]
      exact φ.nsmul_eq_zero_of_mem_ker_pointMapHom hP

/-- Inclusion in degree torsion does not change the underlying point. -/
@[simp]
theorem coe_kerToTorsion (P : (Hom.ofIsogeny φ).pointMapHom.ker) :
    (φ.kerToTorsion P : W₁.Point) = P :=
  (rfl)

/-- The isogeny kills every point in the image of its kernel inclusion. -/
theorem pointMap_kerToTorsion (P : (Hom.ofIsogeny φ).pointMapHom.ker) :
    (Hom.ofIsogeny φ).pointMap (φ.kerToTorsion P) = 0 := by
  rw [coe_kerToTorsion]
  exact (Hom.mem_ker_pointMapHom_iff _ _).mp P.property

/-- The map from the kernel to degree torsion is injective. -/
theorem kerToTorsion_injective : Function.Injective φ.kerToTorsion :=
  AddSubgroup.inclusion_injective _

/-- The map from degree torsion to the dual kernel, `R ↦ φ R`. -/
def torsionToDualKer :
    Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ) →+
      (Hom.ofIsogeny φ.dual).pointMapHom.ker where
  toFun R := ⟨(Hom.ofIsogeny φ).pointMap R, by
    rw [Hom.mem_ker_pointMapHom_iff, φ.pointMap_dual_pointMap]
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using R.property⟩
  map_zero' := Subtype.ext ((Hom.ofIsogeny φ).pointMap_zero)
  map_add' R S := Subtype.ext ((Hom.ofIsogeny φ).pointMap_add R S)

/-- The map to the dual kernel is the original isogeny on underlying points. -/
@[simp]
theorem coe_torsionToDualKer (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    (φ.torsionToDualKer R : W₂.Point) = (Hom.ofIsogeny φ).pointMap R :=
  (rfl)

/-- The dual sends degree torsion into the original kernel. -/
theorem dual_pointMap_mem_ker_pointMapHom
    (S : Submodule.torsionBy ℤ W₂.Point (φ.degree : ℤ)) :
    (Hom.ofIsogeny φ.dual).pointMap S ∈ (Hom.ofIsogeny φ).pointMapHom.ker := by
  rw [Hom.mem_ker_pointMapHom_iff, φ.pointMap_pointMap_dual]
  simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using S.property

/-- The kernel of the map from degree torsion consists exactly of the points killed by `φ`. -/
@[simp]
theorem torsionToDualKer_eq_zero_iff
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    φ.torsionToDualKer R = 0 ↔ (Hom.ofIsogeny φ).pointMap R = 0 :=
  Subtype.ext_iff

/-- The image of the kernel inclusion is exactly the degree-torsion points killed by `φ`.
Together with `torsionToDualKer_eq_zero_iff`, this expresses exactness at degree
torsion. -/
theorem mem_range_kerToTorsion_iff
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    R ∈ φ.kerToTorsion.range ↔ (Hom.ofIsogeny φ).pointMap R = 0 := by
  constructor
  · rintro ⟨P, rfl⟩
    exact φ.pointMap_kerToTorsion P
  · intro hR
    refine ⟨⟨R, (Hom.mem_ker_pointMapHom_iff _ _).mpr hR⟩, ?_⟩
    exact Subtype.ext (φ.coe_kerToTorsion _)

variable [IsSepClosed F]

/-- For a separable isogeny, every point of the dual kernel is the image under `φ` of a
degree-torsion point. -/
theorem torsionToDualKer_surjective
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    Function.Surjective φ.torsionToDualKer := by
  intro Q
  obtain ⟨R, hR⟩ := φ.toPointHom_surjective (Q : W₂.Point)
  rw [← Hom.pointMap_ofIsogeny_eq_toPointHom] at hR
  refine ⟨⟨R, ?_⟩, Subtype.ext hR⟩
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← φ.pointMap_dual_pointMap, hR]
  exact (Hom.mem_ker_pointMapHom_iff _ _).mp Q.property

/-- If the dual is separable, every point killed by `φ` lifts through `φ̂` on degree torsion. -/
theorem exists_dual_pointMap_eq_of_mem_ker
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField] {P : W₁.Point}
    (hP : P ∈ (Hom.ofIsogeny φ).pointMapHom.ker) :
    ∃ S : Submodule.torsionBy ℤ W₂.Point (φ.degree : ℤ),
      (Hom.ofIsogeny φ.dual).pointMap S = P := by
  obtain ⟨S, hS⟩ := φ.dual.toPointHom_surjective P
  rw [← Hom.pointMap_ofIsogeny_eq_toPointHom] at hS
  refine ⟨⟨S, ?_⟩, hS⟩
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← φ.pointMap_pointMap_dual, hS]
  exact (Hom.mem_ker_pointMapHom_iff _ _).mp hP

end TauCeti.Isogeny
