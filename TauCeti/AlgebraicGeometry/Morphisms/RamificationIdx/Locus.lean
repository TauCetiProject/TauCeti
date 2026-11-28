/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus.Basic

/-!
# Pointwise relation between ramification index and ramification locus

For a morphism `f : X ⟶ Y` locally of finite type, a point `x : X` lies outside
`f.ramificationLocus` iff `f.ramificationIdxAt x = 1` and `κ(x) / κ(f x)` is separable; see
`AlgebraicGeometry.Scheme.Hom.notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable`
below. In particular `f.ramificationIdxAt x = 1` outside `f.ramificationLocus`, and at a
quasi-finite point over a perfect residue field `κ(f x)`, `x ∈ f.ramificationLocus` iff
`f.ramificationIdxAt x ≠ 1`.
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Pointwise criterion for the ramification locus.** For `f` locally of finite type,
`x ∉ f.ramificationLocus` iff `f.ramificationIdxAt x = 1` and `κ(x) / κ(f x)` is separable. -/
theorem notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    x ∉ f.ramificationLocus ↔
      f.ramificationIdxAt x = 1 ∧
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have := essFiniteType_stalkMap_toAlgebra f x
  have hfu : (f.stalkMap x).hom.FormallyUnramified ↔
      Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap
  rw [mem_ramificationLocus_iff, not_not, hfu, Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]
  simp only [← isSeparable_residueFieldMap_iff, ramificationIdxAt_def,
    ramificationIdx_maximalIdeal_eq_one_iff_of_isLocalHom, and_comm]

/-- Outside `f.ramificationLocus` (for `f` locally of finite type), `f.ramificationIdxAt x = 1`. -/
theorem ramificationIdxAt_eq_one_of_notMem_ramificationLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hx : x ∉ f.ramificationLocus) :
    f.ramificationIdxAt x = 1 :=
  ((notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable f x).mp hx).1

/-- At a quasi-finite point over a perfect residue field `κ(f x)`, `x ∈ f.ramificationLocus` iff
`f.ramificationIdxAt x ≠ 1`. -/
theorem mem_ramificationLocus_iff_ramificationIdxAt_ne_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hqf : f.QuasiFiniteAt x)
    [PerfectField (Y.residueField (f x))] :
    x ∈ f.ramificationLocus ↔ f.ramificationIdxAt x ≠ 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := hqf.finite_residueField
  have hsep : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := inferInstance
  rw [← not_iff_not, not_not, notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hsep⟩⟩

end AlgebraicGeometry.Scheme.Hom
