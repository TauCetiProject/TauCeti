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

/-- `f.residueFieldMap x` acts on residues via `f.stalkMap x`. -/
private theorem residueFieldMap_residue {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (a : Y.presheaf.stalk (f x)) :
    ((f.residueFieldMap x).hom (IsLocalRing.residue _ a) :
        IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      IsLocalRing.residue _ ((f.stalkMap x).hom a) :=
  -- `Hom.residueFieldMap f x` is defined as
  -- `CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)`.
  (rfl)

/-- **Pointwise criterion for the ramification locus.** For `f` locally of finite type,
`x ∉ f.ramificationLocus` iff `f.ramificationIdxAt x = 1` and `κ(x) / κ(f x)` is separable. -/
theorem notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    x ∉ f.ramificationLocus ↔
      f.ramificationIdxAt x = 1 ∧
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  let R := Y.presheaf.stalk (f x); let S := X.presheaf.stalk x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType R S :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)
  have halg : (f.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (ResidueField R) (ResidueField S)) := by
    apply Algebra.algebra_ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    rw [RingHom.algebraMap_toAlgebra, residueFieldMap_residue]
    -- `Algebra.algebra_ext` leaves `Y.residueField (f x)` / `X.residueField x` on the RHS,
    -- which only match `ResidueField R` / `ResidueField S` at default transparency so `rw` fails.
    change IsLocalRing.residue S ((f.stalkMap x).hom a) =
      algebraMap (ResidueField R) (ResidueField S) (IsLocalRing.residue R a)
    rw [ResidueField.algebraMap_residue, RingHom.algebraMap_toAlgebra]
  have hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S) ↔
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) :=
    iff_of_eq (congrArg (fun inst ↦ @Algebra.IsSeparable (ResidueField R) (ResidueField S) _ _ inst)
      halg.symm)
  rw [mem_ramificationLocus_iff, not_not, RingHom.FormallyUnramified,
    ← RingHom.algebraMap_toAlgebra (f.stalkMap x).hom,
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, hsep, ramificationIdxAt_def,
    ramificationIdx_maximalIdeal_eq_one_iff, Ideal.under, maximalIdeal_comap, and_comm]

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
