/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.RingTheory.Conductor

/-!
# The conductor of a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes. Over an affine open `U` of `Y`, the ring
`Γ(X, f⁻¹ U)` is a finite `Γ(Y, U)`-algebra, and its conductor `TauCeti.Algebra.conductor` is the
ideal of `a ∈ Γ(Y, U)` with `a • Γ(X, f⁻¹ U) ⊆ Γ(Y, U)`, the annihilator of the cokernel of
`𝒪_Y → f_* 𝒪_X` over `U`. Because the conductor of a finite algebra commutes with localization,
these ideals glue to the **conductor ideal sheaf** `f.conductor` of `Y`.

For the normalization `ν : X̃ ⟶ X` of a reduced curve, `ν.conductor` is the classical conductor,
whose zero locus is the set of non-normal points; for a nodal curve these are the nodes. In
general the conductor measures the failure of `f` to be a closed
immersion: `f.conductor = ⊤` exactly when `f` is a closed immersion
(`AlgebraicGeometry.Scheme.Hom.conductor_eq_top_iff`), and a point `y` of `Y` lies outside the
support of `f.conductor` exactly when `𝒪_Y → f_* 𝒪_X` is surjective over some affine
neighbourhood of `y` (`AlgebraicGeometry.Scheme.Hom.notMem_support_conductor_iff`).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.conductor f`: the conductor ideal sheaf of a finite morphism `f`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.conductor_ideal`: over an affine open `U`, it is the conductor of
  `Γ(X, f⁻¹ U)` over `Γ(Y, U)`.
* `AlgebraicGeometry.Scheme.Hom.conductor_of_isAffine`: over an affine target it is the ideal sheaf
  of the conductor of the global sections.
* `AlgebraicGeometry.Scheme.Hom.ker_le_conductor`: the kernel ideal sheaf of `f` is contained in
  the conductor.
* `AlgebraicGeometry.Scheme.Hom.conductor_eq_top_iff`: the conductor is the unit ideal sheaf
  exactly when `f` is a closed immersion.
* `AlgebraicGeometry.Scheme.Hom.notMem_support_conductor_iff`: the complement of the support of
  the conductor is the set of points over a neighbourhood of which `f` is surjective on
  sections.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter IV, §1, for the conductor of the
  normalization of a singular curve.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- Over a basic open `D(g)` of an affine open `U` of the target of a finite morphism `f`, the
conductor of `Γ(X, f⁻¹ D(g))` over `Γ(Y, D(g))` is the extension of the conductor of
`Γ(X, f⁻¹ U)` over `Γ(Y, U)`. -/
private theorem map_conductor_basicOpen (U : Y.affineOpens) (g : Γ(Y, U)) :
    letI := (f.app U).hom.toAlgebra
    letI := (f.app (Y.basicOpen g)).hom.toAlgebra
    (TauCeti.Algebra.conductor Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).map
        (Y.presheaf.map (homOfLE <| Y.basicOpen_le g).op).hom =
      TauCeti.Algebra.conductor Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  let := (f.app U).hom.toAlgebra
  let := (f.app (Y.basicOpen g)).hom.toAlgebra
  have hle : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ U.1 := f.preimage_mono (Y.basicOpen_le g)
  let : Algebra Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    ((Y.presheaf.map (homOfLE <| Y.basicOpen_le g).op) ≫ f.app (Y.basicOpen g)).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.naturality]
      rfl)
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := IsFinite.finite_app f U U.2
  have := U.2.isLocalization_basicOpen g
  -- `Γ(X, f⁻¹ D(g)) = Γ(X, D(f g))` is the localization of `Γ(X, f⁻¹ U)` at the image of `g`.
  have : IsLocalization.Away (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) g)
      Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (U.2.preimage f).isLocalization_of_eq_basicOpen _ (homOfLE hle) (f.preimage_basicOpen g)
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U) (.powers g))
      Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  exact (TauCeti.Algebra.conductor_eq_map (.powers g) Γ(Y, Y.basicOpen g)
    Γ(X, f ⁻¹ᵁ Y.basicOpen g)).symm

/-- The **conductor** of a finite morphism `f : X ⟶ Y`, an ideal sheaf on `Y`: over an affine
open `U` it is the conductor of `Γ(X, f⁻¹ U)` over `Γ(Y, U)`, the ideal of `a ∈ Γ(Y, U)` with
`a • Γ(X, f⁻¹ U) ⊆ Γ(Y, U)`, that is, the annihilator of the cokernel of `𝒪_Y → f_* 𝒪_X`. -/
def conductor : Y.IdealSheafData where
  ideal U := letI := (f.app U).hom.toAlgebra; TauCeti.Algebra.conductor Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  map_ideal_basicOpen U g := map_conductor_basicOpen f U g

/-- Over an affine open `U`, the conductor of `f` is the conductor of `Γ(X, f⁻¹ U)` over
`Γ(Y, U)`. -/
theorem conductor_ideal (U : Y.affineOpens) :
    f.conductor.ideal U =
      letI := (f.app U).hom.toAlgebra; TauCeti.Algebra.conductor Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (rfl)

/-- Over an affine target, the conductor of `f` is the ideal sheaf associated to the conductor of
`Γ(X, ⊤)` over `Γ(Y, ⊤)`. -/
theorem conductor_of_isAffine [IsAffine Y] :
    f.conductor = Scheme.IdealSheafData.ofIdealTop
      (letI := f.appTop.hom.toAlgebra; TauCeti.Algebra.conductor Γ(Y, ⊤) Γ(X, ⊤)) :=
  -- On an affine scheme an ideal sheaf is determined by its global sections, and over `⊤` the
  -- conductor of `f` is by definition that of `Γ(X, f⁻¹ ⊤) = Γ(X, ⊤)` over `Γ(Y, ⊤)`.
  (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply f.conductor).symm

/-- A section `a` over an affine open `U` lies in the conductor of `f` exactly when multiplication
by its image carries every section of `𝒪_X` over `f⁻¹ U` into the image of `Γ(Y, U)`. -/
@[simp]
theorem mem_conductor_ideal_iff {U : Y.affineOpens} {a : Γ(Y, U)} :
    a ∈ f.conductor.ideal U ↔ ∀ b : Γ(X, f ⁻¹ᵁ U), ∃ c : Γ(Y, U), f.app U c = f.app U a * b := by
  let := (f.app U).hom.toAlgebra
  exact TauCeti.Algebra.mem_conductor_iff

/-- The conductor of `f` is the unit ideal over an affine open `U` exactly when
`Γ(Y, U) → Γ(X, f⁻¹ U)` is surjective. -/
theorem conductor_ideal_eq_top_iff {U : Y.affineOpens} :
    f.conductor.ideal U = ⊤ ↔ Function.Surjective (f.app U) := by
  let := (f.app U).hom.toAlgebra
  exact TauCeti.Algebra.conductor_eq_top_iff

/-- The kernel ideal sheaf of a finite morphism is contained in its conductor. -/
theorem ker_le_conductor : f.ker ≤ f.conductor := fun U ↦ by
  let := (f.app U).hom.toAlgebra
  rw [f.ker_apply U]
  exact TauCeti.Algebra.ker_algebraMap_le_conductor

/-- **The conductor detects closed immersions.** The conductor of a finite morphism is the unit
ideal sheaf exactly when the morphism is a closed immersion. -/
theorem conductor_eq_top_iff : f.conductor = ⊤ ↔ IsClosedImmersion f := by
  rw [isClosedImmersion_iff_isAffineHom, and_iff_right (inferInstance : IsAffineHom f),
    Scheme.IdealSheafData.ext_iff, funext_iff]
  simp only [Scheme.IdealSheafData.ideal_top, Pi.top_apply, conductor_ideal_eq_top_iff]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U U.2⟩

/-- The conductor of a closed immersion is the unit ideal sheaf. -/
@[simp]
theorem conductor_eq_top [IsClosedImmersion f] : f.conductor = ⊤ :=
  (conductor_eq_top_iff f).mpr inferInstance

/-- **The support of the conductor.** A point `y` of `Y` lies outside the support of the
conductor of `f` exactly when it has an affine neighbourhood `U` over which
`Γ(Y, U) → Γ(X, f⁻¹ U)` is surjective. -/
theorem notMem_support_conductor_iff {y : Y} :
    y ∉ f.conductor.support ↔
      ∃ U : Y.affineOpens, y ∈ U.1 ∧ Function.Surjective (f.app U) := by
  refine ⟨fun hy ↦ ?_, fun ⟨U, hyU, hU⟩ ↦ ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
    -- Some section `a` of the conductor over `U` does not vanish at `y`; over `D(a)` the
    -- conductor contains the unit `a`, so it is the unit ideal there.
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hyU] at hy
    obtain ⟨a, ha, hya⟩ : ∃ a ∈ f.conductor.ideal ⟨U, hU⟩, y ∈ Y.basicOpen a := by
      simpa [Scheme.mem_zeroLocus_iff] using hy
    refine ⟨Y.affineBasicOpen a, hya, (f.conductor_ideal_eq_top_iff).mp
      ((f.conductor.map_ideal_basicOpen ⟨U, hU⟩ a).symm.trans ?_)⟩
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
      (Y.toRingedSpace.isUnit_res_basicOpen a)
  · rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyU,
      (f.conductor_ideal_eq_top_iff).mpr hU]
    simp [hyU]

end

end AlgebraicGeometry.Scheme.Hom
