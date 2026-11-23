/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.RepresentationTheory.Continuous.Hom
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.Topology.Algebra.Star.Unitary

/-!
# Group homomorphisms induced by unitary continuous representations

When `V` is a Hilbert space over `𝕜` (`ℝ` or `ℂ`) and `π : ContRepresentation 𝕜 G V` is unitary,
its operators land in `unitary (V →L[𝕜] V)` and in the closed subgroup
`unitarySubgroup (V →L[𝕜] V)ˣ`. Because inversion on unitary operators is the isometric adjoint,
continuity of `π : G → (V →L[𝕜] V)` alone upgrades all of these homomorphisms to
`ContinuousMonoidHom`s (and makes `π.toMonoidHom.toHomUnits` continuous without assuming
continuity of inversion on `G`), and on `EuclideanSpace 𝕜 ι` transports them to
`Matrix.unitaryGroup ι 𝕜`.

For the general (nonunitary) homomorphism into `(V →L[𝕜] V)ˣ` and the no-small-subgroups criterion
for injective representations, see `TauCeti.RepresentationTheory.Continuous.Hom`.

## Main definitions and results

* `ContRepresentation.IsUnitary.toUnitaryMonoidHom`,
  `ContRepresentation.IsUnitary.toUnitaryContinuousMonoidHom`: homomorphism into
  `unitary (V →L[𝕜] V)`.
* `ContRepresentation.IsUnitary.continuous_toHomUnits`: continuity of `π.toMonoidHom.toHomUnits`
  for a unitary representation without assuming continuity of inversion on `G`.
* `ContRepresentation.IsUnitary.toUnitarySubgroupHom`: continuous homomorphism into
  `unitarySubgroup (V →L[𝕜] V)ˣ`.
* `ContRepresentation.IsUnitary.toMatrixUnitaryGroupHom`: continuous homomorphism from a unitary
  representation on `EuclideanSpace 𝕜 ι` into `Matrix.unitaryGroup ι 𝕜`.
-/

public section

noncomputable section

namespace ContRepresentation

namespace IsUnitary

section HilbertSpace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [CompleteSpace V] {π : ContRepresentation 𝕜 G V}

/-- A unitary group representation as a group homomorphism into `unitary (V →L[𝕜] V)`. -/
def toUnitaryMonoidHom (hπ : π.IsUnitary) : G →* unitary (V →L[𝕜] V) where
  toFun g := ⟨π g, hπ.mem_unitary g⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' g h := Subtype.ext (map_mul π g h)

/-- The operator underlying `hπ.toUnitaryMonoidHom g` is `π g`. -/
@[simp]
theorem coe_toUnitaryMonoidHom_apply (hπ : π.IsUnitary) (g : G) :
    (hπ.toUnitaryMonoidHom g : V →L[𝕜] V) = π g :=
  (rfl)

/-- `hπ.toUnitaryMonoidHom` has the same kernel as `π`. -/
@[simp]
theorem ker_toUnitaryMonoidHom (hπ : π.IsUnitary) :
    hπ.toUnitaryMonoidHom.ker = π.toMonoidHom.ker := by
  ext g
  simp [MonoidHom.mem_ker, Subtype.ext_iff, toMonoidHom_apply]

/-- `hπ.toUnitaryMonoidHom` is injective if and only if `π` is injective. -/
@[simp]
theorem injective_toUnitaryMonoidHom_iff (hπ : π.IsUnitary) :
    Function.Injective hπ.toUnitaryMonoidHom ↔ Function.Injective π :=
  ⟨fun h _ _ hxy ↦ h (Subtype.ext hxy), fun h _ _ hxy ↦ h (congrArg Subtype.val hxy)⟩

/-- Continuity of `π` passes to `hπ.toUnitaryMonoidHom`. -/
theorem continuous_toUnitaryMonoidHom [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) : Continuous hπ.toUnitaryMonoidHom :=
  hπc.subtype_mk _

/-- A continuous unitary group representation as a continuous group homomorphism into
`unitary (V →L[𝕜] V)`. -/
def toUnitaryContinuousMonoidHom [TopologicalSpace G] (hπ : π.IsUnitary) (hπc : Continuous π) :
    G →ₜ* unitary (V →L[𝕜] V) :=
  ⟨hπ.toUnitaryMonoidHom, hπ.continuous_toUnitaryMonoidHom hπc⟩

/-- Evaluation of `IsUnitary.toUnitaryContinuousMonoidHom`. -/
@[simp]
theorem coe_toUnitaryContinuousMonoidHom [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) :
    ⇑(hπ.toUnitaryContinuousMonoidHom hπc) = hπ.toUnitaryMonoidHom :=
  (rfl)

/-- For a unitary representation, `π.toMonoidHom.toHomUnits` is continuous as soon as `π` is,
without assuming continuity of inversion on `G`. -/
theorem continuous_toHomUnits [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) : Continuous π.toMonoidHom.toHomUnits := by
  have heq : ⇑π.toMonoidHom.toHomUnits = Unitary.toUnits ∘ hπ.toUnitaryMonoidHom := by
    funext g
    exact Units.ext rfl
  rw [heq]
  exact Unitary.continuous_toUnits.comp (hπ.continuous_toUnitaryMonoidHom hπc)

/-- Every unit `π.toMonoidHom.toHomUnits g` of a unitary representation belongs to
`unitarySubgroup (V →L[𝕜] V)ˣ`. -/
theorem toHomUnits_mem_unitarySubgroup (hπ : π.IsUnitary) (g : G) :
    π.toMonoidHom.toHomUnits g ∈ unitarySubgroup (V →L[𝕜] V)ˣ :=
  mem_unitarySubgroup_iff.mpr (TauCeti.mem_unitary_units_iff.mpr (hπ.mem_unitary g))

/-- A continuous unitary group representation as a continuous group homomorphism into
`unitarySubgroup (V →L[𝕜] V)ˣ`. -/
def toUnitarySubgroupHom [TopologicalSpace G] (hπ : π.IsUnitary) (hπc : Continuous π) :
    G →ₜ* unitarySubgroup (V →L[𝕜] V)ˣ where
  toMonoidHom := π.toMonoidHom.toHomUnits.codRestrict (unitarySubgroup (V →L[𝕜] V)ˣ)
    hπ.toHomUnits_mem_unitarySubgroup
  continuous_toFun := (hπ.continuous_toHomUnits hπc).subtype_mk _

/-- The operator underlying `hπ.toUnitarySubgroupHom hπc g` is `π g`. -/
@[simp]
theorem val_coe_toUnitarySubgroupHom_apply [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) (g : G) :
    ((hπ.toUnitarySubgroupHom hπc g : (V →L[𝕜] V)ˣ) : V →L[𝕜] V) = π g :=
  (rfl)

/-- `hπ.toUnitarySubgroupHom hπc` has the same kernel as `π`. -/
@[simp]
theorem ker_toUnitarySubgroupHom [TopologicalSpace G] (hπ : π.IsUnitary) (hπc : Continuous π) :
    (hπ.toUnitarySubgroupHom hπc : G →* unitarySubgroup (V →L[𝕜] V)ˣ).ker =
      π.toMonoidHom.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, Units.ext_iff]
  rfl

/-- `hπ.toUnitarySubgroupHom hπc` is injective if and only if `π` is injective. -/
@[simp]
theorem injective_toUnitarySubgroupHom_iff [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) :
    Function.Injective (hπ.toUnitarySubgroupHom hπc) ↔ Function.Injective π :=
  ⟨fun h _ _ hxy ↦ h (Subtype.ext (Units.ext hxy)),
    fun h _ _ hxy ↦ h (congrArg (fun u : unitarySubgroup (V →L[𝕜] V)ˣ ↦ ((u : (V →L[𝕜] V)ˣ) :
      V →L[𝕜] V)) hxy)⟩

end HilbertSpace

section Euclidean

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Group G] [Fintype ι] [DecidableEq ι]
  {π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 ι)}

/-- A continuous unitary representation on `EuclideanSpace 𝕜 ι`, bundled as a continuous group
homomorphism into `Matrix.unitaryGroup ι 𝕜`. -/
def toMatrixUnitaryGroupHom [TopologicalSpace G] (hπ : π.IsUnitary) (hπc : Continuous π) :
    G →ₜ* Matrix.unitaryGroup ι 𝕜 where
  toFun g := ⟨(Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (π g),
    Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (hπ.mem_unitary g)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)
  continuous_toFun := (Matrix.continuous_toEuclideanCLM_symm.comp hπc).subtype_mk _

/-- The matrix underlying `hπ.toMatrixUnitaryGroupHom hπc g` is
`(Matrix.toEuclideanCLM).symm (π g)`. -/
@[simp]
theorem coe_toMatrixUnitaryGroupHom_apply [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) (g : G) :
    (hπ.toMatrixUnitaryGroupHom hπc g : Matrix ι ι 𝕜) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (π g) :=
  (rfl)

/-- Applying `Matrix.toEuclideanCLM` to `hπ.toMatrixUnitaryGroupHom hπc g` recovers `π g`. -/
theorem toEuclideanCLM_toMatrixUnitaryGroupHom_apply [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) (g : G) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) (hπ.toMatrixUnitaryGroupHom hπc g : Matrix ι ι 𝕜) =
      π g :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).apply_symm_apply (π g)

/-- `hπ.toMatrixUnitaryGroupHom hπc` has the same kernel as `π`. -/
@[simp]
theorem ker_toMatrixUnitaryGroupHom [TopologicalSpace G] (hπ : π.IsUnitary) (hπc : Continuous π) :
    (hπ.toMatrixUnitaryGroupHom hπc : G →* Matrix.unitaryGroup ι 𝕜).ker =
      π.toMonoidHom.ker := by
  ext g
  simp only [MonoidHom.mem_ker, Subtype.ext_iff, OneMemClass.coe_one, toMonoidHom_apply]
  exact ⟨fun h ↦ by simpa using congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)) h,
    fun h ↦ by simp [h]⟩

/-- `hπ.toMatrixUnitaryGroupHom hπc` is injective if and only if `π` is injective. -/
@[simp]
theorem injective_toMatrixUnitaryGroupHom_iff [TopologicalSpace G] (hπ : π.IsUnitary)
    (hπc : Continuous π) :
    Function.Injective (hπ.toMatrixUnitaryGroupHom hπc) ↔ Function.Injective π := by
  refine ⟨fun h _ _ hxy ↦ h (Subtype.ext (congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm
    hxy)), fun h _ _ hxy ↦ h ?_⟩
  simpa using congrArg
    (fun U : Matrix.unitaryGroup ι 𝕜 ↦ Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) (U : Matrix ι ι 𝕜))
    hxy

end Euclidean

end IsUnitary

end ContRepresentation
