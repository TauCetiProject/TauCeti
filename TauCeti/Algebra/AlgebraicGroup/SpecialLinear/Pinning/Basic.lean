/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# The standard pinning of the special linear group

For `SL_{r+1}`, the determinant-one diagonal torus and upper-triangular Borel determine
the consecutive simple roots `ε_i - ε_(i+1)`. The normalized matrix units `E_(i,i+1)`
trivialize their integral adjoint root spaces and give the standard pinning. This works
over every nontrivial commutative ring with connected spectrum, in particular over `ℤ`,
with no restriction on characteristic or reducedness. The weight characterizations below
do not require connectedness of the base.

The positive-root and simple-root characterizations identify the intrinsic definitions
with the base of `SpecialLinear.diagonalRootDatum`. The construction uses
`SpecialLinear.rootSpaceEquiv`, `SpecialLinear.splitMaximalTorus`, and the existing
upper-triangular tangent calculation. Indecomposability of the base is supplied by
`TauCeti.mem_support_iff_isPos_and_forall_ne_add`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
-/

public section

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] [Nontrivial R] {r : ℕ}

/-- The intrinsic positive roots for the standard special-linear torus and Borel are
exactly the positive roots of its diagonal root datum. -/
@[simp]
theorem isPositiveRoot_diagonalRoot_iff
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (splitMaximalTorus R r).IsPositiveRoot (UpperTriangular.definingHopfIdeal R (r + 1))
        ((diagonalRootDatum.{u} r).root p) ↔ (diagonalRootBase.{u} r).IsPos p := by
  have hvector :
      Derivation.cotangentLinearEquiv (B := R) (rootVector (R := R) p) ∈
          (UpperTriangular.definingHopfIdeal R (r + 1)).lieSubalgebra ↔
        (diagonalRootBase.{u} r).IsPos p := by
    rw [UpperTriangular.mem_lieSubalgebra_definingHopfIdeal_iff,
      tangentMatrix_cotangentLinearEquiv_rootVector,
      ← UpperTriangular.mem_matrixLieSubalgebra_iff,
      UpperTriangular.single_mem_matrixLieSubalgebra_iff _ _ _ _ one_ne_zero,
      diagonalRootBase_isPos_iff]
  rw [SplitMaximalTorus.isPositiveRoot_iff, splitMaximalTorus_coordinateMap]
  constructor
  · intro h
    have hx : rootVector (R := R) p ∈ Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap r R).hom
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) := by
      rw [adjointWeightSpace_root_eq_span]
      exact Submodule.mem_span_singleton_self _
    exact hvector.mp (h.2 _ hx)
  · intro hp
    refine ⟨ofAdd_root_mem_nontrivialAdjointWeights (R := R) p, ?_⟩
    intro x hx
    rw [adjointWeightSpace_root_eq_span, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_smul]
    exact (UpperTriangular.definingHopfIdeal R (r + 1)).lieSubalgebra.smul_mem c
      (hvector.mpr hp)

/-- Every intrinsic positive root is a positive root of the diagonal root datum. -/
theorem isPositiveRoot_iff_exists_diagonalRoot (α : ULift.{u} (Fin r) →₀ ℤ) :
    (splitMaximalTorus R r).IsPositiveRoot (UpperTriangular.definingHopfIdeal R (r + 1)) α ↔
      ∃ p : SplitTorus.CoordinateRootIndex (Fin (r + 1)),
        α = (diagonalRootDatum.{u} r).root p ∧ (diagonalRootBase.{u} r).IsPos p := by
  constructor
  · intro h
    have hweight := ((splitMaximalTorus R r).isPositiveRoot_iff
      (UpperTriangular.definingHopfIdeal R (r + 1)) α).mp h
    rw [splitMaximalTorus_coordinateMap] at hweight
    obtain ⟨p, hp⟩ := (mem_nontrivialAdjointWeights_iff_exists_diagonalRoot
      (R := R) (Multiplicative.ofAdd α)).mp hweight.1
    have heq := Multiplicative.ofAdd.injective hp
    exact ⟨p, heq, isPositiveRoot_diagonalRoot_iff p |>.mp (heq ▸ h)⟩
  · rintro ⟨p, rfl, hp⟩
    exact (isPositiveRoot_diagonalRoot_iff p).mpr hp

/-- The intrinsic simple roots are precisely the members of the consecutive-root base. -/
@[simp]
theorem isSimpleRoot_diagonalRoot_iff
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (splitMaximalTorus R r).IsSimpleRoot (UpperTriangular.definingHopfIdeal R (r + 1))
        ((diagonalRootDatum.{u} r).root p) ↔ p ∈ (diagonalRootBase.{u} r).support := by
  rw [SplitMaximalTorus.isSimpleRoot_iff, mem_support_iff_isPos_and_forall_ne_add]
  refine and_congr (isPositiveRoot_diagonalRoot_iff p) ?_
  constructor
  · intro h j k hj hk
    exact h _ _ ((isPositiveRoot_diagonalRoot_iff j).mpr hj)
      ((isPositiveRoot_diagonalRoot_iff k).mpr hk)
  · intro h β γ hβ hγ
    obtain ⟨j, rfl, hj⟩ := (isPositiveRoot_iff_exists_diagonalRoot β).mp hβ
    obtain ⟨k, rfl, hk⟩ := (isPositiveRoot_iff_exists_diagonalRoot γ).mp hγ
    exact h j k hj hk

/-- The consecutive simple roots exhaust the actual simple adjoint weights selected by
the upper-triangular Borel. -/
theorem isSimpleRoot_iff_exists_diagonalSimpleRoot (α : ULift.{u} (Fin r) →₀ ℤ) :
    (splitMaximalTorus R r).IsSimpleRoot (UpperTriangular.definingHopfIdeal R (r + 1)) α ↔
      ∃ i : Fin r, α = (diagonalRootDatum.{u} r).root (diagonalSimpleRootIndex r i) := by
  constructor
  · intro h
    have hpos := ((splitMaximalTorus R r).isSimpleRoot_iff
      (UpperTriangular.definingHopfIdeal R (r + 1)) α).mp h
    obtain ⟨p, rfl, _⟩ := (isPositiveRoot_iff_exists_diagonalRoot α).mp hpos.1
    obtain ⟨i, rfl⟩ := (mem_diagonalRootBase_support.{u} r p).mp
      ((isSimpleRoot_diagonalRoot_iff p).mp h)
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (isSimpleRoot_diagonalRoot_iff _).mpr
      ((mem_diagonalRootBase_support.{u} r _).mpr ⟨i, rfl⟩)

/-- Bourbaki numbering as an equivalence onto the intrinsic simple roots of the standard
special-linear torus and Borel. -/
def diagonalSimpleRootEquiv :
    Fin r ≃ {α // (splitMaximalTorus R r).IsSimpleRoot
      (UpperTriangular.definingHopfIdeal R (r + 1)) α} :=
  Equiv.ofBijective (fun i ↦ ⟨(diagonalRootDatum.{u} r).root (diagonalSimpleRootIndex r i),
    (isSimpleRoot_iff_exists_diagonalSimpleRoot _).mpr ⟨i, rfl⟩⟩) <| by
      constructor
      · intro i j h
        exact diagonalSimpleRootIndex_injective r
          ((diagonalRootDatum.{u} r).root.injective (congrArg Subtype.val h))
      · intro α
        obtain ⟨i, hi⟩ := (isSimpleRoot_iff_exists_diagonalSimpleRoot α.val).mp α.property
        exact ⟨i, Subtype.ext hi.symm⟩

/-- The intrinsic simple root at number `i` is the consecutive coordinate difference. -/
@[simp]
theorem diagonalSimpleRootEquiv_apply (i : Fin r) :
    (diagonalSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} r).root (diagonalSimpleRootIndex r i) := (rfl)

variable [ConnectedSpace (PrimeSpectrum R)]

/-- The standard integral pinning of `SL_{r+1}`: diagonal torus, upper-triangular Borel,
and normalized consecutive matrix-unit root vectors. -/
def standardPinning (R : Type u) [CommRing R] [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum R)] (r : ℕ) :
    Pinning R (coordinateHopfAlgebra R (r + 1)) r where
  reductive := by
    have h : finiteTypeCoordinateHopfAlgebra R (r + 1) =
        FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra R (r + 1)) := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      exact finiteTypeCoordinateHopfAlgebra_obj R (r + 1)
    exact h ▸ reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra R (r + 1)
  torus := splitMaximalTorus R r
  borel := UpperTriangular.definingHopfIdeal R (r + 1)
  isBorel := UpperTriangular.isBorelOver_definingHopfIdeal R (r + 1)
  borel_le_torus := UpperTriangular.definingHopfIdeal_le_splitMaximalTorus_definingIdeal R r
  rootSpaceEquiv α :=
    (rootSpaceEquiv (diagonalSimpleRootIndex r ((diagonalSimpleRootEquiv (R := R)).symm α))).trans
      (LinearEquiv.ofEq _ _ (by
        have h := congrArg Subtype.val ((diagonalSimpleRootEquiv (R := R)).apply_symm_apply α)
        rw [diagonalSimpleRootEquiv_apply] at h
        rw [splitMaximalTorus_coordinateMap, h]))

@[simp] theorem standardPinning_torus : (standardPinning R r).torus = splitMaximalTorus R r :=
  (rfl)

@[simp] theorem standardPinning_borel :
    (standardPinning R r).borel = UpperTriangular.definingHopfIdeal R (r + 1) := (rfl)

/-- Bourbaki numbering of the simple roots in the dependent type of the standard pinning. -/
def standardPinningSimpleRootEquiv :
    Fin r ≃ {α // (standardPinning R r).torus.IsSimpleRoot (standardPinning R r).borel α} :=
  diagonalSimpleRootEquiv (R := R)

/-- The pinning's numbered simple root has the consecutive-difference character. -/
@[simp]
theorem standardPinningSimpleRootEquiv_apply (i : Fin r) :
    (standardPinningSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} r).root (diagonalSimpleRootIndex r i) :=
  diagonalSimpleRootEquiv_apply i

/-- The chosen simple-root trivialization uses the normalized consecutive matrix unit.
This computation identifies the pinning's generators with the root-subgroup differentials. -/
@[simp]
theorem standardPinning_rootSpaceEquiv_apply_coe (i : Fin r) (c : R) :
    ((standardPinning R r).rootSpaceEquiv (standardPinningSimpleRootEquiv (R := R) i) c :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1)))) =
        c • rootVector (R := R) (diagonalSimpleRootIndex r i) := by
  simp only [standardPinning, standardPinningSimpleRootEquiv]
  -- The categorical character lattice and cotangent module use indexed presentations.
  erw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Equiv.symm_apply_apply, rootSpaceEquiv_apply_coe]

/-- The standard pinning chooses the normalized consecutive matrix-unit root vectors. -/
@[simp↓ 1100]
theorem standardPinning_rootVector (i : Fin r) :
    (standardPinning R r).rootVector (standardPinningSimpleRootEquiv (R := R) i) =
      rootVector (R := R) (diagonalSimpleRootIndex r i) := by
  -- The pinning and special-linear formulas use indexed cotangent presentations.
  erw [Pinning.rootVector_def, standardPinning_rootSpaceEquiv_apply_coe, one_smul]

end

end TauCeti.SpecialLinear
