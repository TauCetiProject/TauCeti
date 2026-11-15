/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Borel
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.PositiveRoots
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Adjoint
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# The standard integral pinning of the symplectic group

The paired diagonal torus and the complete isotropic flag Borel of `Sp₂ₘ` select the
Bourbaki-numbered type-C simple roots: the consecutive differences and the final long
root `2e_(m-1)`. Their normalized root-subgroup differentials trivialize the adjoint
root spaces and define a pinning over every nontrivial commutative ring with connected
spectrum. This includes `ℤ` and characteristic two, and also rank zero.

The simple-root characterizations identify the intrinsically defined simple roots
with the diagonal root base. The construction assembles the existing split maximal
torus, reductivity and Borel results, and the integral root-space trivializations.
It follows `TauCeti.SpecialLinear.standardPinning` and its numbering interface.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

namespace TauCeti.Symplectic

universe u

noncomputable section

variable {R : Type u} [CommRing R] [Nontrivial R] {m : ℕ}

/-- The intrinsic positive roots for the standard symplectic torus and Borel are
exactly the positive roots of its diagonal root datum. -/
@[simp]
theorem isPositiveRoot_diagonalRoot_iff
    (p : GLSymplecticFin.RootSubgroupIndex m) :
    (splitMaximalTorus R m).IsPositiveRoot (IsotropicFlag.definingHopfIdeal R m)
        ((diagonalRootDatum.{u} m).root p) ↔ (diagonalRootBase.{u} m).IsPos p := by
  rw [SplitMaximalTorus.isPositiveRoot_iff, splitMaximalTorus_coordinateMap]
  exact IsotropicFlag.nontrivialAdjointWeight_and_forall_mem_lieSubalgebra_iff p

/-- Every intrinsic positive root is a positive root of the diagonal root datum. -/
theorem isPositiveRoot_iff_exists_diagonalRoot (α : ULift.{u} (Fin m) →₀ ℤ) :
    (splitMaximalTorus R m).IsPositiveRoot (IsotropicFlag.definingHopfIdeal R m) α ↔
      ∃ p : GLSymplecticFin.RootSubgroupIndex m,
        α = (diagonalRootDatum.{u} m).root p ∧ (diagonalRootBase.{u} m).IsPos p := by
  rw [SplitMaximalTorus.isPositiveRoot_iff, splitMaximalTorus_coordinateMap]
  have h :=
    IsotropicFlag.mem_nontrivialAdjointWeights_and_forall_mem_lieSubalgebra_iff_exists_root_isPos
      (R := R) (m := m) (Multiplicative.ofAdd α)
  -- The intrinsic torus uses the same character lattice with an indexed presentation.
  convert h using 1
  · rfl
  · simp only [Multiplicative.ofAdd.injective.eq_iff]

/-- The intrinsic simple roots are precisely the members of the type-C root base. -/
@[simp]
theorem isSimpleRoot_diagonalRoot_iff
    (p : GLSymplecticFin.RootSubgroupIndex m) :
    (splitMaximalTorus R m).IsSimpleRoot (IsotropicFlag.definingHopfIdeal R m)
        ((diagonalRootDatum.{u} m).root p) ↔ p ∈ (diagonalRootBase.{u} m).support := by
  let : Finite (GLSymplecticFin.RootSubgroupIndex m) :=
    Finite.of_equiv (DynkinType.TypeCIndex m)
      (GLSymplecticFin.RootSubgroupIndex.equivTypeCIndex m).symm
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

/-- The numbered simple roots exhaust the actual simple adjoint weights selected by
the isotropic flag Borel. -/
theorem isSimpleRoot_iff_exists_diagonalSimpleRoot (α : ULift.{u} (Fin m) →₀ ℤ) :
    (splitMaximalTorus R m).IsSimpleRoot (IsotropicFlag.definingHopfIdeal R m) α ↔
      ∃ i : Fin m, α = (diagonalRootDatum.{u} m).root (diagonalSimpleRootIndex m i) := by
  constructor
  · intro h
    have hpos := ((splitMaximalTorus R m).isSimpleRoot_iff
      (IsotropicFlag.definingHopfIdeal R m) α).mp h
    obtain ⟨p, rfl, _⟩ := (isPositiveRoot_iff_exists_diagonalRoot α).mp hpos.1
    obtain ⟨i, hi⟩ := (mem_diagonalRootBase_support.{u} p).mp
      ((isSimpleRoot_diagonalRoot_iff p).mp h)
    exact ⟨i, congrArg (diagonalRootDatum.{u} m).root hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact (isSimpleRoot_diagonalRoot_iff _).mpr
      ((mem_diagonalRootBase_support.{u} _).mpr ⟨i, rfl⟩)

/-- Bourbaki numbering as an equivalence onto the intrinsic simple roots of the standard
symplectic torus and Borel. -/
def diagonalSimpleRootEquiv :
    Fin m ≃ {α // (splitMaximalTorus R m).IsSimpleRoot
      (IsotropicFlag.definingHopfIdeal R m) α} :=
  Equiv.ofBijective (fun i ↦ ⟨(diagonalRootDatum.{u} m).root (diagonalSimpleRootIndex m i),
    (isSimpleRoot_iff_exists_diagonalSimpleRoot _).mpr ⟨i, rfl⟩⟩) <| by
      constructor
      · intro i j h
        exact diagonalSimpleRootIndex_injective m
          ((diagonalRootDatum.{u} m).root.injective (congrArg Subtype.val h))
      · intro α
        obtain ⟨i, hi⟩ := (isSimpleRoot_iff_exists_diagonalSimpleRoot α.val).mp α.property
        exact ⟨i, Subtype.ext hi.symm⟩

/-- The intrinsic simple root at number `i` is the numbered type-C character. -/
@[simp]
theorem diagonalSimpleRootEquiv_apply (i : Fin m) :
    (diagonalSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} m).root (diagonalSimpleRootIndex m i) := (rfl)

variable [ConnectedSpace (PrimeSpectrum R)]

/-- The standard integral pinning of `Sp₂ₘ`: paired diagonal torus, isotropic flag Borel,
and normalized root-subgroup differentials. -/
def standardPinning (R : Type u) [CommRing R] [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum R)] (m : ℕ) :
    Pinning R (coordinateHopfAlgebra R m) m where
  reductive := by
    have h : finiteTypeCoordinateHopfAlgebra R m =
        FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra R m) := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      exact finiteTypeCoordinateHopfAlgebra_obj R m
    exact h ▸ reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra R m
  torus := splitMaximalTorus R m
  borel := IsotropicFlag.definingHopfIdeal R m
  isBorel := IsotropicFlag.isBorelOver_definingHopfIdeal R m
  borel_le_torus := IsotropicFlag.definingHopfIdeal_le_splitMaximalTorus_definingIdeal R m
  rootSpaceEquiv α :=
    (rootSpaceEquiv (diagonalSimpleRootIndex m ((diagonalSimpleRootEquiv (R := R)).symm α))).trans
      (LinearEquiv.ofEq _ _ (by
        have h := congrArg Subtype.val ((diagonalSimpleRootEquiv (R := R)).apply_symm_apply α)
        rw [diagonalSimpleRootEquiv_apply] at h
        rw [splitMaximalTorus_coordinateMap, h]
        -- Both sides use the same quotient-indexed adjoint comodule.
        rfl))

@[simp] theorem standardPinning_torus : (standardPinning R m).torus = splitMaximalTorus R m :=
  (rfl)

@[simp] theorem standardPinning_borel :
    (standardPinning R m).borel = IsotropicFlag.definingHopfIdeal R m := (rfl)

/-- Bourbaki numbering of the simple roots in the dependent type of the standard pinning. -/
def standardPinningSimpleRootEquiv :
    Fin m ≃ {α // (standardPinning R m).torus.IsSimpleRoot (standardPinning R m).borel α} :=
  diagonalSimpleRootEquiv (R := R)

/-- The pinning's numbered simple root has the numbered type-C character. -/
@[simp]
theorem standardPinningSimpleRootEquiv_apply (i : Fin m) :
    (standardPinningSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} m).root (diagonalSimpleRootIndex m i) :=
  diagonalSimpleRootEquiv_apply i

/-- The chosen simple-root trivialization uses the normalized root-subgroup differential.
This computation identifies the pinning's generators with the root-subgroup differentials. -/
@[simp]
theorem standardPinning_rootSpaceEquiv_apply_coe (i : Fin m) (c : R) :
    ((standardPinning R m).rootSpaceEquiv (standardPinningSimpleRootEquiv (R := R) i) c :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m))) =
        c • (Derivation.cotangentLinearEquiv (B := R)).symm
          (rootVector (R := R) (B := R) (diagonalSimpleRootIndex m i)) := by
  simp only [standardPinning, standardPinningSimpleRootEquiv]
  -- The categorical character lattice and cotangent module use indexed presentations.
  erw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Equiv.symm_apply_apply, rootSpaceEquiv_apply_coe]

/-- The standard pinning chooses the normalized root-subgroup differentials. -/
@[simp↓ 1100]
theorem standardPinning_rootVector (i : Fin m) :
    (standardPinning R m).rootVector (standardPinningSimpleRootEquiv (R := R) i) =
      (Derivation.cotangentLinearEquiv (B := R)).symm
        (rootVector (R := R) (B := R) (diagonalSimpleRootIndex m i)) := by
  -- The pinning and symplectic formulas use indexed cotangent presentations.
  erw [Pinning.rootVector_def, standardPinning_rootSpaceEquiv_apply_coe, one_smul]

end

end TauCeti.Symplectic
