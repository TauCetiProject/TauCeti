/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Adjoint.WeightSpace
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Line

/-!
# Positive adjoint weights of the symplectic flag subgroup

A root of the diagonal type-C datum is a nontrivial adjoint weight whose whole weight space
lies in the standard isotropic flag Lie algebra exactly when it is positive in the standard
base. This is the intrinsic positivity condition used to select simple roots for a pinning.
The result holds over every nontrivial commutative ring, including characteristic two.

The argument combines the entrywise adjoint-weight criterion with recognition of represented
root-subgroup tangent images and the flag tangent equations. Its organization follows the
positive-root calculation in `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic`.
No Borel maximality assertion or choice of split maximal torus is needed for this calculation.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.Symplectic.IsotropicFlag

universe u

variable {R : Type u} [CommRing R] [Nontrivial R] {m : ℕ}

/-- A type-C root is a nontrivial adjoint weight with its entire root space in the flag
Lie algebra exactly when it is positive for the standard symplectic root base. -/
@[simp↓]
theorem nontrivialAdjointWeight_and_forall_mem_lieSubalgebra_iff
    (root : GLSymplecticFin.RootSubgroupIndex m) :
    (Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root) ∈
        Derivation.nontrivialAdjointWeights
          (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom ∧
      ∀ x ∈ Derivation.adjointWeightSpace
          (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom
          (Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root)),
        Derivation.cotangentLinearEquiv (B := R) x ∈ (definingHopfIdeal R m).lieSubalgebra) ↔
      (diagonalRootBase.{u} m).IsPos root := by
  -- The normalized root vector witnesses a nonzero weight space in every characteristic.
  let v := (Derivation.cotangentLinearEquiv (B := R)).symm
    (rootVector (R := R) (B := R) root)
  have hweights (i : Fin m ⊕ Fin m) :
      pairedCoordinateWeight.{u} i = diagonalTorusWeight i := by
    cases i <;> simp [Finsupp.single_neg]
  have hv : v ∈ Derivation.adjointWeightSpace
      (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root)) := by
    rw [mem_adjointWeightSpace_iff]
    intro i j hij
    rw [LinearEquiv.apply_symm_apply, tangentMatrix_rootVector]
    apply root.tangentMatrix_apply_eq_zero_of_int_eq_zero
    apply (tangentMatrix_apply_eq_zero_iff_root_ne.{u} root i j).mpr
    rw [hweights i, hweights j]
    exact fun h ↦ hij (congrArg Multiplicative.ofAdd h.symm)
  have hnontrivial : Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root) ∈
      Derivation.nontrivialAdjointWeights
        (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom := by
    rw [Derivation.mem_nontrivialAdjointWeights]
    refine ⟨?_, ?_⟩
    · simpa only [ne_eq, ofAdd_eq_one] using
        (diagonalRootDatum.{u} m).ne_zero root
    · intro hbot
      have hz := hv
      rw [hbot, Submodule.mem_bot] at hz
      have := congrArg (Derivation.cotangentLinearEquiv (B := R)) hz
      exact rootVector_ne_zero (R := R) (B := R) root
        (by simpa only [v, LinearEquiv.apply_symm_apply, map_zero] using this)
  refine ⟨fun h ↦ ?_, fun hpos ↦ ⟨hnontrivial, ?_⟩⟩
  · have h := h.2 v hv
    rw [LinearEquiv.apply_symm_apply] at h
    exact (rootVector_mem_lieSubalgebra_iff root).mp h
  -- Every vector of this weight is in the represented root-subgroup tangent image.
  · intro x hx
    have hentries := (mem_adjointWeightSpace_iff _ x).mp hx
    have hrange : Derivation.cotangentLinearEquiv (B := R) x ∈
        (derivationCompLieHom (B := R)
          (Symplectic.rootSubgroupCoordinateMap (R := R) root).hom).range := by
      rw [mem_range_derivationCompLieHom_rootSubgroup_iff]
      intro i j hij
      apply hentries i j
      rw [hweights i, hweights j] at hij
      exact fun h ↦ hij (Multiplicative.ofAdd.injective h.symm)
    rw [← LieSubalgebra.mem_toSubmodule,
      range_derivationCompLieHom_rootSubgroup_eq_span, Submodule.mem_span_singleton] at hrange
    obtain ⟨c, hc⟩ := hrange
    rw [← hc]
    exact (definingHopfIdeal R m).lieSubalgebra.smul_mem c
      (rootVector_mem_lieSubalgebra_of_isPos root hpos)

/-- The nontrivial adjoint characters whose whole weight space lies in the flag Lie algebra
are exactly the positive roots of the standard type-C datum. This also excludes characters
outside that root datum, over any nontrivial commutative base ring. -/
theorem mem_nontrivialAdjointWeights_and_forall_mem_lieSubalgebra_iff_exists_root_isPos
    (α : Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) :
    (α ∈ Derivation.nontrivialAdjointWeights
        (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom ∧
      ∀ x ∈ Derivation.adjointWeightSpace
          (Symplectic.diagonalTorusCoordinateMap (R := R) (m := m)).hom α,
        Derivation.cotangentLinearEquiv (B := R) x ∈ (definingHopfIdeal R m).lieSubalgebra) ↔
      ∃ root : GLSymplecticFin.RootSubgroupIndex m,
        α = Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root) ∧
          (diagonalRootBase.{u} m).IsPos root := by
  constructor
  · intro h
    obtain ⟨hα, hspace⟩ := Derivation.mem_nontrivialAdjointWeights.mp h.1
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspace
    have hmatrix : (tangentMatrix m (Derivation.cotangentLinearEquiv (B := R) x) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) ≠ 0 := by
      intro hz
      apply hx0
      apply (Derivation.cotangentLinearEquiv (B := R)).injective
      apply (tangentLieEquivSp (R := R) (B := R) m).injective
      apply Subtype.ext
      simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSp_apply (R := R) (B := R),
        map_zero, ZeroMemClass.coe_zero] using hz
    obtain ⟨i, j, hij⟩ : ∃ i j,
        (tangentMatrix m (Derivation.cotangentLinearEquiv (B := R) x) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j ≠ 0 := by
      by_contra! hz
      exact hmatrix (Matrix.ext hz)
    have hweight := ofAdd_diagonalTorusWeight_sub_eq_of_mem_adjointWeightSpace_of_apply_ne_zero
      hx hij
    have hdiff : diagonalTorusWeight i - diagonalTorusWeight j ≠ 0 := by
      intro hz
      rw [hz, ofAdd_zero] at hweight
      exact hα hweight.symm
    have hweights (i : Fin m ⊕ Fin m) :
        pairedCoordinateWeight.{u} i = diagonalTorusWeight i := by
      cases i <;> simp [Finsupp.single_neg]
    obtain ⟨root, hroot⟩ := exists_root_eq_pairedCoordinateWeight_sub.{u} i j
      (by simpa only [hweights] using hdiff)
    rw [hweights i, hweights j] at hroot
    have heq : α = Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root root) := by
      rw [hroot, hweight]
    refine ⟨root, heq, ?_⟩
    exact (nontrivialAdjointWeight_and_forall_mem_lieSubalgebra_iff root).mp (heq ▸ h)
  · rintro ⟨root, rfl, hroot⟩
    exact (nontrivialAdjointWeight_and_forall_mem_lieSubalgebra_iff root).mpr hroot

end TauCeti.Symplectic.IsotropicFlag
