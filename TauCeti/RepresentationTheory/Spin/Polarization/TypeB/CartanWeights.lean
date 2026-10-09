/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Basis
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Representation

/-!
# Cartan weight spaces of the type-B spin module

The diagonal Cartan of the split odd orthogonal Lie algebra acts diagonally on the exterior
spinor basis. Its weights are the half-integral sign vectors, transported to the dual Cartan
by `typeBWeightEquiv`. Each weight occurs with multiplicity one, and there are no other
generalized weights. These statements use the canonical Lie-module weight spaces, so they
can be used directly in highest-weight theory.

The comparison with `spinWeightSpace` identifies the matrix Cartan action with the simultaneous
eigenspaces of the diagonal Clifford bivectors. The equality of honest and generalized weight
spaces follows from the existing weight-basis API; it requires neither algebraic closedness nor
characteristic zero.

## Main results

* `typeBSpinLieRep_apply_cartan_exteriorBasis`: the sign-vector eigenvalue formula.
* `weightSpace_typeBSpinLieRep_eq_spinWeightSpace`: the comparison with Clifford eigenspaces.
* `genWeightSpace_typeBSpinLieRep_eq_spinWeightSpace`: the same comparison for generalized weights.
* `genWeightSpace_typeBSpinLieRep_spinWeight`: every occurring weight space is a basis-vector line.
* `genWeightSpace_typeBSpinLieRep_ne_bot_iff`: the complete set of occurring weights.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.

The Cartan-action calculation follows the type-D comparison in
`TauCeti.RepresentationTheory.Spin.Polarization.TypeD.CartanWeights`.
-/

public section

open CliffordAlgebra LieModule Module

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- Every diagonal Cartan element acts on an exterior-basis spinor by its half-integral
sign-vector weight. -/
theorem typeBSpinLieRep_apply_cartan_exteriorBasis
    (A : typeBDiagonalCartan K ι) (s : Finset ι) :
    P.typeBSpinLieRep b z hz (A : LieAlgebra.Orthogonal.typeB ι K) (b.ExteriorAlgebra s) =
      typeBWeightEquiv (spinWeight K s) A • b.ExteriorAlgebra s := by
  let lhs : typeBDiagonalCartan K ι →ₗ[K] ExteriorAlgebra K P.W :=
    { toFun := fun A => P.typeBSpinLieRep b z hz
          (A : LieAlgebra.Orthogonal.typeB ι K) (b.ExteriorAlgebra s)
      map_add' := by simp
      map_smul' := by simp }
  let rhs := (typeBWeightEquiv (K := K) (spinWeight K s)).smulRight
    (b.ExteriorAlgebra s)
  have h : lhs = rhs :=
    (typeBDiagonalCartanBasis (K := K) (ι := ι)).ext fun i => by
      simp only [lhs, LinearMap.coe_mk, AddHom.coe_mk, coe_typeBDiagonalCartanBasis_apply]
      rw [P.typeBSpinLieRep_apply, P.typeBQuadraticEquiv_typeBDiagonalMatrix_single b z hz]
      rw [P.spinAction_diagonalBivector_basis]
      simp [rhs, Pi.single_apply]
  exact LinearMap.congr_fun h A

/-- The canonical Cartan weight space is the simultaneous eigenspace of the diagonal Clifford
bivectors with the corresponding coordinate eigenvalues. -/
theorem weightSpace_typeBSpinLieRep_eq_spinWeightSpace (χ : ι → K) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    (weightSpace (ExteriorAlgebra K P.W)
      (typeBWeightEquiv χ : typeBDiagonalCartan K ι → K)).toSubmodule =
        spinWeightSpace Q P b χ := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  ext x
  rw [LieSubmodule.mem_toSubmodule, mem_weightSpace, mem_spinWeightSpace_iff]
  constructor
  · intro hx i
    have hi := hx (typeBDiagonalCartanBasis (K := K) (ι := ι) i)
    simpa [LieRingModule.compLieHom_apply, P.typeBSpinLieRep_apply,
      P.typeBQuadraticEquiv_typeBDiagonalMatrix_single, Pi.single_apply] using hi
  · intro hx
    let lhs : typeBDiagonalCartan K ι →ₗ[K] ExteriorAlgebra K P.W :=
      (toEnd K (typeBDiagonalCartan K ι) (ExteriorAlgebra K P.W)).toLinearMap.flip x
    let rhs := (typeBWeightEquiv (K := K) χ).smulRight x
    have h : lhs = rhs :=
      (typeBDiagonalCartanBasis (K := K) (ι := ι)).ext fun i => by
        simpa [lhs, rhs, LieRingModule.compLieHom_apply, P.typeBSpinLieRep_apply,
          P.typeBQuadraticEquiv_typeBDiagonalMatrix_single, Pi.single_apply] using hx i
    exact LinearMap.congr_fun h

/-- The generalized Cartan weight space agrees with the honest Clifford eigenspace: the
exterior basis diagonalizes the whole Cartan action. -/
theorem genWeightSpace_typeBSpinLieRep_eq_spinWeightSpace (χ : ι → K) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    (genWeightSpace (ExteriorAlgebra K P.W)
      (typeBWeightEquiv χ : typeBDiagonalCartan K ι → K)).toSubmodule =
        spinWeightSpace Q P b χ := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  rw [b.ExteriorAlgebra.genWeightSpace_eq_weightSpace_of_weight_basis
    (μ := fun s => typeBWeightEquiv (spinWeight K s))
    (fun s A => P.typeBSpinLieRep_apply_cartan_exteriorBasis b z hz A s)]
  exact P.weightSpace_typeBSpinLieRep_eq_spinWeightSpace b z hz χ

/-- Each sign-vector generalized weight space of the type-B spin module is precisely the line
spanned by its exterior-basis vector. -/
@[simp]
theorem genWeightSpace_typeBSpinLieRep_spinWeight (s : Finset ι) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    (genWeightSpace (ExteriorAlgebra K P.W)
      (typeBWeightEquiv (spinWeight K s) : typeBDiagonalCartan K ι → K)).toSubmodule =
        K ∙ b.ExteriorAlgebra s := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  rw [P.genWeightSpace_typeBSpinLieRep_eq_spinWeightSpace b z hz]
  exact spinWeightSpace_spinWeight P b s

/-- The type-B spin module has exactly the half-integral sign-vector Cartan weights. This also
rules out any additional generalized weights. -/
@[simp]
theorem genWeightSpace_typeBSpinLieRep_ne_bot_iff
    (χ : typeBDiagonalCartan K ι → K) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    genWeightSpace (ExteriorAlgebra K P.W) χ ≠ ⊥ ↔
      ∃ s : Finset ι, (typeBWeightEquiv (spinWeight K s) : typeBDiagonalCartan K ι → K) = χ := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ := b.ExteriorAlgebra.linearWeights_of_weight_basis
    (μ := fun s => typeBWeightEquiv (spinWeight K s))
    (fun s A => P.typeBSpinLieRep_apply_cartan_exteriorBasis b z hz A s)
  constructor
  · intro hχ
    let wt : Weight K (typeBDiagonalCartan K ι) (ExteriorAlgebra K P.W) := ⟨χ, hχ⟩
    obtain ⟨c, hc⟩ := typeBWeightEquiv.surjective (wt : Module.Dual K (typeBDiagonalCartan K ι))
    have hfun : (typeBWeightEquiv c : typeBDiagonalCartan K ι → K) = χ := by
      simpa only [Weight.coe_coe, wt, Weight.coe_weight_mk] using congrArg DFunLike.coe hc
    have hspace : spinWeightSpace Q P b c ≠ ⊥ := by
      rw [ne_eq, ← P.genWeightSpace_typeBSpinLieRep_eq_spinWeightSpace b z hz,
        LieSubmodule.toSubmodule_eq_bot, hfun, ← ne_eq]
      exact hχ
    obtain ⟨s, hs⟩ := (spinWeightSpace_ne_bot_iff P b).mp hspace
    exact ⟨s, hs ▸ hfun⟩
  · rintro ⟨s, rfl⟩
    rw [ne_eq, ← LieSubmodule.toSubmodule_inj, LieSubmodule.bot_toSubmodule,
      P.genWeightSpace_typeBSpinLieRep_spinWeight b z hz,
      Submodule.span_singleton_eq_bot]
    exact b.ExteriorAlgebra.ne_zero s

end TauCeti.SpinPolarizationData
