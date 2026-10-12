/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.BaseChange

/-!
# Base change of the standard symplectic pinning

The standard pinning of `Sp₂ₘ` commutes with scalar extension between nontrivial
commutative rings with connected spectra. Bourbaki numbering identifies its simple
roots over both bases. The root-space comparison preserves the chosen rank-one
trivializations and agrees, after inclusion into the ambient cotangent dual, with
geometric tangent base change. In particular, the integral generators specialize
with their normalization intact, also in characteristic two and over nonreduced rings.

The other data of the pinning already commute with base change:
`Symplectic.splitMaximalTorus_baseChange_comapOfIso` treats the parametrized torus,
and `Symplectic.IsotropicFlag.map_baseChangeHopfIdeal_definingHopfIdeal` treats the
Borel. Together with the root-space comparison, these identify all the chosen data
of the integral pinning after extension to a connected nontrivial base.

The construction follows `SpecialLinear.Pinning.BaseChange`, using the symplectic
root-vector normalization `standardPinning_rootSpaceEquiv_apply_coe` and the geometric
comparison in `Symplectic.Tangent.BaseChange`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
-/

public section

open scoped TensorProduct

namespace TauCeti.Symplectic

universe u v

noncomputable section

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
  [Nontrivial R] [Nontrivial K]
  [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum K)]
variable (m : ℕ)

/-- Scalar extension of the numbered simple root space, preserving the
trivialization chosen by the standard symplectic pinning. -/
def standardPinningRootSpaceBaseChangeEquiv (i : Fin m) :
    K ⊗[R] Derivation.adjointWeightSpace (standardPinning R m).torus.coordinateMap.hom
        (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val) ≃ₗ[K]
      Derivation.adjointWeightSpace (standardPinning K m).torus.coordinateMap.hom
        (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := K) i).val) :=
  (((standardPinning R m).rootSpaceEquiv
    (standardPinningSimpleRootEquiv (R := R) i)).symm.baseChange R K _ _).trans
      ((TensorProduct.AlgebraTensorModule.rid R K K).trans
        ((standardPinning K m).rootSpaceEquiv
          (standardPinningSimpleRootEquiv (R := K) i)))

/-- The simple-root comparison preserves the chosen scalar coordinates. -/
@[simp↓]
theorem standardPinningRootSpaceBaseChangeEquiv_tmul (i : Fin m) (c : K) (b : R) :
    standardPinningRootSpaceBaseChangeEquiv R K m i
        (c ⊗ₜ[R] (standardPinning R m).rootSpaceEquiv
          (standardPinningSimpleRootEquiv (R := R) i) b) =
      (standardPinning K m).rootSpaceEquiv (standardPinningSimpleRootEquiv (R := K) i)
        (c * algebraMap R K b) := by
  simp only [standardPinningRootSpaceBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rw [mul_comm]

/-- The inverse comparison expresses a chosen vector over the new base as its
scalar coordinate times the chosen integral generator. -/
@[simp↓]
theorem standardPinningRootSpaceBaseChangeEquiv_symm_apply (i : Fin m) (c : K) :
    (standardPinningRootSpaceBaseChangeEquiv R K m i).symm
        ((standardPinning K m).rootSpaceEquiv
          (standardPinningSimpleRootEquiv (R := K) i) c) =
      c ⊗ₜ[R] (standardPinning R m).rootSpaceEquiv
        (standardPinningSimpleRootEquiv (R := R) i) 1 := by
  apply (standardPinningRootSpaceBaseChangeEquiv R K m i).symm_apply_eq.mpr
  rw [standardPinningRootSpaceBaseChangeEquiv_tmul R K m, map_one, mul_one]

/-- On pure tensors, the root-space comparison is the geometric scalar extension
of the ambient cotangent dual, not just an abstract rank-one identification. -/
theorem standardPinningRootSpaceBaseChangeEquiv_tmul_coe (i : Fin m) (c : K)
    (x : Derivation.adjointWeightSpace (standardPinning R m).torus.coordinateMap.hom
      (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)) :
    (standardPinningRootSpaceBaseChangeEquiv R K m i (c ⊗ₜ[R] x) :
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K m))) =
      cotangentDualBaseChangeEquiv R K m
        (c ⊗ₜ[R] (x : Module.Dual R
          (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m)))) := by
  obtain ⟨b, rfl⟩ := ((standardPinning R m).rootSpaceEquiv
    (standardPinningSimpleRootEquiv (R := R) i)).surjective x
  rw [standardPinningRootSpaceBaseChangeEquiv_tmul]
  -- The root-space inclusions use the quotient-indexed cotangent presentation.
  erw [standardPinning_rootSpaceEquiv_apply_coe,
    standardPinning_rootSpaceEquiv_apply_coe, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', cotangentDualBaseChangeEquiv_tmul_rootVector]
  rw [Algebra.smul_def, mul_comm]

/-- The scalar-extended simple root space maps into the corresponding simple
root space by the ambient geometric comparison. -/
@[simp↓]
theorem standardPinningRootSpaceBaseChangeEquiv_apply_coe (i : Fin m)
    (x : K ⊗[R] Derivation.adjointWeightSpace (standardPinning R m).torus.coordinateMap.hom
      (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)) :
    (standardPinningRootSpaceBaseChangeEquiv R K m i x :
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K m))) =
      cotangentDualBaseChangeEquiv R K m
        (LinearMap.baseChange K
          (Derivation.adjointWeightSpace (standardPinning R m).torus.coordinateMap.hom
            (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)).subtype x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | tmul c x =>
    rw [LinearMap.baseChange_tmul]
    exact standardPinningRootSpaceBaseChangeEquiv_tmul_coe R K m i c x

/-- Geometric scalar extension preserves the normalized simple-root generators
of the standard symplectic pinning. -/
@[simp↓]
theorem cotangentDualBaseChangeEquiv_tmul_standardPinning_rootVector (i : Fin m) (c : K) :
    cotangentDualBaseChangeEquiv R K m
        (c ⊗ₜ[R] (standardPinning R m).rootVector
          (standardPinningSimpleRootEquiv (R := R) i)) =
      c • (standardPinning K m).rootVector (standardPinningSimpleRootEquiv (R := K) i) := by
  simp only [standardPinning_rootVector]
  exact cotangentDualBaseChangeEquiv_tmul_rootVector R K (diagonalSimpleRootIndex m i) c

end

end TauCeti.Symplectic
