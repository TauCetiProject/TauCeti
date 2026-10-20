/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.Pinning.BaseChange

/-!
# Base change of the standard general-linear pinning

The standard pinning of `GL_{r+1}` is compatible with scalar extension between
nontrivial commutative rings with connected spectra. Consecutive numbering identifies
its simple roots over both rings. The equivalence below identifies the scalar-extended
simple root spaces with the new simple root spaces and preserves their chosen generators.
Its ambient equation uses the geometric cotangent-dual base-change comparison, so it
certifies compatibility of the chosen trivializations, not just abstract rank-one freeness.

The other pinning data already commute with base change:
`GeneralLinear.splitMaximalTorus_baseChange_comapOfIso` treats the parametrized torus,
and `GeneralLinear.UpperTriangular.map_baseChangeHopfIdeal_definingHopfIdeal` treats
its Borel. The computation rules `standardPinning_torus` and `standardPinning_borel`
identify those data in the assembled pinning. Together these results identify the
integral pinning after extension to any nontrivial ring with connected spectrum.

## References

* `SpecialLinear.Pinning.BaseChange`: the corresponding special-linear construction.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
* The construction uses `GeneralLinear.standardPinning` and its normalized
  `standardPinning_rootSpaceEquiv_apply_coe` computation rule.
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
  [Nontrivial R] [Nontrivial K]
  [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum K)]
variable (r : ℕ)

/-- Scalar extension of the simple root space numbered `i`, preserving the
trivialization chosen by the standard pinning. -/
def standardPinningRootSpaceBaseChangeEquiv (i : Fin r) :
    K ⊗[R] Derivation.adjointWeightSpace (standardPinning R r).torus.coordinateMap.hom
        (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val) ≃ₗ[K]
      Derivation.adjointWeightSpace (standardPinning K r).torus.coordinateMap.hom
        (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := K) i).val) :=
  (standardPinning R r).rootSpaceBaseChangeEquiv (standardPinning K r)
    (standardPinningSimpleRootEquiv (R := R) i)
    (standardPinningSimpleRootEquiv (R := K) i)

/-- Forgetting the root-space restrictions identifies the base-change equivalence
with the geometric scalar extension of the ambient Lie algebra. -/
theorem standardPinningRootSpaceBaseChangeEquiv_tmul_coe (i : Fin r) (c : K)
    (x : Derivation.adjointWeightSpace (standardPinning R r).torus.coordinateMap.hom
      (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)) :
    (standardPinningRootSpaceBaseChangeEquiv R K r i (c ⊗ₜ[R] x) :
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K (r + 1)))) =
      cotangentDualBaseChangeEquiv R K (r + 1)
        (c ⊗ₜ[R] (x : Module.Dual R
          (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1))))) := by
  obtain ⟨b, rfl⟩ := ((standardPinning R r).rootSpaceEquiv
    (standardPinningSimpleRootEquiv (R := R) i)).surjective x
  rw [standardPinningRootSpaceBaseChangeEquiv, Pinning.rootSpaceBaseChangeEquiv_tmul]
  rw [standardPinning_rootSpaceEquiv_apply_coe,
    standardPinning_rootSpaceEquiv_apply_coe, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', cotangentDualBaseChangeEquiv_tmul_matrixUnitTangent]
  rw [Algebra.smul_def, mul_comm]

/-- The entire scalar-extended simple root space maps into the corresponding
simple root space by the ambient geometric comparison. -/
-- Use `rw`: `simp` does not match this dependent root-space coercion in importing modules.
theorem standardPinningRootSpaceBaseChangeEquiv_apply_coe (i : Fin r)
    (x : K ⊗[R] Derivation.adjointWeightSpace (standardPinning R r).torus.coordinateMap.hom
      (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)) :
    (standardPinningRootSpaceBaseChangeEquiv R K r i x :
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K (r + 1)))) =
      cotangentDualBaseChangeEquiv R K (r + 1)
        (LinearMap.baseChange K
          (Derivation.adjointWeightSpace (standardPinning R r).torus.coordinateMap.hom
            (Multiplicative.ofAdd (standardPinningSimpleRootEquiv (R := R) i).val)).subtype x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | tmul c x =>
    rw [LinearMap.baseChange_tmul]
    exact standardPinningRootSpaceBaseChangeEquiv_tmul_coe R K r i c x

/-- Scalar extension preserves the normalized simple-root generators of the standard
pinning. The rule runs before simplification of the dependent cotangent presentations. -/
@[simp↓]
theorem cotangentDualBaseChangeEquiv_tmul_standardPinning_rootVector (i : Fin r) (c : K) :
    cotangentDualBaseChangeEquiv R K (r + 1)
        (c ⊗ₜ[R] (standardPinning R r).rootVector
          (standardPinningSimpleRootEquiv (R := R) i)) =
      c • (standardPinning K r).rootVector (standardPinningSimpleRootEquiv (R := K) i) := by
  simp only [standardPinning_rootVector]
  exact cotangentDualBaseChangeEquiv_tmul_matrixUnitTangent R K i.castSucc i.succ c

end

end TauCeti.GeneralLinear
