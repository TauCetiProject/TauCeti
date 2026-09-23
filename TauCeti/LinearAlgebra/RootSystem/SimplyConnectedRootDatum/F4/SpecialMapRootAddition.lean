/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap

/-!
# Root-addition transport under the F4 special map

The special matrix transports root-addition edges from the long-root side to the short-root side.
The coefficient on the source root is its exponent after applying the special root permutation;
this uniformly covers both possible source lengths without division in the integral root lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

private theorem f4SpecialIsogenyMatrix_mulVec_root_image (i : Fin 48) :
    Matrix.mulVec f4SpecialIsogenyMatrix
        (f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv i)) =
      f4Length (f4SpecialIsogenyIndexEquiv i) •
        f4SimplyConnectedRootDatum.root i := by
  rw [f4SpecialIsogenyMatrix_mulVec_root,
    show f4SpecialIsogenyIndexEquiv (f4SpecialIsogenyIndexEquiv i) = i by
      simpa only [f4SpecialIsogenyIndexEquiv_apply] using f4SpecialIsogenyIndex_involutive i]

private theorem f4SpecialIsogenyMatrix_mulVec_injective :
    Function.Injective (Matrix.mulVec f4SpecialIsogenyMatrix) :=
  Matrix.mulVec_injective_of_det_ne_zero (by simp)

/-- **Root-addition edges transport through the F4 special root permutation.** If `β` and `γ`
are long, applying the special matrix removes their exponent and leaves exactly the exponent of
the possibly short root `α`. -/
theorem f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
    (α β γ : Fin 48) (hβ : f4Length β = 2) (hγ : f4Length γ = 2) :
    f4SimplyConnectedRootDatum.root γ =
        f4SimplyConnectedRootDatum.root β +
          f4Length (f4SpecialIsogenyIndexEquiv α) •
            f4SimplyConnectedRootDatum.root α ↔
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α) := by
  have hβ' : f4Length (f4SpecialIsogenyIndexEquiv β) = 1 := by
    simpa only [f4SpecialIsogenyIndexEquiv_apply,
      f4Length_specialIsogenyIndex_eq_one_iff] using hβ
  have hγ' : f4Length (f4SpecialIsogenyIndexEquiv γ) = 1 := by
    simpa only [f4SpecialIsogenyIndexEquiv_apply,
      f4Length_specialIsogenyIndex_eq_one_iff] using hγ
  constructor
  · intro h
    apply f4SpecialIsogenyMatrix_mulVec_injective
    rw [Matrix.mulVec_add, f4SpecialIsogenyMatrix_mulVec_root_image,
      f4SpecialIsogenyMatrix_mulVec_root_image,
      f4SpecialIsogenyMatrix_mulVec_root_image, hβ', hγ', one_smul, one_smul, h]
  · intro h
    have h' := congrArg (Matrix.mulVec f4SpecialIsogenyMatrix) h
    simpa only [Matrix.mulVec_add, f4SpecialIsogenyMatrix_mulVec_root_image,
      hβ', hγ', one_smul] using h'

end TauCeti.DynkinType
