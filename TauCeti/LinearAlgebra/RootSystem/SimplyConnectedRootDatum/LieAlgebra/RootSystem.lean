/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# The root system of the pinned rational Lie algebra

This file identifies the rational root system attached to a valid Dynkin type with the Killing
root system of its pinned rational Geck Lie algebra. The identification is pinned: on simple roots
it follows the common Bourbaki numbering supplied by `Fin t.rank`. Unlike
`RootPairing.GeckConstruction.equivRootSystem`, which assumes an algebraically closed coefficient
field, this construction works over `ℚ` by using the rational splitting and distinguished basis
already established for the pinned Lie algebra.

## Main declarations

* `TauCeti.DynkinType.rationalRootSystemEquiv`: the pinned equivalence from the rational root
  system to the Killing root system of the rational Lie algebra.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The support equivalence between the pinned rational base and the base of the distinguished
Lie-algebra basis, following the common Bourbaki numbering. -/
private def rationalLieBaseSupportEquiv :
    (t.rationalBase ht).support ≃ (t.lieBasis ht).base.support :=
  (t.simpleSupportEquiv ht).symm.trans (t.lieBasis ht).baseSupportEquiv

private theorem cartanMatrix_rationalLieBaseSupportEquiv (i j : (t.rationalBase ht).support) :
    (t.lieBasis ht).base.cartanMatrix (t.rationalLieBaseSupportEquiv ht i)
        (t.rationalLieBaseSupportEquiv ht j) =
      (t.rationalBase ht).cartanMatrix i j := by
  let a := (t.simpleSupportEquiv ht).symm i
  let b := (t.simpleSupportEquiv ht).symm j
  have hi : t.simpleSupportEquiv ht a = i := (t.simpleSupportEquiv ht).apply_symm_apply i
  have hj : t.simpleSupportEquiv ht b = j := (t.simpleSupportEquiv ht).apply_symm_apply j
  rw [← hi, ← hj]
  simp only [rationalLieBaseSupportEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    LieAlgebra.Basis.cartanMatrix_base_eq, Matrix.reindex_apply, Matrix.submatrix_apply,
    lieBasis_A_eq, cartanMatrix_rationalBase]

/-- **The pinned rational root system is equivalent to the Killing root system of the pinned
rational Lie algebra.** The equivalence sends each rational simple root to the root attached to
the correspondingly numbered generator of the distinguished Lie-algebra basis. -/
def rationalRootSystemEquiv :
    (t.rationalRootSystem ht).Equiv (rootSystem (t.cartanSubalgebra ht)) :=
  (t.rationalBase ht).equivOfCartanMatrixEq (t.lieBasis ht).base
    (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)

/-- The pinned root-system equivalence sends a Bourbaki-numbered simple root to the simple root
of the distinguished Lie-algebra basis with the same number. -/
@[simp] theorem rationalRootSystemEquiv_indexEquiv_simpleIndex (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i) =
      (t.lieBasis ht).baseSupportEquiv i := by
  simpa only [rationalRootSystemEquiv, rationalLieBaseSupportEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, coe_simpleSupportEquiv] using
    equivOfCartanMatrixEq_indexEquiv_apply (t.rationalBase ht) (t.lieBasis ht).base
      (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)
      (t.simpleSupportEquiv ht i)

/-- On a Bourbaki-numbered simple root, the weight equivalence lands at the simple Killing root
of the correspondingly numbered Lie-algebra generator. -/
@[simp] theorem rationalRootSystemEquiv_weightMap_root_simpleIndex (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).weightMap
        ((t.rationalRootSystem ht).root (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).root
        ((t.lieBasis ht).baseSupportEquiv i) := by
  calc
    _ = (rootSystem (t.cartanSubalgebra ht)).root
        ((t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i)) := by
      exact RootPairing.Hom.root_weightMap_apply _ _ (t.simpleIndex ht i)
        (t.rationalRootSystemEquiv ht).toHom
    _ = _ := congrArg _ (t.rationalRootSystemEquiv_indexEquiv_simpleIndex ht i)

/-- On a Bourbaki-numbered simple coroot, the covariant inverse coweight equivalence lands at the
simple Killing coroot of the correspondingly numbered Lie-algebra generator. -/
@[simp] theorem rationalRootSystemEquiv_coweightEquiv_symm_coroot_simpleIndex (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).coweightEquiv.symm
        ((t.rationalRootSystem ht).coroot (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).coroot
        ((t.lieBasis ht).baseSupportEquiv i) := by
  simpa only [rationalRootSystemEquiv, rationalLieBaseSupportEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, coe_simpleSupportEquiv] using
    equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot (t.rationalBase ht) (t.lieBasis ht).base
      (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)
      (t.simpleSupportEquiv ht i)

end


end TauCeti.DynkinType
