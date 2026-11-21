/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# The Coxeter matrix of the numbered simply connected root datum

In the pinned datum `TauCeti.DynkinType.simplyConnectedRootDatum`, simple roots are numbered by
`Fin t.rank` in the Bourbaki order. This file records that, read through that numbering, the Coxeter
matrix of the pinned base is the standard Coxeter matrix `t.coxeterMatrix` of the type.

## Main results

* `TauCeti.DynkinType.coxeterMatrixOfBase_simplyConnectedBase`: the Coxeter matrix of the pinned
  base is `t.coxeterMatrix`, reindexed by
  `TauCeti.DynkinType.simpleSupportEquivSimplyConnectedBase`.
* `TauCeti.DynkinType.coxeterMatrixOfBase_simplyConnectedBase_apply`: its entries, in the
  numbering.
-/

public section

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The Coxeter matrix of the numbered base is the Bourbaki-numbered Coxeter matrix of the type. -/
theorem coxeterMatrixOfBase_simplyConnectedBase :
    coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) =
      t.coxeterMatrix.reindex (t.simpleSupportEquivSimplyConnectedBase ht) := by
  rw [coxeterMatrixOfBase_eq_coxeterMatrix_reindex
    (t.simpleSupportEquivSimplyConnectedBase ht).symm, Equiv.symm_symm]
  intro i j
  simpa using t.cartanMatrix_simplyConnectedBase_apply ht
    ((t.simpleSupportEquivSimplyConnectedBase ht).symm i)
    ((t.simpleSupportEquivSimplyConnectedBase ht).symm j)

/-- The entries of the Coxeter matrix of the numbered base are those of the Bourbaki-numbered
Coxeter matrix of the type. -/
theorem coxeterMatrixOfBase_simplyConnectedBase_apply (i j : Fin t.rank) :
    coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (t.simpleSupportEquivSimplyConnectedBase ht i)
        (t.simpleSupportEquivSimplyConnectedBase ht j) =
      t.coxeterMatrix i j := by
  rw [coxeterMatrixOfBase_simplyConnectedBase, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

end TauCeti.DynkinType
