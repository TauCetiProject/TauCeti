/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive.Rational
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.HighestWeight

/-!
# Primitive highest vectors in fundamental lattices

The distinguished highest vector of a fundamental representation is primitive in its
integral Kostant lattice. Thus an integral linear functional takes it to one, and its
scalar extensions remain detectable even in positive characteristic. The integral
normalization is supplied by `smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2, Corollary 1 to Theorem 2.
-/

public section

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The distinguished highest vector is primitive in its fundamental Kostant lattice. -/
theorem isPrimitive_fundamentalModuleGenerator (i : Fin t.rank) :
    IsPrimitive (⟨t.fundamentalModuleGenerator ht i,
      t.fundamentalModuleGenerator_mem_fundamentalLattice ht i⟩ :
        t.fundamentalLattice ht i) := by
  apply Submodule.isPrimitive_of_forall_smul_mem
  exact fun q hq => (t.smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff ht i q).mp hq

end TauCeti.DynkinType
