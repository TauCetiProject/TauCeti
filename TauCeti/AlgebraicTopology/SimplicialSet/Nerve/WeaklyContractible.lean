/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Weak contractibility of nerves with initial or terminal objects

If a category `C` has an initial or terminal object, the contracting simplicial homotopies from
`TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homotopy` show that `nerve C` is weakly contractible
(`CategoryTheory.Limits.isWeaklyContractible_nerve_of_hasInitial`,
`CategoryTheory.Limits.isWeaklyContractible_nerve_of_hasTerminal`).
-/

public section

universe v u

namespace CategoryTheory.Limits

instance isWeaklyContractible_nerve_of_hasInitial (C : Type u) [Category.{v} C] [HasInitial C] :
    SSet.IsWeaklyContractible (nerve C) :=
  SSet.IsWeaklyContractible.of_homotopy initialIsInitial.nerveHomotopy

instance isWeaklyContractible_nerve_of_hasTerminal (C : Type u) [Category.{v} C] [HasTerminal C] :
    SSet.IsWeaklyContractible (nerve C) :=
  SSet.IsWeaklyContractible.of_homotopy_id_const terminalIsTerminal.nerveHomotopy

end CategoryTheory.Limits
