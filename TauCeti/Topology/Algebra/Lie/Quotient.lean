/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The quotient topology on quotients of Lie modules

Mathlib defines the quotient `M ⧸ N` of a Lie module by a Lie submodule as the quotient
`M ⧸ N.toSubmodule` of the underlying module, and transfers the additive group and module
structures to it explicitly. This file transfers the quotient topology in the same way, so that a
quotient of a topological Lie algebra by a Lie ideal, such as an algebra of outer derivations, is a
topological additive group whose quotient map is open.

## Main definitions

* `LieSubmodule.Quotient.topologicalSpace`: the quotient topology on `M ⧸ N`.

## Main results

* `LieSubmodule.Quotient.isOpenQuotientMap_mk`: the quotient map of a Lie module is an open
  quotient map.
* `LieIdeal.isOpenQuotientMap_mkQ`: the quotient homomorphism of a Lie algebra by a Lie ideal is an
  open quotient map.
-/

public section

namespace LieSubmodule.Quotient

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [TopologicalSpace M] {N : LieSubmodule R L M}

/-- The quotient topology on the quotient of a Lie module by a Lie submodule: the quotient
topology of the underlying module quotient `M ⧸ N.toSubmodule`. -/
instance topologicalSpace : TopologicalSpace (M ⧸ N) :=
  QuotientModule.Quotient.topologicalSpace N.toSubmodule

instance isTopologicalAddGroup [IsTopologicalAddGroup M] : IsTopologicalAddGroup (M ⧸ N) :=
  Submodule.isTopologicalAddGroup_quotient N.toSubmodule

/-- The quotient map of a Lie module is an open quotient map. -/
theorem isOpenQuotientMap_mk [ContinuousAdd M] : IsOpenQuotientMap (mk : M → M ⧸ N) :=
  Submodule.isOpenQuotientMap_mkQ N.toSubmodule

end LieSubmodule.Quotient

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [ContinuousAdd L]

/-- The quotient homomorphism of a Lie algebra by a Lie ideal is an open quotient map. -/
theorem isOpenQuotientMap_mkQ (I : LieIdeal R L) : IsOpenQuotientMap I.mkQ :=
  Submodule.isOpenQuotientMap_mkQ I.toSubmodule

end LieIdeal
