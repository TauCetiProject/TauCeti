/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Corner

/-!
# Finite corner spanning families for type-`D` preprojective algebras

The explicit arm and fork words of `TauCeti.signlessPreprojectiveDNormalForms` span every
source/target corner of the signless preprojective algebra of `Dₙ`, for `n ≥ 3`, over any
commutative ring. The fork words alternate between the two leaf backtracks; no choice of
arbitrary paths remains in the spanning families. These words provide the finite families
needed for the projective-socle and Frobenius-pairing calculations. Linear independence,
nonvanishing, and a dimension formula are not claimed.

The path reduction is `TauCeti.signlessPreprojectiveMk_D_ofPath_mem_span_normalForms`.
The passage from path classes to corners follows the corresponding type-`A` construction in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the local relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius property.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [CommRing k] {n : ℕ}

attribute [local instance] forkNeighborSetFintype

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))

/-- The finite family of arm valleys, alternating fork words, and leaf idempotents spans the
entire corner `e_b Π e_a` of the type-`D` signless preprojective algebra. -/
theorem cornerSubmodule_signlessPreprojective_D_eq_span_normalForms (hn : 3 ≤ n)
    (a b : Fin (DynkinType.D n).rank) :
    cornerSubmodule k (e b) (e a) = Submodule.span k (signlessPreprojectiveDNormalForms k a b) := by
  apply le_antisymm
  · exact PathAlgebra.cornerSubmodule_le_of_ofPath_mem (π).toNonUnitalAlgHom
      (signlessPreprojectiveMk_surjective k (DoubledQuiver DG)) (vertex DG a) (vertex DG b)
      (Submodule.span k (signlessPreprojectiveDNormalForms k a b))
      (signlessPreprojectiveMk_D_ofPath_mem_span_normalForms k hn)
  · exact Submodule.span_le.mpr (signlessPreprojectiveDNormalForms_subset_cornerSubmodule k a b)

end TauCeti
