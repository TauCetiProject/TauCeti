/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility

/-!
# Complete reducibility from a semisimple Lie algebra in characteristic zero

Let `G` be a connected affine group of finite type over an algebraically closed field `k` of
characteristic zero. If the Lie algebra `Lie(G)` has nondegenerate Killing form, equivalently
(by Cartan's criterion) `Lie(G)` is semisimple, then every finite-dimensional representation of
`G` is completely reducible, so `G` is linearly reductive.

A representation `M` of `G` differentiates to a representation of `Lie(G)`. By Weyl's complete
reducibility theorem every `Lie(G)`-submodule of `M` has a `Lie(G)`-stable complement. In
characteristic zero, for connected `G`, the `Lie(G)`-stable subspaces of `M` are exactly its
subrepresentations, so these complements are subrepresentations. Connectedness is used only in
that identification; characteristic zero is used there, through Cartier's theorem, and in Weyl's
theorem.

Over an arbitrary field of characteristic zero the same holds for geometrically connected `G`:
nondegeneracy of the Killing form survives extension to an algebraic closure, and linear
reductivity descends from it.

## Main declarations

* `TauCeti.Comodule.isCompletelyReducible_of_isKilling`: over an algebraically closed field, a
  finite-dimensional representation of a connected group whose Lie algebra has nondegenerate
  Killing form is completely reducible.
* `TauCeti.Coalgebra.isLinearlyReductive_of_isKilling` and
  `TauCeti.linearlyReductiveCommHopfAlgProperty.of_isKilling`: such a group is linearly
  reductive.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_geometricallyConnected_of_isKilling`: over any
  field of characteristic zero, a geometrically connected finite-type affine group whose Lie
  algebra has nondegenerate Killing form is linearly reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), §22.42.
* J. E. Humphreys, *Linear Algebraic Groups*, §13 (characteristic zero theory).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §6.3, for Weyl's
  theorem.
-/

public section

open TauCeti
open scoped TensorProduct

universe u w

namespace TauCeti

section AlgClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable [LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k))]

namespace Comodule

/-- **Weyl's theorem for algebraic groups.** Over an algebraically closed field of characteristic
zero, every finite-dimensional representation of a connected group whose Lie algebra has
nondegenerate Killing form is completely reducible. -/
theorem isCompletelyReducible_of_isKilling
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M] :
    IsCompletelyReducible k H M := by
  refine isCompletelyReducible_iff_forall_differential_mem.2 fun W hW ↦ ?_
  -- Make `M` a `Lie(G)`-module through the differentiated representation, with the commutator
  -- Lie ring structure on `Module.End k M` that `differential` is a Lie homomorphism into.
  let _ : LieRing (Module.End k M) := LieRing.ofAssociativeRing
  let _ : LieRingModule (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieRingModule.compLieHom M (differential (R := k) (H := H) (M := M))
  have : LieModule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieModule.compLieHom M (differential (R := k) (H := H) (M := M))
  have hlie (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M) :
      ⁅d, m⁆ = differential (R := k) (H := H) (M := M) d m := by
    rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]
  let N : LieSubmodule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    { W with lie_mem := fun {d _} hm ↦ (hlie d _).symm ▸ hW d _ hm }
  obtain ⟨N', hN'⟩ := exists_isCompl_of_isKilling N
  refine ⟨N'.toSubmodule, fun d m hm ↦ hlie d m ▸ N'.lie_mem hm, ?_⟩
  rwa [← LieSubmodule.isCompl_toSubmodule] at hN'

end Comodule

/-- Over an algebraically closed field of characteristic zero, a connected group whose Lie algebra
has nondegenerate Killing form is linearly reductive, with comodule carriers in any universe. -/
theorem Coalgebra.isLinearlyReductive_of_isKilling :
    Coalgebra.IsLinearlyReductive.{u, u, w} k H :=
  Coalgebra.IsLinearlyReductive.of_forall_isCompletelyReducible k fun V _ _ _ _ ↦ by
    let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    exact Comodule.isCompletelyReducible_of_isKilling

/-- Over an algebraically closed field of characteristic zero, the coordinate Hopf algebra of a
connected group whose Lie algebra has nondegenerate Killing form is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty.of_isKilling :
    linearlyReductiveCommHopfAlgProperty k H.obj :=
  (linearlyReductiveCommHopfAlgProperty_iff k H.obj).2 Coalgebra.isLinearlyReductive_of_isKilling

end AlgClosed

/-- **Lie-semisimple groups are linearly reductive in characteristic zero.** Over a field of
characteristic zero, a geometrically connected finite-type affine group whose Lie algebra has
nondegenerate Killing form is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty.of_geometricallyConnected_of_isKilling
    {k : Type u} [Field k] [CharZero k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k))]
    (hH : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let HK := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  have : ConnectedSpace (PrimeSpectrum HK) := hH.connectedSpace_algebraicClosureBaseChange
  have := (isKilling_lie_baseChange_iff (k := k) (K := AlgebraicClosure k) (H := H)).2 ‹_›
  exact linearlyReductiveCommHopfAlgProperty.of_baseChange (AlgebraicClosure k)
    (linearlyReductiveCommHopfAlgProperty.of_isKilling (H := HK))

end TauCeti
