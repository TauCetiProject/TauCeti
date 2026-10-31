/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# The identity component is characteristic

Every isomorphism of affine groups identifies their identity components: in coordinate
algebras, a Hopf algebra isomorphism matches the defining Hopf ideals
(`TauCeti.HopfAlgebra.apply_mem_identityComponentHopfIdeal_iff`). In particular every
automorphism of an affine group preserves its identity component, so the defining Hopf ideal is
fixed by inverse image along every automorphism. This allows the identity component of a normal
closed subgroup to be treated as a normal subgroup of the ambient group, using the
characteristic-subgroup criterion, and identifies the identity components of conjugate closed
subgroups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
-/

public section

open CategoryTheory

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

section Equiv

variable {H K : Type v} [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]
  [CommRing K] [_root_.HopfAlgebra k K] [Algebra.FiniteType k K]

/-- An isomorphism of affine groups identifies their identity components: a Hopf algebra
isomorphism carries the defining Hopf ideal of the identity component onto that of the target. -/
theorem apply_mem_identityComponentHopfIdeal_iff (e : H ≃ₐc[k] K) {x : H} :
    e x ∈ identityComponentHopfIdeal (k := k) (H := K) ↔
      x ∈ identityComponentHopfIdeal (k := k) (H := H) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  let E : H ≃+* K := e.toAlgEquiv.toRingEquiv
  have hpt : PrimeSpectrum.comap (E.symm : K →+* H) (Bialgebra.augmentationPoint k H) =
      Bialgebra.augmentationPoint k K :=
    (AlgHom.comap_kernelPoint (Bialgebra.counitAlgHom k H) (AlgHom.ofClass e.symm)).trans
      (congrArg AlgHom.kernelPoint (BialgHomClass.counitAlgHom_comp e.symm))
  rw [mem_identityComponentHopfIdeal, mem_identityComponentHopfIdeal, ← hpt]
  exact PrimeSpectrum.apply_mem_connectedComponentIdeal_iff E _

end Equiv

variable {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H]

/-- Every automorphism of an affine group preserves its identity component. -/
@[simp]
theorem comapOfSurjective_identityComponentHopfIdeal (e : H ≅ H) :
    (identityComponentHopfIdeal (k := k) (H := H)).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      identityComponentHopfIdeal (k := k) (H := H) := by
  ext x
  rw [HopfIdeal.mem_comapOfSurjective]
  exact apply_mem_identityComponentHopfIdeal_iff (_root_.CommHopfAlgCat.ofIso e)

end TauCeti.HopfAlgebra
