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

Every automorphism of an affine group preserves its identity component. In coordinate
algebras, the defining Hopf ideal is fixed by inverse image along every automorphism.
This allows the identity component of a normal closed subgroup to be treated as a normal
subgroup of the ambient group, using the characteristic-subgroup criterion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
-/

public section

open CategoryTheory

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H]

/-- Every automorphism of an affine group preserves its identity component. -/
@[simp]
theorem comapOfSurjective_identityComponentHopfIdeal (e : H ≅ H) :
    (identityComponentHopfIdeal (k := k) (H := H)).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      identityComponentHopfIdeal (k := k) (H := H) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let E := (_root_.CommHopfAlgCat.ofIso e).toAlgEquiv.toRingEquiv
  have hfix : PrimeSpectrum.comap (E : H →+* H) (Bialgebra.augmentationPoint k H) =
      Bialgebra.augmentationPoint k H := by
    exact (AlgHom.comap_kernelPoint (Bialgebra.counitAlgHom k H) e.hom.hom.toAlgHom).trans
      (congrArg AlgHom.kernelPoint (BialgHom.counitAlgHom_comp e.hom.hom))
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, mem_identityComponentHopfIdeal,
    mem_identityComponentHopfIdeal]
  exact PrimeSpectrum.apply_mem_connectedComponentIdeal_iff_of_comap_eq_self
    E (Bialgebra.augmentationPoint k H) hfix

end TauCeti.HopfAlgebra
