/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic

/-!
# Central isogenies from groups with trivial center

A central isogeny from an affine group with trivial scheme-theoretic center is an
isomorphism. In particular, adjoint semisimple groups admit no nontrivial central-isogeny
quotients. The result itself needs neither semisimplicity, smoothness, nor finite type of
the ambient groups.

For a coordinate morphism `f : H ⟶ K`, the source group is `Spec K`: it is the center of
`K` that must be trivial. Centrality puts the kernel inside that center, and the trivial-kernel
criterion for isogenies then applies. Both the center and kernel are scheme-theoretic, so
the statement also rules out infinitesimal central kernels in positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K}

/-- A central isogeny from an affine group with trivial scheme-theoretic center is an
isomorphism. Coordinate arrows reverse, so the trivial-center hypothesis is on `K`. -/
theorem IsCentralIsogeny.isIso_of_centerDefiningIdeal_eq_augmentation
    (hf : IsCentralIsogeny f)
    (hK : centerDefiningIdeal K = HopfIdeal.augmentation k K) : IsIso f := by
  apply hf.isIsogeny.isIso_iff_kernelHopfIdeal_eq_augmentation.mpr
  apply le_antisymm (HopfIdeal.le_augmentation k K _)
  rw [← hK]
  exact (centerDefiningIdeal_le_iff K _).mpr hf.isCentral_kernelHopfIdeal

end TauCeti.CommHopfAlgCat
