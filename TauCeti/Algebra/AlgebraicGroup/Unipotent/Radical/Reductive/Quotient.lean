/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Image
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Unipotent radicals and reductive quotients

This file applies ground-field triviality of the radical of a reductive group to an exact-sequence
criterion. Suppose a homomorphism of affine groups is represented contravariantly by an injective
coordinate map `f : D ⟶ H`. If its
kernel is connected, normal, smooth, and unipotent, and the quotient group represented by `D` is
reductive, then the kernel is the unipotent radical of the group represented by `H`.

The reverse containment sends the unipotent radical through the quotient map. Its
scheme-theoretic image remains connected, smooth, and unipotent; injectivity of `f` makes it
normal in the quotient. Reductivity therefore makes that image trivial.

## Main declarations

* The trivial-radical criterion identifies a connected normal smooth unipotent kernel with the
  radical when the target radical is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive`:
  a connected normal smooth unipotent kernel with reductive quotient is the unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A connected normal smooth unipotent kernel of a schematically dominant homomorphism to a group
with trivial unipotent radical is the unipotent radical. -/
theorem
unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_unipotentRadicalDefiningIdeal_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : unipotentRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf_injective : Function.Injective f.hom)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f)) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  le_antisymm (unipotentRadicalDefiningIdeal_le H _ hf)
    (kernelHopfIdeal_le_unipotentRadicalDefiningIdeal_of_eq_augmentation
      H D hD f hf_injective)

/-- A connected normal smooth unipotent kernel of a quotient homomorphism to a reductive group is
the unipotent radical. -/
theorem unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : reductiveCommHopfAlgProperty k D)
    (f : D.obj ⟶ H.obj) (hf_injective : Function.Injective f.hom)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f)) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_unipotentRadicalDefiningIdeal_eq_augmentation
    H D
    hD.unipotentRadicalDefiningIdeal_eq_augmentation f hf_injective hf

end FiniteTypeCommHopfAlgCat

end

end TauCeti
