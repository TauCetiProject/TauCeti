/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import TauCeti.Algebra.Group.ULift
import TauCeti.GroupTheory.Coprod.Factors
import TauCeti.GroupTheory.CoprodI.Centralizer
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of factor elements in a free product of two groups

In the free product `G ∗ H` of two groups, the centralizer of a nontrivial element `g` of `G` is
the centralizer of `g` in `G`, and likewise for `H`. This is the case of the family
`Monoid.Coprod.Factors G H` indexed by `Bool` (`Monoid.Coprod.equivCoprodI`) of the description of
the centralizers of factor elements of a free product (`Monoid.CoprodI.centralizer_of_eq_map`).

## Main results

* `Monoid.Coprod.centralizer_inl_eq_map`: the centralizer of `inl g`, for `g ≠ 1`, is the image
  of the centralizer of `g` in `G`.
* `Monoid.Coprod.centralizer_inr_eq_map`: the centralizer of `inr h`, for `h ≠ 1`, is the image
  of the centralizer of `h` in `H`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §1
  (the normal form theorem for free products).
-/

public section

open Subgroup

universe u v

namespace Monoid.Coprod

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- **Centralizers of elements of the first factor of a free product.** The centralizer in `G ∗ H`
of a nontrivial `g ∈ G` is the centralizer of `g` in `G`. -/
theorem centralizer_inl_eq_map {g : G} (hg : g ≠ 1) :
    centralizer {(inl g : G ∗ H)} = (centralizer {g}).map inl := by
  simpa using MulEquiv.centralizer_image_eq_map equivCoprodI.symm
    (f := CoprodI.of (M := Factors G H) (i := false)) (s := {ULift.up g})
    MulEquiv.ulift.toMonoidHom equivCoprodI_symm_of_false (by
      rw [Set.image_singleton]
      exact CoprodI.centralizer_of_eq_map fun h1 => hg (congrArg ULift.down h1))

/-- **Centralizers of elements of the second factor of a free product.** The centralizer in
`G ∗ H` of a nontrivial `h ∈ H` is the centralizer of `h` in `H`. -/
theorem centralizer_inr_eq_map {h : H} (hh : h ≠ 1) :
    centralizer {(inr h : G ∗ H)} = (centralizer {h}).map inr := by
  simpa using MulEquiv.centralizer_image_eq_map equivCoprodI.symm
    (f := CoprodI.of (M := Factors G H) (i := true)) (s := {ULift.up h})
    MulEquiv.ulift.toMonoidHom equivCoprodI_symm_of_true (by
      rw [Set.image_singleton]
      exact CoprodI.centralizer_of_eq_map fun h1 => hh (congrArg ULift.down h1))

end Monoid.Coprod
