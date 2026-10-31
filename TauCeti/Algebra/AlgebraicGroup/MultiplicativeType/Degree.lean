/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Kernel
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Degree
import Mathlib.GroupTheory.Index

/-!
# Degrees of homomorphisms of multiplicative-type groups

Kernel degrees multiply under composition when the second coordinate morphism has injective
geometric character map. In particular, they multiply for central isogenies. The calculation
uses the index of the character map's range, so it also applies to arbitrary homomorphisms
with that injectivity hypothesis: when a character cokernel is infinite, its cardinality
and the corresponding coordinate-algebra `finrank` are both zero.

Together with the general degree-one criterion for affine isogenies, this supplies degree
arithmetic without assuming smoothness, a perfect ground field, or a split presentation.
In positive characteristic it retains the length of infinitesimal kernels.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9 and §12.d.
-/

public section

open CategoryTheory

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}
variable (hH : multiplicativeTypeCommHopfAlgProperty k H)
variable (hK : multiplicativeTypeCommHopfAlgProperty k K)
variable (hL : multiplicativeTypeCommHopfAlgProperty k L)

include hH hK hL

/-- Kernel-coordinate dimensions multiply when the second coordinate map is injective on
geometric characters. The formula also covers infinite-dimensional kernels using `finrank`. -/
theorem finrank_kernelCoordinate_comp (f : H.obj ⟶ K.obj) (g : K.obj ⟶ L.obj)
    (hg : Function.Injective (CommHopfAlgCat.geometricCharacterMap g)) :
    Module.finrank k (CommHopfAlgCat.quotient L.obj
        (CommHopfAlgCat.kernelHopfIdeal (f ≫ g))) =
      Module.finrank k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) *
        Module.finrank k (CommHopfAlgCat.quotient L.obj (CommHopfAlgCat.kernelHopfIdeal g)) := by
  rw [finrank_kernelCoordinate hH hL, finrank_kernelCoordinate hH hK,
    finrank_kernelCoordinate hK hL, CommHopfAlgCat.geometricCharacterMap_comp,
    ← Subgroup.index_eq_card, ← Subgroup.index_eq_card, ← Subgroup.index_eq_card,
    MonoidHom.range_comp, Subgroup.index_map_of_injective _ hg]

/-- For a central isogeny as the second coordinate map, kernel degrees multiply under
composition. The first map need not be an isogeny. -/
theorem finrank_kernelCoordinate_comp_of_isCentralIsogeny
    (f : H.obj ⟶ K.obj) (g : K.obj ⟶ L.obj) (hg : CommHopfAlgCat.IsCentralIsogeny g) :
    Module.finrank k (CommHopfAlgCat.quotient L.obj
        (CommHopfAlgCat.kernelHopfIdeal (f ≫ g))) =
      Module.finrank k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) *
        Module.finrank k (CommHopfAlgCat.quotient L.obj (CommHopfAlgCat.kernelHopfIdeal g)) :=
  finrank_kernelCoordinate_comp hH hK hL f g
    ((isCentralIsogeny_iff_geometricCharacterMap_injective_and_finite_quotient hK hL g).mp hg).1

end TauCeti.multiplicativeTypeCommHopfAlgProperty
