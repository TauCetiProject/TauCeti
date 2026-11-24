/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Decomposition
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
import TauCeti.Algebra.Coalgebra.Subcoalgebra.RegularSubcomodule

/-!
# Subcomodules of the regular comodule of a group-like-spanned coalgebra

Let `C` be a coalgebra over a field `k` that is spanned by its group-like elements, such as a
group algebra. A weight vector of the regular comodule is a scalar multiple of its weight, so the
weight decomposition of a subcomodule `N` of the regular comodule writes every element of `N` as
a combination of group-like elements lying in `N`. Hence `N` is spanned by the group-like
elements it contains. This applies in particular to every subcoalgebra of `C`, and to the image
of an injective coalgebra morphism into `C`: a coalgebra that embeds in a group-like-spanned
coalgebra is itself spanned by its group-like elements.

For a commutative Hopf algebra this is the coordinate form of the fact that a quotient group of
a diagonalizable group is diagonalizable: the coordinate ring of the quotient is a Hopf
subalgebra of a group algebra.

The field hypothesis cannot be weakened to a domain: in the group coalgebra `ℤ[G]` the
submodule `2ℤ • g` is a subcomodule of the regular comodule that contains no group-like element.

## Main declarations

* `TauCeti.Subcomodule.toSubmodule_eq_span_groupLike`: a subcomodule of the regular comodule of a
  group-like-spanned coalgebra is spanned by the group-like elements it contains.
* `TauCeti.Subcoalgebra.groupLikeSetSpan_setOf_mem`: a subcoalgebra of a group-like-spanned
  coalgebra is the subcoalgebra spanned by the group-like elements it contains.
* `CoalgHom.groupLikeSetSpan_eq_top_of_injective`: the source of an injective coalgebra morphism
  into a group-like-spanned coalgebra is spanned by its group-like elements.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(c).
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

namespace Subcomodule

/-- **A subcomodule of the regular comodule of a group-like-spanned coalgebra over a field is
spanned by the group-like elements it contains.** -/
theorem toSubmodule_eq_span_groupLike
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) (N : Subcomodule k C C) :
    N.toSubmodule = Submodule.span k ((↑) '' {g : GroupLike k C | (g : C) ∈ N}) := by
  refine le_antisymm (fun c hc ↦ ?_) (Submodule.span_le.mpr ?_)
  · -- `N` is the sum of its weight spaces, whose vectors are multiples of weights lying in `N`.
    have hmem := iSup_groupLikeWeightSpace_le_comap_span_groupLike N
      (Comodule.iSup_groupLikeWeightSpace_eq_top (M := N) hC ▸
        (Submodule.mem_top : (⟨c, hc⟩ : N) ∈ ⊤))
    simpa only [Submodule.mem_comap, Subcomodule.subtype_toLinearMap,
      SMulMemClass.subtype_apply] using hmem
  · rintro _ ⟨g, hg, rfl⟩
    exact hg

end Subcomodule

namespace Subcoalgebra

/-- **A subcoalgebra of a group-like-spanned coalgebra over a field is spanned by the group-like
elements it contains.** -/
theorem groupLikeSetSpan_setOf_mem
    (hC : groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) (D : Subcoalgebra k C) :
    groupLikeSetSpan {g : GroupLike k C | (g : C) ∈ D} = D := by
  ext c
  rw [mem_groupLikeSetSpan, ← mem_toRegularSubcomodule, ← Subcomodule.mem_toSubmodule,
    Subcomodule.toSubmodule_eq_span_groupLike hC]
  simp only [mem_toRegularSubcomodule]

end Subcoalgebra

end TauCeti

namespace CoalgHom

variable {k A B : Type*} [Field k] [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
  [Coalgebra k A] [Coalgebra k B]

/-- **A coalgebra over a field that embeds in a group-like-spanned coalgebra is spanned by its
group-like elements.** This is the counterpart for injective morphisms of
`CoalgHom.groupLikeSetSpan_eq_top_of_surjective`. -/
theorem groupLikeSetSpan_eq_top_of_injective (f : A →ₗc[k] B) (hf : Function.Injective f)
    (hB : TauCeti.Subcoalgebra.groupLikeSetSpan (R := k) (C := B) Set.univ = ⊤) :
    TauCeti.Subcoalgebra.groupLikeSetSpan (R := k) (C := A) Set.univ = ⊤ := by
  rw [TauCeti.Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  refine eq_top_iff.mpr fun a _ ↦ ?_
  -- The group-like elements of the image of `f` are the images of group-like elements.
  have hle : Submodule.span k ((↑) '' {g : GroupLike k B |
        (g : B) ∈ (⊤ : TauCeti.Subcoalgebra k A).map f}) ≤
      (Submodule.span k (Set.range (GroupLike.val (R := k) (A := A)))).map f.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, -, hx⟩ := TauCeti.Subcoalgebra.mem_map.mp hg
    have hxg : IsGroupLikeElem k x :=
      (TauCeti.isGroupLikeElem_map_iff_of_injective f hf).mp (hx ▸ g.isGroupLikeElem_val)
    exact ⟨x, Submodule.subset_span ⟨⟨x, hxg⟩, rfl⟩, hx⟩
  have hfa : f a ∈ (⊤ : TauCeti.Subcoalgebra k A).map f :=
    TauCeti.Subcoalgebra.mem_map_of_mem f (TauCeti.Subcoalgebra.mem_top a)
  rw [← TauCeti.Subcoalgebra.groupLikeSetSpan_setOf_mem hB (.map f ⊤),
    TauCeti.Subcoalgebra.mem_groupLikeSetSpan] at hfa
  obtain ⟨x, hx, hxa⟩ := hle hfa
  exact hf hxa ▸ hx

end CoalgHom
