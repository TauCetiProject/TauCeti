/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Types.Pushouts
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# Open embeddings from pushouts and coproducts in `TopCat`

This file records the open embeddings produced by the two colimits used to attach cells.

* Pushouts: in a pushout square
  ```
       g
    A ───> B
  f │      │ f'
    v      v
    A' ──> B'
       g'
  ```
  of `TopCat`, the map `g'` carries the complement of the range of `f` onto the complement of the
  range of `f'` (`TauCeti.TopCat.image_compl_range_of_isPushout`), sends open subsets of that
  complement to open subsets (`TauCeti.TopCat.isOpen_image_of_isPushout`), and so restricts to an
  open embedding on it when the range of `f` is closed
  (`TauCeti.TopCat.isOpenEmbedding_domRestrict_compl_range_of_isPushout`).
* Coproducts: the injections of a colimit cofan in `TopCat` are open embeddings
  (`TauCeti.TopCat.isOpenEmbedding_inj_of_isColimit`).

When `f` is a coproduct of boundary inclusions `∂𝔻 n ⟶ 𝔻 n`, the complement of its range is the
union of the open disks, so these statements show that attaching cells embeds each open disk
homeomorphically onto an open subset of the new space, away from the old one; see
`TauCeti.Topology.CWComplex.Abstract.OpenCell`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, on the topology of cell complexes.
-/

public section

open CategoryTheory Limits Topology

universe w u

namespace TauCeti.TopCat

section Pushout

variable {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}

/-- In a pushout square in `TopCat`, the map opposite to `f'` carries the complement of the range
of `f` onto the complement of the range of `f'`. -/
theorem image_compl_range_of_isPushout (sq : IsPushout g f f' g') :
    g' '' (Set.range f)ᶜ = (Set.range f')ᶜ :=
  Types.image_compl_range_of_isPushout ((forget TopCat).map_isPushout sq)

/-- In a pushout square in `TopCat`, the map opposite to `f'` sends open subsets of the complement
of the range of `f` to open subsets. -/
theorem isOpen_image_of_isPushout (sq : IsPushout g f f' g') {W : Set A'} (hW : IsOpen W)
    (hWf : W ⊆ (Set.range f)ᶜ) : IsOpen (g' '' W) := by
  have hinj := Types.injOn_compl_range_of_isPushout ((forget TopCat).map_isPushout sq)
  have himage : g' '' W ⊆ (Set.range f')ᶜ :=
    (Set.image_mono hWf).trans (image_compl_range_of_isPushout sq).subset
  have h₁ : f' ⁻¹' (g' '' W) = ∅ :=
    Set.eq_empty_of_forall_notMem fun b hb ↦ himage hb ⟨b, rfl⟩
  have h₂ : g' ⁻¹' (g' '' W) = W := by
    refine subset_antisymm (fun a ⟨w, hw, hwa⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    by_cases ha : a ∈ Set.range f
    · obtain ⟨x, rfl⟩ := ha
      refine (himage ⟨w, hw, hwa⟩ ⟨g x, ?_⟩).elim
      rw [← ConcreteCategory.comp_apply, sq.w, ConcreteCategory.comp_apply]
    · exact hinj ha (hWf hw) hwa.symm ▸ hw
  rw [← isClosed_compl_iff, isClosed_iff_of_isPushout sq, Set.preimage_compl, Set.preimage_compl,
    h₁, h₂, Set.compl_empty, isClosed_compl_iff]
  exact ⟨isClosed_univ, hW⟩

/-- In a pushout square in `TopCat` where the range of `f` is closed, the map opposite to `f'`
restricts to an open embedding on the complement of the range of `f`. -/
theorem isOpenEmbedding_domRestrict_compl_range_of_isPushout (sq : IsPushout g f f' g')
    (hf : IsClosed (Set.range f)) : IsOpenEmbedding ((Set.range f)ᶜ.domRestrict g') := by
  refine .of_continuous_injective_isOpenMap (g'.hom.continuous.comp continuous_subtype_val)
    (Set.injOn_iff_injective.1
      (Types.injOn_compl_range_of_isPushout ((forget TopCat).map_isPushout sq)))
    fun V hV ↦ ?_
  rw [Set.domRestrict_eq, Set.image_comp]
  exact isOpen_image_of_isPushout sq (hf.isOpen_compl.isOpenMap_subtype_val V hV)
    (Subtype.coe_image_subset _ _)

end Pushout

section Coproduct

variable {ι : Type w} {X : ι → TopCat.{u}} {c : Cofan X}

/-- In `TopCat`, the injections of a colimit cofan are open embeddings. -/
theorem isOpenEmbedding_inj_of_isColimit (hc : IsColimit c) (i : ι) :
    IsOpenEmbedding (c.inj i) := by
  have hc' := isColimitCofanMkObjOfIsColimit (forget TopCat) X c.inj hc
  have hinj : Function.Injective (c.inj i) := Cofan.inj_injective_of_isColimit hc' i
  refine .of_continuous_injective_isOpenMap (c.inj i).hom.continuous hinj fun V hV ↦ ?_
  rw [TopCat.isOpen_iff_of_isColimit _ hc]
  rintro ⟨j⟩
  by_cases hij : i = j
  · subst hij
    exact (congrArg IsOpen (hinj.preimage_image V)).mpr hV
  · convert isOpen_empty
    refine Set.eq_empty_of_forall_notMem fun x ⟨y, _, hy⟩ ↦ hij ?_
    exact Cofan.eq_of_inj_apply_eq_of_isColimit hc' y x hy

end Coproduct

end TauCeti.TopCat
