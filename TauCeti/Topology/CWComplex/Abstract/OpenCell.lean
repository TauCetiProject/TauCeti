/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.OpenEmbedding
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding

/-!
# The open cells of a categorical relative CW complex

Mathlib's categorical relative CW complex `c : TopCat.RelativeCWComplex f`, for a morphism
`f : X ⟶ Y` of `TopCat`, presents `Y` as the colimit of a sequence of spaces `c.F.obj n`, each
obtained from the previous one by attaching `n`-disks along their boundary spheres. A cell `γ` of
`c` comes with its inclusion `γ.ι : 𝔻 γ.j ⟶ Y`, and its *open cell* is the image under `γ.ι` of
the open disk, the complement of the boundary sphere. This file proves, for the open cells of `c`
and the range of `f`, the properties that the axioms of a classical `Topology.RelCWComplex` on `Y`
relative to the range of `f` ask of open cells individually:

* `γ.ι` restricts to an embedding of the open disk into `Y`
  (`TopCat.RelativeCWComplex.isEmbedding_domRestrict_cells_ι`);
* distinct open cells are disjoint (`TopCat.RelativeCWComplex.disjoint_image_cells_ι`), and every
  open cell is disjoint from the range of `f`
  (`TopCat.RelativeCWComplex.disjoint_range_image_cells_ι`);
* the image of `c.F.obj n` in `Y` is the range of `f` together with the open cells of dimension
  less than `n` (`TopCat.RelativeCWComplex.range_incl_app_eq_union_iUnion_image_cells_ι`), or
  equivalently together with the closed cells of dimension less than `n`
  (`TopCat.RelativeCWComplex.range_incl_app_eq_union_iUnion_range_cells_ι`), so `Y` is the
  disjoint union of the range of `f` and all open cells
  (`TopCat.RelativeCWComplex.range_union_iUnion_image_cells_ι`).

The two remaining axioms, that the boundary of a cell meets only finitely many cells of lower
dimension and that `Y` carries the weak topology of its closed cells, concern how closed cells meet
and are not treated here.

These come from the corresponding statements for a single step of attaching cells in `TopCat`
(`HomotopicalAlgebra.AttachCells.isOpenEmbedding_domRestrict_cell`,
`HomotopicalAlgebra.AttachCells.disjoint_image_cell`,
`HomotopicalAlgebra.AttachCells.compl_range_eq_iUnion_image_cell`), which in turn come from the
behaviour of pushouts and coproducts in `TopCat` on complements of ranges
(`TauCeti.Topology.Category.TopCat.OpenEmbedding`), together with the closed embedding of each
stage into `Y` (`TopCat.RelativeCWComplex.isClosedEmbedding_incl_app`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, on the topology of cell complexes.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical definition.
-/

public section

open CategoryTheory Limits Topology

universe w t u

namespace HomotopicalAlgebra.AttachCells

variable {α : Type t} {A B : α → TopCat.{u}} {g : (a : α) → A a ⟶ B a} {X₁ X₂ : TopCat.{u}}
  {f : X₁ ⟶ X₂} (c : AttachCells.{w} g f)

/-- The complement of the range of the coproduct of the basic cells is the union of the images of
the complements of the ranges of the basic cells. -/
private lemma compl_range_m :
    (Set.range c.m)ᶜ = ⋃ i, c.cofan₂.inj i '' (Set.range (g (c.π i)))ᶜ := by
  have h₁ := isColimitCofanMkObjOfIsColimit (forget TopCat) _ c.cofan₁.inj c.isColimit₁
  have h₂ := isColimitCofanMkObjOfIsColimit (forget TopCat) _ c.cofan₂.inj c.isColimit₂
  have hm (i : c.ι) (a : A (c.π i)) : c.m (c.cofan₁.inj i a) = c.cofan₂.inj i (g (c.π i) a) := by
    rw [← ConcreteCategory.comp_apply, c.hm, ConcreteCategory.comp_apply]
  ext y
  obtain ⟨i, b, rfl⟩ : ∃ i b, c.cofan₂.inj i b = y :=
    Cofan.inj_jointly_surjective_of_isColimit h₂ y
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image]
  constructor
  · exact fun hb ↦ ⟨i, b, fun ⟨a, ha⟩ ↦ hb ⟨c.cofan₁.inj i a, by rw [hm, ha]⟩, rfl⟩
  · rintro ⟨j, b', hb', hb'b⟩ ⟨x, hx⟩
    obtain ⟨k, a, rfl⟩ : ∃ k a, c.cofan₁.inj k a = x :=
      Cofan.inj_jointly_surjective_of_isColimit h₁ x
    rw [hm] at hx
    have hx' := hx.trans hb'b.symm
    obtain rfl : k = j := Cofan.eq_of_inj_apply_eq_of_isColimit h₂ _ _ hx'
    exact hb' ⟨a, Cofan.inj_injective_of_isColimit h₂ _ hx'⟩

/-- When cells are attached in `TopCat`, the complement of the old space in the new one is the
union of the images of the interiors of the cells, the complements of the ranges of the basic
cells. -/
theorem compl_range_eq_iUnion_image_cell :
    (Set.range f)ᶜ = ⋃ i, c.cell i '' (Set.range (g (c.π i)))ᶜ := by
  simp_rw [cell_def, TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp, ← Set.image_iUnion,
    ← c.compl_range_m]
  exact (TauCeti.TopCat.image_compl_range_of_isPushout c.isPushout).symm

/-- When cells are attached in `TopCat`, the images of the interiors of distinct cells are
disjoint. -/
theorem disjoint_image_cell {i j : c.ι} (hij : i ≠ j) :
    Disjoint (c.cell i '' (Set.range (g (c.π i)))ᶜ) (c.cell j '' (Set.range (g (c.π j)))ᶜ) := by
  have h₂ := isColimitCofanMkObjOfIsColimit (forget TopCat) _ c.cofan₂.inj c.isColimit₂
  simp_rw [cell_def, TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp]
  refine Disjoint.image ?_
    (TauCeti.Types.injOn_compl_range_of_isPushout ((forget TopCat).map_isPushout c.isPushout))
    (c.compl_range_m ▸ Set.subset_iUnion_of_subset i subset_rfl)
    (c.compl_range_m ▸ Set.subset_iUnion_of_subset j subset_rfl)
  exact Set.disjoint_left.2 fun _ ⟨a, _, ha⟩ ⟨b, _, hb⟩ ↦
    hij (Cofan.eq_of_inj_apply_eq_of_isColimit h₂ a b (ha.trans hb.symm))

/-- When cells are attached in `TopCat` along basic cells with closed ranges, each cell restricts
to an open embedding on its interior, the complement of the range of its basic cell. -/
theorem isOpenEmbedding_domRestrict_cell (hg : ∀ i, IsClosed (Set.range (g (c.π i)))) (i : c.ι) :
    IsOpenEmbedding ((Set.range (g (c.π i)))ᶜ.domRestrict (c.cell i)) := by
  have hm : IsClosed (Set.range c.m) := by
    rw [← isOpen_compl_iff, c.compl_range_m]
    exact isOpen_iUnion fun j ↦
      (TauCeti.TopCat.isOpenEmbedding_inj_of_isColimit c.isColimit₂ j).isOpenMap _
        (hg j).isOpen_compl
  have hinj := (TauCeti.TopCat.isOpenEmbedding_inj_of_isColimit c.isColimit₂ i)
  have hsub : c.cofan₂.inj i '' (Set.range (g (c.π i)))ᶜ ⊆ (Set.range c.m)ᶜ :=
    c.compl_range_m ▸ Set.subset_iUnion_of_subset i subset_rfl
  have hg₂ := TauCeti.TopCat.isOpenEmbedding_domRestrict_compl_range_of_isPushout c.isPushout hm
  -- The restricted cell factors through the restriction of `c.g₂` to the complement of the range
  -- of `c.m`, which is an open embedding.
  have : (Set.range (g (c.π i)))ᶜ.domRestrict (c.cell i) =
      (Set.range c.m)ᶜ.domRestrict c.g₂ ∘
        Set.MapsTo.restrict (c.cofan₂.inj i) _ _ (Set.mapsTo_iff_image_subset.2 hsub) := by
    ext; simp [cell_def]
  rw [this]
  exact hg₂.comp (hinj.restrict (Set.mapsTo_iff_image_subset.2 hsub) (hg i).isOpen_compl)

end HomotopicalAlgebra.AttachCells

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)

open HomotopicalAlgebra.RelativeCellComplex

/-- The image of the `m`-th stage of a relative CW complex is the image of the `m`-th stage in the
`n`-th stage, for `m ≤ n`. -/
private lemma range_incl_app_eq {m n : ℕ} (h : m ≤ n) :
    Set.range (c.incl.app m) = c.incl.app n '' Set.range (c.F.map (homOfLE h)) := by
  have := c.incl.naturality (homOfLE h)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
  rw [← this, ConcreteCategory.coe_comp, Set.range_comp]

/-- The images of the stages of a relative CW complex increase. -/
private lemma range_incl_app_subset {m n : ℕ} (h : m ≤ n) :
    Set.range (c.incl.app m) ⊆ Set.range (c.incl.app n) :=
  c.range_incl_app_eq h ▸ Set.image_subset_range _ _

/-- The range of a relative CW complex is the image of its initial stage. -/
private lemma range_eq_range_incl_app_zero : Set.range f = Set.range (c.incl.app 0) :=
  calc Set.range f = Set.range (c.isoBot.inv ≫ c.incl.app ⊥) := by rw [c.fac]
    _ = Set.range (c.incl.app 0) := by
      have hs : Function.Surjective c.isoBot.inv := fun x ↦ ⟨c.isoBot.hom x, by simp⟩
      rw [ConcreteCategory.coe_comp, Set.range_comp, hs.range_eq, Set.image_univ, Nat.bot_eq_zero]

/-- The closed cell of `γ` lies in the image of the stage where `γ` is attached. -/
private lemma range_cells_ι_subset_succ (γ : c.Cells) :
    Set.range γ.ι ⊆ Set.range (c.incl.app (Order.succ γ.j)) := by
  rw [Cells.ι, ConcreteCategory.coe_comp]
  exact Set.range_comp_subset_range _ _

/-- The closed cell of `γ` lies in the image of every stage after the one where `γ` is attached. -/
private lemma range_cells_ι_subset (γ : c.Cells) {n : ℕ} (h : γ.j < n) :
    Set.range γ.ι ⊆ Set.range (c.incl.app n) :=
  (c.range_cells_ι_subset_succ γ).trans (c.range_incl_app_subset (Order.succ_le_of_lt h))

/-- The open cell of `γ` is the image of the interior of the cell attached at the stage
`Order.succ γ.j`. -/
private lemma image_cells_ι (γ : c.Cells) :
    γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ =
      c.incl.app (Order.succ γ.j) ''
        ((c.attachCells γ.j γ.hj).cell γ.k '' (Set.range (diskBoundaryInclusion γ.j))ᶜ) := by
  rw [Cells.ι, ConcreteCategory.coe_comp, Set.image_comp]

/-- In a relative CW complex, the inclusion of a cell restricts to an embedding of the open disk,
the complement of the boundary sphere. -/
theorem isEmbedding_domRestrict_cells_ι (γ : c.Cells) :
    IsEmbedding ((Set.range (diskBoundaryInclusion γ.j))ᶜ.domRestrict γ.ι) := by
  rw [Cells.ι, ConcreteCategory.coe_comp, Set.domRestrict_eq, Function.comp_assoc,
    ← Set.domRestrict_eq]
  exact (c.isClosedEmbedding_incl_app _).isEmbedding.comp
    ((c.attachCells γ.j γ.hj).isOpenEmbedding_domRestrict_cell
      (fun _ ↦ (TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion _).isClosed_range)
      γ.k).isEmbedding

/-- In a relative CW complex, the open cell of `γ` is disjoint from the image of every stage up to
the one where `γ` is attached. -/
theorem disjoint_range_incl_app_image_cells_ι (γ : c.Cells) {n : ℕ} (hn : n ≤ γ.j) :
    Disjoint (Set.range (c.incl.app n)) (γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ) := by
  refine Disjoint.mono_left (c.range_incl_app_subset hn) ?_
  rw [c.range_incl_app_eq (Order.le_succ γ.j), image_cells_ι,
    Set.disjoint_image_iff (c.isClosedEmbedding_incl_app _).injective,
    ← Set.subset_compl_iff_disjoint_left,
    (c.attachCells γ.j γ.hj).compl_range_eq_iUnion_image_cell]
  exact Set.subset_iUnion_of_subset γ.k subset_rfl

/-- In a relative CW complex, every open cell is disjoint from the range of the complex. -/
theorem disjoint_range_image_cells_ι (γ : c.Cells) :
    Disjoint (Set.range f) (γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ) :=
  c.range_eq_range_incl_app_zero ▸ c.disjoint_range_incl_app_image_cells_ι γ (Nat.zero_le _)

/-- In a relative CW complex, distinct cells have disjoint open cells. -/
theorem disjoint_image_cells_ι {γ γ' : c.Cells} (h : γ ≠ γ') :
    Disjoint (γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ)
      (γ'.ι '' (Set.range (diskBoundaryInclusion γ'.j))ᶜ) := by
  rcases lt_trichotomy γ.j γ'.j with hlt | heq | hgt
  · exact (c.disjoint_range_incl_app_image_cells_ι γ' (Order.succ_le_of_lt hlt)).mono_left
      ((Set.image_subset_range _ _).trans (c.range_cells_ι_subset_succ γ))
  · obtain ⟨j, hj, k⟩ := γ
    obtain ⟨j', hj', k'⟩ := γ'
    obtain rfl : j = j' := heq
    have hk : k ≠ k' := by
      rintro rfl
      exact h rfl
    rw [image_cells_ι, image_cells_ι,
      Set.disjoint_image_iff (c.isClosedEmbedding_incl_app _).injective]
    exact (c.attachCells j hj).disjoint_image_cell hk
  · exact (c.disjoint_range_incl_app_image_cells_ι γ (Order.succ_le_of_lt hgt)).mono_left
      ((Set.image_subset_range _ _).trans (c.range_cells_ι_subset_succ γ')) |>.symm

/-- In a relative CW complex, the image of the `n`-th stage is the range of the complex together
with the open cells of dimension less than `n`. -/
theorem range_incl_app_eq_union_iUnion_image_cells_ι (n : ℕ) :
    Set.range (c.incl.app n) = Set.range f ∪
      ⋃ (γ : c.Cells) (_ : γ.j < n), γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ := by
  refine subset_antisymm ?_ (Set.union_subset
    (c.range_eq_range_incl_app_zero ▸ c.range_incl_app_subset (Nat.zero_le n))
    (Set.iUnion₂_subset fun γ hγ ↦ (Set.image_subset_range _ _).trans
      (c.range_cells_ι_subset γ hγ)))
  induction n with
  | zero => exact c.range_eq_range_incl_app_zero ▸ Set.subset_union_left
  | succ n ih =>
    rintro _ ⟨x, rfl⟩
    have h := c.incl.naturality (homOfLE (Order.le_succ n))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
    by_cases hx : x ∈ Set.range (c.F.map (homOfLE (Order.le_succ n)))
    · obtain ⟨x, rfl⟩ := hx
      -- `Order.succ n` is `n + 1` by definition in `ℕ`.
      have hx : c.incl.app (n + 1) (c.F.map (homOfLE (Order.le_succ n)) x) = c.incl.app n x :=
        ConcreteCategory.congr_hom h x
      rw [hx]
      refine Set.union_subset_union_right _ ?_ (ih ⟨x, rfl⟩)
      exact Set.iUnion₂_mono' fun γ hγ ↦ ⟨γ, Nat.lt_succ_of_lt hγ, subset_rfl⟩
    · obtain ⟨k, z, hz, rfl⟩ := Set.mem_iUnion.1
        ((c.attachCells n (not_isMax n)).compl_range_eq_iUnion_image_cell.subset hx)
      refine Or.inr (Set.mem_iUnion₂_of_mem (i := ⟨n, not_isMax n, k⟩) (Nat.lt_succ_self n) ?_)
      exact ⟨z, hz, rfl⟩

/-- In a relative CW complex, the image of the `n`-th stage is the range of the complex together
with the closed cells of dimension less than `n`. -/
theorem range_incl_app_eq_union_iUnion_range_cells_ι (n : ℕ) :
    Set.range (c.incl.app n) = Set.range f ∪ ⋃ (γ : c.Cells) (_ : γ.j < n), Set.range γ.ι :=
  subset_antisymm
    (c.range_incl_app_eq_union_iUnion_image_cells_ι n ▸ Set.union_subset_union_right _
      (Set.iUnion₂_mono fun _ _ ↦ Set.image_subset_range _ _))
    (Set.union_subset (c.range_eq_range_incl_app_zero ▸ c.range_incl_app_subset (Nat.zero_le n))
      (Set.iUnion₂_subset fun γ hγ ↦ c.range_cells_ι_subset γ hγ))

/-- A relative CW complex `f : X ⟶ Y` covers `Y` by the range of `f` and the open cells. -/
theorem range_union_iUnion_image_cells_ι :
    Set.range f ∪ ⋃ γ : c.Cells, γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ?_
  obtain ⟨n, x, rfl⟩ : ∃ n x, c.incl.app n x = y :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) c.isColimit) y
  have hx : c.incl.app n x ∈ Set.range (c.incl.app n) := ⟨x, rfl⟩
  rw [range_incl_app_eq_union_iUnion_image_cells_ι] at hx
  exact Set.union_subset_union_right _ (Set.iUnion₂_subset fun γ _ ↦ Set.subset_iUnion
    (fun γ : c.Cells ↦ γ.ι '' (Set.range (diskBoundaryInclusion γ.j))ᶜ) γ) hx

end TopCat.RelativeCWComplex
