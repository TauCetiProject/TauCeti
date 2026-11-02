/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Real-valued contents, contents on all subsets, and pushforward

This file complements Mathlib's `MeasureTheory.AddContent` with the material needed to treat a
finitely additive probability on *all* subsets of a type, given as an
`AddContent ℝ≥0∞ (Set.univ : Set (Set α))` of total mass one, as an ordinary real-valued
nonnegative finitely additive set function, and to move such set functions along maps and group
actions. Finitely additive probabilities on all subsets of a type are the set-theoretic form of
means on bounded functions, and on a group the invariant ones correspond to invariant means;
unlike measures, they cannot be replaced by countably additive set functions on a σ-algebra.

* For a ring of sets `C`, every content satisfies inclusion–exclusion, a content with values in an
  additive group satisfies the difference formula `m (t \ s) = m t - m s` for `s ⊆ t`, and a
  nonnegative content with values in an ordered additive monoid is monotone and finitely
  subadditive. Mathlib proves the last facts only for canonically ordered values such as `ℝ≥0∞`,
  which excludes real-valued contents.
* `MeasureTheory.AddContent.toReal` turns a content with finite values on `C` into a real-valued
  one, and `MeasureTheory.AddContent.ofReal` turns a nonnegative real-valued content into an
  `ℝ≥0∞`-valued one. They are inverse on `C`, hence inverse when `C` is the set of all subsets.
* `MeasureTheory.isSetRing_univ`: all subsets form a ring of sets, so a set function on all subsets
  that vanishes at `∅` and is additive on disjoint pairs is a content
  (`MeasureTheory.IsSetRing.addContent_of_union`). A content on all subsets with canonically
  ordered values is bounded by its total mass, so an `ℝ≥0∞`-valued one is finite when its total
  mass is. A content on all subsets takes complements to differences with the total mass, for
  values in an additive group, or for `ℝ≥0∞` values at sets of finite content.
* `MeasureTheory.AddContent.map` pushes a content forward along a map, with identity and
  composition laws. Pushforward along an equivariant map preserves invariance under a group
  action, and invariance of a content on all subsets is invariance under pushforward by every
  group element.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 1.12–1.13.
-/

public section

noncomputable section

open Set

open scoped ENNReal Pointwise

namespace MeasureTheory

variable {α β γ : Type*} {C : Set (Set α)} {s t : Set α}

/-- All subsets of a type form a ring of sets. -/
theorem isSetRing_univ : IsSetRing (univ : Set (Set α)) where
  empty_mem := mem_univ _
  union_mem _ _ _ _ := mem_univ _
  sdiff_mem _ _ _ _ := mem_univ _

section Ring

variable {G : Type*}

/-- Inclusion–exclusion for two sets in a ring of sets. -/
theorem addContent_union_add_inter [AddCommMonoid G] {m : AddContent G C} (hC : IsSetRing C)
    (hs : s ∈ C) (ht : t ∈ C) : m (s ∪ t) + m (s ∩ t) = m s + m t := by
  have hts : t \ s ∈ C := hC.sdiff_mem ht hs
  have hunion : m (s ∪ t) = m s + m (t \ s) := by
    rw [← addContent_union hC hs hts disjoint_sdiff_right, union_sdiff_self]
  have ht' : m t = m (s ∩ t) + m (t \ s) := by
    rw [inter_comm, ← addContent_union hC (hC.inter_mem ht hs) hts disjoint_inf_sdiff,
      inter_union_sdiff]
  rw [hunion, ht']
  abel

/-- In a ring of sets, a content with values in an additive group takes the difference of two
nested sets to the difference of their values. -/
theorem addContent_sdiff_of_subset [AddCommGroup G] {m : AddContent G C} (hC : IsSetRing C)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) : m (t \ s) = m t - m s := by
  rw [eq_sub_iff_add_eq, ← addContent_union hC (hC.sdiff_mem ht hs) hs disjoint_sdiff_left,
    sdiff_union_of_subset hst]

variable [AddCommMonoid G] [PartialOrder G] [IsOrderedAddMonoid G] {m : AddContent G C}

/-- A nonnegative content on a ring of sets is monotone. Unlike `MeasureTheory.addContent_mono`,
the values need not be canonically ordered, so this applies to real-valued contents. -/
theorem addContent_mono_of_nonneg (hC : IsSetRing C) (hm : ∀ u ∈ C, 0 ≤ m u) (hs : s ∈ C)
    (ht : t ∈ C) (hst : s ⊆ t) : m s ≤ m t := by
  rw [← union_sdiff_cancel hst, addContent_union hC hs (hC.sdiff_mem ht hs)
    disjoint_sdiff_right]
  exact le_add_of_nonneg_right (hm _ (hC.sdiff_mem ht hs))

/-- A nonnegative content on a ring of sets is subadditive. -/
theorem addContent_union_le_of_nonneg (hC : IsSetRing C) (hm : ∀ u ∈ C, 0 ≤ m u) (hs : s ∈ C)
    (ht : t ∈ C) : m (s ∪ t) ≤ m s + m t := by
  rw [← addContent_union_add_inter hC hs ht]
  exact le_add_of_nonneg_right (hm _ (hC.inter_mem hs ht))

/-- A nonnegative content on a ring of sets is finitely subadditive. -/
theorem addContent_biUnion_le_of_nonneg {ι : Type*} (hC : IsSetRing C) (hm : ∀ u ∈ C, 0 ≤ m u)
    {f : ι → Set α} {S : Finset ι} (hf : ∀ i ∈ S, f i ∈ C) :
    m (⋃ i ∈ S, f i) ≤ ∑ i ∈ S, m (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hiS ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.sum_insert hiS, Finset.set_biUnion_insert]
    exact (addContent_union_le_of_nonneg hC hm hf.1 (hC.biUnion_mem S hf.2)).trans
      (add_le_add_right (ih hf.2) _)

end Ring

section Univ

/-- A content on all subsets with canonically ordered values is bounded by its total mass. -/
theorem addContent_le_univ {G : Type*} [AddCommMonoid G] [PartialOrder G]
    [CanonicallyOrderedAdd G] (m : AddContent G (univ : Set (Set α))) (s : Set α) :
    m s ≤ m univ :=
  addContent_mono isSetRing_univ.isSetSemiring (mem_univ _) (mem_univ _) (subset_univ s)

/-- A content on all subsets with values in an additive group takes complements to differences
with the total mass. -/
theorem addContent_compl {G : Type*} [AddCommGroup G] (m : AddContent G (univ : Set (Set α)))
    (s : Set α) : m sᶜ = m univ - m s := by
  rw [compl_eq_univ_sdiff]
  exact addContent_sdiff_of_subset isSetRing_univ (mem_univ _) (mem_univ _) (subset_univ s)

variable {m : AddContent ℝ≥0∞ (univ : Set (Set α))}

/-- A content on all subsets with finite total mass takes only finite values. -/
theorem addContent_ne_top_of_univ_ne_top (hm : m univ ≠ ∞) (s : Set α) : m s ≠ ∞ :=
  ne_top_of_le_ne_top hm (addContent_le_univ m s)

/-- An `ℝ≥0∞`-valued content on all subsets takes the complement of a set of finite content to the
difference with the total mass. -/
theorem addContent_compl_of_ne_top (hs : m s ≠ ∞) : m sᶜ = m univ - m s := by
  rw [← union_compl_self s,
    addContent_union isSetRing_univ (mem_univ _) (mem_univ _) disjoint_compl_right,
    ENNReal.add_sub_cancel_left hs]

end Univ

namespace AddContent

section Real

/-- The real-valued content obtained from an `ℝ≥0∞`-valued content which is finite on `C`. -/
def toReal (m : AddContent ℝ≥0∞ C) (hm : ∀ u ∈ C, m u ≠ ∞) : AddContent ℝ C where
  toFun u := (m u).toReal
  empty' := by simp
  sUnion' I hI hdis hU := by
    rw [addContent_sUnion hI hdis hU, ENNReal.toReal_sum fun u hu ↦ hm u (hI hu)]

@[simp]
theorem toReal_apply (m : AddContent ℝ≥0∞ C) (hm : ∀ u ∈ C, m u ≠ ∞) (u : Set α) :
    m.toReal hm u = (m u).toReal :=
  (rfl)

/-- The `ℝ≥0∞`-valued content obtained from a real-valued content which is nonnegative on `C`. -/
def ofReal (m : AddContent ℝ C) (hm : ∀ u ∈ C, 0 ≤ m u) : AddContent ℝ≥0∞ C where
  toFun u := ENNReal.ofReal (m u)
  empty' := by simp
  sUnion' I hI hdis hU := by
    rw [addContent_sUnion hI hdis hU, ENNReal.ofReal_sum_of_nonneg fun u hu ↦ hm u (hI hu)]

@[simp]
theorem ofReal_apply (m : AddContent ℝ C) (hm : ∀ u ∈ C, 0 ≤ m u) (u : Set α) :
    m.ofReal hm u = ENNReal.ofReal (m u) :=
  (rfl)

theorem toReal_nonneg (m : AddContent ℝ≥0∞ C) (hm : ∀ u ∈ C, m u ≠ ∞) (u : Set α) :
    0 ≤ m.toReal hm u :=
  ENNReal.toReal_nonneg

theorem ofReal_ne_top (m : AddContent ℝ C) (hm : ∀ u ∈ C, 0 ≤ m u) (u : Set α) :
    m.ofReal hm u ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem ofReal_toReal_apply (m : AddContent ℝ≥0∞ C) (hm : ∀ u ∈ C, m u ≠ ∞) (hs : s ∈ C) :
    (m.toReal hm).ofReal (fun u _ ↦ toReal_nonneg m hm u) s = m s := by
  simp [ENNReal.ofReal_toReal (hm s hs)]

theorem toReal_ofReal_apply (m : AddContent ℝ C) (hm : ∀ u ∈ C, 0 ≤ m u) (hs : s ∈ C) :
    (m.ofReal hm).toReal (fun u _ ↦ ofReal_ne_top m hm u) s = m s := by
  simp [ENNReal.toReal_ofReal (hm s hs)]

/-- On all subsets, `ofReal` is a left inverse of `toReal`. -/
@[simp]
theorem ofReal_toReal (m : AddContent ℝ≥0∞ (univ : Set (Set α))) (hm : ∀ u ∈ univ, m u ≠ ∞) :
    (m.toReal hm).ofReal (fun u _ ↦ toReal_nonneg m hm u) = m :=
  AddContent.ext fun _ ↦ ofReal_toReal_apply m hm (mem_univ _)

/-- On all subsets, `toReal` is a left inverse of `ofReal`. -/
@[simp]
theorem toReal_ofReal (m : AddContent ℝ (univ : Set (Set α))) (hm : ∀ u ∈ univ, 0 ≤ m u) :
    (m.ofReal hm).toReal (fun u _ ↦ ofReal_ne_top m hm u) = m :=
  AddContent.ext fun _ ↦ toReal_ofReal_apply m hm (mem_univ _)

end Real

section Map

variable {G : Type*} [AddCommMonoid G] {D : Set (Set β)} {E : Set (Set γ)}

/-- The pushforward of a content along a map `f`, defined on a family `D` of sets whose preimages
under `f` lie in `C`. -/
def map (m : AddContent G C) (f : α → β) (hf : ∀ u ∈ D, f ⁻¹' u ∈ C) : AddContent G D where
  toFun u := m (f ⁻¹' u)
  empty' := by simp
  sUnion' I hI hdis hU := by
    rw [preimage_sUnion]
    refine addContent_biUnion (fun u hu ↦ hf u (hI hu)) ?_ ?_
    · exact fun u hu v hv huv ↦ (hdis hu hv huv).preimage f
    · simpa only [preimage_sUnion, Finset.mem_coe] using hf _ hU

@[simp]
theorem map_apply (m : AddContent G C) (f : α → β) (hf : ∀ u ∈ D, f ⁻¹' u ∈ C) (u : Set β) :
    m.map f hf u = m (f ⁻¹' u) :=
  (rfl)

@[simp]
theorem map_id (m : AddContent G C) : m.map id (fun _ hu ↦ hu) = m :=
  AddContent.ext fun _ ↦ (rfl)

theorem map_map (m : AddContent G C) {f : α → β} {g : β → γ} (hf : ∀ u ∈ D, f ⁻¹' u ∈ C)
    (hg : ∀ u ∈ E, g ⁻¹' u ∈ D) :
    (m.map f hf).map g hg = m.map (g ∘ f) (fun u hu ↦ hf _ (hg u hu)) :=
  AddContent.ext fun _ ↦ (rfl)

variable {Γ : Type*} [Group Γ] [MulAction Γ α] [MulAction Γ β]

/-- Pushforward along an equivariant map preserves invariance under a group action. -/
theorem map_apply_smul_set {F : Type*} [FunLike F α β] [MulActionHomClass F Γ α β]
    (m : AddContent G C) (f : F) (hf : ∀ u ∈ D, f ⁻¹' u ∈ C)
    (hm : ∀ (c : Γ), ∀ u ∈ C, m (c • u) = m u) (c : Γ) {u : Set β} (hu : u ∈ D) :
    m.map f hf (c • u) = m.map f hf u := by
  rw [map_apply, map_apply, Group.preimage_smul_set, hm c _ (hf u hu)]

/-- Pushing a content on all subsets forward along the action of `c` evaluates it on translates
by `c⁻¹`. -/
theorem map_smul_apply (m : AddContent G (univ : Set (Set α))) (c : Γ) (u : Set α) :
    m.map (D := univ) (c • ·) (fun _ _ ↦ mem_univ _) u = m (c⁻¹ • u) := by
  rw [map_apply, preimage_smul]

/-- A content on all subsets is invariant under a group action if and only if it is fixed by
pushforward along the action of every group element. -/
theorem forall_map_smul_eq_iff (m : AddContent G (univ : Set (Set α))) :
    (∀ c : Γ, m.map (D := univ) (c • ·) (fun _ _ ↦ mem_univ _) = m) ↔
      ∀ (c : Γ) (u : Set α), m (c • u) = m u := by
  refine ⟨fun h c u ↦ ?_, fun h c ↦ AddContent.ext fun u ↦ by rw [map_smul_apply, h]⟩
  simpa [preimage_smul] using DFunLike.congr_fun (h c⁻¹) u

end Map

end AddContent

end MeasureTheory
