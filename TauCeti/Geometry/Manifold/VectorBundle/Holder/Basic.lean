/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Hölder spaces of sections of a vector bundle

Let `V → M` be a real vector bundle with normed model fibre `F` over a manifold `M` modelled on a
real normed space `E`, and let `A` be a finite bundle atlas: finitely many relatively compact open
sets `A.dom i` covering `M`, each inside a manifold chart and a bundle chart. In chart `i` a section
`s` of `V` is read as the function `A.coord i s : E → F` on the open set `A.image i`. This file
constructs the Banach space `C^{k,α}(V)` of sections whose readings in every chart lie in the
Hölder space `C^{k,α}(A.image i, F)` of `TauCeti.CkHolderSpaceOn`: their derivatives through order
`k` are bounded on `A.image i`, and their `k`-th derivative is `α`-Hölder there. Its norm is the
maximum over the charts of the `C^{k,α}(A.image i)` norms of the readings. These are the Hölder
norms on sections of a vector bundle over a compact manifold, the carriers of the Schauder theory
of elliptic operators on bundles.

An element is a tuple `w` of chart components, `w i ∈ C^{k,α}(A.image i, F)`, that are the
readings of a single section `s`: `w i y = A.coord i s y` for every `y ∈ A.image i`. Such tuples
are exactly those whose components are related on every overlap of two charts by the chart
transition and the coordinate change of the bundle
(`TauCeti.FiniteBundleAtlas.mem_holderSections_iff_forall_eqOn`), by gluing
(`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn`). Each of these relations is a closed
condition, since the components are continuous functions and evaluation is continuous on
`C^{k,α}(A.image i, F)`. So the tuples of readings of sections form a closed subspace of the finite
product of Hölder spaces (`TauCeti.FiniteBundleAtlas.isClosed_holderSections`), which is complete
when `F` is.

A section is determined by its readings, so every element of `C^{k,α}(V)` has a unique underlying
section (`TauCeti.HolderSection.toSection`), which is continuous. Conversely a section lies in
`C^{k,α}(V)` exactly when its readings in all charts are `C^{k,α}`
(`TauCeti.FiniteBundleAtlas.MemHolderSection`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.holderSections A k α`: the tuples of `C^{k,α}` chart components of
  sections, a submodule of `∀ i, CkHolderSpaceOn k α (A.image i) F`.
* `TauCeti.HolderSection A k α`: the Hölder space `C^{k,α}(V)`, with the maximum of the
  chartwise `C^{k,α}` norms.
* `TauCeti.HolderSection.toSection`: the underlying section, as an injective linear map.
* `TauCeti.FiniteBundleAtlas.MemHolderSection A k α s`: the readings of a section `s` in all
  charts of `A` are `C^{k,α}`.
* `TauCeti.HolderSection.ofSection`: the element of `C^{k,α}(V)` defined by such a section.

## Main results

* `TauCeti.FiniteBundleAtlas.mem_holderSections_iff_forall_eqOn`: the cocycle description of the
  tuples of readings of sections.
* `TauCeti.FiniteBundleAtlas.isClosed_holderSections` and
  `TauCeti.HolderSection.instCompleteSpace`: completeness.
* `TauCeti.HolderSection.coord_toSection`: the readings of the underlying section are the
  components, and `TauCeti.HolderSection.continuous_toSection`: the underlying section is
  continuous.
* `TauCeti.HolderSection.norm_coord_toSection_le`: the readings are bounded by the norm.
* `TauCeti.FiniteBundleAtlas.memHolderSection_iff_exists_toSection_eq`: the sections with
  `C^{k,α}` readings are exactly the underlying sections of the elements of `C^{k,α}(V)`.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9, for spaces of
  sections of a vector bundle defined chartwise from spaces of vector-valued functions.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped NNReal

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V) (k : ℕ) (α : ℝ≥0)

namespace FiniteBundleAtlas

/-- A section has `C^{k,α}` readings: in every chart of `A` its reading agrees on the chart image
with an element of `C^{k,α}(A.image i, F)`. -/
def MemHolderSection (s : ∀ x, V x) : Prop :=
  ∀ i, ∃ f : CkHolderSpaceOn k α (A.image i) F, ∀ y : A.image i, f y = A.coord i s y

variable {A k α}

theorem memHolderSection_iff {s : ∀ x, V x} :
    A.MemHolderSection k α s ↔
      ∀ i, ∃ f : CkHolderSpaceOn k α (A.image i) F, ∀ y : A.image i, f y = A.coord i s y :=
  Iff.rfl

/-- If `w` consists of the readings of `s`, then the extension by zero of each component agrees
with the reading of `s` on the image of the chart. -/
theorem eqOn_extend_coord {w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F} {s : ∀ x, V x}
    (hs : ∀ i, ∀ y : A.image i, w i y = A.coord i s y) (i : Fin A.n) :
    EqOn (w i).extend (A.coord i s) (A.image i) := fun y hy ↦
  ((w i).extend_apply ⟨y, hy⟩).trans (hs i ⟨y, hy⟩)

end FiniteBundleAtlas

variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

/-- The tuples of `C^{k,α}` chart components of sections: a tuple `w` belongs to it when some
section `s` has, in every chart `i`, reading `A.coord i s` equal to `w i` on `A.image i`. -/
def holderSections : Submodule ℝ (∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) where
  carrier := {w | ∃ s : ∀ x, V x, ∀ i, ∀ y : A.image i, w i y = A.coord i s y}
  add_mem' := by
    rintro w w' ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, fun i y ↦ by
      rw [Pi.add_apply, CkHolderSpaceOn.coe_add, Pi.add_apply, hs, ht,
          A.coord_add i s t y.property]⟩
  zero_mem' := ⟨0, fun i y ↦ by
    rw [Pi.zero_apply, CkHolderSpaceOn.coe_zero, Pi.zero_apply, A.coord_zero i y.property]⟩
  smul_mem' := by
    rintro c w ⟨s, hs⟩
    exact ⟨c • s, fun i y ↦ by
      rw [Pi.smul_apply, CkHolderSpaceOn.coe_smul, Pi.smul_apply, hs,
          A.coord_smul i c s y.property]⟩

variable {A k α}

theorem mem_holderSections_iff {w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F} :
    w ∈ A.holderSections k α ↔ ∃ s : ∀ x, V x, ∀ i, ∀ y : A.image i, w i y = A.coord i s y :=
  Iff.rfl

/-- **The cocycle description.** A tuple of `C^{k,α}` chart components consists of the readings of
a section exactly when, on the overlap of every two charts `i` and `i'`, the component in chart
`i'` is the coordinate change of the bundle applied to the component in chart `i` at the
transition point. -/
theorem mem_holderSections_iff_forall_eqOn
    {w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F} :
    w ∈ A.holderSections k α ↔ ∀ i i', EqOn (w i').extend
      (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        ((w i).extend (A.transition i i' y))) (A.overlap i i') := by
  constructor
  · rintro ⟨s, hs⟩ i i' y hy
    dsimp only
    rw [eqOn_extend_coord hs i' (A.overlap_subset_image i i' hy), A.coord_eq_coordChange s hy,
      eqOn_extend_coord hs i (A.overlap_subset_image i' i (A.transition_mem_overlap hy))]
  · intro h
    obtain ⟨t, -, ht⟩ := A.exists_continuous_coord_eqOn
      (fun i ↦ (w i).contDiffOn_extend.continuousOn) h
    exact ⟨t, fun i y ↦ by rw [← CkHolderSpaceOn.extend_apply, ht i y.property]⟩

variable (A k α)

/-- The tuples of `C^{k,α}` chart components of sections form a closed subspace of the product of
the Hölder spaces of the chart images. -/
theorem isClosed_holderSections :
    IsClosed (A.holderSections k α : Set (∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F)) := by
  have hset : (A.holderSections k α : Set (∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F)) =
      ⋂ i, ⋂ i', ⋂ y ∈ A.overlap i i', {w | (w i').extend y =
        (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
          ((w i).extend (A.transition i i' y))} := by
    ext w
    simp only [SetLike.mem_coe, mem_holderSections_iff_forall_eqOn, mem_iInter, EqOn,
      mem_ofPred_eq]
  rw [hset]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦ isClosed_biInter fun y hy ↦
    isClosed_eq ((CkHolderSpaceOn.continuous_extend_apply
      (A.overlap_subset_image i i' hy)).comp (continuous_apply i')) ?_
  exact ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)).continuous.comp
    ((CkHolderSpaceOn.continuous_extend_apply
      (A.overlap_subset_image i' i (A.transition_mem_overlap hy))).comp (continuous_apply i))

end FiniteBundleAtlas

/-- The Hölder space `C^{k,α}(V)` of sections of `V` with respect to the finite bundle atlas `A`:
the tuples of `C^{k,α}` chart components of sections, with the maximum of the chartwise
`C^{k,α}` norms. -/
abbrev HolderSection : Type _ :=
  A.holderSections k α

namespace HolderSection

/-- **Completeness.** The Hölder space of sections of a vector bundle with Banach model fibre is a
Banach space. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (HolderSection A k α) :=
  (A.isClosed_holderSections k α).completeSpace_coe

variable {A k α}

/-- The norm of `C^{k,α}(V)` is the norm of the tuple of chart components, the maximum of their
`C^{k,α}` norms. -/
theorem norm_def (w : HolderSection A k α) :
    ‖w‖ = ‖(w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F)‖ :=
  (Submodule.norm_coe w).symm

/-- Each chart component has norm at most the norm of the section. -/
theorem norm_component_le (w : HolderSection A k α) (i : Fin A.n) :
    ‖(w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i‖ ≤ ‖w‖ :=
  norm_le_pi_norm _ i

/-- A bound on the norms of all chart components bounds the norm of the section. -/
theorem norm_le_of_forall_norm_component_le (w : HolderSection A k α) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖(w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i‖ ≤ C) : ‖w‖ ≤ C :=
  pi_norm_le_iff_of_nonneg hC |>.2 h

/-- The readings of the section chosen for an element of `C^{k,α}(V)` are its chart components. -/
private theorem coord_choose (w : HolderSection A k α) {i : Fin A.n} {y : E} (hy : y ∈ A.image i) :
    A.coord i w.property.choose y = (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ⟨y, hy⟩
        :=
  (w.property.choose_spec i ⟨y, hy⟩).symm

/-- The section of an element of `C^{k,α}(V)`: the unique section whose readings are its chart
components (`TauCeti.HolderSection.coord_toSection`). -/
def toSection : HolderSection A k α →ₗ[ℝ] ∀ x, V x where
  toFun w := w.property.choose
  map_add' w w' := A.eq_of_forall_eqOn_coord fun i y hy ↦ by
    rw [A.coord_add i _ _ hy, coord_choose _ hy, coord_choose _ hy, coord_choose _ hy]
    simp
  map_smul' c w := A.eq_of_forall_eqOn_coord fun i y hy ↦ by
    rw [RingHom.id_apply, A.coord_smul i _ _ hy, coord_choose _ hy, coord_choose _ hy]
    simp

/-- **The readings of the underlying section are the chart components.** -/
@[simp]
theorem coord_toSection (w : HolderSection A k α) (i : Fin A.n) (y : A.image i) :
    A.coord i (toSection w) y = (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i y :=
  (w.property.choose_spec i y).symm

/-- The underlying section is the only section whose readings are the chart components. -/
theorem toSection_eq_iff {w : HolderSection A k α} {s : ∀ x, V x} :
    toSection w = s ↔
      ∀ i, ∀ y : A.image i, (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i y =
        A.coord i s y := by
  refine ⟨fun h i y ↦ by rw [← h, coord_toSection], fun h ↦ ?_⟩
  exact A.eq_of_forall_eqOn_coord fun i y hy ↦ by rw [coord_toSection w i ⟨y, hy⟩, h i ⟨y, hy⟩]

/-- **Uniqueness.** An element of `C^{k,α}(V)` is determined by its underlying section. -/
theorem toSection_injective : Function.Injective (toSection : HolderSection A k α → ∀ x, V x) :=
  fun w w' h ↦ Subtype.ext <| funext fun i ↦ CkHolderSpaceOn.ext fun y ↦ by
    rw [← coord_toSection, ← coord_toSection, h]

/-- Two elements of `C^{k,α}(V)` are equal when their underlying sections are. -/
@[ext]
theorem ext {w w' : HolderSection A k α} (h : toSection w = toSection w') : w = w' :=
  toSection_injective h

/-- The underlying section of an element of `C^{k,α}(V)` is continuous. -/
theorem continuous_toSection (w : HolderSection A k α) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection w x) := by
  obtain ⟨t, ht, htw⟩ := A.exists_continuous_coord_eqOn
    (fun i ↦
      ((w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i).contDiffOn_extend.continuousOn)
    (A.mem_holderSections_iff_forall_eqOn.1 w.property)
  obtain rfl : t = toSection w := A.eq_of_forall_eqOn_coord fun i y hy ↦ by
    rw [htw i hy, coord_toSection w i ⟨y, hy⟩, ← CkHolderSpaceOn.extend_apply]
  exact ht

/-- The readings of the underlying section are bounded by the norm of the section. -/
theorem norm_coord_toSection_le (w : HolderSection A k α) (i : Fin A.n) (y : A.image i) :
    ‖A.coord i (toSection w) y‖ ≤ ‖w‖ := by
  rw [coord_toSection]
  exact (CkHolderSpaceOn.norm_apply_le _ y).trans (norm_component_le w i)

/-- The element of `C^{k,α}(V)` defined by a section whose readings are `C^{k,α}`. -/
def ofSection (s : ∀ x, V x) (hs : A.MemHolderSection k α s) : HolderSection A k α :=
  ⟨fun i ↦ (hs i).choose, s, fun i ↦ (hs i).choose_spec⟩

/-- The chart components of `ofSection s` are the readings of `s`. -/
@[simp]
theorem ofSection_apply (s : ∀ x, V x) (hs : A.MemHolderSection k α s) (i : Fin A.n)
    (y : A.image i) :
    (ofSection s hs : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i y = A.coord i s y :=
  (hs i).choose_spec y

@[simp]
theorem toSection_ofSection (s : ∀ x, V x) (hs : A.MemHolderSection k α s) :
    toSection (ofSection s hs) = s :=
  toSection_eq_iff.2 (ofSection_apply s hs)

@[simp]
theorem ofSection_toSection (w : HolderSection A k α) (hs : A.MemHolderSection k α (toSection w)) :
    ofSection (toSection w) hs = w :=
  toSection_injective (toSection_ofSection _ hs)

end HolderSection

namespace FiniteBundleAtlas

variable {A k α}

/-- The underlying section of an element of `C^{k,α}(V)` has `C^{k,α}` readings. -/
theorem memHolderSection_toSection (w : HolderSection A k α) :
    A.MemHolderSection k α (HolderSection.toSection w) :=
  fun i ↦ ⟨(w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i,
    fun y ↦ (HolderSection.coord_toSection w i y).symm⟩

/-- **The sections of class `C^{k,α}`.** A section has `C^{k,α}` readings exactly when it is the
underlying section of an element of `C^{k,α}(V)`. -/
theorem memHolderSection_iff_exists_toSection_eq {s : ∀ x, V x} :
    A.MemHolderSection k α s ↔ ∃ w : HolderSection A k α, HolderSection.toSection w = s :=
  ⟨fun hs ↦ ⟨HolderSection.ofSection s hs, HolderSection.toSection_ofSection s hs⟩,
    fun ⟨w, hw⟩ ↦ hw ▸ memHolderSection_toSection w⟩

/-- The zero section is of class `C^{k,α}`. -/
theorem MemHolderSection.zero : A.MemHolderSection k α (0 : ∀ x, V x) :=
  memHolderSection_iff_exists_toSection_eq.2 ⟨0, map_zero _⟩

/-- A sum of sections of class `C^{k,α}` is of class `C^{k,α}`. -/
theorem MemHolderSection.add {s t : ∀ x, V x} (hs : A.MemHolderSection k α s)
    (ht : A.MemHolderSection k α t) : A.MemHolderSection k α (s + t) := by
  obtain ⟨w, rfl⟩ := memHolderSection_iff_exists_toSection_eq.1 hs
  obtain ⟨w', rfl⟩ := memHolderSection_iff_exists_toSection_eq.1 ht
  exact memHolderSection_iff_exists_toSection_eq.2 ⟨w + w', map_add _ w w'⟩

/-- A scalar multiple of a section of class `C^{k,α}` is of class `C^{k,α}`. -/
theorem MemHolderSection.smul (c : ℝ) {s : ∀ x, V x} (hs : A.MemHolderSection k α s) :
    A.MemHolderSection k α (c • s) := by
  obtain ⟨w, rfl⟩ := memHolderSection_iff_exists_toSection_eq.1 hs
  exact memHolderSection_iff_exists_toSection_eq.2 ⟨c • w, map_smul _ c w⟩

/-- Sections of class `C^{k,α}` are continuous. -/
theorem MemHolderSection.continuous {s : ∀ x, V x} (hs : A.MemHolderSection k α s) :
    Continuous fun x ↦ TotalSpace.mk' F x (s x) := by
  obtain ⟨w, rfl⟩ := memHolderSection_iff_exists_toSection_eq.1 hs
  exact HolderSection.continuous_toSection w

end FiniteBundleAtlas

end TauCeti
