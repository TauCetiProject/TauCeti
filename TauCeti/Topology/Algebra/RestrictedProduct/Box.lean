/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Coordinate boxes in restricted products

For a restricted product `Πʳ i, [R i, A i]_[𝓕]` and a family of subsets `C : ∀ i, Set (R i)`, the
coordinate box `RestrictedProduct.box C` is `{x | ∀ i, x i ∈ C i}`, i.e. the preimage of
`Set.univ.pi C` under coercion to the ambient product `Π i, R i`.

In the cofinite restricted product `Πʳ i, [R i, A i]`, a box of open sets `C i` with `A i ⊆ C i`
for all but finitely many `i` is open (`RestrictedProduct.isOpen_box_of_eventually_subset`), a box
of closed sets is closed for every filter `𝓕` (`RestrictedProduct.isClosed_box`), and a box of
compact sets with `C i ⊆ A i` cofinitely is compact (`RestrictedProduct.isCompact_box`). When every
reference set `A i` is open, open boxes `box C` satisfying `C i = A i` cofinitely form a
topological basis of `Πʳ i, [R i, A i]` (`RestrictedProduct.isTopologicalBasis_open_box`).

## Main definitions and results

* `RestrictedProduct.box`: the coordinate box `{x | ∀ i, x i ∈ C i}` in `Πʳ i, [R i, A i]_[𝓕]`.
* `RestrictedProduct.isOpen_box_of_eventually_subset`, `RestrictedProduct.isOpen_box`,
  `RestrictedProduct.isClosed_box`, `RestrictedProduct.isCompact_box`: openness, closedness, and
  compactness of coordinate boxes.
* `RestrictedProduct.isTopologicalBasis_open_box`: open boxes that agree with `A i` cofinitely form
  a topological basis of `Πʳ i, [R i, A i]` when every `A i` is open.
* `TauCeti.coe_integralSubgroupOf_eq_box`, `TauCeti.coe_integralSubgroup_eq_box`: the carrier of an
  integral subgroup is the corresponding coordinate box.

## References

* A. Weil, *Basic Number Theory*, 3rd ed., Springer (1974), Chapter IV, §1.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5, pp. 188–189.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

section SetAlgebra

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} {𝓕 𝓖 : Filter ι}

/-- The coordinate box `{x | ∀ i, x i ∈ C i}` in a restricted product `Πʳ i, [R i, A i]_[𝓕]`. -/
def box (C : ∀ i, Set (R i)) : Set (Πʳ i, [R i, A i]_[𝓕]) :=
  {x | ∀ i, x i ∈ C i}

/-- An element of a restricted product belongs to `box C` if and only if each coordinate `x i`
belongs to `C i`. -/
@[simp]
theorem mem_box {C : ∀ i, Set (R i)} {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ box C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

/-- The coordinate box with `Set.univ` in every factor is the whole restricted product. -/
@[simp]
theorem box_univ : (box (fun _ ↦ Set.univ) : Set (Πʳ i, [R i, A i]_[𝓕])) = Set.univ :=
  eq_univ_of_forall fun _ _ ↦ trivial

/-- A coordinate box with an empty factor is empty. -/
theorem box_eq_empty_of_eq_empty {C : ∀ i, Set (R i)} {i : ι} (hi : C i = ∅) :
    (box C : Set (Πʳ j, [R j, A j]_[𝓕])) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have hxi := hx i
    rw [hi] at hxi
    exact hxi

/-- When `C i ⊆ A i` along `𝓕`, `box C` is nonempty if and only if every factor `C i` is
nonempty. -/
theorem nonempty_box_iff_of_eventually_subset {C : ∀ i, Set (R i)}
    (hCA : ∀ᶠ i in 𝓕, C i ⊆ A i) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])).Nonempty ↔ ∀ i, (C i).Nonempty := by
  refine ⟨fun ⟨x, hx⟩ i ↦ ⟨x i, hx i⟩, fun hne ↦ ?_⟩
  choose f hf using hne
  refine ⟨⟨f, ?_⟩, hf⟩
  filter_upwards [hCA] with i hi
  exact hi (hf i)

/-- Coordinate boxes are monotone in their factors. -/
theorem box_mono {C D : ∀ i, Set (R i)} (h : ∀ i, C i ⊆ D i) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])) ⊆ box D :=
  fun _ hx i ↦ h i (hx i)

/-- Intersection of two coordinate boxes is the box of coordinatewise intersections. -/
@[simp]
theorem box_inter (C D : ∀ i, Set (R i)) :
    (box (fun i ↦ C i ∩ D i) : Set (Πʳ i, [R i, A i]_[𝓕])) = box C ∩ box D := by
  ext x
  exact forall_and

/-- Intersection of an indexed family of coordinate boxes is the box of coordinatewise
intersections. -/
theorem box_iInter {κ : Sort*} (C : κ → ∀ i, Set (R i)) :
    (box (fun i ↦ ⋂ k, C k i) : Set (Πʳ i, [R i, A i]_[𝓕])) = ⋂ k, box (C k) := by
  ext x
  simp only [mem_box, mem_iInter]
  exact forall_comm

/-- The coordinate box `box C` is the preimage of `Set.univ.pi C` under coercion to `Π i, R i`. -/
@[simp]
theorem preimage_coe_univ_pi (C : ∀ i, Set (R i)) :
    ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) ⁻¹' (univ.pi C) = box C := by
  ext x
  simp

/-- Pulling a coordinate box back along a filter-refinement inclusion gives the box with the same
factors. -/
@[simp]
theorem preimage_inclusion_box (h : 𝓕 ≤ 𝓖) (C : ∀ i, Set (R i)) :
    inclusion R A h ⁻¹' (box C : Set (Πʳ i, [R i, A i]_[𝓕])) =
      (box C : Set (Πʳ i, [R i, A i]_[𝓖])) := by
  ext
  simp

/-- The range of `structureMap` (the everywhere-restricted subspace) is `box A`. -/
theorem range_structureMap_eq_box :
    range (structureMap R A 𝓕) = (box A : Set (Πʳ i, [R i, A i]_[𝓕])) :=
  range_structureMap R A

/-- When `C i ⊆ A i` at every `i ∈ S` for a principal filter `𝓟 S ≥ 𝓕`, the image of `box C` under
the principal inclusion `inclusion R A hS` is `box C`. -/
theorem image_inclusion_box_of_principal {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) {C : ∀ i, Set (R i)}
    (hCA : ∀ i ∈ S, C i ⊆ A i) :
    inclusion R A hS '' (box C : Set (Πʳ i, [R i, A i]_[𝓟 S])) = box C := by
  ext x
  simp only [mem_image, mem_box]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨_, hy, rfl⟩ i
    exact hy i
  · exact ⟨⟨x, eventually_principal.mpr fun i hi ↦ hCA i hi (hx i)⟩, hx, rfl⟩

/-- The coordinate box of coordinate singletons `{x i}` is the singleton `{x}`. -/
@[simp]
theorem box_singleton (x : Πʳ i, [R i, A i]_[𝓕]) :
    (box (fun i ↦ ({x i} : Set (R i))) : Set (Πʳ i, [R i, A i]_[𝓕])) = {x} := by
  ext y
  simp [RestrictedProduct.ext_iff]

/-- When `A i` is nontrivial frequently along `𝓕`, no singleton `{x}` can be written as a coordinate
box `box C` whose factors satisfy `C i = A i` eventually along `𝓕`. -/
theorem not_exists_eventually_eq_box_eq_singleton (hA : ∃ᶠ i in 𝓕, (A i).Nontrivial)
    (x : Πʳ i, [R i, A i]_[𝓕]) :
    ¬ ∃ C : ∀ i, Set (R i), (∀ᶠ i in 𝓕, C i = A i) ∧
      (box C : Set (Πʳ i, [R i, A i]_[𝓕])) = {x} := by
  classical
  rintro ⟨C, hCA, hCx⟩
  have hxC : x ∈ box C := hCx.symm ▸ mem_singleton x
  obtain ⟨i₀, hi₀_nt, hi₀_eq⟩ := (hA.and_eventually hCA).exists
  obtain ⟨z, hzA, hzx⟩ := hi₀_nt.exists_ne (x i₀)
  let y : Πʳ i, [R i, A i]_[𝓕] :=
    ⟨Function.update (⇑x) i₀ z, x.eventually.mono fun i hi ↦ by
      by_cases h : i = i₀
      · subst h
        simpa using hzA
      · simpa [h] using hi⟩
  have hyC : y ∈ box C := mem_box.mpr fun i ↦ by
    by_cases h : i = i₀
    · subst h
      simpa [y, hi₀_eq] using hzA
    · simpa [y, h] using hxC i
  have hyx : y = x := mem_singleton_iff.mp (hCx ▸ hyC)
  exact hzx (by simpa [y] using congr_arg (fun w : Πʳ i, [R i, A i]_[𝓕] ↦ w i₀) hyx)

end SetAlgebra

section Topology

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)]

/-- For any filter `𝓕`, a coordinate box of closed sets is closed in `Πʳ i, [R i, A i]_[𝓕]`. -/
theorem isClosed_box {C : ∀ i, Set (R i)} (hC : ∀ i, IsClosed (C i)) :
    IsClosed (box C : Set (Πʳ i, [R i, A i]_[𝓕])) := by
  rw [← preimage_coe_univ_pi]
  exact (isClosed_set_pi fun i _ ↦ hC i).preimage continuous_coe

/-- In a cofinite restricted product, a coordinate box of open sets `C i` containing `A i` at all
but finitely many indices is open: on every principal stage `𝓟 T` (`T` cofinite), membership in
`C i` is automatic on `{i | A i ⊆ C i} ∩ T`, leaving finitely many open coordinate conditions. -/
theorem isOpen_box_of_eventually_subset {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen (box C : Set (Πʳ i, [R i, A i])) := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  intro T hT
  have hfin : ({i | A i ⊆ C i} ∩ T)ᶜ.Finite := mem_cofinite.mp (hAC.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage continuous_coe using 1
  ext y
  simp only [preimage_inclusion_box, mem_box, mem_preimage, Set.mem_pi]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ {i | A i ⊆ C i} ∩ T
  · exact hi.1 (y.2 hi.2)
  · exact h i hi

/-- In a cofinite restricted product, a coordinate box of open sets `C i` equal to `A i` at all but
finitely many indices is open. -/
theorem isOpen_box {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hCA : ∀ᶠ i in cofinite, C i = A i) :
    IsOpen (box C : Set (Πʳ i, [R i, A i])) :=
  isOpen_box_of_eventually_subset hC (hCA.mono fun _ hi ↦ hi.symm.subset)

/-- In a cofinite restricted product, a coordinate box of compact sets `C i` contained in `A i` at
all but finitely many indices is compact. -/
theorem isCompact_box {C : ∀ i, Set (R i)} (hC : ∀ i, IsCompact (C i))
    (hCA : ∀ᶠ i in cofinite, C i ⊆ A i) :
    IsCompact (box C : Set (Πʳ i, [R i, A i])) := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hCA
  have hK : IsCompact (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' univ.pi C) := by
    refine isEmbedding_coe_of_principal.isCompact_preimage' (isCompact_univ_pi hC) ?_
    rw [range_coe_principal]
    exact fun x hx i hi ↦ hi (hx i trivial)
  rw [preimage_coe_univ_pi] at hK
  rw [← image_inclusion_box_of_principal hS fun _ hi ↦ hi]
  exact hK.image (continuous_inclusion hS)

/-- When `A i ⊆ interior (C i)` for all but finitely many `i`, the box of interiors `interior (C i)`
lies inside the interior of `box C`. -/
theorem box_interior_subset_interior_box {C : ∀ i, Set (R i)}
    (hAC : ∀ᶠ i in cofinite, A i ⊆ interior (C i)) :
    (box (fun i ↦ interior (C i)) : Set (Πʳ i, [R i, A i])) ⊆ interior (box C) :=
  interior_maximal (box_mono fun _ ↦ interior_subset)
    (isOpen_box_of_eventually_subset (fun _ ↦ isOpen_interior) hAC)

/-- When every reference set `A i` is open in `R i`, the open boxes `box C` with `C i` open and
`C i = A i` for all but finitely many `i` form a topological basis of `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_open_box (hA : ∀ i, IsOpen (A i)) :
    TopologicalSpace.IsTopologicalBasis
      {s : Set (Πʳ i, [R i, A i]) | ∃ C : ∀ i, Set (R i),
        (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧ s = box C} := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨C, hC, hCA, rfl⟩
    exact isOpen_box hC hCA
  · intro x U hxU hU
    set S : Set ι := {i | x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
    let x₀ : Πʳ i, [R i, A i]_[𝓟 S] := ⟨x, eventually_principal.mpr fun _ hi ↦ hi⟩
    have hU₀ : IsOpen (inclusion R A hS ⁻¹' U) := hU.preimage (continuous_inclusion hS)
    obtain ⟨V, hV, hpreV⟩ := isEmbedding_coe_of_principal.isOpen_iff.mp hU₀
    have hxV : (x₀ : Π i, R i) ∈ V := by
      have hxU₀ : x₀ ∈ inclusion R A hS ⁻¹' U := hxU
      rwa [← hpreV] at hxU₀
    obtain ⟨F, W, hW, hFW⟩ := isOpen_pi_iff.mp hV _ hxV
    let C : ∀ i, Set (R i) := fun i ↦
      (if i ∈ F then W i else univ) ∩ (if i ∈ S then A i else univ)
    have hCopen (i : ι) : IsOpen (C i) := by
      refine IsOpen.inter ?_ ?_ <;> split_ifs
      · exact (hW i ‹_›).1
      · exact isOpen_univ
      · exact hA i
      · exact isOpen_univ
    have hCA : ∀ᶠ i in cofinite, C i = A i := by
      filter_upwards [x.2, F.finite_toSet.compl_mem_cofinite] with i hiS hiF
      have hiF' : i ∉ F := hiF
      simp [C, hiF', show i ∈ S from hiS]
    refine ⟨box C, ⟨C, hCopen, hCA, rfl⟩, ?_, ?_⟩
    · refine mem_box.mpr fun i ↦ ⟨?_, ?_⟩ <;> split_ifs
      · exact (hW i ‹_›).2
      · trivial
      · exact ‹i ∈ S›
      · trivial
    · intro y hy
      have hyS : ∀ i ∈ S, y i ∈ A i := fun i hiS ↦ by
        have hyi := (mem_box.mp hy i).2
        simpa [hiS] using hyi
      let y₀ : Πʳ i, [R i, A i]_[𝓟 S] := ⟨y, eventually_principal.mpr hyS⟩
      have hyF : (y₀ : Π i, R i) ∈ (F : Set ι).pi W := fun i hiF ↦ show y i ∈ W i by
        have hyi := (mem_box.mp hy i).1
        simpa [Finset.mem_coe.mp hiF] using hyi
      have hyU₀ : y₀ ∈ inclusion R A hS ⁻¹' U := by
        rw [← hpreV]
        exact hFW hyF
      exact hyU₀

/-- In a cofinite restricted product where infinitely many reference sets `A i` are nontrivial, no
singleton `{x}` is open. -/
theorem not_isOpen_singleton_of_frequently_nontrivial (hA : ∃ᶠ i in cofinite, (A i).Nontrivial)
    (x : Πʳ i, [R i, A i]) :
    ¬ IsOpen ({x} : Set (Πʳ i, [R i, A i])) := by
  classical
  intro hOpen
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.eventually
  let x₀ : Πʳ i, [R i, A i]_[𝓟 S] := ⟨x.1, eventually_principal.mpr fun _ hi ↦ hi⟩
  have hU₀ : IsOpen (inclusion R A hS ⁻¹' ({x} : Set (Πʳ i, [R i, A i]))) :=
    hOpen.preimage (continuous_inclusion hS)
  obtain ⟨V, hV, hpreV⟩ := isEmbedding_coe_of_principal.isOpen_iff.mp hU₀
  have hxV : (x₀ : Π i, R i) ∈ V := by
    have hxU₀ : x₀ ∈ inclusion R A hS ⁻¹' ({x} : Set (Πʳ i, [R i, A i])) := rfl
    rwa [← hpreV] at hxU₀
  obtain ⟨F, W, hW, hFW⟩ := isOpen_pi_iff.mp hV _ hxV
  have hSF : ∀ᶠ i in cofinite, i ∈ S ∧ i ∉ F :=
    x.eventually.and F.finite_toSet.compl_mem_cofinite
  obtain ⟨i₀, hi₀_nt, hi₀S, hi₀F⟩ := (hA.and_eventually hSF).exists
  obtain ⟨z, hzA, hzx⟩ := hi₀_nt.exists_ne (x i₀)
  let y₀ : Πʳ i, [R i, A i]_[𝓟 S] :=
    mk (Function.update (⇑x) i₀ z) (eventually_principal.mpr fun i hi ↦ by
      by_cases h : i = i₀
      · subst h
        simpa using hzA
      · simpa [h] using (show x i ∈ A i from hi))
  have hyF : (y₀ : Π i, R i) ∈ (F : Set ι).pi W := fun i hiF ↦ by
    have hii₀ : i ≠ i₀ := fun h ↦ hi₀F (h ▸ Finset.mem_coe.mp hiF)
    change Function.update (⇑x) i₀ z i ∈ W i
    rw [Function.update_of_ne hii₀]
    exact (hW i hiF).2
  have hyU₀ : y₀ ∈ inclusion R A hS ⁻¹' ({x} : Set (Πʳ i, [R i, A i])) := by
    rw [← hpreV]
    exact hFW hyF
  have hyx : inclusion R A hS y₀ = x := mem_singleton_iff.mp hyU₀
  exact hzx (by simpa [y₀] using congr_arg (fun w : Πʳ i, [R i, A i] ↦ w i₀) hyx)

end Topology

end RestrictedProduct

namespace TauCeti

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- The carrier set of `integralSubgroupOf U V` is the coordinate box `RestrictedProduct.box` of the
subgroups `V i`. -/
@[to_additive /-- The carrier set of `integralAddSubgroupOf U V` is the coordinate box
`RestrictedProduct.box` of the additive subgroups `V i`. -/]
theorem coe_integralSubgroupOf_eq_box (U V : ∀ i, Subgroup (G i)) :
    (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) =
      RestrictedProduct.box fun i ↦ (V i : Set (G i)) := by
  ext x
  exact mem_integralSubgroupOf U V x

/-- The carrier set of `integralSubgroup U` is the integral box `RestrictedProduct.box` of the
reference subgroups `U i`. -/
@[to_additive /-- The carrier set of `integralAddSubgroup U` is the integral box
`RestrictedProduct.box` of the reference additive subgroups `U i`. -/]
theorem coe_integralSubgroup_eq_box (U : ∀ i, Subgroup (G i)) :
    (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) =
      RestrictedProduct.box fun i ↦ (U i : Set (G i)) := by
  rw [← integralSubgroupOf_self, coe_integralSubgroupOf_eq_box]

end TauCeti
