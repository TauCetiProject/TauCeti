/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuity under monotone order extensions

Let `X` be a topological space and `f : X → β` a map into a preorder whose upper level sets
`f ⁻¹' Set.Ici v` are closed and which takes only finitely many values on a neighborhood of each
point. For any monotone map `φ : β → γ` into another preorder, every upper level set
`(φ ∘ f) ⁻¹' Set.Ici c` locally agrees with a finite union of upper level sets of `f`
(`TauCeti.inter_preimage_Ici_comp_eq_biUnion`), so it is closed
(`TauCeti.isClosed_preimage_Ici_comp`).

When `γ` is linearly ordered, this transfers upper semicontinuity to `φ ∘ f`
(`TauCeti.upperSemicontinuous_comp_of_monotone`). In particular, if each coordinate of a locally
finitely valued map `f : X → ∀ i, β i` into a well-ordered product of linear orders is upper
semicontinuous, then `toLex ∘ f` is upper semicontinuous for the lexicographic order
(`TauCeti.upperSemicontinuous_toLex_comp`).

## Main results

* `TauCeti.inter_preimage_Ici_comp_eq_biUnion`: on any set `U`, the upper level set of `φ ∘ f`
  equals the union of the upper level sets of `f` over values attained in `U` satisfying `c ≤ φ v`.
* `TauCeti.isClosed_preimage_Ici_comp`: closedness of upper level sets transfers along a monotone
  map when `f` takes locally finitely many values.
* `TauCeti.upperSemicontinuous_comp_of_monotone`: upper semicontinuity into a linear order `γ`
  from closedness of upper level sets of `f` and local finiteness of the values of `f`.
* `TauCeti.upperSemicontinuous_toLex_comp`: coordinatewise upper semicontinuity plus locally
  finitely many values implies lexicographic upper semicontinuity.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*,
  Asian J. Math. 16 (2012), no. 4, 711–740, §6.1.
-/

public section

namespace TauCeti

/-- On any subset `U` of `X`, the upper level set of `φ ∘ f` above `c` is the union over the
values `v ∈ f '' U` with `c ≤ φ v` of the corresponding upper level sets of `f` inside `U`. -/
theorem inter_preimage_Ici_comp_eq_biUnion {X β γ : Type*} [Preorder β] [Preorder γ]
    {f : X → β} {φ : β → γ} (hφ : Monotone φ) (U : Set X) (c : γ) :
    U ∩ (φ ∘ f) ⁻¹' Set.Ici c =
      ⋃ v ∈ f '' U ∩ φ ⁻¹' Set.Ici c, (U ∩ f ⁻¹' Set.Ici v) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply, Set.mem_Ici,
    Set.mem_iUnion, Set.mem_image, exists_prop]
  refine ⟨fun ⟨hxU, hcx⟩ ↦ ⟨f x, ⟨⟨x, hxU, rfl⟩, hcx⟩, hxU, le_rfl⟩, ?_⟩
  rintro ⟨v, ⟨-, hcv⟩, hxU, hvx⟩
  exact ⟨hxU, hcv.trans (hφ hvx)⟩

/-- If `f : X → β` has closed upper level sets `f ⁻¹' Set.Ici v` and takes only finitely many
values on an open neighborhood of each point, then for any monotone `φ : β → γ` the upper level
sets `(φ ∘ f) ⁻¹' Set.Ici c` are closed. -/
theorem isClosed_preimage_Ici_comp {X β γ : Type*} [TopologicalSpace X] [Preorder β] [Preorder γ]
    {f : X → β} {φ : β → γ} (hφ : Monotone φ)
    (hclosed : ∀ v : β, IsClosed (f ⁻¹' Set.Ici v))
    (hfin : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (f '' U).Finite) (c : γ) :
    IsClosed ((φ ∘ f) ⁻¹' Set.Ici c) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hUopen, hxU, hUfin⟩ := hfin x
  let S : Set β := f '' U ∩ φ ⁻¹' Set.Ici c
  let F : Set X := ⋃ v ∈ S, f ⁻¹' Set.Ici v
  have hFclosed : IsClosed F :=
    (hUfin.subset Set.inter_subset_left).isClosed_biUnion fun v _ ↦ hclosed v
  have hlocal : U ∩ (φ ∘ f) ⁻¹' Set.Ici c = U ∩ F := by
    rw [inter_preimage_Ici_comp_eq_biUnion hφ U c, Set.inter_iUnion₂]
  refine ⟨U ∩ Fᶜ, ?_, hUopen.inter hFclosed.isOpen_compl, hxU, ?_⟩
  · intro y ⟨hyU, hyF⟩ hyc
    have : y ∈ U ∩ F := hlocal ▸ ⟨hyU, hyc⟩
    exact hyF this.2
  · intro hxF
    have : x ∈ U ∩ (φ ∘ f) ⁻¹' Set.Ici c := hlocal.symm ▸ ⟨hxU, hxF⟩
    exact hx this.2

/-- If `f : X → β` has closed upper level sets and takes locally finitely many values, then `φ ∘ f`
is upper semicontinuous for every monotone map `φ : β → γ` into a linear order `γ`. -/
theorem upperSemicontinuous_comp_of_monotone {X β γ : Type*} [TopologicalSpace X] [Preorder β]
    [LinearOrder γ] {f : X → β} {φ : β → γ} (hφ : Monotone φ)
    (hclosed : ∀ v : β, IsClosed (f ⁻¹' Set.Ici v))
    (hfin : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (f '' U).Finite) :
    UpperSemicontinuous (φ ∘ f) :=
  upperSemicontinuous_iff_isClosed_preimage.mpr
    (isClosed_preimage_Ici_comp hφ hclosed hfin)

/-- If every coordinate `x ↦ f x i` of a map `f : X → ∀ i, β i` into a well-ordered product of
linear orders is upper semicontinuous and `f` attains only finitely many values on a neighborhood
of each point, then `toLex ∘ f` is upper semicontinuous for the lexicographic order. -/
theorem upperSemicontinuous_toLex_comp {X ι : Type*} {β : ι → Type*}
    [TopologicalSpace X] [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]
    {f : X → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous fun x ↦ f x i)
    (hfin : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (f '' U).Finite) :
    UpperSemicontinuous (toLex ∘ f) := by
  refine upperSemicontinuous_comp_of_monotone Pi.toLex_monotone (fun v ↦ ?_) hfin
  have hpre : f ⁻¹' Set.Ici v = ⋂ i, (fun x ↦ f x i) ⁻¹' Set.Ici (v i) := by
    ext x
    simp [Pi.le_def]
  rw [hpre]
  exact isClosed_iInter fun i ↦ (hf i).isClosed_preimage (v i)

end TauCeti
