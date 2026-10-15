/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Extending a homeomorphism of an open piece by the identity

Let `χ : Z → Y` be an open embedding, for instance a chart onto an open subset of `Y`, and let `Λ`
be a homeomorphism of `Z` that moves only points lying over a closed subset `C` of `Y` contained in
the image of `χ`. Transporting `Λ` along `χ` and extending by the identity off `C` gives a
homeomorphism of `Y`. This is how a homeomorphism written down in coordinates is made global: the
closedness of `C` is what makes the identity extension continuous at the frontier of the image of
`χ`.

## Main results

* `Topology.IsOpenEmbedding.exists_homeomorph_extend`: the homeomorphism of `Y` extending `Λ`
  along `χ` by the identity.
-/

public section

open Set Filter Topology

namespace Topology.IsOpenEmbedding

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {χ : Z → Y} {C : Set Y}

/-- The transport of `Φ` along `χ`, extended by the identity off the image of `χ`. -/
private noncomputable def extendFun (χ : Z → Y) (Φ : Z → Z) (y : Y) : Y :=
  open Classical in if hy : y ∈ range χ then χ (Φ hy.choose) else y

private theorem extendFun_apply (hχ : IsOpenEmbedding χ) (Φ : Z → Z) (z : Z) :
    extendFun χ Φ (χ z) = χ (Φ z) := by
  have hz : χ z ∈ range χ := mem_range_self z
  rw [extendFun, dite_eq_left hz, hχ.injective hz.choose_spec]

private theorem extendFun_eq_self (hχ : IsOpenEmbedding χ) {Φ : Z → Z}
    (hΦ : ∀ z, χ z ∉ C → Φ z = z) {y : Y} (hy : y ∉ C) : extendFun χ Φ y = y := by
  by_cases hyχ : y ∈ range χ
  · obtain ⟨z, rfl⟩ := hyχ
    rw [extendFun_apply hχ, hΦ z hy]
  · rw [extendFun, dite_eq_right hyχ]

private theorem continuous_extendFun (hχ : IsOpenEmbedding χ) (hC : IsClosed C)
    (hCχ : C ⊆ range χ) {Φ : Z → Z} (hΦc : Continuous Φ) (hΦ : ∀ z, χ z ∉ C → Φ z = z) :
    Continuous (extendFun χ Φ) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hyχ : y ∈ range χ
  · -- On the open image of `χ` the extension is `χ ∘ Φ` read through the chart.
    obtain ⟨z, rfl⟩ := hyχ
    rw [← hχ.isInducing.continuousAt_iff' (hχ.isOpen_range.mem_nhds (mem_range_self z))]
    have hcomp : extendFun χ Φ ∘ χ = χ ∘ Φ := funext (extendFun_apply hχ Φ)
    rw [hcomp]
    exact (hχ.continuous.comp hΦc).continuousAt
  · -- Off the image of `χ` the point lies in the open complement of `C`, where the extension is
    -- the identity.
    have hyC : y ∉ C := fun h => hyχ (hCχ h)
    refine continuousAt_id.congr ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hyC] with w hw
    exact (extendFun_eq_self hχ hΦ hw).symm

/-- A homeomorphism `Λ` of `Z`, moving only points whose images under the open embedding `χ` lie in
a closed set `C ⊆ range χ`, extends along `χ` by the identity to a homeomorphism of `Y`: one that
agrees with `Λ` read through `χ` and fixes every point off `C`. -/
theorem exists_homeomorph_extend (hχ : IsOpenEmbedding χ) (Λ : Z ≃ₜ Z) (hC : IsClosed C)
    (hCχ : C ⊆ range χ) (hΛ : ∀ z, χ z ∉ C → Λ z = z) :
    ∃ H : Y ≃ₜ Y, (∀ z, H (χ z) = χ (Λ z)) ∧ ∀ y ∉ C, H y = y := by
  have hΛs : ∀ z, χ z ∉ C → Λ.symm z = z := fun z hz => by
    rw [Λ.symm_apply_eq, hΛ z hz]
  -- Both extensions fix `C`'s complement, and they are mutually inverse on the image of `χ`.
  have hinv : ∀ (Φ Ψ : Z ≃ₜ Z), (∀ z, Ψ (Φ z) = z) → (∀ z, χ z ∉ C → Φ z = z) →
      (∀ z, χ z ∉ C → Ψ z = z) → ∀ y, extendFun χ Ψ (extendFun χ Φ y) = y := by
    intro Φ Ψ hΨΦ hΦ hΨ y
    by_cases hyχ : y ∈ range χ
    · obtain ⟨z, rfl⟩ := hyχ
      rw [extendFun_apply hχ, extendFun_apply hχ, hΨΦ]
    · have hyC : y ∉ C := fun h => hyχ (hCχ h)
      rw [extendFun_eq_self hχ hΦ hyC, extendFun_eq_self hχ hΨ hyC]
  exact ⟨{ toFun := extendFun χ Λ
           invFun := extendFun χ Λ.symm
           left_inv := hinv Λ Λ.symm Λ.symm_apply_apply hΛ hΛs
           right_inv := hinv Λ.symm Λ Λ.apply_symm_apply hΛs hΛ
           continuous_toFun := continuous_extendFun hχ hC hCχ Λ.continuous hΛ
           continuous_invFun := continuous_extendFun hχ hC hCχ Λ.symm.continuous hΛs },
    extendFun_apply hχ Λ, fun _ hy => extendFun_eq_self hχ hΛ hy⟩

end Topology.IsOpenEmbedding
