/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Extending maps of an open piece by the identity

Let `j : Y → X` be an open embedding. A continuous family of self-maps of `Y` which fixes the
points of `j ⁻¹' V`, for an open neighbourhood `V` of the complement of the range of `j`, extends
by the identity to a continuous family of self-maps of `X` which fixes every point of `V`.

Let `χ : Z → Y` be an open embedding, for instance a chart onto an open subset of `Y`, and let `Λ`
be a homeomorphism of `Z` that moves only points lying over a closed subset `C` of `Y` contained in
the image of `χ`. Transporting `Λ` along `χ` and extending by the identity off `C` gives a
homeomorphism of `Y`. This is how a homeomorphism written down in coordinates is made global: the
closedness of `C` is what makes the identity extension continuous at the frontier of the image of
`χ`.

## Main results

* `Topology.IsOpenEmbedding.exists_continuousMap_extend_id`: a continuous family of self-maps of
  `Y` extended along `j` by the identity.
* `Topology.IsOpenEmbedding.exists_homeomorph_extend`: the homeomorphism of `Y` extending `Λ`
  along `χ` by the identity.
-/

public section

open Set Filter Topology

namespace Topology.IsOpenEmbedding

/-- **A family of self-maps of an open piece extends by the identity.** Let `j : Y → X` be an open
embedding and `G : Z × Y → Y` a continuous family of self-maps of `Y`. If `V` is an open set
containing the points outside the range of `j` and every `G z` fixes the points of `j ⁻¹' V`, then
the family transported along `j` extends to a continuous family of self-maps of `X` that fixes
every point of `V`. -/
theorem exists_continuousMap_extend_id {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {j : Y → X} (hj : IsOpenEmbedding j) {Z : Type*} [TopologicalSpace Z]
    {V : Set X} (hV : IsOpen V) (hjV : (range j)ᶜ ⊆ V) (G : C(Z × Y, Y))
    (hG : ∀ z y, j y ∈ V → G (z, y) = y) :
    ∃ Φ : C(Z × X, X), (∀ z y, Φ (z, j y) = j (G (z, y))) ∧ ∀ z, ∀ x ∈ V, Φ (z, x) = x := by
  let Φ : Z × X → X := fun p ↦ Function.extend j (fun y ↦ j (G (p.1, y))) id p.2
  have hΦj (z : Z) (y : Y) : Φ (z, j y) = j (G (z, y)) := hj.injective.extend_apply _ _ y
  -- `Φ` is the identity on `V`.
  have hΦV (z : Z) (x : X) (hx : x ∈ V) : Φ (z, x) = x := by
    by_cases hxj : x ∈ range j
    · obtain ⟨y, rfl⟩ := hxj
      rw [hΦj, hG z y hx]
    · exact Function.extend_apply' _ _ _ hxj
  refine ⟨⟨Φ, continuous_iff_continuousAt.2 fun ⟨z, x⟩ ↦ ?_⟩, hΦj, hΦV⟩
  by_cases hxj : x ∈ range j
  · -- Over the open range of `j`, `Φ` is the transported family.
    obtain ⟨y, rfl⟩ := hxj
    have hcomp : Φ ∘ Prod.map id j = j ∘ G := funext fun q ↦ hΦj q.1 q.2
    refine ((IsOpenEmbedding.id.prodMap hj).continuousAt_iff (x := (z, y))).1 ?_
    rw [hcomp]
    exact (hj.continuous.comp G.continuous).continuousAt
  · -- Near a point outside the range of `j`, `Φ` is the identity.
    exact continuousAt_snd.congr (Filter.eventually_of_mem
      ((hV.preimage continuous_snd).mem_nhds (hjV hxj)) fun q hq ↦ (hΦV q.1 q.2 hq).symm)

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {χ : Z → Y} {C : Set Y}

/-- A homeomorphism `Λ` of `Z`, moving only points whose images under the open embedding `χ` lie in
a closed set `C ⊆ range χ`, extends along `χ` by the identity to a homeomorphism of `Y`: one that
agrees with `Λ` read through `χ` and fixes every point off `C`. -/
theorem exists_homeomorph_extend (hχ : IsOpenEmbedding χ) (Λ : Z ≃ₜ Z) (hC : IsClosed C)
    (hCχ : C ⊆ range χ) (hΛ : ∀ z, χ z ∉ C → Λ z = z) :
    ∃ H : Y ≃ₜ Y, (∀ z, H (χ z) = χ (Λ z)) ∧ ∀ y ∉ C, H y = y := by
  have hΛs : ∀ z, χ z ∉ C → Λ.symm z = z := fun z hz => by
    rw [Λ.symm_apply_eq, hΛ z hz]
  -- Extend `Λ` and `Λ.symm`, viewed as constant families over `Unit`, by the identity off `C`.
  have hext (Φ : Z ≃ₜ Z) (hΦ : ∀ z, χ z ∉ C → Φ z = z) :
      ∃ f : C(Y, Y), (∀ z, f (χ z) = χ (Φ z)) ∧ ∀ y ∉ C, f y = y := by
    obtain ⟨F, hFχ, hF⟩ := hχ.exists_continuousMap_extend_id hC.isOpen_compl
      (fun _ hy h => hy (hCχ h)) ⟨fun p : Unit × Z => Φ p.2, Φ.continuous.comp continuous_snd⟩
      fun _ => hΦ
    exact ⟨⟨fun y => F ((), y), F.continuous.comp (.prodMk continuous_const continuous_id)⟩,
      hFχ (), hF ()⟩
  obtain ⟨f, hfχ, hf⟩ := hext Λ hΛ
  obtain ⟨g, hgχ, hg⟩ := hext Λ.symm hΛs
  -- The two extensions fix `C`'s complement, and they are mutually inverse on the image of `χ`.
  have hinv : ∀ (u v : C(Y, Y)) (Φ Ψ : Z → Z), (∀ z, Ψ (Φ z) = z) → (∀ z, u (χ z) = χ (Φ z)) →
      (∀ z, v (χ z) = χ (Ψ z)) → (∀ y ∉ C, u y = y) → (∀ y ∉ C, v y = y) → ∀ y, v (u y) = y := by
    intro u v Φ Ψ hΨΦ hu hv hu' hv' y
    by_cases hyχ : y ∈ range χ
    · obtain ⟨z, rfl⟩ := hyχ
      rw [hu, hv, hΨΦ]
    · have hyC : y ∉ C := fun h => hyχ (hCχ h)
      rw [hu' y hyC, hv' y hyC]
  exact ⟨{ toFun := f
           invFun := g
           left_inv := hinv f g Λ Λ.symm Λ.symm_apply_apply hfχ hgχ hf hg
           right_inv := hinv g f Λ.symm Λ Λ.apply_symm_apply hgχ hfχ hg hf
           continuous_toFun := f.continuous
           continuous_invFun := g.continuous }, hfχ, hf⟩

end Topology.IsOpenEmbedding
