/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions

/-!
# The fibrewise product as a closed relation

The total space of a fibrewise product has the topology induced from the product of total
spaces. Its image consists exactly of pairs with equal base points. Over a Hausdorff base
this gives a closed embedding, useful for properness of bundle actions.
-/

public section

open Bundle Set

namespace FiberBundle.Prod

variable {B F₁ F₂ : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

/-- The diagonal map of a fibrewise product is a topological embedding. -/
theorem isEmbedding_diag :
    Topology.IsEmbedding (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      ((⟨p.proj, p.snd.1⟩ : TotalSpace F₁ E₁), (⟨p.proj, p.snd.2⟩ : TotalSpace F₂ E₂))) := by
  refine ⟨isInducing_diag F₁ E₁ F₂ E₂, ?_⟩
  rintro ⟨b, u, v⟩ ⟨b', u', v'⟩ h
  have hb := congrArg (fun q ↦ q.1.proj) h
  dsimp at hb
  subst b'
  simp only [Prod.mk.injEq, TotalSpace.mk_inj] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

omit [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)] in
/-- The image of the fibrewise product is exactly the same-base relation. -/
theorem range_diag :
    range (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      ((⟨p.proj, p.snd.1⟩ : TotalSpace F₁ E₁), (⟨p.proj, p.snd.2⟩ : TotalSpace F₂ E₂))) =
      {p | p.1.proj = p.2.proj} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · rcases p with ⟨⟨b, u⟩, ⟨b', v⟩⟩
    intro h
    dsimp at h
    subst b'
    exact ⟨⟨b, u, v⟩, rfl⟩

/-- Over a Hausdorff base the fibrewise product is closed in the product of total spaces. -/
theorem isClosedEmbedding_diag [TopologicalSpace B] [T2Space B]
    (h₁ : Continuous (π F₁ E₁)) (h₂ : Continuous (π F₂ E₂)) :
    Topology.IsClosedEmbedding (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      ((⟨p.proj, p.snd.1⟩ : TotalSpace F₁ E₁), (⟨p.proj, p.snd.2⟩ : TotalSpace F₂ E₂))) := by
  refine ⟨isEmbedding_diag, ?_⟩
  rw [range_diag]
  exact isClosed_eq (h₁.comp continuous_fst) (h₂.comp continuous_snd)

end FiberBundle.Prod
