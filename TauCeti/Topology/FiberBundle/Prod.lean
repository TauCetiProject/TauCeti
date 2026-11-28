/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Fibrewise products of bundles

The total space of a fibrewise product has the topology induced from the product of total
spaces, so each of its two components depends continuously on a vector. Its image consists
exactly of pairs with equal base points. Over a Hausdorff base this gives a closed embedding,
useful for properness of bundle actions. Preferred fibre coordinates and their changes are
componentwise (`TauCeti.trivializationAt_prod_snd`, `Bundle.Trivialization.coordChange_prod`).
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

/-- The first component of a vector of a fibrewise product, as a point of the first bundle,
depends continuously on the vector. -/
theorem continuous_totalSpaceFst :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ (⟨p.proj, p.snd.1⟩ : TotalSpace F₁ E₁) :=
  (isInducing_diag F₁ E₁ F₂ E₂).continuous.fst

/-- The second component of a vector of a fibrewise product, as a point of the second bundle,
depends continuously on the vector. -/
theorem continuous_totalSpaceSnd :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ (⟨p.proj, p.snd.2⟩ : TotalSpace F₂ E₂) :=
  (isInducing_diag F₁ E₁ F₂ E₂).continuous.snd

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

section ProductTrivializations

open Bundle.Trivialization

variable {B F₁ F₂ : Type*} {E₁ E₂ : B → Type*}
  [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, Zero (E₁ b)] [∀ b, Zero (E₂ b)]

/-- A change from a product trivialization has the two factor coordinate changes as its
components, over the base of the source trivialization. -/
theorem _root_.Bundle.Trivialization.coordChange_prod (e₁ e₁' : Bundle.Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Bundle.Trivialization F₂ (π F₂ E₂)) {b : B}
    (h₁ : b ∈ e₁.baseSet) (h₂ : b ∈ e₂.baseSet) (v₁ : F₁) (v₂ : F₂) :
    (e₁.prod e₂).coordChange (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChange e₁' b v₁, e₂.coordChange e₂' b v₂) := by
  have hsymm : (e₁.prod e₂).toOpenPartialHomeomorph.symm (b, v₁, v₂) =
      ⟨b, e₁.symm b v₁, e₂.symm b v₂⟩ := e₁.prod_symm_apply e₂ b v₁ v₂
  simp only [coordChange, hsymm, prod_apply, Prod.toFun', ← e₁.mk_symm h₁, ← e₂.mk_symm h₂]

end ProductTrivializations

namespace TauCeti

variable {B F₁ F₂ : Type*} {E₁ E₂ : B → Type*}
  [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, TopologicalSpace (E₁ b)] [∀ b, TopologicalSpace (E₂ b)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] [∀ b, Zero (E₁ b)] [∀ b, Zero (E₂ b)]

/-- The fibre coordinate in the preferred chart of a fibrewise product is the pair of
preferred fibre coordinates of its components. -/
theorem trivializationAt_prod_snd (b : B) (z : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    (trivializationAt (F₁ × F₂) (E₁ ×ᵇ E₂) b z).2 =
      ((trivializationAt F₁ E₁ b ⟨z.proj, z.snd.fst⟩).2,
        (trivializationAt F₂ E₂ b ⟨z.proj, z.snd.snd⟩).2) :=
  (rfl)

end TauCeti
