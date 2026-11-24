/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable embeddings and equivalences

An injective measurable map out of a countable type into a type with measurable singletons is a
measurable embedding: every subset of the domain is countable, hence so is its image, hence
measurable.

The two inclusions into a disjoint union are measurable embeddings, so pushing a measure forward
along them preserves the measure of every set, measurable or not. A countable product of
measurable embeddings is likewise a measurable embedding (`MeasurableEmbedding.piMap`), because
coordinatewise pullbacks generate the product σ-algebra and the countable product of the factor
ranges is measurable.

On measurable equivalences, function-coercion simp lemmas identify `MeasurableEquiv.refl`,
`MeasurableEquiv.prodCongr`, and `MeasurableEquiv.prodComm` with `id`, `Prod.map`, and `Prod.swap`,
and `MeasurableEquiv.boolArrowEquivProd` lifts `Equiv.boolArrowEquivProd` to `(Bool → α) ≃ᵐ α × α`.

## Main declarations

* `MeasurableEmbedding.of_injective_of_countable`
* `MeasurableEmbedding.inl` and `MeasurableEmbedding.inr`
* `MeasurableSpace.comap_piMap` and `MeasurableEmbedding.piMap`
* `MeasurableEquiv.coe_refl`, `MeasurableEquiv.coe_prodCongr`, and `MeasurableEquiv.coe_prodComm`
* `MeasurableEquiv.boolArrowEquivProd`
-/

public section

open MeasureTheory

/-- Pulling back the product σ-algebra along `Pi.map f` gives the product of the coordinatewise
pullback σ-algebras. -/
theorem MeasurableSpace.comap_piMap {ι : Type*} {α β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] (f : ∀ i, α i → β i) :
    MeasurableSpace.pi.comap (Pi.map f) =
      @MeasurableSpace.pi ι α fun i => (mβ i).comap (f i) := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- A countable product of measurable embeddings is a measurable embedding. Countability of the
index type ensures that the product of the factor ranges is measurable in the product
σ-algebra. -/
protected theorem MeasurableEmbedding.piMap {ι : Type*} {α β : ι → Type*} [Countable ι]
    [mα : ∀ i, MeasurableSpace (α i)] [mβ : ∀ i, MeasurableSpace (β i)]
    {f : ∀ i, α i → β i} (hf : ∀ i, MeasurableEmbedding (f i)) :
    MeasurableEmbedding (Pi.map f) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨.piMap fun i => (hf i).injective, ?_, ?_⟩
  · rw [MeasurableSpace.comap_piMap]
    congr 1
    funext i
    exact (hf i).comap_eq
  · rw [Set.range_piMap]
    exact MeasurableSet.univ_pi fun i => (hf i).measurableSet_range

/-- An injective measurable map out of a countable type into a type with measurable singletons
is a measurable embedding. -/
theorem MeasurableEmbedding.of_injective_of_countable {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass γ] {f : β → γ}
    (hf : Measurable f) (hinj : Function.Injective f) : MeasurableEmbedding f where
  injective := hinj
  measurable := hf
  measurableSet_image' s _ := ((Set.to_countable s).image f).measurableSet

/-- The left inclusion into a disjoint union is a measurable embedding. -/
theorem MeasurableEmbedding.inl {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inl : α → α ⊕ β) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' _ hs := hs.inl_image

/-- The right inclusion into a disjoint union is a measurable embedding. -/
theorem MeasurableEmbedding.inr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inr : β → α ⊕ β) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' _ hs := hs.inr_image

namespace MeasurableEquiv

/-- The coercion of `MeasurableEquiv.refl` to a function is `id`. -/
@[simp]
theorem coe_refl (α : Type*) [MeasurableSpace α] : ⇑(refl α) = id :=
  (rfl)

/-- The coercion of `MeasurableEquiv.prodCongr` to a function is `Prod.map`. -/
@[simp]
theorem coe_prodCongr {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (e₁ : α ≃ᵐ β) (e₂ : γ ≃ᵐ δ) :
    ⇑(e₁.prodCongr e₂) = Prod.map e₁ e₂ :=
  (rfl)

/-- The coercion of `MeasurableEquiv.prodComm` to a function is `Prod.swap`. -/
@[simp]
theorem coe_prodComm {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    ⇑(prodComm : α × β ≃ᵐ β × α) = Prod.swap :=
  (rfl)

/-- The function type `Bool → α` is measurably equivalent to `α × α`, sending `f` to
`(f false, f true)`. Measurable version of `Equiv.boolArrowEquivProd`. -/
def boolArrowEquivProd (α : Type*) [MeasurableSpace α] : (Bool → α) ≃ᵐ α × α where
  toEquiv := Equiv.boolArrowEquivProd α
  measurable_toFun := (measurable_pi_apply false).prodMk (measurable_pi_apply true)
  measurable_invFun := measurable_pi_iff.2 <| Bool.forall_bool.2 ⟨measurable_fst, measurable_snd⟩

/-- Applying `MeasurableEquiv.boolArrowEquivProd` evaluates at `false` and `true`. -/
@[simp]
theorem boolArrowEquivProd_apply (α : Type*) [MeasurableSpace α] (f : Bool → α) :
    boolArrowEquivProd α f = (f false, f true) :=
  (rfl)

/-- Applying `(MeasurableEquiv.boolArrowEquivProd α).symm` selects the second coordinate on `true`
and the first coordinate on `false`. -/
@[simp]
theorem boolArrowEquivProd_symm_apply (α : Type*) [MeasurableSpace α] (p : α × α) (b : Bool) :
    (boolArrowEquivProd α).symm p b = if b then p.2 else p.1 :=
  (rfl)

end MeasurableEquiv
