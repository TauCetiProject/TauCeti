/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.Prod
public import TauCeti.Topology.VectorBundle.Thom.Prod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Thom and Euler classes of direct sums of oriented bundles

Let `E₁` and `E₂` be real vector bundles over a common base `B`, with model fibres `F₁` and `F₂`,
and let `E₁ ⊕ E₂` be their fibrewise direct sum `E₁ ×ᵇ E₂`, with model fibre `F₁ × F₂`. The
product `TauCeti.thomPairCup` of classes of the Thom pairs of `E₁` and `E₂`, `(a, b) ↦ p₁^* a ⌣
p₂^* b`, and its Euler class `TauCeti.eulerClass_thomPairCup` are in
`TauCeti.Topology.VectorBundle.Thom.Prod`.

For orientations `o₁` and `o₂`, the direct sum carries the orientation `o₁.prod o₂`, the first
factor before the second. Normalize Thom classes as in
`TauCeti.VectorBundleOrientation.thomClassOfModel`, by orientations `ω₁`, `ω₂` of the model fibres
and classes `g₁ ∈ Hᵖ(F₁, F₁ ∖ {0})`, `g₂ ∈ H^q(F₂, F₂ ∖ {0})`, and normalize the class of the
direct sum by `ω₁.prod ω₂` and the product `TauCeti.complZeroPairCross` of `g₁` and `g₂`. Then
the class of the direct sum so normalized is the product of the classes of `E₁` and `E₂`
(`TauCeti.VectorBundleOrientation.thomClassOfModel_prod`), and so its Euler class is the cup
product of their Euler classes
(`TauCeti.VectorBundleOrientation.eulerClass_thomClassOfModel_prod`). Both hold over an arbitrary
base, for any commutative ring `K`, projective coefficient modules `R₁`, `R₂`, `R₃` over `K`,
arbitrary coefficient modules `M₁`, `M₂`, `M₃`, arbitrary pairings and arbitrary model classes.
The proof reads both sides on the fibre over each point in the product of the preferred
trivializations: it reads the product orientation as the product of the two readings, and
reversing either factor reverses both the orientation and the product of the model classes.

These identities are the Whitney product formulas `U(E₁ ⊕ E₂) = p₁^* U(E₁) ⌣ p₂^* U(E₂)` and
`e(E₁ ⊕ E₂) = e(E₁) ⌣ e(E₂)` for genuine Thom and Euler classes when `g₁`, `g₂` and their
product `complZeroPairCross g₁ g₂` are generators of the local cohomology groups. This file does
not prove that `complZeroPairCross` sends generators to a generator, for any coefficients; in
particular, the integral form for `TauCeti.VectorBundleOrientation.thomClass`, normalized by the
generators `Orientation.localCohomologyClass`, further needs the product of the generators
selected by `ω₁` and `ω₂` to be the generator selected by `ω₁.prod ω₂`.

## Main results

* `TauCeti.VectorBundleOrientation.thomClassOfModel_prod`: the class of the direct sum normalized
  by the product of the model classes is the product of the normalized classes of the factors.
* `TauCeti.VectorBundleOrientation.eulerClass_thomClassOfModel_prod`: its Euler class is the cup
  product of the Euler classes of the factors.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, Property 9.6 (the Euler class of a Whitney sum) and the product formula
  for Thom classes used in its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Set

universe w

namespace TauCeti

namespace VectorBundleOrientation

section Whitney

variable {B : Type w} [TopologicalSpace B]
  {F₁ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {E₁ : B → Type w} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {E₂ : B → Type w} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  {m n : ℕ} {K : Type w} [CommRing K] {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} K}
  [Module.Projective K R₁] [Module.Projective K R₂] [Module.Projective K R₃]

/-- **The normalized Thom pair class of a direct sum is the product of those of the factors.**
Let `o₁` and `o₂` be orientations of real vector bundles `E₁` and `E₂` over a common base, and
normalize classes of their Thom pairs by orientations `ω₁`, `ω₂` of the model fibres and classes
`g₁ ∈ Hᵖ(F₁, F₁ ∖ {0})`, `g₂ ∈ H^q(F₂, F₂ ∖ {0})`. The class of the direct sum `E₁ ⊕ E₂`, with the
orientation `o₁.prod o₂` and normalized by `ω₁.prod ω₂` and the product of `g₁` and `g₂`, is the
product `p₁^* U₁ ⌣ p₂^* U₂` of the normalized classes `U₁`, `U₂` of `E₁` and `E₂`
(`TauCeti.thomPairCup`). It is the Whitney product formula for Thom classes when `g₁`, `g₂` and
`complZeroPairCross g₁ g₂` are generators, which is not proved here. -/
theorem thomClassOfModel_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n)) (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (ω₁ : Orientation ℝ F₁ (Fin m)) (ω₂ : Orientation ℝ F₂ (Fin n)) (u : R₃ ⟶ R₁ ⊗ R₂)
    (μ : M₁ ⊗ M₂ ⟶ M₃)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology R₁ K M₁
      (finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology R₂ K M₂
      (finrank ℝ F₂)) :
    (o₁.prod o₂ hm hn).thomClassOfModel (by rw [Fintype.card_fin, Module.finrank_prod, hm, hn])
        (ω₁.prod ω₂ hm hn) (complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁ g₂) =
      thomPairCup K F₁ E₁ F₂ E₂ u μ _ _ _ Module.finrank_prod.symm
        (o₁.thomClassOfModel (by rw [Fintype.card_fin, hm]) ω₁ g₁)
        (o₂.thomClassOfModel (by rw [Fintype.card_fin, hn]) ω₂ g₂) := by
  symm
  refine eq_thomClassOfModel_of_forall_exists _ _ _ _ fun b ↦ ?_
  let e₁ := trivializationAt F₁ E₁ b
  let e₂ := trivializationAt F₂ E₂ b
  have hb₁ : b ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb₂ : b ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb : b ∈ (e₁.prod e₂).baseSet := ⟨hb₁, hb₂⟩
  -- Read each factor in its own preferred trivialization, and the sum in their product.
  obtain ⟨g₁', hg₁', hr₁⟩ :=
    exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel o₁
      (by rw [Fintype.card_fin, hm]) ω₁ g₁ e₁ hb₁
  obtain ⟨g₂', hg₂', hr₂⟩ :=
    exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel o₂
      (by rw [Fintype.card_fin, hn]) ω₂ g₂ e₂ hb₂
  refine ⟨e₁.prod e₂, inferInstance, hb,
    complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁' g₂', ?_, ?_⟩
  · -- The product trivialization reads the product orientation as the product of the readings,
    -- and reversing either factor reverses both the orientation and the product class.
    rw [prod_apply, Trivialization.mapOrientation_prod e₁ e₂ hb₁ hb₂ _ _ hm hn]
    rcases hg₁' with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases hg₂' with ⟨h₂, rfl⟩ | ⟨h₂, rfl⟩ <;>
      rw [h₁, h₂]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨Orientation.prod_neg_right _ _ _ _, map_neg _ _⟩
    · exact Or.inr ⟨Orientation.prod_neg_left _ _ _ _,
        by simp only [complZeroPairCross_def, map_neg, LinearMap.neg_apply]⟩
    · exact Or.inl ⟨Orientation.prod_neg_neg _ _ _ _,
        by simp only [complZeroPairCross_def, map_neg, LinearMap.neg_apply, neg_neg]⟩
  · -- The fibres are T1, being homeomorphic to the model fibres.
    have : T1Space (E₁ b) :=
      (e₁.continuousLinearEquivAt ℝ b hb₁).toHomeomorph.isEmbedding.t1Space
    have : T1Space (E₂ b) :=
      (e₂.continuousLinearEquivAt ℝ b hb₂).toHomeomorph.isEmbedding.t1Space
    rw [singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross, hr₁, hr₂,
      Trivialization.continuousLinearEquivAt_prod]
    exact complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom K u μ
      (e₁.continuousLinearEquivAt ℝ b hb₁) (e₂.continuousLinearEquivAt ℝ b hb₂) _ _ _ _ g₁' g₂'

/-- **The Euler class of a normalized class of a direct sum.** For orientations `o₁` and `o₂` of
real vector bundles `E₁` and `E₂` over a common base, the Euler class of the class of the Thom pair
of the direct sum `E₁ ⊕ E₂`, with the orientation `o₁.prod o₂` and normalized by `ω₁.prod ω₂` and
the product of the model classes `g₁` and `g₂`, is the cup product of the Euler classes of the
classes of `E₁` and `E₂` normalized by `ω₁, g₁` and `ω₂, g₂`. It is the Whitney product formula
`e(E₁ ⊕ E₂) = e(E₁) ⌣ e(E₂)` when `g₁`, `g₂` and `complZeroPairCross g₁ g₂` are generators, which
is not proved here. -/
theorem eulerClass_thomClassOfModel_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n)) (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (ω₁ : Orientation ℝ F₁ (Fin m)) (ω₂ : Orientation ℝ F₂ (Fin n)) (u : R₃ ⟶ R₁ ⊗ R₂)
    (μ : M₁ ⊗ M₂ ⟶ M₃)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology R₁ K M₁
      (finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology R₂ K M₂
      (finrank ℝ F₂)) :
    TauCeti.eulerClass R₃ K M₃ (F₁ × F₂) (E₁ ×ᵇ E₂) _
        ((o₁.prod o₂ hm hn).thomClassOfModel
          (by rw [Fintype.card_fin, Module.finrank_prod, hm, hn]) (ω₁.prod ω₂ hm hn)
          (complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁ g₂)) =
      (TopCat.of B).singularCup K u μ _ _ _ Module.finrank_prod.symm
        (TauCeti.eulerClass R₁ K M₁ F₁ E₁ _
          (o₁.thomClassOfModel (by rw [Fintype.card_fin, hm]) ω₁ g₁))
        (TauCeti.eulerClass R₂ K M₂ F₂ E₂ _
          (o₂.thomClassOfModel (by rw [Fintype.card_fin, hn]) ω₂ g₂)) := by
  rw [thomClassOfModel_prod, eulerClass_thomPairCup]

end Whitney

end VectorBundleOrientation

end TauCeti
