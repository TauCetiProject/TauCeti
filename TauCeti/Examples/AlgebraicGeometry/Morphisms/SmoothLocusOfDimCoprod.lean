/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.OfDim
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Check: the smooth locus of a scheme that is not pure-dimensional

For a field `k`, the disjoint union `X = 𝔸²_k ⊔ 𝔸¹_k` is smooth over `k`, so its smooth locus is
all of `X`, and in particular dense. But `X` is not pure-dimensional, and the smooth locus of
dimension `2` misses the line: a point of `𝔸¹_k` lies in `X_sm` but not in `X_sm^{(2)}`. So the
equality `X_sm = X_sm^{(d)}` of the setting of Nash blowups needs `X` to be pure of dimension `d`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.SmoothLocusOfDimCoprodExample

noncomputable section

variable (k : Type u) [Field k]

/-- The plane `𝔸²_k`. -/
abbrev plane : Scheme.{u} := 𝔸(ULift.{u} (Fin 2); Spec (.of k))

/-- The line `𝔸¹_k`. -/
abbrev line : Scheme.{u} := 𝔸(ULift.{u} (Fin 1); Spec (.of k))

/-- The disjoint union `𝔸²_k ⊔ 𝔸¹_k`. -/
abbrev planeLine : Scheme.{u} := plane k ⨿ line k

/-- `𝔸²_k ⊔ 𝔸¹_k` lies over `Spec k` through the structure morphisms of its two components. -/
instance overPlaneLine : (planeLine k).Over (Spec (.of k)) :=
  ⟨coprod.desc (plane k ↘ Spec (.of k)) (line k ↘ Spec (.of k))⟩

/-- The inclusion of the line is a morphism over `Spec k`. -/
instance isOver_inr : (coprod.inr : line k ⟶ planeLine k).IsOver (Spec (.of k)) :=
  ⟨coprod.inr_desc _ _⟩

/-- A property local at the source holds for `𝔸²_k ⊔ 𝔸¹_k ⟶ Spec k` when it holds for both
components. -/
theorem planeLine_over {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    (h₁ : P (plane k ↘ Spec (.of k))) (h₂ : P (line k ↘ Spec (.of k))) :
    P (planeLine k ↘ Spec (.of k)) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (coprodOpenCover.{_, 0} (plane k) (line k))]
  rintro (⟨⟩ | ⟨⟩)
  · change P (coprod.inl ≫ coprod.desc (plane k ↘ Spec (.of k)) (line k ↘ Spec (.of k)))
    rwa [coprod.inl_desc]
  · change P (coprod.inr ≫ coprod.desc (plane k ↘ Spec (.of k)) (line k ↘ Spec (.of k)))
    rwa [coprod.inr_desc]

/-- `𝔸²_k ⊔ 𝔸¹_k` is smooth over `Spec k`. -/
instance smooth_planeLine : Smooth (planeLine k ↘ Spec (.of k)) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  planeLine_over k inferInstance inferInstance

/-- `𝔸²_k ⊔ 𝔸¹_k` is locally of finite presentation over `Spec k`. -/
instance locallyOfFinitePresentation_planeLine :
    LocallyOfFinitePresentation (planeLine k ↘ Spec (.of k)) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  planeLine_over k inferInstance inferInstance

-- **Check.** The smooth locus of `𝔸²_k ⊔ 𝔸¹_k` is everything, so it is dense.
example : (planeLine k ↘ Spec (.of k)).smoothLocus = ⊤ :=
  Scheme.Hom.smoothLocus_eq_top _

/-- The image of a point of the line lies outside the smooth locus of dimension `2`. -/
theorem inr_notMem_smoothLocusOfDim_two (p : line k) :
    (coprod.inr : line k ⟶ planeLine k) p ∉ smoothLocusOfDim k (planeLine k) 2 := by
  rw [← Scheme.Hom.mem_preimage, preimage_smoothLocusOfDim_eq]
  intro hp
  have h1 : p ∈ smoothLocusOfDim k (line k) 1 := by
    rw [smoothLocusOfDim_eq_top (d := 1)]
    trivial
  exact (disjoint_smoothLocusOfDim k (line k) (by norm_num : 2 ≠ 1)).le_bot ⟨hp, h1⟩

-- **Check.** The smooth locus of dimension `2` of `𝔸²_k ⊔ 𝔸¹_k` is not its smooth locus.
example : smoothLocusOfDim k (planeLine k) 2 ≠ (planeLine k ↘ Spec (.of k)).smoothLocus := by
  intro h
  obtain ⟨p⟩ : Nonempty (line k) := inferInstance
  refine inr_notMem_smoothLocusOfDim_two k p ?_
  rw [h, Scheme.Hom.smoothLocus_eq_top]
  trivial

end

end TauCeti.SmoothLocusOfDimCoprodExample
