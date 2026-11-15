/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Syntomic.StandardSyntomic
public import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# Standard smooth algebras are standard syntomic

A standard smooth algebra of relative dimension `n` is standard syntomic of relative dimension
`n`. Thus smooth local charts are also syntomic local charts, with the same dimension. This
comparison supplies the complete-intersection condition for smooth families of curves.

A submersive presentation has an injection from its relations to its variables, so its dimension
is an exact difference rather than a truncated one. Smoothness supplies flatness. After base
change to a residue field, the standard smooth dimension theorem supplies the dimension of every
nonempty fibre. No Noetherian or nontriviality assumption on the base or algebra is required.

## References

* [Stacks Project, Lemma 10.137.9, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA):
  smooth ring maps are syntomic.
* The construction uses Mathlib's `Algebra.SubmersivePresentation` and
  `Algebra.IsStandardSmoothOfRelativeDimension` by Jung Tao Cheng, Christian Merten and
  Andrew Yang, and the existing `TauCeti.ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension`.
-/

public section

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

universe u v

/-- A standard smooth algebra is standard syntomic of the same relative dimension. -/
instance of_standardSmooth (n : ℕ) (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [h : _root_.Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSyntomicOfRelativeDimension n R S := by
  have : _root_.Algebra.IsStandardSmooth R S :=
    _root_.Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨ι, σ, _, _, P, hP⟩ := h.out
  have hcard := P.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  refine P.toPresentation.isStandardSyntomicOfRelativeDimension ?_ fun p _ _ ↦ ?_
  · simp only [_root_.Algebra.Presentation.dimension] at hP
    omega
  · exact ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension p.ResidueField n

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension
