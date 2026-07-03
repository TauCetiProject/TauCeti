/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic

/-!
# Negating both almost complex structures

This file records the elementary sign-change invariance of the pointwise Cauchy--Riemann
equation used by the analytic Heegaard Floer roadmap. A real-linear map satisfies
`F ∘ J = J' ∘ F` exactly when it satisfies the same equation after both almost complex
structures are negated:

`F ∘ (-J) = (-J') ∘ F`.

The same invariance is packaged for the pointwise, within-set, setwise, and global
`J`-holomorphic predicates. These lemmas are useful bookkeeping before the local theory of
`J`-holomorphic curves starts reflecting domains or changing orientation conventions: the
analytic content stays in the Frechet derivative, while the simultaneous sign change is only
linear algebra.

## Main declarations

* `TauCeti.IsComplexLinearMap.neg_structures`: complex-linearity survives negating source and
  target almost complex structures.
* `TauCeti.isComplexLinearMap_neg_neg_iff`: the corresponding equivalence.
* `TauCeti.IsJHolomorphicAt.neg_structures`,
  `TauCeti.IsJHolomorphicWithinAt.neg_structures`,
  `TauCeti.IsJHolomorphicOn.neg_structures`, and
  `TauCeti.IsJHolomorphic.neg_structures`: the four map-level forms.
* `TauCeti.isJHolomorphicAt_neg_neg_iff` and its within-set, setwise, and global analogues:
  rewrite-friendly equivalences.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: `J`-holomorphicity is the equation `df ∘ J = J' ∘ df`.
-/

public section

namespace TauCeti

variable {V W : Type*}

section Linear

variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {F : V →ₗ[ℝ] W}

namespace IsComplexLinearMap

/-- Complex-linearity is unchanged after negating both the source and target almost complex
structures. -/
lemma neg_structures (hF : IsComplexLinearMap J J' F) : IsComplexLinearMap (-J) (-J') F := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  have hFv := (isComplexLinearMap_iff_apply J J' F).mp hF v
  simp [hFv]

/-- If a map is complex-linear after negating both structures, then it was complex-linear before
the sign change. -/
lemma of_neg_structures (hF : IsComplexLinearMap (-J) (-J') F) : IsComplexLinearMap J J' F := by
  rw [isComplexLinearMap_iff_apply] at hF ⊢
  intro v
  simpa using congrArg Neg.neg (hF v)

end IsComplexLinearMap

/-- Negating both almost complex structures leaves the complex-linearity condition unchanged. -/
lemma isComplexLinearMap_neg_neg_iff :
    IsComplexLinearMap (-J) (-J') F ↔ IsComplexLinearMap J J' F :=
  ⟨fun hF => hF.of_neg_structures, fun hF => hF.neg_structures⟩

/-- Negating both almost complex structures is an involutive change of notation for
complex-linearity. -/
lemma isComplexLinearMap_iff_neg_neg :
    IsComplexLinearMap J J' F ↔ IsComplexLinearMap (-J) (-J') F :=
  isComplexLinearMap_neg_neg_iff.symm

end Linear

section JHolomorphic

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x : V}

namespace IsJHolomorphicAt

/-- Pointwise `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_structures (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt (-J) (-J') f x :=
  ⟨hf.choose, hf.hasFDerivAt, hf.derivative_isComplexLinear.neg_structures⟩

end IsJHolomorphicAt

/-- Negating both almost complex structures leaves pointwise `J`-holomorphicity unchanged. -/
lemma isJHolomorphicAt_neg_neg_iff :
    IsJHolomorphicAt (-J) (-J') f x ↔ IsJHolomorphicAt J J' f x :=
  ⟨fun hf => ⟨hf.choose, hf.hasFDerivAt, hf.derivative_isComplexLinear.of_neg_structures⟩,
    fun hf => hf.neg_structures⟩

/-- Negating both almost complex structures is an involutive change of notation for pointwise
`J`-holomorphicity. -/
lemma isJHolomorphicAt_iff_neg_neg :
    IsJHolomorphicAt J J' f x ↔ IsJHolomorphicAt (-J) (-J') f x :=
  isJHolomorphicAt_neg_neg_iff.symm

namespace IsJHolomorphicWithinAt

/-- Within-set `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_structures (hf : IsJHolomorphicWithinAt J J' f s x) :
    IsJHolomorphicWithinAt (-J) (-J') f s x :=
  ⟨hf.choose, hf.hasFDerivWithinAt, hf.derivative_isComplexLinear.neg_structures⟩

end IsJHolomorphicWithinAt

/-- Negating both almost complex structures leaves within-set `J`-holomorphicity unchanged. -/
lemma isJHolomorphicWithinAt_neg_neg_iff :
    IsJHolomorphicWithinAt (-J) (-J') f s x ↔ IsJHolomorphicWithinAt J J' f s x :=
  ⟨fun hf =>
    ⟨hf.choose, hf.hasFDerivWithinAt, hf.derivative_isComplexLinear.of_neg_structures⟩,
    fun hf => hf.neg_structures⟩

/-- Negating both almost complex structures is an involutive change of notation for within-set
`J`-holomorphicity. -/
lemma isJHolomorphicWithinAt_iff_neg_neg :
    IsJHolomorphicWithinAt J J' f s x ↔ IsJHolomorphicWithinAt (-J) (-J') f s x :=
  isJHolomorphicWithinAt_neg_neg_iff.symm

namespace IsJHolomorphicOn

/-- Setwise `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_structures (hf : IsJHolomorphicOn J J' f s) :
    IsJHolomorphicOn (-J) (-J') f s :=
  fun x hx => (hf x hx).neg_structures

end IsJHolomorphicOn

/-- Negating both almost complex structures leaves setwise `J`-holomorphicity unchanged. -/
lemma isJHolomorphicOn_neg_neg_iff :
    IsJHolomorphicOn (-J) (-J') f s ↔ IsJHolomorphicOn J J' f s :=
  ⟨fun hf x hx => (isJHolomorphicWithinAt_neg_neg_iff (x := x)).mp (hf x hx),
    fun hf => hf.neg_structures⟩

/-- Negating both almost complex structures is an involutive change of notation for setwise
`J`-holomorphicity. -/
lemma isJHolomorphicOn_iff_neg_neg :
    IsJHolomorphicOn J J' f s ↔ IsJHolomorphicOn (-J) (-J') f s :=
  isJHolomorphicOn_neg_neg_iff.symm

namespace IsJHolomorphic

/-- Global `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_structures (hf : IsJHolomorphic J J' f) : IsJHolomorphic (-J) (-J') f :=
  fun x => (hf x).neg_structures

end IsJHolomorphic

/-- Negating both almost complex structures leaves global `J`-holomorphicity unchanged. -/
lemma isJHolomorphic_neg_neg_iff :
    IsJHolomorphic (-J) (-J') f ↔ IsJHolomorphic J J' f :=
  ⟨fun hf x => (isJHolomorphicAt_neg_neg_iff (x := x)).mp (hf x),
    fun hf => hf.neg_structures⟩

/-- Negating both almost complex structures is an involutive change of notation for global
`J`-holomorphicity. -/
lemma isJHolomorphic_iff_neg_neg :
    IsJHolomorphic J J' f ↔ IsJHolomorphic (-J) (-J') f :=
  isJHolomorphic_neg_neg_iff.symm

end JHolomorphic

end TauCeti
