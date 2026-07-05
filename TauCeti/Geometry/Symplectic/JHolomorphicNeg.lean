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

* `TauCeti.IsJHolomorphicAt.neg_neg`,
  `TauCeti.IsJHolomorphicWithinAt.neg_neg`,
  `TauCeti.IsJHolomorphicOn.neg_neg`, and
  `TauCeti.IsJHolomorphic.neg_neg`: the four map-level forms.
* `TauCeti.isJHolomorphicAt_neg_neg_iff` and its within-set, setwise, and global analogues:
  rewrite-friendly equivalences.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: `J`-holomorphicity is the equation `df ∘ J = J' ∘ df`.
-/

public section

namespace TauCeti

variable {V W : Type*}

section JHolomorphic

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x : V}

namespace IsJHolomorphicAt

/-- Pointwise `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_neg (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt (-J) (-J') f x :=
  ⟨hf.choose, hf.hasFDerivAt, hf.derivative_isComplexLinear.neg_neg⟩

end IsJHolomorphicAt

/-- Negating both almost complex structures leaves pointwise `J`-holomorphicity unchanged. -/
@[simp]
lemma isJHolomorphicAt_neg_neg_iff :
    IsJHolomorphicAt (-J) (-J') f x ↔ IsJHolomorphicAt J J' f x :=
  ⟨fun hf => ⟨hf.choose, hf.hasFDerivAt, hf.derivative_isComplexLinear.of_neg_neg⟩,
    fun hf => hf.neg_neg⟩

namespace IsJHolomorphicWithinAt

/-- Within-set `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_neg (hf : IsJHolomorphicWithinAt J J' f s x) :
    IsJHolomorphicWithinAt (-J) (-J') f s x :=
  ⟨hf.choose, hf.hasFDerivWithinAt, hf.derivative_isComplexLinear.neg_neg⟩

end IsJHolomorphicWithinAt

/-- Negating both almost complex structures leaves within-set `J`-holomorphicity unchanged. -/
@[simp]
lemma isJHolomorphicWithinAt_neg_neg_iff :
    IsJHolomorphicWithinAt (-J) (-J') f s x ↔ IsJHolomorphicWithinAt J J' f s x :=
  ⟨fun hf =>
    ⟨hf.choose, hf.hasFDerivWithinAt, hf.derivative_isComplexLinear.of_neg_neg⟩,
    fun hf => hf.neg_neg⟩

namespace IsJHolomorphicOn

/-- Setwise `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_neg (hf : IsJHolomorphicOn J J' f s) :
    IsJHolomorphicOn (-J) (-J') f s :=
  fun x hx => (hf x hx).neg_neg

end IsJHolomorphicOn

/-- Negating both almost complex structures leaves setwise `J`-holomorphicity unchanged. -/
@[simp]
lemma isJHolomorphicOn_neg_neg_iff :
    IsJHolomorphicOn (-J) (-J') f s ↔ IsJHolomorphicOn J J' f s :=
  ⟨fun hf x hx => (isJHolomorphicWithinAt_neg_neg_iff (x := x)).mp (hf x hx),
    fun hf => hf.neg_neg⟩

namespace IsJHolomorphic

/-- Global `J`-holomorphicity is unchanged after negating both almost complex structures. -/
lemma neg_neg (hf : IsJHolomorphic J J' f) : IsJHolomorphic (-J) (-J') f :=
  fun x => (hf x).neg_neg

end IsJHolomorphic

/-- Negating both almost complex structures leaves global `J`-holomorphicity unchanged. -/
@[simp]
lemma isJHolomorphic_neg_neg_iff :
    IsJHolomorphic (-J) (-J') f ↔ IsJHolomorphic J J' f :=
  ⟨fun hf x => (isJHolomorphicAt_neg_neg_iff (x := x)).mp (hf x),
    fun hf => hf.neg_neg⟩

end JHolomorphic

end TauCeti
