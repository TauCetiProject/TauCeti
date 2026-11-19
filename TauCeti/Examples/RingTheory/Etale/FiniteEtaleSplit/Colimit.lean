/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Category.Profinite.Basic
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Colimit

/-!
# Tests for filtered colimits of rings without nonsplit finite étale covers

Locally constant functions on a profinite set with values in a separably closed field have no
nonsplit finite étale covers. For a one-point space the function ring is the field itself, so the
condition is separable closedness; for the empty space it is the zero ring; for a two-point space
a totally split cover may have different ranks over the two points. Directed colimits of
separably closed fields have no nonsplit finite étale covers either.
-/

namespace TauCeti

/-- Locally constant functions on a profinite set with values in a separably closed field have no
nonsplit finite étale covers. -/
example (S : Profinite) (K : Type*) [Field K] [IsSepClosed K] :
    IsFiniteEtaleSplit (LocallyConstant S K) :=
  inferInstance

/-- For a one-point space, evaluation identifies the function ring with `K`, and the conclusion
agrees with `isFiniteEtaleSplit_iff_isSepClosed`. -/
example (K : Type) [Field K] : IsFiniteEtaleSplit (LocallyConstant Unit K) ↔ IsSepClosed K := by
  let e : LocallyConstant Unit K ≃+* K := RingEquiv.ofBijective (LocallyConstant.evalRingHom ())
    ⟨fun f g h ↦ LocallyConstant.ext fun _ ↦ h, fun a ↦ ⟨LocallyConstant.const Unit a, rfl⟩⟩
  rw [← isFiniteEtaleSplit_iff_isSepClosed]
  exact ⟨fun _ ↦ e.isFiniteEtaleSplit, fun _ ↦ e.symm.isFiniteEtaleSplit⟩

/-- For the empty space, the function ring is the zero ring, and it has no nonsplit finite étale
covers whatever the coefficient ring. -/
example (X : Type*) [TopologicalSpace X] [IsEmpty X] (A : Type*) [CommRing A] :
    Subsingleton (LocallyConstant X A) ∧ IsFiniteEtaleSplit (LocallyConstant X A) :=
  have : Subsingleton (LocallyConstant X A) := ⟨fun _ _ ↦ LocallyConstant.ext isEmptyElim⟩
  ⟨this, inferInstance⟩

/-- For a two-point discrete space, the function ring is `K × K`, and total splitting allows
different ranks over the two points: the quotient by the indicator function of `false` is finite
étale of rank one over `true` and of rank zero over `false`. -/
example (K : Type*) [Field K] [IsSepClosed K] :
    let e : LocallyConstant Bool K := ⟨fun b ↦ if b then 0 else 1, .of_discrete _⟩
    Algebra.IsTotallySplit (LocallyConstant Bool K)
      (LocallyConstant Bool K ⧸ Ideal.span {e}) := by
  intro e
  have he : IsIdempotentElem e := LocallyConstant.ext fun b ↦ by cases b <;> simp [e]
  have : Algebra.Etale (LocallyConstant Bool K) (LocallyConstant Bool K ⧸ Ideal.span {e}) :=
    Algebra.Etale.quotient_span_singleton he
  exact .of_isFiniteEtaleSplit _

/-- A directed colimit of separably closed fields has no nonsplit finite étale covers. -/
example {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {K : ι → Type*}
    [∀ i, Field (K i)] [∀ i, IsSepClosed (K i)] {f : ∀ i j, i ≤ j → K i →+* K j}
    [DirectedSystem K (f · · ·)] : IsFiniteEtaleSplit (Ring.DirectLimit K (f · · ·)) :=
  inferInstance

end TauCeti
