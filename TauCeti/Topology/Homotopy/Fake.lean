/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible

/-!
# Fake spaces

A space `X` is a **fake** `M` when it is homotopy equivalent to `M` but not homeomorphic to it.
This is the sense of the classical names of four-dimensional topology: Freedman's fake complex
projective plane `∗ℂℙ²` (the Chern manifold) is a closed topological `4`-manifold homotopy
equivalent to `ℂℙ²` and not homeomorphic to it, and Ruberman's fake real projective space `∗ℝℙ⁴`
is a closed topological `4`-manifold homotopy equivalent to `ℝℙ⁴` and not homeomorphic to it.
Statements about such manifolds quantify over the spaces with `TauCeti.IsFake M X`, together with
whatever manifold hypotheses they need on `X`.

Being a fake `M` only depends on `X` and `M` up to homeomorphism
(`Homeomorph.isFake_congr_left`, `Homeomorph.isFake_congr_right`), no space is a fake copy of itself
(`TauCeti.not_isFake_self`), and the predicate is not empty: the real line is a fake point
(`TauCeti.isFake_punit_real`), since it is contractible.

## Main definitions

* `TauCeti.IsFake M X`: `X` is homotopy equivalent but not homeomorphic to `M`.

## Main results

* `Homeomorph.isFake_congr_left`, `Homeomorph.isFake_congr_right`: invariance under
  homeomorphisms.
* `TauCeti.IsFake.not_homeomorph`: a fake `M` is not homeomorphic to `M`.
* `TauCeti.not_isFake_self`: no space is a fake copy of itself.
* `TauCeti.isFake_punit_real`: the real line is a fake point.

## References

* M. Freedman, F. Quinn, *Topology of 4-Manifolds*, Princeton University Press (1990),
  Section 10.4, for the fake projective plane `∗ℂℙ²`.
* D. Ruberman, *Invariant knots of free involutions of `S⁴`*, Topology Appl. 18 (1984), 217–224,
  for the fake real projective space `∗ℝℙ⁴`.
-/

public section

open ContinuousMap

namespace TauCeti

universe u v

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]

variable (M X) in
/-- A space `X` is a **fake** `M` if it is homotopy equivalent to `M` but not homeomorphic to it.
For example Freedman's fake projective plane `∗ℂℙ²` is a fake `ℂℙ²`. -/
def IsFake : Prop :=
  Nonempty (X ≃ₕ M) ∧ ¬ Nonempty (X ≃ₜ M)

/-- The definition of `TauCeti.IsFake`, restated. -/
theorem isFake_iff : IsFake M X ↔ Nonempty (X ≃ₕ M) ∧ ¬ Nonempty (X ≃ₜ M) :=
  Iff.rfl

namespace IsFake

/-- A fake `M` is homotopy equivalent to `M`. -/
theorem nonempty_homotopyEquiv (h : IsFake M X) : Nonempty (X ≃ₕ M) :=
  h.1

/-- A fake `M` is not homeomorphic to `M`. -/
theorem not_homeomorph (h : IsFake M X) (e : X ≃ₜ M) : False :=
  h.2 ⟨e⟩

end IsFake

/-- No space is a fake copy of itself. -/
@[simp]
theorem not_isFake_self : ¬ IsFake M M :=
  fun h => h.not_homeomorph (Homeomorph.refl M)

/-- The real line is a **fake point**: it is contractible, so homotopy equivalent to a point,
but it has more than one point. -/
theorem isFake_punit_real : IsFake PUnit.{u + 1} ℝ := by
  obtain ⟨f⟩ := ContractibleSpace.hequiv_unit ℝ
  refine ⟨⟨f.trans (Homeomorph.homeomorphOfUnique Unit PUnit).toHomotopyEquiv⟩, fun ⟨e⟩ => ?_⟩
  exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))

end TauCeti

namespace Homeomorph

open TauCeti

variable {M : Type*} {M' : Type*} {X : Type*} {X' : Type*} [TopologicalSpace M]
  [TopologicalSpace M'] [TopologicalSpace X] [TopologicalSpace X']

/-- Being a fake `M` only depends on `M` up to homeomorphism. -/
theorem isFake_congr_left (e : M ≃ₜ M') : IsFake M X ↔ IsFake M' X := by
  constructor
  · rintro ⟨⟨f⟩, hf⟩
    exact ⟨⟨f.trans e.toHomotopyEquiv⟩, fun ⟨g⟩ => hf ⟨g.trans e.symm⟩⟩
  · rintro ⟨⟨f⟩, hf⟩
    exact ⟨⟨f.trans e.symm.toHomotopyEquiv⟩, fun ⟨g⟩ => hf ⟨g.trans e⟩⟩

/-- Being a fake `M` is invariant under homeomorphisms of the candidate space. -/
theorem isFake_congr_right (e : X ≃ₜ X') : IsFake M X ↔ IsFake M X' := by
  constructor
  · rintro ⟨⟨f⟩, hf⟩
    exact ⟨⟨e.symm.toHomotopyEquiv.trans f⟩, fun ⟨g⟩ => hf ⟨e.trans g⟩⟩
  · rintro ⟨⟨f⟩, hf⟩
    exact ⟨⟨e.toHomotopyEquiv.trans f⟩, fun ⟨g⟩ => hf ⟨e.symm.trans g⟩⟩

end Homeomorph
