/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Foelner
import TauCeti.GroupTheory.Amenable.Int

/-!
# The integers do not have property (T)

The regular representation of the integer group has almost invariant vectors, obtained from
normalized indicators of intervals, but no nonzero invariant vector. Thus the integer group
does not have property (T). The counterexample works in every universe in which the Hilbert
spaces in the definition are quantified.

The reference is Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory

namespace Subgroup

universe u

/-- The infinite cyclic group does not have property (T): its regular representation has
almost invariant unit vectors and no nonzero invariant vectors. -/
theorem not_relativePropertyT_top_multiplicative_int :
    ¬ (⊤ : Subgroup (Multiplicative ℤ)).RelativePropertyT.{u} := by
  classical
  -- Lifting the group places its regular Hilbert space in the quantified universe.
  let G := ULift.{u} (Multiplicative ℤ)
  let : MeasurableSpace G := ⊤
  let e : G ≃* Multiplicative ℤ := MulEquiv.ulift
  let ρ := (Measure.count : Measure G).leftRegular ℂ ℂ 2
  have hF : TauCeti.HasFoelnerSets G :=
    e.hasFoelnerSets_iff.mpr TauCeti.hasFoelnerSets_multiplicative_int
  intro hT
  rw [relativePropertyT_def] at hT
  obtain ⟨v, hv, hfixed⟩ := hT (Lp ℂ 2 (Measure.count : Measure G))
    (ρ.restrict e.symm.toMonoidHom) (Measure.isUnitary_leftRegular Measure.count |>.restrict _)
    ((Measure.hasAlmostInvariantVectors_count_leftRegular hF).restrict _)
  have hmem : v ∈ ρ.invariants := by
    intro g
    simpa using hfixed ⟨e g, mem_top _⟩
  have hinv : ρ.invariants = ⊥ := Measure.invariants_count_leftRegular (by simp)
  exact hv (by simpa [hinv] using hmem)

end Subgroup
