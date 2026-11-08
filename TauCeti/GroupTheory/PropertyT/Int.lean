/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Foelner
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
  let e : G ≃* Multiplicative ℤ := MulEquiv.ulift
  have hF : TauCeti.HasFoelnerSets G :=
    e.hasFoelnerSets_iff.mpr TauCeti.hasFoelnerSets_multiplicative_int
  intro hT
  exact not_relativePropertyT_top_of_hasFoelnerSets hF (by
    simpa using hT.map e.symm.toMonoidHom)

end Subgroup
