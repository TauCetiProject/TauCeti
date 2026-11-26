/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.LensSpace.Diagram
public import TauCeti.LowDimTopology.Heegaard.Summand

/-!
# The `ε`-classes of the genus-one diagram of a lens space

For the genus-one diagram of the lens space `L(p, q)` the `p` generators lie in pairwise
different `ε`-classes (`TauCeti.HeegaardRegionSystem.EpsilonClass`), so there are exactly `p` of
them (`TauCeti.HeegaardRegionSystem.card_epsilonClass_lensSpace`), one for each spin^c structure
of `L(p, q)`, and each class contains exactly one generator.

## Main results

* `TauCeti.HeegaardRegionSystem.epsilonClass_lensSpace_injective`: distinct generators lie in
  distinct classes.
* `TauCeti.HeegaardRegionSystem.card_epsilonClass_lensSpace`: the diagram of `L(p, q)` has `p`
  classes.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

section LensSpace

variable {p : ℕ} [NeZero p] {q : (ZMod p)ˣ} {r : ZMod p}

/-- In the genus-one diagram of `L(p, q)` distinct generators lie in distinct `ε`-classes. -/
theorem epsilonClass_lensSpace_injective : Function.Injective (lensSpace p q r).epsilonClass :=
  fun _ _ h => epsilon_lensSpace_eq_zero_iff.mp (epsilonClass_eq_epsilonClass_iff.mp h)

/-- The genus-one diagram of `L(p, q)` has exactly `p` `ε`-classes, one for each of its
generators. -/
theorem card_epsilonClass_lensSpace : Nat.card (lensSpace p q r).EpsilonClass = p := by
  rw [← Nat.card_congr (Equiv.ofBijective _
      ⟨epsilonClass_lensSpace_injective, epsilonClass_surjective _⟩),
    ← Nat.card_congr (Equiv.ofBijective _ lensSpaceGenerator_bijective), Nat.card_zmod]

end LensSpace

end HeegaardRegionSystem

end TauCeti
