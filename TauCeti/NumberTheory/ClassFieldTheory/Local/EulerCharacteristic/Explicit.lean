/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
public import TauCeti.NumberTheory.ClassFieldTheory.GalRep.FiniteModule

/-!
# The local Euler characteristic on explicit cohomology

Tate's local Euler characteristic formula for a finite discrete Galois module, expressed
using the explicit `H⁰`, `H¹`, and `H²` of the separable-closure Galois group. This permits
coefficient modules such as isogeny kernels to use the formula without choosing scalar
structures or changing the model of the absolute Galois group.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
  [Finite M]

/-- Tate's local Euler characteristic formula for a finite discrete module,
read in the explicit cohomology of the separable-closure Galois group. -/
theorem natCard_H1_eq_mul :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p (Nat.card M)) := by
  have h := eulerCharacteristic_mixed p K (Nat.card M) Nat.card_pos.ne'
    (finiteModuleRep K M) inferInstance
  rw [← Nat.card_congr (finiteModuleRepH0Equiv K M).toEquiv,
    ← Nat.card_congr (finiteModuleRepH1Equiv K M).toEquiv,
    ← Nat.card_congr (finiteModuleRepH2Equiv K M).toEquiv,
    ← Nat.card_congr (finiteModuleEquivRep K M).toEquiv] at h
  exact h

end TauCeti.ClassFieldTheory
