/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem

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
  (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
  [Finite M]

/-- Tate's local Euler characteristic formula for a finite discrete module killed by `n`,
read in the explicit cohomology of the separable-closure Galois group. -/
theorem natCard_H1_eq_mul (hM : ∀ x : M, n • x = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p (Nat.card M)) := by
  let : Module (ZMod n) M := AddCommGroup.zmodModule hM
  let : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  let B := ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup K) M
  let A : GalRep n K := TopRep.res
    (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →ₜ* AbsoluteGaloisGroup K) B
  have hAdisc : DiscreteTopology A.V := inferInstanceAs (DiscreteTopology M)
  have : Finite A.V := inferInstanceAs (Finite M)
  have : Fact (IsSmoothDiscrete (ZMod n) A) :=
    ⟨(ofDiscreteModule_isSmoothDiscrete (ZMod n) (AbsoluteGaloisGroup K) M).res
      (absoluteGaloisGroupRestrictEquiv K).continuous_toFun⟩
  let := TopRep.distribMulAction A
  have : ContinuousSMul (Field.absoluteGaloisGroup K) A.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) A).continuousSMul
  have h := eulerCharacteristic_mixed p K n (NeZero.ne _) A inferInstance
  -- Transport the Galois group by restriction from the algebraic to the separable closure,
  -- then use the scalar-independent comparisons with continuous cohomology.
  let e₁ := explicitMap1Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K) A.V
    (absoluteGaloisGroupRestrictEquiv K) (AddEquiv.refl _) continuous_id continuous_id
    (fun _ _ ↦ rfl)
  let e₂ := explicitMap2Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K) A.V
    (absoluteGaloisGroupRestrictEquiv K) (AddEquiv.refl _) continuous_id continuous_id
    (fun _ _ ↦ rfl)
  have h₁ : Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (continuousCohomology 1 A) :=
    Nat.card_congr (e₁.trans (@TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete
      (Field.absoluteGaloisGroup K) _ _ _ (ZMod n) _ _ A hAdisc inferInstance)).toEquiv
  have h₂ : Nat.card (H2 (AbsoluteGaloisGroup K) M) =
      Nat.card (continuousCohomology 2 A) :=
    Nat.card_congr (e₂.trans (@TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete
      (Field.absoluteGaloisGroup K) _ _ _ (ZMod n) _ _ A hAdisc
      inferInstance inferInstance)).toEquiv
  let e₀ := Equiv.ofBijective _ (explicitMap0_bijective (AbsoluteGaloisGroup K) M (N := A.V)
    (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →* _)
    (absoluteGaloisGroupRestrictEquiv K).surjective (AddMonoidHom.id M)
    Function.bijective_id (fun _ _ ↦ rfl))
  let c₀ := (@explicitH0IsoContinuousCohomology
    (Field.absoluteGaloisGroup K) _ _ _ A.V _ _ _ hAdisc _).toContinuousLinearEquiv
  let d₀ := @ofDiscreteModuleRestrictScalarsIntEquiv (ZMod n) _ _
    (Field.absoluteGaloisGroup K) _ _ _ A hAdisc 0
  have h₀ := Nat.card_congr (e₀.trans (c₀.toEquiv.trans d₀.toEquiv))
  rwa [← h₁, ← h₂, ← h₀] at h

end TauCeti.ClassFieldTheory
