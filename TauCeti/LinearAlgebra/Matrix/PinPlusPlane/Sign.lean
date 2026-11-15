/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.Basic

/-!
# The sign between two `Pin⁺` lifts

Two `Pin⁺` lifts of the same orthogonal matrix differ by a unique sign. This file records that
sign as an element of `ZMod 2`: `TauCeti.pinLiftSign x x'` is `0` when `x' = x` and `1`
otherwise. If `x` and `x'` lift the same matrix, then

```text
x' = (-1) ^ (pinLiftSign x x').val • x.
```

The sign varies continuously in continuous families over a discrete coefficient field. Thus two
continuous families of lifts of the same family of orthogonal matrices differ by a unique
continuous `ZMod 2`-valued function. This is the cochain needed when a change of orthogonal frame
compares two lifts: its coboundary measures the change in their factor sets.

## Main definitions

* `TauCeti.pinLiftSign`: the mod-two sign comparing two matrices.

## Main results

* `TauCeti.IsPinLift.eq_negOnePow_pinLiftSign_smul`: two lifts of the same matrix differ by the
  sign selected by `pinLiftSign`.
* `TauCeti.continuous_pinLiftSign`: the sign between two continuous matrix-valued functions is
  continuous when the coefficient topology is discrete.
* `TauCeti.IsPinLift.existsUnique_continuous_sign`: two continuous families of lifts of the same
  family differ by a unique continuous mod-two sign.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

section Algebra

variable {R : Type*}

/-- The mod-two sign comparing two matrices: it is `0` when they agree and `1` otherwise.

For arbitrary matrices this is simply a total sign selector. Its mathematical characterization
as the unique sign relating the matrices requires that they are `Pin⁺` lifts of the same matrix;
see `TauCeti.IsPinLift.pinLiftSign_eq_iff`. -/
noncomputable def pinLiftSign (x x' : Matrix (Fin 2) (Fin 2) R) : ZMod 2 := by
  classical
  exact if x' = x then 0 else 1

/-- The sign comparing a matrix with itself is zero. -/
@[simp]
theorem pinLiftSign_self (x : Matrix (Fin 2) (Fin 2) R) : pinLiftSign x x = 0 := by
  simp [pinLiftSign]

/-- The sign selector is zero exactly when the two matrices agree. -/
@[simp]
theorem pinLiftSign_eq_zero_iff (x x' : Matrix (Fin 2) (Fin 2) R) :
    pinLiftSign x x' = 0 ↔ x' = x := by
  simp [pinLiftSign]

/-- The sign selector is one exactly when the two matrices differ. -/
@[simp]
theorem pinLiftSign_eq_one_iff (x x' : Matrix (Fin 2) (Fin 2) R) :
    pinLiftSign x x' = 1 ↔ x' ≠ x := by
  simp [pinLiftSign]

/-- Reversing the order of the two matrices does not change their mod-two sign. -/
theorem pinLiftSign_comm (x x' : Matrix (Fin 2) (Fin 2) R) :
    pinLiftSign x x' = pinLiftSign x' x := by
  by_cases h : x' = x
  · subst x'
    rfl
  · have h' : x ≠ x' := Ne.symm h
    simp [pinLiftSign, h, h']

end Algebra

section Lifts

variable {R : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)]

private theorem IsPinLift.ne_neg_self {x w : Matrix (Fin 2) (Fin 2) R}
    (hx : IsPinLift x w) : x ≠ -x := by
  intro h
  have htwo : (2 : R) • x = 0 := by
    simpa [two_smul] using eq_neg_iff_add_eq_zero.mp h
  have hx0 : x = 0 := (smul_eq_zero.mp htwo).resolve_left (NeZero.ne 2)
  have hmem : (0 : Matrix (Fin 2) (Fin 2) R) ∈ orthogonalGroup (Fin 2) R :=
    hx0 ▸ hx.mem_orthogonalGroup
  simp [mem_orthogonalGroup_iff'] at hmem

/-- **The selected sign relates two lifts of the same matrix.** -/
theorem IsPinLift.eq_negOnePow_pinLiftSign_smul {x x' w : Matrix (Fin 2) (Fin 2) R}
    (hx : IsPinLift x w) (hx' : IsPinLift x' w) :
    x' = (-1 : R) ^ (pinLiftSign x x').val • x := by
  rcases hx.eq_or_eq_neg hx' with h | h
  · simp [h]
  · have hne : x' ≠ x := by
      intro heq
      exact hx.ne_neg_self (heq.symm.trans h)
    rw [(pinLiftSign_eq_one_iff x x').2 hne, ZMod.val_one, pow_one, neg_one_smul]
    exact h

/-- **The sign between two lifts is characterized by its scalar action.** -/
theorem IsPinLift.pinLiftSign_eq_iff {x x' w : Matrix (Fin 2) (Fin 2) R}
    (hx : IsPinLift x w) (hx' : IsPinLift x' w) (ε : ZMod 2) :
    pinLiftSign x x' = ε ↔ x' = (-1 : R) ^ ε.val • x := by
  constructor
  · rintro rfl
    exact hx.eq_negOnePow_pinLiftSign_smul hx'
  · intro hε
    generalize ε = z at hε ⊢
    fin_cases z
    · apply (pinLiftSign_eq_zero_iff x x').2
      simpa [ZMod.val] using hε
    · apply (pinLiftSign_eq_one_iff x x').2
      intro heq
      rw [heq] at hε
      exact hx.ne_neg_self (by simpa [ZMod.val] using hε)

end Lifts

section Topology

variable {X R : Type*} [TopologicalSpace X] [TopologicalSpace R] [DiscreteTopology R]

/-- **The sign between continuous matrix-valued functions is continuous** when the coefficient
ring has the discrete topology. -/
theorem continuous_pinLiftSign {x x' : X → Matrix (Fin 2) (Fin 2) R}
    (hx : Continuous x) (hx' : Continuous x') :
    Continuous fun g => pinLiftSign (x g) (x' g) :=
  (continuous_of_discreteTopology
    (f := fun p : Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R => pinLiftSign p.1 p.2)).comp
    (hx.prodMk hx')

variable [CommRing R] [IsDomain R] [NeZero (2 : R)]

/-- **Two continuous families of lifts of the same family differ by a unique continuous sign.**
The sign is a `ZMod 2`-valued function `ψ` characterized by
`x' g = (-1)^(ψ g).val • x g` at every point. -/
theorem IsPinLift.existsUnique_continuous_sign {x x' w : X → Matrix (Fin 2) (Fin 2) R}
    (hxcont : Continuous x) (hx'cont : Continuous x')
    (hx : ∀ g, IsPinLift (x g) (w g)) (hx' : ∀ g, IsPinLift (x' g) (w g)) :
    ∃! ψ : X → ZMod 2,
      Continuous ψ ∧ ∀ g, x' g = (-1 : R) ^ (ψ g).val • x g := by
  refine ⟨fun g => pinLiftSign (x g) (x' g), ⟨continuous_pinLiftSign hxcont hx'cont, ?_⟩, ?_⟩
  · intro g
    exact (hx g).eq_negOnePow_pinLiftSign_smul (hx' g)
  intro ψ hψ
  funext g
  exact (((hx g).pinLiftSign_eq_iff (hx' g) (ψ g)).2 (hψ.2 g)).symm

end Topology

end TauCeti
