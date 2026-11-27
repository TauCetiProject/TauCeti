/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.TateTwist
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Cyclotomic

/-!
# Examples: Tate twists

* `M(0) = M`.
* `ℤ_ℓ(1)` is the first Tate twist of the trivial line, and twisting it once more gives
  determinant `χ_ℓ²`.
* `ℤ_ℓ(1)^∨ ≅ ℤ_ℓ(−1)`, the line of `χ_ℓ⁻¹`, and not `ℤ_ℓ(1)`: over a nonarchimedean local field
  with residue field of `q` elements and `ℓ` prime to the residue characteristic, an arithmetic
  Frobenius lift acts on `ℤ_ℓ(1)` by `q` and on `ℤ_ℓ(−1)` by `q⁻¹`, and `q² ≠ 1`.
-/

open TauCeti ContinuousRep

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type*) [Field F]

-- The zeroth Tate twist changes nothing.
example {M : Type*} [AddCommMonoid M] [Module ℤ_[ℓ] M] [TopologicalSpace M]
    [ContinuousSMul ℤ_[ℓ] M] (ρ : ContinuousRep (Field.absoluteGaloisGroup F) ℤ_[ℓ] M) :
    ρ.tateTwist ℓ 0 = ρ :=
  tateTwist_zero ρ

-- `ℤ_ℓ(1)` is the Tate twist of the trivial line.
example : (trivial (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ 1 = cyclotomicLine ℓ F :=
  tateTwist_trivial_one

-- `ℤ_ℓ(1)(1) = ℤ_ℓ(2)` has determinant `χ_ℓ²`, not `χ_ℓ`.
example : ((cyclotomicLine ℓ F).tateTwist ℓ 1).det =
    (cyclotomicPow ℓ F ℤ_[ℓ] 2 : Field.absoluteGaloisGroup F →* ℤ_[ℓ]ˣ) := by
  rw [← tateTwist_trivial_one, tateTwist_tateTwist, tateTwist_trivial, det_ofCharacter,
    one_add_one_eq_two]

-- The dual of `ℤ_ℓ(1)` is `ℤ_ℓ(−1)`, the `(−1)`-st Tate twist of the trivial line.
example [TopologicalSpace (Module.Dual ℤ_[ℓ] ℤ_[ℓ])]
    [IsModuleTopology ℤ_[ℓ] (Module.Dual ℤ_[ℓ] ℤ_[ℓ])] :
    Nonempty (Iso (cyclotomicLine ℓ F).dual
      ((trivial (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ (-1))) := by
  rw [tateTwist_trivial_neg_one, cyclotomicLine_def]
  exact ⟨dualOfCharacterIso _⟩

open ValuativeRel in
-- Over a nonarchimedean local field `K` and for `ℓ` prime to the residue characteristic, the dual
-- of `ℤ_ℓ(1)` is not `ℤ_ℓ(1)`: an arithmetic Frobenius lift acts on them by `q⁻¹` and by `q`.
example (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (hℓ : ℓ.Coprime (ringChar 𝓀[K]))
    [TopologicalSpace (Module.Dual ℤ_[ℓ] ℤ_[ℓ])]
    [IsModuleTopology ℤ_[ℓ] (Module.Dual ℤ_[ℓ] ℤ_[ℓ])] :
    IsEmpty (Iso (cyclotomicLine ℓ K).dual (cyclotomicLine ℓ K)) := by
  refine ⟨fun e => ?_⟩
  rw [cyclotomicLine_def] at e
  have h := (nonempty_iso_ofCharacter_iff _ _).1 ⟨(dualOfCharacterIso _).symm.trans e⟩
  have hu : (continuousLocalCyclotomicCharacter ℓ K (arithFrobLift K) : ℤ_[ℓ]) =
      Nat.card 𝓀[K] := by
    rw [continuousLocalCyclotomicCharacter_apply,
      (isArithFrobeniusLift_arithFrobLift K).coe_localCyclotomicCharacter ℓ hℓ]
  have h1 : continuousLocalCyclotomicCharacter ℓ K (arithFrobLift K) *
      continuousLocalCyclotomicCharacter ℓ K (arithFrobLift K) = 1 := by
    have := DFunLike.congr_fun h (arithFrobLift K)
    rw [ContinuousMonoidHom.inv_apply] at this
    nth_rw 1 [← this]
    exact inv_mul_cancel _
  have h2 : ((Nat.card 𝓀[K] * Nat.card 𝓀[K] : ℕ) : ℤ_[ℓ]) = ((1 : ℕ) : ℤ_[ℓ]) := by
    push_cast
    rw [← hu, ← Units.val_mul, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  have h4 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  nlinarith
