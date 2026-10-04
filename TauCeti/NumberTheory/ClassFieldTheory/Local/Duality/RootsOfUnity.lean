/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# The Tate dual of the roots of unity

A primitive `n`th root of unity `ζ` identifies `μₙ` with its Tate dual.  The identification sends
`x : μₙ` to the character `y ↦ (x, y)ζ`, where the coefficient pairing is the one selected by
`ζ`.  This file packages that identification as a morphism of Galois representations and proves
that it is bijective.

The final theorem compares the local Tate-duality pairing transported along this morphism with the
cohomological local symbol.  It is the coefficient-level bridge needed to use nondegeneracy of the
Hilbert pairing as the `(1, 1)` base case in local Tate duality.

## Main results

* `TauCeti.ClassFieldTheory.muNRepToTateDual`: the coefficient morphism
  `μₙ → Hom(μₙ, μₙ)` defined by the chosen-root pairing.
* `TauCeti.ClassFieldTheory.bijective_muNRepToTateDual`: this coefficient morphism is bijective.
* `TauCeti.ClassFieldTheory.tateDualityPairing_muNRepToTateDual`: after transport along the
  coefficient morphism, the Tate pairing in bidegree `(1, 1)` is the local symbol.

The constructions follow Serre, *Galois Cohomology*, Chapter II, §5.2.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

universe u

attribute [local instance] TopRep.distribMulAction

variable {n : ℕ} {F : Type u} [Field F] [NeZero n]

section ChosenRoot

variable (ζ : F) (hζ : IsPrimitiveRoot ζ n)

/-- The identification of `μₙ` with `ZMod n` determined by `ζ`. -/
private def muNRepZModEquiv : (muNRep n F).V ≃+ ZMod n :=
  (muNRepEquivTrivialFp n F hζ).trans (trivialFpEquiv n _).toAddEquiv

/-- The element of `μₙ` corresponding to `1 : ZMod n` under the coordinate selected by `ζ`. -/
private def muNRepGenerator : (muNRep n F).V :=
  (muNRepZModEquiv ζ hζ).symm 1

/-- Every element of `μₙ` is its chosen coordinate times the generator. -/
private theorem eq_nsmul_muNRepGenerator (x : (muNRep n F).V) :
    x = (muNRepZModEquiv ζ hζ x).val • muNRepGenerator ζ hζ := by
  apply (muNRepZModEquiv ζ hζ).injective
  simp [muNRepGenerator]

/-- The chosen-root pairing evaluates to the identity at the generator in the right variable. -/
private theorem kummerCupPairing_apply_generator (x : (muNRep n F).V) :
    (kummerCupPairing ζ hζ).bil x (muNRepGenerator ζ hζ) = x := by
  let i := (muNRepZModEquiv ζ hζ x).val
  have hx : x = (muNRepEquivTrivialFp n F hζ).symm
      ((trivialFpEquiv n _).symm (i : ZMod n)) := by
    apply (muNRepZModEquiv ζ hζ).injective
    simp [muNRepZModEquiv, i]
  have hpow :=
    coe_kummerCoeffEquivMuNRep_symm_muNRepEquivTrivialFp_symm_natCast n F hζ i
  rw [← hx] at hpow
  rw [kummerCupPairing_bil_apply ζ hζ (i := (i : ℤ)) (by simpa using hpow)]
  simpa using (eq_nsmul_muNRepGenerator ζ hζ x).symm

/-- **The chosen-root identification `μₙ → Hom(μₙ, μₙ)`**.  It sends `x` to the character
`y ↦ kummerCupPairing ζ hζ x y`, viewed as an element of the named Tate dual. -/
def muNRepToTateDual : muNRep n F ⟶ tateDual (muNRep n F) :=
  pairingToTateDual (kummerCupPairing ζ hζ)

/-- `muNRepToTateDual` is the character furnished by the chosen-root pairing. -/
@[simp]
theorem tateDualEquiv_muNRepToTateDual_apply (x y : (muNRep n F).V) :
    tateDualEquiv (muNRep n F) ((muNRepToTateDual ζ hζ).hom x) y =
      (kummerCupPairing ζ hζ).bil x y := by
  rw [muNRepToTateDual, tateDualEquiv_pairingToTateDual_apply]

/-- **The chosen-root identification of `μₙ` with its Tate dual is bijective.** -/
theorem bijective_muNRepToTateDual : Function.Bijective (muNRepToTateDual ζ hζ).hom := by
  have : Finite (muNRep n F).V := Finite.of_equiv _ (muNRepZModEquiv ζ hζ).symm.toEquiv
  refine Function.Injective.bijective_of_nat_card_le (fun x y hxy => ?_) ?_
  · have := congrArg
      (fun ψ => tateDualEquiv (muNRep n F) ψ (muNRepGenerator ζ hζ)) hxy
    simpa [kummerCupPairing_apply_generator ζ hζ] using this
  · have hM (x : (muNRep n F).V) : n • x = 0 :=
      (muNRepZModEquiv ζ hζ).injective (by simp)
    rw [Nat.card_congr (tateDualEquiv (muNRep n F)).toEquiv,
      (muNRepZModEquiv ζ hζ).natCard_addMonoidHom_zmod hM]

/-- **The `(1, 1)` Tate pairing on `μₙ`, transported through the chosen-root identification, is
the local symbol.** -/
theorem tateDualityPairing_muNRepToTateDual
    (tr : _root_.continuousCohomology 2 (muNRep n F) ≃+ ZMod n)
    (x y : _root_.continuousCohomology 1 (muNRep n F)) :
    tateDualityPairing (muNRep n F) tr 1 1 rfl
        ((ContinuousCohomology.coeffMap (muNRepToTateDual ζ hζ) 1).hom x) y =
      localSymbol (kummerCupPairing ζ hζ) tr x y := by
  rw [muNRepToTateDual, tateDualityPairing_pairingToTateDual, localSymbol_apply]

end ChosenRoot

end TauCeti.ClassFieldTheory
