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

/-- The chosen-root pairing, curried as an additive map into additive maps. -/
private def kummerCupPairingAddHom :
    (muNRep n F).V →+ ((muNRep n F).V →+ (muNRep n F).V) where
  toFun x := ((kummerCupPairing ζ hζ).bil x).toAddMonoidHom
  map_zero' := by
    ext y
    change (kummerCupPairing ζ hζ).bil 0 y = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' x y := by
    ext z
    change (kummerCupPairing ζ hζ).bil (x + y) z =
      (kummerCupPairing ζ hζ).bil x z + (kummerCupPairing ζ hζ).bil y z
    rw [map_add, LinearMap.add_apply]

/-- **The chosen-root identification `μₙ → Hom(μₙ, μₙ)`**.  It sends `x` to the character
`y ↦ kummerCupPairing ζ hζ x y`, viewed as an element of the named Tate dual. -/
def muNRepToTateDual : muNRep n F ⟶ tateDual (muNRep n F) :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨AddMonoidHom.toZModLinearMap n
            ((tateDualEquiv (muNRep n F)).symm.toAddMonoidHom.comp
              (kummerCupPairingAddHom ζ hζ)),
          continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext x
        simp only [ContinuousLinearMap.comp_apply]
        apply (tateDualEquiv (muNRep n F)).injective
        ext y
        change tateDualEquiv (muNRep n F)
            ((tateDualEquiv (muNRep n F)).symm
              ((kummerCupPairing ζ hζ).bil ((muNRep n F).ρ g x)).toAddMonoidHom) y =
          tateDualEquiv (muNRep n F)
            ((tateDual (muNRep n F)).ρ g
              ((tateDualEquiv (muNRep n F)).symm
                ((kummerCupPairing ζ hζ).bil x).toAddMonoidHom)) y
        rw [tateDualEquiv_ρ_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        rw [muNRep_ρ_apply_eq_self hζ, muNRep_ρ_apply_eq_self hζ,
          muNRep_ρ_apply_eq_self hζ] }

/-- `muNRepToTateDual` is the character furnished by the chosen-root pairing. -/
@[simp]
theorem tateDualEquiv_muNRepToTateDual_apply (x y : (muNRep n F).V) :
    tateDualEquiv (muNRep n F) ((muNRepToTateDual ζ hζ).hom x) y =
      (kummerCupPairing ζ hζ).bil x y := by
  change tateDualEquiv (muNRep n F)
      ((tateDualEquiv (muNRep n F)).symm
        ((kummerCupPairing ζ hζ).bil x).toAddMonoidHom) y = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- **The chosen-root identification of `μₙ` with its Tate dual is bijective.** -/
theorem bijective_muNRepToTateDual : Function.Bijective (muNRepToTateDual ζ hζ).hom := by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · have := congrArg
      (fun ψ => tateDualEquiv (muNRep n F) ψ (muNRepGenerator ζ hζ)) hxy
    simpa [kummerCupPairing_apply_generator ζ hζ] using this
  · refine ⟨tateDualEquiv (muNRep n F) φ (muNRepGenerator ζ hζ), ?_⟩
    apply (tateDualEquiv (muNRep n F)).injective
    ext x
    rw [tateDualEquiv_muNRepToTateDual_apply]
    let i := (muNRepZModEquiv ζ hζ x).val
    have hx : x = i • muNRepGenerator ζ hζ := eq_nsmul_muNRepGenerator ζ hζ x
    calc
      (kummerCupPairing ζ hζ).bil
          (tateDualEquiv (muNRep n F) φ (muNRepGenerator ζ hζ)) x =
        (kummerCupPairing ζ hζ).bil
          (tateDualEquiv (muNRep n F) φ (muNRepGenerator ζ hζ))
            (i • muNRepGenerator ζ hζ) := congrArg _ hx
      _ = i • (kummerCupPairing ζ hζ).bil
          (tateDualEquiv (muNRep n F) φ (muNRepGenerator ζ hζ))
            (muNRepGenerator ζ hζ) := by rw [map_nsmul]
      _ = i • tateDualEquiv (muNRep n F) φ (muNRepGenerator ζ hζ) := by
        rw [kummerCupPairing_apply_generator]
      _ = tateDualEquiv (muNRep n F) φ (i • muNRepGenerator ζ hζ) := by
        rw [map_nsmul]
      _ = tateDualEquiv (muNRep n F) φ x := congrArg _ hx.symm

/-- **The `(1, 1)` Tate pairing on `μₙ`, transported through the chosen-root identification, is
the local symbol.** -/
theorem tateDualityPairing_muNRepToTateDual
    (tr : _root_.continuousCohomology 2 (muNRep n F) ≃+ ZMod n)
    (x y : _root_.continuousCohomology 1 (muNRep n F)) :
    tateDualityPairing (muNRep n F) tr 1 1 rfl
        ((ContinuousCohomology.coeffMap (muNRepToTateDual ζ hζ) 1).hom x) y =
      localSymbol (kummerCupPairing ζ hζ) tr x y := by
  have hcup := (kummerCupPairing ζ hζ).cup_coeffMap
    (tateEvaluationPairing (muNRep n F)) (muNRepToTateDual ζ hζ) (𝟙 _) (𝟙 _)
    (fun a b => by
      rw [TopRep.id_apply, TopRep.id_apply, tateEvaluationPairing_bil,
        tateDualEquiv_muNRepToTateDual_apply]) 1 1 x y
  have hcup' :
      (kummerCupPairing ζ hζ).cup 1 1 x y =
        (tateEvaluationPairing (muNRep n F)).cup 1 1
          ((ContinuousCohomology.coeffMap (muNRepToTateDual ζ hζ) 1).hom x) y := by
    simpa only [ContinuousCohomology.coeffMap_id, CategoryTheory.id_apply] using hcup
  rw [tateDualityPairing_def, localSymbol_apply]
  exact congrArg tr hcup'.symm

end ChosenRoot

end TauCeti.ClassFieldTheory
