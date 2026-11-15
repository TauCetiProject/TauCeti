/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol
import TauCeti.Algebra.Module.ZMod.Dual

/-!
# The Tate dual of the roots of unity

A primitive `n`th root of unity `ζ` identifies `μₙ` with its Tate dual.  The identification sends
`x : μₙ` to the character `y ↦ (x, y)ζ`, where the coefficient pairing is the one selected by
`ζ`.  This file packages that identification as a morphism of Galois representations and proves
that it is bijective. The coefficient isomorphism `muNRepIsoTateDual` packages this
identification, and its inverse evaluates a character at the chosen primitive root.

The final theorem compares the local Tate-duality pairing transported along this morphism with the
cohomological local symbol.  It is the coefficient-level bridge needed to use nondegeneracy of the
Hilbert pairing as the `(1, 1)` base case in local Tate duality.

## Main results

* `TauCeti.ClassFieldTheory.muNRepToTateDual`: the coefficient morphism
  `μₙ → Hom(μₙ, μₙ)` defined by the chosen-root pairing.
* `TauCeti.ClassFieldTheory.bijective_muNRepToTateDual`: this coefficient morphism is bijective.
* `TauCeti.ClassFieldTheory.muNRepIsoTateDual`: the chosen-root coefficient isomorphism.
* `TauCeti.ClassFieldTheory.muNRepIsoTateDual_inv_apply`: its inverse is evaluation at `ζ`.
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

/-- The chosen-root pairing evaluates to the identity at the generator in the right variable. -/
private theorem kummerCupPairing_apply_generator (x : (muNRep n F).V) :
    (kummerCupPairing ζ hζ).bil x (muNRepGenerator ζ hζ) = x := by
  rw [kummerCupPairing_bil_comm, kummerCupPairing_bil, muNRepEquivZMod_generator, one_smul]

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
  have : Finite (muNRep n F).V := Finite.of_equiv _ (muNRepEquivZMod ζ hζ).symm.toEquiv
  refine Function.Injective.bijective_of_nat_card_le (fun x y hxy => ?_) ?_
  · have := congrArg
      (fun ψ => tateDualEquiv (muNRep n F) ψ (muNRepGenerator ζ hζ)) hxy
    simpa [kummerCupPairing_apply_generator ζ hζ] using this
  · have hM (x : (muNRep n F).V) : n • x = 0 :=
      (muNRepEquivZMod ζ hζ).injective (by simp)
    rw [Nat.card_congr (tateDualEquiv (muNRep n F)).toEquiv,
      (muNRepEquivZMod ζ hζ).natCard_addMonoidHom_zmod hM]

/-- The chosen-root identification with the Tate dual, as an isomorphism of coefficient objects. -/
def muNRepIsoTateDual : muNRep n F ≅ tateDual (muNRep n F) :=
  let e := LinearEquiv.ofBijective
    (muNRepToTateDual ζ hζ).hom.toContinuousLinearMap.toLinearMap
    (bijective_muNRepToTateDual ζ hζ)
  { hom := muNRepToTateDual ζ hζ
    inv := ConcreteCategory.ofHom
      ⟨⟨e.symm.toLinearMap, continuous_of_discreteTopology⟩,
        fun g => ContinuousLinearMap.ext fun φ => e.injective <| by
          -- The inverse intertwines because the forward coefficient map does.
          calc
            e (e.symm ((tateDual (muNRep n F)).ρ g φ)) =
                (tateDual (muNRep n F)).ρ g φ := e.apply_symm_apply _
            _ = (tateDual (muNRep n F)).ρ g (e (e.symm φ)) := by
              rw [e.apply_symm_apply]
            _ = e ((muNRep n F).ρ g (e.symm φ)) :=
              (TopRep.hom_comm_apply (muNRepToTateDual ζ hζ) g (e.symm φ)).symm⟩
    hom_inv_id := by ext x; exact e.symm_apply_apply x
    inv_hom_id := by ext φ; exact e.apply_symm_apply φ }

/-- The forward map of the chosen-root coefficient isomorphism is `muNRepToTateDual`. -/
@[simp]
theorem muNRepIsoTateDual_hom : (muNRepIsoTateDual ζ hζ).hom = muNRepToTateDual ζ hζ :=
  (rfl)

/-- The inverse chosen-root map evaluates a homomorphism at the chosen primitive root. -/
@[simp]
theorem muNRepIsoTateDual_inv_apply (φ : (tateDual (muNRep n F)).V) :
    (muNRepIsoTateDual ζ hζ).inv φ = tateDualEquiv (muNRep n F) φ
      (muNRepGenerator ζ hζ) := by
  have h := kummerCupPairing_apply_generator ζ hζ ((muNRepIsoTateDual ζ hζ).inv φ)
  rw [← tateDualEquiv_muNRepToTateDual_apply, ← muNRepIsoTateDual_hom,
    Iso.inv_hom_id_apply] at h
  exact h.symm

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
