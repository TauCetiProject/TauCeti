/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.Padics.RingHoms

import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Surjectivity of a local cyclotomic character

This file gives a criterion for the local `p`-adic cyclotomic character to be surjective: every
`p`-power cyclotomic polynomial must be irreducible over the base field. It is intended for local
Galois-theory applications where those finite-layer irreducibility results are available; see
Serre, *Local Fields*, Chapter IV, §2.
-/

public section

open Polynomial

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]

private theorem exists_localCyclotomicCharacter_toZModPow_eq
    (hirr : ∀ n : ℕ, Irreducible (cyclotomic (p ^ n) K))
    (u : ℤ_[p]ˣ) (n : ℕ) :
    ∃ σ : Field.absoluteGaloisGroup K,
      PadicInt.toZModPow n (localCyclotomicCharacter p K σ : ℤ_[p]) =
        PadicInt.toZModPow n (u : ℤ_[p]) := by
  let ζ : AlgebraicClosure K :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n) |>.choose
  have hζ : IsPrimitiveRoot ζ (p ^ n) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n) |>.choose_spec
  let L := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
  let _ : IsCyclotomicExtension {p ^ n} K L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  let c : (ZMod (p ^ n))ˣ := Units.map (PadicInt.toZModPow n).toMonoidHom u
  let τ : L ≃ₐ[K] L := (IsCyclotomicExtension.autEquivPow L (hirr n)).symm c
  let _ : IsGalois K L := IsCyclotomicExtension.isGalois (S := {p ^ n}) K L
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
  let g : Field.absoluteGaloisGroup K := σ
  refine ⟨g, ?_⟩
  have hζL : ζ ∈ L := by
    dsimp only [L]
    exact IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
  have hτζ : τ ⟨ζ, hζL⟩ = (⟨ζ, hζL⟩ : L) ^ (c : ZMod (p ^ n)).val := by
    have hζsub : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) (p ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := L.val) (by simpa using hζ) L.val.injective
    have hc : hζsub.autToPow K τ = c := by
      calc
        hζsub.autToPow K τ = modularCyclotomicCharacter L hζsub.card_rootsOfUnity τ :=
          IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ K hζsub τ
        _ = (IsCyclotomicExtension.zeta_spec (p ^ n) K L).autToPow K τ := by
          simpa only [MonoidHom.toFun_eq_coe] using
            (IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ K
              (IsCyclotomicExtension.zeta_spec (p ^ n) K L) τ).symm
        _ = (IsCyclotomicExtension.autEquivPow L (hirr n)) τ := by
          simpa only [MonoidHom.toFun_eq_coe] using
            (IsCyclotomicExtension.autEquivPow_apply L (hirr n) τ).symm
        _ = c := (IsCyclotomicExtension.autEquivPow L (hirr n)).apply_symm_apply c
    rw [← hc]
    exact (IsPrimitiveRoot.autToPow_spec K hζsub τ).symm
  have hσζ : σ ζ = ζ ^ (c : ZMod (p ^ n)).val := by
    have hcomm := AlgEquiv.restrictNormal_commutes σ L ⟨ζ, hζL⟩
    have hrestrict : σ.restrictNormal L = τ := hσ
    rw [hrestrict] at hcomm
    exact hcomm.symm.trans (congrArg Subtype.val hτζ)
  have hchar := cyclotomicCharacter.spec p g.toRingEquiv ζ hζ.pow_eq_one
  rw [localCyclotomicCharacter_apply]
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact hchar.symm.trans (hσζ.trans (by simp [c]))

/-- The local `p`-adic cyclotomic character is surjective if all `p`-power cyclotomic
polynomials are irreducible over the base field. -/
theorem localCyclotomicCharacter_surjective_of_irreducible
    (hirr : ∀ n : ℕ, Irreducible (cyclotomic (p ^ n) K)) :
    Function.Surjective (localCyclotomicCharacter p K) := by
  intro u
  let t : ℕ → Set (Field.absoluteGaloisGroup K) := fun n ↦
    {σ | PadicInt.toZModPow n (localCyclotomicCharacter p K σ : ℤ_[p]) =
      PadicInt.toZModPow n (u : ℤ_[p])}
  have htclosed (n : ℕ) : IsClosed (t n) := by
    exact isClosed_eq
      ((PadicInt.continuous_toZModPow n).comp
        (Units.continuous_val.comp (localCyclotomicCharacter_continuous p K)))
      continuous_const
  have htnonempty (n : ℕ) : (t n).Nonempty :=
    exists_localCyclotomicCharacter_toZModPow_eq hirr u n
  have htmono (n : ℕ) : t (n + 1) ⊆ t n := by
    intro σ hσ
    dsimp [t] at hσ ⊢
    rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n), hσ,
      PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n)]
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t htmono htnonempty (htclosed 0).isCompact htclosed
  refine ⟨σ, Units.ext (PadicInt.ext_of_toZModPow.mp fun n ↦ ?_)⟩
  exact Set.mem_iInter.mp hσ n

end TauCeti
