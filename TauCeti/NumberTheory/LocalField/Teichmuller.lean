/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Teichmuller
public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.RingTheory.Henselian.Teichmuller

/-!
# The zero-preserving Teichmüller lift of a nonarchimedean local field

For a nonarchimedean local field `K`, `TauCeti.teichmuller 𝒪[K]` is the canonical
multiplicative section `𝓀[K]ˣ →* 𝒪[K]ˣ`. This file adds its zero-preserving extension
`teichmullerLift K : 𝓀[K] →*₀ 𝒪[K]`, obtained from Mathlib's `Perfection.teichmuller₀`, and proves
that the two constructions agree on units.

## Main definitions

* `TauCeti.teichmullerLift`: the zero-preserving Teichmüller lift `𝓀[K] →*₀ 𝒪[K]`.

## Main results

* `TauCeti.residue_teichmullerLift`: the lift is a section of reduction.
* `TauCeti.eq_teichmullerLift_iff`: an element of `𝒪[K]` is `teichmullerLift K a` exactly
  when it reduces to `a` and is fixed by the `q`-th power map.
* `TauCeti.teichmullerLift_unique`: it is the unique zero-preserving multiplicative section of
  reduction.

## References

* J.-P. Serre, *Corps Locaux*, II §4.
* J. Neukirch, *Algebraic Number Theory*, II §5.
-/

public section

noncomputable section

open IsLocalRing ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- Provenance: this is the finite-residue-field specialization of Mathlib's
-- `Perfection.teichmuller₀`, using `PerfectionMap.id` to identify a perfect field with its
-- perfection.
/-- The zero-preserving **Teichmüller lift** `𝓀[K] →*₀ 𝒪[K]`. -/
def teichmullerLift : 𝓀[K] →*₀ 𝒪[K] := by
  let p := ringChar 𝓀[K]
  letI : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  letI : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  have h : Perfection 𝓀[K] p →*₀ 𝒪[K] := Perfection.teichmuller₀ p 𝓂[K]
  exact h.comp (PerfectionMap.id p 𝓀[K]).equiv.toMonoidWithZeroHom

/-- The zero-preserving Teichmüller lift is a section of reduction. -/
@[simp]
theorem residue_teichmullerLift (a : 𝓀[K]) : residue 𝒪[K] (teichmullerLift K a) = a := by
  let p := ringChar 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  let _ : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  exact (Perfection.mk_teichmuller₀ ((PerfectionMap.id p 𝓀[K]).equiv a)).trans
    (PerfectionMap.comp_equiv (PerfectionMap.id p 𝓀[K]) a)

/-- Each Teichmüller representative is fixed by the `q`-th power map. -/
theorem teichmullerLift_pow_natCard (a : 𝓀[K]) :
    teichmullerLift K a ^ Nat.card 𝓀[K] = teichmullerLift K a := by
  classical
  let _ := Fintype.ofFinite 𝓀[K]
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- The simplifier-normalized form of the Frobenius equation for the zero-preserving lift. -/
@[simp]
theorem teichmullerLift_pow_fintype_card (a : 𝓀[K]) :
    teichmullerLift K a ^ @Fintype.card 𝓀[K] (Fintype.ofFinite 𝓀[K]) = teichmullerLift K a := by
  rw [← @Nat.card_eq_fintype_card 𝓀[K] (Fintype.ofFinite 𝓀[K])]
  exact teichmullerLift_pow_natCard K a

/-- On units, the zero-preserving lift is the Henselian-local-ring Teichmüller lift. -/
@[simp]
theorem coe_teichmuller_apply (a : 𝓀[K]ˣ) :
    ((TauCeti.teichmuller 𝒪[K] a : 𝒪[K]ˣ) : 𝒪[K]) = teichmullerLift K (a : 𝓀[K]) := by
  have hsection (b : 𝓀[K]ˣ) :
      residue 𝒪[K] ((Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K]) b : 𝒪[K]ˣ) : 𝒪[K]) =
        (b : 𝓀[K]) := by
    rw [Units.coe_map, MonoidHom.coe_coe]
    exact residue_teichmullerLift K b
  have h : Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K]) a =
      TauCeti.teichmuller 𝒪[K] a :=
    congrArg (fun f : 𝓀[K]ˣ →* 𝒪[K]ˣ ↦ f a)
      (TauCeti.eq_teichmuller 𝒪[K]
        (Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K])) hsection)
  rw [← h, Units.coe_map, MonoidHom.coe_coe]

/-- An element of `𝒪[K]` is `teichmullerLift K a` exactly when it reduces to `a` and is
fixed by the `q`-th power map. -/
theorem eq_teichmullerLift_iff {a : 𝓀[K]} {x : 𝒪[K]} :
    x = teichmullerLift K a ↔ residue 𝒪[K] x = a ∧ x ^ Nat.card 𝓀[K] = x := by
  refine ⟨?_, fun ⟨hres, hpow⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨residue_teichmullerLift K a, teichmullerLift_pow_natCard K a⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [← hres, map_zero, map_zero]
  have hq : Nat.card 𝓀[K] ≠ 0 := Nat.card_pos.ne'
  have hq₁ : Nat.card 𝓀[K] - 1 ≠ 0 := Nat.sub_ne_zero_of_lt Finite.one_lt_card
  have hunit : x ^ (Nat.card 𝓀[K] - 1) = 1 :=
    mul_right_cancel₀ hx (by rw [pow_sub_one_mul hq, hpow, one_mul])
  let u := Units.ofPowEqOne x _ hunit hq₁
  have ha : a ≠ 0 := by
    rw [← hres]
    exact (residue_ne_zero_iff_isUnit x).2 u.isUnit
  have hres' : residue 𝒪[K] (u : 𝒪[K]) = (Units.mk0 a ha : 𝓀[K]ˣ) := by
    simpa [u] using hres
  have h := (TauCeti.teichmuller_eq_iff 𝒪[K]
    (x := Units.mk0 a ha) (u := u)).2 ⟨Units.pow_ofPowEqOne hunit hq₁, hres'⟩
  rw [← Units.val_mk0 ha, ← coe_teichmuller_apply, h, Units.val_ofPowEqOne]

/-- The zero-preserving Teichmüller lift is the unique multiplicative section of reduction. -/
theorem teichmullerLift_unique (f : 𝓀[K] →*₀ 𝒪[K])
    (hsection : ∀ a, residue 𝒪[K] (f a) = a) : f = teichmullerLift K := by
  have hunits : Units.map (f : 𝓀[K] →* 𝒪[K]) = TauCeti.teichmuller 𝒪[K] :=
    TauCeti.eq_teichmuller 𝒪[K] _ fun a ↦ hsection a
  ext a
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero]
  · simpa [coe_teichmuller_apply] using
      congrArg (fun g : 𝓀[K]ˣ →* 𝒪[K]ˣ ↦ ((g (Units.mk0 a ha) : 𝒪[K]ˣ) : 𝒪[K])) hunits

end TauCeti
