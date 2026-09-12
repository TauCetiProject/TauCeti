/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Factoring a Dirichlet character through a divisor

Two facts about when a Dirichlet character `χ` mod `N` factors through a divisor of `N`, both
stated for characters valued in any `CommMonoidWithZero`, which is the generality of
`DirichletCharacter.factorsThrough_iff_ker_unitsMap` and of the conductor.

If `χ` does not factor through `d ∣ N`, then knowing a unit's reduction modulo `d` does not
determine its character value: every unit has a partner in the same fibre of `ZMod.unitsMap` on
which `χ` takes a different value. This is the form the level-lowering argument for the
conductor theorem consumes.

If the lift of `χ` to a multiple level factors through `d`, then `χ` itself factors through
`gcd (N, d)`: `changeLevel` preserves the conductor, which then divides both. This is how a
factorisation found at an auxiliary level is brought back to the level of `χ`; the arithmetic
case the descent uses is `d = L N / p` with `p ∣ N` coprime to `L`, where the gcd is `N / p`.

## Main results

* `DirichletCharacter.exists_alt_unit_in_coset_with_char_separation`: character separation within
  a fibre of the reduction map.
* `DirichletCharacter.factorsThrough_gcd_of_changeLevel_factorsThrough`: a factorisation of the
  lift to a multiple level through `d` descends to a factorisation of `χ` through `gcd (N, d)`,
  and `DirichletCharacter.factorsThrough_div_of_changeLevel_factorsThrough`: its arithmetic
  specialisation, from `L N / p` to `N / p`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`exists_alt_unit_in_coset_with_char_separation` (:656). The source reaches it through an
intermediate shift form (`exists_kernel_unit_with_char_shift`, :646) and a separate
non-factorisation witness (`exists_unit_of_not_factorsThrough`, :542); each is a one-line
consequence of the other, so only this form is ported and the extraction is done inline.

`factorsThrough_div_of_changeLevel_factorsThrough` is extracted from the same project at commit
`eb9621e7bcb0ce220ad53983ec45d987cb5b9002`, file
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean`: the
conductor step inside the proof of `miyake_4_6_8_factor_dichotomy`, which the source carries as
the private lemmas `conductor_dvd_of_factorsThrough`, `factorsThrough_of_conductor_dvd` and
`conductor_changeLevel` specialised to `L N / p`. Here those three are Mathlib's
`conductor_dvd_of_mem_conductorSet`, `mem_conductorSet_iff_conductor_dvd` and
`conductor_changeLevel`, so what is ported is the arithmetic of the descent — the conductor
divides `gcd (N, L N / p) = N / p` — stated once for characters valued in any
`CommMonoidWithZero`.
-/

public section

namespace DirichletCharacter

/-- **Character separation within a coset.** If `χ` does not factor through `d ∣ N`, then every
unit `u` has a partner `u'` with the same reduction modulo `d` but a different character value —
so the character cannot be read off the reduction alone. -/
theorem exists_alt_unit_in_coset_with_char_separation {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    [NeZero N] {d : ℕ} (hd : d ∣ N) {χ : DirichletCharacter R N}
    (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  rw [factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨v, hv_ker, hv_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  have hv_ker' : ZMod.unitsMap hd v = 1 := MonoidHom.mem_ker.mp hv_ker
  have hv_chi' : χ.toUnitHom v ≠ 1 := hv_chi ∘ MonoidHom.mem_ker.mpr
  exact ⟨u * v, by rw [map_mul, hv_ker', mul_one],
    by rw [map_mul, Ne, mul_eq_left]; exact hv_chi'⟩

/-- **A factorisation found at a multiple level descends to the gcd.** If the lift of `ψ` mod `N`
to a multiple level `M` factors through `d`, then `ψ` factors through `gcd (N, d)`:
`changeLevel` preserves the conductor, which then divides both the level `N` and `d`. -/
theorem factorsThrough_gcd_of_changeLevel_factorsThrough {R : Type*} [CommMonoidWithZero R]
    {N M d : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) {ψ : DirichletCharacter R N}
    (hfac : (changeLevel hNM ψ).FactorsThrough d) : ψ.FactorsThrough (Nat.gcd N d) := by
  have hc : ψ.conductor ∣ d := by
    have := conductor_dvd_of_mem_conductorSet _ hfac
    rwa [conductor_changeLevel] at this
  exact (mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left N d)).mpr
    (Nat.dvd_gcd ψ.conductor_dvd_level hc)

/-- **A factorisation found at an auxiliary level descends.** If the lift of `ψ` mod `N` to level
`L N` factors through `L N / p`, for `p ∣ N` coprime to `L`, then `ψ` factors through `N / p`.
This is `factorsThrough_gcd_of_changeLevel_factorsThrough` at the gcd
`gcd (N, L N / p) = gcd (p, L) · (N / p) = N / p`. -/
theorem factorsThrough_div_of_changeLevel_factorsThrough {R : Type*} [CommMonoidWithZero R]
    {N p L : ℕ} [NeZero N] [NeZero L] (hpN : p ∣ N) (hpL : Nat.Coprime p L)
    {ψ : DirichletCharacter R N}
    (hfac : (changeLevel (Nat.dvd_mul_left N L) ψ).FactorsThrough (L * N / p)) :
    ψ.FactorsThrough (N / p) := by
  have : NeZero (L * N) := ⟨mul_ne_zero (NeZero.ne L) (NeZero.ne N)⟩
  have hgcd : Nat.gcd N (L * N / p) = N / p := by
    rw [Nat.mul_div_assoc L hpN]
    calc Nat.gcd N (L * (N / p)) = Nat.gcd (p * (N / p)) (L * (N / p)) := by
          rw [Nat.mul_div_cancel' hpN]
      _ = Nat.gcd p L * (N / p) := Nat.gcd_mul_right p (N / p) L
      _ = N / p := by rw [hpL.gcd_eq_one, one_mul]
  rw [← hgcd]
  exact factorsThrough_gcd_of_changeLevel_factorsThrough _ hfac

end DirichletCharacter
