/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Depletion
public import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Depletion, and twists by imprimitive characters

The `d`-depletion `f - V_d U_d f` of a modular form `f` for `Γ₁(N)`
(`TauCeti/NumberTheory/ModularForms/HeckeSlash/UpperTri/Depletion.lean`) deletes the
`q`-expansion terms whose index is divisible by `d`, and lands at level `Γ₁(L)` whenever
`N * d ∣ L` and `d * d ∣ L`. These are exactly the conditions under which
`TauCeti/NumberTheory/ModularForms/Twist/Basic.lean` places the twist `f ⊗ Φ` of `f` by a function
`Φ` modulo `d` at level `Γ₁(L)`.

The twist by a Dirichlet character `ψ` uses its zero extension, so it already deletes the
coefficients at the indices sharing a prime with the modulus. Raising the modulus of `ψ` by a
prime `p` therefore deletes the multiples of `p` as well, and that is the `p`-depletion:

`f ⊗ ψ' = (f ⊗ ψ) - V_p U_p (f ⊗ ψ)`, for `ψ'` the character `ψ` read modulo `M p`.

Both sides are compared as functions on `ℍ`, since the two constructions land at their own
levels. If `ψ` is induced from a character `ψ₀` of modulus `r ∣ m`, write `m = r p₁ ⋯ pₛ` with
primes `pᵢ`. Applying the identity once for each `pᵢ`, the twist `f ⊗ ψ` is the iterated
depletion of `f ⊗ ψ₀` at `p₁, …, pₛ`. A depletion at a prime that already divides the modulus
changes nothing (`coe_depletion_twist_of_not_coprime`), and depleting twice at the same index
is depleting once (`coe_depletion_depletion`), so only the primes dividing `m` but not `r` act,
each once. The first case, `ψ₀ = 1` modulo `1`, says that the twist by the trivial character
modulo `p` is the `p`-depletion. It is not `f`: the trivial character modulo `2` has conductor
`1`, but it vanishes at the even integers.

## Main results

* `ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`,
  `CuspForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`: raising the modulus of the character
  by a prime `p` replaces the twist by its `p`-depletion.
* `ModularForm.coe_depletion_twist_of_not_coprime`, `CuspForm.coe_depletion_twist_of_not_coprime`:
  depleting at an index `d` not coprime to the modulus of the character does not change the twist.
* `ModularForm.coe_twist_one_eq_coe_depletion`, `CuspForm.coe_twist_one_eq_coe_depletion`: the
  twist by the trivial character modulo a prime `p` is the `p`-depletion.

## References

* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978), 221–243, §3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.64.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N L M d p : ℕ} {k : ℤ}

/-! ### Twists by imprimitive characters -/

/-- **Raising the modulus of the character by a prime depletes the twist.** For a Dirichlet
character `ψ` modulo `M` and a prime `p`, the twist of `f` by `ψ` read modulo `M * p` is the
`p`-depletion of the twist of `f` by `ψ`: the zero extension modulo `M * p` vanishes at the
multiples of `p` and agrees with `ψ` elsewhere. The two sides are compared as functions, each at
its own level. -/
theorem _root_.ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist [NeZero M]
    [NeZero p] {L' L'' : ℕ} [NeZero L''] (hp : p.Prime) (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) (hNL' : N * (M * p) ∣ L') (hML' : M * p * (M * p) ∣ L')
    (hLL'' : L * p ∣ L'') (hpL'' : p * p ∣ L'')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.twist (DirichletCharacter.changeLevel (dvd_mul_right M p) ψ) hNL' hML' f) =
      ⇑(ModularForm.depletion p hLL'' hpL'' (ModularForm.twist ψ hNL hML f)) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L'') (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_twist_coeff, ModularForm.qExpansion_depletion_coeff,
    ModularForm.qExpansion_twist_coeff,
    DirichletCharacter.changeLevel_mul_prime_natCast hp]
  split_ifs <;> simp

/-- **Depleting at an index not coprime to the modulus does not change the twist.** If `d` is
not coprime to `M` (for instance a divisor `d ≠ 1` of `M`), the twist of `f` by a character
modulo `M` already vanishes at the multiples of `d`, which share a factor with `M`. -/
theorem _root_.ModularForm.coe_depletion_twist_of_not_coprime [NeZero M] [NeZero d] {L' : ℕ}
    [NeZero L'] (hdM : ¬ d.Coprime M) (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.depletion d hLL' hdL' (ModularForm.twist ψ hNL hML f)) =
      ⇑(ModularForm.twist ψ hNL hML f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L) (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_depletion_coeff]
  split_ifs with hdn
  · rw [ModularForm.qExpansion_twist_coeff,
      ψ.map_nonunit (fun hu ↦ hdM (Nat.Coprime.coprime_dvd_left hdn
        ((ZMod.isUnit_iff_coprime n M).mp hu))), zero_mul]
  · rfl

/-- **The twist by the trivial character modulo a prime `p` is the `p`-depletion.** The trivial
character modulo `p` has conductor `1`, but its zero extension vanishes at the multiples of `p`,
so the twist deletes those coefficients of `f` and keeps the others. -/
theorem _root_.ModularForm.coe_twist_one_eq_coe_depletion [NeZero p] {L' : ℕ}
    [NeZero L'] (hp : p.Prime) (hNL : N * p ∣ L) (hpL : p * p ∣ L) (hNL' : N * p ∣ L')
    (hpL' : p * p ∣ L') (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.twist (1 : DirichletCharacter ℂ p) hNL hpL f) =
      ⇑(ModularForm.depletion p hNL' hpL' f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L)
    (one_mem_strictPeriods_Gamma1_map L') (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_twist_coeff, ModularForm.qExpansion_depletion_coeff,
    DirichletCharacter.one_natCast]
  split_ifs with hn hpn hpn
  · exact absurd (hn.symm.eq_one_of_dvd hpn) hp.one_lt.ne'
  · rw [one_mul]
  · rw [zero_mul]
  · exact absurd ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn))) hn

/-- **Depleting a twisted cusp form at an index not coprime to the modulus does not change
it.** The cusp-form reading of `ModularForm.coe_depletion_twist_of_not_coprime`. -/
theorem _root_.CuspForm.coe_depletion_twist_of_not_coprime [NeZero M] [NeZero d] {L' : ℕ}
    [NeZero L'] (hdM : ¬ d.Coprime M) (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hLL' hdL' (CuspForm.twist ψ hNL hML f)) =
      ⇑(CuspForm.twist ψ hNL hML f) := by
  rw [CuspForm.coe_depletion, CuspForm.coe_twist, ← ModularForm.twist_coe_cuspForm]
  exact ModularForm.coe_depletion_twist_of_not_coprime hdM ψ hNL hML hLL' hdL' _

/-- **Raising the modulus of the character by a prime depletes the twist of a cusp form.** The
cusp-form reading of `ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`. -/
theorem _root_.CuspForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist [NeZero M]
    [NeZero p] {L' L'' : ℕ} [NeZero L''] (hp : p.Prime) (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) (hNL' : N * (M * p) ∣ L') (hML' : M * p * (M * p) ∣ L')
    (hLL'' : L * p ∣ L'') (hpL'' : p * p ∣ L'')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist (DirichletCharacter.changeLevel (dvd_mul_right M p) ψ) hNL' hML' f) =
      ⇑(CuspForm.depletion p hLL'' hpL'' (CuspForm.twist ψ hNL hML f)) := by
  rw [CuspForm.coe_twist, CuspForm.coe_depletion, ← ModularForm.twist_coe_cuspForm]
  exact ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist hp ψ hNL hML hNL' hML'
    hLL'' hpL'' _

/-- **The twist of a cusp form by the trivial character modulo a prime `p` is its
`p`-depletion.** -/
theorem _root_.CuspForm.coe_twist_one_eq_coe_depletion [NeZero p] {L' : ℕ}
    [NeZero L'] (hp : p.Prime) (hNL : N * p ∣ L) (hpL : p * p ∣ L) (hNL' : N * p ∣ L')
    (hpL' : p * p ∣ L') (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist (1 : DirichletCharacter ℂ p) hNL hpL f) =
      ⇑(CuspForm.depletion p hNL' hpL' f) := by
  rw [CuspForm.coe_twist, CuspForm.coe_depletion]
  exact ModularForm.coe_twist_one_eq_coe_depletion hp hNL hpL hNL' hpL' _

end TauCeti
