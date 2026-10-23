/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.Topology.Algebra.ContinuousMulEquiv
import TauCeti.Topology.Connected.TotallyDisconnected

/-!
# Characters of a free pro-`p` group into `ℤ_pˣ`

A continuous character `χ : freeProP p X →ₜ* ℤ_pˣ` of a free pro-`p` group takes its values in the
principal units `1 + pℤ_p` (`TauCeti.IsProP.mem_unitsPrincipal_one`) and is determined by its
values on the generators; more precisely, two characters congruent modulo `p ^ k` on the generators
are congruent modulo `p ^ k` everywhere (`TauCeti.freeProP.pow_dvd_sub_of_forall_of`). Conversely,
every family `u : X → 1 + pℤ_p` is the family of generator values of a continuous character: the
universal property of `freeProP p X` applied to the pro-`p` group `1 + pℤ_p`, lifted to the
universe of `X`. So the continuous characters of `freeProP p X` into `ℤ_pˣ` correspond exactly to
the families `X → 1 + pℤ_p`.

## Main definitions

* `TauCeti.freeProP.characterOfUnits`: the continuous character of `freeProP p X` with prescribed
  principal-unit values on the generators.

## Main results

* `TauCeti.freeProP.characterOfUnits_of`: the character takes the prescribed values on the
  generators.
* `TauCeti.freeProP.eq_characterOfUnits`: every continuous character of a free pro-`p` group into
  `ℤ_pˣ` is the character of its values on the generators.
* `TauCeti.freeProP.pow_dvd_sub_of_forall_of`: two continuous characters congruent modulo `p ^ k`
  on the generators are congruent modulo `p ^ k` everywhere.
-/

public section

namespace TauCeti

open freeProP

universe u

variable (p : ℕ) [Fact p.Prime] (X : Type u)

/-- **The continuous character of a free pro-`p` group with prescribed principal-unit values on
the generators**: for `u : X → 1 + pℤ_p`, the character `freeProP p X → ℤ_pˣ` with `x ↦ u x` on
the generators, the universal property applied to the pro-`p` group `1 + pℤ_p`, lifted to the
universe of `X`. -/
noncomputable def freeProP.characterOfUnits (u : X → unitsPrincipal p 1) :
    freeProP p X →ₜ* ℤ_[p]ˣ :=
  ((ContinuousMonoidHom.subgroupSubtype (unitsPrincipal p 1)).comp
    ((ContinuousMulEquiv.ulift : ULift.{u} (unitsPrincipal p 1) ≃ₜ* unitsPrincipal p 1) :
      ULift.{u} (unitsPrincipal p 1) →ₜ* unitsPrincipal p 1)).comp
    (lift ((isProP_unitsPrincipal p one_pos).of_equiv ContinuousMulEquiv.ulift.symm)
      fun x ↦ ULift.up (u x))

/-- The character attached to `u` takes the value `u x` at the generator `x`. -/
@[simp]
theorem freeProP.characterOfUnits_of (u : X → unitsPrincipal p 1) (x : X) :
    characterOfUnits p X u (of x) = u x := by
  simp [characterOfUnits]

/-- Every continuous character of a free pro-`p` group is the character of its values on the
generators, which are principal units. -/
theorem freeProP.eq_characterOfUnits (χ : freeProP p X →ₜ* ℤ_[p]ˣ) :
    χ = characterOfUnits p X fun x ↦ ⟨χ (of x), (isProP_freeProP p X).mem_unitsPrincipal_one χ _⟩ :=
  hom_ext fun x ↦ by rw [characterOfUnits_of]

variable {p X} in
/-- **Two continuous characters congruent modulo `p ^ k` on the generators are congruent modulo
`p ^ k` everywhere**: their truncations modulo `p ^ k` are continuous homomorphisms to a finite
group agreeing on the generators. -/
theorem freeProP.pow_dvd_sub_of_forall_of {χ χ' : freeProP p X →ₜ* ℤ_[p]ˣ} {k : ℕ}
    (hχ : ∀ x, (p : ℤ_[p]) ^ k ∣ (χ' (of x) : ℤ_[p]) - χ (of x)) (g : freeProP p X) :
    (p : ℤ_[p]) ^ k ∣ (χ' g : ℤ_[p]) - χ g := by
  have h : (PadicInt.unitsToZModPow k).comp χ' = (PadicInt.unitsToZModPow k).comp χ :=
    hom_ext fun x ↦ Units.ext (by
      rw [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.comp_toFun,
        PadicInt.coe_unitsToZModPow_apply, PadicInt.coe_unitsToZModPow_apply, ← sub_eq_zero,
        ← map_sub, PadicInt.toZModPow_eq_zero_iff_dvd]
      exact hχ x)
  rw [← PadicInt.toZModPow_eq_zero_iff_dvd, map_sub, sub_eq_zero,
    ← PadicInt.coe_unitsToZModPow_apply, ← PadicInt.coe_unitsToZModPow_apply,
    ← ContinuousMonoidHom.comp_toFun, h, ContinuousMonoidHom.comp_toFun]

end TauCeti
