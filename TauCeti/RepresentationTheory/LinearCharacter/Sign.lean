/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Group.ZMultiples
public import TauCeti.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# The sign representation of `ℤ`

The sign representation `TauCeti.intSignRep` of `ℤ` on `ℤ` is the linear character
`n ↦ (-1)ⁿ`. Its generator acts by `-1`, so it has no nonzero invariants, and `T - 1` for the
generator `T` is multiplication by `-2`, whose range is `2ℤ`. These are the algebraic inputs for
the rank-one integral local system on the circle with monodromy `-1`.

## Main definitions

* `TauCeti.intSignRep`: the sign representation of `ℤ` on `ℤ`.

## Main results

* `TauCeti.invariants_intSignRep`: the sign representation has no nonzero invariants.
* `TauCeti.range_intSignRep_ρ_ofAdd_one_sub_id`: the range of `T - 1` is `2ℤ`.
-/

public section

namespace TauCeti

/-- The sign representation of `ℤ` on `ℤ`, in which `n` acts by `(-1)ⁿ`. Its local system
`circleLocalSystem ℤ intSignRep` is the rank-one integral system on the circle with monodromy
`-1`. -/
abbrev intSignRep : Rep ℤ (Multiplicative ℤ) :=
  Rep.of (Representation.ofLinearCharacter (zpowersHom ℤˣ (-1)))

/-- The generator of `ℤ` acts on the sign representation by `-1`. -/
@[simp]
lemma intSignRep_ρ_ofAdd_one : intSignRep.ρ (Multiplicative.ofAdd 1) = -LinearMap.id := by
  ext
  simp

/-- The sign representation of `ℤ` on `ℤ` has no nonzero invariants. -/
@[simp]
lemma invariants_intSignRep : intSignRep.ρ.invariants = ⊥ := by
  rw [Rep.FiniteCyclicGroup.invariants_eq_ker_apply_sub _ _
    Multiplicative.mem_zpowers_ofAdd_one_int, intSignRep_ρ_ofAdd_one]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq,
    Submodule.mem_bot]
  omega

/-- For the sign representation, `T - 1` is multiplication by `-2`, whose range is `2ℤ`. -/
lemma range_intSignRep_ρ_ofAdd_one_sub_id :
    LinearMap.range (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id) =
      Ideal.span {(2 : ℤ)} := by
  rw [intSignRep_ρ_ofAdd_one]
  ext x
  simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨-y, by rw [← hy]; ring⟩, fun ⟨c, hc⟩ ↦ ⟨-c, by rw [hc]; ring⟩⟩

end TauCeti
