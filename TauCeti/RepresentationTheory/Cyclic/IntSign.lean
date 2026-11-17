/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# The integral sign representation of `ℤ`

The integral sign representation `TauCeti.intSignRep` of the infinite cyclic group
`Multiplicative ℤ`, in which `n` acts on `ℤ` by `(-1) ^ n`. For its generator `T`, the map
`T - 𝟙` is multiplication by `-2`, so it has range `2ℤ`.

## Main definitions

* `TauCeti.intSignRep`: the integral sign representation of `ℤ`.

## Main results

* `TauCeti.intSignRep_ρ_ofAdd_one`: the generator acts by `-1`.
* `TauCeti.intSignRep_ρ_ofAdd_one_sub_id_apply`: `T - 𝟙` is multiplication by `-2`.
* `TauCeti.range_intSignRep_ρ_ofAdd_one_sub_id`: `T - 𝟙` has range `2ℤ`.
-/

public section

noncomputable section

namespace TauCeti

/-- The integral sign representation of `ℤ`, in which `n` acts on `ℤ` by `(-1) ^ n`. Its local
system on the circle is the rank-one integral system of monodromy `-1`. -/
abbrev intSignRep : Rep ℤ (Multiplicative ℤ) :=
  Rep.of ((Units.coeHom (Module.End ℤ ℤ)).comp (zpowersHom (Module.End ℤ ℤ)ˣ (-1)))

/-- In the sign representation, `n` acts by `(-1) ^ n`. -/
theorem intSignRep_ρ_apply (n : Multiplicative ℤ) :
    intSignRep.ρ n = ↑((-1 : (Module.End ℤ ℤ)ˣ) ^ n.toAdd) :=
  rfl

/-- The generator of `ℤ` acts by `-1` in the sign representation. -/
theorem intSignRep_ρ_ofAdd_one : intSignRep.ρ (Multiplicative.ofAdd 1) = -1 := by
  simp [intSignRep]

/-- In the sign representation, `T - 𝟙` acts as multiplication by `-2`. -/
theorem intSignRep_ρ_ofAdd_one_sub_id_apply (x : ℤ) :
    (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id : Module.End ℤ ℤ) x = -2 * x := by
  rw [intSignRep_ρ_ofAdd_one]
  simp
  ring

/-- In the sign representation, `T - 𝟙 = -2` has range `2ℤ`. -/
theorem range_intSignRep_ρ_ofAdd_one_sub_id :
    LinearMap.range (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id) =
      Ideal.span {2} := by
  ext x
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨y, rfl⟩ <;>
    exact ⟨-y, by rw [intSignRep_ρ_ofAdd_one_sub_id_apply]; ring⟩

end TauCeti
