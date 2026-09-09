/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The sign group as a line over `ZMod 2`

Mathlib makes the two-element group `ℤˣ = {±1}`, written additively, a module over `ZMod 2`
(`Mathlib.Data.ZMod.IntUnitsPower`). This file records that it *is* the line `ZMod 2`: the map
sending `-1` to `1` is a `ZMod 2`-linear equivalence, so in particular the dimension is `1`. This
is what lets a family of `±1`-valued characters indexed by a finite set `ι` be read as a linear
map into a `ZMod 2`-space of dimension `#ι`, and lets such a family be compared with a family of
`ZMod 2`-valued sign patterns.

## Main results

* `TauCeti.additiveIntUnitsLinearEquiv`: the linear equivalence `Additive ℤˣ ≃ₗ[ZMod 2] ZMod 2`.
* `TauCeti.finrank_zmod_two_additive_intUnits`: `Module.finrank (ZMod 2) (Additive ℤˣ) = 1`.
-/

public section

namespace TauCeti

/-- **The sign group is the line `ZMod 2`.** The additive form of `ℤˣ = {±1}` is isomorphic to
`ZMod 2`, by the map sending `1` to `0` and `-1` to `1`. This is the unique isomorphism between
the two groups, so no choice is involved. -/
def additiveIntUnitsAddEquiv : Additive ℤˣ ≃+ ZMod 2 where
  toFun u := if Additive.toMul u = 1 then 0 else 1
  invFun z := Additive.ofMul (if z = 0 then 1 else -1)
  left_inv u := by
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective u
    revert v; decide
  right_inv z := by revert z; decide
  map_add' u w := by revert u w; decide

@[simp] theorem additiveIntUnitsAddEquiv_apply (u : Additive ℤˣ) :
    additiveIntUnitsAddEquiv u = if Additive.toMul u = 1 then 0 else 1 :=
  (rfl)

/-- **The sign group is the line `ZMod 2`, linearly.** `TauCeti.additiveIntUnitsAddEquiv` is
automatically `ZMod 2`-linear, every additive map between `ZMod 2`-modules being so. -/
def additiveIntUnitsLinearEquiv : Additive ℤˣ ≃ₗ[ZMod 2] ZMod 2 :=
  additiveIntUnitsAddEquiv.toLinearEquiv fun c u =>
    _root_.ZMod.map_smul (additiveIntUnitsAddEquiv : Additive ℤˣ →+ ZMod 2) c u

@[simp] theorem additiveIntUnitsLinearEquiv_apply (u : Additive ℤˣ) :
    additiveIntUnitsLinearEquiv u = if Additive.toMul u = 1 then 0 else 1 :=
  (rfl)

/-- The sign group `Additive ℤˣ` is one-dimensional over `ZMod 2`. -/
@[simp] theorem finrank_zmod_two_additive_intUnits :
    Module.finrank (ZMod 2) (Additive ℤˣ) = 1 := by
  rw [additiveIntUnitsLinearEquiv.finrank_eq, Module.finrank_self]

/-- The sum of the coordinates of a finite family of signs, as a `ZMod 2`-linear functional. -/
noncomputable def additiveIntUnitsCoordinateSum (ι : Type*) [Fintype ι] :
    (ι → Additive ℤˣ) →ₗ[ZMod 2] Additive ℤˣ := by
  classical
  exact ∑ i : ι, LinearMap.proj i

/-- The coordinate-sum functional is the sum of the coordinates. -/
theorem additiveIntUnitsCoordinateSum_apply (ι : Type*) [Fintype ι]
    (v : ι → Additive ℤˣ) :
    additiveIntUnitsCoordinateSum ι v = ∑ i : ι, v i := by
  classical
  simp [additiveIntUnitsCoordinateSum]

/-- The hyperplane of sign vectors of coordinate sum zero has dimension one less than the number
of coordinates. -/
theorem finrank_ker_additiveIntUnitsCoordinateSum (ι : Type*) [Fintype ι] [Nonempty ι] :
    Module.finrank (ZMod 2) (LinearMap.ker (additiveIntUnitsCoordinateSum ι)) =
      Fintype.card ι - 1 := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hpi : Module.finrank (ZMod 2) (ι → Additive ℤˣ) = Fintype.card ι := by
    rw [Module.finrank_pi_fintype, finrank_zmod_two_additive_intUnits]
    simp
  have hsurj : Function.Surjective (additiveIntUnitsCoordinateSum ι) := fun w =>
    ⟨Pi.single i₀ w, by rw [additiveIntUnitsCoordinateSum_apply]; simp⟩
  have hrange :
      Module.finrank (ZMod 2) (LinearMap.range (additiveIntUnitsCoordinateSum ι)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_zmod_two_additive_intUnits]
  have hrn := LinearMap.finrank_range_add_finrank_ker (additiveIntUnitsCoordinateSum ι)
  rw [hpi, hrange] at hrn
  omega

end TauCeti
