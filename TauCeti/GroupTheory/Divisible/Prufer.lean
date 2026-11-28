/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.GroupTheory.Divisible.Basic

/-!
# Prüfer groups in the rational circle

The Prüfer group `prufer p` is the `p`-primary subgroup of `ℚ/ℤ`. For prime `p` it is
divisible. For nonzero `p`, the canonical map `pruferTorsion p` of `ZMod p` is injective
and identifies its image with the `p`-torsion of this group. At `p = 0`, this map is zero.

## Main definitions

* `TauCeti.prufer`: the `p`-primary subgroup of the rational circle.
* `TauCeti.pruferTorsion`: the canonical cyclic map into the Prüfer group.

## Main results

* `TauCeti.isDivisible_prufer`: a Prüfer group at a prime is divisible.
* `TauCeti.pruferTorsion_injective`, `TauCeti.pruferTorsion_range`: the cyclic embedding is
  injective for nonzero `p`, with image the `p`-torsion.
-/

public section

namespace TauCeti

open AddSubgroup

/-- For prime `p`, the Prüfer `p`-group, realized inside the rational circle `ℚ/ℤ`. -/
abbrev prufer (p : ℕ) := AddCommGroup.primaryComponent (AddCircle (1 : ℚ)) p

/-- For prime `p`, the Prüfer subgroup of the rational circle is divisible. -/
theorem isDivisible_prufer (p : ℕ) [Fact p.Prime] : (prufer p).IsDivisible := by
  let : DivisibleBy (AddCircle (1 : ℚ)) ℕ :=
    AddGroup.divisibleByNatOfDivisibleByInt _
  exact AddCommGroup.isDivisible_primaryComponent p (Fact.out : p.Prime)

/-- The canonical map from `ZMod p` to the Prüfer group. For nonzero `p`, it embeds the
order-`p` cyclic group. At `p = 0`, it is the zero map. -/
def pruferTorsion (p : ℕ) : ZMod p →+ prufer p where
  toFun x := ⟨ZMod.toRatAddCircle p x, 1, by
    have hx : p • ZMod.toRatAddCircle p x = 0 := by rw [← map_nsmul]; simp
    simpa using hx⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- The cyclic embedding agrees with the rational-circle character. -/
@[simp]
theorem coe_pruferTorsion (p : ℕ) (a : ZMod p) :
    (pruferTorsion p a : AddCircle (1 : ℚ)) = ZMod.toRatAddCircle p a := by
  simp only [pruferTorsion, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- The canonical cyclic embedding in a Prüfer group is injective. -/
theorem pruferTorsion_injective (p : ℕ) [NeZero p] : Function.Injective (pruferTorsion p) :=
  fun _ _ h ↦ ZMod.toRatAddCircle_injective p (congrArg Subtype.val h)

/-- For a nonzero modulus, only zero maps to zero in the Prüfer group. -/
@[simp]
theorem pruferTorsion_eq_zero (p : ℕ) [NeZero p] {a : ZMod p} :
    pruferTorsion p a = 0 ↔ a = 0 :=
  (pruferTorsion_injective p).eq_iff' (map_zero _)

/-- The image of the canonical cyclic embedding is exactly the `p`-torsion. -/
theorem pruferTorsion_range (p : ℕ) [NeZero p] :
    (pruferTorsion p).range = (prufer p)[p] := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
    simp
  · intro hx
    obtain ⟨a, ha⟩ := ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero p
      (congrArg Subtype.val (AddSubgroup.torsionBy.nsmul_iff.mp hx))
    exact ⟨a, Subtype.ext ha⟩

end TauCeti
