/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.Algebra.CrossedProduct.TwoTorsion
public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CentralSimple.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant

/-!
# The local invariant of central simple algebras

Let `K` be a nonarchimedean local field. The local invariant
`TauCeti.ClassFieldTheory.invMap K : Br K ≃+ ℚ/ℤ` of class field theory, read on Brauer classes
of central simple algebras through `TauCeti.ClassFieldTheory.brauerGroupEquivBr K`, identifies the
Brauer group `BrauerGroup K` of central simple algebras with `ℚ/ℤ`. So for every positive `n` the
`n`-torsion of `BrauerGroup K` has exactly `n` elements, being the `n`-torsion `(1/n)ℤ/ℤ` of
`ℚ/ℤ`. In particular `Br(K)[2]` is the two-element group `(½ℤ)/ℤ`, and its nontrivial class has
invariant `1/2`.

## Main results

* `TauCeti.BrauerGroup.natCard_torsionBy`: the `n`-torsion of the Brauer group of a local field
  has `n` elements.
* `TauCeti.BrauerGroup.natCard_twoTorsion`: `Br(K)[2]` has two elements.
* `TauCeti.BrauerGroup.invMap_brauerGroupEquivBr_eq_half_iff`: a class of `Br(K)[2]` has local
  invariant `1/2` exactly when it is nontrivial.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §3.
-/

public section

noncomputable section

namespace TauCeti.BrauerGroup

open ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A Brauer class is `2`-torsion exactly when its local invariant is killed by `2`. -/
private theorem mem_twoTorsion_iff_two_nsmul_invMap (x : BrauerGroup K) :
    x ∈ twoTorsion K ↔ 2 • invMap K (brauerGroupEquivBr K (Additive.ofMul x)) = 0 := by
  rw [← map_nsmul, ← map_nsmul, AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff,
    ← ofMul_pow, ofMul_eq_zero, mem_twoTorsion]

/-- **The `n`-torsion of the Brauer group of a local field has `n` elements**, because the local
invariant identifies it with the `n`-torsion `(1/n)ℤ/ℤ` of `ℚ/ℤ`. -/
theorem natCard_torsionBy {n : ℕ} (hn : 0 < n) :
    Nat.card (AddSubgroup.torsionBy (Additive (BrauerGroup K)) (n : ℤ)) = n :=
  (Nat.card_congr
    (AddEquiv.torsionByCongr ((brauerGroupEquivBr K).trans (invMap K)) n).toEquiv).trans
      (AddCircle.natCard_torsionBy (1 : ℚ) hn)

/-- **The `2`-torsion of the Brauer group of a local field has two elements**: this is
`natCard_torsionBy` for `n = 2`. -/
theorem natCard_twoTorsion : Nat.card (twoTorsion K) = 2 := by
  rw [← natCard_torsionBy K two_pos]
  exact Nat.card_congr <| Additive.ofMul.subtypeEquiv fun x ↦ by
    rw [mem_twoTorsion, AddSubgroup.torsionBy.nsmul_iff, ← ofMul_pow, ofMul_eq_zero]

/-- **The nontrivial `2`-torsion Brauer class has local invariant `1/2`.** A class of `Br(K)[2]`
has invariant `1/2` exactly when it is nontrivial; the trivial class has invariant `0`. -/
theorem invMap_brauerGroupEquivBr_eq_half_iff {x : BrauerGroup K} (hx : x ∈ twoTorsion K) :
    invMap K (brauerGroupEquivBr K (Additive.ofMul x)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) ↔
      x ≠ 1 := by
  have half : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) ≠ 0 := by
    intro h
    have := AddCircle.addOrderOf_period_div_of_ne_zero (1 : ℚ) (n := 2) two_pos
    rw [Nat.cast_ofNat, h, addOrderOf_zero] at this
    exact absurd this (by norm_num)
  have hzero : invMap K (brauerGroupEquivBr K (Additive.ofMul x)) = 0 ↔ x = 1 := by
    rw [AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff, ofMul_eq_zero]
  have h2 : (2 : ℤ) • invMap K (brauerGroupEquivBr K (Additive.ofMul x)) = 0 := by
    rw [two_zsmul, ← two_nsmul]
    exact (mem_twoTorsion_iff_two_nsmul_invMap K x).1 hx
  rcases AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℚ) two_ne_zero h2 with h | h
  · rw [ne_eq, ← hzero, h]
    exact iff_of_false half.symm (not_not.2 rfl)
  · rw [ne_eq, ← hzero, h]
    exact iff_of_true rfl half

end TauCeti.BrauerGroup
