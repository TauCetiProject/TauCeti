/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SerreClass.PowerTorsion

/-!
# The Serre class of torsion abelian groups

The torsion abelian groups, those in which every element has finite order, form a Serre class:
the class contains the zero group and is closed under subgroups, quotients and extensions.
Equivalently, by `TauCeti.isAddTorsion_iff_subsingleton_rat_tensorProduct`, it is the class of
abelian groups `G` with `ℚ ⊗ G = 0`. It is the class of the rational form of Serre's Hurewicz
theorem modulo a class of abelian groups.

For every nonzero natural number `d`, the class `isKilledBySomePower d` of groups annihilated by
some power of `d` is contained in the torsion class (`isKilledBySomePower_le_isTorsion`).

## Main definitions

* `AddCommGrpCat.isTorsion`: the torsion abelian groups, as an object property of
  `AddCommGrpCat`, with its `IsSerreClass` instance.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

universe u

open CategoryTheory Limits

namespace AddCommGrpCat

/-- The Serre class of torsion abelian groups, in which every element has finite order. -/
def isTorsion : ObjectProperty AddCommGrpCat.{u} := fun M ↦ IsAddTorsion M

/-- An abelian group belongs to `isTorsion` exactly when it is a torsion group. -/
@[simp]
lemma prop_isTorsion_iff (M : AddCommGrpCat.{u}) : isTorsion M ↔ IsAddTorsion M := Iff.rfl

/-- Torsion abelian groups contain the zero group and are closed under subgroups, quotients and
extensions, so they form a Serre class. -/
instance : isTorsion.{u}.IsSerreClass where
  exists_zero := ⟨AddCommGrpCat.of PUnit, isZero_of_subsingleton _, isAddTorsion_of_finite⟩
  prop_of_mono {M N} f hf hN := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    exact fun x ↦ (hf.isOfFinAddOrder_iff (f := f.hom)).1 (hN (f x))
  prop_of_epi {M N} f hf hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    exact IsAddTorsion.of_surjective (f := f.hom) hf hM
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    refine IsAddTorsion.extension_closed (f := S.g.hom) rfl h₃ fun x ↦ ?_
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact x (AddMonoidHom.mem_ker.1 x.2)
    exact AddSubmonoid.isOfFinAddOrder_coe.1 (hx₁ ▸ S.f.hom.isOfFinAddOrder (h₁ x₁))

/-- A group annihilated by some power of a nonzero natural number `d` is a torsion group. -/
lemma isKilledBySomePower_le_isTorsion {d : ℕ} (hd : d ≠ 0) :
    isKilledBySomePower.{u} d ≤ isTorsion := fun M hM x ↦ by
  obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d M).1 hM
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨d ^ n, pow_pos (Nat.pos_of_ne_zero hd) n, by rw [← natCast_zsmul, Nat.cast_pow, hn]⟩

end AddCommGrpCat
