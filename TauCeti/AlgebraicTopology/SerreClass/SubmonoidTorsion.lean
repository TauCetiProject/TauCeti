/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SerreClass.Torsion
import TauCeti.Algebra.Module.Torsion.Finite

/-!
# The Serre class of `S`-torsion abelian groups

For any submonoid `S` of `ℤ`, the abelian groups in which every element is annihilated by some
element of `S` (`Module.IsTorsion' M S`) form a Serre class `AddCommGrpCat.isSubmonoidTorsion S`.
Equivalently, by `Submonoid.isTorsion'_iff_subsingleton_tensorProduct`, it is the class of abelian
groups `G` whose localization `A ⊗[ℤ] G` at `S` vanishes.

Special cases include:

* `S = nonZeroDivisors ℤ`: `isSubmonoidTorsion (nonZeroDivisors ℤ) = isTorsion`, the Serre class
  of all torsion abelian groups.
* `S = Submonoid.powers (d : ℤ)`: the class of abelian groups in which every element is killed by
  some power of `d`. It contains the uniform power-torsion class `isKilledBySomePower d` and agrees
  with it on finitely generated abelian groups
  (`AddCommGrpCat.isSubmonoidTorsion_powers_iff_isKilledBySomePower_of_finite`).

## Main definitions

* `AddCommGrpCat.isSubmonoidTorsion S`: the `S`-torsion abelian groups, as an object property of
  `AddCommGrpCat`, with its `IsSerreClass` instance.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

universe u

open CategoryTheory Limits

namespace AddCommGrpCat

/-- The Serre class of `S`-torsion abelian groups, in which every element is annihilated by some
element of the submonoid `S` of `ℤ`. -/
def isSubmonoidTorsion (S : Submonoid ℤ) : ObjectProperty AddCommGrpCat.{u} := fun M ↦
  Module.IsTorsion' M S

/-- An abelian group belongs to `isSubmonoidTorsion S` exactly when it is `S`-torsion as a
`ℤ`-module. -/
@[simp]
lemma prop_isSubmonoidTorsion_iff (S : Submonoid ℤ) (M : AddCommGrpCat.{u}) :
    isSubmonoidTorsion S M ↔ Module.IsTorsion' M S :=
  Iff.rfl

/-- `S`-torsion abelian groups contain the zero group and are closed under subgroups, quotients,
and extensions, so they form a Serre class. -/
instance (S : Submonoid ℤ) : (isSubmonoidTorsion.{u} S).IsSerreClass where
  exists_zero := ⟨AddCommGrpCat.of PUnit, isZero_of_subsingleton _, fun _ ↦ ⟨1, rfl⟩⟩
  prop_of_mono {M N} f hf hN x := by
    obtain ⟨s, hs⟩ := @hN (f x)
    refine ⟨s, (AddCommGrpCat.mono_iff_injective f).1 hf ?_⟩
    rw [map_zero, Submonoid.smul_def, map_zsmul]
    exact hs
  prop_of_epi {M N} f hf hM y := by
    obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective f).1 hf y
    obtain ⟨s, hs⟩ := @hM x
    refine ⟨s, ?_⟩
    rw [Submonoid.smul_def, ← map_zsmul]
    exact (congrArg f.hom hs).trans (map_zero f.hom)
  prop_X₂_of_shortExact {C} hC h₁ h₃ x₂ := by
    obtain ⟨s₃, hs₃⟩ := @h₃ (C.g x₂)
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff C).1 hC.exact (s₃ • x₂)
      (by rw [Submonoid.smul_def, map_zsmul]; exact hs₃)
    obtain ⟨s₁, hs₁⟩ := @h₁ x₁
    refine ⟨s₁ * s₃, ?_⟩
    rw [mul_smul, ← hx₁, Submonoid.smul_def, ← map_zsmul]
    exact (congrArg C.f.hom hs₁).trans (map_zero C.f.hom)

/-- For the submonoid of nonzero integers, `isSubmonoidTorsion` is the class of torsion abelian
groups. -/
@[simp]
lemma isSubmonoidTorsion_nonZeroDivisors :
    isSubmonoidTorsion.{u} (nonZeroDivisors ℤ) = isTorsion := by
  ext M
  rw [prop_isSubmonoidTorsion_iff, prop_isTorsion_iff]
  exact (isAddTorsion_iff_isTorsion_int (M := M)).symm

/-- Whenever `0 ∉ S`, every `S`-torsion abelian group is a torsion group. -/
lemma isSubmonoidTorsion_le_isTorsion {S : Submonoid ℤ} (h0 : (0 : ℤ) ∉ S) :
    isSubmonoidTorsion.{u} S ≤ isTorsion := fun _ hM ↦ (prop_isTorsion_iff _).2 fun x ↦ by
  obtain ⟨⟨s, hs⟩, hsx⟩ := @hM x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨s.natAbs, Int.natAbs_pos.2 fun h ↦ h0 (h ▸ hs), ?_⟩
  rw [← natCast_zsmul]
  rcases Int.natAbs_eq s with h | h
  · exact h ▸ hsx
  · rw [← neg_eq_iff_eq_neg.2 h, neg_smul, neg_eq_zero]
    exact hsx

/-- Uniform `d`-power torsion is contained in elementwise `d`-power torsion. -/
lemma isKilledBySomePower_le_isSubmonoidTorsion (d : ℕ) :
    isKilledBySomePower.{u} d ≤ isSubmonoidTorsion (Submonoid.powers (d : ℤ)) := by
  intro M hM x
  obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d M).1 hM
  exact ⟨⟨(d : ℤ) ^ n, n, rfl⟩, hn x⟩

/-- On a finitely generated abelian group, elementwise `d`-power torsion coincides with uniform
annihilation by a single power of `d`. -/
lemma isSubmonoidTorsion_powers_iff_isKilledBySomePower_of_finite (d : ℕ) (M : AddCommGrpCat.{u})
    [Module.Finite ℤ M] :
    isSubmonoidTorsion (Submonoid.powers (d : ℤ)) M ↔ isKilledBySomePower d M := by
  refine ⟨fun hM ↦ ?_, isKilledBySomePower_le_isSubmonoidTorsion d M⟩
  obtain ⟨s, ⟨n, rfl⟩, hs⟩ := Module.IsTorsion'.exists_isTorsionBy_of_finite hM
  exact (prop_isKilledBySomePower_iff d M).2 ⟨n, fun x ↦ hs (x := x)⟩

end AddCommGrpCat
