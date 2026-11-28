/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import TauCeti.AlgebraicTopology.SerreClass.PowerTorsion
import TauCeti.Algebra.Module.Torsion.Finite
import TauCeti.Algebra.Module.Torsion.Int

/-!
# The Serre class of `S`-torsion abelian groups

For any submonoid `S` of `ℤ`, the abelian groups in which every element is annihilated by some
element of `S` (`Module.IsTorsion' M S`) form a Serre class `AddCommGrpCat.isSubmonoidTorsion S`.
Equivalently, by `Submonoid.isTorsion'_iff_subsingleton_tensorProduct`, it is the class of abelian
groups `G` whose localization `A ⊗[ℤ] G` at `S` vanishes.

For `S = Submonoid.powers (d : ℤ)`, this is the class of abelian groups in which every element is
killed by some power of `d`. It contains the uniform power-torsion class `isKilledBySomePower d`
and agrees with it on finitely generated abelian groups
(`AddCommGrpCat.isSubmonoidTorsion_powers_iff_isKilledBySomePower_of_finite`).

## Main definitions

* `AddCommGrpCat.isSubmonoidTorsion S`: the `S`-torsion abelian groups, as an object property of
  `AddCommGrpCat`, with its `IsSerreClass` instance.
* `AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff`: a module lies in the `S`-torsion
  class read in `ModuleCat R` exactly when its underlying group is `S`-torsion.
* `AddCommGrpCat.isClosedUnderColimitsOfShape_discrete_inverseImage_isSubmonoidTorsion`: modules
  whose underlying groups are `S`-torsion are closed under coproducts.

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
    exact f.hom.map_mem_torsion' (@hM x)
  prop_X₂_of_shortExact {C} hC h₁ h₃ x₂ := by
    obtain ⟨s₃, hs₃⟩ := @h₃ (C.g x₂)
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff C).1 hC.exact (s₃ • x₂)
      (by rw [Submonoid.smul_def, map_zsmul]; exact hs₃)
    obtain ⟨s₁, hs₁⟩ := C.f.hom.map_mem_torsion' (@h₁ x₁)
    exact ⟨s₁ * s₃, by rw [mul_smul, ← hx₁, hs₁]⟩

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

/-- A module lies in the `S`-torsion class read in `ModuleCat R` through the forgetful functor
exactly when its underlying abelian group is `S`-torsion. -/
lemma prop_inverseImage_isSubmonoidTorsion_iff (S : Submonoid ℤ) {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) :
    (isSubmonoidTorsion S).inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) M ↔
      Module.IsTorsion' M S :=
  Iff.rfl

/-- **`S`-torsion is closed under direct sums.** A coproduct in `ModuleCat R` of modules whose
underlying abelian groups are `S`-torsion is `S`-torsion: it is the direct sum, each element of
which is a finite sum of elements of the summands. -/
instance isClosedUnderColimitsOfShape_discrete_inverseImage_isSubmonoidTorsion (S : Submonoid ℤ)
    (R : Type u) [Ring R] (J : Type u) :
    ((isSubmonoidTorsion S).inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
      |>.IsClosedUnderColimitsOfShape (Discrete J) := by
  classical
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  have hc := (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor _).symm
    (ModuleCat.coproductCoconeIsColimit fun j ↦ F.obj ⟨j⟩)
  suffices h : Module.IsTorsion' (DirectSum J fun j ↦ F.obj ⟨j⟩) S from
    ObjectProperty.prop_of_iso _ ((colimit.isColimit F).coconePointUniqueUpToIso hc).symm h
  rw [Submodule.isTorsion'_iff_torsion'_eq_top (R := ℤ), eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of j a => exact (DirectSum.of (fun j ↦ F.obj ⟨j⟩) j).map_mem_torsion' (@hF ⟨j⟩ a)
  | add _ _ hx hy => exact add_mem hx hy

end AddCommGrpCat
