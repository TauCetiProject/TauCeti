/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.Data.Rat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.AlgebraicTopology.SerreClass.PowerTorsion
import Mathlib.Algebra.Category.ModuleCat.Kernels
import TauCeti.Algebra.Module.Torsion.Localization

/-!
# The Serre class of torsion abelian groups

The torsion abelian groups, those in which every element has finite order, form a Serre class:
the class contains the zero group and is closed under subgroups, quotients and extensions.
Equivalently, by `TauCeti.isAddTorsion_iff_subsingleton_rat_tensorProduct`, it is the class of
abelian groups `G` with `ℚ ⊗ G = 0`. It is the class of the rational form of Serre's Hurewicz
theorem modulo a class of abelian groups.

For every nonzero natural number `d`, the class `isKilledBySomePower d` of groups annihilated by
some power of `d` is contained in the torsion class (`isKilledBySomePower_le_isTorsion`).

Unlike the groups annihilated by some power of `d`, torsion groups are closed under arbitrary
direct sums. Read in `ModuleCat R` through the forgetful functor, they are closed under coproducts
(`AddCommGrpCat.isClosedUnderColimitsOfShape_discrete_inverseImage_isTorsion`), which is the
hypothesis on the fibres in the comparison theorem for Serre fibrations modulo a class.

A morphism of `ℤ`-modules is an isomorphism modulo torsion, its kernel and cokernel being torsion
groups, exactly when it becomes bijective after tensoring with `ℚ`
(`AddCommGrpCat.isoModSerre_inverseImage_isTorsion_iff`): base change to `ℚ` is exact and kills
exactly the torsion groups. This turns statements modulo torsion into rational isomorphisms.

## Main definitions

* `AddCommGrpCat.isTorsion`: the torsion abelian groups, as an object property of
  `AddCommGrpCat`, with its `IsSerreClass` instance.
* `AddCommGrpCat.prop_inverseImage_isTorsion_iff`: a module lies in the torsion class read in
  `ModuleCat R` exactly when its underlying group is torsion.
* `AddCommGrpCat.isClosedUnderColimitsOfShape_discrete_inverseImage_isTorsion`: modules whose
  underlying groups are torsion are closed under coproducts.
* `AddCommGrpCat.isoModSerre_inverseImage_isTorsion_iff`: the isomorphisms modulo torsion are the
  morphisms that become bijective after tensoring with `ℚ`.

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
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact x
        (AddMonoidHom.mem_ker.1 x.property)
    exact AddSubmonoid.isOfFinAddOrder_coe.1 (hx₁ ▸ S.f.hom.isOfFinAddOrder (h₁ x₁))

/-- A group annihilated by some power of a nonzero natural number `d` is a torsion group. -/
lemma isKilledBySomePower_le_isTorsion {d : ℕ} (hd : d ≠ 0) :
    isKilledBySomePower.{u} d ≤ isTorsion := fun M hM x ↦ by
  obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d M).1 hM
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨d ^ n, pow_pos (Nat.pos_of_ne_zero hd) n, by rw [← natCast_zsmul, Nat.cast_pow, hn]⟩

/-- A module lies in the torsion class read in `ModuleCat R` through the forgetful functor exactly
when its underlying abelian group is a torsion group. `simp` proves this from
`ObjectProperty.prop_inverseImage_iff` and `prop_isTorsion_iff`, so it is not a `simp` lemma; it
is the form to apply in either direction. -/
lemma prop_inverseImage_isTorsion_iff {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    isTorsion.inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) M ↔ IsAddTorsion M :=
  Iff.rfl

/-- **Torsion is closed under direct sums.** A coproduct in `ModuleCat R` of modules whose
underlying abelian groups are torsion is torsion: it is the direct sum, each element of which is a
finite sum of elements of the summands. -/
instance isClosedUnderColimitsOfShape_discrete_inverseImage_isTorsion (R : Type u) [Ring R]
    (J : Type u) :
    (isTorsion.inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
      |>.IsClosedUnderColimitsOfShape (Discrete J) := by
  classical
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  -- The colimit of `F` is the direct sum of its values.
  have hc := (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor _).symm
    (ModuleCat.coproductCoconeIsColimit fun j ↦ F.obj ⟨j⟩)
  refine ObjectProperty.prop_of_iso _ ((colimit.isColimit F).coconePointUniqueUpToIso hc).symm
    fun x ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => exact IsOfFinAddOrder.zero
  | of j a => exact (DirectSum.of (fun j ↦ F.obj ⟨j⟩) j).isOfFinAddOrder (hF ⟨j⟩ a)
  | add x y hx hy => exact hx.add hy

/-- **Isomorphisms modulo torsion are the rational isomorphisms.** A morphism `f` of `ℤ`-modules
is an isomorphism modulo the Serre class of torsion groups, its kernel and cokernel being torsion,
exactly when `ℚ ⊗ f` is bijective. -/
lemma isoModSerre_inverseImage_isTorsion_iff {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) :
    (isTorsion.inverseImage (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).isoModSerre f ↔
      Function.Bijective (f.hom.baseChange ℚ) := by
  rw [LinearMap.baseChange_bijective_iff_isTorsion, ObjectProperty.isoModSerre_iff,
    ObjectProperty.monoModSerre_iff, ObjectProperty.epiModSerre_iff,
    ObjectProperty.prop_iff_of_iso (isTorsion.inverseImage (forget₂ (ModuleCat.{u} ℤ) _))
      (ModuleCat.kernelIsoKer f),
    ObjectProperty.prop_iff_of_iso (isTorsion.inverseImage (forget₂ (ModuleCat.{u} ℤ) _))
      (ModuleCat.cokernelIsoRangeQuotient f)]
  -- The `ℤ`-module structures of `ModuleCat ℤ` agree with the canonical ones, as all do.
  refine and_congr ?_ ?_ <;>
    exact isAddTorsion_iff_isTorsion_int.trans (by congr!; exact Subsingleton.elim _ _)

end AddCommGrpCat
