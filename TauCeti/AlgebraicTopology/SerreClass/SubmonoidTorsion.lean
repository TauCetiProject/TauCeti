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

/-- An additive homomorphism sends an `S`-torsion element to an `S`-torsion element. -/
private lemma map_mem_torsion' {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (S : Submonoid ℤ) (f : M →+ N) {x : M} (hx : x ∈ Submodule.torsion' ℤ M S) :
    f x ∈ Submodule.torsion' ℤ N S :=
  let ⟨s, hs⟩ := hx
  ⟨s, by rw [Submonoid.smul_def, ← map_zsmul]; exact (congrArg f hs).trans (map_zero f)⟩

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
    exact map_mem_torsion' S f.hom (@hM x)
  prop_X₂_of_shortExact {C} hC h₁ h₃ x₂ := by
    obtain ⟨s₃, hs₃⟩ := @h₃ (C.g x₂)
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff C).1 hC.exact (s₃ • x₂)
      (by rw [Submonoid.smul_def, map_zsmul]; exact hs₃)
    obtain ⟨s₁, hs₁⟩ := map_mem_torsion' S C.f.hom (@h₁ x₁)
    exact ⟨s₁ * s₃, by rw [mul_smul, ← hx₁, hs₁]⟩

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
  exact isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨s, fun h ↦ h0 (h ▸ hs), hsx⟩

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
  | of j a => exact map_mem_torsion' S (DirectSum.of (fun j ↦ F.obj ⟨j⟩) j) (@hF ⟨j⟩ a)
  | add _ _ hx hy => exact add_mem hx hy

end AddCommGrpCat
