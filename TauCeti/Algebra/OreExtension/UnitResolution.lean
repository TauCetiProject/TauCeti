/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.OreExtension.SkewModule
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton

/-!
# Ext out of the unit module of a skew polynomial ring

Let `σ` be an endomorphism of a ring `R` and let `A = R[X; σ]` be the skew polynomial ring, the
Ore extension `TauCeti.OreExtension σ 0` with `X * a = σ a * X`. A left `A`-module is the same
thing as an `R`-module `N` with a `σ`-semilinear endomorphism `F`, through which `X` acts
(`TauCeti.OreExtension.SkewModule F`). The *unit module* is `R` itself, with `X` acting by `σ`.

The unit module has the length-one free resolution

`0 → A --(· * (X - 1))--> A --(p ↦ p • 1)--> R → 0`

by *right* multiplication by `X - 1`, which is a map of left `A`-modules. Applying `Hom_A(-, N)`
and identifying `Hom_A(A, N)` with `N` by evaluation at `1`, right multiplication by `X - 1`
becomes the action of `X - 1` on `N`. Hence for every left `A`-module `N`,

* `Ext⁰_A(R, N) = ker (X - 1) = {n | X • n = n}`,
* `Ext¹_A(R, N) = N ⧸ (X - 1) N`,
* `Extⁱ_A(R, N) = 0` for `i ≥ 2`.

For a Frobenius module, these are the two cohomology groups of the complex `N --(F - 1)--> N`
(`TauCeti.FrobeniusModuleCat.extZeroAddEquivHomology`). The orientation matters: left
multiplication by `X - 1` is not a map of left modules.

The identifications are additive equivalences. The `Ext` groups carry the `ℤ`-module structure of
the preadditive category, which is not definitionally that of an additive group, so `ℤ`-linear
statements would need a separate comparison.

## Main definitions

* `TauCeti.OreExtension.unitModuleCat σ`: the unit module `R`, with `X` acting by `σ`.
* `TauCeti.OreExtension.unitShortComplex σ`: the resolution `A → A → R` of the unit module.
* `TauCeti.OreExtension.homUnitLinearEquiv`: `Hom_A(R, N)` is the group of vectors of `N` fixed by
  `X`.
* `TauCeti.OreExtension.extZeroAddEquiv` and `TauCeti.OreExtension.extOneAddEquiv`: the
  identifications of `Ext⁰_A(R, N)` and `Ext¹_A(R, N)` with the kernel and the cokernel of the
  action of `X - 1` on `N`.

## Main results

* `TauCeti.OreExtension.unitShortComplex_shortExact`: the resolution is a short exact sequence.
* `TauCeti.OreExtension.hasProjectiveDimensionLT_unitModuleCat`: the unit module has projective
  dimension at most one.
* `TauCeti.OreExtension.subsingleton_ext_unitModuleCat`: `Extⁱ_A(R, N)` vanishes for `i ≥ 2`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.5.6.
-/

public section

noncomputable section

namespace TauCeti.OreExtension

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v

variable {k : Type u} {R : Type v} [CommSemiring k] [Ring R] [Algebra k R] (σ : R →ₐ[k] R)

/-- The *unit module* of the skew polynomial ring `R[X; σ]`: the ring `R`, with the constants
acting by left multiplication and `X` acting by `σ`. -/
abbrev unitModuleCat : ModuleCat.{v} (OreExtension σ 0) :=
  ModuleCat.of _ (SkewModule (σ : R →+* R).toSemilinearMap)

/-- `Xⁿ` fixes `1` in the unit module, since `σ 1 = 1`. -/
theorem X_pow_smul_of_one (n : ℕ) :
    (X ^ n : OreExtension σ 0) • SkewModule.of (σ : R →+* R).toSemilinearMap 1 =
      SkewModule.of (σ : R →+* R).toSemilinearMap 1 := by
  induction n with
  | zero => exact one_smul _ _
  | succ n ih =>
    rw [pow_succ, mul_smul, SkewModule.X_smul_of]
    simp [ih]

section Resolution

/-- Right multiplication by `X - 1` on the skew polynomial ring `R[X; σ]`, a map of left modules
over `R[X; σ]`. -/
def mulXSubOne : ModuleCat.of (OreExtension σ 0) (OreExtension σ 0) ⟶
    ModuleCat.of (OreExtension σ 0) (OreExtension σ 0) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (X - 1))

/-- Right multiplication by `X - 1` sends `p` to `p * (X - 1)`. -/
@[simp]
theorem mulXSubOne_apply (p : OreExtension σ 0) : (mulXSubOne σ).hom p = p * (X - 1) :=
  (rfl)

/-- The augmentation `R[X; σ] → R`, `p ↦ p • 1`, onto the unit module. It sends `∑ aₙ Xⁿ` to
`∑ aₙ`. -/
def augmentation : ModuleCat.of (OreExtension σ 0) (OreExtension σ 0) ⟶ unitModuleCat σ :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (SkewModule.of (σ : R →+* R).toSemilinearMap 1))

/-- The augmentation sends `p` to `p • 1`. -/
theorem augmentation_apply (p : OreExtension σ 0) :
    (augmentation σ).hom p = p • SkewModule.of (σ : R →+* R).toSemilinearMap 1 :=
  (rfl)

/-- The augmentation sends the monomial `a Xⁿ` to `a`. -/
@[simp]
theorem augmentation_monomial (n : ℕ) (a : R) :
    (augmentation σ).hom (monomial n a) = SkewModule.of (σ : R →+* R).toSemilinearMap a := by
  rw [← C_mul_X_pow_eq_monomial, augmentation_apply, mul_smul, X_pow_smul_of_one,
    SkewModule.C_smul_of, smul_eq_mul, mul_one]

/-- The augmentation sends the constant `a` to `a`. -/
@[simp]
theorem augmentation_C (a : R) :
    (augmentation σ).hom (C a) = SkewModule.of (σ : R →+* R).toSemilinearMap a := by
  rw [← monomial_zero_left, augmentation_monomial]

/-- The augmentation kills the left ideal generated by `X - 1`, since `X • 1 = σ 1 = 1`. -/
theorem augmentation_mulXSubOne (p : OreExtension σ 0) :
    (augmentation σ).hom ((mulXSubOne σ).hom p) = 0 := by
  rw [augmentation_apply, mulXSubOne_apply, mul_smul, sub_smul, one_smul, SkewModule.X_smul_of]
  simp

/-- Every `p ∈ R[X; σ]` is congruent to the constant `C a`, where `augmentation p = a`, modulo the
left ideal generated by `X - 1`: `C a * Xⁿ - C a = C a * (1 + X + ⋯ + Xⁿ⁻¹) * (X - 1)`. -/
theorem sub_C_mem_range_mulXSubOne (p : OreExtension σ 0) :
    p - C ((SkewModule.of (σ : R →+* R).toSemilinearMap).symm ((augmentation σ).hom p)) ∈
      LinearMap.range (mulXSubOne σ).hom := by
  induction p using induction_on with
  | zero => simp
  | add n a p _ _ ih =>
    rw [map_add, augmentation_monomial]
    simp only [map_add, AddEquiv.symm_apply_apply]
    rw [add_sub_add_comm]
    refine Submodule.add_mem _ ⟨C a * ∑ i ∈ Finset.range n, X ^ i, ?_⟩ ih
    rw [mulXSubOne_apply, mul_assoc, geom_sum_mul]
    simp [mul_sub, C_mul_X_pow_eq_monomial]

/-- Right multiplication by `X - 1` is injective: `q * X = q` forces `q = 0`. -/
theorem mulXSubOne_injective : Function.Injective (mulXSubOne σ) := by
  refine (injective_iff_map_eq_zero (mulXSubOne σ).hom).2 fun q hq ↦ ?_
  rw [mulXSubOne_apply, mul_sub, mul_one, sub_eq_zero] at hq
  -- `q * X = q` shifts the coefficients of `q` up by one, so they all vanish.
  have h (n : ℕ) : coeff q n = 0 := by
    induction n with
    | zero => rw [← hq, coeff_mul_X_zero]
    | succ n ih => rw [← hq, coeff_mul_X_succ, ih]
  exact ext fun n ↦ by rw [h, coeff_zero]

/-- The length-one resolution `0 → R[X; σ] → R[X; σ] → R → 0` of the unit module, by right
multiplication by `X - 1` followed by the augmentation. -/
abbrev unitShortComplex : ShortComplex (ModuleCat.{v} (OreExtension σ 0)) :=
  ShortComplex.mk (mulXSubOne σ) (augmentation σ)
    (ModuleCat.hom_ext (LinearMap.ext (augmentation_mulXSubOne σ)))

/-- `0 → R[X; σ] → R[X; σ] → R → 0` is exact: the unit module has the free resolution of length
one by right multiplication by `X - 1`. -/
theorem unitShortComplex_shortExact : (unitShortComplex σ).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (fun (p : OreExtension σ 0) ↦ ⟨fun hp ↦ ?_, ?_⟩)
    (mulXSubOne_injective σ)
    fun a ↦ ⟨C ((SkewModule.of (σ : R →+* R).toSemilinearMap).symm a),
      (augmentation_C σ _).trans (AddEquiv.apply_symm_apply _ a)⟩
  · simpa [hp] using sub_C_mem_range_mulXSubOne σ p
  · rintro ⟨q, rfl⟩
    exact augmentation_mulXSubOne σ q

end Resolution

section Ext

variable (N : ModuleCat.{v} (OreExtension σ 0))

/-- The unit module of `R[X; σ]` has projective dimension at most one. -/
instance hasProjectiveDimensionLT_unitModuleCat : HasProjectiveDimensionLT (unitModuleCat σ) 2 :=
  (unitShortComplex_shortExact σ).hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

/-- `Extⁱ` out of the unit module of `R[X; σ]` vanishes for `i ≥ 2`. -/
theorem subsingleton_ext_unitModuleCat (n : ℕ) :
    Subsingleton (Ext.{v} (unitModuleCat σ) N (n + 2)) :=
  HasProjectiveDimensionLT.subsingleton _ 2 (n + 2) (by omega) N

/-- The morphism from the unit module to `N` sending `1` to a vector `n` fixed by `X`. It exists
because the unit module is the cokernel of right multiplication by `X - 1`. -/
def homOfMemKer (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) :
    unitModuleCat σ ⟶ N :=
  (Cofork.IsColimit.desc' (unitShortComplex_shortExact σ).gIsCokernel
    (ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n)) <| by
      have hn : (X - 1 : OreExtension σ 0) • (n : N) = 0 := LinearMap.mem_ker.mp n.property
      have h : mulXSubOne σ ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n) = 0 := by
        rw [mulXSubOne,
          ModuleCat.ofHom_toSpanSingleton_comp (M := ModuleCat.of _ (OreExtension σ 0))]
        simp [hn]
      rw [h, zero_comp]).val

/-- The morphism `homOfMemKer σ N n` sends the class of `p` to `p • n`. -/
@[reassoc (attr := simp)]
theorem augmentation_comp_homOfMemKer
    (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) :
    augmentation σ ≫ homOfMemKer σ N n = ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n) :=
  (Cofork.IsColimit.desc' (unitShortComplex_shortExact σ).gIsCokernel _ _).property

/-- The morphism `homOfMemKer σ N n` sends `a` to `C a • n`. The function type is spelled out
with the carrier `SkewModule _` rather than that of `unitModuleCat σ`: `simp` reduces the
`ModuleCat.of` carrier in the goal, so a left-hand side stated with it would never match. -/
@[simp]
theorem homOfMemKer_apply
    (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) (a : R) :
    @DFunLike.coe (SkewModule (σ : R →+* R).toSemilinearMap →ₗ[OreExtension σ 0] N) _ _ _
        (homOfMemKer σ N n).hom (SkewModule.of (σ : R →+* R).toSemilinearMap a) =
      (C a : OreExtension σ 0) • (n : N) := by
  have h := ConcreteCategory.congr_hom (augmentation_comp_homOfMemKer σ N n) (C a)
  rw [ConcreteCategory.comp_apply, augmentation_C] at h
  simpa using h

/-- Evaluation at `1` identifies the morphisms from the unit module to `N` with the vectors of `N`
fixed by `X`, the kernel of the action of `X - 1`. -/
def homUnitLinearEquiv : (unitModuleCat σ ⟶ N) ≃ₗ[ℤ]
    LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0)) where
  toFun f := ⟨f (SkewModule.of (σ : R →+* R).toSemilinearMap 1), by
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← map_smul, sub_smul, one_smul,
      SkewModule.X_smul_of]
    simp⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)
  invFun := homOfMemKer σ N
  left_inv f := Cofork.IsColimit.hom_ext (unitShortComplex_shortExact σ).gIsCokernel <| by
    rw [Cofork.π_ofπ, augmentation_comp_homOfMemKer]
    exact ModuleCat.hom_ext (LinearMap.ext fun p ↦ (map_smul f.hom p _).symm)
  right_inv n := Subtype.ext <| by simp

/-- A morphism from the unit module corresponds to its value at `1`. -/
@[simp]
theorem coe_homUnitLinearEquiv_apply (f : unitModuleCat σ ⟶ N) :
    (homUnitLinearEquiv σ N f : N) = f (SkewModule.of (σ : R →+* R).toSemilinearMap 1) :=
  (rfl)

@[simp]
theorem homUnitLinearEquiv_symm_apply
    (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) :
    (homUnitLinearEquiv σ N).symm n = homOfMemKer σ N n :=
  (rfl)

/-- `Ext⁰` from the unit module of `R[X; σ]` to `N` is the group of vectors of `N` fixed by `X`. -/
def extZeroAddEquiv : Ext.{v} (unitModuleCat σ) N 0 ≃+
    LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0)) :=
  Ext.addEquiv₀.trans (homUnitLinearEquiv σ N).toAddEquiv

/-- The class in `Ext⁰` of a morphism `f` out of the unit module corresponds to `f 1`. -/
@[simp]
theorem coe_extZeroAddEquiv_mk₀ (f : unitModuleCat σ ⟶ N) :
    (extZeroAddEquiv σ N (Ext.mk₀ f) : N) = f (SkewModule.of (σ : R →+* R).toSemilinearMap 1) := by
  rw [extZeroAddEquiv, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact coe_homUnitLinearEquiv_apply σ N f

/-- A vector `n` fixed by `X` corresponds to the class in `Ext⁰` of `homOfMemKer σ N n`. -/
@[simp]
theorem extZeroAddEquiv_symm_apply
    (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) :
    (extZeroAddEquiv σ N).symm n = Ext.mk₀ (homOfMemKer σ N n) :=
  (extZeroAddEquiv σ N).symm_apply_eq.mpr <| Subtype.ext <| by simp

/-- `Ext¹` from the unit module of `R[X; σ]` to `N` is the cokernel of the action of `X - 1` on
`N`. It is computed by the resolution `unitShortComplex σ`, in which right multiplication by
`X - 1` becomes the action of `X - 1` under `Hom(R[X; σ], N) ≃ N`. -/
def extOneAddEquiv : Ext.{v} (unitModuleCat σ) N 1 ≃+
    N ⧸ LinearMap.range (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0)) :=
  AddEquiv.trans (AddEquiv.symm (homCokernelEquivExt ℤ (unitShortComplex_shortExact σ) N :
    HomCokernel ℤ (mulXSubOne σ) N ≃+ Ext.{v} (unitModuleCat σ) N 1)) <|
    (Submodule.Quotient.equiv _ _ (ModuleCat.homSelfLinearEquiv ℤ N) <| by
      -- Under evaluation at `1`, precomposition with right multiplication by `X - 1` is the action
      -- of `X - 1`.
      have h : (ModuleCat.homSelfLinearEquiv ℤ N).toLinearMap ∘ₗ
            Linear.leftComp ℤ N (mulXSubOne σ) =
          DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0) ∘ₗ
            (ModuleCat.homSelfLinearEquiv ℤ N).toLinearMap := by
        refine LinearMap.ext fun g ↦ ?_
        simp [← map_smul, mulXSubOne]
      rw [← LinearMap.range_comp, h,
        LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]).toAddEquiv

/-- Under `extOneAddEquiv`, the class of `n ∈ N` is the pushout of the extension class of the
resolution `unitShortComplex σ` along the morphism `R[X; σ] → N`, `p ↦ p • n`. -/
@[simp]
theorem extOneAddEquiv_symm_mk (n : N) :
    (extOneAddEquiv σ N).symm (Submodule.Quotient.mk n) =
      (unitShortComplex_shortExact σ).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n))) (add_zero 1) := by
  simp only [extOneAddEquiv, AddEquiv.symm_trans_apply,
    LinearEquiv.coe_toAddEquiv, ← LinearEquiv.coe_toAddEquiv_symm, LinearEquiv.coe_addEquiv_apply,
    Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_symm, ModuleCat.homSelfLinearEquiv_symm_apply]
  -- `homCokernelEquivExt_mk` is stated for `(unitShortComplex σ).f`, which is `mulXSubOne σ` by
  -- the `ShortComplex.mk` projection; `simp` does not see through it.
  exact homCokernelEquivExt_mk ℤ (unitShortComplex_shortExact σ) N _

end Ext

end TauCeti.OreExtension
