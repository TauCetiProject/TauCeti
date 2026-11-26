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
public import TauCeti.Algebra.OreExtension.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Ring.GeomSum

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

* `TauCeti.OreExtension.SkewModule F`: an `R`-module `N`, as an `R[X; σ]`-module in which `X`
  acts by a `σ`-semilinear map `F`.
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

section SkewModule

variable {N : Type*} [AddCommGroup N] [Module R N] (F : N →ₛₗ[(σ : R →+* R)] N)

/-- The action of the skew polynomial ring `R[X; σ]` on an `R`-module `N` in which `X` acts by the
`σ`-semilinear map `F`, as a ring homomorphism to the additive endomorphisms of `N`. -/
def semilinearEndHom : OreExtension σ 0 →+* Module.End ℤ N :=
  lift (Module.toModuleEnd ℤ N) F.toAddMonoidHom.toIntLinearMap fun a ↦ LinearMap.ext fun n ↦ by
    simp [SigmaDerivation.coe_zero]

/-- The constants act through the `R`-module structure. -/
@[simp]
theorem semilinearEndHom_C (a : R) (n : N) : semilinearEndHom σ F (C a) n = a • n := by
  simp [semilinearEndHom]

/-- The variable acts by `F`. -/
@[simp]
theorem semilinearEndHom_X (n : N) : semilinearEndHom σ F X n = F n := by
  simp [semilinearEndHom]

variable {σ}

/-- A type synonym for an `R`-module `N` with a `σ`-semilinear endomorphism `F`, regarded as a left
module over the skew polynomial ring `R[X; σ]` in which `X` acts by `F` and the constants act
through `R`. -/
@[expose]
def SkewModule (_F : N →ₛₗ[(σ : R →+* R)] N) : Type _ :=
  N

namespace SkewModule

instance : AddCommGroup (SkewModule F) :=
  inferInstanceAs (AddCommGroup N)

instance : Module (OreExtension σ 0) (SkewModule F) :=
  Module.compHom N (semilinearEndHom σ F)

/-- The identification of `N` with the skew module `SkewModule F`. -/
def of : N ≃+ SkewModule F :=
  AddEquiv.refl N

/-- `R[X; σ]` acts on `SkewModule F` through `semilinearEndHom σ F`. -/
theorem smul_of (p : OreExtension σ 0) (n : N) : p • of F n = of F (semilinearEndHom σ F p n) :=
  (rfl)

/-- The constants act on `SkewModule F` through the `R`-module structure of `N`. -/
@[simp]
theorem C_smul_of (a : R) (n : N) : (C a : OreExtension σ 0) • of F n = of F (a • n) :=
  congrArg (of F) (semilinearEndHom_C σ F a n)

/-- The variable acts on `SkewModule F` by `F`. -/
@[simp]
theorem X_smul_of (n : N) : (X : OreExtension σ 0) • of F n = of F (F n) :=
  congrArg (of F) (semilinearEndHom_X σ F n)

/-- `X - 1` acts on `SkewModule F` by `F - 1`. -/
theorem X_sub_one_smul_of (n : N) : (X - 1 : OreExtension σ 0) • of F n = of F (F n - n) := by
  rw [sub_smul, one_smul, X_smul_of, map_sub]

end SkewModule

end SkewModule

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
  | succ n ih => rw [pow_succ, mul_smul, SkewModule.X_smul_of, RingHom.coe_toSemilinearMap,
      AlgHom.coe_toRingHom, map_one, ih]

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
    rw [map_add, augmentation_monomial, map_add, map_add, AddEquiv.symm_apply_apply,
      add_sub_add_comm, ← C_mul_X_pow_eq_monomial]
    refine Submodule.add_mem _ ⟨C a * ∑ i ∈ Finset.range n, X ^ i, ?_⟩ ih
    rw [mulXSubOne_apply, mul_assoc, geom_sum_mul, mul_sub, mul_one, C_mul_X_pow_eq_monomial]

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
    fun a ↦ ⟨C ((SkewModule.of (σ : R →+* R).toSemilinearMap).symm a), augmentation_C σ _⟩
  · have h := sub_C_mem_range_mulXSubOne σ p
    rw [(hp : (augmentation σ).hom p = 0), map_zero, map_zero, sub_zero] at h
    exact h
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
      have h : mulXSubOne σ ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n) = 0 :=
        ModuleCat.hom_ext (LinearMap.ext fun p ↦ by
          rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
            LinearMap.toSpanSingleton_apply, mulXSubOne_apply, mul_smul, hn, smul_zero,
            ModuleCat.hom_zero, LinearMap.zero_apply])
      rw [h, zero_comp]).val

/-- The morphism `homOfMemKer σ N n` sends the class of `p` to `p • n`. -/
theorem augmentation_comp_homOfMemKer
    (n : LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0))) :
    augmentation σ ≫ homOfMemKer σ N n = ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n) :=
  (Cofork.IsColimit.desc' (unitShortComplex_shortExact σ).gIsCokernel _ _).property

/-- Evaluation at `1` identifies the morphisms from the unit module to `N` with the vectors of `N`
fixed by `X`, the kernel of the action of `X - 1`. -/
def homUnitLinearEquiv : (unitModuleCat σ ⟶ N) ≃ₗ[ℤ]
    LinearMap.ker (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0)) where
  toFun f := ⟨f (SkewModule.of (σ : R →+* R).toSemilinearMap 1), by
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← map_smul, sub_smul, one_smul,
      SkewModule.X_smul_of]
    simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := homOfMemKer σ N
  left_inv f := Cofork.IsColimit.hom_ext (unitShortComplex_shortExact σ).gIsCokernel <| by
    rw [Cofork.π_ofπ, augmentation_comp_homOfMemKer]
    exact ModuleCat.hom_ext (LinearMap.ext fun p ↦ (map_smul f.hom p _).symm)
  right_inv n := Subtype.ext <| by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (augmentation_comp_homOfMemKer σ N n))
      (C 1)
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply, augmentation_C, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, C_one, one_smul] at h

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

/-- `Ext¹` from the unit module of `R[X; σ]` to `N` is the cokernel of the action of `X - 1` on
`N`. It is computed by the resolution `unitShortComplex σ`, in which right multiplication by
`X - 1` becomes the action of `X - 1` under `Hom(R[X; σ], N) ≃ N`. -/
def extOneAddEquiv : Ext.{v} (unitModuleCat σ) N 1 ≃+
    N ⧸ LinearMap.range (DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0)) :=
  -- `e` is evaluation at `1`, the identification `Hom(R[X; σ], N) ≃ N`.
  let e : (ModuleCat.of (OreExtension σ 0) (OreExtension σ 0) ⟶ N) ≃ₗ[ℤ] N :=
    ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf _ ℤ N)
  AddEquiv.trans (AddEquiv.symm (homCokernelEquivExt ℤ (unitShortComplex_shortExact σ) N :
    HomCokernel ℤ (mulXSubOne σ) N ≃+ Ext.{v} (unitModuleCat σ) N 1)) <|
    (Submodule.Quotient.equiv _ _ e <| by
      -- Under `e`, precomposition with right multiplication by `X - 1` is the action of `X - 1`.
      have h : e.toLinearMap ∘ₗ Linear.leftComp ℤ N (mulXSubOne σ) =
          DistribSMul.toLinearMap ℤ N (X - 1 : OreExtension σ 0) ∘ₗ e.toLinearMap := by
        refine LinearMap.ext fun g ↦ ?_
        simp only [e, LinearMap.comp_apply, Linear.leftComp_apply, LinearEquiv.coe_coe,
          LinearEquiv.trans_apply, LinearMap.ringLmapEquivSelf_apply, DistribSMul.toLinearMap_apply]
        rw [← map_smul, smul_eq_mul, mul_one]
        exact congrArg g.hom ((mulXSubOne_apply σ 1).trans (one_mul _))
      rw [← LinearMap.range_comp, h,
        LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]).toAddEquiv

/-- Under `extOneAddEquiv`, the class of `n ∈ N` is the pushout of the extension class of the
resolution `unitShortComplex σ` along the morphism `R[X; σ] → N`, `p ↦ p • n`. -/
@[simp]
theorem extOneAddEquiv_symm_mk (n : N) :
    (extOneAddEquiv σ N).symm (Submodule.Quotient.mk n) =
      (unitShortComplex_shortExact σ).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton _ N n))) (add_zero 1) :=
  homCokernelEquivExt_mk ℤ (unitShortComplex_shortExact σ) N _

end Ext

end TauCeti.OreExtension
