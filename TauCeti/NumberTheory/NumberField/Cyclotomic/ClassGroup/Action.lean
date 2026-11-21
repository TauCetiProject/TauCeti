/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.Padics.TensorPrimaryComponent
public import TauCeti.RingTheory.ClassGroup.Galois
import TauCeti.NumberTheory.ClassGroup.Equiv
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# The Galois action on cyclotomic ideal class groups

Let `K` be the `m`-th rational cyclotomic field (`IsCyclotomicExtension {m} ℚ K`). Under Mathlib's
identification `IsCyclotomicExtension.Rat.galEquivZMod m K : Gal(K/ℚ) ≃* (ZMod m)ˣ`, each unit
`a ∈ (ZMod m)ˣ` corresponds to the automorphism `σ_a` sending every `m`-th root of unity `ζ` to
`ζ ^ a`. Restricting `σ_a` to the ring of integers `𝓞 K` induces a **covariant** action on the
ideal class group: `a` sends `[𝔞]` to `[σ_a(𝔞)]` (with no inverse), bundled as
`TauCeti.cyclotomicClassMulAction m K : (ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K))`.

Base-changing along a commutative ring `R` yields the `R`-linear representation
`TauCeti.cyclotomicClassRepresentation R m K` of `(ZMod m)ˣ` on
`R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. For a prime `p`, the finiteness of `ClassGroup (𝓞 K)` turns
`TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor` into a `ℤ_[p]`-linear equivalence
`TauCeti.numberFieldClassPrimaryEquiv` identifying the `p`-primary subgroup of
`Additive (ClassGroup (𝓞 K))` with `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`, compatibly with the
Galois action, relative norms, and ideal-class extensions.

In a cyclotomic tower `K ⊆ L` with conductors `m ∣ n`, restriction of automorphisms matches
`ZMod.unitsMap hmn`, identifying `Gal(L/K)` with `(ZMod.unitsMap hmn).ker`. Relative norm and
extension of ideal classes are therefore equivariant under `ZMod.unitsMap hmn`, and their two
composites on `R ⊗[ℤ] Additive (ClassGroup _)` evaluate to `[L : K] • id` and the orbit sum over
`(ZMod.unitsMap hmn).ker`.

## Main definitions

* `TauCeti.cyclotomicClassMulAction`: the covariant action `(ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K))`.
* `TauCeti.cyclotomicClassRepresentation`: the base-changed representation of `(ZMod m)ˣ` on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.
* `TauCeti.numberFieldClassPrimaryEquiv`: the `ℤ_[p]`-linear identification between the `p`-primary
  subgroup of `Additive (ClassGroup (𝓞 K))` and `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.
* `TauCeti.galCyclotomicEquivKerUnitsMap`: the isomorphism `Gal(L/K) ≃* (ZMod.unitsMap hmn).ker`
  for a cyclotomic tower with conductors `m ∣ n`.

## Main results

* `TauCeti.cyclotomicClassMulAction_mk0`: explicit covariant formula on integral ideal classes.
* `TauCeti.numberFieldClassPrimaryEquiv_cyclotomicAction`,
  `TauCeti.numberFieldClassPrimaryEquiv_relNorm`, and
  `TauCeti.numberFieldClassPrimaryEquiv_extended`: compatibility of the `p`-primary equivalence with
  Galois automorphisms, relative norms, and class extensions.
* `TauCeti.relNorm_cyclotomicClassMulAction`, `TauCeti.extendedHom_cyclotomicClassMulAction`, and
  `TauCeti.extendedHom_relNorm_cyclotomic`: equivariance and orbit-product formulas in a cyclotomic
  tower.
* `TauCeti.relNormBaseChange_cyclotomicClassRepresentation`,
  `TauCeti.extendedBaseChange_cyclotomicClassRepresentation`,
  `TauCeti.relNormBaseChange_comp_extendedBaseChange_cyclotomic`, and
  `TauCeti.extendedBaseChange_comp_relNormBaseChange_cyclotomic`: base-changed equivariance and
  norm-extension identities.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped NumberField TensorProduct nonZeroDivisors

namespace TauCeti

section Action

variable (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

/-- **Covariant Galois action on a cyclotomic class group.** The unit `a ∈ (ZMod m)ˣ` acts on
`ClassGroup (𝓞 K)` by pushing ideal classes forward along the ring-of-integers automorphism
induced by `σ_a = (galEquivZMod m K).symm a`. -/
noncomputable def cyclotomicClassMulAction : (ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K)) where
  toFun a := ClassGroup.mulEquiv
    (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv)
  map_one' := by
    rw [map_one]
    change ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)) =
      MulEquiv.refl (ClassGroup (𝓞 K))
    rw [RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl]
  map_mul' a b := by
    rw [map_mul]
    have hmul : (((galEquivZMod m K).symm a * (galEquivZMod m K).symm b).toRingEquiv) =
        ((galEquivZMod m K).symm b).toRingEquiv.trans ((galEquivZMod m K).symm a).toRingEquiv :=
      RingEquiv.ext fun _ ↦ rfl
    rw [hmul, RingOfIntegers.mapRingEquiv_trans, ClassGroup.mulEquiv_trans]
    rfl

theorem cyclotomicClassMulAction_apply (a : (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassMulAction m K a c =
      ClassGroup.mulEquiv
        (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv) c := by
  rfl

/-- **Covariant ideal-class action formula**: `σ_a` sends the class of a nonzero ideal `I` to the
class of its forward image `Ideal.map σ_a I`. -/
theorem cyclotomicClassMulAction_mk0 (a : (ZMod m)ˣ) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicClassMulAction m K a (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map
        (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective
            (RingOfIntegers.mapRingEquiv _).injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ :=
  ClassGroup.mulEquiv_mk0 _ I

/-- **The base-changed cyclotomic class-group representation.** For any commutative ring `R`,
`(ZMod m)ˣ` acts `R`-linearly on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` by base change of the
covariant action `TauCeti.cyclotomicClassMulAction`. -/
noncomputable def cyclotomicClassRepresentation (R : Type*) [CommRing R] :
    Representation R (ZMod m)ˣ (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) where
  toFun a := ClassGroup.mulEquivBaseChange R
    (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv)
  map_one' := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    change ClassGroup.mulEquivBaseChange R _ (1 ⊗ₜ[ℤ] Additive.ofMul c) = 1 ⊗ₜ[ℤ] Additive.ofMul c
    rw [ClassGroup.mulEquivBaseChange_tmul, ← cyclotomicClassMulAction_apply, map_one,
      MulAut.one_apply]
  map_mul' a b := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    change ClassGroup.mulEquivBaseChange R _ (1 ⊗ₜ[ℤ] Additive.ofMul c) =
      ClassGroup.mulEquivBaseChange R _ (ClassGroup.mulEquivBaseChange R _
        (1 ⊗ₜ[ℤ] Additive.ofMul c))
    rw [ClassGroup.mulEquivBaseChange_tmul, ClassGroup.mulEquivBaseChange_tmul,
      ClassGroup.mulEquivBaseChange_tmul, ← cyclotomicClassMulAction_apply,
      ← cyclotomicClassMulAction_apply, ← cyclotomicClassMulAction_apply, map_mul]
    rfl

theorem cyclotomicClassRepresentation_apply (R : Type*) [CommRing R] (a : (ZMod m)ˣ) :
    cyclotomicClassRepresentation m K R a =
      ClassGroup.mulEquivBaseChange R
        (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv) := by
  rfl

@[simp]
theorem cyclotomicClassRepresentation_tmul (R : Type*) [CommRing R] (a : (ZMod m)ˣ) (r : R)
    (c : ClassGroup (𝓞 K)) :
    cyclotomicClassRepresentation m K R a (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (cyclotomicClassMulAction m K a c) :=
  ClassGroup.mulEquivBaseChange_tmul R _ r c

end Action

section PrimaryEquiv

variable (p : ℕ) [Fact p.Prime]

/-- **Native `p`-primary equivalence for a number-field class group**: the `p`-primary subgroup of
`Additive (ClassGroup (𝓞 K))` is canonically `ℤ_[p]`-linearly isomorphic to
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
noncomputable def numberFieldClassPrimaryEquiv (K : Type*) [Field K] [NumberField K] :
    AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p ≃ₗ[ℤ_[p]]
      ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K)) :=
  TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor p
    (Additive (ClassGroup (𝓞 K))) (AddMonoid.ExponentExists.of_finite)

@[simp]
theorem numberFieldClassPrimaryEquiv_apply (K : Type*) [Field K] [NumberField K]
    (x : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p) :
    numberFieldClassPrimaryEquiv p K x = (1 : ℤ_[p]) ⊗ₜ[ℤ] (x : Additive (ClassGroup (𝓞 K))) :=
  TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor_apply
    AddMonoid.ExponentExists.of_finite x

/-- **Equivariance of the `p`-primary equivalence for cyclotomic fields.** -/
theorem numberFieldClassPrimaryEquiv_cyclotomicAction (m : ℕ) [NeZero m] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {m} ℚ K] (a : (ZMod m)ˣ)
    (x : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p) :
    numberFieldClassPrimaryEquiv p K
        (TauCeti.AddCommGroup.primaryComponentMap p
          (MonoidHom.toAdditive (cyclotomicClassMulAction m K a).toMonoidHom) x) =
      cyclotomicClassRepresentation m K ℤ_[p] a (numberFieldClassPrimaryEquiv p K x) := by
  obtain ⟨c, hc⟩ := Additive.ofMul.surjective (x : Additive (ClassGroup (𝓞 K)))
  simp [numberFieldClassPrimaryEquiv_apply, ← hc]

/-- **Naturality of the `p`-primary equivalence under relative norm.** -/
theorem numberFieldClassPrimaryEquiv_relNorm (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L]
    (x : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 L))) p) :
    numberFieldClassPrimaryEquiv p K
        (TauCeti.AddCommGroup.primaryComponentMap p
          (MonoidHom.toAdditive (ClassGroup.relNorm (𝓞 K) (S := 𝓞 L))) x) =
      ClassGroup.relNormBaseChange ℤ_[p] (𝓞 K) (𝓞 L) (numberFieldClassPrimaryEquiv p L x) := by
  obtain ⟨c, hc⟩ := Additive.ofMul.surjective (x : Additive (ClassGroup (𝓞 L)))
  simp [numberFieldClassPrimaryEquiv_apply, ← hc]

/-- **Naturality of the `p`-primary equivalence under class-group extension.** -/
theorem numberFieldClassPrimaryEquiv_extended (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L]
    (x : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p) :
    numberFieldClassPrimaryEquiv p L
        (TauCeti.AddCommGroup.primaryComponentMap p
          (MonoidHom.toAdditive (ClassGroup.extendedHom (𝓞 K) (𝓞 L))) x) =
      ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K) (𝓞 L) (numberFieldClassPrimaryEquiv p K x) := by
  obtain ⟨c, hc⟩ := Additive.ofMul.surjective (x : Additive (ClassGroup (𝓞 K)))
  simp [numberFieldClassPrimaryEquiv_apply, ← hc]

end PrimaryEquiv

section Tower

variable {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
  (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] [Algebra K L]

/-- **Restriction in a cyclotomic tower matches `ZMod.unitsMap`.** -/
theorem galEquivZMod_symm_restrictNormal [Normal ℚ K] (a : (ZMod n)ˣ) :
    ((galEquivZMod n L).symm a).restrictNormal K =
      (galEquivZMod m K).symm (ZMod.unitsMap hmn a) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  apply (galEquivZMod m K).injective
  rw [galEquivZMod_restrictNormal_apply n L K hmn, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- **Relative Galois group in a cyclotomic tower**: for `m ∣ n`, `galEquivZMod n L` restricts to
a group isomorphism `Gal(L/K) ≃* (ZMod.unitsMap hmn).ker`. -/
noncomputable def galCyclotomicEquivKerUnitsMap :
    (L ≃ₐ[K] L) ≃* (ZMod.unitsMap hmn).ker := by
  have hgalK : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  let inv : (ZMod.unitsMap hmn).ker → (L ≃ₐ[K] L) := fun u ↦
    { ((galEquivZMod n L).symm u.1).toRingEquiv with
      commutes' x := by
        have hres : ((galEquivZMod n L).symm u.1).restrictNormal K = 1 := by
          rw [galEquivZMod_symm_restrictNormal hmn K L u.1,
            MonoidHom.mem_ker.mp u.2, map_one]
        have hcomm := ((galEquivZMod n L).symm u.1).restrictNormal_commutes K x
        rw [hres, AlgEquiv.one_apply] at hcomm
        exact hcomm.symm }
  refine
    { toFun σ := ⟨galEquivZMod n L (σ.restrictScalars ℚ), ?_⟩
      invFun := inv
      left_inv σ := by
        ext x
        change ((galEquivZMod n L).symm (galEquivZMod n L (σ.restrictScalars ℚ))) x = σ x
        rw [MulEquiv.symm_apply_apply]
        rfl
      right_inv u := by
        apply Subtype.ext
        change galEquivZMod n L ((inv u).restrictScalars ℚ) = u.1
        have heq : (inv u).restrictScalars ℚ = (galEquivZMod n L).symm u.1 :=
          AlgEquiv.ext fun _ ↦ rfl
        rw [heq, MulEquiv.apply_symm_apply]
      map_mul' σ τ := by
        apply Subtype.ext
        change galEquivZMod n L ((σ * τ).restrictScalars ℚ) =
          galEquivZMod n L (σ.restrictScalars ℚ) * galEquivZMod n L (τ.restrictScalars ℚ)
        rw [← map_mul]
        rfl }
  · rw [MonoidHom.mem_ker, ← galEquivZMod_restrictNormal_apply n L K hmn]
    have hres : (σ.restrictScalars ℚ).restrictNormal K = 1 := by
      ext x
      apply (algebraMap K L).injective
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact σ.commutes x
    rw [hres, map_one]

@[simp]
theorem coe_galCyclotomicEquivKerUnitsMap_apply (σ : L ≃ₐ[K] L) :
    (galCyclotomicEquivKerUnitsMap hmn K L σ : (ZMod n)ˣ) =
      galEquivZMod n L (σ.restrictScalars ℚ) := by
  rfl

/-- **Equivariance of `ClassGroup.relNorm` in a cyclotomic tower.** -/
theorem relNorm_cyclotomicClassMulAction (a : (ZMod n)ˣ) (c : ClassGroup (𝓞 L)) :
    ClassGroup.relNorm (𝓞 K) (cyclotomicClassMulAction n L a c) =
      cyclotomicClassMulAction m K (ZMod.unitsMap hmn a) (ClassGroup.relNorm (𝓞 K) c) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassMulAction_apply, cyclotomicClassMulAction_apply,
    ← ClassGroup.relNorm_mulEquiv_ringOfIntegers (F := ℚ) ((galEquivZMod n L).symm a) c,
    galEquivZMod_symm_restrictNormal hmn K L a]

/-- **Equivariance of `ClassGroup.extendedHom` in a cyclotomic tower.** -/
theorem extendedHom_cyclotomicClassMulAction (a : (ZMod n)ˣ) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassMulAction n L a (ClassGroup.extendedHom (𝓞 K) (𝓞 L) c) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (cyclotomicClassMulAction m K (ZMod.unitsMap hmn a) c) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassMulAction_apply, cyclotomicClassMulAction_apply,
    ClassGroup.extendedHom_mulEquiv_ringOfIntegers (F := ℚ) ((galEquivZMod n L).symm a) c,
    galEquivZMod_symm_restrictNormal hmn K L a]

/-- **Galois orbit product in a cyclotomic tower**: `j ∘ N` multiplies over
`ker (ZMod.unitsMap hmn)`. -/
theorem extendedHom_relNorm_cyclotomic (c : ClassGroup (𝓞 L)) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) (ClassGroup.relNorm (𝓞 K) c) =
      ∏ g : (ZMod.unitsMap hmn).ker, cyclotomicClassMulAction n L g.1 c := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  rw [ClassGroup.extendedHom_relNorm_ringOfIntegers K L c]
  refine Fintype.prod_equiv (galCyclotomicEquivKerUnitsMap hmn K L).toEquiv _ _ fun σ ↦ ?_
  rw [cyclotomicClassMulAction_apply]
  change ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) c =
    ClassGroup.mulEquiv
      (RingOfIntegers.mapRingEquiv
        ((galEquivZMod n L).symm (galEquivZMod n L (σ.restrictScalars ℚ))).toRingEquiv) c
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- **Base-changed equivariance of relative norm in a cyclotomic tower.** -/
theorem relNormBaseChange_cyclotomicClassRepresentation (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) (cyclotomicClassRepresentation n L R a x) =
      cyclotomicClassRepresentation m K R (ZMod.unitsMap hmn a)
        (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x) := by
  have hcomp :
      (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)).comp
          (cyclotomicClassRepresentation n L R a) =
        (cyclotomicClassRepresentation m K R (ZMod.unitsMap hmn a)).comp
          (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)) := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp [relNorm_cyclotomicClassMulAction hmn K L]
  exact LinearMap.congr_fun hcomp x

/-- **Base-changed equivariance of class extension in a cyclotomic tower.** -/
theorem extendedBaseChange_cyclotomicClassRepresentation (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassRepresentation n L R a (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L) x) =
      ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)
        (cyclotomicClassRepresentation m K R (ZMod.unitsMap hmn a) x) := by
  have hcomp :
      (cyclotomicClassRepresentation n L R a).comp
          (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)) =
        (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)).comp
          (cyclotomicClassRepresentation m K R (ZMod.unitsMap hmn a)) := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp [extendedHom_cyclotomicClassMulAction hmn K L]
  exact LinearMap.congr_fun hcomp x

/-- **Extend then norm on base-changed cyclotomic class modules is multiplication by `[L : K]`.** -/
theorem relNormBaseChange_comp_extendedBaseChange_cyclotomic (R : Type*) [CommRing R] :
    (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)).comp
        (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)) =
      (Module.finrank K L : R) • LinearMap.id := by
  rw [ClassGroup.relNormBaseChange_comp_extendedBaseChange,
    IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

/-- **Norm then extend on base-changed cyclotomic class modules is the orbit sum over
`ker (ZMod.unitsMap hmn)`.** -/
theorem extendedBaseChange_comp_relNormBaseChange_cyclotomic (R : Type*) [CommRing R] :
    (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)).comp
        (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)) =
      ∑ g : (ZMod.unitsMap hmn).ker, cyclotomicClassRepresentation n L R g.1 := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [extendedHom_relNorm_cyclotomic hmn K L, TensorProduct.tmul_sum]

end Tower

end TauCeti
