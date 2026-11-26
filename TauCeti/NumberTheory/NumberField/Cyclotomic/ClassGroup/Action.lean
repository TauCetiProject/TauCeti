/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
public import TauCeti.NumberTheory.Padics.TensorPrimaryComponent
public import TauCeti.RingTheory.ClassGroup.Galois

/-!
# The Galois action on the ideal class group of a cyclotomic field

Let `K` be the `m`-th cyclotomic field over `ℚ`. Mathlib identifies `Gal(K/ℚ)` with `(ZMod m)ˣ`
through `IsCyclotomicExtension.Rat.galEquivZMod`, under which a residue `a` corresponds to the
automorphism `σ_a` with `σ_a ζ = ζ ^ a` on every `m`-th root of unity `ζ`. Transporting `σ_a` to the
ring of integers and then to ideal classes gives the covariant action `σ_a [𝔞] = [σ_a 𝔞]` of
`(ZMod m)ˣ` on `ClassGroup (𝓞 K)` (`TauCeti.cyclotomicClassGroupAction m K`). Its scalar extension
to `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`, for a ring `R` such as `ℤ_[p]`, is the Galois module
`TauCeti.cyclotomicClassAction R m K` in which the tame character eigenspaces of the cyclotomic
class group are cut out and on which Stickelberger elements act.

The action is covariant: no inverse is inserted, so `a` acts through `σ_a` itself and not through
`σ_a⁻¹`. Both actions are bundled as monoid homomorphisms, so the identity residue acts trivially
and products of residues act by composition (`map_one`, `map_mul`).

For a prime `p`, the finiteness of `ClassGroup (𝓞 K)` turns
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

* `TauCeti.cyclotomicClassGroupAction m K`: the action `(ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K))`.
* `TauCeti.cyclotomicClassAction R m K`: its scalar extension
  `(ZMod m)ˣ →* Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K)))`.
* `TauCeti.numberFieldClassPrimaryEquiv`: the `ℤ_[p]`-linear identification between the `p`-primary
  subgroup of `Additive (ClassGroup (𝓞 K))` and `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.
* `TauCeti.galCyclotomicEquivKerUnitsMap`: the isomorphism `Gal(L/K) ≃* (ZMod.unitsMap hmn).ker`
  for a cyclotomic tower with conductors `m ∣ n`.

## Main results

* `TauCeti.cyclotomicClassGroupAction_mk0`: `σ_a` sends the class of a nonzero ideal `𝔞` to the
  class of its image `σ_a 𝔞`.
* `TauCeti.cyclotomicClassAction_tmul` and `TauCeti.cyclotomicClassAction_eq_mulEquivBaseChange`:
  on a pure tensor `r ⊗ c ↦ r ⊗ σ_a c`, matching `ClassGroup.mulEquivBaseChange`.
* `TauCeti.numberFieldClassPrimaryEquiv_cyclotomicAction`,
  `TauCeti.numberFieldClassPrimaryEquiv_relNorm`, and
  `TauCeti.numberFieldClassPrimaryEquiv_extended`: compatibility of the `p`-primary equivalence with
  Galois automorphisms, relative norms, and class extensions.
* `TauCeti.relNorm_cyclotomicClassGroupAction`, `TauCeti.extendedHom_cyclotomicClassGroupAction`,
  and `TauCeti.extendedHom_relNorm_cyclotomic`: equivariance and orbit-product formulas in a
  cyclotomic tower.
* `TauCeti.relNormBaseChange_cyclotomicClassAction`,
  `TauCeti.extendedBaseChange_cyclotomicClassAction`,
  `TauCeti.relNormBaseChange_comp_extendedBaseChange_cyclotomic`, and
  `TauCeti.extendedBaseChange_comp_relNormBaseChange_cyclotomic`: base-changed equivariance and
  norm-extension identities.

## References

* R. Sharifi, *Iwasawa theory*, §1.3, Propositions 1.3.1–1.3.2.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped NumberField TensorProduct nonZeroDivisors

namespace TauCeti

section Action

variable (R : Type*) [Ring R] (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

/-- The covariant action of `(ZMod m)ˣ ≃* Gal(K/ℚ)` on the ideal class group of the `m`-th
cyclotomic field `K`: the residue `a` acts by the class-group automorphism induced by the
automorphism `σ_a` of `𝓞 K`, where `σ_a ζ = ζ ^ a` for every `m`-th root of unity `ζ`. It is the
Galois action `classGroupAction` transported along `galEquivZMod m K`. -/
noncomputable def cyclotomicClassGroupAction : (ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K)) :=
  (classGroupAction (K ≃ₐ[ℚ] K) K).comp (galEquivZMod m K).symm.toMonoidHom

variable {m K} in
/-- The residue `a` acts on ideal classes through the class-group isomorphism
`RingEquiv.classGroupEquiv` of the automorphism `σ_a = (galEquivZMod m K).symm a` of `K`. -/
theorem cyclotomicClassGroupAction_apply (a : (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassGroupAction m K a c =
      ((galEquivZMod m K).symm a).toRingEquiv.classGroupEquiv c :=
  DFunLike.congr_fun (classGroupAction_apply _) c

variable {m K} in
/-- **The action on ideal classes.** The residue `a` sends the class of a nonzero ideal `𝔞` of
`𝓞 K` to the class of its image `σ_a 𝔞`. -/
@[simp]
theorem cyclotomicClassGroupAction_mk0 (a : (ZMod m)ˣ) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicClassGroupAction m K a (ClassGroup.mk0 I) = ClassGroup.mk0
      ⟨I.val.map (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingEquiv.injective _)).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ :=
  (cyclotomicClassGroupAction_apply a _).trans (RingEquiv.classGroupEquiv_mk0 _ I)

/-- **The cyclotomic class action.** The scalar extension, to `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`,
of the covariant action `cyclotomicClassGroupAction m K` of `(ZMod m)ˣ` on the ideal class group of
the `m`-th cyclotomic field `K`. The residue `a` acts by `r ⊗ c ↦ r ⊗ σ_a c`. -/
noncomputable def cyclotomicClassAction :
    (ZMod m)ˣ →* Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) where
  toFun a := LinearMap.baseChange R
    (cyclotomicClassGroupAction m K a).toAdditive.toAddMonoidHom.toIntLinearMap
  map_one' := by
    ext c
    simp
  map_mul' a b := by
    ext c
    simp

variable {R m K} in
/-- The cyclotomic class action is the scalar extension of the action on ideal classes. -/
theorem cyclotomicClassAction_apply (a : (ZMod m)ˣ) :
    cyclotomicClassAction R m K a = LinearMap.baseChange R
      (cyclotomicClassGroupAction m K a).toAdditive.toAddMonoidHom.toIntLinearMap :=
  (rfl)

variable {R m K} in
/-- **The action on pure tensors.** The residue `a` sends `r ⊗ c` to `r ⊗ σ_a c`. -/
@[simp]
theorem cyclotomicClassAction_tmul (a : (ZMod m)ˣ) (r : R) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassAction R m K a (r ⊗ₜ Additive.ofMul c) =
      r ⊗ₜ Additive.ofMul (cyclotomicClassGroupAction m K a c) := by
  simp [cyclotomicClassAction_apply]

variable {R m K} in
/-- The cyclotomic class action of `a` agrees with `ClassGroup.mulEquivBaseChange` for the
automorphism `σ_a = (galEquivZMod m K).symm a` of `𝓞 K`. -/
theorem cyclotomicClassAction_eq_mulEquivBaseChange (a : (ZMod m)ˣ) :
    cyclotomicClassAction R m K a =
      (ClassGroup.mulEquivBaseChange R
        (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv)).toLinearMap := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [cyclotomicClassGroupAction_apply, RingEquiv.classGroupEquiv_def]

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
    (Additive (ClassGroup (𝓞 K))) AddMonoid.ExponentExists.of_finite

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
          (cyclotomicClassGroupAction m K a).toAdditive.toAddMonoidHom x) =
      cyclotomicClassAction ℤ_[p] m K a (numberFieldClassPrimaryEquiv p K x) := by
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
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  refine MulEquiv.ofBijective
    (((galEquivZMod n L).toMonoidHom.comp (AlgEquiv.restrictScalarsHom ℚ)).codRestrict
      (ZMod.unitsMap hmn).ker fun σ ↦ ?_) ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AlgEquiv.restrictScalarsHom_apply, ← galEquivZMod_restrictNormal_apply n L K hmn]
    have hres : (σ.restrictScalars ℚ).restrictNormal K = 1 := by
      ext x
      apply (algebraMap K L).injective
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact σ.commutes x
    rw [hres, map_one]
  · intro σ τ hστ
    have h := congrArg Subtype.val hστ
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AlgEquiv.restrictScalarsHom_apply] at h
    exact AlgEquiv.restrictScalars_injective ℚ ((galEquivZMod n L).injective h)
  · intro u
    let σ : L ≃ₐ[K] L :=
      { ((galEquivZMod n L).symm u.val).toRingEquiv with
        commutes' x := by
          have hres : ((galEquivZMod n L).symm u.val).restrictNormal K = 1 := by
            rw [galEquivZMod_symm_restrictNormal hmn K L u.val,
              MonoidHom.mem_ker.mp u.property, map_one]
          have hcomm := ((galEquivZMod n L).symm u.val).restrictNormal_commutes K x
          rw [hres, AlgEquiv.one_apply] at hcomm
          exact hcomm.symm }
    refine ⟨σ, Subtype.ext ?_⟩
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AlgEquiv.restrictScalarsHom_apply]
    have hσ : σ.restrictScalars ℚ = (galEquivZMod n L).symm u.val := by
      ext x
      simp [σ]
    rw [hσ, MulEquiv.apply_symm_apply]

@[simp]
theorem coe_galCyclotomicEquivKerUnitsMap_apply (σ : L ≃ₐ[K] L) :
    (galCyclotomicEquivKerUnitsMap hmn K L σ : (ZMod n)ˣ) =
      galEquivZMod n L (σ.restrictScalars ℚ) :=
  (rfl)

/-- **Equivariance of `ClassGroup.relNorm` in a cyclotomic tower.** -/
theorem relNorm_cyclotomicClassGroupAction (a : (ZMod n)ˣ) (c : ClassGroup (𝓞 L)) :
    ClassGroup.relNorm (𝓞 K) (cyclotomicClassGroupAction n L a c) =
      cyclotomicClassGroupAction m K (ZMod.unitsMap hmn a) (ClassGroup.relNorm (𝓞 K) c) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassGroupAction_apply, cyclotomicClassGroupAction_apply,
    RingEquiv.classGroupEquiv_def, RingEquiv.classGroupEquiv_def,
    ← ClassGroup.relNorm_mulEquiv_ringOfIntegers (F := ℚ) ((galEquivZMod n L).symm a) c,
    galEquivZMod_symm_restrictNormal hmn K L a]

/-- **Equivariance of `ClassGroup.extendedHom` in a cyclotomic tower.** -/
theorem extendedHom_cyclotomicClassGroupAction (a : (ZMod n)ˣ) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassGroupAction n L a (ClassGroup.extendedHom (𝓞 K) (𝓞 L) c) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (cyclotomicClassGroupAction m K (ZMod.unitsMap hmn a) c) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassGroupAction_apply, cyclotomicClassGroupAction_apply,
    RingEquiv.classGroupEquiv_def, RingEquiv.classGroupEquiv_def,
    ClassGroup.extendedHom_mulEquiv_ringOfIntegers (F := ℚ) ((galEquivZMod n L).symm a) c,
    galEquivZMod_symm_restrictNormal hmn K L a]

/-- **Galois orbit product in a cyclotomic tower**: `j ∘ N` multiplies over
`ker (ZMod.unitsMap hmn)`. -/
theorem extendedHom_relNorm_cyclotomic (c : ClassGroup (𝓞 L)) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) (ClassGroup.relNorm (𝓞 K) c) =
      ∏ g : (ZMod.unitsMap hmn).ker, cyclotomicClassGroupAction n L g.val c := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  rw [ClassGroup.extendedHom_relNorm_ringOfIntegers K L c]
  refine Fintype.prod_equiv (galCyclotomicEquivKerUnitsMap hmn K L).toEquiv _ _ fun σ ↦ ?_
  rw [cyclotomicClassGroupAction_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    coe_galCyclotomicEquivKerUnitsMap_apply, MulEquiv.symm_apply_apply,
    RingEquiv.classGroupEquiv_def]
  have hσ : (σ.restrictScalars ℚ).toRingEquiv = σ.toRingEquiv := by
    ext x
    simp
  rw [hσ]

/-- **Base-changed equivariance of relative norm in a cyclotomic tower.** -/
theorem relNormBaseChange_cyclotomicClassAction (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) (cyclotomicClassAction R n L a x) =
      cyclotomicClassAction R m K (ZMod.unitsMap hmn a)
        (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassAction_eq_mulEquivBaseChange, cyclotomicClassAction_eq_mulEquivBaseChange,
    ← galEquivZMod_symm_restrictNormal hmn K L a]
  exact LinearMap.congr_fun
    (ClassGroup.mulEquivBaseChange_comp_relNormBaseChange R _ _
      (RingOfIntegers.mapRingEquiv_algebraMap_restrictNormal ((galEquivZMod n L).symm a))).symm x

/-- **Base-changed equivariance of class extension in a cyclotomic tower.** -/
theorem extendedBaseChange_cyclotomicClassAction (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassAction R n L a (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L) x) =
      ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)
        (cyclotomicClassAction R m K (ZMod.unitsMap hmn a) x) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [cyclotomicClassAction_eq_mulEquivBaseChange, cyclotomicClassAction_eq_mulEquivBaseChange,
    ← galEquivZMod_symm_restrictNormal hmn K L a]
  exact LinearMap.congr_fun
    (ClassGroup.mulEquivBaseChange_comp_extendedBaseChange R _ _
      (RingOfIntegers.mapRingEquiv_algebraMap_restrictNormal ((galEquivZMod n L).symm a))) x

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
      ∑ g : (ZMod.unitsMap hmn).ker, cyclotomicClassAction R n L g.val := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  rw [ClassGroup.extendedBaseChange_comp_relNormBaseChange R (𝓞 K) K L (𝓞 L)]
  refine Fintype.sum_equiv (galCyclotomicEquivKerUnitsMap hmn K L).toEquiv _ _ fun σ ↦ ?_
  rw [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, coe_galCyclotomicEquivKerUnitsMap_apply,
    cyclotomicClassAction_eq_mulEquivBaseChange, MulEquiv.symm_apply_apply]
  have hEq : (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv =
      RingOfIntegers.mapRingEquiv (σ.restrictScalars ℚ).toRingEquiv :=
    RingEquiv.ext fun z ↦ RingOfIntegers.ext (algebraMap_galRestrict_apply (𝓞 K) σ z)
  rw [hEq]

end Tower

end TauCeti
