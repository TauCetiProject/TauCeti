/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Injective
public import TauCeti.FieldTheory.GaloisCohomology.DiscreteGalRep
public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# The roots of unity as a coefficient object, and the transported Kummer isomorphism

Local class field theory writes its Galois cohomology with `ZMod n` coefficients on Mathlib's
carrier: a coefficient object is an object of `TopRep (ZMod n) G_F` for
`G_F = Field.absoluteGaloisGroup F`, the automorphism group of an algebraic closure, and its
cohomology is Mathlib's `continuousCohomology`. This file supplies the coefficient object `μₙ`,
the `n`th roots of unity, and moves the Kummer isomorphism onto it.

The roots of unity themselves are those of the **separable** closure, `μₙ = μₙ(Fˢ)`, that is the
module `TauCeti.KummerCoeff F n` on which `TauCeti.AbsoluteGaloisGroup F = Gal(Fˢ/F)` acts and for
which the Kummer isomorphism `TauCeti.kummerIso` is proved. `Field.absoluteGaloisGroup F` acts on
it through the restriction isomorphism `TauCeti.absoluteGaloisGroupRestrictEquiv`, an isomorphism
because the algebraic closure is purely inseparable over `Fˢ`, and `μₙ` is a `ZMod n`-module
because it is killed by `n`. The result is `muNRep n F := galRepOfZModModule n F (KummerCoeff F n)`.
Its underlying module is identified with `TauCeti.KummerCoeff F n` via `galRepOfZModModuleEquiv`,
which intertwines the action of `σ` on `muNRep n F` with the action of its restriction to `Fˢ`
(`galRepOfZModModuleEquiv_smul`); both modules are discrete.

Pullback along the restriction isomorphism, the degree-one comparison of explicit and canonical
continuous cohomology, and the fact that continuous cohomology does not see the scalars assemble
into `galRepOfZModModuleH1Equiv n F (KummerCoeff F n) : H¹(Gal(Fˢ/F), μₙ) ≃+ H¹(G_F, muNRep n F)`.
Composing it with the Kummer isomorphism gives `kummerEquiv : Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, muNRep n F)`
for `n` invertible in `F`, and `kummerClass` is the Kummer class of a unit in this carrier. It is
the transport of the Kummer map `TauCeti.kummerMap`, not a second Kummer cocycle, and is
represented by `g ↦ g α / α` for any `n`th root `α` of the unit
(`kummerClass_eq_galRepOfZModModuleH1Equiv_kummerCocycleClass`).
The degree-two comparison gives
`galRepOfZModModuleH2Equiv n F (KummerCoeff F n) : H²(Gal(Fˢ/F), μₙ) ≃+ H²(G_F, muNRep n F)` in
the same way.

In characteristic zero every `n ≠ 0` is invertible, so the Kummer equivalence
`kummerEquivOfCharZero` holds for every `n ≠ 0`. This covers every finite extension of `ℚ_p`,
including the exponents `n` divisible by `p`, which are units of the field but not of its valuation
ring.

The name `kummerClass` here is `TauCeti.ClassFieldTheory.kummerClass`; it is not the mod-two
Kummer class `TauCeti.kummerClass`, which lives in the trivial `𝔽₂` coefficient object of
`TauCeti.AbsoluteGaloisGroup`.

When `F` contains a chosen primitive `n`th root of unity `ζ`, the action of `G_F` on `μₙ` is
trivial. The coordinate `muNRepEquivZMod` sends the chosen generator `muNRepGenerator` to `1`,
and `muNRepEquivTrivialFp` identifies `μₙ` with the trivial coefficients `ℤ/n`, sending
`ζ` to `1`. As an isomorphism of coefficient objects, `muNRepIsoTrivialFp`, it induces
`muNRepCohomologyEquivTrivialFp`, comparing the cohomology of `μₙ` with that of `ℤ/n` in every
degree; in degrees one and two it is the pullback of explicit cocycles. In degree one,
`kummerEquivTrivialFp` identifies `n`th-power classes with `H¹(G_F, ℤ/n)` for the trivial action.
This works for arbitrary nonzero `n`, without a finiteness assumption, and yields the
corresponding cardinality equality.

## Main definitions

* `TauCeti.GalRep n F`: coefficient objects `TopRep (ZMod n) G_F`
  (`TauCeti/FieldTheory/GaloisCohomology/DiscreteGalRep.lean`).
* `TauCeti.ClassFieldTheory.muNRep n F`: the roots of unity `μₙ(Fˢ)` as a coefficient object
  (`galRepOfZModModule n F (KummerCoeff F n)`).
* `TauCeti.ClassFieldTheory.kummerEquiv`, `TauCeti.ClassFieldTheory.kummerEquivOfCharZero`: the
  Kummer isomorphism `Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, muNRep n F)`, for `n` invertible in `F` and for
  `n ≠ 0` in characteristic zero.
* `TauCeti.ClassFieldTheory.kummerClass`: the Kummer class of a unit in `H¹(G_F, muNRep n F)`.
* `TauCeti.ClassFieldTheory.muNRepEquivZMod`: the chosen-root coordinate on `μₙ`.
* `TauCeti.ClassFieldTheory.muNRepGenerator`: the root with chosen coordinate `1`.
* `TauCeti.ClassFieldTheory.muNRepEquivTrivialFp`: the identification of `μₙ` with trivial `ℤ/n`
  coefficients determined by a primitive `n`th root of unity in `F`.
* `TauCeti.ClassFieldTheory.muNRepIsoTrivialFp`: the same identification as an isomorphism of
  coefficient objects.
* `TauCeti.ClassFieldTheory.muNRepCohomologyEquivTrivialFp`: its transport to `Hᵈ` in every
  degree `d`.
* `TauCeti.ClassFieldTheory.kummerEquivTrivialFp`: the Kummer isomorphism with trivial `ℤ/n`
  coefficients, given a primitive `n`th root of unity in `F`.

## Main results

* `TauCeti.ClassFieldTheory.muNRep_ρ_apply_eq_self`: `G_F` acts trivially on `muNRep n F` when `F`
  contains a primitive `n`th root of unity.
* `TauCeti.ClassFieldTheory.baer_muNRep`: `muNRep n F` is an injective `ZMod n`-module when `n` is
  invertible in `F`.
* `TauCeti.ClassFieldTheory.kummerClass_eq_galRepOfZModModuleH1Equiv_kummerCocycleClass`: the
  Kummer class of `a` is the transported class of `g ↦ g α / α`, for any `n`th root `α` of `a`.
* `TauCeti.ClassFieldTheory.kummerClass_eq_zero_iff`: the Kummer class of `a` vanishes exactly
  when `a` is an `n`th power.
* `TauCeti.ClassFieldTheory.kummerClass_surjective`: every class of `H¹(G_F, muNRep n F)` is a
  Kummer class.
* `TauCeti.ClassFieldTheory.muNRepEquivZMod_eq_mul_muNRepEquivZMod_pow`: the chosen-root
  coordinate of `ζ` is `k` times the chosen-root coordinate of `ζ ^ k`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it, for the Kummer sequence and the Kummer isomorphism.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-! ### The coefficient object `μₙ` -/

/-- **The `n`th roots of unity `μₙ(Fˢ)` of a separable closure, written additively, as a
coefficient object.** An automorphism of the algebraic closure acts through its restriction to
the separable closure, `TauCeti.absoluteGaloisGroupRestrictEquiv`; `galRepOfZModModuleEquiv`
identifies the underlying module with `TauCeti.KummerCoeff F n`. -/
abbrev muNRep : GalRep n F :=
  galRepOfZModModule n F (KummerCoeff F n)

attribute [local instance] TopRep.distribMulAction

variable {n F} in
/-- **`G_F` acts trivially on `μₙ` when `F` contains a primitive `n`th root of unity**, by
`TauCeti.smul_kummerCoeff_eq_self` read through `galRepOfZModModuleEquiv`. -/
theorem muNRep_ρ_apply_eq_self [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (g : Field.absoluteGaloisGroup F) (x : (muNRep n F).V) : (muNRep n F).ρ g x = x := by
  have h := galRepOfZModModuleEquiv_smul n F (KummerCoeff F n) g
    ((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm x)
  rwa [smul_kummerCoeff_eq_self hζ, AddEquiv.apply_symm_apply, eq_comm] at h

variable {n F} in
/-- **`μₙ` is an injective `ZMod n`-module** for `n` invertible in `F`, in the form of Baer's
criterion: `μₙ` is then cyclic of order `n` (`TauCeti.kummerCoeffAddEquivZMod`), and `ℤ/nℤ` is
self-injective (`Module.Baer.zmod_self`). Consequently `Hom(-, μₙ)` is exact on the modules killed
by `n` (`TauCeti.InternalHom.precomp_surjective_of_baer`). -/
theorem baer_muNRep (hn : IsUnit (n : F)) : Module.Baer (ZMod n) (muNRep n F).V :=
  have : NeZero (n : F) := ⟨hn.ne_zero⟩
  have : NeZero n := .of_neZero_natCast F
  Module.Baer.of_addEquiv_zmod
    ((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm.trans (kummerCoeffAddEquivZMod hn))

/-- An element of `μₙ` is determined by the root of unity of `Fˢ` that it represents. -/
theorem coe_galRepOfZModModuleEquiv_symm_injective :
    Function.Injective fun x : (muNRep n F).V ↦
      ((((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm x).toMul : (SeparableClosure F)ˣ) :
        SeparableClosure F) :=
  fun _ _ h ↦ (galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm.injective <|
    Additive.toMul.injective <| Subtype.ext <| Units.ext h

variable {n F} in
/-- The root of unity represented by `i • x` is the `i`th power of the root represented by `x`. -/
theorem coe_galRepOfZModModuleEquiv_symm_zsmul (x : (muNRep n F).V) (i : ℤ) :
    ((((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm (i • x)).toMul :
        (SeparableClosure F)ˣ) : SeparableClosure F) =
      ((((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm x).toMul :
        (SeparableClosure F)ˣ) : SeparableClosure F) ^ i := by
  rw [map_zsmul, toMul_zsmul, Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val]

/-! ### The Kummer isomorphism on `muNRep n F` -/

variable {n}

/-- **The Kummer isomorphism** `Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, μₙ)` on the coefficient object
`muNRep n F`, for `n` invertible in `F`: the Kummer isomorphism `TauCeti.kummerIso` followed by
`galRepOfZModModuleH1Equiv n F (KummerCoeff F n)`. -/
def kummerEquiv (hn : IsUnit (n : F)) :
    Additive (powerClassQuotient Fˣ n) ≃+ continuousCohomology 1 (muNRep n F) :=
  (MulEquiv.toAdditiveLeft (kummerIso F n hn)).trans
    (galRepOfZModModuleH1Equiv n F (KummerCoeff F n))

/-- `kummerEquiv` is the Kummer isomorphism `TauCeti.kummerIso` transported by
`galRepOfZModModuleH1Equiv n F (KummerCoeff F n)`. -/
theorem kummerEquiv_apply (hn : IsUnit (n : F)) (x : Additive (powerClassQuotient Fˣ n)) :
    kummerEquiv F hn x =
      galRepOfZModModuleH1Equiv n F (KummerCoeff F n)
        (Multiplicative.toAdd (kummerIso F n hn x.toMul)) :=
  (rfl)

/-- **The Kummer class** of a unit `a` of `F` in `H¹(G_F, μₙ)`, on the coefficient object
`muNRep n F`, for `n` invertible in `F`: the image of the power class of `a` under
`kummerEquiv`. -/
def kummerClass (hn : IsUnit (n : F)) (a : Fˣ) : continuousCohomology 1 (muNRep n F) :=
  kummerEquiv F hn (Additive.ofMul (powerClassHom Fˣ n a))

/-- The Kummer equivalence sends the power class of `a` to the Kummer class of `a`. -/
@[simp]
theorem kummerEquiv_ofMul_mk (hn : IsUnit (n : F)) (a : Fˣ) :
    kummerEquiv F hn (Additive.ofMul (a : powerClassQuotient Fˣ n)) = kummerClass F hn a := by
  rw [kummerClass, powerClassHom_apply]

/-- **The Kummer class is the transported Kummer map**: it is `TauCeti.kummerMap` read through
`galRepOfZModModuleH1Equiv n F (KummerCoeff F n)`. -/
theorem kummerClass_eq_galRepOfZModModuleH1Equiv_kummerMap (hn : IsUnit (n : F)) (a : Fˣ) :
    kummerClass F hn a =
      galRepOfZModModuleH1Equiv n F (KummerCoeff F n)
        (Multiplicative.toAdd (kummerMap F n hn a)) := by
  rw [← kummerEquiv_ofMul_mk, kummerEquiv_apply, toMul_ofMul, kummerIso_mk]

/-- **The Kummer class of `a` is represented by `g ↦ g α / α`**, transported to `muNRep n F`, for
any `n`th root `α` of `a` in `Fˢ`. -/
theorem kummerClass_eq_galRepOfZModModuleH1Equiv_kummerCocycleClass (hn : IsUnit (n : F)) {a : Fˣ}
    {α : (SeparableClosure F)ˣ}
    (hα : α ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a) :
    kummerClass F hn a =
      galRepOfZModModuleH1Equiv n F (KummerCoeff F n) (kummerCocycleClass hα) := by
  rw [kummerClass_eq_galRepOfZModModuleH1Equiv_kummerMap, kummerMap_eq_kummerCocycleClass hn hα]

/-- The Kummer class of `1` is zero. -/
@[simp]
theorem kummerClass_one (hn : IsUnit (n : F)) : kummerClass F hn 1 = 0 := by
  rw [kummerClass, map_one, ofMul_one, map_zero]

/-- **The Kummer class turns products into sums.** -/
@[simp]
theorem kummerClass_mul (hn : IsUnit (n : F)) (a b : Fˣ) :
    kummerClass F hn (a * b) = kummerClass F hn a + kummerClass F hn b := by
  rw [kummerClass, kummerClass, kummerClass, map_mul, ofMul_mul, map_add]

/-- **The Kummer class turns inverses into negatives.** -/
@[simp]
theorem kummerClass_inv (hn : IsUnit (n : F)) (a : Fˣ) :
    kummerClass F hn a⁻¹ = -kummerClass F hn a := by
  rw [kummerClass, kummerClass, map_inv, ofMul_inv, map_neg]

/-- **The Kummer class turns quotients into differences.** -/
@[simp]
theorem kummerClass_div (hn : IsUnit (n : F)) (a b : Fˣ) :
    kummerClass F hn (a / b) = kummerClass F hn a - kummerClass F hn b := by
  rw [kummerClass, kummerClass, kummerClass, map_div, ofMul_div, map_sub]

/-- **The Kummer class turns powers into multiples.** -/
@[simp]
theorem kummerClass_pow (hn : IsUnit (n : F)) (a : Fˣ) (k : ℕ) :
    kummerClass F hn (a ^ k) = k • kummerClass F hn a := by
  rw [kummerClass, kummerClass, map_pow, ofMul_pow, map_nsmul]

/-- **The Kummer class turns integer powers into integer multiples.** -/
@[simp]
theorem kummerClass_zpow (hn : IsUnit (n : F)) (a : Fˣ) (k : ℤ) :
    kummerClass F hn (a ^ k) = k • kummerClass F hn a := by
  rw [kummerClass, kummerClass, map_zpow, ofMul_zpow, map_zsmul]

/-- **The Kummer class of `a` vanishes exactly when `a` is an `n`th power in `F`.** -/
theorem kummerClass_eq_zero_iff (hn : IsUnit (n : F)) {a : Fˣ} :
    kummerClass F hn a = 0 ↔ a ∈ powerSubgroup Fˣ n := by
  rw [kummerClass, AddEquivClass.map_eq_zero_iff, ofMul_eq_zero, ← MonoidHom.mem_ker,
    ker_powerClassHom]

/-- **Every class of `H¹(G_F, μₙ)` is a Kummer class**, `n` being invertible in `F`. -/
theorem kummerClass_surjective (hn : IsUnit (n : F)) :
    Function.Surjective (kummerClass F hn) := by
  intro y
  obtain ⟨x, rfl⟩ := (kummerEquiv F hn).surjective y
  obtain ⟨a, ha⟩ := powerClassHom_surjective Fˣ n x.toMul
  exact ⟨a, by rw [← kummerEquiv_ofMul_mk, ← powerClassHom_apply, ha, ofMul_toMul]⟩

/-- **The Kummer isomorphism in characteristic zero**, valid for every `n ≠ 0`. This covers every
finite extension `F` of `ℚ_p` and every exponent, including those divisible by `p`, which are
units of `F` but not of its valuation ring. -/
def kummerEquivOfCharZero [CharZero F] (hn : n ≠ 0) :
    Additive (powerClassQuotient Fˣ n) ≃+ continuousCohomology 1 (muNRep n F) :=
  kummerEquiv F (Nat.cast_ne_zero.2 hn).isUnit

/-- The characteristic-zero Kummer isomorphism is `kummerEquiv` at the unit `(n : F)`. -/
theorem kummerEquivOfCharZero_apply [CharZero F] (hn : n ≠ 0)
    (x : Additive (powerClassQuotient Fˣ n)) :
    kummerEquivOfCharZero F hn x = kummerEquiv F (Nat.cast_ne_zero.2 hn).isUnit x :=
  (rfl)

/-- The characteristic-zero Kummer isomorphism sends the power class of `a` to the Kummer class
of `a`. -/
@[simp]
theorem kummerEquivOfCharZero_ofMul_mk [CharZero F] (hn : n ≠ 0) (a : Fˣ) :
    kummerEquivOfCharZero F hn (Additive.ofMul (a : powerClassQuotient Fˣ n)) =
      kummerClass F (Nat.cast_ne_zero.2 hn).isUnit a :=
  kummerEquiv_ofMul_mk F _ a

/-! ### Kummer theory with trivial coefficients -/

section

variable (n) [NeZero n]

attribute [local instance] continuousSMul_trivialFp

/-- **The coefficient identification `μₙ ≃ ℤ/n` of a primitive root**: a primitive `n`th root of
unity `ζ ∈ F` identifies `μₙ` with the trivial coefficients `ℤ/n`, sending `ζ ^ i` to the class
of `i` (`coe_galRepOfZModModuleEquiv_symm_muNRepEquivTrivialFp_symm_natCast`). It is equivariant
(`muNRepEquivTrivialFp_smul`) because `G_F` fixes `ζ` and hence acts trivially on `μₙ`. -/
def muNRepEquivTrivialFp {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    (muNRep n F).V ≃+ (trivialFp n (Field.absoluteGaloisGroup F)).V :=
  have hζu : IsPrimitiveRoot
      (Units.map (algebraMap F (SeparableClosure F)).toMonoidHom
        (Units.mk0 ζ (hζ.ne_zero (NeZero.ne n)))) n :=
    (IsPrimitiveRoot.coe_units_iff.mp hζ).map_of_injective
      (Units.map_injective (algebraMap F (SeparableClosure F)).injective)
  (galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm.trans <|
    hζu.zmodEquivRootsOfUnity.symm.trans (trivialFpEquiv n _).symm.toAddEquiv

/-- The coefficient identification of a primitive root `ζ` sends `ζ ^ i` to the class of `i`:
read back in `μₙ(Fˢ)`, the class of `i` is the image of `ζ ^ i`. -/
theorem coe_galRepOfZModModuleEquiv_symm_muNRepEquivTrivialFp_symm_natCast {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (i : ℕ) :
    ((((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm ((muNRepEquivTrivialFp n F hζ).symm
        ((trivialFpEquiv n _).symm (i : ZMod n)))).toMul : (SeparableClosure F)ˣ) :
        SeparableClosure F) = algebraMap F (SeparableClosure F) ζ ^ i := by
  simp [muNRepEquivTrivialFp]

variable {n F} in
/-- The additive coordinate on `μₙ` selected by the primitive root `ζ`, sending `ζ` to `1`. -/
def muNRepEquivZMod (ζ : F) (hζ : IsPrimitiveRoot ζ n) : (muNRep n F).V ≃+ ZMod n :=
  (muNRepEquivTrivialFp n F hζ).trans (trivialFpEquiv n _).toAddEquiv

variable {n F} in
/-- The chosen-root coordinate is the trivial-coefficient identification, read in `ZMod n`. -/
theorem muNRepEquivZMod_apply (ζ : F) (hζ : IsPrimitiveRoot ζ n) (x : (muNRep n F).V) :
    muNRepEquivZMod ζ hζ x = trivialFpEquiv n _ (muNRepEquivTrivialFp n F hζ x) :=
  (rfl)

variable {n F} in
/-- The inverse chosen-root coordinate is the inverse trivial-coefficient identification. -/
theorem muNRepEquivZMod_symm_apply (ζ : F) (hζ : IsPrimitiveRoot ζ n) (c : ZMod n) :
    (muNRepEquivZMod ζ hζ).symm c =
      (muNRepEquivTrivialFp n F hζ).symm ((trivialFpEquiv n _).symm c) :=
  (rfl)

variable {n F} in
/-- The chosen primitive root, as the element of `μₙ` with coordinate `1`. -/
def muNRepGenerator (ζ : F) (hζ : IsPrimitiveRoot ζ n) : (muNRep n F).V :=
  (muNRepEquivZMod ζ hζ).symm 1

variable {n F} in
/-- The chosen primitive root has coordinate `1`. -/
@[simp]
theorem muNRepEquivZMod_generator (ζ : F) (hζ : IsPrimitiveRoot ζ n) :
    muNRepEquivZMod ζ hζ (muNRepGenerator ζ hζ) = 1 := by
  simp only [muNRepGenerator, AddEquiv.apply_symm_apply]

variable {n F} in
/-- The chosen generator `muNRepGenerator ζ hζ` of `μₙ` represents the root `ζ` of `Fˢ`. -/
@[simp]
theorem coe_galRepOfZModModuleEquiv_symm_muNRepGenerator {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    ((((galRepOfZModModuleEquiv n F (KummerCoeff F n)).symm (muNRepGenerator ζ hζ)).toMul :
        (SeparableClosure F)ˣ) : SeparableClosure F) = algebraMap F (SeparableClosure F) ζ := by
  rw [muNRepGenerator, muNRepEquivZMod_symm_apply]
  simpa only [Nat.cast_one, pow_one] using
    coe_galRepOfZModModuleEquiv_symm_muNRepEquivTrivialFp_symm_natCast n F hζ 1

variable {n F} in
/-- Every element of `μₙ` is its chosen-root coordinate times the chosen generator. -/
@[simp]
theorem muNRepEquivZMod_smul_generator {ζ : F} (hζ : IsPrimitiveRoot ζ n) (x : (muNRep n F).V) :
    muNRepEquivZMod ζ hζ x • muNRepGenerator ζ hζ = x := by
  apply (muNRepEquivZMod ζ hζ).injective
  rw [ZMod.map_smul, muNRepEquivZMod_generator, smul_eq_mul, mul_one]

variable {n F} in
/-- The chosen generator of the primitive root `ζ ^ k` is `k` times the chosen generator of
`ζ`. -/
theorem muNRepGenerator_pow {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    (hζk : IsPrimitiveRoot (ζ ^ k) n) : muNRepGenerator (ζ ^ k) hζk = k • muNRepGenerator ζ hζ := by
  apply coe_galRepOfZModModuleEquiv_symm_injective n F
  simp only [coe_galRepOfZModModuleEquiv_symm_muNRepGenerator, ← natCast_zsmul,
    coe_galRepOfZModModuleEquiv_symm_zsmul, map_pow, zpow_natCast]

variable {n F} in
/-- **The chosen-root coordinate under a change of root**: if `ζ ^ k` is also a primitive root,
the coordinate of `x` with respect to `ζ` is `k` times its coordinate with respect to `ζ ^ k`. -/
theorem muNRepEquivZMod_eq_mul_muNRepEquivZMod_pow {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    (hζk : IsPrimitiveRoot (ζ ^ k) n) (x : (muNRep n F).V) :
    muNRepEquivZMod ζ hζ x = k * muNRepEquivZMod (ζ ^ k) hζk x := by
  conv_lhs => rw [← muNRepEquivZMod_smul_generator hζk x, muNRepGenerator_pow hζ hζk]
  rw [ZMod.map_smul, map_nsmul, muNRepEquivZMod_generator, smul_eq_mul, nsmul_eq_mul, mul_one,
    mul_comm]

/-- The coefficient identification of a primitive root intertwines the action of `G_F` on `μₙ`
with the trivial action on `ℤ/n`. -/
theorem muNRepEquivTrivialFp_smul {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (g : Field.absoluteGaloisGroup F) (x : (muNRep n F).V) :
    muNRepEquivTrivialFp n F hζ (g • x) = g • muNRepEquivTrivialFp n F hζ x := by
  rw [TopRep.distribMulAction_smul, muNRep_ρ_apply_eq_self hζ, smul_trivialFp_V]

/-- The coefficient identification of a primitive root is invariant under the action of `G_F` on
`μₙ`, which is trivial. This is the simp-normal form of `muNRepEquivTrivialFp_smul`. -/
@[simp]
theorem muNRepEquivTrivialFp_ρ_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (g : Field.absoluteGaloisGroup F) (x : (muNRep n F).V) :
    muNRepEquivTrivialFp n F hζ ((muNRep n F).ρ g x) = muNRepEquivTrivialFp n F hζ x := by
  rw [muNRep_ρ_apply_eq_self hζ]

/-- **The coefficient isomorphism `μₙ ≅ ℤ/n` of a primitive root** as coefficient objects: the
identification `muNRepEquivTrivialFp` packaged as an isomorphism of topological representations,
continuous because both sides are discrete and equivariant because `G_F` acts trivially on both
(`muNRep_ρ_apply_eq_self`). -/
def muNRepIsoTrivialFp {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    muNRep n F ≅ trivialFp n (Field.absoluteGaloisGroup F) where
  hom := ConcreteCategory.ofHom
    ⟨⟨(muNRepEquivTrivialFp n F hζ).toAddMonoidHom.toZModLinearMap n,
      continuous_of_discreteTopology⟩, fun g ↦ ContinuousLinearMap.ext fun x ↦ by
        simp [muNRep_ρ_apply_eq_self hζ, trivialFp_ρ_apply_apply]⟩
  inv := ConcreteCategory.ofHom
    ⟨⟨(muNRepEquivTrivialFp n F hζ).symm.toAddMonoidHom.toZModLinearMap n,
      continuous_of_discreteTopology⟩, fun g ↦ ContinuousLinearMap.ext fun x ↦ by
        simp [muNRep_ρ_apply_eq_self hζ, trivialFp_ρ_apply_apply]⟩
  hom_inv_id := by ext x; exact (muNRepEquivTrivialFp n F hζ).symm_apply_apply x
  inv_hom_id := by ext x; exact (muNRepEquivTrivialFp n F hζ).apply_symm_apply x

/-- The coefficient isomorphism of a primitive root acts on elements as the coefficient
identification `muNRepEquivTrivialFp`. -/
@[simp]
theorem muNRepIsoTrivialFp_hom_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n) (x : (muNRep n F).V) :
    (muNRepIsoTrivialFp n F hζ).hom x = muNRepEquivTrivialFp n F hζ x :=
  (rfl)

/-- The inverse coefficient isomorphism of a primitive root acts on elements as the inverse of the
coefficient identification `muNRepEquivTrivialFp`. -/
@[simp]
theorem muNRepIsoTrivialFp_inv_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : (trivialFp n (Field.absoluteGaloisGroup F)).V) :
    (muNRepIsoTrivialFp n F hζ).inv x = (muNRepEquivTrivialFp n F hζ).symm x :=
  (rfl)

/-- **The coefficient transport from `μₙ` to trivial `ℤ/n` coefficients in every degree**: the
image of the coefficient isomorphism `muNRepIsoTrivialFp` of the chosen primitive root under
`H^d(G_F, -)`. The chosen root is identified with `1 : ZMod n`. -/
def muNRepCohomologyEquivTrivialFp {ζ : F} (hζ : IsPrimitiveRoot ζ n) (d : ℕ) :
    continuousCohomology d (muNRep n F) ≃ₗ[ZMod n] cohomFp n (Field.absoluteGaloisGroup F) d :=
  ((TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod n) _ d).mapIso
    (muNRepIsoTrivialFp n F hζ)).toContinuousLinearEquiv.toLinearEquiv

-- Not `@[simp]`: the transport is the intended normal form, and this lemma unfolds it.
/-- The coefficient transport is the coefficient map `coeffMap` of the coefficient isomorphism
`muNRepIsoTrivialFp`. -/
theorem muNRepCohomologyEquivTrivialFp_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n) (d : ℕ)
    (x : continuousCohomology d (muNRep n F)) :
    muNRepCohomologyEquivTrivialFp n F hζ d x =
      TauCeti.ContinuousCohomology.coeffMap (muNRepIsoTrivialFp n F hζ).hom d x :=
  (rfl)

-- Not `@[simp]`: the transport is the intended normal form, and this lemma unfolds it.
/-- The inverse coefficient transport is the coefficient map `coeffMap` of the inverse of the
coefficient isomorphism `muNRepIsoTrivialFp`. -/
theorem muNRepCohomologyEquivTrivialFp_symm_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n) (d : ℕ)
    (x : cohomFp n (Field.absoluteGaloisGroup F) d) :
    (muNRepCohomologyEquivTrivialFp n F hζ d).symm x =
      TauCeti.ContinuousCohomology.coeffMap (muNRepIsoTrivialFp n F hζ).inv d x :=
  (rfl)

/-- In degree one, the coefficient transport is the pullback of explicit cocycles along the
coefficient identification `muNRepEquivTrivialFp` of the chosen primitive root. -/
theorem muNRepCohomologyEquivTrivialFp_one_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : continuousCohomology 1 (muNRep n F)) :
    muNRepCohomologyEquivTrivialFp n F hζ 1 x =
      (trivialFp n (Field.absoluteGaloisGroup F)).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (explicitMap1 (Field.absoluteGaloisGroup F) (muNRep n F).V
          (Field.absoluteGaloisGroup F) (trivialFp n (Field.absoluteGaloisGroup F)).V
          (ContinuousMulEquiv.refl (Field.absoluteGaloisGroup F) :
            Field.absoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F)
          (muNRepEquivTrivialFp n F hζ).toAddMonoidHom continuous_of_discreteTopology
          (muNRepEquivTrivialFp_smul n F hζ)
          ((muNRep n F).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm x)) := by
  obtain ⟨y, rfl⟩ := (muNRep n F).explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective x
  rw [AddEquiv.symm_apply_apply, muNRepCohomologyEquivTrivialFp_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  exact TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_map _ _ _ _ _ (fun _ ↦ rfl) _ y

/-- In degree two, the coefficient transport is the pullback of explicit cocycles along the
coefficient identification `muNRepEquivTrivialFp` of the chosen primitive root. -/
theorem muNRepCohomologyEquivTrivialFp_two_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : continuousCohomology 2 (muNRep n F)) :
    muNRepCohomologyEquivTrivialFp n F hζ 2 x =
      (trivialFp n (Field.absoluteGaloisGroup F)).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (Field.absoluteGaloisGroup F) (muNRep n F).V
          (Field.absoluteGaloisGroup F) (trivialFp n (Field.absoluteGaloisGroup F)).V
          (ContinuousMulEquiv.refl (Field.absoluteGaloisGroup F) :
            Field.absoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F)
          (muNRepEquivTrivialFp n F hζ).toAddMonoidHom continuous_of_discreteTopology
          (muNRepEquivTrivialFp_smul n F hζ)
          ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm x)) := by
  obtain ⟨y, rfl⟩ := (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete.surjective x
  rw [AddEquiv.symm_apply_apply, muNRepCohomologyEquivTrivialFp_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  exact TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_map _ _ _ _ _ (fun _ ↦ rfl) _ y

/-- Given a primitive `n`th root of unity in `F`, the Kummer isomorphism identifies the
`n`th-power classes with `H¹(G_F, ℤ/n)` for the trivial action. The coefficient identification
sends the chosen root to `1 : ZMod n`. No finiteness assumption is required. -/
def kummerEquivTrivialFp {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    Additive (powerClassQuotient Fˣ n) ≃+ cohomFp n (Field.absoluteGaloisGroup F) 1 := by
  have := hζ.neZero'
  exact (kummerEquiv F (NeZero.ne (n : F)).isUnit).trans
    (muNRepCohomologyEquivTrivialFp n F hζ 1).toAddEquiv

/-- The trivial-coefficient Kummer equivalence sends the power class of `a` to its `μₙ`
Kummer class transported by the coefficient identification determined by the chosen root. -/
@[simp]
theorem kummerEquivTrivialFp_ofMul_mk {ζ : F} (hζ : IsPrimitiveRoot ζ n) (a : Fˣ) :
    kummerEquivTrivialFp n F hζ (Additive.ofMul (a : powerClassQuotient Fˣ n)) =
      muNRepCohomologyEquivTrivialFp n F hζ 1 (kummerClass F hζ.neZero'.out.isUnit a) := by
  rw [kummerEquivTrivialFp, AddEquiv.trans_apply, kummerEquiv_ofMul_mk,
    LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]

/-- If `F` contains a primitive `n`th root, the cardinality of `H¹(G_F, ℤ/n)` equals the
number of `n`th-power classes. This equality of `Nat.card` also holds when both groups are
infinite; it does not assert finiteness. -/
theorem natCard_cohomFp_one_absoluteGaloisGroup_of_isPrimitiveRoot
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (cohomFp n (Field.absoluteGaloisGroup F) 1) =
      Nat.card (powerClassQuotient Fˣ n) :=
  (Nat.card_congr (kummerEquivTrivialFp n F hζ).toEquiv).symm.trans
    (Nat.card_congr Additive.toMul)

end

end TauCeti.ClassFieldTheory
