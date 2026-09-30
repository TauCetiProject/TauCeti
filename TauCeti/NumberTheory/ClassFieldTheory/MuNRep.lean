/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RingTheory.RootsOfUnity.ZMod
public import TauCeti.Topology.Instances.ZMod

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
because it is killed by `n`. The result is `muNRep n F`. Its underlying module is related to
`TauCeti.KummerCoeff F n` only through the additive equivalence `kummerCoeffEquivMuNRep`, whose
defining property is that it intertwines the action of `σ` on `muNRep n F` with the action of its
restriction to `Fˢ` (`kummerCoeffEquivMuNRep_smul`); both modules are discrete.

Pullback along the restriction isomorphism, the degree-one comparison of explicit and canonical
continuous cohomology, and the fact that continuous cohomology does not see the scalars assemble
into `muNRepH1Equiv : H¹(Gal(Fˢ/F), μₙ) ≃+ H¹(G_F, muNRep n F)`. Composing it with the Kummer
isomorphism gives `kummerEquiv : Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, muNRep n F)` for `n` invertible in `F`, and
`kummerClass` is the Kummer class of a unit in this carrier. It is the transport of the Kummer map
`TauCeti.kummerMap`, not a second Kummer cocycle, and is represented by `g ↦ g α / α` for any
`n`th root `α` of the unit (`kummerClass_eq_muNRepH1Equiv_kummerCocycleClass`).
The degree-two comparison gives `muNRepH2Equiv : H²(Gal(Fˢ/F), μₙ) ≃+ H²(G_F, muNRep n F)` in the
same way.

In characteristic zero every `n ≠ 0` is invertible, so the Kummer equivalence
`kummerEquivOfCharZero` holds for every `n ≠ 0`. This covers every finite extension of `ℚ_p`,
including the exponents `n` divisible by `p`, which are units of the field but not of its valuation
ring.

The name `kummerClass` here is `TauCeti.ClassFieldTheory.kummerClass`; it is not the mod-two
Kummer class `TauCeti.kummerClass`, which lives in the trivial `𝔽₂` coefficient object of
`TauCeti.AbsoluteGaloisGroup`.

## Main definitions

* `TauCeti.ClassFieldTheory.GalRep n F`: coefficient objects `TopRep (ZMod n) G_F`.
* `TauCeti.ClassFieldTheory.muNRep n F`: the roots of unity `μₙ(Fˢ)` as a coefficient object.
* `TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep`: the identification of its underlying module
  with `TauCeti.KummerCoeff F n`.
* `TauCeti.ClassFieldTheory.muNRepH1Equiv`: `H¹(Gal(Fˢ/F), μₙ) ≃+ H¹(G_F, muNRep n F)`.
* `TauCeti.ClassFieldTheory.muNRepH2Equiv`: `H²(Gal(Fˢ/F), μₙ) ≃+ H²(G_F, muNRep n F)`.
* `TauCeti.ClassFieldTheory.kummerEquiv`, `TauCeti.ClassFieldTheory.kummerEquivOfCharZero`: the
  Kummer isomorphism `Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, muNRep n F)`, for `n` invertible in `F` and for
  `n ≠ 0` in characteristic zero.
* `TauCeti.ClassFieldTheory.kummerClass`: the Kummer class of a unit in `H¹(G_F, muNRep n F)`.

## Main results

* `TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep_smul`: the dictionary is equivariant along the
  restriction isomorphism.
* `TauCeti.ClassFieldTheory.continuous_kummerCoeffEquivMuNRep`,
  `TauCeti.ClassFieldTheory.continuous_kummerCoeffEquivMuNRep_symm`: the dictionary and its
  inverse are continuous.
* `TauCeti.ClassFieldTheory.isSmoothDiscrete_muNRep`: `muNRep n F` is a smooth discrete
  coefficient object.
* `TauCeti.ClassFieldTheory.kummerClass_eq_muNRepH1Equiv_kummerCocycleClass`: the Kummer class of
  `a` is the transported class of `g ↦ g α / α`, for any `n`th root `α` of `a`.
* `TauCeti.ClassFieldTheory.kummerClass_eq_zero_iff`: the Kummer class of `a` vanishes exactly
  when `a` is an `n`th power.
* `TauCeti.ClassFieldTheory.kummerClass_surjective`: every class of `H¹(G_F, muNRep n F)` is a
  Kummer class.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it, for the Kummer sequence and the Kummer isomorphism.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-! ### The coefficient object `μₙ` -/

/-- **Coefficient objects for the absolute Galois group with `ZMod n` scalars**: topological
representations of `G_F = Field.absoluteGaloisGroup F` over `ZMod n`, on which Mathlib's
`continuousCohomology` is defined. -/
abbrev GalRep : Type (u + 1) :=
  TopRep.{u} (ZMod n) (Field.absoluteGaloisGroup F)

/-- **The `n`th roots of unity `μₙ(Fˢ)` of a separable closure, written additively, as a
coefficient object.** An automorphism of the algebraic closure acts through its restriction to
the separable closure, `TauCeti.absoluteGaloisGroupRestrictEquiv`; `kummerCoeffEquivMuNRep`
identifies the underlying module with `TauCeti.KummerCoeff F n`. -/
def muNRep : GalRep n F :=
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
    (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) (KummerCoeff F n))

/-- `μₙ` carries the discrete topology. -/
instance : DiscreteTopology (muNRep n F).V :=
  inferInstanceAs (DiscreteTopology (KummerCoeff F n))

/-- **The coefficient dictionary** between the Kummer coefficient module `TauCeti.KummerCoeff F n`
of `Gal(Fˢ/F)` and the underlying module of `muNRep n F`. It and its inverse are continuous
(`continuous_kummerCoeffEquivMuNRep`, `continuous_kummerCoeffEquivMuNRep_symm`), and it is
equivariant along the restriction isomorphism by `kummerCoeffEquivMuNRep_smul`. -/
def kummerCoeffEquivMuNRep : KummerCoeff F n ≃+ (muNRep n F).V :=
  AddEquiv.refl _

/-- The coefficient dictionary is continuous, `TauCeti.KummerCoeff F n` being discrete. -/
theorem continuous_kummerCoeffEquivMuNRep : Continuous (kummerCoeffEquivMuNRep n F) :=
  continuous_of_discreteTopology

/-- The inverse of the coefficient dictionary is continuous, `muNRep n F` being discrete. -/
theorem continuous_kummerCoeffEquivMuNRep_symm :
    Continuous (kummerCoeffEquivMuNRep n F).symm :=
  continuous_of_discreteTopology

/-- **The coefficient dictionary is equivariant**: `σ ∈ G_F` acts on `muNRep n F` as its
restriction to the separable closure acts on `TauCeti.KummerCoeff F n`. -/
@[simp]
theorem kummerCoeffEquivMuNRep_smul (g : Field.absoluteGaloisGroup F) (x : KummerCoeff F n) :
    kummerCoeffEquivMuNRep n F (absoluteGaloisGroupRestrictEquiv F g • x) =
      (muNRep n F).ρ g (kummerCoeffEquivMuNRep n F x) :=
  (ofDiscreteModule_ρ_apply_apply (R := ZMod n) (absoluteGaloisGroupRestrictEquiv F g) x).symm.trans
    (ContRepresentation.restrict_apply_apply
      (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) (KummerCoeff F n)).ρ
      (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
      g x).symm

/-- **`μₙ` is a smooth discrete coefficient object**: the stabilizer of a root of unity is the
preimage, under the restriction isomorphism, of its open stabilizer in `Gal(Fˢ/F)`. -/
theorem isSmoothDiscrete_muNRep : IsSmoothDiscrete (ZMod n) (muNRep n F) :=
  (ofDiscreteModule_isSmoothDiscrete (ZMod n) (AbsoluteGaloisGroup F) (KummerCoeff F n)).res
    (absoluteGaloisGroupRestrictEquiv F).continuous

attribute [local instance] TopRep.distribMulAction

/-- The action of `G_F` on `μₙ` is continuous, `μₙ` being smooth discrete. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup F) (muNRep n F).V :=
  (isSmoothDiscrete_muNRep n F).continuousSMul

/-! ### Transport of `H¹` -/

/-- **`H¹` of `μₙ` transported to the coefficient object `muNRep n F`**: pullback along the
restriction isomorphism `G_F ≃ Gal(Fˢ/F)` and the coefficient dictionary, followed by the
comparison of explicit and canonical continuous cohomology, and by forgetting the `ZMod n`
scalars, which continuous cohomology does not see. -/
def muNRepH1Equiv :
    H1 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+ continuousCohomology 1 (muNRep n F) :=
  (explicitMap1Equiv (AbsoluteGaloisGroup F) (KummerCoeff F n) (Field.absoluteGaloisGroup F)
      (muNRep n F).V (absoluteGaloisGroupRestrictEquiv F) (kummerCoeffEquivMuNRep n F)
      (continuous_kummerCoeffEquivMuNRep n F) (continuous_kummerCoeffEquivMuNRep_symm n F)
      fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans <|
    (muNRep n F).explicitH1AddEquivContinuousCohomologyOfDiscrete

/-- `muNRepH1Equiv` is the pullback along the restriction isomorphism and the coefficient
dictionary, followed by the degree-one comparison for the discrete object `muNRep n F`. -/
theorem muNRepH1Equiv_apply (x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    muNRepH1Equiv n F x =
      (muNRep n F).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F n) (Field.absoluteGaloisGroup F)
          (muNRep n F).V (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom (continuous_kummerCoeffEquivMuNRep n F)
          (fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [muNRepH1Equiv, AddEquiv.trans_apply, explicitMap1Equiv_apply]

/-! ### Transport of `H²` -/

/-- **`H²` of `μₙ` transported to `muNRep n F`.** This is pullback along
`absoluteGaloisGroupRestrictEquiv`, the coefficient dictionary
`kummerCoeffEquivMuNRep`, and the comparison between explicit and canonical continuous
cohomology. -/
def muNRepH2Equiv :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+
      continuousCohomology 2 (muNRep n F) :=
  (explicitMap2Equiv (AbsoluteGaloisGroup F) (KummerCoeff F n)
      (Field.absoluteGaloisGroup F) (muNRep n F).V
      (absoluteGaloisGroupRestrictEquiv F) (kummerCoeffEquivMuNRep n F)
      (continuous_kummerCoeffEquivMuNRep n F) (continuous_kummerCoeffEquivMuNRep_symm n F)
      fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans <|
    (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete

/-- `muNRepH2Equiv` is the degree-two explicit transport followed by the comparison with
Mathlib's canonical continuous cohomology. -/
theorem muNRepH2Equiv_apply (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    muNRepH2Equiv n F x =
      (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (AbsoluteGaloisGroup F) (KummerCoeff F n)
          (Field.absoluteGaloisGroup F) (muNRep n F).V
          (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom
          (continuous_kummerCoeffEquivMuNRep n F)
          (fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [muNRepH2Equiv, AddEquiv.trans_apply, explicitMap2Equiv_apply]

/-! ### The Kummer isomorphism on `muNRep n F` -/

variable {n}

/-- **The Kummer isomorphism** `Fˣ ⧸ (Fˣ)ⁿ ≃+ H¹(G_F, μₙ)` on the coefficient object
`muNRep n F`, for `n` invertible in `F`: the Kummer isomorphism `TauCeti.kummerIso` followed by
`muNRepH1Equiv`. -/
def kummerEquiv (hn : IsUnit (n : F)) :
    Additive (powerClassQuotient Fˣ n) ≃+ continuousCohomology 1 (muNRep n F) :=
  (MulEquiv.toAdditiveLeft (kummerIso F n hn)).trans (muNRepH1Equiv n F)

/-- `kummerEquiv` is the Kummer isomorphism `TauCeti.kummerIso` transported by
`muNRepH1Equiv`. -/
theorem kummerEquiv_apply (hn : IsUnit (n : F)) (x : Additive (powerClassQuotient Fˣ n)) :
    kummerEquiv F hn x = muNRepH1Equiv n F (Multiplicative.toAdd (kummerIso F n hn x.toMul)) :=
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
`muNRepH1Equiv`. -/
theorem kummerClass_eq_muNRepH1Equiv_kummerMap (hn : IsUnit (n : F)) (a : Fˣ) :
    kummerClass F hn a = muNRepH1Equiv n F (Multiplicative.toAdd (kummerMap F n hn a)) := by
  rw [← kummerEquiv_ofMul_mk, kummerEquiv_apply, toMul_ofMul, kummerIso_mk]

/-- **The Kummer class of `a` is represented by `g ↦ g α / α`**, transported to `muNRep n F`, for
any `n`th root `α` of `a` in `Fˢ`. -/
theorem kummerClass_eq_muNRepH1Equiv_kummerCocycleClass (hn : IsUnit (n : F)) {a : Fˣ}
    {α : (SeparableClosure F)ˣ}
    (hα : α ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a) :
    kummerClass F hn a = muNRepH1Equiv n F (kummerCocycleClass hα) := by
  rw [kummerClass_eq_muNRepH1Equiv_kummerMap, kummerMap_eq_kummerCocycleClass hn hα]

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

end TauCeti.ClassFieldTheory
