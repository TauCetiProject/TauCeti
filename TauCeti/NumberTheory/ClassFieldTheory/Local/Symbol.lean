/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Steinberg
public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic

/-!
# The cohomological local symbol

Let `F` be a field and `n` a natural number invertible in `F`. Two Kummer classes
`(a), (b) ∈ H¹(G_F, μₙ)` cup naturally into `H²(G_F, μₙ ⊗ μₙ)`, not into `H²(G_F, μₙ)`:
multiplication of roots of unity is not biadditive. A primitive `n`th root of unity `ζ ∈ F`
supplies the missing coefficient pairing `kummerCupPairing ζ hζ : μₙ × μₙ → μₙ`,
`(ζ ^ i, y) ↦ y ^ i`, which is equivariant because `G_F` acts trivially on `μₙ` once `ζ ∈ F`.

The **local symbol** `localSymbol P tr` is the cup product along a coefficient pairing
`P : μₙ × μₙ → μₙ` followed by an identification `tr : H²(G_F, μₙ) ≃+ ZMod n`, as a
`ZMod n`-bilinear map on `H¹(G_F, μₙ)`. For a local field, with `P = kummerCupPairing ζ hζ` and
`tr` the local invariant, its values on Kummer classes are the cohomological Hilbert symbol
`(a, b) = inv ((a) ⌣ (b))`. Bilinearity is carried by the type; on Kummer classes it reads
`(a a', b) = (a, b) + (a', b)` and `(a, b b') = (a, b) + (a, b')`.

The **Steinberg relation** `(a, b) = 0` for `a + b = 1` is proved for the cup product along every
coefficient pairing (`cup_kummerClass_eq_zero_of_add_eq_one`), by computing the cup product of
Kummer classes on explicit cocycles and applying Tate's argument
`TauCeti.explicitCup11_kummerMap_eq_zero_of_add_eq_one`. It is recorded for the local symbol along
every coefficient pairing, in particular at the pairing of a primitive root
(`localSymbol_kummerClass_eq_zero_of_add_eq_one`).

The explicit computation goes through `kummerCoeffPairing P`, the pairing `P` read on the Kummer
coefficients `TauCeti.KummerCoeff F n` of `Gal(Fˢ/F)`: on classes transported by `muNRepH1Equiv`,
the cup product along `P` is the transported explicit cup product along `kummerCoeffPairing P`
(`cup_muNRepH1Equiv`).

## Main definitions

* `TauCeti.ClassFieldTheory.kummerCoeffPairing`: a coefficient pairing on `muNRep n F`, read on
  `TauCeti.KummerCoeff F n`.
* `TauCeti.ClassFieldTheory.kummerCupPairing`: the coefficient pairing `μₙ × μₙ → μₙ` of a
  primitive `n`th root of unity `ζ ∈ F`.
* `TauCeti.ClassFieldTheory.localSymbol`: cup product along a coefficient pairing followed by an
  identification `H²(G_F, μₙ) ≃+ ZMod n`.

## Main results

* `TauCeti.ClassFieldTheory.kummerCoeffPairing_smul`: `kummerCoeffPairing P` is equivariant for
  `Gal(Fˢ/F)`.
* `TauCeti.ClassFieldTheory.cup_muNRepH1Equiv`: the cup product along `P` of transported classes
  is the transported explicit cup product along `kummerCoeffPairing P`.
* `TauCeti.ClassFieldTheory.kummerCupPairing_bil`: the pairing is scalar multiplication by the
  chosen-root coordinate.
* `TauCeti.ClassFieldTheory.kummerCupPairing_bil_apply`: the pairing sends `(ζ ^ i, y)` to `i • y`.
* `TauCeti.ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`: through the
  chosen-root identification of `μₙ` with the trivial coefficients `ℤ/n`, the cup product along
  `kummerCupPairing ζ hζ` is the cup square `cupFp`.
* `TauCeti.ClassFieldTheory.localSymbol_kummerClass_mul`,
  `TauCeti.ClassFieldTheory.localSymbol_kummerClass_mul_right`: bilinearity on Kummer classes.
* `TauCeti.ClassFieldTheory.cup_kummerClass_eq_zero_of_add_eq_one`: the Steinberg relation for the
  cup product of Kummer classes along any coefficient pairing.
* `TauCeti.ClassFieldTheory.localSymbol_kummerClass_eq_zero_of_add_eq_one`: the Steinberg
  relation for the local symbol along any coefficient pairing.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Chapter XIV, §2, for the cohomological definition of the
  Hilbert symbol and its Steinberg relation.
* J. Tate, *Relations between K₂ and Galois cohomology*, Invent. Math. 36 (1976), 257–274.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology _root_.ContinuousCohomology

universe u

variable {n : ℕ} {F : Type u} [Field F]

attribute [local instance] TopRep.distribMulAction

/-! ### Cup products on `μₙ` computed on explicit cocycles -/

section Transport

variable (P : TopPairing (muNRep n F) (muNRep n F) (muNRep n F))

/-- The coefficient pairing `P` on `muNRep n F`, read on the Kummer coefficients
`TauCeti.KummerCoeff F n` through the dictionary `kummerCoeffEquivMuNRep`
(`kummerCoeffEquivMuNRep_kummerCoeffPairing`). It is the pairing along which cup products on
`muNRep n F` are computed on explicit cocycles of `Gal(Fˢ/F)` (`cup_muNRepH1Equiv`). -/
def kummerCoeffPairing : KummerCoeff F n →+ KummerCoeff F n →+ KummerCoeff F n :=
  (((LinearMap.toAddMonoidHom'.comp P.bil.toAddMonoidHom).compl₂
      (kummerCoeffEquivMuNRep n F).toAddMonoidHom).compr₂
    (kummerCoeffEquivMuNRep n F).symm.toAddMonoidHom).comp
    (kummerCoeffEquivMuNRep n F).toAddMonoidHom

/-- `kummerCoeffPairing P` is `P` under the dictionary `kummerCoeffEquivMuNRep`. -/
theorem kummerCoeffEquivMuNRep_kummerCoeffPairing (x y : KummerCoeff F n) :
    kummerCoeffEquivMuNRep n F (kummerCoeffPairing P x y) =
      P.bil (kummerCoeffEquivMuNRep n F x) (kummerCoeffEquivMuNRep n F y) := by
  simp [kummerCoeffPairing]

/-- `kummerCoeffPairing P` is equivariant for `Gal(Fˢ/F)`, since `P` is equivariant for `G_F`. -/
theorem kummerCoeffPairing_smul (g : AbsoluteGaloisGroup F) (x y : KummerCoeff F n) :
    kummerCoeffPairing P (g • x) (g • y) = g • kummerCoeffPairing P x y := by
  obtain ⟨g, rfl⟩ := (absoluteGaloisGroupRestrictEquiv F).surjective g
  refine (kummerCoeffEquivMuNRep n F).injective ?_
  rw [kummerCoeffEquivMuNRep_kummerCoeffPairing, kummerCoeffEquivMuNRep_smul,
    kummerCoeffEquivMuNRep_smul, kummerCoeffEquivMuNRep_smul, P.equivariant,
    kummerCoeffEquivMuNRep_kummerCoeffPairing]

/-- **The cup product along `P` on explicit cocycles**: the cup product along `P` of classes
transported by `muNRepH1Equiv` is the transport by `muNRepH2Equiv` of their explicit cup product
along `kummerCoeffPairing P`. -/
theorem cup_muNRepH1Equiv (x y : H1 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    P.cup 1 1 (muNRepH1Equiv n F x) (muNRepH1Equiv n F y) =
      muNRepH2Equiv n F (explicitCup11 (AbsoluteGaloisGroup F) (KummerCoeff F n)
        (KummerCoeff F n) (KummerCoeff F n) (kummerCoeffPairing P) continuous_of_discreteTopology
        (kummerCoeffPairing_smul P) x y) := by
  rw [muNRepH1Equiv_apply, muNRepH1Equiv_apply,
    P.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
      (LinearMap.toAddMonoidHom'.comp P.bil.toAddMonoidHom) (fun _ _ => by simp),
    muNRepH2Equiv_apply]
  exact congrArg _ (explicitMap2_explicitCup11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    _ _ _ (kummerCoeffEquivMuNRep_kummerCoeffPairing P) x y).symm

end Transport

/-- **The Steinberg relation** on the coefficient object `μₙ`: for `n` invertible in `F`, units
`a`, `b` of `F` with `a + b = 1`, and any coefficient pairing `P : μₙ × μₙ → μₙ`, the cup product
of the Kummer classes of `a` and `b` vanishes. -/
theorem cup_kummerClass_eq_zero_of_add_eq_one
    (P : TopPairing (muNRep n F) (muNRep n F) (muNRep n F)) (hn : IsUnit (n : F)) {a b : Fˣ}
    (hab : (a : F) + b = 1) : P.cup 1 1 (kummerClass F hn a) (kummerClass F hn b) = 0 := by
  rw [kummerClass_eq_muNRepH1Equiv_kummerMap, kummerClass_eq_muNRepH1Equiv_kummerMap,
    cup_muNRepH1Equiv, explicitCup11_kummerMap_eq_zero_of_add_eq_one _ _ hn hab, map_zero]

/-! ### The coefficient pairing of a primitive root -/

section Pairing

variable [NeZero n] (ζ : F) (hζ : IsPrimitiveRoot ζ n)

/-- **The coefficient pairing `μₙ × μₙ → μₙ` selected by a primitive `n`th root of unity
`ζ ∈ F`**: `(ζ ^ i, y) ↦ y ^ i`, written additively `(ζ ^ i, y) ↦ i • y`
(`kummerCupPairing_bil_apply`). It is equivariant because `G_F` acts trivially on `μₙ` once
`ζ ∈ F` (`muNRep_ρ_apply_eq_self`). It is the identification `μₙ ⊗ μₙ ≅ μₙ`, `ζ ⊗ ζ ↦ ζ`, through
which two Kummer classes cup into `μₙ`. -/
def kummerCupPairing : TopPairing (muNRep n F) (muNRep n F) (muNRep n F) where
  bil :=
    have hζs := (hζ.map_of_injective (algebraMap F (SeparableClosure F)).injective).isUnit_unit
      (NeZero.ne n)
    LinearMap.mk₂ (ZMod n)
      (fun x y => hζs.zmodEquivRootsOfUnity.symm ((kummerCoeffEquivMuNRep n F).symm x) • y)
      (fun x x' y => by rw [map_add, map_add, add_smul])
      (fun c x y => by
        have h₁ := ZMod.map_smul (kummerCoeffEquivMuNRep n F).symm.toAddMonoidHom c x
        have h₂ := ZMod.map_smul hζs.zmodEquivRootsOfUnity.symm.toAddMonoidHom c
          ((kummerCoeffEquivMuNRep n F).symm x)
        simp only [AddEquiv.coe_toAddMonoidHom] at h₁ h₂
        rw [h₁, h₂, smul_eq_mul, mul_smul])
      (fun x y y' => smul_add _ _ _)
      (fun c x y => smul_comm _ _ _)
  cont := continuous_of_discreteTopology
  equivariant g x y := by
    rw [muNRep_ρ_apply_eq_self hζ, muNRep_ρ_apply_eq_self hζ, muNRep_ρ_apply_eq_self hζ]

/-- **The pairing of a primitive root on powers of it**: if `x` is the root of unity `ζ ^ i`, then
`kummerCupPairing ζ hζ` pairs `x` with `y` to `i • y`, that is `y ^ i` multiplicatively. Every
`x ∈ μₙ` is a power of `ζ`, so this determines the pairing. -/
theorem kummerCupPairing_bil_apply {x : (muNRep n F).V} {i : ℤ}
    (hx : ((((kummerCoeffEquivMuNRep n F).symm x).toMul : (SeparableClosure F)ˣ) :
      SeparableClosure F) = algebraMap F (SeparableClosure F) ζ ^ i) (y : (muNRep n F).V) :
    (kummerCupPairing ζ hζ).bil x y = i • y := by
  have hζs := (hζ.map_of_injective (algebraMap F (SeparableClosure F)).injective).isUnit_unit
    (NeZero.ne n)
  have hu : (((kummerCoeffEquivMuNRep n F).symm x).toMul : (SeparableClosure F)ˣ) =
      ((hζ.map_of_injective (algebraMap F (SeparableClosure F)).injective).isUnit
        (NeZero.ne n)).unit ^ i :=
    Units.ext (by simp [hx])
  have hi : hζs.zmodEquivRootsOfUnity.symm ((kummerCoeffEquivMuNRep n F).symm x) = i := by
    rw [← hζs.zmodEquivRootsOfUnity_symm_apply_zpow i
      (hu ▸ ((kummerCoeffEquivMuNRep n F).symm x).toMul.prop)]
    exact congrArg _ (Additive.toMul.injective (Subtype.ext hu))
  simp only [kummerCupPairing, LinearMap.mk₂_apply]
  rw [hi, Int.cast_smul_eq_zsmul]

/-- The Kummer coefficient pairing is scalar multiplication by the chosen-root coordinate. -/
@[simp]
theorem kummerCupPairing_bil (x y : (muNRep n F).V) :
    (kummerCupPairing ζ hζ).bil x y = muNRepEquivZMod ζ hζ x • y := by
  obtain ⟨c, rfl⟩ := (muNRepEquivZMod ζ hζ).symm.surjective x
  obtain ⟨i, rfl⟩ := ZMod.natCast_zmod_surjective c
  have hx := coe_kummerCoeffEquivMuNRep_symm_muNRepEquivTrivialFp_symm_natCast n F hζ i
  rw [← muNRepEquivZMod_symm_apply] at hx
  have h := kummerCupPairing_bil_apply ζ hζ
    (x := (muNRepEquivZMod ζ hζ).symm (i : ZMod n))
    (i := (i : ℤ)) (by simpa only [zpow_natCast] using hx) y
  simpa only [AddEquiv.apply_symm_apply, Int.cast_natCast, Nat.cast_smul_eq_nsmul,
    natCast_zsmul] using h

/-- The coefficient pairing selected by a primitive root is symmetric. -/
theorem kummerCupPairing_bil_comm (x y : (muNRep n F).V) :
    (kummerCupPairing ζ hζ).bil x y = (kummerCupPairing ζ hζ).bil y x := by
  rw [kummerCupPairing_bil, kummerCupPairing_bil]
  apply (muNRepEquivZMod ζ hζ).injective
  simp only [ZMod.map_smul (muNRepEquivZMod ζ hζ), smul_eq_mul, mul_comm]

/-- **The pairing of a primitive root is multiplication in the chosen-root coordinate**: the
identification `μₙ ≅ ℤ/n` of `ζ` carries `kummerCupPairing ζ hζ` to the multiplication pairing
`fpPairing` of the trivial coefficients. -/
private theorem muNRepIsoTrivialFp_hom_kummerCupPairing_bil (x y : (muNRep n F).V) :
    (muNRepIsoTrivialFp n F hζ).hom ((kummerCupPairing ζ hζ).bil x y) =
      (fpPairing n (Field.absoluteGaloisGroup F)).bil ((muNRepIsoTrivialFp n F hζ).hom x)
        ((muNRepIsoTrivialFp n F hζ).hom y) := by
  apply (trivialFpEquiv n (Field.absoluteGaloisGroup F)).injective
  simp only [muNRepIsoTrivialFp_hom_apply, fpPairing_bil_apply, LinearEquiv.apply_symm_apply,
    kummerCupPairing_bil, ← muNRepEquivZMod_apply, ZMod.map_smul, smul_eq_mul]

/-- **The cup product along the pairing of a primitive root is the cup square with trivial
coefficients**: under the chosen-root identification `muNRepCohomologyEquivTrivialFp` of `μₙ`
with the trivial coefficients `ℤ/n`, the cup product along `kummerCupPairing ζ hζ` on
`H¹(G_F, μₙ)` is `cupFp` on `H¹(G_F, ℤ/n)`. -/
theorem muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup
    (x y : continuousCohomology 1 (muNRep n F)) :
    muNRepCohomologyEquivTrivialFp n F hζ 2 ((kummerCupPairing ζ hζ).cup 1 1 x y) =
      cupFp n (Field.absoluteGaloisGroup F) (muNRepCohomologyEquivTrivialFp n F hζ 1 x)
        (muNRepCohomologyEquivTrivialFp n F hζ 1 y) := by
  rw [muNRepCohomologyEquivTrivialFp_apply, muNRepCohomologyEquivTrivialFp_apply,
    muNRepCohomologyEquivTrivialFp_apply, cupFp_def]
  exact (kummerCupPairing ζ hζ).cup_coeffMap _ _ _ _
    (muNRepIsoTrivialFp_hom_kummerCupPairing_bil ζ hζ) 1 1 x y

end Pairing

/-! ### The local symbol -/

section LocalSymbol

variable (P : TopPairing (muNRep n F) (muNRep n F) (muNRep n F))
  (tr : continuousCohomology 2 (muNRep n F) ≃+ ZMod n)

/-- **The cohomological local symbol**: the cup product `H¹(G_F, μₙ) × H¹(G_F, μₙ) → H²(G_F, μₙ)`
along a coefficient pairing `P`, followed by an identification `tr : H²(G_F, μₙ) ≃+ ZMod n`, as a
`ZMod n`-bilinear map. For a local field, at `P = kummerCupPairing ζ hζ` and with `tr` the local
invariant, its values on Kummer classes are the cohomological Hilbert symbol. -/
def localSymbol :
    continuousCohomology 1 (muNRep n F) →ₗ[ZMod n] continuousCohomology 1 (muNRep n F) →ₗ[ZMod n]
      ZMod n :=
  (P.cup 1 1).compr₂ (tr.toAddMonoidHom.toZModLinearMap n)

/-- The local symbol is the cup product followed by `tr`. -/
@[simp]
theorem localSymbol_apply (x y : continuousCohomology 1 (muNRep n F)) :
    localSymbol P tr x y = tr (P.cup 1 1 x y) :=
  (rfl)

/-- **The local symbol is multiplicative in the first unit**: `(a a', b) = (a, b) + (a', b)`. -/
theorem localSymbol_kummerClass_mul (hn : IsUnit (n : F)) (a a' b : Fˣ) :
    localSymbol P tr (kummerClass F hn (a * a')) (kummerClass F hn b) =
      localSymbol P tr (kummerClass F hn a) (kummerClass F hn b) +
        localSymbol P tr (kummerClass F hn a') (kummerClass F hn b) := by
  rw [kummerClass_mul, map_add, LinearMap.add_apply]

/-- **The local symbol is multiplicative in the second unit**: `(a, b b') = (a, b) + (a, b')`. -/
theorem localSymbol_kummerClass_mul_right (hn : IsUnit (n : F)) (a b b' : Fˣ) :
    localSymbol P tr (kummerClass F hn a) (kummerClass F hn (b * b')) =
      localSymbol P tr (kummerClass F hn a) (kummerClass F hn b) +
        localSymbol P tr (kummerClass F hn a) (kummerClass F hn b') := by
  rw [kummerClass_mul, map_add]

/-- **The Steinberg relation for the local symbol** along any coefficient pairing `P`, in
particular along the pairing `kummerCupPairing ζ hζ` of a primitive `n`th root of unity `ζ ∈ F`:
`(a, b) = 0` whenever `a + b = 1`. -/
theorem localSymbol_kummerClass_eq_zero_of_add_eq_one (hn : IsUnit (n : F)) {a b : Fˣ}
    (hab : (a : F) + b = 1) :
    localSymbol P tr (kummerClass F hn a) (kummerClass F hn b) = 0 := by
  rw [localSymbol_apply, cup_kummerClass_eq_zero_of_add_eq_one _ hn hab, map_zero]

end LocalSymbol

end TauCeti.ClassFieldTheory
