/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.IntUnitsPower
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# Comparing the two mod-two Kummer cups

The Kummer cup with roots-of-unity coefficients and the cup with trivial `𝔽₂` coefficients
have the same vanishing criterion. The coefficient dictionary sends the pairing selected by a
primitive second root of unity to multiplication in `𝔽₂`. Naturality of the explicit cup and
the supplied comparisons with canonical continuous cohomology then identify the two cups.

Consequently the cohomological local symbol, formed from the roots-of-unity cup and any
additive identification of its degree-two cohomology with `ZMod 2`, vanishes exactly when the
norm equation `b = x² - a y²` is solvable. Translating `0, 1 : ZMod 2` to `+1, -1`
upgrades this vanishing criterion to equality with the norm-equation Hilbert symbol. The cup
comparison itself requires no local-field hypothesis and no choice of a degree-two invariant.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Propositions 4–5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1)–(6.2.2).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology _root_.ContinuousCohomology

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

attribute [local instance] TopRep.distribMulAction

local instance : ContinuousSMul (AbsoluteGaloisGroup K)
    (trivialF2 (AbsoluteGaloisGroup K)).V :=
  (isSmoothDiscrete_trivialF2 (AbsoluteGaloisGroup K)).continuousSMul

/-- The `μ₂ ≃ 𝔽₂` dictionary carries the pairing of a primitive second root of unity to
multiplication in `𝔽₂`. -/
theorem kummerCoeffEquiv_kummerCoeffPairing {ζ : K} (hζ : IsPrimitiveRoot ζ 2)
    (x y : KummerCoeff K 2) :
    kummerCoeffEquiv K (ClassFieldTheory.kummerCoeffPairing
        (ClassFieldTheory.kummerCupPairing ζ hζ) x y) =
      trivialF2Pairing (AbsoluteGaloisGroup K) (kummerCoeffEquiv K x) (kummerCoeffEquiv K y) := by
  rcases eq_zero_or_eq_mu2NegOne x with rfl | rfl
  · simp
  · have hp : ClassFieldTheory.kummerCoeffPairing
        (ClassFieldTheory.kummerCupPairing ζ hζ) mu2NegOne y = y := by
      apply (ClassFieldTheory.kummerCoeffEquivMuNRep 2 K).injective
      rw [ClassFieldTheory.kummerCoeffEquivMuNRep_kummerCoeffPairing]
      simpa using ClassFieldTheory.kummerCupPairing_bil_apply ζ hζ
        (x := ClassFieldTheory.kummerCoeffEquivMuNRep 2 K mu2NegOne) (i := 1)
        (by simp [hζ.eq_neg_one_of_two_right])
        (ClassFieldTheory.kummerCoeffEquivMuNRep 2 K y)
    simp [hp, trivialF2Pairing_apply]

private theorem explicitCup11_kummerCoeffPairing_eq_zero_iff {ζ : K}
    (hζ : IsPrimitiveRoot ζ 2) (x y : H1 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
    explicitCup11 (AbsoluteGaloisGroup K) _ _ _
        (ClassFieldTheory.kummerCoeffPairing (ClassFieldTheory.kummerCupPairing ζ hζ))
        continuous_of_discreteTopology
        (ClassFieldTheory.kummerCoeffPairing_smul _) x y = 0 ↔
      explicitCup11 (AbsoluteGaloisGroup K) _ _ _ (trivialF2Pairing (AbsoluteGaloisGroup K))
        continuous_of_discreteTopology (trivialF2Pairing_smul_smul _)
        (explicitCoeff1Equiv (AbsoluteGaloisGroup K) (KummerCoeff K 2) (kummerCoeffEquiv K)
          continuous_of_discreteTopology continuous_of_discreteTopology
          (kummerCoeffEquiv_equivariant K) x)
        (explicitCoeff1Equiv (AbsoluteGaloisGroup K) (KummerCoeff K 2) (kummerCoeffEquiv K)
          continuous_of_discreteTopology continuous_of_discreteTopology
          (kummerCoeffEquiv_equivariant K) y) = 0 := by
  let G := AbsoluteGaloisGroup K
  let P := ClassFieldTheory.kummerCupPairing ζ hζ
  let e := kummerCoeffEquiv K
  let f : KummerCoeff K 2 →+[G] (trivialF2 G).V :=
    { e.toAddMonoidHom with map_smul' := kummerCoeffEquiv_equivariant K }
  have hn := explicitCoeff2_explicitCup11 G (KummerCoeff K 2) (KummerCoeff K 2)
    (KummerCoeff K 2) (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
    (ClassFieldTheory.kummerCoeffPairing P) continuous_of_discreteTopology
    (ClassFieldTheory.kummerCoeffPairing_smul P)
    (trivialF2Pairing G) continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
    f f f continuous_of_discreteTopology continuous_of_discreteTopology
    continuous_of_discreteTopology (kummerCoeffEquiv_kummerCoeffPairing hζ) x y
  simp only [explicitCoeff1Equiv_apply]
  rw [← hn]
  simpa only [explicitCoeff2Equiv_apply] using
    (AddEquiv.map_eq_zero_iff (explicitCoeff2Equiv G (KummerCoeff K 2) e
      continuous_of_discreteTopology continuous_of_discreteTopology
      (kummerCoeffEquiv_equivariant K))
      (x := explicitCup11 G _ _ _ (ClassFieldTheory.kummerCoeffPairing P)
        continuous_of_discreteTopology (ClassFieldTheory.kummerCoeffPairing_smul P) x y)).symm

/-- Transporting arbitrary degree-one classes through the two coefficient dictionaries
preserves cup vanishing: the roots-of-unity cup vanishes exactly when the corresponding
trivial-`𝔽₂` cup does. -/
theorem cup_muNRepH1Equiv_eq_zero_iff {ζ : K} (hζ : IsPrimitiveRoot ζ 2)
    (x y : H1 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
    (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
        (ClassFieldTheory.muNRepH1Equiv 2 K x) (ClassFieldTheory.muNRepH1Equiv 2 K y) = 0 ↔
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        ((kummerCohomMap K).hom
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (KummerCoeff K 2) x))
        ((kummerCohomMap K).hom
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (KummerCoeff K 2) y))
        = 0 := by
  let G := AbsoluteGaloisGroup K
  -- Give instance search the Hausdorff separation data of the Krull topology explicitly.
  let : T2Space G := krullTopology_t2 (K := K) (L := SeparableClosure K)
  let : R1Space G := T2Space.r1Space
  let : LocallyCompactSpace G := WeaklyLocallyCompactSpace.locallyCompactSpace
  have ht (z : continuousCohomology 2 (ofDiscreteModule ℤ G (trivialF2 G).V)) :=
    map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G)))).1 (x := z)
  -- Naturality identifies each canonical cup with its explicit cup; all degree-two
  -- transports are injective, so only the explicit coefficient comparison remains.
  simpa only [ClassFieldTheory.cup_muNRepH1Equiv, AddEquiv.map_eq_zero_iff,
    kummerCohomMap_explicitH1, trivialF2TopPairing_cup_one_one_explicitH1, ht] using
    explicitCup11_kummerCoeffPairing_eq_zero_iff hζ x y

/-- The roots-of-unity cup and the trivial-`𝔽₂` cup have the same vanishing criterion on
Kummer classes, over every field in which `2` is invertible. -/
@[simp]
theorem cup_muNRep_kummerClass_eq_zero_iff {ζ : K} (hζ : IsPrimitiveRoot ζ 2) (a b : Kˣ) :
    (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
        (ClassFieldTheory.kummerClass K (isUnit_of_invertible (2 : K)) a)
        (ClassFieldTheory.kummerClass K (isUnit_of_invertible (2 : K)) b) = 0 ↔
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b) = 0 := by
  -- `kummerClass` has an unexposed body in `Basic`, so the imported characteristic
  -- lemma is needed to identify its canonical Kummer map without unfolding it.
  simpa only [ClassFieldTheory.kummerClass_eq_muNRepH1Equiv_kummerMap,
    kummerClass_def, explicitIso_kummerMap] using
    cup_muNRepH1Equiv_eq_zero_iff hζ
      (Multiplicative.toAdd (kummerMap K 2 (isUnit_of_invertible (2 : K)) a))
      (Multiplicative.toAdd (kummerMap K 2 (isUnit_of_invertible (2 : K)) b))

/-- The mod-two local symbol vanishes exactly when the canonical trivial-`𝔽₂` Kummer cup
vanishes. The statement is independent of the additive degree-two identification. -/
theorem localSymbol_eq_zero_iff_cup {ζ : K} (hζ : IsPrimitiveRoot ζ 2)
    (tr : continuousCohomology 2 (ClassFieldTheory.muNRep 2 K) ≃+ ZMod 2) (a b : Kˣ) :
    ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
        (ClassFieldTheory.kummerClass K (isUnit_of_invertible (2 : K)) a)
        (ClassFieldTheory.kummerClass K (isUnit_of_invertible (2 : K)) b) = 0 ↔
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b) = 0 := by
  rw [ClassFieldTheory.localSymbol_apply, tr.map_eq_zero_iff]
  exact cup_muNRep_kummerClass_eq_zero_iff hζ a b

/-- The roots-of-unity local symbol vanishes exactly when the norm-equation Hilbert symbol
is `1`. This criterion applies to any additive identification of degree-two cohomology. -/
theorem localSymbol_eq_zero_iff_hilbertSymbol_eq_one
    {F : Type} [Field F] [Invertible (2 : F)] {ζ : F} (hζ : IsPrimitiveRoot ζ 2)
    (tr : continuousCohomology 2 (ClassFieldTheory.muNRep 2 F) ≃+ ZMod 2) (a b : Fˣ) :
    ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) a)
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) b) = 0 ↔
      hilbertSymbol a b = 1 :=
  (localSymbol_eq_zero_iff_cup hζ tr a b).trans
    (cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one a b)

/-- The cohomological mod-two local symbol detects solvability of the quadratic norm equation. -/
theorem localSymbol_eq_zero_iff
    {F : Type} [Field F] [Invertible (2 : F)] {ζ : F} (hζ : IsPrimitiveRoot ζ 2)
    (tr : continuousCohomology 2 (ClassFieldTheory.muNRep 2 F) ≃+ ZMod 2) (a b : Fˣ) :
    ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) a)
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) b) = 0 ↔
      ∃ x y : F, (b : F) = x ^ 2 - (a : F) * y ^ 2 :=
  (localSymbol_eq_zero_iff_hilbertSymbol_eq_one hζ tr a b).trans (hilbertSymbol_eq_one_iff a b)

/-- The norm-equation Hilbert symbol agrees with the cohomological mod-two local symbol after
translating its additive invariant to a sign. -/
theorem hilbertSymbol_eq_cohomological
    {F : Type} [Field F] [Invertible (2 : F)] {ζ : F} (hζ : IsPrimitiveRoot ζ 2)
    (tr : continuousCohomology 2 (ClassFieldTheory.muNRep 2 F) ≃+ ZMod 2) (a b : Fˣ) :
    hilbertSymbol a b =
      hilbertSign (ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) a)
        (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) b)) := by
  let s := ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
    (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) a)
    (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) b)
  have hs : s = 0 ↔ hilbertSymbol a b = 1 :=
    localSymbol_eq_zero_iff_hilbertSymbol_eq_one hζ tr a b
  have hs_def : ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
      (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) a)
      (ClassFieldTheory.kummerClass F (isUnit_of_invertible (2 : F)) b) = s := rfl
  rw [hs_def]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) s with hzero | hone
  · rw [hzero, hilbertSign_zero]
    exact hs.mp hzero
  · rw [hone, hilbertSign_one]
    rcases Int.units_eq_one_or (hilbertSymbol a b) with h | h
    · exact (one_ne_zero (hone.symm.trans (hs.mpr h))).elim
    · exact h

end TauCeti
