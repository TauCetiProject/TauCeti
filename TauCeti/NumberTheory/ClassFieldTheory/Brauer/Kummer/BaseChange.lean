/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# Base change of Kummer-cup Brauer classes

A primitive root of unity selects a pairing on Kummer coefficients. The cup product of two
Kummer classes, followed by the inclusion into the Brauer group, commutes with arbitrary field
extension, including extension to a completion. Thus the local symbols of a global pair are
invariants of the localizations of one global Brauer class.

The construction uses the existing Kummer map, explicit cup product and coefficient dictionaries;
it introduces no new cohomology carrier. The root of unity is transported along the field map,
so the statement preserves the chosen normalization.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and (1.5.3).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable (n : ℕ) (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The coefficient map on roots of unity induced by an embedding of separable closures. -/
def kummerCoeffBaseChange : KummerCoeff K n →+ KummerCoeff L n :=
  (restrictRootsOfUnity τ n).toAdditive

/-- The coefficient map applies the embedding to the underlying root of unity. -/
@[simp]
theorem toMul_kummerCoeffBaseChange (x : KummerCoeff K n) :
    ((kummerCoeffBaseChange n τ x).toMul : (SeparableClosure L)ˣ) =
      Units.map (τ : SeparableClosure K →* SeparableClosure L) x.toMul :=
  (rfl)

/-- The roots-of-unity coefficient map is equivariant along the induced Galois map. -/
theorem kummerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (x : KummerCoeff K n) :
    kummerCoeffBaseChange n τ (absoluteGaloisGroupMap τ g • x) =
      g • kummerCoeffBaseChange n τ x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp [kummerCoeffBaseChange, absoluteGaloisGroupMap_commutes]

/-- Pullback along an arbitrary field extension carries a Kummer class to the Kummer class
of the image of its unit. -/
theorem explicitMap1_kummerMap (hn : IsUnit (n : K)) (hnL : IsUnit (n : L)) (a : Kˣ) :
    explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L)
      (KummerCoeff L n) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
      continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ)
      (kummerMap K n hn a).toAdd =
        (kummerMap L n hnL (Units.map (algebraMap K L : K →* L) a)).toAdd := by
  obtain ⟨α, hα⟩ := exists_pow_eq_units_map hn a
  have hβ : (Units.map (τ : SeparableClosure K →* SeparableClosure L) α) ^ n =
      Units.map (algebraMap L (SeparableClosure L) : L →* _)
        (Units.map (algebraMap K L : K →* L) a) := by
    rw [← map_pow, hα]
    apply Units.ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [kummerMap_eq_kummerCocycleClass hn hα, kummerMap_eq_kummerCocycleClass hnL hβ,
    TauCeti.kummerCocycleClass_def, TauCeti.kummerCocycleClass_def, H1pi, H1pi,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, explicitMap1_mk]
  congr 1
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp [cocyclesMap1_apply, absoluteGaloisGroupMap_commutes]

/-- Base change commutes with the inclusion of roots-of-unity cohomology into the Brauer group,
read on the explicit roots-of-unity model. -/
theorem brBaseChange_h2MuToBr_muNRepH2Equiv
    (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :
    brBaseChange K L (h2MuToBr n K (muNRepH2Equiv n K x)) =
      h2MuToBr n L (muNRepH2Equiv n L
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L)
          (KummerCoeff L n) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ) x)) := by
  rw [h2MuToBr_muNRepH2Equiv_eq_explicitMap2, h2MuToBr_muNRepH2Equiv_eq_explicitMap2,
    brBaseChange_apply K L τ, AddEquiv.symm_apply_apply]
  apply congrArg (unitsRepH2Equiv L)
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitMap2_mk, explicitMap2_mk, explicitMap2_mk, explicitMap2_mk]
    congr 1
    apply Subtype.ext
    funext ⟨g, h⟩
    apply Additive.toMul.injective
    apply Units.ext
    simp [cochainsMap2_apply, toMul_unitsCoeffBaseChange, toMul_kummerCoeffIncl,
      toMul_kummerCoeffBaseChange]

/-- Transporting roots of unity preserves the coefficient pairing selected by a primitive root,
provided that root is transported along the field map as well. -/
theorem kummerCoeffBaseChange_kummerCoeffPairing {n : ℕ} [NeZero n]
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (x y : KummerCoeff K n) :
    kummerCoeffBaseChange n τ (kummerCoeffPairing (kummerCupPairing ζ hζ) x y) =
      kummerCoeffPairing
        (kummerCupPairing (algebraMap K L ζ) (hζ.map_of_injective (algebraMap K L).injective))
        (kummerCoeffBaseChange n τ x) (kummerCoeffBaseChange n τ y) := by
  let hζL := hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨c, hc⟩ := (muNRepEquivZMod ζ hζ).symm.surjective (kummerCoeffEquivMuNRep n K x)
  obtain ⟨i, rfl⟩ := ZMod.natCast_zmod_surjective c
  have hx : ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
      algebraMap K (SeparableClosure K) ζ ^ i := by
    have h := coe_kummerCoeffEquivMuNRep_symm_muNRepEquivTrivialFp_symm_natCast n K hζ i
    rw [← muNRepEquivZMod_symm_apply, hc, AddEquiv.symm_apply_apply] at h
    exact h
  have hxL : (((kummerCoeffBaseChange n τ x).toMul : (SeparableClosure L)ˣ) :
      SeparableClosure L) = algebraMap L (SeparableClosure L) (algebraMap K L ζ) ^ i := by
    simp [hx, ← IsScalarTower.algebraMap_apply]
  have hp : kummerCoeffPairing (kummerCupPairing ζ hζ) x y = (i : ℤ) • y := by
    apply (kummerCoeffEquivMuNRep n K).injective
    rw [kummerCoeffEquivMuNRep_kummerCoeffPairing, map_zsmul]
    exact kummerCupPairing_bil_apply ζ hζ (by simpa only [AddEquiv.symm_apply_apply,
      zpow_natCast] using hx) _
  have hpL : kummerCoeffPairing (kummerCupPairing (algebraMap K L ζ) hζL)
      (kummerCoeffBaseChange n τ x) (kummerCoeffBaseChange n τ y) =
      (i : ℤ) • kummerCoeffBaseChange n τ y := by
    apply (kummerCoeffEquivMuNRep n L).injective
    rw [kummerCoeffEquivMuNRep_kummerCoeffPairing, map_zsmul]
    exact kummerCupPairing_bil_apply _ hζL (by simpa only [AddEquiv.symm_apply_apply,
      zpow_natCast] using hxL) _
  rw [hp, map_zsmul, hpL]

section BrauerClass

variable {n} [NeZero n] (ζ : K) (hζ : IsPrimitiveRoot ζ n) (hn : IsUnit (n : K))

/-- The Brauer class of the cup of two Kummer classes, using the pairing selected by `ζ`. -/
def kummerBrauerClass (a b : Kˣ) : Br K :=
  h2MuToBr n K ((kummerCupPairing ζ hζ).cup 1 1
    (kummerClass K hn a) (kummerClass K hn b))

/-- The Kummer-cup Brauer class is the canonical cup followed by the coefficient inclusion. -/
theorem kummerBrauerClass_def (a b : Kˣ) :
    kummerBrauerClass ζ hζ hn a b =
      h2MuToBr n K ((kummerCupPairing ζ hζ).cup 1 1
        (kummerClass K hn a) (kummerClass K hn b)) :=
  (rfl)

/-- The argument `1` on the left gives the zero Brauer class. -/
@[simp]
theorem kummerBrauerClass_one_left (b : Kˣ) : kummerBrauerClass ζ hζ hn 1 b = 0 := by
  simp [kummerBrauerClass_def]

/-- The argument `1` on the right gives the zero Brauer class. -/
@[simp]
theorem kummerBrauerClass_one_right (a : Kˣ) : kummerBrauerClass ζ hζ hn a 1 = 0 := by
  simp [kummerBrauerClass_def]

/-- The Kummer-cup Brauer class is additive in its first unit argument. -/
theorem kummerBrauerClass_mul_left (a a' b : Kˣ) :
    kummerBrauerClass ζ hζ hn (a * a') b =
      kummerBrauerClass ζ hζ hn a b + kummerBrauerClass ζ hζ hn a' b := by
  simp [kummerBrauerClass_def, kummerClass_mul, LinearMap.add_apply]

/-- The Kummer-cup Brauer class is additive in its second unit argument. -/
theorem kummerBrauerClass_mul_right (a b b' : Kˣ) :
    kummerBrauerClass ζ hζ hn a (b * b') =
      kummerBrauerClass ζ hζ hn a b + kummerBrauerClass ζ hζ hn a b' := by
  simp [kummerBrauerClass_def, kummerClass_mul]

/-- The Kummer-cup Brauer class is killed by its exponent. -/
theorem nsmul_kummerBrauerClass (a b : Kˣ) : n • kummerBrauerClass ζ hζ hn a b = 0 :=
  (h2MuToBr_range n K hn _).mp ⟨_, kummerBrauerClass_def ζ hζ hn a b |>.symm⟩

/-- The Kummer-cup Brauer class satisfies the Steinberg relation. -/
theorem kummerBrauerClass_eq_zero_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    kummerBrauerClass ζ hζ hn a b = 0 := by
  rw [kummerBrauerClass_def, cup_kummerClass_eq_zero_of_add_eq_one _ hn hab, map_zero]

/-- Kummer-cup Brauer classes commute with arbitrary field extension. -/
theorem brBaseChange_kummerBrauerClass (hnL : IsUnit (n : L)) (a b : Kˣ) :
    brBaseChange K L (kummerBrauerClass ζ hζ hn a b) =
      kummerBrauerClass (algebraMap K L ζ)
        (hζ.map_of_injective (algebraMap K L).injective) hnL
        (Units.map (algebraMap K L : K →* L) a) (Units.map (algebraMap K L : K →* L) b) := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  simp only [kummerBrauerClass_def, kummerClass_eq_muNRepH1Equiv_kummerMap,
    cup_muNRepH1Equiv]
  rw [brBaseChange_h2MuToBr_muNRepH2Equiv n τ]
  rw [explicitMap2_explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n)
    (KummerCoeff K n) (KummerCoeff K n) _ _ _ (AbsoluteGaloisGroup L)
    (KummerCoeff L n) (KummerCoeff L n) (KummerCoeff L n)
    (kummerCoeffPairing (kummerCupPairing (algebraMap K L ζ)
      (hζ.map_of_injective (algebraMap K L).injective))) continuous_of_discreteTopology
    (kummerCoeffPairing_smul _) (absoluteGaloisGroupMap τ)
    (kummerCoeffBaseChange n τ) (kummerCoeffBaseChange n τ) (kummerCoeffBaseChange n τ)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (kummerCoeffBaseChange_smul n τ) (kummerCoeffBaseChange_smul n τ)
    (kummerCoeffBaseChange_smul n τ) (kummerCoeffBaseChange_kummerCoeffPairing τ ζ hζ),
    explicitMap1_kummerMap n τ hn hnL, explicitMap1_kummerMap n τ hn hnL]

end BrauerClass

end TauCeti.ClassFieldTheory
