/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
public import TauCeti.NumberTheory.LFunctions.Theta.Inversion
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic

/-!
# Harmonic polynomials and Hecke's lemma for Grossencharacters

The theta series attached to an algebraic Hecke character weights the archimedean Gaussian by a
harmonic monomial on the mixed space `mixedSpace K = ℝ^r₁ × ℂ^r₂`, chosen to match the angular part
of the character at the infinite places with the sign dictated by `Grossencharacter.compatibility`
(Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8).

For a presentation `χ : Grossencharacter K 𝔪`:

* `Grossencharacter.harmonicExponent` assigns to each infinite place `w` its harmonic degree `P_w`:
  at a real place, the parity `ε_w ∈ {0, 1}` of `χ.toHeckeCharacter.infinityType.realParity`; at a
  complex place, the absolute angular frequency `|k_w|` of `χ.infinityType`.
* `Grossencharacter.harmonicDegree` is the total degree `Tr(p) = ∑_w P_w`, by which the Mellin
  transform variable is shifted in Hecke's integral representation.
* `Grossencharacter.harmonicFactor` is the coordinatewise multiplicative polynomial `N(x^p)` on
  `mixedSpace K`: `x_w ^ ε_w` at each real place and `conj(z_w) ^ k_w` (for `k_w ≥ 0`) or
  `z_w ^ (-k_w)` (for `k_w < 0`) at each complex place of angular frequency `k_w`
  (`n w.embedding - n (conjugate w.embedding)`).
  Because `compatibility` equates the ideal-side value with the inverse of `∏_τ τ(a) ^ (n τ)`, a
  positive angular frequency puts the conjugate coordinate into `harmonicFactor`.
* `Grossencharacter.harmonicFactorMulGaussianSchwartz` bundles `harmonicFactor * archGaussian y`
  into a Schwartz function on `mixedSpace K` for positive parameters `y`, giving absolute
  summability over every discrete lattice.
* `Grossencharacter.mixedFourier_harmonicFactor_mul_archGaussian` (**Hecke's lemma**): for positive
  parameters `y`, the mixed-space Fourier transform of `x ↦ χ.harmonicFactor x * archGaussian y x`
  is `(-i) ^ (Tr p) * N(y) ^ (-1/2) * (∏_w y_w ^ (-P_w)) * χ.harmonicFactor ξ * archGaussian y⁻¹ ξ`.
* `Grossencharacter.heckeEpsilon` is the constant-term indicator `ε(χ)` of the twisted theta
  series, equal to `1` when both the finite conductor is trivial and `harmonicDegree` vanishes, and
  `0` otherwise.

Because the real parities of `χ.toHeckeCharacter.infinityType` and the algebraic infinity type
`χ.infinityType` depend only on `χ.toHeckeCharacter`, every invariant in this file is independent
of the modulus of presentation (`harmonicExponent_congr`, `harmonicDegree_congr`,
`harmonicFactor_congr`, `heckeEpsilon_congr`). Under `Grossencharacter.inverse`, the exponents,
total degree, and constant-term indicator are unchanged while `harmonicFactor` is complex
conjugated. The coordinatewise Fourier evaluation at parameter `1` uses the harmonic Gaussian
transforms of `TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic`, and the rescaling to general
positive `y` follows the dilation argument of `TauCeti.LFunctions.mixedFourier_archGaussian`.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
  Zweite Mitteilung*, Mathematische Zeitschrift **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3, 7, and 8.
-/

public section
noncomputable section

open Complex ComplexConjugate MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding TauCeti.NumberField.mixedEmbedding
open scoped NumberField Real FourierTransform RealInnerProductSpace SchwartzMap

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Cross-modulus agreement on the infinity type -/

/-- Two presentations of the same Hecke character, possibly at different moduli, have the same
algebraic infinity type. -/
theorem infinityType_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.infinityType = ψ.infinityType :=
  AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
    (χ.agreesOnIdentityComponent.symm.trans (h ▸ ψ.agreesOnIdentityComponent))

/-- The complex angular frequency of the underlying Hecke character agrees with that of the
presented algebraic infinity type. -/
theorem complexAngularFrequency_toHeckeCharacter (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    χ.toHeckeCharacter.infinityType.complexAngularFrequency w =
      (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w :=
  congrFun
    ((ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
      χ.agreesOnIdentityComponent).2.2 w

/-! ### Harmonic exponents and total degree -/

open scoped Classical in
/-- **The harmonic exponent `P_w`** of a presentation `χ` at an infinite place `w`: the parity
`ε_w ∈ {0, 1}` of the archimedean restriction at a real place, and the absolute angular frequency
`|k_w|` at a complex place. -/
def harmonicExponent (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) : ℕ :=
  if h : w.IsReal then (χ.toHeckeCharacter.infinityType.realParity ⟨w, h⟩).val
  else ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
    ⟨w, not_isReal_iff_isComplex.mp h⟩).natAbs

/-- At a real place, `harmonicExponent` is the `{0, 1}`-valued parity of the archimedean
restriction. -/
@[simp]
theorem harmonicExponent_of_isReal (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsReal) :
    χ.harmonicExponent w = (χ.toHeckeCharacter.infinityType.realParity ⟨w, hw⟩).val := by
  classical
  simp [harmonicExponent, hw]

/-- At a complex place, `harmonicExponent` is the absolute angular frequency `|k_w|`. -/
@[simp]
theorem harmonicExponent_of_isComplex (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    χ.harmonicExponent w =
      ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
        ⟨w, hw⟩).natAbs := by
  classical
  have hnr : ¬ w.IsReal := not_isReal_iff_isComplex.mpr hw
  simp [harmonicExponent, hnr]

/-- At a real place, the harmonic exponent is at most `1`. -/
theorem harmonicExponent_le_one_of_isReal (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsReal) : χ.harmonicExponent w ≤ 1 := by
  rw [harmonicExponent_of_isReal χ hw]
  exact Nat.lt_succ_iff.mp (ZMod.val_lt _)

/-- `harmonicExponent` depends only on the presented Hecke character, not on the modulus. -/
theorem harmonicExponent_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicExponent = ψ.harmonicExponent := by
  ext w
  rcases w.isReal_or_isComplex with hw | hw
  · simp [hw, h]
  · simp [hw, infinityType_congr h]

/-- Inverting a presentation leaves every harmonic exponent unchanged. -/
@[simp]
theorem harmonicExponent_inverse (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) :
    χ.inverse.harmonicExponent w = χ.harmonicExponent w := by
  rcases w.isReal_or_isComplex with hw | hw
  · have hneg : ∀ a : ZMod 2, -a = a := by decide
    simp [hw, hneg]
  · rw [harmonicExponent_of_isComplex _ hw, harmonicExponent_of_isComplex _ hw,
      infinityType_inverse, map_neg, ContinuousInfinityType.neg_complexAngularFrequency,
      Pi.neg_apply, Int.natAbs_neg]

/-- A ray class character has harmonic exponent `0` at every complex place. -/
theorem harmonicExponent_ofRayClassCharacter_of_isComplex (η : RayClassCharacter 𝔪)
    {w : InfinitePlace K} (hw : w.IsComplex) :
    (ofRayClassCharacter η).harmonicExponent w = 0 := by
  simp [hw]

/-- A ray class character of `𝔪` has harmonic exponent `0` at every real place outside `𝔪`. -/
theorem harmonicExponent_ofRayClassCharacter_of_notMem_infinitePart (η : RayClassCharacter 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w ∉ 𝔪.infinitePart) :
    (ofRayClassCharacter η).harmonicExponent w.1 = 0 := by
  rw [harmonicExponent_of_isReal _ w.2, (ofRayClassCharacter η).realParity_eq w hw]
  simp

/-- At a modulus with empty infinite part, a ray class character has zero harmonic exponents. -/
theorem harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) (w : InfinitePlace K) :
    (ofRayClassCharacter η).harmonicExponent w = 0 := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact harmonicExponent_ofRayClassCharacter_of_notMem_infinitePart η ⟨w, hw⟩ (by simp [h𝔪])
  · exact harmonicExponent_ofRayClassCharacter_of_isComplex η hw

/-- A ray class character at the trivial modulus has harmonic exponent `0` everywhere. -/
@[simp]
theorem harmonicExponent_ofRayClassCharacter_one (η : RayClassCharacter (Modulus.one K))
    (w : InfinitePlace K) :
    (ofRayClassCharacter η).harmonicExponent w = 0 :=
  harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η w

/-- Any presentation of the trivial Hecke character has harmonic exponent `0` everywhere. -/
theorem harmonicExponent_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (w : InfinitePlace K) : χ.harmonicExponent w = 0 := by
  have h1 : χ.toHeckeCharacter =
      (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).toHeckeCharacter := by
    simp [hχ]
  rw [congrFun (harmonicExponent_congr h1) w, harmonicExponent_ofRayClassCharacter_one]

open scoped Classical in
/-- **The total harmonic degree `Tr(p)`** of a presentation `χ`: the sum of `harmonicExponent`
over all infinite places, equal to the number of odd real places plus `∑_{w complex} |k_w|`.
It shifts the Mellin variable by `Tr(p) / [K : ℚ]` in the completed L-function integral. -/
def harmonicDegree (χ : Grossencharacter K 𝔪) : ℕ :=
  ∑ w : InfinitePlace K, χ.harmonicExponent w

open scoped Classical in
/-- The defining sum of `harmonicDegree`. -/
theorem harmonicDegree_def (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = ∑ w : InfinitePlace K, χ.harmonicExponent w :=
  (rfl)

open scoped Classical in
/-- Splitting `harmonicDegree` into the real-place parities and complex-place angular
frequencies. -/
theorem harmonicDegree_eq_sum_add_sum (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree =
      (∑ w : {w : InfinitePlace K // w.IsReal},
        (χ.toHeckeCharacter.infinityType.realParity w).val) +
      ∑ w : {w : InfinitePlace K // w.IsComplex},
        ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).natAbs := by
  rw [harmonicDegree_def, sum_eq_sum_add_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ ↦ χ.harmonicExponent_of_isReal w.2
  · exact Finset.sum_congr rfl fun w _ ↦ χ.harmonicExponent_of_isComplex w.2

/-- The total harmonic degree vanishes if and only if every harmonic exponent vanishes. -/
theorem harmonicDegree_eq_zero_iff (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = 0 ↔ ∀ w, χ.harmonicExponent w = 0 := by
  classical
  simp [harmonicDegree_def]

/-- `harmonicDegree` depends only on the presented Hecke character, not on the modulus. -/
theorem harmonicDegree_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicDegree = ψ.harmonicDegree := by
  classical
  simp_rw [harmonicDegree_def, harmonicExponent_congr h]

/-- Inverting a presentation preserves `harmonicDegree`. -/
@[simp]
theorem harmonicDegree_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.harmonicDegree = χ.harmonicDegree := by
  classical
  simp [harmonicDegree_def]

/-- At a modulus with empty infinite part, every ray class character has harmonic degree `0`. -/
theorem harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).harmonicDegree = 0 := by
  rw [harmonicDegree_eq_zero_iff]
  exact harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η

/-- At the trivial modulus, every ray class character has harmonic degree `0`. -/
@[simp]
theorem harmonicDegree_ofRayClassCharacter_one (η : RayClassCharacter (Modulus.one K)) :
    (ofRayClassCharacter η).harmonicDegree = 0 :=
  harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η

/-- Any presentation of the trivial Hecke character has harmonic degree `0`. -/
theorem harmonicDegree_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) : χ.harmonicDegree = 0 :=
  (harmonicDegree_eq_zero_iff χ).mpr (harmonicExponent_of_toHeckeCharacter_eq_one hχ)

/-! ### The harmonic polynomial on the mixed space -/

/-- The single-coordinate harmonic monomial at a complex place `w`: `conj(z) ^ k_w` when the
angular frequency `k_w` is nonnegative, and `z ^ (-k_w)` when `k_w < 0`. -/
private def complexHarmonicMonomial (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) : ℂ :=
  if 0 ≤ (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w then
    conj z ^ ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat
  else
    z ^ (-(AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat

private theorem complexHarmonicMonomial_one (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    complexHarmonicMonomial χ w 1 = 1 := by
  simp [complexHarmonicMonomial]

private theorem complexHarmonicMonomial_mul (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z₁ z₂ : ℂ) :
    complexHarmonicMonomial χ w (z₁ * z₂) =
      complexHarmonicMonomial χ w z₁ * complexHarmonicMonomial χ w z₂ := by
  dsimp only [complexHarmonicMonomial]
  split_ifs <;> simp [mul_pow]

private theorem complexHarmonicMonomial_ofReal (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (r : ℝ) :
    complexHarmonicMonomial χ w (r : ℂ) = ((r ^ χ.harmonicExponent w.1 : ℝ) : ℂ) := by
  rw [harmonicExponent_of_isComplex χ w.2]
  dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · have hk' : k.toNat = k.natAbs := by omega
    rw [conj_ofReal, hk', ofReal_pow]
  · have hk' : (-k).toNat = k.natAbs := by omega
    rw [hk', ofReal_pow]

private theorem norm_complexHarmonicMonomial (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) :
    ‖complexHarmonicMonomial χ w z‖ = ‖z‖ ^ χ.harmonicExponent w.1 := by
  rw [harmonicExponent_of_isComplex χ w.2]
  dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · have hk' : k.toNat = k.natAbs := by omega
    rw [norm_pow, norm_conj, hk']
  · have hk' : (-k).toNat = k.natAbs := by omega
    rw [norm_pow, hk']

private theorem complexHarmonicMonomial_inverse (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) :
    complexHarmonicMonomial χ.inverse w z = conj (complexHarmonicMonomial χ w z) := by
  dsimp only [complexHarmonicMonomial]
  rw [infinityType_inverse, map_neg, ContinuousInfinityType.neg_complexAngularFrequency,
    Pi.neg_apply, neg_neg]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with h1 h2
  · have hk : k = 0 := by omega
    simp [hk]
  · rw [map_pow]
  · rw [map_pow, conj_conj]
  · omega

open scoped Classical in
/-- **The harmonic polynomial `N(x^p)` of the theta kernel** on the mixed space (Neukirch VII §7):
at each real place `w`, `x_w ^ ε_w` where `ε_w ∈ {0, 1}` is the real parity of `χ`; at each complex
place `w` with angular frequency `k_w`, `conj(z_w) ^ k_w` if `k_w ≥ 0` and `z_w ^ (-k_w)` if
`k_w < 0`. The choice of conjugate at positive angular frequency matches the inverse sign in
`Grossencharacter.compatibility`. -/
def harmonicFactor (χ : Grossencharacter K 𝔪) (x : mixedSpace K) : ℂ :=
  (∏ w : {w : InfinitePlace K // w.IsReal},
      ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
    ∏ w : {w : InfinitePlace K // w.IsComplex},
      if 0 ≤ (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w then
        conj (x.2 w) ^
          ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat
      else
        x.2 w ^
          (-(AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat

open scoped Classical in
/-- Defining product formula for `harmonicFactor`. -/
theorem harmonicFactor_def (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x =
      (∏ w : {w : InfinitePlace K // w.IsReal},
          ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          if 0 ≤ (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w then
            conj (x.2 w) ^
              ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat
          else
            x.2 w ^
              (-(AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
                w).toNat :=
  (rfl)

open scoped Classical in
private theorem harmonicFactor_eq_prod_complexHarmonicMonomial (χ : Grossencharacter K 𝔪)
    (x : mixedSpace K) :
    χ.harmonicFactor x =
      (∏ w : {w : InfinitePlace K // w.IsReal},
          ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, complexHarmonicMonomial χ w (x.2 w) :=
  (rfl)

/-- `harmonicFactor` takes the value `1` at `1`. -/
@[simp]
theorem harmonicFactor_one (χ : Grossencharacter K 𝔪) : χ.harmonicFactor 1 = 1 := by
  classical
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial]
  simp [complexHarmonicMonomial_one]

/-- `harmonicFactor` is completely multiplicative for the coordinatewise multiplication on
`mixedSpace K`. -/
theorem harmonicFactor_mul (χ : Grossencharacter K 𝔪) (x y : mixedSpace K) :
    χ.harmonicFactor (x * y) = χ.harmonicFactor x * χ.harmonicFactor y := by
  classical
  simp only [harmonicFactor_eq_prod_complexHarmonicMonomial, Prod.fst_mul, Prod.snd_mul,
    Pi.mul_apply, ofReal_mul, mul_pow, complexHarmonicMonomial_mul, Finset.prod_mul_distrib]
  ring

/-- `harmonicFactor` commutes with natural powers on `mixedSpace K`. -/
theorem harmonicFactor_pow (χ : Grossencharacter K 𝔪) (x : mixedSpace K) (n : ℕ) :
    χ.harmonicFactor (x ^ n) = χ.harmonicFactor x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, harmonicFactor_mul, ih, pow_succ]

/-- `harmonicFactor` depends only on the presented Hecke character, not on the modulus. -/
theorem harmonicFactor_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicFactor = ψ.harmonicFactor := by
  classical
  ext x
  simp [harmonicFactor_def, h, infinityType_congr h]

/-- Inverting a presentation conjugates its harmonic polynomial pointwise. -/
@[simp]
theorem harmonicFactor_inverse (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.inverse.harmonicFactor x = conj (χ.harmonicFactor x) := by
  classical
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial,
    harmonicFactor_eq_prod_complexHarmonicMonomial, map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    simp [hneg]
  · exact Finset.prod_congr rfl fun w _ ↦ complexHarmonicMonomial_inverse χ w (x.2 w)

/-- When `harmonicDegree` vanishes, `harmonicFactor` is identically `1`. -/
theorem harmonicFactor_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (x : mixedSpace K) : χ.harmonicFactor x = 1 := by
  classical
  have hw := (harmonicDegree_eq_zero_iff χ).mp h
  rw [harmonicFactor_def]
  have hR : ∀ w : {w : InfinitePlace K // w.IsReal},
      (χ.toHeckeCharacter.infinityType.realParity w).val = 0 := fun w ↦ by
    simpa [w.2] using hw w.1
  have hC : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w = 0 :=
    fun w ↦ Int.natAbs_eq_zero.mp (by simpa [w.2] using hw w.1)
  simp [hR, hC]

/-- When `harmonicDegree` is nonzero, `harmonicFactor` vanishes at the origin. -/
theorem harmonicFactor_zero_of_harmonicDegree_ne_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree ≠ 0) : χ.harmonicFactor 0 = 0 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, χ.harmonicExponent w ≠ 0 := by
    by_contra! h0
    exact h ((harmonicDegree_eq_zero_iff χ).mpr h0)
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial]
  rcases w.isReal_or_isComplex with hwr | hwc
  · have hw' : (χ.toHeckeCharacter.infinityType.realParity ⟨w, hwr⟩).val ≠ 0 := by
      rwa [harmonicExponent_of_isReal χ hwr] at hw
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwr⟩ : {v // v.IsReal}))
    simp [zero_pow hw']
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwc⟩ : {v // v.IsComplex}))
    rw [harmonicExponent_of_isComplex χ hwc] at hw
    dsimp only [complexHarmonicMonomial, Prod.snd_zero, Pi.zero_apply]
    set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency ⟨w, hwc⟩
    split_ifs with hk
    · have hk0 : k.toNat ≠ 0 := by omega
      simp [zero_pow hk0]
    · have hk0 : (-k).toNat ≠ 0 := by omega
      simp [zero_pow hk0]

/-- At the origin, `harmonicFactor 0` is `1` if `harmonicDegree = 0` and `0` otherwise. -/
@[simp]
theorem harmonicFactor_zero (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor 0 = if χ.harmonicDegree = 0 then 1 else 0 := by
  split_ifs with h
  · exact harmonicFactor_of_harmonicDegree_eq_zero h 0
  · exact harmonicFactor_zero_of_harmonicDegree_ne_zero h

/-- At a modulus with empty infinite part, a ray class character has trivial `harmonicFactor`. -/
theorem harmonicFactor_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) (x : mixedSpace K) :
    (ofRayClassCharacter η).harmonicFactor x = 1 :=
  harmonicFactor_of_harmonicDegree_eq_zero
    (harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η) x

/-- At the trivial modulus, a ray class character has trivial `harmonicFactor`. -/
@[simp]
theorem harmonicFactor_ofRayClassCharacter_one (η : RayClassCharacter (Modulus.one K))
    (x : mixedSpace K) :
    (ofRayClassCharacter η).harmonicFactor x = 1 :=
  harmonicFactor_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η x

/-- Any presentation of the trivial Hecke character has `harmonicFactor` identically `1`. -/
theorem harmonicFactor_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (x : mixedSpace K) : χ.harmonicFactor x = 1 :=
  harmonicFactor_of_harmonicDegree_eq_zero (harmonicDegree_of_toHeckeCharacter_eq_one hχ) x

/-! ### Scaling, norm, and action of real parameters -/

/-- On a real-coordinate vector `mixedSpaceOfRealSpace r`, `harmonicFactor` is the product of
`r w ^ harmonicExponent w` over all infinite places. -/
theorem harmonicFactor_mixedSpaceOfRealSpace (χ : Grossencharacter K 𝔪) (r : realSpace K) :
    χ.harmonicFactor (mixedSpaceOfRealSpace r) =
      ((∏ w : InfinitePlace K, r w ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  classical
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial, prod_eq_prod_mul_prod, ofReal_mul,
    ofReal_prod, ofReal_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mixedSpaceOfRealSpace_apply, χ.harmonicExponent_of_isReal w.2, ofReal_pow]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mixedSpaceOfRealSpace_apply, complexHarmonicMonomial_ofReal]

/-- Multiplying by `mixedSpaceOfRealSpace r` scales `harmonicFactor` by
`∏_w r_w ^ harmonicExponent w`. -/
theorem harmonicFactor_mixedSpaceOfRealSpace_mul (χ : Grossencharacter K 𝔪) (r : realSpace K)
    (x : mixedSpace K) :
    χ.harmonicFactor (mixedSpaceOfRealSpace r * x) =
      ((∏ w : InfinitePlace K, r w ^ χ.harmonicExponent w : ℝ) : ℂ) * χ.harmonicFactor x := by
  rw [harmonicFactor_mul, harmonicFactor_mixedSpaceOfRealSpace]

/-- `harmonicFactor` is homogeneous of degree `harmonicDegree` under real scalar multiplication. -/
theorem harmonicFactor_smul (χ : Grossencharacter K 𝔪) (c : ℝ) (x : mixedSpace K) :
    χ.harmonicFactor (c • x) = (c : ℂ) ^ χ.harmonicDegree * χ.harmonicFactor x := by
  classical
  have hsmul : c • x = mixedSpaceOfRealSpace (fun _ ↦ c) * x := by
    ext w <;> simp [mixedSpaceOfRealSpace_apply]
  rw [hsmul, harmonicFactor_mixedSpaceOfRealSpace_mul, Finset.prod_pow_eq_pow_sum,
    ← harmonicDegree_def, ofReal_pow]

/-- Under negation on `mixedSpace K`, `harmonicFactor` transforms by `(-1) ^ harmonicDegree`. -/
theorem harmonicFactor_neg (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor (-x) = (-1 : ℂ) ^ χ.harmonicDegree * χ.harmonicFactor x := by
  simpa using χ.harmonicFactor_smul (-1 : ℝ) x

/-- Under the action of a unit `u : (𝓞 K)ˣ` on `mixedSpace K`, `harmonicFactor` multiplies by
`harmonicFactor (mixedEmbedding K u)`. -/
theorem harmonicFactor_unit_smul (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    χ.harmonicFactor (u • x) =
      χ.harmonicFactor (mixedEmbedding K (u : K)) * χ.harmonicFactor x := by
  rw [unitSMul_smul, harmonicFactor_mul]

/-- The complex norm of `harmonicFactor x` is `∏_w normAtPlace w x ^ harmonicExponent w`. -/
theorem norm_harmonicFactor (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    ‖χ.harmonicFactor x‖ = ∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w := by
  classical
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial, norm_mul, norm_prod, norm_prod,
    prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [norm_pow, norm_real, ← normAtPlace_apply_of_isReal w.2, χ.harmonicExponent_of_isReal w.2]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [norm_complexHarmonicMonomial, normAtPlace_apply_of_isComplex w.2]

/-! ### Temperate growth and the weighted Schwartz Gaussian -/

open scoped Classical in
/-- `harmonicFactor` has temperate growth on `mixedSpace K`. -/
@[fun_prop]
theorem hasTemperateGrowth_harmonicFactor (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor.HasTemperateGrowth := by
  rw [funext χ.harmonicFactor_eq_prod_complexHarmonicMonomial]
  refine (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ ?_).mul
    (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ ?_)
  · let L : mixedSpace K →L[ℝ] ℂ :=
      (ofRealCLM.comp (ContinuousLinearMap.proj w)).comp
        (ContinuousLinearMap.fst ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
          ({v : InfinitePlace K // v.IsComplex} → ℂ))
    exact L.hasTemperateGrowth.pow _
  · let L : mixedSpace K →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj w).comp
        (ContinuousLinearMap.snd ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
          ({v : InfinitePlace K // v.IsComplex} → ℂ))
    dsimp only [complexHarmonicMonomial]
    split_ifs
    · exact (conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth.pow _
    · exact L.hasTemperateGrowth.pow _

open scoped Classical in
/-- `harmonicFactor` is smooth (`C^∞`) over `ℝ`. -/
@[fun_prop]
theorem contDiff_harmonicFactor (χ : Grossencharacter K 𝔪) :
    ContDiff ℝ (⊤ : ℕ∞) χ.harmonicFactor :=
  χ.hasTemperateGrowth_harmonicFactor.1

open scoped Classical in
/-- **The harmonic-weighted archimedean Gaussian as a Schwartz function** on `mixedSpace K`, for
positive parameters `y`. -/
def harmonicFactorMulGaussianSchwartz (χ : Grossencharacter K 𝔪) (y : realSpace K)
    (hy : ∀ w, 0 < y w) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ χ.harmonicFactor (archGaussianSchwartz y hy)

open scoped Classical in
/-- Evaluation of `harmonicFactorMulGaussianSchwartz`. -/
@[simp]
theorem harmonicFactorMulGaussianSchwartz_apply (χ : Grossencharacter K 𝔪) (y : realSpace K)
    (hy : ∀ w, 0 < y w) (x : mixedSpace K) :
    χ.harmonicFactorMulGaussianSchwartz y hy x = χ.harmonicFactor x * archGaussian y x := by
  rw [harmonicFactorMulGaussianSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth_harmonicFactor,
    archGaussianSchwartz_apply, smul_eq_mul]

/-- Absolute convergence of `harmonicFactor * archGaussian y` over any discrete lattice of the
mixed space. -/
theorem summable_harmonicFactor_mul_archGaussian (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K)
    (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ χ.harmonicFactor x * archGaussian y x := by
  classical
  simpa using ZLattice.summable_poisson_left L (χ.harmonicFactorMulGaussianSchwartz y hy) 0

/-- Absolute convergence in norm of `harmonicFactor * archGaussian y` over any discrete lattice of
the mixed space. -/
theorem summable_norm_harmonicFactor_mul_archGaussian (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K)
    (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ ‖χ.harmonicFactor x * archGaussian y x‖ :=
  summable_norm_iff.mpr (χ.summable_harmonicFactor_mul_archGaussian L y hy)

/-! ### Hecke's lemma: Fourier transform of the harmonic-weighted Gaussian -/

/-- One real-place factor of Hecke's lemma at parameter `1`. -/
private theorem fourier_realFactor_one (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (η : ℝ) :
    (∫ t : ℝ, cexp ((-2 * π * (t * η) : ℝ) * I) *
        ((t : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
          cexp (-(π : ℂ) * (t : ℂ) ^ 2))) =
      (-I) ^ χ.harmonicExponent w.1 *
        ((η : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
          cexp (-(π : ℂ) * (η : ℂ) ^ 2)) := by
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hε : (χ.toHeckeCharacter.infinityType.realParity w).val ≤ 1 :=
    Nat.lt_succ_iff.mp (ZMod.val_lt _)
  have hint : (fun t : ℝ ↦ cexp ((-2 * π * (t * η) : ℝ) * I) *
        ((t : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
          cexp (-(π : ℂ) * (t : ℂ) ^ 2))) =
      fun t : ℝ ↦ cexp ((-2 * π * ⟪t, η⟫ : ℝ) * I) •
        ((t : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
          cexp (-(π : ℂ) * (t : ℂ) ^ 2)) := by
    ext t
    simp [mul_comm t η]
  rw [hint, ← Real.fourier_eq', TauCeti.fourier_pow_mul_cexp_neg_mul_sq_of_le_one hb hε η,
    div_self hπ0, one_cpow, one_mul, χ.harmonicExponent_of_isReal w.2]
  have hexp : -(π : ℂ) ^ 2 * (η : ℂ) ^ 2 / (π : ℂ) = -(π : ℂ) * (η : ℂ) ^ 2 := by
    field_simp
  rw [hexp, mul_assoc]

/-- One complex-place factor of Hecke's lemma at parameter `1`. -/
private theorem fourier_complexFactor_one (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (ζ : ℂ) :
    (∫ z : ℂ, cexp ((-2 * π * (z * conj ζ).re : ℝ) * I) *
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2))) =
      (-I) ^ χ.harmonicExponent w.1 *
        (complexHarmonicMonomial χ w ζ * cexp (-(π : ℂ) * ‖ζ‖ ^ 2)) := by
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinner (z : ℂ) : (z * conj ζ).re = ⟪z, ζ⟫ := by
    simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply, RCLike.re_to_complex,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hint : (fun z : ℂ ↦ cexp ((-2 * π * (z * conj ζ).re : ℝ) * I) *
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2))) =
      fun z : ℂ ↦ cexp ((-2 * π * ⟪z, ζ⟫ : ℝ) * I) •
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2)) := by
    ext z
    rw [hinner, smul_eq_mul]
  have hexp : -(π : ℂ) ^ 2 * ‖ζ‖ ^ 2 / (π : ℂ) = -(π : ℂ) * ‖ζ‖ ^ 2 := by
    field_simp
  rw [hint, ← Real.fourier_eq', χ.harmonicExponent_of_isComplex w.2]
  dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · have hk' : k.toNat = k.natAbs := by omega
    rw [TauCeti.fourier_conj_pow_mul_cexp_neg_mul_norm_sq hb k.toNat ζ, div_self hπ0, one_pow,
      one_mul, hexp, hk', mul_assoc]
  · have hk' : (-k).toNat = k.natAbs := by omega
    rw [TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq hb (-k).toNat ζ, div_self hπ0, one_pow,
      one_mul, hexp, hk', mul_assoc]

open scoped Classical in
/-- Factorization of `archGaussian 1 x` into real-place and complex-place complex exponentials. -/
private theorem archGaussian_one_eq_prod_mul_prod (x : mixedSpace K) :
    archGaussian 1 x =
      (∏ w : {w : InfinitePlace K // w.IsReal}, cexp (-(π : ℂ) * (x.1 w : ℂ) ^ 2)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, cexp (-(π : ℂ) * ‖x.2 w‖ ^ 2) := by
  rw [archGaussian_apply, Finset.mul_sum, Real.exp_sum, ofReal_prod, prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Pi.one_apply, one_mul, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, sq_abs,
      ofReal_exp]
    push_cast
    rfl
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Pi.one_apply, one_mul, normAtPlace_apply_of_isComplex w.2, ofReal_exp]
    push_cast
    rfl

open scoped Classical in
/-- **Hecke's lemma at the unit parameter `1`**: the harmonic polynomial times `archGaussian 1` is
an eigenfunction of `mixedFourier K` with eigenvalue `(-i) ^ harmonicDegree`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian_one (χ : Grossencharacter K 𝔪)
    (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian 1 x) ξ =
      (-I) ^ χ.harmonicDegree * χ.harmonicFactor ξ * archGaussian 1 ξ := by
  -- Factor the Fourier integrand across the real and complex coordinates.
  set fR : ({w : InfinitePlace K // w.IsReal} → ℝ) → ℂ := fun x₁ ↦
    ∏ w, cexp ((-2 * π * (x₁ w * ξ.1 w) : ℝ) * I) *
      ((x₁ w : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
        cexp (-(π : ℂ) * (x₁ w : ℂ) ^ 2))
  set fC : ({w : InfinitePlace K // w.IsComplex} → ℂ) → ℂ := fun x₂ ↦
    ∏ w, cexp ((-2 * π * (x₂ w * conj (ξ.2 w)).re : ℝ) * I) *
      (complexHarmonicMonomial χ w (x₂ w) * cexp (-(π : ℂ) * ‖x₂ w‖ ^ 2))
  have hfactor (x : mixedSpace K) :
      𝐞 (-mixedInner K x ξ) • (χ.harmonicFactor x * archGaussian 1 x) = fR x.1 * fC x.2 := by
    have hchar : (𝐞 (-mixedInner K x ξ) : ℂ) =
        (∏ w : {w : InfinitePlace K // w.IsReal}, cexp ((-2 * π * (x.1 w * ξ.1 w) : ℝ) * I)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            cexp ((-2 * π * (x.2 w * conj (ξ.2 w)).re : ℝ) * I) := by
      rw [Real.fourierChar_apply, mixedInner_def, mul_neg, neg_mul, mul_add, neg_add,
        ofReal_add, add_mul, Complex.exp_add]
      congr 1
      · simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ofReal_sum, Finset.sum_mul,
          Complex.exp_sum, neg_mul]
      · simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ofReal_sum, Finset.sum_mul,
          Complex.exp_sum, neg_mul]
    rw [Circle.smul_def, smul_eq_mul, hchar, harmonicFactor_eq_prod_complexHarmonicMonomial,
      archGaussian_one_eq_prod_mul_prod]
    dsimp only [fR, fC]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [mixedFourier_apply]
  simp_rw [hfactor]
  rw [Measure.volume_eq_prod, integral_prod_mul fR fC]
  dsimp only [fR, fC]
  rw [integral_fintype_prod_volume_eq_prod (fun (w : {w : InfinitePlace K // w.IsReal}) (t : ℝ) ↦
      cexp ((-2 * π * (t * ξ.1 w) : ℝ) * I) *
        ((t : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val *
          cexp (-(π : ℂ) * (t : ℂ) ^ 2))),
    integral_fintype_prod_volume_eq_prod (fun (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) ↦
      cexp ((-2 * π * (z * conj (ξ.2 w)).re : ℝ) * I) *
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2)))]
  simp_rw [fourier_realFactor_one, fourier_complexFactor_one, Finset.prod_mul_distrib]
  have hdeg : (-I) ^ χ.harmonicDegree =
      (∏ w : {w : InfinitePlace K // w.IsReal}, (-I) ^ χ.harmonicExponent w.1) *
        (∏ w : {w : InfinitePlace K // w.IsComplex}, (-I) ^ χ.harmonicExponent w.1) := by
    rw [harmonicDegree_def, ← Finset.prod_pow_eq_pow_sum, prod_eq_prod_mul_prod]
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial, archGaussian_one_eq_prod_mul_prod, hdeg]
  ring

/-- **Hecke's lemma** (Neukirch VII (3.5)–(3.6) and §7): for positive parameters `y : realSpace K`,
the Fourier transform of `x ↦ χ.harmonicFactor x * archGaussian y x` on the mixed space is
`(-i) ^ (Tr p) * N(y) ^ (-1/2) * (∏_w y_w ^ (-P_w)) * χ.harmonicFactor ξ * archGaussian y⁻¹ ξ`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian (χ : Grossencharacter K 𝔪)
    (y : realSpace K) (hy : ∀ w, 0 < y w) (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian y x) ξ =
      (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) *
        χ.harmonicFactor ξ * archGaussian y⁻¹ ξ := by
  have hy' : ∀ w, 0 < y⁻¹ w := fun w ↦ inv_pos.mpr (hy w)
  set c : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y w)
  set c' : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y⁻¹ w)
  have hcc' : c * c' = 1 := by
    ext w <;> simp [c, c', mixedSpaceOfRealSpace_apply, (Real.sqrt_pos.mpr (hy _)).ne']
  have hc : mixedEmbedding.norm c = √(archNorm y) :=
    norm_mixedSpaceOfRealSpace_sqrt fun w ↦ (hy w).le
  have hc0 : mixedEmbedding.norm c ≠ 0 := by
    rw [hc]
    exact (Real.sqrt_pos.mpr (archNorm_pos hy)).ne'
  -- Substitute `x = c' * (c * x)` in `harmonicFactor` and `archGaussian`.
  have hint (x : mixedSpace K) :
      𝐞 (-mixedInner K x ξ) • (χ.harmonicFactor x * archGaussian y x) =
        χ.harmonicFactor c' *
          (𝐞 (-mixedInner K (c * x) (c' * ξ)) •
            (χ.harmonicFactor (c * x) * archGaussian 1 (c * x))) := by
    have hx : x = c' * (c * x) := by rw [← mul_assoc, mul_comm c' c, hcc', one_mul]
    have hinner : mixedInner K x ξ = mixedInner K (c * x) (c' * ξ) := by
      have hξ : c * (c' * ξ) = ξ := by rw [← mul_assoc, hcc', one_mul]
      conv_lhs => rw [← hξ]
      exact (mixedInner_mixedSpaceOfRealSpace_mul K (fun w ↦ √(y w)) x (c' * ξ)).symm
    have hharm : χ.harmonicFactor x = χ.harmonicFactor c' * χ.harmonicFactor (c * x) := by
      conv_lhs => rw [hx]
      exact χ.harmonicFactor_mul c' (c * x)
    have hgauss : archGaussian y x = archGaussian 1 (c * x) := by
      rw [← archGaussian_one_archGaussianDilation y hy, archGaussianDilation_apply]
    rw [hinner, hharm, hgauss, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul]
    ring
  have hc'_sq : χ.harmonicFactor c' * χ.harmonicFactor c' =
      ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) := by
    rw [harmonicFactor_mixedSpaceOfRealSpace, ← ofReal_mul, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← mul_pow, Real.mul_self_sqrt (hy' w).le, Pi.inv_apply]
  rw [mixedFourier_apply]
  simp_rw [hint]
  rw [integral_const_mul,
    integral_comp_mul_left
      (fun z ↦ 𝐞 (-mixedInner K z (c' * ξ)) • (χ.harmonicFactor z * archGaussian 1 z)) hc0,
    ← mixedFourier_apply, mixedFourier_harmonicFactor_mul_archGaussian_one,
    harmonicFactor_mul, ← archGaussianDilation_apply y⁻¹ hy',
    archGaussian_one_archGaussianDilation, hc, Complex.real_smul]
  linear_combination
    (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) * χ.harmonicFactor ξ *
      archGaussian y⁻¹ ξ * hc'_sq

/-! ### Constant-term indicator of the twisted theta series -/

/-- **Neukirch's constant-term indicator `ε(χ)`** for the twisted theta series: `1` when both the
finite conductor `χ.toHeckeCharacter.finiteConductor` is trivial (`⊤`) and `harmonicDegree` is `0`,
and `0` otherwise. Note that this tests `finiteConductor = ⊤` and `harmonicDegree = 0` rather than
triviality of the presentation conductor, because an unramified odd norm power over `ℚ` has
nontrivial presentation conductor at `∞` yet still has constant term `1`. -/
def heckeEpsilon (χ : Grossencharacter K 𝔪) : ℂ :=
  if χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 then 1 else 0

/-- Defining formula for `heckeEpsilon`. -/
theorem heckeEpsilon_def (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon =
      if χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 then 1 else 0 :=
  (rfl)

/-- `heckeEpsilon` equals `1` if and only if the finite conductor is trivial and `harmonicDegree`
vanishes. -/
theorem heckeEpsilon_eq_one_iff (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon = 1 ↔ χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 := by
  simp [heckeEpsilon_def]

/-- `heckeEpsilon` vanishes if and only if either the finite conductor is nontrivial or
`harmonicDegree` is nonzero. -/
theorem heckeEpsilon_eq_zero_iff (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon = 0 ↔ χ.toHeckeCharacter.finiteConductor ≠ ⊤ ∨ χ.harmonicDegree ≠ 0 := by
  rw [heckeEpsilon_def, ite_eq_right_iff]
  simp only [one_ne_zero, imp_false, not_and_or]

/-- A nontrivial finite conductor forces `heckeEpsilon = 0`. -/
theorem heckeEpsilon_eq_zero_of_finiteConductor_ne_top {χ : Grossencharacter K 𝔪}
    (h : χ.toHeckeCharacter.finiteConductor ≠ ⊤) : χ.heckeEpsilon = 0 :=
  (heckeEpsilon_eq_zero_iff χ).mpr (Or.inl h)

/-- A nonzero harmonic degree forces `heckeEpsilon = 0`. -/
theorem heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree ≠ 0) : χ.heckeEpsilon = 0 :=
  (heckeEpsilon_eq_zero_iff χ).mpr (Or.inr h)

/-- `heckeEpsilon` depends only on the presented Hecke character, not on the modulus. -/
theorem heckeEpsilon_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.heckeEpsilon = ψ.heckeEpsilon := by
  simp [heckeEpsilon_def, h, harmonicDegree_congr h]

/-- Inverting a presentation preserves `heckeEpsilon`. -/
@[simp]
theorem heckeEpsilon_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.heckeEpsilon = χ.heckeEpsilon := by
  simp [heckeEpsilon_def]

/-- Any presentation of the trivial Hecke character has `heckeEpsilon = 1`. -/
theorem heckeEpsilon_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) : χ.heckeEpsilon = 1 := by
  rw [heckeEpsilon_eq_one_iff]
  exact ⟨by simp [hχ], harmonicDegree_of_toHeckeCharacter_eq_one hχ⟩

/-- The trivial ray class character at the trivial modulus has `heckeEpsilon = 1`. -/
@[simp]
theorem heckeEpsilon_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeEpsilon = 1 :=
  heckeEpsilon_of_toHeckeCharacter_eq_one (by simp)

end TauCeti.LFunctions.Grossencharacter
