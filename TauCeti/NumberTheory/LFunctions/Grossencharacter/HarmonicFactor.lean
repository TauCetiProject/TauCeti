/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.Theta.Inversion
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.UnitCompatibility

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
* `Grossencharacter.harmonicDegree` is the total degree `Tr(p) = ∑_w P_w`; under radial scaling on
  the norm-one surface it shifts the radial Mellin variable `s / 2` by `Tr(p) / (2 [K : ℚ])` (and
  `s` by `Tr(p) / [K : ℚ]`).
* `Grossencharacter.harmonicFactor` is the coordinatewise multiplicative polynomial `N(x^p)` on
  `mixedSpace K`: `x_w ^ ε_w` at each real place and `conj(z_w) ^ k_w` (for `k_w ≥ 0`) or
  `z_w ^ (-k_w)` (for `k_w < 0`) at each complex place of angular frequency `k_w`
  (`n w.embedding - n (conjugate w.embedding)`).
  Because `compatibility` equates the ideal-side value with the inverse of `∏_τ τ(a) ^ (n τ)`, a
  positive angular frequency puts the conjugate coordinate into `harmonicFactor`.
* `Grossencharacter.prod_infiniteComponent_mul_harmonicFactor_mixedEmbedding`,
  `Grossencharacter.prod_infiniteComponent_mul_harmonicFactor_unit`,
  `Grossencharacter.harmonicFactor_mixedEmbedding_of_isCongrOne`, and
  `Grossencharacter.harmonicFactor_mixedEmbedding_unit_of_mem_unitsCongruenceSubgroup`: on global
  elements `x : Kˣ` and units `u : (𝓞 K)ˣ`, multiplying `harmonicFactor` by the archimedean
  components cancels all sign and angular factors to leave the placewise norm power
  `∏_w w(x) ^ P_w` (times `|N(x)| ^ (-idealShift)` on `Kˣ`), and on generators `a ≡ 1 mod* 𝔪`
  evaluates `harmonicFactor` as `χ_u((a)) * ∏_w w(a) ^ P_w`.
* `Grossencharacter.harmonicFactorMulGaussianSchwartz` bundles `harmonicFactor * archGaussian y`
  into a Schwartz function on `mixedSpace K` for positive parameters `y`, giving absolute
  summability over every discrete lattice.
* `Grossencharacter.mixedFourier_harmonicFactor_mul_archGaussian` (**Hecke's lemma**): for positive
  parameters `y`, the mixed-space Fourier transform of `x ↦ χ.harmonicFactor x * archGaussian y x`
  is `(-i) ^ (Tr p) * N(y) ^ (-1/2) * (∏_w y_w ^ (-P_w)) * χ.harmonicFactor ξ * archGaussian y⁻¹ ξ`,
  generalizing the unweighted Gaussian transform `TauCeti.LFunctions.mixedFourier_archGaussian` via
  the single-place harmonic Gaussian transforms of
  `TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic`.
* `Grossencharacter.heckeEpsilon` is the constant-term indicator `ε(χ)` of the twisted theta
  series, equal to `1` when both the finite conductor is trivial and `harmonicDegree` vanishes, and
  `0` otherwise.

Because the real parities of `χ.toHeckeCharacter.infinityType` and the algebraic infinity type
`χ.infinityType` depend only on `χ.toHeckeCharacter`, every invariant in this file is independent
of the modulus of presentation (`harmonicExponent_congr`, `harmonicDegree_congr`,
`harmonicFactor_congr`, `heckeEpsilon_congr`). Under `Grossencharacter.inverse`, the exponents,
total degree, and constant-term indicator are unchanged while `harmonicFactor` is complex
conjugated.

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
  classical simp [harmonicExponent, hw]

/-- At a complex place, `harmonicExponent` is the absolute angular frequency `|k_w|`. -/
@[simp]
theorem harmonicExponent_of_isComplex (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    χ.harmonicExponent w =
      ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
        ⟨w, hw⟩).natAbs := by
  classical simp [harmonicExponent, not_isReal_iff_isComplex.mpr hw]

/-- At a real place, the harmonic exponent is at most `1`. -/
theorem harmonicExponent_le_one_of_isReal (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsReal) : χ.harmonicExponent w ≤ 1 :=
  harmonicExponent_of_isReal χ hw ▸ Nat.lt_succ_iff.mp (ZMod.val_lt _)

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
  · simp [hw, (by decide : ∀ a : ZMod 2, -a = a)]
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
  rw [harmonicExponent_of_isReal _ w.2, (ofRayClassCharacter η).realParity_eq w hw]; simp

/-- At a modulus with empty infinite part, a ray class character has zero harmonic exponents. -/
theorem harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) (w : InfinitePlace K) :
    (ofRayClassCharacter η).harmonicExponent w = 0 := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact harmonicExponent_ofRayClassCharacter_of_notMem_infinitePart η ⟨w, hw⟩ (by simp [h𝔪])
  · exact harmonicExponent_ofRayClassCharacter_of_isComplex η hw

/-- A ray class character at the trivial modulus has harmonic exponent `0` everywhere. -/
@[simp]
theorem harmonicExponent_ofRayClassCharacter_of_modulus_one
    (η : RayClassCharacter (Modulus.one K)) (w : InfinitePlace K) :
    (ofRayClassCharacter η).harmonicExponent w = 0 :=
  harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η w

/-- Any presentation of the trivial Hecke character has harmonic exponent `0` everywhere. -/
theorem harmonicExponent_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (w : InfinitePlace K) : χ.harmonicExponent w = 0 := by
  have h1 : χ.toHeckeCharacter =
      (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).toHeckeCharacter := by
    simp [hχ]
  rw [congrFun (harmonicExponent_congr h1) w, harmonicExponent_ofRayClassCharacter_of_modulus_one]

/-- The trivial ray class character at any modulus has harmonic exponent `0` everywhere. -/
@[simp]
theorem harmonicExponent_ofRayClassCharacter_one (w : InfinitePlace K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicExponent w = 0 :=
  harmonicExponent_of_toHeckeCharacter_eq_one (by simp) w

open scoped Classical in
/-- **The total harmonic degree `Tr(p)`** of a presentation `χ`: the sum of `harmonicExponent`
over all infinite places, equal to the number of odd real places plus `∑_{w complex} |k_w|`.
Under radial scaling on the norm-one surface, it shifts `s` by `Tr(p) / [K : ℚ]` (the radial Mellin
variable `s / 2` by `Tr(p) / (2 [K : ℚ])`). -/
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
  exact congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ χ.harmonicExponent_of_isReal w.2)
    (Finset.sum_congr rfl fun w _ ↦ χ.harmonicExponent_of_isComplex w.2)

/-- The total harmonic degree vanishes if and only if every harmonic exponent vanishes. -/
theorem harmonicDegree_eq_zero_iff (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = 0 ↔ ∀ w, χ.harmonicExponent w = 0 := by
  classical simp [harmonicDegree_def]

/-- `harmonicDegree` depends only on the presented Hecke character, not on the modulus. -/
theorem harmonicDegree_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicDegree = ψ.harmonicDegree := by
  classical simp_rw [harmonicDegree_def, harmonicExponent_congr h]

/-- Inverting a presentation preserves `harmonicDegree`. -/
@[simp]
theorem harmonicDegree_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.harmonicDegree = χ.harmonicDegree := by
  classical simp [harmonicDegree_def]

/-- At a modulus with empty infinite part, every ray class character has harmonic degree `0`. -/
theorem harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter η).harmonicDegree = 0 :=
  (harmonicDegree_eq_zero_iff _).mpr
    (harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η)

/-- At the trivial modulus, every ray class character has harmonic degree `0`. -/
@[simp]
theorem harmonicDegree_ofRayClassCharacter_of_modulus_one
    (η : RayClassCharacter (Modulus.one K)) :
    (ofRayClassCharacter η).harmonicDegree = 0 :=
  harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η

/-- Any presentation of the trivial Hecke character has harmonic degree `0`. -/
theorem harmonicDegree_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) : χ.harmonicDegree = 0 :=
  (harmonicDegree_eq_zero_iff χ).mpr (harmonicExponent_of_toHeckeCharacter_eq_one hχ)

/-- The trivial ray class character at any modulus has harmonic degree `0`. -/
@[simp]
theorem harmonicDegree_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicDegree = 0 :=
  harmonicDegree_of_toHeckeCharacter_eq_one (by simp)

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

private theorem complexHarmonicMonomial_inv (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) :
    complexHarmonicMonomial χ w z⁻¹ = (complexHarmonicMonomial χ w z)⁻¹ := by
  dsimp only [complexHarmonicMonomial]
  split_ifs <;> simp [inv_pow]

private theorem complexHarmonicMonomial_ofReal (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (r : ℝ) :
    complexHarmonicMonomial χ w (r : ℂ) = ((r ^ χ.harmonicExponent w.1 : ℝ) : ℂ) := by
  rw [harmonicExponent_of_isComplex χ w.2]; dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · rw [conj_ofReal, (by omega : k.toNat = k.natAbs), ofReal_pow]
  · rw [(by omega : (-k).toNat = k.natAbs), ofReal_pow]

private theorem norm_complexHarmonicMonomial (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) :
    ‖complexHarmonicMonomial χ w z‖ = ‖z‖ ^ χ.harmonicExponent w.1 := by
  rw [harmonicExponent_of_isComplex χ w.2]; dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · rw [norm_pow, norm_conj, (by omega : k.toNat = k.natAbs)]
  · rw [norm_pow, (by omega : (-k).toNat = k.natAbs)]

private theorem complexHarmonicMonomial_inverse (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂ) :
    complexHarmonicMonomial χ.inverse w z = conj (complexHarmonicMonomial χ w z) := by
  dsimp only [complexHarmonicMonomial]
  rw [infinityType_inverse, map_neg, ContinuousInfinityType.neg_complexAngularFrequency,
    Pi.neg_apply, neg_neg]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with h1 h2
  · simp [(by omega : k = 0)]
  · rw [map_pow]
  · rw [map_pow, conj_conj]
  · omega

private theorem div_norm_zpow_mul_complexHarmonicMonomial (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) {z : ℂ} (hz0 : z ≠ 0) :
    (z / ‖z‖) ^ ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w) *
      complexHarmonicMonomial χ w z =
      ((‖z‖ ^ χ.harmonicExponent w.1 : ℝ) : ℂ) := by
  have hnorm0 : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)
  rw [χ.harmonicExponent_of_isComplex w.2]; dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk0
  · have hpow : (z / ‖z‖) ^ k = (z / ‖z‖) ^ k.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hk0]
    have hzc : z / ‖z‖ * conj z = (‖z‖ : ℂ) := by
      rw [div_mul_eq_mul_div, mul_conj, normSq_eq_norm_sq, ofReal_pow, sq,
        mul_div_cancel_right₀ _ hnorm0]
    rw [hpow, ← mul_pow, hzc, (by omega : k.toNat = k.natAbs), ofReal_pow]
  · have hpow : (z / ‖z‖) ^ k = (z / ‖z‖)⁻¹ ^ (-k).toNat := by
      conv_lhs => rw [(by omega : k = -((-k).toNat : ℤ))]
      rw [zpow_neg, zpow_natCast, ← inv_pow]
    have hzc : (z / ‖z‖)⁻¹ * z = (‖z‖ : ℂ) := by rw [inv_div, div_mul_cancel₀ _ hz0]
    rw [hpow, ← mul_pow, hzc, (by omega : (-k).toNat = k.natAbs), ofReal_pow]

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
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial]; simp [complexHarmonicMonomial_one]

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

/-- `harmonicFactor` commutes with coordinatewise inversion on `mixedSpace K`. -/
theorem harmonicFactor_inv (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x⁻¹ = (χ.harmonicFactor x)⁻¹ := by
  classical
  simp only [harmonicFactor_eq_prod_complexHarmonicMonomial, Prod.fst_inv, Prod.snd_inv,
    Pi.inv_apply, ofReal_inv, inv_pow, complexHarmonicMonomial_inv, Finset.prod_inv_distrib,
    mul_inv]

/-- `harmonicFactor` depends only on the presented Hecke character, not on the modulus. -/
theorem harmonicFactor_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicFactor = ψ.harmonicFactor := by
  classical
  ext x; simp [harmonicFactor_def, h, infinityType_congr h]

/-- Inverting a presentation conjugates its harmonic polynomial pointwise. -/
@[simp]
theorem harmonicFactor_inverse (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.inverse.harmonicFactor x = conj (χ.harmonicFactor x) := by
  classical
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  rw [harmonicFactor_eq_prod_complexHarmonicMonomial,
    harmonicFactor_eq_prod_complexHarmonicMonomial, map_mul, map_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ by simp [hneg]
  · exact Finset.prod_congr rfl fun w _ ↦ complexHarmonicMonomial_inverse χ w (x.2 w)

/-- When `harmonicDegree` vanishes, `harmonicFactor` is identically `1`. -/
theorem harmonicFactor_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (x : mixedSpace K) : χ.harmonicFactor x = 1 := by
  classical
  have hw := (harmonicDegree_eq_zero_iff χ).mp h
  have hR (w : {w : InfinitePlace K // w.IsReal}) :
      (χ.toHeckeCharacter.infinityType.realParity w).val = 0 := by simpa [w.2] using hw w.1
  have hC (w : {w : InfinitePlace K // w.IsComplex}) :
      (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w = 0 :=
    Int.natAbs_eq_zero.mp (by simpa [w.2] using hw w.1)
  rw [harmonicFactor_def]; simp [hR, hC]

/-- At a modulus with empty infinite part, a ray class character has trivial `harmonicFactor`. -/
theorem harmonicFactor_ofRayClassCharacter_of_infinitePart_eq_empty
    (h𝔪 : 𝔪.infinitePart = ∅) (η : RayClassCharacter 𝔪) (x : mixedSpace K) :
    (ofRayClassCharacter η).harmonicFactor x = 1 :=
  harmonicFactor_of_harmonicDegree_eq_zero
    (harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η) x

/-- At the trivial modulus, a ray class character has trivial `harmonicFactor`. -/
@[simp]
theorem harmonicFactor_ofRayClassCharacter_of_modulus_one (η : RayClassCharacter (Modulus.one K))
    (x : mixedSpace K) :
    (ofRayClassCharacter η).harmonicFactor x = 1 :=
  harmonicFactor_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η x

/-- Any presentation of the trivial Hecke character has `harmonicFactor` identically `1`. -/
theorem harmonicFactor_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (x : mixedSpace K) : χ.harmonicFactor x = 1 :=
  harmonicFactor_of_harmonicDegree_eq_zero (harmonicDegree_of_toHeckeCharacter_eq_one hχ) x

/-- The trivial ray class character at any modulus has `harmonicFactor` identically `1`. -/
@[simp]
theorem harmonicFactor_ofRayClassCharacter_one (x : mixedSpace K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicFactor x = 1 :=
  harmonicFactor_of_toHeckeCharacter_eq_one (by simp) x

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

/-- When `harmonicDegree` is nonzero, `harmonicFactor` vanishes at the origin. -/
theorem harmonicFactor_zero_of_harmonicDegree_ne_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree ≠ 0) : χ.harmonicFactor 0 = 0 := by
  simpa [zero_pow h] using χ.harmonicFactor_smul 0 1

/-- At the origin, `harmonicFactor 0` is `1` if `harmonicDegree = 0` and `0` otherwise. -/
@[simp]
theorem harmonicFactor_zero (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor 0 = if χ.harmonicDegree = 0 then 1 else 0 := by
  split_ifs with h
  · exact harmonicFactor_of_harmonicDegree_eq_zero h 0
  · exact harmonicFactor_zero_of_harmonicDegree_ne_zero h

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

/-- On `K`, `harmonicFactor` commutes with inversion through `mixedEmbedding K`. -/
theorem harmonicFactor_mixedEmbedding_inv (χ : Grossencharacter K 𝔪) (x : K) :
    χ.harmonicFactor (mixedEmbedding K x⁻¹) = (χ.harmonicFactor (mixedEmbedding K x))⁻¹ := by
  have hinv : mixedEmbedding K x⁻¹ = (mixedEmbedding K x)⁻¹ := by
    ext w <;> simp
  rw [hinv, χ.harmonicFactor_inv]

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

/-! ### Compatibility with the archimedean components and principal ideals -/

private theorem infiniteComponent_mul_realFactor (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    (χ.toHeckeCharacter.infiniteComponent w.1
        (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) *
      (((mixedEmbedding K (x : K)).1 w : ℝ) : ℂ) ^
        (χ.toHeckeCharacter.infinityType.realParity w).val =
      (w.1 (x : K) : ℂ) ^ ((mult w.1 : ℂ) * (-χ.idealShift : ℂ)) *
        ((w.1 (x : K) ^ χ.harmonicExponent w.1 : ℝ) : ℂ) := by
  set uR := Units.map (InfinitePlace.embedding_of_isReal w.2).toMonoidHom x
  set ε := χ.toHeckeCharacter.infinityType.realParity w
  have ht : (mixedEmbedding K (x : K)).1 w = (uR : ℝ) := by simp [uR]
  have habs : |(uR : ℝ)| = w.1 (x : K) := by
    simpa [uR, Real.norm_eq_abs] using norm_embedding_of_isReal w.2 (x : K)
  have hsign : (SignType.sign (uR : ℝ) : ℂ) ^ ε.val * ((uR : ℝ) : ℂ) ^ ε.val =
      ((|(uR : ℝ)| ^ ε.val : ℝ) : ℂ) := by
    rw [← mul_pow, ofReal_pow]; congr 1
    rcases lt_or_gt_of_ne uR.ne_zero with hlt | hgt
    · simp [sign_neg hlt, abs_of_neg hlt]
    · simp [sign_pos hgt, abs_of_pos hgt]
  rw [HeckeCharacter.infiniteComponent_map_algebraMap_eq_realComponent,
    HeckeCharacter.realComponent_eq, χ.realExponent_toHeckeCharacter w,
    TauCeti.coe_realUnitsCharacter_apply, ht, mul_assoc, hsign, habs, mult_isReal w,
    Nat.cast_one, one_mul, χ.harmonicExponent_of_isReal w.2]

private theorem infiniteComponent_mul_complexFactor (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.toHeckeCharacter.infiniteComponent w.1
        (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) *
      complexHarmonicMonomial χ w ((mixedEmbedding K (x : K)).2 w) =
      (w.1 (x : K) : ℂ) ^ ((mult w.1 : ℂ) * (-χ.idealShift : ℂ)) *
        ((w.1 (x : K) ^ χ.harmonicExponent w.1 : ℝ) : ℂ) := by
  set uC := Units.map w.1.embedding.toMonoidHom x
  have hz_eq : (mixedEmbedding K (x : K)).2 w = (uC : ℂ) := by simp [uC]
  have hnorm : ‖(uC : ℂ)‖ = w.1 (x : K) := by simpa [uC] using norm_embedding_eq w.1 (x : K)
  rw [HeckeCharacter.infiniteComponent_map_algebraMap_eq_complexComponent,
    HeckeCharacter.complexComponent_eq, χ.complexExponent_toHeckeCharacter w,
    χ.complexAngularFrequency_toHeckeCharacter w, TauCeti.coe_complexUnitsCharacter_apply,
    hz_eq, mul_assoc, div_norm_zpow_mul_complexHarmonicMonomial χ w uC.ne_zero, hnorm,
    mult_isComplex w, Nat.cast_ofNat]

/-- **Archimedean compatibility of `harmonicFactor` on `Kˣ`.** Multiplying the product of the
archimedean components of `χ` at `x : Kˣ` by `χ.harmonicFactor (mixedEmbedding K x)` cancels all
real sign parities and complex angular frequencies, leaving `|N(x)| ^ (-idealShift)` times the
placewise norm power `∏_w w(x) ^ harmonicExponent w`. -/
theorem prod_infiniteComponent_mul_harmonicFactor_mixedEmbedding (χ : Grossencharacter K 𝔪)
    (x : Kˣ) :
    ((∏ w : InfinitePlace K,
        χ.toHeckeCharacter.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) *
      χ.harmonicFactor (mixedEmbedding K (x : K)) =
      ((mixedEmbedding.norm (mixedEmbedding K (x : K)) : ℝ) : ℂ) ^ (-χ.idealShift : ℂ) *
        ((∏ w : InfinitePlace K, w (x : K) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  classical
  have hnorm :
      ((mixedEmbedding.norm (mixedEmbedding K (x : K)) : ℝ) : ℂ) ^ (-χ.idealShift : ℂ) =
        ∏ w : InfinitePlace K, (w (x : K) : ℂ) ^ ((mult w : ℂ) * (-χ.idealShift : ℂ)) := by
    simp_rw [mixedEmbedding.norm_apply, normAtPlace_apply]
    exact TauCeti.ofReal_prod_pow_cpow _ (fun w _ ↦ apply_nonneg w _) _
  rw [prod_eq_prod_mul_prod, harmonicFactor_eq_prod_complexHarmonicMonomial, mul_mul_mul_comm,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [χ.infiniteComponent_mul_realFactor _ x, χ.infiniteComponent_mul_complexFactor _ x,
    Finset.prod_mul_distrib]
  rw [hnorm, ofReal_prod, prod_eq_prod_mul_prod, prod_eq_prod_mul_prod]
  ring

/-- **Unit compatibility of `harmonicFactor`.** For every global unit `u : (𝓞 K)ˣ` (which has mixed
norm `1`), multiplying the archimedean character value of `χ` at `u` by
`χ.harmonicFactor (mixedEmbedding K u)` gives `∏_w w(u) ^ harmonicExponent w`; applied to `u⁻¹`,
this supplies the inverse factor `(∏_w w(u) ^ harmonicExponent w)⁻¹` cancelling
`archWeight_unitScale` when a twisted theta sum is reindexed by `u`. -/
theorem prod_infiniteComponent_mul_harmonicFactor_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    ((∏ w : InfinitePlace K,
        χ.toHeckeCharacter.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))) : ℂ) *
      χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K, w (u : K) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  simpa [mixedEmbedding.norm_unit u] using
    χ.prod_infiniteComponent_mul_harmonicFactor_mixedEmbedding
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)

/-- **Principal-ideal compatibility of `harmonicFactor`** (via `Grossencharacter.compatibility`):
for `a ∈ 𝓞 K` congruent to `1` modulo `𝔪` (`IsCongrOne 𝔪 x`), `χ.harmonicFactor` at the mixed
embedding of `a` equals `χ_u((a)) * ∏_w w(a) ^ harmonicExponent w`. -/
theorem harmonicFactor_mixedEmbedding_of_isCongrOne (χ : Grossencharacter K 𝔪) (x : Kˣ)
    (hx : IsCongrOne 𝔪 x) (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a = x) :
    χ.harmonicFactor (mixedEmbedding K (a : K)) =
      χ.unitaryWeight.1 (Ideal.span {a}) *
        ((∏ w : InfinitePlace K, w (a : K) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  have ha' : (a : K) = (x : K) := ha
  have hpos (w : {w : InfinitePlace K // w.IsReal})
      (hw : χ.toHeckeCharacter.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w) :
      0 < InfinitePlace.embedding_of_isReal w.2 (x : K) :=
    (isCongrOne_iff.mp hx).2 w (not_imp_comm.mp (χ.realParity_eq w) hw)
  have hinf : ((∏ w : InfinitePlace K, χ.toHeckeCharacter.infiniteComponent w
        (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      ∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ := by
    rw [χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity
      χ.infinityType χ.agreesOnIdentityComponent x hpos,
      AlgebraicInfinityType.coe_embeddingCharacter_apply]
  have hnorm : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) =
      mixedEmbedding.norm (mixedEmbedding K (x : K)) := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, mixedEmbedding.norm_eq_norm,
      ← ha', ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast]
  have hnorm0 : mixedEmbedding.norm (mixedEmbedding K (x : K)) ≠ 0 := by
    rw [Ne, mixedEmbedding.norm_eq_zero_iff' ⟨(x : K), rfl⟩]
    exact (map_ne_zero_iff (mixedEmbedding K) (mixedEmbedding_injective K)).mpr x.ne_zero
  have hN : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
      ((mixedEmbedding.norm (mixedEmbedding K (x : K)) : ℝ) : ℂ) ^ (-χ.idealShift : ℂ) = 1 := by
    rw [← ofReal_natCast, hnorm, ← cpow_add _ _ (ofReal_ne_zero.mpr hnorm0), add_neg_cancel,
      cpow_zero]
  have hM0 : (∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ ↦ zpow_ne_zero _ ((map_ne_zero τ).mpr x.ne_zero)
  have hprod := χ.prod_infiniteComponent_mul_harmonicFactor_mixedEmbedding x
  rw [hinf] at hprod
  have hcomp := χ.compatibility x hx a ha
  rw [ha']
  refine mul_left_cancel₀ hM0 ?_
  linear_combination hprod -
    (((mixedEmbedding.norm (mixedEmbedding K (x : K)) : ℝ) : ℂ) ^ (-χ.idealShift : ℂ) *
      ((∏ w : InfinitePlace K, w (x : K) ^ χ.harmonicExponent w : ℝ) : ℂ)) * hcomp +
    ((∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ) * χ.unitaryWeight.1 (Ideal.span {a}) *
      ((∏ w : InfinitePlace K, w (x : K) ^ χ.harmonicExponent w : ℝ) : ℂ)) * hN

/-- **Congruence-unit compatibility of `harmonicFactor`.** On a unit `u ∈ unitsCongruenceSubgroup 𝔪`
(`u ≡ 1 mod* 𝔪`), `χ.harmonicFactor (mixedEmbedding K u)` equals the positive real norm power
`∏_w w(u) ^ harmonicExponent w`. -/
theorem harmonicFactor_mixedEmbedding_unit_of_mem_unitsCongruenceSubgroup
    (χ : Grossencharacter K 𝔪) {u : (𝓞 K)ˣ} (hu : u ∈ unitsCongruenceSubgroup 𝔪) :
    χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K, w (u : K) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  rw [χ.harmonicFactor_mixedEmbedding_of_isCongrOne (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
      (mem_unitsCongruenceSubgroup.mp hu) (u : 𝓞 K) rfl,
    Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top, map_one, one_mul]

/-! ### Temperate growth and the weighted Schwartz Gaussian -/

open scoped Classical in
/-- `harmonicFactor` has temperate growth on `mixedSpace K`. -/
@[fun_prop]
theorem hasTemperateGrowth_harmonicFactor (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor.HasTemperateGrowth := by
  rw [funext χ.harmonicFactor_eq_prod_complexHarmonicMonomial]
  refine (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ ?_).mul
    (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ ?_)
  · exact (((ofRealCLM.comp (ContinuousLinearMap.proj w)).comp
      (ContinuousLinearMap.fst ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
        ({v : InfinitePlace K // v.IsComplex} → ℂ))).hasTemperateGrowth).pow _
  · let L : mixedSpace K →L[ℝ] ℂ := (ContinuousLinearMap.proj w).comp
      (ContinuousLinearMap.snd ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
        ({v : InfinitePlace K // v.IsComplex} → ℂ))
    dsimp only [complexHarmonicMonomial]
    split_ifs
    · exact (conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth.pow _
    · exact L.hasTemperateGrowth.pow _

open scoped Classical in
/-- `harmonicFactor` is smooth (`C^n` for every order `n : WithTop ℕ∞`, including real-analytic)
over `ℝ`. -/
@[fun_prop]
theorem contDiff_harmonicFactor (χ : Grossencharacter K 𝔪) {n : WithTop ℕ∞} :
    ContDiff ℝ n χ.harmonicFactor := by
  rw [funext χ.harmonicFactor_eq_prod_complexHarmonicMonomial]
  refine (contDiff_prod fun w _ ↦ ?_).mul (contDiff_prod fun w _ ↦ ?_)
  · exact (((ofRealCLM.comp (ContinuousLinearMap.proj w)).comp
      (ContinuousLinearMap.fst ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
        ({v : InfinitePlace K // v.IsComplex} → ℂ))).contDiff).pow _
  · let L : mixedSpace K →L[ℝ] ℂ := (ContinuousLinearMap.proj w).comp
      (ContinuousLinearMap.snd ℝ ({v : InfinitePlace K // v.IsReal} → ℝ)
        ({v : InfinitePlace K // v.IsComplex} → ℂ))
    dsimp only [complexHarmonicMonomial]
    split_ifs
    · exact (conjCLE.toContinuousLinearMap.comp L).contDiff.pow _
    · exact L.contDiff.pow _

open scoped Classical in
/-- `harmonicFactor` is differentiable over `ℝ`. -/
@[fun_prop]
theorem differentiable_harmonicFactor (χ : Grossencharacter K 𝔪) :
    Differentiable ℝ χ.harmonicFactor :=
  (χ.contDiff_harmonicFactor (n := 1)).differentiable one_ne_zero

/-- `harmonicFactor` is continuous on `mixedSpace K`. -/
@[fun_prop]
theorem continuous_harmonicFactor (χ : Grossencharacter K 𝔪) :
    Continuous χ.harmonicFactor := by
  classical exact χ.differentiable_harmonicFactor.continuous

/-- `harmonicFactor` is measurable on `mixedSpace K`. -/
@[fun_prop]
theorem measurable_harmonicFactor (χ : Grossencharacter K 𝔪) :
    Measurable χ.harmonicFactor :=
  χ.continuous_harmonicFactor.measurable

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
          cexp (-(π : ℂ) * (t : ℂ) ^ 2)) := by ext t; simp [mul_comm t η]
  have hexp : -(π : ℂ) ^ 2 * (η : ℂ) ^ 2 / (π : ℂ) = -(π : ℂ) * (η : ℂ) ^ 2 := by field_simp
  rw [hint, ← Real.fourier_eq', TauCeti.fourier_pow_mul_cexp_neg_mul_sq_of_le_one hb hε η,
    div_self hπ0, one_cpow, one_mul, χ.harmonicExponent_of_isReal w.2, hexp, mul_assoc]

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
      Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have hint : (fun z : ℂ ↦ cexp ((-2 * π * (z * conj ζ).re : ℝ) * I) *
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2))) =
      fun z : ℂ ↦ cexp ((-2 * π * ⟪z, ζ⟫ : ℝ) * I) •
        (complexHarmonicMonomial χ w z * cexp (-(π : ℂ) * ‖z‖ ^ 2)) := by
    ext z; rw [hinner, smul_eq_mul]
  have hexp : -(π : ℂ) ^ 2 * ‖ζ‖ ^ 2 / (π : ℂ) = -(π : ℂ) * ‖ζ‖ ^ 2 := by field_simp
  rw [hint, ← Real.fourier_eq', χ.harmonicExponent_of_isComplex w.2]
  dsimp only [complexHarmonicMonomial]
  set k := (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w
  split_ifs with hk
  · rw [TauCeti.fourier_conj_pow_mul_cexp_neg_mul_norm_sq hb k.toNat ζ, div_self hπ0, one_pow,
      one_mul, hexp, (by omega : k.toNat = k.natAbs), mul_assoc]
  · rw [TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq hb (-k).toNat ζ, div_self hπ0, one_pow,
      one_mul, hexp, (by omega : (-k).toNat = k.natAbs), mul_assoc]

open scoped Classical in
/-- **Hecke's lemma at the unit parameter `1`**: the harmonic polynomial times `archGaussian 1` is
an eigenfunction of `mixedFourier K` with eigenvalue `(-i) ^ harmonicDegree`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian_one (χ : Grossencharacter K 𝔪)
    (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian 1 x) ξ =
      (-I) ^ χ.harmonicDegree * χ.harmonicFactor ξ * archGaussian 1 ξ := by
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
      congr 1 <;> simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ofReal_sum, Finset.sum_mul,
        Complex.exp_sum, neg_mul]
    rw [Circle.smul_def, smul_eq_mul, hchar, harmonicFactor_eq_prod_complexHarmonicMonomial,
      archGaussian_one_eq_prod_mul_prod]
    dsimp only [fR, fC]; simp only [Finset.prod_mul_distrib]; ring
  rw [mixedFourier_apply]; simp_rw [hfactor]
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
  set c' : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y⁻¹ w)
  have hcc' : c' * mixedSpaceOfRealSpace (fun w ↦ √(y w)) = 1 := by
    ext w <;> simp [c', mixedSpaceOfRealSpace_apply, (Real.sqrt_pos.mpr (hy _)).ne']
  have hF : mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian y x) ξ =
      χ.harmonicFactor c' * mixedFourier K
        (fun x ↦ χ.harmonicFactor (archGaussianDilation y hy x) *
          archGaussian 1 (archGaussianDilation y hy x)) ξ := by
    classical
    rw [mixedFourier_apply, mixedFourier_apply, ← integral_const_mul]
    congr 1; ext x
    have hx : x = c' * archGaussianDilation y hy x := by
      rw [archGaussianDilation_apply, ← mul_assoc, hcc', one_mul]
    have hharm : χ.harmonicFactor x =
        χ.harmonicFactor c' * χ.harmonicFactor (archGaussianDilation y hy x) := by
      rw [← χ.harmonicFactor_mul, ← hx]
    rw [hharm, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul,
      archGaussian_one_archGaussianDilation]
    ring
  have hc'_sq : χ.harmonicFactor c' * χ.harmonicFactor c' =
      ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) := by
    rw [harmonicFactor_mixedSpaceOfRealSpace, ← ofReal_mul, ← Finset.prod_mul_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun w _ ↦ by
      rw [← mul_pow, Real.mul_self_sqrt (hy' w).le, Pi.inv_apply])
  rw [hF,
    mixedFourier_comp_archGaussianDilation (fun z ↦ χ.harmonicFactor z * archGaussian 1 z) y hy ξ,
    mixedFourier_harmonicFactor_mul_archGaussian_one, archGaussian_one_archGaussianDilation,
    archGaussianDilation_apply, harmonicFactor_mul]
  linear_combination
    (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) * χ.harmonicFactor ξ *
      archGaussian y⁻¹ ξ * hc'_sq

/-! ### Constant-term indicator of the twisted theta series -/

/-- **Neukirch's constant-term indicator `ε(χ)`** for the twisted theta series: `1` when both the
finite conductor `χ.toHeckeCharacter.finiteConductor` is trivial (`⊤`) and `harmonicDegree` is `0`,
and `0` otherwise. Note that this tests `finiteConductor = ⊤` and `harmonicDegree = 0` rather than
`𝔪 = Modulus.one K`, because an unramified odd norm power over `ℚ` cannot be presented at
`Modulus.one ℚ` (as `Grossencharacter.realParity_eq` forces `∞ ∈ 𝔪.infinitePart`), yet still has
`finiteConductor = ⊤`, `harmonicDegree = 0`, and constant term `1`. -/
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

/-- At the trivial modulus, every ray class character has `heckeEpsilon = 1`. -/
@[simp]
theorem heckeEpsilon_ofRayClassCharacter_of_modulus_one (η : RayClassCharacter (Modulus.one K)) :
    (ofRayClassCharacter η).heckeEpsilon = 1 := by
  rw [heckeEpsilon_eq_one_iff]
  refine ⟨top_unique ?_, harmonicDegree_ofRayClassCharacter_of_modulus_one η⟩
  have hdvd := (ofRayClassCharacter η).finiteConductor_dvd_finitePart
  rw [Modulus.one_finitePart, Ideal.dvd_iff_le] at hdvd
  exact hdvd

/-- Any presentation of the trivial Hecke character has `heckeEpsilon = 1`. -/
theorem heckeEpsilon_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) : χ.heckeEpsilon = 1 := by
  rw [heckeEpsilon_eq_one_iff]
  exact ⟨by simp [hχ], harmonicDegree_of_toHeckeCharacter_eq_one hχ⟩

/-- The trivial ray class character at any modulus has `heckeEpsilon = 1`. -/
@[simp]
theorem heckeEpsilon_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).heckeEpsilon = 1 :=
  heckeEpsilon_of_toHeckeCharacter_eq_one (by simp)

end TauCeti.LFunctions.Grossencharacter
