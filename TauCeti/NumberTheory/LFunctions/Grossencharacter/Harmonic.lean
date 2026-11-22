/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
public import TauCeti.NumberTheory.LFunctions.Theta.Harmonic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.RealParity
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.UnitCompatibility

/-!
# Harmonic polynomials and Hecke's Fourier lemma for Grossencharacters

A presentation `χ : Grossencharacter K 𝔪` of an algebraic Hecke character determines an
archimedean harmonic polynomial `χ.harmonicFactor` on `mixedSpace K`, its local and total degrees
`χ.harmonicExponent` and `χ.harmonicDegree`, the parameter weight `χ.archWeight`, and the constant
term `χ.heckeEpsilon` of Hecke's twisted theta series.

At a real place `w`, `χ.harmonicFactor` carries the parity of `χ.toHeckeCharacter.infinityType`
rather than that of `χ.infinityType` (so a finite-order character ramified at `w ∈ 𝔪.infinitePart`
retains the odd factor `x_w`). At a complex place `w`, `χ.agreesOnIdentityComponent` identifies the
angular frequency of `χ.toHeckeCharacter.infinityType` with `n τ - n (conj τ)`, so all four
archimedean quantities agree with their `ContinuousInfinityType` counterparts on
`χ.toHeckeCharacter.infinityType` and are independent of the presentation modulus `𝔪`:

* `χ.harmonicFactor * archGaussian y` transforms under `mixedFourier K` into
  `χ.harmonicFactor * archGaussian y⁻¹` up to
  `(-i) ^ χ.harmonicDegree * N(y)^(-1/2) * ∏_w y_w^(-P_w)`;
* multiplying `χ.harmonicFactor (mixedEmbedding K x)` by the archimedean components of
  `χ.toHeckeCharacter.unitaryPart` clears all signs and phases on `Kˣ`, leaving `∏_w |x_w| ^ P_w`
  (and likewise for `χ.toHeckeCharacter` on `Kˣ` up to `|N(x)| ^ (-χ.idealShift)`, and on
  `(𝓞 K)ˣ`);
* for `a ∈ 𝓞 K` congruent to `1` modulo `𝔪`, `Grossencharacter.compatibility` evaluates
  `χ.harmonicFactor (mixedEmbedding K a)` as `χ.unitaryWeight.1 (Ideal.span {a}) * ∏_w w(a) ^ P_w`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.harmonicExponent`, `harmonicDegree`, `harmonicFactor`,
  `archWeight`, `heckeEpsilon`: local/total harmonic degrees, harmonic polynomial, weight, and
  theta constant term.

## Main results

* `TauCeti.LFunctions.Grossencharacter.mixedFourier_harmonicFactor_mul_archGaussian`: Hecke's
  Fourier eigenfunction lemma for `χ`.
* `TauCeti.LFunctions.Grossencharacter.integral_archGaussian_mul_archWeight_mul_archNorm_cpow`:
  the shifted archimedean gamma integral for `χ`.
* `TauCeti.LFunctions.Grossencharacter.prod_unitaryPart_infiniteComponent_mul_harmonicFactor`,
  `TauCeti.LFunctions.Grossencharacter.prod_infiniteComponent_mul_harmonicFactor_mixedEmbedding`,
  `TauCeti.LFunctions.Grossencharacter.prod_infiniteComponent_unit_mul_harmonicFactor`,
  `TauCeti.LFunctions.Grossencharacter.harmonicFactor_mixedEmbedding_of_isCongrOne`, and
  `harmonicFactor_mixedEmbedding_unit_of_mem_unitsCongruenceSubgroup`: archimedean sign and phase
  cancellation on `Kˣ`, `(𝓞 K)ˣ`, and principal ideals `≡ 1 mod* 𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3, 7–8.
-/

public noncomputable section

open Complex ComplexConjugate MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding TauCeti.NumberField.mixedEmbedding
open scoped FourierTransform NumberField Real

namespace TauCeti.LFunctions

open GlobalNumberFields

namespace Grossencharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Local and total harmonic degrees -/

open scoped Classical in
/-- The local harmonic degree `P_w` of `χ` at an infinite place `w`: the parity of the archimedean
restriction at a real place, and the absolute angular frequency `|n τ - n (conj τ)|` at a complex
place. -/
def harmonicExponent (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) : ℕ :=
  if h : w.IsReal then (χ.toHeckeCharacter.infinityType.realParity ⟨w, h⟩).val
  else ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
    ⟨w, not_isReal_iff_isComplex.mp h⟩).natAbs

open scoped Classical in
/-- The defining formula of `Grossencharacter.harmonicExponent`. -/
theorem harmonicExponent_def (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) :
    χ.harmonicExponent w =
      if h : w.IsReal then (χ.toHeckeCharacter.infinityType.realParity ⟨w, h⟩).val
      else ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency
        ⟨w, not_isReal_iff_isComplex.mp h⟩).natAbs :=
  (rfl)

/-- `Grossencharacter.harmonicExponent` agrees with the `ContinuousInfinityType` harmonic exponent
of `χ.toHeckeCharacter.infinityType`. -/
theorem harmonicExponent_eq_infinityType (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) :
    χ.harmonicExponent w = χ.toHeckeCharacter.infinityType.harmonicExponent w := by
  classical
  have hfreq :=
    ((χ.toHeckeCharacter.infinityType.agreesOnIdentityComponent_iff _).mp
      χ.agreesOnIdentityComponent).2.2
  simp only [harmonicExponent_def, ContinuousInfinityType.harmonicExponent_def, hfreq]

@[simp]
theorem harmonicExponent_of_isReal (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsReal) :
    χ.harmonicExponent w = (χ.toHeckeCharacter.infinityType.realParity ⟨w, hw⟩).val := by
  rw [harmonicExponent_eq_infinityType, ContinuousInfinityType.harmonicExponent_of_isReal _ hw]

@[simp]
theorem harmonicExponent_of_isComplex (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    χ.harmonicExponent w =
      (χ.infinityType w.embedding -
        χ.infinityType (ComplexEmbedding.conjugate w.embedding)).natAbs := by
  rw [harmonicExponent_eq_infinityType,
    ContinuousInfinityType.harmonicExponent_eq_of_agreesOnIdentityComponent
      χ.agreesOnIdentityComponent hw,
    ContinuousInfinityType.toContinuous_harmonicExponent_of_isComplex _ hw]

/-- At a real place, `χ.harmonicExponent w` is `0` or `1`. -/
theorem harmonicExponent_le_one_of_isReal (χ : Grossencharacter K 𝔪) {w : InfinitePlace K}
    (hw : w.IsReal) :
    χ.harmonicExponent w ≤ 1 := by
  rw [harmonicExponent_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.harmonicExponent_le_one_of_isReal hw

/-- At a real place outside `𝔪.infinitePart`, the harmonic exponent is the parity of the algebraic
exponent `χ.infinityType w.embedding`. -/
theorem harmonicExponent_of_notMem_infinitePart (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w ∉ 𝔪.infinitePart) :
    χ.harmonicExponent w.val = (χ.infinityType w.val.embedding : ZMod 2).val := by
  rw [χ.harmonicExponent_of_isReal w.property, χ.realParity_eq w hw,
    AlgebraicInfinityType.toContinuous_realParity]

/-- Neukirch's `Tr(p)`: the total degree `∑_w P_w` of the harmonic polynomial of `χ`. -/
def harmonicDegree (χ : Grossencharacter K 𝔪) : ℕ :=
  ∑ w : InfinitePlace K, χ.harmonicExponent w

/-- The defining equation of `Grossencharacter.harmonicDegree`. -/
theorem harmonicDegree_def (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = ∑ w : InfinitePlace K, χ.harmonicExponent w :=
  (rfl)

/-- `Grossencharacter.harmonicDegree` agrees with the `ContinuousInfinityType` harmonic degree of
`χ.toHeckeCharacter.infinityType`. -/
theorem harmonicDegree_eq_infinityType (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = χ.toHeckeCharacter.infinityType.harmonicDegree := by
  simp only [harmonicDegree_def, ContinuousInfinityType.harmonicDegree_def,
    harmonicExponent_eq_infinityType]

/-! ### The harmonic polynomial and parameter weight -/

open scoped Classical in
/-- **The harmonic polynomial of the theta kernel** (Neukirch VII §7, p. 489): at a real place `w`
it is `x_w ^ ε_w`, where `ε_w` is the parity of the archimedean restriction; at a complex place `w`
with angular frequency `k_w = n τ - n (conj τ)` it is `conj(z_w) ^ k_w` for `k_w ≥ 0` and
`z_w ^ (-k_w)` for `k_w < 0`. Because the ideal-side value in `Grossencharacter.compatibility` is
the inverse of the idelic archimedean value, positive angular frequency places the conjugate
coordinate in the polynomial. -/
def harmonicFactor (χ : Grossencharacter K 𝔪) (x : mixedSpace K) : ℂ :=
  (∏ w : {w : InfinitePlace K // w.IsReal},
      ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
    ∏ w : {w : InfinitePlace K // w.IsComplex},
      TauCeti.complexHarmonicMonomial
        ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w) (x.2 w)

open scoped Classical in
/-- The defining formula of `Grossencharacter.harmonicFactor`. -/
theorem harmonicFactor_def (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x =
      (∏ w : {w : InfinitePlace K // w.IsReal},
          ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          TauCeti.complexHarmonicMonomial
            ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w)
            (x.2 w) :=
  (rfl)

open scoped Classical in
/-- Explicit piecewise formula for `χ.harmonicFactor` in terms of `conj(z_w) ^ k_w` (`k_w ≥ 0`)
and `z_w ^ (-k_w)` (`k_w < 0`). -/
theorem harmonicFactor_eq_prod_mul_prod_ite (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x =
      (∏ w : {w : InfinitePlace K // w.IsReal},
          ((x.1 w : ℝ) : ℂ) ^ (χ.toHeckeCharacter.infinityType.realParity w).val) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          if 0 ≤ (AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w then
            conj (x.2 w) ^
              ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).toNat
          else
            x.2 w ^
              (-(AlgebraicInfinityType.toContinuous
                χ.infinityType).complexAngularFrequency w).toNat := by
  simp only [harmonicFactor_def, TauCeti.complexHarmonicMonomial_def]

/-- `Grossencharacter.harmonicFactor` agrees with the `ContinuousInfinityType` harmonic polynomial
of `χ.toHeckeCharacter.infinityType`. -/
theorem harmonicFactor_eq_infinityType (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x = χ.toHeckeCharacter.infinityType.harmonicFactor x := by
  classical
  have hfreq :=
    ((χ.toHeckeCharacter.infinityType.agreesOnIdentityComponent_iff _).mp
      χ.agreesOnIdentityComponent).2.2
  simp only [harmonicFactor_def, ContinuousInfinityType.harmonicFactor_def, hfreq]

@[simp]
theorem harmonicFactor_one (χ : Grossencharacter K 𝔪) : χ.harmonicFactor 1 = 1 := by
  rw [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_one]

/-- `χ.harmonicFactor` is completely multiplicative on `mixedSpace K`. -/
theorem harmonicFactor_mul (χ : Grossencharacter K 𝔪) (x z : mixedSpace K) :
    χ.harmonicFactor (x * z) = χ.harmonicFactor x * χ.harmonicFactor z := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_mul]

/-- The norm of `χ.harmonicFactor x` is `∏_w normAtPlace w x ^ χ.harmonicExponent w`. -/
theorem norm_harmonicFactor (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    ‖χ.harmonicFactor x‖ = ∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.norm_harmonicFactor,
    harmonicExponent_eq_infinityType]

/-- At `0`, `χ.harmonicFactor` takes the value `1` if `χ.harmonicDegree = 0` and `0` otherwise. -/
theorem harmonicFactor_zero_right (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor 0 = if χ.harmonicDegree = 0 then 1 else 0 := by
  rw [harmonicFactor_eq_infinityType, harmonicDegree_eq_infinityType,
    ContinuousInfinityType.harmonicFactor_zero_right]

/-- Scaling by `mixedSpaceOfRealSpace r` multiplies `χ.harmonicFactor` by `∏_w r_w ^ P_w`. -/
theorem harmonicFactor_mixedSpaceOfRealSpace_mul (χ : Grossencharacter K 𝔪) (r : realSpace K)
    (x : mixedSpace K) :
    χ.harmonicFactor (mixedSpaceOfRealSpace r * x) =
      ((∏ w : InfinitePlace K, r w ^ χ.harmonicExponent w : ℝ) : ℂ) * χ.harmonicFactor x := by
  simp only [harmonicFactor_eq_infinityType,
    ContinuousInfinityType.harmonicFactor_mixedSpaceOfRealSpace_mul,
    harmonicExponent_eq_infinityType]

/-- The action of a unit `u` on `mixedSpace K` multiplies `χ.harmonicFactor` by its value at
`mixedEmbedding K u`. -/
theorem harmonicFactor_unit_smul (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    χ.harmonicFactor (u • x) = χ.harmonicFactor (mixedEmbedding K u) * χ.harmonicFactor x := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_unit_smul]

/-- The archimedean parameter weight `∏_w y_w ^ (P_w / 2)` of Neukirch VII (8.2)–(8.3). -/
def archWeight (χ : Grossencharacter K 𝔪) (y : realSpace K) : ℝ :=
  ∏ w : InfinitePlace K, y w ^ ((χ.harmonicExponent w : ℝ) / 2)

/-- The defining equation of `Grossencharacter.archWeight`. -/
theorem archWeight_def (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.archWeight y = ∏ w : InfinitePlace K, y w ^ ((χ.harmonicExponent w : ℝ) / 2) :=
  (rfl)

/-- `Grossencharacter.archWeight` agrees with the `ContinuousInfinityType` parameter weight of
`χ.toHeckeCharacter.infinityType`. -/
theorem archWeight_eq_infinityType (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.archWeight y = χ.toHeckeCharacter.infinityType.archWeight y := by
  simp only [archWeight_def, ContinuousInfinityType.archWeight_def,
    harmonicExponent_eq_infinityType]

@[simp]
theorem archWeight_one (χ : Grossencharacter K 𝔪) : χ.archWeight 1 = 1 := by
  rw [archWeight_eq_infinityType, ContinuousInfinityType.archWeight_one]

/-- For nonnegative parameters, `χ.archWeight` is nonnegative. -/
theorem archWeight_nonneg (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 ≤ y w) :
    0 ≤ χ.archWeight y := by
  rw [archWeight_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.archWeight_nonneg hy

/-- For positive parameters, `χ.archWeight` is strictly positive. -/
theorem archWeight_pos (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 < y w) :
    0 < χ.archWeight y := by
  rw [archWeight_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.archWeight_pos hy

/-- `χ.archWeight` distributes over a product whose first factor is nonnegative, with no sign
condition on the second factor. -/
theorem archWeight_mul (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 ≤ y w)
    (z : realSpace K) :
    χ.archWeight (y * z) = χ.archWeight y * χ.archWeight z := by
  simp only [archWeight_eq_infinityType, ContinuousInfinityType.archWeight_mul _ hy z]

/-- `χ.archWeight` commutes with coordinatewise parameter inversion. -/
theorem archWeight_inv (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.archWeight y⁻¹ = (χ.archWeight y)⁻¹ := by
  simp only [archWeight_eq_infinityType, ContinuousInfinityType.archWeight_inv]

/-- For nonnegative parameters, squaring `χ.archWeight y` gives `∏_w y_w ^ P_w`. -/
theorem archWeight_sq (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 ≤ y w) :
    χ.archWeight y ^ 2 = ∏ w : InfinitePlace K, y w ^ χ.harmonicExponent w := by
  simp only [archWeight_eq_infinityType, ContinuousInfinityType.archWeight_sq _ hy,
    harmonicExponent_eq_infinityType]

/-- Under `unitScale u`, `χ.archWeight` multiplies by `∏_w |u_w| ^ P_w`. -/
theorem archWeight_unitScale (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (y : realSpace K) :
    χ.archWeight (unitScale u y) =
      (∏ w : InfinitePlace K, normAtPlace w (mixedEmbedding K u) ^ χ.harmonicExponent w) *
        χ.archWeight y := by
  simp only [archWeight_eq_infinityType, ContinuousInfinityType.archWeight_unitScale,
    harmonicExponent_eq_infinityType]

/-! ### Constant term of Hecke's theta series -/

/-- Neukirch's `ε(χ)`: the constant term of the twisted theta series, equal to `1` when the finite
conductor `χ.toHeckeCharacter.finiteConductor` is trivial (`⊤`) and `χ.harmonicDegree = 0`, and `0`
otherwise. It uses `finiteConductor` rather than a full modulus conductor because odd norm powers
of `ℚ` have real places in their modulus discrepancy while still having `ε(χ) = 1`. -/
def heckeEpsilon (χ : Grossencharacter K 𝔪) : ℂ :=
  if χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 then 1 else 0

/-- The defining equation of `Grossencharacter.heckeEpsilon`. -/
theorem heckeEpsilon_def (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon =
      if χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 then 1 else 0 :=
  (rfl)

@[simp]
theorem heckeEpsilon_eq_one_iff (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon = 1 ↔ χ.toHeckeCharacter.finiteConductor = ⊤ ∧ χ.harmonicDegree = 0 := by
  simp [heckeEpsilon_def]

@[simp]
theorem heckeEpsilon_eq_zero_iff (χ : Grossencharacter K 𝔪) :
    χ.heckeEpsilon = 0 ↔ χ.toHeckeCharacter.finiteConductor ≠ ⊤ ∨ χ.harmonicDegree ≠ 0 := by
  simp only [heckeEpsilon_def, ite_eq_right_iff, one_ne_zero, imp_false, not_and_or]

/-- When `χ.toHeckeCharacter.finiteConductor ≠ ⊤`, the constant term `χ.heckeEpsilon` vanishes. -/
theorem heckeEpsilon_eq_zero_of_finiteConductor_ne_top (χ : Grossencharacter K 𝔪)
    (h : χ.toHeckeCharacter.finiteConductor ≠ ⊤) : χ.heckeEpsilon = 0 :=
  χ.heckeEpsilon_eq_zero_iff.mpr (Or.inl h)

/-- When `χ.harmonicDegree ≠ 0`, the constant term `χ.heckeEpsilon` vanishes. -/
theorem heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero (χ : Grossencharacter K 𝔪)
    (h : χ.harmonicDegree ≠ 0) : χ.heckeEpsilon = 0 :=
  χ.heckeEpsilon_eq_zero_iff.mpr (Or.inr h)

/-! ### Modulus independence and inverse symmetry -/

section Congruence

variable {𝔫 : Modulus K}

/-- Two presentations with the same underlying `HeckeCharacter` have the same `harmonicExponent`. -/
theorem harmonicExponent_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (w : InfinitePlace K) :
    χ.harmonicExponent w = ψ.harmonicExponent w := by
  rw [harmonicExponent_eq_infinityType, harmonicExponent_eq_infinityType, h]

/-- Two presentations with the same underlying `HeckeCharacter` have the same `harmonicDegree`. -/
theorem harmonicDegree_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.harmonicDegree = ψ.harmonicDegree := by
  rw [harmonicDegree_eq_infinityType, harmonicDegree_eq_infinityType, h]

/-- Two presentations with the same underlying `HeckeCharacter` have the same `harmonicFactor`. -/
theorem harmonicFactor_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (x : mixedSpace K) :
    χ.harmonicFactor x = ψ.harmonicFactor x := by
  rw [harmonicFactor_eq_infinityType, harmonicFactor_eq_infinityType, h]

/-- Two presentations with the same underlying `HeckeCharacter` have the same `archWeight`. -/
theorem archWeight_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (y : realSpace K) :
    χ.archWeight y = ψ.archWeight y := by
  rw [archWeight_eq_infinityType, archWeight_eq_infinityType, h]

/-- Two presentations with the same underlying `HeckeCharacter` have the same `heckeEpsilon`. -/
theorem heckeEpsilon_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.heckeEpsilon = ψ.heckeEpsilon := by
  rw [heckeEpsilon_def, heckeEpsilon_def, h, harmonicDegree_congr h]

/-- Inverting the underlying Hecke character preserves every local harmonic exponent. -/
theorem harmonicExponent_of_toHeckeCharacter_eq_inv {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : ψ.toHeckeCharacter = χ.toHeckeCharacter⁻¹)
    (w : InfinitePlace K) :
    ψ.harmonicExponent w = χ.harmonicExponent w := by
  rw [harmonicExponent_eq_infinityType, harmonicExponent_eq_infinityType, h,
    HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_harmonicExponent]

/-- Inverting the underlying Hecke character preserves `harmonicDegree`. -/
theorem harmonicDegree_of_toHeckeCharacter_eq_inv {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : ψ.toHeckeCharacter = χ.toHeckeCharacter⁻¹) :
    ψ.harmonicDegree = χ.harmonicDegree := by
  rw [harmonicDegree_eq_infinityType, harmonicDegree_eq_infinityType, h,
    HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_harmonicDegree]

/-- Inverting the underlying Hecke character conjugates `harmonicFactor`. -/
theorem harmonicFactor_of_toHeckeCharacter_eq_inv {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : ψ.toHeckeCharacter = χ.toHeckeCharacter⁻¹)
    (x : mixedSpace K) :
    ψ.harmonicFactor x = conj (χ.harmonicFactor x) := by
  rw [harmonicFactor_eq_infinityType, harmonicFactor_eq_infinityType, h,
    HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_harmonicFactor]

/-- Inverting the underlying Hecke character preserves `archWeight`. -/
theorem archWeight_of_toHeckeCharacter_eq_inv {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : ψ.toHeckeCharacter = χ.toHeckeCharacter⁻¹)
    (y : realSpace K) :
    ψ.archWeight y = χ.archWeight y := by
  rw [archWeight_eq_infinityType, archWeight_eq_infinityType, h,
    HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_archWeight]

/-- Inverting the underlying Hecke character preserves `heckeEpsilon`. -/
theorem heckeEpsilon_of_toHeckeCharacter_eq_inv {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : ψ.toHeckeCharacter = χ.toHeckeCharacter⁻¹) :
    ψ.heckeEpsilon = χ.heckeEpsilon := by
  rw [heckeEpsilon_def, heckeEpsilon_def, h, HeckeCharacter.finiteConductor_inv,
    harmonicDegree_of_toHeckeCharacter_eq_inv h]

end Congruence

/-! ### Hecke's Fourier lemma, Poisson summation, and gamma integral -/

/-- For positive parameters `y`, a shifted harmonic-weighted archimedean Gaussian of `χ` is
summable over any discrete `ℤ`-submodule of `mixedSpace K`. -/
theorem summable_harmonicFactor_mul_archGaussian_add (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K) (hy : ∀ w, 0 < y w)
    (v : mixedSpace K) :
    Summable fun x : L ↦ χ.harmonicFactor (v + x) * archGaussian y (v + x) := by
  simp_rw [harmonicFactor_eq_infinityType]
  exact TauCeti.LFunctions.summable_harmonicFactor_mul_archGaussian_add
    χ.toHeckeCharacter.infinityType L y hy v

/-- For positive parameters `y`, `χ.harmonicFactor x * archGaussian y x` is summable over any
discrete `ℤ`-submodule of `mixedSpace K`. -/
theorem summable_harmonicFactor_mul_archGaussian (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K) (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ χ.harmonicFactor x * archGaussian y x := by
  simpa using χ.summable_harmonicFactor_mul_archGaussian_add L y hy 0

open scoped Classical in
/-- Over a full lattice `L` of `mixedSpace K`, the shifted harmonic-weighted archimedean Gaussian of
`χ` is summable if and only if every parameter coordinate `y w` is positive. -/
theorem summable_harmonicFactor_mul_archGaussian_add_iff (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) (v : mixedSpace K) :
    (Summable fun x : L ↦ χ.harmonicFactor (v + x) * archGaussian y (v + x)) ↔ ∀ w, 0 < y w := by
  simp_rw [harmonicFactor_eq_infinityType]
  exact TauCeti.LFunctions.summable_harmonicFactor_mul_archGaussian_add_iff
    χ.toHeckeCharacter.infinityType L y v

open scoped Classical in
/-- Over a full lattice `L` of `mixedSpace K`, `χ.harmonicFactor x * archGaussian y x` is summable
if and only if every parameter coordinate `y w` is positive. -/
theorem summable_harmonicFactor_mul_archGaussian_iff (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] (y : realSpace K) :
    (Summable fun x : L ↦ χ.harmonicFactor x * archGaussian y x) ↔ ∀ w, 0 < y w := by
  simpa using χ.summable_harmonicFactor_mul_archGaussian_add_iff L y 0

/-- **Hecke's Fourier eigenfunction lemma at parameter `1`** for a presented algebraic Hecke
character `χ`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian_one (χ : Grossencharacter K 𝔪)
    (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian 1 x) ξ =
      (-I) ^ χ.harmonicDegree * χ.harmonicFactor ξ * archGaussian 1 ξ := by
  simp_rw [harmonicFactor_eq_infinityType, harmonicDegree_eq_infinityType]
  exact TauCeti.LFunctions.mixedFourier_harmonicFactor_mul_archGaussian_one
    χ.toHeckeCharacter.infinityType ξ

/-- **Hecke's Fourier eigenfunction lemma** (Neukirch VII (3.5)–(3.6) at `z = i y`): for every
presented algebraic Hecke character `χ` and positive parameter vector `y`, `χ.harmonicFactor` times
`archGaussian y` transforms under `mixedFourier K` into `χ.harmonicFactor` times `archGaussian y⁻¹`
multiplied by `(-i) ^ χ.harmonicDegree * N(y)^(-1/2) * ∏_w y_w^(-P_w)`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian (χ : Grossencharacter K 𝔪)
    (y : realSpace K) (hy : ∀ w, 0 < y w) (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ χ.harmonicFactor x * archGaussian y x) ξ =
      (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) *
        χ.harmonicFactor ξ * archGaussian y⁻¹ ξ := by
  simp_rw [harmonicFactor_eq_infinityType, harmonicDegree_eq_infinityType,
    harmonicExponent_eq_infinityType]
  exact TauCeti.LFunctions.mixedFourier_harmonicFactor_mul_archGaussian
    χ.toHeckeCharacter.infinityType y hy ξ

open scoped Classical in
/-- Shifted Poisson summation for `χ.harmonicFactor * archGaussian y` over a full lattice `L` of
`mixedSpace K` (when any coordinate `y w ≤ 0`, both series fail to converge absolutely and vanish).
-/
theorem tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) (v : mixedSpace K) :
    ∑' ℓ : L, χ.harmonicFactor (v + ℓ) * archGaussian y (v + ℓ) =
      (ZLattice.covolume L : ℂ)⁻¹ * (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) *
        ∑' m : mixedDual K L,
          χ.harmonicFactor m * archGaussian y⁻¹ m * cexp (2 * π * I * mixedInner K v m) := by
  simp_rw [harmonicFactor_eq_infinityType, harmonicDegree_eq_infinityType,
    harmonicExponent_eq_infinityType]
  exact TauCeti.LFunctions.tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual
    χ.toHeckeCharacter.infinityType L y v

open scoped Classical in
/-- Poisson summation for `χ.harmonicFactor * archGaussian y` over a full lattice `L` of
`mixedSpace K` at shift `0`. -/
theorem tsum_harmonicFactor_mul_archGaussian_eq_mixedDual (χ : Grossencharacter K 𝔪)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) :
    ∑' ℓ : L, χ.harmonicFactor ℓ * archGaussian y ℓ =
      (ZLattice.covolume L : ℂ)⁻¹ * (-I) ^ χ.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w : ℝ) : ℂ) *
        ∑' m : mixedDual K L, χ.harmonicFactor m * archGaussian y⁻¹ m := by
  simpa [← mixedInnerBilin_apply] using
    χ.tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual L y 0

/-- For `x` of nonzero norm and `s` in the local convergence half-plane
`∀ w, 0 < mult w * Re s + P_w`, `archGaussian y x * χ.archWeight y * N(y)^(s / 2)` is integrable
over `archHaar K`. -/
theorem integrable_archGaussian_mul_archWeight_mul_archNorm_cpow (χ : Grossencharacter K 𝔪)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    Integrable (fun y ↦ archGaussian y x * (χ.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2))
      (archHaar K) := by
  simp_rw [archWeight_eq_infinityType]
  refine TauCeti.LFunctions.integrable_archGaussian_mul_archWeight_mul_archNorm_cpow
    χ.toHeckeCharacter.infinityType hx fun w ↦ ?_
  simpa only [← harmonicExponent_eq_infinityType] using hs w

/-- **The weighted archimedean gamma integral** for a presented algebraic Hecke character `χ` on the
half-plane `∀ w, 0 < mult w * Re s + P_w` (when `mixedEmbedding.norm x = 0`, both sides vanish). -/
theorem integral_archGaussian_mul_archWeight_mul_archNorm_cpow (χ : Grossencharacter K 𝔪)
    (x : mixedSpace K) {s : ℂ}
    (hs : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    ∫ y, archGaussian y x * (χ.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      (∏ w : InfinitePlace K, Gammaℝ (mult w * s + χ.harmonicExponent w)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  simp_rw [archWeight_eq_infinityType, harmonicExponent_eq_infinityType]
  refine TauCeti.LFunctions.integral_archGaussian_mul_archWeight_mul_archNorm_cpow
    χ.toHeckeCharacter.infinityType x fun w ↦ ?_
  simpa only [← harmonicExponent_eq_infinityType] using hs w

/-! ### Archimedean sign and phase cancellation on `Kˣ` and `(𝓞 K)ˣ` -/

private theorem unitaryPart_real_mul_pow (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    (χ.toHeckeCharacter.unitaryPart.infiniteComponent w.val
        (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) *
      (((mixedEmbedding K (x : K)).1 w : ℝ) : ℂ) ^
        (χ.toHeckeCharacter.infinityType.realParity w).val =
      ((normAtPlace w.val (mixedEmbedding K (x : K)) ^ χ.harmonicExponent w.val : ℝ) : ℂ) := by
  rw [HeckeCharacter.infiniteComponent_map_algebraMap_eq_realComponent,
    HeckeCharacter.realComponent_eq, χ.infinityType_unitaryPart]
  simp only [Pi.zero_apply, TauCeti.realUnitsCharacter_zero_left]
  rw [mixedEmbedding_apply_isReal, normAtPlace_apply_of_isReal w.property,
      mixedEmbedding_apply_isReal,
    Real.norm_eq_abs, χ.harmonicExponent_of_isReal w.property]
  have hr0 : embedding_of_isReal w.property (x : K) ≠ 0 := (map_ne_zero _).mpr x.ne_zero
  have hpar := (χ.toHeckeCharacter.infinityType.realParity w).val_lt
  interval_cases (χ.toHeckeCharacter.infinityType.realParity w).val
  · simp
  · simp only [pow_one, TauCeti.coe_realSignCharacter_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rcases lt_or_gt_of_ne hr0 with hlt | hgt
    · simp [sign_neg hlt, abs_of_neg hlt]
    · simp [sign_pos hgt, abs_of_pos hgt]

private theorem unitaryPart_complex_mul_monomial (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.toHeckeCharacter.unitaryPart.infiniteComponent w.val
        (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) *
      TauCeti.complexHarmonicMonomial
        ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w)
        ((mixedEmbedding K (x : K)).2 w) =
      ((normAtPlace w.val (mixedEmbedding K (x : K)) ^ χ.harmonicExponent w.val : ℝ) : ℂ) := by
  rw [HeckeCharacter.infiniteComponent_map_algebraMap_eq_complexComponent,
    HeckeCharacter.complexComponent_eq, χ.infinityType_unitaryPart]
  simp only [Pi.zero_apply, TauCeti.coe_complexUnitsCharacter_apply, cpow_zero, one_mul,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [mixedEmbedding_apply_isComplex, TauCeti.angular_mul_complexHarmonicMonomial,
    normAtPlace_apply_of_isComplex w.property, mixedEmbedding_apply_isComplex,
    χ.harmonicExponent_eq_infinityType,
    ContinuousInfinityType.harmonicExponent_eq_of_agreesOnIdentityComponent
      χ.agreesOnIdentityComponent w.property,
    ContinuousInfinityType.harmonicExponent_of_isComplex _ w.property, ofReal_pow]

/-- **Archimedean sign and phase cancellation on `Kˣ`**: for any `x : Kˣ`, multiplying the product
of the archimedean components of `χ.toHeckeCharacter.unitaryPart` at `x` by
`χ.harmonicFactor (mixedEmbedding K x)` cancels all real signs and complex angular phases, leaving
`∏_w |x_w| ^ P_w`. -/
theorem prod_unitaryPart_infiniteComponent_mul_harmonicFactor (χ : Grossencharacter K 𝔪)
    (x : Kˣ) :
    (∏ w : InfinitePlace K,
        (χ.toHeckeCharacter.unitaryPart.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ)) *
      χ.harmonicFactor (mixedEmbedding K (x : K)) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (x : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  classical
  rw [InfinitePlace.prod_eq_prod_mul_prod, χ.harmonicFactor_def,
    mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    InfinitePlace.prod_eq_prod_mul_prod, ofReal_mul, ofReal_prod, ofReal_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ unitaryPart_real_mul_pow χ w x
  · exact Finset.prod_congr rfl fun w _ ↦ unitaryPart_complex_mul_monomial χ w x

/-- **Archimedean sign and phase cancellation on global units**: for any integer unit `u : (𝓞 K)ˣ`,
multiplying the product of the archimedean components of `χ.toHeckeCharacter` at `u` by
`χ.harmonicFactor (mixedEmbedding K u)` yields `∏_w |u_w| ^ P_w`. At `u = -1` for an odd character
modulo `4∞`, both factors are `-1` and their product is `1`. -/
theorem prod_infiniteComponent_unit_mul_harmonicFactor (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    (∏ w : InfinitePlace K,
        (χ.toHeckeCharacter.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) : ℂ)) *
      χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  set x : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  have hx : (x : K) = algebraMap (𝓞 K) K u := rfl
  have hnorm_one :
      (∏ w : InfinitePlace K,
          ((HeckeCharacter.normPow K χ.toHeckeCharacter.shift).infiniteComponent w
            (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ)) = 1 := by
    simp_rw [HeckeCharacter.coe_infiniteComponent_normPow_apply]
    have hcoord (w : InfinitePlace K) :
        (completionNormalizedAbsValue w
          (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℝ) =
          normAtPlace w (mixedEmbedding K (u : K)) ^ mult w := by
      simp [x, normAtPlace_apply]
    simp_rw [hcoord]
    rw [← TauCeti.ofReal_prod_cpow _ fun w _ ↦ pow_nonneg (normAtPlace_nonneg w _) _,
      ← mixedEmbedding.norm_apply, norm_unit, ofReal_one, one_cpow]
  conv_lhs =>
    rw [← χ.toHeckeCharacter.unitaryPart_mul_normPow_shift]
  simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply,
    Units.val_mul, Finset.prod_mul_distrib, hnorm_one, mul_one, ← hx]
  exact χ.prod_unitaryPart_infiniteComponent_mul_harmonicFactor x

/-! ### Specializations to ray class characters -/

/-- For a ray class character `η`, `harmonicExponent` vanishes at every complex place `w`. -/
theorem harmonicExponent_ofRayClassCharacter_of_isComplex (η : RayClassCharacter 𝔪)
    {w : InfinitePlace K} (hw : w.IsComplex) :
    (ofRayClassCharacter η).harmonicExponent w = 0 := by
  simp [hw]

/-- For a ray class character `η`, `harmonicExponent` at a real place `w` is `1` if and only if `w`
lies in the infinite part of the conductor of `HeckeCharacter.ofRayClassCharacter 𝔪 η`. -/
theorem harmonicExponent_ofRayClassCharacter_eq_one_iff (η : RayClassCharacter 𝔪)
    {w : InfinitePlace K} (hw : w.IsReal) :
    (ofRayClassCharacter η).harmonicExponent w = 1 ↔
      ⟨w, hw⟩ ∈
        ((HeckeCharacter.ofRayClassCharacter 𝔪 η).conductor
          (HeckeCharacter.isFiniteOrder_ofRayClassCharacter η)).infinitePart := by
  rw [(ofRayClassCharacter η).harmonicExponent_of_isReal hw, toHeckeCharacter_ofRayClassCharacter,
    HeckeCharacter.mem_conductor_infinitePart_iff]
  generalize (HeckeCharacter.ofRayClassCharacter 𝔪 η).infinityType.realParity ⟨w, hw⟩ = ε
  revert ε
  decide

@[simp]
theorem harmonicExponent_ofRayClassCharacter_one (w : InfinitePlace K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicExponent w = 0 := by
  rw [harmonicExponent_eq_infinityType, toHeckeCharacter_ofRayClassCharacter, map_one,
    HeckeCharacter.infinityType_one, ContinuousInfinityType.zero_harmonicExponent]

@[simp]
theorem harmonicDegree_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicDegree = 0 := by
  simp [harmonicDegree_def]

@[simp]
theorem harmonicFactor_ofRayClassCharacter_one (x : mixedSpace K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).harmonicFactor x = 1 := by
  rw [harmonicFactor_eq_infinityType, toHeckeCharacter_ofRayClassCharacter, map_one,
    HeckeCharacter.infinityType_one, ContinuousInfinityType.zero_harmonicFactor]

@[simp]
theorem archWeight_ofRayClassCharacter_one (y : realSpace K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).archWeight y = 1 := by
  rw [archWeight_eq_infinityType, toHeckeCharacter_ofRayClassCharacter, map_one,
    HeckeCharacter.infinityType_one, ContinuousInfinityType.zero_archWeight]

@[simp]
theorem heckeEpsilon_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).heckeEpsilon = 1 := by
  rw [heckeEpsilon_eq_one_iff, toHeckeCharacter_ofRayClassCharacter, map_one]
  exact ⟨HeckeCharacter.finiteConductor_one, harmonicDegree_ofRayClassCharacter_one⟩

/-! ### Additional algebraic, regularity, inverse, and congruence compatibility properties -/

open scoped Classical in
/-- Splitting `harmonicDegree` into the real-place parities and complex-place angular
frequencies. -/
theorem harmonicDegree_eq_sum_add_sum (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree =
      (∑ w : {w : InfinitePlace K // w.IsReal},
        (χ.toHeckeCharacter.infinityType.realParity w).val) +
      ∑ w : {w : InfinitePlace K // w.IsComplex},
        ((AlgebraicInfinityType.toContinuous χ.infinityType).complexAngularFrequency w).natAbs := by
  classical
  rw [harmonicDegree_def, InfinitePlace.sum_eq_sum_add_sum]
  refine congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ χ.harmonicExponent_of_isReal w.property)
    (Finset.sum_congr rfl fun w _ ↦ ?_)
  simp [harmonicExponent_def, not_isReal_iff_isComplex.mpr w.property]

/-- The total harmonic degree vanishes if and only if every harmonic exponent vanishes. -/
theorem harmonicDegree_eq_zero_iff (χ : Grossencharacter K 𝔪) :
    χ.harmonicDegree = 0 ↔ ∀ w, χ.harmonicExponent w = 0 := by
  classical simp [harmonicDegree_def]

/-- Inverting a presentation leaves every harmonic exponent unchanged. -/
@[simp]
theorem harmonicExponent_inverse (χ : Grossencharacter K 𝔪) (w : InfinitePlace K) :
    χ.inverse.harmonicExponent w = χ.harmonicExponent w :=
  harmonicExponent_of_toHeckeCharacter_eq_inv (toHeckeCharacter_inverse χ) w

/-- Inverting a presentation preserves `harmonicDegree`. -/
@[simp]
theorem harmonicDegree_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.harmonicDegree = χ.harmonicDegree :=
  harmonicDegree_of_toHeckeCharacter_eq_inv (toHeckeCharacter_inverse χ)

/-- Inverting a presentation conjugates its harmonic polynomial pointwise. -/
@[simp]
theorem harmonicFactor_inverse (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.inverse.harmonicFactor x = conj (χ.harmonicFactor x) :=
  harmonicFactor_of_toHeckeCharacter_eq_inv (toHeckeCharacter_inverse χ) x

/-- Inverting a presentation preserves `archWeight`. -/
@[simp]
theorem archWeight_inverse (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.inverse.archWeight y = χ.archWeight y :=
  archWeight_of_toHeckeCharacter_eq_inv (toHeckeCharacter_inverse χ) y

/-- Inverting a presentation preserves `heckeEpsilon`. -/
@[simp]
theorem heckeEpsilon_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.heckeEpsilon = χ.heckeEpsilon :=
  heckeEpsilon_of_toHeckeCharacter_eq_inv (toHeckeCharacter_inverse χ)

/-- A ray class character of `𝔪` has harmonic exponent `0` at every real place outside `𝔪`. -/
theorem harmonicExponent_ofRayClassCharacter_of_notMem_infinitePart (η : RayClassCharacter 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w ∉ 𝔪.infinitePart) :
    (ofRayClassCharacter η).harmonicExponent w.val = 0 := by
  rw [(ofRayClassCharacter η).harmonicExponent_of_notMem_infinitePart w hw,
    infinityType_ofRayClassCharacter]
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
theorem harmonicExponent_ofRayClassCharacter_of_modulus_one
    (η : RayClassCharacter (Modulus.one K)) (w : InfinitePlace K) :
    (ofRayClassCharacter η).harmonicExponent w = 0 :=
  harmonicExponent_ofRayClassCharacter_of_infinitePart_eq_empty Modulus.one_infinitePart η w

/-- Any presentation of the trivial Hecke character has harmonic exponent `0` everywhere. -/
theorem harmonicExponent_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (w : InfinitePlace K) : χ.harmonicExponent w = 0 := by
  rw [harmonicExponent_eq_infinityType, hχ, HeckeCharacter.infinityType_one,
    ContinuousInfinityType.zero_harmonicExponent]

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

/-- `harmonicFactor` commutes with natural powers on `mixedSpace K`. -/
theorem harmonicFactor_pow (χ : Grossencharacter K 𝔪) (x : mixedSpace K) (n : ℕ) :
    χ.harmonicFactor (x ^ n) = χ.harmonicFactor x ^ n := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_pow]

/-- `harmonicFactor` commutes with coordinatewise inversion on `mixedSpace K`. -/
theorem harmonicFactor_inv (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor x⁻¹ = (χ.harmonicFactor x)⁻¹ := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_inv]

/-- When `harmonicDegree` vanishes, `harmonicFactor` is identically `1`. -/
theorem harmonicFactor_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (x : mixedSpace K) : χ.harmonicFactor x = 1 := by
  rw [harmonicFactor_eq_infinityType]
  rw [harmonicDegree_eq_infinityType] at h
  obtain ⟨hr, hc⟩ := χ.toHeckeCharacter.infinityType.harmonicDegree_eq_zero_iff.mp h
  classical simp [ContinuousInfinityType.harmonicFactor_def, hr, hc]

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

/-- On a real-coordinate vector `mixedSpaceOfRealSpace r`, `harmonicFactor` is the product of
`r w ^ harmonicExponent w` over all infinite places. -/
theorem harmonicFactor_mixedSpaceOfRealSpace (χ : Grossencharacter K 𝔪) (r : realSpace K) :
    χ.harmonicFactor (mixedSpaceOfRealSpace r) =
      ((∏ w : InfinitePlace K, r w ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  simp only [harmonicFactor_eq_infinityType,
    ContinuousInfinityType.harmonicFactor_mixedSpaceOfRealSpace, harmonicExponent_eq_infinityType]

/-- `harmonicFactor` is homogeneous of degree `harmonicDegree` under real scalar multiplication. -/
theorem harmonicFactor_smul (χ : Grossencharacter K 𝔪) (c : ℝ) (x : mixedSpace K) :
    χ.harmonicFactor (c • x) = (c : ℂ) ^ χ.harmonicDegree * χ.harmonicFactor x := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_smul,
    harmonicDegree_eq_infinityType]

/-- When `harmonicDegree` is nonzero, `harmonicFactor` vanishes at the origin. -/
theorem harmonicFactor_zero_of_harmonicDegree_ne_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree ≠ 0) : χ.harmonicFactor 0 = 0 := by
  simp [harmonicFactor_zero_right, h]

/-- Under negation on `mixedSpace K`, `harmonicFactor` transforms by `(-1) ^ harmonicDegree`. -/
theorem harmonicFactor_neg (χ : Grossencharacter K 𝔪) (x : mixedSpace K) :
    χ.harmonicFactor (-x) = (-1 : ℂ) ^ χ.harmonicDegree * χ.harmonicFactor x := by
  simp only [harmonicFactor_eq_infinityType, ContinuousInfinityType.harmonicFactor_neg,
    harmonicDegree_eq_infinityType]

/-- On `K`, `harmonicFactor` commutes with inversion through `mixedEmbedding K`. -/
theorem harmonicFactor_mixedEmbedding_inv (χ : Grossencharacter K 𝔪) (x : K) :
    χ.harmonicFactor (mixedEmbedding K x⁻¹) = (χ.harmonicFactor (mixedEmbedding K x))⁻¹ := by
  have hinv : mixedEmbedding K x⁻¹ = (mixedEmbedding K x)⁻¹ := by
    ext w <;> simp
  rw [hinv, χ.harmonicFactor_inv]

open scoped Classical in
/-- `harmonicFactor` has temperate growth on `mixedSpace K`. -/
@[fun_prop]
theorem hasTemperateGrowth_harmonicFactor (χ : Grossencharacter K 𝔪) :
    χ.harmonicFactor.HasTemperateGrowth := by
  rw [funext χ.harmonicFactor_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.hasTemperateGrowth_harmonicFactor

open scoped Classical in
/-- `harmonicFactor` is smooth (`C^n` for every order `n : WithTop ℕ∞`, including real-analytic)
over `ℝ`. -/
@[fun_prop]
theorem contDiff_harmonicFactor (χ : Grossencharacter K 𝔪) {n : WithTop ℕ∞} :
    ContDiff ℝ n χ.harmonicFactor := by
  rw [funext χ.harmonicFactor_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.contDiff_harmonicFactor

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
  rw [funext χ.harmonicFactor_eq_infinityType]
  exact χ.toHeckeCharacter.infinityType.continuous_harmonicFactor

/-- `harmonicFactor` is measurable on `mixedSpace K`. -/
@[fun_prop]
theorem measurable_harmonicFactor (χ : Grossencharacter K 𝔪) :
    Measurable χ.harmonicFactor :=
  χ.continuous_harmonicFactor.measurable

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
  have hnorm_pow :
      (∏ w : InfinitePlace K,
          ((HeckeCharacter.normPow K χ.toHeckeCharacter.shift).infiniteComponent w
            (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ)) =
        ((mixedEmbedding.norm (mixedEmbedding K (x : K)) : ℝ) : ℂ) ^ (-χ.idealShift : ℂ) := by
    simp_rw [HeckeCharacter.coe_infiniteComponent_normPow_apply]
    have hcoord (w : InfinitePlace K) :
        (completionNormalizedAbsValue w
          (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℝ) =
          normAtPlace w (mixedEmbedding K (x : K)) ^ mult w := by
      simp [normAtPlace_apply]
    simp_rw [hcoord]
    rw [← TauCeti.ofReal_prod_cpow _ fun w _ ↦ pow_nonneg (normAtPlace_nonneg w _) _,
      ← mixedEmbedding.norm_apply, idealShift_def, ofReal_neg, neg_neg]
  have hprod := χ.prod_unitaryPart_infiniteComponent_mul_harmonicFactor x
  simp_rw [normAtPlace_apply] at hprod
  conv_lhs =>
    rw [← χ.toHeckeCharacter.unitaryPart_mul_normPow_shift]
  simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply,
    Units.val_mul, Finset.prod_mul_distrib, hnorm_pow]
  rw [mul_right_comm, hprod, mul_comm]

/-- **Principal-ideal compatibility of `harmonicFactor`** (via `Grossencharacter.compatibility`):
for `a ∈ 𝓞 K` congruent to `1` modulo `𝔪` (`IsCongrOne 𝔪 x`), `χ.harmonicFactor` at the mixed
embedding of `a` equals `χ_u((a)) * ∏_w w(a) ^ harmonicExponent w`. -/
theorem harmonicFactor_mixedEmbedding_of_isCongrOne (χ : Grossencharacter K 𝔪) (x : Kˣ)
    (hx : IsCongrOne 𝔪 x) (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a = x) :
    χ.harmonicFactor (mixedEmbedding K (a : K)) =
      χ.unitaryWeight.val (Ideal.span {a}) *
        ((∏ w : InfinitePlace K, w (a : K) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  have ha' : (a : K) = (x : K) := ha
  have hpos (w : {w : InfinitePlace K // w.IsReal})
      (hw : χ.toHeckeCharacter.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w) :
      0 < InfinitePlace.embedding_of_isReal w.property (x : K) :=
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
    ((∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ) * χ.unitaryWeight.val (Ideal.span {a}) *
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

end Grossencharacter

end TauCeti.LFunctions
