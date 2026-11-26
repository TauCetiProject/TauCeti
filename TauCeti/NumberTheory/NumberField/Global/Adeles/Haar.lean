/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Prod
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace
public import TauCeti.NumberTheory.NumberField.Global.Adeles.LocallyCompact
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.HaarCharacter
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar

/-!
# Normalized Haar measures on the adeles and the idele norm as a Haar character

Let `K` be a number field with `r₂` complex places. This file fixes the normalized additive Haar
measures of the adelic rings of `K` and computes how multiplication by an idele scales them. A
unit `x` scales images by its Haar character, `μ (x • s) = distribHaarChar _ x * μ s`, and so
pushes `μ` forward to `(distribHaarChar _ x)⁻¹ • μ`.

* **The finite adeles.** `μ_f` is the additive Haar measure on `𝔸_{K,f}` giving the integral
  adeles `∏_v 𝒪_v` mass `1`. It is the restricted product of the local Haar measures `μ_v` with
  `μ_v(𝒪_v) = 1` (`TauCeti.GlobalNumberFields.finiteAdeleHaar_eq_restrictedAddHaar`). A finite
  idele `a` has Haar character `∏ᶠ_v ‖a_v‖`, so multiplication by `a` pushes `μ_f` forward to
  `(∏ᶠ_v ‖a_v‖)⁻¹ • μ_f`. These are the general results of
  `TauCeti/RingTheory/DedekindDomain/FiniteAdeleRing/Haar.lean`, specialized to `𝓞 K`.
* **The infinite adeles.** `μ_∞` on `K_∞ = ∏_{w | ∞} K_w` is `2^{r₂}` times the transport of the
  volume of the Minkowski space `ℝ^{r₁} × ℂ^{r₂}`; it is Lebesgue measure at the real places and
  twice Lebesgue measure at the complex places. A unit `x` of `K_∞` has Haar character
  `∏_w ‖x_w‖^{m_w}`, the multiplicity `m_w` being `2` at complex places.
* **The adeles.** `μ_𝔸 = μ_∞ × μ_f` on `𝔸_K = K_∞ × 𝔸_{K,f}`.
* **The idele norm is the Haar character.** For an idele `x`, the Haar character of `x` on the
  additive group of `𝔸_K` is the idele norm `‖x‖`, so multiplication by `x` pushes `μ_𝔸` forward to
  `‖x‖⁻¹ • μ_𝔸`. Its kernel is the norm-one subgroup, and by the product formula every principal
  idele preserves `μ_𝔸`.

The Haar characters do not depend on the normalizations; those enter only in the descriptions of
`μ_f` and `μ_∞`.

## Main definitions

* `TauCeti.GlobalNumberFields.finiteAdeleHaar`, `TauCeti.GlobalNumberFields.infiniteAdeleHaar`,
  `TauCeti.GlobalNumberFields.adeleHaar`.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleHaar_integralAdeles`,
  `TauCeti.GlobalNumberFields.finiteAdeleHaar_eq_restrictedAddHaar`.
* `TauCeti.GlobalNumberFields.infiniteAdeleHaar_apply`, `TauCeti.GlobalNumberFields.adeleHaar_prod`:
  evaluation of the infinite and full adelic measures.
* `TauCeti.GlobalNumberFields.distribHaarChar_finiteAdeleRing`: main's
  `IsDedekindDomain.FiniteAdeleRing.distribHaarChar_eq_finprod`, with the local factors written as
  norms.
* `TauCeti.GlobalNumberFields.distribHaarChar_infiniteAdeleRing`, from the local characters
  `NumberField.InfinitePlace.distribHaarChar_completion`.
* `TauCeti.GlobalNumberFields.distribHaarChar_adeleRing`: the idele norm is the Haar character of
  `𝔸_K`.
* `TauCeti.GlobalNumberFields.map_adeleHaar_mul`,
  `TauCeti.GlobalNumberFields.distribHaarChar_adeleRing_eq_one_iff`,
  `TauCeti.GlobalNumberFields.map_adeleHaar_mul_eq_self_iff`,
  `TauCeti.GlobalNumberFields.map_adeleHaar_mul_unitEmbedding`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism, and restricted Haar products).
* A. V. Sutherland, *Number Theory I*, MIT 18.785 lecture notes, Lecture 23, §23.3, p. 6.
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) computes Haar characters on adele
  rings in `FLT/HaarMeasure/HaarChar/FiniteAdeleRing.lean` (by Kevin Buzzard, Bryan Wang Peng Jun
  and Pietro Monticone) and `FLT/HaarMeasure/HaarChar/AdeleRing.lean` (by Kevin Buzzard, Bryan Wang
  Peng Jun, Salvatore Mercuri, Pietro Monticone and Ruben Van de Velde).
-/

public section

noncomputable section

open IsDedekindDomain MeasureTheory Measure NumberField RestrictedProduct TauCeti
  TopologicalSpace
open scoped NNReal ENNReal

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-! ### The finite adeles -/

/-- **The normalized Haar measure on the finite adeles**: the additive Haar measure on `𝔸_{K,f}`
giving the integral adeles `∏_v 𝒪_v` mass `1`. -/
def finiteAdeleHaar : Measure (FiniteAdeleRing (𝓞 K) K) :=
  addHaarMeasure (FiniteAdeleRing.integralAdelesPositiveCompacts (𝓞 K) K)

theorem finiteAdeleHaar_def :
    finiteAdeleHaar K = addHaarMeasure (FiniteAdeleRing.integralAdelesPositiveCompacts (𝓞 K) K) :=
  (rfl)

instance isAddHaarMeasure_finiteAdeleHaar : (finiteAdeleHaar K).IsAddHaarMeasure := by
  rw [finiteAdeleHaar_def]
  infer_instance

instance regular_finiteAdeleHaar : (finiteAdeleHaar K).Regular := by
  rw [finiteAdeleHaar_def]
  infer_instance

/-- The integral adeles have mass `1` for `finiteAdeleHaar`. -/
@[simp]
theorem finiteAdeleHaar_integralAdeles :
    finiteAdeleHaar K (FiniteAdeleRing.integralAdeles (𝓞 K) K) = 1 :=
  FiniteAdeleRing.coe_integralAdelesPositiveCompacts (𝓞 K) K ▸ addHaarMeasure_self

/-- An additive Haar measure on `𝔸_{K,f}` giving the integral adeles mass `1` is
`finiteAdeleHaar`. -/
theorem eq_finiteAdeleHaar {μ : Measure (FiniteAdeleRing (𝓞 K) K)} [μ.IsAddHaarMeasure]
    (hμ : μ (FiniteAdeleRing.integralAdeles (𝓞 K) K) = 1) : μ = finiteAdeleHaar K :=
  ((addHaarMeasure_eq_iff (FiniteAdeleRing.integralAdelesPositiveCompacts (𝓞 K) K) μ).2 hμ).symm

/-- **`finiteAdeleHaar` is a restricted product of local Haar measures**: it is the restricted
product of the normalized additive Haar measures `μ_v` on the local fields `K_v`, those with
`μ_v(𝒪_v) = 1` (`TauCeti.existsUnique_isAddHaarMeasure_measure_integer_eq_one`). This is
`IsDedekindDomain.FiniteAdeleRing.addHaarMeasure_eq_restrictedAddHaar` for these measures. -/
theorem finiteAdeleHaar_eq_restrictedAddHaar :
    finiteAdeleHaar K =
      restrictedAddHaar (G := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
        (fun v ↦ v.adicCompletionIntegers K)
        (fun v ↦ addHaarMeasure (integerPositiveCompacts (v.adicCompletion K)))
        (.of_forall HeightOneSpectrum.addHaarMeasure_adicCompletionIntegers) :=
  FiniteAdeleRing.addHaarMeasure_eq_restrictedAddHaar (𝓞 K) K _
    HeightOneSpectrum.addHaarMeasure_adicCompletionIntegers

/-- **The Haar character of a finite idele**, in terms of the norms of the local fields: a finite
idele `a` scales Haar measure on `𝔸_{K,f}` by `∏ᶠ_v ‖a_v‖`. This is
`IsDedekindDomain.FiniteAdeleRing.distribHaarChar_eq_finprod`, whose local factors `|a_v|_v` are
the norms `‖a_v‖` (`IsDedekindDomain.HeightOneSpectrum.coe_normalizedAbsoluteValue_adicCompletion`).
-/
@[simp]
theorem distribHaarChar_finiteAdeleRing (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    distribHaarChar (FiniteAdeleRing (𝓞 K) K) a =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a : FiniteAdeleRing (𝓞 K) K) v‖₊ := by
  rw [FiniteAdeleRing.distribHaarChar_eq_finprod]
  refine finprod_congr fun v ↦ NNReal.eq ?_
  simpa using v.coe_normalizedAbsoluteValue_adicCompletion ((a : FiniteAdeleRing (𝓞 K) K) v)

/-! ### The infinite adeles -/

/-- **The Haar character of the infinite adeles.** A unit `x` of `K_∞` scales Haar measure by
`∏_w ‖x_w‖ ^ m_w`. -/
@[simp]
theorem distribHaarChar_infiniteAdeleRing (x : (InfiniteAdeleRing K)ˣ) :
    distribHaarChar (InfiniteAdeleRing K) x =
      ∏ w : InfinitePlace K, ‖(x : InfiniteAdeleRing K) w‖₊ ^ w.mult := by
  exact (distribHaarChar_pi (T := fun w : InfinitePlace K ↦ w.Completion) x).trans
    (Finset.prod_congr rfl fun w _ ↦ InfinitePlace.distribHaarChar_completion w _)

open scoped Classical in
/-- **The normalized Haar measure on the infinite adeles**: `2 ^ r₂` times the transport of the
volume of the Minkowski space `ℝ^{r₁} × ℂ^{r₂}`, that is, Lebesgue measure at the real places and
twice Lebesgue measure at the complex places. The transport along
`NumberField.InfiniteAdeleRing.continuousAddEquivMixedSpace` is an additive Haar measure by
Mathlib's `ContinuousAddEquiv.isAddHaarMeasure_map`. -/
def infiniteAdeleHaar : Measure (InfiniteAdeleRing K) :=
  (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces K •
    (volume : Measure (mixedEmbedding.mixedSpace K)).map
      (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm

open scoped Classical in
theorem infiniteAdeleHaar_def :
    infiniteAdeleHaar K = (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces K •
      (volume : Measure (mixedEmbedding.mixedSpace K)).map
        (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm :=
  (rfl)

open scoped Classical in
/-- `infiniteAdeleHaar` evaluated on a set: `2 ^ r₂` times the volume of its image in the
Minkowski space. -/
theorem infiniteAdeleHaar_apply (s : Set (InfiniteAdeleRing K)) :
    infiniteAdeleHaar K s = 2 ^ InfinitePlace.nrComplexPlaces K *
      volume (InfiniteAdeleRing.continuousAddEquivMixedSpace K '' s) := by
  have he : MeasurableEmbedding (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm :=
    (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm.toHomeomorph.measurableEmbedding
  rw [infiniteAdeleHaar_def, _root_.smul_apply, he.map_apply, smul_eq_mul]
  exact congrArg (_ * volume ·)
    ((InfiniteAdeleRing.continuousAddEquivMixedSpace K).toHomeomorph.image_eq_preimage_symm s).symm

open scoped Classical in
instance isAddHaarMeasure_infiniteAdeleHaar : (infiniteAdeleHaar K).IsAddHaarMeasure := by
  have : ((volume : Measure (mixedEmbedding.mixedSpace K)).map
      (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm).IsAddHaarMeasure :=
    (InfiniteAdeleRing.continuousAddEquivMixedSpace K).symm.isAddHaarMeasure_map _
  rw [infiniteAdeleHaar_def]
  exact IsAddHaarMeasure.smul _ (by simp) (by simp)

/-! ### The adeles and the ideles -/

/-- **The normalized Haar measure on the adeles**: the product `μ_∞ × μ_f` of
`infiniteAdeleHaar` and `finiteAdeleHaar` on `𝔸_K = K_∞ × 𝔸_{K,f}`. -/
def adeleHaar : Measure (AdeleRing (𝓞 K) K) :=
  (infiniteAdeleHaar K).prod (finiteAdeleHaar K)

theorem adeleHaar_def : adeleHaar K = (infiniteAdeleHaar K).prod (finiteAdeleHaar K) :=
  (rfl)

/-- `adeleHaar` on a box `s × t` is the product of the masses of its two factors. -/
@[simp]
theorem adeleHaar_prod (s : Set (InfiniteAdeleRing K)) (t : Set (FiniteAdeleRing (𝓞 K) K)) :
    adeleHaar K (s ×ˢ t) = infiniteAdeleHaar K s * finiteAdeleHaar K t := by
  rw [adeleHaar_def]
  exact prod_prod s t

instance isAddHaarMeasure_adeleHaar : (adeleHaar K).IsAddHaarMeasure :=
  inferInstanceAs <|
    ((infiniteAdeleHaar K).prod (finiteAdeleHaar K)).IsAddHaarMeasure

/-- **The idele norm is the Haar character of the adeles.** Multiplication by an idele `x`
scales additive Haar measure on `𝔸_K` by the idele norm `‖x‖`: `μ (x • s) = ‖x‖ * μ s` for
regular additive Haar measures `μ`. -/
@[simp]
theorem distribHaarChar_adeleRing (x : IdeleGroup (𝓞 K) K) :
    distribHaarChar (AdeleRing (𝓞 K) K) x = ideleNorm x := by
  have h := distribHaarChar_prod (R := InfiniteAdeleRing K) (S := FiniteAdeleRing (𝓞 K) K) x
  refine h.trans ?_
  rw [distribHaarChar_infiniteAdeleRing, distribHaarChar_finiteAdeleRing]
  refine NNReal.eq ?_
  rw [coe_ideleNorm, NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    simp [InfinitePlace.completionNormalizedAbsValue_apply, InfinitePlace.coe_ideleInfiniteCoord]
  · refine ((NNReal.toRealHom : ℝ≥0 →* ℝ).map_finprod_of_injective NNReal.coe_injective _).trans
      (finprod_congr fun v ↦ ?_)
    simp [HeightOneSpectrum.coe_ideleFiniteCoord]

/-- **Pushforward of the adelic Haar measure.** Multiplication by an idele `x` pushes `adeleHaar`
forward to `‖x‖⁻¹ • adeleHaar`. -/
theorem map_adeleHaar_mul (x : IdeleGroup (𝓞 K) K) :
    (adeleHaar K).map ((x : AdeleRing (𝓞 K) K) * ·) = (ideleNorm x : ℝ≥0)⁻¹ • adeleHaar K := by
  simp_rw [← smul_eq_mul, ← Units.smul_def]
  rw [map_smul_eq_inv_distribHaarChar_smul, distribHaarChar_adeleRing]

/-- The kernel of the Haar character of the adeles is the norm-one subgroup of the ideles. -/
theorem distribHaarChar_adeleRing_eq_one_iff (x : IdeleGroup (𝓞 K) K) :
    distribHaarChar (AdeleRing (𝓞 K) K) x = 1 ↔ ideleNorm x = 1 := by
  rw [distribHaarChar_adeleRing, Units.val_eq_one]

/-- An idele preserves `adeleHaar` under multiplication exactly when its idele norm is `1`. -/
theorem map_adeleHaar_mul_eq_self_iff (x : IdeleGroup (𝓞 K) K) :
    (adeleHaar K).map ((x : AdeleRing (𝓞 K) K) * ·) = adeleHaar K ↔ ideleNorm x = 1 := by
  simp_rw [← smul_eq_mul, ← Units.smul_def]
  rw [map_smul_eq_self_iff_distribHaarChar_eq_one, distribHaarChar_adeleRing_eq_one_iff]

/-- **The product formula, measure-theoretically.** Multiplication by a principal idele preserves
`adeleHaar`. -/
theorem map_adeleHaar_mul_unitEmbedding (a : Kˣ) :
    (adeleHaar K).map ((IdeleGroup.unitEmbedding (𝓞 K) K a : AdeleRing (𝓞 K) K) * ·) =
      adeleHaar K := by
  rw [map_adeleHaar_mul, ideleNorm_unitEmbedding, Units.val_one, inv_one, one_smul]

end TauCeti.GlobalNumberFields
