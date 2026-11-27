/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BoundedCoefficients
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar
import TauCeti.MeasureTheory.Constructions.Polish.Units
import TauCeti.NumberTheory.NumberField.Countable
import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteOpenSubgroup
import TauCeti.NumberTheory.NumberField.Global.Places.PowerClasses
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.RingTheory.FractionalIdeal.Norm

/-!
# The finite Tate integral

Let `K` be a number field, `𝔸_{K,f}ˣ` its finite ideles, `Ô^× ⊂ 𝔸_{K,f}ˣ` the everywhere-integral
units and `|x| = ∏_v |x_v|_v` the idele norm, read here as the Haar character
`MeasureTheory.distribHaarChar` of `x` on the finite adeles. For a character `ψ` of the finite
ideles and a set `S` of finite places, this file computes Tate's zeta integral of `ψ` at the finite
places against a function `f` that is determined at `S`: if `f` vanishes unless `x` is integral
outside `S` and a unit at `S`, `f(u) ψ(u) = 1_V(u)` on `Ô^×`, and `f` depends on integral ideles
only through their components at `S`, then for `Re s > 1` and every left-invariant measure `μ` that
is finite on compact sets,

`∫ f(x) ψ(x) |x| ^ s dμ(x) = L^S(s, ψ) · μ(Ô^× ∩ V)`,

where `L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ϖ_v) N(v) ^ (-s))⁻¹` is the partial Euler product
`TauCeti.primeEulerProduct` of the values of `ψ` at uniformizers.

The computation is Tate's, at the finite places only. The fractional ideal of a finite idele
(`IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal`) has kernel `Ô^×`, so the integrand is
supported on the integral ideles, the disjoint union over the nonzero integral ideals `𝔞` of the
cosets `ϖ ^ 𝔞 · Ô^×` (`IsDedekindDomain.FiniteAdeleRing.uniformizerPow`). On the coset of `𝔞` the
idele norm is `N(𝔞)⁻¹` (`IsDedekindDomain.FiniteAdeleRing.coe_distribHaarChar_eq_inv_absNorm`) and
the integrand is `ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s)` times the translate of `1_V`, so by invariance of `μ` its
integral is `ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s) μ(Ô^× ∩ V)`. The map `𝔞 ↦ ψ(ϖ ^ 𝔞)` on the ideals prime to `S`,
extended by zero, is completely multiplicative (`MonoidHom.heckeIdealCharacter`), so the sum of
these terms is the Euler product by `TauCeti.hasSum_primeEulerProduct`.

The Euler product converges when the values `ψ(ϖ_v)` have modulus at most one. This holds for the
characters of interest, the *Hecke characters of type `n`* (`MonoidHom.IsHeckeOfType`): those with
open kernel such that `ψ(x) ∏_w (Φ_w(x) / |Φ_w(x)|) ^ n_w = 1` on `Kˣ`. Such a character is
unitary (`MonoidHom.IsHeckeOfType.norm_eq_one`): `|ψ|` is trivial on `Kˣ` and on an open subgroup,
which together generate a subgroup of finite index.

## Main definitions

* `MonoidHom.heckeCoeff`: the Euler coefficient `ψ(ι_v(ϖ_v))` of a character of the finite ideles.
* `MonoidHom.heckeIdealCharacter`: the completely multiplicative function `𝔞 ↦ ψ(ϖ ^ 𝔞)` on the
  ideals prime to `S`, extended by zero.
* `MonoidHom.IsHeckeOfType`: Hecke characters of type `n` on the finite ideles.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.coe_distribHaarChar_eq_inv_absNorm`: the idele norm of a finite
  idele is the inverse of the absolute norm of its fractional ideal.
* `MonoidHom.hasSum_heckeIdealCharacter_div_absNorm_cpow`: the Dirichlet series of the ideal
  character is the partial Euler product `L^S(s, ψ)`.
* `MonoidHom.IsHeckeOfType.norm_eq_one`: a Hecke character of type `n` is unitary.
* `TauCeti.integrable_mul_distribHaarChar_cpow` and
  `TauCeti.integral_mul_distribHaarChar_cpow_eq_primeEulerProduct_mul`: the finite Tate integral
  converges and equals `L^S(s, ψ) · μ(Ô^× ∩ V)`.

## Provenance

The finite Tate integral, the unitarity of Hecke characters of type `n` and the ideal character
correspond to results of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC), file `src/Lib/ClassField/HeckeL/ContinuationAtOne.lean`:
`New.IsHeckeOfType.integral_mul_finIdeleAbs_rpow_eq_eulerProd_mul`,
`New.IsHeckeOfType.tate_integral`, `New.IsHeckeOfType.norm_eq_one`,
`New.IsHeckeOfType.norm_heckeCoeff_le` and
`New.IsHeckeOfType.exists_monoidHom_asIdeal_eq_heckeCoeff`, and the proof follows its method, an
unfolding over the fibres of the fractional-ideal map. Here the integral is stated for complex `s`,
every left-invariant measure finite on compact sets, every set `S` of places and a measurable `V`,
under a bound on the Euler coefficients alone.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter XV, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField MeasureTheory
open scoped nonZeroDivisors Pointwise

/-! ### The idele norm of a finite idele -/

namespace IsDedekindDomain.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K]

/-- **The idele norm of a finite idele is the inverse norm of its ideal.** Multiplication by a
finite idele `x` of a number field scales additive Haar measure on the finite adeles by
`|x| = ∏_v |x_v|_v = N(x)⁻¹`, where `N(x)` is the absolute norm of the fractional ideal of `x`. -/
theorem coe_distribHaarChar_eq_inv_absNorm (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) =
      (FractionalIdeal.absNorm (toFractionalIdeal x : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹ := by
  -- the component of `x` at `v` has norm `N(v) ^ (-ord_v(x))`
  have hnorm (v : HeightOneSpectrum (𝓞 K)) :
      ‖(x : FiniteAdeleRing (𝓞 K) K) v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-adicOrd x v) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
      (valued_coe_units_apply_ne_zero x v), adicOrd_def, neg_neg, NNReal.coe_zpow,
      NNReal.coe_natCast]
  have hQ (f : HeightOneSpectrum (𝓞 K) → ℚ) : ((∏ᶠ v, f v : ℚ) : ℝ) = ∏ᶠ v, (f v : ℝ) :=
    (Rat.castHom ℝ : ℚ →* ℝ).map_finprod_of_injective Rat.cast_injective f
  have hN (f : HeightOneSpectrum (𝓞 K) → NNReal) :
      ((∏ᶠ v, f v : NNReal) : ℝ) = ∏ᶠ v, (f v : ℝ) :=
    (NNReal.toRealHom : NNReal →* ℝ).map_finprod_of_injective NNReal.coe_injective f
  rw [distribHaarChar_eq_finprod, ← FractionalIdeal.finprod_zpow_count_units_eq_absNorm, hQ, hN,
    ← finprod_inv_distrib]
  refine finprod_congr fun v ↦ ?_
  rw [count_coe_toFractionalIdeal, Rat.cast_zpow, Rat.cast_natCast, ← zpow_neg,
    ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← hnorm,
    ← v.coe_normalizedAbsoluteValue_adicCompletion]
  exact Nonneg.coe_nnratCast _

end IsDedekindDomain.FiniteAdeleRing

/-! ### Euler coefficients and the ideal character -/

namespace MonoidHom

section IdealCharacter

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The **Euler coefficient** at a place `v` of a character `ψ` of the finite ideles, for a choice
`ϖ` of units of the completions: the value `ψ(ι_v(ϖ_v))` of `ψ` at the finite idele with component
`ϖ_v` at `v` and `1` elsewhere. When `ϖ_v` is a uniformizer and `ψ` is trivial on the local units at
`v`, it does not depend on the choice of `ϖ_v` (`MonoidHom.heckeCoeff_eq_of_valued_eq`). -/
def heckeCoeff (ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ) (ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (v : HeightOneSpectrum R) : ℂ :=
  ψ (unitsOfAdicCompletion K v (ϖ v))

variable {ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ} {ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ}
  {S : Set (HeightOneSpectrum R)}

/-- The defining formula of `MonoidHom.heckeCoeff`. -/
theorem heckeCoeff_def (v : HeightOneSpectrum R) :
    ψ.heckeCoeff ϖ v = ψ (unitsOfAdicCompletion K v (ϖ v)) :=
  (rfl)

/-- **The Euler coefficient does not depend on the uniformizer** at a place `v` where `ψ` is
trivial on the local units: `ψ.heckeCoeff ϖ v = ψ(ι_v(π))` for every `π ∈ K_vˣ` with the valuation
of `ϖ_v`, for instance for every uniformizer `π` if `ϖ_v` is one. -/
theorem heckeCoeff_eq_of_valued_eq {v : HeightOneSpectrum R}
    (hψ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ψ (unitsOfAdicCompletion K v u) = 1)
    {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = Valued.v (ϖ v : v.adicCompletion K)) :
    ψ.heckeCoeff ϖ v = ψ (unitsOfAdicCompletion K v π) := by
  -- `π = ϖ_v · (ϖ_v⁻¹ π)`, and `ϖ_v⁻¹ π` is a local unit
  rw [heckeCoeff_def, ← mul_inv_cancel_left (ϖ v) π, map_mul, map_mul, hψ ((ϖ v)⁻¹ * π), mul_one]
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπ,
    inv_mul_cancel₀ (Valued.v.ne_zero_iff.mpr (ϖ v).ne_zero)]

open scoped Classical in
/-- The **ideal character** of a character `ψ` of the finite ideles away from a set `S` of places,
for a choice `ϖ` of units of the completions: the completely multiplicative function on the
integral ideals sending an ideal `𝔞` prime to `S` to `ψ(ϖ ^ 𝔞)`, where
`ϖ ^ 𝔞 = ∏_v ϖ_v ^ ord_v(𝔞)` (`IsDedekindDomain.FiniteAdeleRing.uniformizerPow`), and every other
ideal to `0`. At a prime `v` it is the Euler coefficient `ψ.heckeCoeff ϖ v` if `v ∉ S` and `0` if
`v ∈ S` (`MonoidHom.heckeIdealCharacter_apply_asIdeal`). -/
def heckeIdealCharacter (ψ : 𝔸ᶠ[R, K]ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ) (S : Set (HeightOneSpectrum R)) :
    Ideal R →*₀ ℂ where
  toFun I := if h : I.IsPrimeTo S then
      (ψ (uniformizerPow ϖ (FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.ne_bot⟩)) :
        ℂ)
    else 0
  map_zero' := dite_eq_right Ideal.not_isPrimeTo_bot
  map_one' := by
    rw [dite_eq_left (Ideal.one_eq_top (R := R) ▸ Ideal.isPrimeTo_top)]
    -- the unit of `(Ideal R)⁰` is the unit ideal
    have h1 : (⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ : (Ideal R)⁰) = 1 := rfl
    simp only [h1, map_one, Units.val_one]
  map_mul' I J := by
    by_cases h : (I * J).IsPrimeTo S
    · obtain ⟨hI, hJ⟩ := Ideal.isPrimeTo_mul_iff.mp h
      rw [dite_eq_left h, dite_eq_left hI, dite_eq_left hJ, ← Units.val_mul, ← map_mul,
        ← map_mul, ← map_mul]
      -- products in `(Ideal R)⁰` are computed on the underlying ideals
      rfl
    · rcases not_and_or.mp (fun hc ↦ h (Ideal.isPrimeTo_mul_iff.mpr hc)) with h' | h' <;>
        simp [h, h']

/-- On an ideal `𝔞` prime to `S`, the ideal character is `ψ(ϖ ^ 𝔞)`. -/
@[simp]
theorem heckeIdealCharacter_apply_of_isPrimeTo {I : Ideal R} (hI : I.IsPrimeTo S) :
    ψ.heckeIdealCharacter ϖ S I =
      ψ (uniformizerPow ϖ
        (FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hI.ne_bot⟩)) :=
  dite_eq_left hI

/-- On an ideal not prime to `S`, the ideal character vanishes. -/
@[simp]
theorem heckeIdealCharacter_apply_of_not_isPrimeTo {I : Ideal R} (hI : ¬ I.IsPrimeTo S) :
    ψ.heckeIdealCharacter ϖ S I = 0 :=
  dite_eq_right hI

/-- **The ideal character at a prime** `v` is the Euler coefficient `ψ.heckeCoeff ϖ v` if `v ∉ S`
and `0` if `v ∈ S`. -/
@[simp]
theorem heckeIdealCharacter_apply_asIdeal (v : HeightOneSpectrum R) :
    ψ.heckeIdealCharacter ϖ S v.asIdeal = Sᶜ.indicator (ψ.heckeCoeff ϖ) v := by
  by_cases hv : v ∈ S
  · rw [heckeIdealCharacter_apply_of_not_isPrimeTo (Ideal.isPrimeTo_asIdeal_iff.not.mpr
      (not_not.mpr hv)), Set.indicator_of_notMem (not_not.mpr hv)]
  · rw [heckeIdealCharacter_apply_of_isPrimeTo (Ideal.isPrimeTo_asIdeal_iff.mpr hv),
      Set.indicator_of_mem (Set.mem_compl hv), heckeCoeff_def, ← uniformizerPow_unitOfPrime]
    congr 3
    exact Units.ext (by rw [FractionalIdeal.coe_mk0, HeightOneSpectrum.coe_unitOfPrime])

/-- If the Euler coefficients outside `S` have modulus at most one, so do all values of the ideal
character. -/
theorem norm_heckeIdealCharacter_le_one (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (I : Ideal R) :
    ‖ψ.heckeIdealCharacter ϖ S I‖ ≤ 1 := by
  by_cases hI : I.IsPrimeTo S
  · refine hI.induction_on (by rw [← Ideal.one_eq_top, map_one, norm_one]) fun v J hv _ hJ ↦ ?_
    rw [map_mul, norm_mul, heckeIdealCharacter_apply_asIdeal,
      Set.indicator_of_mem (Set.mem_compl hv)]
    simpa using mul_le_mul (hψ v hv) hJ (norm_nonneg _) zero_le_one
  · rw [heckeIdealCharacter_apply_of_not_isPrimeTo hI, norm_zero]
    exact zero_le_one

end IdealCharacter

section EulerProduct

variable {K : Type*} [Field K] [NumberField K] {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  {ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ} {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The Dirichlet series of the ideal character is the partial Euler product.** If the Euler
coefficients outside `S` have modulus at most one, then for `Re s > 1` the series
`∑_𝔞 ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s)` over the nonzero ideals prime to `S` sums to
`L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ϖ_v) N(v) ^ (-s))⁻¹`. -/
theorem hasSum_heckeIdealCharacter_div_absNorm_cpow (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ ↦
        ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)
      (TauCeti.primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s) := by
  simpa only [heckeIdealCharacter_apply_asIdeal] using
    TauCeti.hasSum_primeEulerProduct _ (norm_heckeIdealCharacter_le_one hψ) hs

end EulerProduct

/-! ### Hecke characters of type `n` -/

section HeckeType

variable {K : Type*} [Field K] [NumberField K]

/-- A character `ψ` of the finite ideles of a number field `K` is a **Hecke character of type `n`**,
for integers `n w` indexed by the infinite places `w` of `K`, when its kernel is open and
`ψ(x) ∏_w (Φ_w(x) / |Φ_w(x)|) ^ n_w = 1` for every `x ∈ Kˣ`, where `Φ_w = w.embedding` is the
embedding `K → ℂ` inducing `w` chosen by Mathlib. Replacing `Φ_w` by its complex conjugate replaces
`n_w` by `-n_w`. -/
structure IsHeckeOfType (ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : InfinitePlace K → ℤ) :
    Prop where
  /-- The kernel of `ψ` is open. -/
  isOpen_ker : IsOpen (ψ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ)
  /-- On the principal finite ideles, `ψ` inverts the angular character of type `n`. -/
  map_unitEmbedding_mul_prod_eq_one (x : Kˣ) :
    (ψ (unitEmbedding (𝓞 K) K x) : ℂ) *
      ∏ w, (w.embedding (x : K) / (‖w.embedding (x : K)‖ : ℂ)) ^ n w = 1

variable {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ} {n : InfinitePlace K → ℤ}

/-- **A Hecke character of type `n` is unitary**: `|ψ(x)| = 1` for every finite idele `x`. The
finite ideles where `ψ` has modulus one form an open subgroup, as it contains the open kernel of
`ψ`, and it contains the principal finite ideles, on which `ψ` is a product of complex numbers of
modulus one. Such a subgroup has finite index
(`NumberField.finiteIndex_of_isOpen_of_totallyPositiveUnits_le`), so some power of every `x` lies
in it. -/
theorem IsHeckeOfType.norm_eq_one (hψ : ψ.IsHeckeOfType n) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ‖(ψ x : ℂ)‖ = 1 := by
  -- the finite ideles where `ψ` has modulus one
  let H : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
    { carrier := {y | ‖(ψ y : ℂ)‖ = 1}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul, norm_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_ofPred_eq, map_inv, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
        rw [ha, inv_one] }
  -- membership in `H` is its defining condition
  have hmem (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : y ∈ H ↔ ‖(ψ y : ℂ)‖ = 1 := Iff.rfl
  have hopen : IsOpen (H : Set (FiniteAdeleRing (𝓞 K) K)ˣ) :=
    Subgroup.isOpen_mono (fun y hy ↦ (hmem y).mpr (by
      rw [MonoidHom.mem_ker.mp hy, Units.val_one, norm_one])) hψ.isOpen_ker
  have hpos : totallyPositiveUnits ≤ H.comap (unitEmbedding (𝓞 K) K) := fun y _ ↦ by
    refine (hmem _).mpr ?_
    -- every factor `Φ_w(y) / |Φ_w(y)|` of the product has modulus one
    have hprod : ‖∏ w, (w.embedding (y : K) / (‖w.embedding (y : K)‖ : ℂ)) ^ n w‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun w _ ↦ ?_
      have hne : ‖w.embedding (y : K)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr ((map_ne_zero _).mpr y.ne_zero)
      rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self hne, one_zpow]
    have h := congrArg norm (hψ.map_unitEmbedding_mul_prod_eq_one y)
    rwa [norm_mul, hprod, mul_one, norm_one] at h
  have := finiteIndex_of_isOpen_of_totallyPositiveUnits_le hopen hpos
  have hx := (hmem _).mp (H.pow_index_mem x)
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at hx
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Subgroup.FiniteIndex.index_ne_zero).mp hx

/-- The Euler coefficients of a Hecke character of type `n` have modulus one. -/
theorem IsHeckeOfType.norm_heckeCoeff (hψ : ψ.IsHeckeOfType n)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖ψ.heckeCoeff ϖ v‖ = 1 :=
  hψ.norm_eq_one _

end HeckeType

end MonoidHom

/-! ### The finite Tate integral -/

namespace TauCeti

section TateIntegral

variable {K : Type*} [Field K] [NumberField K] {μ : Measure (FiniteAdeleRing (𝓞 K) K)ˣ}
  {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ} {ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ}
  {S : Set (HeightOneSpectrum (𝓞 K))} {V : Set (FiniteAdeleRing (𝓞 K) K)ˣ}
  {f : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ} {s : ℂ}

/-- A function vanishing unless `x` is a unit at `S` vanishes on the finite ideles whose fractional
ideal is a nonzero integral ideal divisible by a prime of `S`. -/
private theorem apply_eq_zero_of_not_isPrimeTo
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (I : (Ideal (𝓞 K))⁰) {x : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hx : toFractionalIdeal x = FractionalIdeal.mk0 K I) (hI : ¬ (I : Ideal (𝓞 K)).IsPrimeTo S) :
    f x = 0 := by
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  by_contra h
  obtain ⟨v, hv, hdvd⟩ : ∃ v ∈ S, v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    by_contra! h'
    exact hI (Ideal.isPrimeTo_iff.mpr ⟨hI0, h'⟩)
  have h0 : adicOrd x v = 0 := adicOrd_eq_zero_iff.mpr ((hf₀ x h).2 v hv)
  rw [← count_coe_toFractionalIdeal, hx, FractionalIdeal.coe_mk0,
    FractionalIdeal.count_coeIdeal_eq_zero_iff hI0] at h0
  exact h0 hdvd

/-- On the finite ideles whose fractional ideal is a nonzero integral ideal `I`, the Tate integrand
is the term of `I` in the Dirichlet series of the ideal character on the translate of `V` by
`ϖ ^ I`, and `0` off it. -/
private theorem tateIntegrand_eq_indicator
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (I : (Ideal (𝓞 K))⁰) {x : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hx : toFractionalIdeal x = FractionalIdeal.mk0 K I) :
    f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s =
      (uniformizerPow ϖ (FractionalIdeal.mk0 K I) • V).indicator
        (fun _ ↦ ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s) x := by
  classical
  set y := uniformizerPow ϖ (FractionalIdeal.mk0 K I)
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  -- the idele norm of `x` is `N(I)⁻¹`
  have hnorm : ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s =
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ := by
    rw [coe_distribHaarChar_eq_inv_absNorm, hx, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.inv_cpow _ _ (by
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm)]
  by_cases hI : (I : Ideal (𝓞 K)).IsPrimeTo S
  · -- `u = y⁻¹ x` is an everywhere-integral unit with the components of `x` at `S`
    have hu : y⁻¹ * x ∈ integralUnits (𝓞 K) K := by
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, hx,
        toFractionalIdeal_uniformizerPow hϖ, inv_mul_cancel]
    have hxint : (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K := by
      rw [← toFractionalIdeal_le_one_iff, hx, FractionalIdeal.coe_mk0]
      exact FractionalIdeal.coeIdeal_le_one
    have hS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
        (x : FiniteAdeleRing (𝓞 K) K) v = ((y⁻¹ * x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) v := by
      rw [← coe_unitsProj_apply, ← coe_unitsProj_apply, map_mul, map_inv,
        unitsProj_uniformizerPow, FractionalIdeal.coe_mk0,
        (FractionalIdeal.count_coeIdeal_eq_zero_iff hI0).mpr (hI.not_dvd hv), zpow_zero, inv_one,
        one_mul]
    have hfx : f x = f (y⁻¹ * x) := hf₂ x hxint _ hu hS
    have hψx : (ψ x : ℂ) = ψ y * ψ (y⁻¹ * x) := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
    have h1 := hf₁ _ hu
    rw [hnorm, hfx, hψx, Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
      MonoidHom.heckeIdealCharacter_apply_of_isPrimeTo hI, div_eq_mul_inv]
    by_cases hV : y⁻¹ * x ∈ V
    · rw [Set.indicator_of_mem hV, Pi.one_apply] at h1
      rw [ite_eq_left hV]
      linear_combination (ψ y * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ : ℂ) * h1
    · rw [Set.indicator_of_notMem hV] at h1
      rw [ite_eq_right hV]
      linear_combination (ψ y * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ : ℂ) * h1
  · simp [apply_eq_zero_of_not_isPrimeTo hf₀ I hx hI,
      MonoidHom.heckeIdealCharacter_apply_of_not_isPrimeTo hI]

/-- A finite idele where a function vanishing off the ideles integral outside `S` and units at `S`
is nonzero has a nonzero integral ideal as its fractional ideal. -/
private theorem exists_toFractionalIdeal_eq_mk0
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    {x : (FiniteAdeleRing (𝓞 K) K)ˣ} (hx : f x ≠ 0) :
    ∃ I : (Ideal (𝓞 K))⁰, toFractionalIdeal x = FractionalIdeal.mk0 K I := by
  have hxint : (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K := by
    refine mem_integralAdeles.mpr fun v ↦ ?_
    by_cases hv : v ∈ S
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, (hf₀ x hx).2 v hv]
    · exact (hf₀ x hx).1 v hv
  refine ⟨toIntegralIdeal ⟨x, mem_integralFiniteIdeles.mpr hxint⟩, Units.ext ?_⟩
  rw [FractionalIdeal.coe_mk0, coe_toIntegralIdeal]

/-- The integral, over the finite ideles with fractional ideal `J`, of a constant `e` on the
translate of `V` by `ϖ ^ J` is `μ(Ô^× ∩ V) e`: the fibre is the coset `ϖ ^ J • Ô^×`. -/
private theorem setIntegral_preimage_toFractionalIdeal_indicator [μ.IsMulLeftInvariant]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1)) (hV : MeasurableSet V)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (e : E) :
    ∫ x in toFractionalIdeal ⁻¹' {J}, (uniformizerPow ϖ J • V).indicator (fun _ ↦ e) x ∂μ =
      μ.real (integralUnits (𝓞 K) K ∩ V) • e := by
  rw [integral_indicator_const e (hV.const_smul _), measureReal_restrict_apply (hV.const_smul _),
    preimage_toFractionalIdeal_singleton hϖ, measureReal_def, measureReal_def,
    ← Set.smul_set_inter, measure_smul, Set.inter_comm]

/-- The finite Tate integral converges, and its value is the partial Euler product times
`μ(Ô^× ∩ V)`. -/
private theorem integrable_and_integral_eq [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    Integrable (fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s)
        μ ∧
      ∫ x, f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s ∂μ =
        primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s *
          μ.real (integralUnits (𝓞 K) K ∩ V) := by
  set U := (integralUnits (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)ˣ)
  set F := fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s
  -- the fibre `P I` of the fractional-ideal map over `I` is the coset `y I • Ô^×`, on which `F`
  -- is the constant `c I` on the translate of `V`
  let y (I : (Ideal (𝓞 K))⁰) := uniformizerPow ϖ (FractionalIdeal.mk0 K I)
  let P (I : (Ideal (𝓞 K))⁰) := toFractionalIdeal ⁻¹' {FractionalIdeal.mk0 K I}
  let c (I : (Ideal (𝓞 K))⁰) : ℂ :=
    ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s
  have hc := MonoidHom.hasSum_heckeIdealCharacter_div_absNorm_cpow hψ hs
  have hPm (I) : MeasurableSet (P I) :=
    ((isLocallyConstant_toFractionalIdeal (𝓞 K) K).isOpen_fiber _).measurableSet
  have hFP (I) : Set.EqOn F ((y I • V).indicator fun _ ↦ c I) (P I) := fun _ hx ↦
    tateIntegrand_eq_indicator hϖ hf₀ hf₁ hf₂ I hx
  have hμP (I) : μ (P I) < ⊤ := by
    simp only [P, preimage_toFractionalIdeal_singleton hϖ, measure_smul]
    exact (isCompact_integralUnits (𝓞 K) K).measure_lt_top
  have hint (I) : ∫ x in P I, F x ∂μ = c I * μ.real (U ∩ V) := by
    rw [setIntegral_congr_fun (hPm I) (hFP I),
      setIntegral_preimage_toFractionalIdeal_indicator hϖ hV, Complex.real_smul, mul_comm]
  have hint_norm (I) : ∫ x in P I, ‖F x‖ ∂μ = μ.real (U ∩ V) * ‖c I‖ := by
    rw [setIntegral_congr_fun (hPm I) fun x hx ↦ by
      rw [hFP I hx, norm_indicator_eq_indicator_norm],
      setIntegral_preimage_toFractionalIdeal_indicator hϖ hV, smul_eq_mul]
  have hFint (I) : IntegrableOn F (P I) μ :=
    ((integrableOn_const (hμP I).ne).indicator (hV.const_smul _)).congr_fun (hFP I).symm (hPm I)
  have hdisj : Pairwise (Function.onFun Disjoint P) := fun I J hIJ ↦
    Set.disjoint_left.mpr fun x hxI hxJ ↦ hIJ <| Subtype.ext <| FractionalIdeal.coeIdeal_injective
      (K := K) <| by
        simpa only [FractionalIdeal.coe_mk0] using congrArg Units.val (hxI.symm.trans hxJ)
  have hUnion : IntegrableOn F (⋃ I, P I) μ :=
    integrableOn_iUnion_of_summable_integral_norm hFint <| by
      simpa only [hint_norm] using (summable_norm_iff.mpr hc.summable).mul_left _
  -- `F` vanishes off the integral ideles, which are the union of the fibres
  have hzero : ∀ x ∉ ⋃ I, P I, F x = 0 := fun x hx ↦ by
    by_contra hF
    obtain ⟨I, hI⟩ := exists_toFractionalIdeal_eq_mk0 hf₀
      (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    exact hx (Set.mem_iUnion.mpr ⟨I, hI⟩)
  refine ⟨hUnion.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h := hasSum_integral_iUnion hPm hdisj hUnion
  simp only [hint] at h
  exact h.unique (hc.mul_right _)

/-- **The finite Tate integral converges.** Let `ϖ` be uniformizers of the completions, `S` a set of
places such that the Euler coefficients `ψ(ι_v(ϖ_v))` of `ψ` have modulus at most one outside `S`,
`V` a measurable set of finite ideles, and `f` a function on the finite ideles that vanishes unless
`x` is integral outside `S` and a unit at `S`, satisfies `f(u) ψ(u) = 1_V(u)` on `Ô^×`, and takes
the same value at an integral idele and at an integral unit with the same components at `S` (as it
does when its value on integral ideles depends only on the components at `S`). Then for
`Re s > 1` and every left-invariant measure `μ` that is finite on compact sets,
`f(x) ψ(x) |x| ^ s` is integrable. -/
theorem integrable_mul_distribHaarChar_cpow [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    Integrable
      (fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s) μ :=
  (integrable_and_integral_eq hϖ hψ hV hf₀ hf₁ hf₂ hs).1

/-- **The finite Tate integral.** Under the hypotheses of
`TauCeti.integrable_mul_distribHaarChar_cpow`, for `Re s > 1`,

`∫ f(x) ψ(x) |x| ^ s dμ(x) = L^S(s, ψ) · μ(Ô^× ∩ V)`,

where `L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ι_v(ϖ_v)) N(v) ^ (-s))⁻¹` and `|x|` is the idele norm. For a
Hecke character of type `n` the hypothesis on the Euler coefficients holds for every `S`
(`MonoidHom.IsHeckeOfType.norm_heckeCoeff`). For an open `V ∋ 1` and a Haar measure `μ`, the factor
`μ(Ô^× ∩ V)` is finite and nonzero, `Ô^× ∩ V` being a compact neighbourhood of `1` intersected with
an open one (`TauCeti.isCompact_integralUnits`, `TauCeti.isOpen_integralUnits`). -/
theorem integral_mul_distribHaarChar_cpow_eq_primeEulerProduct_mul [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    ∫ x, f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s ∂μ =
      primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s *
        μ.real (integralUnits (𝓞 K) K ∩ V) :=
  (integrable_and_integral_eq hϖ hψ hV hf₀ hf₁ hf₂ hs).2

end TateIntegral

end TauCeti
