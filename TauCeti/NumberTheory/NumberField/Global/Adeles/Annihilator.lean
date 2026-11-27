/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.AddChar
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.DedekindDomain.Different
import TauCeti.Algebra.Group.AddChar.Basic
import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic

/-!
# A number field is its own annihilator in its adeles

Let `K` be a number field with adele ring `𝔸 = K∞ × 𝔸ᶠ` and standard additive character
`ψ = adeleAddChar K`, `ψ (x) = exp (-2πi ∑_w Tr_{K_w/ℝ} x_w) · ψ_f (x_f)`, which is trivial on `K`.
This file proves that `K` is exactly its own annihilator under the pairing `(x, y) ↦ ψ (x y)`:
an adele `y` with `ψ (ξ y) = 1` for every `ξ ∈ K` lies in `K`. It follows that the pairing is
nondegenerate, so `ψ` is nontrivial and `y ↦ (x ↦ ψ (x y))` is injective.

The proof is elementary and uses no Pontryagin duality.

* The values of `ψ_f` are `exp (2πi q)` with `q` rational, since by strong approximation every
  finite adele is an element of `K` plus an integral finite adele. So if `ψ (ξ y) = 1` for all
  `ξ ∈ K`, every trace `∑_w Tr_{K_w/ℝ} (ξ y_∞)_w` is rational.
* An infinite adele all of whose traces against `K` are rational lies in `K`. In the mixed space
  `ℝ^{r₁} × ℂ^{r₂}` the trace is `ℝ`-linear, and the images of an integral basis `(v_i)` of `K`
  form an `ℝ`-basis (`NumberField.mixedEmbedding.latticeBasis`); pairing with the trace dual basis
  shows that the coordinates of `y_∞` are rational.
* Subtracting that element of `K`, the finite part `z` satisfies `ψ_f (ξ z) = 1` for every
  `ξ ∈ K`, hence for every finite adele `ξ` because `K` is dense in `𝔸ᶠ`. By the annihilator of
  `Ô` under `ψ_f` (`forall_finiteAdeleAddChar_mul_eq_one_iff`), all multiples of `z` lie in
  `𝔇⁻¹ Ô`; multiplying by an element of the different, all multiples of `z` by elements of `K` are
  integral, which forces `z = 0`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.eq_zero_of_forall_algebraMap_mul_mem_integralAdeles`: a finite
  adele whose multiples by every element of `K` are integral is zero.
* `TauCeti.GlobalNumberFields.exists_finiteAdeleAddChar_eq_fourierChar`: the values of `ψ_f` are
  `exp (2πi q)` with `q ∈ ℚ`.
* `TauCeti.GlobalNumberFields.eq_zero_of_forall_finiteAdeleAddChar_algebraMap_mul_eq_one`: a finite
  adele `z` with `ψ_f (ξ z) = 1` for every `ξ ∈ K` is zero.
* `TauCeti.GlobalNumberFields.exists_algebraMap_eq_of_forall_infiniteAdeleTrace_mul_eq_ratCast`: an
  infinite adele whose traces against `K` are all rational lies in `K`.
* `TauCeti.GlobalNumberFields.forall_adeleAddChar_algebraMap_mul_eq_one_iff`: **`K^⊥ = K`**, an
  adele `y` satisfies `ψ (ξ y) = 1` for all `ξ ∈ K` exactly when `y ∈ K`.
* `TauCeti.GlobalNumberFields.forall_adeleAddChar_sum_mul_eq_one_iff`: the same for `K^n ⊂ 𝔸^n`
  with the pairing `ψ (∑_i ξ_i y_i)`.
* `TauCeti.GlobalNumberFields.eq_zero_of_forall_adeleAddChar_mul_eq_one`,
  `TauCeti.GlobalNumberFields.injective_mulShift_adeleAddChar`,
  `TauCeti.GlobalNumberFields.adeleAddChar_ne_one`: the pairing `ψ (x y)` on `𝔸` is
  nondegenerate, and `ψ` is nontrivial.

The standard character of AnalyticNumberTheoryPartII §5.3g is `x ↦ ψ (-x)`; all statements here
hold for it as well, since `ψ (-x) = 1` exactly when `ψ (x) = 1`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory* (1967), Theorem 4.1.4.

The argument follows grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC), `src/Lib/Adelic/Adeles/StrongApproximation.lean` (`New.exists_ψf_eq_fourierChar`,
`New.eq_zero_of_forall_mul_integral`, `New.eq_of_forall_ψf_mul_eq`,
`New.exists_eq_Φ_of_forall_sum_re_rat`, `New.mem_ratAdeles_of_stdAddChar_eq_one`,
`New.eq_zero_of_forall_stdAddChar_eq_one`), where it is proved for totally complex fields; here
it is stated for every number field.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
open scoped NumberField.AdeleRing nonZeroDivisors

/-! ### Finite adeles of a Dedekind domain -/

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **A finite adele whose multiples by `K` are all integral is zero.** If `x z` is an integral
finite adele for every `x ∈ K`, then `z` lies in every neighbourhood `r Ô` of `0`, `r ∈ R`
nonzero. -/
theorem eq_zero_of_forall_algebraMap_mul_mem_integralAdeles {z : FiniteAdeleRing R K}
    (hz : ∀ x : K, algebraMap K (FiniteAdeleRing R K) x * z ∈ integralAdeles R K) : z = 0 := by
  refine pure_le_nhds_iff.mp (Filter.le_def.mpr fun U hU ↦ Filter.mem_pure.mpr ?_)
  -- `U` contains the integral adeles that are divisible by `∏_{v ∈ I} v ^ n v`
  obtain ⟨I, n, hIn⟩ := exists_finset_forall_mem_of_mem_nhds_zero hU
  have hN : ∏ v ∈ I, v.asIdeal ^ n v ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ ↦ pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrN, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  -- `z = r * w` with `w = r⁻¹ z` integral
  set w := algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)⁻¹ * z
  have hzw : z = algebraMap R (FiniteAdeleRing R K) r * w := by
    rw [IsScalarTower.algebraMap_apply R K, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hrK, map_one,
      one_mul]
  rw [hzw]
  refine hIn _ (mul_mem ((integralAdeles R K).algebraMap_mem r) (hz _)) fun v hv ↦ ?_
  have hrv : r ∈ v.asIdeal ^ n v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) hrN
  have hwv : Valued.v (w v) ≤ 1 := mem_integralAdeles.mp (hz _) v
  change Valued.v (algebraMap R (v.adicCompletion K) r * w v) ≤ _
  rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
    HeightOneSpectrum.valuation_of_algebraMap]
  calc v.intValuation r * Valued.v (w v) ≤ v.intValuation r * 1 := by gcongr
    _ ≤ _ := by rw [mul_one]; exact (v.intValuation_le_pow_iff_mem r (n v)).mpr hrv

end IsDedekindDomain.FiniteAdeleRing

/-! ### The trace of the mixed space -/

namespace NumberField.mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The trace `∑_{w real} y_w + ∑_{w complex} 2 Re y_w` of the mixed space, an `ℝ`-linear form.
It is the trace of the infinite adeles read through `InfiniteAdeleRing.ringEquiv_mixedSpace`. -/
private def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun y := ∑ w : {w : InfinitePlace K // IsReal w}, y.1 w +
    ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (y.2 w).re
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re,
    mul_add, Finset.sum_add_distrib]; ring
  map_smul' c y := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by ring

variable {K}

/-- The trace of the infinite adeles is the trace of the mixed space. -/
private theorem infiniteAdeleTrace_eq_mixedTrace (x : InfiniteAdeleRing K) :
    TauCeti.GlobalNumberFields.infiniteAdeleTrace K x =
      mixedTrace K (InfiniteAdeleRing.ringEquiv_mixedSpace K x) := by
  classical
  rw [TauCeti.GlobalNumberFields.infiniteAdeleTrace_apply,
    ← Fintype.sum_subtype_add_sum_subtype IsReal]
  simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  congr 1
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [mult_isReal w, Nat.cast_one, one_mul,
      ← Completion.extensionEmbeddingOfIsReal_apply w.property, Complex.ofReal_re]
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex) _ _
      fun w ↦ ?_
    have hw : ¬IsReal w.val := w.property
    simp only [mult, hw, ↓reduceIte, Nat.cast_ofNat]
    rfl

/-- On the image of `K`, the trace of the mixed space is `Tr_{K/ℚ}`. -/
private theorem mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = Algebra.trace ℚ K x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← infiniteAdeleTrace_eq_mixedTrace,
    TauCeti.GlobalNumberFields.infiniteAdeleTrace_algebraMap]

/-- **A point of the mixed space with rational traces against `K` lies in `K`.** Its coordinates
in the `ℝ`-basis `latticeBasis K` are its traces against the trace dual of the integral basis. -/
private theorem exists_mixedEmbedding_eq_of_forall_mixedTrace_mul_eq_ratCast {y : mixedSpace K}
    (h : ∀ b : K, ∃ q : ℚ, mixedTrace K (mixedEmbedding K b * y) = q) :
    ∃ a : K, mixedEmbedding K a = y := by
  classical
  set β := latticeBasis K
  set v := integralBasis K
  -- the trace of `b y` is linear in the coordinates `c` of `y`
  have hpair (b : K) :
      mixedTrace K (mixedEmbedding K b * y) = ∑ i, β.repr y i * Algebra.trace ℚ K (b * v i) := by
    conv_lhs => rw [← β.sum_repr y]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, latticeBasis_apply, ← map_mul,
      mixedTrace_mixedEmbedding]
  -- pairing with the trace dual basis picks out a coordinate, which is therefore rational
  have hrat (j) : ∃ q : ℚ, β.repr y j = q := by
    obtain ⟨q, hq⟩ := h (v.traceDual j)
    refine ⟨q, ?_⟩
    rw [← hq, hpair, Finset.sum_eq_single j (fun i _ hij ↦ by simp [hij]) (by simp)]
    simp
  choose q hq using hrat
  refine ⟨∑ j, q j • v j, ?_⟩
  conv_rhs => rw [← β.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_rat_smul, hq, Rat.cast_smul_eq_qsmul, latticeBasis_apply]

end NumberField.mixedEmbedding

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The finite part -/

/-- `Real.fourierChar x = 1` exactly when `x` is an integer. -/
private theorem fourierChar_eq_one_iff {x : ℝ} : Real.fourierChar x = 1 ↔ ∃ n : ℤ, x = n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  refine exists_congr fun n ↦ ?_
  constructor <;> intro h
  · nlinarith [Real.pi_pos]
  · rw [h]; ring

/-- **The values of `ψ_f` are rational phases**: `ψ_f (a) = exp (2πi q)` with `q ∈ ℚ`, namely
`q = Tr_{K/ℚ} x` for any `x ∈ K` with `a - x` integral. -/
theorem exists_finiteAdeleAddChar_eq_fourierChar (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ q : ℚ, finiteAdeleAddChar K a = Real.fourierChar q := by
  obtain ⟨x, -, hx⟩ := exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem
  exact ⟨Algebra.trace ℚ K x, by
    rw [finiteAdeleAddChar_apply_of_sub_mem (sub_mem_comm_iff.mp hx), numberFieldTraceChar_apply]⟩

/-- **`ψ_f` separates points from `K`-multiples**: a finite adele `z` with `ψ_f (ξ z) = 1` for every
`ξ ∈ K` is zero. -/
theorem eq_zero_of_forall_finiteAdeleAddChar_algebraMap_mul_eq_one {z : FiniteAdeleRing (𝓞 K) K}
    (hz : ∀ ξ : K, finiteAdeleAddChar K (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ * z) = 1) :
    z = 0 := by
  -- by density of `K`, `ψ_f (t z) = 1` for every finite adele `t`
  have hall (t : FiniteAdeleRing (𝓞 K) K) : finiteAdeleAddChar K (t * z) = 1 :=
    (denseRange_algebraMap (𝓞 K) K).induction_on t
      (isClosed_eq (continuous_finiteAdeleAddChar.comp (continuous_id.mul continuous_const))
        continuous_const) hz
  set D := Units.mk0 (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  -- so every multiple `t z` lies in `𝔇⁻¹ Ô`
  have hmem (t : FiniteAdeleRing (𝓞 K) K) : t * z ∈ finiteAdelicIdeal D :=
    (forall_finiteAdeleAddChar_mul_eq_one_iff (t * z)).mp fun u _ ↦ by
      rw [mul_right_comm]; exact hall _
  -- a nonzero element `d` of the different multiplies `𝔇⁻¹ Ô` into `Ô`
  obtain ⟨d, hdD, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ)
    (B := 𝓞 K))
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hd : algebraMap K (FiniteAdeleRing (𝓞 K) K) d ∈ finiteAdelicIdeal D⁻¹ := by
    rw [algebraMap_mem_finiteAdelicIdeal_iff, Units.val_inv_eq_inv_val, Units.val_mk0,
      ← coeIdeal_differentIdeal ℤ ℚ]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hdD
  refine eq_zero_of_forall_algebraMap_mul_mem_integralAdeles fun x ↦ ?_
  have h := mul_mem_finiteAdelicIdeal hd (hmem (algebraMap K _ (x / d)))
  rwa [inv_mul_cancel, mem_finiteAdelicIdeal_one, ← mul_assoc, ← map_mul,
    mul_div_cancel₀ _ hdK] at h

/-! ### The infinite part -/

/-- **An infinite adele with rational traces against `K` lies in `K`**: if
`∑_w Tr_{K_w/ℝ} (ξ x)_w` is rational for every `ξ ∈ K`, then `x` is the image of an element
of `K`. -/
theorem exists_algebraMap_eq_of_forall_infiniteAdeleTrace_mul_eq_ratCast
    {x : InfiniteAdeleRing K}
    (h : ∀ ξ : K, ∃ q : ℚ, infiniteAdeleTrace K (algebraMap K (InfiniteAdeleRing K) ξ * x) = q) :
    ∃ a : K, algebraMap K (InfiniteAdeleRing K) a = x := by
  obtain ⟨a, ha⟩ := mixedEmbedding.exists_mixedEmbedding_eq_of_forall_mixedTrace_mul_eq_ratCast
    (y := InfiniteAdeleRing.ringEquiv_mixedSpace K x) fun ξ ↦ by
      obtain ⟨q, hq⟩ := h ξ
      refine ⟨q, ?_⟩
      rw [← hq, mixedEmbedding.infiniteAdeleTrace_eq_mixedTrace,
        map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K),
        InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  refine ⟨a, (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective ?_⟩
  rw [← ha, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

/-! ### The annihilator of `K` in the adeles -/

/-- If `y` is in the annihilator of `K` and `a ∈ K`, then so is `y - a`. -/
private theorem forall_adeleAddChar_algebraMap_mul_sub_eq_one {y : 𝔸[K]}
    (h : ∀ ξ : K, adeleAddChar K (algebraMap K 𝔸[K] ξ * y) = 1) (a ξ : K) :
    adeleAddChar K (algebraMap K 𝔸[K] ξ * (y - algebraMap K 𝔸[K] a)) = 1 := by
  rw [mul_sub, ← map_mul, AddChar.map_sub_eq_div, h, adeleAddChar_algebraMap, div_one]

/-- **`K` is its own annihilator in the adeles** (Tate's thesis, Theorem 4.1.4): an adele `y`
satisfies `ψ (ξ y) = 1` for every `ξ ∈ K` exactly when `y ∈ K`, where `ψ = adeleAddChar K` is the
standard character. -/
theorem forall_adeleAddChar_algebraMap_mul_eq_one_iff (y : 𝔸[K]) :
    (∀ ξ : K, adeleAddChar K (algebraMap K 𝔸[K] ξ * y) = 1) ↔
      y ∈ Set.range (algebraMap K 𝔸[K]) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro ⟨a, rfl⟩ ξ
    rw [← map_mul, adeleAddChar_algebraMap]
  -- the traces of the infinite part against `K` are rational, so it is some `a ∈ K`
  have hrat (ξ : K) : ∃ q : ℚ,
      infiniteAdeleTrace K (algebraMap K (InfiniteAdeleRing K) ξ * y.1) = q := by
    obtain ⟨q, hq⟩ := exists_finiteAdeleAddChar_eq_fourierChar
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ * y.2)
    have h1 := h ξ
    rw [adeleAddChar_apply, Prod.fst_mul, Prod.snd_mul, AdeleRing.algebraMap_fst_def,
      AdeleRing.algebraMap_snd_def, hq, infiniteAdeleAddChar_apply, ← AddChar.map_add_eq_mul,
      fourierChar_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨q - n, by push_cast; linarith⟩
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_forall_infiniteAdeleTrace_mul_eq_ratCast hrat
  -- `y - a` has infinite part zero, so its finite part is annihilated by `K` under `ψ_f`
  refine ⟨a, (sub_eq_zero.mp (Prod.ext ?_ ?_)).symm⟩
  · rw [Prod.fst_sub, AdeleRing.algebraMap_fst_def, ha, sub_self, Prod.fst_zero]
  · refine eq_zero_of_forall_finiteAdeleAddChar_algebraMap_mul_eq_one fun ξ ↦ ?_
    have h1 := forall_adeleAddChar_algebraMap_mul_sub_eq_one h a ξ
    rwa [adeleAddChar_apply, Prod.fst_mul, Prod.fst_sub, AdeleRing.algebraMap_fst_def,
      AdeleRing.algebraMap_fst_def, ha, sub_self, mul_zero, AddChar.map_zero_eq_one, one_mul,
      Prod.snd_mul, AdeleRing.algebraMap_snd_def] at h1

/-- **`K^n` is its own annihilator in `𝔸^n`**: for a finite family `y` of adeles,
`ψ (∑_i ξ_i y_i) = 1` for every family `ξ` of elements of `K` exactly when every `y_i` lies
in `K`. -/
theorem forall_adeleAddChar_sum_mul_eq_one_iff {ι : Type*} [Fintype ι] (y : ι → 𝔸[K]) :
    (∀ ξ : ι → K, adeleAddChar K (∑ i, algebraMap K 𝔸[K] (ξ i) * y i) = 1) ↔
      ∀ i, y i ∈ Set.range (algebraMap K 𝔸[K]) := by
  classical
  refine ⟨fun h i ↦ (forall_adeleAddChar_algebraMap_mul_eq_one_iff _).mp fun η ↦ ?_,
    fun h ξ ↦ ?_⟩
  · have hi := h (Pi.single i η)
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul])
      (by simp), Pi.single_eq_same] at hi
  · rw [AddChar.map_sum_eq_prod]
    exact Finset.prod_eq_one fun i _ ↦
      (forall_adeleAddChar_algebraMap_mul_eq_one_iff (y i)).mpr (h i) (ξ i)

/-- **The pairing `ψ (x y)` on the adeles is nondegenerate**: if `ψ (u y) = 1` for every adele `u`,
then `y = 0`. -/
theorem eq_zero_of_forall_adeleAddChar_mul_eq_one {y : 𝔸[K]}
    (h : ∀ u : 𝔸[K], adeleAddChar K (u * y) = 1) : y = 0 := by
  obtain ⟨a, rfl⟩ := (forall_adeleAddChar_algebraMap_mul_eq_one_iff y).mp fun ξ ↦ h _
  -- testing against the finite adeles shows that the finite part of `a` vanishes
  have hfin : algebraMap K (FiniteAdeleRing (𝓞 K) K) a = 0 :=
    eq_zero_of_forall_finiteAdeleAddChar_algebraMap_mul_eq_one fun ξ ↦ by
      have h1 := h (0, algebraMap K _ ξ)
      rwa [adeleAddChar_apply, Prod.fst_mul, Prod.snd_mul, AdeleRing.algebraMap_snd_def,
        show ((0, algebraMap K _ ξ) : 𝔸[K]).1 = 0 from rfl, zero_mul,
        AddChar.map_zero_eq_one, one_mul] at h1
  rw [(map_eq_zero_iff _ (FiniteAdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)
    (RingOfIntegers.not_isField K))).mp hfin, map_zero]

/-- The map `y ↦ (x ↦ ψ (x y))` from the adeles to their additive characters is injective. -/
theorem injective_mulShift_adeleAddChar : Function.Injective (adeleAddChar K).mulShift := by
  intro y y' hyy'
  refine sub_eq_zero.mp (eq_zero_of_forall_adeleAddChar_mul_eq_one fun u ↦ ?_)
  have hu := DFunLike.congr_fun hyy' u
  rw [AddChar.mulShift_apply, AddChar.mulShift_apply] at hu
  rw [mul_sub, AddChar.map_sub_eq_div, mul_comm u, mul_comm u, hu, div_self']

/-- **The standard character of the adeles is nontrivial.** -/
theorem adeleAddChar_ne_one : adeleAddChar K ≠ 1 := fun h ↦
  one_ne_zero (α := InfiniteAdeleRing K) (congrArg Prod.fst
    (eq_zero_of_forall_adeleAddChar_mul_eq_one (K := K) (y := 1) fun u ↦ by simp [h]))

end TauCeti.GlobalNumberFields
