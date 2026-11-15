/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.Theta.UnitCone

/-!
# Completed partial zeta functions and their functional equation

For an invertible fractional ideal `I` of a number field `K`, Hecke's integral representation
identifies the completed Mellin transform of the lattice theta kernel `mellinKernel D σ(I)` at
`s / 2` with the completed partial zeta function of the inverse ideal class `(ClassGroup.mk K I)⁻¹`
(Neukirch, Chapter VII, §5, (5.3)–(5.9)).

On the half-plane `Re s > 1` of absolute convergence, the completed partial zeta function equals

`|d_K| ^ (s / 2) * Γ_ℝ(s) ^ r₁ * Γ_ℂ(s) ^ r₂ * ∑_{𝔟 ∈ [I]⁻¹} N(𝔟) ^ (-s)`,

where `Γ_ℝ(s) = π ^ (-s / 2) Γ(s / 2)` and `Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)` are Deligne's archimedean
gamma factors; the factor `2` in `Γ_ℂ` absorbs the `2 ^ (-r₂)` coming from the lattice covolume
`covol σ(I) = N(I) · 2 ^ (-r₂) · √|d_K|`. Defining `completedPartialZeta I` as the canonical
meromorphic continuation (`TauCeti.meromorphicContinuation`, in meromorphic normal form on `ℂ`) of
this product makes it manifestly independent of the choice of unit fundamental domain `D`, while
identifying it with `toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD σ(I)).Λ (s / 2)) univ`
transfers meromorphic continuation, exact simple poles at `s = 0` and `s = 1`, their residues
`∓ 2 a₀` (`a₀ = mellinConstant K = 2 ^ (r₁ + r₂ - 1) R / w`), and the functional equation
`completedPartialZeta I (1 - s) = completedPartialZeta J s` against the trace dual
`J = FractionalIdeal.dual ℤ ℚ I`.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function attached to an
  invertible fractional ideal `I : (FractionalIdeal (𝓞 K)⁰ K)ˣ`, normalized in meromorphic normal
  form on `ℂ`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_congr`: depends only on `ClassGroup.mk K I`.
* `TauCeti.LFunctions.completedPartialZeta_eq_toMeromorphicNFOn`,
  `completedPartialZeta_eventuallyEq_Λ`, `completedPartialZeta_eq_Λ`: global comparison with
  Hecke's Mellin pair `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` for any unit
  fundamental domain `D`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `completedPartialZeta_eq_tsum_fundamentalCone`,
  `completedPartialZeta_eq_LSeries_rayClassCoeff`,
  `completedPartialZeta_eq_integral_unitCone`,
  `hasMellin_mellinKernel_sub_completedPartialZeta`,
  `completedPartialZeta_eq_mellin`: series, cone-sum, ray-class `LSeries`, unfolded cone-integral,
  and Mellin representations on `Re s > 1` (Neukirch VII (5.3)–(5.5)).
* `TauCeti.LFunctions.meromorphic_completedPartialZeta`,
  `analyticAt_completedPartialZeta_iff`, `meromorphicOrderAt_completedPartialZeta_zero`,
  `meromorphicOrderAt_completedPartialZeta_one`: meromorphy on `ℂ`, holomorphy away from `0` and
  `1`, and simple poles at `0` and `1`.
* `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `tendsto_sub_one_mul_completedPartialZeta`: residues `-2 * mellinConstant K` at `s = 0` and
  `2 * mellinConstant K` at `s = 1` (Neukirch VII (5.8)–(5.9)).
* `TauCeti.LFunctions.completedPartialZeta_one_sub`: the functional equation
  `completedPartialZeta I (1 - s) = completedPartialZeta J s` for the trace dual `J` of `I`
  (Neukirch VII (5.9)).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section
noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units Set
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and ideal-class invariance -/

/-- **The completed partial zeta function** attached to an invertible fractional ideal `I` of `K`
(Neukirch VII, §5): the canonical meromorphic continuation (`TauCeti.meromorphicContinuation`, in
meromorphic normal form on `ℂ`) from `Re s > 1` of

`|d_K| ^ (s / 2) * Γ_ℝ(s) ^ r₁ * Γ_ℂ(s) ^ r₂ * ∑_{𝔟 ∈ [I]⁻¹} N(𝔟) ^ (-s)`,

where the sum runs over the nonzero integral ideals `𝔟` in the inverse ideal class
`(ClassGroup.mk K I)⁻¹`. Using Deligne's `Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)` absorbs the factor
`2 ^ (-r₂)` from the covolume of `σ(I)`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((discr K).natAbs : ℂ) ^ (s / 2) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- Defining equation of `TauCeti.LFunctions.completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := (rfl)

/-- The completed partial zeta function is in meromorphic normal form on the whole complex plane. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The completed partial zeta function is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- The completed partial zeta function depends only on the ideal class of `I`. -/
theorem completedPartialZeta_congr {I I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K I') :
    completedPartialZeta I = completedPartialZeta I' := by
  rw [completedPartialZeta_def, completedPartialZeta_def, h]

/-! ### Identification with Hecke's Mellin pair -/

open scoped Classical in
/-- Covolume, gamma-factor, and torsion-order cancellation in Hecke's unfolded cone integral:
`(2 ^ r₂ / w) * (V_I ^ 2) ^ (s / 2) * Γ_ℝ(s) ^ r₁ * Γ_ℝ(2s) ^ r₂ * (w * N(I) ^ (-s) * T)`
simplifies to `|d_K| ^ (s / 2) * Γ_ℝ(s) ^ r₁ * Γ_ℂ(s) ^ r₂ * T`. -/
private theorem covolume_gamma_cancel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s T : ℂ) :
    (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((torsionOrder K : ℂ) *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s) * T)) =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * T := by
  set a : ℝ := (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  set b : ℝ := (2⁻¹ : ℝ) ^ nrComplexPlaces K
  set c : ℝ := √|(discr K : ℝ)|
  have ha : 0 < a := Rat.cast_pos.mpr ((FractionalIdeal.absNorm_nonneg I.1).lt_of_ne'
    (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero))
  have hb : 0 ≤ b := by positivity
  have hV : ZLattice.covolume (idealLattice K I) = a * b * c := by
    simpa only [a, b, c, Int.cast_abs] using covolume_idealLattice K I
  have hVs : (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (a : ℂ) ^ s * (b : ℂ) ^ s * (c : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow (ZLattice.covolume_pos _ volume).le, Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero, hV, Complex.ofReal_mul,
      TauCeti.ofReal_mul_cpow (mul_nonneg ha.le hb), Complex.ofReal_mul,
      TauCeti.ofReal_mul_cpow ha.le]
  have hc_discr : ((discr K).natAbs : ℂ) ^ (s / 2) = (c : ℂ) ^ s := by
    have hsq : ((discr K).natAbs : ℝ) = c ^ 2 := by
      rw [Real.sq_sqrt (abs_nonneg _), ← Int.cast_abs, ← Int.cast_natCast, Int.natCast_natAbs]
    rw [← Complex.ofReal_natCast, hsq, Complex.ofReal_pow,
      TauCeti.ofReal_pow_cpow (Real.sqrt_nonneg _), Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero]
  have h2gamma : (2 : ℂ) ^ nrComplexPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K =
      ((2 : ℂ) ^ s) ^ nrComplexPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, Gammaℝ_two_mul, ← mul_assoc, sub_eq_add_neg, cpow_add _ _ two_ne_zero,
      cpow_neg_one, mul_comm ((2 : ℂ) ^ s), ← mul_assoc,
      mul_inv_cancel₀ (two_ne_zero (α := ℂ)), one_mul, mul_pow]
  have hb2 : (b : ℂ) ^ s * ((2 : ℂ) ^ s) ^ nrComplexPlaces K = 1 := by
    rw [← Complex.cpow_nat_mul, ← Complex.ofReal_ofNat, ← TauCeti.ofReal_pow_cpow zero_le_two,
      ← Complex.ofReal_pow, ← TauCeti.ofReal_mul_cpow hb, ← Complex.ofReal_mul]
    simp [b, inv_pow]
  have ha_inv : (a : ℂ) ^ s * (a : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), add_neg_cancel,
      Complex.cpow_zero]
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [hVs, hc_discr]
  calc (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
          ((a : ℂ) ^ s * (b : ℂ) ^ s * (c : ℂ) ^ s) *
          (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
            ((torsionOrder K : ℂ) * (a : ℂ) ^ (-s) * T))
      = ((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) * ((a : ℂ) ^ s * (a : ℂ) ^ (-s)) *
          ((b : ℂ) ^ s * ((2 : ℂ) ^ nrComplexPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K)) *
          ((c : ℂ) ^ s * Gammaℝ s ^ nrRealPlaces K * T) := by ring
    _ = (c : ℂ) ^ s * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * T := by
      rw [div_self hw, ha_inv, h2gamma, ← mul_assoc ((b : ℂ) ^ s), hb2]; ring

open scoped Classical in
/-- On `Re s > 1`, the completed function of Hecke's Mellin pair at `s / 2` equals the completed
Dirichlet series of the inverse ideal class. -/
private theorem mellinKernelFEPair_Λ_div_two_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hconst] at hm2
  rw [← hm1.2, hm2.2, ← (hasSum_gamma_mul_norm_cpow_fundamentalCone hD I hs).tsum_eq,
    tsum_mul_left, tsum_norm_cpow_fundamentalCone_inter_idealLattice]
  exact covolume_gamma_cancel I s _

open scoped Classical in
private theorem meromorphic_Λ_div_two {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
  fun s ↦ MeromorphicAt.comp_analyticAt (g := fun z : ℂ ↦ z / 2)
    ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (s / 2)) analyticAt_id.div_const

open scoped Classical in
private theorem analyticAt_Λ_div_two {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have ha : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
    rw [(mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff]
    refine ⟨Or.inl (div_ne_zero hs0 two_ne_zero), Or.inl fun h ↦ hs1 ?_⟩
    simp only [mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h
    linear_combination 2 * h
  exact AnalyticAt.comp (f := fun z : ℂ ↦ z / 2) ha analyticAt_id.div_const

open scoped Classical in
private theorem analyticOnNhd_Λ_div_two {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2))
      {s | 1 < s.re} :=
  fun s hs ↦ analyticAt_Λ_div_two hD I
    (by rintro rfl; norm_num at hs) (by rintro rfl; norm_num at hs)

open scoped Classical in
/-- **Global identification with Hecke's Mellin pair.** For every unit fundamental domain `D`,
`completedPartialZeta I` is the meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_Λ_div_two hD I)
    (analyticOnNhd_Λ_div_two hD I) fun s hs ↦ mellinKernelFEPair_Λ_div_two_eq hD I hs

open scoped Classical in
/-- At every point of `ℂ` (including the poles `0` and `1`), `completedPartialZeta I` has the
same punctured germ as `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eventuallyEq_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_Λ_div_two hD I)
    (analyticOnNhd_Λ_div_two hD I) (fun z hz ↦ mellinKernelFEPair_Λ_div_two_eq hD I hz) s

open scoped Classical in
/-- Away from the poles `0` and `1`, `completedPartialZeta I s` agrees pointwise with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` for every unit fundamental domain `D`. -/
theorem completedPartialZeta_eq_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_apply (meromorphic_Λ_div_two hD I)
    (analyticOnNhd_Λ_div_two hD I) (fun z hz ↦ mellinKernelFEPair_Λ_div_two_eq hD I hz)
    (analyticAt_Λ_div_two hD I hs0 hs1)

/-! ### Representations on `Re s > 1` -/

/-- **Series representation on `Re s > 1`**, Neukirch VII (5.3)–(5.5). -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_Λ hD I (by rintro rfl; norm_num at hs)
    (by rintro rfl; norm_num at hs)]
  exact mellinKernelFEPair_Λ_div_two_eq hD I hs

/-- **Ray-class `LSeries` representation on `Re s > 1`.** For `c : RayClassGroup (Modulus.one K)`
corresponding to `(ClassGroup.mk K I)⁻¹`, `completedPartialZeta I s` completes the partial zeta
Dirichlet series `LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s`. -/
theorem completedPartialZeta_eq_LSeries_rayClassCoeff {c : RayClassGroup (Modulus.one K)}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
          LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  rw [completedPartialZeta_eq_tsum I hs, LSeries_rayClassCoeff_one_eq_tsum_classGroup I hc s]

/-- **Fundamental-cone representation on `Re s > 1`**, Neukirch VII (5.4). -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
          (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s /
            torsionOrder K *
            ∑' a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
              ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)) := by
  rw [completedPartialZeta_eq_LSeries_rayClassCoeff I
      (oneEquivClassGroup.apply_symm_apply (ClassGroup.mk K I)⁻¹) hs,
    LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone_inter_idealLattice I
      (oneEquivClassGroup.apply_symm_apply (ClassGroup.mk K I)⁻¹) s]

open scoped Classical in
/-- **Unfolded cone-integral representation on `Re s > 1`**, Neukirch VII (5.5). -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
            ∂archHaar K := by
  rw [completedPartialZeta_eq_tsum I hs,
    ← (hasSum_gamma_mul_norm_cpow_fundamentalCone hD I hs).tsum_eq, tsum_mul_left,
    tsum_norm_cpow_fundamentalCone_inter_idealLattice, covolume_gamma_cancel]

open scoped Classical in
/-- **Mellin representation on `Re s > 1`**, Neukirch VII (5.5): `completedPartialZeta I s` is the
Mellin transform at `s / 2` of `u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K`. -/
theorem hasMellin_mellinKernel_sub_completedPartialZeta {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  rw [completedPartialZeta_eq_Λ hD I (by rintro rfl; norm_num at hs)
    (by rintro rfl; norm_num at hs)]
  exact hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2

open scoped Classical in
/-- Pointwise Mellin formula on `Re s > 1`, Neukirch VII (5.5). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_mellinKernel_sub_completedPartialZeta hD I hs).2.symm

/-! ### Regularity, poles, and residues -/

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_Λ hD I 0)]
  have hd : deriv (fun z : ℂ ↦ z / 2) 0 ≠ 0 := by
    rw [((hasDerivAt_id' (0 : ℂ)).div_const (2 : ℂ)).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 0)
    analyticAt_id.div_const hd
  rw [Function.comp_def] at hcomp
  rw [hcomp, zero_div]
  exact (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_zero
    (by simp [Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K)])

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_Λ hD I 1)]
  have hd : deriv (fun z : ℂ ↦ z / 2) 1 ≠ 0 := by
    rw [((hasDerivAt_id' (1 : ℂ)).div_const (2 : ℂ)).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 1)
    analyticAt_id.div_const hd
  rw [Function.comp_def] at hcomp
  have hk : ((1 : ℂ) / 2) = ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by simp
  rw [hcomp, hk]
  exact (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_k
    (by simp [Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K)])

/-- `completedPartialZeta I` is analytic at every point `s ∉ {0, 1}`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : AnalyticAt ℂ (completedPartialZeta I) s := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  refine (meromorphicNFOn_completedPartialZeta I (mem_univ s)
    ).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_Λ hD I s)]
  exact (analyticAt_Λ_div_two hD I hs0 hs1).meromorphicOrderAt_nonneg

/-- `completedPartialZeta I` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun ha ↦ ⟨?_, ?_⟩, fun ⟨hs0, hs1⟩ ↦ analyticAt_completedPartialZeta I hs0 hs1⟩
  · rintro rfl
    have h := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero] at h
    exact absurd h (by decide)
  · rintro rfl
    have h := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one] at h
    exact absurd h (by decide)

/-- `completedPartialZeta I` is complex differentiable away from `0` and `1`. -/
theorem differentiableAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : DifferentiableAt ℂ (completedPartialZeta I) s :=
  (analyticAt_completedPartialZeta I hs0 hs1).differentiableAt

/-- Being in meromorphic normal form, `completedPartialZeta I` takes the value `0` at `0`. -/
@[simp]
theorem completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 0 = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp
    (meromorphicNFOn_completedPartialZeta I (mem_univ 0)) with ha | ⟨_, _, h0⟩
  · simp at ha
  · exact h0

/-- Being in meromorphic normal form, `completedPartialZeta I` takes the value `0` at `1`. -/
@[simp]
theorem completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 1 = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp
    (meromorphicNFOn_completedPartialZeta I (mem_univ 1)) with ha | ⟨_, _, h1⟩
  · simp at ha
  · exact h1

/-- **Residue of `completedPartialZeta` at `s = 0`** (Neukirch VII (5.8)):
`s * completedPartialZeta I s → -2 * mellinConstant K` as `s → 0` (`s ≠ 0`). -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s ↦ s * completedPartialZeta I s) (𝓝[≠] 0) (𝓝 (-2 * (mellinConstant K : ℂ))) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  set P := mellinKernelFEPair hD (idealLattice K I)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using ((continuous_id.div_const (2 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono self_mem_nhdsWithin fun s hs ↦ div_ne_zero hs two_ne_zero⟩
  have hres : Tendsto (fun s : ℂ ↦ 2 * ((s / 2) • P.Λ (s / 2))) (𝓝[≠] 0)
      (𝓝 (2 * -P.f₀)) := (P.Λ_residue_zero.comp hdiv).const_mul 2
  have hlim : 2 * -P.f₀ = -2 * (mellinConstant K : ℂ) := by
    simp only [P, mellinKernelFEPair_f₀]
    ring
  rw [hlim] at hres
  refine hres.congr' ?_
  filter_upwards [Filter.inter_mem self_mem_nhdsWithin
    (nhdsWithin_le_nhds (eventually_ne_nhds zero_ne_one))] with s ⟨hs0, hs1⟩
  rw [smul_eq_mul, completedPartialZeta_eq_Λ hD I hs0 hs1]
  ring

/-- **Residue of `completedPartialZeta` at `s = 1`** (Neukirch VII (5.8)–(5.9)):
`(s - 1) * completedPartialZeta I s → 2 * mellinConstant K` as `s → 1` (`s ≠ 1`). -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  set P := mellinKernelFEPair hD (idealLattice K I)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa [P, one_div] using
          ((continuous_id.div_const (2 : ℂ)).tendsto 1).mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono self_mem_nhdsWithin fun s (hs : s ≠ 1) (h : s / 2 = (P.k : ℂ)) ↦
          hs <| by
            simp only [P, mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one,
              Complex.ofReal_ofNat] at h
            linear_combination 2 * h⟩
  have hres : Tendsto (fun s : ℂ ↦ 2 * ((s / 2 - (P.k : ℂ)) • P.Λ (s / 2))) (𝓝[≠] 1)
      (𝓝 (2 * ((P.ε * (P.N : ℂ) ^ (-(P.k : ℂ))) • P.g₀))) :=
    (P.Λ_residue_k.comp hdiv).const_mul 2
  have hlim : 2 * ((P.ε * (P.N : ℂ) ^ (-(P.k : ℂ))) • P.g₀) = 2 * (mellinConstant K : ℂ) := by
    simp [P]
  rw [hlim] at hres
  refine hres.congr' ?_
  filter_upwards [Filter.inter_mem self_mem_nhdsWithin
    (nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero))] with s ⟨hs1, hs0⟩
  simp only [P, mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, smul_eq_mul]
  rw [completedPartialZeta_eq_Λ hD I hs0 hs1]
  ring

/-! ### The functional equation -/

open scoped Classical in
/-- Identifying the Euclidean dual of `σ(I)` with the lattice `σ(J)` of the trace dual translates
the unit fundamental domain by `traceShift K` without changing the completed Mellin transform. -/
private theorem mellinKernelFEPair_mixedDual_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (mellinKernelFEPair hD (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair (hD.mul traceShift_mem_normOneSurface) (idealLattice K J)).Λ := by
  rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
  refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
  simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, indicator_of_mem hu,
    mellinKernel_mixedDual_idealLattice hJ D u]

/-- **The functional equation of the completed partial zeta function**, Neukirch VII (5.9).
If `J` is the trace dual `FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹` of an invertible fractional ideal
`I`, then `completedPartialZeta I (1 - s) = completedPartialZeta J s` for all `s : ℂ` (including
at the poles `0` and `1`, where both sides take the canonical normal-form value `0`). -/
theorem completedPartialZeta_one_sub {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  classical
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h1s1 : 1 - s ≠ 1 := fun h ↦ hs0 (by linear_combination -h)
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_Λ hD I h1s0 h1s1,
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) (div_ne_zero h1s0 two_ne_zero)
      (fun h ↦ hs0 (by linear_combination -2 * h)),
    mellinKernelFEPair_mixedDual_Λ hD.inv hJ,
    completedPartialZeta_eq_Λ (hD.inv.mul traceShift_mem_normOneSurface) J hs0 hs1]
  congr 1
  ring

end TauCeti.LFunctions
