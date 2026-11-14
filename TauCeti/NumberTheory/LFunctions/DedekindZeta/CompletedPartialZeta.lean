/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Mellin
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.NumberTheory.LFunctions.Theta.UnitCone

/-!
# Completed partial zeta functions and their functional equation

Let `I` be an invertible fractional ideal of a number field `K`, and let `𝔎` be the ideal class of
`I⁻¹` in `ClassGroup (𝓞 K)`. For `Re s > 1`, the partial zeta function of `𝔎` is
`ζ(𝔎, s) = ∑_{𝔟 ∈ 𝔎} N(𝔟) ^ (-s)`, and its archimedean completion in Neukirch's Chapter VII,
(5.4) and (5.9) is

`Z(𝔎, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ(𝔎, s)`,

where `d_K = discr K`, `r₁ = nrRealPlaces K`, and `r₂ = nrComplexPlaces K`.

This file constructs `TauCeti.LFunctions.completedPartialZeta I` as the canonical meromorphic
continuation (`TauCeti.meromorphicContinuation`) of this completed series from `Re s > 1` to `ℂ`.
Combining `hasMellin_mellinKernel_idealLattice_sub_mellinConstant` with
`mellinKernelFEPair hD (idealLattice K I)` (built on Mathlib's `WeakFEPair`) identifies
`completedPartialZeta I` away from `0` and `1` with `(mellinKernelFEPair hD (idealLattice K I)).Λ`
evaluated at `s / 2`, and yields:

* series, fundamental-cone, ray-class `LSeries`, cone-integral, and Mellin-transform
  representations on `Re s > 1`;
* meromorphic continuation to `ℂ` in meromorphic normal form (`MeromorphicNFOn`), analytic
  everywhere except at `s = 0` and `s = 1`, with simple poles of class-independent residues
  `-2 * mellinConstant K` at `0` and `2 * mellinConstant K = 2 ^ (r₁ + r₂) R / w` at `1` (and
  canonical normal-form value `0` at both poles);
* the functional equation `completedPartialZeta I (1 - s) = completedPartialZeta J s` for all
  `s : ℂ` whenever `J = FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹`, or more generally whenever
  `I * J * differentIdeal ℤ (𝓞 K)` is principal (Neukirch VII (5.9)).

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function of the class of
  `I⁻¹`, in meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_eq_mellinKernelFEPair_Λ`,
  `TauCeti.LFunctions.completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ`: comparison with the
  Mellin functional-equation pair over any unit fundamental domain `D`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_LSeries_rayClassCoeff_one`,
  `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: series, cone-integral, and Mellin
  representations on `Re s > 1`.
* `TauCeti.LFunctions.meromorphic_completedPartialZeta`,
  `TauCeti.LFunctions.analyticAt_completedPartialZeta_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`,
  `TauCeti.LFunctions.completedPartialZeta_zero`,
  `TauCeti.LFunctions.completedPartialZeta_one`: meromorphicity, exact poles, residues, and
  canonical pole values at `0` and `1`.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub_of_isPrincipal`: Neukirch VII (5.9), the
  functional equation `completedPartialZeta I (1 - s) = completedPartialZeta J s` for all `s : ℂ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.4)–(5.9).
* Mathlib's `WeakFEPair` (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`, D. Loeffler).
-/

public section

noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped Pointwise Topology nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and Mellin continuation -/

/-- **The completed partial zeta function** of the ideal class `(ClassGroup.mk K I)⁻¹`
(Neukirch VII (5.4) and (5.9)): the canonical meromorphic continuation from `Re s > 1` of
`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{[𝔟] = [I]⁻¹} N(𝔟) ^ (-s)`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      meromorphicContinuation 1 fun s ↦
        ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
  (rfl)

/-- `completedPartialZeta I` depends on `I` only through its ideal class `ClassGroup.mk K I`. -/
theorem completedPartialZeta_eq_of_mk_eq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ≃
      {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K J)⁻¹} :=
    Equiv.subtypeEquivRight fun 𝔟 ↦ by rw [h]
  have htsum (s : ℂ) :
      (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K J)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
    e.tsum_eq (fun 𝔟 ↦ (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
  simp only [completedPartialZeta_def, htsum]

/-- `completedPartialZeta I` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

open scoped Classical in
private theorem meromorphic_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := fun s ↦
  ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (s / 2)).comp_analyticAt
    (g := fun z : ℂ ↦ z / 2) (by fun_prop)

open scoped Classical in
private theorem analyticAt_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have h0' : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have h1' : s / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    rw [mellinKernelFEPair_k]
    push_cast
    intro h
    exact h1 (by linear_combination 2 * h)
  exact (((mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff (s / 2)).mpr
    ⟨.inl h0', .inl h1'⟩).comp (f := fun z : ℂ ↦ z / 2) (by fun_prop)

open scoped Classical in
private theorem analyticOnNhd_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2))
      {s | 1 < s.re} := fun s hs ↦
  analyticAt_mellinKernelFEPair_div_two hD I
    (by rintro rfl; norm_num at hs) (by rintro rfl; norm_num at hs)

open scoped Classical in
private theorem eqOn_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    EqOn (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2))
      (fun s ↦
        ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
      {s | 1 < s.re} := by
  intro s hs
  have hs_re : 1 < s.re := hs
  have hs' : 1 / 2 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have h1 := (hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs').2
  have h2 := (hasMellin_mellinKernel_idealLattice_sub_mellinConstant hD I hs).2
  exact h1.symm.trans h2

open scoped Classical in
/-- Over any unit fundamental domain `D`, `completedPartialZeta I` has the punctured germ of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` at every point of `ℂ`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_mellinKernelFEPair_div_two hD I)
    (analyticOnNhd_mellinKernelFEPair_div_two hD I) (eqOn_mellinKernelFEPair_div_two hD I) s

open scoped Classical in
/-- Over any unit fundamental domain `D`, `completedPartialZeta I s` agrees with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` away from the poles `0` and `1`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_apply (meromorphic_mellinKernelFEPair_div_two hD I)
    (analyticOnNhd_mellinKernelFEPair_div_two hD I) (eqOn_mellinKernelFEPair_div_two hD I)
    (analyticAt_mellinKernelFEPair_div_two hD I h0 h1)

/-! ### Series and integral representations on `Re s > 1` -/

/-- **Series representation on `Re s > 1`.** On its initial half-plane of convergence,
`completedPartialZeta I s` equals the completed Dirichlet series of `(ClassGroup.mk K I)⁻¹`. -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I
      (by rintro rfl; norm_num at hs) (by rintro rfl; norm_num at hs)]
  exact eqOn_mellinKernelFEPair_div_two hD I hs

/-- **Fundamental-cone series representation on `Re s > 1`** (Neukirch VII (5.4)). -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        (((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s / (torsionOrder K : ℂ)) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          (mixedEmbedding.norm (x.1 : mixedSpace K) : ℂ) ^ (-s) := by
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hN_ne : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hN_cancel : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s *
      ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ hN_ne, add_neg_cancel, cpow_zero]
  rw [completedPartialZeta_eq_tsum I hs, (hasSum_norm_cpow_fundamentalCone I hs).tsum_eq]
  calc ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
      = (((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) *
          (((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s *
            ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s))) *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
          rw [div_self hw, hN_cancel, one_mul, one_mul]
    _ = _ := by ring

/-- **Ray-class `LSeries` representation on `Re s > 1`.** Under `oneEquivClassGroup`, the
uncompleted Dirichlet series in `completedPartialZeta I s` is
`LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s` for the class `c` corresponding to
`(ClassGroup.mk K I)⁻¹`. -/
theorem completedPartialZeta_eq_LSeries_rayClassCoeff_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : RayClassGroup (Modulus.one K)}
    (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  rw [completedPartialZeta_eq_tsum I hs, LSeries_rayClassCoeff_one_eq_tsum_mk0 hc hs]

open scoped Classical in
/-- **Cone-integral representation on `Re s > 1`** (Neukirch VII (5.5)). -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have hm := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hc : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hc] at hm
  rw [completedPartialZeta_eq_tsum I hs,
    ← (hasMellin_mellinKernel_idealLattice_sub_mellinConstant hD I hs).2, hm.2]

/-- **Mellin-transform representation on `Re s > 1`** (Neukirch VII (5.5)). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) := by
  rw [completedPartialZeta_eq_tsum I hs,
    (hasMellin_mellinKernel_idealLattice_sub_mellinConstant hD I hs).2]

/-! ### Poles, residues, and analyticity -/

/-- **Residue of `completedPartialZeta I` at `s = 0`**, equal to `-2 * mellinConstant K =
-2 ^ (r₁ + r₂) R / w` independently of the ideal class (Neukirch VII (5.9)). -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-2 * (mellinConstant K : ℂ))) := by
  classical
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using ((continuous_id.div_const (2 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono self_mem_nhdsWithin fun s hs ↦ div_ne_zero hs two_ne_zero⟩
  have hlim := ((P.Λ_residue_zero.comp hdiv).const_mul (2 : ℂ))
  have hval : (2 : ℂ) * -P.f₀ = -2 * (mellinConstant K : ℂ) := by
    rw [mellinKernelFEPair_f₀]
    ring
  rw [hval] at hlim
  have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 1 := nhdsWithin_le_nhds (eventually_ne_nhds zero_ne_one)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, h1] with s hs0 hs1
  change 2 * (s / 2 * P.Λ (s / 2)) = s * completedPartialZeta I s
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hs0 hs1]
  ring

/-- **Residue of `completedPartialZeta I` at `s = 1`**, equal to `2 * mellinConstant K =
2 ^ (r₁ + r₂) R / w` independently of the ideal class (Neukirch VII (5.9)). -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  classical
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨?_, Filter.Eventually.mono self_mem_nhdsWithin fun s hs ↦ ?_⟩
    · rw [mellinKernelFEPair_k]
      push_cast
      exact ((continuous_id.div_const (2 : ℂ)).tendsto 1).mono_left nhdsWithin_le_nhds
    · have hs' : s ≠ 1 := hs
      rw [mem_compl_singleton_iff, mellinKernelFEPair_k]
      push_cast
      intro h
      exact hs' (by linear_combination 2 * h)
  have hlim := ((P.Λ_residue_k.comp hdiv).const_mul (2 : ℂ))
  have hval : (2 : ℂ) * ((P.ε * (P.N : ℂ) ^ (-(P.k : ℂ))) • P.g₀) =
      2 * (mellinConstant K : ℂ) := by
    simp [P]
  rw [hval] at hlim
  have h0 : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 0 := nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)
  refine hlim.congr' ?_
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1
  change 2 * ((s / 2 - P.k) * P.Λ (s / 2)) = (s - 1) * completedPartialZeta I s
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hs0 hs1, mellinKernelFEPair_k]
  push_cast
  ring

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  have hne : (-2 * (mellinConstant K : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  refine (meromorphic_completedPartialZeta I 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZeta_zero I

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  have hne : (2 * (mellinConstant K : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  refine (meromorphic_completedPartialZeta I 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedPartialZeta I

/-- In meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its pole
`s = 0`. -/
@[simp]
theorem completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 0 = 0 := by
  by_contra hne
  have h :=
    (meromorphicNFOn_completedPartialZeta I (mem_univ 0)).meromorphicOrderAt_eq_zero_iff.mpr hne
  rw [meromorphicOrderAt_completedPartialZeta_zero] at h
  exact absurd h (by decide)

/-- In meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its pole
`s = 1`. -/
@[simp]
theorem completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 1 = 0 := by
  by_contra hne
  have h :=
    (meromorphicNFOn_completedPartialZeta I (mem_univ 1)).meromorphicOrderAt_eq_zero_iff.mpr hne
  rw [meromorphicOrderAt_completedPartialZeta_one] at h
  exact absurd h (by decide)

/-- `completedPartialZeta I` is analytic at every `s ∉ {0, 1}`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : AnalyticAt ℂ (completedPartialZeta I) s := by
  classical
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hopen : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  have hmem : s ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by simp [h0, h1]
  refine (analyticAt_mellinKernelFEPair_div_two hD I h0 h1).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with z hz
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
  exact (completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hz.1 hz.2).symm

/-- `completedPartialZeta I` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun ha ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZeta I h0 h1⟩
  · rintro rfl
    have hnn := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero] at hnn
    exact absurd hnn (by decide)
  · rintro rfl
    have hnn := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one] at hnn
    exact absurd hnn (by decide)

/-! ### The functional equation -/

/-- **Neukirch VII (5.9): the functional equation of the completed partial zeta function.** If `J`
is the trace dual `FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹` of `I`, then
`completedPartialZeta I (1 - s) = completedPartialZeta J s` for all `s : ℂ` (including the poles
`0` and `1`, where both sides take the canonical normal-form value `0`). -/
theorem completedPartialZeta_one_sub {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp
  rcases eq_or_ne s 1 with rfl | h1
  · simp
  classical
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  have hhalf0 : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hhalf1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h1s1 (by linear_combination 2 * h)
  let hD' : IsUnitFundamentalDomain K ((traceShift K * ·) '' (unitFundamentalDomain K)⁻¹) :=
    hD.inv.mul traceShift_mem_normOneSurface
  have hΛ_congr :
      (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
        (mellinKernelFEPair hD' (idealLattice K J)).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, indicator_of_mem hu,
      mellinKernel_mixedDual_idealLattice hJ]
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1,
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) hhalf0 hhalf1, hΛ_congr,
    show (1 : ℂ) / 2 - (1 - s) / 2 = s / 2 by ring,
    ← completedPartialZeta_eq_mellinKernelFEPair_Λ hD' J h0 h1]

/-- **Neukirch VII (5.9) in ideal-class form**: if `I * J * 𝔡` is a principal fractional ideal, so
that the ideal classes of `I⁻¹` and `J⁻¹` are exchanged by `𝔎 ↦ [𝔡] * 𝔎⁻¹`, then
`completedPartialZeta I (1 - s) = completedPartialZeta J s` for all `s : ℂ`. -/
theorem completedPartialZeta_one_sub_of_isPrincipal {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ((I : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K) *
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal)
    (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  have hdiff_ne : (differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) ≠ ⊥ := differentIdeal_ne_bot
  let D : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    FractionalIdeal.mk0 K ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_iff_ne_zero.mpr hdiff_ne⟩
  let Idual : (FractionalIdeal (𝓞 K)⁰ K)ˣ := (I * D)⁻¹
  have hD_inv : ((D : FractionalIdeal (𝓞 K)⁰ K))⁻¹ = FractionalIdeal.dual ℤ ℚ 1 := by
    rw [FractionalIdeal.coe_mk0]
    change ((differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ = FractionalIdeal.dual ℤ ℚ 1
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  have hIdual : (Idual : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.dual_eq_mul_inv, ← hD_inv,
      show Idual = D⁻¹ * I⁻¹ by simp [Idual, mul_comm],
      Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  have hprin : ClassGroup.mk K (I * J * D) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr (by simpa [D] using h)
  have hmk : ClassGroup.mk K Idual = ClassGroup.mk K J := by
    have hmul : ClassGroup.mk K J * ClassGroup.mk K (I * D) = 1 := by
      rw [← map_mul, show J * (I * D) = I * J * D by simp only [mul_assoc, mul_left_comm],
        hprin]
    rw [show Idual = (I * D)⁻¹ from rfl, map_inv]
    exact inv_eq_of_mul_eq_one_left hmul
  rw [completedPartialZeta_one_sub hIdual s, completedPartialZeta_eq_of_mk_eq hmk]

end TauCeti.LFunctions
