/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
public import TauCeti.RingTheory.DedekindDomain.Different.Basic
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.RingTheory.FractionalIdeal.Norm
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Completed partial zeta functions of ideal classes

For an ideal class `c : ClassGroup (𝓞 K)` of a number field `K`, we define
`TauCeti.LFunctions.completedPartialZetaClass c` as the canonical whole-plane meromorphic
normal-form continuation (`TauCeti.meromorphicContinuation 1`) from `Re s > 1` of

`Z(c, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ c} N(𝔟) ^ (-s)`,

where the sum runs over the nonzero integral ideals `𝔟` of `𝓞 K` in the class `c`. For an
invertible fractional ideal `I`, the representative-indexed function
`TauCeti.LFunctions.completedPartialZeta I` is defined as
`completedPartialZetaClass (ClassGroup.mk K I)⁻¹`, continuing the sum over the nonzero integral
ideals `𝔟` in the inverse class `[I]⁻¹` — that is, the nonzero integral ideals `𝔟` such that
`𝔟 I` is principal.

Following Hecke (Neukirch, Chapter VII, §5), we combine the unit-cone unfolding in
`TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding`
(`hasMellin_mellinKernel_idealLattice_sub_mellinConstant` and
`integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`) with the covolume formula
`V_{σ(I)} = N(I) 2 ^ (-r₂) √|d_K|`. This identifies `completedPartialZeta I` on `Re s > 1` with the
Mellin transform at `s / 2` of `mellinKernel D (idealLattice K I) - mellinConstant K`, and hence
globally with the normal form of `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.

From `mellinKernelFEPair` and the trace-dual kernel identity `mellinKernel_mixedDual_idealLattice`
we deduce meromorphic continuation to `ℂ`, analyticity away from simple poles at `s = 0` and
`s = 1` with residues `-2 a₀` and `2 a₀` (`a₀ = mellinConstant K = 2 ^ (r - 1) R / w`), and
Hecke's functional equation `Z(I, 1 - s) = Z(I^∨, s)` against the trace dual
`FractionalIdeal.dualEquiv ℤ ℚ I` (which on classes reads
`completedPartialZetaClass c (1 - s) = completedPartialZetaClass ([𝔡] * c⁻¹) s`, where
`[𝔡] = (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ 1))⁻¹` is the class of the different).

## Main definitions

* `TauCeti.LFunctions.completedPartialZetaClass`: the completed partial zeta function of an ideal
  class `c : ClassGroup (𝓞 K)` in meromorphic normal form on `ℂ`, summing over nonzero integral
  ideals in `c`.
* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function attached to an
  invertible fractional ideal `I`, defined as `completedPartialZetaClass (ClassGroup.mk K I)⁻¹`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_eq_completedPartialZetaClass`: relating
  `completedPartialZeta` and `completedPartialZetaClass`.
* `TauCeti.LFunctions.completedPartialZeta_eq_toMeromorphicNFOn`: identification of
  `completedPartialZeta I` with the normal form of
  `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.
* `TauCeti.LFunctions.completedPartialZetaClass_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_spanSingleton`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`: representations on `Re s > 1`
  over ideal classes, the trivial-modulus ray-class Dirichlet series, principal products, and
  fundamental-cone lattice points.
* `TauCeti.LFunctions.hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZeta`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`,
  `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`: Mellin-transform and cone-integral
  representations on `Re s > 1` (Neukirch VII (5.5)).
* `TauCeti.LFunctions.analyticAt_completedPartialZetaClass_iff`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZetaClass`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZetaClass_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZetaClass_one`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZetaClass_zero`: regularity, simple
  poles at `0` and `1`, and their residues.
* `TauCeti.LFunctions.completedPartialZetaClass_one_sub`,
  `TauCeti.LFunctions.completedPartialZetaClass_one_sub_eventuallyEq`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub_eventuallyEq`,
  `TauCeti.LFunctions.completedPartialZetaClass_conj`: Hecke's functional equation (pointwise and
  as punctured germs) and reflection symmetry.

## References

* E. Hecke, *Über die Zetafunktion beliebiger algebraischer Zahlkörper*, Nachr. Ges. Wiss.
  Göttingen (1917), 77–89.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section
noncomputable section

open Complex ComplexConjugate Filter MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone Set Submodule
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped ENNReal nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and class invariance -/

/-- **The completed partial zeta function of an ideal class** `c : ClassGroup (𝓞 K)`: the
canonical whole-plane meromorphic normal-form continuation from `Re s > 1` of
`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ c} N(𝔟) ^ (-s)`, where the sum runs over the
nonzero integral ideals `𝔟` of `𝓞 K` in the class `c`. For an invertible fractional ideal `I`,
`completedPartialZeta I = completedPartialZetaClass (ClassGroup.mk K I)⁻¹`. -/
def completedPartialZetaClass (c : ClassGroup (𝓞 K)) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = c},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- Defining equation of `TauCeti.LFunctions.completedPartialZetaClass`. -/
theorem completedPartialZetaClass_def (c : ClassGroup (𝓞 K)) :
    completedPartialZetaClass c = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = c},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
  (rfl)

/-- `completedPartialZetaClass c` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZetaClass (c : ClassGroup (𝓞 K)) :
    MeromorphicNFOn (completedPartialZetaClass c) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZetaClass c` is meromorphic on `ℂ`. -/
@[fun_prop]
theorem meromorphic_completedPartialZetaClass (c : ClassGroup (𝓞 K)) :
    Meromorphic (completedPartialZetaClass c) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZetaClass c).meromorphicOn

/-- **The completed partial zeta function** attached to an invertible fractional ideal `I` of `K`,
Neukirch VII (5.4) and (5.9): defined as `completedPartialZetaClass (ClassGroup.mk K I)⁻¹`, the
canonical whole-plane meromorphic normal-form continuation from `Re s > 1` of
`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ [I]⁻¹} N(𝔟) ^ (-s)`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  completedPartialZetaClass (ClassGroup.mk K I)⁻¹

/-- Simplifying `completedPartialZeta I` exposes the canonical class-indexed function
`completedPartialZetaClass (ClassGroup.mk K I)⁻¹`. -/
@[simp]
theorem completedPartialZeta_eq_completedPartialZetaClass (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = completedPartialZetaClass (ClassGroup.mk K I)⁻¹ :=
  (rfl)

private theorem exists_fractionalIdeal_inv_mk (c : ClassGroup (𝓞 K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (ClassGroup.mk K I)⁻¹ = c := by
  obtain ⟨I, hI⟩ := ClassGroup.mk_surjective (𝓞 K) K c⁻¹
  exact ⟨I, by rw [hI, inv_inv]⟩

/-! ### Normalization and identification with the Mellin functional-equation pair -/

open scoped Classical in
/-- Complex power `(V_{σ(I)} ^ 2) ^ (s / 2)` expanded in terms of `N(I)`, `2 ^ (-r₂)`, and
`|d_K|`. -/
private theorem covolume_sq_idealLattice_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm I.val : ℝ) : ℂ) ^ s *
        (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ)) ^ (s / 2) := by
  set N_I : ℝ := (FractionalIdeal.absNorm I.val : ℝ)
  set D_K : ℝ := ((|discr K| : ℤ) : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  have hDK_pos : 0 < D_K := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero K))
  have hV_pos : 0 < ZLattice.covolume (idealLattice K I) := ZLattice.covolume_pos (idealLattice K I)
  have h1 : (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow hV_pos.le 2 (s / 2), Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero]
  have hcov : ZLattice.covolume (idealLattice K I) = N_I * 2⁻¹ ^ nrComplexPlaces K * √D_K := by
    rw [covolume_idealLattice]
    simp [N_I, D_K]
  rw [h1, hcov, ofReal_mul,
    ofReal_mul_cpow (mul_nonneg hNI_pos.le (by positivity)),
    ofReal_mul, ofReal_mul_cpow hNI_pos.le, ofReal_pow,
    TauCeti.ofReal_pow_cpow (by positivity) (nrComplexPlaces K) s, cpow_nat_mul,
    Real.sqrt_eq_rpow, ← cpow_mul_ofReal_nonneg hDK_pos.le, ofReal_intCast |discr K|]
  congr 2
  push_cast
  ring

open scoped Classical in
/-- Covolume-rescaled normalization algebra converting the Mellin output of `Unfolding` into the
archimedean factor `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂`. -/
private theorem covolume_gamma_mul_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (2 : ℂ) ^ nrComplexPlaces K *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K := by
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set N_I : ℝ := (FractionalIdeal.absNorm I.val : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  have h2gamma : (2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂ = ((2 : ℂ) ^ s) ^ r₂ * Gammaℂ s ^ r₂ := by
    rw [← mul_pow, two_mul_Gammaℝ_two_mul, mul_pow]
  have h2cancel : (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ s) ^ r₂ = 1 := by
    rw [← ofReal_ofNat, ← mul_pow, ← ofReal_mul_cpow (by positivity)]
    norm_num
  have hNI_cancel : (N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← ofReal_ratCast, ← cpow_add _ _ (ofReal_ne_zero.mpr hNI_pos.ne'), add_neg_cancel,
      cpow_zero]
  rw [covolume_sq_idealLattice_cpow]
  calc (2 : ℂ) ^ r₂ *
          ((N_I : ℂ) ^ s * (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s) *
          (Gammaℝ s ^ r₁ * Gammaℝ (2 * s) ^ r₂)
      = ((N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s)) *
          ((((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂)) *
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁) := by ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ := by
        rw [hNI_cancel, h2gamma]
        linear_combination
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) * h2cancel

/-- On `Re s > 1`, `mellinKernel D (idealLattice K I) - mellinConstant K` has Mellin transform at
`s / 2` equal to the completed partial zeta series of `I`. -/
private theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  have hm := hasMellin_mellinKernel_idealLattice_sub_mellinConstant I hD
    (c := oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹)
    (by rw [rayClassMk_idealsPrimeToEquiv_symm_eq, ← map_inv, inv_inv]) hs
  rw [LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup _ hs, MulEquiv.apply_symm_apply] at hm
  simpa only [covolume_gamma_mul_eq] using hm

/-- On `Re s > 1`, `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` equals the completed
partial zeta series of `I`. -/
theorem mellinKernelFEPair_Λ_div_two_eq_tsum {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  exact (hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2).2.symm.trans
    (hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum hD I hs).2

/-- `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is meromorphic on `ℂ`. -/
private theorem meromorphic_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) :=
  fun z ↦ ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (z / 2)).comp_analyticAt
    (g := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- Away from `0` and `1`, `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is analytic
at `s`. -/
private theorem analyticAt_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have h0' : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have h1' : s / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    simp only [mellinKernelFEPair_k, ofReal_div, ofReal_one, ofReal_ofNat]
    exact fun h ↦ h1 (by linear_combination 2 * h)
  have han : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
    ((mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff (s / 2)).mpr ⟨.inl h0', .inl h1'⟩
  exact han.comp (f := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- On `{s | 1 < s.re}`, `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is analytic. -/
private theorem analyticOnNhd_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2))
      {s | 1 < s.re} :=
  fun s (hs : 1 < s.re) ↦ analyticAt_mellinKernelFEPair_Λ_div_two hD I
    (fun h ↦ by linarith [h ▸ hs, zero_re]) (fun h ↦ by linarith [h ▸ hs, one_re])

/-- **Global identification with Hecke's Mellin pair.** Over any unit fundamental domain `D`,
`completedPartialZeta I` is the whole-plane meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  rw [completedPartialZeta_eq_completedPartialZetaClass, completedPartialZetaClass_def]
  exact meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticOnNhd_mellinKernelFEPair_Λ_div_two hD I)
    fun _ hs ↦ mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs

/-- At every point `s : ℂ` (poles included), `completedPartialZeta I` has the same punctured germ
as `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZeta I s` agrees pointwise with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1)

/-! ### Half-plane and integral representations -/

/-- **Ideal-sum representation on `Re s > 1` for an ideal class**, Neukirch VII (5.4). -/
theorem completedPartialZetaClass_eq_tsum (c : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZetaClass c s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = c},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  obtain ⟨I, rfl⟩ := exists_fractionalIdeal_inv_mk (K := K) c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [← completedPartialZeta_eq_completedPartialZetaClass,
    completedPartialZeta_eq_toMeromorphicNFOn hD I,
    toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
      (analyticOnNhd_mellinKernelFEPair_Λ_div_two hD I s hs),
    mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs]

/-- **Relation to the ray-class Dirichlet series at the trivial modulus for an ideal class**:
on `Re s > 1`, `completedPartialZetaClass c s` is the archimedean factor times the trivial-modulus
ray-class Dirichlet series at `oneEquivClassGroup.symm c`. -/
theorem completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one (c : ClassGroup (𝓞 K))
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZetaClass c s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) s := by
  rw [completedPartialZetaClass_eq_tsum c hs,
    LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup _ hs, MulEquiv.apply_symm_apply]

/-- **Principal-product ideal-sum representation on `Re s > 1`**: the sum runs over nonzero
integral ideals `𝔟` such that `𝔟 I = (x)` for some `x : Kˣ`. -/
theorem completedPartialZeta_eq_tsum_spanSingleton (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_completedPartialZetaClass, completedPartialZetaClass_eq_tsum _ hs]
  congr 1
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ≃
      {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} :=
    (Equiv.subtypeEquivRight fun 𝔟 ↦ ClassGroup.mk0_eq_inv_mk_iff I 𝔟).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun 𝔟 : Ideal (𝓞 K) ↦ 𝔟 ∈ (Ideal (𝓞 K))⁰)
        (fun 𝔟 : Ideal (𝓞 K) ↦ ∃ x : Kˣ,
          (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))).trans <|
        Equiv.subtypeEquivRight fun 𝔟 ↦ and_congr_left' (mem_nonZeroDivisors_iff_ne_zero (x := 𝔟))
  rw [← e.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)]
  simp [e]

/-- **Fundamental-cone lattice-sum representation on `Re s > 1`**, Neukirch VII (5.3)–(5.4):
each ideal of class `[I]⁻¹` contributes `w = #μ(K)` generators in `fundamentalCone K`. -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (Units.torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_completedPartialZetaClass, completedPartialZetaClass_eq_tsum _ hs,
    tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone I hs]
  ring

/-- **Mellin-transform representation on `Re s > 1` (`HasMellin` form)**, Neukirch VII (5.5):
`completedPartialZeta I s` is the Mellin transform at `s / 2` of
`mellinKernel D (idealLattice K I) - mellinConstant K`. -/
theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZeta
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  rw [completedPartialZeta_eq_completedPartialZetaClass, completedPartialZetaClass_eq_tsum _ hs]
  exact hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum hD I hs

/-- **Mellin-transform representation on `Re s > 1` (`mellin` form)**, Neukirch VII (5.5). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZeta hD I hs).2.symm

open scoped Classical in
/-- **Cone-integral representation on `Re s > 1`**, Neukirch VII (5.5): over any unit fundamental
domain `D`, `completedPartialZeta I s` is `(2 ^ r₂ / w) V_{σ(I)} ^ s` times the cone integral of
`N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have hm₁ := hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZeta hD I hs
  have hm₂ := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_unitCone_archNorm_cpow_mul_latticeTheta_sub_one I hD hs)
  simp only [mellinConstant_eq_mul_surfaceHaar_real hD, ofReal_mul, ofReal_div, ofReal_pow,
    ofReal_ofNat, ofReal_natCast] at hm₁
  exact hm₁.2.symm.trans hm₂.2

/-! ### Regularity, poles, and residues -/

/-- `completedPartialZetaClass c` is analytic away from `s = 0` and `s = 1`. -/
@[fun_prop]
theorem analyticAt_completedPartialZetaClass (c : ClassGroup (𝓞 K)) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZetaClass c) s := by
  obtain ⟨I, rfl⟩ := exists_fractionalIdeal_inv_mk (K := K) c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [← completedPartialZeta_eq_completedPartialZetaClass,
    completedPartialZeta_eq_toMeromorphicNFOn hD I,
    ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn
      (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn (mem_univ s)]
  exact (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1).meromorphicOrderAt_nonneg

/-- **Residue of `completedPartialZetaClass c` at `s = 1`**, Neukirch VII (5.9):
`lim_{s → 1} (s - 1) Z(c, s) = 2 a₀ = 2 ^ r R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZetaClass (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZetaClass c s) (𝓝[≠] 1)
      (𝓝 (2 * mellinConstant K : ℂ)) := by
  obtain ⟨I, rfl⟩ := exists_fractionalIdeal_inv_mk (K := K) c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      ((continuous_id'.div_const (2 : ℂ)).continuousAt (x := 1)).tendsto_nhdsNE
        fun _ _ ↦ (div_left_inj₀ two_ne_zero).mp
  have hres := P.Λ_residue_k
  simp only [P, mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, ofReal_one, one_cpow, mul_one, smul_eq_mul, one_mul] at hres
  refine ((hres.comp hhalf).const_mul 2).congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with s hs
  rw [Function.comp_apply, ← completedPartialZeta_eq_completedPartialZetaClass, hs]
  push_cast
  ring

/-- `completedPartialZetaClass c` has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZetaClass_one (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZetaClass c) 1 = (-1 : ℤ) := by
  have ha : (2 * mellinConstant K : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  exact (meromorphic_completedPartialZetaClass c 1)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
      (tendsto_sub_one_mul_completedPartialZetaClass c)

/-- As a meromorphic normal form, `completedPartialZetaClass c` takes the canonical value `0` at
its pole `s = 1`. -/
@[simp]
theorem completedPartialZetaClass_one (c : ClassGroup (𝓞 K)) :
    completedPartialZetaClass c 1 = 0 :=
  (meromorphicNFOn_completedPartialZetaClass c (mem_univ 1))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by simp)

private theorem completedPartialZeta_one_sub_of_ne (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I (1 - s) =
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s := by
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1,
    completedPartialZeta_eq_mellinKernelFEPair_Λ hD' (FractionalIdeal.dualEquiv ℤ ℚ I) h0 h1]
  have hs0 : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hs1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h0 (by linear_combination -2 * h)
  have hsub : (1 / 2 : ℂ) - (1 - s) / 2 = s / 2 := by ring
  rw [mellinKernelFEPair_Λ_eq hD (idealLattice K I) hs0 hs1, hsub]
  have hcongr : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair hD' (idealLattice K (FractionalIdeal.dualEquiv ℤ ℚ I))).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u (hu : 0 < u) ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f,
      indicator_of_mem (mem_Ioi.mpr hu)]
    exact mellinKernel_mixedDual_idealLattice (FractionalIdeal.coe_dualEquiv ℤ ℚ I) _ u
  exact congrFun hcongr (s / 2)

private theorem completedPartialZetaClass_one_sub_of_ne (c : ClassGroup (𝓞 K))
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZetaClass c (1 - s) =
      completedPartialZetaClass
        ((ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _)))⁻¹ * c⁻¹) s := by
  obtain ⟨I, rfl⟩ := exists_fractionalIdeal_inv_mk (K := K) c
  rw [← completedPartialZeta_eq_completedPartialZetaClass,
    completedPartialZeta_one_sub_of_ne I h0 h1,
    completedPartialZeta_eq_completedPartialZetaClass,
    FractionalIdeal.classGroupMk_dualEquiv, mul_inv]

/-- **Residue of `completedPartialZetaClass c` at `s = 0`**, Neukirch VII (5.9):
`lim_{s → 0} s Z(c, s) = -2 a₀ = -2 ^ r R / w`. -/
theorem tendsto_mul_completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZetaClass c s) (𝓝[≠] 0)
      (𝓝 (-(2 * mellinConstant K : ℂ))) := by
  let d : ClassGroup (𝓞 K) := (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _)))⁻¹
  have hsub : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] 1) := by
    simpa only [sub_zero] using
      ((continuous_sub_left (1 : ℂ)).continuousAt (x := (0 : ℂ))).tendsto_nhdsNE
        fun _ _ h ↦ sub_right_injective h
  have hlim := ((tendsto_sub_one_mul_completedPartialZetaClass (d * c⁻¹)).comp hsub).neg
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1))] with s hs0 hs1
  have hfe := completedPartialZetaClass_one_sub_of_ne (d * c⁻¹) hs0 hs1
  rw [mul_inv, mul_inv_cancel_left, inv_inv] at hfe
  simp only [Function.comp_apply, hfe]
  ring

/-- `completedPartialZetaClass c` has a simple pole at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZetaClass c) 0 = (-1 : ℤ) := by
  have ha : -(2 * mellinConstant K : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZetaClass c 0)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZetaClass_zero c

/-- `completedPartialZetaClass c` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZetaClass_iff (c : ClassGroup (𝓞 K)) {s : ℂ} :
    AnalyticAt ℂ (completedPartialZetaClass c) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZetaClass c h0 h1⟩
  · rintro rfl
    exact not_analyticAt_of_meromorphicOrderAt_neg
      (by rw [meromorphicOrderAt_completedPartialZetaClass_zero]
          exact WithTop.coe_lt_zero.mpr (by norm_num)) han
  · rintro rfl
    exact not_analyticAt_of_meromorphicOrderAt_neg
      (by rw [meromorphicOrderAt_completedPartialZetaClass_one]
          exact WithTop.coe_lt_zero.mpr (by norm_num)) han

/-- As a meromorphic normal form, `completedPartialZetaClass c` takes the canonical value `0` at
its pole `s = 0`. -/
@[simp]
theorem completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    completedPartialZetaClass c 0 = 0 :=
  (meromorphicNFOn_completedPartialZetaClass c (mem_univ 0))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by simp)

/-! ### Functional equation -/

/-- **Hecke's functional equation for completed partial zeta functions**, Neukirch VII (5.9):
`Z(I, 1 - s) = Z(I^∨, s)` for every `s : ℂ` (at the poles `0` and `1` both sides take the
normal-form value `0`). -/
theorem completedPartialZeta_one_sub (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (1 - s) =
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s := by
  by_cases h0 : s = 0
  · subst h0
    simp
  by_cases h1 : s = 1
  · subst h1
    simp
  exact completedPartialZeta_one_sub_of_ne I h0 h1

/-- Punctured-germ form of `TauCeti.LFunctions.completedPartialZeta_one_sub` at every point
`s : ℂ` (poles included). -/
theorem completedPartialZeta_one_sub_eventuallyEq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (fun z : ℂ ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s]
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) :=
  Eventually.of_forall (completedPartialZeta_one_sub I)

/-- **Hecke's functional equation on ideal classes**, Neukirch VII (5.9):
`completedPartialZetaClass c (1 - s) = completedPartialZetaClass ([𝔡] * c⁻¹) s`, where
`[𝔡] = (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ 1))⁻¹` is the class of the different
ideal. -/
theorem completedPartialZetaClass_one_sub (c : ClassGroup (𝓞 K)) (s : ℂ) :
    completedPartialZetaClass c (1 - s) =
      completedPartialZetaClass
        ((ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _)))⁻¹ * c⁻¹) s := by
  obtain ⟨I, rfl⟩ := exists_fractionalIdeal_inv_mk (K := K) c
  rw [← completedPartialZeta_eq_completedPartialZetaClass, completedPartialZeta_one_sub,
    completedPartialZeta_eq_completedPartialZetaClass, FractionalIdeal.classGroupMk_dualEquiv,
    mul_inv]

/-- Punctured-germ form of `TauCeti.LFunctions.completedPartialZetaClass_one_sub` at every point
`s : ℂ` (poles included). -/
theorem completedPartialZetaClass_one_sub_eventuallyEq (c : ClassGroup (𝓞 K)) (s : ℂ) :
    (fun z : ℂ ↦ completedPartialZetaClass c (1 - z)) =ᶠ[𝓝[≠] s]
      completedPartialZetaClass
        ((ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _)))⁻¹ * c⁻¹) :=
  Eventually.of_forall (completedPartialZetaClass_one_sub c)

/-! ### Reflection symmetry -/

/-- **Reflection symmetry of a class-indexed completed partial zeta function**:
`completedPartialZetaClass c (conj s) = conj (completedPartialZetaClass c s)` for every `s : ℂ`. -/
@[simp]
theorem completedPartialZetaClass_conj (c : ClassGroup (𝓞 K)) (s : ℂ) :
    completedPartialZetaClass c (conj s) = conj (completedPartialZetaClass c s) := by
  have hnf : MeromorphicNFOn (conj ∘ completedPartialZetaClass c ∘ conj) univ :=
    TauCeti.meromorphicNFOn_conj_conj_iff.mpr
      (by simpa using meromorphicNFOn_completedPartialZetaClass c)
  have hfun : conj ∘ completedPartialZetaClass c ∘ conj = completedPartialZetaClass c := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1) hnf
      (meromorphicNFOn_completedPartialZetaClass c) fun z hz ↦ ?_
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply]
    rw [completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one c hzc,
      completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one c hz]
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (z / 2) := by
      have hnonneg : (0 : ℝ) ≤ (|discr K| : ℤ) := by exact_mod_cast abs_nonneg (discr K)
      have h := TauCeti.ofReal_cpow_conj hnonneg (conj z / 2)
      rw [Complex.ofReal_intCast, map_div₀, map_ofNat, Complex.conj_conj] at h
      exact h.symm
    have hcoeff : star (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c)) =
        rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c) := by
      funext J
      rw [Pi.star_apply, rayClassCoeff_apply]
      split_ifs <;> simp
    have hL : conj (LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c))) (conj z)) =
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c))) z := by
      have h := TauCeti.LSeries_normCoeff_star K
        (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c)) (conj z)
      rw [hcoeff, Complex.conj_conj] at h
      simpa only [Complex.star_def] using h.symm
    simp only [map_mul, map_pow, Gammaℝ_conj, Gammaℂ_conj, Complex.conj_conj, hdiscr, hL]
  simpa only [Function.comp_apply, Complex.conj_conj] using (congrFun hfun (conj s)).symm

end TauCeti.LFunctions
