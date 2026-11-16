/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
import TauCeti.NumberTheory.LSeries.Conjugate
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.TraceDual

/-!
# Completed partial zeta functions and the completed Dedekind zeta function

For each ideal class `c` of a number field `K`, the completed partial zeta function
`TauCeti.LFunctions.completedPartialZeta c` is the canonical meromorphic continuation from
`Re s > 1` of

`Λ(s, c) = |d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ(s, c)`.

Unfolding the theta kernel of an ideal lattice `σ(I)` with `[I⁻¹] = c` over any unit fundamental
domain `D` (`TauCeti.LFunctions.mellinKernelFEPair_idealLattice_Λ_div_two`) identifies `Λ(s, c)` on
`Re s > 1` with the completed function `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` of
Hecke's Mellin pair. Passing to meromorphic normal forms transfers the whole-plane meromorphy,
analyticity off `{0, 1}`, simple poles with residues `∓ 2 a₀ = ∓ 2^(r₁ + r₂) R / w` at `0` and `1`,
and functional equation

`Λ(1 - s, c) = Λ(s, [𝔡] * c⁻¹)`,

where `𝔡 = differentIdeal ℤ (𝓞 K)` is the different of `K`. Because `completedPartialZeta c` is
normalized in meromorphic normal form on `ℂ`, both poles take the canonical value `0`, so the
functional equation and reflection symmetry `conj (Λ(conj s, c)) = Λ(s, c)` hold pointwise on all
of `ℂ`.

Summing over `c : ClassGroup (𝓞 K)` gives the completed Dedekind zeta function
`TauCeti.LFunctions.completedDedekindZeta K`, which agrees with
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)` on `Re s > 1`, is meromorphic on `ℂ` and analytic off
`{0, 1}`, has simple poles at `0` and `1` with residues `∓ 2^(r₁ + r₂) R h / w`, satisfies
`Λ_K(1 - s) = Λ_K(s)` since `c ↦ [𝔡] * c⁻¹` permutes the class group, and satisfies
`conj (Λ_K(conj s)) = Λ_K(s)`.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function of an ideal class.
* `TauCeti.LFunctions.completedDedekindZeta`: the completed Dedekind zeta function of `K`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_eq_mellinKernelFEPair_Λ`,
  `TauCeti.LFunctions.completedPartialZeta_eq`: identification with the Mellin pair and the
  completed partial Dirichlet series.
* `TauCeti.LFunctions.analyticAt_completedPartialZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`: analyticity and simple poles
  of `completedPartialZeta`.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_conj`: functional equation and reflection symmetry of
  `completedPartialZeta`.
* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eq`: class-group decomposition and half-plane
  Dirichlet-series formula.
* `TauCeti.LFunctions.analyticAt_completedDedekindZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`: analyticity, residues, and
  simple poles of `completedDedekindZeta`.
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`,
  `TauCeti.LFunctions.completedDedekindZeta_conj`: the functional equation `Λ_K(1 - s) = Λ_K(s)`
  and reflection symmetry `conj (Λ_K(conj s)) = Λ_K(s)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Theorems 5.5 and 5.9, Corollary 5.10.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Completed partial zeta functions -/

/-- **The completed partial zeta function** of an ideal class `c : ClassGroup (𝓞 K)`: the
canonical meromorphic continuation (in meromorphic normal form on `ℂ`) from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ(s, c)`. -/
def completedPartialZeta (c : ClassGroup (𝓞 K)) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
      LSeries (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) s

theorem completedPartialZeta_def (c : ClassGroup (𝓞 K)) :
    completedPartialZeta c = meromorphicContinuation 1 (fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) s) :=
  (rfl)

/-- The completed partial zeta function is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (c : ClassGroup (𝓞 K)) :
    MeromorphicNFOn (completedPartialZeta c) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The completed partial zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (c : ClassGroup (𝓞 K)) :
    Meromorphic (completedPartialZeta c) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta c).meromorphicOn

open scoped Classical in
/-- On `ℂ`, the rescaled Mellin-pair function `s ↦ Λ(s / 2)` is meromorphic and analytic away from
`0` and `1`. -/
private theorem meromorphic_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Meromorphic (fun s : ℂ ↦ (mellinKernelFEPair hD L).Λ (s / 2)) := fun s ↦ by
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s := by
    simpa only [id_eq] using ((differentiable_id (𝕜 := ℂ)).div_const (2 : ℂ)).analyticAt s
  exact ((mellinKernelFEPair hD L).meromorphic_Λ ((fun z : ℂ ↦ z / 2) s)).comp_analyticAt
    (g := fun z : ℂ ↦ z / 2) hdiv

open scoped Classical in
private theorem analyticAt_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ (mellinKernelFEPair hD L).Λ (z / 2)) s := by
  have hs0 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hs1 : s / 2 ≠ ((mellinKernelFEPair hD L).k : ℂ) := by
    simp only [mellinKernelFEPair_k, ofReal_div, ofReal_one, ofReal_ofNat]
    exact fun h ↦ h1 ((div_left_inj₀ two_ne_zero).mp h)
  have hΛ : AnalyticAt ℂ (mellinKernelFEPair hD L).Λ ((fun z : ℂ ↦ z / 2) s) :=
    ((mellinKernelFEPair hD L).analyticAt_Λ_iff (s / 2)).mpr ⟨Or.inl hs0, Or.inl hs1⟩
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s := by
    simpa only [id_eq] using ((differentiable_id (𝕜 := ℂ)).div_const (2 : ℂ)).analyticAt s
  exact hΛ.comp (f := fun z : ℂ ↦ z / 2) hdiv

private theorem exists_fractionalIdeal_classGroup_inv_eq (c : ClassGroup (𝓞 K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (ClassGroup.mk K I)⁻¹ = c := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) c⁻¹
  refine ⟨FractionalIdeal.mk0 K J, ?_⟩
  rw [ClassGroup.mk_mk0, hJ, inv_inv]

/-- **Normal-form identification with Hecke's Mellin pair**: for any unit fundamental domain `D`
and fractional ideal `I` with `[I⁻¹] = c`, `completedPartialZeta c` is the meromorphic normal form
of `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {c : ClassGroup (𝓞 K)} (hc : (ClassGroup.mk K I)⁻¹ = c) :
    completedPartialZeta c =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  rw [completedPartialZeta_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_mellinKernelFEPair_Λ_div_two hD (idealLattice K I)) (fun s hs ↦ ?_)
    (fun s hs ↦ ?_)
  · have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact analyticAt_mellinKernelFEPair_Λ_div_two hD (idealLattice K I) h0 h1
  · rw [← hc]
    exact mellinKernelFEPair_idealLattice_Λ_div_two hD I hs

/-- At every `s : ℂ`, `completedPartialZeta c` has the same punctured germ as Hecke's Mellin pair
evaluated at `z / 2`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {c : ClassGroup (𝓞 K)} (hc : (ClassGroup.mk K I)⁻¹ = c) (s : ℂ) :
    completedPartialZeta c =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD hc]
  exact (meromorphic_mellinKernelFEPair_Λ_div_two hD
    (idealLattice K I)).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZeta c s` equals Hecke's Mellin-pair value
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {c : ClassGroup (𝓞 K)} (hc : (ClassGroup.mk K I)⁻¹ = c)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta c s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD hc]
  exact toMeromorphicNFOn_apply_of_analyticAt
    (meromorphic_mellinKernelFEPair_Λ_div_two hD (idealLattice K I))
    (analyticAt_mellinKernelFEPair_Λ_div_two hD (idealLattice K I) h0 h1)

/-- On `Re s > 1`, `completedPartialZeta c` equals the completed partial zeta Dirichlet series. -/
theorem completedPartialZeta_eq (c : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta c s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) s := by
  obtain ⟨I, hI⟩ := exists_fractionalIdeal_classGroup_inv_eq c
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ
      (isUnitFundamentalDomain_unitFundamentalDomain (K := K)) hI h0 h1,
    mellinKernelFEPair_idealLattice_Λ_div_two _ I hs, hI]

/-- The completed partial zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedPartialZeta (c : ClassGroup (𝓞 K)) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta c) s := by
  obtain ⟨I, hI⟩ := exists_fractionalIdeal_classGroup_inv_eq c
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hA := analyticAt_mellinKernelFEPair_Λ_div_two hD (idealLattice K I) h0 h1
  have hev : completedPartialZeta c =ᶠ[𝓝 s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
    filter_upwards [eventually_nhdsWithin_iff.mp
      (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD hI s)] with z hz
    rcases eq_or_ne z s with rfl | hne
    · exact completedPartialZeta_eq_mellinKernelFEPair_Λ hD hI h0 h1
    · exact hz hne
  exact (analyticAt_congr hev).mpr hA

/-- **Residue of `completedPartialZeta` at `s = 0`**: `s * Λ(s, c) → -2 a₀` as `s → 0`, where
`a₀ = mellinConstant K = 2^(r₁ + r₂ - 1) R / w`. -/
theorem tendsto_mul_completedPartialZeta_zero (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta c s) (𝓝[≠] 0)
      (𝓝 (-(2 * (mellinConstant K : ℂ)))) := by
  obtain ⟨I, hI⟩ := exists_fractionalIdeal_classGroup_inv_eq c
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  set P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_id.div_const (2 : ℂ)).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using div_ne_zero hz two_ne_zero
  have hres : Tendsto (fun s : ℂ ↦ (s / 2) * P.Λ (s / 2)) (𝓝[≠] 0)
      (𝓝 (-(mellinConstant K : ℂ))) := by
    simpa only [Function.comp_def, smul_eq_mul, P, mellinKernelFEPair_f₀] using
      P.Λ_residue_zero.comp hhalf
  have h2 : Tendsto (fun s : ℂ ↦ 2 * ((s / 2) * P.Λ (s / 2))) (𝓝[≠] 0)
      (𝓝 (2 * (-(mellinConstant K : ℂ)))) := hres.const_mul 2
  rw [mul_neg] at h2
  refine h2.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD hI 0] with s hs
  rw [hs]
  ring

/-- **Residue of `completedPartialZeta` at `s = 1`**: `(s - 1) * Λ(s, c) → 2 a₀` as `s → 1`, where
`a₀ = mellinConstant K = 2^(r₁ + r₂ - 1) R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta c s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  obtain ⟨I, hI⟩ := exists_fractionalIdeal_classGroup_inv_eq c
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  set P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    have hk : (P.k : ℂ) = 1 / 2 := by simp [P]
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · rw [hk]
      exact ((continuous_id.div_const (2 : ℂ)).tendsto (1 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [mem_compl_iff, mem_singleton_iff, hk]
      exact fun h ↦ hz ((div_left_inj₀ two_ne_zero).mp h)
  have hres : Tendsto (fun s : ℂ ↦ (s / 2 - 1 / 2) * P.Λ (s / 2)) (𝓝[≠] 1)
      (𝓝 (mellinConstant K : ℂ)) := by
    have h := P.Λ_residue_k.comp hhalf
    simpa only [Function.comp_def, smul_eq_mul, P, mellinKernelFEPair_k, mellinKernelFEPair_ε,
      mellinKernelFEPair_N, mellinKernelFEPair_g₀, ofReal_div, ofReal_one, ofReal_ofNat,
      one_cpow, mul_one, one_mul] using h
  have h2 : Tendsto (fun s : ℂ ↦ 2 * ((s / 2 - 1 / 2) * P.Λ (s / 2))) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := hres.const_mul 2
  refine h2.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD hI 1] with s hs
  rw [hs]
  ring

/-- The completed partial zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZeta c) 0 = (-1 : ℤ) := by
  have hne : -(2 * (mellinConstant K : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZeta c 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZeta_zero c

/-- The completed partial zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZeta c) 1 = (-1 : ℤ) := by
  have hne : 2 * (mellinConstant K : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  refine (meromorphic_completedPartialZeta c 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedPartialZeta c

/-- Because `completedPartialZeta` is in meromorphic normal form, it vanishes at its poles `0`
and `1`. -/
private theorem completedPartialZeta_zero (c : ClassGroup (𝓞 K)) :
    completedPartialZeta c 0 = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp
      (meromorphicNFOn_completedPartialZeta c (mem_univ 0)) with hA | ⟨_, _, h0⟩
  · have hge := hA.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero c] at hge
    exact absurd (WithTop.coe_le_coe.mp hge) (by norm_num)
  · exact h0

private theorem completedPartialZeta_one (c : ClassGroup (𝓞 K)) :
    completedPartialZeta c 1 = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp
      (meromorphicNFOn_completedPartialZeta c (mem_univ 1)) with hA | ⟨_, _, h0⟩
  · have hge := hA.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one c] at hge
    exact absurd (WithTop.coe_le_coe.mp hge) (by norm_num)
  · exact h0

/-- **Hecke's functional equation for a completed partial zeta function**, Neukirch VII (5.9):
`Λ(1 - s, c) = Λ(s, [𝔡] * c⁻¹)`, where `𝔡 = differentIdeal ℤ (𝓞 K)`. Since both sides are in
meromorphic normal form on `ℂ`, the equality holds at every `s : ℂ`, including the poles `0` and
`1` where both sides take the canonical value `0`. -/
theorem completedPartialZeta_one_sub (c : ClassGroup (𝓞 K)) (s : ℂ) :
    completedPartialZeta c (1 - s) =
      completedPartialZeta
        (ClassGroup.mk0 ⟨differentIdeal ℤ (𝓞 K),
          mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩ * c⁻¹) s := by
  rcases eq_or_ne s 0 with rfl | h0
  · rw [sub_zero, completedPartialZeta_one, completedPartialZeta_zero]
  rcases eq_or_ne s 1 with rfl | h1
  · rw [sub_self, completedPartialZeta_zero, completedPartialZeta_one]
  obtain ⟨I, hI⟩ := exists_fractionalIdeal_classGroup_inv_eq c
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
      (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)
  have hJval : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl
  -- Identify the class of `J⁻¹` as `[𝔡] * c⁻¹`.
  set 𝔡 : (Ideal (𝓞 K))⁰ :=
    ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩
  have hJclass : (ClassGroup.mk K J)⁻¹ = ClassGroup.mk0 𝔡 * c⁻¹ := by
    have hJinv : J⁻¹ = FractionalIdeal.mk0 K 𝔡 * I := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val, Units.val_mul, FractionalIdeal.coe_mk0, hJval,
        FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K), mul_inv, inv_inv,
        ← coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
    rw [← map_inv, hJinv, map_mul, ClassGroup.mk_mk0, ← hI, inv_inv]
  -- Compare the Mellin pairs of `mixedDual K (idealLattice K I)` and `idealLattice K J`.
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  have hΛ_eq :
      (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
        (mellinKernelFEPair hD' (idealLattice K J)).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, indicator_of_mem hu]
    exact mellinKernel_mixedDual_idealLattice hJval _ u
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  have hhalf0 : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hhalf1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h1s1 ((div_left_inj₀ two_ne_zero).mp h)
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD hI h1s0 h1s1,
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) hhalf0 hhalf1, hΛ_eq,
    show (1 / 2 : ℂ) - (1 - s) / 2 = s / 2 by ring,
    ← completedPartialZeta_eq_mellinKernelFEPair_Λ hD' hJclass h0 h1]

/-- Reflection preserves meromorphic normal form on `ℂ`. -/
private theorem meromorphicNFOn_conj_conj {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) :
    MeromorphicNFOn (conj ∘ f ∘ conj) univ := by
  intro z _
  rw [meromorphicNFAt_iff_analyticAt_or]
  rcases meromorphicNFAt_iff_analyticAt_or.mp (hf (mem_univ (conj z))) with hA | ⟨hM, hlt, h0⟩
  · exact Or.inl (TauCeti.analyticAt_conj_conj_iff.mpr hA)
  · refine Or.inr ⟨TauCeti.meromorphicAt_conj_conj_iff.mpr hM, ?_, ?_⟩
    · rwa [TauCeti.meromorphicOrderAt_conj_conj]
    · simp only [Function.comp_apply, h0, map_zero]

/-- **Reflection symmetry of a completed partial zeta function**:
`conj (Λ(conj s, c)) = Λ(s, c)` for every `s : ℂ`. -/
theorem completedPartialZeta_conj (c : ClassGroup (𝓞 K)) (s : ℂ) :
    conj (completedPartialZeta c (conj s)) = completedPartialZeta c s := by
  have hnf : MeromorphicNFOn (conj ∘ completedPartialZeta c ∘ conj) univ :=
    meromorphicNFOn_conj_conj (meromorphicNFOn_completedPartialZeta c)
  have hfun : conj ∘ completedPartialZeta c ∘ conj = completedPartialZeta c := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1) hnf
      (meromorphicNFOn_completedPartialZeta c) fun z hz ↦ ?_
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply]
    rw [completedPartialZeta_eq c hzc, completedPartialZeta_eq c hz]
    -- Each factor commutes with conjugation because its parameters and coefficients are real.
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (z / 2) := by
      have hnonneg : (0 : ℝ) ≤ (|discr K| : ℤ) := by exact_mod_cast abs_nonneg (discr K)
      have h := TauCeti.ofReal_cpow_conj hnonneg (conj z / 2)
      rw [Complex.ofReal_intCast, map_div₀, map_ofNat, Complex.conj_conj] at h
      exact h.symm
    have hcoeff : star (⇑(normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm c)))) =
        ⇑(normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) := by
      funext n
      simp only [Pi.star_apply, normCoeff_eq_sum_normFiber, star_sum, rayClassCoeff_apply]
      refine Finset.sum_congr rfl fun I _ ↦ ?_
      split_ifs <;> simp
    have hL : conj (LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c))) (conj z)) =
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) z := by
      have h := TauCeti.LSeries.LSeries_star
        (normCoeff K (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c))) z
      rw [hcoeff] at h
      simpa only [Complex.star_def, Complex.conj_conj] using congrArg conj h
    simp only [map_mul, map_pow, Gammaℝ_conj, Gammaℂ_conj, Complex.conj_conj, hdiscr, hL]
  exact congrFun hfun s

/-! ### The completed Dedekind zeta function -/

variable (K) in
/-- **The completed Dedekind zeta function** of a number field `K`: the canonical meromorphic
continuation (in meromorphic normal form on `ℂ`) from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
      NumberField.dedekindZeta K s

variable (K) in
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 (fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        NumberField.dedekindZeta K s) :=
  (rfl)

variable (K) in
/-- The completed Dedekind zeta function is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedDedekindZeta : MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

variable (K) in
/-- The completed Dedekind zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

variable (K) in
/-- Algebraic identity relating the sum of the partial-zeta residues `h * (2 a₀)` to the
completed Dedekind zeta residue `2^(r₁ + r₂) R h / w`. -/
private theorem classNumber_mul_two_mul_mellinConstant :
    (classNumber K : ℝ) * (2 * mellinConstant K) =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K := by
  have hr : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have h2pow : (2 : ℝ) * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  rw [mellinConstant_def]
  calc (classNumber K : ℝ) *
        (2 * (2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K))
      = (2 * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1)) * regulator K * classNumber K /
          torsionOrder K := by ring
    _ = 2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
          torsionOrder K := by rw [h2pow]

variable (K) in
/-- The completed Dedekind zeta residue equals `|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ ρ_K`, where
`ρ_K = NumberField.dedekindZeta_residue K`. -/
theorem completedDedekindZeta_residue_eq :
    (((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ)) =
      ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) *
        Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K *
        (NumberField.dedekindZeta_residue K : ℂ) := by
  have hd_pos : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hsqrt : ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt |(discr K : ℝ)| : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hd_pos.le, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, ← Int.cast_abs, Complex.ofReal_intCast]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hsq : (Real.sqrt |(discr K : ℝ)| : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd_pos).ne'
  rw [hsqrt, Gammaℝ_one, one_pow, mul_one, Gammaℂ_one, dedekindZeta_residue_def]
  push_cast
  rw [pow_add, mul_pow, one_div, inv_pow]
  field_simp

/-- **Class-group decomposition of the completed Dedekind zeta function**:
`Λ_K(s) = ∑_{c ∈ Cl_K} Λ(s, c)` for every `s : ℂ`, including the poles `0` and `1` where both
sides are in meromorphic normal form and take the value `0`. -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta (s : ℂ) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZeta c s := by
  let F : ℂ → ℂ := fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta c z
  have hM : Meromorphic F := fun z ↦ MeromorphicAt.fun_sum fun c _ ↦
    meromorphic_completedPartialZeta c z
  have hres0 : Tendsto (fun z : ℂ ↦ z * F z) (𝓝[≠] 0)
      (𝓝 (-(classNumber K * (2 * (mellinConstant K : ℂ))))) := by
    have hsum : Tendsto (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), z * completedPartialZeta c z)
        (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ)))) :=
      tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_mul_completedPartialZeta_zero c
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg] at hsum
    rw [← NumberField.classNumber] at hsum
    exact hsum.congr fun z ↦ (Finset.mul_sum _ _ _).symm
  have hres1 : Tendsto (fun z : ℂ ↦ (z - 1) * F z) (𝓝[≠] 1)
      (𝓝 (classNumber K * (2 * (mellinConstant K : ℂ)))) := by
    have hsum : Tendsto (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), (z - 1) * completedPartialZeta c z)
        (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
      tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta c
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rw [← NumberField.classNumber] at hsum
    exact hsum.congr fun z ↦ (Finset.mul_sum _ _ _).symm
  have hne_res : (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  -- Show `F` is already in meromorphic normal form on `ℂ`.
  have hNF : MeromorphicNFOn F univ := by
    intro z _
    rw [meromorphicNFAt_iff_analyticAt_or]
    rcases eq_or_ne z 0 with rfl | hz0
    · refine Or.inr ⟨hM 0, ?_, ?_⟩
      · have hord := (hM 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
          (neg_ne_zero.mpr hne_res) (by simpa only [sub_zero, smul_eq_mul] using hres0)
        rw [hord]
        exact WithTop.coe_lt_zero.mpr (by norm_num)
      · simp [F, completedPartialZeta_zero]
    rcases eq_or_ne z 1 with rfl | hz1
    · refine Or.inr ⟨hM 1, ?_, ?_⟩
      · have hord := (hM 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
          hne_res (by simpa only [smul_eq_mul] using hres1)
        rw [hord]
        exact WithTop.coe_lt_zero.mpr (by norm_num)
      · simp [F, completedPartialZeta_one]
    · exact Or.inl (Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
        analyticAt_completedPartialZeta c hz0 hz1)
  have heq : completedDedekindZeta K = F := by
    rw [completedDedekindZeta_def]
    refine meromorphicContinuation_eq hNF fun z hz ↦ ?_
    simp only [F]
    simp_rw [completedPartialZeta_eq _ hz, ← Finset.mul_sum]
    congr 1
    let _ : Fintype (RayClassGroup (Modulus.one K)) :=
      Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
    rw [← sum_LSeries_rayClassCoeff_one hz]
    exact Equiv.sum_comp oneEquivClassGroup.symm.toEquiv
      (fun c ↦ LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) z)
  exact congrFun heq s

/-- On `Re s > 1`, `completedDedekindZeta K` equals `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        NumberField.dedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta]
  simp_rw [completedPartialZeta_eq _ hs, ← Finset.mul_sum]
  congr 1
  let _ : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
  rw [← sum_LSeries_rayClassCoeff_one hs]
  exact Equiv.sum_comp oneEquivClassGroup.symm.toEquiv
    (fun c ↦ LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s)

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  have heq : completedDedekindZeta K = fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta c z :=
    funext completedDedekindZeta_eq_sum_completedPartialZeta
  rw [heq]
  exact Finset.analyticAt_fun_sum Finset.univ fun c _ ↦ analyticAt_completedPartialZeta c h0 h1

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 0`**:
`s * Λ_K(s) → -2^(r₁ + r₂) R h / w` as `s → 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ))) := by
  have hsum : Tendsto (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K), s * completedPartialZeta c s)
      (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_mul_completedPartialZeta_zero c
  have hlim : ∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ)) =
      -((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← NumberField.classNumber, mul_neg,
      ← classNumber_mul_two_mul_mellinConstant]
    push_cast
    rfl
  rw [hlim] at hsum
  exact hsum.congr fun s ↦ by
    rw [completedDedekindZeta_eq_sum_completedPartialZeta, Finset.mul_sum]

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 1`**:
`(s - 1) * Λ_K(s) → 2^(r₁ + r₂) R h / w` as `s → 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ)) := by
  have hsum : Tendsto (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K), (s - 1) * completedPartialZeta c s)
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta c
  have hlim : ∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)) =
      ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← NumberField.classNumber,
      ← classNumber_mul_two_mul_mellinConstant]
    push_cast
    rfl
  rw [hlim] at hsum
  exact hsum.congr fun s ↦ by
    rw [completedDedekindZeta_eq_sum_completedPartialZeta, Finset.mul_sum]

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  have hpos : (0 : ℝ) <
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K := by
    have := regulator_pos K
    have : (0 : ℝ) < classNumber K := Nat.cast_pos.mpr (classNumber_pos K)
    have : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (torsionOrder_pos K)
    positivity
  refine (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr (ofReal_ne_zero.mpr hpos.ne')) ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  have hpos : (0 : ℝ) <
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K := by
    have := regulator_pos K
    have : (0 : ℝ) < classNumber K := Nat.cast_pos.mpr (classNumber_pos K)
    have : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (torsionOrder_pos K)
    positivity
  refine (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (ofReal_ne_zero.mpr hpos.ne') ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K

variable (K) in
/-- **Hecke's functional equation for the completed Dedekind zeta function**, Neukirch VII
Corollary 5.10: `Λ_K(1 - s) = Λ_K(s)` for every `s : ℂ`. -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  set d : ClassGroup (𝓞 K) :=
    ClassGroup.mk0 ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) := (Equiv.inv _).trans (Equiv.mulLeft d)
  rw [completedDedekindZeta_eq_sum_completedPartialZeta,
    completedDedekindZeta_eq_sum_completedPartialZeta]
  simp_rw [completedPartialZeta_one_sub]
  exact Equiv.sum_comp e (fun c ↦ completedPartialZeta c s)

variable (K) in
/-- **Reflection symmetry of the completed Dedekind zeta function**:
`conj (Λ_K(conj s)) = Λ_K(s)` for every `s : ℂ`. -/
theorem completedDedekindZeta_conj (s : ℂ) :
    conj (completedDedekindZeta K (conj s)) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta,
    completedDedekindZeta_eq_sum_completedPartialZeta, map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_conj c s

end TauCeti.LFunctions
