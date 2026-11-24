/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
public import TauCeti.RingTheory.DedekindDomain.Different.ClassGroup
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Completed partial zeta functions of ideal classes

For an ideal class `c : ClassGroup (𝓞 K)` of a number field `K`, we define
`TauCeti.LFunctions.completedPartialZetaClass c` as the canonical whole-plane meromorphic
normal-form continuation (`TauCeti.meromorphicContinuation 1`) from `Re s > 1` of

`Z(c, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ c} N(𝔟) ^ (-s)`,

where the sum runs over the nonzero integral ideals `𝔟` of `𝓞 K` in the class `c`. For an
invertible fractional ideal `I`, the inverse class `(ClassGroup.mk K I)⁻¹` indexes the nonzero
integral ideals `𝔟` such that `𝔟 I` is principal.

Following Hecke (Neukirch, Chapter VII, §5), we combine the unit-cone unfolding in
`TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding`
(`hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum` and
`mellinKernelFEPair_Λ_div_two_eq_tsum`) to identify
`completedPartialZetaClass (ClassGroup.mk K I)⁻¹` on `Re s > 1` with the Mellin transform at
`s / 2` of `mellinKernel D (idealLattice K I) - mellinConstant K`, and hence globally with the
normal form of `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.

From `mellinKernelFEPair` and the trace-dual kernel identity `mellinKernel_mixedDual_idealLattice`
we deduce meromorphic continuation to `ℂ`, analyticity away from simple poles at `s = 0` and
`s = 1` with residues `-2 a₀ = -2 ^ (r₁ + r₂) R / w` and `2 a₀ = 2 ^ (r₁ + r₂) R / w`
(`a₀ = mellinConstant K`), and Hecke's functional equation
`completedPartialZetaClass c (1 - s) = completedPartialZetaClass (differentClass K * c⁻¹) s`,
where `TauCeti.LFunctions.differentClass K`
(`= (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ 1))⁻¹`) is the class of the different ideal.

## Main definitions

* `TauCeti.LFunctions.completedPartialZetaClass`: the completed partial zeta function of an ideal
  class `c : ClassGroup (𝓞 K)` in meromorphic normal form on `ℂ`, continuing the ideal series
  `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ c} N(𝔟) ^ (-s)` from `Re s > 1`.
* `TauCeti.LFunctions.differentClass`: the ideal class of `differentIdeal ℤ (𝓞 K)` in
  `ClassGroup (𝓞 K)`.

## Main results

* `TauCeti.LFunctions.differentClass_def`,
  `TauCeti.LFunctions.differentClass_eq_inv_mk_dualEquiv_one`: defining formula and
  inverse-different identity for `differentClass K`.
* `TauCeti.LFunctions.completedPartialZetaClass_eq_toMeromorphicNFOn`: identification of
  `completedPartialZetaClass (ClassGroup.mk K I)⁻¹` with the normal form of
  `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.
* `TauCeti.LFunctions.completedPartialZetaClass_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_tsum_spanSingleton`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_tsum_fundamentalCone`: representations on
  `Re s > 1` over ideal classes, the trivial-modulus ray-class Dirichlet series, principal
  products, and fundamental-cone lattice points.
* `hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZetaClass`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_mellin`,
  `TauCeti.LFunctions.completedPartialZetaClass_eq_integral_unitCone`: Mellin-transform and
  cone-integral representations on `Re s > 1` (Neukirch VII (5.5)).
* `TauCeti.LFunctions.analyticAt_completedPartialZetaClass_iff`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZetaClass`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZetaClass_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZetaClass_one`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZetaClass_zero`: regularity, simple
  poles at `0` and `1`, and their residues.
* `TauCeti.LFunctions.completedPartialZetaClass_one_sub`,
  `TauCeti.LFunctions.completedPartialZetaClass_conj`: Hecke's functional equation and reflection
  symmetry.

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
nonzero integral ideals `𝔟` of `𝓞 K` in the class `c`. -/
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

variable (K) in
/-- **The ideal class of the different ideal** `differentIdeal ℤ (𝓞 K)` in `ClassGroup (𝓞 K)`. -/
def differentClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩

variable (K) in
/-- Defining equation of `TauCeti.LFunctions.differentClass`. -/
theorem differentClass_def :
    differentClass K =
      ClassGroup.mk0
        ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩ :=
  (rfl)

variable (K) in
/-- The ideal class of the different ideal equals the inverse of the class of the inverse
different `FractionalIdeal.dualEquiv ℤ ℚ 1`. -/
theorem differentClass_eq_inv_mk_dualEquiv_one :
    differentClass K =
      (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)))⁻¹ := by
  rw [differentClass_def, ClassGroup.mk0_differentIdeal ℤ ℚ (L := K)]

private theorem exists_inv_classGroupMk (c : ClassGroup (𝓞 K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (ClassGroup.mk K I)⁻¹ = c := by
  obtain ⟨I, hI⟩ := ClassGroup.mk_surjective (𝓞 K) K c⁻¹
  exact ⟨I, by rw [hI, inv_inv]⟩

/-! ### Identification with the Mellin functional-equation pair -/

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
`completedPartialZetaClass (ClassGroup.mk K I)⁻¹` is the whole-plane meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZetaClass_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  rw [completedPartialZetaClass_def]
  exact meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticOnNhd_mellinKernelFEPair_Λ_div_two hD I)
    fun _ hs ↦ mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs

/-- At every point `s : ℂ` (poles included), `completedPartialZetaClass (ClassGroup.mk K I)⁻¹` has
the same punctured germ as `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZetaClass_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZetaClass_eq_toMeromorphicNFOn hD I]
  exact (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s` agrees
pointwise with `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZetaClass_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s =
      (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZetaClass_eq_toMeromorphicNFOn hD I]
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
  obtain ⟨I, rfl⟩ := exists_inv_classGroupMk c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZetaClass_eq_toMeromorphicNFOn hD I,
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
theorem completedPartialZetaClass_eq_tsum_spanSingleton (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZetaClass_eq_tsum _ hs]
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
theorem completedPartialZetaClass_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (Units.torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  rw [completedPartialZetaClass_eq_tsum _ hs,
    tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone I hs]
  ring

/-- **Mellin-transform representation on `Re s > 1` (`HasMellin` form)**, Neukirch VII (5.5):
`completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s` is the Mellin transform at `s / 2` of
`mellinKernel D (idealLattice K I) - mellinConstant K`. -/
theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZetaClass
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s) := by
  rw [completedPartialZetaClass_eq_tsum _ hs]
  exact hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum hD I hs

/-- **Mellin-transform representation on `Re s > 1` (`mellin` form)**, Neukirch VII (5.5). -/
theorem completedPartialZetaClass_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZetaClass
    hD I hs).2.symm

open scoped Classical in
/-- **Cone-integral representation on `Re s > 1`**, Neukirch VII (5.5): over any unit fundamental
domain `D`, `completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s` is `(2 ^ r₂ / w) V_{σ(I)} ^ s`
times the cone integral of `N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)`. -/
theorem completedPartialZetaClass_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZetaClass (ClassGroup.mk K I)⁻¹ s =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have hm₁ :=
    hasMellin_mellinKernel_idealLattice_sub_mellinConstant_completedPartialZetaClass hD I hs
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
  obtain ⟨I, rfl⟩ := exists_inv_classGroupMk c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZetaClass_eq_toMeromorphicNFOn hD I,
    ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn
      (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn (mem_univ s)]
  exact (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1).meromorphicOrderAt_nonneg

/-- **Residue of `completedPartialZetaClass c` at `s = 1`**, Neukirch VII (5.9):
`lim_{s → 1} (s - 1) Z(c, s) = 2 a₀ = 2 ^ (r₁ + r₂) R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZetaClass (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZetaClass c s) (𝓝[≠] 1)
      (𝓝 ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * Units.regulator K /
        Units.torsionOrder K : ℝ) : ℂ)) := by
  obtain ⟨I, rfl⟩ := exists_inv_classGroupMk c
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      ((continuous_id'.div_const (2 : ℂ)).continuousAt (x := 1)).tendsto_nhdsNE
        fun _ _ ↦ (div_left_inj₀ two_ne_zero).mp
  have hres := P.Λ_residue_k
  simp only [P, mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, ofReal_one, one_cpow, mul_one, smul_eq_mul, one_mul] at hres
  rw [← two_mul_mellinConstant, ofReal_mul, ofReal_ofNat]
  refine ((hres.comp hhalf).const_mul 2).congr' ?_
  filter_upwards [completedPartialZetaClass_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with s hs
  rw [Function.comp_apply, hs]
  push_cast
  ring

/-- `completedPartialZetaClass c` has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZetaClass_one (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZetaClass c) 1 = (-1 : ℤ) := by
  have ha :
      ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * Units.regulator K /
        Units.torsionOrder K : ℝ) : ℂ) ≠ 0 := by
    rw [← two_mul_mellinConstant]
    exact ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero (mellinConstant_ne_zero K))
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

private theorem completedPartialZetaClass_one_sub_of_ne (c : ClassGroup (𝓞 K))
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZetaClass c (1 - s) =
      completedPartialZetaClass (differentClass K * c⁻¹) s := by
  obtain ⟨I, rfl⟩ := exists_inv_classGroupMk c
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  have hd : (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ I))⁻¹ =
      differentClass K * ((ClassGroup.mk K I)⁻¹)⁻¹ := by
    rw [ClassGroup.mk_dualEquiv, mul_inv, differentClass_eq_inv_mk_dualEquiv_one]
  rw [completedPartialZetaClass_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1, ← hd,
    completedPartialZetaClass_eq_mellinKernelFEPair_Λ hD' (FractionalIdeal.dualEquiv ℤ ℚ I) h0 h1]
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

/-- **Residue of `completedPartialZetaClass c` at `s = 0`**, Neukirch VII (5.9):
`lim_{s → 0} s Z(c, s) = -2 a₀ = -2 ^ (r₁ + r₂) R / w`. -/
theorem tendsto_mul_completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZetaClass c s) (𝓝[≠] 0)
      (𝓝 (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * Units.regulator K /
        Units.torsionOrder K : ℝ) : ℂ))) := by
  have hsub : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] 1) := by
    simpa only [sub_zero] using
      ((continuous_sub_left (1 : ℂ)).continuousAt (x := (0 : ℂ))).tendsto_nhdsNE
        fun _ _ h ↦ sub_right_injective h
  have hlim :=
    ((tendsto_sub_one_mul_completedPartialZetaClass (differentClass K * c⁻¹)).comp hsub).neg
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1))] with s hs0 hs1
  have hfe := completedPartialZetaClass_one_sub_of_ne (differentClass K * c⁻¹) hs0 hs1
  rw [mul_inv, mul_inv_cancel_left, inv_inv] at hfe
  simp only [Function.comp_apply, hfe]
  ring

/-- `completedPartialZetaClass c` has a simple pole at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    meromorphicOrderAt (completedPartialZetaClass c) 0 = (-1 : ℤ) := by
  have ha :
      -((2 ^ (nrRealPlaces K + nrComplexPlaces K) * Units.regulator K /
        Units.torsionOrder K : ℝ) : ℂ) ≠ 0 := by
    rw [← two_mul_mellinConstant]
    exact neg_ne_zero.mpr (ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZetaClass c 0)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZetaClass_zero c

/-- `completedPartialZetaClass c` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZetaClass_iff (c : ClassGroup (𝓞 K)) {s : ℂ} :
    AnalyticAt ℂ (completedPartialZetaClass c) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZetaClass c h0 h1⟩
  · rintro rfl
    exact TauCeti.not_analyticAt_of_meromorphicOrderAt_eq_neg_one
      (meromorphicOrderAt_completedPartialZetaClass_zero c) han
  · rintro rfl
    exact TauCeti.not_analyticAt_of_meromorphicOrderAt_eq_neg_one
      (meromorphicOrderAt_completedPartialZetaClass_one c) han

/-- As a meromorphic normal form, `completedPartialZetaClass c` takes the canonical value `0` at
its pole `s = 0`. -/
@[simp]
theorem completedPartialZetaClass_zero (c : ClassGroup (𝓞 K)) :
    completedPartialZetaClass c 0 = 0 :=
  (meromorphicNFOn_completedPartialZetaClass c (mem_univ 0))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by simp)

/-! ### Functional equation -/

/-- **Hecke's functional equation on ideal classes**, Neukirch VII (5.9):
`completedPartialZetaClass c (1 - s) = completedPartialZetaClass (differentClass K * c⁻¹) s`,
where `differentClass K` is the ideal class of `differentIdeal ℤ (𝓞 K)`. -/
theorem completedPartialZetaClass_one_sub (c : ClassGroup (𝓞 K)) (s : ℂ) :
    completedPartialZetaClass c (1 - s) =
      completedPartialZetaClass (differentClass K * c⁻¹) s := by
  by_cases h0 : s = 0
  · subst h0
    simp
  by_cases h1 : s = 1
  · subst h1
    simp
  exact completedPartialZetaClass_one_sub_of_ne c h0 h1

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
    have hL : conj (LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c))) (conj z)) =
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c))) z := by
      have h := TauCeti.LSeries_normCoeff_star K
        (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm c)) (conj z)
      rw [star_rayClassCoeff, Complex.conj_conj] at h
      simpa only [Complex.star_def] using h.symm
    simp only [map_mul, map_pow, Gammaℝ_conj, Gammaℂ_conj, Complex.conj_conj, hdiscr, hL]
  simpa only [Function.comp_apply, Complex.conj_conj] using (congrFun hfun (conj s)).symm

end TauCeti.LFunctions
