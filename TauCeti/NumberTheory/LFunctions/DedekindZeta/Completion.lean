/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.Theta.UnitFundamentalDomain
import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Completed partial zeta functions and the completed Dedekind zeta function

For a number field `K`, this file constructs the completed partial zeta functions
`TauCeti.LFunctions.completedPartialZeta` of ideal classes and the completed Dedekind zeta function
`TauCeti.LFunctions.completedDedekindZeta`, establishes Hecke's functional equation and simple-pole
residues at `s = 0` and `s = 1`, and deduces the full meromorphic continuation, residue at `s = 1`,
and leading-term expansion at `s = 0` of `TauCeti.LFunctions.dedekindZetaC K`
(Neukirch, Chapter VII, §5, (5.5)–(5.11)).

## Main definitions

* `TauCeti.LFunctions.dualUnit`: the trace dual `I^∨ = (I 𝔡)⁻¹` as a unit of the fractional
  ideals.
* `TauCeti.LFunctions.completedPartialZeta`: the canonical meromorphic continuation from `Re s > 1`
  of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ(s, [I⁻¹])`.
* `TauCeti.LFunctions.completedDedekindZeta`: the canonical meromorphic continuation from
  `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_eq_mellinKernelFEPair_Λ`: away from `0` and `1`, the
  completed partial zeta function equals `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` for
  every unit fundamental domain `D`.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`: the functional equation
  `completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s`.
* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`: the completed Dedekind
  zeta function is the sum of the completed partial zeta functions over the ideal classes.
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`,
  `TauCeti.LFunctions.completedDedekindZeta_conj`: the functional equation `Λ_K(1 - s) = Λ_K(s)`
  and reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.
* `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`: simple poles of `Λ_K` at `0`
  and `1` with residues `∓ 2^(r₁ + r₂) h R / w`.
* `TauCeti.LFunctions.analyticAt_dedekindZetaC`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`: meromorphic continuation of
  `dedekindZetaC K`, analytic away from its simple pole at `s = 1` with residue
  `dedekindZeta_residue K`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.tendsto_dedekindZetaC_div_pow_rank_zero`: at `s = 0`, `dedekindZetaC K`
  vanishes to order `Units.rank K` with leading coefficient `-h R / w` (Neukirch VII (5.11)).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5)–(5.11).
-/

public section
noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The trace dual as a fractional-ideal unit -/

/-- The trace dual `I^∨ = FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹` of an invertible
fractional ideal `I`, packaged as a unit of `FractionalIdeal (𝓞 K)⁰ K`. -/
def dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero (A := ℤ) (K := ℚ) I.ne_zero)

@[simp]
theorem coe_dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (dualUnit I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := (rfl)

/-- The trace dual satisfies `I^∨ = (1^∨) I⁻¹` as a unit of the fractional ideals. -/
theorem dualUnit_eq_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualUnit I = dualUnit 1 * I⁻¹ := by
  apply Units.ext
  simpa [coe_dualUnit, Units.val_mul] using
    FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)

/-- The trace dual is an involution on invertible fractional ideals. -/
@[simp]
theorem dualUnit_dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualUnit (dualUnit I) = I :=
  Units.ext (FractionalIdeal.dual_dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))

/-! ### Auxiliary lemmas on normal forms and class-group sums -/

/-- Reflection across the real axis preserves meromorphic normal form on `ℂ`. -/
private theorem meromorphicNFOn_conj_conj {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) :
    MeromorphicNFOn (conj ∘ f ∘ conj) univ := fun z _ ↦ by
  rw [meromorphicNFAt_iff_analyticAt_or]
  rcases meromorphicNFAt_iff_analyticAt_or.mp (hf (mem_univ (conj z))) with ha | ⟨hm, ho, hz⟩
  · exact Or.inl (analyticAt_conj_conj_iff.mpr ha)
  · exact Or.inr ⟨meromorphicAt_conj_conj_iff.mpr hm, by rwa [meromorphicOrderAt_conj_conj],
      by simp [hz]⟩

/-- A meromorphic normal form vanishes at any simple pole. -/
private theorem eq_zero_of_meromorphicNFOn_of_order_eq_neg_one {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f univ) {p : ℂ} (hp : meromorphicOrderAt f p = (-1 : ℤ)) : f p = 0 :=
  not_ne_iff.mp <| (hf (mem_univ p)).meromorphicOrderAt_eq_zero_iff.not.mp (by rw [hp]; simp)

/-- The Dirichlet series of the class of `I⁻¹` at the trivial modulus equals the sum of
`N(𝔟)^(-s)` over nonzero integral ideals `𝔟` with `𝔟 I` principal. -/
private theorem LSeries_rayClassCoeff_one_eq_tsum_fractional (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s =
      ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
          (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  set c : RayClassGroup (Modulus.one K) := oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹
  rw [LSeries_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re
    (norm_rayClassCoeff_le_one (Modulus.one K) c) hs)]
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ≃
      {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} :=
    { toFun := fun 𝔟 ↦ ⟨𝔟.1.1, nonZeroDivisors.coe_ne_zero 𝔟.1, 𝔟.2⟩
      invFun := fun 𝔟 ↦ ⟨⟨𝔟.1, mem_nonZeroDivisors_of_ne_zero 𝔟.2.1⟩, 𝔟.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← e.tsum_eq]
  refine Eq.symm ((tsum_subtype {𝔟 : (Ideal (𝓞 K))⁰ | ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)}
    fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).trans
      (tsum_congr fun 𝔟 ↦ ?_))
  have hcop : (Modulus.one K).IsCoprimeTo (𝔟 : Ideal (𝓞 K)) :=
    Modulus.mem_integralIdealsPrimeTo.mp <| by
      simpa using (integralIdealsPrimeToOneEquiv.symm 𝔟).2
  have hclass :
      idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
        ∃ x : Kˣ, ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
    have hiff :
        idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
          oneEquivClassGroup
            (idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩) =
            (ClassGroup.mk K I)⁻¹ := by
      simp only [c, ← oneEquivClassGroup.apply_eq_iff_eq, MulEquiv.apply_symm_apply]
    rw [hiff, idealClass_apply, oneEquivClassGroup_rayClassMk, eq_inv_iff_mul_eq_one,
      ← map_mul, ClassGroup.mk_eq_one_iff_exists]
    refine exists_congr fun x ↦ ?_
    rw [Units.ext_iff, Units.val_mul, coe_toPrincipalIdeal,
      NumberFieldArithmetic.coe_integralIdealsAwayHom]
    exact eq_comm
  rw [idealTerm_def, rayClassCoeff_apply_of_isCoprimeTo c hcop, Set.indicator_apply]
  by_cases h : ∃ x : Kˣ, ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)
  · simp [hclass.mpr h, h, Complex.cpow_neg]
  · simp [mt hclass.mp h, h]

/-- Summing the trivial-modulus partial zeta series over the class group gives `dedekindZeta K`. -/
private theorem sum_LSeries_rayClassCoeff_classGroup {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K),
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm c⁻¹))) s =
      dedekindZeta K s := by
  let _ : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
  rw [← sum_LSeries_rayClassCoeff_one hs]
  let e : ClassGroup (𝓞 K) ≃ RayClassGroup (Modulus.one K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans oneEquivClassGroup.symm.toEquiv
  exact Fintype.sum_equiv e _ _ fun _ ↦ rfl

/-! ### Completed partial zeta functions -/

/-- **The completed partial zeta function** of the ideal class of `I⁻¹` (Neukirch VII §5): the
canonical meromorphic continuation from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ(s, [I⁻¹])`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s

/-- Defining equation of `TauCeti.LFunctions.completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 (fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s) := (rfl)

/-- The completed partial zeta function is in meromorphic normal form on the whole plane. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The completed partial zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- The completed partial zeta function depends only on the ideal class of `I`. -/
theorem completedPartialZeta_eq_of_classGroup_mk_eq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  rw [completedPartialZeta_def, completedPartialZeta_def, h]

section MellinBridge

private theorem meromorphic_mellinKernelFEPair_Λ_half {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (fun s : ℂ ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) := by
  intro s
  have h := ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (s / 2)).comp_analyticAt
    (g := fun z : ℂ ↦ z / 2) (by fun_prop)
  exact h

private theorem analyticAt_mellinKernelFEPair_Λ_half {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have hs0 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hs1 : s / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    simp only [mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    intro h
    exact h1 (by linear_combination 2 * h)
  have hΛ : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
    (mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff (s / 2) |>.mpr
      ⟨Or.inl hs0, Or.inl hs1⟩
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s := by fun_prop
  exact AnalyticAt.comp (f := fun z : ℂ ↦ z / 2) hΛ hdiv

private theorem eqOn_mellinKernelFEPair_Λ_half {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    EqOn (fun s : ℂ ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2))
      (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s)
      {s | 1 < s.re} := by
  intro s hs
  dsimp only
  rw [mellinKernelFEPair_Λ_idealLattice_eq hD I hs,
    LSeries_rayClassCoeff_one_eq_tsum_fractional I hs]

end MellinBridge

/-- **Identification with the Mellin pair, as germs.** At every complex number `s` (including the
poles `0` and `1`) and for every unit fundamental domain `D`, `completedPartialZeta I` has the same
punctured germ as `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_mellinKernelFEPair_Λ_half hD I)
    (fun z hz ↦ analyticAt_mellinKernelFEPair_Λ_half hD I
      (by rintro rfl; norm_num at hz) (by rintro rfl; norm_num at hz))
    (eqOn_mellinKernelFEPair_Λ_half hD I) s

/-- **Identification with the Mellin pair away from `0` and `1`.** For every unit fundamental
domain `D` and every `s ∉ {0, 1}`, `completedPartialZeta I s = (mellinKernelFEPair hD
(idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_apply (meromorphic_mellinKernelFEPair_Λ_half hD I)
    (fun z hz ↦ analyticAt_mellinKernelFEPair_Λ_half hD I
      (by rintro rfl; norm_num at hz) (by rintro rfl; norm_num at hz))
    (eqOn_mellinKernelFEPair_Λ_half hD I)
    (analyticAt_mellinKernelFEPair_Λ_half hD I h0 h1)

/-- On `Re s > 1`, `completedPartialZeta I` agrees with the completed Dirichlet series of the ideal
class of `I⁻¹`. -/
theorem completedPartialZeta_eq_partialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ
    (isUnitFundamentalDomain_unitFundamentalDomain (K := K)) I h0 h1]
  exact eqOn_mellinKernelFEPair_Λ_half
    (isUnitFundamentalDomain_unitFundamentalDomain (K := K)) I hs

/-- On `Re s > 1`, `completedPartialZeta I` equals the completed sum over nonzero integral ideals
`𝔟` with `𝔟 I` principal. -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_partialZeta I hs, LSeries_rayClassCoeff_one_eq_tsum_fractional I hs]

/-- The completed partial zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have ha := analyticAt_mellinKernelFEPair_Λ_half hD I h0 h1
  have hev := completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I s
  refine (meromorphicNFOn_completedPartialZeta I
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
  rw [meromorphicOrderAt_congr hev]
  exact ha.meromorphicOrderAt_nonneg

/-- Division by `2` maps the punctured neighborhood of `a` into that of `a / 2`. -/
private theorem tendsto_div_two_nhdsNE (a : ℂ) :
    Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] a) (𝓝[≠] (a / 2)) := by
  have hcont : ContinuousAt (fun s : ℂ ↦ s / 2) a := by fun_prop
  refine hcont.continuousWithinAt.tendsto_nhdsWithin fun s hs ↦ ?_
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
  exact fun h ↦ hs (by linear_combination 2 * h)

/-- The completed partial zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0)]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 0)
    (by fun_prop) (by simp)
  rw [zero_div] at hcomp
  change meromorphicOrderAt
    ((mellinKernelFEPair hD (idealLattice K I)).Λ ∘ fun z : ℂ ↦ z / 2) 0 = _
  rw [hcomp]
  exact (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_zero
    (by simp [mellinConstant_ne_zero])

/-- The completed partial zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1)]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 1)
    (by fun_prop) (by simp)
  change meromorphicOrderAt
    ((mellinKernelFEPair hD (idealLattice K I)).Λ ∘ fun z : ℂ ↦ z / 2) 1 = _
  rw [hcomp]
  simpa using (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_k
    (by simp [mellinConstant_ne_zero])

/-- **Residue of the completed partial zeta function at `s = 0`**:
`s * completedPartialZeta I s → -(2 * mellinConstant K)` as `s → 0`, `s ≠ 0`. -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * (mellinConstant K : ℂ)))) := by
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa using tendsto_div_two_nhdsNE 0
  have hres :=
    ((mellinKernelFEPair hD (idealLattice K I)).Λ_residue_zero.comp hdiv).const_mul (2 : ℂ)
  simp only [mellinKernelFEPair_f₀, smul_eq_mul, Function.comp_def, mul_neg] at hres
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0] with s hs
  rw [hs]
  ring

/-- **Residue of the completed partial zeta function at `s = 1`**:
`(s - 1) * completedPartialZeta I s → 2 * mellinConstant K` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1)
      (𝓝[≠] ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ)) := by
    simpa [mellinKernelFEPair_k] using tendsto_div_two_nhdsNE 1
  have hres :=
    ((mellinKernelFEPair hD (idealLattice K I)).Λ_residue_k.comp hdiv).const_mul (2 : ℂ)
  simp only [mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.one_cpow, mul_one, one_mul, smul_eq_mul, Function.comp_def] at hres
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with s hs
  rw [hs]
  ring

/-- **Functional equation of the completed partial zeta function** (Neukirch VII (5.9)):
`completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s` for all `s : ℂ`. -/
theorem completedPartialZeta_one_sub (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s := by
  by_cases h0 : s = 0
  · subst h0
    rw [sub_zero,
      eq_zero_of_meromorphicNFOn_of_order_eq_neg_one (meromorphicNFOn_completedPartialZeta I)
        (meromorphicOrderAt_completedPartialZeta_one I),
      eq_zero_of_meromorphicNFOn_of_order_eq_neg_one
        (meromorphicNFOn_completedPartialZeta (dualUnit I))
        (meromorphicOrderAt_completedPartialZeta_zero (dualUnit I))]
  by_cases h1 : s = 1
  · subst h1
    rw [sub_self,
      eq_zero_of_meromorphicNFOn_of_order_eq_neg_one (meromorphicNFOn_completedPartialZeta I)
        (meromorphicOrderAt_completedPartialZeta_zero I),
      eq_zero_of_meromorphicNFOn_of_order_eq_neg_one
        (meromorphicNFOn_completedPartialZeta (dualUnit I))
        (meromorphicOrderAt_completedPartialZeta_one (dualUnit I))]
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : 1 - s ≠ 1 := by intro h; exact h0 (by linear_combination -h)
  set D := unitFundamentalDomain K
  set hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  set hD' := hD.inv.mul traceShift_mem_normOneSurface
  have hcongr :
      (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
        (mellinKernelFEPair hD' (idealLattice K (dualUnit I))).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, Set.indicator_of_mem hu]
    exact mellinKernel_mixedDual_idealLattice (coe_dualUnit I) D⁻¹ u
  have hs0' : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hs1' : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h1s1 (by linear_combination 2 * h)
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1,
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) hs0' hs1', hcongr,
    completedPartialZeta_eq_mellinKernelFEPair_Λ hD' (dualUnit I) h0 h1]
  congr 1
  ring

/-- Reflection symmetry of the completed partial zeta function across the real axis. -/
theorem completedPartialZeta_conj (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (conj s) = conj (completedPartialZeta I s) := by
  have heq : conj ∘ completedPartialZeta I ∘ conj = completedPartialZeta I := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane
      (meromorphicNFOn_conj_conj (meromorphicNFOn_completedPartialZeta I))
      (meromorphicNFOn_completedPartialZeta I) fun z (hz : 1 < z.re) ↦ ?_
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply]
    rw [completedPartialZeta_eq_partialZeta I hzc, completedPartialZeta_eq_partialZeta I hz,
      map_mul, map_mul, map_mul, map_pow, map_pow, ← Complex.Gammaℝ_conj,
      ← Complex.Gammaℂ_conj, Complex.conj_conj]
    have hdiscr_nn : (0 : ℝ) ≤ (|discr K| : ℤ) := by positivity
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (z / 2) := by
      have h := TauCeti.ofReal_cpow_conj hdiscr_nn (z / 2)
      rw [Complex.ofReal_intCast, map_div₀, map_ofNat] at h
      rw [h, Complex.conj_conj]
    have hstar : star (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹)) =
        rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) := by
      funext 𝔟
      simp only [Pi.star_apply, rayClassCoeff_apply]
      split_ifs <;> simp
    have hL : conj (LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) (conj z)) =
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) z := by
      have h := LSeries_normCoeff_star (K := K)
        (rayClassCoeff (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹)) z
      rw [hstar] at h
      simpa [Complex.star_def] using congrArg conj h
    rw [hdiscr, hL]
  have h := congrFun heq (conj s)
  simpa only [Function.comp_apply, Complex.conj_conj] using h.symm

/-! ### The completed Dedekind zeta function -/

variable (K) in
/-- **The completed Dedekind zeta function** of a number field `K`: the canonical meromorphic
continuation from `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

variable (K) in
/-- Defining equation of `TauCeti.LFunctions.completedDedekindZeta`. -/
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 (fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s) := (rfl)

variable (K) in
/-- The completed Dedekind zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_completedDedekindZeta :
    MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

variable (K) in
/-- The completed Dedekind zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

/-- **Decomposition into completed partial zeta functions, as germs.** For any system of ideal-class
representatives `rep`, `completedDedekindZeta K` has the punctured germ of
`∑ c, completedPartialZeta (rep c)` at every point of `ℂ`. -/
private theorem completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s]
      fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z := by
  have hm : Meromorphic fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z := by
    intro z
    exact MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) z
  have ha : AnalyticOnNhd ℂ
      (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z) {z | 1 < z.re} := by
    intro z hz
    have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
    exact Finset.analyticAt_fun_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1
  have heqOn : EqOn (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z)
      (fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
        Gammaℂ z ^ nrComplexPlaces K * dedekindZeta K z) {z | 1 < z.re} := by
    intro z hz
    simp_rw [completedPartialZeta_eq_partialZeta _ hz, hrep, ← Finset.mul_sum]
    rw [sum_LSeries_rayClassCoeff_classGroup hz]
  rw [completedDedekindZeta_def]
  exact meromorphicContinuation_eventuallyEq hm ha heqOn s

/-- Choosing a representative in every ideal class. -/
private def classGroupRep (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (ClassGroup.mk0_surjective c).choose

private theorem classGroup_mk_classGroupRep (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (classGroupRep K c) = c := by
  dsimp only [classGroupRep]
  rw [ClassGroup.mk_mk0]
  exact (ClassGroup.mk0_surjective c).choose_spec

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  have hev := completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep s
  have ha : AnalyticAt ℂ (fun z ↦ ∑ c : ClassGroup (𝓞 K),
      completedPartialZeta (classGroupRep K c) z) s :=
    Finset.analyticAt_fun_sum _ fun c _ ↦
      analyticAt_completedPartialZeta (classGroupRep K c) h0 h1
  refine (meromorphicNFOn_completedDedekindZeta K
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
  rw [meromorphicOrderAt_congr hev]
  exact ha.meromorphicOrderAt_nonneg

variable (K) in
/-- **Residue of the completed Dedekind zeta function at `s = 0`**:
`s * completedDedekindZeta K s → -(classNumber K * (2 * mellinConstant K))`
as `s → 0`, `s ≠ 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))))) := by
  have hsum : Tendsto
      (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K), s * completedPartialZeta (classGroupRep K c) s)
      (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum _ fun c _ ↦ tendsto_mul_completedPartialZeta_zero (classGroupRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ))) =
      -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) := by
    simp [NumberField.classNumber]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep 0] with s hs
  rw [hs, Finset.mul_sum]

variable (K) in
/-- **Residue of the completed Dedekind zeta function at `s = 1`**:
`(s - 1) * completedDedekindZeta K s → classNumber K * (2 * mellinConstant K)` as `s → 1`,
`s ≠ 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)))) := by
  have hsum : Tendsto
      (fun s : ℂ ↦
        ∑ c : ClassGroup (𝓞 K), (s - 1) * completedPartialZeta (classGroupRep K c) s)
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum _ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta (classGroupRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ))) =
      (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) := by
    simp [NumberField.classNumber]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep 1] with s hs
  rw [hs, Finset.mul_sum]

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  have hL : -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) ≠ 0 := by
    simp [classNumber_ne_zero, mellinConstant_ne_zero]
  refine (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hL ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  have hL : (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) ≠ 0 := by
    simp [classNumber_ne_zero, mellinConstant_ne_zero]
  exact (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hL (by simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K)

/-- **Decomposition into completed partial zeta functions.** For any system of ideal-class
representatives `rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ` with
`ClassGroup.mk K (rep c) = c`, the completed Dedekind zeta function is the sum of the completed
partial zeta functions at every `s : ℂ`. -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s := by
  by_cases h0 : s = 0
  · subst h0
    rw [eq_zero_of_meromorphicNFOn_of_order_eq_neg_one (meromorphicNFOn_completedDedekindZeta K)
        (meromorphicOrderAt_completedDedekindZeta_zero K), Finset.sum_eq_zero]
    intro c _
    exact eq_zero_of_meromorphicNFOn_of_order_eq_neg_one
      (meromorphicNFOn_completedPartialZeta (rep c))
      (meromorphicOrderAt_completedPartialZeta_zero (rep c))
  by_cases h1 : s = 1
  · subst h1
    rw [eq_zero_of_meromorphicNFOn_of_order_eq_neg_one (meromorphicNFOn_completedDedekindZeta K)
        (meromorphicOrderAt_completedDedekindZeta_one K), Finset.sum_eq_zero]
    intro c _
    exact eq_zero_of_meromorphicNFOn_of_order_eq_neg_one
      (meromorphicNFOn_completedPartialZeta (rep c))
      (meromorphicOrderAt_completedPartialZeta_one (rep c))
  have hev := completedDedekindZeta_eventuallyEq_sum_completedPartialZeta rep hrep s
  have haL := (analyticAt_completedDedekindZeta (K := K) h0 h1).continuousAt
  have haR :
      ContinuousAt (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z) s :=
    (Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
      analyticAt_completedPartialZeta (rep c) h0 h1).continuousAt
  exact (haL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE haR).mp hev |>.eq_of_nhds

/-- On `Re s > 1`, `completedDedekindZeta K` equals
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep s]
  simp_rw [completedPartialZeta_eq_partialZeta _ hs, classGroup_mk_classGroupRep,
    ← Finset.mul_sum]
  rw [sum_LSeries_rayClassCoeff_classGroup hs]

variable (K) in
/-- **Functional equation of the completed Dedekind zeta function** (Neukirch VII (5.10)):
`completedDedekindZeta K (1 - s) = completedDedekindZeta K s` for all `s : ℂ`. -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep (1 - s),
    completedDedekindZeta_eq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep s]
  simp_rw [completedPartialZeta_one_sub]
  let δ : ClassGroup (𝓞 K) := ClassGroup.mk K (dualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft δ)
  refine Fintype.sum_equiv e _ _ fun c ↦ ?_
  have hmk : ClassGroup.mk K (dualUnit (classGroupRep K c)) =
      ClassGroup.mk K (classGroupRep K (e c)) := by
    rw [dualUnit_eq_mul_inv, map_mul, map_inv, classGroup_mk_classGroupRep,
      classGroup_mk_classGroupRep]
    rfl
  exact congrFun (completedPartialZeta_eq_of_classGroup_mk_eq hmk) s

variable (K) in
/-- Reflection symmetry of the completed Dedekind zeta function across the real axis. -/
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep (conj s),
    completedDedekindZeta_eq_sum_completedPartialZeta
    (classGroupRep K) classGroup_mk_classGroupRep s, map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_conj (classGroupRep K c) s

variable (K) in
/-- The residue of `completedDedekindZeta K` at `s = 1` matches the completed form of
`dedekindZeta_residue K`:
`|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ ρ_K = classNumber K * (2 * mellinConstant K)`. -/
theorem completedDedekindZeta_residue_eq :
    ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ) =
      (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) := by
  have hdiscr_pos : (0 : ℝ) < (|discr K| : ℤ) :=
    Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero K))
  have hsqrt :
      ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt |(discr K : ℝ)| : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (abs_nonneg _),
      ← Int.cast_abs (R := ℝ) (a := discr K), Complex.ofReal_intCast, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
  have hGℂ1 : Gammaℂ 1 = ((Real.pi : ℂ))⁻¹ := by simp [Gammaℂ_one]
  have h1le : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have h2pow : (2 : ℝ) * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) =
      2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K := by
    rw [← pow_succ', Nat.sub_add_cancel h1le, pow_add]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hsqrt_ne : Real.sqrt |(discr K : ℝ)| ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hdiscr_pos)).ne'
  rw [hsqrt, Gammaℝ_one, one_pow, mul_one, hGℂ1, mellinConstant_def, dedekindZeta_residue_def]
  have hreal :
      Real.sqrt |(discr K : ℝ)| * Real.pi⁻¹ ^ nrComplexPlaces K *
          ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K * Real.sqrt |(discr K : ℝ)|)) =
        (classNumber K : ℝ) *
          (2 * (2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K)) := by
    have hpipow : Real.pi⁻¹ ^ nrComplexPlaces K * Real.pi ^ nrComplexPlaces K = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hpi, one_pow]
    rw [mul_pow]
    calc
      Real.sqrt |(discr K : ℝ)| * Real.pi⁻¹ ^ nrComplexPlaces K *
          (2 ^ nrRealPlaces K * (2 ^ nrComplexPlaces K * Real.pi ^ nrComplexPlaces K) *
            regulator K * classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|))
          = (Real.pi⁻¹ ^ nrComplexPlaces K * Real.pi ^ nrComplexPlaces K) *
            (Real.sqrt |(discr K : ℝ)| / Real.sqrt |(discr K : ℝ)|) *
            (classNumber K * (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K /
              torsionOrder K)) := by ring
      _ = classNumber K *
          (2 * (2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K)) := by
        rw [hpipow, div_self hsqrt_ne, one_mul, one_mul, ← h2pow]
        ring
  exact_mod_cast hreal

/-! ### Continuation, residue, and leading term at `0` of `dedekindZetaC` -/

private theorem analyticAt_discr_inv_cpow (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) s := by
  have hmem : ((|discr K| : ℤ) : ℂ) ∈ slitPlane :=
    Or.inl (by norm_cast; exact abs_pos.mpr (discr_ne_zero K))
  exact analyticAt_const.cpow (by fun_prop) hmem

private theorem analyticAt_invGamma_prod (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) s :=
  ((analyticAt_discr_inv_cpow K s).mul
    ((differentiable_Gammaℝ_inv.analyticAt s).pow _)).mul
    ((differentiable_Gammaℂ_inv.analyticAt s).pow _)

/-- On `Re z > 0`, multiplying by the inverse discriminant and Gamma factors cancels the
completion factor `|d_K|^(z/2) Γ_ℝ(z)^r₁ Γ_ℂ(z)^r₂`. -/
private theorem invGamma_mul_gamma_cancel (K : Type*) [Field K] [NumberField K]
    {z : ℂ} (hz : 0 < z.re) (w : ℂ) :
    ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
          Gammaℂ z ^ nrComplexPlaces K * w) = w := by
  have hdiscr_ne : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (discr_ne_zero K)).ne'
  have hGℝ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz
  have hGℂ : Gammaℂ z ≠ 0 := Gammaℂ_ne_zero_of_re_pos hz
  have hd : ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * ((|discr K| : ℤ) : ℂ) ^ (z / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hdiscr_ne, neg_div, neg_add_cancel, Complex.cpow_zero]
  have h1 : (Gammaℝ z)⁻¹ ^ nrRealPlaces K * Gammaℝ z ^ nrRealPlaces K = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hGℝ, one_pow]
  have h2 : (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * Gammaℂ z ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hGℂ, one_pow]
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
          Gammaℂ z ^ nrComplexPlaces K * w)
        = (((|discr K| : ℤ) : ℂ) ^ (-z / 2) * ((|discr K| : ℤ) : ℂ) ^ (z / 2)) *
          ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * Gammaℝ z ^ nrRealPlaces K) *
          ((Gammaℂ z)⁻¹ ^ nrComplexPlaces K * Gammaℂ z ^ nrComplexPlaces K) * w := by ring
    _ = w := by rw [hd, h1, h2]; ring

variable (K) in
/-- **Relation between `dedekindZetaC` and `completedDedekindZeta`, as germs.** At every complex
number `s` (including `0` and `1`), `dedekindZetaC K` has the punctured germ of
`|d_K|^(-z/2) Γ_ℝ(z)^(-r₁) Γ_ℂ(z)^(-r₂) completedDedekindZeta K z`. -/
theorem dedekindZetaC_eventuallyEq_completedDedekindZeta_mul (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z := by
  set F : ℂ → ℂ := fun z ↦
    ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
      (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z
  have hm : Meromorphic F := fun z ↦
    (analyticAt_invGamma_prod K z).meromorphicAt.mul (meromorphic_completedDedekindZeta K z)
  have ha : AnalyticOnNhd ℂ F {z | 1 < z.re} := fun z hz ↦
    (analyticAt_invGamma_prod K z).mul
      (analyticAt_completedDedekindZeta (by rintro rfl; norm_num at hz)
        (by rintro rfl; norm_num at hz))
  have heqOn : EqOn F (dedekindZeta K) {z | 1 < z.re} := by
    intro z hz
    change 1 < z.re at hz
    dsimp only [F]
    rw [completedDedekindZeta_eq hz]
    exact invGamma_mul_gamma_cancel K (by linarith) _
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq hm ha heqOn s

/-- Away from `0` and `1` (including at all negative integers), `dedekindZetaC K s` equals
`|d_K|^(-s/2) Γ_ℝ(s)^(-r₁) Γ_ℂ(s)^(-r₂) completedDedekindZeta K s`. -/
theorem dedekindZetaC_eq_completedDedekindZeta_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    dedekindZetaC K s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s := by
  have hev := dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K s
  have haR : AnalyticAt ℂ (fun z ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z) s :=
    (analyticAt_invGamma_prod K s).mul (analyticAt_completedDedekindZeta h0 h1)
  have haL : AnalyticAt ℂ (dedekindZetaC K) s :=
    (meromorphicNFOn_dedekindZetaC K (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp <| by
      rw [meromorphicOrderAt_congr hev]
      exact haR.meromorphicOrderAt_nonneg
  exact (haL.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE haR.continuousAt).mp hev
    |>.eq_of_nhds

/-- On `Re s > 1`, `dedekindZetaC K` agrees with Mathlib's `NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [dedekindZetaC_eq_completedDedekindZeta_mul h0 h1, completedDedekindZeta_eq hs]
  exact invGamma_mul_gamma_cancel K (by linarith) _

variable (K) in
/-- The continued Dedekind zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_dedekindZetaC : Meromorphic (dedekindZetaC K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_dedekindZetaC K).meromorphicOn

variable (K) in
/-- **Order of vanishing of `dedekindZetaC K` at `s = 0`** (Neukirch VII (5.11)):
`meromorphicOrderAt (dedekindZetaC K) 0 = Units.rank K = r₁ + r₂ - 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (Units.rank K : ℤ) := by
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K 0)]
  have hdiscr_ord :
      meromorphicOrderAt (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 = 0 := by
    have ha := analyticAt_discr_inv_cpow K 0
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr (by simp)]
    rfl
  have hGℝ_ord : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 =
      (nrRealPlaces K : ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ ↦ (Gammaℝ z)⁻¹) ^ nrRealPlaces K) 0 = _
    rw [meromorphicOrderAt_pow (differentiable_Gammaℝ_inv.analyticAt 0).meromorphicAt,
      ← Pi.inv_def, meromorphicOrderAt_inv,
      (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    simp
  have hGℂ_ord : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 =
      (nrComplexPlaces K : ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ ↦ (Gammaℂ z)⁻¹) ^ nrComplexPlaces K) 0 = _
    rw [meromorphicOrderAt_pow (differentiable_Gammaℂ_inv.analyticAt 0).meromorphicAt,
      ← Pi.inv_def, meromorphicOrderAt_inv,
      (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    simp
  have h1le : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hrank : (Units.rank K : ℤ) = (nrRealPlaces K : ℤ) + (nrComplexPlaces K : ℤ) - 1 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hGℝ_an : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 :=
    (differentiable_Gammaℝ_inv.analyticAt 0).pow _
  have hGℂ_an : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 :=
    (differentiable_Gammaℂ_inv.analyticAt 0).pow _
  have hprod1 :
      meromorphicOrderAt (fun z : ℂ ↦
          ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 =
        (nrRealPlaces K : ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) *
      (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K)) 0 = _
    rw [meromorphicOrderAt_mul (analyticAt_discr_inv_cpow K 0).meromorphicAt hGℝ_an.meromorphicAt,
      hdiscr_ord, hGℝ_ord, zero_add]
  have hprod1_an : AnalyticAt ℂ (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 :=
    (analyticAt_discr_inv_cpow K 0).mul hGℝ_an
  have hprod2 :
      meromorphicOrderAt (fun z : ℂ ↦
          ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
            (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 =
        (nrRealPlaces K : ℤ) + (nrComplexPlaces K : ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ ↦
        ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K) *
      (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K)) 0 = _
    rw [meromorphicOrderAt_mul hprod1_an.meromorphicAt hGℂ_an.meromorphicAt,
      hprod1, hGℂ_ord]
  change meromorphicOrderAt ((fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) * completedDedekindZeta K) 0 = _
  rw [meromorphicOrderAt_mul (analyticAt_invGamma_prod K 0).meromorphicAt
      (meromorphic_completedDedekindZeta K 0),
    hprod2, meromorphicOrderAt_completedDedekindZeta_zero K]
  norm_cast
  omega

variable (K) in
/-- **Simple pole of `dedekindZetaC K` at `s = 1`**:
`meromorphicOrderAt (dedekindZetaC K) 1 = -1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K 1)]
  have hGℝ1 : Gammaℝ 1 ≠ 0 := by simp
  have hGℂ1 : Gammaℂ 1 ≠ 0 := by simp [Gammaℂ_one, Real.pi_ne_zero]
  have hdiscr_ne : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (discr_ne_zero K)).ne'
  have hdiscr1 : ((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hdiscr_ne h.1
  have hprod_ne :
      ((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * (Gammaℝ 1)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdiscr1 (pow_ne_zero _ (inv_ne_zero hGℝ1)))
      (pow_ne_zero _ (inv_ne_zero hGℂ1))
  have hprod_ord : meromorphicOrderAt (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 1 = 0 := by
    have ha := analyticAt_invGamma_prod K 1
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hprod_ne]
    rfl
  change meromorphicOrderAt ((fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) * completedDedekindZeta K) 1 = _
  rw [meromorphicOrderAt_mul (analyticAt_invGamma_prod K 1).meromorphicAt
      (meromorphic_completedDedekindZeta K 1),
    hprod_ord, meromorphicOrderAt_completedDedekindZeta_one K, zero_add]

/-- **Holomorphy of `dedekindZetaC K` away from `s = 1`** (including at `s = 0`). -/
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaC K) s := by
  rcases eq_or_ne s 0 with rfl | h0
  · refine (meromorphicNFOn_dedekindZetaC K
        (mem_univ (0 : ℂ))).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_dedekindZetaC_zero K]
    exact WithTop.coe_nonneg.mpr (Nat.cast_nonneg _)
  · refine (meromorphicNFOn_dedekindZetaC K
        (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K s)]
    exact ((analyticAt_invGamma_prod K s).mul
      (analyticAt_completedDedekindZeta h0 hs)).meromorphicOrderAt_nonneg

variable (K) in
/-- **Analytic class number formula for `dedekindZetaC K`**:
`(s - 1) * dedekindZetaC K s → dedekindZeta_residue K` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have h1 : Tendsto (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 1)
      (𝓝 (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * (Gammaℝ 1)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K)) :=
    (analyticAt_invGamma_prod K 1).continuousAt.mono_left nhdsWithin_le_nhds
  have hmul := h1.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hlim :
      (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * (Gammaℝ 1)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
        ((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) =
        (dedekindZeta_residue K : ℂ) := by
    rw [← completedDedekindZeta_residue_eq K]
    exact invGamma_mul_gamma_cancel K (by simp) _
  rw [hlim] at hmul
  refine hmul.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K 1] with z hz
  rw [hz]
  ring

variable (K) in
/-- **Leading term of `dedekindZetaC K` at `s = 0`** (Neukirch VII (5.11)):
`dedekindZetaC K s / s ^ Units.rank K → -(classNumber K * regulator K / torsionOrder K)`
as `s → 0`, `s ≠ 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ)) := by
  have hdiscr :
      Tendsto (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (analyticAt_discr_inv_cpow K 0).continuousAt.mono_left nhdsWithin_le_nhds
  have hGℝ : Tendsto (fun z : ℂ ↦ (z * Gammaℝ z)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hGℂ : Tendsto (fun z : ℂ ↦ (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod :=
    ((tendsto_mul_completedDedekindZeta_zero K).mul hdiscr).mul (hGℝ.mul hGℂ)
  have h1le : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hrank : Units.rank K + 1 = nrRealPlaces K + nrComplexPlaces K := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hlim :
      -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) * 1 *
          ((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K) =
        (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
    have h2cancel :
        (2 : ℝ) * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) *
          ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel h1le, ← pow_add, ← mul_pow,
        mul_inv_cancel₀ two_ne_zero, one_pow]
    have hreal :
        -((classNumber K : ℝ) * (2 * mellinConstant K)) * 1 *
            ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) =
          -((classNumber K : ℝ) * regulator K / torsionOrder K) := by
      rw [mellinConstant_def]
      calc
        -((classNumber K : ℝ) *
            (2 * (2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K))) *
            1 * ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K)
            = -((2 * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) *
                ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K)) *
                ((classNumber K : ℝ) * regulator K / torsionOrder K)) := by ring
        _ = -((classNumber K : ℝ) * regulator K / torsionOrder K) := by rw [h2cancel, one_mul]
    simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_completedDedekindZeta_mul K 0, self_mem_nhdsWithin]
    with z hz (hz0 : z ≠ 0)
  rw [hz]
  have hmul : (z * Gammaℝ z)⁻¹ ^ nrRealPlaces K * (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K =
      (z⁻¹ ^ (Units.rank K + 1)) *
        ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) := by
    simp_rw [mul_inv, mul_pow]
    rw [hrank, pow_add]
    ring
  rw [hmul, pow_succ', inv_pow]
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  calc
    z * completedDedekindZeta K z * ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (z⁻¹ * (z ^ Units.rank K)⁻¹ *
          ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K))
        = (z * z⁻¹) * (((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
            (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
            (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z *
            (z ^ Units.rank K)⁻¹) := by ring
    _ = _ := by rw [hzinv, one_mul, ← div_eq_mul_inv]

end TauCeti.LFunctions
