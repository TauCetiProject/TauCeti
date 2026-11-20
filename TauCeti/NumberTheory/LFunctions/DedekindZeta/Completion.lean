/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
import TauCeti.NumberTheory.LFunctions.Theta.UnitFundamentalDomain
import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# The completed Dedekind zeta function and analytic continuation of `dedekindZetaC`

For a number field `K`, this file constructs the completed Dedekind zeta function
`TauCeti.LFunctions.completedDedekindZeta` from the completed partial zeta functions
`TauCeti.LFunctions.completedPartialZeta`, establishes Hecke's functional equation, reflection
symmetry, and simple-pole residues at `s = 0` and `s = 1`, and deduces the full meromorphic
continuation, residue at `s = 1`, and leading-term expansion at `s = 0` of
`TauCeti.LFunctions.dedekindZetaC K` (Neukirch, Chapter VII, §5, (5.5)–(5.11)).

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the canonical meromorphic continuation from
  `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`.

## Main results

* `TauCeti.LFunctions.completedPartialZeta_conj`: reflection symmetry of `completedPartialZeta`.
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

/-! ### Auxiliary lemmas on class-group sums and reflection symmetry -/

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

/-- Reflection symmetry of the completed partial zeta function across the real axis. -/
theorem completedPartialZeta_conj (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (conj s) = conj (completedPartialZeta I s) := by
  have heq : conj ∘ completedPartialZeta I ∘ conj = completedPartialZeta I := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane
      (meromorphicNFOn_conj_conj_iff.mpr (meromorphicNFOn_completedPartialZeta I))
      (meromorphicNFOn_completedPartialZeta I) fun z (hz : 1 < z.re) ↦ ?_
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply]
    rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one I hzc,
      completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one I hz,
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
    simp_rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hz, hrep, ← Finset.mul_sum]
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
      (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), -(2 * mellinConstant K : ℂ))) :=
    tendsto_finsetSum _ fun c _ ↦ tendsto_mul_completedPartialZeta_zero (classGroupRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), -(2 * mellinConstant K : ℂ)) =
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
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * mellinConstant K : ℂ))) :=
    tendsto_finsetSum _ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta (classGroupRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), (2 * mellinConstant K : ℂ)) =
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

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedDedekindZeta_zero : completedDedekindZeta K 0 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedDedekindZeta K (mem_univ 0))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp
    (by simp [meromorphicOrderAt_completedDedekindZeta_zero])

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedDedekindZeta_one : completedDedekindZeta K 1 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedDedekindZeta K (mem_univ 1))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp
    (by simp [meromorphicOrderAt_completedDedekindZeta_one])

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
    simp
  by_cases h1 : s = 1
  · subst h1
    simp
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
  simp_rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hs, classGroup_mk_classGroupRep,
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
  let δ : ClassGroup (𝓞 K) :=
    ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft δ)
  refine Fintype.sum_equiv e _ _ fun c ↦ ?_
  have hmk : ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (classGroupRep K c)) =
      ClassGroup.mk K (classGroupRep K (e c)) := by
    rw [FractionalIdeal.dualEquiv_eq_mul_inv, map_mul, map_inv, classGroup_mk_classGroupRep,
      classGroup_mk_classGroupRep]
    rfl
  exact congrFun (completedPartialZeta_congr_class hmk) s

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
