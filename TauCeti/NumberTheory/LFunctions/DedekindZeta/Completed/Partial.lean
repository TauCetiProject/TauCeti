/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Unfolding
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Completed partial zeta functions of ideal classes

For an invertible fractional ideal `I` of a number field `K`, the completed partial zeta function
`completedPartialZeta I` is the canonical meromorphic continuation from `Re s > 1` of

`Z(I, s) = |d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_{𝔟} N(𝔟)^(-s)`,

where `𝔟` runs over the nonzero integral ideals of `𝓞 K` such that `𝔟 * I` is principal, i.e.,
the integral ideals in the inverse ideal class `(ClassGroup.mk K I)⁻¹`.

By Hecke's unfolding (`mellinKernelFEPair_Λ_idealLattice_eq`), for any fundamental domain `D` for
the unit action modulo torsion on the norm-one hypersurface, the completed function
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` agrees with `Z(I, s)` on `Re s > 1`.
This yields the meromorphic continuation of `completedPartialZeta I` to the entire complex plane,
analyticity away from `{0, 1}`, simple poles at `0` and `1` with residues `∓ 2 * mellinConstant K`
(`= ∓ 2^(r₁ + r₂) R / w`), complex conjugation symmetry, invariance under replacing `I` by an ideal
in the same ideal class, and Hecke's functional equation relating `I` to its trace dual
`dualUnit I = I^∨`:

`completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s` (`s ≠ 0, 1`).

## Main definitions

* `TauCeti.LFunctions.dualUnit`: the trace dual of an invertible fractional ideal as an element of
  `(FractionalIdeal (𝓞 K)⁰ K)ˣ`.
* `TauCeti.LFunctions.completedPartialZeta`: the canonical completed partial zeta function of the
  ideal class of `I⁻¹`.

## Main results

* `TauCeti.LFunctions.dualUnit_dualUnit`: `dualUnit` is an involution.
* `TauCeti.LFunctions.classGroup_mk_dualUnit`: action of `dualUnit` on the ideal class group.
* `TauCeti.LFunctions.exists_spanSingleton_iff_classGroup_mk0`: `𝔟 * I` is principal iff
  `ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹`.
* `TauCeti.LFunctions.completedPartialZeta_eq_toMeromorphicNFOn`: identification with the
  normal-form Mellin pair `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: explicit formulas on `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_completedPartialZeta`: analyticity away from `0` and `1`.
* `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`: simple poles at `0` and `1`.
* `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`: residues `∓ 2 * mellinConstant K`.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub_eventuallyEq`: Hecke's functional equation
  relating `I` and `dualUnit I`.
* `TauCeti.LFunctions.completedPartialZeta_conj`: Schwarz reflection symmetry on the whole plane.
* `TauCeti.LFunctions.completedPartialZeta_eq_of_classGroup_eq`: depends only on the ideal class.
* `TauCeti.LFunctions.completedPartialZeta_mk0_eq_LSeries_rayClassCoeff`: link to
  `LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c))`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5)–(5.9).
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The trace dual as a unit fractional ideal -/

/-- **The trace dual of an invertible fractional ideal**, packaged as a unit of
`FractionalIdeal (𝓞 K)⁰ K`. -/
def dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

/-- As a fractional ideal, `dualUnit I` is the trace dual `FractionalIdeal.dual ℤ ℚ I`. -/
@[simp]
theorem coe_dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (dualUnit I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  simp [dualUnit]

/-- Taking the trace dual twice returns the original ideal. -/
@[simp]
theorem dualUnit_dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualUnit (dualUnit I) = I := by
  ext1
  exact FractionalIdeal.dual_dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)

/-- The trace dual factors as `dualUnit 1 * I⁻¹`. -/
theorem dualUnit_eq_dualUnit_one_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualUnit I = dualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * I⁻¹ := by
  ext1
  simpa using FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)

/-- In the ideal class group, `dualUnit` sends `[I]` to `[dualUnit 1] * [I]⁻¹`. -/
theorem classGroup_mk_dualUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (dualUnit I) =
      ClassGroup.mk K (dualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) * (ClassGroup.mk K I)⁻¹ := by
  rw [dualUnit_eq_dualUnit_one_mul_inv, map_mul, map_inv]

/-! ### Principal multiples and the ideal class group -/

/-- A nonzero integral ideal `𝔟` satisfies `𝔟 * I = (x)` for some `x ∈ Kˣ` if and only if its ideal
class is the inverse of the class of `I`. -/
theorem exists_spanSingleton_iff_classGroup_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : (Ideal (𝓞 K))⁰) :
    (∃ x : Kˣ, ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) ↔
      ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹ := by
  have hcls : ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹ ↔
      ClassGroup.mk K (FractionalIdeal.mk0 K 𝔟 * I) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, mul_eq_one_iff_eq_inv]
  rw [hcls, ClassGroup.mk_eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨(x : K), ?_⟩⟩
    have hval : ((FractionalIdeal.mk0 K 𝔟 * I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
      simpa using hx
    simp [hval, FractionalIdeal.coeToSubmodule_spanSingleton]
  · intro hP
    obtain ⟨a, ha⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hP
    have hval : ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      apply Subtype.ext
      simpa [FractionalIdeal.coeToSubmodule_spanSingleton] using ha
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, FractionalIdeal.spanSingleton_eq_zero_iff.mpr rfl] at hval
      exact (FractionalIdeal.mk0 K 𝔟 * I).ne_zero (by simpa using hval)
    exact ⟨Units.mk0 a ha0, hval⟩

/-- Scaling the constant term `mellinConstant K` by `2` clears the `- 1` in the exponent of `2`. -/
theorem two_mul_mellinConstant (K : Type*) [Field K] [NumberField K] :
    2 * mellinConstant K =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K / torsionOrder K := by
  have hpos : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hpow : (2 : ℝ) * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  rw [mellinConstant_def, ← mul_div_assoc, ← mul_assoc, hpow]

/-! ### Definition and Mellin identification of `completedPartialZeta` -/

/-- **The completed partial zeta function** of the class of `I⁻¹`: the canonical meromorphic
continuation from `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_𝔟 N(𝔟)^(-s)`, where `𝔟` ranges
over nonzero integral ideals with `𝔟 * I` principal (Neukirch VII, §5). -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- The defining equation of `completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := (rfl)

/-- `completedPartialZeta I` is in meromorphic normal form on the whole complex plane. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

open scoped Classical in
private theorem meromorphic_mellinKernelFEPair_Λ_half {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    Meromorphic (fun s : ℂ ↦ (mellinKernelFEPair hD L).Λ (s / 2)) := fun s ↦ by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s := by fun_prop
  exact ((mellinKernelFEPair hD L).meromorphic_Λ (s / 2)).comp_analyticAt
    (g := fun z : ℂ ↦ z / 2) hg

open scoped Classical in
private theorem analyticAt_mellinKernelFEPair_Λ_half {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ (mellinKernelFEPair hD L).Λ (z / 2)) s := by
  have hz0 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hz1 : s / 2 ≠ ((mellinKernelFEPair hD L).k : ℂ) := by
    simp only [mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    intro h
    exact h1 (by linear_combination 2 * h)
  have hΛ : AnalyticAt ℂ (mellinKernelFEPair hD L).Λ (s / 2) :=
    ((mellinKernelFEPair hD L).analyticAt_Λ_iff (s / 2)).mpr ⟨Or.inl hz0, Or.inl hz1⟩
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s := by fun_prop
  exact hΛ.comp (f := fun z : ℂ ↦ z / 2) hg

open scoped Classical in
/-- For any unit fundamental domain `D`, `completedPartialZeta I` is the meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  refine meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_mellinKernelFEPair_Λ_half hD (idealLattice K I))
    (fun s hs ↦ analyticAt_mellinKernelFEPair_Λ_half hD (idealLattice K I)
      (by rintro rfl; norm_num at hs) (by rintro rfl; norm_num at hs))
    (fun s hs ↦ mellinKernelFEPair_Λ_idealLattice_eq hD I hs)

open scoped Classical in
/-- At every point `s : ℂ` (poles included), `completedPartialZeta I` shares the punctured germ of
`z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact (meromorphic_mellinKernelFEPair_Λ_half hD (idealLattice K I)).meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

open scoped Classical in
/-- Away from `0` and `1`, `completedPartialZeta I` agrees pointwise with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` for any unit fundamental domain `D`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact toMeromorphicNFOn_apply_of_analyticAt
    (meromorphic_mellinKernelFEPair_Λ_half hD (idealLattice K I))
    (analyticAt_mellinKernelFEPair_Λ_half hD (idealLattice K I) h0 h1)

/-- `completedPartialZeta I` is analytic away from `0` and `1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have ha := analyticAt_mellinKernelFEPair_Λ_half hD (idealLattice K I) h0 h1
  have hopen : ∀ᶠ z in 𝓝 s, z ≠ 0 ∧ z ≠ 1 :=
    Filter.eventually_and.mpr ⟨eventually_ne_nhds h0, eventually_ne_nhds h1⟩
  refine ha.congr ?_
  filter_upwards [hopen] with z ⟨hz0, hz1⟩
  exact (completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hz0 hz1).symm

/-- On `Re s > 1`, `completedPartialZeta I` agrees with the completed partial zeta Dirichlet series
of the class of `I⁻¹`. -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h0 h1,
    mellinKernelFEPair_Λ_idealLattice_eq hD I hs]

/-- On `Re s > 1`, `completedPartialZeta I s` is the Mellin transform at `s / 2` of
`mellinKernel D (idealLattice K I) - mellinConstant K` for any unit fundamental domain `D`
(Neukirch VII, §5, (5.5)). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - (mellinConstant K : ℂ)) (s / 2) := by
  rw [completedPartialZeta_eq_tsum I hs]
  exact (hasMellin_mellinKernel_idealLattice hD I hs).2.symm

/-! ### Dependence only on the ideal class and bridge to ray classes -/

/-- `completedPartialZeta I` depends only on the ideal class of `I` in `ClassGroup (𝓞 K)`. -/
theorem completedPartialZeta_eq_of_classGroup_eq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  refine meromorphicContinuation_congr fun s _ ↦ ?_
  congr 1
  refine (Equiv.subtypeEquivRight fun 𝔟 ↦ ?_).tsum_eq
    (f := fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ↦
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
  rw [exists_spanSingleton_iff_classGroup_mk0, exists_spanSingleton_iff_classGroup_mk0, h]

/-- Link to the partial zeta series `LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c))` on
`Re s > 1`: for an integral ideal `J` in the class `c⁻¹`, `completedPartialZeta (mk0 K J)` is the
completed ray-class partial zeta series. -/
theorem completedPartialZeta_mk0_eq_LSeries_rayClassCoeff {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰)
    (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta (FractionalIdeal.mk0 K J) s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  rw [completedPartialZeta_eq_tsum _ hs, LSeries_rayClassCoeff_one_eq_tsum J hJ hs]
  congr 1
  refine (Equiv.subtypeEquivRight fun 𝔟 ↦ ?_).tsum_eq
    (f := fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
        Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))} ↦
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
  rw [exists_spanSingleton_iff_classGroup_mk0, ClassGroup.mk_mk0,
    ← mul_eq_one_iff_eq_inv, ← map_mul, ClassGroup.mk0_eq_one_iff]
  rfl

/-! ### Poles, residues, functional equation, and reflection symmetry -/

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : WithTop ℤ) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hev := completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0
  rw [meromorphicOrderAt_congr hev]
  have hcomp : meromorphicOrderAt
      ((mellinKernelFEPair hD (idealLattice K I)).Λ ∘ fun z : ℂ ↦ z / 2) 0 =
      meromorphicOrderAt (mellinKernelFEPair hD (idealLattice K I)).Λ 0 := by
    simpa using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 0)
      (analyticAt_id.div analyticAt_const two_ne_zero) (by simp)
  have hf0 : (mellinKernelFEPair hD (idealLattice K I)).f₀ ≠ 0 := by
    simp [mellinConstant_ne_zero]
  refine hcomp.trans ?_
  simpa using (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_zero hf0

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : WithTop ℤ) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hev := completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1
  rw [meromorphicOrderAt_congr hev]
  have hcomp : meromorphicOrderAt
      ((mellinKernelFEPair hD (idealLattice K I)).Λ ∘ fun z : ℂ ↦ z / 2) 1 =
      meromorphicOrderAt (mellinKernelFEPair hD (idealLattice K I)).Λ (1 / 2) := by
    simpa using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun z : ℂ ↦ z / 2) (x := 1)
      (analyticAt_id.div analyticAt_const two_ne_zero) (by simp)
  have hg0 : (mellinKernelFEPair hD (idealLattice K I)).g₀ ≠ 0 := by
    simp [mellinConstant_ne_zero]
  refine hcomp.trans ?_
  have hord := (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_k hg0
  simpa using hord

/-- The residue of `completedPartialZeta I` at `s = 0` is `-2 * mellinConstant K`
(`= -2^(r₁ + r₂) R / w`). -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * (mellinConstant K : ℂ)))) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hmap : Tendsto (fun z : ℂ ↦ z / 2) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun z : ℂ ↦ z / 2) 0 :=
        (continuous_id.div_const (2 : ℂ)).continuousAt
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact div_ne_zero hz two_ne_zero
  have hres0 := (mellinKernelFEPair hD (idealLattice K I)).Λ_residue_zero
  simp only [mellinKernelFEPair_f₀] at hres0
  have hres : Tendsto (fun z : ℂ ↦
        2 * ((z / 2) * (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)))
      (𝓝[≠] 0) (𝓝 (-(2 * (mellinConstant K : ℂ)))) := by
    simpa [mul_neg] using (hres0.comp hmap).const_mul (2 : ℂ)
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0] with z hz
  rw [hz]
  ring

/-- The residue of `completedPartialZeta I` at `s = 1` is `2 * mellinConstant K`
(`= 2^(r₁ + r₂) R / w`), Neukirch VII, §5, (5.9). -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hmap : Tendsto (fun z : ℂ ↦ z / 2) (𝓝[≠] (1 : ℂ)) (𝓝[≠] ((1 : ℂ) / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun z : ℂ ↦ z / 2) 1 :=
        (continuous_id.div_const (2 : ℂ)).continuousAt
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro h
      have h' : z / 2 = 1 / 2 := h
      exact Set.mem_compl_singleton_iff.mp hz (by linear_combination 2 * h')
  have hres0 := (mellinKernelFEPair hD (idealLattice K I)).Λ_residue_k
  simp only [mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    one_cpow, mul_one, one_smul] at hres0
  have hres : Tendsto (fun z : ℂ ↦
        2 * ((z / 2 - 1 / 2) * (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)))
      (𝓝[≠] 1) (𝓝 (2 * (mellinConstant K : ℂ))) := by
    simpa using (hres0.comp hmap).const_mul (2 : ℂ)
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with z hz
  rw [hz]
  ring

/-- **Hecke's functional equation for the completed partial zeta function**
(Neukirch VII, §5, (5.9)):
`completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s` away from `{0, 1}`. -/
theorem completedPartialZeta_one_sub (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I (1 - s) = completedPartialZeta (dualUnit I) s := by
  classical
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hs0' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have hs1' : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  have hz0 : (1 - s) / 2 ≠ 0 := div_ne_zero hs0' two_ne_zero
  have hz1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h0 (by linear_combination -2 * h)
  have hhalf : (1 : ℂ) / 2 - (1 - s) / 2 = s / 2 := by ring
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hs0' hs1',
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) hz0 hz1, hhalf,
    completedPartialZeta_eq_mellinKernelFEPair_Λ
      (hD.inv.mul traceShift_mem_normOneSurface) (dualUnit I) h0 h1]
  -- Identify the dual Euclidean pair with the shifted ideal lattice pair via `WeakFEPair.Λ_congr`.
  have hpair : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair (hD.inv.mul traceShift_mem_normOneSurface)
        (idealLattice K (dualUnit I))).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun t ht ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, indicator_of_mem ht]
    exact mellinKernel_mixedDual_idealLattice (coe_dualUnit I) _ t
  exact congrFun hpair (s / 2)

/-- Hecke's functional equation for `completedPartialZeta I` as an equality of punctured germs at
every point of the complex plane, the poles included. -/
theorem completedPartialZeta_one_sub_eventuallyEq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (fun z ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s] completedPartialZeta (dualUnit I) := by
  have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
    rcases eq_or_ne s a with rfl | h
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h)
  filter_upwards [hne 0, hne 1] with z hz0 hz1
  exact completedPartialZeta_one_sub I hz0 hz1

/-- **Schwarz reflection symmetry**:
`completedPartialZeta I (conj s) = conj (completedPartialZeta I s)` for every `s : ℂ` (including
at poles, where both sides vanish in meromorphic normal form). -/
theorem completedPartialZeta_conj (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (conj s) = conj (completedPartialZeta I s) := by
  have hnf : MeromorphicNFOn (conj ∘ completedPartialZeta I ∘ conj) univ := by
    simpa only [preimage_univ] using (meromorphicNFOn_completedPartialZeta I).conj_conj
  have heq : conj ∘ completedPartialZeta I ∘ conj = completedPartialZeta I := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1) hnf
      (meromorphicNFOn_completedPartialZeta I) fun z hz ↦ ?_
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply, completedPartialZeta_eq_tsum I hzc,
      completedPartialZeta_eq_tsum I hz]
    have hd_nn : (0 : ℝ) ≤ (|discr K| : ℤ) := by positivity
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (z / 2) := by
      have h1 : conj z / 2 = conj (z / 2) := by rw [map_div₀, map_ofNat]
      rw [h1, ← Complex.ofReal_intCast, TauCeti.ofReal_cpow_conj hd_nn, conj_conj]
    have htsum : conj (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-conj z)) =
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-z) := by
      rw [Complex.conj_tsum]
      refine tsum_congr fun 𝔟 ↦ ?_
      rw [← Complex.ofReal_natCast, ← map_neg (starRingEnd ℂ),
        TauCeti.ofReal_cpow_conj (Nat.cast_nonneg _), conj_conj]
    simp only [map_mul, map_pow, hdiscr, Gammaℝ_conj, Gammaℂ_conj, conj_conj, htsum]
  have hval := congrFun heq (conj s)
  simpa only [Function.comp_apply, conj_conj] using hval.symm

end TauCeti.LFunctions
