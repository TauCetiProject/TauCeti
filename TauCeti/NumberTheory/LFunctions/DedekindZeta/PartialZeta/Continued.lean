/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta

/-!
# The continued partial zeta functions

For a modulus `𝔪` of a number field `K` and a ray class `c` of `𝔪`, the partial zeta function
`ζ(s, c) = ∑_{𝔞 ∈ c} N(𝔞) ^ (-s)` is the Dirichlet series of the class indicator
`rayClassCoeff 𝔪 c`, which converges absolutely on `Re s > 1`.
`TauCeti.LFunctions.partialZeta 𝔪 c` is its canonical meromorphic continuation
(`TauCeti.meromorphicContinuation 1`): the function in meromorphic normal form on the whole plane
that agrees with the series on `Re s > 1`, and `0` if there is none.

At the trivial modulus the ray classes are the ideal classes, and Hecke's completed partial zeta
functions provide the continuation. For an invertible fractional ideal `I` whose inverse lies in
the class `c`,

`Z(I, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ(s, c)`  on `Re s > 1`

(`completedPartialZeta_eq_partialZeta`). The reciprocal of the archimedean factor is entire and
vanishes at `s = 0`, where it cancels the simple pole of `Z(I, ·)`. Hence
`partialZeta (Modulus.one K) c` is the series on `Re s > 1`, is analytic away from `s = 1`, and
has a simple pole at `s = 1` whose residue is the main term `rayClassIdealMainTerm (Modulus.one K)`
of the ideal counts of one class, which equals `ρ_K / h` with `ρ_K = dedekindZeta_residue K` and
`h` the class number (`ofReal_rayClassIdealMainTerm`). Every ideal class has the same residue, and
the partial zeta functions of the ideal classes sum to `dedekindZetaC K` on the whole plane.

For a modulus with a nontrivial finite part or with real places, the continuation of
`partialZeta 𝔪 c` to the plane rests on the continuation of the Hecke L-functions of the ray class
characters of `𝔪`, through the orthogonality relation; for such a modulus this file proves only
what holds for every canonical continuation, the normal form and analyticity on `Re s > 1`.

## Main definitions

* `TauCeti.LFunctions.partialZeta`: the continued partial zeta function of a ray class.

## Main results

* `TauCeti.LFunctions.partialZeta_eq_LSeries_of_modulus_one`: at the trivial modulus,
  `partialZeta` agrees with the Dirichlet series of the class on `Re s > 1`.
* `TauCeti.LFunctions.completedPartialZeta_eq_partialZeta` and
  `TauCeti.LFunctions.completedPartialZeta_eventuallyEq_partialZeta`: the completed partial zeta
  function `Z(I, ·)` is the archimedean factor times the partial zeta function of the ideal class
  of `I⁻¹`, on `Re s > 1` and as punctured germs at every point.
* `TauCeti.LFunctions.analyticAt_partialZeta_iff_of_modulus_one`: at the trivial modulus,
  `partialZeta` is analytic exactly away from `s = 1`.
* `TauCeti.LFunctions.tendsto_sub_one_mul_partialZeta_of_modulus_one` and
  `TauCeti.LFunctions.meromorphicOrderAt_partialZeta_one_of_modulus_one`: a simple pole at `s = 1`
  with residue `rayClassIdealMainTerm (Modulus.one K)`, the same for every class.
* `TauCeti.LFunctions.sum_partialZeta_of_modulus_one`: the partial zeta functions of the ideal
  classes sum to `dedekindZetaC K`.

## References

* E. Hecke, *Über die Zetafunktion beliebiger algebraischer Zahlkörper*, Nachr. Ges. Wiss.
  Göttingen (1917), 77–89.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.4)–(5.10).
-/

public section
noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace Set TauCeti.GlobalNumberFields
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The continued partial zeta function of a ray class -/

/-- **The partial zeta function of a ray class** `c` of a modulus `𝔪`: the canonical meromorphic
continuation from `Re s > 1` of `ζ(s, c) = ∑_{𝔞 ∈ c} N(𝔞) ^ (-s)`, the Dirichlet series of the
class indicator `rayClassCoeff 𝔪 c`. It agrees with the series on `Re s > 1` once a continuation to
the plane exists (`meromorphicContinuation_eqOn`), and is `0` otherwise. -/
def partialZeta (𝔪 : Modulus K) (c : RayClassGroup 𝔪) : ℂ → ℂ :=
  meromorphicContinuation 1 (LSeries (normCoeff K (rayClassCoeff 𝔪 c)))

/-- The defining equation of the partial zeta function, through which the general results on
`meromorphicContinuation` apply to it. -/
theorem partialZeta_def (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    partialZeta 𝔪 c = meromorphicContinuation 1 (LSeries (normCoeff K (rayClassCoeff 𝔪 c))) :=
  (rfl)

/-- The partial zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_partialZeta (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    MeromorphicNFOn (partialZeta 𝔪 c) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The partial zeta function is meromorphic on the plane. -/
@[fun_prop]
theorem meromorphic_partialZeta (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    Meromorphic (partialZeta 𝔪 c) :=
  meromorphicOn_univ.mp (meromorphicNFOn_partialZeta 𝔪 c).meromorphicOn

/-- The partial zeta function is holomorphic on `Re s > 1`, for every modulus. -/
theorem analyticOnNhd_partialZeta (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    AnalyticOnNhd ℂ (partialZeta 𝔪 c) {s | 1 < s.re} :=
  analyticOnNhd_meromorphicContinuation
    (analyticOnNhd_LSeries_of_bounded (norm_rayClassCoeff_le_one 𝔪 c))

/-! ### The trivial modulus -/

section ModulusOne

variable (K) in
/-- The reciprocal `|d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂` of the archimedean factor of a
completed partial zeta function, written with the conductor and the reciprocal gamma factor of the
Dedekind zeta card. -/
private def invCompletionFactor (s : ℂ) : ℂ :=
  (((dedekindZetaData K).conductor : ℕ) : ℂ) ^ (-s / 2) * (dedekindZetaData K).invGammaFactor s

/-- The reciprocal archimedean factor is entire. -/
private theorem analyticAt_invCompletionFactor (s : ℂ) :
    AnalyticAt ℂ (invCompletionFactor K) s :=
  ((dedekindZetaData K).analyticAt_conductor_cpow (by fun_prop)).mul
    ((dedekindZetaData K).analyticAt_invGammaFactor s)

/-- On `Re s > 0` the archimedean factor has no zeros, so it cancels against its reciprocal. -/
private theorem invCompletionFactor_mul {s : ℂ} (hs : 0 < s.re) :
    invCompletionFactor K s * (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K) = 1 := by
  have hγ : (dedekindZetaData K).gammaFactor s ≠ 0 := by
    rw [dedekindZetaData_gammaFactor]
    exact mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs))
      (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))
  have hN := (dedekindZetaData K).conductor_cpow_ne_zero (s / 2)
  have hd : ((|discr K| : ℤ) : ℂ) = (((dedekindZetaData K).conductor : ℕ) : ℂ) := by
    rw [dedekindZetaData_conductor, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hd, mul_assoc _ (Gammaℝ s ^ _), ← dedekindZetaData_gammaFactor, invCompletionFactor,
    neg_div, cpow_neg, mul_mul_mul_comm, inv_mul_cancel₀ hN,
    (dedekindZetaData K).invGammaFactor_mul_gammaFactor hγ, one_mul]

/-- The reciprocal archimedean factor vanishes at `s = 0`, where `Γ_ℝ` and `Γ_ℂ` have poles and
`K` has at least one infinite place. -/
private theorem invCompletionFactor_zero : invCompletionFactor K 0 = 0 := by
  have hγ : (dedekindZetaData K).invGammaFactor 0 = 0 := by
    rw [AnalyticLFunctionData.invGammaFactor_eq_zero_iff_exists, dedekindZetaData_gammaR,
      dedekindZetaData_gammaC]
    rcases Nat.eq_zero_or_pos (nrRealPlaces K) with h | h
    · have := nrRealPlaces_add_nrComplexPlaces_pos K
      exact Or.inr ⟨0, Multiset.mem_replicate.mpr ⟨by omega, rfl⟩, 0, by simp⟩
    · exact Or.inl ⟨0, Multiset.mem_replicate.mpr ⟨h.ne', rfl⟩, 0, by simp⟩
  rw [invCompletionFactor, hγ, mul_zero]

/-- The reciprocal archimedean factor times a completed partial zeta function is meromorphic. -/
private theorem meromorphic_invCompletionFactor_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (invCompletionFactor K * completedPartialZeta I) :=
  fun s ↦ (analyticAt_invCompletionFactor s).meromorphicAt.mul
    (meromorphic_completedPartialZeta I s)

/-- At the trivial modulus, the partial zeta function of the ideal class of `I⁻¹` is the normal form
of the reciprocal archimedean factor times the completed partial zeta function of `I`. -/
private theorem partialZeta_eq_toMeromorphicNFOn (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    partialZeta (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) =
      toMeromorphicNFOn (invCompletionFactor K * completedPartialZeta I) univ := by
  rw [partialZeta_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_invCompletionFactor_mul I)
    (fun s hs ↦ ?_) fun s hs ↦ ?_
  · have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact (analyticAt_invCompletionFactor s).mul (analyticAt_completedPartialZeta I h0 h1)
  · rw [Pi.mul_apply, completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one I hs, ← mul_assoc,
      invCompletionFactor_mul (zero_lt_one.trans hs), one_mul]

/-- Every ideal class is the class of `I⁻¹` for some invertible fractional ideal `I`. -/
private theorem exists_oneEquivClassGroup_symm_eq (c : RayClassGroup (Modulus.one K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹ = c := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) (oneEquivClassGroup c)⁻¹
  exact ⟨FractionalIdeal.mk0 K J, by rw [ClassGroup.mk_mk0, hJ, inv_inv,
    MulEquiv.symm_apply_apply]⟩

/-- **Continuation of the partial zeta functions of the ideal classes.** At the trivial modulus,
`partialZeta` agrees with the Dirichlet series `∑_{𝔞 ∈ c} N(𝔞) ^ (-s)` of the class on `Re s > 1`:
the series continues to a meromorphic function on the plane. -/
theorem partialZeta_eq_LSeries_of_modulus_one (c : RayClassGroup (Modulus.one K)) {s : ℂ}
    (hs : 1 < s.re) :
    partialZeta (Modulus.one K) c s =
      LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  obtain ⟨I, rfl⟩ := exists_oneEquivClassGroup_symm_eq c
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [partialZeta_eq_toMeromorphicNFOn, toMeromorphicNFOn_apply_of_analyticAt
    (meromorphic_invCompletionFactor_mul I)
    ((analyticAt_invCompletionFactor s).mul (analyticAt_completedPartialZeta I h0 h1)),
    Pi.mul_apply, completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one I hs, ← mul_assoc,
    invCompletionFactor_mul (zero_lt_one.trans hs), one_mul]

/-- **The completed partial zeta function completes the partial zeta function of its class**,
Neukirch VII (5.4): on `Re s > 1`,
`Z(I, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ(s, c)` for `c` the ideal class of `I⁻¹`, read
as a ray class of the trivial modulus. -/
theorem completedPartialZeta_eq_partialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        partialZeta (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) s := by
  rw [partialZeta_eq_LSeries_of_modulus_one _ hs,
    completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one I hs]

/-- **The completed partial zeta function completes the partial zeta function of its class, as
germs**: at every point of the plane, `Z(I, ·)` has the punctured germ of
`s ↦ |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ(s, c)`, for `c` the ideal class of `I⁻¹`. The values
themselves differ at the poles of `Γ_ℝ` and `Γ_ℂ`, where Mathlib's gamma function takes the junk
value `0`. -/
theorem completedPartialZeta_eventuallyEq_partialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s] fun z ↦
      ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
        Gammaℂ z ^ nrComplexPlaces K *
        partialZeta (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) z := by
  have hd : ((|discr K| : ℤ) : ℂ) = (((dedekindZetaData K).conductor : ℕ) : ℂ) := by
    rw [dedekindZetaData_conductor, Int.abs_eq_natAbs, Int.cast_natCast]
  -- The archimedean factor is the conductor power times the gamma factor of the Dedekind card.
  have hA : Meromorphic fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
      Gammaℂ z ^ nrComplexPlaces K := by
    intro z
    simp_rw [hd, mul_assoc, ← dedekindZetaData_gammaFactor]
    exact ((dedekindZetaData K).analyticAt_conductor_cpow (by fun_prop)).meromorphicAt.mul
      ((dedekindZetaData K).meromorphic_gammaFactor z)
  exact eventuallyEq_of_meromorphic_of_eqOn_halfPlane (meromorphic_completedPartialZeta I)
    (hA.mul (meromorphic_partialZeta _ _)) (fun z hz ↦ completedPartialZeta_eq_partialZeta I hz) s

/-- **The partial zeta functions of the ideal classes are analytic away from `s = 1`.** At `s = 0`
the simple pole of the completed partial zeta function is cancelled by the zero of the reciprocal
archimedean factor. -/
theorem analyticAt_partialZeta_of_modulus_one (c : RayClassGroup (Modulus.one K)) {s : ℂ}
    (hs : s ≠ 1) : AnalyticAt ℂ (partialZeta (Modulus.one K) c) s := by
  obtain ⟨I, rfl⟩ := exists_oneEquivClassGroup_symm_eq c
  rw [partialZeta_eq_toMeromorphicNFOn, ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn (meromorphic_invCompletionFactor_mul I).meromorphicOn
      (mem_univ s)]
  by_cases h0 : s = 0
  · subst h0
    -- The reciprocal factor has a zero at `0` and the completed function a simple pole.
    have hpos : 0 < meromorphicOrderAt (invCompletionFactor K) 0 := by
      have h := (analyticAt_invCompletionFactor (K := K) 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [invCompletionFactor_zero] at h
      exact (tendsto_zero_iff_meromorphicOrderAt_pos
        (analyticAt_invCompletionFactor 0).meromorphicAt).mp h
    rw [meromorphicOrderAt_mul (analyticAt_invCompletionFactor 0).meromorphicAt
      (meromorphic_completedPartialZeta I 0), meromorphicOrderAt_completedPartialZeta_zero]
    generalize meromorphicOrderAt (invCompletionFactor K) 0 = n at hpos ⊢
    induction n using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      norm_cast at hpos ⊢
      omega
  · exact ((analyticAt_invCompletionFactor s).mul
      (analyticAt_completedPartialZeta I h0 hs)).meromorphicOrderAt_nonneg

/-- **The common residue of the partial zeta functions of the ideal classes**: as `s → 1` in `ℂ`,
`(s - 1) ζ(s, c)` tends to `rayClassIdealMainTerm (Modulus.one K)`, the main term of the count of
the ideals of one class, for every ideal class `c`. By `ofReal_rayClassIdealMainTerm` this
residue is `ρ_K / h`, with `ρ_K = dedekindZeta_residue K` and `h` the number of ideal classes. -/
theorem tendsto_sub_one_mul_partialZeta_of_modulus_one (c : RayClassGroup (Modulus.one K)) :
    Tendsto (fun s : ℂ ↦ (s - 1) * partialZeta (Modulus.one K) c s) (𝓝[≠] 1)
      (𝓝 (rayClassIdealMainTerm (Modulus.one K) : ℂ)) := by
  obtain ⟨I, rfl⟩ := exists_oneEquivClassGroup_symm_eq c
  -- Near `s = 1` the partial zeta function is the reciprocal factor times `Z(I, s)`, so the
  -- two-sided limit exists; along the real axis from the right it is the residue of the series.
  have hlim : Tendsto (fun s : ℂ ↦ (s - 1) *
      partialZeta (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) s) (𝓝[≠] 1)
      (𝓝 (invCompletionFactor K 1 * (2 * mellinConstant K))) := by
    refine (((analyticAt_invCompletionFactor 1).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).mul (tendsto_sub_one_mul_completedPartialZeta I)).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero), self_mem_nhdsWithin]
      with s hs0 hs1
    rw [partialZeta_eq_toMeromorphicNFOn, toMeromorphicNFOn_apply_of_analyticAt
      (meromorphic_invCompletionFactor_mul I)
      ((analyticAt_invCompletionFactor s).mul (analyticAt_completedPartialZeta I hs0 hs1)),
      Pi.mul_apply]
    ring
  have hreal : Tendsto (fun s : ℝ ↦ (s - 1 : ℂ) *
      partialZeta (Modulus.one K) (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹) s) (𝓝[>] 1)
      (𝓝 (rayClassIdealMainTerm (Modulus.one K) : ℂ)) := by
    refine (tendsto_sub_one_mul_LSeries_rayClassCoeff (Modulus.one K)
      (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [partialZeta_eq_LSeries_of_modulus_one _ (by simpa using hs)]
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto' 1 1 ofReal_one).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun s hs ↦
        by simpa using (show (1 : ℝ) < s from hs).ne'⟩
  rwa [tendsto_nhds_unique (hlim.comp hofReal) hreal] at hlim

/-- **The partial zeta functions of the ideal classes have a simple pole at `s = 1`.** -/
theorem meromorphicOrderAt_partialZeta_one_of_modulus_one (c : RayClassGroup (Modulus.one K)) :
    meromorphicOrderAt (partialZeta (Modulus.one K) c) 1 = (-1 : ℤ) :=
  (meromorphic_partialZeta _ c 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (ofReal_ne_zero.mpr (rayClassIdealMainTerm_pos _).ne')
    (tendsto_sub_one_mul_partialZeta_of_modulus_one c)

/-- At the trivial modulus, `partialZeta` is analytic at `s` if and only if `s ≠ 1`. -/
@[simp]
theorem analyticAt_partialZeta_iff_of_modulus_one (c : RayClassGroup (Modulus.one K)) {s : ℂ} :
    AnalyticAt ℂ (partialZeta (Modulus.one K) c) s ↔ s ≠ 1 := by
  refine ⟨fun han ↦ ?_, analyticAt_partialZeta_of_modulus_one c⟩
  rintro rfl
  have hnonneg := han.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_partialZeta_one_of_modulus_one] at hnonneg
  exact absurd hnonneg (by decide)

/-- As a meromorphic normal form, the partial zeta function of an ideal class takes the canonical
value `0` at its pole `s = 1`. -/
@[simp]
theorem partialZeta_apply_one_of_modulus_one (c : RayClassGroup (Modulus.one K)) :
    partialZeta (Modulus.one K) c 1 = 0 :=
  not_not.mp <| (meromorphicNFOn_partialZeta _ c (mem_univ 1))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp
    (by simp [meromorphicOrderAt_partialZeta_one_of_modulus_one])

/-- **The partial zeta functions of the ideal classes sum to the Dedekind zeta function** on the
whole plane, as functions in meromorphic normal form: on `Re s > 1` this is the decomposition of
`ζ_K(s)` over the ideal classes (`sum_LSeries_rayClassCoeff_one`), away from `s = 1` both sides
are analytic, and at `s = 1` both take the normal-form value `0`. -/
theorem sum_partialZeta_of_modulus_one [Fintype (RayClassGroup (Modulus.one K))] :
    ∑ c : RayClassGroup (Modulus.one K), partialZeta (Modulus.one K) c = dedekindZetaC K := by
  have h1 : dedekindZetaC K 1 = 0 :=
    not_not.mp <| (meromorphicNFOn_dedekindZetaC K (mem_univ 1))
      |>.meromorphicOrderAt_eq_zero_iff.not.mp
      (by simp [meromorphicOrderAt_dedekindZetaC_one])
  have hoff : EqOn (∑ c : RayClassGroup (Modulus.one K), partialZeta (Modulus.one K) c)
      (dedekindZetaC K) {1}ᶜ := by
    refine eqOn_dedekindZetaC_of_eqOn_dedekindZeta K (fun z hz ↦ ?_) fun z hz ↦ ?_
    · rw [Finset.sum_fn]
      exact Finset.analyticAt_fun_sum _ fun c _ ↦ analyticAt_partialZeta_of_modulus_one c hz
    · rw [Finset.sum_apply, ← sum_LSeries_rayClassCoeff_one hz]
      exact Finset.sum_congr rfl fun c _ ↦ partialZeta_eq_LSeries_of_modulus_one c hz
  funext z
  by_cases hz : z = 1
  · subst hz
    simp [h1]
  · exact hoff hz

/-- **The decomposition of `ζ_K` over the ideal classes**, for the continued functions on
`Re s > 1`, where `dedekindZetaC K` is Mathlib's Dirichlet series `NumberField.dedekindZeta K`. -/
theorem sum_partialZeta_eq_dedekindZeta_of_modulus_one [Fintype (RayClassGroup (Modulus.one K))]
    {s : ℂ} (hs : 1 < s.re) :
    ∑ c : RayClassGroup (Modulus.one K), partialZeta (Modulus.one K) c s = dedekindZeta K s := by
  rw [← Finset.sum_apply, sum_partialZeta_of_modulus_one, dedekindZetaC_eq_dedekindZeta K hs]

end ModulusOne

end TauCeti.LFunctions
