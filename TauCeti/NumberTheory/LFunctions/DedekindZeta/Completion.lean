/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta

/-!
# The completed Dedekind zeta function

The completed Dedekind zeta function `TauCeti.LFunctions.completedDedekindZeta K` is defined as the
canonical meromorphic continuation in meromorphic normal form on `ℂ`
(`TauCeti.meromorphicContinuation`) from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`.

The class-group decomposition
`TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZetaClass` identifies
`completedDedekindZeta K` globally with the sum of `TauCeti.LFunctions.completedPartialZetaClass`
over `ClassGroup (𝓞 K)`. Because `completedPartialZetaClass c` is already meromorphic on `ℂ`,
analytic away from `{0, 1}` with simple poles of residue `∓ 2 a₀ = ∓ 2^(r₁ + r₂) R / w` at `0`
and `1`, and satisfies
`completedPartialZetaClass c (1 - s) = completedPartialZetaClass ([𝔡] * c⁻¹) s`,
summing over the `h = classNumber K` ideal classes shows that `completedDedekindZeta K` is analytic
away from `{0, 1}`, has simple poles at `0` and `1` with residues `∓ 2^(r₁ + r₂) R h / w`,
satisfies `Λ_K(1 - s) = Λ_K(s)` since `c ↦ [𝔡] * c⁻¹` permutes the class group, and satisfies
reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the completed Dedekind zeta function of `K`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZetaClass`,
  `TauCeti.LFunctions.completedDedekindZeta_eq`: class-group decomposition and half-plane
  Dirichlet-series formula.
* `TauCeti.LFunctions.analyticAt_completedDedekindZeta`,
  `TauCeti.LFunctions.analyticAt_completedDedekindZeta_iff`,
  `TauCeti.LFunctions.completedDedekindZeta_zero`,
  `TauCeti.LFunctions.completedDedekindZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`: analyticity, canonical pole
  values, residues, and simple poles of `completedDedekindZeta`.
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`,
  `TauCeti.LFunctions.completedDedekindZeta_one_sub_eventuallyEq`,
  `TauCeti.LFunctions.completedDedekindZeta_conj`: the functional equation `Λ_K(1 - s) = Λ_K(s)`
  (pointwise and as punctured germs) and reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Theorem 5.9 and Corollary 5.10.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.Units Set TauCeti.GlobalNumberFields
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

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
@[fun_prop]
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
/-- Complex cast of `classNumber_mul_two_mul_mellinConstant`. -/
private theorem classNumber_mul_two_mul_mellinConstant_complex :
    (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) =
      ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) := by
  exact_mod_cast classNumber_mul_two_mul_mellinConstant K

variable (K) in
/-- Nonvanishing of the common residue `h * (2 a₀)` in `ℂ`. -/
private theorem classNumber_mul_two_mul_mellinConstant_ne_zero :
    (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
    (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))

/-! ### Class-sum helpers and decomposition -/

private theorem meromorphic_sum_completedPartialZetaClass :
    Meromorphic (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z) :=
  fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZetaClass c z

private theorem analyticAt_sum_completedPartialZetaClass {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z) s :=
  Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
    analyticAt_completedPartialZetaClass c h0 h1

private theorem sum_completedPartialZetaClass_one_sub (s : ℂ) :
    (∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c (1 - s)) =
      ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c s := by
  set d : ClassGroup (𝓞 K) :=
    (ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _)))⁻¹
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) := (Equiv.inv _).trans (Equiv.mulLeft d)
  simp_rw [fun c ↦ completedPartialZetaClass_one_sub c s]
  exact Equiv.sum_comp e (fun c ↦ completedPartialZetaClass c s)

private theorem tendsto_sub_one_mul_sum_completedPartialZetaClass :
    Tendsto (fun z : ℂ ↦ (z - 1) * ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z)
      (𝓝[≠] 1) (𝓝 (classNumber K * (2 * (mellinConstant K : ℂ)))) := by
  have hsum : Tendsto
      (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), (z - 1) * completedPartialZetaClass c z)
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_sub_one_mul_completedPartialZetaClass c
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← NumberField.classNumber] at hsum
  exact hsum.congr fun z ↦ (Finset.mul_sum _ _ _).symm

private theorem tendsto_mul_sum_completedPartialZetaClass_zero :
    Tendsto (fun z : ℂ ↦ z * ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z)
      (𝓝[≠] 0) (𝓝 (-(classNumber K * (2 * (mellinConstant K : ℂ))))) := by
  have hsub : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [sub_zero] using
        ((continuous_sub_left (1 : ℂ)).continuousAt (x := (0 : ℂ))).tendsto.mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      exact fun h ↦ hz (sub_eq_self.mp h)
  have hlim := ((tendsto_sub_one_mul_sum_completedPartialZetaClass (K := K)).comp hsub).neg
  refine hlim.congr fun z ↦ ?_
  simp only [Function.comp_apply, sum_completedPartialZetaClass_one_sub]
  ring

private theorem meromorphicOrderAt_sum_completedPartialZetaClass_zero :
    meromorphicOrderAt
        (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z) 0 = (-1 : ℤ) := by
  refine (meromorphic_sum_completedPartialZetaClass 0)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
      (neg_ne_zero.mpr (classNumber_mul_two_mul_mellinConstant_ne_zero K)) ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_sum_completedPartialZetaClass_zero (K := K)

private theorem meromorphicOrderAt_sum_completedPartialZetaClass_one :
    meromorphicOrderAt
        (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z) 1 = (-1 : ℤ) := by
  refine (meromorphic_sum_completedPartialZetaClass 1)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
      (classNumber_mul_two_mul_mellinConstant_ne_zero K) ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_sum_completedPartialZetaClass (K := K)

private theorem sum_completedPartialZetaClass_eqOn :
    EqOn (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z)
      (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        NumberField.dedekindZeta K z)
      {z : ℂ | 1 < z.re} := by
  intro z hz
  simp_rw [fun c ↦ completedPartialZetaClass_eq_mul_LSeries_rayClassCoeff_one c hz,
    ← Finset.mul_sum]
  congr 1
  let _ : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
  rw [← sum_LSeries_rayClassCoeff_one hz]
  exact Equiv.sum_comp oneEquivClassGroup.symm.toEquiv
    (fun c ↦ LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) z)

/-- **Class-group decomposition of the completed Dedekind zeta function**:
`Λ_K(s) = ∑_{c ∈ Cl_K} completedPartialZetaClass c s` for every `s : ℂ`, including the poles `0`
and `1` where both sides are in meromorphic normal form and take the canonical value `0`. -/
theorem completedDedekindZeta_eq_sum_completedPartialZetaClass (s : ℂ) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c s := by
  let F : ℂ → ℂ := fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZetaClass c z
  have hNF : MeromorphicNFOn F univ := by
    intro z _
    rw [meromorphicNFAt_iff_analyticAt_or]
    rcases eq_or_ne z 0 with rfl | hz0
    · refine Or.inr ⟨meromorphic_sum_completedPartialZetaClass 0, ?_, ?_⟩
      · rw [meromorphicOrderAt_sum_completedPartialZetaClass_zero]
        exact WithTop.coe_lt_zero.mpr (by norm_num)
      · exact Finset.sum_eq_zero fun c _ ↦ completedPartialZetaClass_zero c
    rcases eq_or_ne z 1 with rfl | hz1
    · refine Or.inr ⟨meromorphic_sum_completedPartialZetaClass 1, ?_, ?_⟩
      · rw [meromorphicOrderAt_sum_completedPartialZetaClass_one]
        exact WithTop.coe_lt_zero.mpr (by norm_num)
      · exact Finset.sum_eq_zero fun c _ ↦ completedPartialZetaClass_one c
    · exact Or.inl (analyticAt_sum_completedPartialZetaClass hz0 hz1)
  have heq : completedDedekindZeta K = F := by
    rw [completedDedekindZeta_def]
    exact meromorphicContinuation_eq hNF (sum_completedPartialZetaClass_eqOn (K := K))
  exact congrFun heq s

/-- On `Re s > 1`, `completedDedekindZeta K` equals `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        NumberField.dedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZetaClass]
  exact sum_completedPartialZetaClass_eqOn hs

/-! ### Analyticity, poles, and residues -/

/- The analyticity, residue, simple-pole, and canonical normal-form value proofs below follow the
corresponding class-indexed partial-zeta API in
`TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta`
(`analyticAt_completedPartialZetaClass`, `tendsto_mul_completedPartialZetaClass_zero`,
`tendsto_sub_one_mul_completedPartialZetaClass`,
`meromorphicOrderAt_completedPartialZetaClass_zero`,
`meromorphicOrderAt_completedPartialZetaClass_one`, `analyticAt_completedPartialZetaClass_iff`,
`completedPartialZetaClass_zero`, and `completedPartialZetaClass_one`) as their formal template. -/

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
@[fun_prop]
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  rw [funext (completedDedekindZeta_eq_sum_completedPartialZetaClass (K := K))]
  exact analyticAt_sum_completedPartialZetaClass h0 h1

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 0`**:
`s * Λ_K(s) → -2^(r₁ + r₂) R h / w` as `s → 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ))) := by
  simpa only [completedDedekindZeta_eq_sum_completedPartialZetaClass,
    classNumber_mul_two_mul_mellinConstant_complex] using
    tendsto_mul_sum_completedPartialZetaClass_zero (K := K)

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 1`**:
`(s - 1) * Λ_K(s) → 2^(r₁ + r₂) R h / w` as `s → 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ)) := by
  simpa only [completedDedekindZeta_eq_sum_completedPartialZetaClass,
    classNumber_mul_two_mul_mellinConstant_complex] using
    tendsto_sub_one_mul_sum_completedPartialZetaClass (K := K)

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  rw [funext (completedDedekindZeta_eq_sum_completedPartialZetaClass (K := K))]
  exact meromorphicOrderAt_sum_completedPartialZetaClass_zero

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  rw [funext (completedDedekindZeta_eq_sum_completedPartialZetaClass (K := K))]
  exact meromorphicOrderAt_sum_completedPartialZetaClass_one

/-- `completedDedekindZeta K` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedDedekindZeta_iff {s : ℂ} :
    AnalyticAt ℂ (completedDedekindZeta K) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedDedekindZeta h0 h1⟩
  · rintro rfl
    exact not_analyticAt_of_meromorphicOrderAt_neg
      (by rw [meromorphicOrderAt_completedDedekindZeta_zero]
          exact WithTop.coe_lt_zero.mpr (by norm_num)) han
  · rintro rfl
    exact not_analyticAt_of_meromorphicOrderAt_neg
      (by rw [meromorphicOrderAt_completedDedekindZeta_one]
          exact WithTop.coe_lt_zero.mpr (by norm_num)) han

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedDedekindZeta_zero : completedDedekindZeta K 0 = 0 :=
  (meromorphicNFOn_completedDedekindZeta K (mem_univ 0))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by simp)

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedDedekindZeta_one : completedDedekindZeta K 1 = 0 :=
  (meromorphicNFOn_completedDedekindZeta K (mem_univ 1))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by simp)

/-! ### Functional equation and reflection symmetry -/

variable (K) in
/-- **Hecke's functional equation for the completed Dedekind zeta function**, Neukirch VII
Corollary 5.10: `Λ_K(1 - s) = Λ_K(s)` for every `s : ℂ`. -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZetaClass,
    completedDedekindZeta_eq_sum_completedPartialZetaClass,
    sum_completedPartialZetaClass_one_sub]

variable (K) in
/-- Punctured-germ form of `TauCeti.LFunctions.completedDedekindZeta_one_sub` at every point
`s : ℂ` (poles included). -/
theorem completedDedekindZeta_one_sub_eventuallyEq (s : ℂ) :
    (fun z : ℂ ↦ completedDedekindZeta K (1 - z)) =ᶠ[𝓝[≠] s] completedDedekindZeta K :=
  Eventually.of_forall (completedDedekindZeta_one_sub K)

variable (K) in
/-- **Reflection symmetry of the completed Dedekind zeta function**:
`Λ_K(conj s) = conj (Λ_K(s))` for every `s : ℂ`. -/
@[simp]
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  rw [completedDedekindZeta_eq_sum_completedPartialZetaClass,
    completedDedekindZeta_eq_sum_completedPartialZetaClass, map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZetaClass_conj c s

end TauCeti.LFunctions
