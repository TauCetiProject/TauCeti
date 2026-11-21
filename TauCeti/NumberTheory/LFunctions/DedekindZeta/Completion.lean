/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# The completed Dedekind zeta function

The completed Dedekind zeta function `TauCeti.LFunctions.completedDedekindZeta K` is defined as the
canonical meromorphic continuation in meromorphic normal form on `ℂ`
(`TauCeti.meromorphicContinuation`) from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`.

The class-group decomposition `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`
identifies `completedDedekindZeta K` globally with the sum of
`TauCeti.LFunctions.completedPartialZeta` over any section of `ClassGroup.mk K`. Because
`completedPartialZeta` is already meromorphic on `ℂ`, analytic away from `{0, 1}` with simple poles
of residue `∓ 2 a₀ = ∓ 2^(r₁ + r₂) R / w` at `0` and `1`, and satisfies
`completedPartialZeta I (1 - s) = completedPartialZeta (dualEquiv ℤ ℚ I) s`, summing over the
`h = classNumber K` ideal classes shows that `completedDedekindZeta K` is analytic
away from `{0, 1}`, has simple poles at `0` and `1` with residues `∓ 2^(r₁ + r₂) R h / w`,
satisfies `Λ_K(1 - s) = Λ_K(s)` since `c ↦ [I^∨]` permutes the class group, and satisfies
reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.

Over `ℚ`, `completedDedekindZeta ℚ` has the same punctured germ as `completedRiemannZeta`
everywhere on `ℂ` and agrees with it pointwise away from the poles `0` and `1`.

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the completed Dedekind zeta function of `K`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eq`,
  `TauCeti.LFunctions.two_pow_mul_regulator_mul_classNumber_div_torsionOrder_eq`: class-group
  decomposition, half-plane Dirichlet-series formula, and algebraic residue comparison.
* `TauCeti.LFunctions.completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_rat_eq_completedRiemannZeta`: comparison with
  `completedRiemannZeta` over `ℚ`.
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
  `TauCeti.LFunctions.completedDedekindZeta_conj`: the functional equation `Λ_K(1 - s) = Λ_K(s)`,
  its punctured-neighborhood form, and reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.

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
/-- Nonvanishing of the common residue `h * (2 a₀)` in `ℂ`. -/
private theorem classNumber_mul_two_mul_mellinConstant_ne_zero :
    (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
    (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))

variable (K) in
/-- Algebraic identity comparing `2^(r₁ + r₂) R h / w` with
`|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ ρ_K`, where `ρ_K = NumberField.dedekindZeta_residue K`. -/
theorem two_pow_mul_regulator_mul_classNumber_div_torsionOrder_eq :
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

private theorem tendsto_mul_sum_completedPartialZeta_zero
    (f : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun z : ℂ ↦ z * ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) z)
      (𝓝[≠] 0) (𝓝 (-(classNumber K * (2 * (mellinConstant K : ℂ))))) := by
  have hsum : Tendsto (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), z * completedPartialZeta (f c) z)
      (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), -(2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_mul_completedPartialZeta_zero (f c)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg] at hsum
  rw [← NumberField.classNumber] at hsum
  exact hsum.congr fun z ↦ (Finset.mul_sum _ _ _).symm

private theorem tendsto_sub_one_mul_sum_completedPartialZeta
    (f : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun z : ℂ ↦ (z - 1) * ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) z)
      (𝓝[≠] 1) (𝓝 (classNumber K * (2 * (mellinConstant K : ℂ)))) := by
  have hsum : Tendsto
      (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), (z - 1) * completedPartialZeta (f c) z)
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta (f c)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← NumberField.classNumber] at hsum
  exact hsum.congr fun z ↦ (Finset.mul_sum _ _ _).symm

private theorem sum_completedPartialZeta_eqOn
    {f : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hf : ∀ c, ClassGroup.mk K (f c) = c) :
    EqOn (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) z)
      (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        NumberField.dedekindZeta K z)
      {z : ℂ | 1 < z.re} := by
  intro z hz
  simp_rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hz, hf, ← Finset.mul_sum]
  congr 1
  let _ : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
  rw [← sum_LSeries_rayClassCoeff_one hz]
  exact Equiv.sum_comp ((Equiv.inv _).trans oneEquivClassGroup.symm.toEquiv)
    (fun c ↦ LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) z)

/-- **Class-group decomposition of the completed Dedekind zeta function**:
`Λ_K(s) = ∑_{c ∈ Cl_K} Λ(f c, s)` for any section `f` of `ClassGroup.mk K` and every `s : ℂ`,
including the poles `0` and `1` where both sides are in meromorphic normal form and take the
canonical value `0`. -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    {f : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hf : ∀ c, ClassGroup.mk K (f c) = c) (s : ℂ) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) s := by
  let F : ℂ → ℂ := fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) z
  have hM : Meromorphic F := fun z ↦ MeromorphicAt.fun_sum fun c _ ↦
    meromorphic_completedPartialZeta (f c) z
  have hres0 := tendsto_mul_sum_completedPartialZeta_zero f
  have hres1 := tendsto_sub_one_mul_sum_completedPartialZeta f
  have hne_res := classNumber_mul_two_mul_mellinConstant_ne_zero K
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
        analyticAt_completedPartialZeta (f c) hz0 hz1)
  have heq : completedDedekindZeta K = F := by
    rw [completedDedekindZeta_def]
    exact meromorphicContinuation_eq hNF (sum_completedPartialZeta_eqOn hf)
  exact congrFun heq s

/-- On `Re s > 1`, `completedDedekindZeta K` equals `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        NumberField.dedekindZeta K s := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  rw [completedDedekindZeta_eq_sum_completedPartialZeta hf]
  exact sum_completedPartialZeta_eqOn hf hs

/-! ### Comparison with the completed Riemann zeta function over `ℚ` -/

private theorem completedDedekindZeta_rat_eqOn :
    EqOn (completedDedekindZeta ℚ) completedRiemannZeta {s | 1 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [completedDedekindZeta_eq hs, NumberField.discr_rat,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta_rat_eq_riemannZeta hs, riemannZeta_def_of_ne_zero hs0]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by change 1 < s.re at hs; linarith)
  simp [field]

/-- **The completed Dedekind zeta function of `ℚ` has the punctured germ of
`completedRiemannZeta`** at every point of the plane, including the poles `0` and `1`. -/
theorem completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta (s : ℂ) :
    completedDedekindZeta ℚ =ᶠ[𝓝[≠] s] completedRiemannZeta :=
  eventuallyEq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta ℚ) meromorphic_completedRiemannZeta
    completedDedekindZeta_rat_eqOn s

/-- **The completed Dedekind zeta function of `ℚ` equals `completedRiemannZeta`** away from `0` and
`1`. At `0` and `1` both sides have simple poles, and
`completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta` compares their germs there. -/
theorem completedDedekindZeta_rat_eq_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s := by
  have han : AnalyticAt ℂ (completedDedekindZeta ℚ) s := by
    obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 ℚ) ℚ).hasRightInverse
    rw [funext (completedDedekindZeta_eq_sum_completedPartialZeta hf)]
    exact Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
      analyticAt_completedPartialZeta (f c) h0 h1
  exact eq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta ℚ) meromorphic_completedRiemannZeta
    completedDedekindZeta_rat_eqOn han (analyticAt_completedRiemannZeta h0 h1)

/-! ### Analyticity, poles, and residues -/

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
@[fun_prop]
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  have heq : completedDedekindZeta K =
      fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (f c) z :=
    funext (completedDedekindZeta_eq_sum_completedPartialZeta hf)
  rw [heq]
  exact Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
    analyticAt_completedPartialZeta (f c) h0 h1

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 0`**:
`s * Λ_K(s) → -2^(r₁ + r₂) R h / w` as `s → 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ))) := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  have hlim : -(classNumber K * (2 * (mellinConstant K : ℂ))) =
      -((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_mul,
      classNumber_mul_two_mul_mellinConstant]
  simpa only [completedDedekindZeta_eq_sum_completedPartialZeta hf, hlim] using
    tendsto_mul_sum_completedPartialZeta_zero f

variable (K) in
/-- **Residue of `completedDedekindZeta` at `s = 1`**:
`(s - 1) * Λ_K(s) → 2^(r₁ + r₂) R h / w` as `s → 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ)) := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  have hlim : (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) =
      ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_mul,
      classNumber_mul_two_mul_mellinConstant]
  simpa only [completedDedekindZeta_eq_sum_completedPartialZeta hf, hlim] using
    tendsto_sub_one_mul_sum_completedPartialZeta f

private theorem completedDedekindZeta_residue_ne_zero (K : Type*) [Field K] [NumberField K] :
    ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
        torsionOrder K : ℝ) : ℂ) ≠ 0 := by
  have h := classNumber_mul_two_mul_mellinConstant_ne_zero K
  rwa [← ofReal_natCast, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_mul,
    classNumber_mul_two_mul_mellinConstant] at h

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  refine (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr (completedDedekindZeta_residue_ne_zero K)) ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  refine (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (completedDedekindZeta_residue_ne_zero K) ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K

/-- `completedDedekindZeta K` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedDedekindZeta_iff {s : ℂ} :
    AnalyticAt ℂ (completedDedekindZeta K) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedDedekindZeta h0 h1⟩
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    simp only [meromorphicOrderAt_completedDedekindZeta_zero, WithTop.coe_nonneg] at hnonneg
    omega
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    simp only [meromorphicOrderAt_completedDedekindZeta_one, WithTop.coe_nonneg] at hnonneg
    omega

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedDedekindZeta_zero : completedDedekindZeta K 0 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedDedekindZeta K (mem_univ 0))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp (by simp)

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedDedekindZeta_one : completedDedekindZeta K 1 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedDedekindZeta K (mem_univ 1))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp (by simp)

/-! ### Functional equation and reflection symmetry -/

variable (K) in
/-- **Hecke's functional equation for the completed Dedekind zeta function**, Neukirch VII
Corollary 5.10: `Λ_K(1 - s) = Λ_K(s)` for every `s : ℂ`. -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  set d : ClassGroup (𝓞 K) := ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : _))
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) := (Equiv.inv _).trans (Equiv.mulLeft d)
  rw [completedDedekindZeta_eq_sum_completedPartialZeta hf,
    completedDedekindZeta_eq_sum_completedPartialZeta hf]
  have hterm (c : ClassGroup (𝓞 K)) :
      completedPartialZeta (f c) (1 - s) = completedPartialZeta (f (e c)) s := by
    rw [completedPartialZeta_one_sub]
    refine congrFun (completedPartialZeta_congr_class ?_) s
    rw [FractionalIdeal.dualEquiv_eq_mul_inv, map_mul, map_inv, hf c, hf (e c)]
    rfl
  simp_rw [hterm]
  exact Equiv.sum_comp e (fun c ↦ completedPartialZeta (f c) s)

variable (K) in
/-- **Punctured-neighborhood form of Hecke's functional equation for the completed Dedekind zeta
function**: `fun z ↦ Λ_K(1 - z)` agrees with `Λ_K` on `𝓝[≠] s` for every `s : ℂ`. -/
theorem completedDedekindZeta_one_sub_eventuallyEq (s : ℂ) :
    (fun z : ℂ ↦ completedDedekindZeta K (1 - z)) =ᶠ[𝓝[≠] s] completedDedekindZeta K :=
  Eventually.of_forall (completedDedekindZeta_one_sub K)

variable (K) in
/-- **Reflection symmetry of the completed Dedekind zeta function**:
`Λ_K(conj s) = conj (Λ_K(s))` for every `s : ℂ`. -/
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  obtain ⟨f, hf⟩ := (ClassGroup.mk_surjective (𝓞 K) K).hasRightInverse
  rw [completedDedekindZeta_eq_sum_completedPartialZeta hf,
    completedDedekindZeta_eq_sum_completedPartialZeta hf, map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_conj (f c) s

end TauCeti.LFunctions
