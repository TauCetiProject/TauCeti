/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The completed Dedekind zeta function

For a number field `K` with `r₁` real and `r₂` complex places, the completed Dedekind zeta
function is, on `Re s > 1`,

`Λ_K(s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ_K(s)`.

We define `TauCeti.LFunctions.completedDedekindZeta K` globally on `ℂ` as the canonical
meromorphic normal-form continuation (`TauCeti.meromorphicContinuation 1`) of this function from
`Re s > 1`. The continuation exists because the Dirichlet series `ζ_K(s)` is the sum over the
ideal classes of the partial Dirichlet series, so that `Λ_K` is the sum over `ClassGroup (𝓞 K)`
of the completed partial zeta functions `completedPartialZeta I` of representatives
(`completedDedekindZeta_eq_sum_completedPartialZeta`). Hecke's theory of these partial functions
then gives:

* analyticity of `Λ_K` away from `s = 0` and `s = 1`, where it has simple poles with residues
  `∓ 2 ^ (r₁ + r₂) h R / w`, `h` the class number, `R` the regulator and `w` the number of roots
  of unity in `K`;
* the functional equation `Λ_K(1 - s) = Λ_K(s)`. The trace dual `I ↦ I^∨ = 𝔡⁻¹ I⁻¹` induces the
  bijection `[I] ↦ [𝔡]⁻¹ [I]⁻¹` of the class group, so Hecke's functional equation
  `Z(I, 1 - s) = Z(I^∨, s)` for the partial functions sums to that of `Λ_K`.

Dividing by the archimedean factor, whose reciprocal `|d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂`
is entire, transfers this to the continued Dedekind zeta function
`TauCeti.LFunctions.dedekindZetaC K`: it agrees with Mathlib's `NumberField.dedekindZeta K` on
`Re s > 1`, is analytic away from `s = 1` (the zero of the reciprocal factor at `s = 0` cancels the
pole of `Λ_K` there), and has a simple pole at `s = 1` whose residue is Mathlib's
`NumberField.dedekindZeta_residue K`, the analytic class number formula.

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the completed Dedekind zeta function of `K` in
  meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_eq_mul_dedekindZeta`: on `Re s > 1`,
  `Λ_K(s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ_K(s)`.
* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`: `Λ_K` is the sum of
  the completed partial zeta functions of any system of representatives of the ideal classes.
* `TauCeti.LFunctions.analyticAt_completedDedekindZeta_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`: `Λ_K` is analytic exactly
  away from `0` and `1`, where it has simple poles.
* `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`: the residues
  `2 ^ (r₁ + r₂) h R / w` at `s = 1` and `-2 ^ (r₁ + r₂) h R / w` at `s = 0`.
* `TauCeti.LFunctions.toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum`: the entire repair of
  `s(s - 1) Λ_K(s)` is the sum of the pole-cleared ideal-lattice Mellin completions. At both
  former poles it takes the value of the residue of `Λ_K` at `1`.
  The identity `completedPartialZeta_eq_mellinKernelFEPair_Λ` uses Neukirch's normalization
  (Chapter VII, §5).
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`: the functional equation
  `Λ_K(1 - s) = Λ_K(s)` for every `s : ℂ`.
* `TauCeti.LFunctions.dedekindZetaC_eq_mul_completedDedekindZeta`: away from `0` and `1`,
  `ζ_K(s) = |d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂ Λ_K(s)`.
* `TauCeti.LFunctions.dedekindZetaC_eq_dedekindZeta`: `dedekindZetaC K` agrees with
  `NumberField.dedekindZeta K` on `Re s > 1`.
* `TauCeti.LFunctions.eqOn_dedekindZetaC_of_eqOn_dedekindZeta`: uniqueness away from `1` of
  an analytic continuation agreeing with the Dedekind zeta series on `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_dedekindZetaC_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`: `ζ_K` is analytic exactly away
  from `1`, where it has a simple pole.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_ne_top`: `ζ_K` has finite order
  everywhere.
* `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`: its residue at `s = 1` is
  `NumberField.dedekindZeta_residue K = 2 ^ r₁ (2π) ^ r₂ h R / (w √|d_K|)`.

## References

* E. Hecke, *Über die Zetafunktion beliebiger algebraischer Zahlkörper*, Nachr. Ges. Wiss.
  Göttingen (1917), 77–89.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.Units Set
  TauCeti.GlobalNumberFields
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The completed Dedekind zeta function** of a number field `K`: the canonical whole-plane
meromorphic normal-form continuation from `Re s > 1` of
`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ_K(s)`. -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

/-- Defining equation of `TauCeti.LFunctions.completedDedekindZeta`. -/
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s :=
  (rfl)

/-! ### The sum over the ideal classes -/

section ClassSum

variable {K}

/-- On `Re s > 1`, the completed partial zeta functions of a system of representatives of the
ideal classes sum to the archimedean factor times `ζ_K(s)`. -/
private theorem sum_completedPartialZeta_eq_mul_dedekindZeta
    {rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) {s : ℂ} (hs : 1 < s.re) :
    ∑ c, completedPartialZeta (rep c) s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  let : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv _ (oneEquivClassGroup (K := K)).symm.toEquiv
  simp_rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hs, hrep, ← Finset.mul_sum,
    ← sum_LSeries_rayClassCoeff_one hs]
  congr 1
  exact Fintype.sum_equiv ((Equiv.inv _).trans (oneEquivClassGroup (K := K)).symm.toEquiv) _ _
    fun _ ↦ rfl

/-- The residue at `s = 1` of the sum of the completed partial zeta functions of a system of
representatives of the ideal classes. -/
private theorem tendsto_sub_one_mul_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑ c, completedPartialZeta (rep c) s) (𝓝[≠] 1)
      (𝓝 (classNumber K * (2 * mellinConstant K) : ℂ)) := by
  simp_rw [Finset.mul_sum]
  convert tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta (rep c)
  simp [classNumber]

/-- The residue at `s = 0` of the sum of the completed partial zeta functions of a system of
representatives of the ideal classes. -/
private theorem tendsto_mul_sum_completedPartialZeta_zero
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * ∑ c, completedPartialZeta (rep c) s) (𝓝[≠] 0)
      (𝓝 (-(classNumber K * (2 * mellinConstant K)) : ℂ)) := by
  simp_rw [Finset.mul_sum]
  convert tendsto_finsetSum Finset.univ fun c _ ↦ tendsto_mul_completedPartialZeta_zero (rep c)
  simp [classNumber]

/-- The sum of the completed partial zeta functions of a system of representatives of the ideal
classes is in meromorphic normal form on `ℂ`: it is analytic off `{0, 1}`, and at `0` and `1`
it has a pole, where every summand takes the normal-form value `0`. -/
private theorem meromorphicNFOn_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (∑ c, completedPartialZeta (rep c)) univ := by
  have hm : Meromorphic (∑ c, completedPartialZeta (rep c)) :=
    Meromorphic.sum fun c _ ↦ meromorphic_completedPartialZeta (rep c)
  have ha : (classNumber K * (2 * mellinConstant K) : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  intro z _
  by_cases h0 : z = 0
  · subst h0
    refine meromorphicNFAt_iff_analyticAt_or.mpr (Or.inr ⟨hm 0, ?_, by simp⟩)
    rw [(hm 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul (neg_ne_zero.mpr ha)
      (by simpa only [sub_zero, smul_eq_mul, Finset.sum_apply] using
        tendsto_mul_sum_completedPartialZeta_zero rep)]
    decide
  by_cases h1 : z = 1
  · subst h1
    refine meromorphicNFAt_iff_analyticAt_or.mpr (Or.inr ⟨hm 1, ?_, by simp⟩)
    rw [(hm 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
      (by simpa only [smul_eq_mul, Finset.sum_apply] using
        tendsto_sub_one_mul_sum_completedPartialZeta rep)]
    decide
  exact (Finset.analyticAt_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1)
    |>.meromorphicNFAt

/-- **`Λ_K` is the sum of the completed partial zeta functions over the ideal classes**: for any
system of representatives `rep` of `ClassGroup (𝓞 K)`, `Λ_K = ∑_c Z(rep c, ·)`, as functions on
`ℂ` (both sides take the value `0` at the poles `0` and `1`). -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) :
    completedDedekindZeta K = ∑ c, completedPartialZeta (rep c) :=
  meromorphicContinuation_eq (meromorphicNFOn_sum_completedPartialZeta rep) fun s hs ↦ by
    rw [Finset.sum_apply]
    exact sum_completedPartialZeta_eq_mul_dedekindZeta hrep hs

end ClassSum

/-! ### Basic properties -/

/-- `completedDedekindZeta K` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedDedekindZeta : MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedDedekindZeta K` is meromorphic on `ℂ`. -/
@[fun_prop]
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

/-- There is a system of representatives of the ideal classes, through which
`completedDedekindZeta_eq_sum_completedPartialZeta` applies. -/
theorem exists_completedDedekindZeta_eq_sum :
    ∃ rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (∀ c, ClassGroup.mk K (rep c) = c) ∧
        completedDedekindZeta K = ∑ c, completedPartialZeta (rep c) := by
  choose J hJ using ClassGroup.mk0_surjective (R := 𝓞 K)
  have hrep : ∀ c, ClassGroup.mk K (FractionalIdeal.mk0 K (J c)) = c := fun c ↦ by
    rw [ClassGroup.mk_mk0, hJ]
  exact ⟨_, hrep, completedDedekindZeta_eq_sum_completedPartialZeta _ hrep⟩

/-- **Agreement on `Re s > 1`**: there,
`Λ_K(s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq_mul_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  obtain ⟨rep, hrep, h⟩ := exists_completedDedekindZeta_eq_sum K
  rw [h, Finset.sum_apply]
  exact sum_completedPartialZeta_eq_mul_dedekindZeta hrep hs

open scoped ComplexConjugate in
/-- The completed Dedekind zeta function commutes with complex conjugation, including at its
poles where both representatives have the canonical value zero. -/
@[simp] theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  have h : conj ∘ completedDedekindZeta K ∘ conj = completedDedekindZeta K := by
    apply eq_of_meromorphicNFOn_of_eqOn_halfPlane
      (meromorphicNFOn_conj_conj_iff.mpr (by simpa using meromorphicNFOn_completedDedekindZeta K))
      (meromorphicNFOn_completedDedekindZeta K) (σ := 1)
    intro z hz
    have hz' : 1 < (conj z).re := by simpa only [conj_re] using Set.mem_ofPred.mp hz
    have hD := ofReal_cpow_conj (r := ((discr K).natAbs : ℝ)) (by positivity) (z / 2)
    rw [ofReal_natCast, map_div₀, map_ofNat] at hD
    simp only [Function.comp_apply, completedDedekindZeta_eq_mul_dedekindZeta K hz',
      completedDedekindZeta_eq_mul_dedekindZeta K hz, Int.abs_eq_natAbs, Int.cast_natCast,
      dedekindZeta_conj, Gammaℝ_conj, Gammaℂ_conj, hD, map_mul, map_pow, conj_conj]
  simpa only [Function.comp_apply, conj_conj] using (congrFun h (conj s)).symm

/-! ### Regularity, poles, and residues -/

/-- `completedDedekindZeta K` is analytic away from `s = 0` and `s = 1`. -/
@[fun_prop]
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  obtain ⟨rep, -, h⟩ := exists_completedDedekindZeta_eq_sum K
  rw [h]
  exact Finset.analyticAt_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1

/-- The common absolute value `2 ^ (r₁ + r₂) h R / w` of the residues of `Λ_K` is `h` times the
residue `2 a₀` of each completed partial zeta function. -/
private theorem classNumber_mul_two_mul_mellinConstant :
    (classNumber K * (2 * mellinConstant K) : ℂ) =
      (2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
        torsionOrder K : ℝ) := by
  rw [mellinConstant_def, ← Nat.sub_add_cancel (nrRealPlaces_add_nrComplexPlaces_pos K), pow_succ]
  push_cast
  ring

/-- **Residue of `Λ_K` at `s = 1`**:
`lim_{s → 1} (s - 1) Λ_K(s) = 2 ^ (r₁ + r₂) h R / w`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
        torsionOrder K : ℝ)) := by
  obtain ⟨rep, -, h⟩ := exists_completedDedekindZeta_eq_sum K
  simpa only [h, Finset.sum_apply, classNumber_mul_two_mul_mellinConstant] using
    tendsto_sub_one_mul_sum_completedPartialZeta rep

/-- **Residue of `Λ_K` at `s = 0`**:
`lim_{s → 0} s Λ_K(s) = -2 ^ (r₁ + r₂) h R / w`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
        torsionOrder K : ℝ) : ℂ)) := by
  obtain ⟨rep, -, h⟩ := exists_completedDedekindZeta_eq_sum K
  simpa only [h, Finset.sum_apply, classNumber_mul_two_mul_mellinConstant] using
    tendsto_mul_sum_completedPartialZeta_zero rep

/-- The residues `± 2 ^ (r₁ + r₂) h R / w` of `Λ_K` are nonzero. -/
private theorem residue_completedDedekindZeta_ne_zero :
    ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
        torsionOrder K : ℝ) : ℂ) ≠ 0 := by
  have := regulator_pos K
  have := classNumber_pos K
  have : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (torsionOrder_pos K)
  exact ofReal_ne_zero.mpr (by positivity)

/-- `completedDedekindZeta K` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) :=
  (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (residue_completedDedekindZeta_ne_zero K) (tendsto_sub_one_mul_completedDedekindZeta K)

/-- `completedDedekindZeta K` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) :=
  (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr (residue_completedDedekindZeta_ne_zero K))
    (by simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K)

/-- `completedDedekindZeta K` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedDedekindZeta_iff {s : ℂ} :
    AnalyticAt ℂ (completedDedekindZeta K) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedDedekindZeta K h0 h1⟩
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedDedekindZeta_zero] at hnonneg
    exact absurd hnonneg (by decide)
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedDedekindZeta_one] at hnonneg
    exact absurd hnonneg (by decide)

/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedDedekindZeta_zero : completedDedekindZeta K 0 = 0 := by
  obtain ⟨rep, -, h⟩ := exists_completedDedekindZeta_eq_sum K
  simp [h]

/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedDedekindZeta_one : completedDedekindZeta K 1 = 0 := by
  obtain ⟨rep, -, h⟩ := exists_completedDedekindZeta_eq_sum K
  simp [h]

/-! ### Pole-cleared completion -/

open _root_.NumberField.mixedEmbedding in
/-- The pole-cleared Dedekind completion is the sum of the pole-cleared Mellin completions
of the lattices of any system of ideal class representatives, including at `0` and `1`. -/
theorem toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ =
      ∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c)) := by
  classical
  have hm : Meromorphic (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) := by fun_prop
  have hd : Differentiable ℂ (∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c))) :=
    Differentiable.sum fun c _ ↦ differentiable_mellinKernelEntireCompletion hD _
  ext z
  have hne (w : ℂ) : ∀ᶠ s in 𝓝[≠] z, s ≠ w := by
    by_cases h : z = w
    · subst w
      exact self_mem_nhdsWithin
    · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
  -- Compare the punctured germs: the finite sum gives the analytic value even at a pole.
  have hgerm : (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) =ᶠ[𝓝[≠] z]
      ∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c)) := by
    filter_upwards [hne 0, hne 1] with s hs₀ hs₁
    rw [completedDedekindZeta_eq_sum_completedPartialZeta rep hrep, Finset.sum_apply,
      Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [mellinKernelEntireCompletion_eq_mul_Λ hD _ hs₀ hs₁,
      completedPartialZeta_eq_mellinKernelFEPair_Λ hD (rep c) hs₀ hs₁]
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ (mem_univ z)
  exact ((hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hd.analyticAt z).meromorphicNFAt).mp
    ((hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).trans hgerm)).eq_of_nhds

/-- The repaired product `s(s - 1) Λ_K(s)` is entire. -/
@[fun_prop]
theorem differentiable_toMeromorphicNFOn_mul_completedDedekindZeta :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep]
  exact Differentiable.sum fun c _ ↦ differentiable_mellinKernelEntireCompletion _ _

/-- The repaired product `s(s - 1) Λ_K(s)` at `0` equals the residue of `Λ_K` at `1`. -/
@[simp]
theorem toMeromorphicNFOn_mul_completedDedekindZeta_zero :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ 0 =
      classNumber K * (2 * mellinConstant K) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep, Finset.sum_apply]
  simp [classNumber]

/-- The repaired product `s(s - 1) Λ_K(s)` at `1` equals the residue of `Λ_K` at `1`. -/
@[simp]
theorem toMeromorphicNFOn_mul_completedDedekindZeta_one :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ 1 =
      classNumber K * (2 * mellinConstant K) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep, Finset.sum_apply]
  simp [classNumber]

/-! ### Functional equation -/

/-- **The functional equation of the completed Dedekind zeta function**:
`Λ_K(1 - s) = Λ_K(s)` for every `s : ℂ` (at the poles `0` and `1` both sides are `0`). -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  obtain ⟨rep, hrep, h⟩ := exists_completedDedekindZeta_eq_sum K
  -- The trace dual `I ↦ I^∨ = 𝔡⁻¹ I⁻¹` acts on classes by `c ↦ [𝔡⁻¹] c⁻¹`, so the duals of the
  -- representatives of the classes `c⁻¹ [𝔡⁻¹]` represent the classes `c`.
  let d := ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  have hrep' : ∀ c, ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (rep (c⁻¹ * d))) = c := by
    intro c
    rw [FractionalIdeal.dualEquiv_eq_mul_inv, map_mul, map_inv, hrep, mul_inv_rev, inv_inv,
      ← mul_assoc, mul_inv_cancel, one_mul]
  rw [congrFun h (1 - s), congrFun (completedDedekindZeta_eq_sum_completedPartialZeta _ hrep') s,
    Finset.sum_apply, Finset.sum_apply]
  simp_rw [completedPartialZeta_one_sub]
  exact (Equiv.sum_comp ((Equiv.inv _).trans (Equiv.mulRight d))
    fun c ↦ completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ (rep c)) s).symm

/-! ### The continued Dedekind zeta function -/

section Continued

/-- The reciprocal `|d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂` of the archimedean factor of
`Λ_K`. -/
private def invArchFactor (s : ℂ) : ℂ :=
  ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ nrComplexPlaces K

/-- The reciprocal of the archimedean factor is entire. -/
private theorem analyticAt_invArchFactor (s : ℂ) : AnalyticAt ℂ (invArchFactor K) s := by
  have hd : ((|discr K| : ℤ) : ℂ) ∈ slitPlane := by
    rw [← ofReal_intCast]
    exact ofReal_mem_slitPlane.mpr (by exact_mod_cast abs_pos.mpr (discr_ne_zero K))
  exact ((AnalyticAt.cpow analyticAt_const (by fun_prop) hd).mul
    ((differentiable_Gammaℝ_inv.analyticAt s).pow _)).mul
    ((differentiable_Gammaℂ_inv.analyticAt s).pow _)

/-- On `Re s > 0` the archimedean factor has no zeros, so it cancels against its reciprocal. -/
private theorem invArchFactor_mul {s : ℂ} (hs : 0 < s.re) :
    invArchFactor K s * (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K) = 1 := by
  have hd : ((|discr K| : ℤ) : ℂ) ^ (s / 2) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K))))
  have hR := Gammaℝ_ne_zero_of_re_pos hs
  have hC := Gammaℂ_ne_zero_of_re_pos hs
  rw [invArchFactor, neg_div, cpow_neg, inv_pow, inv_pow]
  field_simp

/-- The reciprocal of the archimedean factor vanishes at `s = 0`, where `Γ_ℝ` and `Γ_ℂ` have
poles and `K` has at least one infinite place. -/
private theorem invArchFactor_zero : invArchFactor K 0 = 0 := by
  have hR : (Gammaℝ 0)⁻¹ = 0 := by simp [Gammaℝ_def]
  have hC : (Gammaℂ 0)⁻¹ = 0 := by simp [Gammaℂ_def]
  rw [invArchFactor, hR, hC]
  rcases Nat.eq_zero_or_pos (nrRealPlaces K) with h | h
  · have := nrRealPlaces_add_nrComplexPlaces_pos K
    rw [zero_pow (by omega : nrComplexPlaces K ≠ 0), mul_zero]
  · rw [zero_pow h.ne', mul_zero, zero_mul]

/-- The reciprocal of the archimedean factor times `Λ_K` is meromorphic on `ℂ`. -/
private theorem meromorphic_invArchFactor_mul :
    Meromorphic (invArchFactor K * completedDedekindZeta K) :=
  fun s ↦ (analyticAt_invArchFactor K s).meromorphicAt.mul (meromorphic_completedDedekindZeta K s)

/-- `dedekindZetaC K` is the normal form of the reciprocal of the archimedean factor times
`Λ_K`. -/
private theorem dedekindZetaC_eq_toMeromorphicNFOn :
    dedekindZetaC K = toMeromorphicNFOn (invArchFactor K * completedDedekindZeta K) univ := by
  rw [dedekindZetaC_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_invArchFactor_mul K)
    (fun s hs ↦ ?_) fun s hs ↦ ?_
  · have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact (analyticAt_invArchFactor K s).mul (analyticAt_completedDedekindZeta K h0 h1)
  · rw [Pi.mul_apply, completedDedekindZeta_eq_mul_dedekindZeta K hs, ← mul_assoc,
      invArchFactor_mul K (zero_lt_one.trans hs), one_mul]

/-- **`ζ_K` is the reciprocal of the archimedean factor times `Λ_K`**: away from `s = 0` and
`s = 1`, `ζ_K(s) = |d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂ Λ_K(s)`, where `Γ_ℝ⁻¹` and `Γ_ℂ⁻¹`
are entire. Together with `completedDedekindZeta_one_sub` this relates the values of `ζ_K` at
`s` and `1 - s`. -/
theorem dedekindZetaC_eq_mul_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    dedekindZetaC K s = ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
      (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s := by
  rw [dedekindZetaC_eq_toMeromorphicNFOn, toMeromorphicNFOn_apply_of_analyticAt
    (meromorphic_invArchFactor_mul K)
    ((analyticAt_invArchFactor K s).mul (analyticAt_completedDedekindZeta K h0 h1)),
    Pi.mul_apply, invArchFactor]

/-- **Agreement on `Re s > 1`**: `dedekindZetaC K` agrees with Mathlib's Dirichlet series
`NumberField.dedekindZeta K` there, since `ζ_K` has a meromorphic continuation to `ℂ`. -/
theorem dedekindZetaC_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [dedekindZetaC_eq_mul_completedDedekindZeta K h0 h1,
    completedDedekindZeta_eq_mul_dedekindZeta K hs, ← mul_assoc, ← invArchFactor,
    invArchFactor_mul K (zero_lt_one.trans hs), one_mul]

/-- **`ζ_K` is analytic away from `s = 1`.** At `s = 0` the simple pole of `Λ_K` is cancelled by
the zero of the reciprocal archimedean factor. -/
@[fun_prop]
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (dedekindZetaC K) s := by
  rw [dedekindZetaC_eq_toMeromorphicNFOn, ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn (meromorphic_invArchFactor_mul K).meromorphicOn
      (mem_univ s)]
  by_cases h0 : s = 0
  · subst h0
    have hpos : 0 < meromorphicOrderAt (invArchFactor K) 0 := by
      have h := (analyticAt_invArchFactor K 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [invArchFactor_zero] at h
      exact (tendsto_zero_iff_meromorphicOrderAt_pos
        (analyticAt_invArchFactor K 0).meromorphicAt).mp h
    rw [meromorphicOrderAt_mul (analyticAt_invArchFactor K 0).meromorphicAt
      (meromorphic_completedDedekindZeta K 0), meromorphicOrderAt_completedDedekindZeta_zero]
    generalize meromorphicOrderAt (invArchFactor K) 0 = n at hpos ⊢
    induction n using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      norm_cast at hpos ⊢
      omega
  · exact ((analyticAt_invArchFactor K s).mul
      (analyticAt_completedDedekindZeta K h0 hs)).meromorphicOrderAt_nonneg

/-- Any function analytic off `1` and agreeing with the Dedekind zeta series on `Re s > 1`
agrees with the continued Dedekind zeta function off `1`. -/
theorem eqOn_dedekindZetaC_of_eqOn_dedekindZeta {Z : ℂ → ℂ}
    (hZ : ∀ z ≠ 1, AnalyticAt ℂ Z z)
    (hseries : Set.EqOn Z (dedekindZeta K) {z | 1 < z.re}) :
    Set.EqOn Z (dedekindZetaC K) ({1}ᶜ : Set ℂ) := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z hz ↦ hZ z (Set.mem_compl_singleton_iff.mp hz))
    (fun _ hz ↦ analyticAt_dedekindZetaC K (Set.mem_compl_singleton_iff.mp hz))
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
    (z₀ := 2) (by norm_num) ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)] with z hz
  exact (hseries hz).trans (dedekindZetaC_eq_dedekindZeta K hz).symm

/-- **The analytic class number formula for the continued Dedekind zeta function**:
`lim_{s → 1} (s - 1) ζ_K(s) = 2 ^ r₁ (2π) ^ r₂ h R / (w √|d_K|)`, Mathlib's
`NumberField.dedekindZeta_residue K`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have hlim := ((analyticAt_invArchFactor K 1).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hres : invArchFactor K 1 * ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K *
      regulator K / torsionOrder K : ℝ) : ℂ) = (dedekindZeta_residue K : ℂ) := by
    have hd : ((|discr K| : ℤ) : ℂ) = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [← Int.cast_abs, ofReal_intCast]
    rw [invArchFactor, hd, ofReal_cpow_neg_one_half (abs_nonneg _), Gammaℝ_one, Gammaℂ_one,
      one_div, inv_inv, dedekindZeta_residue_def]
    push_cast
    ring
  rw [← hres]
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero), self_mem_nhdsWithin]
    with s hs0 hs1
  rw [dedekindZetaC_eq_mul_completedDedekindZeta K hs0 hs1, ← invArchFactor]
  ring

/-- `ζ_K` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) :=
  (meromorphic_dedekindZetaC K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (ofReal_ne_zero.mpr (dedekindZeta_residue_pos K).ne') (tendsto_sub_one_mul_dedekindZetaC K)

/-- `ζ_K` has finite order at every point, since it has a simple pole at `1` and therefore is
not the zero meromorphic function. -/
theorem meromorphicOrderAt_dedekindZetaC_ne_top (z : ℂ) :
    meromorphicOrderAt (dedekindZetaC K) z ≠ ⊤ :=
  ((meromorphic_dedekindZetaC K).exists_meromorphicOrderAt_ne_top_iff_forall.mp
    ⟨1, by simp [meromorphicOrderAt_dedekindZetaC_one]⟩) z

/-- `ζ_K` is analytic at `s` if and only if `s ≠ 1`. -/
@[simp]
theorem analyticAt_dedekindZetaC_iff {s : ℂ} : AnalyticAt ℂ (dedekindZetaC K) s ↔ s ≠ 1 := by
  refine ⟨fun han ↦ ?_, analyticAt_dedekindZetaC K⟩
  rintro rfl
  have hnonneg := han.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_dedekindZetaC_one] at hnonneg
  exact absurd hnonneg (by decide)

end Continued

end TauCeti.LFunctions
