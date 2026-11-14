/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Operator.SNumbers.Uniqueness

/-!
# Hilbert numbers

The `n`-th Hilbert number of a bounded operator `T : E →L[𝕜] F` over `ℝ` or `ℂ` is
`hₙ(T) = sup {aₙ(B ∘ T ∘ A) : A : ℓ₂ →L[𝕜] E, B : F →L[𝕜] ℓ₂, ‖A‖ ≤ 1, ‖B‖ ≤ 1}`, the supremum of
the approximation numbers of all factorizations of `T` between copies of `ℓ₂ = lp (fun _ : ℕ ↦ 𝕜) 2`
by contractions. Equivalently, `hₙ(T)` is the supremum of `aₙ(B ∘ T ∘ A) / (‖B‖ ‖A‖)` over nonzero
operators `A` and `B` (`ContinuousLinearMap.hilbertNumber_eq_iSup_div`). The indexing is zero-based,
so `h₀(T) = ‖T‖`.

Monotonicity, rank vanishing, mixed-index additivity `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`, scalar
homogeneity and the two-sided ideal inequality pass directly through the supremum from the
corresponding laws for approximation numbers. For `h₀(T) = ‖T‖`, a rank-one coordinate map from
`ℓ₂` onto a normalized vector in `E` and a Hahn–Banach norming functional into the zeroth coordinate
of `ℓ₂` realize the norm of each image vector.

On operators from a complete inner product space into an inner product space, `hₙ(T) = aₙ(T)`
(`ContinuousLinearMap.hilbertNumber_eq_singularValue`): the scalar factorization below `aₙ(T)`
embeds into the first `n + 1` coordinates of `ℓ₂`. In particular, `hₙ(id) = 1` on
`EuclideanSpace 𝕜 (Fin (n + 1))`, so the Hilbert numbers form an s-number sequence
(`TauCeti.SNumbers.isSNumberSequence_hilbert`). Combining uniqueness of s-number sequences on `ℓ₂`
with the ideal inequality shows `hₙ(T) ≤ s T n` for every s-number sequence `s`
(`TauCeti.SNumbers.IsSNumberSequence.hilbertNumber_le`), making the Hilbert numbers the smallest
s-number sequence.

In `ContinuousLinearMap`, the general calculus assumes only seminormed spaces across independent
universes.

## Main declarations

* `ContinuousLinearMap.hilbertNumber`: the Hilbert numbers `hₙ(T)`.
* `ContinuousLinearMap.hilbertNumber_eq_iSup_div`: the ratio formula
  `hₙ(T) = sup_{A ≠ 0, B ≠ 0} aₙ(B T A) / (‖B‖ ‖A‖)`.
* `ContinuousLinearMap.hilbertNumber_zero`: `h₀(T) = ‖T‖`.
* `ContinuousLinearMap.hilbertNumber_add_index_le`: `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`.
* `ContinuousLinearMap.hilbertNumber_comp_comp_le`: `hₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖`.
* `ContinuousLinearMap.hilbertNumber_eq_singularValue`: `hₙ(T) = aₙ(T)` on operators from a
  complete inner product space into an inner product space.
* `ContinuousLinearMap.singularValue_comp_comp_le_mul_hilbertNumber`:
  `aₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖` for test maps between arbitrary Hilbert spaces.
* `TauCeti.SNumbers.isSNumberSequence_hilbert`: the Hilbert numbers form an s-number sequence.
* `TauCeti.SNumbers.IsSNumberSequence.hilbertNumber_le`: `hₙ(T) ≤ s T n` for every s-number
  sequence `s`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §§4–5.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §§2.4, 2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Hilbert.lean` and `SNumbers/Uniqueness.lean`: an earlier Lean formalization of the
  Hilbert numbers and their minimality among s-number sequences.
-/

public section

open Module
open scoped NNReal

namespace ContinuousLinearMap

section Seminormed

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `n`-th Hilbert number `hₙ(T)` of a bounded linear map `T`: the supremum of the
approximation numbers `aₙ(B ∘ T ∘ A)` over all contractions `A : ℓ₂ →L[𝕜] E` and `B : F →L[𝕜] ℓ₂`,
where `ℓ₂ = lp (fun _ : ℕ ↦ 𝕜) 2`. The indexing is zero-based, so `h₀(T) = ‖T‖`
(`hilbertNumber_zero`). -/
noncomputable def hilbertNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨆ A : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // ‖A‖ ≤ 1},
    ⨆ B : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // ‖B‖ ≤ 1},
      (B.1 ∘L T ∘L A.1).singularValue n

/-- `hₙ(T)` is the supremum of `aₙ(B ∘ T ∘ A)` over contractions `A : ℓ₂ →L[𝕜] E` and
`B : F →L[𝕜] ℓ₂`. -/
theorem hilbertNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ A : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // ‖A‖ ≤ 1},
        ⨆ B : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // ‖B‖ ≤ 1},
          (B.1 ∘L T ∘L A.1).singularValue n := (rfl)

private theorem singularValue_comp_comp_le_of_le_one (T : E →L[𝕜] F)
    {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E} (hA : ‖A‖ ≤ 1)
    {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2} (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ T.singularValue n := by
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  calc (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.singularValue n * ‖A‖₊ :=
        B.singularValue_comp_comp_le T A n
    _ ≤ 1 * T.singularValue n * 1 := by gcongr
    _ = T.singularValue n := by simp

private theorem bddAbove_inner (T : E →L[𝕜] F)
    (A : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // ‖A‖ ≤ 1}) (n : ℕ) :
    BddAbove (Set.range fun B : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // ‖B‖ ≤ 1} ↦
      (B.1 ∘L T ∘L A.1).singularValue n) :=
  ⟨T.singularValue n, Set.forall_mem_range.mpr fun B ↦
    singularValue_comp_comp_le_of_le_one T A.2 B.2 n⟩

private theorem bddAbove_outer (T : E →L[𝕜] F) (n : ℕ) :
    BddAbove (Set.range fun A : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // ‖A‖ ≤ 1} ↦
      ⨆ B : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // ‖B‖ ≤ 1},
        (B.1 ∘L T ∘L A.1).singularValue n) :=
  ⟨T.singularValue n, Set.forall_mem_range.mpr fun A ↦
    ciSup_le' fun B ↦ singularValue_comp_comp_le_of_le_one T A.2 B.2 n⟩

/-- **Lower bound from contractions.** Every pair of contractions `A : ℓ₂ →L[𝕜] E` and
`B : F →L[𝕜] ℓ₂` bounds `hₙ(T)` below by `aₙ(B ∘ T ∘ A)`. -/
theorem le_hilbertNumber (T : E →L[𝕜] F)
    {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E} {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ T.hilbertNumber n := by
  rw [hilbertNumber_def]
  exact (le_ciSup (bddAbove_inner T ⟨A, hA⟩ n) ⟨B, hB⟩).trans
    (le_ciSup (bddAbove_outer T n) ⟨A, hA⟩)

/-- **Upper-bound characterization.** `hₙ(T) ≤ c` exactly when `aₙ(B ∘ T ∘ A) ≤ c` for all
contractions `A : ℓ₂ →L[𝕜] E` and `B : F →L[𝕜] ℓ₂`. -/
theorem hilbertNumber_le_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    T.hilbertNumber n ≤ c ↔
      ∀ (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E), ‖A‖ ≤ 1 →
        ∀ (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2), ‖B‖ ≤ 1 →
          (B ∘L T ∘L A).singularValue n ≤ c := by
  refine ⟨fun h A hA B hB ↦ (T.le_hilbertNumber hA hB n).trans h, fun h ↦ ?_⟩
  rw [hilbertNumber_def]
  exact ciSup_le' fun A ↦ ciSup_le' fun B ↦ h A.1 A.2 B.1 B.2

/-- **Supremum formula.** `hₙ(T)` is the least upper bound of the approximation numbers
`aₙ(B ∘ T ∘ A)` as `A : ℓ₂ →L[𝕜] E` and `B : F →L[𝕜] ℓ₂` range over contractions. -/
theorem isLUB_hilbertNumber (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB {x | ∃ (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E) (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ (B ∘L T ∘L A).singularValue n = x} (T.hilbertNumber n) := by
  refine ⟨?_, fun c hc ↦ hilbertNumber_le_iff.mpr fun A hA B hB ↦ hc ⟨A, B, hA, hB, rfl⟩⟩
  rintro _ ⟨A, B, hA, hB, rfl⟩
  exact T.le_hilbertNumber hA hB n

/-- **Near-optimal contractions.** If `c < hₙ(T)`, some contractions `A : ℓ₂ →L[𝕜] E` and
`B : F →L[𝕜] ℓ₂` satisfy `c < aₙ(B ∘ T ∘ A)`. -/
theorem exists_lt_singularValue_comp_comp_of_lt_hilbertNumber
    {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} (h : c < T.hilbertNumber n) :
    ∃ (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E) (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ c < (B ∘L T ∘L A).singularValue n := by
  obtain ⟨A, hA, B, hB, hlt⟩ :
      ∃ (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E), ‖A‖ ≤ 1 ∧
        ∃ (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2), ‖B‖ ≤ 1 ∧ c < (B ∘L T ∘L A).singularValue n := by
    simpa using mt hilbertNumber_le_iff.mpr h.not_ge
  exact ⟨A, B, hA, hB, hlt⟩

/-- Scaling bound for `ℓ₂` test operators: `aₙ(B ∘ T ∘ A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
private theorem singularValue_comp_comp_le_mul_hilbertNumber_lp
    (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) (T : E →L[𝕜] F)
    (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by
  rcases eq_or_ne ‖A‖₊ 0 with hA0 | hA0
  · exact ((B.singularValue_comp_comp_le T A n).trans_eq (by simp [hA0])).trans bot_le
  rcases eq_or_ne ‖B‖₊ 0 with hB0 | hB0
  · exact ((B.singularValue_comp_comp_le T A n).trans_eq (by simp [hB0])).trans bot_le
  have hA_pos : 0 < ‖A‖ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hA0)
  have hB_pos : 0 < ‖B‖ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hB0)
  set A' : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E := ((‖A‖⁻¹ : ℝ) : 𝕜) • A
  set B' : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 := ((‖B‖⁻¹ : ℝ) : 𝕜) • B
  have hA' : ‖A'‖ ≤ 1 := by simp [A', norm_smul, inv_mul_cancel₀ hA_pos.ne']
  have hB' : ‖B'‖ ≤ 1 := by simp [B', norm_smul, inv_mul_cancel₀ hB_pos.ne']
  have hle := T.le_hilbertNumber hA' hB' n
  have hsmul : B' ∘L T ∘L A' = (((‖B‖⁻¹ : ℝ) : 𝕜) * ((‖A‖⁻¹ : ℝ) : 𝕜)) • (B ∘L T ∘L A) := by
    simp [A', B', smul_comp, smul_smul, mul_comm]
  have hinv : ‖(((‖B‖⁻¹ : ℝ) : 𝕜) * ((‖A‖⁻¹ : ℝ) : 𝕜))‖₊ = (‖B‖₊ * ‖A‖₊)⁻¹ := by
    apply NNReal.coe_injective
    simp [mul_comm]
  rw [hsmul, singularValue_smul, hinv] at hle
  calc (B ∘L T ∘L A).singularValue n =
        (‖B‖₊ * ‖A‖₊) * ((‖B‖₊ * ‖A‖₊)⁻¹ * (B ∘L T ∘L A).singularValue n) := by
          rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hB0 hA0), one_mul]
    _ ≤ (‖B‖₊ * ‖A‖₊) * T.hilbertNumber n := by gcongr
    _ = ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by ring

/-- **Ratio formula.** The `n`-th Hilbert number equals the supremum of
`aₙ(B ∘ T ∘ A) / (‖B‖ ‖A‖)` over all nonzero bounded maps `A : ℓ₂ →L[𝕜] E` and `B : F →L[𝕜] ℓ₂`. -/
theorem hilbertNumber_eq_iSup_div (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ A : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // A ≠ 0},
        ⨆ B : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // B ≠ 0},
          (B.1 ∘L T ∘L A.1).singularValue n / (‖B.1‖₊ * ‖A.1‖₊) := by
  have hdiv_le (A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E) (B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) :
      (B ∘L T ∘L A).singularValue n / (‖B‖₊ * ‖A‖₊) ≤ T.hilbertNumber n := by
    rcases eq_or_ne (‖B‖₊ * ‖A‖₊) 0 with h0 | h0
    · simp [h0]
    refine (div_le_iff₀ (pos_iff_ne_zero.mpr h0)).mpr ?_
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      singularValue_comp_comp_le_mul_hilbertNumber_lp B T A n
  refine le_antisymm (hilbertNumber_le_iff.mpr fun A hA B hB ↦ ?_)
    (ciSup_le' fun A ↦ ciSup_le' fun B ↦ hdiv_le A.1 B.1)
  rcases eq_or_ne ‖A‖₊ 0 with hA0 | hA0
  · exact ((B.singularValue_comp_comp_le T A n).trans_eq (by simp [hA0])).trans bot_le
  rcases eq_or_ne ‖B‖₊ 0 with hB0 | hB0
  · exact ((B.singularValue_comp_comp_le T A n).trans_eq (by simp [hB0])).trans bot_le
  have hA_ne : A ≠ 0 := fun h ↦ hA0 (by simp [h])
  have hB_ne : B ≠ 0 := fun h ↦ hB0 (by simp [h])
  have hBA_le : ‖B‖₊ * ‖A‖₊ ≤ 1 := by
    have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
    have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
    simpa using mul_le_mul' hB' hA'
  have hle_div : (B ∘L T ∘L A).singularValue n ≤
      (B ∘L T ∘L A).singularValue n / (‖B‖₊ * ‖A‖₊) := by
    rw [le_div_iff₀ (pos_iff_ne_zero.mpr (mul_ne_zero hB0 hA0))]
    exact mul_le_of_le_one_right' hBA_le
  have hbdd_in : BddAbove (Set.range fun B' : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // B ≠ 0} ↦
      (B'.1 ∘L T ∘L A).singularValue n / (‖B'.1‖₊ * ‖A‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun B' ↦ hdiv_le A B'.1⟩
  have hbdd_out : BddAbove (Set.range fun A' : {A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E // A ≠ 0} ↦
      ⨆ B' : {B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 // B ≠ 0},
        (B'.1 ∘L T ∘L A'.1).singularValue n / (‖B'.1‖₊ * ‖A'.1‖₊)) :=
    ⟨T.hilbertNumber n,
      Set.forall_mem_range.mpr fun A' ↦ ciSup_le' fun B' ↦ hdiv_le A'.1 B'.1⟩
  exact hle_div.trans ((le_ciSup hbdd_in ⟨B, hB_ne⟩).trans (le_ciSup hbdd_out ⟨A, hA_ne⟩))

/-- Every Hilbert number is at most the corresponding approximation number. -/
theorem hilbertNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n ≤ T.singularValue n :=
  hilbertNumber_le_iff.mpr fun _ hA _ hB ↦ singularValue_comp_comp_le_of_le_one T hA hB n

/-- The Hilbert numbers are bounded by the operator norm. -/
theorem hilbertNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.hilbertNumber n ≤ ‖T‖₊ :=
  (T.hilbertNumber_le_singularValue n).trans (T.singularValue_le_nnnorm n)

/-- **Zeroth Hilbert number.** `h₀(T) = ‖T‖`, testing each vector via a rank-one coordinate map
from `ℓ₂` and a Hahn–Banach norming functional into `ℓ₂`. -/
@[simp]
theorem hilbertNumber_zero (T : E →L[𝕜] F) : T.hilbertNumber 0 = ‖T‖₊ := by
  refine (T.hilbertNumber_le_nnnorm 0).antisymm (opNNNorm_le_bound _ _ fun x ↦ ?_)
  rcases eq_or_ne ‖x‖₊ 0 with hx0 | hx0
  · exact (T.le_opNNNorm x).trans_eq (by simp [hx0])
  have hx_pos : 0 < ‖x‖ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hx0)
  set u : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hu_norm : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ hx_pos.ne']
  set e₀ : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] 𝕜 := lp.evalCLM 𝕜 (fun _ : ℕ ↦ 𝕜) 2 0
  have he₀ : ‖e₀‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  set A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] E := e₀.smulRight u
  have hA : ‖A‖ ≤ 1 := by simpa [A, norm_smulRight_apply, hu_norm] using he₀
  obtain ⟨g, hg_norm, hgx⟩ := exists_dual_vector'' 𝕜 (T x)
  set ι₀ : 𝕜 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 := lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ 𝕜) 2 0
  have hι₀ : ‖ι₀‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun c ↦ by
    simp [ι₀, lp.norm_single zero_lt_two]
  set B : F →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 := ι₀ ∘L g
  have hB : ‖B‖ ≤ 1 := by
    calc ‖B‖ ≤ ‖ι₀‖ * ‖g‖ := ι₀.opNorm_comp_le g
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := mul_one 1
  set δ₀ : lp (fun _ : ℕ ↦ 𝕜) 2 := lp.single 2 0 (1 : 𝕜)
  have hδ₀ : ‖δ₀‖ = 1 := by simp [δ₀, lp.norm_single zero_lt_two]
  have heval : (B ∘L T ∘L A) δ₀ = ((‖x‖⁻¹ : ℝ) : 𝕜) • lp.single 2 0 (‖T x‖ : 𝕜) := by
    have hAδ : A δ₀ = u := by simp [A, e₀, lp.evalCLM, δ₀]
    simp [B, ι₀, hAδ, u, hgx]
  have hgain : ‖x‖⁻¹ * ‖T x‖ ≤ (T.hilbertNumber 0 : ℝ) := by
    calc ‖x‖⁻¹ * ‖T x‖ = ‖(B ∘L T ∘L A) δ₀‖ := by
          rw [heval, norm_smul, lp.norm_single zero_lt_two]
          simp
      _ ≤ ‖B ∘L T ∘L A‖ * ‖δ₀‖ := (B ∘L T ∘L A).le_opNorm δ₀
      _ = ((B ∘L T ∘L A).singularValue 0 : ℝ) := by simp [hδ₀]
      _ ≤ T.hilbertNumber 0 := by exact_mod_cast T.le_hilbertNumber hA hB 0
  have hbound : ‖T x‖ ≤ (T.hilbertNumber 0 : ℝ) * ‖x‖ := by
    simpa [mul_comm] using (inv_mul_le_iff₀ hx_pos).mp hgain
  exact_mod_cast hbound

/-- The Hilbert numbers form an antitone sequence. -/
theorem antitone_hilbertNumber (T : E →L[𝕜] F) : Antitone T.hilbertNumber :=
  fun _ _ hmn ↦ hilbertNumber_le_iff.mpr fun A hA B hB ↦
    ((B ∘L T ∘L A).antitone_singularValue hmn).trans (T.le_hilbertNumber hA hB _)

/-- The Hilbert numbers are bounded above by the operator norm. -/
theorem bddAbove_range_hilbertNumber (T : E →L[𝕜] F) : BddAbove (Set.range T.hilbertNumber) :=
  ⟨‖T‖₊, Set.forall_mem_range.mpr T.hilbertNumber_le_nnnorm⟩

/-- The supremum of the Hilbert numbers is the operator norm, attained at `h₀(T)`. -/
@[simp]
theorem iSup_hilbertNumber (T : E →L[𝕜] F) : ⨆ n, T.hilbertNumber n = ‖T‖₊ :=
  (ciSup_le T.hilbertNumber_le_nnnorm).antisymm
    (T.hilbertNumber_zero ▸ le_ciSup T.bddAbove_range_hilbertNumber 0)

/-- The Hilbert numbers of the zero map vanish. -/
@[simp]
theorem zero_hilbertNumber (n : ℕ) : (0 : E →L[𝕜] F).hilbertNumber n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).hilbertNumber_le_nnnorm n) bot_le

/-- **Vanishing from rank.** A bounded map of rank at most `n` has `hₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T.hilbertNumber n = 0 :=
  le_antisymm ((T.hilbertNumber_le_singularValue n).trans_eq
    (singularValue_eq_zero_of_rank_le hT)) bot_le

/-- **Dimension cutoff.** If the source has rank at most `n`, then `hₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_of_rank_domain_le (T : E →L[𝕜] F) {n : ℕ}
    (hE : Module.rank 𝕜 E ≤ n) : T.hilbertNumber n = 0 :=
  le_antisymm ((T.hilbertNumber_le_singularValue n).trans_eq
    (T.singularValue_eq_zero_of_rank_domain_le hE)) bot_le

/-- **Mixed-index additive inequality.** `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`. -/
theorem hilbertNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).hilbertNumber (m + n) ≤ S.hilbertNumber m + T.hilbertNumber n :=
  hilbertNumber_le_iff.mpr fun A hA B hB ↦ by
    have hcomp : B ∘L (S + T) ∘L A = B ∘L S ∘L A + B ∘L T ∘L A := by
      simp [add_comp, comp_add]
    rw [hcomp]
    exact ((B ∘L S ∘L A).singularValue_add_index_le (B ∘L T ∘L A) m n).trans
      (add_le_add (S.le_hilbertNumber hA hB m) (T.le_hilbertNumber hA hB n))

/-- **Perturbative triangle bound.** `hₙ(S + T) ≤ hₙ(S) + ‖T‖`. -/
theorem hilbertNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).hilbertNumber n ≤ S.hilbertNumber n + ‖T‖₊ := by
  simpa using S.hilbertNumber_add_index_le T n 0

/-- **Two-sided ideal inequality.** `hₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem hilbertNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ :=
  hilbertNumber_le_iff.mpr fun U hU V hV ↦ by
    have hU' : ‖U‖₊ ≤ 1 := by exact_mod_cast hU
    have hV' : ‖V‖₊ ≤ 1 := by exact_mod_cast hV
    have hVB : ‖V ∘L B‖₊ ≤ ‖B‖₊ :=
      (V.opNNNorm_comp_le B).trans (mul_le_of_le_one_left' hV')
    have hAU : ‖A ∘L U‖₊ ≤ ‖A‖₊ :=
      (A.opNNNorm_comp_le U).trans (mul_le_of_le_one_right' hU')
    have hassoc : V ∘L (B ∘L T ∘L A) ∘L U = (V ∘L B) ∘L T ∘L (A ∘L U) := rfl
    rw [hassoc]
    exact (singularValue_comp_comp_le_mul_hilbertNumber_lp (V ∘L B) T (A ∘L U) n).trans
      (by gcongr)

/-- Postcomposition scales Hilbert numbers by at most the operator norm. -/
theorem hilbertNumber_comp_le_left (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n := by
  have hid : ‖ContinuousLinearMap.id 𝕜 E‖₊ ≤ 1 := by exact_mod_cast norm_id_le
  calc (B ∘L T).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n * ‖ContinuousLinearMap.id 𝕜 E‖₊ := by
        simpa using B.hilbertNumber_comp_comp_le T (ContinuousLinearMap.id 𝕜 E) n
    _ ≤ ‖B‖₊ * T.hilbertNumber n := mul_le_of_le_one_right' hid

/-- Precomposition scales Hilbert numbers by at most the operator norm. -/
theorem hilbertNumber_comp_le_right (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (T ∘L A).hilbertNumber n ≤ T.hilbertNumber n * ‖A‖₊ := by
  have hid : ‖ContinuousLinearMap.id 𝕜 G‖₊ ≤ 1 := by exact_mod_cast norm_id_le
  calc (T ∘L A).hilbertNumber n ≤ ‖ContinuousLinearMap.id 𝕜 G‖₊ * T.hilbertNumber n * ‖A‖₊ := by
        simpa using (ContinuousLinearMap.id 𝕜 G).hilbertNumber_comp_comp_le T A n
    _ ≤ T.hilbertNumber n * ‖A‖₊ := by gcongr; exact mul_le_of_le_one_left' hid

/-- **Scalar homogeneity.** `hₙ(c T) = ‖c‖ hₙ(T)`. -/
@[simp]
theorem hilbertNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).hilbertNumber n = ‖c‖₊ * T.hilbertNumber n := by
  have hle (c : 𝕜) (T : E →L[𝕜] F) : (c • T).hilbertNumber n ≤ ‖c‖₊ * T.hilbertNumber n :=
    hilbertNumber_le_iff.mpr fun A hA B hB ↦ by
      have hsmul : B ∘L (c • T) ∘L A = c • (B ∘L T ∘L A) := by simp [smul_comp]
      rw [hsmul, singularValue_smul]
      gcongr
      exact T.le_hilbertNumber hA hB n
  refine (hle c T).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ * T.hilbertNumber n = ‖c‖₊ * (c⁻¹ • c • T).hilbertNumber n := by
        rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * (c • T).hilbertNumber n) := by gcongr; exact hle _ _
    _ = (c • T).hilbertNumber n := by
        rw [← mul_assoc, nnNorm_inv, mul_inv_cancel₀ (nnNorm_ne_zero_iff.mpr hc), one_mul]

/-- Negation leaves every Hilbert number unchanged. -/
@[simp]
theorem hilbertNumber_neg (T : E →L[𝕜] F) (n : ℕ) : (-T).hilbertNumber n = T.hilbertNumber n := by
  simpa using hilbertNumber_smul (-1 : 𝕜) T n

end Seminormed

section HilbertSpace

variable {𝕜 E F H₁ H₂ : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- `EuclideanSpace 𝕜 (Fin k)` embeds isometrically as a `1`-complemented subspace of `ℓ₂`. -/
private theorem exists_euclideanSpace_retraction (k : ℕ) :
    ∃ (ι : EuclideanSpace 𝕜 (Fin k) →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)
      (π : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] EuclideanSpace 𝕜 (Fin k)),
      ‖ι‖ ≤ 1 ∧ ‖π‖ ≤ 1 ∧ π ∘L ι = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) := by
  set v : Fin k → lp (fun _ : ℕ ↦ 𝕜) 2 := fun i ↦ lp.single 2 (i : ℕ) (1 : 𝕜)
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [lp.inner_single_left, lp.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : (j : ℕ) ≠ (i : ℕ) := fun h ↦ hij (Fin.ext h.symm)
      simp [hne, hij]
  set V : Submodule 𝕜 (lp (fun _ : ℕ ↦ 𝕜) 2) := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hfin : finrank 𝕜 V = k := by
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]
  set e : EuclideanSpace 𝕜 (Fin k) ≃ₗᵢ[𝕜] V :=
    ((stdOrthonormalBasis 𝕜 V).reindex (finCongr hfin)).repr.symm
  set ι : EuclideanSpace 𝕜 (Fin k) →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
    V.subtypeL ∘L e.toLinearIsometry.toContinuousLinearMap
  set π : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    e.symm.toLinearIsometry.toContinuousLinearMap ∘L V.orthogonalProjectionOnto
  refine ⟨ι, π, opNorm_le_bound _ zero_le_one fun x ↦ by simp [ι, Submodule.norm_coe],
    opNorm_le_bound _ zero_le_one fun f ↦ ?_, ?_⟩
  · simpa [π] using V.norm_orthogonalProjectionOnto_apply_le f
  · ext x
    have hproj : V.orthogonalProjectionOnto (ι x) = e x :=
      V.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
    simp [π, hproj]

/-- **Hilbert numbers on Hilbert spaces.** For a bounded operator from a complete inner product
space into an inner product space, the Hilbert numbers coincide with the approximation numbers. -/
theorem hilbertNumber_eq_singularValue (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    T.hilbertNumber n = T.singularValue n := by
  refine (T.hilbertNumber_le_singularValue n).antisymm ?_
  by_contra! hlt
  set c : ℝ := ((T.hilbertNumber n : ℝ) + T.singularValue n) / 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hhc : (T.hilbertNumber n : ℝ) < c := by
    have : (T.hilbertNumber n : ℝ) < T.singularValue n := by exact_mod_cast hlt
    linarith
  have hca : c < T.singularValue n := by
    have : (T.hilbertNumber n : ℝ) < T.singularValue n := by exact_mod_cast hlt
    linarith
  obtain ⟨A₀, B₀, hA₀, hB₀, hfac⟩ := T.exists_comp_comp_eq_smul_id n hc0 hca
  obtain ⟨ι, π, hι, hπ, hret⟩ := exists_euclideanSpace_retraction (𝕜 := 𝕜) (n + 1)
  set A : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] H₁ := A₀ ∘L π
  set B : H₂ →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 := ι ∘L B₀
  have hA : ‖A‖ ≤ 1 := by
    calc ‖A‖ ≤ ‖A₀‖ * ‖π‖ := A₀.opNorm_comp_le π
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := mul_one 1
  have hB : ‖B‖ ≤ 1 := by
    calc ‖B‖ ≤ ‖ι‖ * ‖B₀‖ := ι.opNorm_comp_le B₀
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := mul_one 1
  have hι' : ‖ι‖₊ ≤ 1 := by exact_mod_cast hι
  have hπ' : ‖π‖₊ ≤ 1 := by exact_mod_cast hπ
  have hcomp : π ∘L (B ∘L T ∘L A) ∘L ι =
      (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    calc π ∘L (B ∘L T ∘L A) ∘L ι = (π ∘L ι) ∘L (B₀ ∘L T ∘L A₀) ∘L (π ∘L ι) := rfl
      _ = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
            rw [hret, hfac, id_comp, comp_id]
  have hid_sv :
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).singularValue n = 1 := by
    rw [singularValue_id_of_finiteDimensional]
    simp
  have hle : ‖(c : 𝕜)‖₊ ≤ T.hilbertNumber n := by
    calc ‖(c : 𝕜)‖₊ =
            ((c : 𝕜) • ContinuousLinearMap.id 𝕜
              (EuclideanSpace 𝕜 (Fin (n + 1)))).singularValue n := by
          rw [singularValue_smul, hid_sv, mul_one]
      _ = (π ∘L (B ∘L T ∘L A) ∘L ι).singularValue n := by rw [hcomp]
      _ ≤ ‖π‖₊ * (B ∘L T ∘L A).singularValue n * ‖ι‖₊ :=
          π.singularValue_comp_comp_le (B ∘L T ∘L A) ι n
      _ ≤ 1 * (B ∘L T ∘L A).singularValue n * 1 := by gcongr
      _ ≤ T.hilbertNumber n := by simpa using T.le_hilbertNumber hA hB n
  have hle' : c ≤ T.hilbertNumber n := by
    have h := NNReal.coe_le_coe.mpr hle
    rwa [coe_nnNorm, RCLike.norm_ofReal, abs_of_nonneg hc0] at h
  exact hhc.not_ge hle'

/-- **General Hilbert test bound.** For any test operators `A : H₁ →L[𝕜] E` from a complete inner
product space and `B : F →L[𝕜] H₂` into an inner product space,
`aₙ(B ∘ T ∘ A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem singularValue_comp_comp_le_mul_hilbertNumber
    (B : F →L[𝕜] H₂) (T : E →L[𝕜] F) (A : H₁ →L[𝕜] E) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by
  rw [← (B ∘L T ∘L A).hilbertNumber_eq_singularValue n]
  exact B.hilbertNumber_comp_comp_le T A n

/-- **Contraction bound for arbitrary Hilbert spaces.** Contractions `A : H₁ →L[𝕜] E` from a
complete inner product space and `B : F →L[𝕜] H₂` into an inner product space bound `hₙ(T)`
below by `aₙ(B ∘ T ∘ A)`. -/
theorem singularValue_comp_comp_le_hilbertNumber (T : E →L[𝕜] F)
    {A : H₁ →L[𝕜] E} {B : F →L[𝕜] H₂} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ T.hilbertNumber n := by
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  calc (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ :=
        singularValue_comp_comp_le_mul_hilbertNumber B T A n
    _ ≤ 1 * T.hilbertNumber n * 1 := by gcongr
    _ = T.hilbertNumber n := by simp

/-- **Hilbert numbers of a Hilbert-space identity.** On a complete inner product space, `hₙ(id) = 1`
for `n` strictly below the rank and `hₙ(id) = 0` otherwise. -/
theorem hilbertNumber_id_of_completeSpace (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 H₁).hilbertNumber n =
      if (n : Cardinal) < Module.rank 𝕜 H₁ then 1 else 0 := by
  rw [hilbertNumber_eq_singularValue, singularValue_id]

/-- **Euclidean normalization.** The identity on `EuclideanSpace 𝕜 (Fin (n + 1))` has `n`-th
Hilbert number `1`. -/
@[simp]
theorem hilbertNumber_id_euclideanSpace (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).hilbertNumber n = 1 := by
  have := FiniteDimensional.completeSpace 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))
  rw [hilbertNumber_eq_singularValue, singularValue_id_of_finiteDimensional]
  simp

end HilbertSpace

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The family of Hilbert numbers on all normed spaces over `ℝ` or `ℂ`. -/
noncomputable def hilbert : SNumberFamily 𝕜 :=
  fun T ↦ T.hilbertNumber

/-- Evaluation of the Hilbert family is the Hilbert number. -/
@[simp]
theorem hilbert_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : hilbert T n = T.hilbertNumber n := (rfl)

/-- Hilbert numbers satisfy Pietsch's s-number axioms over `ℝ` or `ℂ`. -/
theorem isSNumberSequence_hilbert : IsSNumberSequence (hilbert (𝕜 := 𝕜)) where
  norm T := T.hilbertNumber_zero
  antitone T := T.antitone_hilbertNumber
  add_le S T n := S.hilbertNumber_add_le T n
  comp_le B T A n := B.hilbertNumber_comp_comp_le T A n
  eq_zero_of_rank_le hT := ContinuousLinearMap.hilbertNumber_eq_zero_of_rank_le hT
  normalize n := ContinuousLinearMap.hilbertNumber_id_euclideanSpace n

/-- **Minimality of the Hilbert numbers.** Hilbert numbers are the smallest s-number sequence,
pointwise on every bounded operator over `ℝ` or `ℂ`. -/
theorem IsSNumberSequence.hilbertNumber_le {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.hilbertNumber n ≤ s T n := by
  refine ContinuousLinearMap.hilbertNumber_le_iff.mpr fun A hA B hB ↦ ?_
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  calc (B ∘L T ∘L A).singularValue n = s (B ∘L T ∘L A) n := (hs.eq_singularValue _ n).symm
    _ ≤ ‖B‖₊ * s T n * ‖A‖₊ := hs.comp_le B T A n
    _ ≤ 1 * s T n * 1 := by gcongr
    _ = s T n := by simp

end TauCeti.SNumbers
