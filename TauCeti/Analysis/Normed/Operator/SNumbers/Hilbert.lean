/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Hilbert numbers

The `n`-th Hilbert number of a bounded operator `T : E →L[𝕜] F` over `RCLike 𝕜` is
`hₙ(T) = sup {aₙ(B ∘ T ∘ A) : A : ℓ₂ → E, B : F → ℓ₂, ‖A‖ ≤ 1, ‖B‖ ≤ 1}`,
the largest approximation number of a compression of `T` to the separable Hilbert space
`ℓ₂ = ℓ²(ℕ, 𝕜)`. The indexing is zero-based, so `h₀(T) = ‖T‖`.

Every compression scales: `aₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖` for all bounded `A` and `B`
(`ContinuousLinearMap.singularValue_comp_comp_le_hilbertNumber`), which gives the ratio form
`hₙ(T) = sup {aₙ(B T A) / (‖B‖ ‖A‖) : A ≠ 0, B ≠ 0}`.

The Hilbert numbers satisfy Pietsch's s-number axioms. The zeroth term is the operator norm
because every vector `x` and a norming functional of `T x` (Hahn–Banach) factor through a
rank-one compression of `T`. The Euclidean normalization factors the identity of `ℓ₂^{n+1}` as
`A ∘ (B ∘ id ∘ A) ∘ B`, with `B : ℓ₂^{n+1} → ℓ₂` an isometric embedding and `A` its adjoint.
The remaining axioms are inherited from the approximation numbers through the supremum.

## Main declarations

* `ContinuousLinearMap.hilbertNumber`: the Hilbert numbers `hₙ(T)`.
* `ContinuousLinearMap.singularValue_comp_comp_le_hilbertNumber`: `aₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖`.
* `ContinuousLinearMap.hilbertNumber_eq_iSup_div`: the ratio form of `hₙ(T)`.
* `ContinuousLinearMap.hilbertNumber_le_singularValue`: `hₙ(T) ≤ aₙ(T)`.
* `ContinuousLinearMap.hilbertNumber_zero`: `h₀(T) = ‖T‖`.
* `TauCeti.SNumbers.isSNumberSequence_hilbert`: the Hilbert numbers form an s-number sequence.

## References

* W. Bauhardt, *Hilbert-Zahlen von Operatoren in Banachräumen*, Math. Nachr. 79 (1977),
  181–187.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, *Inequalities between s-numbers*, Adv. Oper. Theory 9 (2024), art. 82.
-/

public section

open scoped NNReal lp

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `n`-th Hilbert number `hₙ(T)` of a bounded linear map `T`: the supremum of the
approximation numbers `aₙ(B ∘ T ∘ A)` over all contractions `A : ℓ₂ → E` and `B : F → ℓ₂`,
where `ℓ₂ = ℓ²(ℕ, 𝕜)`. The indexing is zero-based, so `h₀(T) = ‖T‖` (`hilbertNumber_zero`). -/
noncomputable def hilbertNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨆ p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) // ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1},
    (p.1.2 ∘L T ∘L p.1.1).singularValue n

/-- `hₙ(T)` is the supremum of `aₙ(B ∘ T ∘ A)` over the contractions `A : ℓ₂ → E` and
`B : F → ℓ₂`. -/
theorem hilbertNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) // ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1},
        (p.1.2 ∘L T ∘L p.1.1).singularValue n := by
  rw [hilbertNumber]

private instance :
    Nonempty {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) // ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} :=
  ⟨⟨0, by simp, by simp⟩⟩

/-- A compression of `T` by contractions has approximation numbers at most `‖T‖`. -/
private theorem singularValue_comp_comp_le_nnnorm {T : E →L[𝕜] F} {A : ℓ²(ℕ, 𝕜) →L[𝕜] E}
    {B : F →L[𝕜] ℓ²(ℕ, 𝕜)} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖T‖₊ := by
  refine ((B ∘L T ∘L A).singularValue_le_nnnorm n).trans ?_
  have hA' : ‖A‖₊ ≤ 1 := mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := mod_cast hB
  calc ‖B ∘L T ∘L A‖₊ ≤ ‖B‖₊ * (‖T‖₊ * ‖A‖₊) :=
        (opNNNorm_comp_le _ _).trans (by gcongr; exact opNNNorm_comp_le _ _)
    _ ≤ 1 * (‖T‖₊ * 1) := by gcongr
    _ = ‖T‖₊ := by simp

private theorem bddAbove_range_singularValue_comp_comp (T : E →L[𝕜] F) (n : ℕ) :
    BddAbove (Set.range fun p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) //
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} ↦ (p.1.2 ∘L T ∘L p.1.1).singularValue n) :=
  ⟨‖T‖₊, Set.forall_mem_range.mpr fun p ↦ singularValue_comp_comp_le_nnnorm p.2.1 p.2.2 n⟩

/-- Every compression of `T` by contractions bounds `hₙ(T)` from below. -/
private theorem singularValue_comp_comp_le_hilbertNumber_of_norm_le_one (T : E →L[𝕜] F)
    {A : ℓ²(ℕ, 𝕜) →L[𝕜] E} {B : F →L[𝕜] ℓ²(ℕ, 𝕜)} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ T.hilbertNumber n :=
  le_ciSup (f := fun p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) //
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} ↦ (p.1.2 ∘L T ∘L p.1.1).singularValue n)
    (bddAbove_range_singularValue_comp_comp T n) ⟨(A, B), hA, hB⟩

/-- **Upper-bound characterization.** `hₙ(T) ≤ c` exactly when `aₙ(B ∘ T ∘ A) ≤ c` for all
contractions `A : ℓ₂ → E` and `B : F → ℓ₂`. -/
theorem hilbertNumber_le_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    T.hilbertNumber n ≤ c ↔ ∀ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → (B ∘L T ∘L A).singularValue n ≤ c := by
  rw [hilbertNumber, ciSup_le_iff (bddAbove_range_singularValue_comp_comp T n), Subtype.forall,
    Prod.forall]
  exact forall₂_congr fun A B ↦ ⟨fun h hA hB ↦ h ⟨hA, hB⟩, fun h hAB ↦ h hAB.1 hAB.2⟩

/-- **Compressions.** `aₙ(B ∘ T ∘ A) ≤ ‖B‖ hₙ(T) ‖A‖` for all bounded `A : ℓ₂ → E` and
`B : F → ℓ₂`. -/
theorem singularValue_comp_comp_le_hilbertNumber (B : F →L[𝕜] ℓ²(ℕ, 𝕜)) (T : E →L[𝕜] F)
    (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by
  -- A factor of norm zero makes both sides vanish.
  rcases eq_or_ne ‖B‖₊ 0 with hB | hB
  · simpa [hB] using B.singularValue_comp_comp_le T A n
  rcases eq_or_ne ‖A‖₊ 0 with hA | hA
  · simpa [hA] using B.singularValue_comp_comp_le T A n
  have hA₀ : ‖A‖ ≠ 0 := by rwa [← coe_nnNorm, NNReal.coe_ne_zero]
  have hB₀ : ‖B‖ ≠ 0 := by rwa [← coe_nnNorm, NNReal.coe_ne_zero]
  -- The normalized compression `(‖B‖⁻¹ B) T (‖A‖⁻¹ A)` is admissible for `hₙ(T)`.
  have hle := T.singularValue_comp_comp_le_hilbertNumber_of_norm_le_one
    (A := ((‖A‖ : 𝕜))⁻¹ • A) (B := ((‖B‖ : 𝕜))⁻¹ • B)
    (by rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hA₀])
    (by rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hB₀]) n
  have heq : B ∘L T ∘L A =
      ((‖B‖ * ‖A‖ : ℝ) : 𝕜) • ((((‖B‖ : 𝕜))⁻¹ • B) ∘L T ∘L (((‖A‖ : 𝕜))⁻¹ • A)) := by
    have hc : (‖B‖ : 𝕜) * ‖A‖ * ((‖A‖ : 𝕜)⁻¹ * (‖B‖ : 𝕜)⁻¹) = 1 := by
      field_simp [RCLike.ofReal_ne_zero.mpr hA₀, RCLike.ofReal_ne_zero.mpr hB₀]
    ext1 x
    simp only [comp_apply, smul_apply, map_smul, smul_smul, RCLike.ofReal_mul, hc, one_smul]
  have hn : ‖((‖B‖ * ‖A‖ : ℝ) : 𝕜)‖₊ = ‖B‖₊ * ‖A‖₊ := by
    ext
    simp
  rw [heq, singularValue_smul, hn]
  calc ‖B‖₊ * ‖A‖₊ * ((((‖B‖ : 𝕜))⁻¹ • B) ∘L T ∘L (((‖A‖ : 𝕜))⁻¹ • A)).singularValue n
      ≤ ‖B‖₊ * ‖A‖₊ * T.hilbertNumber n := by gcongr
    _ = ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := mul_right_comm _ _ _

/-- **Ratio form.** `hₙ(T)` is the supremum of `aₙ(B ∘ T ∘ A) / (‖B‖ ‖A‖)` over all nonzero
bounded `A : ℓ₂ → E` and `B : F → ℓ₂`. -/
theorem hilbertNumber_eq_iSup_div (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) // p.1 ≠ 0 ∧ p.2 ≠ 0},
        (p.1.2 ∘L T ∘L p.1.1).singularValue n / (‖p.1.2‖₊ * ‖p.1.1‖₊) := by
  have hdiv (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)) :
      (B ∘L T ∘L A).singularValue n / (‖B‖₊ * ‖A‖₊) ≤ T.hilbertNumber n := by
    rcases eq_or_ne (‖B‖₊ * ‖A‖₊) 0 with h0 | h0
    · simp [h0]
    rw [div_le_iff₀ (pos_iff_ne_zero.mpr h0)]
    exact (singularValue_comp_comp_le_hilbertNumber B T A n).trans_eq (by ring)
  have hbdd : BddAbove (Set.range fun p : {p : (ℓ²(ℕ, 𝕜) →L[𝕜] E) × (F →L[𝕜] ℓ²(ℕ, 𝕜)) //
      p.1 ≠ 0 ∧ p.2 ≠ 0} ↦
        (p.1.2 ∘L T ∘L p.1.1).singularValue n / (‖p.1.2‖₊ * ‖p.1.1‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun p ↦ hdiv p.1.1 p.1.2⟩
  refine le_antisymm (hilbertNumber_le_iff.mpr fun A B hA hB ↦ ?_)
    (ciSup_le' fun p ↦ hdiv p.1.1 p.1.2)
  rcases eq_or_ne (‖B‖₊ * ‖A‖₊) 0 with h0 | h0
  · -- A factor of norm zero makes the compression vanish.
    have h := B.singularValue_comp_comp_le T A n
    rw [mul_right_comm, h0, zero_mul] at h
    exact h.trans bot_le
  have hA₀ : A ≠ 0 := by rintro rfl; simp at h0
  have hB₀ : B ≠ 0 := by rintro rfl; simp at h0
  -- Dividing by `‖B‖ ‖A‖ ≤ 1` does not decrease the approximation number.
  have hBA : ‖B‖₊ * ‖A‖₊ ≤ 1 := mul_le_one' (mod_cast hB) (mod_cast hA)
  exact (le_div_self (by positivity) (pos_iff_ne_zero.mpr h0) hBA).trans
    (le_ciSup hbdd ⟨(A, B), hA₀, hB₀⟩)

/-- The Hilbert numbers are bounded by the approximation numbers. -/
theorem hilbertNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n ≤ T.singularValue n :=
  hilbertNumber_le_iff.mpr fun A B hA hB ↦ (B.singularValue_comp_comp_le T A n).trans <| by
    have hA' : ‖A‖₊ ≤ 1 := mod_cast hA
    have hB' : ‖B‖₊ ≤ 1 := mod_cast hB
    calc ‖B‖₊ * T.singularValue n * ‖A‖₊ ≤ 1 * T.singularValue n * 1 := by gcongr
      _ = T.singularValue n := by simp

/-- The Hilbert numbers are bounded by the operator norm. -/
theorem hilbertNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.hilbertNumber n ≤ ‖T‖₊ :=
  (T.hilbertNumber_le_singularValue n).trans (T.singularValue_le_nnnorm n)

/-- **Zeroth Hilbert number.** `h₀(T) = ‖T‖`: a vector `x` and a norming functional `g` of
`T x` give a rank-one compression `α ↦ g (T (α₀ • x)) • e₀` through `ℓ₂`. -/
@[simp]
theorem hilbertNumber_zero (T : E →L[𝕜] F) : T.hilbertNumber 0 = ‖T‖₊ := by
  refine (T.hilbertNumber_le_nnnorm 0).antisymm (opNNNorm_le_bound _ _ fun x ↦ ?_)
  -- The first unit vector `e₀` of `ℓ₂`.
  set e : ℓ²(ℕ, 𝕜) := lp.single 2 0 1
  have he : ‖e‖ = 1 := by simp [e, lp.norm_single]
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 (T x)
  let A : ℓ²(ℕ, 𝕜) →L[𝕜] E := (innerSL 𝕜 e).smulRight x
  let B : F →L[𝕜] ℓ²(ℕ, 𝕜) := g.smulRight e
  have hBTA : (B ∘L T ∘L A) e = (‖T x‖ : 𝕜) • e := by
    simp [A, B, inner_self_eq_norm_sq_to_K, he, hgx]
  have hA : ‖A‖₊ = ‖x‖₊ := by simp [A, ← NNReal.coe_inj, he]
  have hB : ‖B‖₊ ≤ 1 := by
    rw [nnNorm_smulRight_apply]
    have : ‖e‖₊ = 1 := NNReal.coe_eq_one.mp he
    simpa [this] using (show ‖g‖₊ ≤ 1 from mod_cast hg)
  calc ‖T x‖₊ = ‖(B ∘L T ∘L A) e‖₊ := by
        rw [hBTA, nnNorm_smul, ← NNReal.coe_inj]; simp [he]
    _ ≤ ‖B ∘L T ∘L A‖₊ := by
        simpa [show ‖e‖₊ = 1 from NNReal.coe_eq_one.mp he] using (B ∘L T ∘L A).le_opNNNorm e
    _ = (B ∘L T ∘L A).singularValue 0 := (singularValue_zero _).symm
    _ ≤ ‖B‖₊ * T.hilbertNumber 0 * ‖A‖₊ := singularValue_comp_comp_le_hilbertNumber B T A 0
    _ ≤ 1 * T.hilbertNumber 0 * ‖x‖₊ := by rw [hA]; gcongr
    _ = T.hilbertNumber 0 * ‖x‖₊ := by rw [one_mul]

/-- The Hilbert numbers form an antitone sequence. -/
theorem antitone_hilbertNumber (T : E →L[𝕜] F) : Antitone T.hilbertNumber :=
  fun _ _ hmn ↦ hilbertNumber_le_iff.mpr fun _ _ hA hB ↦
    ((antitone_singularValue _ hmn).trans
      (T.singularValue_comp_comp_le_hilbertNumber_of_norm_le_one hA hB _))

/-- The Hilbert numbers of the zero map vanish. -/
@[simp]
theorem zero_hilbertNumber (n : ℕ) : (0 : E →L[𝕜] F).hilbertNumber n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).hilbertNumber_le_nnnorm n) bot_le

/-- **Vanishing from rank.** A bounded map of rank at most `n` has `hₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T.hilbertNumber n = 0 :=
  le_antisymm ((T.hilbertNumber_le_singularValue n).trans_eq
    (singularValue_eq_zero_of_rank_le hT)) bot_le

/-- **Perturbative triangle bound.** `hₙ(S + T) ≤ hₙ(S) + ‖T‖`. -/
theorem hilbertNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).hilbertNumber n ≤ S.hilbertNumber n + ‖T‖₊ :=
  hilbertNumber_le_iff.mpr fun A B hA hB ↦ by
    rw [add_comp, comp_add]
    exact ((B ∘L S ∘L A).singularValue_add_le _ n).trans <| add_le_add
      (S.singularValue_comp_comp_le_hilbertNumber_of_norm_le_one hA hB n)
      (((B ∘L T ∘L A).singularValue_zero).symm.trans_le
        (singularValue_comp_comp_le_nnnorm hA hB 0))

/-- **Two-sided ideal inequality.** `hₙ(B T A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem hilbertNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ :=
  hilbertNumber_le_iff.mpr fun A' B' hA' hB' ↦ by
    have hA'' : ‖A'‖₊ ≤ 1 := mod_cast hA'
    have hB'' : ‖B'‖₊ ≤ 1 := mod_cast hB'
    calc (B' ∘L (B ∘L T ∘L A) ∘L A').singularValue n
        = ((B' ∘L B) ∘L T ∘L (A ∘L A')).singularValue n := by simp only [comp_assoc]
      _ ≤ ‖B' ∘L B‖₊ * T.hilbertNumber n * ‖A ∘L A'‖₊ :=
        singularValue_comp_comp_le_hilbertNumber _ T _ n
      _ ≤ (‖B'‖₊ * ‖B‖₊) * T.hilbertNumber n * (‖A‖₊ * ‖A'‖₊) := by
        gcongr <;> exact opNNNorm_comp_le _ _
      _ ≤ (1 * ‖B‖₊) * T.hilbertNumber n * (‖A‖₊ * 1) := by gcongr
      _ = ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by simp

variable (𝕜) in
/-- The identity of `ℓ₂^{n+1}` is a compression of a contraction of `ℓ₂` by contractions: an
isometric embedding `B : ℓ₂^{n+1} → ℓ₂` and its adjoint satisfy `B† ∘ B = id`. -/
private theorem exists_comp_eq_id_euclideanSpace (n : ℕ) :
    ∃ (A : ℓ²(ℕ, 𝕜) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
      (B : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ ∀ x, A (B x) = x := by
  classical
  let b := EuclideanSpace.basisFun (Fin (n + 1)) 𝕜
  let v : Fin (n + 1) → ℓ²(ℕ, 𝕜) := fun i ↦ lp.single 2 (i : ℕ) 1
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp [v, lp.inner_single_left, Pi.single_apply, Fin.val_inj]
  -- The linear map `x ↦ ∑ i, x i • v i` sends the standard basis to `v`.
  let f : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
    Fintype.linearCombination 𝕜 v ∘ₗ (WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).toLinearMap
  have hfb : ⇑f ∘ ⇑b.toBasis = v := by
    ext1 i
    simp [f, b]
  have hb : Orthonormal 𝕜 b.toBasis := by rw [b.coe_toBasis]; exact b.orthonormal
  let L := f.isometryOfOrthonormal hb (hfb ▸ hv)
  refine ⟨L.toContinuousLinearMap.adjoint, L.toContinuousLinearMap, ?_,
    L.norm_toContinuousLinearMap_le, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact L.norm_toContinuousLinearMap_le
  · refine fun x ↦ ext_inner_left 𝕜 fun y ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp

/-- **Euclidean normalization.** The identity of `ℓ₂^{n+1}` has `hₙ = 1`. -/
theorem hilbertNumber_id_euclideanSpace (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).hilbertNumber n = 1 := by
  set I := ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_comp_eq_id_euclideanSpace 𝕜 n
  have hA' : ‖A‖₊ ≤ 1 := mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := mod_cast hB
  have hrank : (n : Cardinal) < Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq]
    simp
  refine le_antisymm ((I.hilbertNumber_le_nnnorm n).trans (by exact_mod_cast norm_id_le)) ?_
  -- `id = A ∘ (B ∘ id ∘ A) ∘ B`, and `aₙ(id) = 1` below the dimension.
  have hid : A ∘L (B ∘L I ∘L A) ∘L B = I := by
    ext1 x
    simp [I, hAB]
  calc (1 : ℝ≥0) = I.singularValue n := by simp [I, singularValue_id, hrank]
    _ = (A ∘L (B ∘L I ∘L A) ∘L B).singularValue n := by rw [hid]
    _ ≤ ‖A‖₊ * (B ∘L I ∘L A).singularValue n * ‖B‖₊ := singularValue_comp_comp_le _ _ _ n
    _ ≤ 1 * (B ∘L I ∘L A).singularValue n * 1 := by gcongr
    _ ≤ I.hilbertNumber n := by
      rw [one_mul, mul_one]
      exact I.singularValue_comp_comp_le_hilbertNumber_of_norm_le_one hA hB n

end ContinuousLinearMap

namespace TauCeti.SNumbers

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The family of Hilbert numbers on all normed spaces over the scalar field. -/
noncomputable def hilbert : SNumberFamily 𝕜 :=
  fun T ↦ T.hilbertNumber

/-- Evaluation of the Hilbert family is the Hilbert number. -/
@[simp]
theorem hilbert_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : hilbert T n = T.hilbertNumber n := (rfl)

/-- Hilbert numbers form an s-number sequence over every `RCLike` field. -/
theorem isSNumberSequence_hilbert : IsSNumberSequence (hilbert (𝕜 := 𝕜)) where
  norm T := T.hilbertNumber_zero
  antitone T := T.antitone_hilbertNumber
  add_le S T n := S.hilbertNumber_add_le T n
  comp_le B T A n := B.hilbertNumber_comp_comp_le T A n
  eq_zero_of_rank_le hT := ContinuousLinearMap.hilbertNumber_eq_zero_of_rank_le hT
  normalize n := ContinuousLinearMap.hilbertNumber_id_euclideanSpace n

end TauCeti.SNumbers
