/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Bernstein numbers

The `n`-th Bernstein number of a bounded operator `T : E →L[𝕜] F` is
`bₙ(T) = sup {inf_{0 ≠ x ∈ M} ‖T x‖ / ‖x‖ : M ≤ E, rank M = n + 1}`, the largest gain of `T` on
an `(n + 1)`-dimensional subspace of its source. The indexing is zero-based, so
`b₀(T) = ‖T‖`, and the supremum over an empty family is `0`, so `bₙ(T) = 0` when `E` has rank at
most `n`.

The gain of `T` on `M` is the largest `c` with `c ‖x‖ ≤ ‖T x‖` for all `x ∈ M`, so `bₙ(T)` is the
least upper bound of the constants `c` for which `T` is `c`-coercive on some subspace of rank
`n + 1` (`ContinuousLinearMap.isLUB_bernsteinNumber`). The rest of the calculus is read off this
characterization.

The Bernstein numbers form a strict s-number sequence over every nontrivially normed field,
without completeness of the field or of the spaces. The perturbation bound is the pointwise
triangle inequality. For the ideal inequality, a positive gain of `B ∘ T ∘ A` on `M` makes `A`
injective on `M`, so `A(M)` again has rank `n + 1`. An operator of rank at most `n` kills a
nonzero vector of every subspace of rank `n + 1`, and the identity has gain `1` on every nonzero
subspace.

The source spaces are normed, since the gain divides by the norm of the source vector; the
target spaces may be seminormed.

## Main declarations

* `ContinuousLinearMap.bernsteinNumber`: the Bernstein numbers `bₙ(T)`.
* `ContinuousLinearMap.isLUB_bernsteinNumber`: `bₙ(T)` is the least upper bound of the
  coercivity constants of `T` on subspaces of rank `n + 1`.
* `ContinuousLinearMap.bernsteinNumber_le_of_forall_rank_eq`: a nonzero vector with small gain in
  every subspace of rank `n + 1` bounds `bₙ(T)` from above.
* `ContinuousLinearMap.bernsteinNumber_comp_comp_le`: `bₙ(B T A) ≤ ‖B‖ bₙ(T) ‖A‖`.
* `ContinuousLinearMap.bernsteinNumber_id`: `bₙ(id_E) = 1` when `n` is below the rank of `E`.
* `TauCeti.SNumbers.isStrictSNumberSequence_bernstein`: the Bernstein numbers form a strict
  s-number sequence.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4,
  Theorems 4.5 and 4.6.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Bernstein.lean`: an earlier Lean formalization of the Bernstein numbers.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The `n`-th Bernstein number `bₙ(T)` of a bounded linear map `T`: the supremum, over the
subspaces `M` of the source of rank `n + 1`, of the gain `inf_{0 ≠ x ∈ M} ‖T x‖ / ‖x‖` of `T` on
`M`. The indexing is zero-based, so `b₀(T) = ‖T‖` (`bernsteinNumber_zero`). -/
noncomputable def bernsteinNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨆ M : {M : Submodule 𝕜 E // Module.rank 𝕜 M = n + 1},
    ⨅ x : {x : E // x ∈ M.1 ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊

/-- `bₙ(T)` is the supremum over the subspaces `M` of rank `n + 1` of the gain of `T` on `M`. -/
theorem bernsteinNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.bernsteinNumber n = ⨆ M : {M : Submodule 𝕜 E // Module.rank 𝕜 M = n + 1},
      ⨅ x : {x : E // x ∈ M.1 ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊ := by
  rw [bernsteinNumber]

/-- The gain of `T` on `M` is a coercivity constant of `T` on `M`. -/
private theorem iInf_mul_nnnorm_le (T : E →L[𝕜] F) (M : Submodule 𝕜 E) {x : E} (hx : x ∈ M) :
    (⨅ y : {y : E // y ∈ M ∧ y ≠ 0}, ‖T y‖₊ / ‖(y : E)‖₊) * ‖x‖₊ ≤ ‖T x‖₊ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  refine (le_div_iff₀ (nnNorm_pos.mpr hx0)).mp ?_
  exact ciInf_le (f := fun y : {y : E // y ∈ M ∧ y ≠ 0} ↦ ‖T y‖₊ / ‖(y : E)‖₊)
    (OrderBot.bddBelow _) ⟨x, hx, hx0⟩

/-- Every coercivity constant of `T` on a subspace of rank `n + 1` is at most the gain. -/
private theorem le_iInf_of_rank_eq (T : E →L[𝕜] F) {M : Submodule 𝕜 E} {n : ℕ}
    (hM : Module.rank 𝕜 M = n + 1) {c : ℝ≥0} (h : ∀ x ∈ M, c * ‖x‖₊ ≤ ‖T x‖₊) :
    c ≤ ⨅ y : {y : E // y ∈ M ∧ y ≠ 0}, ‖T y‖₊ / ‖(y : E)‖₊ := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_rank_pos (hM ▸ n.cast_add_one_pos)
  have : Nonempty {y : E // y ∈ M ∧ y ≠ 0} := ⟨⟨x, hx, hx0⟩⟩
  exact le_ciInf fun y ↦ (le_div_iff₀ (nnNorm_pos.mpr y.2.2)).mpr (h y y.2.1)

/-- The gain of `T` on a subspace of rank `n + 1` is at most `‖T‖`. -/
private theorem iInf_le_nnnorm (T : E →L[𝕜] F) {M : Submodule 𝕜 E} {n : ℕ}
    (hM : Module.rank 𝕜 M = n + 1) :
    ⨅ y : {y : E // y ∈ M ∧ y ≠ 0}, ‖T y‖₊ / ‖(y : E)‖₊ ≤ ‖T‖₊ := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_rank_pos (hM ▸ n.cast_add_one_pos)
  refine le_of_mul_le_mul_right ?_ (nnNorm_pos.mpr hx0)
  exact (iInf_mul_nnnorm_le T M hx).trans (T.le_opNNNorm x)

/-- **Characterization of upper bounds.** `bₙ(T) ≤ c` exactly when every coercivity constant of
`T` on a subspace of rank `n + 1` is at most `c`. -/
theorem bernsteinNumber_le_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    T.bernsteinNumber n ≤ c ↔ ∀ M : Submodule 𝕜 E, Module.rank 𝕜 M = n + 1 →
      ∀ d : ℝ≥0, (∀ x ∈ M, d * ‖x‖₊ ≤ ‖T x‖₊) → d ≤ c := by
  refine ⟨fun h M hM d hd ↦ ?_, fun h ↦ ?_⟩
  · refine ((le_iInf_of_rank_eq T hM hd).trans ?_).trans h
    exact le_ciSup (f := fun M : {M : Submodule 𝕜 E // Module.rank 𝕜 M = n + 1} ↦
        ⨅ x : {x : E // x ∈ M.1 ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊)
      ⟨‖T‖₊, Set.forall_mem_range.mpr fun M ↦ iInf_le_nnnorm T M.2⟩ ⟨M, hM⟩
  · exact ciSup_le' fun M ↦ h M.1 M.2 _ fun x hx ↦ iInf_mul_nnnorm_le T M.1 hx

/-- **Coercive-subspace lower bound.** If `c ‖x‖ ≤ ‖T x‖` for every `x` in a subspace of rank
`n + 1`, then `c ≤ bₙ(T)`. -/
theorem le_bernsteinNumber_of_rank_eq (T : E →L[𝕜] F) {n : ℕ} {M : Submodule 𝕜 E}
    (hM : Module.rank 𝕜 M = n + 1) {c : ℝ≥0} (h : ∀ x ∈ M, c * ‖x‖₊ ≤ ‖T x‖₊) :
    c ≤ T.bernsteinNumber n :=
  bernsteinNumber_le_iff.mp le_rfl M hM c h

/-- **Supremum formula.** `bₙ(T)` is the least upper bound of the constants `c` for which
`c ‖x‖ ≤ ‖T x‖` on some subspace of rank `n + 1`. -/
theorem isLUB_bernsteinNumber (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB {c : ℝ≥0 | ∃ M : Submodule 𝕜 E, Module.rank 𝕜 M = n + 1 ∧
      ∀ x ∈ M, c * ‖x‖₊ ≤ ‖T x‖₊} (T.bernsteinNumber n) := by
  refine ⟨?_, fun c hc ↦ bernsteinNumber_le_iff.mpr fun M hM d hd ↦ hc ⟨M, hM, hd⟩⟩
  rintro c ⟨M, hM, h⟩
  exact T.le_bernsteinNumber_of_rank_eq hM h

/-- **Near-optimal subspaces.** If `c < bₙ(T)`, then `T` is `c`-coercive on some subspace of rank
`n + 1`. -/
theorem exists_rank_eq_coercive_of_lt_bernsteinNumber {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : c < T.bernsteinNumber n) :
    ∃ M : Submodule 𝕜 E, Module.rank 𝕜 M = n + 1 ∧ ∀ x ∈ M, c * ‖x‖₊ ≤ ‖T x‖₊ := by
  obtain ⟨M, hM, d, hd, hcd⟩ : ∃ M : Submodule 𝕜 E, Module.rank 𝕜 M = n + 1 ∧
      ∃ d : ℝ≥0, (∀ x ∈ M, d * ‖x‖₊ ≤ ‖T x‖₊) ∧ c < d := by
    simpa using mt bernsteinNumber_le_iff.mpr h.not_ge
  exact ⟨M, hM, fun x hx ↦ (mul_le_mul_left hcd.le _).trans (hd x hx)⟩

/-- **Upper bound from small gains.** If every subspace of rank `n + 1` contains a nonzero vector
`x` with `‖T x‖ ≤ c ‖x‖`, then `bₙ(T) ≤ c`. -/
theorem bernsteinNumber_le_of_forall_rank_eq {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : ∀ M : Submodule 𝕜 E, Module.rank 𝕜 M = n + 1 →
      ∃ x ∈ M, x ≠ 0 ∧ ‖T x‖₊ ≤ c * ‖x‖₊) :
    T.bernsteinNumber n ≤ c := by
  refine bernsteinNumber_le_iff.mpr fun M hM d hd ↦ ?_
  obtain ⟨x, hx, hx0, hTx⟩ := h M hM
  exact le_of_mul_le_mul_right ((hd x hx).trans hTx) (nnNorm_pos.mpr hx0)

/-- A coercivity estimate with a factor `k` on `‖T x‖` bounds `d` by `k bₙ(T)`. -/
private theorem le_mul_bernsteinNumber_of_rank_eq (T : E →L[𝕜] F) {n : ℕ} {M : Submodule 𝕜 E}
    (hM : Module.rank 𝕜 M = n + 1) {d k : ℝ≥0} (h : ∀ x ∈ M, d * ‖x‖₊ ≤ k * ‖T x‖₊) :
    d ≤ k * T.bernsteinNumber n := by
  rcases eq_or_ne k 0 with rfl | hk
  · obtain ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_rank_pos (hM ▸ n.cast_add_one_pos)
    have hdx := h x hx
    rw [zero_mul, nonpos_iff_eq_zero, mul_eq_zero, nnNorm_eq_zero] at hdx
    simp [hdx.resolve_right hx0]
  rw [← div_le_iff₀' (pos_iff_ne_zero.mpr hk)]
  exact T.le_bernsteinNumber_of_rank_eq hM fun x hx ↦ by
    rw [div_mul_eq_mul_div, div_le_iff₀' (pos_iff_ne_zero.mpr hk)]
    exact h x hx

/-- The Bernstein numbers are bounded by the operator norm. -/
theorem bernsteinNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.bernsteinNumber n ≤ ‖T‖₊ :=
  bernsteinNumber_le_of_forall_rank_eq fun _ hM ↦
    let ⟨x, hx, hx0⟩ := exists_mem_ne_zero_of_rank_pos (hM ▸ n.cast_add_one_pos)
    ⟨x, hx, hx0, T.le_opNNNorm x⟩

/-- **Zeroth Bernstein number.** `b₀(T) = ‖T‖`, testing the gain on the line through each
nonzero vector. -/
@[simp]
theorem bernsteinNumber_zero (T : E →L[𝕜] F) : T.bernsteinNumber 0 = ‖T‖₊ := by
  refine (T.bernsteinNumber_le_nnnorm 0).antisymm (opNNNorm_le_bound _ _ fun x ↦ ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hM : Module.rank 𝕜 (𝕜 ∙ x) = (0 : ℕ) + 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hx]
    simp
  rw [mul_comm]
  refine T.le_mul_bernsteinNumber_of_rank_eq hM fun y hy ↦ ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_smul, nnNorm_smul, nnNorm_smul]
  exact le_of_eq (by ring)

/-- The Bernstein numbers form an antitone sequence. -/
theorem antitone_bernsteinNumber (T : E →L[𝕜] F) : Antitone T.bernsteinNumber := by
  intro m n hmn
  refine bernsteinNumber_le_iff.mpr fun M hM d hd ↦ ?_
  -- A subspace of rank `n + 1` contains one of rank `m + 1`.
  obtain ⟨N, hNM, hN⟩ := Submodule.exists_le_rank_eq (M := M) (k := m + 1)
    (by rw [hM]; exact_mod_cast Nat.add_le_add_right hmn 1)
  exact T.le_bernsteinNumber_of_rank_eq (by exact_mod_cast hN) fun x hx ↦ hd x (hNM hx)

/-- The Bernstein numbers of the zero map vanish. -/
@[simp]
theorem zero_bernsteinNumber (n : ℕ) : (0 : E →L[𝕜] F).bernsteinNumber n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).bernsteinNumber_le_nnnorm n) bot_le

/-- **Vanishing from rank.** A bounded map of rank at most `n` has `bₙ(T) = 0`: it kills a
nonzero vector of every subspace of rank `n + 1`. -/
theorem bernsteinNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T.bernsteinNumber n = 0 := by
  refine le_antisymm (bernsteinNumber_le_of_forall_rank_eq fun M hM ↦ ?_) bot_le
  obtain ⟨x, hxM, hTx, hx0⟩ : ∃ x ∈ M, T x = 0 ∧ x ≠ 0 := by
    by_contra! h
    have hle := (Submodule.lift_rank_le_of_disjoint_ker (f := (T : E →ₗ[𝕜] F))
      (Submodule.disjoint_def.mpr h)).trans (Cardinal.lift_le.mpr hT)
    rw [hM, Cardinal.lift_natCast, ← Nat.cast_add_one, Cardinal.lift_natCast,
      Nat.cast_le] at hle
    omega
  exact ⟨x, hxM, hx0, by simp [hTx]⟩

/-- **Perturbative triangle bound.** `bₙ(S + T) ≤ bₙ(S) + ‖T‖`. -/
theorem bernsteinNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).bernsteinNumber n ≤ S.bernsteinNumber n + ‖T‖₊ := by
  refine bernsteinNumber_le_iff.mpr fun M hM d hd ↦ tsub_le_iff_right.mp ?_
  refine S.le_bernsteinNumber_of_rank_eq hM fun x hx ↦ ?_
  calc (d - ‖T‖₊) * ‖x‖₊ = d * ‖x‖₊ - ‖T‖₊ * ‖x‖₊ := tsub_mul _ _ _
    _ ≤ ‖(S + T) x‖₊ - ‖T x‖₊ := tsub_le_tsub (hd x hx) (T.le_opNNNorm x)
    _ ≤ ‖S x‖₊ := tsub_le_iff_right.mpr (by simpa using nnNorm_add_le (S x) (T x))

/-- **Two-sided ideal inequality.** `bₙ(B T A) ≤ ‖B‖ bₙ(T) ‖A‖`: a positive gain of `B T A` on a
subspace `M` makes `A` injective on `M`, and `A(M)` then has rank `n + 1`. -/
theorem bernsteinNumber_comp_comp_le (B : F →L[𝕜] G) (T : E →L[𝕜] F) (A : W →L[𝕜] E) (n : ℕ) :
    (B ∘L T ∘L A).bernsteinNumber n ≤ ‖B‖₊ * T.bernsteinNumber n * ‖A‖₊ := by
  refine bernsteinNumber_le_iff.mpr fun M hM d hd ↦ ?_
  rcases eq_or_ne d 0 with rfl | hd0
  · exact zero_le
  -- `A` is injective on `M`, since `B T A` is `d`-coercive there with `d ≠ 0`.
  have hinj : Function.Injective ((A : W →ₗ[𝕜] E) ∘ₗ M.subtype) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    have hAx : A x = 0 := by simpa using hx
    simpa [hAx, hd0] using hd x x.2
  have hrank : Module.rank 𝕜 (LinearMap.range ((A : W →ₗ[𝕜] E) ∘ₗ M.subtype)) = n + 1 := by
    have h := lift_rank_range_of_injective _ hinj
    rw [hM, ← Nat.cast_add_one, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff] at h
    exact_mod_cast h
  rw [mul_right_comm]
  refine T.le_mul_bernsteinNumber_of_rank_eq hrank fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := hy
  calc d * ‖A x‖₊ ≤ d * (‖A‖₊ * ‖(x : W)‖₊) := by gcongr; exact A.le_opNNNorm x
    _ = ‖A‖₊ * (d * ‖(x : W)‖₊) := mul_left_comm _ _ _
    _ ≤ ‖A‖₊ * (‖B‖₊ * ‖T (A x)‖₊) :=
      mul_le_mul_right ((hd x x.2).trans (B.le_opNNNorm _)) _
    _ = ‖B‖₊ * ‖A‖₊ * ‖T (A x)‖₊ := by ring

/-- **Identity normalization.** If `n` is strictly below the rank of `E`, then `bₙ(id_E) = 1`:
the identity has gain `1` on every subspace of rank `n + 1`. -/
theorem bernsteinNumber_id {n : ℕ} (hn : (n : Cardinal) < Module.rank 𝕜 E) :
    (ContinuousLinearMap.id 𝕜 E).bernsteinNumber n = 1 := by
  refine le_antisymm ((bernsteinNumber_le_nnnorm _ n).trans ?_) ?_
  · exact_mod_cast norm_id_le
  obtain ⟨M, -, hM⟩ := Submodule.exists_le_rank_eq (M := (⊤ : Submodule 𝕜 E)) (k := n + 1)
    (by rw [rank_top, Nat.cast_add_one]; exact Cardinal.natCast_add_one_le_iff.mpr hn)
  exact (ContinuousLinearMap.id 𝕜 E).le_bernsteinNumber_of_rank_eq (by exact_mod_cast hM)
    fun x _ ↦ by simp

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The family of Bernstein numbers on all normed spaces over the scalar field. -/
noncomputable def bernstein : SNumberFamily 𝕜 :=
  fun T ↦ T.bernsteinNumber

/-- Evaluation of the Bernstein family is the Bernstein number. -/
@[simp]
theorem bernstein_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : bernstein T n = T.bernsteinNumber n := (rfl)

/-- Bernstein numbers form a strict s-number sequence over every nontrivially normed field. -/
theorem isStrictSNumberSequence_bernstein : IsStrictSNumberSequence (bernstein (𝕜 := 𝕜)) :=
  .of_normalize_of_lt_rank (fun T ↦ T.bernsteinNumber_zero) (fun T ↦ T.antitone_bernsteinNumber)
    (fun S T n ↦ S.bernsteinNumber_add_le T n) (fun B T A n ↦ B.bernsteinNumber_comp_comp_le T A n)
    ContinuousLinearMap.bernsteinNumber_eq_zero_of_rank_le
    fun _ hn ↦ ContinuousLinearMap.bernsteinNumber_id hn

end TauCeti.SNumbers
