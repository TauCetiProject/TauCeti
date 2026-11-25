/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.LinearAlgebra.Dimension.Submodule
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.InnerProductSpace.Projection.Diagonal
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Operator.Extend

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

The Bernstein numbers are injective, since a linear isometry on the target preserves every gain,
and they lie below the Gelfand numbers, since a subspace of rank `n + 1` meets every subspace of
codimension at most `n` in a nonzero vector. They are the smallest injective strict s-number
sequence: if `T` is `d`-coercive with `d > 0` on a subspace `M` of rank `n + 1`, then `id_M`
factors through the corestriction of `T` to its range on `M`, with a factor of norm at most
`d⁻¹`, and the normalization `s (id_M) n = 1` gives `d ≤ s T n`.

Unlike approximation, Gelfand and Kolmogorov numbers (which are additive and multiplicative) and
Hilbert numbers (which are additive), the Bernstein numbers are neither multiplicative nor additive
over `ℝ` or `ℂ`. On a finite index type `ι`, the identity map `ℓ₂(ι) → ℓ_∞(ι)` has
`bₙ ≤ (√(n + 1))⁻¹` because every `(n + 1)`-dimensional subspace of `ℓ_∞(ι)` contains a unit-ball
vector attaining norm `1` on at least `n + 1` coordinates, while over `ℝ` or `ℂ` the reverse
identity `ℓ_∞(ι) → ℓ₂(ι)` has `bₙ ≤ √(card ι / (n + 1))` by testing the orthogonal projections of
the standard basis vectors onto an `(n + 1)`-dimensional subspace. Factoring `id : ℓ₂³ → ℓ₂³`
through `ℓ_∞³` at `m = n = 1` refutes multiplicativity, and Pietsch's `71`-dimensional block
anti-diagonal combination on `ℓ₂⁷¹ × ℓ_∞⁷¹` at `m = n = 35` refutes additivity.

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
* `ContinuousLinearMap.bernsteinNumber_le_gelfandNumber`: `bₙ(T) ≤ cₙ(T)`.
* `ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_le`:
  `bₙ(ℓ₂(ι) → ℓ_∞(ι)) ≤ (√(n + 1))⁻¹`.
* `ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_symm_le`:
  `bₙ(ℓ_∞(ι) → ℓ₂(ι)) ≤ √(card ι / (n + 1))` over `ℝ` or `ℂ`.
* `LinearIsometry.bernsteinNumber_toContinuousLinearMap_comp`,
  `TauCeti.SNumbers.isInjective_bernstein`: the Bernstein numbers are injective.
* `TauCeti.SNumbers.isStrictSNumberSequence_bernstein`,
  `TauCeti.SNumbers.isSNumberSequence_bernstein`: the Bernstein numbers form a strict s-number
  sequence.
* `TauCeti.SNumbers.IsStrictSNumberSequence.bernsteinNumber_le`: `bₙ(T) ≤ s T n` for every
  injective strict s-number sequence `s`.
* `TauCeti.SNumbers.not_multiplicative_bernstein`: the Bernstein family is not multiplicative over
  `ℝ` or `ℂ`.
* `TauCeti.SNumbers.not_additive_bernstein`: the Bernstein family is not additive over `ℝ` or `ℂ`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4,
  Theorems 4.5 and 4.6.
* A. Pietsch, *Operator Ideals*, North-Holland (1980), Chapter 11, for the minimality of the
  Bernstein numbers among injective strict s-number sequences.
* A. Pietsch, *Bad properties of the Bernstein numbers*, Studia Math. 184 (2008), 263–269,
  Theorem 3.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Bernstein.lean`, `SNumbers/Injectivity.lean` and
  `SNumbers/Examples/IdentityL2Linfty.lean`: an earlier Lean formalization of the Bernstein
  numbers, injective s-number sequences and the `ℓ₂ ↔ ℓ_∞` identity bounds.
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
    ⨅ x : {x : E // x ∈ M.val ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊

/-- `bₙ(T)` is the supremum over the subspaces `M` of rank `n + 1` of the gain of `T` on `M`. -/
theorem bernsteinNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.bernsteinNumber n = ⨆ M : {M : Submodule 𝕜 E // Module.rank 𝕜 M = n + 1},
      ⨅ x : {x : E // x ∈ M.val ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊ := by
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
  exact le_ciInf fun y ↦ (le_div_iff₀ (nnNorm_pos.mpr y.property.2)).mpr (h y y.property.1)

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
        ⨅ x : {x : E // x ∈ M.val ∧ x ≠ 0}, ‖T x‖₊ / ‖(x : E)‖₊)
      ⟨‖T‖₊, Set.forall_mem_range.mpr fun M ↦ iInf_le_nnnorm T M.property⟩ ⟨M, hM⟩
  · exact ciSup_le' fun M ↦ h M.val M.property _ fun x hx ↦ iInf_mul_nnnorm_le T M.val hx

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
  obtain ⟨x, hxM, hTx, hx0⟩ := Submodule.exists_mem_ker_ne_zero_of_rank_lt
    (f := (T : E →ₗ[𝕜] F)) (by rw [hM]; exact_mod_cast n.lt_succ_self) hT
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hTx
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
    simpa [hAx, hd0] using hd x x.property
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
      mul_le_mul_right ((hd x x.property).trans (B.le_opNNNorm _)) _
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

/-- **Bernstein numbers below Gelfand numbers.** `bₙ(T) ≤ cₙ(T)`: a subspace of rank `n + 1` and
a subspace of codimension at most `n` meet in a nonzero vector. -/
theorem bernsteinNumber_le_gelfandNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.bernsteinNumber n ≤ T.gelfandNumber n := by
  refine le_gelfandNumber_iff.mpr fun N _ hN ↦ bernsteinNumber_le_of_forall_rank_eq fun M hM ↦ ?_
  obtain ⟨x, hxM, hxN, hx0⟩ := Submodule.exists_mem_ker_ne_zero_of_rank_lt (f := N.mkQ)
    (by rw [hM]; exact_mod_cast n.lt_succ_self) ((Submodule.rank_le _).trans hN)
  rw [Submodule.ker_mkQ] at hxN
  exact ⟨x, hxM, hx0, (T ∘L N.subtypeL).le_opNNNorm ⟨x, hxN⟩⟩

/-- **Upper bound for `ℓ₂ → ℓ_∞`.** On a finite index type `ι`, the identity map
`EuclideanSpace 𝕜 ι →L[𝕜] (ι → 𝕜)` has `n`-th Bernstein number at most `(√(n + 1))⁻¹`: every
`(n + 1)`-dimensional subspace contains a sup-norm unit-ball vector attaining norm `1` on at
least `n + 1` coordinates, whose `ℓ₂` norm is at least `√(n + 1)`. -/
theorem bernsteinNumber_piLp_continuousLinearEquiv_le
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [Fintype ι] (n : ℕ) :
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ 𝕜) :
      EuclideanSpace 𝕜 ι →L[𝕜] ι → 𝕜).bernsteinNumber n ≤ (NNReal.sqrt (n + 1))⁻¹ := by
  classical
  let e : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 := PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ 𝕜)
  refine bernsteinNumber_le_of_forall_rank_eq fun M hM ↦ ?_
  let M' : Submodule 𝕜 (ι → 𝕜) := M.map (e.toLinearEquiv : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜)
  have hfinM' : Module.finrank 𝕜 M' = n + 1 :=
    (e.toLinearEquiv.finrank_map_eq M).trans (Module.finrank_eq_of_rank_eq (by exact_mod_cast hM))
  obtain ⟨y, hyM', hy1, hcard⟩ := M'.exists_mem_norm_le_one_le_ncard_norm_eq_one
  rw [hfinM'] at hcard
  obtain ⟨x, hxM, rfl⟩ := Submodule.mem_map.mp hyM'
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hy1 hcard
  have hex_apply (i : ι) : e x i = x i := by simp [e]
  let S : Set ι := {i : ι | ‖x i‖ = 1}
  have hcardS : n + 1 ≤ S.ncard := by simpa only [hex_apply] using hcard
  obtain ⟨i₀, hi₀⟩ := S.nonempty_of_ncard_ne_zero ((Nat.succ_pos n).trans_le hcardS).ne'
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [S] at hi₀
  have hex : ‖(e : EuclideanSpace 𝕜 ι →L[𝕜] ι → 𝕜) x‖₊ ≤ 1 := by
    exact_mod_cast (pi_norm_le_iff_of_nonneg zero_le_one).mpr hy1
  let s : Finset ι := S.toFinset
  have hs : s.card = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
  have hsq : (n + 1 : ℝ≥0) ≤ ‖x‖₊ ^ 2 := by
    rw [PiLp.nnNorm_eq_of_L2, NNReal.sq_sqrt]
    calc (n + 1 : ℝ≥0) ≤ (s.card : ℝ≥0) := by exact_mod_cast hs ▸ hcardS
      _ = ∑ _i ∈ s, (1 : ℝ≥0) := by simp
      _ ≤ ∑ i ∈ s, ‖x i‖₊ ^ 2 := Finset.sum_le_sum fun i hi ↦ by
          have hi1 : ‖x i‖₊ = 1 := by
            rw [← NNReal.coe_eq_one, coe_nnNorm]
            exact Set.mem_toFinset.mp hi
          simp [hi1]
      _ ≤ ∑ i : ι, ‖x i‖₊ ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ ↦ zero_le
  have hsqrt : NNReal.sqrt (n + 1) ≤ ‖x‖₊ := NNReal.sqrt_le_iff_le_sq.mpr hsq
  have hpos : 0 < NNReal.sqrt (n + 1) := NNReal.sqrt_pos.mpr (by positivity)
  refine ⟨x, hxM, hx0, hex.trans ?_⟩
  calc (1 : ℝ≥0)
      = (NNReal.sqrt (n + 1))⁻¹ * NNReal.sqrt (n + 1) := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (NNReal.sqrt (n + 1))⁻¹ * ‖x‖₊ := by gcongr

/-- **Upper bound for `ℓ_∞ → ℓ₂`.** On a finite index type `ι` over `ℝ` or `ℂ`, the identity map
`(ι → 𝕜) →L[𝕜] EuclideanSpace 𝕜 ι` has `n`-th Bernstein number at most `√(card ι / (n + 1))`:
testing the orthogonal projections of the standard basis vectors onto an `(n + 1)`-dimensional
subspace bounds the squared coercivity constant by `card ι / (n + 1)`. -/
theorem bernsteinNumber_piLp_continuousLinearEquiv_symm_le
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] (n : ℕ) :
    ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ 𝕜)).symm :
      (ι → 𝕜) →L[𝕜] EuclideanSpace 𝕜 ι).bernsteinNumber n ≤
      NNReal.sqrt (Fintype.card ι / (n + 1)) := by
  classical
  let e : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 := PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ 𝕜)
  refine bernsteinNumber_le_iff.mpr fun M hM d hd ↦ ?_
  -- Transport `M` to `M₂ ≤ EuclideanSpace 𝕜 ι` and test coercivity on `x k = P_{M₂} e_k`.
  let M₂ : Submodule 𝕜 (EuclideanSpace 𝕜 ι) :=
    M.map (e.symm.toLinearEquiv : (ι → 𝕜) →ₗ[𝕜] EuclideanSpace 𝕜 ι)
  have hfinM₂ : Module.finrank 𝕜 M₂ = n + 1 :=
    (e.symm.toLinearEquiv.finrank_map_eq M).trans
      (Module.finrank_eq_of_rank_eq (by exact_mod_cast hM))
  let x (k : ι) : EuclideanSpace 𝕜 ι := M₂.starProjection (EuclideanSpace.single k (1 : 𝕜))
  -- For each coordinate `k`, `e (x k) ∈ M` satisfies `‖x k‖² = (x k) k ≤ ‖e (x k)‖`,
  -- whence `d ‖x k‖² ≤ ‖x k‖` and therefore `d² ‖x k‖² ≤ 1`.
  have hdk (k : ι) : (d : ℝ) ^ 2 * ‖x k‖ ^ 2 ≤ 1 := by
    have hexM : e (x k) ∈ M := by
      obtain ⟨y, hyM, hy⟩ := Submodule.mem_map.mp
        (M₂.starProjection_apply_mem (EuclideanSpace.single k (1 : 𝕜)))
      have hy' : e (x k) = y := by simpa [x] using (congrArg e hy).symm
      rwa [hy']
    have hx_coord : ‖x k‖ ^ 2 ≤ ‖e (x k)‖ := by
      calc ‖x k‖ ^ 2 = |‖x k‖ ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
        _ = ‖((‖x k‖ ^ 2 : ℝ) : 𝕜)‖ := (RCLike.norm_ofReal _).symm
        _ = ‖(x k) k‖ := by rw [← M₂.starProjection_single_apply_self k]
        _ = ‖e (x k) k‖ := by simp [e]
        _ ≤ ‖e (x k)‖ := norm_le_pi_norm (e (x k)) k
    have hd_real : (d : ℝ) * ‖e (x k)‖ ≤ ‖x k‖ := by
      have h := NNReal.coe_le_coe.mpr (hd (e (x k)) hexM)
      simpa [e] using h.trans_eq (congrArg norm (e.symm_apply_apply (x k)))
    have hdx : (d : ℝ) * ‖x k‖ ^ 2 ≤ ‖x k‖ :=
      (mul_le_mul_of_nonneg_left hx_coord d.coe_nonneg).trans hd_real
    rcases eq_or_lt_of_le (norm_nonneg (x k)) with h0 | hpos
    · rw [← h0]; norm_num
    · have h1 : (d : ℝ) * ‖x k‖ ≤ 1 :=
        le_of_mul_le_mul_right (by simpa [sq, mul_assoc] using hdx) hpos
      calc (d : ℝ) ^ 2 * ‖x k‖ ^ 2 = ((d : ℝ) * ‖x k‖) ^ 2 := by ring
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = 1 := one_pow 2
  -- Summing `d² ‖x k‖² ≤ 1` over `k : ι` uses `∑ ‖P_{M₂} e_k‖² = finrank M₂ = n + 1`.
  have hsum_norm : ∑ k : ι, ‖x k‖ ^ 2 = (n + 1 : ℝ) := by
    simpa [x, M₂.projectorDiagonal_eq_norm_sq, hfinM₂] using M₂.sum_projectorDiagonal
  have hd_sum_real : (d : ℝ) ^ 2 * (n + 1 : ℝ) ≤ Fintype.card ι := by
    calc (d : ℝ) ^ 2 * (n + 1 : ℝ) = (d : ℝ) ^ 2 * ∑ k : ι, ‖x k‖ ^ 2 := by rw [hsum_norm]
      _ = ∑ k : ι, (d : ℝ) ^ 2 * ‖x k‖ ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ _k : ι, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hdk k
      _ = Fintype.card ι := by simp
  have hd_sum : d ^ 2 * (n + 1 : ℝ≥0) ≤ Fintype.card ι := by exact_mod_cast hd_sum_real
  exact NNReal.le_sqrt_iff_sq_le.mpr ((le_div_iff₀ (by positivity)).mpr hd_sum)

end ContinuousLinearMap

namespace LinearIsometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Injectivity.** Postcomposition with a linear isometry leaves the Bernstein numbers
unchanged: `bₙ(J T) = bₙ(T)`, since `J` preserves every gain of `T`. -/
@[simp]
theorem bernsteinNumber_toContinuousLinearMap_comp (J : F →ₗᵢ[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (J.toContinuousLinearMap ∘L T).bernsteinNumber n = T.bernsteinNumber n := by
  simp [ContinuousLinearMap.bernsteinNumber_def]

end LinearIsometry

universe u

namespace TauCeti.SNumbers

section NontriviallyNormedField

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

/-- Bernstein numbers satisfy the s-number axioms over every nontrivially normed field. -/
theorem isSNumberSequence_bernstein : IsSNumberSequence (bernstein (𝕜 := 𝕜)) :=
  isStrictSNumberSequence_bernstein.toIsSNumberSequence

/-- Bernstein numbers form an injective family. -/
theorem isInjective_bernstein : IsInjective (bernstein (𝕜 := 𝕜)) where
  linearIsometry_comp J T n := J.bernsteinNumber_toContinuousLinearMap_comp T n

/-- **Minimality of the Bernstein numbers.** Every injective strict s-number sequence dominates
the Bernstein numbers: `bₙ(T) ≤ s T n`. Together with `isStrictSNumberSequence_bernstein` and
`isInjective_bernstein`, the Bernstein numbers are the smallest injective strict s-number
sequence. -/
theorem IsStrictSNumberSequence.bernsteinNumber_le {s : SNumberFamily 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : IsInjective s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.bernsteinNumber n ≤ s T n := by
  refine ContinuousLinearMap.bernsteinNumber_le_iff.mpr fun M hM d hd ↦ ?_
  rcases eq_or_ne d 0 with rfl | hd0
  · exact zero_le
  have hd0' : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd0)
  -- The coercivity bound factors `id_M` through the range of `g = T|_M`, with norm `≤ d⁻¹`.
  let g := T ∘L M.subtypeL
  obtain ⟨S, hS, hST⟩ := (ContinuousLinearMap.exists_eq_comp_rangeRestrict_iff
      (f := ContinuousLinearMap.id 𝕜 M) (g := g) (C := (d : ℝ)⁻¹) (by positivity)).mpr fun x ↦ by
    rw [ContinuousLinearMap.id_apply, inv_mul_eq_div, le_div_iff₀ hd0', mul_comm]
    exact_mod_cast hd x x.property
  have hS' : ‖S‖₊ ≤ d⁻¹ := by rwa [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_inv]
  have hsub : ‖M.subtypeL‖₊ ≤ 1 := by exact_mod_cast Submodule.norm_subtypeL_le M
  -- Normalization on `id_M`, then injectivity along the inclusion of the range of `g`.
  have key : 1 ≤ d⁻¹ * s T n :=
    calc (1 : ℝ≥0) = s (ContinuousLinearMap.id 𝕜 M) n :=
          (hs.normalize_of_lt_rank n (by rw [hM]; exact_mod_cast n.lt_succ_self)).symm
      _ = s (S ∘L g.rangeRestrict) n := by rw [← hST]
      _ ≤ ‖S‖₊ * s g.rangeRestrict n := hs.comp_le_left S _ n
      _ = ‖S‖₊ * s g n := by
          rw [← hinj.linearIsometry_comp (LinearMap.range (g : M →ₗ[𝕜] Y)).subtypeₗᵢ
            g.rangeRestrict n, Submodule.subtypeₗᵢ_toContinuousLinearMap,
            ContinuousLinearMap.subtypeL_comp_codRestrict]
      _ ≤ d⁻¹ * (s T n * ‖M.subtypeL‖₊) := by gcongr; exact hs.comp_le_right T M.subtypeL n
      _ ≤ d⁻¹ * s T n := by gcongr; exact mul_le_of_le_one_right' hsub
  simpa using (le_inv_mul_iff₀ (pos_iff_ne_zero.mpr hd0)).mp key

end NontriviallyNormedField

/-- Arithmetic step for `not_multiplicative_bernstein`: `√(3 / 2) · (√2)⁻¹ < 1`. -/
private theorem sqrt_three_div_two_mul_inv_sqrt_two_lt_one :
    NNReal.sqrt (3 / 2) * (NNReal.sqrt 2)⁻¹ < 1 := by
  rw [mul_inv_lt_iff₀ (NNReal.sqrt_pos.mpr (by norm_num)), one_mul]
  exact NNReal.sqrt_lt_sqrt.mpr (by norm_num)

/-- **Bernstein numbers are not multiplicative.** Over `ℝ` or `ℂ`, the factorization
`id : ℓ₂³ → ℓ_∞³ → ℓ₂³` gives
`1 = b₂(id) > √(3 / 2) · (√2)⁻¹ ≥ b₁(ℓ_∞³ → ℓ₂³) b₁(ℓ₂³ → ℓ_∞³)`. -/
theorem not_multiplicative_bernstein {𝕜 : Type u} [RCLike 𝕜] :
    ¬ Multiplicative (bernstein (𝕜 := 𝕜)) := by
  intro hmul
  let e : EuclideanSpace 𝕜 (Fin 3) ≃L[𝕜] (Fin 3 → 𝕜) :=
    PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin 3 ↦ 𝕜)
  let T : EuclideanSpace 𝕜 (Fin 3) →L[𝕜] (Fin 3 → 𝕜) := e
  let S : (Fin 3 → 𝕜) →L[𝕜] EuclideanSpace 𝕜 (Fin 3) := e.symm
  have hcomp : S ∘L T = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin 3)) := by
    ext x; simp [S, T]
  have hid : bernstein (S ∘L T) (1 + 1) = 1 := by
    rw [hcomp]
    exact isStrictSNumberSequence_bernstein.normalize 2
  have hT : bernstein T 1 ≤ (NNReal.sqrt 2)⁻¹ := by
    simpa [T, one_add_one_eq_two] using
      ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_le (𝕜 := 𝕜) (ι := Fin 3) 1
  have hS : bernstein S 1 ≤ NNReal.sqrt (3 / 2) := by
    simpa [S, one_add_one_eq_two] using
      ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_symm_le
        (𝕜 := 𝕜) (ι := Fin 3) 1
  exact lt_irrefl (1 : ℝ≥0) <|
    ((hid.symm.trans_le (hmul S T 1 1)).trans (mul_le_mul' hS hT)).trans_lt
      sqrt_three_div_two_mul_inv_sqrt_two_lt_one

/-- On the graph `{(x, 3 e x)}` of `3 e`, the block anti-diagonal operator
`inr ∘ e ∘ fst + (9 : 𝕜)⁻¹ • (inl ∘ e⁻¹ ∘ snd)` acts as `(3 : 𝕜)⁻¹ • ·`, yielding the
Bernstein-number lower bound `3⁻¹ ≤ bₙ(S + T)` when `rank X = n + 1`. -/
private theorem inv_three_le_bernstein_antiDiag {𝕜 X Y : Type u} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (e : X ≃L[𝕜] Y) {n : ℕ} (hrank : Module.rank 𝕜 X = n + 1) :
    (3 : ℝ≥0)⁻¹ ≤ bernstein
      ((ContinuousLinearMap.inr 𝕜 X Y) ∘L (e : X →L[𝕜] Y) ∘L (ContinuousLinearMap.fst 𝕜 X Y) +
        (9 : 𝕜)⁻¹ • ((ContinuousLinearMap.inl 𝕜 X Y) ∘L (e.symm : Y →L[𝕜] X) ∘L
          (ContinuousLinearMap.snd 𝕜 X Y))) n := by
  let S : (X × Y) →L[𝕜] (X × Y) :=
    (ContinuousLinearMap.inr 𝕜 X Y) ∘L (e : X →L[𝕜] Y) ∘L (ContinuousLinearMap.fst 𝕜 X Y)
  let T : (X × Y) →L[𝕜] (X × Y) := (9 : 𝕜)⁻¹ •
    ((ContinuousLinearMap.inl 𝕜 X Y) ∘L (e.symm : Y →L[𝕜] X) ∘L (ContinuousLinearMap.snd 𝕜 X Y))
  let φ : X →ₗ[𝕜] X × Y := LinearMap.id.prod ((3 : 𝕜) • e.toLinearEquiv.toLinearMap)
  have hφ_inj : Function.Injective φ := fun _ _ hxy ↦ congrArg Prod.fst hxy
  have hrankM : Module.rank 𝕜 (LinearMap.range φ) = n + 1 :=
    (Cardinal.lift_inj.mp (lift_rank_range_of_injective φ hφ_inj)).trans hrank
  have h3 : ‖(3 : 𝕜)⁻¹‖₊ = (3 : ℝ≥0)⁻¹ := Subtype.ext (by simp)
  have h93 : (9 : 𝕜)⁻¹ * 3 = 3⁻¹ := by norm_num
  refine (S + T).le_bernsteinNumber_of_rank_eq hrankM ?_
  rintro _ ⟨x, rfl⟩
  have hact : (S + T) (φ x) = (3 : 𝕜)⁻¹ • φ x := by
    apply Prod.ext <;> simp [S, T, φ, smul_smul, h93]
  rw [hact, nnNorm_smul, h3]

/-- Arithmetic step for `not_additive_bernstein`: `6⁻¹ + 9⁻¹ √(71 / 36) < 3⁻¹`. -/
private theorem inv_six_add_inv_nine_mul_sqrt_lt_inv_three :
    (6 : ℝ≥0)⁻¹ + 9⁻¹ * NNReal.sqrt (71 / 36) < 3⁻¹ := by
  have h : NNReal.sqrt (71 / 36) < 3 / 2 := by
    rw [← NNReal.sqrt_sq (3 / 2)]
    exact NNReal.sqrt_lt_sqrt.mpr (by norm_num)
  calc (6 : ℝ≥0)⁻¹ + 9⁻¹ * NNReal.sqrt (71 / 36)
      < 6⁻¹ + 9⁻¹ * (3 / 2) := by gcongr
    _ = 3⁻¹ := by norm_num

/-- **Bernstein numbers are not additive** (Pietsch 2008, Theorem 3). Over `ℝ` or `ℂ`, a block
anti-diagonal sum of `ℓ₂⁷¹ → ℓ_∞⁷¹` and `(9 : 𝕜)⁻¹` times `ℓ_∞⁷¹ → ℓ₂⁷¹` on `ℓ₂⁷¹ × ℓ_∞⁷¹` acts as
scalar multiplication by `(3 : 𝕜)⁻¹` on a `71`-dimensional graph subspace, giving
`b₇₀(S + T) ≥ 3⁻¹` while `b₃₅(S) + b₃₅(T) ≤ 6⁻¹ + 9⁻¹ √(71 / 36) < 3⁻¹`. -/
theorem not_additive_bernstein {𝕜 : Type u} [RCLike 𝕜] :
    ¬ Additive (bernstein (𝕜 := 𝕜)) := by
  intro hadd
  let E₂ := EuclideanSpace 𝕜 (Fin 71)
  let Einf := Fin 71 → 𝕜
  let e : E₂ ≃L[𝕜] Einf := PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin 71 ↦ 𝕜)
  let S : (E₂ × Einf) →L[𝕜] (E₂ × Einf) :=
    (ContinuousLinearMap.inr 𝕜 E₂ Einf) ∘L (e : E₂ →L[𝕜] Einf) ∘L
      (ContinuousLinearMap.fst 𝕜 E₂ Einf)
  let T₁ : (E₂ × Einf) →L[𝕜] (E₂ × Einf) :=
    (ContinuousLinearMap.inl 𝕜 E₂ Einf) ∘L (e.symm : Einf →L[𝕜] E₂) ∘L
      (ContinuousLinearMap.snd 𝕜 E₂ Einf)
  let T : (E₂ × Einf) →L[𝕜] (E₂ × Einf) := (9 : 𝕜)⁻¹ • T₁
  -- Upper bounds on `b₃₅(S)` and `b₃₅(T)` via the `ℓ₂ ↔ ℓ_∞` bounds and contraction factors.
  have hsqrt36 : NNReal.sqrt (35 + 1) = 6 := NNReal.sqrt_eq_iff_eq_sq.mpr (by norm_num)
  have hS : bernstein S 35 ≤ 6⁻¹ :=
    (isSNumberSequence_bernstein.comp_comp_le_of_norm_le_one
      (ContinuousLinearMap.norm_inr_le_one 𝕜 E₂ Einf)
      (ContinuousLinearMap.norm_fst_le 𝕜 E₂ Einf) _ 35).trans <| by
      simpa [e, hsqrt36] using
        ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_le
          (𝕜 := 𝕜) (ι := Fin 71) 35
  have hT : bernstein T 35 ≤ 9⁻¹ * NNReal.sqrt (71 / 36) := by
    have hT₁ : bernstein T₁ 35 ≤ NNReal.sqrt (71 / 36) :=
      (isSNumberSequence_bernstein.comp_comp_le_of_norm_le_one
        (ContinuousLinearMap.norm_inl_le_one 𝕜 E₂ Einf)
        (ContinuousLinearMap.norm_snd_le 𝕜 E₂ Einf) _ 35).trans <| by
        have h36 : (35 : ℝ≥0) + 1 = 36 := by norm_num
        simpa [e, h36] using
          ContinuousLinearMap.bernsteinNumber_piLp_continuousLinearEquiv_symm_le
            (𝕜 := 𝕜) (ι := Fin 71) 35
    have h9 : ‖(9 : 𝕜)⁻¹‖₊ = (9 : ℝ≥0)⁻¹ := Subtype.ext (by simp)
    calc bernstein T 35 = ‖(9 : 𝕜)⁻¹‖₊ * bernstein T₁ 35 :=
          isSNumberSequence_bernstein.smul (9 : 𝕜)⁻¹ T₁ 35
      _ = 9⁻¹ * bernstein T₁ 35 := by rw [h9]
      _ ≤ 9⁻¹ * NNReal.sqrt (71 / 36) := by gcongr
  -- Lower bound `3⁻¹ ≤ b₇₀(S + T)` on the `71`-dimensional graph subspace, giving a contradiction.
  have hrank : Module.rank 𝕜 E₂ = (35 + 35 : ℕ) + 1 := by
    rw [e.toLinearEquiv.rank_eq, ← Module.finrank_eq_rank, Module.finrank_pi, Fintype.card_fin]
    norm_num
  have hST : (3 : ℝ≥0)⁻¹ ≤ bernstein (S + T) (35 + 35) :=
    inv_three_le_bernstein_antiDiag e hrank
  exact lt_irrefl (3 : ℝ≥0)⁻¹ <|
    (hST.trans ((hadd S T 35 35).trans (add_le_add hS hT))).trans_lt
      inv_six_add_inv_nine_mul_sqrt_lt_inv_three

end TauCeti.SNumbers
