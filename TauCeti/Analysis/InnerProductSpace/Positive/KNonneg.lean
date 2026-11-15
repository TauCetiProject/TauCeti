/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KyFan
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Data.Fin.Basic

/-!
# `k`-nonnegative and `k`-positive operators

An operator `T` on an inner product space is **`k`-nonnegative** (`LinearMap.IsKNonneg`) when
its diagonal entries along any orthonormal family of `k` vectors have nonnegative sum,
`0 ≤ ∑ᵢ re ⟪T wᵢ, wᵢ⟫`, and **`k`-positive** (`LinearMap.IsKPos`) when that sum is always
positive. For `k = 1` and symmetric `T` this is ordinary positivity. The condition interpolates
between positivity and nonnegativity of the trace: by Ky Fan's minimum principle a symmetric
`T` on an `n`-dimensional space with `k ≤ n` is `k`-nonnegative exactly when the sum of its `k`
smallest eigenvalues is nonnegative (`LinearMap.IsSymmetric.isKNonneg_iff_sum_eigenvalues_nonneg`),
and equivalently when the compression of `T` to every `k`-dimensional subspace has nonnegative
trace (`LinearMap.isKNonneg_iff_forall_re_trace_nonneg`).

The case `k = 2` is the curvature condition of Böhm and Wilking: a curvature operator on the
bivectors `Λ²V` is `2`-nonnegative when the sum of its two smallest eigenvalues is nonnegative.
In dimension three this is nonnegativity of the Ricci curvature. Operators that are
`k`-nonnegative form a closed convex cone, invariant under conjugation by linear isometries,
and `k`-nonnegativity implies `m`-nonnegativity for `1 ≤ k ≤ m`
(`LinearMap.IsKNonneg.mono`): positive operators are `2`-nonnegative.

## Main declarations

* `LinearMap.IsKNonneg`, `LinearMap.IsKPos`: the two conditions.
* `LinearMap.IsKNonneg.mono`, `LinearMap.IsKPos.mono`: monotonicity in `k`.
* `LinearMap.isPositive_iff_isSymmetric_and_isKNonneg_one`: positivity is `1`-nonnegativity of
  a symmetric operator.
* `LinearMap.IsSymmetric.isKNonneg_iff_sum_eigenvalues_nonneg`,
  `LinearMap.IsSymmetric.isKPos_iff_sum_eigenvalues_pos`: the eigenvalue characterizations, and
  `LinearMap.IsSymmetric.isKNonneg_two_iff`, `LinearMap.IsSymmetric.isKPos_two_iff`: their form
  for the two smallest eigenvalues.
* `LinearMap.trace_orthogonalProjectionOnto_comp_comp_subtype`: the trace of the compression of
  an operator to a finite-dimensional subspace is its diagonal sum along an orthonormal basis.
* `LinearMap.isKNonneg_iff_forall_re_trace_nonneg`,
  `LinearMap.isKPos_iff_forall_re_trace_pos`: the characterizations by traces of compressions.
* `LinearMap.isKNonneg_conj_iff`, `LinearMap.isKPos_conj_iff`: invariance under conjugation by
  linear isometries.
* `ContinuousLinearMap.isClosed_setOf_isKNonneg`: the `k`-nonnegative bounded operators form a
  closed set.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. **167** (2008), 1079–1097.
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations. I*,
  Proc. Nat. Acad. Sci. U.S.A. **35** (1949), 652–655.
-/

public section

open Module Finset

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- An operator `T` is **`k`-nonnegative** when along every orthonormal family `(wᵢ)` of `k`
vectors its diagonal entries have nonnegative sum, `0 ≤ ∑ᵢ re ⟪T wᵢ, wᵢ⟫`. -/
def IsKNonneg (T : E →ₗ[𝕜] E) (k : ℕ) : Prop :=
  ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫

/-- An operator `T` is **`k`-positive** when along every orthonormal family `(wᵢ)` of `k`
vectors its diagonal entries have positive sum, `0 < ∑ᵢ re ⟪T wᵢ, wᵢ⟫`. -/
def IsKPos (T : E →ₗ[𝕜] E) (k : ℕ) : Prop :=
  ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 < ∑ i, RCLike.re ⟪T (w i), w i⟫

variable {T S : E →ₗ[𝕜] E} {k m : ℕ}

theorem isKNonneg_iff :
    T.IsKNonneg k ↔ ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  Iff.rfl

theorem isKPos_iff :
    T.IsKPos k ↔ ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 < ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  Iff.rfl

/-- A condition on the diagonal sums of `T` along all orthonormal families of `k` vectors holds
along every orthonormal family indexed by a type with `k` elements. -/
private theorem forall_orthonormal_fintype (P : ℝ → Prop)
    (h : ∀ w : Fin k → E, Orthonormal 𝕜 w → P (∑ i, RCLike.re ⟪T (w i), w i⟫)) {ι : Type*}
    [Fintype ι] (hι : Fintype.card ι = k) {w : ι → E} (hw : Orthonormal 𝕜 w) :
    P (∑ i, RCLike.re ⟪T (w i), w i⟫) := by
  let e := Fintype.equivFinOfCardEq hι
  simpa [← e.symm.sum_comp] using h (w ∘ e.symm) (hw.comp _ e.symm.injective)

/-- A `k`-nonnegative operator has nonnegative diagonal sum along every orthonormal family indexed
by a type with `k` elements. -/
theorem IsKNonneg.sum_re_inner_nonneg (h : T.IsKNonneg k) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = k) {w : ι → E} (hw : Orthonormal 𝕜 w) :
    0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  forall_orthonormal_fintype (0 ≤ ·) h hι hw

/-- A `k`-positive operator has positive diagonal sum along every orthonormal family indexed by a
type with `k` elements. -/
theorem IsKPos.sum_re_inner_pos (h : T.IsKPos k) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = k) {w : ι → E} (hw : Orthonormal 𝕜 w) :
    0 < ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  forall_orthonormal_fintype (0 < ·) h hι hw

/-- A `k`-positive operator is `k`-nonnegative. -/
theorem IsKPos.isKNonneg (h : T.IsKPos k) : T.IsKNonneg k :=
  fun w hw ↦ (h w hw).le

/-- Every operator is `0`-nonnegative: the empty sum vanishes. -/
@[simp]
theorem isKNonneg_zero_right (T : E →ₗ[𝕜] E) : T.IsKNonneg 0 :=
  fun _ _ ↦ by simp

/-- No operator is `0`-positive: the empty sum vanishes. -/
@[simp]
theorem not_isKPos_zero_right (T : E →ₗ[𝕜] E) : ¬T.IsKPos 0 :=
  fun h ↦ by simpa using h Fin.elim0 ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩

/-- `1`-nonnegativity is nonnegativity of the quadratic form `x ↦ re ⟪T x, x⟫`. -/
theorem isKNonneg_one_iff : T.IsKNonneg 1 ↔ ∀ x, 0 ≤ RCLike.re ⟪T x, x⟫ := by
  refine ⟨fun h x ↦ ?_, fun h w _ ↦ by simpa using h (w 0)⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  -- `x` is `‖x‖` times a unit vector `u`, so its diagonal entry is `‖x‖ ^ 2` times that of `u`.
  set u := (‖x‖⁻¹ : 𝕜) • x
  have hu : Orthonormal 𝕜 fun _ : Fin 1 ↦ u :=
    ⟨fun _ ↦ norm_smul_inv_norm hx, fun i j hij ↦ absurd (Subsingleton.elim i j) hij⟩
  have hxu : x = (‖x‖ : 𝕜) • u := by
    simp [u, smul_smul, norm_ne_zero_iff.2 hx]
  have hscale : RCLike.re ⟪T x, x⟫ = ‖x‖ ^ 2 * RCLike.re ⟪T u, u⟫ := by
    conv_lhs => rw [hxu]
    simp [inner_smul_left, inner_smul_right]
    ring
  rw [hscale]
  exact mul_nonneg (sq_nonneg _) (by simpa using h _ hu)

/-- A positive operator is `k`-nonnegative for every `k`. -/
theorem IsPositive.isKNonneg (hT : T.IsPositive) (k : ℕ) : T.IsKNonneg k :=
  fun _ _ ↦ sum_nonneg fun _ _ ↦ hT.re_inner_nonneg_left _

/-- A symmetric operator is positive exactly when it is `1`-nonnegative. -/
theorem isPositive_iff_isSymmetric_and_isKNonneg_one :
    T.IsPositive ↔ T.IsSymmetric ∧ T.IsKNonneg 1 := by
  rw [isKNonneg_one_iff, IsPositive]

/-- A `k`-nonnegative operator with `k ≠ 0` is `(k + 1)`-nonnegative: averaging over the `k + 1`
ways to drop one vector from an orthonormal family of `k + 1` vectors. -/
theorem IsKNonneg.succ (h : T.IsKNonneg k) (hk : k ≠ 0) : T.IsKNonneg (k + 1) := by
  intro w hw
  have hsum := Fin.sum_sum_succAbove (k := k) fun i ↦ RCLike.re ⟪T (w i), w i⟫
  rw [nsmul_eq_mul] at hsum
  have hk' : (0 : ℝ) < k := by positivity
  have : 0 ≤ (k : ℝ) * ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
    hsum ▸ sum_nonneg fun j _ ↦ h _ (hw.comp _ (Fin.succAbove_right_injective (p := j)))
  exact (mul_nonneg_iff_of_pos_left hk').1 this

/-- `k`-nonnegativity implies `m`-nonnegativity for `1 ≤ k ≤ m`. -/
theorem IsKNonneg.mono (h : T.IsKNonneg k) (hk : k ≠ 0) (hkm : k ≤ m) : T.IsKNonneg m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m hkm ih => exact ih.succ (by omega)

/-- A `k`-positive operator is `(k + 1)`-positive. -/
theorem IsKPos.succ (h : T.IsKPos k) : T.IsKPos (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd h (not_isKPos_zero_right T)
  intro w hw
  have hsum := Fin.sum_sum_succAbove (k := k) fun i ↦ RCLike.re ⟪T (w i), w i⟫
  rw [nsmul_eq_mul] at hsum
  have : 0 < (k : ℝ) * ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
    hsum ▸ sum_pos (fun j _ ↦ h _ (hw.comp _ (Fin.succAbove_right_injective (p := j))))
      univ_nonempty
  exact pos_of_mul_pos_right this (by positivity)

/-- `k`-positivity implies `m`-positivity for `k ≤ m`. -/
theorem IsKPos.mono (h : T.IsKPos k) (hkm : k ≤ m) : T.IsKPos m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ

/-! ### The cone of `k`-nonnegative operators -/

/-- The zero operator is `k`-nonnegative. -/
protected theorem IsKNonneg.zero (k : ℕ) : (0 : E →ₗ[𝕜] E).IsKNonneg k :=
  fun _ _ ↦ by simp

/-- The sum of two `k`-nonnegative operators is `k`-nonnegative. -/
protected theorem IsKNonneg.add (hT : T.IsKNonneg k) (hS : S.IsKNonneg k) : (T + S).IsKNonneg k :=
  fun w hw ↦ by simpa [inner_add_left, sum_add_distrib] using add_nonneg (hT w hw) (hS w hw)

/-- The sum of a `k`-positive and a `k`-nonnegative operator is `k`-positive. -/
theorem IsKPos.add_isKNonneg (hT : T.IsKPos k) (hS : S.IsKNonneg k) : (T + S).IsKPos k :=
  fun w hw ↦ by
    simpa [inner_add_left, sum_add_distrib] using add_pos_of_pos_of_nonneg (hT w hw) (hS w hw)

/-- A nonnegative real multiple of a `k`-nonnegative operator is `k`-nonnegative. -/
theorem IsKNonneg.smul (hT : T.IsKNonneg k) {c : ℝ} (hc : 0 ≤ c) : ((c : 𝕜) • T).IsKNonneg k :=
  fun w hw ↦ by simpa [inner_smul_left, ← mul_sum] using mul_nonneg hc (hT w hw)

/-- A positive real multiple of a `k`-positive operator is `k`-positive. -/
theorem IsKPos.smul (hT : T.IsKPos k) {c : ℝ} (hc : 0 < c) : ((c : 𝕜) • T).IsKPos k :=
  fun w hw ↦ by simpa [inner_smul_left, ← mul_sum] using mul_pos hc (hT w hw)

/-- A condition on the diagonal sums along all orthonormal families of `k` vectors holds for the
conjugate of `T` by a linear isometry equivalence exactly when it holds for `T`. -/
private theorem forall_orthonormal_conj_iff (P : ℝ → Prop) (U : E ≃ₗᵢ[𝕜] F) :
    (∀ w : Fin k → F, Orthonormal 𝕜 w →
        P (∑ i, RCLike.re ⟪U.toLinearEquiv.conj T (w i), w i⟫)) ↔
      ∀ w : Fin k → E, Orthonormal 𝕜 w → P (∑ i, RCLike.re ⟪T (w i), w i⟫) := by
  simp only [U.inner_toLinearEquiv_conj_apply]
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ h _ (hw.comp_linearIsometryEquiv U.symm)⟩
  simpa using h _ (hw.comp_linearIsometryEquiv U)

/-- Conjugating by a linear isometry equivalence preserves `k`-nonnegativity. -/
@[simp]
theorem isKNonneg_conj_iff (U : E ≃ₗᵢ[𝕜] F) :
    (U.toLinearEquiv.conj T).IsKNonneg k ↔ T.IsKNonneg k :=
  forall_orthonormal_conj_iff (0 ≤ ·) U

/-- Conjugating by a linear isometry equivalence preserves `k`-positivity. -/
@[simp]
theorem isKPos_conj_iff (U : E ≃ₗᵢ[𝕜] F) :
    (U.toLinearEquiv.conj T).IsKPos k ↔ T.IsKPos k :=
  forall_orthonormal_conj_iff (0 < ·) U

/-! ### Traces of compressions -/

/-- Along an orthonormal basis `b` of a finite-dimensional subspace `W`, the trace of the
compression `P_W ∘ T ∘ ι_W` of `T` to `W` is the sum of the diagonal entries `⟪bᵢ, T bᵢ⟫` of `T`
along `b`. -/
theorem trace_orthogonalProjectionOnto_comp_comp_subtype (T : E →ₗ[𝕜] E) (W : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 W] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 W) :
    trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype) =
      ∑ i, ⟪(b i : E), T (b i)⟫ := by
  rw [trace_eq_sum_inner _ b]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [coe_comp, Function.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Along an orthonormal basis `b` of a finite-dimensional subspace `W`, the real part of the trace
of the compression of `T` to `W` is the sum of the real diagonal entries of `T` along `b`. -/
private theorem re_trace_compression_eq_sum (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 W) :
    RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) =
      ∑ i, RCLike.re ⟪T (b i), b i⟫ := by
  rw [trace_orthogonalProjectionOnto_comp_comp_subtype T W b, map_sum]
  exact sum_congr rfl fun i _ ↦ inner_re_symm _ _

/-- A condition on the diagonal sums of `T` along all orthonormal families of `k` vectors is the
same condition on the traces of the compressions of `T` to all `k`-dimensional subspaces. -/
private theorem forall_orthonormal_iff_forall_re_trace (P : ℝ → Prop) :
    (∀ w : Fin k → E, Orthonormal 𝕜 w → P (∑ i, RCLike.re ⟪T (w i), w i⟫)) ↔
      ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
        P (RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype))) := by
  refine ⟨fun h W _ hW ↦ ?_, fun h w hw ↦ ?_⟩
  · let b := (stdOrthonormalBasis 𝕜 W).reindex (finCongr hW)
    rw [re_trace_compression_eq_sum W b]
    exact h _ (b.orthonormal.comp_linearIsometry W.subtypeₗᵢ)
  · -- Test the hypothesis on the span of `w`, with the orthonormal basis given by `w`.
    set W := Submodule.span 𝕜 (Set.range w)
    have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w)
    have hli := hw.linearIndependent
    let b : OrthonormalBasis (Fin k) 𝕜 W := (Basis.span hli).toOrthonormalBasis (by
      convert orthonormal_span hw
      simp [Basis.span_apply])
    have hb (i : Fin k) : (b i : E) = w i := by simp [b, Basis.span_apply]
    have := h W ((finrank_span_eq_card hli).trans (Fintype.card_fin k))
    simpa [re_trace_compression_eq_sum W b, hb] using this

/-- `T` is `k`-nonnegative exactly when its compression to every `k`-dimensional subspace has
trace with nonnegative real part. -/
theorem isKNonneg_iff_forall_re_trace_nonneg :
    T.IsKNonneg k ↔ ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
      0 ≤ RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) :=
  forall_orthonormal_iff_forall_re_trace (0 ≤ ·)

/-- `T` is `k`-positive exactly when its compression to every `k`-dimensional subspace has trace
with positive real part. -/
theorem isKPos_iff_forall_re_trace_pos :
    T.IsKPos k ↔ ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
      0 < RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) :=
  forall_orthonormal_iff_forall_re_trace (0 < ·)

/-! ### Eigenvalues -/

namespace IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ}

/-- A symmetric operator on an `n`-dimensional space is `k`-nonnegative, for `k ≤ n`, exactly
when the sum `λₙ₋₁ + ⋯ + λₙ₋ₖ` of its `k` smallest eigenvalues is nonnegative. -/
theorem isKNonneg_iff_sum_eigenvalues_nonneg (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hk : k ≤ n) :
    T.IsKNonneg k ↔
      0 ≤ ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < k, hT.eigenvalues hn j.rev := by
  obtain ⟨⟨w, hw, hsum⟩, hle⟩ := hT.isLeast_sum_re_inner_apply_self hn hk
  exact ⟨fun h ↦ hsum ▸ h w hw, fun h w' hw' ↦ h.trans (hle ⟨w', hw', rfl⟩)⟩

/-- A symmetric operator on an `n`-dimensional space is `k`-positive, for `k ≤ n`, exactly when
the sum `λₙ₋₁ + ⋯ + λₙ₋ₖ` of its `k` smallest eigenvalues is positive. -/
theorem isKPos_iff_sum_eigenvalues_pos (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hk : k ≤ n) :
    T.IsKPos k ↔
      0 < ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < k, hT.eigenvalues hn j.rev := by
  obtain ⟨⟨w, hw, hsum⟩, hle⟩ := hT.isLeast_sum_re_inner_apply_self hn hk
  exact ⟨fun h ↦ hsum ▸ h w hw, fun h w' hw' ↦ h.trans_le (hle ⟨w', hw', rfl⟩)⟩

/-- A symmetric operator on a space of dimension `n + 2` is `2`-nonnegative exactly when the sum of
its two smallest eigenvalues is nonnegative. -/
theorem isKNonneg_two_iff (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n + 2) :
    T.IsKNonneg 2 ↔
      0 ≤ hT.eigenvalues hn (Fin.last (n + 1)) + hT.eigenvalues hn (Fin.last n).castSucc := by
  rw [hT.isKNonneg_iff_sum_eigenvalues_nonneg hn le_add_self,
    Fin.sum_filter_val_lt_eq_sum_castLE le_add_self, Fin.sum_univ_two]
  rfl

/-- A symmetric operator on a space of dimension `n + 2` is `2`-positive exactly when the sum of
its two smallest eigenvalues is positive. -/
theorem isKPos_two_iff (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n + 2) :
    T.IsKPos 2 ↔
      0 < hT.eigenvalues hn (Fin.last (n + 1)) + hT.eigenvalues hn (Fin.last n).castSucc := by
  rw [hT.isKPos_iff_sum_eigenvalues_pos hn le_add_self,
    Fin.sum_filter_val_lt_eq_sum_castLE le_add_self, Fin.sum_univ_two]
  rfl

end IsSymmetric

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `k`-nonnegative bounded operators form a closed subset of `E →L[𝕜] E`. -/
theorem isClosed_setOf_isKNonneg (k : ℕ) :
    IsClosed {T : E →L[𝕜] E | (T : E →ₗ[𝕜] E).IsKNonneg k} := by
  simp only [LinearMap.IsKNonneg, coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (by fun_prop)

end ContinuousLinearMap
