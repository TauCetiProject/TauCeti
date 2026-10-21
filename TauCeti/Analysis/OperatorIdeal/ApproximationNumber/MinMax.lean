/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Min–max bounds for approximation numbers

The approximation number `aₙ(T)` of a bounded linear map `T : E →L[𝕜] F` is defined as the
distance from `T` to the maps of rank at most `n`. This file gives the two variational bounds that
make it computable from the geometry of `T`, in the spirit of the Courant–Fischer principle.

* **Coercive subspaces bound `aₙ(T)` from below.** If `V ≤ E` has rank greater than `n` and
  `c ‖x‖ ≤ ‖T x‖` for every `x ∈ V`, then `c ≤ aₙ(T)`. Every map `R` of rank at most `n` kills a
  nonzero vector of `V`, and on that vector `T - R` agrees with `T`. This needs neither an inner
  product nor completeness, only a normed source space. Over `ℝ` or `ℂ` it suffices to check the
  bound on unit vectors, and the subspace may be given as the span of `n + 1` linearly
  independent vectors.
* **Orthogonal tails compute `aₙ(T)`.** On a complete inner product space `E`, `aₙ(T)` is the
  infimum, over subspaces `V` of rank at most `n`, of the operator norm of `T` restricted to
  `Vᗮ`. Composing `T` with the orthogonal projection onto `V` gives an approximant of rank at
  most `n` whose error is `T` on `Vᗮ`. Conversely, for an approximant `R` of rank at most `n` the
  subspace `V = (ker R)ᗮ` has rank at most `n`, and `R` vanishes up to norm zero on
  `Vᗮ = closure (ker R)`, so `T` restricted to `Vᗮ` is no larger than `T - R`.
* **The converse min–max localization.** The coercive-subspace bound has a converse on a pair of
  spaces `E`, `F` exactly when every strict lower bound `r < aₙ(T)` is beaten by a uniform
  coercivity bound on the span of `n + 1` linearly independent vectors. This is the property
  `TauCeti.HasMinMaxLowerBound 𝕜 E F`; it says that `aₙ(T)` is the supremum of the coercivity
  constants of `T` on `(n + 1)`-dimensional subspaces, and it is the input from which the Ky Fan
  triangle inequality for approximation numbers is derived.
* **Complete source spaces have the localization property.** Over `ℝ` or `ℂ`, let `E` be
  complete and `c ≥ 0`. Either `T` is `c`-coercive on an `(n + 1)`-dimensional span, or `T` is
  `c`-contractive on the orthogonal complement of a subspace of rank at most `n`. This is the
  argument behind Sylvester's law of inertia, applied to the hermitian form `‖T x‖² - c² ‖x‖²`.
  A maximal subspace on which the form is nonnegative has dimension at most `n`, unless the
  first alternative holds. The form is nonpositive on the subspace orthogonal to it for the form,
  and that subspace is the orthogonal complement of a subspace of rank at most `n`, by the Riesz
  representation of the form. For `r < c < aₙ(T)`, the second alternative would give
  `aₙ(T) ≤ c` by the orthogonal-tail bound.

## Main declarations

* `ContinuousLinearMap.le_singularValue_of_lt_rank`: a subspace of rank greater than `n` on
  which `T` is `c`-coercive forces `c ≤ aₙ(T)`.
* `ContinuousLinearMap.le_singularValue_of_lt_rank_of_unit_norm`: the same, with the coercivity
  bound checked on unit vectors.
* `ContinuousLinearMap.le_singularValue_of_linearIndependent`: the same, for the span of `n + 1`
  linearly independent vectors.
* `ContinuousLinearMap.singularValue_id`: the approximation numbers of the identity are `1`
  below the rank of the space and `0` from it on.
* `ContinuousLinearMap.singularValue_le_nnnorm_comp_orthogonal`: `aₙ(T) ≤ ‖T|_{Vᗮ}‖` for every
  subspace `V` of rank at most `n`.
* `ContinuousLinearMap.singularValue_eq_iInf_nnnorm_comp_orthogonal`: on a complete inner product
  space, `aₙ(T)` is the infimum of `‖T|_{Vᗮ}‖` over subspaces `V` of rank at most `n`.
* `ContinuousLinearMap.exists_linearIndependent_or_exists_rank_le`: on a complete inner product
  space, `T` is `c`-coercive on the span of `n + 1` linearly independent vectors or
  `c`-contractive on the orthogonal complement of a subspace of rank at most `n`.
* `TauCeti.HasMinMaxLowerBound`: the converse min–max localization property of a pair of spaces.
* `TauCeti.hasMinMaxLowerBound_iff_forall_isLUB`: a pair has this property exactly when, for every
  `T` and `n`, `aₙ(T)` is the least upper bound of the coercivity constants of `T` on spans of
  `n + 1` linearly independent vectors.
* `TauCeti.HasMinMaxLowerBound.exists_rank_eq_coercive`: on a pair with the property, a strict
  lower bound for the first `i` approximation numbers of `T` is a coercivity constant of `T` on a
  subspace of rank `i`.
* `TauCeti.HasMinMaxLowerBound.of_completeSpace`: a complete inner product space has the
  converse min–max localization property towards every inner product space.
* `TauCeti.HasMinMaxLowerBound.exists_singularValue_le_compression`: on a pair with the property,
  the first `k` approximation numbers of `T` are those of a compression of `T` to
  finite-dimensional subspaces, up to any `δ > 0`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped InnerProductSpace NNReal

namespace ContinuousLinearMap

/-! ### Lower bounds from coercive subspaces -/

section Coercive

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Coercive-subspace lower bound.** If `V` has rank greater than `n` and `c ‖x‖ ≤ ‖T x‖` for
every `x ∈ V`, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_lt_rank (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 E}
    (hV : (n : Cardinal) < Module.rank 𝕜 V) {c : ℝ} (hc : ∀ x ∈ V, c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValue n := by
  rcases le_or_gt c 0 with h | h
  · exact h.trans (NNReal.coe_nonneg _)
  lift c to ℝ≥0 using h.le
  refine NNReal.coe_le_coe.mpr (le_singularValue_iff.mpr fun R hR ↦ ?_)
  -- Since `rank R ≤ n < rank V`, the map `R` kills a nonzero vector of `V`.
  obtain ⟨x, hxV, hRx, hx0⟩ : ∃ x ∈ V, R x = 0 ∧ x ≠ 0 := by
    by_contra! h
    have hle := (Submodule.lift_rank_le_of_disjoint_ker (Submodule.disjoint_def.mpr h)).trans
      (Cardinal.lift_le.mpr hR)
    rw [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle
    exact hV.not_ge hle
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine NNReal.coe_le_coe.mp (le_of_mul_le_mul_right ?_ hx)
  calc (c : ℝ) * ‖x‖ ≤ ‖T x‖ := hc x hxV
    _ = ‖(T - R) x‖ := by simp [hRx]
    _ ≤ ‖T - R‖ * ‖x‖ := (T - R).le_opNorm x

/-- **Independent-family lower bound.** If `T` is `c`-coercive on the span of `n + 1` linearly
independent vectors, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_linearIndependent (T : E →L[𝕜] F) {n : ℕ} {v : Fin (n + 1) → E}
    (hv : LinearIndependent 𝕜 v) {c : ℝ}
    (hc : ∀ x ∈ Submodule.span 𝕜 (Set.range v), c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValue n := by
  refine T.le_singularValue_of_lt_rank ?_ hc
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  rw [← Module.finrank_eq_rank, finrank_span_eq_card hv, Fintype.card_fin]
  exact_mod_cast n.lt_succ_self

/-- **Approximation numbers of the identity.** On a normed space of rank `r`, a possibly infinite
cardinal, `aₙ(id) = 1` for `n < r` and `aₙ(id) = 0` for `r ≤ n`. -/
@[simp]
theorem singularValue_id (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 E).singularValue n =
      if (n : Cardinal) < Module.rank 𝕜 E then 1 else 0 := by
  split_ifs with hn
  · refine le_antisymm (((ContinuousLinearMap.id 𝕜 E).singularValue_le_nnnorm n).trans ?_) ?_
    · exact_mod_cast norm_id_le
    · exact_mod_cast (ContinuousLinearMap.id 𝕜 E).le_singularValue_of_lt_rank
        (V := ⊤) (by rwa [rank_top]) (c := 1) (by simp)
  · exact singularValue_eq_zero_of_rank_domain_le _ (le_of_not_gt hn)

/-- **Approximation numbers of a finite-dimensional identity.** `aₙ(id) = 1` below the dimension
and `aₙ(id) = 0` at and above it. -/
theorem singularValue_id_of_finiteDimensional [FiniteDimensional 𝕜 E] (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 E).singularValue n =
      if n < Module.finrank 𝕜 E then 1 else 0 := by
  simp [← Module.finrank_eq_rank]

end Coercive

section UnitNorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Coercive-subspace lower bound on unit vectors.** If `V` has rank greater than `n` and
`c ≤ ‖T x‖` for every unit vector `x ∈ V`, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_lt_rank_of_unit_norm (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 E}
    (hV : (n : Cardinal) < Module.rank 𝕜 V) {c : ℝ}
    (hc : ∀ x ∈ V, ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ T.singularValue n := by
  refine T.le_singularValue_of_lt_rank hV fun x hxV ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hu := hc (((‖x‖⁻¹ : ℝ) : 𝕜) • x) (V.smul_mem _ hxV) (by
    rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hx.ne'])
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, ← div_eq_inv_mul,
    le_div_iff₀ hx] at hu
  exact hu

end UnitNorm

/-! ### The orthogonal-tail formula -/

section OrthogonalTail

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Composing with the projection onto a subspace of rank at most `n` has rank at most `n`.
The target needs only a topology and a module structure; no target norm is used. -/
theorem rank_comp_starProjection_le {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module 𝕜 F] (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 E}
    [V.HasOrthogonalProjection] (hV : Module.rank 𝕜 V ≤ n) :
    (T ∘L V.starProjection).rank ≤ n := by
  have hP : (V.starProjection : E →ₗ[𝕜] E).rank ≤ n := by
    rwa [LinearMap.rank, Submodule.range_starProjection]
  have hle := (LinearMap.lift_rank_comp_le_right (V.starProjection : E →ₗ[𝕜] E)
    (T : E →ₗ[𝕜] F)).trans (Cardinal.lift_le.mpr hP)
  rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The projection approximant's error is bounded by the norm on the orthogonal complement. -/
theorem nnnorm_sub_comp_starProjection_le (T : E →L[𝕜] F) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : ‖T - T ∘L V.starProjection‖₊ ≤ ‖T ∘L Vᗮ.subtypeL‖₊ := by
  refine opNNNorm_le_bound _ _ fun x ↦ ?_
  have hx : x - V.starProjection x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
  calc ‖(T - T ∘L V.starProjection) x‖₊ = ‖(T ∘L Vᗮ.subtypeL) ⟨_, hx⟩‖₊ := by simp
    _ ≤ ‖T ∘L Vᗮ.subtypeL‖₊ * ‖x - V.starProjection x‖₊ :=
      (T ∘L Vᗮ.subtypeL).le_opNNNorm ⟨_, hx⟩
    _ ≤ ‖T ∘L Vᗮ.subtypeL‖₊ * ‖x‖₊ := by
      gcongr
      rw [← Submodule.starProjection_orthogonal_val]
      exact_mod_cast Vᗮ.norm_starProjection_apply_le x

/-- **Orthogonal-tail upper bound.** For every subspace `V` of rank at most `n`, `aₙ(T)` is at
most the operator norm of `T` restricted to `Vᗮ`. -/
theorem singularValue_le_nnnorm_comp_orthogonal (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 E}
    (hV : Module.rank 𝕜 V ≤ n) : T.singularValue n ≤ ‖T ∘L Vᗮ.subtypeL‖₊ := by
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt (Cardinal.natCast_lt_aleph0))
  exact (T.singularValue_le_nnnorm_sub (T.rank_comp_starProjection_le hV)).trans
    (T.nnnorm_sub_comp_starProjection_le V)

/-- **Orthogonal-tail min–max formula.** On a complete inner product space, `aₙ(T)` is the
infimum, over subspaces `V` of rank at most `n`, of the operator norm of `T` restricted
to `Vᗮ`. -/
theorem singularValue_eq_iInf_nnnorm_comp_orthogonal [CompleteSpace E] (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValue n =
      ⨅ V : {V : Submodule 𝕜 E // Module.rank 𝕜 V ≤ n}, ‖T ∘L V.1ᗮ.subtypeL‖₊ := by
  have : Nonempty {V : Submodule 𝕜 E // Module.rank 𝕜 V ≤ n} := ⟨⟨⊥, by simp⟩⟩
  refine le_antisymm (le_ciInf fun V ↦ T.singularValue_le_nnnorm_comp_orthogonal V.2) ?_
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  -- `V = (ker R)ᗮ` meets `ker R` trivially, so `rank V ≤ rank R ≤ n`.
  set V := (LinearMap.ker (R : E →ₗ[𝕜] F))ᗮ
  have hV : Module.rank 𝕜 V ≤ n := by
    have hle := (Submodule.lift_rank_le_of_disjoint_ker
      (LinearMap.ker (R : E →ₗ[𝕜] F)).orthogonal_disjoint.symm).trans (Cardinal.lift_le.mpr hR)
    rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle
  refine (ciInf_le (OrderBot.bddBelow _) ⟨V, hV⟩).trans ?_
  -- `Vᗮ` is the closure of `ker R`, on which `‖R x‖ = 0`; so `‖T x‖ ≤ ‖(T - R) x‖` there.
  refine opNNNorm_le_bound _ _ fun x ↦ ?_
  have hx : (x : E) ∈ closure (LinearMap.ker (R : E →ₗ[𝕜] F) : Set E) := by
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
    exact x.2
  have hRx : ‖R x‖₊ = 0 := by
    rw [← NNReal.coe_eq_zero, coe_nnnorm, ← mem_closure_zero_iff_norm]
    exact map_mem_closure R.continuous hx fun y hy ↦ hy
  calc ‖(T ∘L Vᗮ.subtypeL) x‖₊ = ‖(T - R) x + R x‖₊ := by simp
    _ ≤ ‖(T - R) x‖₊ := by simpa [hRx] using nnnorm_add_le ((T - R) x) (R x)
    _ ≤ ‖T - R‖₊ * ‖x‖₊ := (T - R).le_opNNNorm x

end OrthogonalTail

section Inertia

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

open Submodule

/-- Let `T` be `c`-coercive on the span of a linearly independent family `v`, and let `L`
represent the hermitian form `⟪T x, T y⟫ - c² ⟪x, y⟫`. A vector `y` orthogonal to every `L (v i)`,
on which `T` is more than `c`-coercive, extends `v` to a linearly independent family on whose span
`T` is still `c`-coercive. -/
private theorem linearIndependent_snoc_of_mem_orthogonal (T : E →L[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    {L : E →ₗ[𝕜] E} (hL : ∀ x y, ⟪L x, y⟫_𝕜 = ⟪T x, T y⟫_𝕜 - ((c ^ 2 : ℝ) : 𝕜) * ⟪x, y⟫_𝕜)
    {k : ℕ} {v : Fin k → E} (hv : LinearIndependent 𝕜 v)
    (hvc : ∀ x ∈ span 𝕜 (Set.range v), c * ‖x‖ ≤ ‖T x‖)
    {y : E} (hy : y ∈ (span 𝕜 (Set.range (L ∘ v)))ᗮ) (hTy : c * ‖y‖ < ‖T y‖) :
    LinearIndependent 𝕜 (Fin.snoc v y : Fin (k + 1) → E) ∧
      ∀ x ∈ span 𝕜 (Set.range (Fin.snoc v y : Fin (k + 1) → E)), c * ‖x‖ ≤ ‖T x‖ := by
  -- `y` is orthogonal to the span of `v` for the form `⟪T x, T y⟫ - c² ⟪x, y⟫`.
  have horth : ∀ x ∈ span 𝕜 (Set.range v), ⟪T y, T x⟫_𝕜 = ((c ^ 2 : ℝ) : 𝕜) * ⟪y, x⟫_𝕜 := by
    intro x hx
    have hLx : L x ∈ span 𝕜 (Set.range (L ∘ v)) := by
      rw [Set.range_comp, ← map_span]
      exact mem_map_of_mem hx
    have h0 := (mem_orthogonal _ _).mp hy _ hLx
    rw [hL, sub_eq_zero] at h0
    rw [← inner_conj_symm, h0, map_mul, inner_conj_symm, RCLike.conj_ofReal]
  have hsq_y : (c * ‖y‖) ^ 2 < ‖T y‖ ^ 2 := by gcongr
  have hy_not : y ∉ span 𝕜 (Set.range v) := fun hy' ↦ by
    have h := congrArg RCLike.re (horth y hy')
    rw [inner_self_eq_norm_sq, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h
    nlinarith
  refine ⟨linearIndependent_finSnoc.mpr ⟨hv, hy_not⟩, fun z hz ↦ ?_⟩
  rw [Fin.range_snoc, mem_span_insert] at hz
  obtain ⟨a, x, hx, rfl⟩ := hz
  -- Expanding both squares, the cross terms agree up to the factor `c²`.
  have hcross : RCLike.re ⟪a • T y, T x⟫_𝕜 = c ^ 2 * RCLike.re ⟪a • y, x⟫_𝕜 := by
    rw [inner_smul_left, inner_smul_left, horth x hx, mul_left_comm, RCLike.re_ofReal_mul]
  have hsq_x : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by gcongr; exact hvc x hx
  have key : (c * ‖a • y + x‖) ^ 2 ≤ ‖T (a • y + x)‖ ^ 2 := by
    rw [map_add, map_smul, mul_pow, norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜), hcross,
      norm_smul, norm_smul]
    nlinarith [mul_le_mul_of_nonneg_left hsq_y.le (sq_nonneg ‖a‖)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp key

/-- **Coercive subspace or contractive orthogonal tail.** Let `T : E →L[𝕜] F` be a bounded linear
map on a complete inner product space, `n : ℕ` and `c ≥ 0`. Either `T` is `c`-coercive,
`c ‖x‖ ≤ ‖T x‖`, on the span of `n + 1` linearly independent vectors, or there is a subspace
`U` of rank at most `n` on whose orthogonal complement `‖T x‖ ≤ c ‖x‖`. -/
theorem exists_linearIndependent_or_exists_rank_le [CompleteSpace E] (T : E →L[𝕜] F) (n : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    (∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
      ∀ x ∈ span 𝕜 (Set.range v), c * ‖x‖ ≤ ‖T x‖) ∨
    ∃ U : Submodule 𝕜 E, Module.rank 𝕜 U ≤ n ∧ ∀ x ∈ Uᗮ, ‖T x‖ ≤ c * ‖x‖ := by
  classical
  -- This is the maximality argument behind Sylvester's law of inertia, for the hermitian form
  -- `‖T x‖² - c² ‖x‖²`: a maximal subspace on which the form is nonnegative has dimension at most
  -- `n` unless the first alternative holds, and the form is nonpositive on the subspace orthogonal
  -- to it with respect to the form.
  -- `P k`: `T` is `c`-coercive on the span of `k` linearly independent vectors.
  set P : ℕ → Prop := fun k ↦ ∃ v : Fin k → E, LinearIndependent 𝕜 v ∧
    ∀ x ∈ span 𝕜 (Set.range v), c * ‖x‖ ≤ ‖T x‖
  by_cases hn : P (n + 1)
  · exact Or.inl hn
  refine Or.inr ?_
  -- Restricting a family keeps the coercivity, so `P` fails beyond `n`.
  have hle : ∀ m, P m → m ≤ n := by
    rintro m ⟨v, hv, hvc⟩
    by_contra! hm
    exact hn ⟨v ∘ Fin.castLE hm, hv.comp _ (Fin.castLE_injective hm),
      fun x hx ↦ hvc x (span_mono (Set.range_comp_subset_range _ _) hx)⟩
  have h0 : P 0 := ⟨Fin.elim0, linearIndependent_empty_type, fun x hx ↦ by
    rw [Set.range_eq_empty, span_empty, mem_bot] at hx
    simp [hx]⟩
  -- Take a family `v` of maximal length.
  obtain ⟨v, hv, hvc⟩ : P (Nat.findGreatest P n) := Nat.findGreatest_spec (Nat.zero_le n) h0
  -- `L` represents the hermitian form `⟪T x, T y⟫ - c² ⟪x, y⟫`.
  set L : E →L[𝕜] E := InnerProductSpace.continuousLinearMapOfBilin
    ((innerSL 𝕜).bilinearComp T T - ((c ^ 2 : ℝ) : 𝕜) • innerSL 𝕜)
  have hL : ∀ x y, ⟪L x, y⟫_𝕜 = ⟪T x, T y⟫_𝕜 - ((c ^ 2 : ℝ) : 𝕜) * ⟪x, y⟫_𝕜 := fun x y ↦ by
    simp [L]
  refine ⟨span 𝕜 (Set.range ((L : E →ₗ[𝕜] E) ∘ v)), ?_, fun y hy ↦ ?_⟩
  · have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range ((L : E →ₗ[𝕜] E) ∘ v))
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (finrank_range_le_card _).trans
      ((Fintype.card_fin _).trans_le (hle _ ⟨v, hv, hvc⟩))
  · by_contra! hTy
    obtain ⟨hv', hvc'⟩ :=
      linearIndependent_snoc_of_mem_orthogonal T hc (L := L) hL hv hvc hy hTy
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hle _ ⟨_, hv', hvc'⟩) ⟨_, hv', hvc'⟩

end Inertia

end ContinuousLinearMap

/-! ### The converse min–max localization -/

namespace TauCeti

section HasMinMaxLowerBound

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A pair of spaces `E`, `F` has the **converse min–max localization property** when, for every
bounded linear map `T : E →L[𝕜] F` and every `n`, each nonnegative strict lower bound
`0 ≤ r < aₙ(T)` is improved by a uniform coercivity bound `s ‖x‖ ≤ ‖T x‖`, with `r < s`, on the
span of some `n + 1` linearly independent vectors.

Together with the coercive-subspace bound
`ContinuousLinearMap.le_singularValue_of_linearIndependent` this says that `aₙ(T)` is the supremum
of the coercivity constants of `T` on `(n + 1)`-dimensional subspaces
(`HasMinMaxLowerBound.isLUB_singularValue`). -/
def HasMinMaxLowerBound : Prop :=
  ∀ (T : E →L[𝕜] F) (n : ℕ) {r : ℝ}, 0 ≤ r → r < T.singularValue n →
    ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
      ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖

variable {𝕜 E F}

/-- Unfolding `HasMinMaxLowerBound`. -/
theorem hasMinMaxLowerBound_iff : HasMinMaxLowerBound 𝕜 E F ↔
    ∀ (T : E →L[𝕜] F) (n : ℕ) {r : ℝ}, 0 ≤ r → r < T.singularValue n →
      ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
        ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖ :=
  Iff.rfl

/-- **Coercive subspaces of a prescribed rank.** On a pair with the converse min–max localization
property, if `0 ≤ t` lies strictly below the first `i` approximation numbers of `T`, then `T` is
`t`-coercive on a subspace of rank `i`. The source may be seminormed. -/
theorem HasMinMaxLowerBound.exists_rank_eq_coercive (h : HasMinMaxLowerBound 𝕜 E F)
    (T : E →L[𝕜] F) {i : ℕ} {t : ℝ} (ht : 0 ≤ t) (hi : ∀ k < i, t < T.singularValue k) :
    ∃ V : Submodule 𝕜 E, Module.rank 𝕜 V = i ∧ ∀ x ∈ V, t * ‖x‖ ≤ ‖T x‖ := by
  rcases i with _ | i
  · exact ⟨⊥, by simp, fun x hx ↦ by simp [(Submodule.mem_bot 𝕜).mp hx]⟩
  obtain ⟨s, hts, v, hv, hs⟩ := hasMinMaxLowerBound_iff.mp h T i ht (hi i i.lt_succ_self)
  refine ⟨Submodule.span 𝕜 (Set.range v), ?_, fun x hx ↦
    (mul_le_mul_of_nonneg_right hts.le (norm_nonneg x)).trans (hs x hx)⟩
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  rw [← Module.finrank_eq_rank, finrank_span_eq_card hv, Fintype.card_fin]

end HasMinMaxLowerBound

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The set of coercivity constants of `T` on spans of `n + 1` linearly independent vectors is
bounded above by `aₙ(T)`, and `aₙ(T)` is its least upper bound exactly on pairs with the converse
min–max localization property. -/
theorem hasMinMaxLowerBound_iff_forall_isLUB :
    HasMinMaxLowerBound 𝕜 E F ↔ ∀ (T : E →L[𝕜] F) (n : ℕ),
      IsLUB {s : ℝ≥0 | ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
        ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖} (T.singularValue n) := by
  rw [hasMinMaxLowerBound_iff]
  refine ⟨fun h T n ↦ ⟨?_, fun b hb ↦ ?_⟩, fun h T n r hr0 hr ↦ ?_⟩
  · rintro s ⟨v, hv, hs⟩
    exact_mod_cast T.le_singularValue_of_linearIndependent hv hs
  · -- A bound `b < aₙ(T)` is beaten by the coercivity constant the property supplies.
    by_contra! hlt
    obtain ⟨s, hbs, v, hv, hs⟩ := h T n b.2 (by exact_mod_cast hlt)
    have hs0 : 0 ≤ s := b.2.trans hbs.le
    exact hbs.not_ge (by exact_mod_cast hb (show (⟨s, hs0⟩ : ℝ≥0) ∈ _ from ⟨v, hv, hs⟩))
  · -- `r` lies below the least upper bound, so some member of the set exceeds it.
    lift r to ℝ≥0 using hr0
    obtain ⟨s, ⟨v, hv, hs⟩, hrs⟩ := (lt_isLUB_iff (h T n)).mp (by exact_mod_cast hr)
    exact ⟨s, by exact_mod_cast hrs, v, hv, hs⟩

/-- **Finite-restriction supremum.** On a pair with the converse min–max localization property,
`aₙ(T)` is the least upper bound of the coercivity constants of `T` on spans of `n + 1` linearly
independent vectors. -/
theorem HasMinMaxLowerBound.isLUB_singularValue (h : HasMinMaxLowerBound 𝕜 E F)
    (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB {s : ℝ≥0 | ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
      ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖} (T.singularValue n) :=
  hasMinMaxLowerBound_iff_forall_isLUB.mp h T n

section CompleteSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Converse min–max localization.** If `E` is a complete inner product space, then for every
bounded `T : E →L[𝕜] F` into an inner product space and every `0 ≤ r < aₙ(T)`, the map `T` is
`s`-coercive with `r < s` on the span of `n + 1` linearly independent vectors. Thus `aₙ(T)` is the
supremum of the coercivity constants of `T` on `(n + 1)`-dimensional subspaces
(`TauCeti.HasMinMaxLowerBound.isLUB_singularValue`). -/
theorem HasMinMaxLowerBound.of_completeSpace [CompleteSpace E] : HasMinMaxLowerBound 𝕜 E F := by
  refine hasMinMaxLowerBound_iff.mpr fun T n r hr0 hr ↦ ?_
  -- For `c` strictly between `r` and `aₙ(T)`, a contractive orthogonal tail would give
  -- `aₙ(T) ≤ c`, so `T` is `c`-coercive on an `(n + 1)`-dimensional span.
  set c : ℝ := (r + T.singularValue n) / 2 with hc
  have hrc : r < c := by rw [hc]; linarith
  have hca : c < T.singularValue n := by rw [hc]; linarith
  obtain ⟨v, hv, hvc⟩ | ⟨U, hU, hUc⟩ :=
    T.exists_linearIndependent_or_exists_rank_le n (c := c) (by positivity)
  · exact ⟨c, hrc, v, hv, hvc⟩
  · have hle : (T.singularValue n : ℝ) ≤ c :=
      (NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_comp_orthogonal hU)).trans
        (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ hUc x x.2)
    linarith

end CompleteSpace

section Compression

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Finite-dimensional compressions.** On a pair with the converse min–max localization
property, for every `k` and `δ > 0` there is a finite-dimensional subspace `V` such that the
compression `V → T(V)` of `T`, followed by the orthogonal projection onto `T(V)`, lowers none of
the first `k` approximation numbers of `T` by more than `δ`. -/
theorem HasMinMaxLowerBound.exists_singularValue_le_compression (h : HasMinMaxLowerBound 𝕜 E F)
    (T : E →L[𝕜] F) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (V : Submodule 𝕜 E) (_ : FiniteDimensional 𝕜 V), ∀ n < k,
      (T.singularValue n : ℝ) ≤
        ((V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp
          (T.comp V.subtypeL)).singularValue n + δ := by
  -- For each `n`, either `aₙ(T) ≤ δ` or `T` is `(aₙ(T) - δ)`-coercive on the span of `n + 1`
  -- linearly independent vectors.
  have hv : ∀ n, ∃ v : Fin (n + 1) → E, δ < T.singularValue n →
      LinearIndependent 𝕜 v ∧ ∀ x ∈ Submodule.span 𝕜 (Set.range v),
        (T.singularValue n - δ) * ‖x‖ ≤ ‖T x‖ := by
    intro n
    by_cases hn : δ < T.singularValue n
    · obtain ⟨s, hs, v, hv, hvs⟩ := hasMinMaxLowerBound_iff.mp h T n
        (sub_nonneg.mpr hn.le) (sub_lt_self _ hδ)
      exact ⟨v, fun _ ↦ ⟨hv, fun x hx ↦
        (mul_le_mul_of_nonneg_right hs.le (norm_nonneg x)).trans (hvs x hx)⟩⟩
    · exact ⟨0, fun h ↦ absurd h hn⟩
  choose v hv using hv
  -- `V` is spanned by the witnesses for the first `k` indices.
  set V : Submodule 𝕜 E := Submodule.span 𝕜 (⋃ n ∈ Finset.range k, Set.range (v n))
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜
    ((Finset.range k).finite_toSet.biUnion fun n _ ↦ Set.finite_range (v n))
  set W : Submodule 𝕜 F := V.map (T : E →ₗ[𝕜] F)
  refine ⟨V, this, fun n hn ↦ ?_⟩
  by_cases hδn : δ < T.singularValue n
  · -- The compression keeps the coercivity bound on the span of the witnesses.
    obtain ⟨hvi, hvs⟩ := hv n hδn
    have hmem : ∀ j, v n j ∈ V := fun j ↦ Submodule.subset_span
      (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hn)) ⟨j, rfl⟩)
    have hw : LinearIndependent 𝕜 fun j ↦ (⟨v n j, hmem j⟩ : V) :=
      LinearIndependent.of_comp V.subtype hvi
    rw [← sub_le_iff_le_add]
    refine ContinuousLinearMap.le_singularValue_of_linearIndependent _ hw fun x hx ↦ ?_
    have hx' : (x : E) ∈ Submodule.span 𝕜 (Set.range (v n)) := by
      have := Submodule.mem_map_of_mem (f := V.subtype) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hW : T x ∈ W := Submodule.mem_map_of_mem x.2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      W.norm_orthogonalProjectionOnto_apply hW]
    exact hvs x hx'
  · exact (le_of_not_gt hδn).trans (le_add_of_nonneg_left (NNReal.coe_nonneg _))

end Compression

end TauCeti
