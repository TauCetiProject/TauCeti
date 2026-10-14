/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.HasMinMaxLowerBound`: the converse min–max localization property of a pair of spaces.
* `TauCeti.hasMinMaxLowerBound_iff_forall_isLUB`: a pair has this property exactly when, for every
  `T` and `n`, `aₙ(T)` is the least upper bound of the coercivity constants of `T` on spans of
  `n + 1` linearly independent vectors.
* `TauCeti.HasMinMaxLowerBound.exists_singularValue_le_compression`: on such a pair, the first `k`
  approximation numbers of `T` are those of a compression of `T` to finite-dimensional subspaces,
  up to any `δ > 0`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped NNReal

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

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Composing with the projection onto a subspace of rank at most `n` has rank at most `n`. -/
theorem rank_comp_starProjection_le (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 E}
    [V.HasOrthogonalProjection] (hV : Module.rank 𝕜 V ≤ n) :
    (T ∘L V.starProjection).rank ≤ n := by
  have hP : (V.starProjection : E →ₗ[𝕜] E).rank ≤ n := by
    rwa [LinearMap.rank, Submodule.range_starProjection]
  have hle := (LinearMap.lift_rank_comp_le_right (V.starProjection : E →ₗ[𝕜] E)
    (T : E →ₗ[𝕜] F)).trans (Cardinal.lift_le.mpr hP)
  rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle

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

variable {𝕜 E F} in
/-- Unfolding `HasMinMaxLowerBound`. -/
theorem hasMinMaxLowerBound_iff : HasMinMaxLowerBound 𝕜 E F ↔
    ∀ (T : E →L[𝕜] F) (n : ℕ) {r : ℝ}, 0 ≤ r → r < T.singularValue n →
      ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
        ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖ :=
  Iff.rfl

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
