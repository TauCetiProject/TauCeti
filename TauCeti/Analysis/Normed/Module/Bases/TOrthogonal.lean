/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal

/-!
# `t`-orthogonal families and bases of nonarchimedean normed modules

Let `R` be a normed ring, `M` a normed `R`-module and `t` a nonnegative real number. A family
`e : I → M` is `t`-*orthogonal* (`TauCeti.IsTOrthogonalFamily R t e`) if every finite linear
combination satisfies

`t * max_{i ∈ s} ‖a i • e i‖ ≤ ‖∑ i ∈ s, a i • e i‖`,

with the empty maximum zero. In an ultrametric module the reverse inequality with `t = 1` always
holds, so `1`-orthogonality is the familiar condition that the norm of a combination is the
largest norm of its terms (`TauCeti.isTOrthogonalFamily_one_iff`); an orthonormal family is
`1`-orthogonal. For `0 < t < 1` the condition is the approximate orthogonality with which bases of
Banach spaces of countable type are built over an arbitrary complete nonarchimedean field, where
exactly orthogonal bases need not exist.

A `t`-*orthogonal basis* (`TauCeti.IsTOrthogonalBasis R t e`) is a `t`-orthogonal family of
nonzero vectors with dense span. The main results are:

* `TauCeti.IsTOrthogonalFamily.mul_iSup_norm_smul_le_of_hasSum`: `t`-orthogonality passes to
  unconditional sums, `t * ⨆ i, ‖a i • e i‖ ≤ ‖∑' i, a i • e i‖`; together with the
  ultrametric bound `IsUltrametricDist.norm_tsum_le` this pins the norm of an infinite
  combination between `t` times the largest norm of its terms and that largest norm;
* `TauCeti.IsTOrthogonalBasis.exists_hasSum` and `TauCeti.IsTOrthogonalBasis.eq_of_hasSum`:
  for `t > 0`, over a complete normed ring acting norm-multiplicatively on an ultrametric
  module, every vector is the unconditional sum of a unique family `a i • e i`;
* `TauCeti.IsTOrthogonalBasis.toUnconditionalSchauderBasis`: over a complete nontrivially
  normed field `K`, a `t`-orthogonal basis with `t > 0` is an unconditional Schauder basis in the
  sense of Mathlib's `UnconditionalSchauderBasis`, whose coordinate functionals satisfy
  `t * ‖coord i x‖ * ‖e i‖ ≤ ‖x‖` and `‖coord i x‖ * ‖e i‖ → 0` along the cofinite filter.

Existence and uniqueness of expansions need neither completeness of `M` nor a discrete
valuation. Completeness of `M` is used only in `TauCeti.IsTOrthogonalBasis.coord_tsum`, to sum an
arbitrary family of coefficients with `‖a i‖ * ‖e i‖ → 0`, so that the coordinates identify `M`
with such families.
The comparison with Mathlib's Schauder bases lets the general projection theory of
`GeneralSchauderBasis` apply to `t`-orthogonal bases without being duplicated here.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

variable {R K I J M N : Type*}

section Defs

variable [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M]

variable (R) in
/-- A family `e : I → M` is **`t`-orthogonal** if for every finite linear combination
`∑ i ∈ s, a i • e i`, the product of `t` with the largest norm `s.sup fun i ↦ ‖a i • e i‖₊` of its
terms (the empty maximum being zero) is at most the norm of the combination. -/
def IsTOrthogonalFamily (t : ℝ≥0) (e : I → M) : Prop :=
  ∀ (s : Finset I) (a : I → R), t * (s.sup fun i ↦ ‖a i • e i‖₊) ≤ ‖∑ i ∈ s, a i • e i‖₊

/-- A `t`-orthogonal family is characterized by the lower bound for every finite linear
combination. This is the introduction and elimination interface for `IsTOrthogonalFamily`. -/
theorem isTOrthogonalFamily_def {t : ℝ≥0} {e : I → M} :
    IsTOrthogonalFamily R t e ↔
      ∀ (s : Finset I) (a : I → R), t * (s.sup fun i ↦ ‖a i • e i‖₊) ≤ ‖∑ i ∈ s, a i • e i‖₊ :=
  Iff.rfl

variable (R) in
/-- A **`t`-orthogonal basis** of a normed module is a `t`-orthogonal family of nonzero vectors
whose span is dense. -/
structure IsTOrthogonalBasis (t : ℝ≥0) (e : I → M) : Prop where
  /-- A `t`-orthogonal basis is a `t`-orthogonal family. -/
  isTOrthogonalFamily : IsTOrthogonalFamily R t e
  /-- The vectors of a `t`-orthogonal basis are nonzero. -/
  ne_zero : ∀ i, e i ≠ 0
  /-- The span of a `t`-orthogonal basis is dense. -/
  dense_span : Dense (Submodule.span R (Set.range e) : Set M)

/-- Every family is `0`-orthogonal. -/
@[simp]
theorem isTOrthogonalFamily_zero (e : I → M) : IsTOrthogonalFamily R 0 e := fun s a ↦ by
  simp

/-- In an ultrametric module a family is `1`-orthogonal exactly when the norm of every finite
linear combination is the largest norm of its terms. -/
theorem isTOrthogonalFamily_one_iff [IsUltrametricDist M] {e : I → M} :
    IsTOrthogonalFamily R 1 e ↔
      ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊ := by
  simp only [isTOrthogonalFamily_def, one_mul]
  exact forall₂_congr fun s a ↦
    ⟨fun h ↦ le_antisymm (Finset.nnnorm_sum_le_sup_nnnorm s _) h, ge_of_eq⟩

end Defs

namespace IsTOrthogonalFamily

section Seminormed

variable [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M] {t t' : ℝ≥0} {e : I → M}

/-- A `t`-orthogonal family is `t'`-orthogonal for every `t' ≤ t`. -/
theorem mono (he : IsTOrthogonalFamily R t e) (h : t' ≤ t) : IsTOrthogonalFamily R t' e :=
  fun s a ↦ (mul_le_mul_left h _).trans (he s a)

/-- In a finite linear combination of a `t`-orthogonal family, `t` times the norm of each term
is at most the norm of the combination. -/
theorem mul_norm_smul_le (he : IsTOrthogonalFamily R t e) {s : Finset I} {i : I} (hi : i ∈ s)
    (a : I → R) : t * ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖ := by
  have := (mul_le_mul_right (Finset.le_sup (f := fun j ↦ ‖a j • e j‖₊) hi) t).trans (he s a)
  exact_mod_cast this

/-- The finitely supported version of `IsTOrthogonalFamily.mul_norm_smul_le`: `t` times the norm
of each term of a finitely supported combination is at most the norm of the combination. -/
theorem mul_norm_smul_le_norm_linearCombination (he : IsTOrthogonalFamily R t e) (c : I →₀ R)
    (i : I) : t * ‖c i • e i‖ ≤ ‖Finsupp.linearCombination R e c‖ := by
  classical
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset c (Finset.subset_insert i c.support) (fun j r ↦ r • e j)
      fun _ _ ↦ zero_smul R _]
  exact he.mul_norm_smul_le (Finset.mem_insert_self i _) c

/-- Reindexing a `t`-orthogonal family along an injective map gives a `t`-orthogonal family. -/
theorem comp (he : IsTOrthogonalFamily R t e) {f : J → I} (hf : Function.Injective f) :
    IsTOrthogonalFamily R t (e ∘ f) := fun s a ↦ by
  simpa [Finset.sum_map, Finset.sup_map, Function.comp_def, hf.extend_apply] using
    he (s.map ⟨f, hf⟩) (Function.extend f a 0)

/-- The image of a `t`-orthogonal family under a linear isometry is `t`-orthogonal. -/
theorem map [SeminormedAddCommGroup N] [Module R N] (he : IsTOrthogonalFamily R t e)
    (u : M →ₗᵢ[R] N) : IsTOrthogonalFamily R t (u ∘ e) := fun s a ↦ by
  have hterm (i : I) : ‖a i • u (e i)‖₊ = ‖a i • e i‖₊ := by rw [← map_smul, u.nnnorm_map]
  simpa only [Function.comp_apply, hterm, ← map_smul, ← map_sum, u.nnnorm_map] using he s a

/-- **`t`-orthogonality of unconditional sums**: if `x` is the unconditional sum of the
`a i • e i` for a `t`-orthogonal family `e`, then `t` times the norm of each term is at most
`‖x‖`. -/
theorem mul_norm_smul_le_of_hasSum (he : IsTOrthogonalFamily R t e) {a : I → R} {x : M}
    (h : HasSum (fun i ↦ a i • e i) x) (i : I) : t * ‖a i • e i‖ ≤ ‖x‖ := by
  have hT : Tendsto (fun s : Finset I ↦ ‖∑ j ∈ s, a j • e j‖) atTop (𝓝 ‖x‖) := by
    simpa only [SummationFilter.unconditional_filter] using h.norm
  exact ge_of_tendsto hT <| (eventually_ge_atTop {i}).mono fun s hs ↦
    he.mul_norm_smul_le (hs (Finset.mem_singleton_self i)) a

/-- **`t`-orthogonality of unconditional sums**, supremum form: if `x` is the unconditional sum
of the `a i • e i` for a `t`-orthogonal family `e`, then `t * ⨆ i, ‖a i • e i‖ ≤ ‖x‖`. The
reverse ultrametric bound `‖x‖ ≤ ⨆ i, ‖a i • e i‖` is `IsUltrametricDist.norm_tsum_le`. -/
theorem mul_iSup_norm_smul_le_of_hasSum (he : IsTOrthogonalFamily R t e) {a : I → R} {x : M}
    (h : HasSum (fun i ↦ a i • e i) x) : t * ⨆ i, ‖a i • e i‖ ≤ ‖x‖ := by
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [← le_div_iff₀' ht']
  exact Real.iSup_le (fun i ↦ (le_div_iff₀' ht').2 (he.mul_norm_smul_le_of_hasSum h i))
    (div_nonneg (norm_nonneg _) ht'.le)

end Seminormed

section Normed

variable [SeminormedRing R] [NormedAddCommGroup M] [Module R M] {t : ℝ≥0} {e : I → M}

/-- A `t`-orthogonal family of nonzero vectors with `t > 0` is linearly independent over a ring
acting without zero divisors. -/
theorem linearIndependent [NoZeroSMulDivisors R M] (he : IsTOrthogonalFamily R t e) (ht : 0 < t)
    (h0 : ∀ i, e i ≠ 0) : LinearIndependent R e := by
  refine linearIndependent_iff'.2 fun s a h i hi ↦ ?_
  have hle : (t : ℝ) * ‖a i • e i‖ ≤ 0 := by simpa [h] using he.mul_norm_smul_le hi a
  have : a i • e i = 0 :=
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle (by exact_mod_cast ht))
  exact (eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_right (h0 i)

/-- **Uniqueness of terms of expansions**: for a `t`-orthogonal family with `t > 0`, two
unconditional expansions `∑ a i • e i` and `∑ b i • e i` of the same vector have the same
terms. -/
theorem smul_eq_smul_of_hasSum (he : IsTOrthogonalFamily R t e) (ht : 0 < t) {a b : I → R}
    {x : M} (ha : HasSum (fun i ↦ a i • e i) x) (hb : HasSum (fun i ↦ b i • e i) x) (i : I) :
    a i • e i = b i • e i := by
  have hab : HasSum (fun i ↦ (a - b) i • e i) 0 := by
    simpa [sub_smul] using ha.sub hb
  have hle : (t : ℝ) * ‖(a - b) i • e i‖ ≤ 0 := by
    simpa using he.mul_norm_smul_le_of_hasSum hab i
  rw [← sub_eq_zero, ← sub_smul, ← Pi.sub_apply]
  exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle (by exact_mod_cast ht))

end Normed

end IsTOrthogonalFamily

/-- An orthonormal family is `t`-orthogonal for every `t ≤ 1`. -/
theorem IsOrthonormalFamily.isTOrthogonalFamily [SeminormedRing R] [SeminormedAddCommGroup M]
    [Module R M] {e : I → M} (he : IsOrthonormalFamily R e) {t : ℝ≥0} (ht : t ≤ 1) :
    IsTOrthogonalFamily R t e := by
  refine IsTOrthogonalFamily.mono (fun s a ↦ ?_) ht
  have hterm : ∀ i, ‖a i • e i‖₊ = ‖a i‖₊ := fun i ↦ NNReal.eq (he.norm_smul i (a i))
  simp only [hterm, one_mul, isOrthonormalFamily_def.1 he s a, le_refl]

/-- Over a nontrivial normed ring, an orthonormal basis is a `t`-orthogonal basis for every
`t ≤ 1`. -/
theorem IsOrthonormalBasis.isTOrthogonalBasis [NormedRing R] [Nontrivial R]
    [SeminormedAddCommGroup M] [Module R M] {e : I → M} (he : IsOrthonormalBasis R e) {t : ℝ≥0}
    (ht : t ≤ 1) : IsTOrthogonalBasis R t e where
  isTOrthogonalFamily := he.isOrthonormalFamily.isTOrthogonalFamily ht
  ne_zero i h := by
    have h1 := he.isOrthonormalFamily.norm_apply i
    rw [h, norm_zero] at h1
    exact one_ne_zero (norm_eq_zero.1 h1.symm)
  dense_span := he.dense_span

/-- If `w` is `r`-orthogonal to a submodule `F` (that is, `r * ‖w‖ ≤ ‖w - z‖` for `z ∈ F`) with
`r ≤ 1`, then in an ultrametric space `r * max ‖c • w‖ ‖z‖ ≤ ‖c • w + z‖` for every scalar `c` and
every `z ∈ F`. -/
theorem mul_max_nnnorm_le_nnnorm_smul_add [NormedField K] [NormedAddCommGroup M]
    [NormedSpace K M] [IsUltrametricDist M] {F : Submodule K M} {w : M} {r : ℝ≥0} (hr : r ≤ 1)
    (hw : ∀ z ∈ F, r * ‖w‖₊ ≤ ‖w - z‖₊) (c : K) {z : M} (hz : z ∈ F) :
    r * max ‖c • w‖₊ ‖z‖₊ ≤ ‖c • w + z‖₊ := by
  have h₁ : r * ‖c • w‖₊ ≤ ‖c • w + z‖₊ := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    have : c • w + z = c • (w - (-c⁻¹) • z) := by
      rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ hc, neg_smul, one_smul, sub_neg_eq_add]
    rw [this, nnnorm_smul, nnnorm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hw _ (F.smul_mem _ hz)) zero_le
  rw [mul_max_of_nonneg _ _ zero_le]
  refine max_le h₁ ?_
  rcases le_or_gt ‖z‖₊ ‖c • w‖₊ with h | h
  · exact (mul_le_mul_of_nonneg_left h zero_le).trans h₁
  · rw [IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm h.ne, max_eq_right h.le]
    exact mul_le_of_le_one_left zero_le hr

/-- If each `e N` is `T (N + 1) / T N`-orthogonal to the span of the previous vectors, for a
non-increasing sequence `T` of positive constants at most one, then in an ultrametric space
the vectors `e i` with `i < N` form a `T N`-orthogonal family. -/
theorem isTOrthogonalFamily_Iio_of_mul_nnnorm_le_nnnorm_sub [NormedField K]
    [NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M] {e : ℕ → M} {T : ℕ → ℝ≥0}
    (hT : Antitone T) (hT' : ∀ n, 0 < T n ∧ T n ≤ 1)
    (he : ∀ N, ∀ z ∈ Submodule.span K (e '' Set.Iio N), T (N + 1) / T N * ‖e N‖₊ ≤ ‖e N - z‖₊)
    (N : ℕ) : IsTOrthogonalFamily K (T N) (fun i : Set.Iio N ↦ e i) := by
  -- Reduce to finite combinations of the `e i`, `i < N`, indexed by finite sets of naturals.
  suffices key : ∀ s : Finset ℕ, (∀ i ∈ s, i < N) → ∀ a : ℕ → K,
      T N * s.sup (fun i ↦ ‖a i • e i‖₊) ≤ ‖∑ i ∈ s, a i • e i‖₊ by
    intro s a
    have hN (i : Set.Iio N) : (i : ℕ) < N := i.2
    have h := key (s.map (Function.Embedding.subtype _)) (by simp +contextual)
      fun i ↦ if h : i < N then a ⟨i, h⟩ else 0
    simpa [Finset.sup_map, Finset.sum_map, Function.comp_def, hN] using h
  induction N with
  | zero =>
    intro s hs a
    rw [Finset.eq_empty_of_forall_notMem fun i hi ↦ Nat.not_lt_zero i (hs i hi)]
    simp
  | succ N ih =>
    intro s hs a
    have hs' (i : ℕ) (hi : i ∈ s) (hiN : i ≠ N) : i < N :=
      lt_of_le_of_ne (Nat.lt_succ_iff.1 (hs i hi)) hiN
    by_cases hN : N ∈ s
    · -- Split off the last term `a N • e N`; the others lie in the span of the previous vectors.
      rw [← Finset.insert_erase hN, Finset.sum_insert (Finset.notMem_erase N s),
        Finset.sup_insert]
      have hlt (i : ℕ) (hi : i ∈ s.erase N) : i < N :=
        hs' i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      have hz : ∑ i ∈ s.erase N, a i • e i ∈ Submodule.span K (e '' Set.Iio N) :=
        Submodule.sum_mem _ fun i hi ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hlt i hi, rfl⟩)
      have hTN : T (N + 1) = T (N + 1) / T N * T N := (div_mul_cancel₀ _ (hT' N).1.ne').symm
      calc T (N + 1) * max ‖a N • e N‖₊ ((s.erase N).sup fun i ↦ ‖a i • e i‖₊)
          = T (N + 1) / T N * max (T N * ‖a N • e N‖₊)
              (T N * (s.erase N).sup fun i ↦ ‖a i • e i‖₊) := by
            rw [← mul_max_of_nonneg _ _ zero_le, ← mul_assoc, ← hTN]
        _ ≤ T (N + 1) / T N * max ‖a N • e N‖₊ ‖∑ i ∈ s.erase N, a i • e i‖₊ := by
            gcongr
            · exact mul_le_of_le_one_left zero_le (hT' N).2
            · exact ih _ hlt a
        _ ≤ ‖a N • e N + ∑ i ∈ s.erase N, a i • e i‖₊ :=
            mul_max_nnnorm_le_nnnorm_smul_add
              (div_le_one_of_le₀ (hT N.le_succ) zero_le) (he N) (a N) hz
    · exact (mul_le_mul_of_nonneg_right (hT N.le_succ) zero_le).trans
        (ih s (fun i hi ↦ hs' i hi fun h ↦ hN (h ▸ hi)) a)

namespace IsTOrthogonalBasis

/-- Reindexing a `t`-orthogonal basis along an equivalence gives a `t`-orthogonal basis. -/
theorem comp_equiv [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M] {t : ℝ≥0}
    {e : I → M} (he : IsTOrthogonalBasis R t e) (σ : J ≃ I) : IsTOrthogonalBasis R t (e ∘ σ) where
  isTOrthogonalFamily := he.isTOrthogonalFamily.comp σ.injective
  ne_zero j := he.ne_zero (σ j)
  dense_span := by
    rw [σ.surjective.range_comp]
    exact he.dense_span

/-- **Uniqueness of expansions in a `t`-orthogonal basis**: for `t > 0`, over a ring acting
without zero divisors, two unconditional expansions `∑ a i • e i` and `∑ b i • e i` of the same
vector have the same coefficients. -/
theorem eq_of_hasSum [SeminormedRing R] [NormedAddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] {t : ℝ≥0} {e : I → M} (he : IsTOrthogonalBasis R t e) (ht : 0 < t)
    {a b : I → R} {x : M} (ha : HasSum (fun i ↦ a i • e i) x)
    (hb : HasSum (fun i ↦ b i • e i) x) : a = b := by
  funext i
  have h := he.isTOrthogonalFamily.smul_eq_smul_of_hasSum ht ha hb i
  rw [← sub_eq_zero, ← sub_smul] at h
  exact sub_eq_zero.1 <| (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_right (he.ne_zero i)

section Expansion

variable [NormedRing R] [NormedAddCommGroup M] [Module R M] [NormSMulClass R M] {t : ℝ≥0}
  {e : I → M}

/-- In a `t`-orthogonal basis with `t > 0`, the coefficient sequences of a Cauchy sequence of
finite linear combinations are Cauchy. -/
private theorem cauchySeq_apply_of_cauchySeq_linearCombination (he : IsTOrthogonalBasis R t e)
    (ht : 0 < t) {c : ℕ → I →₀ R} (hc : CauchySeq fun n ↦ Finsupp.linearCombination R e (c n))
    (i : I) : CauchySeq fun n ↦ c n i := by
  have hei : 0 < (t : ℝ) * ‖e i‖ := mul_pos (by exact_mod_cast ht) (norm_pos_iff.2 (he.ne_zero i))
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hc _ (mul_pos hε hei)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := he.isTOrthogonalFamily.mul_norm_smul_le_norm_linearCombination (c n - c N) i
  simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply, norm_smul] at h
  have h' := hN n hn
  rw [dist_eq_norm] at h' ⊢
  have : ‖c n i - c N i‖ * (t * ‖e i‖) < ε * (t * ‖e i‖) := by linarith
  exact lt_of_mul_lt_mul_right this hei.le

omit [NormSMulClass R M] in
/-- In an ultrametric module, if `x` lies in the closure of the finite linear combinations of `e`
and, for some `t > 0`, `t * ‖(a i - d i) • e i‖ ≤ ‖x - Finsupp.linearCombination R e d‖` for
every finitely supported `d`, then `x` is the unconditional sum of the `a i • e i`. -/
private theorem hasSum_of_forall_mul_norm_sub_smul_le [IsUltrametricDist M] (ht : 0 < t)
    {a : I → R} {x : M} (hx : x ∈ closure (Set.range (Finsupp.linearCombination R e)))
    (h : ∀ (d : I →₀ R) (i : I),
      t * ‖(a i - d i) • e i‖ ≤ ‖x - Finsupp.linearCombination R e d‖) :
    HasSum (fun i ↦ a i • e i) x := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [HasSum, SummationFilter.unconditional_filter, NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  -- Choose a finite combination `L d` close to `x`; its support controls the partial sums.
  obtain ⟨_, ⟨d, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hx _ (lt_min hε (mul_pos ht' hε))
  rw [dist_eq_norm] at hd
  refine ⟨d.support, fun s hs ↦ ?_⟩
  have hLs : Finsupp.linearCombination R e d = ∑ i ∈ s, d i • e i := by
    rw [Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ hs _ fun _ _ ↦ zero_smul R _
  have hsplit : ∑ i ∈ s, a i • e i - x =
      ∑ i ∈ s, (a i - d i) • e i + (Finsupp.linearCombination R e d - x) := by
    rw [hLs]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt ?_ ((norm_sub_rev _ _).trans_lt (hd.trans_le (min_le_left _ _))))
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (C := ‖x - Finsupp.linearCombination R e d‖ / t) (by positivity) fun i _ ↦ ?_).trans_lt ?_
  · rw [le_div_iff₀' ht']
    exact h d i
  · rw [div_lt_iff₀' ht']
    exact hd.trans_le (min_le_right _ _)

variable [CompleteSpace R] [IsUltrametricDist M]

/-- **Existence of expansions in a `t`-orthogonal basis**: for `t > 0`, over a complete normed
ring acting norm-multiplicatively on an ultrametric module, every vector `x` is the unconditional
sum of a family `a i • e i`. Completeness of the module is not needed. -/
theorem exists_hasSum (he : IsTOrthogonalBasis R t e) (ht : 0 < t) (x : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) x := by
  set L := Finsupp.linearCombination R e
  -- Approximate `x` by finite linear combinations `L (c n)`.
  have hx : x ∈ closure (Set.range L) := by
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact he.dense_span x
  obtain ⟨y, hy_mem, hyx⟩ := mem_closure_iff_seq_limit.1 hx
  choose c hc using hy_mem
  -- Each coefficient sequence is Cauchy, and has a limit `a i`.
  choose a ha using fun i ↦ cauchySeq_tendsto_of_complete <|
    he.cauchySeq_apply_of_cauchySeq_linearCombination ht (c := c)
      (by convert hyx.cauchySeq using 2 with n; exact hc n) i
  -- Passing to the limit, `t * ‖(a i - d i) • e i‖ ≤ ‖x - L d‖` for every finite combination.
  refine ⟨a, hasSum_of_forall_mul_norm_sub_smul_le ht hx fun d i ↦ ?_⟩
  refine le_of_tendsto_of_tendsto' ((((ha i).sub_const (d i)).smul_const (e i)).norm.const_mul _)
    (hyx.sub_const (L d)).norm fun n ↦ ?_
  simpa [L, hc, map_sub] using
    he.isTOrthogonalFamily.mul_norm_smul_le_norm_linearCombination (c n - d) i

/-- **Expansions in a `t`-orthogonal basis**: for `t > 0`, over a complete normed ring acting
norm-multiplicatively on an ultrametric module, every vector is the unconditional sum of the
`a i • e i` for exactly one family of coefficients `a`. -/
theorem existsUnique_hasSum (he : IsTOrthogonalBasis R t e) (ht : 0 < t) (x : M) :
    ∃! a : I → R, HasSum (fun i ↦ a i • e i) x := by
  have : NoZeroSMulDivisors R M := ⟨fun h ↦ by simpa [norm_smul] using congrArg norm h⟩
  exact (he.exists_hasSum ht x).elim fun a ha ↦ ⟨a, ha, fun _ hb ↦ he.eq_of_hasSum ht hb ha⟩

end Expansion

section Schauder

variable [NontriviallyNormedField K] [CompleteSpace K] [NormedAddCommGroup M] [NormedSpace K M]
  [IsUltrametricDist M] {t : ℝ≥0} {e : I → M}

/-- The coefficients of a vector in a `t`-orthogonal basis, as a linear map to families. -/
private noncomputable def coeffs (he : IsTOrthogonalBasis K t e) (ht : 0 < t) :
    M →ₗ[K] I → K where
  toFun x := (he.exists_hasSum ht x).choose
  map_add' x y := he.eq_of_hasSum ht (he.exists_hasSum ht (x + y)).choose_spec <| by
    simpa only [Pi.add_apply, add_smul] using
      (he.exists_hasSum ht x).choose_spec.add (he.exists_hasSum ht y).choose_spec
  map_smul' c x := he.eq_of_hasSum ht (he.exists_hasSum ht (c • x)).choose_spec <| by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply] using
      (he.exists_hasSum ht x).choose_spec.const_smul c

private theorem hasSum_coeffs (he : IsTOrthogonalBasis K t e) (ht : 0 < t) (x : M) :
    HasSum (fun i ↦ he.coeffs ht x i • e i) x :=
  (he.exists_hasSum ht x).choose_spec

private theorem coeffs_eq_of_hasSum (he : IsTOrthogonalBasis K t e) (ht : 0 < t) {a : I → K}
    {x : M} (h : HasSum (fun i ↦ a i • e i) x) : he.coeffs ht x = a :=
  he.eq_of_hasSum ht (he.hasSum_coeffs ht x) h

private theorem norm_coeffs_le (he : IsTOrthogonalBasis K t e) (ht : 0 < t) (i : I) (x : M) :
    ‖he.coeffs ht x i‖ ≤ (t * ‖e i‖)⁻¹ * ‖x‖ := by
  have hei : 0 < (t : ℝ) * ‖e i‖ := mul_pos (by exact_mod_cast ht) (norm_pos_iff.2 (he.ne_zero i))
  rw [← div_eq_inv_mul, le_div_iff₀' hei, mul_assoc, mul_comm ‖e i‖, ← norm_smul]
  exact he.isTOrthogonalFamily.mul_norm_smul_le_of_hasSum (he.hasSum_coeffs ht x) i

/-- **A `t`-orthogonal basis is an unconditional Schauder basis**: for `t > 0`, a `t`-orthogonal
basis `e` of an ultrametric normed space over a complete nontrivially normed field, with the
coordinate functionals sending a vector to its coefficients in its unique unconditional
expansion `∑ i, a i • e i`. -/
noncomputable def toUnconditionalSchauderBasis (he : IsTOrthogonalBasis K t e) (ht : 0 < t) :
    UnconditionalSchauderBasis I K M where
  basis := e
  coord i := (LinearMap.proj i ∘ₗ he.coeffs ht).mkContinuous (t * ‖e i‖)⁻¹
    (he.norm_coeffs_le ht i)
  ortho i j := by
    classical
    have h : HasSum (fun k ↦ (Pi.single j (1 : K) : I → K) k • e k) (e j) := by
      simpa using hasSum_single (f := fun k ↦ (Pi.single j (1 : K) : I → K) k • e k) j
        fun k hk ↦ by simp [hk]
    simp [he.coeffs_eq_of_hasSum ht h]
  expansion x := by simpa using he.hasSum_coeffs ht x

/-- The coordinates of the Schauder basis attached to `e` are the expansion coefficients. -/
private theorem coord_apply (he : IsTOrthogonalBasis K t e) (ht : 0 < t) (i : I) (x : M) :
    (he.toUnconditionalSchauderBasis ht).coord i x = he.coeffs ht x i :=
  rfl

/-- The vectors of the Schauder basis attached to a `t`-orthogonal basis `e` are those of `e`. -/
@[simp]
theorem coe_toUnconditionalSchauderBasis (he : IsTOrthogonalBasis K t e) (ht : 0 < t) :
    ⇑(he.toUnconditionalSchauderBasis ht) = e :=
  (rfl)

/-- **The coordinates of an expansion**: if `x` is the unconditional sum of the `a i • e i`, then
the coordinates of `x` in the Schauder basis attached to the `t`-orthogonal basis `e` are the
`a i`. -/
theorem coord_eq_of_hasSum (he : IsTOrthogonalBasis K t e)
    (ht : 0 < t) {a : I → K} {x : M} (h : HasSum (fun i ↦ a i • e i) x) (i : I) :
    (he.toUnconditionalSchauderBasis ht).coord i x = a i := by
  rw [coord_apply, he.coeffs_eq_of_hasSum ht h]

/-- **Coordinate estimate**: the `i`-th coordinate of `x` in the Schauder basis attached to a
`t`-orthogonal basis `e` satisfies `t * ‖coord i x‖ * ‖e i‖ ≤ ‖x‖`. -/
theorem mul_norm_coord_mul_norm_le (he : IsTOrthogonalBasis K t e) (ht : 0 < t) (i : I)
    (x : M) : t * ‖(he.toUnconditionalSchauderBasis ht).coord i x‖ * ‖e i‖ ≤ ‖x‖ := by
  rw [mul_assoc, ← norm_smul]
  exact he.isTOrthogonalFamily.mul_norm_smul_le_of_hasSum
    ((he.toUnconditionalSchauderBasis ht).expansion x) i

/-- The `i`-th coordinate functional of the Schauder basis attached to a `t`-orthogonal basis `e`
has operator norm at most `(t * ‖e i‖)⁻¹`. -/
theorem norm_coord_le (he : IsTOrthogonalBasis K t e) (ht : 0 < t)
    (i : I) : ‖(he.toUnconditionalSchauderBasis ht).coord i‖ ≤ (t * ‖e i‖)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) (he.norm_coeffs_le ht i)

/-- **Decay of coordinates**: the coordinates of a vector in the Schauder basis attached to a
`t`-orthogonal basis `e` satisfy `‖coord i x‖ * ‖e i‖ → 0` along the cofinite filter. -/
theorem tendsto_norm_coord_mul_norm (he : IsTOrthogonalBasis K t e) (ht : 0 < t) (x : M) :
    Tendsto (fun i ↦ ‖(he.toUnconditionalSchauderBasis ht).coord i x‖ * ‖e i‖) cofinite
      (𝓝 0) := by
  simpa [norm_smul] using
    ((he.toUnconditionalSchauderBasis ht).expansion x).summable.tendsto_cofinite_zero.norm

/-- **Every null family of coefficients occurs**: in a complete space, if `‖a i‖ * ‖e i‖ → 0`
along the cofinite filter, then the coordinates of `∑' i, a i • e i` in the Schauder basis
attached to the `t`-orthogonal basis `e` are the `a i`. -/
theorem coord_tsum [CompleteSpace M] (he : IsTOrthogonalBasis K t e)
    (ht : 0 < t) {a : I → K} (ha : Tendsto (fun i ↦ ‖a i‖ * ‖e i‖) cofinite (𝓝 0)) (i : I) :
    (he.toUnconditionalSchauderBasis ht).coord i (∑' j, a j • e j) = a i := by
  refine he.coord_eq_of_hasSum ht
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum i
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [norm_smul] using ha)

end Schauder

end IsTOrthogonalBasis

end TauCeti
