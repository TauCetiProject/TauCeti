/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.Bases.TOrthogonal
public import TauCeti.Analysis.Normed.Module.RieszLemma

/-!
# `t`-orthogonal bases of normed spaces of countable type

Let `K` be a complete nontrivially normed field and `E` an ultrametric normed `K`-space. The space
`E` is *of countable type* if some sequence `v : ℕ → E` has dense span. Over a field whose value
group is not discrete, such a space need not have an orthogonal basis, but for every `t < 1` it
has a `t`-orthogonal one. This file constructs these bases by an approximate Gram–Schmidt process.

* `TauCeti.exists_isTOrthogonalFamily_span_image_Iio_eq`: every sequence `w : ℕ → E` can be
  replaced by a `t`-orthogonal sequence `e` with the same initial spans,
  `span (e '' Iio n) = span (w '' Iio n)`. The vector `e n` is `w n` minus an almost best
  approximation of `w n` in the span of the previous vectors (`TauCeti.riesz_lemma_translate`);
  the losses at the successive steps are chosen with product at least `t`.
* `TauCeti.exists_isTOrthogonalBasis_of_dense_span`: a space of countable type has a
  `t`-orthogonal basis indexed by a set of natural numbers.
* `TauCeti.exists_basis_isTOrthogonalFamily`: a finite-dimensional space has a `t`-orthogonal
  basis in the sense of `Module.Basis`, indexed by `Fin (finrank K E)`.
* `TauCeti.exists_isTOrthogonalBasis_nat_of_dense_span`: an infinite-dimensional space of
  countable type has a `t`-orthogonal basis indexed by `ℕ`.

Neither a discrete valuation nor completeness of `E` is needed: only the finite-dimensional
subspaces spanned by initial segments have to be closed, which holds over a complete field.
Together with `TauCeti.IsTOrthogonalBasis.toUnconditionalSchauderBasis`, these bases give the
coordinates in which Banach spaces of countable type are compared with `C₀(ℕ, K)`.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
-/

public section

open Set Submodule
open scoped NNReal

namespace TauCeti

variable {K E : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]

variable [CompleteSpace K] [IsUltrametricDist E]

/-- **Approximate Gram–Schmidt process**: over a complete nontrivially normed field, every sequence
`w` in an ultrametric normed space can be replaced, for each `t < 1`, by a `t`-orthogonal sequence
`e` with the same initial spans: `span K (e '' Iio n) = span K (w '' Iio n)` for every `n`. -/
theorem exists_isTOrthogonalFamily_span_image_Iio_eq (w : ℕ → E) {t : ℝ≥0} (ht : t < 1) :
    ∃ e : ℕ → E, IsTOrthogonalFamily K t e ∧
      ∀ n, span K (e '' Iio n) = span K (w '' Iio n) := by
  -- Orthogonality constants of the successive initial segments: a strictly decreasing sequence
  -- in `(t, 1)`.
  obtain ⟨T, hT, hTt, -⟩ := exists_seq_strictAnti_tendsto' ht
  have hT' (n : ℕ) : 0 < T n ∧ t ≤ T n ∧ T n ≤ 1 :=
    ⟨zero_le.trans_lt (hTt n).1, (hTt n).1.le, (hTt n).2.le⟩
  -- The initial spans `span K (w '' Iio n)` are finite-dimensional, hence closed.
  have hF (n : ℕ) : IsClosed (span K (w '' Iio n) : Set E) :=
    have := FiniteDimensional.span_of_finite K ((finite_Iio n).image w)
    (span K (w '' Iio n)).closed_of_finiteDimensional
  -- Subtract from `w n` an almost best approximation `y n` in the previous span, with loss
  -- `T (n + 1) / T n < 1`.
  have hr (n : ℕ) : ((T (n + 1) / T n : ℝ≥0) : ℝ) < 1 := by
    exact_mod_cast (div_lt_one (hT' n).1).2 (hT n.lt_succ_self)
  choose y hyF hy using fun n ↦ riesz_lemma_translate (hF n) (w n) (hr n)
  set e : ℕ → E := fun n ↦ w n - y n
  have hspan (n : ℕ) : span K (e '' Iio n) = span K (w '' Iio n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← Order.succ_eq_add_one, Order.Iio_succ_eq_insert, image_insert_eq, image_insert_eq,
        span_insert, span_insert, ih]
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · exact span_singleton_le_iff_mem _ _ |>.2 <|
          sub_mem (mem_sup_left (mem_span_singleton_self _)) (mem_sup_right (hyF n))
      · rw [span_singleton_le_iff_mem, ← sub_add_cancel (w n) (y n)]
        exact add_mem (mem_sup_left (mem_span_singleton_self _)) (mem_sup_right (hyF n))
  -- Each `e n` is `T (n + 1) / T n`-orthogonal to the previous vectors, so for every `N` the
  -- vectors `e i` with `i < N` are `T N`-orthogonal, and `t ≤ T N`.
  have key := isTOrthogonalFamily_Iio_of_mul_nnnorm_le_nnnorm_sub (K := K) hT.antitone
    (fun n ↦ ⟨(hT' n).1, (hT' n).2.2⟩) fun N z hz ↦ by
      rw [hspan] at hz
      exact_mod_cast hy N z hz
  refine ⟨e, isTOrthogonalFamily_def.2 fun s a ↦ ?_, hspan⟩
  have hs (i : ℕ) (hi : i ∈ s) : i ∈ Iio (s.sup id + 1) :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [← Finset.subtype_map_of_mem hs, Finset.sup_map, Finset.sum_map]
  exact (mul_le_mul_of_nonneg_right (hT' _).2.1 zero_le).trans
    (isTOrthogonalFamily_def.1 (key _) _ fun i ↦ a i)

/-- **`t`-orthogonal bases of spaces of countable type**: over a complete nontrivially normed
field, if a sequence `v` has dense span in an ultrametric normed space `E`, then for every `t < 1`
the space `E` has a `t`-orthogonal basis indexed by a set of natural numbers. -/
theorem exists_isTOrthogonalBasis_of_dense_span {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {t : ℝ≥0} (ht : t < 1) :
    ∃ (S : Set ℕ) (e : S → E), IsTOrthogonalBasis K t e := by
  obtain ⟨e, he, hspan⟩ := exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) v ht
  -- Discard the zero vectors of `e`; they do not change its span.
  refine ⟨{n | e n ≠ 0}, fun n ↦ e n, he.comp Subtype.val_injective, fun n ↦ n.2, ?_⟩
  have hrange : range e ⊆ insert 0 (range fun n : {n | e n ≠ 0} ↦ e n) := by
    rintro _ ⟨n, rfl⟩
    by_cases h : e n = 0
    · exact Or.inl h
    · exact Or.inr ⟨⟨n, h⟩, rfl⟩
  -- Equal initial spans give equal spans, as `range` is the union of the initial segments.
  have hspan' : span K (range e) = span K (range v) := by
    simp only [← image_univ, ← iUnion_Iio, image_iUnion, span_iUnion, hspan]
  have : span K (range fun n : {n | e n ≠ 0} ↦ e n) = span K (range v) := by
    refine le_antisymm ((span_mono ?_).trans hspan'.le) ?_
    · rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · calc span K (range v) = span K (range e) := hspan'.symm
        _ ≤ span K (insert 0 (range fun n : {n | e n ≠ 0} ↦ e n)) := span_mono hrange
        _ = _ := span_insert_zero
  rw [this]
  exact hv

/-- **`t`-orthogonal bases of finite-dimensional spaces**: over a complete nontrivially normed
field, a finite-dimensional ultrametric normed space has, for every `t < 1`, a basis indexed by
`Fin (finrank K E)` which is a `t`-orthogonal family. -/
theorem exists_basis_isTOrthogonalFamily [FiniteDimensional K E] {t : ℝ≥0} (ht : t < 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E, IsTOrthogonalFamily K t b := by
  set d := Module.finrank K E
  let b₀ := Module.finBasis K E
  -- Run the Gram–Schmidt process on `b₀`, extended by zero to a sequence.
  let w : ℕ → E := fun n ↦ if h : n < d then b₀ ⟨n, h⟩ else 0
  obtain ⟨e, he, hspan⟩ := exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) w ht
  have htop : ⊤ ≤ span K (range fun i : Fin d ↦ e i) :=
    calc ⊤ = span K (range b₀) := b₀.span_eq.symm
      _ ≤ span K (w '' Iio d) :=
        span_mono <| range_subset_iff.2 fun i ↦ ⟨i, i.2, by simp [w, d, i.isLt]⟩
      _ = span K (e '' Iio d) := (hspan d).symm
      _ ≤ span K (range fun i : Fin d ↦ e i) := span_mono <| by
        rintro _ ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin d ↦ e i) htop (Fintype.card_fin d), ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  exact he.comp Fin.val_injective

/-- **`t`-orthogonal bases of infinite-dimensional spaces of countable type**: over a complete
nontrivially normed field, if a sequence has dense span in an infinite-dimensional ultrametric
normed space `E`, then for every `t < 1` the space `E` has a `t`-orthogonal basis indexed by `ℕ`. -/
theorem exists_isTOrthogonalBasis_nat_of_dense_span (hE : ¬FiniteDimensional K E) {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {t : ℝ≥0} (ht : t < 1) :
    ∃ e : ℕ → E, IsTOrthogonalBasis K t e := by
  obtain ⟨S, e, he⟩ := exists_isTOrthogonalBasis_of_dense_span hv ht
  -- A finite basis would span a closed, hence everything, finite-dimensional subspace.
  have : Infinite S := by
    refine not_finite_iff_infinite.1 fun hS ↦ hE ?_
    have := FiniteDimensional.span_of_finite K (finite_range e)
    have htop : span K (range e) = ⊤ := eq_top_iff'.2 fun x ↦
      (span K (range e)).closed_of_finiteDimensional.closure_subset (he.dense_span x)
    exact Module.finite_def.2 (htop ▸ fg_span (finite_range e))
  obtain ⟨σ⟩ : Nonempty (ℕ ≃ S) := nonempty_equiv_of_countable
  exact ⟨e ∘ σ, he.comp_equiv σ⟩

end TauCeti
