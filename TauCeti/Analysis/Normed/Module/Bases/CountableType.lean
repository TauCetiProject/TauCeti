/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Group.Quotient
public import TauCeti.Analysis.Normed.Module.Bases.TOrthogonal
public import TauCeti.Analysis.Normed.Module.RieszLemma

/-!
# `t`-orthogonal bases and subspaces of normed spaces of countable type

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
* `Submodule.exists_finiteDimensional_le_infDist_le`: for a closed subspace `D`, a
  finite-dimensional subspace `G` and `c > 1`, some finite-dimensional `W ≤ D` satisfies
  `infDist g W ≤ c * infDist g D` for every `g ∈ G`. The subspace `W` is cut out of `D` by lifts
  of a `t`-orthogonal basis of the image of `G` in `E ⧸ D`.
* `Submodule.exists_dense_span_of_dense_span`: every subspace of a space of countable type, closed
  or not, is of countable type. The approximation theorem is applied to the closed subspace
  `closure D`: the finite-dimensional subspaces `W ≤ closure D` attached to the initial spans of a
  densely spanning sequence together span a dense subspace of `closure D`, and each of their
  countably many spanning vectors is then replaced by a sequence in `D` converging to it.

Neither a discrete valuation nor completeness of `E` is needed: only the finite-dimensional
subspaces spanned by initial segments have to be closed, which holds over a complete field.
The constant `c` in the approximation theorem does not depend on `G`; this uniformity is what
lets the subspaces `W` attached to the increasing initial spans together span a dense subspace of
the closure of `D`. Quotients of spaces of countable type are of countable type by
`DenseRange.dense_span_range_comp`, applied to the quotient map.
Together with `TauCeti.IsTOrthogonalBasis.toUnconditionalSchauderBasis`, these bases give the
coordinates in which Banach spaces of countable type are compared with `C₀(ℕ, K)`.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
-/

public section

open Set Submodule Metric Filter
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

/-- **Relative approximation by finite-dimensional subspaces**: let `D` be a closed subspace and
`G` a finite-dimensional subspace of an ultrametric normed space over a complete nontrivially
normed field. For every `c > 1` there is a finite-dimensional subspace `W ≤ D` such that every
`g ∈ G` is within `c * infDist g D` of `W`. -/
theorem _root_.Submodule.exists_finiteDimensional_le_infDist_le (D G : Submodule K E)
    (hD : IsClosed (D : Set E)) [FiniteDimensional K G] {c : ℝ} (hc : 1 < c) :
    ∃ W : Submodule K E, W ≤ D ∧ FiniteDimensional K W ∧
      ∀ g ∈ G, infDist g W ≤ c * infDist g D := by
  -- A `t`-orthogonal basis `b` of the image of `G` in the normed quotient `E ⧸ D`, for some
  -- `c⁻¹ < t < 1`.
  obtain ⟨t, hct, ht⟩ : ∃ t : ℝ≥0, (c⁻¹ : ℝ) < t ∧ t < 1 := by
    obtain ⟨t, h₁, h₂⟩ := exists_between (inv_lt_one_of_one_lt₀ hc)
    exact ⟨⟨t, (inv_pos.2 (one_pos.trans hc)).le.trans h₁.le⟩, h₁, by exact_mod_cast h₂⟩
  have hct' : 1 < c * t := by
    rw [inv_lt_iff_one_lt_mul₀ (one_pos.trans hc)] at hct
    linarith
  obtain ⟨b, hb⟩ := exists_basis_isTOrthogonalFamily (K := K) (E := G.map D.mkQ) ht
  -- Lift each `b i` to a vector `y i` of norm at most `c * t * ‖b i‖`.
  have hlift (i : Fin (Module.finrank K (G.map D.mkQ))) :
      ∃ y : E, D.mkQ y = b i ∧ ‖y‖ ≤ c * t * ‖b i‖ := by
    have hpos : 0 < ‖b i‖ := norm_pos_iff.2 (b.ne_zero i)
    obtain ⟨y, hy, hny⟩ := Submodule.Quotient.norm_mk_lt (b i : E ⧸ D)
      (mul_pos (sub_pos.2 hct') hpos)
    refine ⟨y, hy, ?_⟩
    rw [norm_coe] at hny
    linarith
  choose y hy hny using hlift
  refine ⟨D ⊓ (G ⊔ span K (range y)), inf_le_left, ?_, fun g hg ↦ ?_⟩
  · have := FiniteDimensional.span_of_finite K (finite_range y)
    exact Submodule.finiteDimensional_inf_right _ _
  -- Expand the class `x` of `g` in the basis `b`; subtracting the same combination of the lifts
  -- from `g` gives a point of `W = D ⊓ (G ⊔ span K (range y))`.
  obtain ⟨x, hxg⟩ : ∃ x : G.map D.mkQ, (x : E ⧸ D) = D.mkQ g :=
    ⟨⟨D.mkQ g, mem_map_of_mem hg⟩, rfl⟩
  set a := b.repr x
  have hx : D.mkQ g = ∑ i, a i • (b i : E ⧸ D) := by
    rw [← hxg, ← b.sum_repr x, Submodule.coe_sum]
    simp only [Submodule.coe_smul, a]
  have hmem : g - ∑ i, a i • y i ∈ D ⊓ (G ⊔ span K (range y)) := by
    refine ⟨?_, sub_mem (mem_sup_left hg) (mem_sup_right
      (sum_mem fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i))))⟩
    rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero, ← mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hy, hx, sub_self]
  -- `E ⧸ D` is the quotient group by `D.toAddSubgroup`, carrying its quotient norm.
  have hnorm : ‖D.mkQ g‖ = infDist g D := QuotientAddGroup.norm_mk (S := D.toAddSubgroup) g
  -- By the ultrametric inequality and `t`-orthogonality, the combination of the lifts has norm
  -- at most `c * ‖x‖`.
  calc infDist g (D ⊓ (G ⊔ span K (range y)) : Submodule K E)
      ≤ dist g (g - ∑ i, a i • y i) := infDist_le_dist_of_mem hmem
    _ = ‖∑ i, a i • y i‖ := by rw [dist_eq_norm, sub_sub_cancel]
    _ ≤ c * ‖x‖ := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (one_pos.trans hc).le (norm_nonneg _)) fun i _ ↦ ?_
      have h := hb.mul_norm_smul_le (Finset.mem_univ i) a
      rw [b.sum_repr, norm_smul] at h
      rw [norm_smul]
      calc ‖a i‖ * ‖y i‖ ≤ ‖a i‖ * (c * t * ‖b i‖) := by gcongr; exact hny i
        _ = c * (t * (‖a i‖ * ‖b i‖)) := by ring
        _ ≤ c * ‖x‖ := by gcongr
    _ = c * infDist g D := by rw [← norm_coe, hxg, hnorm]

/-- A closed subspace of a space of countable type is the closure of the span of a countable
subset of it. -/
private theorem exists_countable_subset_closure_span_of_isClosed {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {D : Submodule K E} (hD : IsClosed (D : Set E)) :
    ∃ S : Set E, S.Countable ∧ S ⊆ D ∧ (D : Set E) ⊆ closure (span K S) := by
  -- For each initial span `G n` of `v`, a finite-dimensional `W n ≤ D` approximating the points
  -- of `G n` as well as `D` does, up to the factor `2`; `s n` is a finite spanning set of `W n`.
  set G : ℕ → Submodule K E := fun n ↦ span K (v '' Iio n)
  have (n : ℕ) : FiniteDimensional K (G n) :=
    FiniteDimensional.span_of_finite K ((finite_Iio n).image v)
  choose W hWD hWfin hW using fun n ↦ D.exists_finiteDimensional_le_infDist_le (G n) hD one_lt_two
  choose s hs using fun n ↦ (fg_iff_finiteDimensional (W n)).2 (hWfin n)
  have hsW (n : ℕ) : (s n : Set E) ⊆ span K (⋃ n, (s n : Set E)) :=
    subset_span.trans' (subset_iUnion (fun n ↦ (s n : Set E)) n)
  refine ⟨⋃ n, (s n : Set E), countable_iUnion fun n ↦ (s n).countable_toSet,
    iUnion_subset fun n ↦ fun x hx ↦ hWD n (hs n ▸ subset_span hx), fun d hd ↦ ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Approximate `d` by a point `g` of some `G n`, then `g` by a point of `W n`.
  obtain ⟨g, hg, hdg⟩ := Metric.mem_closure_iff.1 (hv d) (ε / 3) (by positivity)
  have hGmono : Monotone G := fun m n hmn ↦ span_mono (image_mono (Iio_subset_Iio hmn))
  have hrange : span K (range v) = ⨆ n, G n := by
    simp only [G, ← image_univ, ← iUnion_Iio, image_iUnion, span_iUnion]
  rw [SetLike.mem_coe, hrange, mem_iSup_of_directed _ hGmono.directed_le] at hg
  obtain ⟨n, hgn⟩ := hg
  have hgW : infDist g (W n) < 2 * (ε / 3) :=
    (hW n g hgn).trans_lt (by
      gcongr
      exact (infDist_le_dist_of_mem hd).trans_lt (by rwa [dist_comm]))
  obtain ⟨w, hw, hgw⟩ := (infDist_lt_iff ⟨0, (W n).zero_mem⟩).1 hgW
  refine ⟨w, ?_, ?_⟩
  · rw [← hs n] at hw
    exact span_le.2 (hsW n) hw
  · calc dist d w ≤ dist d g + dist g w := dist_triangle _ _ _
      _ < ε / 3 + 2 * (ε / 3) := add_lt_add hdg hgw
      _ = ε := by ring

/-- **Subspaces of spaces of countable type**: over a complete nontrivially normed field, if a
sequence has dense span in an ultrametric normed space `E`, then every subspace `D` of `E`, closed
or not, is of countable type: some sequence in `D` has dense span in `D`. -/
theorem _root_.Submodule.exists_dense_span_of_dense_span (D : Submodule K E) {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) :
    ∃ w : ℕ → D, Dense (span K (range w) : Set D) := by
  obtain ⟨S, hS, hSD, hDS⟩ :=
    exists_countable_subset_closure_span_of_isClosed hv D.isClosed_topologicalClosure
  -- Replace each point of `S ⊆ closure D` by a sequence in `D` converging to it.
  choose! u hu hlim using fun x (hx : x ∈ S) ↦ mem_closure_iff_seq_limit.1 (hSD hx)
  set T : Set E := insert 0 (⋃ x ∈ S, range (u x))
  have hTD : T ⊆ D :=
    insert_subset D.zero_mem (iUnion₂_subset fun x hx ↦ range_subset_iff.2 (hu x hx))
  have hST : S ⊆ (span K T).topologicalClosure := fun x hx ↦
    mem_closure_of_tendsto (hlim x hx) (Eventually.of_forall fun n ↦
      subset_span (mem_insert_of_mem _ (mem_biUnion hx (mem_range_self n))))
  have hDT : (D : Set E) ⊆ closure (span K T) :=
    calc (D : Set E) ⊆ D.topologicalClosure := D.le_topologicalClosure
      _ ⊆ closure (span K S) := hDS
      _ ⊆ closure (span K T) :=
        closure_minimal (span_le.2 hST) (span K T).isClosed_topologicalClosure
  -- Enumerate the countable set `T ⊆ D`.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → E, T = range f :=
    ((hS.biUnion fun x _ ↦ countable_range (u x)).insert 0).exists_eq_range (insert_nonempty _ _)
  have hfD (n : ℕ) : f n ∈ D := hTD (hf ▸ mem_range_self n)
  let w : ℕ → D := fun n ↦ ⟨f n, hfD n⟩
  have hspan : ((↑) '' (span K (range w) : Set D) : Set E) = span K T := by
    -- `D.subtype ∘ w` is `f` by the definition of `w`.
    rw [hf, ← D.coe_subtype, ← Submodule.map_coe, Submodule.map_span, ← range_comp]
    rfl
  exact ⟨w, Subtype.dense_iff.2 (hspan ▸ hDT)⟩

end TauCeti
