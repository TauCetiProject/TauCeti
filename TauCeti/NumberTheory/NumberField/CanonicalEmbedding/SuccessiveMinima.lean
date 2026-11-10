/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MixedImage
import TauCeti.Analysis.Convex.Gauge
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Basic

/-!
# Successive minima over a number field

Let `K` be a number field of degree `d`, let `ι` be a finite type, and let `Λ` be an
`𝓞 K`-submodule of `ι → K` whose mixed image `Λ.mixedImage` is a full lattice in
`ι → mixedSpace K` (`Submodule.isZLattice_mixedImage`). For a convex body `B` in
`ι → mixedSpace K` with `0` in its interior, the `l`-th **successive minimum of `Λ` over `K`**,
`Submodule.successiveMinimum Λ B l`, is the infimum of the `t > 0` for which `t • B` contains
the images of `l + 1` vectors of `Λ` linearly independent over `K`. It is indexed from `0`, like
`ZLattice.successiveMin`, and it vanishes for `l ≥ #ι`, where no such family exists.

These are the minima of Bombieri and Gubler's adelic geometry of numbers, stated for the real
lattice `Λ.mixedImage` of rank `d * #ι` instead of in the adèles. Writing `μ` for the minima over
`K` and `λ` for the real minima of `Λ.mixedImage` (`ZLattice.successiveMinNat`), this file proves
that the minima over `K` are attained, all by a single family of `#ι` vectors independent over
`K`, and compares them with the real minima:

```text
λ l  ≤  μ l  ≤  λ (d * l)        (l < #ι).
```

The first inequality holds because vectors independent over `K` have images independent over
`ℝ`; the second extracts, from `d * #ι` real-independent lattice vectors realizing the real minima,
`#ι` vectors independent over `K` (`TauCeti.exists_linearIndependent_comp_finrank_mul`).

## Main definitions

* `Submodule.successiveMinimum Λ B l`: the `l`-th successive minimum of `Λ` over `K` with
  respect to `B`.

## Main results

* `Submodule.successiveMinimum_of_card_le`: the minima vanish from `#ι` on.
* `Submodule.finite_setOf_gauge_le`: only finitely many vectors of `Λ` have image of bounded
  gauge.
* `Submodule.successiveMinimum_le_iff`: below `#ι` and for `t > 0`, `μ l ≤ t` exactly when
  `t • B` contains the images of `l + 1` vectors of `Λ` independent over `K`; in particular each
  minimum is attained.
* `Submodule.successiveMinimum_pos`, `Submodule.monotoneOn_successiveMinimum`: below `#ι` the
  minima are positive and nondecreasing.
* `Submodule.exists_linearIndependent_mem_smul_successiveMinimum`: there are `#ι` vectors of
  `Λ`, independent over `K`, the `l`-th of them with image in `μ l • B`.
* `Submodule.successiveMin_mixedImage_le` and
  `Submodule.successiveMinimum_le_successiveMin_mixedImage`: `λ l ≤ μ l ≤ λ (d * l)`.
* `Submodule.finrank_span_setOf_mem`: the rank of the lattice points in a positive dilate
  is the number of successive minima at most the dilation factor.
* `Submodule.span_setOf_mem_eq_span_image`: any family realizing the minima spans those
  lattice points with its initial segment of that rank.

## Implementation notes

Each minimum is attained by finiteness alone: a bounded dilate of `B` holds the images of only
finitely many vectors of `Λ`, so among the independent families of such vectors one minimizes the
largest gauge. A single family realizing all the minima is then assembled one vector at a time,
since `l + 1` independent vectors realizing `μ l` include one outside the span of the `l` already
chosen; Cassels' greedy construction with its minimality clause is not needed. Positivity and the
existence of admissible dilations need no comparison with the real minima: a full lattice
`Λ.mixedImage` forces `Λ` to span `ι → K` over `K` (`Submodule.span_real_mixedImage_eq_top_iff`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Appendix C.2, Definition C.2.9.
* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter VIII.
* The definition and the proofs adapt `DiophantineApproximation/FieldMinima.lean` of
  R. Stephan's `Subspace-Theorems` formalization (Apache 2.0),
  <https://github.com/rwst/Subspace-Theorems>, to the real successive minima
  `ZLattice.successiveMin` of Tau Ceti.
-/

public section

open Module NumberField NumberField.mixedEmbedding
open scoped Pointwise

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*}

/-- The `l`-th **successive minimum over `K`** of an `𝓞 K`-submodule `Λ` of `ι → K` with respect
to a set `B` of `ι → mixedSpace K`: the infimum of the `t > 0` for which the dilate `t • B`
contains the mixed embeddings of `l + 1` vectors of `Λ` linearly independent over `K`. It is
indexed from `0`, like `ZLattice.successiveMin`.

From `l = #ι` on there is no such family, and the value is the junk value `sInf ∅ = 0`
(`Submodule.successiveMinimum_of_card_le`). Below `#ι`, for a full lattice `Λ.mixedImage` and a
convex body `B` with `0` in its interior, the infimum is attained and positive
(`Submodule.successiveMinimum_le_iff`, `Submodule.successiveMinimum_pos`). -/
noncomputable def successiveMinimum (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (l : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧
    ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B}

theorem successiveMinimum_def (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (l : ℕ) :
    successiveMinimum Λ B l = sInf {t : ℝ | 0 < t ∧ ∃ x : Fin (l + 1) → ι → K,
      LinearIndependent K x ∧
        ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B} :=
  (rfl)

variable {Λ : Submodule (𝓞 K) (ι → K)} {l : ℕ}

theorem successiveMinimum_nonneg (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (l : ℕ) : 0 ≤ successiveMinimum Λ B l :=
  Real.sInf_nonneg fun _ ht ↦ ht.1.le

/-- A dilate `t • B` containing the images of `l + 1` vectors of `Λ` independent over `K` bounds
the `l`-th successive minimum by `t`. -/
theorem successiveMinimum_le {B : Set (ι → mixedSpace K)} {t : ℝ} (ht : 0 < t)
    {x : Fin (l + 1) → ι → K} (hx : LinearIndependent K x) (hxΛ : ∀ k, x k ∈ Λ)
    (hxB : ∀ k, (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) :
    successiveMinimum Λ B l ≤ t :=
  csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ⟨ht, x, hx, fun k ↦ ⟨hxΛ k, hxB k⟩⟩

/-- From `#ι` on the successive minima over `K` vanish: `ι → K` holds no `#ι + 1` vectors
independent over `K`. -/
@[simp]
theorem successiveMinimum_of_card_le [Fintype ι] (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (hl : Fintype.card ι ≤ l) :
    successiveMinimum Λ B l = 0 := by
  rw [successiveMinimum_def, ← Real.sInf_empty]
  congr 1
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro t ⟨-, x, hx, -⟩
  have := hx.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
  omega

variable [NumberField K] [Fintype ι]

omit [Fintype ι] in
/-- **Bounded gauge sublevels of `Λ` are finite.** If the mixed image of `Λ` is discrete and `0`
lies in the interior of `B`, only finitely many vectors of `Λ` have a mixed embedding of gauge at
most `r` with respect to `B`. -/
theorem finite_setOf_gauge_le [Finite ι] (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)} (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) (r : ℝ) :
    {x : ι → K | x ∈ Λ ∧
      gauge (B : Set (ι → mixedSpace K)) (fun j ↦ mixedEmbedding K (x j)) ≤ r}.Finite := by
  classical
  cases nonempty_fintype ι
  refine ((ZLattice.finite_setOf_gauge_le Λ.mixedImage hB r).preimage
    (f := fun x j ↦ mixedEmbedding K (x j)) ?_).subset ?_
  · exact fun x _ y _ h ↦ funext fun j ↦ mixedEmbedding_injective K (congrFun h j)
  · rintro x ⟨hx, hr⟩
    exact ⟨Submodule.mem_mixedImage.2 ⟨x, hx, rfl⟩, hr⟩

section Lattice

open scoped Classical in
/-- Below `#ι`, the dilates of `B` contain the images of `l + 1` vectors of `Λ` independent
over `K`: a full lattice `Λ.mixedImage` forces `Λ` to span `ι → K`, and `B` absorbs any finite
family. -/
private theorem exists_mem_smul [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hl : l < Fintype.card ι) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧
      ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • (B : Set (ι → mixedSpace K)) := by
  have hspan : Submodule.span K (Λ : Set (ι → K)) = ⊤ :=
    Submodule.span_real_mixedImage_eq_top_iff.1 IsZLattice.span_top
  obtain ⟨x, hx, hxΛ⟩ : ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧ ∀ k, x k ∈ Λ := by
    refine Submodule.le_finrank_span_iff_exists_linearIndependent.1 ?_
    rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card]
    exact hl
  set g := fun k ↦ gauge (B : Set (ι → mixedSpace K)) (fun j ↦ mixedEmbedding K (x k j))
  have hg : ∀ k, g k ≤ ∑ k, g k := fun k ↦
    Finset.single_le_sum (f := g) (fun k _ ↦ gauge_nonneg _) (Finset.mem_univ k)
  have ht : 0 < 1 + ∑ k, g k := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) ↦ gauge_nonneg (s := (B : Set _))
      (fun j ↦ mixedEmbedding K (x k j))
    linarith
  refine ⟨1 + ∑ k, g k, ht, x, hx, fun k ↦ ⟨hxΛ k, ?_⟩⟩
  rw [← ConvexBody.gauge_le_iff_mem_smul hB ht]
  linarith [hg k]

open scoped Classical in
/-- **Each successive minimum over `K` is attained.** Among the finitely many independent
families of vectors of `Λ` with image of gauge at most `μ l + 1`, one of least largest gauge has
largest gauge at most `μ l`. -/
private theorem exists_gauge_le_successiveMinimum
    [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) (hl : l < Fintype.card ι) :
    ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧ ∀ k, x k ∈ Λ ∧
      gauge (B : Set (ι → mixedSpace K)) (fun j ↦ mixedEmbedding K (x k j)) ≤
        successiveMinimum Λ B l := by
  set m := successiveMinimum Λ B l
  set S := {t : ℝ | 0 < t ∧ ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧
    ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • (B : Set (ι → mixedSpace K))}
  have hm : m = sInf S := successiveMinimum_def Λ B l
  have hS : S.Nonempty := exists_mem_smul (Λ := Λ) hB hl
  set G := fun y : ι → K ↦ gauge (B : Set (ι → mixedSpace K)) (fun j ↦ mixedEmbedding K (y j))
  -- The candidate families, made of vectors of gauge at most `m + 1`, are finitely many.
  set P : Set (Fin (l + 1) → ι → K) :=
    {x | (∀ k, x k ∈ Λ ∧ G (x k) ≤ m + 1) ∧ LinearIndependent K x}
  have hP : P.Finite :=
    (Set.Finite.pi fun _ ↦ finite_setOf_gauge_le Λ hB (m + 1)).subset fun x hx ↦
      Set.mem_univ_pi.2 hx.1
  set g : (Fin (l + 1) → ι → K) → ℝ := fun x ↦ Finset.univ.sup' Finset.univ_nonempty (G ∘ x)
  -- An admissible dilation `t ≤ m + 1` yields a candidate family of largest gauge at most `t`.
  have key : ∀ t ∈ S, t ≤ m + 1 → ∃ y ∈ P, g y ≤ t := by
    rintro t ⟨ht, y, hy, hyB⟩ htm
    have hle : ∀ k, G (y k) ≤ t := fun k ↦
      (ConvexBody.gauge_le_iff_mem_smul hB ht).2 (hyB k).2
    exact ⟨y, ⟨fun k ↦ ⟨(hyB k).1, (hle k).trans htm⟩, hy⟩, Finset.sup'_le _ _ fun k _ ↦ hle k⟩
  obtain ⟨t₀, ht₀S, ht₀⟩ := exists_lt_of_csInf_lt hS (hm ▸ lt_add_one m)
  obtain ⟨y₀, hy₀P, -⟩ := key t₀ ht₀S ht₀.le
  obtain ⟨x, hxP, hxmin⟩ := Set.exists_min_image P g hP ⟨y₀, hy₀P⟩
  have hgx : g x ≤ m := by
    refine le_of_forall_gt_imp_ge_of_dense fun s hs ↦ ?_
    obtain ⟨t, htS, hts⟩ := exists_lt_of_csInf_lt hS (hm ▸ lt_min hs (lt_add_one m))
    obtain ⟨y, hyP, hyt⟩ := key t htS (hts.le.trans (min_le_right _ _))
    exact (hxmin y hyP).trans (hyt.trans (hts.le.trans (min_le_left _ _)))
  exact ⟨x, hxP.2, fun k ↦ ⟨(hxP.1 k).1,
    (Finset.le_sup' (G ∘ x) (Finset.mem_univ k)).trans hgx⟩⟩

open scoped Classical in
/-- Below `#ι` the successive minima over `K` are positive. -/
theorem successiveMinimum_pos [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hl : l < Fintype.card ι) : 0 < successiveMinimum Λ B l := by
  obtain ⟨x, hx, hxB⟩ := exists_gauge_le_successiveMinimum (Λ := Λ) hB hl
  refine lt_of_lt_of_le ((ConvexBody.gauge_pos_iff hB).2 fun h ↦ hx.ne_zero 0 ?_) (hxB 0).2
  exact funext fun j ↦ (map_eq_zero_iff _ (mixedEmbedding_injective K)).1 (congrFun h j)

open scoped Classical in
/-- **The successive minima over `K` as thresholds.** Below `#ι` and for `t > 0`, the `l`-th
successive minimum over `K` is at most `t` exactly when `t • B` contains the images of `l + 1`
vectors of `Λ` independent over `K`. In particular, for `t = μ l`, each minimum is attained. -/
theorem successiveMinimum_le_iff [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hl : l < Fintype.card ι) {t : ℝ} (ht : 0 < t) :
    successiveMinimum Λ B l ≤ t ↔ ∃ x : Fin (l + 1) → ι → K, LinearIndependent K x ∧
      ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • (B : Set (ι → mixedSpace K)) := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, hxB⟩ ↦
    successiveMinimum_le ht hx (fun k ↦ (hxB k).1) fun k ↦ (hxB k).2⟩
  obtain ⟨x, hx, hxB⟩ := exists_gauge_le_successiveMinimum (Λ := Λ) hB hl
  exact ⟨x, hx, fun k ↦
    ⟨(hxB k).1, (ConvexBody.gauge_le_iff_mem_smul hB ht).1 ((hxB k).2.trans h)⟩⟩

open scoped Classical in
/-- The successive minima over `K` are nondecreasing below `#ι`. They are not monotone on all of
`ℕ`, since they vanish from `#ι` on (`Submodule.successiveMinimum_of_card_le`). -/
theorem monotoneOn_successiveMinimum [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) :
    MonotoneOn (successiveMinimum Λ B) (Set.Iio (Fintype.card ι)) := by
  intro i _ j hj hij
  have hpos := successiveMinimum_pos (Λ := Λ) hB hj
  obtain ⟨x, hx, hxB⟩ := (successiveMinimum_le_iff (Λ := Λ) hB hj hpos).1 le_rfl
  have hle : i + 1 ≤ j + 1 := by omega
  exact successiveMinimum_le hpos (hx.comp _ (Fin.castLE_injective hle)) (fun k ↦ (hxB _).1)
    fun k ↦ (hxB _).2

open scoped Classical in
/-- **The successive minima over `K` are attained by one family**: there are `#ι` vectors of `Λ`,
linearly independent over `K`, the `l`-th of which has its image in `μ l • B`. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum
    [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧ ∀ l, x l ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (x l j)) ∈
        successiveMinimum Λ B l • (B : Set (ι → mixedSpace K)) := by
  suffices H : ∀ n ≤ Fintype.card ι, ∃ x : Fin n → ι → K, LinearIndependent K x ∧ ∀ l : Fin n,
      x l ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x l j)) ∈
        successiveMinimum Λ B l • (B : Set (ι → mixedSpace K)) from H _ le_rfl
  intro n hn
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun l ↦ l.elim0⟩
  | succ n ih =>
    obtain ⟨x, hx, hxB⟩ := ih (by omega)
    obtain ⟨y, hy, hyB⟩ :=
      (successiveMinimum_le_iff (Λ := Λ) hB hn (successiveMinimum_pos hB hn)).1 le_rfl
    -- Of the `n + 1` independent vectors `y`, one lies outside the span of the `n` vectors `x`.
    obtain ⟨j, hj⟩ : ∃ j, y j ∉ Submodule.span K (Set.range x) := by
      by_contra! h
      have h₁ := Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 h))
      have h₂ := finrank_range_le_card (R := K) x
      rw [finrank_span_eq_card hy, Fintype.card_fin] at h₁
      rw [Set.finrank, Fintype.card_fin] at h₂
      omega
    refine ⟨Fin.snoc x (y j), linearIndependent_finSnoc.2 ⟨hx, hj⟩, Fin.lastCases ?_ fun l ↦ ?_⟩
    · simpa using hyB j
    · simpa using hxB l

open scoped Classical in
/-- **The real minima are at most the minima over `K`**: below `#ι`, the `l`-th successive minimum
of the lattice `Λ.mixedImage` is at most the `l`-th successive minimum of `Λ` over `K`. -/
theorem successiveMin_mixedImage_le [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hl : l < Fintype.card ι) :
    ZLattice.successiveMinNat Λ.mixedImage B l ≤ successiveMinimum Λ B l := by
  have hl' : l < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    nlinarith [Module.finrank_pos (R := ℚ) (M := K)]
  obtain ⟨x, hx, hxB⟩ :=
    (successiveMinimum_le_iff (Λ := Λ) hB hl (successiveMinimum_pos hB hl)).1 le_rfl
  -- Vectors independent over `K` have mixed embeddings independent over `ℝ`.
  rw [ZLattice.successiveMinNat_of_lt _ _ hl']
  exact ZLattice.successiveMin_le (successiveMinimum_nonneg Λ B l)
    (v := fun k j ↦ mixedEmbedding K (x k j))
    (mixedEmbedding.linearIndependent_pi (hx.restrict_scalars' ℚ))
    (fun k ↦ Submodule.mem_mixedImage.2 ⟨x k, (hxB k).1, rfl⟩) fun k ↦ (hxB k).2

open scoped Classical in
/-- **The minima over `K` are at most real minima of index `[K : ℚ]` times larger**: below `#ι`,
the `l`-th successive minimum of `Λ` over `K` is at most the `([K : ℚ] * l)`-th successive minimum
of the lattice `Λ.mixedImage`. -/
theorem successiveMinimum_le_successiveMin_mixedImage
    [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) (hl : l < Fintype.card ι) :
    successiveMinimum Λ B l ≤ ZLattice.successiveMinNat Λ.mixedImage B (finrank ℚ K * l) := by
  have hdim := mixedEmbedding.finrank_pi (K := K) (ι := ι)
  have hdl : finrank ℚ K * l < finrank ℝ (ι → mixedSpace K) := by
    rw [hdim]
    exact Nat.mul_lt_mul_of_pos_left hl finrank_pos
  -- Among the `[K : ℚ] * #ι` real-independent lattice vectors `a` realizing the real minima there
  -- are `#ι` preimages independent over `K`, the `k`-th among the first `[K : ℚ] * k + 1`.
  obtain ⟨a, ha, haΛ⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin Λ.mixedImage hB
  choose u huΛ hu using fun i ↦ Submodule.mem_mixedImage.1 (haΛ i).1
  set e := finCongr hdim
  set f : (ι → K) →ₗ[ℚ] ι → mixedSpace K :=
    LinearMap.piMap fun _ ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap
  have hfu : f ∘ (u ∘ e.symm) = a ∘ e.symm := by
    ext1 i
    exact hu (e.symm i)
  obtain ⟨s, hs, hsd⟩ := TauCeti.exists_linearIndependent_comp_finrank_mul (F := ℚ) (E := ℝ)
    (k := Fintype.card ι) (u := u ∘ e.symm) (hfu ▸ ha.comp _ e.symm.injective)
  rw [ZLattice.successiveMinNat_of_lt _ _ hdl]
  have ht := ZLattice.successiveMin_pos Λ.mixedImage hB ⟨_, hdl⟩
  have hle : l + 1 ≤ Fintype.card ι := hl
  refine successiveMinimum_le ht (hs.comp _ (Fin.castLE_injective hle)) (fun k ↦ huΛ _)
    fun k ↦ ?_
  rw [← ConvexBody.gauge_le_iff_mem_smul hB ht]
  simp only [Function.comp_apply, hu, (haΛ _).2]
  refine ZLattice.monotone_successiveMin Λ.mixedImage hB (Fin.le_def.2 ?_)
  have hk := hsd (Fin.castLE hle k)
  simp only [Fin.val_castLE, e, finCongr_symm_apply_coe] at hk ⊢
  exact hk.trans (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 k.isLt))

open scoped Classical in
/-- A positive dilate contains lattice points spanning more than `l` dimensions exactly when
its dilation factor is at least the `l`-th successive minimum. -/
theorem successiveMinimum_le_iff_lt_finrank_span [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hl : l < Fintype.card ι) {t : ℝ} (ht : 0 < t) :
    successiveMinimum Λ B l ≤ t ↔
      l < finrank K (span K {x | x ∈ Λ ∧
        (fun j ↦ mixedEmbedding K (x j)) ∈ t • (B : Set (ι → mixedSpace K))}) := by
  rw [successiveMinimum_le_iff hB hl ht, ← Nat.succ_le_iff,
    le_finrank_span_iff_exists_linearIndependent]
  simp only [Set.mem_ofPred_eq]

open scoped Classical in
/-- The rank of the lattice points in a positive dilate of a convex body is the number of
successive minima at most the dilation factor. Only indices below the ambient dimension are
counted, since the minima have junk value zero beyond that dimension. -/
theorem finrank_span_setOf_mem [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) {t : ℝ} (ht : 0 < t) :
    finrank K (span K {x | x ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (x j)) ∈ t • (B : Set (ι → mixedSpace K))}) =
        (Finset.univ.filter fun l : Fin (Fintype.card ι) ↦ successiveMinimum Λ B l ≤ t).card := by
  classical
  simp_rw [successiveMinimum_le_iff_lt_finrank_span hB (Fin.isLt _) ht]
  rw [Fin.card_filter_val_lt, min_eq_right]
  exact (span K {x | x ∈ Λ ∧
    (fun j ↦ mixedEmbedding K (x j)) ∈ t • (B : Set (ι → mixedSpace K))}).finrank_le.trans_eq
      (Module.finrank_fintype_fun_eq_card K)

open scoped Classical in
/-- Any family realizing the successive minima spans the lattice points in a positive dilate
with its first `r` vectors, where `r` is the rank of those lattice points. -/
theorem span_setOf_mem_eq_span_image [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) {t : ℝ} (ht : 0 < t)
    {x : Fin (Fintype.card ι) → ι → K} (hx : LinearIndependent K x)
    (hxΛ : ∀ l, x l ∈ Λ)
    (hxB : ∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
      successiveMinimum Λ B l • (B : Set (ι → mixedSpace K))) :
    span K {a | a ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (a j)) ∈ t • (B : Set (ι → mixedSpace K))} =
      span K (x '' {l | l.val < finrank K (span K {a | a ∈ Λ ∧
        (fun j ↦ mixedEmbedding K (a j)) ∈ t • (B : Set (ι → mixedSpace K))})}) := by
  classical
  let U := span K {a | a ∈ Λ ∧
    (fun j ↦ mixedEmbedding K (a j)) ∈ t • (B : Set (ι → mixedSpace K))}
  have hle : span K (x '' {l | l.val < finrank K U}) ≤ U := by
    refine span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have hμ := (successiveMinimum_le_iff_lt_finrank_span hB l.isLt ht).2 hl
    exact subset_span ⟨hxΛ l, (ConvexBody.gauge_le_iff_mem_smul hB ht).1
      (((ConvexBody.gauge_le_iff_mem_smul hB
        (successiveMinimum_pos hB l.isLt)).2 (hxB l)).trans hμ)⟩
  have hr : finrank K U ≤ Fintype.card ι :=
    U.finrank_le.trans_eq (Module.finrank_fintype_fun_eq_card K)
  have hdim : finrank K (span K (x '' {l | l.val < finrank K U})) = finrank K U := by
    rw [Set.image_eq_range]
    exact (finrank_span_eq_card (hx.comp _ Subtype.val_injective)).trans
      (Fintype.card_fin_lt_of_le hr)
  exact (eq_of_le_of_finrank_eq hle hdim).symm

open scoped Classical in
-- At the minimum itself the boundary vectors already contribute `l + 1` dimensions.
example [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) (hl : l < Fintype.card ι) :
    l < finrank K (span K {x | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈
      successiveMinimum Λ B l • (B : Set (ι → mixedSpace K))}) :=
  (successiveMinimum_le_iff_lt_finrank_span hB hl (successiveMinimum_pos hB hl)).1 le_rfl

end Lattice

end Submodule
