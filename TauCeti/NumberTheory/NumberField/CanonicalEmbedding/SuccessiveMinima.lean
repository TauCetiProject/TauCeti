/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ModuleCovolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ReducedBasis
import Mathlib.Analysis.Convex.Measure
import TauCeti.Analysis.Convex.Gauge.Basic
import TauCeti.Analysis.Convex.Topology
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Basic
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Successive minima and Minkowski's second theorem over a number field

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
`K`, compares them with the real minima, and deduces Minkowski's second theorem over `K`.

Without any balancedness assumption on `B`:

```text
λ l  ≤  μ l  ≤  λ (d * l)        (l < #ι),
```

so in particular `μ 0 = λ 0` when `ι` is nonempty
(`Submodule.successiveMinimum_zero_eq_successiveMin_mixedImage`).
The first inequality holds because vectors independent over `K` have images independent over `ℝ`;
the second extracts, from `d * #ι` real-independent lattice vectors realizing the real minima,
`#ι` vectors independent over `K` (`TauCeti.exists_linearIndependent_comp_finrank_mul`). When `B`
is moreover balanced at every infinite place (`∀ z ∈ B, ∀ a, (∀ w, normAtPlace w a ≤ 1) →
(fun i ↦ a * z i) ∈ B`), multiplying `l + 1` `K`-independent vectors of `Λ` by
`reducedIntegralBasis K` gives `d * (l + 1)` `ℝ`-independent vectors in `Λ.mixedImage`
(`NumberField.mixedEmbedding.linearIndependent_real_mixedEmbedding_mul`), yielding

```text
λ (d * (l + 1) - 1)  ≤  c_K * μ l        (l < #ι),
```

where `c_K = integralBasisHouse K ≤ max 1 (d / 2) * √|discr K|` and `c_ℚ = 1`. Combining these
blockwise comparisons with Minkowski's second theorem over `ℝ` yields **Minkowski's second theorem
over `K`**:

```text
2 ^ (d n) / ((d n)! · c_K ^ (d n)) · covolume Λ.mixedImage μ
  ≤ (∏ l, μ l ^ d) · μ B
  ≤ 2 ^ (d n) · covolume Λ.mixedImage μ,
```

where `n = #ι`, the upper bound holds for any compact symmetric convex set `B`, and the lower bound
holds for any compact convex neighbourhood `B` of `0` balanced at every infinite place.

## Main definitions

* `Submodule.successiveMinimum Λ B l`: the `l`-th successive minimum of `Λ` over `K` with
  respect to `B`.

## Main results

* `Submodule.successiveMinimum_of_card_le` and `Submodule.successiveMinimum_smul`: the minima
  vanish from `#ι` on and scale inversely with positive dilations of `B`.
* `Submodule.finite_setOf_gauge_le`: only finitely many vectors of `Λ` have image of bounded
  gauge.
* `Submodule.successiveMinimum_le_iff`: below `#ι` and for `t > 0`, `μ l ≤ t` exactly when
  `t • B` contains the images of `l + 1` vectors of `Λ` independent over `K`; in particular each
  minimum is attained.
* `Submodule.successiveMinimum_pos`, `Submodule.monotoneOn_successiveMinimum`,
  `Submodule.successiveMinimum_antitone_body`, `Submodule.successiveMinimum_antitone_lattice`:
  positivity and monotonicity properties below `#ι`.
* `Submodule.exists_linearIndependent_mem_smul_successiveMinimum`: there are `#ι` vectors of
  `Λ`, independent over `K`, the `l`-th of them with image in `μ l • B`.
* `Submodule.successiveMin_mixedImage_le`,
  `Submodule.successiveMinimum_le_successiveMin_mixedImage`,
  `Submodule.successiveMinimum_zero_eq_successiveMin_mixedImage`, and
  `Submodule.successiveMin_mixedImage_le_mul`: comparisons between `μ` and `λ`.
* `Submodule.finrank_span_setOf_mem` and `Submodule.span_setOf_mem_eq_span_image`: the rank and
  initial-segment span of the lattice points in a positive dilate.
* `Submodule.prod_successiveMinimum_pow_mul_measure_le_two_pow_mul_covolume` and
  `Submodule.two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measure`
  (together with their `measureReal` counterparts): Minkowski's second theorem over `K`.

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
  Appendix C.2, Definition C.2.9, Remark C.2.10, and Theorem C.2.11.
* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter VIII.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics **785**, Springer, 1980,
  Chapter IV.
* The definition and the proofs of attainment and basic comparisons adapt
  `DiophantineApproximation/FieldMinima.lean` of R. Stephan's `Subspace-Theorems` formalization
  (Apache 2.0), <https://github.com/rwst/Subspace-Theorems>, to the real successive minima
  `ZLattice.successiveMin` of Tau Ceti.
-/

public section

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField
open scoped Pointwise Topology

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

/-- Dilating `B` by `c > 0` divides every successive minimum over `K` by `c`. -/
theorem successiveMinimum_smul (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K))
    {c : ℝ} (hc : 0 < c) (l : ℕ) :
    successiveMinimum Λ (c • B) l = successiveMinimum Λ B l / c := by
  rw [successiveMinimum_def, successiveMinimum_def, div_eq_inv_mul, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le)]
  congr 1
  ext t
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne'), inv_inv, smul_eq_mul,
    Set.mem_ofPred_eq, smul_smul, mul_comm t c, mul_pos_iff_of_pos_left hc]

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
/-- **Enlarging the body decreases the successive minima over `K`.** -/
theorem successiveMinimum_antitone_body (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    {B' : Set (ι → mixedSpace K)} (hBB' : (B : Set (ι → mixedSpace K)) ⊆ B')
    (hl : l < Fintype.card ι) :
    successiveMinimum Λ B' l ≤ successiveMinimum Λ B l := by
  have hpos := successiveMinimum_pos (Λ := Λ) hB hl
  obtain ⟨x, hx, hxB⟩ := (successiveMinimum_le_iff (Λ := Λ) hB hl hpos).1 le_rfl
  exact successiveMinimum_le hpos hx (fun k ↦ (hxB k).1)
    fun k ↦ Set.smul_set_mono hBB' (hxB k).2

open scoped Classical in
/-- **Enlarging the `𝓞 K`-submodule decreases the successive minima over `K`.** -/
theorem successiveMinimum_antitone_lattice (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    {Λ' : Submodule (𝓞 K) (ι → K)} (hΛ : Λ ≤ Λ') (hl : l < Fintype.card ι) :
    successiveMinimum Λ' B l ≤ successiveMinimum Λ B l := by
  have hpos := successiveMinimum_pos (Λ := Λ) hB hl
  obtain ⟨x, hx, hxB⟩ := (successiveMinimum_le_iff (Λ := Λ) hB hl hpos).1 le_rfl
  exact successiveMinimum_le hpos hx (fun k ↦ hΛ (hxB k).1) fun k ↦ (hxB k).2

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
/-- **Bombieri–Gubler Remark C.2.10**: when `ι` is nonempty, the zeroth successive minimum over `K`
equals the zeroth real successive minimum of `Λ.mixedImage`, without symmetry or balancedness. -/
theorem successiveMinimum_zero_eq_successiveMin_mixedImage [Nonempty ι]
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K))) :
    successiveMinimum Λ B 0 = ZLattice.successiveMinNat Λ.mixedImage B 0 := by
  refine le_antisymm ?_ (successiveMin_mixedImage_le hB Fintype.card_pos)
  simpa using successiveMinimum_le_successiveMin_mixedImage (Λ := Λ) hB Fintype.card_pos

open scoped Classical in
/-- **Upper bound on the `(d * (l + 1) - 1)`-th real successive minimum**: if `0 ∈ interior B`,
`B` is balanced at every infinite place (`∀ z ∈ B, ∀ a, (∀ w, normAtPlace w a ≤ 1) →
(fun i ↦ a * z i) ∈ B`), and `l < Fintype.card ι`, then the `([K : ℚ] * (l + 1) - 1)`-th real
successive minimum of `Λ.mixedImage` is at most
`integralBasisHouse K * successiveMinimum Λ B l`. -/
theorem successiveMin_mixedImage_le_mul (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB : 0 ∈ interior (B : Set (ι → mixedSpace K)))
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B)
    (hl : l < Fintype.card ι) :
    ZLattice.successiveMinNat Λ.mixedImage B (finrank ℚ K * (l + 1) - 1) ≤
      integralBasisHouse K * successiveMinimum Λ B l := by
  have ht := successiveMinimum_pos (Λ := Λ) hB hl
  obtain ⟨v, hv, hvΛB⟩ := (successiveMinimum_le_iff (Λ := Λ) hB hl ht).1 le_rfl
  set cK := integralBasisHouse K
  have hcK : 0 < cK := integralBasisHouse_pos
  have hd_pos : 0 < finrank ℚ K * (l + 1) := Nat.mul_pos Module.finrank_pos (Nat.succ_pos l)
  have hlt : finrank ℚ K * (l + 1) - 1 < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    have hle : finrank ℚ K * (l + 1) ≤ finrank ℚ K * Fintype.card ι := Nat.mul_le_mul_left _ hl
    omega
  -- Index the `[K : ℚ] * (l + 1)` products of `reducedIntegralBasis K` and `v` by `Fin`.
  have hsub : finrank ℚ K * (l + 1) - 1 + 1 = finrank ℚ K * (l + 1) := Nat.sub_add_cancel hd_pos
  let e : Fin (finrank ℚ K * (l + 1) - 1 + 1) ≃ Fin (finrank ℚ K) × Fin (l + 1) :=
    (finCongr hsub).trans finProdFinEquiv.symm
  let w : Fin (finrank ℚ K * (l + 1) - 1 + 1) → ι → mixedSpace K := fun m i ↦
    mixedEmbedding K ((reducedIntegralBasis K (e m).1 : K) * v (e m).2 i)
  have hw_lin : LinearIndependent ℝ w :=
    (linearIndependent_real_mixedEmbedding_mul
      (linearIndependent_real_mixedEmbedding_reducedIntegralBasis K) hv).comp e e.injective
  have hw_mem (m : Fin (finrank ℚ K * (l + 1) - 1 + 1)) : w m ∈ Λ.mixedImage := by
    refine mem_mixedImage.2 ⟨reducedIntegralBasis K (e m).1 • v (e m).2,
      Λ.smul_mem _ (hvΛB (e m).2).1, ?_⟩
    ext1 i
    simp [w, Algebra.smul_def]
  -- Rescale by `cK⁻¹` and apply placewise balancedness to keep each `w m` in the dilated body.
  have hw_body (m : Fin (finrank ℚ K * (l + 1) - 1 + 1)) :
      w m ∈ (cK * successiveMinimum Λ B l) • (B : Set (ι → mixedSpace K)) := by
    rcases (hvΛB (e m).2).2 with ⟨z, hz, hzv⟩
    set a : mixedSpace K := cK⁻¹ • mixedEmbedding K (reducedIntegralBasis K (e m).1 : K)
    have ha (u : InfinitePlace K) : normAtPlace u a ≤ 1 := by
      rw [normAtPlace_smul, abs_of_pos (inv_pos.2 hcK)]
      have hub := normAtPlace_mixedEmbedding_reducedIntegralBasis_le u (e m).1
      exact (mul_le_mul_of_nonneg_left hub (inv_nonneg.2 hcK.le)).trans_eq
        (inv_mul_cancel₀ hcK.ne')
    refine ⟨fun i ↦ a * z i, hBbal z hz a ha, ?_⟩
    ext1 i
    have hzi' : successiveMinimum Λ B l • z i = mixedEmbedding K (v (e m).2 i) := by
      simpa using congr_fun hzv i
    simp [w, a, map_mul, ← hzi', mul_comm cK, mul_smul, hcK.ne']
  rw [ZLattice.successiveMinNat_of_lt _ _ hlt]
  exact ZLattice.successiveMin_le (mul_pos hcK ht).le hw_lin hw_mem hw_body

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

section MinkowskiSecond

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Equivalence `Fin (card ι) × Fin [K : ℚ] ≃ Fin (finrank ℝ (ι → mixedSpace K))` sending `(l, r)`
to `[K : ℚ] * l + r`. -/
private noncomputable def blockIndexEquiv :
    Fin (Fintype.card ι) × Fin (finrank ℚ K) ≃ Fin (finrank ℝ (ι → mixedSpace K)) :=
  finProdFinEquiv.trans (finCongr (by rw [mul_comm, mixedEmbedding.finrank_pi]))

private theorem coe_blockIndexEquiv (l : Fin (Fintype.card ι)) (r : Fin (finrank ℚ K)) :
    (blockIndexEquiv (l, r) : ℕ) = finrank ℚ K * (l : ℕ) + (r : ℕ) := by
  simp [blockIndexEquiv, add_comm]

private theorem prod_pow_finrank_eq (g : Fin (Fintype.card ι) → ℝ) :
    ∏ l, g l ^ finrank ℚ K =
      ∏ p : Fin (Fintype.card ι) × Fin (finrank ℚ K), g p.1 := by
  rw [Fintype.prod_prod_type]
  simp

open scoped Classical in
/-- Block-product lower bound on `∏ m, ZLattice.successiveMin Λ.mixedImage B m` in terms of the
`[K : ℚ]`-th powers of `Λ.successiveMinimum B`. -/
private theorem prod_successiveMinimum_pow_le_prod_successiveMin
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K))) :
    ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K ≤
      ∏ m, ZLattice.successiveMin Λ.mixedImage B m := by
  rw [prod_pow_finrank_eq, ← Equiv.prod_comp (blockIndexEquiv (K := K) (ι := ι))]
  refine Finset.prod_le_prod₀ (fun p _ ↦ Λ.successiveMinimum_nonneg B p.1) fun ⟨l, r⟩ _ ↦ ?_
  have hdl : finrank ℚ K * (l : ℕ) < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    exact Nat.mul_lt_mul_of_pos_left l.isLt Module.finrank_pos
  refine (successiveMinimum_le_successiveMin_mixedImage (Λ := Λ) hB0 l.isLt).trans ?_
  rw [ZLattice.successiveMinNat_of_lt _ _ hdl]
  refine ZLattice.monotone_successiveMin Λ.mixedImage hB0 (Fin.le_def.2 ?_)
  simp only [coe_blockIndexEquiv]
  exact Nat.le_add_right _ _

open scoped Classical in
/-- Block-product upper bound on `∏ m, ZLattice.successiveMin Λ.mixedImage B m` for a body balanced
at every infinite place. -/
private theorem prod_successiveMin_le_integralBasisHouse_pow_mul_prod
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : ConvexBody (ι → mixedSpace K)}
    (hB0 : (0 : ι → mixedSpace K) ∈ interior (B : Set (ι → mixedSpace K)))
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) →
      (fun i ↦ a * z i) ∈ B) :
    ∏ m, ZLattice.successiveMin Λ.mixedImage B m ≤
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) *
        ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K := by
  have hpow : integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) *
      ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K =
      ∏ l : Fin (Fintype.card ι),
        (integralBasisHouse K * Λ.successiveMinimum B l) ^ finrank ℚ K := by
    simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← pow_mul]
  rw [hpow, prod_pow_finrank_eq, ← Equiv.prod_comp (blockIndexEquiv (K := K) (ι := ι))]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _) fun ⟨l, r⟩ _ ↦ ?_
  have hlt : finrank ℚ K * ((l : ℕ) + 1) - 1 < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    have hd_pos : 0 < finrank ℚ K * ((l : ℕ) + 1) :=
      Nat.mul_pos Module.finrank_pos (Nat.succ_pos _)
    have hle : finrank ℚ K * ((l : ℕ) + 1) ≤ finrank ℚ K * Fintype.card ι :=
      Nat.mul_le_mul_left _ l.isLt
    omega
  refine (ZLattice.monotone_successiveMin Λ.mixedImage hB0 (a := blockIndexEquiv (l, r))
    (b := ⟨finrank ℚ K * ((l : ℕ) + 1) - 1, hlt⟩) (Fin.le_def.2 ?_)).trans ?_
  · simp only [coe_blockIndexEquiv]
    have hr : (r : ℕ) + 1 ≤ finrank ℚ K := r.isLt
    have hmul : finrank ℚ K * ((l : ℕ) + 1) = finrank ℚ K * (l : ℕ) + finrank ℚ K :=
      Nat.mul_succ _ _
    omega
  · rw [← ZLattice.successiveMinNat_of_lt _ _ hlt]
    exact Λ.successiveMin_mixedImage_le_mul hB0 hBbal l.isLt

open scoped Classical in
/-- **Minkowski's second theorem over `K`, upper bound** (`ENNReal` measure form; Bombieri–Gubler
Theorem C.2.11, upper inequality): for a full `𝓞 K`-lattice `Λ` in `ι → K`, an additive Haar
measure `μ` on `ι → mixedSpace K`, and a compact symmetric convex set `B`,
`(∏ l, μ l ^ [K : ℚ]) * μ B ≤ 2 ^ ([K : ℚ] * card ι) * covolume Λ.mixedImage μ`. -/
theorem prod_successiveMinimum_pow_mul_measure_le_two_pow_mul_covolume
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) :
    ENNReal.ofReal (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) * μ B ≤
      2 ^ (finrank ℚ K * Fintype.card ι) *
        ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) := by
  rcases (interior B).eq_empty_or_nonempty with hempty | hne
  · rw [← measure_interior_of_null_frontier (hBc.addHaar_frontier μ), hempty]
    simp
  let Bbody : ConvexBody (ι → mixedSpace K) := ⟨B, hBc, hBk, hne.mono interior_subset⟩
  have hB0 : (0 : ι → mixedSpace K) ∈ interior (Bbody : Set (ι → mixedSpace K)) :=
    hBc.zero_mem_interior_of_symmetric hBs hne
  have hprod := Λ.prod_successiveMinimum_pow_le_prod_successiveMin hB0
  calc ENNReal.ofReal (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) * μ B
      ≤ ENNReal.ofReal (∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m) * μ B := by
        gcongr
        exact hprod
      _ ≤ 2 ^ finrank ℝ (ι → mixedSpace K) *
          ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) :=
        ZLattice.prod_successiveMin_mul_measure_le_two_pow_mul_covolume Λ.mixedImage μ hBs
      _ = 2 ^ (finrank ℚ K * Fintype.card ι) *
          ENNReal.ofReal (ZLattice.covolume Λ.mixedImage μ) := by rw [mixedEmbedding.finrank_pi]

open scoped Classical in
/-- **Minkowski's second theorem over `K`, upper bound** (`ℝ`-valued measure form):
`(∏ l, μ l ^ [K : ℚ]) * μ.real B ≤ 2 ^ ([K : ℚ] * card ι) * covolume Λ.mixedImage μ`. -/
theorem prod_successiveMinimum_pow_mul_measureReal_le_two_pow_mul_covolume
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B)
    (hBs : ∀ z ∈ B, -z ∈ B) :
    (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) * μ.real B ≤
      2 ^ (finrank ℚ K * Fintype.card ι) * ZLattice.covolume Λ.mixedImage μ := by
  have h := ENNReal.toReal_mono (by finiteness)
    (Λ.prod_successiveMinimum_pow_mul_measure_le_two_pow_mul_covolume μ hBc hBk hBs)
  have hnn : 0 ≤ ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K :=
    Finset.prod_nonneg fun l _ ↦ pow_nonneg (Λ.successiveMinimum_nonneg B l) _
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos Λ.mixedImage μ).le, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ← measureReal_def] at h

open scoped Classical in
/-- **Minkowski's second theorem over `K`, lower bound** (`ENNReal` measure form; Bombieri–Gubler
Theorem C.2.11, lower inequality): for a full `𝓞 K`-lattice `Λ` in `ι → K`, an additive Haar
measure `μ` on `ι → mixedSpace K`, and a compact convex neighbourhood `B` of `0` balanced at every
infinite place,
`2 ^ N / (N! · c_K ^ N) * covolume Λ.mixedImage μ ≤ (∏ l, μ l ^ [K : ℚ]) * μ B`,
where `N = [K : ℚ] * card ι` and `c_K = integralBasisHouse K`. -/
theorem two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measure
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    ENNReal.ofReal ((2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) /
        (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
          integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι)) *
        ZLattice.covolume Λ.mixedImage μ) ≤
      ENNReal.ofReal (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) *
        μ B := by
  let Bbody : ConvexBody (ι → mixedSpace K) := ⟨B, hBc, hBk, ⟨0, mem_of_mem_nhds hB0⟩⟩
  have hBint : (0 : ι → mixedSpace K) ∈ interior (Bbody : Set (ι → mixedSpace K)) :=
    mem_interior_iff_mem_nhds.2 hB0
  have hBs : ∀ z ∈ B, -z ∈ B := fun z hz ↦ by
    simpa [Pi.neg_def] using hBbal z hz (-1) fun w ↦ by simp [normAtPlace_neg]
  set N := finrank ℚ K * Fintype.card ι
  have hN : finrank ℝ (ι → mixedSpace K) = N := mixedEmbedding.finrank_pi
  have hcK : 0 < integralBasisHouse K ^ N := pow_pos integralBasisHouse_pos N
  have hprod := Λ.prod_successiveMin_le_integralBasisHouse_pow_mul_prod hBint hBbal
  have hmink := ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measure
    Λ.mixedImage μ hBint hBs
  rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hcK).ne' ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (integralBasisHouse K ^ N) *
        ENNReal.ofReal ((2 : ℝ) ^ N / ((N.factorial : ℝ) * integralBasisHouse K ^ N) *
          ZLattice.covolume Λ.mixedImage μ)
      = ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ (ι → mixedSpace K) /
          (finrank ℝ (ι → mixedSpace K)).factorial * ZLattice.covolume Λ.mixedImage μ) := by
          rw [hN, ← ENNReal.ofReal_mul hcK.le]
          congr 1
          field_simp [hcK.ne']
    _ ≤ ENNReal.ofReal (∏ m, ZLattice.successiveMin Λ.mixedImage Bbody m) * μ B := hmink
    _ ≤ ENNReal.ofReal (integralBasisHouse K ^ N *
          ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) * μ B := by
          gcongr
          exact hprod
    _ = ENNReal.ofReal (integralBasisHouse K ^ N) *
          (ENNReal.ofReal (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) *
            μ B) := by
          rw [ENNReal.ofReal_mul hcK.le, mul_assoc]

open scoped Classical in
/-- **Minkowski's second theorem over `K`, lower bound** (`ℝ`-valued measure form): for a compact
convex neighbourhood `B` of `0` balanced at every infinite place,
`2 ^ N / (N! · c_K ^ N) * covolume Λ.mixedImage μ ≤ (∏ l, μ l ^ [K : ℚ]) * μ.real B`. -/
theorem two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measureReal
    (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K) := by volume_tac) [μ.IsAddHaarMeasure]
    {B : Set (ι → mixedSpace K)} (hBc : Convex ℝ B) (hBk : IsCompact B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    (2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) /
        (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
          integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι)) *
        ZLattice.covolume Λ.mixedImage μ ≤
      (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K) * μ.real B := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBk.measure_lt_top.ne)
    (Λ.two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measure
      μ hBc hBk hB0 hBbal)
  have hnn : 0 ≤ ∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l ^ finrank ℚ K :=
    Finset.prod_nonneg fun l _ ↦ pow_nonneg (Λ.successiveMinimum_nonneg B l) _
  have hcK : 0 < integralBasisHouse K := integralBasisHouse_pos
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn, ENNReal.toReal_ofReal
    (mul_nonneg (by positivity) (ZLattice.covolume_pos Λ.mixedImage μ).le),
    ← measureReal_def] at h

open scoped Classical in
-- Over `ℚ`, `integralBasisHouse ℚ = 1`, so the lower bound in Minkowski's second theorem over `ℚ`
-- recovers the classical constant `2 ^ n / n!` without loss.
example {ι : Type*} [Fintype ι] (Λ : Submodule (𝓞 ℚ) (ι → ℚ))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    {B : Set (ι → mixedSpace ℚ)} (hBc : Convex ℝ B) (hBk : IsCompact B) (hB0 : B ∈ 𝓝 0)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace ℚ, (∀ w, normAtPlace w a ≤ 1) → (fun i ↦ a * z i) ∈ B) :
    (2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial *
        ZLattice.covolume Λ.mixedImage ≤
      (∏ l : Fin (Fintype.card ι), Λ.successiveMinimum B l) * volume.real B := by
  simpa [Module.finrank_self, integralBasisHouse_rat] using
    Λ.two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measureReal
      volume hBc hBk hB0 hBbal

end MinkowskiSecond

end Submodule
