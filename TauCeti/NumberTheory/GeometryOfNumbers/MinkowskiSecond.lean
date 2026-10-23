/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import TauCeti.Algebra.Module.ZLattice.AdaptedBasis
import TauCeti.Algebra.Module.ZLattice.Covolume
import TauCeti.LinearAlgebra.Basis.Triangular
import TauCeti.LinearAlgebra.Pi
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Minkowski's second theorem: the upper bound

Let `L` be a full lattice in an `n`-dimensional real normed space `E`, let `μ` be an additive
Haar measure on `E`, and let `K` be a convex set symmetric about the origin. Minkowski's second
theorem bounds the product of the successive minima `λ₀ ≤ ⋯ ≤ λₙ₋₁` of `L` with respect to `K`:

```text
λ₀ ⋯ λₙ₋₁ · μ K ≤ 2ⁿ · covolume L μ.
```

Since `λ₀ ≤ λᵢ` for every `i`, this strengthens Minkowski's first theorem, and it is the bound
against which the products of the gauges of short lattice bases (such as fundamental systems of
units, or bases of the integer kernel of a matrix) are measured.

The main statement does not use a successive-minima function. It takes `ℝ`-independent lattice
vectors `a i` and nonnegative numbers `g i` such that every lattice vector `v` with
`gauge K v < g j` lies in the span of `a 0, …, a (j - 1)`. Independent vectors realizing the
successive minima satisfy this with `g = λ`: if `gauge K v < λ_j` and `i ≤ j` is least with
`λ_i > gauge K v`, then `a 0, …, a (i - 1)` and `v` lie in `(gauge K v) • K`, so `v` is in the span
of `a 0, …, a (i - 1)` (`ZLattice.mem_span_image_Iio_of_gauge_lt_successiveMin`). Conversely,
every such `g` satisfies `g j ≤ λ_j`.

## Main results

* `ZLattice.prod_mul_measure_le_two_pow_mul_covolume`:
  `(∏ i, g i) * μ K ≤ 2 ^ n * covolume L μ`.
* `ZLattice.prod_successiveMin_mul_measure_le_two_pow_mul_covolume`: the classical form
  `λ₀ ⋯ λₙ₋₁ · μ K ≤ 2ⁿ · covolume L μ` for a symmetric convex body `K` with `0` in its interior.

## Proof

Coordinates in a `ℤ`-basis of `L` adapted to the flag spanned by the `a i`
(`ZLattice.exists_basis_triangular`) reduce the statement to `L = ℤⁿ ⊆ ℝⁿ`, with
`span (a 0, …, a (j - 1))` the span of the first `j` coordinate vectors, and to the open convex
set `C = ½ • interior K`, whose volume is `2⁻ⁿ μ K / covolume L μ`
(`ZLattice.volume_image_eq_measure_div_covolume`). The hypothesis says that two points of `g j • C`
whose difference is an integer vector agree in all coordinates from the `j`-th on.

For `m ≤ n`, fold a set `Y ⊆ ℝⁿ` modulo the integer vectors supported on the first `m`
coordinates into the slab where those coordinates lie in `[0, 1)`. Folding all `n` coordinates
gives a subset of the unit cube, of volume at most `1`. Folding no coordinate does nothing. Write
`Vₘ(t)` for the volume of the `m`-fold of `t • C`. Two estimates relate these volumes:

* *unfolding* (`volume_fold_le_fold_succ`): `Vₘ(t) ≤ Vₘ₊₁(t)` when `t ≤ g m`, because the
  translates of the `m`-fold of `t • C` by integer multiples of the `m`-th coordinate vector are
  then pairwise disjoint;
* *dilation* (`volume_fold_smul`): `ρ ^ (n - m) · Vₘ(t) ≤ Vₘ(ρ t)` for `ρ ≥ 1`. On each fibre over
  the last `n - m` coordinates, `ρ` times a nonempty convex set contains a translate of it, and
  the folded volume of a set is translation invariant.

Chaining them from `V₀(g 0) = g 0 ^ n · vol C` up to `Vₙ(g (n - 1)) ≤ 1` gives
`g 0 ⋯ g (n - 1) · vol C ≤ 1`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter VIII.
* H. Davenport, *Minkowski's inequality for the minima associated with a convex body*, Quart. J.
  Math. Oxford **10** (1939), 119–121.
-/

public section

open MeasureTheory Module Set Submodule
open scoped Pointwise

namespace ZLattice

/-! ### Folding modulo integer vectors -/

section Fold

/-- The fold of `W ⊆ ℝ^ι` modulo `ℤ^ι` into the unit cube: the points of `[0, 1)^ι` some integer
translate of which lies in `W`. -/
private def foldPi {ι : Type*} (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {y | (∀ i, y i ∈ Ico (0 : ℝ) 1) ∧ ∃ k : ι → ℤ, (y + fun i ↦ (k i : ℝ)) ∈ W}

private theorem foldPi_mono {ι : Type*} {W W' : Set (ι → ℝ)} (h : W ⊆ W') :
    foldPi W ⊆ foldPi W' :=
  fun _ ⟨hy, k, hk⟩ ↦ ⟨hy, k, h hk⟩

variable {ι : Type*} [Fintype ι]

/-- The fold of a set has the same volume as the fold of any of its translates: both are cut
from one `ℤ^ι`-invariant set by two fundamental domains of `ℤ^ι`. -/
private theorem volume_foldPi_preimage_add {W : Set (ι → ℝ)} (hW : MeasurableSet W)
    (c : ι → ℝ) : volume (foldPi ((· + c) ⁻¹' W)) = volume (foldPi W) := by
  let b := Pi.basisFun ℝ ι
  have hF : IsAddFundamentalDomain (span ℤ (range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain' b volume
  have : Countable (span ℤ (range b)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (range b)))
  have hF' := hF.vadd_of_comm c
  -- `G` is the saturation of `W` under integer translations.
  set G : Set (ι → ℝ) := {y | ∃ k : ι → ℤ, (y + fun i ↦ (k i : ℝ)) ∈ W}
  have hG : MeasurableSet G := by
    have : G = ⋃ k : ι → ℤ, (· + fun i ↦ (k i : ℝ)) ⁻¹' W := by ext; simp [G]
    rw [this]
    exact MeasurableSet.iUnion fun k ↦ measurable_add_const _ hW
  have hGinv : ∀ g : (span ℤ (range b)).toAddSubgroup, (fun x ↦ g +ᵥ x) ⁻¹' G = G := by
    rintro ⟨g, hg⟩
    have hz : ∀ i, ∃ z : ℤ, (z : ℝ) = g i := fun i ↦ by
      obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ g).1 hg i
      exact ⟨z, by simpa [b] using hz⟩
    choose z hz using hz
    ext x
    simp only [mem_preimage, AddSubgroup.vadd_def, vadd_eq_add, G, mem_ofPred_eq]
    refine ⟨fun ⟨k, hk⟩ ↦ ⟨k + z, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k - z, ?_⟩⟩ <;>
    · convert hk using 1
      ext i
      simp [hz]
      ring
  have hFeq : ZSpan.fundamentalDomain b = {y : ι → ℝ | ∀ i, y i ∈ Ico (0 : ℝ) 1} := by
    ext; simp [b]
  have h1 : foldPi W = G ∩ ZSpan.fundamentalDomain b := by
    ext y; simp [foldPi, G, hFeq, and_comm]
  have h2 : (· + -c) ⁻¹' foldPi ((· + c) ⁻¹' W) = G ∩ (c +ᵥ ZSpan.fundamentalDomain b) := by
    ext y
    simp only [mem_preimage, foldPi, mem_ofPred_eq, mem_inter_iff, G, hFeq,
      mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Pi.add_apply, Pi.neg_apply]
    constructor
    · rintro ⟨hy, k, hk⟩
      exact ⟨⟨k, by convert hk using 1; ext; simp; ring⟩, fun i ↦ by simpa [add_comm] using hy i⟩
    · rintro ⟨⟨k, hk⟩, hy⟩
      exact ⟨fun i ↦ by simpa [add_comm] using hy i, k, by convert hk using 1; ext; simp; ring⟩
  rw [← measure_preimage_add_right volume (-c), h2, h1, hF'.measure_set_eq hF hG hGinv]

/-- Dilating a convex set by `ρ ≥ 1` does not decrease the volume of its fold, since the dilate
contains a translate of the set. -/
private theorem volume_foldPi_le_smul {W : Set (ι → ℝ)} (hW : MeasurableSet W)
    (hWc : Convex ℝ W) {ρ : ℝ} (hρ : 1 ≤ ρ) : volume (foldPi W) ≤ volume (foldPi (ρ • W)) := by
  rcases W.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · simp [foldPi]
  have hρ0 : 0 < ρ := by linarith
  rw [← volume_foldPi_preimage_add hW (-((ρ - 1) • w))]
  refine measure_mono (foldPi_mono fun y hy ↦ ?_)
  rw [mem_smul_set_iff_inv_smul_mem₀ hρ0.ne']
  have := hWc hy hw (inv_nonneg.2 hρ0.le) (sub_nonneg.2 (inv_le_one_of_one_le₀ hρ))
    (add_sub_cancel _ _)
  convert this using 1
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

variable {n : ℕ}

/-- The fold of `Y ⊆ ℝⁿ` modulo the integer vectors supported on the first `m` coordinates, into
the slab where those coordinates lie in `[0, 1)`. -/
private def fold (m : ℕ) (Y : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | (∀ i : Fin n, (i : ℕ) < m → x i ∈ Ico (0 : ℝ) 1) ∧
    ∃ k : Fin n → ℤ, (∀ i : Fin n, m ≤ (i : ℕ) → k i = 0) ∧ (x + fun i ↦ (k i : ℝ)) ∈ Y}

private theorem fold_zero (Y : Set (Fin n → ℝ)) : fold 0 Y = Y := by
  ext x
  refine ⟨fun ⟨_, k, hk, hx⟩ ↦ ?_, fun hx ↦ ⟨fun _ hi ↦ absurd hi (Nat.not_lt_zero _), 0,
    fun _ _ ↦ rfl, by convert hx; ext; simp⟩⟩
  have : (fun i ↦ (k i : ℝ)) = 0 := funext fun i ↦ by simp [hk i (Nat.zero_le _)]
  simpa [this] using hx

private theorem volume_fold_le_one (Y : Set (Fin n → ℝ)) : volume (fold n Y) ≤ 1 :=
  calc volume (fold n Y) ≤ volume (Set.pi univ fun _ : Fin n ↦ Ico (0 : ℝ) 1) :=
        measure_mono fun _ hx i _ ↦ hx.1 i i.isLt
    _ = 1 := by simp [Real.volume_pi_Ico]

private theorem measurableSet_fold (m : ℕ) {Y : Set (Fin n → ℝ)} (hY : MeasurableSet Y) :
    MeasurableSet (fold m Y) := by
  have : fold m Y = (⋂ i : Fin n, ⋂ (_ : (i : ℕ) < m), (fun x ↦ x i) ⁻¹' Ico (0 : ℝ) 1) ∩
      ⋃ k ∈ {k : Fin n → ℤ | ∀ i : Fin n, m ≤ (i : ℕ) → k i = 0},
        (· + fun i ↦ (k i : ℝ)) ⁻¹' Y := by
    ext x; simp [fold]
  rw [this]
  exact (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    measurable_pi_apply i measurableSet_Ico).inter
    (MeasurableSet.biUnion (to_countable _) fun k _ ↦ measurable_add_const _ hY)

/-- The translates of the `j`-fold of `X` by integer multiples of the `j`-th coordinate vector,
cut to the slab `0 ≤ x j < 1`, lie in the `(j + 1)`-fold of `X`. -/
private theorem preimage_add_inter_subset_fold_succ (X : Set (Fin n → ℝ)) {j : ℕ} (hj : j < n)
    (m : ℤ) : (· + (m : ℝ) • Pi.single ⟨j, hj⟩ 1) ⁻¹' fold j X ∩
      {x | x ⟨j, hj⟩ ∈ Ico (0 : ℝ) 1} ⊆ fold (j + 1) X := by
  rintro x ⟨⟨hlt, k, hk, hxk⟩, hxJ⟩
  set J : Fin n := ⟨j, hj⟩
  refine ⟨fun i hi ↦ ?_, k + m • Pi.single J 1, fun i hi ↦ ?_, ?_⟩
  · rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
    · have hiJ : i ≠ J := fun h ↦ by simp [h, J] at hi
      simpa [hiJ] using hlt i hi
    · simpa [show i = J from Fin.ext hi] using hxJ
  · have hiJ : i ≠ J := fun h ↦ by simp [h, J] at hi
    simp [hk i (by omega), hiJ]
  · convert hxk using 1
    ext i
    by_cases hi : i = J
    · simp [hi]
      ring
    · simp [hi]

/-- **Unfolding.** If two points of `X` whose difference is an integer vector have the same
`j`-th coordinate, then folding the `j`-th coordinate as well does not decrease the volume of the
`j`-fold of `X`. -/
private theorem volume_fold_le_fold_succ {X : Set (Fin n → ℝ)} (hX : MeasurableSet X) {j : ℕ}
    (hj : j < n)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, (∀ i, ∃ k : ℤ, x i - y i = k) → x ⟨j, hj⟩ = y ⟨j, hj⟩) :
    volume (fold j X) ≤ volume (fold (j + 1) X) := by
  set J : Fin n := ⟨j, hj⟩
  set e : Fin n → ℝ := Pi.single J 1
  set T := fold j X
  have hT : MeasurableSet T := measurableSet_fold j hX
  let B : ℤ → Set (Fin n → ℝ) := fun m ↦ (· + (m : ℝ) • e) ⁻¹' T ∩ {x | x J ∈ Ico 0 1}
  -- Two translates of a point by multiples of `e` that lie in `T` coincide.
  have key : ∀ x : Fin n → ℝ, ∀ m m' : ℤ, x + (m : ℝ) • e ∈ T → x + (m' : ℝ) • e ∈ T →
      m = m' := by
    rintro x m m' ⟨-, k, hk, hx⟩ ⟨-, k', hk', hx'⟩
    have h := hsep _ hx _ hx' fun i ↦
      ⟨(m - m') * (Pi.single J (1 : ℤ) : Fin n → ℤ) i + k i - k' i, by
        by_cases hi : i = J <;> simp [e, hi]; ring⟩
    have h' : (m : ℝ) = m' := by simpa [e, hk J le_rfl, hk' J le_rfl] using h
    exact_mod_cast h'
  -- Cut `T` along the integer parts of its `j`-th coordinate and translate the pieces.
  calc volume T = ∑' m : ℤ, volume (T ∩ {x | x J ∈ Ico (m : ℝ) (m + 1)}) := by
        rw [← measure_iUnion]
        · congr 1
          ext x
          simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_Ico]
          exact ⟨fun hx ↦ ⟨⌊x J⌋, hx, Int.floor_le _, Int.lt_floor_add_one _⟩,
            fun ⟨_, hx, _⟩ ↦ hx⟩
        · intro m m' hmm'
          refine Set.disjoint_left.2 fun x hx hx' ↦ hmm' ?_
          rw [← Int.floor_eq_iff.2 hx.2, ← Int.floor_eq_iff.2 hx'.2]
        · exact fun m ↦ hT.inter (measurable_pi_apply J measurableSet_Ico)
    _ = ∑' m : ℤ, volume (B m) := by
        congr 1
        ext m
        rw [← measure_preimage_add_right volume ((m : ℝ) • e)]
        congr 1
        ext x
        simp [B, e, J, add_comm (m : ℝ)]
    _ = volume (⋃ m, B m) := by
        refine (measure_iUnion (fun m m' hmm' ↦ Set.disjoint_left.2 fun x hx hx' ↦ hmm' ?_)
          fun m ↦ (measurable_add_const _ hT).inter (measurable_pi_apply J measurableSet_Ico)).symm
        exact key x m m' hx.1 hx'.1
    _ ≤ volume (fold (j + 1) X) :=
        measure_mono (iUnion_subset fun m ↦ preimage_add_inter_subset_fold_succ X hj m)

/-- The splitting of `ℝⁿ` into its first `m` coordinates and the remaining ones. -/
private abbrev splitEquiv (n m : ℕ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ ℝ) (fun i : Fin n ↦ (i : ℕ) < m)

private theorem splitEquiv_symm_apply (m : ℕ) (y : {i : Fin n // (i : ℕ) < m} → ℝ)
    (z : {i : Fin n // ¬(i : ℕ) < m} → ℝ) (i : Fin n) :
    (splitEquiv n m).symm (y, z) i = if h : (i : ℕ) < m then y ⟨i, h⟩ else z ⟨i, h⟩ := (rfl)

/-- The fibre of the `m`-fold of `Y` over the last `n - m` coordinates is the full fold of the
fibre of `Y`. -/
private theorem fiber_fold (m : ℕ) (Y : Set (Fin n → ℝ)) (z : {i : Fin n // ¬(i : ℕ) < m} → ℝ) :
    {y | (splitEquiv n m).symm (y, z) ∈ fold m Y} =
      foldPi {y | (splitEquiv n m).symm (y, z) ∈ Y} := by
  ext y
  simp only [fold, foldPi, mem_ofPred_eq]
  constructor
  · rintro ⟨hI, k, hk, hY⟩
    refine ⟨fun i ↦ by simpa [splitEquiv_symm_apply, i.2] using hI i.1 i.2,
      fun i ↦ k i.1, ?_⟩
    convert hY using 1
    ext i
    by_cases h : (i : ℕ) < m
    · simp [splitEquiv_symm_apply, h]
    · simp [splitEquiv_symm_apply, h, hk i (not_lt.1 h)]
  · rintro ⟨hI, k, hY⟩
    refine ⟨fun i hi ↦ by simpa [splitEquiv_symm_apply, hi] using hI ⟨i, hi⟩,
      fun i ↦ if h : (i : ℕ) < m then k ⟨i, h⟩ else 0, fun i hi ↦ by simp [not_lt.2 hi], ?_⟩
    convert hY using 1
    ext i
    by_cases h : (i : ℕ) < m <;> simp [splitEquiv_symm_apply, h]

/-- **Dilation.** Dilating a convex set by `ρ ≥ 1` multiplies the volume of its `m`-fold by at
least `ρ ^ (n - m)`. Dividing the last `n - m` coordinates by `ρ` multiplies volumes by
`ρ ^ -(n - m)` and commutes with folding, and fibrewise it turns the dilate into `ρ` times a convex
set, whose fold is at least as large. -/
private theorem volume_fold_smul {X : Set (Fin n → ℝ)} (hX : MeasurableSet X)
    (hXc : Convex ℝ X) (m : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ENNReal.ofReal (ρ ^ (n - m)) * volume (fold m X) ≤ volume (fold m (ρ • X)) := by
  have hρ0 : 0 < ρ := by linarith
  -- `D` divides the last `n - m` coordinates by `ρ`.
  let d : Fin n → ℝ := fun i ↦ if (i : ℕ) < m then 1 else ρ⁻¹
  let D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' (Matrix.diagonal d)
  have hD : ∀ x i, D x i = d i * x i := fun x i ↦ by simp [D, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det D = ρ⁻¹ ^ (n - m) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i : Fin n ↦ (i : ℕ) < m
    simp only [Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt, not_lt] at h
    simp [D, d, Finset.prod_ite]
    congr 1
    omega
  set X' := D ⁻¹' X
  have hX' : MeasurableSet X' := D.continuous_of_finiteDimensional.measurable hX
  have hfold : fold m X' = D ⁻¹' fold m X := by
    ext x
    simp only [fold, mem_ofPred_eq, mem_preimage, X', hD, d]
    refine and_congr (forall_congr' fun i ↦ imp_congr_right fun hi ↦ by simp [hi])
      (exists_congr fun k ↦ and_congr_right fun hk ↦ ?_)
    rw [show D (x + fun i ↦ (k i : ℝ)) = D x + fun i ↦ (k i : ℝ) from ?_]
    ext i
    by_cases h : (i : ℕ) < m
    · simp [hD, d, h]
    · simp [hD, d, h, hk i (not_lt.1 h)]
  have hvol : volume (fold m X') = ENNReal.ofReal (ρ ^ (n - m)) * volume (fold m X) := by
    rw [hfold, Measure.addHaar_preimage_linearMap _ (by simp [hdet, hρ0.ne']), hdet, inv_pow,
      inv_inv, abs_of_pos (by positivity)]
  -- The fibre of `ρ • X` is `ρ` times the fibre of `X'`.
  have hfib : ∀ z, {y | (splitEquiv n m).symm (y, z) ∈ ρ • X} =
      ρ • {y | (splitEquiv n m).symm (y, z) ∈ X'} := by
    intro z
    ext y
    simp only [mem_ofPred_eq, mem_smul_set_iff_inv_smul_mem₀ hρ0.ne', X', mem_preimage]
    rw [show D ((splitEquiv n m).symm (ρ⁻¹ • y, z)) = ρ⁻¹ • (splitEquiv n m).symm (y, z) from ?_]
    ext i
    by_cases h : (i : ℕ) < m <;> simp [hD, d, h]
  -- Compare the folds fibrewise over the last `n - m` coordinates.
  have hsplit := fun S : Set (Fin n → ℝ) ↦ Measure.pi_apply_eq_lintegral_piEquivPiSubtypeProd_symm
    (fun _ : Fin n ↦ (volume : Measure ℝ)) (fun i : Fin n ↦ (i : ℕ) < m) (s := S)
  rw [← hvol]
  refine (hsplit _ (measurableSet_fold m hX')).trans_le ((lintegral_mono fun z ↦ ?_).trans_eq
    (hsplit _ (measurableSet_fold m (hX.const_smul₀ ρ))).symm)
  rw [fiber_fold, fiber_fold, hfib]
  -- The fibre of the convex set `X'` is the preimage under an affine map.
  have hc : Convex ℝ {y | (splitEquiv n m).symm (y, z) ∈ X'} := by
    convert ((hXc.linear_preimage D).linear_preimage (LinearEquiv.piEquivPiSubtypeProd ℝ
      (fun i : Fin n ↦ (i : ℕ) < m) fun _ ↦ ℝ).symm.toLinearMap).affine_preimage
      ((AffineMap.id ℝ _).prod (AffineMap.const ℝ _ z)) using 1
    ext y
    simp only [mem_ofPred_eq, mem_preimage, AffineMap.prod_apply, AffineMap.id_apply,
      AffineMap.const_apply, LinearEquiv.coe_coe, X']
    congr! 2
    ext i
    simp [splitEquiv_symm_apply]
  exact volume_foldPi_le_smul ((splitEquiv n m).symm.measurable.comp measurable_prodMk_right hX')
    hc hρ

end Fold

/-! ### The theorem in coordinates -/

/-- Minkowski's second theorem for `ℤⁿ ⊆ ℝⁿ`, in the form produced by the coordinates: if two
points of `g j • C` whose difference is an integer vector always have the same `j`-th coordinate,
then `g 0 ⋯ g (n - 1) · vol C ≤ 1`. -/
private theorem prod_mul_volume_le_one {n : ℕ} {C : Set (Fin n → ℝ)} (hC : MeasurableSet C)
    (hCc : Convex ℝ C) (g : ℕ → ℝ) (hg0 : ∀ i < n, 0 < g i)
    (hg : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hsep : ∀ j (hj : j < n), ∀ x ∈ g j • C, ∀ y ∈ g j • C, (∀ i, ∃ k : ℤ, x i - y i = k) →
      x ⟨j, hj⟩ = y ⟨j, hj⟩) :
    ENNReal.ofReal (∏ i ∈ Finset.range n, g i) * volume C ≤ 1 := by
  -- The volume of the `m`-fold of `t • C` is at least `(∏ i < m, g i) * t ^ (n - m) * vol C`.
  have claim : ∀ m ≤ n, ∀ t : ℝ, 0 < t → (∀ i < m, g i ≤ t) →
      ENNReal.ofReal ((∏ i ∈ Finset.range m, g i) * t ^ (n - m)) * volume C ≤
        volume (fold m (t • C)) := by
    intro m
    induction m with
    | zero =>
      intro _ t ht _
      rw [fold_zero, Measure.addHaar_smul_of_nonneg _ ht.le, finrank_fin_fun]
      simp
    | succ m ih =>
      intro hm t ht hgt
      have hm' : m < n := hm
      have hs : 0 < g m := hg0 m hm'
      have h1 := volume_fold_smul (hC.const_smul₀ (g m)) (hCc.smul (g m)) (m + 1)
        ((one_le_div hs).2 (hgt m (Nat.lt_succ_self m)))
      rw [smul_smul, div_mul_cancel₀ t hs.ne'] at h1
      have h2 := volume_fold_le_fold_succ (hC.const_smul₀ (g m)) hm' (hsep m hm')
      have h3 := ih hm'.le (g m) hs fun i hi ↦ hg i m hi.le hm'
      calc ENNReal.ofReal ((∏ i ∈ Finset.range (m + 1), g i) * t ^ (n - (m + 1))) * volume C
          = ENNReal.ofReal ((t / g m) ^ (n - (m + 1))) *
              (ENNReal.ofReal ((∏ i ∈ Finset.range m, g i) * g m ^ (n - m)) * volume C) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            rw [Finset.prod_range_succ, div_pow, show n - m = n - (m + 1) + 1 by omega, pow_succ]
            field_simp
        _ ≤ _ := (mul_le_mul_right (h3.trans h2) _).trans h1
  have ht : 0 < ∑ i ∈ Finset.range n, g i + 1 := by
    have := Finset.sum_nonneg fun i (hi : i ∈ Finset.range n) ↦ (hg0 i (by simpa using hi)).le
    linarith
  have := claim n le_rfl _ ht fun i hi ↦ by
    have := Finset.single_le_sum (fun j (hj : j ∈ Finset.range n) ↦ (hg0 j (by simpa using hj)).le)
      (Finset.mem_range.2 hi)
    linarith
  simpa using this.trans (volume_fold_le_one _)

/-! ### The general theorem -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In coordinates `φ` in which `L` is `ℤⁿ` and the span of `a 0, …, a (j - 1)` lies in the kernel
of the `j`-th coordinate, two points of `g j • φ '' (½ • interior K)` whose difference is an
integer vector have the same `j`-th coordinate: their difference is `φ w` for some `w ∈ L` with
`gauge K w < g j`. -/
private theorem apply_eq_of_mem_smul_image {L : Submodule ℤ E} {K : Set E} (hK : Convex ℝ K)
    (hKs : ∀ x ∈ K, -x ∈ K) (hKabs : Absorbent ℝ K) {n : ℕ} {a : Fin n → E} {g : Fin n → ℝ}
    (hg0 : ∀ i, 0 < g i) (hgap : ∀ j, ∀ v ∈ L, gauge K v < g j → v ∈ span ℝ (a '' Iio j))
    (φ : E ≃ₗ[ℝ] (Fin n → ℝ)) (hmemL : ∀ v, v ∈ L ↔ ∀ i, φ v i ∈ range ((↑) : ℤ → ℝ))
    (hflag : ∀ j, ∀ v ∈ span ℝ (a '' Iio j), φ v j = 0) (j : Fin n) {x y : Fin n → ℝ}
    (hx : x ∈ g j • φ '' ((1 / 2 : ℝ) • interior K))
    (hy : y ∈ g j • φ '' ((1 / 2 : ℝ) • interior K)) (hxy : ∀ i, ∃ k : ℤ, x i - y i = k) :
    x j = y j := by
  obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨_, ⟨u', hu', rfl⟩, rfl⟩, rfl⟩ := hy
  set w : E := (g j / 2) • (u - u')
  have hw : φ w = g j • φ ((1 / 2 : ℝ) • u) - g j • φ ((1 / 2 : ℝ) • u') := by
    simp only [w, map_smul, map_sub, smul_sub, smul_smul]
    ring_nf
  have hwL : w ∈ L := (hmemL w).2 fun i ↦ by
    obtain ⟨k, hk⟩ := hxy i
    exact ⟨k, by rw [hw, Pi.sub_apply, hk]⟩
  have hgauge : gauge K w < g j := by
    have h1 := interior_subset_gauge_lt_one K hu
    have h2 := interior_subset_gauge_lt_one K hu'
    have h3 : gauge K (u - u') ≤ gauge K u + gauge K u' := by
      simpa [sub_eq_add_neg, gauge_neg hKs] using gauge_add_le hK hKabs u (-u')
    simp only [mem_ofPred_eq] at h1 h2
    rw [gauge_smul_of_nonneg (by linarith [hg0 j]), smul_eq_mul]
    nlinarith [hg0 j]
  have := hflag j w (hgap j w hwL hgauge)
  rwa [hw, Pi.sub_apply, sub_eq_zero] at this

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The theorem for the interior of `K`, assuming `0 ∈ interior K` and `0 < g i`. -/
private theorem prod_mul_measure_interior_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : Convex ℝ K)
    (hKs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ interior K) {n : ℕ} (hn : n = finrank ℝ E)
    {a : Fin n → E} (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) {g : Fin n → ℝ}
    (hg0 : ∀ i, 0 < g i) (hg : Monotone g)
    (hgap : ∀ j, ∀ v ∈ L, gauge K v < g j → v ∈ span ℝ (a '' Iio j)) :
    ENNReal.ofReal (∏ i, g i) * μ (interior K) ≤
      2 ^ n * ENNReal.ofReal (ZLattice.covolume L μ) := by
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 h0)
  -- Coordinates `φ` from a basis `b` of `L` adapted to the flag spanned by `a`.
  set e := basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn])
  have he : ⇑e = a := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  obtain ⟨b, hb⟩ := exists_basis_triangular e (by simpa [he] using haL)
  set bR := b.ofZLatticeBasis ℝ L
  set φ := bR.equivFun
  have hmemL : ∀ v, v ∈ L ↔ ∀ i, φ v i ∈ range ((↑) : ℤ → ℝ) := fun v ↦ by
    rw [← b.ofZLatticeBasis_span ℝ L]
    exact bR.mem_span_iff_repr_mem ℤ v
  -- `C`, the image in coordinates of `½ • interior K`, is open and convex.
  have hCopen : IsOpen (φ '' ((1 / 2 : ℝ) • interior K)) :=
    φ.toContinuousLinearEquiv.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))
  have hCc : Convex ℝ (φ '' ((1 / 2 : ℝ) • interior K)) :=
    (hK.interior.smul _).linear_image φ.toLinearMap
  let g' : ℕ → ℝ := fun i ↦ if h : i < n then g ⟨i, h⟩ else 0
  have hflag : ∀ j, ∀ v ∈ span ℝ (a '' Iio j), φ v j = 0 := fun j v hv ↦ by
    have hv' : v ∈ e.flag j.castSucc := by
      simp only [Basis.flag, Fin.castSucc_lt_castSucc_iff]
      exact he ▸ hv
    rw [← bR.flag_eq_of_triangular
      (fun l ↦ by rw [b.ofZLatticeBasis_apply ℝ L l]; exact (hb l).1)] at hv'
    exact bR.mem_flag_iff_repr_eq_zero.1 hv' j le_rfl
  have core := prod_mul_volume_le_one hCopen.measurableSet hCc g'
    (fun i hi ↦ by simp [g', hi, hg0]) (fun i j hij hj ↦ by
      simp only [g', hj, lt_of_le_of_lt hij hj, dite_true]
      exact hg (Fin.mk_le_mk.2 hij)) (fun j hj x hx y hy hxy ↦ by
      simp only [g', hj, dite_true] at hx hy
      exact apply_eq_of_mem_smul_image hK hKs hKabs hg0 hgap φ hmemL hflag _ hx hy hxy)
  have hprod : ∏ i ∈ Finset.range n, g' i = ∏ i, g i := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [g', i.isLt]
  rw [hprod, image_smul_set, Measure.addHaar_smul_of_nonneg _ (by norm_num), finrank_fin_fun,
    ZLattice.volume_image_eq_measure_div_covolume L b μ] at core
  -- `core` reads `(∏ g) * (2⁻ⁿ * (μ (interior K) / covolume L μ)) ≤ 1`.
  have hcov : ENNReal.ofReal (ZLattice.covolume L μ) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L μ)).ne'
  -- Divide the goal by `covolume L μ` and by `2 ^ n`.
  rw [← ENNReal.div_le_iff hcov ENNReal.ofReal_ne_top, ← one_mul ((2 : ENNReal) ^ n),
    ← ENNReal.div_le_iff (by simp) (by simp)]
  convert core using 1
  simp [div_eq_mul_inv, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos]
  ring

/-- **Minkowski's second theorem**, upper bound. Let `L` be a full lattice in an `n`-dimensional
real normed space `E`, `μ` a Haar measure on `E`, and `K ⊆ E` convex and symmetric about `0`. Let
`a 0, …, a (n - 1)` be `ℝ`-linearly independent vectors of `L` and `g 0, …, g (n - 1)`
nonnegative numbers such that every `v ∈ L` with `gauge K v < g j` lies in the span of
`a 0, …, a (j - 1)`. Then `(∏ i, g i) * μ K ≤ 2 ^ n * covolume L μ`.

Independent lattice vectors realizing the successive minima `λ₀ ≤ ⋯ ≤ λₙ₋₁` of `L` with respect to
`K` satisfy the hypothesis with `g = λ`, which gives the classical form
`λ₀ ⋯ λₙ₋₁ · μ K ≤ 2ⁿ · covolume L μ`. -/
theorem prod_mul_measure_le_two_pow_mul_covolume (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] {K : Set E}
    (hK : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K) {n : ℕ} (hn : n = finrank ℝ E) {a : Fin n → E}
    (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) {g : Fin n → ℝ} (hg0 : ∀ i, 0 ≤ g i)
    (hgap : ∀ j, ∀ v ∈ L, gauge K v < g j → v ∈ span ℝ (a '' Iio j)) :
    ENNReal.ofReal (∏ i, g i) * μ K ≤ 2 ^ n * ENNReal.ofReal (ZLattice.covolume L μ) := by
  -- Degenerate cases: some `g i` vanishes, or `K` has empty interior and hence measure zero.
  by_cases hgz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hgz
    simp [Finset.prod_eq_zero (Finset.mem_univ i) hi]
  push Not at hgz
  have hKint : μ (interior K) = μ K := measure_interior_of_null_frontier (hK.addHaar_frontier μ)
  rcases (interior K).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · simp [← hKint, hempty]
  -- Otherwise `K` is a neighbourhood of `0`, being convex and symmetric.
  have hneg : -K = K := Set.ext fun x ↦ ⟨fun hx ↦ by simpa using hKs _ hx,
    fun hx ↦ by simpa using hKs _ hx⟩
  have h0 : (0 : E) ∈ interior K := by
    have hx₀' : -x₀ ∈ interior K := by
      have h := mem_image_of_mem (Homeomorph.neg E) hx₀
      rwa [(Homeomorph.neg E).image_interior, Homeomorph.coe_neg, image_neg_eq_neg, hneg] at h
    simpa using hK.interior hx₀ hx₀' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  -- Replace `g` by its running maximum `G`, which is monotone and still satisfies `hgap`.
  let G : Fin n → ℝ := fun j ↦ (Finset.Iic j).sup' ⟨j, Finset.mem_Iic.2 le_rfl⟩ g
  have hgG : ∀ i, g i ≤ G i := fun i ↦ Finset.le_sup' g (Finset.mem_Iic.2 le_rfl)
  have hG : Monotone G := fun i j hij ↦ Finset.sup'_mono g (Finset.Iic_subset_Iic.2 hij) _
  have hGgap : ∀ j, ∀ v ∈ L, gauge K v < G j → v ∈ span ℝ (a '' Iio j) := fun j v hv hlt ↦ by
    obtain ⟨i, hi, hGi⟩ := Finset.exists_mem_eq_sup' ⟨j, Finset.mem_Iic.2 le_rfl⟩ g
    exact span_mono (image_mono (Iio_subset_Iio (Finset.mem_Iic.1 hi)))
      (hgap i v hv (hGi ▸ hlt))
  rw [← hKint]
  calc ENNReal.ofReal (∏ i, g i) * μ (interior K)
      ≤ ENNReal.ofReal (∏ i, G i) * μ (interior K) := by
        gcongr with i
        exacts [fun i _ ↦ hg0 i, hgG i]
    _ ≤ _ := prod_mul_measure_interior_le L μ hK hKs h0 hn haL ha
      (fun i ↦ ((hg0 i).lt_of_ne' (hgz i)).trans_le (hgG i)) hG hGgap

/-- **Minkowski's second theorem**, upper bound, in terms of the successive minima. For a full
lattice `L` in a real normed space `E` of dimension `n`, a Haar measure `μ` on `E`, and a convex
body `K` symmetric about `0` with `0` in its interior, the successive minima
`λ i = successiveMin L K i` satisfy `λ₀ ⋯ λₙ₋₁ · μ K ≤ 2ⁿ · covolume L μ`. -/
theorem prod_successiveMin_mul_measure_le_two_pow_mul_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {K : ConvexBody E} (hK : 0 ∈ interior (K : Set E)) (hKs : ∀ x ∈ K, -x ∈ K) :
    ENNReal.ofReal (∏ i, successiveMin L K i) * μ K ≤
      2 ^ finrank ℝ E * ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  exact prod_mul_measure_le_two_pow_mul_covolume L μ K.convex hKs rfl (fun i ↦ (haL i).1) ha
    (successiveMin_nonneg L K) fun j v hvL hv ↦ mem_span_image_Iio_of_gauge_lt_successiveMin hK ha
      (fun i ↦ (haL i).1) (fun i ↦ (haL i).2.le) hvL hv

end ZLattice
