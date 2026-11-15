/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Subspace.Slice

import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Basic
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.NumberTheory.Height.Extraction

/-!
# Siegel's lemma and bounded-height bases for subspaces and kernels over number fields

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places, `r₂` complex places, and
discriminant `discr K`, and let `W` be a `K`-subspace of `ι → K` of dimension `k` over a finite
linearly ordered coordinate type `ι`. Inside the `D * k`-dimensional Euclidean Minkowski span
`W.euclideanSpan`, the saturated integral lattice `W.integerLattice` (`W ∩ 𝓞_K^ι`) has covolume
`((2⁻¹) ^ r₂ * √|discr K|) ^ k * W.subspaceHeight ^ D` (`Submodule.covolume_integerLattice`).
Combining Minkowski's second theorem on the symmetric convex-body slices `W.polydiscSlice` and
`W.euclideanBallSlice` (`Submodule.prod_successiveMin_polydiscSlice_le_mul_covolume` and
`Submodule.prod_successiveMin_euclideanBallSlice_le_mul_covolume`) with extraction through the
field tower `K / ℚ` (`TauCeti.exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le` and
`TauCeti.exists_linearIndependent_prod_height2_le`) yields a `K`-basis `x 0, …, x (k - 1)` of `W`
consisting of tuples in `W.integerPoints` whose heights satisfy:

* **Sup-height product bound (Bombieri–Vaaler):**
  ```text
  ∏ j, H(x j) ≤ (2 / π) ^ (r₂ * k / D) * |discr K| ^ (k / (2 * D)) * H₂(W),
  ```
  where `H` is `TauCeti.absoluteProjectiveTupleHeight` and `H₂(W)` is `Submodule.subspaceHeight W`.
* **Euclidean-height product bound (exact ball volumes and inscribed-cube bound):**
  ```text
  ∏ j, H₂(x j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *
                    |discr K| ^ (k / (2 * D)) * H₂(W)
               ≤ (√k) ^ k * |discr K| ^ (k / (2 * D)) * H₂(W),
  ```
  where `H₂` is `TauCeti.height2` and `ω_d` is the real volume of the `d`-dimensional closed unit
  ball.

No freeness of `W ∩ 𝓞_K^ι` over `𝓞 K` is assumed, and the basis statements include the boundary
case `k = 0`. When `W ≠ ⊥`, selecting a basis vector of smallest height gives the one-vector bounds
with exponent `1 / k` on `H₂(W)`.

Specializing `W` to `LinearMap.ker A.mulVecLin` for an arbitrary finite matrix `A : Matrix m ι K`
of rank `R` (without assuming linearly independent rows) and applying Hodge duality of subspace
heights (`Matrix.subspaceHeight_ker_mulVecLin`) produces an integral `K`-basis of `#ι - R` vectors
for `ker A` bounded in terms of the row-space height `(span K (range A.row)).subspaceHeight`.
Bounding the row-space height by the product of the Euclidean heights of the nonzero rows
(`Matrix.subspaceHeight_ker_mulVecLin_le_prod`) yields Evertse and Ferretti's fixed-field Siegel
lemma (`TauCeti.exists_ne_zero_height2_le`): for `#u < #ι` nonzero linear forms `L : u → ι → K`,
there is a nonzero `x : ι → 𝓞 K` in their common kernel with
`H₂(x) ≤ √#ι * |discr K| ^ (1 / (2 * D)) * (∏ i, H₂(L i)) ^ (1 / (#ι - #u))`.

## Main results

In `Submodule`:
* `exists_linearIndependent_integerPoints_comp_finrank_mul`: index-bounded extraction of a `K`-basis
  of `W` in `W.integerPoints` from `[K : ℚ] * finrank K W` `ℝ`-independent integral points.
* `exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le_successiveMin` and
  `exists_linearIndependent_integerPoints_prod_height2_le_successiveMin`: integral `K`-bases of `W`
  bounded by the successive minima of `W.polydiscSlice` and `W.euclideanBallSlice`.
* `exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le`,
  `exists_linearIndependent_integerPoints_prod_height2_le`, and
  `exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow`: integral `K`-bases of `W` of
  bounded sup height and Euclidean height.
* `exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le`,
  `exists_ne_zero_mem_integerPoints_height2_le`, and
  `exists_ne_zero_mem_integerPoints_height2_le_sqrt`: smallest-vector corollaries for `W ≠ ⊥`.

In `Matrix` and `TauCeti`:
* `Matrix.exists_linearIndependent_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le`,
  `Matrix.exists_linearIndependent_ker_mulVecLin_prod_height2_le`, and
  `Matrix.exists_linearIndependent_ker_mulVecLin_prod_height2_le_sqrt_pow`: integral `K`-bases of
  the kernel of an arbitrary `m × ι` matrix over `K`.
* `Matrix.exists_ne_zero_mulVec_eq_zero_absoluteProjectiveTupleHeight_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le`, and
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_sqrt`: nonzero integral solutions when
  `A.rank < #ι`.
* `TauCeti.exists_ne_zero_height2_le`: Evertse–Ferretti's fixed-field Siegel lemma in Euclidean
  height without row-independence assumptions.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32, Theorems 1,
  2, 8, and 9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8, §2.9 (Theorem 2.9.4, Corollary 2.9.7, Proposition 2.9.18), and Appendix C, Theorem C.3.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  Set TauCeti
open scoped BigOperators Matrix Real

/-- From a product bound `∏ i, f i ≤ B` with `0 < k` and `0 < B`, at least one factor is at most
`B ^ (1 / k)`. -/
private theorem exists_le_rpow_inv_of_prod_le {k : ℕ} (hk : 0 < k) {f : Fin k → ℝ}
    {B : ℝ} (hB : 0 < B) (hle : ∏ i, f i ≤ B) : ∃ i, f i ≤ B ^ (k : ℝ)⁻¹ := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_contra! h
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (fun _ _ ↦ Real.rpow_pos_of_pos hB _) (fun i _ ↦ h i) Finset.univ_nonempty
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hB.le hk.ne'] at hprod
  exact hprod.not_ge hle

namespace Submodule

section Extraction

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

open Classical in
/-- Coordinatewise projection from `W.euclideanSpan` to `ι → mixedSpace K`. -/
private def euclideanSpanToMixedPi (W : Submodule K (ι → K)) :
    W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) where
  toFun x i := euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)
  map_add' _ _ := by ext1 i; simp
  map_smul' _ _ := by ext1 i; simp

open Classical in
private theorem injective_euclideanSpanToMixedPi (W : Submodule K (ι → K)) :
    Function.Injective (euclideanSpanToMixedPi W) := by
  intro x y h
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  ext1 i
  exact (euclidean.toMixed K).injective (congrFun h i)

open Classical in
private theorem linearIndependent_mixedEmbedding_of_integerPoints [Finite ι]
    {W : Submodule K (ι → K)} {m : Type*} {u : m → ι → 𝓞 K} (huW : ∀ l, u l ∈ W.integerPoints)
    (hu : LinearIndependent ℝ fun l ↦
      (W.integerPointsEquivIntegerLattice ⟨u l, huW l⟩ : W.euclideanSpan)) :
    LinearIndependent ℝ fun l ↦
      (LinearMap.piMap fun _ : ι ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap)
        fun i ↦ (u l i : K) := by
  have hli := hu.map' (euclideanSpanToMixedPi W)
    (LinearMap.ker_eq_bot.2 (injective_euclideanSpanToMixedPi W))
  convert hli with l
  ext1 i
  simp [euclideanSpanToMixedPi]

private theorem span_eq_of_mem_integerPoints [Finite ι] {W : Submodule K (ι → K)}
    {x : Fin (finrank K W) → ι → 𝓞 K} (hxW : ∀ j, x j ∈ W.integerPoints)
    (hli : LinearIndependent K fun j i ↦ (x j i : K)) :
    span K (range fun j i ↦ (x j i : K)) = W := by
  refine eq_of_le_of_finrank_eq (span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact mem_integerPoints.mp (hxW j)
  · rw [finrank_span_eq_card hli, Fintype.card_fin]

/-- **Basis extraction for integral points of a number-field subspace.** Given
`[K : ℚ] * finrank K W` tuples in `W.integerPoints` whose images in `W.euclideanSpan` are linearly
independent over `ℝ`, one can select `finrank K W` of them—the `j`-th at zero-based index at most
`[K : ℚ] * j`—forming a `K`-basis of `W`. -/
theorem exists_linearIndependent_integerPoints_comp_finrank_mul [Finite ι]
    {W : Submodule K (ι → K)} {u : Fin (finrank ℚ K * finrank K W) → ι → 𝓞 K}
    (huW : ∀ l, u l ∈ W.integerPoints)
    (hu : LinearIndependent ℝ fun l ↦
      (W.integerPointsEquivIntegerLattice ⟨u l, huW l⟩ : W.euclideanSpan)) :
    ∃ s : Fin (finrank K W) → Fin (finrank ℚ K * finrank K W),
      LinearIndependent K (fun j i ↦ (u (s j) i : K)) ∧
      span K (range fun j i ↦ (u (s j) i : K)) = W ∧
      ∀ j, (s j : ℕ) ≤ finrank ℚ K * j := by
  have hli := linearIndependent_mixedEmbedding_of_integerPoints huW hu
  obtain ⟨s, hs_li, hs_le⟩ := TauCeti.exists_linearIndependent_comp_finrank_mul
    (F := ℚ) (E := ℝ) (u := fun l i ↦ (u l i : K)) hli
  exact ⟨s, hs_li, span_eq_of_mem_integerPoints (fun j ↦ huW (s j)) hs_li, hs_le⟩

section SuccessiveMinima

variable [Fintype ι]

open Classical in
/-- **Integral `K`-basis of `W` bounded by the successive minima of the polydisc slice.**
Without any ordering on `ι`, `W` admits a `K`-basis in `W.integerPoints` whose product of absolute
sup heights is at most the `[K : ℚ]`-th root of the product of the successive minima of
`W.integerLattice` with respect to `W.polydiscSlice`. -/
theorem exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le_successiveMin
    (W : Submodule K (ι → K)) :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      (∀ j, x j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = W ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (∏ l, ZLattice.successiveMin W.integerLattice W.polydiscSlice l) ^ (finrank ℚ K : ℝ)⁻¹ := by
  have h0 := W.zero_mem_interior_polydiscSlice
  obtain ⟨a, ha, haL⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin
    W.integerLattice h0
  let e : Fin (finrank ℝ W.euclideanSpan) ≃o Fin (finrank ℚ K * finrank K W) :=
    Fin.castOrderIso W.finrank_euclideanSpan
  let u : Fin (finrank ℚ K * finrank K W) → W.integerPoints :=
    fun l ↦ W.integerPointsEquivIntegerLattice.symm ⟨a (e.symm l), (haL (e.symm l)).1⟩
  let c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice W.polydiscSlice (e.symm l)
  have hu_li : LinearIndependent ℝ fun l ↦
      (W.integerPointsEquivIntegerLattice ⟨(u l : ι → 𝓞 K), (u l).2⟩ : W.euclideanSpan) := by
    have heq : (fun l ↦
        (W.integerPointsEquivIntegerLattice ⟨(u l : ι → 𝓞 K), (u l).2⟩ : W.euclideanSpan)) =
        a ∘ e.symm := by
      ext1 l
      simp [u]
    rw [heq]
    exact ha.comp _ e.symm.injective
  have hc_mono : Monotone c := (ZLattice.monotone_successiveMin W.integerLattice h0).comp
    e.symm.monotone
  have hle (l : Fin (finrank ℚ K * finrank K W)) (i : ι) (w : InfinitePlace K) :
      w ((u l : ι → 𝓞 K) i) ≤ c l := by
    have hg := (W.gauge_polydiscSlice_le_iff
      (ZLattice.successiveMin_nonneg W.integerLattice W.polydiscSlice (e.symm l))).1
      (haL (e.symm l)).2.le i w
    rw [← normAtPlace_apply]
    dsimp only [u, c]
    rw [W.mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply]
    exact hg
  obtain ⟨s, hs_li, -, hs_prod⟩ :=
    TauCeti.exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le
      (u := fun l i ↦ (u l : ι → 𝓞 K) i)
      (linearIndependent_mixedEmbedding_of_integerPoints (fun l ↦ (u l).2) hu_li) hc_mono hle
  have hprod_c : ∏ l, c l = ∏ i, ZLattice.successiveMin W.integerLattice W.polydiscSlice i :=
    e.symm.toEquiv.prod_comp (ZLattice.successiveMin W.integerLattice W.polydiscSlice)
  refine ⟨fun j ↦ u (s j), fun j ↦ (u (s j)).2, hs_li,
    span_eq_of_mem_integerPoints (fun j ↦ (u (s j)).2) hs_li, ?_⟩
  rwa [hprod_c] at hs_prod

open Classical in
/-- **Integral `K`-basis of `W` bounded by the successive minima of the Euclidean-ball slice.**
Without any ordering on `ι`, `W` admits a `K`-basis in `W.integerPoints` whose product of absolute
Euclidean heights is at most the `[K : ℚ]`-th root of the product of the successive minima of
`W.integerLattice` with respect to `W.euclideanBallSlice`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le_successiveMin
    (W : Submodule K (ι → K)) :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      (∀ j, x j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = W ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (∏ l, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice l) ^
          (finrank ℚ K : ℝ)⁻¹ := by
  have h0 := W.zero_mem_interior_euclideanBallSlice
  obtain ⟨a, ha, haL⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin
    W.integerLattice h0
  let e : Fin (finrank ℝ W.euclideanSpan) ≃o Fin (finrank ℚ K * finrank K W) :=
    Fin.castOrderIso W.finrank_euclideanSpan
  let u : Fin (finrank ℚ K * finrank K W) → W.integerPoints :=
    fun l ↦ W.integerPointsEquivIntegerLattice.symm ⟨a (e.symm l), (haL (e.symm l)).1⟩
  let c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice W.euclideanBallSlice (e.symm l)
  have hu_li : LinearIndependent ℝ fun l ↦
      (W.integerPointsEquivIntegerLattice ⟨(u l : ι → 𝓞 K), (u l).2⟩ : W.euclideanSpan) := by
    have heq : (fun l ↦
        (W.integerPointsEquivIntegerLattice ⟨(u l : ι → 𝓞 K), (u l).2⟩ : W.euclideanSpan)) =
        a ∘ e.symm := by
      ext1 l
      simp [u]
    rw [heq]
    exact ha.comp _ e.symm.injective
  have hc_mono : Monotone c := (ZLattice.monotone_successiveMin W.integerLattice h0).comp
    e.symm.monotone
  have hle (l : Fin (finrank ℚ K * finrank K W)) (w : InfinitePlace K) :
      √(∑ i, ‖w.embedding ((u l : ι → 𝓞 K) i)‖ ^ 2) ≤ c l := by
    have hg := (W.gauge_euclideanBallSlice_le_iff
      (ZLattice.successiveMin_nonneg W.integerLattice W.euclideanBallSlice (e.symm l))).1
      (haL (e.symm l)).2.le w
    simp_rw [InfinitePlace.norm_embedding_eq, ← normAtPlace_apply, u,
      W.mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply]
    exact hg
  obtain ⟨s, hs_li, -, hs_prod⟩ :=
    TauCeti.exists_linearIndependent_prod_height2_le
      (u := fun l i ↦ (u l : ι → 𝓞 K) i)
      (linearIndependent_mixedEmbedding_of_integerPoints (fun l ↦ (u l).2) hu_li) hc_mono hle
  have hprod_c : ∏ l, c l = ∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i :=
    e.symm.toEquiv.prod_comp (ZLattice.successiveMin W.integerLattice W.euclideanBallSlice)
  refine ⟨fun j ↦ u (s j), fun j ↦ (u (s j)).2, hs_li,
    span_eq_of_mem_integerPoints (fun j ↦ (u (s j)).2) hs_li, ?_⟩
  rwa [hprod_c] at hs_prod

end SuccessiveMinima

end Extraction

section SubspaceBounds

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- Simplify `((√|(discr K : ℝ)|) ^ k) ^ (finrank ℚ K : ℝ)⁻¹` to
`|(discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))`. -/
private theorem sqrt_abs_discr_pow_rpow_inv (k : ℕ) :
    ((√|(discr K : ℝ)|) ^ k) ^ (finrank ℚ K : ℝ)⁻¹ =
      |(discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ k, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

/-- **Bombieri–Vaaler basis theorem for a number-field subspace (sup height).**
Every `K`-subspace `W` of `ι → K` of dimension `k` admits a `K`-basis `x` in `W.integerPoints`
whose absolute sup heights satisfy
`∏ j, H(x j) ≤ (2 / π) ^ (r₂ * k / D) * |discr K| ^ (k / (2 * D)) * W.subspaceHeight`,
where `D = [K : ℚ]` and `r₂ = nrComplexPlaces K`. -/
theorem exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
    (W : Submodule K (ι → K)) :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      (∀ j, x j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = W ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / π) ^ ((nrComplexPlaces K * finrank K W : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
  classical
  cases nonempty_fintype ι
  set D := finrank ℚ K
  set r₂ := nrComplexPlaces K
  set k := finrank K W
  obtain ⟨x, hxW, hli, hspan, hprod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le_successiveMin
  refine ⟨x, hxW, hli, hspan, hprod.trans ?_⟩
  have hmin :
      ∏ l, ZLattice.successiveMin W.integerLattice W.polydiscSlice l ≤
        (2 / π : ℝ) ^ (r₂ * k) * (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D := by
    refine W.prod_successiveMin_polydiscSlice_le_mul_covolume.trans_eq ?_
    rw [W.covolume_integerLattice, mul_pow, ← pow_mul (2⁻¹ : ℝ) r₂ k, ← mul_assoc,
      ← mul_assoc, ← mul_pow (4 / π : ℝ) 2⁻¹ (r₂ * k)]
    congr 2
    ring
  have hmin_nonneg : 0 ≤ ∏ l, ZLattice.successiveMin W.integerLattice W.polydiscSlice l :=
    Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _
  calc (∏ l, ZLattice.successiveMin W.integerLattice W.polydiscSlice l) ^ (D : ℝ)⁻¹
      ≤ ((2 / π : ℝ) ^ (r₂ * k) * (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) ^ (D : ℝ)⁻¹ :=
        Real.rpow_le_rpow hmin_nonneg hmin (by positivity)
    _ = (2 / π) ^ ((r₂ * k : ℝ) / D) * |(discr K : ℝ)| ^ ((k : ℝ) / (2 * D)) *
          W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg (subspaceHeight_pos W).le _),
          Real.mul_rpow (by positivity) (by positivity),
          Real.pow_rpow_inv_natCast (subspaceHeight_pos W).le finrank_pos.ne',
          sqrt_abs_discr_pow_rpow_inv (K := K) k, ← Real.rpow_natCast (2 / π) (r₂ * k),
          ← Real.rpow_mul (by positivity), Nat.cast_mul, ← div_eq_mul_inv]

/-- **Euclidean-height basis theorem for a number-field subspace (exact unit-ball volumes).**
Every `K`-subspace `W` of `ι → K` of dimension `k` admits a `K`-basis `x` in `W.integerPoints`
whose absolute Euclidean heights satisfy
`∏ j, height2 (x j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *
  |discr K| ^ (k / (2 * D)) * W.subspaceHeight`,
where `ω_d` is the real volume of the `d`-dimensional closed unit ball. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le
    (W : Submodule K (ι → K)) :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      (∀ j, x j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = W ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (((2 : ℝ) ^ finrank K W /
              volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^
            nrRealPlaces K *
          ((2 : ℝ) ^ finrank K W /
              volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
            nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
  classical
  cases nonempty_fintype ι
  set D := finrank ℚ K
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set k := finrank K W
  set ω₁ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)
  set ω₂ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)
  have hω₁ : 0 < ω₁ := TauCeti.volume_real_closedUnitBall_pos
  have hω₂ : 0 < ω₂ := TauCeti.volume_real_closedUnitBall_pos
  obtain ⟨x, hxW, hli, hspan, hprod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le_successiveMin
  refine ⟨x, hxW, hli, hspan, hprod.trans ?_⟩
  have hmin :
      ∏ l, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice l ≤
        (((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂) *
          (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D := by
    refine W.prod_successiveMin_euclideanBallSlice_le_mul_covolume.trans_eq ?_
    have h42 : ((4 : ℝ) ^ k / ω₂) ^ r₂ * ((2⁻¹ : ℝ) ^ r₂) ^ k = ((2 : ℝ) ^ k / ω₂) ^ r₂ := by
      have hswap : ((2⁻¹ : ℝ) ^ r₂) ^ k = ((2⁻¹ : ℝ) ^ k) ^ r₂ := by
        rw [← pow_mul, mul_comm, pow_mul]
      rw [hswap, ← mul_pow, div_mul_eq_mul_div, ← mul_pow]
      norm_num
    rw [W.covolume_integerLattice, mul_pow]
    calc ((2 : ℝ) ^ k / ω₁) ^ r₁ * ((4 : ℝ) ^ k / ω₂) ^ r₂ *
            (((2⁻¹ : ℝ) ^ r₂) ^ k * (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D)
        = ((2 : ℝ) ^ k / ω₁) ^ r₁ * (((4 : ℝ) ^ k / ω₂) ^ r₂ * ((2⁻¹ : ℝ) ^ r₂) ^ k) *
            (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D := by ring
      _ = (((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂) *
            (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D := by rw [h42]
  have hmin_nonneg : 0 ≤ ∏ l, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice l :=
    Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _
  calc (∏ l, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice l) ^ (D : ℝ)⁻¹
      ≤ ((((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂) *
          (√|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) ^ (D : ℝ)⁻¹ :=
        Real.rpow_le_rpow hmin_nonneg hmin (by positivity)
    _ = (((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂) ^ (D : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ ((k : ℝ) / (2 * D)) * W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg (subspaceHeight_pos W).le _),
          Real.mul_rpow (by positivity) (by positivity),
          Real.pow_rpow_inv_natCast (subspaceHeight_pos W).le finrank_pos.ne',
          sqrt_abs_discr_pow_rpow_inv (K := K) k]

/-- **Euclidean-height basis theorem for a number-field subspace (inscribed-cube constant).**
Comparing the closed unit balls in dimensions `k` and `2 * k` with their inscribed cubes simplifies
the ball-volume constant in `Submodule.exists_linearIndependent_integerPoints_prod_height2_le` to
`(√k) ^ k`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
    (W : Submodule K (ι → K)) :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      (∀ j, x j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = W ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (√(finrank K W : ℝ)) ^ finrank K W *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
  set D := finrank ℚ K
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set k := finrank K W
  set ω₁ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)
  set ω₂ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)
  have hω₁ : 0 < ω₁ := TauCeti.volume_real_closedUnitBall_pos
  have hω₂ : 0 < ω₂ := TauCeti.volume_real_closedUnitBall_pos
  obtain ⟨x, hxW, hli, hspan, hprod⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  refine ⟨x, hxW, hli, hspan, hprod.trans ?_⟩
  have hb₁ : (2 : ℝ) ^ k / ω₁ ≤ (√(k : ℝ)) ^ k := by
    simpa [k, ω₁, finrank_euclideanSpace_fin] using
      TauCeti.two_pow_div_volume_real_closedUnitBall_le_sqrt_finrank_pow
        (V := EuclideanSpace ℝ (Fin k))
  have hb₂ : (2 : ℝ) ^ k / ω₂ ≤ ((√(k : ℝ)) ^ k) ^ 2 := by
    have h := TauCeti.two_pow_div_volume_real_closedUnitBall_le_pow_of_finrank_eq_two_mul
      (V := EuclideanSpace ℝ (Fin (2 * k))) (k := k) finrank_euclideanSpace_fin
    refine h.trans_eq ?_
    calc (k : ℝ) ^ k = (√(k : ℝ) ^ 2) ^ k := by rw [Real.sq_sqrt (Nat.cast_nonneg k)]
      _ = ((√(k : ℝ)) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
  have hball_prod :
      ((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂ ≤ ((√(k : ℝ)) ^ k) ^ D := by
    calc ((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂
        ≤ ((√(k : ℝ)) ^ k) ^ r₁ * (((√(k : ℝ)) ^ k) ^ 2) ^ r₂ :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hb₁ r₁)
            (pow_le_pow_left₀ (by positivity) hb₂ r₂) (by positivity) (by positivity)
      _ = ((√(k : ℝ)) ^ k) ^ (r₁ + 2 * r₂) := by
          rw [← pow_mul ((√(k : ℝ)) ^ k) 2 r₂, ← pow_add]
      _ = ((√(k : ℝ)) ^ k) ^ D := by rw [card_add_two_mul_card_eq_rank]
  have hrpow :
      (((2 : ℝ) ^ k / ω₁) ^ r₁ * ((2 : ℝ) ^ k / ω₂) ^ r₂) ^ (D : ℝ)⁻¹ ≤ (√(k : ℝ)) ^ k :=
    (Real.rpow_le_rpow (by positivity) hball_prod (by positivity)).trans_eq
      (Real.pow_rpow_inv_natCast (by positivity) finrank_pos.ne')
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hrpow (by positivity)) (subspaceHeight_pos W).le

/-- **Siegel's lemma for a number-field subspace (sup height).** Any nonzero `K`-subspace `W` of
`ι → K` of dimension `k` contains a nonzero integral point `z ∈ W.integerPoints` with
`H(z) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      absoluteProjectiveTupleHeight (fun i ↦ (z i : K)) ≤
        (2 / π) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  have hkR : (finrank K W : ℝ) ≠ 0 := (Nat.cast_pos.2 hk).ne'
  have hdiscr : 0 < |(discr K : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K))
  have hH : 0 < W.subspaceHeight := subspaceHeight_pos W
  obtain ⟨x, hxW, hli, -, hprod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk (by positivity) hprod
  have hxj : x j ≠ 0 := fun h0 ↦ hli.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.mpr h0)
  refine ⟨x j, hxW j, hxj, hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) hH.le, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul hdiscr.le]
  congr 2
  · congr 1
    field_simp [hkR]
  · congr 1
    field_simp [hkR]

/-- **Siegel's lemma for a number-field subspace (Euclidean height, exact unit-ball volumes).**
Any nonzero `K`-subspace `W` of `ι → K` of dimension `k` contains a nonzero integral point
`z ∈ W.integerPoints` bounded by the `(D * k)`-th root of the ball-volume constant times
`|discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        (((2 : ℝ) ^ finrank K W /
              volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^
            nrRealPlaces K *
          ((2 : ℝ) ^ finrank K W /
              volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
            nrComplexPlaces K) ^ ((finrank ℚ K * finrank K W : ℝ))⁻¹ *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  have hkR : (finrank K W : ℝ) ≠ 0 := (Nat.cast_pos.2 hk).ne'
  have hdiscr : 0 < |(discr K : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K))
  have hH : 0 < W.subspaceHeight := subspaceHeight_pos W
  have hω₁ : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) :=
    TauCeti.volume_real_closedUnitBall_pos
  have hω₂ : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) :=
    TauCeti.volume_real_closedUnitBall_pos
  obtain ⟨x, hxW, hli, -, hprod⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk (by positivity) hprod
  have hxj : x j ≠ 0 := fun h0 ↦ hli.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.mpr h0)
  refine ⟨x j, hxW j, hxj, hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) hH.le, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul hdiscr.le, mul_inv_rev, mul_comm
    (finrank K W : ℝ)⁻¹]
  congr 2
  congr 1
  field_simp [hkR]

/-- **Siegel's lemma for a number-field subspace (Euclidean height, `√k` constant).**
Any nonzero `K`-subspace `W` of `ι → K` of dimension `k` contains a nonzero integral point
`z ∈ W.integerPoints` with
`height2 z ≤ √k * |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_sqrt
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        √(finrank K W : ℝ) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  have hk_pos : 0 < (finrank K W : ℝ) := Nat.cast_pos.2 hk
  have hsqrt : 0 < √(finrank K W : ℝ) := Real.sqrt_pos.2 hk_pos
  have hdiscr : 0 < |(discr K : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K))
  have hH : 0 < W.subspaceHeight := subspaceHeight_pos W
  obtain ⟨x, hxW, hli, -, hprod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk (by positivity) hprod
  have hxj : x j ≠ 0 := fun h0 ↦ hli.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.mpr h0)
  refine ⟨x j, hxW j, hxj, hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) hH.le, Real.mul_rpow (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast hsqrt.le hk.ne', ← Real.rpow_mul hdiscr.le]
  congr 2
  congr 1
  field_simp [hk_pos.ne']

end SubspaceBounds

end Submodule

namespace Matrix

open Submodule

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Finite m] [Fintype ι]
  [LinearOrder ι]

omit [NumberField K] [Finite m] [LinearOrder ι] in
/-- Reindex an integral `K`-basis of `LinearMap.ker A.mulVecLin` along
`finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank`. -/
private theorem reindex_ker_basis (A : Matrix m ι K) {P : (ι → 𝓞 K) → ℝ} {B : ℝ}
    (h : ∃ x : Fin (finrank K (LinearMap.ker A.mulVecLin)) → ι → 𝓞 K,
      (∀ j, x j ∈ (LinearMap.ker A.mulVecLin).integerPoints) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      ∏ j, P (x j) ≤ B) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      ∏ j, P (x j) ≤ B := by
  obtain ⟨x, hxW, hli, hspan, hprod⟩ := h
  let e := finCongr A.finrank_ker_mulVecLin
  have hrange : (range fun j i ↦ (x (e.symm j) i : K)) = range fun j i ↦ (x j i : K) :=
    e.symm.surjective.range_comp (fun j i ↦ (x j i : K))
  refine ⟨fun j ↦ x (e.symm j), fun j ↦ ?_, hli.comp _ e.symm.injective, ?_, ?_⟩
  · simpa [Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using hxW (e.symm j)
  · rw [hrange, hspan]
  · rwa [e.symm.prod_comp fun j ↦ P (x j)]

/-- **Bombieri–Vaaler kernel basis theorem over a number field (sup height).**
For any `m × ι` matrix `A` over `K` of rank `R = A.rank` (without assuming linearly independent
rows or freeness of the integral kernel over `𝓞 K`), `LinearMap.ker A.mulVecLin` admits a
`K`-basis of `k = #ι - R` vectors in `ι → 𝓞 K` satisfying
`∏ j, H(x j) ≤ (2 / π) ^ (r₂ * k / D) * |discr K| ^ (k / (2 * D)) *
  (span K (range A.row)).subspaceHeight`. -/
theorem exists_linearIndependent_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le
    (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / π) ^
            ((nrComplexPlaces K * (Fintype.card ι - A.rank : ℕ) : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
          (span K (range A.row)).subspaceHeight := by
  obtain ⟨x, hAx, hli, hspan, hprod⟩ :=
    reindex_ker_basis A (P := fun v ↦ absoluteProjectiveTupleHeight fun i ↦ (v i : K))
      (LinearMap.ker A.mulVecLin
        ).exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  refine ⟨x, hAx, hli, hspan, ?_⟩
  rw [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] at hprod
  exact hprod

/-- **Kernel basis theorem over a number field (Euclidean height, exact unit-ball volumes).**
For any `m × ι` matrix `A` over `K` of rank `R = A.rank`, `LinearMap.ker A.mulVecLin` admits a
`K`-basis of `k = #ι - R` vectors in `ι → 𝓞 K` whose product of Euclidean heights is bounded in
terms of the `k`- and `2 * k`-dimensional unit-ball volumes and the absolute Euclidean height of
the row space of `A`. -/
theorem exists_linearIndependent_ker_mulVecLin_prod_height2_le (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (((2 : ℝ) ^ (Fintype.card ι - A.rank) /
              volume.real
                (closedBall (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^
            nrRealPlaces K *
          ((2 : ℝ) ^ (Fintype.card ι - A.rank) /
              volume.real
                (closedBall (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
            nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
          (span K (range A.row)).subspaceHeight := by
  obtain ⟨x, hAx, hli, hspan, hprod⟩ :=
    reindex_ker_basis A (P := fun v ↦ height2 fun i ↦ (v i : K))
      (LinearMap.ker A.mulVecLin).exists_linearIndependent_integerPoints_prod_height2_le
  refine ⟨x, hAx, hli, hspan, ?_⟩
  rwa [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] at hprod

/-- **Kernel basis theorem over a number field (Euclidean height, `(√k) ^ k` constant).** -/
theorem exists_linearIndependent_ker_mulVecLin_prod_height2_le_sqrt_pow (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (√((Fintype.card ι - A.rank : ℕ) : ℝ)) ^ (Fintype.card ι - A.rank) *
          |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
          (span K (range A.row)).subspaceHeight := by
  obtain ⟨x, hAx, hli, hspan, hprod⟩ :=
    reindex_ker_basis A (P := fun v ↦ height2 fun i ↦ (v i : K))
      (LinearMap.ker A.mulVecLin).exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
  refine ⟨x, hAx, hli, hspan, ?_⟩
  rwa [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] at hprod

/-- **Bombieri–Vaaler Siegel lemma for a matrix over a number field (sup height).**
If `A.rank < #ι`, then `A *ᵥ x = 0` has a nonzero integral solution `x : ι → 𝓞 K` with
`H(x) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) *
  (span K (range A.row)).subspaceHeight ^ (1 / (#ι - A.rank))`. -/
theorem exists_ne_zero_mulVec_eq_zero_absoluteProjectiveTupleHeight_le
    {A : Matrix m ι K} (hrank : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun i ↦ (x i : K)) = 0 ∧
      absoluteProjectiveTupleHeight (fun i ↦ (x i : K)) ≤
        (2 / π) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  have hker_ne_bot : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro h
    have hdim := A.finrank_ker_mulVecLin
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨x, hxW, hx0, hxle⟩ :=
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le
      hker_ne_bot
  refine ⟨x, hx0, ?_, ?_⟩
  · simpa [Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using hxW
  · simpa only [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin,
      Nat.cast_sub hrank.le] using hxle

/-- **Siegel's lemma for a matrix over a number field (Euclidean height, exact unit-ball
volumes).** -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le
    {A : Matrix m ι K} (hrank : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun i ↦ (x i : K)) = 0 ∧
      height2 (fun i ↦ (x i : K)) ≤
        (((2 : ℝ) ^ (Fintype.card ι - A.rank) /
              volume.real
                (closedBall (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^
            nrRealPlaces K *
          ((2 : ℝ) ^ (Fintype.card ι - A.rank) /
              volume.real
                (closedBall (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
            nrComplexPlaces K) ^ ((finrank ℚ K : ℝ) * ((Fintype.card ι : ℝ) - A.rank))⁻¹ *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  have hker_ne_bot : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro h
    have hdim := A.finrank_ker_mulVecLin
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨x, hxW, hx0, hxle⟩ :=
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_height2_le hker_ne_bot
  refine ⟨x, hx0, ?_, ?_⟩
  · simpa [Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using hxW
  · rw [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] at hxle
    simpa only [Nat.cast_sub hrank.le] using hxle

/-- **Siegel's lemma for a matrix over a number field (Euclidean height, `√(#ι - A.rank)`
constant).** -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le_sqrt
    {A : Matrix m ι K} (hrank : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun i ↦ (x i : K)) = 0 ∧
      height2 (fun i ↦ (x i : K)) ≤
        √((Fintype.card ι : ℝ) - A.rank) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  have hker_ne_bot : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro h
    have hdim := A.finrank_ker_mulVecLin
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨x, hxW, hx0, hxle⟩ :=
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_height2_le_sqrt hker_ne_bot
  refine ⟨x, hx0, ?_, ?_⟩
  · simpa [Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using hxW
  · simpa only [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin,
      Nat.cast_sub hrank.le] using hxle

end Matrix

namespace TauCeti

/-- **Fixed-field Siegel's lemma in Euclidean height** (Evertse–Ferretti, §13, Lemma 13.1).
Let `K` be a number field of degree `D = [K : ℚ]` and let `L : u → ι → K` be `#u < #ι` nonzero
linear forms in `#ι` variables, without assuming linear independence of the forms. Then there is a
nonzero tuple `x : ι → 𝓞 K` satisfying `∑ j, L i j * x j = 0` for all `i` whose absolute Euclidean
height satisfies
`height2 x ≤ √#ι * |discr K| ^ (1 / (2 * D)) * (∏ i, height2 (L i)) ^ (1 / (#ι - #u))`. -/
theorem exists_ne_zero_height2_le {K u ι : Type*} [Field K] [NumberField K] [Fintype u]
    [Fintype ι] (hcard : Fintype.card u < Fintype.card ι) {L : u → ι → K}
    (hL : ∀ i, L i ≠ 0) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ (∀ i, ∑ j, L i j * (x j : K) = 0) ∧
      height2 (fun j ↦ (x j : K)) ≤
        √(Fintype.card ι : ℝ) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (∏ i, height2 (L i)) ^ ((Fintype.card ι : ℝ) - Fintype.card u)⁻¹ := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let A : Matrix u ι K := Matrix.of L
  have hrow : A.row = L := rfl
  have hrank_le : A.rank ≤ Fintype.card u := A.rank_le_card_height
  have hrank_lt : A.rank < Fintype.card ι := hrank_le.trans_lt hcard
  obtain ⟨x, hx0, hAx, hxle⟩ := A.exists_ne_zero_mulVec_eq_zero_height2_le_sqrt hrank_lt
  refine ⟨x, hx0, fun i ↦ ?_, hxle.trans ?_⟩
  · simpa [A, Matrix.mulVec, dotProduct] using congrFun hAx i
  have hsub_pos : 0 < (Fintype.card ι : ℝ) - Fintype.card u :=
    sub_pos.2 (Nat.cast_lt.2 hcard)
  have hH_pos : 0 < (Submodule.span K (range A.row)).subspaceHeight :=
    Submodule.subspaceHeight_pos _
  have hsqrt_le : √((Fintype.card ι : ℝ) - A.rank) ≤ √(Fintype.card ι : ℝ) :=
    Real.sqrt_le_sqrt (sub_le_self _ (Nat.cast_nonneg _))
  have hexp_le :
      ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤ ((Fintype.card ι : ℝ) - Fintype.card u)⁻¹ :=
    inv_anti₀ hsub_pos (sub_le_sub_left (Nat.cast_le.2 hrank_le) _)
  have hH_le : (Submodule.span K (range A.row)).subspaceHeight ≤ ∏ i, height2 (L i) := by
    rw [← A.subspaceHeight_ker_mulVecLin]
    exact A.subspaceHeight_ker_mulVecLin_le_prod (hrow ▸ hL)
  have hrpow_le :
      (Submodule.span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤
        (∏ i, height2 (L i)) ^ ((Fintype.card ι : ℝ) - Fintype.card u)⁻¹ :=
    (Real.rpow_le_rpow_of_exponent_le (Submodule.one_le_subspaceHeight _) hexp_le).trans
      (Real.rpow_le_rpow hH_pos.le hH_le (by positivity))
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hsqrt_le (by positivity))
    hrpow_le (Real.rpow_nonneg hH_pos.le _) (by positivity)

end TauCeti

end
