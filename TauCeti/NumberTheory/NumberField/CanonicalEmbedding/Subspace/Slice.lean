/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Subspace.Lattice

import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.Analysis.Convex.Gauge.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Archimedean place decomposition and convex-body slices of a number-field subspace

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places and `r₂` complex places,
let `ι` be a finite coordinate type, and let `W` be a `K`-subspace of `ι → K` of dimension `k`.
Inside the Euclidean Minkowski space `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`, regrouping
coordinates by infinite place identifies `W.euclideanSpan` linear-isometrically with the `L²`
product of its local place spans:

* at each real place `w`, the `ℝ`-span `W.realPlaceSpan hw ⊆ EuclideanSpace ℝ ι` of `(φ_w ∘ v)`
  for `v ∈ W`, of real dimension `k`;
* at each complex place `w`, the real underlying space of the `ℂ`-span
  `W.complexPlaceSpan hw ⊆ EuclideanSpace ℂ ι` of `(φ_w ∘ v)` for `v ∈ W`, of complex dimension
  `k` and real dimension `2 * k`.

Because the local dimensions add up to `r₁ * k + r₂ * (2 * k) = D * k = finrank ℝ W.euclideanSpan`,
the image of `W.euclideanSpan` fills the entire product of local spans without invoking weak
approximation. Two symmetric convex bodies in `W.euclideanSpan` then factor as products of local
slices across the infinite places:

1. **The polydisc slice** `W.polydiscSlice`, cut out by `normAtPlace w (x i) ≤ 1` for all `i` and
   `w`. By Vaaler's cube-slicing theorem at real places (`≥ 2 ^ k`) and its polydisc counterpart at
   complex places (`≥ π ^ k`), its real volume is at least `2 ^ (r₁ * k) * π ^ (r₂ * k)`.
   Minkowski's second theorem bounds the product of the successive minima of `W.integerLattice` with
   respect to `W.polydiscSlice` by `(4 / π) ^ (r₂ * k) * covolume W.integerLattice`.
2. **The Euclidean-ball slice** `W.euclideanBallSlice`, cut out by
   `√(∑ i, normAtPlace w (x i) ^ 2) ≤ 1` at every infinite place `w`. Its real volume is the exact
   product `ω_k ^ r₁ * ω_{2k} ^ r₂` of unit-ball volumes, and Minkowski's second theorem bounds the
   product of the successive minima of `W.integerLattice` accordingly.

## Main definitions

* `Submodule.realPlaceSpan`, `Submodule.complexPlaceSpan`: the `ℝ`-span in `EuclideanSpace ℝ ι` at a
  real infinite place and the `ℂ`-span in `EuclideanSpace ℂ ι` at a complex infinite place.
* `Submodule.euclideanSpanEquivPlaces`: the linear isometry equivalence identifying
  `W.euclideanSpan` with the `L²` product of `W.realPlaceSpan` and `W.complexPlaceSpan` across all
  infinite places.
* `Submodule.polydiscSlice`: the central slice of the unit cube/polydisc box in `W.euclideanSpan`.
* `Submodule.euclideanBallSlice`: the central slice of the placewise unit Euclidean-ball box in
  `W.euclideanSpan`.

## Main results

* `Submodule.finrank_realPlaceSpan`, `Submodule.finrank_complexPlaceSpan`,
  `Submodule.finrank_real_complexPlaceSpan`: local dimensions `k`, `k`, and `2 * k`.
* `Submodule.two_pow_mul_pi_pow_le_volume_polydiscSlice`,
  `Submodule.two_pow_mul_pi_pow_le_volume_real_polydiscSlice`, and
  `Submodule.prod_successiveMin_polydiscSlice_le_mul_covolume`: volume lower bounds and successive
  minima product bound for `W.polydiscSlice`.
* `Submodule.volume_euclideanBallSlice`, `Submodule.volume_real_euclideanBallSlice`, and
  `Submodule.prod_successiveMin_euclideanBallSlice_le_mul_covolume`: exact volume and successive
  minima product bound for `W.euclideanBallSlice`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32, Theorems 8–9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.9 and Appendix C, Theorem C.3.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  Set
open scoped Pointwise Real

namespace Submodule

/-! ### Local spans at real and complex infinite places -/

section PlaceSpan

variable {K : Type*} [Field K] {ι : Type*}

/-- The `L`-span in `EuclideanSpace L ι` of the coordinatewise `φ`-images of vectors in `W`. -/
private def placeSpan {L : Type*} [RCLike L] (φ : K →+* L) (W : Submodule K (ι → K)) :
    Submodule L (EuclideanSpace L ι) :=
  span L ((fun v : ι → K ↦ WithLp.toLp 2 (φ ∘ v)) '' W)

private theorem finrank_placeSpan [Finite ι] {L : Type*} [RCLike L] (φ : K →+* L)
    (W : Submodule K (ι → K)) :
    finrank L (placeSpan φ W) = finrank K W := by
  classical
  cases nonempty_fintype ι
  let _ : Algebra K L := φ.toAlgebra
  let b : Basis (Fin (finrank K W)) K W := finBasis K W
  let u : Fin (finrank K W) → EuclideanSpace L ι :=
    fun j ↦ WithLp.toLp 2 (algebraMap K L ∘ (b j : ι → K))
  have hli_b : LinearIndependent K (fun j : Fin (finrank K W) ↦ (b j : ι → K)) :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  have hli_pi : LinearIndependent L (fun j ↦ algebraMap K L ∘ (b j : ι → K)) :=
    (linearIndependent_algebraMap_comp_iff (R := K) (S := L)).2 hli_b
  have hli : LinearIndependent L u :=
    hli_pi.map' (WithLp.linearEquiv 2 L (ι → L)).symm.toLinearMap (LinearEquiv.ker _)
  have hspan : span L (range u) = placeSpan φ W := by
    refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
    · rintro _ ⟨j, rfl⟩
      exact subset_span ⟨(b j : ι → K), (b j).2, rfl⟩
    · rintro _ ⟨v, hv, rfl⟩
      have hexp : WithLp.toLp 2 (φ ∘ v) =
          ∑ j : Fin (finrank K W), φ (b.repr ⟨v, hv⟩ j) • u j := by
        ext1 i
        have hvi : v i = ∑ j : Fin (finrank K W), b.repr ⟨v, hv⟩ j * (b j : ι → K) i := by
          have hb := congrArg (fun w : ι → K ↦ w i)
            (congrArg W.subtype (b.sum_repr ⟨v, hv⟩).symm)
          rw [map_sum, Finset.sum_apply] at hb
          simpa only [coe_subtype, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] using hb
        simp only [u, Function.comp_apply, RingHom.algebraMap_toAlgebra, hvi, map_sum, map_mul,
          WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      dsimp only
      rw [hexp]
      exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span (mem_range_self j))
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The `ℝ`-span in `EuclideanSpace ℝ ι` of a `K`-subspace `W ⊆ ι → K` under a real infinite place
`w`. -/
def realPlaceSpan (W : Submodule K (ι → K)) {w : InfinitePlace K} (hw : IsReal w) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  placeSpan (embedding_of_isReal hw) W

/-- Defining equation for `W.realPlaceSpan hw`. -/
theorem realPlaceSpan_def (W : Submodule K (ι → K)) {w : InfinitePlace K} (hw : IsReal w) :
    W.realPlaceSpan hw =
      span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 (embedding_of_isReal hw ∘ v)) '' W) :=
  (rfl)

/-- Every vector of `W` embeds into `W.realPlaceSpan hw` at a real place `w`. -/
theorem toLp_mem_realPlaceSpan {W : Submodule K (ι → K)} {w : InfinitePlace K} (hw : IsReal w)
    {v : ι → K} (hv : v ∈ W) :
    WithLp.toLp 2 (embedding_of_isReal hw ∘ v) ∈ W.realPlaceSpan hw :=
  subset_span ⟨v, hv, rfl⟩

/-- At any real infinite place `w`, `W.realPlaceSpan hw` has real dimension `finrank K W`. -/
@[simp]
theorem finrank_realPlaceSpan [Finite ι] (W : Submodule K (ι → K)) {w : InfinitePlace K}
    (hw : IsReal w) :
    finrank ℝ (W.realPlaceSpan hw) = finrank K W :=
  finrank_placeSpan (embedding_of_isReal hw) W

/-- Borel measurable structure on `W.realPlaceSpan hw`. -/
instance instBorelSpaceRealPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    {w : InfinitePlace K} (hw : IsReal w) : BorelSpace (W.realPlaceSpan hw) :=
  Subtype.borelSpace _

/-- Canonical Euclidean Haar `MeasureSpace` on `W.realPlaceSpan hw`. -/
instance instMeasureSpaceRealPlaceSpan [Fintype ι] (W : Submodule K (ι → K))
    {w : InfinitePlace K} (hw : IsReal w) : MeasureSpace (W.realPlaceSpan hw) :=
  measureSpaceOfInnerProductSpace

/-- The `ℂ`-span in `EuclideanSpace ℂ ι` of a `K`-subspace `W ⊆ ι → K` under a complex infinite
place `w`. -/
def complexPlaceSpan (W : Submodule K (ι → K)) {w : InfinitePlace K} (_hw : IsComplex w) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  placeSpan w.embedding W

/-- Defining equation for `W.complexPlaceSpan hw`. -/
theorem complexPlaceSpan_def (W : Submodule K (ι → K)) {w : InfinitePlace K} (hw : IsComplex w) :
    W.complexPlaceSpan hw = span ℂ ((fun v : ι → K ↦ WithLp.toLp 2 (w.embedding ∘ v)) '' W) :=
  (rfl)

/-- Every vector of `W` embeds into `W.complexPlaceSpan hw` at a complex place `w`. -/
theorem toLp_mem_complexPlaceSpan {W : Submodule K (ι → K)} {w : InfinitePlace K}
    (hw : IsComplex w) {v : ι → K} (hv : v ∈ W) :
    WithLp.toLp 2 (w.embedding ∘ v) ∈ W.complexPlaceSpan hw :=
  subset_span ⟨v, hv, rfl⟩

/-- At any complex infinite place `w`, `W.complexPlaceSpan hw` has complex dimension `finrank K W`.
-/
@[simp]
theorem finrank_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K)) {w : InfinitePlace K}
    (hw : IsComplex w) :
    finrank ℂ (W.complexPlaceSpan hw) = finrank K W :=
  finrank_placeSpan w.embedding W

/-- As a real vector space, `W.complexPlaceSpan hw` has dimension `2 * finrank K W`. -/
@[simp]
theorem finrank_real_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K)) {w : InfinitePlace K}
    (hw : IsComplex w) :
    finrank ℝ ((W.complexPlaceSpan hw).restrictScalars ℝ) = 2 * finrank K W := by
  rw [((Submodule.restrictScalarsEquiv ℝ ℂ _ (W.complexPlaceSpan hw)).restrictScalars ℝ).finrank_eq,
    ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_complexPlaceSpan]

/-- Borel measurable structure on `(W.complexPlaceSpan hw).restrictScalars ℝ`. -/
instance instBorelSpaceComplexPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    {w : InfinitePlace K} (hw : IsComplex w) :
    BorelSpace ((W.complexPlaceSpan hw).restrictScalars ℝ) :=
  Subtype.borelSpace _

/-- Canonical Euclidean Haar `MeasureSpace` on `(W.complexPlaceSpan hw).restrictScalars ℝ`. -/
instance instMeasureSpaceComplexPlaceSpan [Fintype ι] (W : Submodule K (ι → K))
    {w : InfinitePlace K} (hw : IsComplex w) :
    MeasureSpace ((W.complexPlaceSpan hw).restrictScalars ℝ) :=
  measureSpaceOfInnerProductSpace

end PlaceSpan

/-! ### Isometric decomposition across infinite places -/

section Decomposition

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Ambient `L²` product of real-place and complex-place Euclidean coordinate spaces. -/
private abbrev AmbientPlaces (K ι : Type*) [Field K] :=
  WithLp 2
    ((PiLp 2 fun _ : {w : InfinitePlace K // IsReal w} ↦ EuclideanSpace ℝ ι) ×
      (PiLp 2 fun _ : {w : InfinitePlace K // IsComplex w} ↦ EuclideanSpace ℂ ι))

open Classical in
/-- Regrouping coordinates `(i : ι)` and infinite places gives a linear isometry equivalence on the
ambient Euclidean Minkowski space. -/
private def ambientEquivPlaces :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) ≃ₗᵢ[ℝ] AmbientPlaces K ι where
  toFun x :=
    WithLp.toLp 2
      (WithLp.toLp 2 fun w ↦ WithLp.toLp 2 fun i ↦ (euclidean.toMixed K (x i)).1 w,
        WithLp.toLp 2 fun w ↦ WithLp.toLp 2 fun i ↦ (euclidean.toMixed K (x i)).2 w)
  invFun y :=
    WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (fun w ↦ y.fst w i, fun w ↦ y.snd w i)
  left_inv x := by
    ext1 i
    apply (euclidean.toMixed K).injective
    ext w <;> simp
  right_inv y := by
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  norm_map' x := by
    dsimp only
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp_rw [PiLp.norm_sq_eq_of_L2]
    have hcoord (i : ι) :
        ‖x i‖ ^ 2 =
          (∑ w : {w : InfinitePlace K // IsReal w}, ‖(euclidean.toMixed K (x i)).1 w‖ ^ 2) +
            ∑ w : {w : InfinitePlace K // IsComplex w}, ‖(euclidean.toMixed K (x i)).2 w‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      rfl
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_comm

open Classical in
/-- Isometric inclusion of the product of local place spans of `W` into `AmbientPlaces K ι`. -/
private def placesSubtypeVal (W : Submodule K (ι → K)) :
    WithLp 2
        ((PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) ×
          (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
            (W.complexPlaceSpan w.2).restrictScalars ℝ)) →ₗᵢ[ℝ]
      AmbientPlaces K ι where
  toFun p :=
    WithLp.toLp 2
      (WithLp.toLp 2 fun w ↦ (p.fst w : EuclideanSpace ℝ ι),
        WithLp.toLp 2 fun w ↦ (p.snd w : EuclideanSpace ℂ ι))
  map_add' _ _ := by
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  map_smul' _ _ := by
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  norm_map' p := by
    dsimp only
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rfl

open Classical in
private theorem map_euclideanSpan_eq_range_placesSubtypeVal (W : Submodule K (ι → K)) :
    W.euclideanSpan.map (ambientEquivPlaces (K := K) (ι := ι)).toLinearEquiv.toLinearMap =
      LinearMap.range (placesSubtypeVal W).toLinearMap := by
  have hle : W.euclideanSpan.map
      (ambientEquivPlaces (K := K) (ι := ι)).toLinearEquiv.toLinearMap ≤
      LinearMap.range (placesSubtypeVal W).toLinearMap := by
    rw [map_le_iff_le_comap, euclideanSpan_le_iff]
    intro v hv
    refine ⟨WithLp.toLp 2
      (WithLp.toLp 2 fun w ↦ ⟨WithLp.toLp 2 (embedding_of_isReal w.2 ∘ v),
          toLp_mem_realPlaceSpan w.2 hv⟩,
        WithLp.toLp 2 fun w ↦ ⟨WithLp.toLp 2 (w.1.embedding ∘ v),
          toLp_mem_complexPlaceSpan w.2 hv⟩), ?_⟩
    apply WithLp.ofLp_injective 2
    ext1
    · ext1 w; ext1 i; simp [placesSubtypeVal, ambientEquivPlaces]
    · ext1 w; ext1 i; simp [placesSubtypeVal, ambientEquivPlaces]
  have hdim : finrank ℝ
      (W.euclideanSpan.map (ambientEquivPlaces (K := K) (ι := ι)).toLinearEquiv.toLinearMap) =
      finrank ℝ (LinearMap.range (placesSubtypeVal W).toLinearMap) := by
    rw [LinearEquiv.finrank_map_eq, W.finrank_euclideanSpan,
      ← LinearEquiv.finrank_eq (placesSubtypeVal W).equivRange.toLinearEquiv,
      LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _), finrank_prod,
      LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
      LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
      Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [finrank_realPlaceSpan, finrank_real_complexPlaceSpan, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← nrRealPlaces, ← nrComplexPlaces, ← card_add_two_mul_card_eq_rank]
    ring
  exact eq_of_le_of_finrank_eq hle hdim

open Classical in
/-- **Placewise isometric decomposition of `W.euclideanSpan`.** Regrouping coordinates by infinite
place identifies `W.euclideanSpan` linear-isometrically with the `L²` product of `W.realPlaceSpan`
over real places and `W.complexPlaceSpan` over complex places. -/
def euclideanSpanEquivPlaces (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗᵢ[ℝ]
      WithLp 2
        ((PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) ×
          (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
            (W.complexPlaceSpan w.2).restrictScalars ℝ)) :=
  (LinearIsometryEquiv.submoduleMap W.euclideanSpan (ambientEquivPlaces (K := K) (ι := ι))).trans
    ((LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_eq_range_placesSubtypeVal W)).trans
      (placesSubtypeVal W).equivRange.symm)

open Classical in
/-- Real-place coordinates of `W.euclideanSpanEquivPlaces u`. -/
@[simp]
theorem coe_fst_euclideanSpanEquivPlaces_apply (W : Submodule K (ι → K)) (u : W.euclideanSpan)
    (w : {w : InfinitePlace K // IsReal w}) (i : ι) :
    (((W.euclideanSpanEquivPlaces u).fst w : W.realPlaceSpan w.2) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w := by
  set y := W.euclideanSpanEquivPlaces u
  have hy : placesSubtypeVal W y =
      ambientEquivPlaces (K := K) (ι := ι) (u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) := by
    have h := (placesSubtypeVal W).equivRange.apply_symm_apply
      ((LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_eq_range_placesSubtypeVal W))
        (LinearIsometryEquiv.submoduleMap W.euclideanSpan (ambientEquivPlaces (K := K) (ι := ι)) u))
    exact congrArg Subtype.val h
  have h1 := congrArg (fun z : AmbientPlaces K ι ↦ z.fst w i) hy
  simpa [placesSubtypeVal, ambientEquivPlaces, y] using h1

open Classical in
/-- Complex-place coordinates of `W.euclideanSpanEquivPlaces u`. -/
@[simp]
theorem coe_snd_euclideanSpanEquivPlaces_apply (W : Submodule K (ι → K)) (u : W.euclideanSpan)
    (w : {w : InfinitePlace K // IsComplex w}) (i : ι) :
    (((W.euclideanSpanEquivPlaces u).snd w : (W.complexPlaceSpan w.2).restrictScalars ℝ) :
        EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w := by
  set y := W.euclideanSpanEquivPlaces u
  have hy : placesSubtypeVal W y =
      ambientEquivPlaces (K := K) (ι := ι) (u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) := by
    have h := (placesSubtypeVal W).equivRange.apply_symm_apply
      ((LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_eq_range_placesSubtypeVal W))
        (LinearIsometryEquiv.submoduleMap W.euclideanSpan (ambientEquivPlaces (K := K) (ι := ι)) u))
    exact congrArg Subtype.val h
  have h2 := congrArg (fun z : AmbientPlaces K ι ↦ z.snd w i) hy
  simpa [placesSubtypeVal, ambientEquivPlaces, y] using h2

open Classical in
/-- Flattened place map forgetting `WithLp` and `PiLp` wrappers for product-measure computations. -/
private def placesFlat (W : Submodule K (ι → K)) (u : W.euclideanSpan) :
    (∀ w : {w : InfinitePlace K // IsReal w}, W.realPlaceSpan w.2) ×
      (∀ w : {w : InfinitePlace K // IsComplex w}, (W.complexPlaceSpan w.2).restrictScalars ℝ) :=
  ((W.euclideanSpanEquivPlaces u).fst.ofLp, (W.euclideanSpanEquivPlaces u).snd.ofLp)

open Classical in
private theorem measurePreserving_placesFlat (W : Submodule K (ι → K)) :
    MeasurePreserving (placesFlat W) := by
  let _ : BorelSpace (PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) :=
    PiLp.borelSpace 2
  let _ : BorelSpace (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
      (W.complexPlaceSpan w.2).restrictScalars ℝ) :=
    PiLp.borelSpace 2
  let _ : BorelSpace
      (WithLp 2
        ((PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) ×
          (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
            (W.complexPlaceSpan w.2).restrictScalars ℝ))) :=
    WithLp.borelSpace 2 _ _
  let _ : MeasureSpace (PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) :=
    measureSpaceOfInnerProductSpace
  let _ : MeasureSpace (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
      (W.complexPlaceSpan w.2).restrictScalars ℝ) :=
    measureSpaceOfInnerProductSpace
  let _ : MeasureSpace
      (WithLp 2
        ((PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) ×
          (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
            (W.complexPlaceSpan w.2).restrictScalars ℝ))) :=
    measureSpaceOfInnerProductSpace
  have h1 := LinearIsometryEquiv.measurePreserving
    (E := W.euclideanSpan)
    (F := WithLp 2
      ((PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2) ×
        (PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
          (W.complexPlaceSpan w.2).restrictScalars ℝ)))
    W.euclideanSpanEquivPlaces
  have h2 := WithLp.volume_preserving_ofLp
    (U := PiLp 2 fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2)
    (V := PiLp 2 fun w : {w : InfinitePlace K // IsComplex w} ↦
      (W.complexPlaceSpan w.2).restrictScalars ℝ)
  have h3 := (PiLp.volume_preserving_symm_measurableEquiv_toLp
      (fun w : {w : InfinitePlace K // IsReal w} ↦ W.realPlaceSpan w.2)).prod
    (PiLp.volume_preserving_symm_measurableEquiv_toLp
      (fun w : {w : InfinitePlace K // IsComplex w} ↦ (W.complexPlaceSpan w.2).restrictScalars ℝ))
  exact (h3.comp h2).comp h1

/-! ### The polydisc slice -/

omit [Fintype ι] in
/-- Coordinate map `W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K)` for the sup-norm polydisc slice. -/
private def coordsPolydisc (W : Submodule K (ι → K)) :
    W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦ (euclidean.toMixed K).toLinearMap.comp
      ((LinearMap.proj i).comp
        (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap)).comp
    W.euclideanSpan.subtype

omit [Fintype ι] in
@[simp]
private theorem coordsPolydisc_apply (W : Submodule K (ι → K)) (x : W.euclideanSpan) (i : ι) :
    coordsPolydisc W x i =
      euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) :=
  rfl

omit [Fintype ι] in
private theorem coordsPolydisc_injective (W : Submodule K (ι → K)) :
    Function.Injective (coordsPolydisc W) := by
  intro x y h
  ext1; ext1 i
  exact (euclidean.toMixed K).injective (congrFun h i)

open Classical in
private theorem setOf_polydiscSlice_eq_preimage (W : Submodule K (ι → K)) {t : ℝ} (ht : 0 ≤ t) :
    {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ t} =
      coordsPolydisc W ⁻¹' closedBall 0 t := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg ht,
    coordsPolydisc_apply]
  exact forall_congr' fun i ↦
    (Set.ext_iff.mp
      (TauCeti.NumberField.mixedEmbedding.closedBall_zero_eq_setOf_forall_normAtPlace_le
        (K := K) t) _).symm.trans mem_closedBall_zero_iff

open Classical in
/-- **The central cube/polydisc slice of `W.euclideanSpan`.** It consists of the points `x` of
`W.euclideanSpan` whose local valuation `normAtPlace w (x i)` is at most `1` at every coordinate
`i : ι` and infinite place `w`. -/
def polydiscSlice (W : Submodule K (ι → K)) : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
    normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1}
  convex' := by
    rw [setOf_polydiscSlice_eq_preimage W zero_le_one]
    exact (convex_closedBall _ _).linear_preimage (coordsPolydisc W)
  isCompact' := by
    rw [setOf_polydiscSlice_eq_preimage W zero_le_one]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (coordsPolydisc_injective W))).isCompact_preimage
      (isCompact_closedBall _ _)
  nonempty' := ⟨0, by simp⟩

open Classical in
/-- Carrier set of `W.polydiscSlice`. -/
@[simp]
theorem coe_polydiscSlice (W : Submodule K (ι → K)) :
    (W.polydiscSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} :=
  (rfl)

open Classical in
/-- Membership in `W.polydiscSlice`. -/
@[simp]
theorem mem_polydiscSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    x ∈ W.polydiscSlice ↔ ∀ (i : ι) (w : InfinitePlace K),
      normAtPlace w
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1 :=
  Iff.rfl

open Classical in
/-- `W.polydiscSlice` is symmetric about the origin. -/
theorem neg_mem_polydiscSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    -x ∈ W.polydiscSlice ↔ x ∈ W.polydiscSlice := by
  simp only [mem_polydiscSlice, Submodule.coe_neg, WithLp.ofLp_neg, Pi.neg_apply, map_neg,
    normAtPlace_neg]

open Classical in
/-- The origin lies in the interior of `W.polydiscSlice`. -/
theorem zero_mem_interior_polydiscSlice (W : Submodule K (ι → K)) :
    (0 : W.euclideanSpan) ∈ interior (W.polydiscSlice : Set W.euclideanSpan) := by
  rw [coe_polydiscSlice, setOf_polydiscSlice_eq_preimage W zero_le_one]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage (coordsPolydisc W).continuous_of_finiteDimensional).mem_nhds (by simp))
    (preimage_mono ball_subset_closedBall)

open Classical in
/-- The gauge of `W.polydiscSlice` is the sup norm on `ι → mixedSpace K`. -/
theorem gauge_polydiscSlice (W : Submodule K (ι → K)) (x : W.euclideanSpan) :
    gauge (W.polydiscSlice : Set W.euclideanSpan) x =
      ‖fun i : ι ↦ euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)‖ := by
  rw [coe_polydiscSlice, setOf_polydiscSlice_eq_preimage W zero_le_one, LinearMap.gauge_preimage,
    gauge_closedBall zero_le_one, div_one]
  rfl

open Classical in
/-- For `0 ≤ t`, `gauge W.polydiscSlice x ≤ t` holds precisely when every local coordinate has
`normAtPlace w ≤ t`. -/
theorem gauge_polydiscSlice_le_iff {W : Submodule K (ι → K)} {x : W.euclideanSpan} {t : ℝ}
    (ht : 0 ≤ t) :
    gauge (W.polydiscSlice : Set W.euclideanSpan) x ≤ t ↔
      ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ t := by
  rw [gauge_polydiscSlice, ← mem_closedBall_zero_iff]
  exact (Set.ext_iff.mp (setOf_polydiscSlice_eq_preimage W ht) x).symm

open Classical in
/-- For `0 < t`, `t • W.polydiscSlice` consists of the points bounded by `t` at every coordinate
and infinite place. -/
theorem mem_smul_polydiscSlice_iff {W : Submodule K (ι → K)} {t : ℝ} (ht : 0 < t)
    {x : W.euclideanSpan} :
    x ∈ t • (W.polydiscSlice : Set W.euclideanSpan) ↔
      ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ t := by
  rw [← ConvexBody.gauge_le_iff_mem_smul W.zero_mem_interior_polydiscSlice ht,
    gauge_polydiscSlice_le_iff ht.le]

open Classical in
/-- **Volume lower bound for the polydisc slice** (Vaaler's cube/polydisc slicing across infinite
places). For a `K`-subspace `W ⊆ ι → K` of dimension `k`, the slice `W.polydiscSlice` has volume
at least `2 ^ (r₁ * k) * π ^ (r₂ * k)` in `W.euclideanSpan`. -/
theorem two_pow_mul_pi_pow_le_volume_polydiscSlice (W : Submodule K (ι → K)) :
    2 ^ (nrRealPlaces K * finrank K W) *
        ENNReal.ofReal π ^ (nrComplexPlaces K * finrank K W) ≤
      volume (W.polydiscSlice : Set W.euclideanSpan) := by
  let Sr (w : {w : InfinitePlace K // IsReal w}) : Set (W.realPlaceSpan w.2) :=
    {x | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1}
  let Sc (w : {w : InfinitePlace K // IsComplex w}) :
      Set ((W.complexPlaceSpan w.2).restrictScalars ℝ) :=
    {x | ∀ i, ‖(x : EuclideanSpace ℂ ι) i‖ ≤ 1}
  have hSr (w : {w : InfinitePlace K // IsReal w}) : MeasurableSet (Sr w) := by
    have : Sr w = ⋂ i : ι, (fun x : W.realPlaceSpan w.2 ↦ |(x : EuclideanSpace ℝ ι) i|) ⁻¹'
        Iic 1 := by ext; simp [Sr]
    exact this ▸ MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (by fun_prop)
  have hSc (w : {w : InfinitePlace K // IsComplex w}) : MeasurableSet (Sc w) := by
    have : Sc w = ⋂ i : ι, (fun x : (W.complexPlaceSpan w.2).restrictScalars ℝ ↦
        ‖(x : EuclideanSpace ℂ ι) i‖) ⁻¹' Iic 1 := by ext; simp [Sc]
    exact this ▸ MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (by fun_prop)
  have hpre : (W.polydiscSlice : Set W.euclideanSpan) =
      placesFlat W ⁻¹' ((univ.pi Sr) ×ˢ (univ.pi Sc)) := by
    ext u
    rw [coe_polydiscSlice, mem_ofPred_eq, mem_preimage, placesFlat, Set.mem_prod, mem_univ_pi,
      mem_univ_pi]
    refine ⟨fun h ↦ ⟨fun w i ↦ ?_, fun w i ↦ ?_⟩, fun ⟨hr, hc⟩ i w ↦ ?_⟩
    · simpa [Sr, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] using h i w.1
    · simpa [Sc, normAtPlace_apply_of_isComplex w.2] using h i w.1
    · rcases w.isReal_or_isComplex with hw | hw
      · simpa [Sr, normAtPlace_apply_of_isReal hw, Real.norm_eq_abs] using hr ⟨w, hw⟩ i
      · simpa [Sc, normAtPlace_apply_of_isComplex hw] using hc ⟨w, hw⟩ i
  rw [hpre, (measurePreserving_placesFlat W).measure_preimage
    ((MeasurableSet.univ_pi hSr).prod (MeasurableSet.univ_pi hSc)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  have h1 : (2 : ENNReal) ^ (nrRealPlaces K * finrank K W) ≤
      ∏ w : {w : InfinitePlace K // IsReal w}, volume (Sr w) := by
    calc (2 : ENNReal) ^ (nrRealPlaces K * finrank K W)
        = ∏ _w : {w : InfinitePlace K // IsReal w}, (2 : ENNReal) ^ finrank K W := by
          rw [Finset.prod_const, Finset.card_univ, ← nrRealPlaces, pow_mul']
      _ ≤ ∏ w : {w : InfinitePlace K // IsReal w}, volume (Sr w) :=
          Finset.prod_le_prod fun w _ ↦ by
            simpa [Sr] using (W.realPlaceSpan w.2).two_pow_finrank_le_volume_setOf_forall_abs_le_one
  have h2 : ENNReal.ofReal π ^ (nrComplexPlaces K * finrank K W) ≤
      ∏ w : {w : InfinitePlace K // IsComplex w}, volume (Sc w) := by
    calc ENNReal.ofReal π ^ (nrComplexPlaces K * finrank K W)
        = ∏ _w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal π ^ finrank K W := by
          rw [Finset.prod_const, Finset.card_univ, ← nrComplexPlaces, pow_mul']
      _ ≤ ∏ w : {w : InfinitePlace K // IsComplex w}, volume (Sc w) :=
          Finset.prod_le_prod fun w _ ↦ by
            simpa [Sc] using
              (W.complexPlaceSpan w.2).pi_pow_finrank_le_volume_setOf_forall_norm_le_one
  exact mul_le_mul' h1 h2

open Classical in
/-- **Real-valued volume lower bound for `W.polydiscSlice`.** -/
theorem two_pow_mul_pi_pow_le_volume_real_polydiscSlice (W : Submodule K (ι → K)) :
    (2 : ℝ) ^ (nrRealPlaces K * finrank K W) * π ^ (nrComplexPlaces K * finrank K W) ≤
      volume.real (W.polydiscSlice : Set W.euclideanSpan) := by
  have h := ENNReal.toReal_mono W.polydiscSlice.isCompact.measure_lt_top.ne
    W.two_pow_mul_pi_pow_le_volume_polydiscSlice
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal Real.pi_pos.le, ← measureReal_def] at h

open Classical in
/-- **Minkowski's second theorem for the polydisc slice.** The product of the successive minima of
`W.integerLattice` with respect to `W.polydiscSlice` is at most
`(4 / π) ^ (nrComplexPlaces K * finrank K W) * ZLattice.covolume W.integerLattice`. -/
theorem prod_successiveMin_polydiscSlice_le_mul_covolume (W : Submodule K (ι → K)) :
    ∏ j, ZLattice.successiveMin W.integerLattice W.polydiscSlice j ≤
      (4 / π) ^ (nrComplexPlaces K * finrank K W) * ZLattice.covolume W.integerLattice := by
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set k := finrank K W
  have hmink := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
    W.integerLattice volume (K := W.polydiscSlice) (fun _ ↦ neg_mem_polydiscSlice.2)
  have hvol := W.two_pow_mul_pi_pow_le_volume_real_polydiscSlice
  have hprod_nonneg :
      0 ≤ ∏ j, ZLattice.successiveMin W.integerLattice W.polydiscSlice j :=
    Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _
  have h2pow : (2 : ℝ) ^ finrank ℝ W.euclideanSpan =
      (2 : ℝ) ^ (r₁ * k) * (4 : ℝ) ^ (r₂ * k) := by
    rw [W.finrank_euclideanSpan, ← card_add_two_mul_card_eq_rank]
    calc (2 : ℝ) ^ ((r₁ + 2 * r₂) * k)
        = (2 : ℝ) ^ (r₁ * k + 2 * (r₂ * k)) := by ring_nf
      _ = (2 : ℝ) ^ (r₁ * k) * ((2 : ℝ) ^ 2) ^ (r₂ * k) := by
          rw [pow_add, pow_mul (2 : ℝ) 2 (r₂ * k)]
      _ = (2 : ℝ) ^ (r₁ * k) * (4 : ℝ) ^ (r₂ * k) := by norm_num
  have hpos : 0 < (2 : ℝ) ^ (r₁ * k) * π ^ (r₂ * k) := by positivity
  rw [← mul_le_mul_iff_left₀ hpos]
  refine (mul_le_mul_of_nonneg_left hvol hprod_nonneg).trans (hmink.trans_eq ?_)
  rw [h2pow, div_pow]
  field_simp [pow_ne_zero (r₂ * k) Real.pi_ne_zero]

/-! ### The Euclidean-ball slice -/

omit [Fintype ι] in
open Classical in
/-- Placewise Euclidean coordinate map from `W.euclideanSpan` to the sup-normed product of local
Euclidean spaces. -/
private def coordsBall (W : Submodule K (ι → K)) :
    W.euclideanSpan →ₗ[ℝ]
      (({w : InfinitePlace K // IsReal w} → EuclideanSpace ℝ ι) ×
        ({w : InfinitePlace K // IsComplex w} → EuclideanSpace ℂ ι)) where
  toFun u :=
    (fun w ↦ WithLp.toLp 2 fun i ↦
        (euclidean.toMixed K ((u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w,
      fun w ↦ WithLp.toLp 2 fun i ↦
        (euclidean.toMixed K ((u : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w)
  map_add' _ _ := by
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp
  map_smul' _ _ := by
    ext1
    · ext1 w; ext1 i; simp
    · ext1 w; ext1 i; simp

omit [Fintype ι] in
open Classical in
private theorem coordsBall_injective (W : Submodule K (ι → K)) :
    Function.Injective (coordsBall W) := by
  intro x y h
  ext1; ext1 i
  apply (euclidean.toMixed K).injective
  ext w
  · exact congrArg (fun p ↦ (p.1 w : EuclideanSpace ℝ ι) i) h
  · exact congrArg (fun p ↦ (p.2 w : EuclideanSpace ℂ ι) i) h

open Classical in
private theorem setOf_euclideanBallSlice_eq_preimage (W : Submodule K (ι → K)) {t : ℝ}
    (ht : 0 ≤ t) :
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι, normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ t} =
      coordsBall W ⁻¹' closedBall 0 t := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
    pi_norm_le_iff_of_nonneg ht, coordsBall, LinearMap.coe_mk, AddHom.coe_mk, PiLp.norm_eq_of_L2]
  refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun ⟨hr, hc⟩ w ↦ ?_⟩
  · simpa [normAtPlace_apply_of_isReal w.2] using h w.1
  · simpa [normAtPlace_apply_of_isComplex w.2] using h w.1
  · rcases w.isReal_or_isComplex with hw | hw
    · simpa [normAtPlace_apply_of_isReal hw] using hr ⟨w, hw⟩
    · simpa [normAtPlace_apply_of_isComplex hw] using hc ⟨w, hw⟩

open Classical in
/-- **The central placewise Euclidean-ball slice of `W.euclideanSpan`.** It consists of the points
`x` of `W.euclideanSpan` whose local Euclidean norm `√(∑ i, normAtPlace w (x i) ^ 2)` is at most
`1` at every infinite place `w`. -/
def euclideanBallSlice (W : Submodule K (ι → K)) : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ w : InfinitePlace K,
    √(∑ i : ι, normAtPlace w
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1}
  convex' := by
    rw [setOf_euclideanBallSlice_eq_preimage W zero_le_one]
    exact (convex_closedBall _ _).linear_preimage (coordsBall W)
  isCompact' := by
    rw [setOf_euclideanBallSlice_eq_preimage W zero_le_one]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (coordsBall_injective W))).isCompact_preimage
      (isCompact_closedBall _ _)
  nonempty' := ⟨0, by simp⟩

open Classical in
/-- Carrier set of `W.euclideanBallSlice`. -/
@[simp]
theorem coe_euclideanBallSlice (W : Submodule K (ι → K)) :
    (W.euclideanBallSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι, normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1} :=
  (rfl)

open Classical in
/-- Membership in `W.euclideanBallSlice`. -/
@[simp]
theorem mem_euclideanBallSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    x ∈ W.euclideanBallSlice ↔ ∀ w : InfinitePlace K,
      √(∑ i : ι, normAtPlace w
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1 :=
  Iff.rfl

open Classical in
/-- `W.euclideanBallSlice` is symmetric about the origin. -/
theorem neg_mem_euclideanBallSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    -x ∈ W.euclideanBallSlice ↔ x ∈ W.euclideanBallSlice := by
  simp only [mem_euclideanBallSlice, Submodule.coe_neg, WithLp.ofLp_neg, Pi.neg_apply, map_neg,
    normAtPlace_neg]

open Classical in
/-- The origin lies in the interior of `W.euclideanBallSlice`. -/
theorem zero_mem_interior_euclideanBallSlice (W : Submodule K (ι → K)) :
    (0 : W.euclideanSpan) ∈ interior (W.euclideanBallSlice : Set W.euclideanSpan) := by
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage W zero_le_one]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage (coordsBall W).continuous_of_finiteDimensional).mem_nhds (by simp))
    (preimage_mono ball_subset_closedBall)

open Classical in
/-- The gauge of `W.euclideanBallSlice` is bounded by `t ≥ 0` precisely when every infinite-place
Euclidean norm is at most `t`. -/
theorem gauge_euclideanBallSlice_le_iff {W : Submodule K (ι → K)} {x : W.euclideanSpan} {t : ℝ}
    (ht : 0 ≤ t) :
    gauge (W.euclideanBallSlice : Set W.euclideanSpan) x ≤ t ↔
      ∀ w : InfinitePlace K,
        √(∑ i : ι, normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ t := by
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage W zero_le_one,
    LinearMap.gauge_preimage, gauge_closedBall zero_le_one, div_one, ← mem_closedBall_zero_iff]
  exact (Set.ext_iff.mp (setOf_euclideanBallSlice_eq_preimage W ht) x).symm

open Classical in
/-- For `0 < t`, `t • W.euclideanBallSlice` consists of the points whose local Euclidean norm at
every infinite place is at most `t`. -/
theorem mem_smul_euclideanBallSlice_iff {W : Submodule K (ι → K)} {t : ℝ} (ht : 0 < t)
    {x : W.euclideanSpan} :
    x ∈ t • (W.euclideanBallSlice : Set W.euclideanSpan) ↔
      ∀ w : InfinitePlace K,
        √(∑ i : ι, normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ t := by
  rw [← ConvexBody.gauge_le_iff_mem_smul W.zero_mem_interior_euclideanBallSlice ht,
    gauge_euclideanBallSlice_le_iff ht.le]

open Classical in
/-- **Exact real volume of `W.euclideanBallSlice`.** At each real place the slice is the closed unit
ball of a `k`-dimensional real inner product space, and at each complex place that of a
`(2 * k)`-dimensional real inner product space, where `k = finrank K W`. -/
theorem volume_real_euclideanBallSlice (W : Submodule K (ι → K)) :
    volume.real (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^
          nrComplexPlaces K := by
  let Br (w : {w : InfinitePlace K // IsReal w}) : Set (W.realPlaceSpan w.2) := closedBall 0 1
  let Bc (w : {w : InfinitePlace K // IsComplex w}) :
      Set ((W.complexPlaceSpan w.2).restrictScalars ℝ) := closedBall 0 1
  have hpre : (W.euclideanBallSlice : Set W.euclideanSpan) =
      placesFlat W ⁻¹' ((univ.pi Br) ×ˢ (univ.pi Bc)) := by
    ext u
    rw [coe_euclideanBallSlice, mem_ofPred_eq, mem_preimage, placesFlat, Set.mem_prod, mem_univ_pi,
      mem_univ_pi]
    refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun ⟨hr, hc⟩ w ↦ ?_⟩
    · simpa only [Br, mem_closedBall_zero_iff, ← Submodule.norm_coe, PiLp.norm_eq_of_L2,
        coe_fst_euclideanSpanEquivPlaces_apply, normAtPlace_apply_of_isReal w.2] using h w.1
    · simpa only [Bc, mem_closedBall_zero_iff, ← Submodule.norm_coe, PiLp.norm_eq_of_L2,
        coe_snd_euclideanSpanEquivPlaces_apply, normAtPlace_apply_of_isComplex w.2] using h w.1
    · rcases w.isReal_or_isComplex with hw | hw
      · simpa only [Br, mem_closedBall_zero_iff, ← Submodule.norm_coe, PiLp.norm_eq_of_L2,
          coe_fst_euclideanSpanEquivPlaces_apply, normAtPlace_apply_of_isReal hw]
          using hr ⟨w, hw⟩
      · simpa only [Bc, mem_closedBall_zero_iff, ← Submodule.norm_coe, PiLp.norm_eq_of_L2,
          coe_snd_euclideanSpanEquivPlaces_apply, normAtPlace_apply_of_isComplex hw]
          using hc ⟨w, hw⟩
  have hvol : volume (W.euclideanBallSlice : Set W.euclideanSpan) =
      (∏ w : {w : InfinitePlace K // IsReal w}, volume (Br w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, volume (Bc w) := by
    rw [hpre, (measurePreserving_placesFlat W).measure_preimage
      ((MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall).prod
        (MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall)).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  have hr (w : {w : InfinitePlace K // IsReal w}) :
      (volume (Br w)).toReal =
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) := by
    rw [← measureReal_def, TauCeti.volume_real_closedUnitBall, TauCeti.volume_real_closedUnitBall,
      W.finrank_realPlaceSpan w.2, finrank_euclideanSpace_fin]
  have hc (w : {w : InfinitePlace K // IsComplex w}) :
      (volume (Bc w)).toReal =
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) := by
    rw [← measureReal_def, TauCeti.volume_real_closedUnitBall, TauCeti.volume_real_closedUnitBall,
      W.finrank_real_complexPlaceSpan w.2, finrank_euclideanSpace_fin]
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod]
  simp_rw [hr, hc, Finset.prod_const, Finset.card_univ]

open Classical in
/-- **Exact `ENNReal` volume of `W.euclideanBallSlice`.** -/
theorem volume_euclideanBallSlice (W : Submodule K (ι → K)) :
    volume (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^
          nrComplexPlaces K := by
  rw [← ofReal_measureReal W.euclideanBallSlice.isCompact.measure_lt_top.ne,
    W.volume_real_euclideanBallSlice, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow measureReal_nonneg, ENNReal.ofReal_pow measureReal_nonneg,
    ofReal_measureReal measure_closedBall_lt_top.ne,
    ofReal_measureReal measure_closedBall_lt_top.ne]

open Classical in
/-- **Minkowski's second theorem for the Euclidean-ball slice.** The product of the successive
minima of `W.integerLattice` with respect to `W.euclideanBallSlice` is at most
`(2 ^ k / ω_k) ^ r₁ * (4 ^ k / ω_{2k}) ^ r₂ * covolume W.integerLattice`, where `k = finrank K W`
and `ω_d` is the real volume of the `d`-dimensional closed unit ball. -/
theorem prod_successiveMin_euclideanBallSlice_le_mul_covolume (W : Submodule K (ι → K)) :
    ∏ j, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice j ≤
      ((2 : ℝ) ^ finrank K W /
          volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^ nrRealPlaces K *
        ((4 : ℝ) ^ finrank K W /
            volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
          nrComplexPlaces K *
        ZLattice.covolume W.integerLattice := by
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set k := finrank K W
  set ω₁ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)
  set ω₂ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)
  have hω₁ : 0 < ω₁ := TauCeti.volume_real_closedUnitBall_pos
  have hω₂ : 0 < ω₂ := TauCeti.volume_real_closedUnitBall_pos
  have hmink := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
    W.integerLattice volume (K := W.euclideanBallSlice) (fun _ ↦ neg_mem_euclideanBallSlice.2)
  rw [W.volume_real_euclideanBallSlice] at hmink
  have h2pow : (2 : ℝ) ^ finrank ℝ W.euclideanSpan = ((2 : ℝ) ^ k) ^ r₁ * ((4 : ℝ) ^ k) ^ r₂ := by
    rw [W.finrank_euclideanSpan, ← card_add_two_mul_card_eq_rank]
    calc (2 : ℝ) ^ ((r₁ + 2 * r₂) * k)
        = (2 : ℝ) ^ (k * r₁ + 2 * k * r₂) := by ring_nf
      _ = ((2 : ℝ) ^ k) ^ r₁ * (((2 : ℝ) ^ 2) ^ k) ^ r₂ := by
          rw [pow_add, pow_mul (2 : ℝ) k r₁, pow_mul (2 : ℝ) (2 * k) r₂, pow_mul (2 : ℝ) 2 k]
      _ = ((2 : ℝ) ^ k) ^ r₁ * ((4 : ℝ) ^ k) ^ r₂ := by norm_num
  have hpos : 0 < ω₁ ^ r₁ * ω₂ ^ r₂ := by positivity
  rw [← mul_le_mul_iff_left₀ hpos]
  refine hmink.trans_eq ?_
  rw [h2pow, div_pow, div_pow]
  field_simp [pow_ne_zero r₁ hω₁.ne', pow_ne_zero r₂ hω₂.ne']

end Decomposition

end Submodule

end
