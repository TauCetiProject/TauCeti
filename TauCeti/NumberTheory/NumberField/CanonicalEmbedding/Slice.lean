/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Body
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SubspaceLattice

import TauCeti.Analysis.Convex.Gauge.Basic
import TauCeti.LinearAlgebra.Basis.Submodule
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Local archimedean slices in the Euclidean Minkowski span of a subspace

Let `K` be a number field of degree `D = r₁ + 2 r₂` and `ι` a finite coordinate type. A
`K`-subspace `W` of `ι → K` of dimension `k` embeds into the Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`, where its real span
`W.euclideanSpan` has real dimension `D * k` (`Submodule.finrank_euclideanSpan`).

Reordering coordinates by the infinite places of `K` identifies the ambient Minkowski space
isometrically with the `L²` product of `EuclideanSpace ℝ ι` over the real places `w` and
`EuclideanSpace ℂ ι` over the complex places `w`. At each real place `w`, the embedded image of `W`
spans a `k`-dimensional real subspace `W.realPlaceSpan w`; at each complex place `w`, it spans a
`k`-dimensional complex subspace `W.complexPlaceSpan w`, of real dimension `2 * k`. By dimension
counting, `W.euclideanSpan` maps isometrically onto the `L²` product of all these local subspaces.

Two symmetric convex bodies in `W.euclideanSpan` govern the archimedean geometry of numbers on
`W.integerLattice`:

* `W.supSlice`, cut out by `normAtPlace w (toMixed K (x i)) ≤ 1` for every coordinate `i` and
  infinite place `w`. Under the placewise isometry it is the product of central cube slices
  `W_w ∩ [-1, 1]^ι` at the real places (each of volume at least `2 ^ k` by Vaaler's theorem
  `Submodule.two_pow_finrank_le_volume_setOf_forall_abs_le_one`) and central unit-polydisc slices
  at the complex places (each of real volume at least `π ^ k` by
  `Submodule.pi_pow_finrank_le_volume_setOf_forall_norm_le_one`), so its volume in
  `W.euclideanSpan` is at least `2 ^ (k * r₁) * π ^ (k * r₂)`.
* `W.euclideanBallSlice`, cut out by `√(∑ i, normAtPlace w (toMixed K (x i)) ^ 2) ≤ 1` at every
  infinite place `w`. Under the placewise isometry it is the product of the closed unit Euclidean
  balls of `W.realPlaceSpan w` (dimension `k`) and `(W.complexPlaceSpan w).restrictScalars ℝ`
  (dimension `2 * k`), so its real volume is `ω_k ^ r₁ * ω_{2k} ^ r₂`.

## Main definitions

* `Submodule.realPlaceSpan W w`, `Submodule.complexPlaceSpan W w`, `Submodule.placeSpanProd W`:
  the local real and complex subspaces spanned by `W` at an infinite place `w`, and their `L²`
  product across all infinite places.
* `Submodule.euclideanSpanEquivPlaceProd W`, `Submodule.placeCoordsEquiv W`: the linear isometry
  equivalence from `W.euclideanSpan` onto `W.placeSpanProd` and the corresponding Cartesian
  product linear equivalence.
* `Submodule.mixedCoords W`: the `ℝ`-linear coordinate map
  `W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K)`.
* `Submodule.supSlice W`: the central slice in `W.euclideanSpan` of the local unit cubes and
  polydiscs, as a `ConvexBody`.
* `Submodule.euclideanBallSlice W`: the central slice in `W.euclideanSpan` of the local unit
  Euclidean balls, as a `ConvexBody`.

## Main results

* `Submodule.finrank_realPlaceSpan`, `Submodule.finrank_complexPlaceSpan`,
  `Submodule.finrank_real_complexPlaceSpan`: dimensions of the local place subspaces.
* `Submodule.measurePreserving_placeCoordsEquiv` and
  `Submodule.volume_preimage_placeCoordsEquiv_pi_prod`: `W.placeCoordsEquiv` preserves subspace
  Haar measure and factors volumes of placewise product sets.
* `Submodule.mixedCoords_injective` and `Submodule.mixedCoords_eq_piMap_mixedEmbedding`:
  injectivity of `W.mixedCoords` and its compatibility with `mixedEmbedding K` on
  `W.integerLattice`.
* `Submodule.two_pow_mul_pi_pow_le_volume_supSlice` and
  `Submodule.two_pow_mul_pi_pow_le_volume_real_supSlice`: the volume of `W.supSlice` is at least
  `2 ^ (finrank K W * nrRealPlaces K) * π ^ (finrank K W * nrComplexPlaces K)`.
* `Submodule.volume_euclideanBallSlice` and `Submodule.volume_real_euclideanBallSlice`: the volume
  of `W.euclideanBallSlice` is `ω_k ^ nrRealPlaces K * ω_{2k} ^ nrComplexPlaces K`.
* `Submodule.gauge_supSlice`, `Submodule.gauge_euclideanBallSlice`,
  `Submodule.mem_smul_supSlice_iff`, `Submodule.mem_smul_euclideanBallSlice_iff`,
  `Submodule.apply_le_gauge_supSlice_of_mem_integerLattice`, and
  `Submodule.sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice`: gauge and dilation formulas
  for `W.supSlice` and `W.euclideanBallSlice` and the resulting archimedean bounds on integral
  points.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.9 and Appendix C, Theorem C.3.8.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. **83**
  (1979), 543–553.
-/

public section

noncomputable section

open ENNReal MeasureTheory Metric Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set
open scoped Pointwise Real

namespace Submodule

section LocalPlaceSpans

variable {K : Type*} [Field K] {ι : Type*}

/-- The real subspace of `EuclideanSpace ℝ ι` spanned by the embeddings of `W` at a real infinite
place `w`. -/
def realPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsReal}) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) '' W)

/-- Defining formula for `W.realPlaceSpan w`. -/
theorem realPlaceSpan_def (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsReal}) :
    W.realPlaceSpan w =
      span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) '' W) :=
  (rfl)

/-- Every vector of `W` maps into `W.realPlaceSpan w` at a real place `w`. -/
theorem toLp_mem_realPlaceSpan {W : Submodule K (ι → K)} {v : ι → K} (hv : v ∈ W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) ∈ W.realPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- `W.realPlaceSpan w` is contained in a real submodule `U` if and only if the real-place
Euclidean embedding of every vector of `W` belongs to `U`. -/
@[simp]
theorem realPlaceSpan_le_iff {W : Submodule K (ι → K)} {w : {w : InfinitePlace K // w.IsReal}}
    {U : Submodule ℝ (EuclideanSpace ℝ ι)} :
    W.realPlaceSpan w ≤ U ↔
      ∀ v ∈ W, (WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) ∈ U := by
  rw [realPlaceSpan_def, span_le, image_subset_iff]
  rfl

/-- The local real span of the zero subspace is zero. -/
@[simp]
theorem realPlaceSpan_bot (w : {w : InfinitePlace K // w.IsReal}) :
    (⊥ : Submodule K (ι → K)).realPlaceSpan w = ⊥ := by
  rw [realPlaceSpan_def, bot_coe, image_singleton, span_singleton_eq_bot]
  ext1 i
  simp

/-- `Submodule.realPlaceSpan` is monotone in the subspace. -/
@[gcongr]
theorem realPlaceSpan_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂)
    (w : {w : InfinitePlace K // w.IsReal}) :
    W₁.realPlaceSpan w ≤ W₂.realPlaceSpan w :=
  realPlaceSpan_le_iff.2 fun _ hv ↦ toLp_mem_realPlaceSpan (h hv) w

/-- `W.realPlaceSpan w` has real dimension `finrank K W`. -/
@[simp]
theorem finrank_realPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    finrank ℝ (W.realPlaceSpan w) = finrank K W := by
  let e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  have himg :
      ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) ''
          (W : Set (ι → K))) =
        e.toLinearMap ''
          ((fun (v : ι → K) i ↦ embedding_of_isReal w.2 (v i)) '' (W : Set (ι → K))) := by
    simp [e, Set.image_image]
  rw [realPlaceSpan_def, himg, ← Submodule.map_span, e.finrank_map_eq,
    W.finrank_span_image_ringHom (embedding_of_isReal w.2)]

/-- The complex subspace of `EuclideanSpace ℂ ι` spanned by the embeddings of `W` at a complex
infinite place `w`. -/
def complexPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsComplex}) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  span ℂ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) '' W)

/-- Defining formula for `W.complexPlaceSpan w`. -/
theorem complexPlaceSpan_def (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    W.complexPlaceSpan w =
      span ℂ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) '' W) :=
  (rfl)

/-- Every vector of `W` maps into `W.complexPlaceSpan w` at a complex place `w`. -/
theorem toLp_mem_complexPlaceSpan {W : Submodule K (ι → K)} {v : ι → K} (hv : v ∈ W)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) ∈ W.complexPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- `W.complexPlaceSpan w` is contained in a complex submodule `U` if and only if the complex-place
Euclidean embedding of every vector of `W` belongs to `U`. -/
@[simp]
theorem complexPlaceSpan_le_iff {W : Submodule K (ι → K)}
    {w : {w : InfinitePlace K // w.IsComplex}} {U : Submodule ℂ (EuclideanSpace ℂ ι)} :
    W.complexPlaceSpan w ≤ U ↔
      ∀ v ∈ W, (WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) ∈ U := by
  rw [complexPlaceSpan_def, span_le, image_subset_iff]
  rfl

/-- The local complex span of the zero subspace is zero. -/
@[simp]
theorem complexPlaceSpan_bot (w : {w : InfinitePlace K // w.IsComplex}) :
    (⊥ : Submodule K (ι → K)).complexPlaceSpan w = ⊥ := by
  rw [complexPlaceSpan_def, bot_coe, image_singleton, span_singleton_eq_bot]
  ext1 i
  simp

/-- `Submodule.complexPlaceSpan` is monotone in the subspace. -/
@[gcongr]
theorem complexPlaceSpan_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    W₁.complexPlaceSpan w ≤ W₂.complexPlaceSpan w :=
  complexPlaceSpan_le_iff.2 fun _ hv ↦ toLp_mem_complexPlaceSpan (h hv) w

/-- `W.complexPlaceSpan w` has complex dimension `finrank K W`. -/
@[simp]
theorem finrank_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℂ (W.complexPlaceSpan w) = finrank K W := by
  let e : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  have himg :
      ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) '' (W : Set (ι → K))) =
        e.toLinearMap '' ((fun (v : ι → K) i ↦ w.1.embedding (v i)) '' (W : Set (ι → K))) := by
    simp [e, Set.image_image]
  rw [complexPlaceSpan_def, himg, ← Submodule.map_span, e.finrank_map_eq,
    W.finrank_span_image_ringHom w.1.embedding]

/-- Viewed as a real subspace of `EuclideanSpace ℂ ι`, `W.complexPlaceSpan w` has real dimension
`2 * finrank K W`. -/
@[simp]
theorem finrank_real_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℝ ((W.complexPlaceSpan w).restrictScalars ℝ) = 2 * finrank K W := by
  rw [(((W.complexPlaceSpan w).restrictScalarsEquiv ℝ ℂ _).restrictScalars ℝ).finrank_eq,
    ← Module.finrank_mul_finrank ℝ ℂ (W.complexPlaceSpan w),
    Complex.finrank_real_complex, finrank_complexPlaceSpan]

end LocalPlaceSpans

section PlaceIsometry

variable {K : Type*} [Field K] {ι : Type*}

/-- `L²` product of the local subspaces `W.realPlaceSpan w` and
`(W.complexPlaceSpan w).restrictScalars ℝ` across all infinite places of `K`. -/
abbrev placeSpanProd (W : Submodule K (ι → K)) : Type _ :=
  WithLp 2
    ((PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) ×
     (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
       (W.complexPlaceSpan w).restrictScalars ℝ))

instance instSecondCountableRealPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    SecondCountableTopology (W.realPlaceSpan w) :=
  TopologicalSpace.secondCountableTopology_induced
    (W.realPlaceSpan w) (EuclideanSpace ℝ ι) Subtype.val

instance instSecondCountableComplexPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    SecondCountableTopology ((W.complexPlaceSpan w).restrictScalars ℝ) :=
  TopologicalSpace.secondCountableTopology_induced
    ((W.complexPlaceSpan w).restrictScalars ℝ) (EuclideanSpace ℂ ι) Subtype.val

variable [NumberField K]

open Classical in
instance instBorelSpaceRealPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) :=
  PiLp.borelSpace 2

open Classical in
instance instBorelSpaceComplexPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace
      (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
        (W.complexPlaceSpan w).restrictScalars ℝ) :=
  PiLp.borelSpace 2

open Classical in
instance instSecondCountableRealPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    SecondCountableTopology
      (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) :=
  inferInstance

open Classical in
instance instBorelSpacePlaceSpanProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace W.placeSpanProd :=
  WithLp.borelSpace 2 _ _

variable [Fintype ι]

open scoped Classical in
/-- Ambient `L²` product of real-place and complex-place Euclidean coordinate spaces. -/
private abbrev placeAmbientProd (K : Type*) [Field K] (ι : Type*) : Type _ :=
  WithLp 2
    ((PiLp 2 fun _ : {w : InfinitePlace K // w.IsReal} ↦ EuclideanSpace ℝ ι) ×
     (PiLp 2 fun _ : {w : InfinitePlace K // w.IsComplex} ↦ EuclideanSpace ℂ ι))

open scoped Classical in
/-- Ambient linear equivalence reordering coordinatewise `euclidean.mixedSpace K` into the `L²`
product of `EuclideanSpace ℝ ι` over real places and `EuclideanSpace ℂ ι` over complex places. -/
private def ambientPlaceLinearEquiv :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) ≃ₗ[ℝ] placeAmbientProd K ι where
  toFun x := WithLp.toLp 2
    (WithLp.toLp 2 fun w ↦ WithLp.toLp 2 fun i ↦ (euclidean.toMixed K (x i)).1 w,
     WithLp.toLp 2 fun w ↦ WithLp.toLp 2 fun i ↦ (euclidean.toMixed K (x i)).2 w)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 i <;> simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 i <;> simp
  invFun y := WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm
    (fun w ↦ ((WithLp.ofLp y).1 w : EuclideanSpace ℝ ι) i,
     fun w ↦ ((WithLp.ofLp y).2 w : EuclideanSpace ℂ ι) i)
  left_inv x := by
    ext1 i
    apply (euclidean.toMixed K).injective
    ext w <;> simp
  right_inv y := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 i <;> simp

open scoped Classical in
/-- `ambientPlaceLinearEquiv` preserves Euclidean norms, hence is a linear isometry equivalence. -/
private def ambientPlaceIsometryEquiv :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) ≃ₗᵢ[ℝ] placeAmbientProd K ι :=
  { ambientPlaceLinearEquiv with
    norm_map' x := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
        PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      have hcoord (i : ι) :
          ‖x i‖ ^ 2 =
            (∑ w : {w : InfinitePlace K // w.IsReal},
              ‖(euclidean.toMixed K (x i)).1 w‖ ^ 2) +
            ∑ w : {w : InfinitePlace K // w.IsComplex},
              ‖(euclidean.toMixed K (x i)).2 w‖ ^ 2 := by
        rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        simp [euclidean.toMixed]
      simp_rw [hcoord, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        simp [ambientPlaceLinearEquiv, PiLp.norm_sq_eq_of_L2]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        simp [ambientPlaceLinearEquiv, PiLp.norm_sq_eq_of_L2] }

open scoped Classical in
/-- The `L²` product of the local place subspaces of `W` as a submodule of
`placeAmbientProd K ι`. -/
private def placeProductSubmodule (W : Submodule K (ι → K)) :
    Submodule ℝ (placeAmbientProd K ι) :=
  (((Submodule.pi univ fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w).comap
      (WithLp.linearEquiv 2 ℝ
        (∀ _ : {w : InfinitePlace K // w.IsReal}, EuclideanSpace ℝ ι)).toLinearMap).prod
    ((Submodule.pi univ fun w : {w : InfinitePlace K // w.IsComplex} ↦
        (W.complexPlaceSpan w).restrictScalars ℝ).comap
      (WithLp.linearEquiv 2 ℝ
        (∀ _ : {w : InfinitePlace K // w.IsComplex}, EuclideanSpace ℂ ι)).toLinearMap)).comap
    (WithLp.linearEquiv 2 ℝ _).toLinearMap

open scoped Classical in
/-- Linear equivalence between `placeProductSubmodule W` and `W.placeSpanProd`. -/
private def placeProductLinearEquiv (W : Submodule K (ι → K)) :
    placeProductSubmodule W ≃ₗ[ℝ] W.placeSpanProd where
  toFun y := WithLp.toLp 2
    (WithLp.toLp 2 fun w ↦
      ⟨(WithLp.ofLp (y : placeAmbientProd K ι)).1 w, y.2.1 w (mem_univ w)⟩,
     WithLp.toLp 2 fun w ↦
      ⟨(WithLp.ofLp (y : placeAmbientProd K ι)).2 w, y.2.2 w (mem_univ w)⟩)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 <;> ext1 i <;> simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 <;> ext1 i <;> simp
  invFun z :=
    ⟨WithLp.toLp 2
      (WithLp.toLp 2 fun w ↦ ((WithLp.ofLp z).1 w : EuclideanSpace ℝ ι),
       WithLp.toLp 2 fun w ↦ ((WithLp.ofLp z).2 w : EuclideanSpace ℂ ι)),
     ⟨fun w _ ↦ ((WithLp.ofLp z).1 w).2, fun w _ ↦ ((WithLp.ofLp z).2 w).2⟩⟩
  left_inv y := by
    ext1
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 i <;> simp
  right_inv z := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_ <;> ext1 w <;> ext1 <;> ext1 i <;> simp

open scoped Classical in
/-- `placeProductSubmodule W` is isometrically equivalent to `W.placeSpanProd`. -/
private def placeProductEquivProd (W : Submodule K (ι → K)) :
    placeProductSubmodule W ≃ₗᵢ[ℝ] W.placeSpanProd :=
  { placeProductLinearEquiv W with
    norm_map' y := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [← Submodule.norm_coe y, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
        PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
        PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      simp [placeProductLinearEquiv] }

open scoped Classical in
/-- `ambientPlaceIsometryEquiv` maps `W.euclideanSpan` onto `placeProductSubmodule W`. -/
private theorem map_euclideanSpan_eq_placeProductSubmodule (W : Submodule K (ι → K)) :
    W.euclideanSpan.map
        (ambientPlaceIsometryEquiv (K := K) (ι := ι) :
          (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] placeAmbientProd K ι) =
      placeProductSubmodule W := by
  have hle :
      W.euclideanSpan.map
          (ambientPlaceIsometryEquiv (K := K) (ι := ι) :
            (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] placeAmbientProd K ι) ≤
        placeProductSubmodule W := by
    rw [map_le_iff_le_comap, euclideanSpan_le_iff]
    intro v hv
    refine ⟨fun w _ ↦ ?_, fun w _ ↦ ?_⟩
    · simpa [ambientPlaceIsometryEquiv, ambientPlaceLinearEquiv] using
        toLp_mem_realPlaceSpan hv w
    · simpa [ambientPlaceIsometryEquiv, ambientPlaceLinearEquiv] using
        toLp_mem_complexPlaceSpan hv w
  have hdim :
      finrank ℝ (W.euclideanSpan.map ambientPlaceIsometryEquiv.toLinearEquiv.toLinearMap) =
        finrank ℝ (placeProductSubmodule W) := by
    have hr : Fintype.card {w : InfinitePlace K // w.IsReal} = nrRealPlaces K :=
      Fintype.card_congr (Equiv.refl _)
    have hc : Fintype.card {w : InfinitePlace K // w.IsComplex} = nrComplexPlaces K :=
      Fintype.card_congr (Equiv.refl _)
    rw [LinearEquiv.finrank_map_eq, W.finrank_euclideanSpan,
      (placeProductEquivProd W).toLinearEquiv.finrank_eq,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ
        (∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w)).finrank_eq,
      (WithLp.linearEquiv 2 ℝ
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          (W.complexPlaceSpan w).restrictScalars ℝ)).finrank_eq,
      Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [finrank_realPlaceSpan, finrank_real_complexPlaceSpan,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, hr, hc]
    rw [← card_add_two_mul_card_eq_rank]
    ring
  exact eq_of_le_of_finrank_eq hle hdim

open scoped Classical in
/-- Canonical linear isometry equivalence between `W.euclideanSpan` and `W.placeSpanProd`. -/
def euclideanSpanEquivPlaceProd (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗᵢ[ℝ] W.placeSpanProd :=
  ((LinearIsometryEquiv.submoduleMap W.euclideanSpan ambientPlaceIsometryEquiv).trans
    (LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_eq_placeProductSubmodule W))).trans
    (placeProductEquivProd W)

open scoped Classical in
/-- Evaluation of the real-place component of `W.euclideanSpanEquivPlaceProd x` at `(w, i)`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceProd_fst (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((W.euclideanSpanEquivPlaceProd x).fst w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w := by
  simp [euclideanSpanEquivPlaceProd, placeProductEquivProd, placeProductLinearEquiv]
  simp [ambientPlaceIsometryEquiv, ambientPlaceLinearEquiv]

open scoped Classical in
/-- Evaluation of the complex-place component of `W.euclideanSpanEquivPlaceProd x` at `(w, i)`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceProd_snd (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((W.euclideanSpanEquivPlaceProd x).snd w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w := by
  simp [euclideanSpanEquivPlaceProd, placeProductEquivProd, placeProductLinearEquiv]
  simp [ambientPlaceIsometryEquiv, ambientPlaceLinearEquiv]

open scoped Classical in
/-- Linear equivalence from `W.euclideanSpan` to the Cartesian product of the real-place and
complex-place local Euclidean subspaces. -/
def placeCoordsEquiv (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗ[ℝ]
      (∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w) ×
      (∀ w : {w : InfinitePlace K // w.IsComplex},
        (W.complexPlaceSpan w).restrictScalars ℝ) :=
  (W.euclideanSpanEquivPlaceProd.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ _)).trans
    ((WithLp.linearEquiv 2 ℝ _).prodCongr (WithLp.linearEquiv 2 ℝ _))

open scoped Classical in
/-- Evaluation of the real-place component of `W.placeCoordsEquiv x` at `(w, i)`. -/
@[simp]
theorem coe_placeCoordsEquiv_fst (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((W.placeCoordsEquiv x).1 w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w := by
  simp [placeCoordsEquiv]

open scoped Classical in
/-- Evaluation of the complex-place component of `W.placeCoordsEquiv x` at `(w, i)`. -/
@[simp]
theorem coe_placeCoordsEquiv_snd (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((W.placeCoordsEquiv x).2 w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w := by
  simp [placeCoordsEquiv]

open scoped Classical in
/-- Euclidean norm of the real-place component `(W.placeCoordsEquiv x).1 w`. -/
theorem norm_placeCoordsEquiv_fst (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ‖(W.placeCoordsEquiv x).1 w‖ =
      √(∑ i : ι,
        normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
  rw [← Submodule.norm_coe, ← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_placeCoordsEquiv_fst, normAtPlace_apply_of_isReal w.2]

open scoped Classical in
/-- Euclidean norm of the complex-place component `(W.placeCoordsEquiv x).2 w`. -/
theorem norm_placeCoordsEquiv_snd (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ‖(W.placeCoordsEquiv x).2 w‖ =
      √(∑ i : ι,
        normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
  rw [← Submodule.norm_coe, ← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_placeCoordsEquiv_snd, normAtPlace_apply_of_isComplex w.2]

open Classical in
instance instMeasureSpacePlaceSpanProd (W : Submodule K (ι → K)) :
    MeasureSpace W.placeSpanProd :=
  measureSpaceOfInnerProductSpace

open Classical in
/-- `W.placeCoordsEquiv` is measure-preserving between the subspace volume on `W.euclideanSpan`
and the product of the subspace volumes on `W.realPlaceSpan w` and `W.complexPlaceSpan w`. -/
theorem measurePreserving_placeCoordsEquiv (W : Submodule K (ι → K)) :
    MeasurePreserving W.placeCoordsEquiv volume volume := by
  have hmp₁ := LinearIsometryEquiv.measurePreserving
    (E := W.euclideanSpan) (F := W.placeSpanProd) W.euclideanSpanEquivPlaceProd
  have hmp :=
    ((PiLp.volume_preserving_symm_measurableEquiv_toLp
        fun w : {w : InfinitePlace K // w.IsReal} ↦ ↥(W.realPlaceSpan w)).prod
      (PiLp.volume_preserving_symm_measurableEquiv_toLp
        fun w : {w : InfinitePlace K // w.IsComplex} ↦
          ↥((W.complexPlaceSpan w).restrictScalars ℝ))).comp
      ((WithLp.volume_preserving_ofLp _ _).comp hmp₁)
  convert hmp using 1
  ext x <;> simp [placeCoordsEquiv]

open Classical in
/-- Volume of a product of local measurable sets across the real and complex places pulled back
along `W.placeCoordsEquiv`. -/
theorem volume_preimage_placeCoordsEquiv_pi_prod (W : Submodule K (ι → K))
    {Sr : ∀ w : {w : InfinitePlace K // w.IsReal}, Set (W.realPlaceSpan w)}
    {Sc : ∀ w : {w : InfinitePlace K // w.IsComplex},
      Set ((W.complexPlaceSpan w).restrictScalars ℝ)}
    (hSr : ∀ w, MeasurableSet (Sr w)) (hSc : ∀ w, MeasurableSet (Sc w)) :
    volume (W.placeCoordsEquiv ⁻¹' ((univ.pi Sr) ×ˢ (univ.pi Sc))) =
      (∏ w, volume (Sr w)) * ∏ w, volume (Sc w) := by
  rw [(measurePreserving_placeCoordsEquiv W).measure_preimage
      ((MeasurableSet.univ_pi hSr).prod (MeasurableSet.univ_pi hSc)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi]

end PlaceIsometry

section SupSlice

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} (W : Submodule K (ι → K))

/-- Coordinate map from `W.euclideanSpan` to the sup-normed product `ι → mixedSpace K`. -/
def mixedCoords : W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦
    (euclidean.toMixed K).toLinearMap.comp
      ((LinearMap.proj i).comp
        (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap)).comp
    W.euclideanSpan.subtype

/-- Evaluation of `W.mixedCoords` at a coordinate `i : ι`. -/
@[simp]
theorem mixedCoords_apply (x : W.euclideanSpan) (i : ι) :
    W.mixedCoords x i =
      euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) := by
  simp [mixedCoords]

/-- `W.mixedCoords` is injective. -/
theorem mixedCoords_injective : Function.Injective W.mixedCoords := by
  intro x y h
  ext1
  ext1 i
  exact (euclidean.toMixed K).injective (congrFun h i)

/-- On `W.integerLattice`, `W.mixedCoords` agrees coordinatewise with `mixedEmbedding K` applied to
the corresponding integral point of `W`. -/
theorem mixedCoords_eq_piMap_mixedEmbedding [Finite ι] {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) :
    W.mixedCoords a =
      (LinearMap.piMap fun _ : ι ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap) fun i ↦
        (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ :
          W.integerPoints) : ι → 𝓞 K) i : K) := by
  ext1 i
  rw [mixedCoords_apply]
  exact (mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply W ⟨a, ha⟩ i).symm

variable [Fintype ι]

open scoped Classical in
private theorem setOf_supSlice_eq_preimage :
    {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} =
      W.mixedCoords ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg zero_le_one]
  refine forall_congr' fun i ↦ ?_
  rw [← mem_closedBall_zero_iff,
    TauCeti.NumberField.mixedEmbedding.closedBall_zero_eq_setOf_forall_normAtPlace_le,
    mem_ofPred_eq, mixedCoords_apply]

open Classical in
/-- The central slice in `W.euclideanSpan` of the product of local unit cubes `[-1, 1]^ι` at real
places and unit polydiscs at complex places, as a `ConvexBody`. -/
def supSlice : ConvexBody W.euclideanSpan :=
  ConvexBody.ofEqPreimageClosedBall
    {x | ∀ (i : ι) (w : InfinitePlace K),
      normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1}
    W.mixedCoords_injective (setOf_supSlice_eq_preimage W)

variable {W}

/-- Carrier of `W.supSlice`. -/
@[simp]
theorem coe_supSlice :
    (W.supSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} := by
  classical
  exact ConvexBody.coe_ofEqPreimageClosedBall _ _ _

/-- Membership in `W.supSlice`. -/
@[simp]
theorem mem_supSlice {x : W.euclideanSpan} :
    x ∈ W.supSlice ↔
      ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1 := by
  rw [← SetLike.mem_coe, coe_supSlice, mem_ofPred_eq]

/-- `W.supSlice` is symmetric about the origin. -/
theorem neg_mem_supSlice {x : W.euclideanSpan} : -x ∈ W.supSlice ↔ x ∈ W.supSlice := by
  classical
  exact ConvexBody.neg_mem_of_coe_eq_preimage_closedBall
    (coe_supSlice.trans (setOf_supSlice_eq_preimage W))

variable (W) in
/-- The origin lies in the interior of `W.supSlice`. -/
theorem zero_mem_interior_supSlice : (0 : W.euclideanSpan) ∈ interior (W.supSlice : Set _) := by
  classical
  exact ConvexBody.zero_mem_interior_of_coe_eq_preimage_closedBall
    (coe_supSlice.trans (setOf_supSlice_eq_preimage W))

open scoped Classical in
/-- The gauge of `W.supSlice` is the sup norm of `W.mixedCoords x` in `ι → mixedSpace K`, i.e., the
maximum of `normAtPlace w (toMixed K (x i))` over all coordinates `i` and infinite places `w`. -/
theorem gauge_supSlice (x : W.euclideanSpan) :
    gauge (W.supSlice : Set W.euclideanSpan) x = ‖W.mixedCoords x‖ :=
  ConvexBody.gauge_of_coe_eq_preimage_closedBall
    (coe_supSlice.trans (setOf_supSlice_eq_preimage W)) x

/-- For `0 ≤ t`, the dilate `t • W.supSlice` consists of the points `x ∈ W.euclideanSpan` with
`normAtPlace w (toMixed K (x i)) ≤ t` at every coordinate `i` and infinite place `w`. -/
theorem mem_smul_supSlice_iff {t : ℝ} (ht : 0 ≤ t) {x : W.euclideanSpan} :
    x ∈ t • (W.supSlice : Set W.euclideanSpan) ↔
      ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ t := by
  classical
  rw [ConvexBody.mem_smul_iff_norm_le_of_coe_eq_preimage_closedBall
      (coe_supSlice.trans (setOf_supSlice_eq_preimage W)) W.mixedCoords_injective ht,
    pi_norm_le_iff_of_nonneg ht]
  refine forall_congr' fun i ↦ ?_
  rw [← mem_closedBall_zero_iff,
    TauCeti.NumberField.mixedEmbedding.closedBall_zero_eq_setOf_forall_normAtPlace_le,
    mem_ofPred_eq, mixedCoords_apply]

/-- At every coordinate `i` and infinite place `w`, the archimedean absolute value of the integral
point corresponding to `a ∈ W.integerLattice` is bounded by `gauge W.supSlice a`. -/
theorem apply_le_gauge_supSlice_of_mem_integerLattice {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) (i : ι) (w : InfinitePlace K) :
    w (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) : ι → 𝓞 K) i : K) ≤
      gauge (W.supSlice : Set W.euclideanSpan) a := by
  classical
  rw [← normAtPlace_apply, mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply,
    ← mixedCoords_apply, gauge_supSlice]
  exact (TauCeti.NumberField.mixedEmbedding.normAtPlace_le_norm w _).trans
    (norm_le_pi_norm (W.mixedCoords a) i)

variable (W) in
/-- **Volume lower bound for `W.supSlice`.** Combining Vaaler's cube-slicing theorem at the real
places with the polydisc-slicing theorem at the complex places bounds the volume of `W.supSlice`
from below by `2 ^ (finrank K W * nrRealPlaces K) * π ^ (finrank K W * nrComplexPlaces K)`. -/
theorem two_pow_mul_pi_pow_le_volume_supSlice :
    (2 : ℝ≥0∞) ^ (finrank K W * nrRealPlaces K) *
        ENNReal.ofReal Real.pi ^ (finrank K W * nrComplexPlaces K) ≤
      volume (W.supSlice : Set W.euclideanSpan) := by
  classical
  let Sr : ∀ w : {w : InfinitePlace K // w.IsReal}, Set (W.realPlaceSpan w) :=
    fun w ↦ {u | ∀ i, |(u : EuclideanSpace ℝ ι) i| ≤ 1}
  let Sc : ∀ w : {w : InfinitePlace K // w.IsComplex},
      Set ((W.complexPlaceSpan w).restrictScalars ℝ) :=
    fun w ↦ {u | ∀ i, ‖(u : EuclideanSpace ℂ ι) i‖ ≤ 1}
  have hpre : (W.supSlice : Set W.euclideanSpan) =
      W.placeCoordsEquiv ⁻¹' ((univ.pi Sr) ×ˢ (univ.pi Sc)) := by
    ext x
    simp only [coe_supSlice, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi,
      Sr, Sc]
    refine ⟨fun hx ↦ ⟨fun w i ↦ ?_, fun w i ↦ ?_⟩, fun ⟨hr, hc⟩ i w ↦ ?_⟩
    · rw [coe_placeCoordsEquiv_fst]
      simpa only [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] using hx i w.1
    · rw [coe_placeCoordsEquiv_snd]
      simpa only [normAtPlace_apply_of_isComplex w.2] using hx i w.1
    · obtain hw | hw := w.isReal_or_isComplex
      · have hrw := hr ⟨w, hw⟩ i
        rw [coe_placeCoordsEquiv_fst] at hrw
        simpa only [normAtPlace_apply_of_isReal hw, Real.norm_eq_abs] using hrw
      · have hcw := hc ⟨w, hw⟩ i
        rw [coe_placeCoordsEquiv_snd] at hcw
        simpa only [normAtPlace_apply_of_isComplex hw] using hcw
  have hmeasSr : ∀ w, MeasurableSet (Sr w) := fun w ↦ by
    dsimp only [Sr]
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const).measurableSet
  have hmeasSc : ∀ w, MeasurableSet (Sc w) := fun w ↦ by
    dsimp only [Sc]
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const).measurableSet
  have hprod_r : (2 : ℝ≥0∞) ^ (finrank K W * nrRealPlaces K) ≤ ∏ w, volume (Sr w) := by
    calc (2 : ℝ≥0∞) ^ (finrank K W * nrRealPlaces K)
        = ∏ _w : {w : InfinitePlace K // w.IsReal}, (2 : ℝ≥0∞) ^ finrank K W := by
          simp [pow_mul]
      _ ≤ ∏ w, volume (Sr w) := Finset.prod_le_prod fun w _ ↦ by
          simpa [Sr, finrank_realPlaceSpan] using
            (W.realPlaceSpan w).two_pow_finrank_le_volume_setOf_forall_abs_le_one
  have hprod_c :
      ENNReal.ofReal Real.pi ^ (finrank K W * nrComplexPlaces K) ≤ ∏ w, volume (Sc w) := by
    calc ENNReal.ofReal Real.pi ^ (finrank K W * nrComplexPlaces K)
        = ∏ _w : {w : InfinitePlace K // w.IsComplex},
            ENNReal.ofReal Real.pi ^ finrank K W := by
          simp [pow_mul]
      _ ≤ ∏ w, volume (Sc w) := Finset.prod_le_prod fun w _ ↦ by
          simpa [Sc, finrank_complexPlaceSpan] using
            (W.complexPlaceSpan w).pi_pow_finrank_le_volume_setOf_forall_norm_le_one
  rw [hpre, volume_preimage_placeCoordsEquiv_pi_prod W hmeasSr hmeasSc]
  exact mul_le_mul' hprod_r hprod_c

variable (W) in
/-- **Real-valued volume lower bound for `W.supSlice`.** -/
theorem two_pow_mul_pi_pow_le_volume_real_supSlice :
    (2 : ℝ) ^ (finrank K W * nrRealPlaces K) *
        Real.pi ^ (finrank K W * nrComplexPlaces K) ≤
      volume.real (W.supSlice : Set W.euclideanSpan) := by
  have hlhs :
      ENNReal.ofReal ((2 : ℝ) ^ (finrank K W * nrRealPlaces K) *
          Real.pi ^ (finrank K W * nrComplexPlaces K)) =
        (2 : ℝ≥0∞) ^ (finrank K W * nrRealPlaces K) *
          ENNReal.ofReal Real.pi ^ (finrank K W * nrComplexPlaces K) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat]
  exact (ENNReal.ofReal_le_iff_le_toReal W.supSlice.isCompact.measure_lt_top.ne).mp
    (hlhs.trans_le (two_pow_mul_pi_pow_le_volume_supSlice W))

end SupSlice

section EuclideanBallSlice

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  (W : Submodule K (ι → K))

open scoped Classical in
private theorem setOf_euclideanBallSlice_eq_preimage :
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1} =
      W.placeCoordsEquiv.toLinearMap ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, LinearEquiv.coe_coe, mem_closedBall_zero_iff,
    Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg zero_le_one,
    norm_placeCoordsEquiv_fst, norm_placeCoordsEquiv_snd]
  exact ⟨fun hx ↦ ⟨fun w ↦ hx w.1, fun w ↦ hx w.1⟩, fun ⟨hr, hc⟩ w ↦
    w.isReal_or_isComplex.elim (fun hw ↦ hr ⟨w, hw⟩) (fun hw ↦ hc ⟨w, hw⟩)⟩

open scoped Classical in
/-- The central slice in `W.euclideanSpan` of the product of closed unit Euclidean balls at the
infinite places of `K`, as a `ConvexBody`. -/
def euclideanBallSlice : ConvexBody W.euclideanSpan :=
  ConvexBody.ofEqPreimageClosedBall
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
      √(∑ i : ι,
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1}
    W.placeCoordsEquiv.injective (setOf_euclideanBallSlice_eq_preimage W)

variable {W}

open scoped Classical in
/-- Carrier of `W.euclideanBallSlice`. -/
@[simp]
theorem coe_euclideanBallSlice :
    (W.euclideanBallSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1} :=
  ConvexBody.coe_ofEqPreimageClosedBall _ _ _

/-- Membership in `W.euclideanBallSlice`. -/
@[simp]
theorem mem_euclideanBallSlice {x : W.euclideanSpan} :
    x ∈ W.euclideanBallSlice ↔
      ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1 := by
  rw [← SetLike.mem_coe, coe_euclideanBallSlice, mem_ofPred_eq]

/-- `W.euclideanBallSlice` is symmetric about the origin. -/
theorem neg_mem_euclideanBallSlice {x : W.euclideanSpan} :
    -x ∈ W.euclideanBallSlice ↔ x ∈ W.euclideanBallSlice := by
  classical
  exact ConvexBody.neg_mem_of_coe_eq_preimage_closedBall
    (coe_euclideanBallSlice.trans (setOf_euclideanBallSlice_eq_preimage W))

variable (W) in
/-- The origin lies in the interior of `W.euclideanBallSlice`. -/
theorem zero_mem_interior_euclideanBallSlice :
    (0 : W.euclideanSpan) ∈ interior (W.euclideanBallSlice : Set _) := by
  classical
  exact ConvexBody.zero_mem_interior_of_coe_eq_preimage_closedBall
    (coe_euclideanBallSlice.trans (setOf_euclideanBallSlice_eq_preimage W))

/-- The gauge of `W.euclideanBallSlice` is the supremum over all infinite places `w` of the local
Euclidean norm `√(∑ i, normAtPlace w (toMixed K (x i)) ^ 2)`. -/
theorem gauge_euclideanBallSlice (x : W.euclideanSpan) :
    gauge (W.euclideanBallSlice : Set W.euclideanSpan) x =
      ⨆ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
  classical
  have hgauge :
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) x = ‖W.placeCoordsEquiv x‖ := by
    simpa only [LinearEquiv.coe_coe] using
      ConvexBody.gauge_of_coe_eq_preimage_closedBall
        (coe_euclideanBallSlice.trans (setOf_euclideanBallSlice_eq_preimage W)) x
  set g : InfinitePlace K → ℝ := fun w ↦
    √(∑ i : ι,
      normAtPlace w
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2)
  rw [hgauge, Prod.norm_def]
  refine le_antisymm ?_ ?_
  · have hsup_nn : 0 ≤ ⨆ w, g w := Real.iSup_nonneg fun _ ↦ Real.sqrt_nonneg _
    refine max_le ((pi_norm_le_iff_of_nonneg hsup_nn).2 fun w ↦ ?_)
      ((pi_norm_le_iff_of_nonneg hsup_nn).2 fun w ↦ ?_)
    · rw [norm_placeCoordsEquiv_fst]
      exact le_ciSup (Set.finite_range g).bddAbove w.1
    · rw [norm_placeCoordsEquiv_snd]
      exact le_ciSup (Set.finite_range g).bddAbove w.1
  · refine ciSup_le fun w ↦ ?_
    dsimp only [g]
    obtain hw | hw := w.isReal_or_isComplex
    · exact (norm_placeCoordsEquiv_fst W x ⟨w, hw⟩).symm.trans_le
        ((norm_le_pi_norm (W.placeCoordsEquiv x).1 ⟨w, hw⟩).trans (le_max_left _ _))
    · exact (norm_placeCoordsEquiv_snd W x ⟨w, hw⟩).symm.trans_le
        ((norm_le_pi_norm (W.placeCoordsEquiv x).2 ⟨w, hw⟩).trans (le_max_right _ _))

/-- For `0 ≤ t`, the dilate `t • W.euclideanBallSlice` consists of the points `x ∈ W.euclideanSpan`
with `√(∑ i, normAtPlace w (toMixed K (x i)) ^ 2) ≤ t` at every infinite place `w`. -/
theorem mem_smul_euclideanBallSlice_iff {t : ℝ} (ht : 0 ≤ t) {x : W.euclideanSpan} :
    x ∈ t • (W.euclideanBallSlice : Set W.euclideanSpan) ↔
      ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ t := by
  classical
  rw [ConvexBody.mem_smul_iff_norm_le_of_coe_eq_preimage_closedBall
      (coe_euclideanBallSlice.trans (setOf_euclideanBallSlice_eq_preimage W))
      W.placeCoordsEquiv.injective ht,
    LinearEquiv.coe_coe, Prod.norm_def, max_le_iff,
    pi_norm_le_iff_of_nonneg ht, pi_norm_le_iff_of_nonneg ht]
  simp only [norm_placeCoordsEquiv_fst, norm_placeCoordsEquiv_snd]
  exact ⟨fun ⟨hr, hc⟩ w ↦
      w.isReal_or_isComplex.elim (fun hw ↦ hr ⟨w, hw⟩) (fun hw ↦ hc ⟨w, hw⟩),
    fun hx ↦ ⟨fun w ↦ hx w.1, fun w ↦ hx w.1⟩⟩

/-- At every infinite place `w`, the local Euclidean norm of the integral point corresponding to
`a ∈ W.integerLattice` is bounded by `gauge W.euclideanBallSlice a`. -/
theorem sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) (w : InfinitePlace K) :
    √(∑ i : ι,
        ‖w.embedding
          (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) :
            ι → 𝓞 K) i : K)‖ ^ 2) ≤
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) a := by
  rw [gauge_euclideanBallSlice]
  set g : InfinitePlace K → ℝ := fun u ↦
    √(∑ i : ι,
      normAtPlace u
        (euclidean.toMixed K ((a : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2)
  have hsum :
      √(∑ i : ι,
          ‖w.embedding
            (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) :
              ι → 𝓞 K) i : K)‖ ^ 2) = g w := by
    dsimp only [g]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_embedding_eq, ← normAtPlace_apply,
      mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply]
  rw [hsum]
  exact le_ciSup (Set.finite_range g).bddAbove w

variable (W) in
/-- **Exact volume of `W.euclideanBallSlice`.** It is `ω_k ^ r₁ * ω_{2k} ^ r₂`, where
`k = finrank K W` and `ω_a` is the volume of the `a`-dimensional unit Euclidean ball. -/
theorem volume_euclideanBallSlice :
    volume (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^ nrComplexPlaces K := by
  classical
  have hpi :
      closedBall
        (0 :
          (∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w) ×
          (∀ w : {w : InfinitePlace K // w.IsComplex},
            (W.complexPlaceSpan w).restrictScalars ℝ))
        1 =
      (univ.pi fun w ↦ closedBall (0 : W.realPlaceSpan w) 1) ×ˢ
        (univ.pi fun w ↦ closedBall (0 : (W.complexPlaceSpan w).restrictScalars ℝ) 1) := by
    ext z
    simp [Prod.norm_def, pi_norm_le_iff_of_nonneg zero_le_one]
  have hr (w : {w : InfinitePlace K // w.IsReal}) :
      volume (closedBall (0 : W.realPlaceSpan w) 1) =
        volume (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) := by
    rw [Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
      ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ofReal_measureReal (μ := volume)
        (s := ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) measure_ball_lt_top.ne,
      TauCeti.volume_real_unitBall, TauCeti.volume_real_unitBall, finrank_realPlaceSpan,
      finrank_euclideanSpace_fin]
  have hc (w : {w : InfinitePlace K // w.IsComplex}) :
      volume (closedBall (0 : (W.complexPlaceSpan w).restrictScalars ℝ) 1) =
        volume (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) := by
    rw [Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
      ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ofReal_measureReal (μ := volume)
        (s := ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) measure_ball_lt_top.ne,
      TauCeti.volume_real_unitBall, TauCeti.volume_real_unitBall, finrank_real_complexPlaceSpan,
      finrank_euclideanSpace_fin]
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage, hpi, LinearEquiv.coe_coe,
    volume_preimage_placeCoordsEquiv_pi_prod W (fun _ ↦ measurableSet_closedBall)
      (fun _ ↦ measurableSet_closedBall)]
  simp [hr, hc]

variable (W) in
/-- **Exact real volume of `W.euclideanBallSlice`.** It is `ω_k ^ r₁ * ω_{2k} ^ r₂`, where
`k = finrank K W` and `ω_a` is the volume of the `a`-dimensional unit Euclidean ball. -/
theorem volume_real_euclideanBallSlice :
    volume.real (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^
          nrComplexPlaces K := by
  rw [measureReal_def, volume_euclideanBallSlice, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ← measureReal_def, ← measureReal_def]

end EuclideanBallSlice

end Submodule

end
