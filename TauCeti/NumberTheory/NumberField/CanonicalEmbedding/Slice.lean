/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SubspaceLattice

import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.Analysis.Convex.Gauge.Basic
import TauCeti.LinearAlgebra.Basis.Submodule
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation

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

* `Submodule.realPlaceSpan W w`, `Submodule.complexPlaceSpan W w`: the local real and complex
  subspaces spanned by `W` at an infinite place `w`.
* `Submodule.supSlice W`: the central slice in `W.euclideanSpan` of the local unit cubes and
  polydiscs, as a `ConvexBody`.
* `Submodule.euclideanBallSlice W`: the central slice in `W.euclideanSpan` of the local unit
  Euclidean balls, as a `ConvexBody`.

## Main results

* `Submodule.finrank_realPlaceSpan`, `Submodule.finrank_complexPlaceSpan`,
  `Submodule.finrank_real_complexPlaceSpan`: dimensions of the local place subspaces.
* `Submodule.two_pow_mul_pi_pow_le_volume_supSlice` and
  `Submodule.two_pow_mul_pi_pow_le_volume_real_supSlice`: the volume of `W.supSlice` is at least
  `2 ^ (finrank K W * nrRealPlaces K) * π ^ (finrank K W * nrComplexPlaces K)`.
* `Submodule.volume_real_euclideanBallSlice`: the real volume of `W.euclideanBallSlice` is
  `ω_k ^ nrRealPlaces K * ω_{2k} ^ nrComplexPlaces K`.
* `Submodule.apply_le_gauge_supSlice_of_mem_integerLattice` and
  `Submodule.sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice`: archimedean bounds on
  integral points in terms of the gauges of `W.supSlice` and `W.euclideanBallSlice`.

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
open scoped Pointwise Real RealInnerProductSpace

namespace Submodule

section LocalPlaceSpans

variable {K : Type*} [Field K] {ι : Type*}

/-- Helper computing the dimension of the `F`-span in `EuclideanSpace F ι` of the image of a
`K`-subspace `W` along a field homomorphism `φ : K →+* F`. -/
private theorem finrank_span_toLp_ringHom [Finite ι] {F : Type*} [RCLike F]
    (φ : K →+* F) (W : Submodule K (ι → K)) :
    finrank F
        (span F ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ φ (v i)) '' (W : Set (ι → K)))) =
      finrank K W := by
  let : Algebra K F := φ.toAlgebra
  have : IsScalarTower K F F := IsScalarTower.of_algebraMap_eq' rfl
  let f : (ι → K) →ₗ[K] EuclideanSpace F ι :=
    (WithLp.linearEquiv 2 F (ι → F)).symm.toLinearMap.restrictScalars K ∘ₗ Pi.algebraMap ι K F
  let b := finBasis K W
  have hspan : span F ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ φ (v i)) '' (W : Set (ι → K))) =
      span F (range fun j ↦ f (b j)) := b.span_image f
  have hli : LinearIndependent F (fun j ↦ f (b j)) := by
    have h1 : LinearIndependent F (fun j i ↦ algebraMap K F ((b j : ι → K) i)) :=
      (linearIndependent_algebraMap_comp_iff (R := K) (S := F)).mpr b.linearIndependent_coe_basis
    exact h1.map' (WithLp.linearEquiv 2 F (ι → F)).symm.toLinearMap (LinearEquiv.ker _)
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

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

/-- `W.realPlaceSpan w` has real dimension `finrank K W`. -/
@[simp]
theorem finrank_realPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    finrank ℝ (W.realPlaceSpan w) = finrank K W :=
  finrank_span_toLp_ringHom (embedding_of_isReal w.2) W

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

/-- `W.complexPlaceSpan w` has complex dimension `finrank K W`. -/
@[simp]
theorem finrank_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℂ (W.complexPlaceSpan w) = finrank K W :=
  finrank_span_toLp_ringHom w.1.embedding W

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

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

open scoped Classical in
/-- `L²` product of the local subspaces `W.realPlaceSpan w` and
`(W.complexPlaceSpan w).restrictScalars ℝ` across all infinite places of `K`. -/
private abbrev placeSpanProd (W : Submodule K (ι → K)) : Type _ :=
  WithLp 2
    ((PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) ×
     (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
       (W.complexPlaceSpan w).restrictScalars ℝ))

private instance instSecondCountableRealPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    SecondCountableTopology (W.realPlaceSpan w) :=
  TopologicalSpace.secondCountableTopology_induced
    (W.realPlaceSpan w) (EuclideanSpace ℝ ι) Subtype.val

private instance instSecondCountableComplexPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    SecondCountableTopology ((W.complexPlaceSpan w).restrictScalars ℝ) :=
  TopologicalSpace.secondCountableTopology_induced
    ((W.complexPlaceSpan w).restrictScalars ℝ) (EuclideanSpace ℂ ι) Subtype.val

open Classical in
private instance instBorelSpaceRealPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) :=
  PiLp.borelSpace 2

open Classical in
private instance instBorelSpaceComplexPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace
      (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
        (W.complexPlaceSpan w).restrictScalars ℝ) :=
  PiLp.borelSpace 2

open Classical in
private instance instSecondCountableRealPlaceProd [Countable ι] (W : Submodule K (ι → K)) :
    SecondCountableTopology
      (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) :=
  inferInstance

open Classical in
private instance instBorelSpacePlaceSpanProd [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace (placeSpanProd W) :=
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
        rw [← real_inner_self_eq_norm_sq (x i),
          ← TauCeti.NumberField.mixedEmbedding.mixedInner_toMixed,
          TauCeti.NumberField.mixedEmbedding.mixedInner_def]
        congr 1
        · refine Finset.sum_congr rfl fun w _ ↦ ?_
          rw [Real.norm_eq_abs, sq_abs, sq]
        · refine Finset.sum_congr rfl fun w _ ↦ ?_
          rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
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
/-- `placeProductSubmodule W` is isometrically equivalent to `placeSpanProd W`. -/
private def placeProductEquivProd (W : Submodule K (ι → K)) :
    placeProductSubmodule W ≃ₗᵢ[ℝ] placeSpanProd W where
  toFun y := WithLp.toLp 2
    (WithLp.toLp 2 fun w ↦
      ⟨(WithLp.ofLp (y : placeAmbientProd K ι)).1 w, y.2.1 w (mem_univ w)⟩,
     WithLp.toLp 2 fun w ↦
      ⟨(WithLp.ofLp (y : placeAmbientProd K ι)).2 w, y.2.2 w (mem_univ w)⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun z :=
    ⟨WithLp.toLp 2
      (WithLp.toLp 2 fun w ↦ ((WithLp.ofLp z).1 w : EuclideanSpace ℝ ι),
       WithLp.toLp 2 fun w ↦ ((WithLp.ofLp z).2 w : EuclideanSpace ℂ ι)),
     ⟨fun w _ ↦ ((WithLp.ofLp z).1 w).2, fun w _ ↦ ((WithLp.ofLp z).2 w).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' y := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    have hy : ‖y‖ = ‖(y : placeAmbientProd K ι)‖ := rfl
    rw [hy, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rfl

open scoped Classical in
/-- `ambientPlaceIsometryEquiv` maps `W.euclideanSpan` onto `placeProductSubmodule W`. -/
private theorem map_euclideanSpan_eq_placeProductSubmodule (W : Submodule K (ι → K)) :
    W.euclideanSpan.map ambientPlaceIsometryEquiv.toLinearEquiv.toLinearMap =
      placeProductSubmodule W := by
  have hle : W.euclideanSpan.map ambientPlaceIsometryEquiv.toLinearEquiv.toLinearMap ≤
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
/-- Canonical linear isometry between `W.euclideanSpan` and `placeSpanProd W`. -/
private def euclideanSpanEquivPlaceProd (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗᵢ[ℝ] placeSpanProd W :=
  ((LinearIsometryEquiv.submoduleMap W.euclideanSpan ambientPlaceIsometryEquiv).trans
    (LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_eq_placeProductSubmodule W))).trans
    (placeProductEquivProd W)

open scoped Classical in
/-- Linear equivalence from `W.euclideanSpan` to the Cartesian product of the real-place and
complex-place local Euclidean subspaces. -/
private def placeCoordsEquiv (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗ[ℝ]
      (∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w) ×
      (∀ w : {w : InfinitePlace K // w.IsComplex},
        (W.complexPlaceSpan w).restrictScalars ℝ) :=
  ((euclideanSpanEquivPlaceProd W).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ _)).trans
    ((WithLp.linearEquiv 2 ℝ _).prodCongr (WithLp.linearEquiv 2 ℝ _))

open scoped Classical in
private theorem coe_placeCoordsEquiv_fst (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((placeCoordsEquiv W x).1 w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w :=
  rfl

open scoped Classical in
private theorem coe_placeCoordsEquiv_snd (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((placeCoordsEquiv W x).2 w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w :=
  rfl

open Classical in
private instance instMeasureSpacePlaceSpanProd (W : Submodule K (ι → K)) :
    MeasureSpace (placeSpanProd W) :=
  measureSpaceOfInnerProductSpace

open Classical in
/-- `placeCoordsEquiv W` is measure-preserving between the subspace volume on `W.euclideanSpan`
and the product of the subspace volumes on `W.realPlaceSpan w` and `W.complexPlaceSpan w`. -/
private theorem measurePreserving_placeCoordsEquiv (W : Submodule K (ι → K)) :
    MeasurePreserving (placeCoordsEquiv W) volume volume := by
  have hmp₁ := LinearIsometryEquiv.measurePreserving
    (E := W.euclideanSpan) (F := placeSpanProd W) (euclideanSpanEquivPlaceProd W)
  have hmp :=
    ((PiLp.volume_preserving_symm_measurableEquiv_toLp
        fun w : {w : InfinitePlace K // w.IsReal} ↦ ↥(W.realPlaceSpan w)).prod
      (PiLp.volume_preserving_symm_measurableEquiv_toLp
        fun w : {w : InfinitePlace K // w.IsComplex} ↦
          ↥((W.complexPlaceSpan w).restrictScalars ℝ))).comp
      ((WithLp.volume_preserving_ofLp _ _).comp hmp₁)
  convert hmp using 1
  ext x <;> rfl

end PlaceIsometry

section SupSlice

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} (W : Submodule K (ι → K))

/-- Coordinate map from `W.euclideanSpan` to the sup-normed product `ι → mixedSpace K`. -/
private def mixedCoords : W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦
    (euclidean.toMixed K).toLinearMap.comp
      ((LinearMap.proj i).comp
        (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap)).comp
    W.euclideanSpan.subtype

private theorem mixedCoords_apply (x : W.euclideanSpan) (i : ι) :
    mixedCoords W x i =
      euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) :=
  rfl

private theorem injective_mixedCoords : Function.Injective (mixedCoords W) := by
  intro x y h
  ext1
  ext1 i
  exact (euclidean.toMixed K).injective (congrFun h i)

variable [Fintype ι]

open scoped Classical in
private theorem setOf_supSlice_eq_preimage :
    {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} =
      mixedCoords W ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg zero_le_one]
  refine forall_congr' fun i ↦ ?_
  rw [← mem_closedBall_zero_iff,
    TauCeti.NumberField.mixedEmbedding.closedBall_zero_eq_setOf_forall_normAtPlace_le]
  rfl

/-- The central slice in `W.euclideanSpan` of the product of local unit cubes `[-1, 1]^ι` at real
places and unit polydiscs at complex places, as a `ConvexBody`. -/
def supSlice : ConvexBody W.euclideanSpan where
  carrier := {x | ∀ (i : ι) (w : InfinitePlace K),
    normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1}
  convex' := by
    classical
    rw [setOf_supSlice_eq_preimage]
    exact (convex_closedBall 0 1).linear_preimage (mixedCoords W)
  isCompact' := by
    classical
    rw [setOf_supSlice_eq_preimage]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (injective_mixedCoords W))).isCompact_preimage
      (isCompact_closedBall 0 1)
  nonempty' := ⟨0, by simp⟩

variable {W}

/-- Carrier of `W.supSlice`. -/
@[simp]
theorem coe_supSlice :
    (W.supSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} :=
  (rfl)

/-- Membership in `W.supSlice`. -/
@[simp]
theorem mem_supSlice {x : W.euclideanSpan} :
    x ∈ W.supSlice ↔
      ∀ (i : ι) (w : InfinitePlace K),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1 :=
  Iff.rfl

/-- `W.supSlice` is symmetric about the origin. -/
theorem neg_mem_supSlice {x : W.euclideanSpan} : -x ∈ W.supSlice ↔ x ∈ W.supSlice := by
  have hneg (i : ι) :
      ((-x : W.euclideanSpan) : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i =
        -((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) :=
    rfl
  simp only [mem_supSlice, hneg, map_neg, normAtPlace_neg]

variable (W) in
/-- The origin lies in the interior of `W.supSlice`. -/
theorem zero_mem_interior_supSlice : (0 : W.euclideanSpan) ∈ interior (W.supSlice : Set _) := by
  classical
  rw [coe_supSlice, setOf_supSlice_eq_preimage]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage (mixedCoords W).continuous_of_finiteDimensional).mem_nhds (by simp))
    (preimage_mono ball_subset_closedBall)

open Classical in
/-- The gauge of `W.supSlice` is the maximum of `normAtPlace w (toMixed K (x i))` over all
coordinates `i` and infinite places `w`. -/
private theorem gauge_supSlice (x : W.euclideanSpan) :
    gauge (W.supSlice : Set W.euclideanSpan) x =
      ‖fun i : ι ↦ euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)‖ := by
  rw [coe_supSlice, setOf_supSlice_eq_preimage, LinearMap.gauge_preimage,
    gauge_closedBall zero_le_one, div_one]
  rfl

/-- At every coordinate `i` and infinite place `w`, the archimedean absolute value of the integral
point corresponding to `a ∈ W.integerLattice` is bounded by `gauge W.supSlice a`. -/
theorem apply_le_gauge_supSlice_of_mem_integerLattice {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) (i : ι) (w : InfinitePlace K) :
    w (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) : ι → 𝓞 K) i : K) ≤
      gauge (W.supSlice : Set W.euclideanSpan) a := by
  classical
  rw [← normAtPlace_apply, mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply,
    gauge_supSlice]
  exact (TauCeti.NumberField.mixedEmbedding.normAtPlace_le_norm w _).trans
    (norm_le_pi_norm
      (fun j : ι ↦ euclidean.toMixed K ((a : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) j)) i)

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
      placeCoordsEquiv W ⁻¹' ((univ.pi Sr) ×ˢ (univ.pi Sc)) := by
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
  have hr : Fintype.card {w : InfinitePlace K // w.IsReal} = nrRealPlaces K :=
    Fintype.card_congr (Equiv.refl _)
  have hc : Fintype.card {w : InfinitePlace K // w.IsComplex} = nrComplexPlaces K :=
    Fintype.card_congr (Equiv.refl _)
  rw [hpre,
    (measurePreserving_placeCoordsEquiv W).measure_preimage
      ((MeasurableSet.univ_pi hmeasSr).prod (MeasurableSet.univ_pi hmeasSc)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, ← hr, ← hc,
    pow_mul, pow_mul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_const]
  exact mul_le_mul'
    (Finset.prod_le_prod fun w _ ↦ by
      simpa [Sr, finrank_realPlaceSpan] using
        (W.realPlaceSpan w).two_pow_finrank_le_volume_setOf_forall_abs_le_one)
    (Finset.prod_le_prod fun w _ ↦ by
      simpa [Sc, finrank_complexPlaceSpan] using
        (W.complexPlaceSpan w).pi_pow_finrank_le_volume_setOf_forall_norm_le_one)

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
private theorem norm_placeCoordsEquiv_fst (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ‖(placeCoordsEquiv W x).1 w‖ =
      √(∑ i : ι,
        normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
  have hcoe :
      ‖(placeCoordsEquiv W x).1 w‖ =
        ‖(((placeCoordsEquiv W x).1 w : W.realPlaceSpan w) : EuclideanSpace ℝ ι)‖ :=
    rfl
  rw [hcoe, ← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_placeCoordsEquiv_fst, normAtPlace_apply_of_isReal w.2]

open scoped Classical in
private theorem norm_placeCoordsEquiv_snd (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ‖(placeCoordsEquiv W x).2 w‖ =
      √(∑ i : ι,
        normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
  have hcoe :
      ‖(placeCoordsEquiv W x).2 w‖ =
        ‖(((placeCoordsEquiv W x).2 w :
            (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι)‖ :=
    rfl
  rw [hcoe, ← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_placeCoordsEquiv_snd, normAtPlace_apply_of_isComplex w.2]

open scoped Classical in
private theorem setOf_euclideanBallSlice_eq_preimage :
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1} =
      (placeCoordsEquiv W).toLinearMap ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, LinearEquiv.coe_coe, mem_closedBall_zero_iff,
    Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg zero_le_one,
    norm_placeCoordsEquiv_fst, norm_placeCoordsEquiv_snd]
  exact ⟨fun hx ↦ ⟨fun w ↦ hx w.1, fun w ↦ hx w.1⟩, fun ⟨hr, hc⟩ w ↦
    w.isReal_or_isComplex.elim (fun hw ↦ hr ⟨w, hw⟩) (fun hw ↦ hc ⟨w, hw⟩)⟩

/-- The central slice in `W.euclideanSpan` of the product of closed unit Euclidean balls at the
infinite places of `K`, as a `ConvexBody`. -/
def euclideanBallSlice : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ w : InfinitePlace K,
    √(∑ i : ι,
      normAtPlace w
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1}
  convex' := by
    classical
    rw [setOf_euclideanBallSlice_eq_preimage]
    exact (convex_closedBall 0 1).linear_preimage (placeCoordsEquiv W).toLinearMap
  isCompact' := by
    classical
    rw [setOf_euclideanBallSlice_eq_preimage]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (placeCoordsEquiv W).injective)).isCompact_preimage
      (isCompact_closedBall 0 1)
  nonempty' := ⟨0, by simp⟩

variable {W}

/-- Carrier of `W.euclideanBallSlice`. -/
@[simp]
theorem coe_euclideanBallSlice :
    (W.euclideanBallSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1} :=
  (rfl)

/-- Membership in `W.euclideanBallSlice`. -/
@[simp]
theorem mem_euclideanBallSlice {x : W.euclideanSpan} :
    x ∈ W.euclideanBallSlice ↔
      ∀ w : InfinitePlace K,
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤ 1 :=
  Iff.rfl

/-- `W.euclideanBallSlice` is symmetric about the origin. -/
theorem neg_mem_euclideanBallSlice {x : W.euclideanSpan} :
    -x ∈ W.euclideanBallSlice ↔ x ∈ W.euclideanBallSlice := by
  have hneg (i : ι) :
      ((-x : W.euclideanSpan) : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i =
        -((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) :=
    rfl
  simp only [mem_euclideanBallSlice, hneg, map_neg, normAtPlace_neg]

variable (W) in
/-- The origin lies in the interior of `W.euclideanBallSlice`. -/
theorem zero_mem_interior_euclideanBallSlice :
    (0 : W.euclideanSpan) ∈ interior (W.euclideanBallSlice : Set _) := by
  classical
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage
      (placeCoordsEquiv W).toLinearMap.continuous_of_finiteDimensional).mem_nhds (by simp))
    (preimage_mono ball_subset_closedBall)

/-- At every infinite place `w`, the local Euclidean norm of the integral point corresponding to
`a ∈ W.integerLattice` is bounded by `gauge W.euclideanBallSlice a`. -/
theorem sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) (w : InfinitePlace K) :
    √(∑ i : ι,
        ‖w.embedding
          (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) :
            ι → 𝓞 K) i : K)‖ ^ 2) ≤
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) a := by
  classical
  have hgauge :
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) a = ‖placeCoordsEquiv W a‖ := by
    rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage, LinearMap.gauge_preimage,
      gauge_closedBall zero_le_one, div_one]
    rfl
  have hsum :
      √(∑ i : ι,
          ‖w.embedding
            (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ : W.integerPoints) :
              ι → 𝓞 K) i : K)‖ ^ 2) =
        √(∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((a : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) := by
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_embedding_eq, ← normAtPlace_apply,
      mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply]
  rw [hsum, hgauge, Prod.norm_def]
  obtain hw | hw := w.isReal_or_isComplex
  · rw [← norm_placeCoordsEquiv_fst W a ⟨w, hw⟩]
    exact (norm_le_pi_norm (placeCoordsEquiv W a).1 ⟨w, hw⟩).trans (le_max_left _ _)
  · rw [← norm_placeCoordsEquiv_snd W a ⟨w, hw⟩]
    exact (norm_le_pi_norm (placeCoordsEquiv W a).2 ⟨w, hw⟩).trans (le_max_right _ _)

/-- Real volume of the closed unit ball in a `d`-dimensional real inner product space `V` agrees
with that of the open unit ball in `EuclideanSpace ℝ (Fin d)`, including `d = 0`. -/
private theorem volume_real_closedBall_eq_model (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {d : ℕ} (hd : finrank ℝ V = d) :
    volume.real (closedBall (0 : V) 1) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  subst hd
  have hcb : volume (closedBall (0 : V) 1) = volume (ball (0 : V) 1) := by
    rcases subsingleton_or_nontrivial V with _ | _
    · rw [TauCeti.volume_eq_one_of_subsingleton (nonempty_closedBall.2 zero_le_one),
        TauCeti.volume_eq_one_of_subsingleton (nonempty_ball.2 one_pos)]
    · simpa using Measure.addHaar_closedBall (volume : Measure V) (0 : V) zero_le_one
  rw [measureReal_def, hcb, ← measureReal_def, TauCeti.volume_real_unitBall,
    TauCeti.volume_real_unitBall, finrank_euclideanSpace_fin]

variable (W) in
/-- **Exact real volume of `W.euclideanBallSlice`.** It is `ω_k ^ r₁ * ω_{2k} ^ r₂`, where
`k = finrank K W` and `ω_a` is the volume of the `a`-dimensional unit Euclidean ball. -/
theorem volume_real_euclideanBallSlice :
    volume.real (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^
          nrComplexPlaces K := by
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
  have hvol :
      volume (W.euclideanBallSlice : Set W.euclideanSpan) =
        (∏ w : {w : InfinitePlace K // w.IsReal}, volume (closedBall (0 : W.realPlaceSpan w) 1)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            volume (closedBall (0 : (W.complexPlaceSpan w).restrictScalars ℝ) 1) := by
    rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage, hpi, LinearEquiv.coe_coe,
      (measurePreserving_placeCoordsEquiv W).measure_preimage
        ((MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall).prod
          (MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall)).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod]
  congr 1
  · simp_rw [← measureReal_def,
      fun w ↦ volume_real_closedBall_eq_model ↥(W.realPlaceSpan w) (finrank_realPlaceSpan W w),
      Finset.prod_const, Finset.card_univ]
  · simp_rw [← measureReal_def,
      fun w ↦ volume_real_closedBall_eq_model ↥((W.complexPlaceSpan w).restrictScalars ℝ)
        (finrank_real_complexPlaceSpan W w),
      Finset.prod_const, Finset.card_univ]

end EuclideanBallSlice

end Submodule

end
