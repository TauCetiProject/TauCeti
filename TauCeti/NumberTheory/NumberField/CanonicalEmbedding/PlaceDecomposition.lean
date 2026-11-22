/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Gauge.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SubspaceLattice

import TauCeti.LinearAlgebra.Dimension.BaseChange
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Archimedean place decomposition and convex slices of a number-field subspace

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places and `r₂` complex places, and
let `W` be a `K`-subspace of `ι → K` of dimension `k`. Inside the Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`, the real span
`W.euclideanSpan` has dimension `D * k`. Regrouping coordinates by infinite place rather than by `ι`
decomposes `W.euclideanSpan` orthogonally into local subspaces:

* at each real place `w`, the real span `W.realPlaceSpan w` of `(φ_w ∘ v)_{v ∈ W}` in
  `EuclideanSpace ℝ ι`, of real dimension `k`;
* at each complex place `w`, the complex span `W.complexPlaceSpan w` of `(φ_w ∘ v)_{v ∈ W}` in
  `EuclideanSpace ℂ ι`, of complex dimension `k` and real dimension `2 * k`.

Because `r₁ * k + 2 * r₂ * k = D * k`, the natural `ℝ`-linear isometry from `W.euclideanSpan` into
the `L²` product `W.placeSpanProd` of these local subspaces is surjective, giving a canonical linear
isometric equivalence `W.euclideanSpanEquivPlaceSpanProd`.

Transporting product bodies across `W.euclideanSpanEquivPlaceSpanProd` yields two origin-symmetric
convex bodies in `W.euclideanSpan` whose gauges bound the projective sup and Euclidean heights of
integral points of `W`:

* `W.supSlice`: `{x ∈ W.euclideanSpan | ∀ w i, |x_i|_w ≤ 1}`, factoring into central cube slices at
  real places and central polydisc slices at complex places, of volume at least
  `2 ^ (r₁ * k) * π ^ (r₂ * k)` by Vaaler's theorem and its complex counterpart.
* `W.euclideanBallSlice`: `{x ∈ W.euclideanSpan | ∀ w, ∑ i, |x_i|_w ^ 2 ≤ 1}`, factoring into unit
  Euclidean balls of dimensions `k` and `2 * k`, of exact volume `ω_k ^ r₁ * ω_{2k} ^ r₂`.

## Main definitions

* `Submodule.realPlaceSpan W w`, `Submodule.complexPlaceSpan W w`: the local `ℝ`- and `ℂ`-spans of
  `W` in `EuclideanSpace ℝ ι` and `EuclideanSpace ℂ ι` at real and complex places `w`, with
  universal properties `Submodule.realPlaceSpan_le_iff` and `Submodule.complexPlaceSpan_le_iff`.
* `Submodule.placeSpanProd W`: the `L²` product of the local place spans across all infinite places.
* `Submodule.euclideanSpanEquivPlaceSpanProd W`: `W.euclideanSpan ≃ₗᵢ[ℝ] W.placeSpanProd`.
* `Submodule.supSlice W`, `Submodule.euclideanBallSlice W`: the local sup-norm and local Euclidean
  unit-ball slices in `W.euclideanSpan`, packaged as `ConvexBody W.euclideanSpan`.

## Main results

* `Submodule.finrank_realPlaceSpan`, `Submodule.finrank_complexPlaceSpan`,
  `Submodule.finrank_restrictScalars_complexPlaceSpan`: dimensions of the local place spans.
* `Submodule.two_pow_mul_pi_pow_le_volume_real_supSlice`: the volume of `W.supSlice` is at least
  `2 ^ (nrRealPlaces K * finrank K W) * π ^ (nrComplexPlaces K * finrank K W)`.
* `Submodule.volume_real_euclideanBallSlice`: the volume of `W.euclideanBallSlice` equals the
  product of the unit-ball volumes in dimensions `finrank K W` and `2 * finrank K W`.
* `Submodule.normAtPlace_le_gauge_supSlice`,
  `Submodule.sum_normAtPlace_sq_le_gauge_euclideanBallSlice_sq`: local archimedean norm bounds on
  `W.euclideanSpan` in terms of the two gauges.

## References

* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math.
  **83** (1979), 543–553.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.9 and Appendix C.3.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §6.1 and §13.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators

namespace Submodule

section PlaceSpan

variable {K : Type*} [Field K] {ι : Type*}

/-- The `ℝ`-span in `EuclideanSpace ℝ ι` of a `K`-subspace `W` of `ι → K` along a real infinite
place `w`. -/
def realPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsReal}) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.property (v i)) '' W)

/-- The `ℂ`-span in `EuclideanSpace ℂ ι` of a `K`-subspace `W` of `ι → K` along a complex infinite
place `w`. -/
def complexPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsComplex}) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  span ℂ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.val.embedding (v i)) '' W)

/-- Every vector of `W` embeds into `W.realPlaceSpan w`. -/
theorem toLp_mem_realPlaceSpan {W : Submodule K (ι → K)} (w : {w : InfinitePlace K // w.IsReal})
    {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ embedding_of_isReal w.property (v i)) ∈ W.realPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- Every vector of `W` embeds into `W.complexPlaceSpan w`. -/
theorem toLp_mem_complexPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsComplex}) {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ w.val.embedding (v i)) ∈ W.complexPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- `W.realPlaceSpan w` is contained in an `ℝ`-submodule `U` if and only if the image of every
vector of `W` under `w` belongs to `U`. -/
@[simp]
theorem realPlaceSpan_le_iff {W : Submodule K (ι → K)} {w : {w : InfinitePlace K // w.IsReal}}
    {U : Submodule ℝ (EuclideanSpace ℝ ι)} :
    W.realPlaceSpan w ≤ U ↔
      ∀ v ∈ W, (WithLp.toLp 2 fun i ↦ embedding_of_isReal w.property (v i)) ∈ U := by
  rw [realPlaceSpan, span_le, image_subset_iff, subset_def]
  simp only [mem_preimage, SetLike.mem_coe]

/-- `W.complexPlaceSpan w` is contained in a `ℂ`-submodule `U` if and only if the image of every
vector of `W` under `w` belongs to `U`. -/
@[simp]
theorem complexPlaceSpan_le_iff {W : Submodule K (ι → K)}
    {w : {w : InfinitePlace K // w.IsComplex}} {U : Submodule ℂ (EuclideanSpace ℂ ι)} :
    W.complexPlaceSpan w ≤ U ↔
      ∀ v ∈ W, (WithLp.toLp 2 fun i ↦ w.val.embedding (v i)) ∈ U := by
  rw [complexPlaceSpan, span_le, image_subset_iff, subset_def]
  simp only [mem_preimage, SetLike.mem_coe]

/-- The real-place span of the zero subspace is zero. -/
@[simp]
theorem realPlaceSpan_bot (w : {w : InfinitePlace K // w.IsReal}) :
    (⊥ : Submodule K (ι → K)).realPlaceSpan w = ⊥ := by
  rw [realPlaceSpan, bot_coe, image_singleton, span_singleton_eq_bot]; ext1; simp

/-- The complex-place span of the zero subspace is zero. -/
@[simp]
theorem complexPlaceSpan_bot (w : {w : InfinitePlace K // w.IsComplex}) :
    (⊥ : Submodule K (ι → K)).complexPlaceSpan w = ⊥ := by
  rw [complexPlaceSpan, bot_coe, image_singleton, span_singleton_eq_bot]; ext1; simp

/-- At each real place `w`, `W.realPlaceSpan w` has real dimension `finrank K W`. -/
@[simp]
theorem finrank_realPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    finrank ℝ (W.realPlaceSpan w) = finrank K W := by
  have himg : (fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.property (v i)) ''
      (W : Set (ι → K)) =
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap ''
        ((fun v : ι → K ↦ embedding_of_isReal w.property ∘ v) '' (W : Set (ι → K))) := by
    ext; simp [Function.comp_def]
  rw [realPlaceSpan, himg, ← Submodule.map_span, LinearEquiv.finrank_map_eq,
    W.finrank_span_image_comp]

/-- At each complex place `w`, `W.complexPlaceSpan w` has complex dimension `finrank K W`. -/
@[simp]
theorem finrank_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℂ (W.complexPlaceSpan w) = finrank K W := by
  have himg : (fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.val.embedding (v i)) ''
      (W : Set (ι → K)) =
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap ''
        ((fun v : ι → K ↦ w.val.embedding ∘ v) '' (W : Set (ι → K))) := by
    ext; simp [Function.comp_def]
  rw [complexPlaceSpan, himg, ← Submodule.map_span, LinearEquiv.finrank_map_eq,
    W.finrank_span_image_comp]

/-- Viewed over `ℝ`, `W.complexPlaceSpan w` has real dimension `2 * finrank K W`. -/
@[simp]
theorem finrank_restrictScalars_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℝ ((W.complexPlaceSpan w).restrictScalars ℝ) = 2 * finrank K W := by
  rw [((Submodule.restrictScalarsEquiv ℝ ℂ _ _).restrictScalars ℝ).finrank_eq,
    ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_complexPlaceSpan]

/-- Shortcut Borel structure on `(W.complexPlaceSpan w).restrictScalars ℝ`. -/
instance instBorelSpaceRestrictScalarsComplexPlaceSpan [Countable ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    BorelSpace ((W.complexPlaceSpan w).restrictScalars ℝ) :=
  Subtype.borelSpace _

/-- Shortcut Haar `MeasureSpace` on `(W.complexPlaceSpan w).restrictScalars ℝ`. -/
instance instMeasureSpaceRestrictScalarsComplexPlaceSpan [Fintype ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    MeasureSpace ((W.complexPlaceSpan w).restrictScalars ℝ) :=
  measureSpaceOfInnerProductSpace

/-- The `L²` product of the local real and complex place spans of `W` across all infinite places of
`K`. -/
abbrev placeSpanProd (W : Submodule K (ι → K)) : Type _ :=
  WithLp 2
    ((PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w) ×
      (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
        (W.complexPlaceSpan w).restrictScalars ℝ))

open scoped Classical in
/-- `W.placeSpanProd` has real dimension `[K : ℚ] * finrank K W`. -/
theorem finrank_placeSpanProd [NumberField K] [Finite ι] (W : Submodule K (ι → K)) :
    finrank ℝ W.placeSpanProd = finrank ℚ K * finrank K W := by
  cases nonempty_fintype ι
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _), Module.finrank_prod,
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [finrank_realPlaceSpan, finrank_restrictScalars_complexPlaceSpan, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  rw [← card_add_two_mul_card_eq_rank (K := K)]
  ring

end PlaceSpan

section IsometricDecomposition

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

private def evalMixed (i : ι) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K :=
  (euclidean.toMixed K).toLinearMap ∘ₗ
    (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap

private def ambientRealProj (w : {w : InfinitePlace K // w.IsReal}) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦
    (LinearMap.proj w).comp ((LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
      ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp (evalMixed i))

private def ambientComplexProj (w : {w : InfinitePlace K // w.IsComplex}) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] EuclideanSpace ℂ ι :=
  ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.pi fun i ↦
    (LinearMap.proj w).comp ((LinearMap.snd ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
      ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp (evalMixed i))

omit [Fintype ι] in
private theorem ambientRealProj_apply (w : {w : InfinitePlace K // w.IsReal})
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    ambientRealProj w x i = (euclidean.toMixed K (x i)).1 w := by
  simp [ambientRealProj, evalMixed]

omit [Fintype ι] in
private theorem ambientComplexProj_apply (w : {w : InfinitePlace K // w.IsComplex})
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    ambientComplexProj w x i = (euclidean.toMixed K (x i)).2 w := by
  simp [ambientComplexProj, evalMixed]

omit [Fintype ι] in
private theorem ambientRealProj_mem_realPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsReal}) {x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K}
    (hx : x ∈ W.euclideanSpan) :
    ambientRealProj w x ∈ W.realPlaceSpan w := by
  refine (euclideanSpan_le_iff (U := (W.realPlaceSpan w).comap (ambientRealProj w))).2 ?_ hx
  intro v hv
  have heq :
      ambientRealProj w
          (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) =
        WithLp.toLp 2 fun i ↦ embedding_of_isReal w.property (v i) := by
    ext i
    rw [ambientRealProj_apply, PiLp.toLp_apply, PiLp.toLp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact mixedEmbedding_apply_isReal K (v i) w
  rw [Submodule.mem_comap, heq]
  exact toLp_mem_realPlaceSpan w hv

omit [Fintype ι] in
private theorem ambientComplexProj_mem_complexPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsComplex}) {x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K}
    (hx : x ∈ W.euclideanSpan) :
    ambientComplexProj w x ∈ (W.complexPlaceSpan w).restrictScalars ℝ := by
  refine (euclideanSpan_le_iff
    (U := ((W.complexPlaceSpan w).restrictScalars ℝ).comap (ambientComplexProj w))).2 ?_ hx
  intro v hv
  have heq :
      ambientComplexProj w
          (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) =
        WithLp.toLp 2 fun i ↦ w.val.embedding (v i) := by
    ext i
    rw [ambientComplexProj_apply, PiLp.toLp_apply, PiLp.toLp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact mixedEmbedding_apply_isComplex K (v i) w
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, heq]
  exact toLp_mem_complexPlaceSpan w hv

open scoped Classical in
private def toPlaceSpanProdLinear (W : Submodule K (ι → K)) :
    W.euclideanSpan →ₗ[ℝ] W.placeSpanProd :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ
    LinearMap.prod
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ LinearMap.pi fun w ↦
        ((ambientRealProj w).comp W.euclideanSpan.subtype).codRestrict (W.realPlaceSpan w)
          fun x ↦ ambientRealProj_mem_realPlaceSpan w x.property)
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ LinearMap.pi fun w ↦
        ((ambientComplexProj w).comp W.euclideanSpan.subtype).codRestrict
          ((W.complexPlaceSpan w).restrictScalars ℝ)
          fun x ↦ ambientComplexProj_mem_complexPlaceSpan w x.property)

open scoped Classical in
private theorem norm_toPlaceSpanProdLinear (W : Submodule K (ι → K)) (x : W.euclideanSpan) :
    ‖toPlaceSpanProdLinear W x‖ = ‖x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    ← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
  simp_rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  rw [Finset.sum_add_distrib]
  congr 1 <;>
    (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
     rw [PiLp.norm_sq_eq_of_L2]; rfl)

open scoped Classical in
/-- The canonical `ℝ`-linear isometric equivalence between `W.euclideanSpan` and the `L²` product
`W.placeSpanProd` of its local real and complex place spans. -/
def euclideanSpanEquivPlaceSpanProd (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗᵢ[ℝ] W.placeSpanProd := by
  let f : W.euclideanSpan →ₗᵢ[ℝ] W.placeSpanProd :=
    { toLinearMap := toPlaceSpanProdLinear W, norm_map' := norm_toPlaceSpanProdLinear W }
  exact LinearIsometryEquiv.ofSurjective f <|
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (W.finrank_euclideanSpan.trans W.finrank_placeSpanProd.symm)).1 f.injective

open scoped Classical in
/-- Real-place coordinates of `W.euclideanSpanEquivPlaceSpanProd x`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceSpanProd_fst_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((W.euclideanSpanEquivPlaceSpanProd x).fst w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w := by
  rw [euclideanSpanEquivPlaceSpanProd, LinearIsometryEquiv.coe_ofSurjective]; rfl

open scoped Classical in
/-- Complex-place coordinates of `W.euclideanSpanEquivPlaceSpanProd x`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceSpanProd_snd_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((W.euclideanSpanEquivPlaceSpanProd x).snd w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w := by
  rw [euclideanSpanEquivPlaceSpanProd, LinearIsometryEquiv.coe_ofSurjective]; rfl

end IsometricDecomposition

section Slices

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-! ### The sup-norm slice `W.supSlice` -/

private def supCoords (W : Submodule K (ι → K)) : W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦ evalMixed i).comp W.euclideanSpan.subtype

omit [Fintype ι] in
private theorem supCoords_injective (W : Submodule K (ι → K)) :
    Function.Injective (supCoords W) := fun _ _ h ↦ by
  ext1; ext1 i; exact (euclidean.toMixed K).injective (congrFun h i)

open scoped Classical in
private theorem setOf_supSlice_eq_preimage (W : Submodule K (ι → K)) :
    {x : W.euclideanSpan | ∀ (w : InfinitePlace K) (i : ι),
        normAtPlace w (euclidean.toMixed K
          ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} =
      supCoords W ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg zero_le_one, norm_eq_sup'_normAtPlace,
    Finset.sup'_le_iff, Finset.mem_univ, forall_true_left]
  exact forall_comm

open scoped Classical in
/-- The symmetric convex body in `W.euclideanSpan` consisting of points `x` whose local coordinates
satisfy `|x_i|_w ≤ 1` at every infinite place `w` and every coordinate `i`. -/
def supSlice (W : Submodule K (ι → K)) : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ (w : InfinitePlace K) (i : ι),
    normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1}
  convex' := by
    rw [setOf_supSlice_eq_preimage]; exact (convex_closedBall 0 1).linear_preimage (supCoords W)
  isCompact' := by
    rw [setOf_supSlice_eq_preimage]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (supCoords_injective W))).isCompact_preimage
      (isCompact_closedBall 0 1)
  nonempty' := ⟨0, by rw [setOf_supSlice_eq_preimage]; simp⟩

/-- Carrier of `W.supSlice`. -/
@[simp]
theorem coe_supSlice (W : Submodule K (ι → K)) :
    (W.supSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ (w : InfinitePlace K) (i : ι),
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} :=
  (rfl)

/-- Membership in `W.supSlice`. -/
@[simp]
theorem mem_supSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    x ∈ W.supSlice ↔ ∀ (w : InfinitePlace K) (i : ι),
      normAtPlace w
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1 :=
  Iff.rfl

/-- `W.supSlice` is symmetric about the origin. -/
theorem neg_mem_supSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    -x ∈ W.supSlice ↔ x ∈ W.supSlice := by
  classical
  simp only [← SetLike.mem_coe, coe_supSlice, setOf_supSlice_eq_preimage, mem_preimage, map_neg,
    mem_closedBall_zero_iff, norm_neg]

/-- `0` lies in the interior of `W.supSlice`. -/
theorem zero_mem_interior_supSlice (W : Submodule K (ι → K)) :
    (0 : W.euclideanSpan) ∈ interior (W.supSlice : Set W.euclideanSpan) := by
  classical
  rw [coe_supSlice, setOf_supSlice_eq_preimage]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage (supCoords W).continuous_of_finiteDimensional).mem_nhds (by simp))
    (preimage_mono ball_subset_closedBall)

/-- At every infinite place `w` and coordinate `i`, the local norm of `x ∈ W.euclideanSpan` is at
most `gauge W.supSlice x`. -/
theorem normAtPlace_le_gauge_supSlice {W : Submodule K (ι → K)} (x : W.euclideanSpan)
    (w : InfinitePlace K) (i : ι) :
    normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤
      gauge (W.supSlice : Set W.euclideanSpan) x := by
  classical
  rw [coe_supSlice, setOf_supSlice_eq_preimage, LinearMap.gauge_preimage,
    gauge_closedBall zero_le_one, div_one]
  exact (normAtPlace_le_norm w _).trans (norm_le_pi_norm (supCoords W x) i)

open scoped Classical in
private theorem measurePreserving_placeCoords (W : Submodule K (ι → K)) :
    MeasurePreserving
      (fun x : W.euclideanSpan ↦
        (WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).fst,
          WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).snd))
      volume (volume.prod volume) := by
  let _ : BorelSpace W.placeSpanProd := inferInstance
  let _ : MeasureSpace W.placeSpanProd := measureSpaceOfInnerProductSpace
  have h2 := WithLp.volume_preserving_ofLp
    (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w)
    (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
      (W.complexPlaceSpan w).restrictScalars ℝ)
  exact (((PiLp.volume_preserving_symm_measurableEquiv_toLp
      (fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w)).prod
    (PiLp.volume_preserving_symm_measurableEquiv_toLp fun w : {w : InfinitePlace K // w.IsComplex} ↦
      (W.complexPlaceSpan w).restrictScalars ℝ)).comp h2).comp
    (LinearIsometryEquiv.measurePreserving
      (E := W.euclideanSpan) (F := W.placeSpanProd) W.euclideanSpanEquivPlaceSpanProd)

/-- **Volume bound for `W.supSlice`.** Decomposing `W.supSlice` place by place and applying
Vaaler's cube-slicing theorem at real places and polydisc slicing at complex places bounds its
Euclidean volume below by
`2 ^ (nrRealPlaces K * finrank K W) * π ^ (nrComplexPlaces K * finrank K W)`. -/
theorem two_pow_mul_pi_pow_le_volume_real_supSlice (W : Submodule K (ι → K)) :
    (2 : ℝ) ^ (nrRealPlaces K * finrank K W) *
        Real.pi ^ (nrComplexPlaces K * finrank K W) ≤
      volume.real (W.supSlice : Set W.euclideanSpan) := by
  classical
  let SR (w : {w : InfinitePlace K // w.IsReal}) : Set (W.realPlaceSpan w) :=
    {u | ∀ i, |(u : EuclideanSpace ℝ ι) i| ≤ 1}
  let SC (w : {w : InfinitePlace K // w.IsComplex}) :
      Set ((W.complexPlaceSpan w).restrictScalars ℝ) :=
    {u | ∀ i, ‖(u : EuclideanSpace ℂ ι) i‖ ≤ 1}
  have hSR (w) : MeasurableSet (SR w) := by
    have hSR_eq :
        SR w = ⋂ i : ι, (fun u : W.realPlaceSpan w ↦ |(u : EuclideanSpace ℝ ι) i|) ⁻¹' Iic 1 := by
      ext; simp [SR]
    rw [hSR_eq]
    exact .iInter fun _ ↦ measurableSet_Iic.preimage (by fun_prop)
  have hSC (w) : MeasurableSet (SC w) := by
    have hSC_eq :
        SC w = ⋂ i : ι, (fun u : (W.complexPlaceSpan w).restrictScalars ℝ ↦
          ‖(u : EuclideanSpace ℂ ι) i‖) ⁻¹' Iic 1 := by
      ext; simp [SC]
    rw [hSC_eq]
    exact .iInter fun _ ↦ measurableSet_Iic.preimage (by fun_prop)
  have hpre : (W.supSlice : Set W.euclideanSpan) =
      (fun x : W.euclideanSpan ↦
        (WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).fst,
          WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).snd)) ⁻¹'
        ((univ.pi SR) ×ˢ (univ.pi SC)) := by
    ext x
    simp only [coe_supSlice, mem_ofPred_eq, mem_preimage, Set.mem_prod, mem_univ_pi, SR, SC,
      coe_euclideanSpanEquivPlaceSpanProd_fst_apply, coe_euclideanSpanEquivPlaceSpanProd_snd_apply]
    refine ⟨fun h ↦ ⟨fun w i ↦ by simpa [normAtPlace_apply_of_isReal w.property] using h w.val i,
      fun w i ↦ by simpa [normAtPlace_apply_of_isComplex w.property] using h w.val i⟩,
      fun ⟨hr, hc⟩ w i ↦ ?_⟩
    by_cases hw : w.IsReal
    · simpa [normAtPlace_apply_of_isReal hw] using hr ⟨w, hw⟩ i
    · have hwc := not_isReal_iff_isComplex.mp hw
      simpa [normAtPlace_apply_of_isComplex hwc] using hc ⟨w, hwc⟩ i
  have hvol : volume (W.supSlice : Set W.euclideanSpan) =
      (∏ w, volume (SR w)) * ∏ w, volume (SC w) := by
    rw [hpre, (measurePreserving_placeCoords W).measure_preimage
      ((MeasurableSet.univ_pi hSR).prod (MeasurableSet.univ_pi hSC)).nullMeasurableSet,
      Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  have hle_enn :
      ENNReal.ofReal ((2 : ℝ) ^ (nrRealPlaces K * finrank K W) *
        Real.pi ^ (nrComplexPlaces K * finrank K W)) ≤
        volume (W.supSlice : Set W.euclideanSpan) := by
    rw [hvol, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm (nrRealPlaces K),
      mul_comm (nrComplexPlaces K), pow_mul, pow_mul]
    refine mul_le_mul' ?_ ?_
    · rw [nrRealPlaces, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod fun w _ ↦ by
        simpa [SR, finrank_realPlaceSpan] using
          (W.realPlaceSpan w).two_pow_finrank_le_volume_setOf_forall_abs_le_one
    · rw [nrComplexPlaces, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod fun w _ ↦ by
        simpa [SC, finrank_complexPlaceSpan] using
          (W.complexPlaceSpan w).pi_pow_finrank_le_volume_setOf_forall_norm_le_one
  rw [measureReal_def, ← ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg zero_le_two _) (pow_nonneg Real.pi_pos.le _))]
  exact ENNReal.toReal_mono W.supSlice.isCompact.measure_lt_top.ne hle_enn

/-! ### The local Euclidean unit-ball slice `W.euclideanBallSlice` -/

open scoped Classical in
private def ballCoords (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗ[ℝ]
      ((∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w) ×
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          (W.complexPlaceSpan w).restrictScalars ℝ)) :=
  W.euclideanSpanEquivPlaceSpanProd.toLinearEquiv.trans <|
    (WithLp.linearEquiv 2 ℝ _).trans <|
      (WithLp.linearEquiv 2 ℝ _).prodCongr (WithLp.linearEquiv 2 ℝ _)

open scoped Classical in
private theorem ballCoords_fst (W : Submodule K (ι → K)) (x : W.euclideanSpan) :
    (ballCoords W x).1 = WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).fst := by
  simp [ballCoords]

open scoped Classical in
private theorem ballCoords_snd (W : Submodule K (ι → K)) (x : W.euclideanSpan) :
    (ballCoords W x).2 = WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).snd := by
  simp [ballCoords]

open scoped Classical in
private theorem norm_sq_placeSpanProd_fst (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ‖(W.euclideanSpanEquivPlaceSpanProd x).fst w‖ ^ 2 =
      ∑ i : ι, normAtPlace w.val
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_euclideanSpanEquivPlaceSpanProd_fst_apply, normAtPlace_apply_of_isReal w.property,
    Real.norm_eq_abs]

open scoped Classical in
private theorem norm_sq_placeSpanProd_snd (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ‖(W.euclideanSpanEquivPlaceSpanProd x).snd w‖ ^ 2 =
      ∑ i : ι, normAtPlace w.val
        (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coe_euclideanSpanEquivPlaceSpanProd_snd_apply, normAtPlace_apply_of_isComplex w.property]

open scoped Classical in
private theorem setOf_euclideanBallSlice_eq_preimage (W : Submodule K (ι → K)) :
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        ∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1} =
      (ballCoords W).toLinearMap ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
    pi_norm_le_iff_of_nonneg zero_le_one, LinearEquiv.coe_toLinearMap, ballCoords_fst,
    ballCoords_snd]
  simp_rw [← sq_le_one_iff₀ (norm_nonneg _), norm_sq_placeSpanProd_fst, norm_sq_placeSpanProd_snd]
  exact ⟨fun h ↦ ⟨fun w ↦ h w.val, fun w ↦ h w.val⟩, fun ⟨h₁, h₂⟩ w ↦
    if hw : w.IsReal then h₁ ⟨w, hw⟩ else h₂ ⟨w, not_isReal_iff_isComplex.mp hw⟩⟩

open scoped Classical in
/-- The symmetric convex body in `W.euclideanSpan` consisting of points `x` whose local Euclidean
norms satisfy `∑ i, |x_i|_w ^ 2 ≤ 1` at every infinite place `w`. -/
def euclideanBallSlice (W : Submodule K (ι → K)) : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ w : InfinitePlace K,
    ∑ i : ι,
      normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤
        1}
  convex' := by
    rw [setOf_euclideanBallSlice_eq_preimage]
    exact (convex_closedBall 0 1).linear_preimage (ballCoords W).toLinearMap
  isCompact' := by
    rw [setOf_euclideanBallSlice_eq_preimage]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (ballCoords W).injective)).isCompact_preimage
      (isCompact_closedBall 0 1)
  nonempty' := ⟨0, by rw [setOf_euclideanBallSlice_eq_preimage]; simp⟩

/-- Carrier of `W.euclideanBallSlice`. -/
@[simp]
theorem coe_euclideanBallSlice (W : Submodule K (ι → K)) :
    (W.euclideanBallSlice : Set W.euclideanSpan) =
      {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        ∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1} :=
  (rfl)

/-- Membership in `W.euclideanBallSlice`. -/
@[simp]
theorem mem_euclideanBallSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    x ∈ W.euclideanBallSlice ↔ ∀ w : InfinitePlace K,
      ∑ i : ι,
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1 :=
  Iff.rfl

/-- `W.euclideanBallSlice` is symmetric about the origin. -/
theorem neg_mem_euclideanBallSlice {W : Submodule K (ι → K)} {x : W.euclideanSpan} :
    -x ∈ W.euclideanBallSlice ↔ x ∈ W.euclideanBallSlice := by
  classical
  simp only [← SetLike.mem_coe, coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage,
    mem_preimage, map_neg, mem_closedBall_zero_iff, norm_neg]

/-- `0` lies in the interior of `W.euclideanBallSlice`. -/
theorem zero_mem_interior_euclideanBallSlice (W : Submodule K (ι → K)) :
    (0 : W.euclideanSpan) ∈ interior (W.euclideanBallSlice : Set W.euclideanSpan) := by
  classical
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((isOpen_ball.preimage (ballCoords W).toLinearMap.continuous_of_finiteDimensional).mem_nhds
      (by simp))
    (preimage_mono ball_subset_closedBall)

/-- At every infinite place `w`, the squared local Euclidean norm of `x ∈ W.euclideanSpan` is at
most `(gauge W.euclideanBallSlice x) ^ 2`. -/
theorem sum_normAtPlace_sq_le_gauge_euclideanBallSlice_sq {W : Submodule K (ι → K)}
    (x : W.euclideanSpan) (w : InfinitePlace K) :
    (∑ i : ι,
        normAtPlace w
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) ≤
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) x ^ 2 := by
  classical
  rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage, LinearMap.gauge_preimage,
    gauge_closedBall zero_le_one, div_one]
  by_cases hw : w.IsReal
  · rw [← norm_sq_placeSpanProd_fst W x ⟨w, hw⟩]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_le_pi_norm (ballCoords W x).1 ⟨w, hw⟩).trans (le_max_left _ _)) 2
  · have hwc := not_isReal_iff_isComplex.mp hw
    rw [← norm_sq_placeSpanProd_snd W x ⟨w, hwc⟩]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_le_pi_norm (ballCoords W x).2 ⟨w, hwc⟩).trans (le_max_right _ _)) 2

/-- **Exact volume of `W.euclideanBallSlice`.** Decomposing `W.euclideanBallSlice` across the `r₁`
real and `r₂` complex places expresses its Euclidean volume as the product of unit-ball volumes in
dimensions `finrank K W` and `2 * finrank K W`. -/
theorem volume_real_euclideanBallSlice (W : Submodule K (ι → K)) :
    volume.real (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^
          nrComplexPlaces K := by
  classical
  have hpre : (W.euclideanBallSlice : Set W.euclideanSpan) =
      (fun x : W.euclideanSpan ↦
        (WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).fst,
          WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).snd)) ⁻¹'
        ((univ.pi fun w : {w : InfinitePlace K // w.IsReal} ↦
            closedBall (0 : W.realPlaceSpan w) 1) ×ˢ
          (univ.pi fun w : {w : InfinitePlace K // w.IsComplex} ↦
            closedBall (0 : (W.complexPlaceSpan w).restrictScalars ℝ) 1)) := by
    ext x
    rw [coe_euclideanBallSlice, setOf_euclideanBallSlice_eq_preimage, mem_preimage,
      mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg zero_le_one,
      pi_norm_le_iff_of_nonneg zero_le_one, mem_preimage, Set.mem_prod, mem_univ_pi, mem_univ_pi]
    simp only [mem_closedBall_zero_iff, LinearEquiv.coe_toLinearMap, ballCoords_fst, ballCoords_snd]
  have hm := (MeasurableSet.univ_pi fun w : {w : InfinitePlace K // w.IsReal} ↦
      measurableSet_closedBall (x := (0 : W.realPlaceSpan w)) (ε := 1)).prod
    (MeasurableSet.univ_pi fun w : {w : InfinitePlace K // w.IsComplex} ↦
      measurableSet_closedBall (x := (0 : (W.complexPlaceSpan w).restrictScalars ℝ)) (ε := 1))
  have hvol : volume (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^ nrComplexPlaces K := by
    rw [hpre, (measurePreserving_placeCoords W).measure_preimage hm.nullMeasurableSet,
      Measure.prod_prod, volume_pi_pi, volume_pi_pi]
    congr 1
    · exact (Finset.prod_congr rfl fun w _ ↦
        (Measure.addHaar_unitClosedBall_eq_addHaar_unitBall _).trans
          (volume_ball_eq_of_finrank_eq
            (by rw [W.finrank_realPlaceSpan w, finrank_euclideanSpace_fin]) 0
            (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)).trans (by simp)
    · exact (Finset.prod_congr rfl fun w _ ↦
        (Measure.addHaar_unitClosedBall_eq_addHaar_unitBall _).trans
          (volume_ball_eq_of_finrank_eq
            (by rw [W.finrank_restrictScalars_complexPlaceSpan w, finrank_euclideanSpace_fin]) 0
            (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)).trans (by simp)
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ← measureReal_def, ← measureReal_def]

end Slices

end Submodule

end
