/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Gauge.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SubspaceLattice

import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.LinearAlgebra.Basis.Submodule
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
the `L²` product `W.placeSpanProd` of these local subspaces is surjective, giving a canonical
linear isometric equivalence `W.euclideanSpanEquivPlaceSpanProd`.

Transporting product bodies across `W.euclideanSpanEquivPlaceSpanProd` yields two origin-symmetric
convex bodies in `W.euclideanSpan` whose gauges bound the projective sup height and Euclidean height
of integral points of `W`:

* `W.supSlice`: the points `x ∈ W.euclideanSpan` with `|x_i|_w ≤ 1` for all `w` and `i`. Under
  `W.euclideanSpanEquivPlaceSpanProd`, it factors into central cube slices at real places and
  central polydisc slices at complex places, so Vaaler's theorem and its complex counterpart bound
  its volume below by `2 ^ (r₁ * k) * π ^ (r₂ * k)`.
* `W.euclideanBallSlice`: the points `x ∈ W.euclideanSpan` with `∑ i, |x_i|_w ^ 2 ≤ 1` for all `w`.
  Under `W.euclideanSpanEquivPlaceSpanProd`, it factors into unit Euclidean balls of dimensions `k`
  and `2 * k`, so its volume equals `ω_k ^ r₁ * ω_{2k} ^ r₂`.

## Main definitions

* `Submodule.realPlaceSpan W w`, `Submodule.complexPlaceSpan W w`: the local `ℝ`- and `ℂ`-spans of
  `W` in `EuclideanSpace ℝ ι` and `EuclideanSpace ℂ ι` at real and complex places `w`.
* `Submodule.placeSpanProd W`: the `L²` product of the local place spans across all infinite places.
* `Submodule.euclideanSpanEquivPlaceSpanProd W`: the linear isometric equivalence
  `W.euclideanSpan ≃ₗᵢ[ℝ] W.placeSpanProd`.
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
open scoped BigOperators ENNReal Pointwise

namespace Submodule

section PlaceSpan

variable {K : Type*} [Field K] {ι : Type*}

/-- The `ℝ`-span in `EuclideanSpace ℝ ι` of a `K`-subspace `W` of `ι → K` along a real infinite
place `w`. -/
def realPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsReal}) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) '' W)

/-- The `ℂ`-span in `EuclideanSpace ℂ ι` of a `K`-subspace `W` of `ι → K` along a complex infinite
place `w`. -/
def complexPlaceSpan (W : Submodule K (ι → K)) (w : {w : InfinitePlace K // w.IsComplex}) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  span ℂ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) '' W)

/-- Every vector of `W` embeds into `W.realPlaceSpan w`. -/
theorem toLp_mem_realPlaceSpan {W : Submodule K (ι → K)} (w : {w : InfinitePlace K // w.IsReal})
    {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ embedding_of_isReal w.2 (v i)) ∈ W.realPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- Every vector of `W` embeds into `W.complexPlaceSpan w`. -/
theorem toLp_mem_complexPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsComplex}) {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ w.1.embedding (v i)) ∈ W.complexPlaceSpan w :=
  subset_span ⟨v, hv, rfl⟩

/-- The real-place span of the zero subspace is zero. -/
@[simp]
theorem realPlaceSpan_bot (w : {w : InfinitePlace K // w.IsReal}) :
    (⊥ : Submodule K (ι → K)).realPlaceSpan w = ⊥ := by
  rw [realPlaceSpan, bot_coe, image_singleton, span_singleton_eq_bot]
  ext1 i
  simp

/-- The complex-place span of the zero subspace is zero. -/
@[simp]
theorem complexPlaceSpan_bot (w : {w : InfinitePlace K // w.IsComplex}) :
    (⊥ : Submodule K (ι → K)).complexPlaceSpan w = ⊥ := by
  rw [complexPlaceSpan, bot_coe, image_singleton, span_singleton_eq_bot]
  ext1 i
  simp

/-- Extending scalars of a `K`-subspace `W` of `ι → K` to a field `E` along a ring homomorphism
`φ : K →+* E` preserves the dimension in `EuclideanSpace E ι`. -/
private theorem finrank_span_toLp_map [Finite ι] {E : Type*} [RCLike E]
    (W : Submodule K (ι → K)) (φ : K →+* E) :
    finrank E (span E ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ φ (v i)) '' W)) = finrank K W := by
  cases nonempty_fintype ι
  let _ : Algebra K E := φ.toAlgebra
  let e := (WithLp.linearEquiv 2 E (ι → E)).symm
  let f : (ι → K) →ₗ[K] (ι → E) :=
    { toFun v i := algebraMap K E (v i)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp [Algebra.smul_def] }
  let b := Module.finBasis K W
  have himg : (fun v : ι → K ↦ WithLp.toLp 2 fun i ↦ φ (v i)) '' (W : Set (ι → K)) =
      e.toLinearMap '' (f '' (W : Set (ι → K))) := by
    ext x
    simp only [mem_image, exists_exists_and_eq_and]
    rfl
  have hli : LinearIndependent E (fun j ↦ f (b j : ι → K)) := by
    have hcomp : (fun j ↦ f (b j : ι → K)) = fun j i ↦ algebraMap K E ((b j : ι → K) i) := rfl
    rw [hcomp]
    exact linearIndependent_algebraMap_comp_iff.2 b.linearIndependent_coe_basis
  rw [himg, ← Submodule.map_span, LinearEquiv.finrank_map_eq, b.span_image f,
    finrank_span_eq_card hli, Fintype.card_fin]

/-- At each real place `w`, `W.realPlaceSpan w` has real dimension `finrank K W`. -/
@[simp]
theorem finrank_realPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsReal}) :
    finrank ℝ (W.realPlaceSpan w) = finrank K W :=
  finrank_span_toLp_map W (embedding_of_isReal w.2)

/-- At each complex place `w`, `W.complexPlaceSpan w` has complex dimension `finrank K W`. -/
@[simp]
theorem finrank_complexPlaceSpan [Finite ι] (W : Submodule K (ι → K))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    finrank ℂ (W.complexPlaceSpan w) = finrank K W :=
  finrank_span_toLp_map W w.1.embedding

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
@[simp]
theorem finrank_placeSpanProd [NumberField K] [Finite ι] (W : Submodule K (ι → K)) :
    finrank ℝ W.placeSpanProd = finrank ℚ K * finrank K W := by
  cases nonempty_fintype ι
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _), Module.finrank_prod,
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ _),
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [finrank_realPlaceSpan, finrank_restrictScalars_complexPlaceSpan, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  calc nrRealPlaces K * finrank K W + nrComplexPlaces K * (2 * finrank K W)
      = (nrRealPlaces K + 2 * nrComplexPlaces K) * finrank K W := by ring
    _ = finrank ℚ K * finrank K W := by rw [card_add_two_mul_card_eq_rank]

end PlaceSpan

section IsometricDecomposition

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Coordinate evaluation `(PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K` at
`i : ι`. -/
private def evalMixed (i : ι) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K :=
  (euclidean.toMixed K).toLinearMap ∘ₗ
    (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap

/-- Real projection of the ambient Euclidean Minkowski space to `EuclideanSpace ℝ ι` at a real
place `w`. -/
private def ambientRealProj (w : {w : InfinitePlace K // w.IsReal}) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i ↦
      (LinearMap.proj w).comp
        ((LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
            ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp
          (evalMixed i))

/-- Complex projection of the ambient Euclidean Minkowski space to `EuclideanSpace ℂ ι` at a
complex place `w`. -/
private def ambientComplexProj (w : {w : InfinitePlace K // w.IsComplex}) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] EuclideanSpace ℂ ι :=
  ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap.restrictScalars ℝ) ∘ₗ
    LinearMap.pi fun i ↦
      (LinearMap.proj w).comp
        ((LinearMap.snd ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
            ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp
          (evalMixed i))

omit [Fintype ι] in
private theorem ambientRealProj_mem_realPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsReal}) {x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K}
    (hx : x ∈ W.euclideanSpan) :
    ambientRealProj w x ∈ W.realPlaceSpan w := by
  refine (euclideanSpan_le_iff (U := (W.realPlaceSpan w).comap (ambientRealProj w))).2 ?_ hx
  intro v hv
  change WithLp.toLp 2 (fun i ↦ (euclidean.toMixed K
    ((euclidean.toMixed K).symm (mixedEmbedding K (v i)))).1 w) ∈ W.realPlaceSpan w
  simp_rw [ContinuousLinearEquiv.apply_symm_apply]
  exact toLp_mem_realPlaceSpan w hv

omit [Fintype ι] in
private theorem ambientComplexProj_mem_complexPlaceSpan {W : Submodule K (ι → K)}
    (w : {w : InfinitePlace K // w.IsComplex}) {x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K}
    (hx : x ∈ W.euclideanSpan) :
    ambientComplexProj w x ∈ (W.complexPlaceSpan w).restrictScalars ℝ := by
  refine (euclideanSpan_le_iff
    (U := ((W.complexPlaceSpan w).restrictScalars ℝ).comap (ambientComplexProj w))).2 ?_ hx
  intro v hv
  change WithLp.toLp 2 (fun i ↦ (euclidean.toMixed K
    ((euclidean.toMixed K).symm (mixedEmbedding K (v i)))).2 w) ∈ W.complexPlaceSpan w
  simp_rw [ContinuousLinearEquiv.apply_symm_apply]
  exact toLp_mem_complexPlaceSpan w hv

open scoped Classical in
/-- The `ℝ`-linear map regrouping coordinates of `W.euclideanSpan` by infinite place. -/
private def toPlaceSpanProdLinear (W : Submodule K (ι → K)) :
    W.euclideanSpan →ₗ[ℝ] W.placeSpanProd :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ
    LinearMap.prod
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ
        LinearMap.pi fun w ↦
          ((ambientRealProj w).comp W.euclideanSpan.subtype).codRestrict (W.realPlaceSpan w)
            fun x ↦ ambientRealProj_mem_realPlaceSpan w x.2)
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ
        LinearMap.pi fun w ↦
          ((ambientComplexProj w).comp W.euclideanSpan.subtype).codRestrict
            ((W.complexPlaceSpan w).restrictScalars ℝ)
            fun x ↦ ambientComplexProj_mem_complexPlaceSpan w x.2)

open scoped Classical in
omit [Fintype ι] in
private theorem coe_toPlaceSpanProdLinear_fst_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((toPlaceSpanProdLinear W x).fst w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w :=
  rfl

open scoped Classical in
omit [Fintype ι] in
private theorem coe_toPlaceSpanProdLinear_snd_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((toPlaceSpanProdLinear W x).snd w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w :=
  rfl

open scoped Classical in
private theorem norm_toPlaceSpanProdLinear (W : Submodule K (ι → K)) (x : W.euclideanSpan) :
    ‖toPlaceSpanProdLinear W x‖ = ‖x‖ := by
  have hsq : ‖toPlaceSpanProdLinear W x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      ← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
    simp_rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
      coe_toPlaceSpanProdLinear_fst_apply, coe_toPlaceSpanProdLinear_snd_apply]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PiLp.norm_sq_eq_of_L2]
      rfl
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PiLp.norm_sq_eq_of_L2]
      rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

open scoped Classical in
/-- The canonical `ℝ`-linear isometric equivalence between `W.euclideanSpan` and the `L²` product
`W.placeSpanProd` of its local real and complex place spans. -/
def euclideanSpanEquivPlaceSpanProd (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗᵢ[ℝ] W.placeSpanProd := by
  let f : W.euclideanSpan →ₗᵢ[ℝ] W.placeSpanProd :=
    { toLinearMap := toPlaceSpanProdLinear W
      norm_map' := norm_toPlaceSpanProdLinear W }
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((W.finrank_euclideanSpan).trans (W.finrank_placeSpanProd).symm)).1 f.injective
  exact LinearIsometryEquiv.ofSurjective f hsurj

open scoped Classical in
/-- Real-place coordinates of `W.euclideanSpanEquivPlaceSpanProd x`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceSpanProd_fst_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsReal}) (i : ι) :
    (((W.euclideanSpanEquivPlaceSpanProd x).fst w : W.realPlaceSpan w) : EuclideanSpace ℝ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).1 w := by
  rw [euclideanSpanEquivPlaceSpanProd, LinearIsometryEquiv.coe_ofSurjective]
  rfl

open scoped Classical in
/-- Complex-place coordinates of `W.euclideanSpanEquivPlaceSpanProd x`. -/
@[simp]
theorem coe_euclideanSpanEquivPlaceSpanProd_snd_apply (W : Submodule K (ι → K))
    (x : W.euclideanSpan) (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) :
    (((W.euclideanSpanEquivPlaceSpanProd x).snd w :
        (W.complexPlaceSpan w).restrictScalars ℝ) : EuclideanSpace ℂ ι) i =
      (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)).2 w := by
  rw [euclideanSpanEquivPlaceSpanProd, LinearIsometryEquiv.coe_ofSurjective]
  rfl

end IsometricDecomposition

section Slices

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-! ### The sup-norm slice `W.supSlice` -/

/-- Coordinate map sending `x ∈ W.euclideanSpan` to its tuple of `mixedSpace K` coordinates. -/
private def supCoords (W : Submodule K (ι → K)) : W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦ evalMixed i).comp W.euclideanSpan.subtype

omit [Fintype ι] in
private theorem supCoords_apply (W : Submodule K (ι → K)) (x : W.euclideanSpan) (i : ι) :
    supCoords W x i =
      euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) :=
  rfl

omit [Fintype ι] in
private theorem supCoords_injective (W : Submodule K (ι → K)) :
    Function.Injective (supCoords W) := by
  intro x y h
  ext1; ext1 i
  exact (euclidean.toMixed K).injective (congrFun h i)

open scoped Classical in
private theorem setOf_supSlice_eq_preimage (W : Submodule K (ι → K)) :
    {x : W.euclideanSpan | ∀ (w : InfinitePlace K) (i : ι),
        normAtPlace w (euclidean.toMixed K
          ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1} =
      supCoords W ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg zero_le_one, supCoords_apply, norm_eq_sup'_normAtPlace,
    Finset.sup'_le_iff, Finset.mem_univ, forall_true_left]
  exact forall_comm

open scoped Classical in
/-- The symmetric convex body in `W.euclideanSpan` consisting of points `x` whose local coordinates
satisfy `|x_i|_w ≤ 1` at every infinite place `w` and every coordinate `i`. -/
def supSlice (W : Submodule K (ι → K)) : ConvexBody W.euclideanSpan where
  carrier := {x : W.euclideanSpan | ∀ (w : InfinitePlace K) (i : ι),
    normAtPlace w (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ≤ 1}
  convex' := by
    rw [setOf_supSlice_eq_preimage]
    exact (convex_closedBall 0 1).linear_preimage (supCoords W)
  isCompact' := by
    rw [setOf_supSlice_eq_preimage]
    exact (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (supCoords_injective W))).isCompact_preimage
      (isCompact_closedBall 0 1)
  nonempty' := ⟨0, by
    rw [setOf_supSlice_eq_preimage]
    simp⟩

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
  have h1 := LinearIsometryEquiv.measurePreserving
    (E := W.euclideanSpan) (F := W.placeSpanProd) W.euclideanSpanEquivPlaceSpanProd
  have h2 := WithLp.volume_preserving_ofLp
    (PiLp 2 fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w)
    (PiLp 2 fun w : {w : InfinitePlace K // w.IsComplex} ↦
      (W.complexPlaceSpan w).restrictScalars ℝ)
  have h3 := (PiLp.volume_preserving_symm_measurableEquiv_toLp
    (fun w : {w : InfinitePlace K // w.IsReal} ↦ W.realPlaceSpan w)).prod
    (PiLp.volume_preserving_symm_measurableEquiv_toLp
      (fun w : {w : InfinitePlace K // w.IsComplex} ↦ (W.complexPlaceSpan w).restrictScalars ℝ))
  exact (h3.comp h2).comp h1

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
    have : SR w =
        ⋂ i : ι, (fun u : W.realPlaceSpan w ↦ |(u : EuclideanSpace ℝ ι) i|) ⁻¹' Iic 1 := by
      ext u; simp [SR]
    rw [this]
    exact MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (by fun_prop)
  have hSC (w) : MeasurableSet (SC w) := by
    have : SC w = ⋂ i : ι,
        (fun u : (W.complexPlaceSpan w).restrictScalars ℝ ↦
          ‖(u : EuclideanSpace ℂ ι) i‖) ⁻¹' Iic 1 := by
      ext u; simp [SC]
    rw [this]
    exact MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (by fun_prop)
  have hpre : (W.supSlice : Set W.euclideanSpan) =
      (fun x : W.euclideanSpan ↦
        (WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).fst,
          WithLp.ofLp (W.euclideanSpanEquivPlaceSpanProd x).snd)) ⁻¹'
        ((univ.pi SR) ×ˢ (univ.pi SC)) := by
    ext x
    rw [coe_supSlice, mem_ofPred_eq, mem_preimage, Set.mem_prod, mem_univ_pi, mem_univ_pi]
    dsimp only [SR, SC]
    simp only [mem_ofPred_eq, coe_euclideanSpanEquivPlaceSpanProd_fst_apply,
      coe_euclideanSpanEquivPlaceSpanProd_snd_apply]
    refine ⟨fun h ↦ ⟨fun w i ↦ ?_, fun w i ↦ ?_⟩, fun ⟨hr, hc⟩ w i ↦ ?_⟩
    · simpa [normAtPlace_apply_of_isReal w.2] using h w.1 i
    · simpa [normAtPlace_apply_of_isComplex w.2] using h w.1 i
    · by_cases hw : w.IsReal
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
    · rw [show nrRealPlaces K = (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).card from
        Finset.card_univ.symm, ← Finset.prod_const]
      exact Finset.prod_le_prod fun w _ ↦ by
        simpa [SR, finrank_realPlaceSpan] using
          (W.realPlaceSpan w).two_pow_finrank_le_volume_setOf_forall_abs_le_one
    · rw [show nrComplexPlaces K =
        (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card from
        Finset.card_univ.symm, ← Finset.prod_const]
      exact Finset.prod_le_prod fun w _ ↦ by
        simpa [SC, finrank_complexPlaceSpan] using
          (W.complexPlaceSpan w).pi_pow_finrank_le_volume_setOf_forall_norm_le_one
  rw [measureReal_def, ← ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg zero_le_two _) (pow_nonneg Real.pi_pos.le _))]
  exact ENNReal.toReal_mono W.supSlice.isCompact.measure_lt_top.ne hle_enn

/-! ### The local Euclidean unit-ball slice `W.euclideanBallSlice` -/

open scoped Classical in
/-- Linear equivalence sending `x ∈ W.euclideanSpan` to the `L∞` product of its local Euclidean
components. -/
private def ballCoords (W : Submodule K (ι → K)) :
    W.euclideanSpan ≃ₗ[ℝ]
      ((∀ w : {w : InfinitePlace K // w.IsReal}, W.realPlaceSpan w) ×
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          (W.complexPlaceSpan w).restrictScalars ℝ)) :=
  W.euclideanSpanEquivPlaceSpanProd.toLinearEquiv.trans <|
    (WithLp.linearEquiv 2 ℝ _).trans <|
      (WithLp.linearEquiv 2 ℝ _).prodCongr (WithLp.linearEquiv 2 ℝ _)

open scoped Classical in
private theorem ballCoords_fst_apply (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (ballCoords W x).1 w = (W.euclideanSpanEquivPlaceSpanProd x).fst w :=
  rfl

open scoped Classical in
private theorem ballCoords_snd_apply (W : Submodule K (ι → K)) (x : W.euclideanSpan)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (ballCoords W x).2 w = (W.euclideanSpanEquivPlaceSpanProd x).snd w :=
  rfl

open scoped Classical in
private theorem setOf_euclideanBallSlice_eq_preimage (W : Submodule K (ι → K)) :
    {x : W.euclideanSpan | ∀ w : InfinitePlace K,
        ∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1} =
      (ballCoords W).toLinearMap ⁻¹' closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
    pi_norm_le_iff_of_nonneg zero_le_one, LinearEquiv.coe_toLinearMap, ballCoords_fst_apply,
    ballCoords_snd_apply]
  have hr (w : {w : InfinitePlace K // w.IsReal}) :
      ‖(W.euclideanSpanEquivPlaceSpanProd x).fst w‖ ≤ 1 ↔
        ∑ i : ι, normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1 := by
    rw [← sq_le_one_iff₀ (norm_nonneg _), ← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
    refine eq_iff_iff.mp (congrArg (· ≤ 1) (Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [coe_euclideanSpanEquivPlaceSpanProd_fst_apply, normAtPlace_apply_of_isReal w.2,
      Real.norm_eq_abs]
  have hc (w : {w : InfinitePlace K // w.IsComplex}) :
      ‖(W.euclideanSpanEquivPlaceSpanProd x).snd w‖ ≤ 1 ↔
        ∑ i : ι, normAtPlace w.1
          (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2 ≤ 1 := by
    rw [← sq_le_one_iff₀ (norm_nonneg _), ← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
    refine eq_iff_iff.mp (congrArg (· ≤ 1) (Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [coe_euclideanSpanEquivPlaceSpanProd_snd_apply, normAtPlace_apply_of_isComplex w.2]
  simp_rw [hr, hc]
  refine ⟨fun h ↦ ⟨fun w ↦ h w.1, fun w ↦ h w.1⟩, fun ⟨h₁, h₂⟩ w ↦ ?_⟩
  by_cases hw : w.IsReal
  · exact h₁ ⟨w, hw⟩
  · exact h₂ ⟨w, not_isReal_iff_isComplex.mp hw⟩

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
  nonempty' := ⟨0, by
    rw [setOf_euclideanBallSlice_eq_preimage]
    simp⟩

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
  · have hsum :
        (∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) =
          ‖(W.euclideanSpanEquivPlaceSpanProd x).fst ⟨w, hw⟩‖ ^ 2 := by
      rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [coe_euclideanSpanEquivPlaceSpanProd_fst_apply, normAtPlace_apply_of_isReal hw,
        Real.norm_eq_abs]
    rw [hsum]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_le_pi_norm (ballCoords W x).1 ⟨w, hw⟩).trans (le_max_left _ _)) 2
  · have hwc := not_isReal_iff_isComplex.mp hw
    have hsum :
        (∑ i : ι,
          normAtPlace w
            (euclidean.toMixed K ((x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) ^ 2) =
          ‖(W.euclideanSpanEquivPlaceSpanProd x).snd ⟨w, hwc⟩‖ ^ 2 := by
      rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [coe_euclideanSpanEquivPlaceSpanProd_snd_apply, normAtPlace_apply_of_isComplex hwc]
    rw [hsum]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_le_pi_norm (ballCoords W x).2 ⟨w, hwc⟩).trans (le_max_right _ _)) 2

/-- Closed unit balls in any two real inner product spaces of the same dimension `m` have volume
equal to `volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)`, including `m = 0`. -/
private theorem volume_closedBall_one_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (hm : finrank ℝ E = m) :
    volume (closedBall (0 : E) 1) = volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  rcases m.eq_zero_or_pos with rfl | hm_pos
  · have : Subsingleton E := finrank_zero_iff.mp hm
    rw [volume_eq_one_of_subsingleton (nonempty_closedBall.2 zero_le_one),
      volume_eq_one_of_subsingleton (nonempty_ball.2 one_pos)]
  · let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hm)).repr
    have he := e.measurePreserving
    have hpre : closedBall (0 : E) 1 = e ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      ext x; simp
    have : Nontrivial (EuclideanSpace ℝ (Fin m)) := by
      rw [← finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]
      exact hm_pos
    rw [hpre, he.measure_preimage measurableSet_closedBall.nullMeasurableSet,
      Measure.addHaar_closedBall_eq_addHaar_ball]

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
    simp only [mem_closedBall_zero_iff, LinearEquiv.coe_toLinearMap, ballCoords_fst_apply,
      ballCoords_snd_apply]
  have hm := (MeasurableSet.univ_pi fun w : {w : InfinitePlace K // w.IsReal} ↦
      measurableSet_closedBall (x := (0 : W.realPlaceSpan w)) (ε := 1)).prod
    (MeasurableSet.univ_pi fun w : {w : InfinitePlace K // w.IsComplex} ↦
      measurableSet_closedBall
        (x := (0 : (W.complexPlaceSpan w).restrictScalars ℝ)) (ε := 1))
  have hvol : volume (W.euclideanBallSlice : Set W.euclideanSpan) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1) ^ nrRealPlaces K *
        volume (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1) ^ nrComplexPlaces K := by
    rw [hpre, (measurePreserving_placeCoords W).measure_preimage hm.nullMeasurableSet,
      Measure.prod_prod, volume_pi_pi, volume_pi_pi]
    congr 1
    · exact (Finset.prod_congr rfl fun w _ ↦
        volume_closedBall_one_eq (W.finrank_realPlaceSpan w)).trans
          (by rw [Finset.prod_const, Finset.card_univ])
    · exact (Finset.prod_congr rfl fun w _ ↦
        volume_closedBall_one_eq (W.finrank_restrictScalars_complexPlaceSpan w)).trans
          (by rw [Finset.prod_const, Finset.card_univ])
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ← measureReal_def, ← measureReal_def]

end Slices

end Submodule

end
