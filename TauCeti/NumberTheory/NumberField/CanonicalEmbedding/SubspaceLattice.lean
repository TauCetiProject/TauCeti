/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Rat
public import TauCeti.NumberTheory.NumberField.SubspaceIntegerPoints

import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The Euclidean span and lattice of integral points of a number-field subspace

Let `K` be a number field of degree `D = [K : ℚ]` and `ι` a finite coordinate type. A `K`-subspace
`W` of `ι → K` of dimension `m` embeds coordinatewise into the Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`, where each complex place
of `K` contributes a single `(Re, Im)` plane with its standard real inner product. Unlike the
sup-normed product `ι → mixedSpace K`, this ambient space is a real inner product space, so the
real span `W.euclideanSpan` of `W` inherits an inner product and canonical Euclidean Haar measure.

Within `W.euclideanSpan`, the points whose coordinates lie in
`NumberField.mixedEmbedding.euclidean.integerLattice K` form a `ℤ`-submodule `W.integerLattice`,
canonically `ℤ`-linearly equivalent to the saturated `𝓞 K`-submodule `W.integerPoints` of tuples in
`ι → 𝓞 K` whose image in `ι → K` belongs to `W`. Even when `W.integerPoints` is not free over
`𝓞 K`, choosing a Steinitz pseudo-basis `W ∩ 𝓞_K^ι = ⊕ k, J k • b k`
(`Submodule.exists_pseudoBasis_integerPoints`) and `ℤ`-bases of the coefficient ideals `J k`
(`Ideal.mixedLatticeBasis`) produces an explicit `ℤ`-basis of `W.integerLattice` that is also an
`ℝ`-basis of `W.euclideanSpan`. In particular, `W.euclideanSpan` has real dimension `D * m` and
`W.integerLattice` is a discrete full `ℤ`-lattice in `W.euclideanSpan`.

Over `ℚ`, the linear isometry
`TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal` carries `V.euclideanSpan`
isometrically onto `V.realSpan` (`Submodule.euclideanSpanEquivRealSpan`) and pulls `V.intLattice`
back to `V.integerLattice` (`Submodule.comap_intLattice_euclideanSpanEquivRealSpan`).

## Main definitions

* `Submodule.euclideanSpan W`: the real span of `W` inside
  `PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`.
* `Submodule.integerLattice W`: the `ℤ`-submodule of points of `W.euclideanSpan` with coordinates
  in `NumberField.mixedEmbedding.euclidean.integerLattice K`.
* `Submodule.integerPointsEquivIntegerLattice W`: the `ℤ`-linear equivalence
  `W.integerPoints ≃ₗ[ℤ] W.integerLattice`.
* `Submodule.euclideanSpanBasisOfPseudoBasis`, `Submodule.integerLatticeBasisOfPseudoBasis`: the
  `ℝ`-basis of `W.euclideanSpan` and `ℤ`-basis of `W.integerLattice` attached to a pseudo-basis
  `(b, J)` of `W.integerPoints`.
* `Submodule.integerPointsEquivIntPoints`, `Submodule.euclideanSpanEquivRealSpan`: identifications
  of the `K = ℚ` constructions with `Submodule.intPoints` and `Submodule.realSpan`.

## Main results

* `Submodule.toLp_mem_euclideanSpan_iff`: the `K`-points of `W.euclideanSpan` are precisely the
  points of `W`.
* `Submodule.finrank_euclideanSpan`, `Submodule.finrank_integerLattice`: `W.euclideanSpan` and
  `W.integerLattice` have rank `[K : ℚ] * finrank K W`.
* The instances `BorelSpace W.euclideanSpan`, `MeasureSpace W.euclideanSpan`,
  `DiscreteTopology W.integerLattice`, and `IsZLattice ℝ W.integerLattice`.
* `Submodule.comap_intLattice_euclideanSpanEquivRealSpan`: over `ℚ`, pulling `V.intLattice` back
  along `V.euclideanSpanEquivRealSpan` gives `V.integerLattice`.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8 and Appendix C.2.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §6.1.
-/

public section

noncomputable section

open MeasureTheory Module NumberField NumberField.mixedEmbedding Set
open scoped nonZeroDivisors

namespace Submodule

section EuclideanSpan

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- The real span of a `K`-subspace `W` of `ι → K` inside the Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`. -/
def euclideanSpan (W : Submodule K (ι → K)) :
    Submodule ℝ (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :=
  span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦
    (euclidean.toMixed K).symm (mixedEmbedding K (v i))) '' W)

/-- Every point of `W` embeds into `W.euclideanSpan`. -/
theorem toLp_mem_euclideanSpan {W : Submodule K (ι → K)} {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) ∈
      W.euclideanSpan :=
  subset_span ⟨v, hv, rfl⟩

/-- The real span of the zero subspace is zero. -/
@[simp]
theorem euclideanSpan_bot : (⊥ : Submodule K (ι → K)).euclideanSpan = ⊥ := by
  rw [euclideanSpan, bot_coe, image_singleton, span_singleton_eq_bot]
  ext1 i
  simp

/-- `Submodule.euclideanSpan` is monotone in the subspace. -/
@[gcongr]
theorem euclideanSpan_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂) :
    W₁.euclideanSpan ≤ W₂.euclideanSpan :=
  span_mono (image_mono h)

open Classical in
/-- `mixedSpace K`-linear extension of a `K`-linear form `f : (ι → K) →ₗ[K] K` to the Euclidean
Minkowski space `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`. -/
private def mixedExtend [Fintype ι] (f : (ι → K) →ₗ[K] K) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K where
  toFun z := ∑ i : ι, mixedEmbedding K (f (Pi.single i 1)) * euclidean.toMixed K (z i)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [Algebra.mul_smul_comm, Finset.smul_sum]

private theorem mixedExtend_toLp_mul [Fintype ι] (f : (ι → K) →ₗ[K] K) (z : mixedSpace K)
    (u : ι → K) :
    mixedExtend f
        (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (z * mixedEmbedding K (u i))) =
      z * mixedEmbedding K (f u) := by
  classical
  conv_rhs => rw [pi_eq_sum_univ' u, map_sum, map_sum, Finset.mul_sum]
  simp only [mixedExtend, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem mixedExtend_toLp [Fintype ι] (f : (ι → K) →ₗ[K] K) (u : ι → K) :
    mixedExtend f (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (u i))) =
      mixedEmbedding K (f u) := by
  simpa using mixedExtend_toLp_mul f 1 u

/-- **The `K`-points of `W.euclideanSpan` are precisely the points of `W`.** -/
@[simp]
theorem toLp_mem_euclideanSpan_iff [Finite ι] {W : Submodule K (ι → K)} {v : ι → K} :
    (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) ∈
      W.euclideanSpan ↔ v ∈ W := by
  cases nonempty_fintype ι
  refine ⟨fun h ↦ ?_, toLp_mem_euclideanSpan⟩
  by_contra hv
  -- Separate `v` from `W` by a `K`-linear form `f` and extend `f` `mixedSpace K`-linearly.
  obtain ⟨f, hfv, hfW⟩ := exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hle : W.euclideanSpan ≤ LinearMap.ker (mixedExtend f) := by
    refine span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    have hfu : f u = 0 := by simpa [hfW] using mem_map_of_mem (f := f) hu
    simp [mixedExtend_toLp, hfu]
  have hgv : mixedEmbedding K (f v) = 0 := (mixedExtend_toLp f v).symm.trans (hle h)
  exact hfv ((map_eq_zero_iff (mixedEmbedding K) (mixedEmbedding_injective K)).1 hgv)

/-- The integral points of `W` as a `ℤ`-submodule of `W.euclideanSpan`: the points of
`W.euclideanSpan` whose coordinates belong to `euclidean.integerLattice K`. -/
def integerLattice (W : Submodule K (ι → K)) : Submodule ℤ W.euclideanSpan where
  carrier := {w | ∀ i, (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i ∈
    euclidean.integerLattice K}
  add_mem' hw hw' i := add_mem (hw i) (hw' i)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hw i := smul_mem _ c (hw i)

/-- A point of `W.euclideanSpan` lies in `W.integerLattice` when every coordinate lies in
`euclidean.integerLattice K`. -/
@[simp]
theorem mem_integerLattice {W : Submodule K (ι → K)} {w : W.euclideanSpan} :
    w ∈ W.integerLattice ↔
      ∀ i, (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i ∈ euclidean.integerLattice K :=
  Iff.rfl

section Equiv

variable [Finite ι]

/-- Every point of `W.integerLattice` comes from an integral point of `W`. -/
private theorem exists_mem_integerPoints_of_mem_integerLattice {W : Submodule K (ι → K)}
    {w : W.euclideanSpan} (hw : w ∈ W.integerLattice) :
    ∃ z ∈ W.integerPoints, (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (z i)) := by
  have hi (i : ι) : ∃ a : 𝓞 K,
      mixedEmbedding K a =
        euclidean.toMixed K ((w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) := by
    simpa [euclidean.integerLattice, ZLattice.comap] using hw i
  choose z hz using hi
  have hwz : (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (z i)) := by
    ext1 i; simp [hz i]
  refine ⟨z, ?_, hwz⟩
  rw [mem_integerPoints, ← toLp_mem_euclideanSpan_iff, ← hwz]
  exact w.2

open Classical in
/-- The `ℤ`-linear map sending an integral point of `W` to the corresponding point of
`W.integerLattice`. -/
private def integerPointsToIntegerLattice (W : Submodule K (ι → K)) :
    W.integerPoints →ₗ[ℤ] W.integerLattice where
  toFun z := ⟨⟨WithLp.toLp 2 fun i ↦
      (euclidean.toMixed K).symm (mixedEmbedding K ((z : ι → 𝓞 K) i)),
    toLp_mem_euclideanSpan (mem_integerPoints.mp z.2)⟩, fun i ↦ ⟨(z : ι → 𝓞 K) i, by simp⟩⟩
  map_add' _ _ := by ext1; ext1; ext1 i; simp
  map_smul' c z := by
    ext1; ext1; ext1 i
    apply (euclidean.toMixed K).injective
    simp only [RingHom.id_apply, SetLike.val_smul, coe_smul_of_tower, PiLp.smul_apply, map_zsmul,
      ContinuousLinearEquiv.apply_symm_apply]
    exact map_zsmul (mixedEmbedding K).toIntAlgHom.toLinearMap c _

private theorem bijective_integerPointsToIntegerLattice (W : Submodule K (ι → K)) :
    Function.Bijective (integerPointsToIntegerLattice W) := by
  refine ⟨fun z z' h ↦ ?_, fun w ↦ ?_⟩
  · ext i
    have hi := congrArg (fun u : W.integerLattice ↦
      euclidean.toMixed K
        (((u : W.euclideanSpan) : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i)) h
    simp only [integerPointsToIntegerLattice, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, ContinuousLinearEquiv.apply_symm_apply] at hi
    exact mixedEmbedding_injective K hi
  · obtain ⟨z, hzW, hwz⟩ := exists_mem_integerPoints_of_mem_integerLattice w.2
    exact ⟨⟨z, hzW⟩, Subtype.ext (Subtype.ext hwz.symm)⟩

/-- The `ℤ`-linear equivalence between `W.integerPoints` and `W.integerLattice`. -/
def integerPointsEquivIntegerLattice (W : Submodule K (ι → K)) :
    W.integerPoints ≃ₗ[ℤ] W.integerLattice :=
  LinearEquiv.ofBijective (integerPointsToIntegerLattice W)
    (bijective_integerPointsToIntegerLattice W)

/-- `integerPointsEquivIntegerLattice` embeds coordinates via
`(toMixed K).symm ∘ mixedEmbedding`. -/
@[simp]
theorem coe_integerPointsEquivIntegerLattice_apply (W : Submodule K (ι → K))
    (z : W.integerPoints) :
    ((W.integerPointsEquivIntegerLattice z : W.euclideanSpan) :
      PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K ((z : ι → 𝓞 K) i)) := by
  simp [integerPointsEquivIntegerLattice, integerPointsToIntegerLattice]

/-- The inverse of `integerPointsEquivIntegerLattice` recovers the mixed-embedded coordinates. -/
@[simp]
theorem mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply (W : Submodule K (ι → K))
    (w : W.integerLattice) (i : ι) :
    mixedEmbedding K (((W.integerPointsEquivIntegerLattice.symm w : W.integerPoints) :
        ι → 𝓞 K) i) =
      euclidean.toMixed K (((w : W.euclideanSpan) :
        PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i) := by
  conv_rhs => rw [← W.integerPointsEquivIntegerLattice.apply_symm_apply w,
    coe_integerPointsEquivIntegerLattice_apply]
  simp

end Equiv

section PseudoBasis

section GivenPseudoBasis

variable {W : Submodule K (ι → K)} {κ : Type*} (b : Basis κ K W) {J : κ → Ideal (𝓞 K)}
  (hJ : ∀ k, J k ≠ ⊥)

/-- The coordinatewise evaluation map `(PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ]
mixedSpace K` at `i : ι`. -/
private def evalMixedLinear (i : ι) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K :=
  (euclidean.toMixed K).toLinearMap ∘ₗ
    (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap

private theorem evalMixedLinear_apply (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    evalMixedLinear i x = euclidean.toMixed K (x i) := by
  simp [evalMixedLinear]

/-- The family of vectors in `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K` attached to `(b, J)`. -/
private def pseudoBasisVec (p : κ × index K) :
    PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K :=
  WithLp.toLp 2 fun i ↦
    (euclidean.toMixed K).symm
      (mixedEmbedding K ((J p.1).mixedBasisElem (hJ p.1) p.2 * (b p.1 : ι → K) i))

private theorem evalMixedLinear_pseudoBasisVec (p : κ × index K) (i : ι) :
    evalMixedLinear i (pseudoBasisVec b hJ p) =
      (J p.1).mixedLatticeBasis (hJ p.1) p.2 * mixedEmbedding K ((b p.1 : ι → K) i) := by
  simp [evalMixedLinear_apply, pseudoBasisVec]

private theorem linearIndependent_pseudoBasisVec [Finite ι] [Finite κ] :
    LinearIndependent ℝ (pseudoBasisVec b hJ) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [Fintype.linearIndependent_iff]
  intro c hc ⟨k₀, ν₀⟩
  -- Extend `b`'s coordinates biorthogonally to `ι → K`, then `mixedSpace K`-linearly.
  obtain ⟨f, hf⟩ := b.linearIndependent_coe_basis.exists_dual_forall_apply_eq_ite
  have hsum : ∑ ν : index K, c (k₀, ν) • (J k₀).mixedLatticeBasis (hJ k₀) ν = 0 := by
    have hm := congrArg (mixedExtend (f k₀)) hc
    have hvec (p : κ × index K) :
        mixedExtend (f k₀) (pseudoBasisVec b hJ p) =
          (J p.1).mixedLatticeBasis (hJ p.1) p.2 * mixedEmbedding K (f k₀ (b p.1 : ι → K)) := by
      simpa [pseudoBasisVec] using
        mixedExtend_toLp_mul (f k₀) ((J p.1).mixedLatticeBasis (hJ p.1) p.2) (b p.1 : ι → K)
    rw [map_sum, map_zero] at hm
    simp_rw [map_smul, hvec, hf k₀] at hm
    rw [Fintype.sum_prod_type] at hm
    simpa [eq_comm] using hm
  exact Fintype.linearIndependent_iff.mp ((J k₀).mixedLatticeBasis (hJ k₀)).linearIndependent
    (fun ν ↦ c (k₀, ν)) hsum ν₀

open Classical in
/-- Expand the Euclidean Minkowski embedding of `v ∈ W` in `pseudoBasisVec b hJ` by expanding
`⟨v, hv⟩` in `b` and each `K`-coordinate in `(J k).mixedLatticeBasis (hJ k)`. -/
private theorem toLp_eq_sum_repr_smul_pseudoBasisVec [Fintype κ] {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) =
      ∑ p : κ × index K,
        ((J p.1).mixedLatticeBasis (hJ p.1)).repr (mixedEmbedding K (b.repr ⟨v, hv⟩ p.1)) p.2 •
          pseudoBasisVec b hJ p := by
  ext1 i
  apply (euclidean.toMixed K).injective
  rw [WithLp.ofLp_toLp, ContinuousLinearEquiv.apply_symm_apply, ← evalMixedLinear_apply, map_sum]
  simp only [map_smul, evalMixedLinear_pseudoBasisVec]
  rw [congrFun (b.eq_sum_repr_smul_of_mem hv) i, Finset.sum_apply, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul,
    ← ((J k).mixedLatticeBasis (hJ k)).sum_repr (mixedEmbedding K (b.repr ⟨v, hv⟩ k)),
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ ↦ Algebra.smul_mul_assoc _ _ _

private theorem span_range_pseudoBasisVec [Finite κ] :
    span ℝ (range (pseudoBasisVec b hJ)) = W.euclideanSpan := by
  classical
  cases nonempty_fintype κ
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨⟨k, ν⟩, rfl⟩
    simpa [pseudoBasisVec, Algebra.smul_def] using
      toLp_mem_euclideanSpan (W.smul_mem ((J k).mixedBasisElem (hJ k) ν) (b k).2)
  · rintro _ ⟨v, hv, rfl⟩
    dsimp only
    rw [toLp_eq_sum_repr_smul_pseudoBasisVec b hJ hv]
    exact sum_mem fun p _ ↦ smul_mem _ _ (subset_span ⟨p, rfl⟩)

/-- The `ℝ`-basis of `W.euclideanSpan` attached to a `K`-basis `b` of `W` and nonzero ideals `J k`
of `𝓞 K`. -/
def euclideanSpanBasisOfPseudoBasis [Finite ι] [Finite κ] :
    Basis (κ × index K) ℝ W.euclideanSpan :=
  (Basis.span (linearIndependent_pseudoBasisVec b hJ)).map
    (LinearEquiv.ofEq _ _ (span_range_pseudoBasisVec b hJ))

/-- Coordinates of `euclideanSpanBasisOfPseudoBasis b hJ` in the ambient Euclidean Minkowski
space. -/
@[simp]
theorem coe_euclideanSpanBasisOfPseudoBasis_apply [Finite ι] [Finite κ] (p : κ × index K) :
    ((euclideanSpanBasisOfPseudoBasis b hJ p : W.euclideanSpan) :
      PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm
        (mixedEmbedding K ((J p.1).mixedBasisElem (hJ p.1) p.2 * (b p.1 : ι → K) i)) := by
  simp [euclideanSpanBasisOfPseudoBasis, Basis.span_apply, pseudoBasisVec]

/-- When `(b, J)` is a pseudo-basis of the integral points of `W`, the `ℤ`-span of
`euclideanSpanBasisOfPseudoBasis b hJ` is `W.integerLattice`. -/
theorem span_int_euclideanSpanBasisOfPseudoBasis [Finite ι] [Finite κ]
    (hW : W.IsIntegerPseudoBasis b J) :
    span ℤ (range (euclideanSpanBasisOfPseudoBasis b hJ)) = W.integerLattice := by
  classical
  cases nonempty_fintype κ
  refine le_antisymm (span_le.2 ?_) (fun w hw ↦ ?_)
  · -- Each `(b, J)`-generator has integral coordinates, hence lies in `W.integerLattice`.
    rintro _ ⟨⟨k, ν⟩, rfl⟩
    rw [SetLike.mem_coe, mem_integerLattice]
    intro i
    obtain ⟨a, ha⟩ := hW.coe_smul_basis_mem_range ((J k).mixedBasisElem_mem (hJ k) ν) i
    rw [coe_euclideanSpanBasisOfPseudoBasis_apply, euclidean.integerLattice, ZLattice.comap,
      Submodule.mem_comap]
    exact ⟨a, by simp [← ha]⟩
  · -- Expand an integral point in `pseudoBasisVec b hJ`; `(hW, J)` makes the coefficients integral.
    obtain ⟨z, hzW, hwz⟩ := exists_mem_integerPoints_of_mem_integerLattice hw
    have hv : (fun i ↦ (z i : K)) ∈ W := mem_integerPoints.mp hzW
    have hint (k : κ) (ν : index K) :
        ∃ m : ℤ, (m : ℝ) =
          ((J k).mixedLatticeBasis (hJ k)).repr (mixedEmbedding K (b.repr ⟨_, hv⟩ k)) ν := by
      have hwK : b.repr ⟨_, hv⟩ k ∈ IsLocalization.coeSubmodule K (J k) :=
        (hW.mem_coeSubmodule_iff ⟨_, hv⟩).1 (fun i ↦ ⟨z i, rfl⟩) k
      have hm :=
        ((J k).mem_coeSubmodule_iff_mem_span_mixedLatticeBasis (hJ k) (b.repr ⟨_, hv⟩ k)).1 hwK
      exact (((J k).mixedLatticeBasis (hJ k)).mem_span_iff_repr_mem ℤ _).1 hm ν
    choose m hm using hint
    have hweq : w = ∑ p : κ × index K, m p.1 p.2 • euclideanSpanBasisOfPseudoBasis b hJ p := by
      apply Subtype.ext
      rw [hwz, toLp_eq_sum_repr_smul_pseudoBasisVec b hJ hv, ← W.euclideanSpan.coe_subtype,
        map_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [map_zsmul, Submodule.coe_subtype, coe_euclideanSpanBasisOfPseudoBasis_apply,
        ← hm p.1 p.2, Int.cast_smul_eq_zsmul, pseudoBasisVec]
    rw [hweq]
    exact sum_mem fun p _ ↦ zsmul_mem (subset_span (mem_range_self p)) _

/-- The `ℤ`-basis of `W.integerLattice` attached to a pseudo-basis `(b, J)` of `W.integerPoints`. -/
def integerLatticeBasisOfPseudoBasis [Finite ι] [Finite κ]
    (hW : W.IsIntegerPseudoBasis b J) :
    Basis (κ × index K) ℤ W.integerLattice :=
  ((euclideanSpanBasisOfPseudoBasis b hJ).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (span_int_euclideanSpanBasisOfPseudoBasis b hJ hW))

/-- Coordinates of `integerLatticeBasisOfPseudoBasis b hJ hW` in the ambient Euclidean Minkowski
space. -/
@[simp]
theorem coe_integerLatticeBasisOfPseudoBasis_apply [Finite ι] [Finite κ]
    (hW : W.IsIntegerPseudoBasis b J) (p : κ × index K) :
    (((integerLatticeBasisOfPseudoBasis b hJ hW p : W.integerLattice) : W.euclideanSpan) :
      PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm
        (mixedEmbedding K ((J p.1).mixedBasisElem (hJ p.1) p.2 * (b p.1 : ι → K) i)) := by
  simp [integerLatticeBasisOfPseudoBasis, Basis.restrictScalars_apply]

end GivenPseudoBasis

section Instances

variable [Finite ι] (W : Submodule K (ι → K))

/-- The real span of `W` in the Euclidean Minkowski space has real dimension
`[K : ℚ] * finrank K W`. -/
theorem finrank_euclideanSpan :
    finrank ℝ W.euclideanSpan = finrank ℚ K * finrank K W := by
  classical
  cases nonempty_fintype ι
  obtain ⟨b, J, hJ, -⟩ := W.exists_pseudoBasis_integerPoints
  rw [finrank_eq_card_basis (euclideanSpanBasisOfPseudoBasis b hJ), Fintype.card_prod,
    Fintype.card_fin, ← finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank, mul_comm]

/-- The real span of `⊤ : Submodule K (ι → K)` is the whole Euclidean Minkowski space. -/
@[simp]
theorem euclideanSpan_top : (⊤ : Submodule K (ι → K)).euclideanSpan = ⊤ := by
  classical
  cases nonempty_fintype ι
  refine eq_top_of_finrank_eq ?_
  rw [finrank_euclideanSpan, finrank_top, Module.finrank_fintype_fun_eq_card,
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)),
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, euclidean.finrank,
    mul_comm]

open Classical in
/-- The integral lattice of `W` is discrete in `W.euclideanSpan`. -/
instance instDiscreteTopologyIntegerLattice : DiscreteTopology W.integerLattice := by
  cases nonempty_fintype ι
  obtain ⟨b, J, hJ, hW⟩ := W.exists_pseudoBasis_integerPoints
  rw [← span_int_euclideanSpanBasisOfPseudoBasis b hJ hW]
  infer_instance

end Instances

open Classical in
/-- The Borel measurable structure on `W.euclideanSpan`. Declared explicitly because instance
search through `PiLp.borelSpace` and `euclidean.mixedSpace` times out when resolving
`MeasureSpace W.euclideanSpan`. -/
instance instBorelSpaceEuclideanSpan [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace W.euclideanSpan :=
  Subtype.borelSpace _

open Classical in
/-- The canonical Euclidean Haar `MeasureSpace` on `W.euclideanSpan`. Declared explicitly so
`volume` resolves without hitting the `priority := 100` search depth of
`measureSpaceOfInnerProductSpace`. -/
instance instMeasureSpaceEuclideanSpan [Fintype ι] (W : Submodule K (ι → K)) :
    MeasureSpace W.euclideanSpan :=
  measureSpaceOfInnerProductSpace

open Classical in
/-- The integral lattice of `W` spans `W.euclideanSpan` over `ℝ`: it is a full `ℤ`-lattice.
Note that `[Fintype ι]` is required in the statement because `IsZLattice ℝ W.integerLattice` takes
`[NormedAddCommGroup W.euclideanSpan]` via `PiLp.normedAddCommGroup`. -/
instance instIsZLatticeIntegerLattice [Fintype ι] (W : Submodule K (ι → K)) :
    IsZLattice ℝ W.integerLattice where
  span_top := by
    obtain ⟨b, J, hJ, hW⟩ := W.exists_pseudoBasis_integerPoints
    rw [← span_int_euclideanSpanBasisOfPseudoBasis b hJ hW]
    exact ZSpan.span_top _

/-- The integral lattice of `W` is free over `ℤ` of rank `[K : ℚ] * finrank K W`. -/
theorem finrank_integerLattice [Finite ι] (W : Submodule K (ι → K)) :
    finrank ℤ W.integerLattice = finrank ℚ K * finrank K W := by
  classical
  cases nonempty_fintype ι
  rw [ZLattice.rank ℝ W.integerLattice, finrank_euclideanSpan]

end PseudoBasis

end EuclideanSpan

section Rat

open TauCeti.NumberField.mixedEmbedding.euclidean

variable {ι : Type*}

/-- Over `ℚ`, `V.integerPoints` is canonically `ℤ`-linearly equivalent to `V.intPoints` via
`Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. -/
def integerPointsEquivIntPoints (V : Submodule ℚ (ι → ℚ)) :
    V.integerPoints ≃ₗ[ℤ] V.intPoints where
  toFun z := ⟨fun i ↦ Rat.ringOfIntegersEquiv ((z : ι → 𝓞 ℚ) i), by
    rw [mem_intPoints]
    convert mem_integerPoints.mp z.2 with i
    exact (Rat.ringOfIntegersEquiv_apply_coe _).trans (RingOfIntegers.coe_eq_algebraMap _).symm⟩
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp
  invFun z := ⟨fun i ↦ Rat.ringOfIntegersEquiv.symm ((z : ι → ℤ) i), by
    rw [mem_integerPoints]
    convert mem_intPoints.mp z.2 with i
    exact (RingOfIntegers.coe_eq_algebraMap _).trans (Rat.ringOfIntegersEquiv_symm_apply_coe _)⟩
  left_inv z := by ext i; simp
  right_inv z := by ext i; simp

/-- Coordinates of `V.integerPointsEquivIntPoints z`. -/
@[simp]
theorem coe_integerPointsEquivIntPoints_apply (V : Submodule ℚ (ι → ℚ)) (z : V.integerPoints)
    (i : ι) :
    (V.integerPointsEquivIntPoints z : ι → ℤ) i = Rat.ringOfIntegersEquiv ((z : ι → 𝓞 ℚ) i) := by
  simp [integerPointsEquivIntPoints]

/-- Coordinates of `V.integerPointsEquivIntPoints.symm z`. -/
@[simp]
theorem coe_integerPointsEquivIntPoints_symm_apply (V : Submodule ℚ (ι → ℚ)) (z : V.intPoints)
    (i : ι) :
    (V.integerPointsEquivIntPoints.symm z : ι → 𝓞 ℚ) i =
      Rat.ringOfIntegersEquiv.symm ((z : ι → ℤ) i) := by
  simp [integerPointsEquivIntPoints]

open Classical in
private theorem map_euclideanSpan_rat [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    V.euclideanSpan.map
        ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal) :
          (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) →ₗ[ℝ] PiLp 2 fun _ : ι ↦ ℝ) =
      V.realSpan := by
  set E := LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal
  set f : (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) →ₗ[ℝ] PiLp 2 fun _ : ι ↦ ℝ := ↑E
  have hle : V.euclideanSpan.map f ≤ V.realSpan := by
    rw [map_le_iff_le_comap, euclideanSpan, span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : f (WithLp.toLp 2 fun i ↦
        (NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ (v i))) =
        WithLp.toLp 2 fun i ↦ (v i : ℝ) := by ext1 i; simp [f, E]
    simpa [Submodule.mem_comap, hv'] using toLp_mem_realSpan hv
  have hdim : finrank ℝ (V.euclideanSpan.map f) = finrank ℝ V.realSpan := by
    have hf : f = E.toLinearEquiv.toLinearMap := by ext; simp [f]
    rw [hf, LinearEquiv.finrank_map_eq E.toLinearEquiv, V.finrank_euclideanSpan,
      Module.finrank_self, one_mul, V.finrank_realSpan]
  exact eq_of_le_of_finrank_eq hle hdim

open Classical in
/-- Over `ℚ`, `V.euclideanSpan` is canonically linearly isometric to `V.realSpan` coordinatewise
via `mixedSpaceRatEquivReal`. -/
def euclideanSpanEquivRealSpan [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    V.euclideanSpan ≃ₗᵢ[ℝ] V.realSpan :=
  (LinearIsometryEquiv.submoduleMap V.euclideanSpan
      (LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_rat V))

open Classical in
/-- Ambient coordinates of `V.euclideanSpanEquivRealSpan w`. -/
@[simp]
theorem coe_euclideanSpanEquivRealSpan_apply [Fintype ι] (V : Submodule ℚ (ι → ℚ))
    (w : V.euclideanSpan) (i : ι) :
    (V.euclideanSpanEquivRealSpan w : EuclideanSpace ℝ ι) i =
      mixedSpaceRatEquivReal ((w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) i) := by
  rw [euclideanSpanEquivRealSpan, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  simp [-mixedSpaceRatEquivReal_apply]

open Classical in
/-- Over `ℚ`, pulling `V.intLattice` back along `V.euclideanSpanEquivRealSpan` recovers
`V.integerLattice`. -/
@[simp]
theorem comap_intLattice_euclideanSpanEquivRealSpan [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.comap ℝ V.intLattice V.euclideanSpanEquivRealSpan.toLinearMap = V.integerLattice := by
  ext w
  simp [ZLattice.comap, mem_integerLattice_rat_iff]

end Rat

end Submodule

end
