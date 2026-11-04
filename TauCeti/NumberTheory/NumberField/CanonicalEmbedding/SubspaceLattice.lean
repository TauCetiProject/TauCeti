/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Localization.Integer
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation
import TauCeti.RingTheory.DedekindDomain.PseudoBasis

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
(`Submodule.exists_pseudoBasis`) and `ℤ`-bases of the coefficient ideals `J k`
(`Ideal.mixedLatticeBasis`) produces an explicit `ℤ`-basis of `W.integerLattice` that is also an
`ℝ`-basis of `W.euclideanSpan`. In particular, `W.euclideanSpan` has real dimension `D * m` and
`W.integerLattice` is a discrete full `ℤ`-lattice in `W.euclideanSpan`.

Over `ℚ`, the linear isometry
`TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal` identifies
`euclidean.mixedSpace ℚ` with `ℝ`, carrying `V.euclideanSpan` isometrically onto `V.realSpan`
(`Submodule.euclideanSpanEquivRealSpan`) and pulling `V.intLattice` back to `V.integerLattice`
(`Submodule.comap_intLattice_euclideanSpanEquivRealSpan`).

## Main definitions

* `Submodule.integerPoints W`: the `𝓞 K`-submodule `W ∩ (𝓞 K)^ι` of `ι → 𝓞 K`.
* `Submodule.IsIntegerPseudoBasis W b J`: the predicate that a `K`-basis `b` of `W` and ideals `J`
  of `𝓞 K` form a Steinitz pseudo-basis of `W.integerPoints`.
* `Submodule.euclideanSpan W`: the real span of `W` inside
  `PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`.
* `Submodule.integerLattice W`: the `ℤ`-submodule of points of `W.euclideanSpan` with coordinates
  in `NumberField.mixedEmbedding.euclidean.integerLattice K`.
* `Submodule.integerPointsEquivIntegerLattice W`: the `ℤ`-linear equivalence
  `W.integerPoints ≃ₗ[ℤ] W.integerLattice`.
* `Submodule.integerLatticeBasisOfPseudoBasis`: the `ℤ`-basis of `W.integerLattice` attached to a
  pseudo-basis `(b, J)` of `W.integerPoints`.
* `TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal`,
  `Submodule.integerPointsEquivIntPoints`, `Submodule.euclideanSpanEquivRealSpan`: identifications
  of the `K = ℚ` constructions with `ℝ`, `Submodule.intPoints`, and `Submodule.realSpan`.

## Main results

* `Submodule.mem_integerPoints_of_smul_mem`: `W.integerPoints` is saturated in `ι → 𝓞 K`.
* `Submodule.toLp_mem_euclideanSpan_iff`: the `K`-points of `W.euclideanSpan` are precisely the
  points of `W`.
* `Submodule.exists_pseudoBasis_integerPoints`: `W` admits a `K`-basis `b` and nonzero ideals `J k`
  of `𝓞 K` satisfying `W.IsIntegerPseudoBasis b J`.
* `Submodule.finrank_euclideanSpan`, `Submodule.finrank_integerLattice`: `W.euclideanSpan` and
  `W.integerLattice` have rank `[K : ℚ] * finrank K W`.
* The instances `BorelSpace W.euclideanSpan`, `MeasureSpace W.euclideanSpan`,
  `DiscreteTopology W.integerLattice`, and `IsZLattice ℝ W.integerLattice`.
* `Submodule.comap_intLattice_euclideanSpanEquivRealSpan`: over `ℚ`, pulling `V.intLattice` back
  along `V.euclideanSpanEquivRealSpan` gives `V.integerLattice`.
* `Matrix.integerPoints_ker_mulVecLin`: the integral points of the `K`-kernel of an `𝓞 K`-matrix
  are its `𝓞 K`-kernel.

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

section IntegerPoints

variable {K : Type*} [Field K] {ι : Type*}

/-- The integral points of a `K`-subspace `W` of `ι → K`: the tuples `z : ι → 𝓞 K` whose image in
`ι → K` lies in `W`. -/
def integerPoints (W : Submodule K (ι → K)) : Submodule (𝓞 K) (ι → 𝓞 K) :=
  (W.restrictScalars (𝓞 K)).comap ((Algebra.linearMap (𝓞 K) K).compLeft ι)

/-- A tuple in `ι → 𝓞 K` is an integral point of `W` when its image in `ι → K` lies in `W`. -/
@[simp]
theorem mem_integerPoints {W : Submodule K (ι → K)} {z : ι → 𝓞 K} :
    z ∈ W.integerPoints ↔ (fun i ↦ (z i : K)) ∈ W :=
  Iff.rfl

/-- The zero subspace has only the zero integral point. -/
@[simp]
theorem integerPoints_bot : (⊥ : Submodule K (ι → K)).integerPoints = ⊥ := by
  ext z
  simp [funext_iff]

/-- The whole space `ι → K` has all of `ι → 𝓞 K` as integral points. -/
@[simp]
theorem integerPoints_top : (⊤ : Submodule K (ι → K)).integerPoints = ⊤ := by
  ext z
  simp

/-- `Submodule.integerPoints` is monotone in the subspace. -/
@[gcongr]
theorem integerPoints_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂) :
    W₁.integerPoints ≤ W₂.integerPoints :=
  fun _ hz ↦ h hz

/-- The integral points of `W` form a saturated `𝓞 K`-submodule of `ι → 𝓞 K`: if a nonzero
`𝓞 K`-multiple of `z` lies in `W.integerPoints`, then so does `z`. -/
theorem mem_integerPoints_of_smul_mem {W : Submodule K (ι → K)} {c : 𝓞 K} {z : ι → 𝓞 K}
    (hc : c ≠ 0) (h : c • z ∈ W.integerPoints) : z ∈ W.integerPoints := by
  rw [mem_integerPoints] at h ⊢
  have hcK : (c : K) ≠ 0 := by simpa using hc
  convert W.smul_mem (c : K)⁻¹ h using 1
  ext i
  simp [inv_mul_cancel_left₀ hcK]

/-- `(b, J)` is a Steinitz pseudo-basis for the integral points of `W`: a vector `w ∈ W` has all
coordinates in `𝓞 K` if and only if its `k`-th `b`-coordinate lies in `J k` for every `k`. -/
def IsIntegerPseudoBasis (W : Submodule K (ι → K)) {κ : Type*} (b : Basis κ K W)
    (J : κ → Ideal (𝓞 K)) : Prop :=
  ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
    ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k)

/-- Unfolding characterization of `Submodule.IsIntegerPseudoBasis`. -/
theorem isIntegerPseudoBasis_iff {W : Submodule K (ι → K)} {κ : Type*} (b : Basis κ K W)
    (J : κ → Ideal (𝓞 K)) :
    W.IsIntegerPseudoBasis b J ↔
      ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
        ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k) :=
  Iff.rfl

/-- Under `W.IsIntegerPseudoBasis b J`, integrality of the ambient coordinates of `w ∈ W` is
equivalent to membership of `b.repr w k` in `J k` for every `k`. -/
theorem IsIntegerPseudoBasis.mem_coeSubmodule_iff {W : Submodule K (ι → K)} {κ : Type*}
    {b : Basis κ K W} {J : κ → Ideal (𝓞 K)} (hW : W.IsIntegerPseudoBasis b J) (w : W) :
    (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k) :=
  hW w

end IntegerPoints

section EuclideanSpan

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

open scoped Classical in
/-- The real span of a `K`-subspace `W` of `ι → K` inside the Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`. -/
def euclideanSpan (W : Submodule K (ι → K)) :
    Submodule ℝ (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :=
  span ℝ ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦
    (euclidean.toMixed K).symm (mixedEmbedding K (v i))) '' W)

open scoped Classical in
/-- Every point of `W` embeds into `W.euclideanSpan`. -/
theorem toLp_mem_euclideanSpan {W : Submodule K (ι → K)} {v : ι → K} (hv : v ∈ W) :
    (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) ∈
      W.euclideanSpan :=
  subset_span ⟨v, hv, rfl⟩

open scoped Classical in
/-- The real span of the zero subspace is zero. -/
@[simp]
theorem euclideanSpan_bot : (⊥ : Submodule K (ι → K)).euclideanSpan = ⊥ := by
  rw [euclideanSpan]
  suffices ((fun v : ι → K ↦ WithLp.toLp 2 fun i ↦
      (euclidean.toMixed K).symm (mixedEmbedding K (v i))) ''
        ((⊥ : Submodule K (ι → K)) : Set (ι → K))) = {0} by
    rw [this, span_singleton_eq_bot]
  simp only [bot_coe, image_singleton, singleton_eq_singleton_iff]
  ext1 i
  simp

open scoped Classical in
/-- `Submodule.euclideanSpan` is monotone in the subspace. -/
@[gcongr]
theorem euclideanSpan_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂) :
    W₁.euclideanSpan ≤ W₂.euclideanSpan :=
  span_mono (image_mono h)

open scoped Classical in
/-- `mixedSpace K`-linear extension of a `K`-linear form `f : (ι → K) →ₗ[K] K` to the Euclidean
Minkowski space `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`. -/
private def mixedExtend [Fintype ι] (f : (ι → K) →ₗ[K] K) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K where
  toFun z := ∑ i : ι, mixedEmbedding K (f (Pi.single i 1)) * euclidean.toMixed K (z i)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [Algebra.mul_smul_comm, Finset.smul_sum]

open scoped Classical in
private theorem mixedExtend_toLp_mul [Fintype ι] (f : (ι → K) →ₗ[K] K) (z : mixedSpace K)
    (u : ι → K) :
    mixedExtend f
        (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (z * mixedEmbedding K (u i))) =
      z * mixedEmbedding K (f u) := by
  conv_rhs => rw [pi_eq_sum_univ' u, map_sum, map_sum, Finset.mul_sum]
  simp only [mixedExtend, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

open scoped Classical in
private theorem mixedExtend_toLp [Fintype ι] (f : (ι → K) →ₗ[K] K) (u : ι → K) :
    mixedExtend f (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (u i))) =
      mixedEmbedding K (f u) := by
  simpa using mixedExtend_toLp_mul f 1 u

open scoped Classical in
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
    have hfu : f u = 0 := by
      have hm := mem_map_of_mem (f := f) hu
      rwa [hfW, mem_bot] at hm
    simp [mixedExtend_toLp, hfu]
  have hgv : mixedEmbedding K (f v) = 0 := (mixedExtend_toLp f v).symm.trans (hle h)
  exact hfv ((map_eq_zero_iff (mixedEmbedding K) (mixedEmbedding_injective K)).1 hgv)

open scoped Classical in
/-- The integral points of `W` as a `ℤ`-submodule of `W.euclideanSpan`: the points of
`W.euclideanSpan` whose coordinates belong to `euclidean.integerLattice K`. -/
def integerLattice (W : Submodule K (ι → K)) : Submodule ℤ W.euclideanSpan where
  carrier := {w | ∀ i, (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i ∈
    euclidean.integerLattice K}
  add_mem' hw hw' i := add_mem (hw i) (hw' i)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hw i := smul_mem _ c (hw i)

open scoped Classical in
/-- A point of `W.euclideanSpan` lies in `W.integerLattice` when every coordinate lies in
`euclidean.integerLattice K`. -/
@[simp]
theorem mem_integerLattice {W : Submodule K (ι → K)} {w : W.euclideanSpan} :
    w ∈ W.integerLattice ↔
      ∀ i, (w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i ∈ euclidean.integerLattice K :=
  Iff.rfl

section Equiv

variable [Finite ι]

open scoped Classical in
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
    ext1 i
    simp [hz i]
  refine ⟨z, ?_, hwz⟩
  rw [mem_integerPoints, ← toLp_mem_euclideanSpan_iff, ← hwz]
  exact w.2

open scoped Classical in
/-- The `ℤ`-linear map sending an integral point of `W` to the corresponding point of
`W.integerLattice`. -/
private def integerPointsToIntegerLattice (W : Submodule K (ι → K)) :
    W.integerPoints →ₗ[ℤ] W.integerLattice where
  toFun z := ⟨⟨WithLp.toLp 2 fun i ↦
      (euclidean.toMixed K).symm (mixedEmbedding K ((z : ι → 𝓞 K) i)),
    toLp_mem_euclideanSpan z.2⟩,
    fun i ↦ by
      rw [euclidean.integerLattice, ZLattice.comap, Submodule.mem_comap]
      exact ⟨(z : ι → 𝓞 K) i, by simp⟩⟩
  map_add' z z' := by
    ext1
    ext1
    ext1 i
    simp
  map_smul' c z := by
    ext1
    ext1
    ext1 i
    apply (euclidean.toMixed K).injective
    simp only [RingHom.id_apply, SetLike.val_smul, coe_smul_of_tower, PiLp.smul_apply, map_zsmul,
      ContinuousLinearEquiv.apply_symm_apply]
    exact map_zsmul (mixedEmbedding K).toIntAlgHom.toLinearMap c _

open scoped Classical in
private theorem bijective_integerPointsToIntegerLattice (W : Submodule K (ι → K)) :
    Function.Bijective (integerPointsToIntegerLattice W) := by
  refine ⟨fun z z' h ↦ ?_, fun w ↦ ?_⟩
  · have h' := congrArg
      (fun u : W.integerLattice ↦
        ((u : W.euclideanSpan) : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K)) h
    ext i
    have hi := congrArg
      (fun x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K ↦ euclidean.toMixed K (x i)) h'
    simp only [integerPointsToIntegerLattice, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, ContinuousLinearEquiv.apply_symm_apply] at hi
    exact mixedEmbedding_injective K hi
  · obtain ⟨z, hzW, hwz⟩ := exists_mem_integerPoints_of_mem_integerLattice w.2
    exact ⟨⟨z, hzW⟩, Subtype.ext (Subtype.ext hwz.symm)⟩

open scoped Classical in
/-- The `ℤ`-linear equivalence between `W.integerPoints` and `W.integerLattice`. -/
def integerPointsEquivIntegerLattice (W : Submodule K (ι → K)) :
    W.integerPoints ≃ₗ[ℤ] W.integerLattice :=
  LinearEquiv.ofBijective (integerPointsToIntegerLattice W)
    (bijective_integerPointsToIntegerLattice W)

open scoped Classical in
/-- `integerPointsEquivIntegerLattice` embeds coordinates via
`(toMixed K).symm ∘ mixedEmbedding`. -/
@[simp]
theorem coe_integerPointsEquivIntegerLattice_apply (W : Submodule K (ι → K))
    (z : W.integerPoints) :
    ((W.integerPointsEquivIntegerLattice z : W.euclideanSpan) :
      PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K ((z : ι → 𝓞 K) i)) := by
  simp [integerPointsEquivIntegerLattice, integerPointsToIntegerLattice]

open scoped Classical in
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

/-- **Existence of a pseudo-basis for the integral points of a subspace.** Any `K`-subspace `W` of
`ι → K` admits a `K`-basis `b` indexed by `Fin (finrank K W)` and nonzero ideals `J k` of `𝓞 K`
satisfying `W.IsIntegerPseudoBasis b J`. -/
theorem exists_pseudoBasis_integerPoints [Finite ι] (W : Submodule K (ι → K)) :
    ∃ (b : Basis (Fin (finrank K W)) K W) (J : Fin (finrank K W) → Ideal (𝓞 K)),
      (∀ k, J k ≠ ⊥) ∧ W.IsIntegerPseudoBasis b J := by
  cases nonempty_fintype ι
  -- View `W ∩ (𝓞 K)^ι` as an `𝓞 K`-submodule `M` of `W`.
  let φ : W.integerPoints →ₗ[𝓞 K] W :=
    { toFun z := ⟨fun i ↦ ((z : ι → 𝓞 K) i : K), z.2⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext i; simp [Algebra.smul_def] }
  set M : Submodule (𝓞 K) W := LinearMap.range φ
  have hmemM (w : W) : w ∈ M ↔ ∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K) := by
    refine ⟨?_, fun hw ↦ ?_⟩
    · rintro ⟨z, rfl⟩ i
      exact ⟨(z : ι → 𝓞 K) i, rfl⟩
    · choose z hz using hw
      have hzW : z ∈ W.integerPoints := by
        rw [mem_integerPoints]
        convert w.2 with i
        exact hz i
      exact ⟨⟨z, hzW⟩, Subtype.ext (funext hz)⟩
  have hFG : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact (IsNoetherian.noetherian ⊤).map φ
  have hspan : span K (M : Set W) = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨⟨d, hd⟩, hdw⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ Finset.univ
      (w : ι → K)
    have hd0 : (algebraMap (𝓞 K) K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hd)
    have hdwM : d • w ∈ M := (hmemM (d • w)).2 fun i ↦ by
      simpa [Algebra.smul_def, IsLocalization.IsInteger] using hdw i (Finset.mem_univ i)
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, inv_smul_smul₀ hd0]
    rw [hw']
    exact smul_mem _ _ (subset_span hdwM)
  obtain ⟨b, J, hJ, hb⟩ := M.exists_pseudoBasis (K := K) (ι := Fin (finrank K W)) hFG hspan
    (Nat.card_fin _)
  exact ⟨b, J, hJ, fun w ↦ (hmemM w).symm.trans (hb w)⟩

section GivenPseudoBasis

variable {W : Submodule K (ι → K)} {κ : Type*} (b : Basis κ K W) {J : κ → Ideal (𝓞 K)}
  (hJ : ∀ k, J k ≠ ⊥)

omit [NumberField K] in
private theorem coe_apply_eq_sum_repr_mul [Fintype κ] (w : W) (i : ι) :
    (w : ι → K) i = ∑ k : κ, b.repr w k * (b k : ι → K) i := by
  have hi := congrFun (congrArg W.subtype (b.sum_repr w).symm) i
  rw [map_sum, Finset.sum_apply] at hi
  simpa only [coe_subtype, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] using hi

omit [NumberField K] in
private theorem apply_eq_sum_repr_mul [Fintype κ] {v : ι → K} (hv : v ∈ W) (i : ι) :
    v i = ∑ k : κ, b.repr ⟨v, hv⟩ k * (b k : ι → K) i :=
  coe_apply_eq_sum_repr_mul b ⟨v, hv⟩ i

open scoped Classical in
/-- The coordinatewise evaluation map `(PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ]
mixedSpace K` at `i : ι`. -/
private def evalMixedLinear (i : ι) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K :=
  (euclidean.toMixed K).toLinearMap ∘ₗ
    (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap

open scoped Classical in
private theorem evalMixedLinear_apply (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    evalMixedLinear i x = euclidean.toMixed K (x i) := by
  simp [evalMixedLinear]

open scoped Classical in
/-- The family of vectors in `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K` attached to `(b, J)`. -/
private def pseudoBasisVec (p : κ × index K) :
    PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K :=
  WithLp.toLp 2 fun i ↦
    (euclidean.toMixed K).symm
      (mixedEmbedding K ((J p.1).mixedBasisElem (hJ p.1) p.2 * (b p.1 : ι → K) i))

open scoped Classical in
private theorem evalMixedLinear_pseudoBasisVec (p : κ × index K) (i : ι) :
    evalMixedLinear i (pseudoBasisVec b hJ p) =
      (J p.1).mixedLatticeBasis (hJ p.1) p.2 * mixedEmbedding K ((b p.1 : ι → K) i) := by
  simp [evalMixedLinear_apply, pseudoBasisVec]

omit [NumberField K] in
/-- Extend the `k₀`-th coordinate functional of a `K`-basis `b` of `W` across a `K`-complement of
`W` in `ι → K`. -/
private theorem exists_linearMap_apply_basis_eq_ite [DecidableEq κ] (k₀ : κ) :
    ∃ f : (ι → K) →ₗ[K] K, ∀ k, f (b k : ι → K) = if k = k₀ then 1 else 0 := by
  obtain ⟨S, hS⟩ := W.exists_isCompl
  refine ⟨(b.coord k₀).comp (Submodule.projectionOnto W S hS), fun k ↦ ?_⟩
  rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_left hS (b k), Basis.coord_apply,
    b.repr_self, Finsupp.single_apply]

open scoped Classical in
private theorem linearIndependent_pseudoBasisVec [Finite ι] [Finite κ] :
    LinearIndependent ℝ (pseudoBasisVec b hJ) := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [Fintype.linearIndependent_iff]
  intro c hc ⟨k₀, ν₀⟩
  -- Extend the `k₀`-th `b`-coordinate to `ι → K`, then `mixedSpace K`-linearly to isolate `k₀`.
  obtain ⟨f, hf⟩ := exists_linearMap_apply_basis_eq_ite b k₀
  have hsum : ∑ ν : index K, c (k₀, ν) • (J k₀).mixedLatticeBasis (hJ k₀) ν = 0 := by
    have hm := congrArg (mixedExtend f) hc
    have hvec (p : κ × index K) :
        mixedExtend f (pseudoBasisVec b hJ p) =
          (J p.1).mixedLatticeBasis (hJ p.1) p.2 * mixedEmbedding K (f (b p.1 : ι → K)) := by
      simpa [pseudoBasisVec] using
        mixedExtend_toLp_mul f ((J p.1).mixedLatticeBasis (hJ p.1) p.2) (b p.1 : ι → K)
    rw [map_sum, map_zero] at hm
    simp_rw [map_smul, hvec, hf] at hm
    rw [Fintype.sum_prod_type] at hm
    simpa using hm
  exact Fintype.linearIndependent_iff.mp ((J k₀).mixedLatticeBasis (hJ k₀)).linearIndependent
    (fun ν ↦ c (k₀, ν)) hsum ν₀

open scoped Classical in
private theorem span_range_pseudoBasisVec [Finite ι] [Finite κ] :
    span ℝ (range (pseudoBasisVec b hJ)) = W.euclideanSpan := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨⟨k, ν⟩, rfl⟩
    have hmem : (J k).mixedBasisElem (hJ k) ν • (b k : ι → K) ∈ W :=
      W.smul_mem _ (b k).2
    simpa [pseudoBasisVec, Algebra.smul_def] using toLp_mem_euclideanSpan hmem
  · rintro _ ⟨v, hv, rfl⟩
    -- Expand `⟨v, hv⟩` in `b`, and each `K`-coordinate in `(J k).mixedLatticeBasis (hJ k)`.
    have hexp :
        (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) =
          ∑ p : κ × index K,
            ((J p.1).mixedLatticeBasis (hJ p.1)).repr (mixedEmbedding K (b.repr ⟨v, hv⟩ p.1)) p.2 •
              pseudoBasisVec b hJ p := by
      ext1 i
      apply (euclidean.toMixed K).injective
      have heval :
          evalMixedLinear i
            (WithLp.toLp 2 fun j ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v j))) =
          evalMixedLinear i (∑ p : κ × index K,
            ((J p.1).mixedLatticeBasis (hJ p.1)).repr (mixedEmbedding K (b.repr ⟨v, hv⟩ p.1)) p.2 •
              pseudoBasisVec b hJ p) := by
        rw [evalMixedLinear_apply, WithLp.ofLp_toLp, ContinuousLinearEquiv.apply_symm_apply,
          map_sum]
        simp only [map_smul, evalMixedLinear_pseudoBasisVec]
        rw [apply_eq_sum_repr_mul b hv i, map_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul,
          ← ((J k).mixedLatticeBasis (hJ k)).sum_repr (mixedEmbedding K (b.repr ⟨v, hv⟩ k)),
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ ↦ Algebra.smul_mul_assoc _ _ _
      exact heval
    dsimp only
    rw [hexp]
    exact sum_mem fun p _ ↦ smul_mem _ _ (subset_span ⟨p, rfl⟩)

open scoped Classical in
/-- The `ℝ`-basis of `W.euclideanSpan` attached to a `K`-basis `b` of `W` and nonzero ideals `J k`
of `𝓞 K`. -/
def euclideanSpanBasisOfPseudoBasis [Finite ι] [Finite κ] :
    Basis (κ × index K) ℝ W.euclideanSpan :=
  (Basis.span (linearIndependent_pseudoBasisVec b hJ)).map
    (LinearEquiv.ofEq _ _ (span_range_pseudoBasisVec b hJ))

open scoped Classical in
/-- Coordinates of `euclideanSpanBasisOfPseudoBasis b hJ` in the ambient Euclidean Minkowski
space. -/
@[simp]
theorem coe_euclideanSpanBasisOfPseudoBasis_apply [Finite ι] [Finite κ] (p : κ × index K) :
    ((euclideanSpanBasisOfPseudoBasis b hJ p : W.euclideanSpan) :
      PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm
        (mixedEmbedding K ((J p.1).mixedBasisElem (hJ p.1) p.2 * (b p.1 : ι → K) i)) := by
  simp [euclideanSpanBasisOfPseudoBasis, Basis.span_apply, pseudoBasisVec]

open scoped Classical in
/-- When `(b, J)` is a pseudo-basis of the integral points of `W`, the `ℤ`-span of
`euclideanSpanBasisOfPseudoBasis b hJ` is `W.integerLattice`. -/
theorem span_int_euclideanSpanBasisOfPseudoBasis [Finite ι] [Finite κ]
    (hW : W.IsIntegerPseudoBasis b J) :
    span ℤ (range (euclideanSpanBasisOfPseudoBasis b hJ)) = W.integerLattice := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  refine le_antisymm (span_le.2 ?_) (fun w hw ↦ ?_)
  · rintro _ ⟨⟨k, ν⟩, rfl⟩
    rw [SetLike.mem_coe, mem_integerLattice]
    have hint : ∀ i,
        (J k).mixedBasisElem (hJ k) ν * (b k : ι → K) i ∈ range (algebraMap (𝓞 K) K) := by
      simpa [Algebra.smul_def] using
        (hW ((J k).mixedBasisElem (hJ k) ν • b k)).2
          (b.repr_smul_self_mem_coeSubmodule J ((J k).mixedBasisElem_mem (hJ k) ν))
    intro i
    obtain ⟨a, ha⟩ := hint i
    rw [coe_euclideanSpanBasisOfPseudoBasis_apply, euclidean.integerLattice, ZLattice.comap,
      Submodule.mem_comap]
    exact ⟨a, by simp [← ha]⟩
  · obtain ⟨z, hzW, hwz⟩ := exists_mem_integerPoints_of_mem_integerLattice hw
    let wK : W := ⟨fun i ↦ (z i : K), hzW⟩
    have hwK : ∀ k, b.repr wK k ∈ IsLocalization.coeSubmodule K (J k) :=
      (hW wK).1 fun i ↦ ⟨z i, rfl⟩
    have hcoord (k : κ) : ∃ m : index K → ℤ,
        mixedEmbedding K (b.repr wK k) =
          ∑ ν : index K, m ν • (J k).mixedLatticeBasis (hJ k) ν := by
      have hm :=
        ((J k).mem_coeSubmodule_iff_mem_span_mixedLatticeBasis (hJ k) (b.repr wK k)).1 (hwK k)
      rw [((J k).mixedLatticeBasis (hJ k)).mem_span_iff_repr_mem ℤ] at hm
      choose m hm' using hm
      refine ⟨m, ?_⟩
      conv_lhs => rw [← ((J k).mixedLatticeBasis (hJ k)).sum_repr (mixedEmbedding K (b.repr wK k))]
      exact Finset.sum_congr rfl fun ν _ ↦ by
        rw [← hm' ν, eq_intCast, Int.cast_smul_eq_zsmul]
    choose m hm using hcoord
    let φ (i : ι) : W.euclideanSpan →ₗ[ℝ] mixedSpace K :=
      (evalMixedLinear i).comp W.euclideanSpan.subtype
    have hweq : w = ∑ p : κ × index K, m p.1 p.2 • euclideanSpanBasisOfPseudoBasis b hJ p := by
      ext1
      ext1 i
      apply (euclidean.toMixed K).injective
      have hφ : φ i w = φ i (∑ p : κ × index K,
          m p.1 p.2 • euclideanSpanBasisOfPseudoBasis b hJ p) := by
        rw [map_sum]
        simp only [φ, LinearMap.comp_apply, Submodule.coe_subtype, evalMixedLinear_apply, hwz,
          ContinuousLinearEquiv.apply_symm_apply, map_zsmul,
          coe_euclideanSpanBasisOfPseudoBasis_apply, map_mul]
        rw [apply_eq_sum_repr_mul b (mem_integerPoints.mp hzW) i, map_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul, hm k, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ν _ ↦ ?_
        rw [Ideal.mixedLatticeBasis_apply, ← Int.cast_smul_eq_zsmul ℝ,
          ← Int.cast_smul_eq_zsmul ℝ, Algebra.smul_mul_assoc]
      exact hφ
    rw [hweq]
    exact sum_mem fun p _ ↦ zsmul_mem (subset_span (mem_range_self p)) _

open scoped Classical in
/-- The `ℤ`-basis of `W.integerLattice` attached to a pseudo-basis `(b, J)` of `W.integerPoints`. -/
def integerLatticeBasisOfPseudoBasis [Finite ι] [Finite κ]
    (hW : W.IsIntegerPseudoBasis b J) :
    Basis (κ × index K) ℤ W.integerLattice :=
  ((euclideanSpanBasisOfPseudoBasis b hJ).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (span_int_euclideanSpanBasisOfPseudoBasis b hJ hW))

open scoped Classical in
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

open scoped Classical in
/-- The real span of `W` in the Euclidean Minkowski space has real dimension
`[K : ℚ] * finrank K W`. -/
theorem finrank_euclideanSpan :
    finrank ℝ W.euclideanSpan = finrank ℚ K * finrank K W := by
  cases nonempty_fintype ι
  obtain ⟨b, J, hJ, -⟩ := W.exists_pseudoBasis_integerPoints
  rw [finrank_eq_card_basis (euclideanSpanBasisOfPseudoBasis b hJ), Fintype.card_prod,
    Fintype.card_fin, ← finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank, mul_comm]

open scoped Classical in
/-- The real span of `⊤ : Submodule K (ι → K)` is the whole Euclidean Minkowski space. -/
@[simp]
theorem euclideanSpan_top : (⊤ : Submodule K (ι → K)).euclideanSpan = ⊤ := by
  cases nonempty_fintype ι
  refine eq_top_of_finrank_eq ?_
  rw [finrank_euclideanSpan, finrank_top, Module.finrank_fintype_fun_eq_card,
    LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)),
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, euclidean.finrank,
    mul_comm]

open scoped Classical in
/-- The integral lattice of `W` is discrete in `W.euclideanSpan`. -/
instance instDiscreteTopologyIntegerLattice : DiscreteTopology W.integerLattice := by
  cases nonempty_fintype ι
  obtain ⟨b, J, hJ, hW⟩ := W.exists_pseudoBasis_integerPoints
  rw [← span_int_euclideanSpanBasisOfPseudoBasis b hJ hW]
  infer_instance

end Instances

open scoped Classical in
/-- The Borel measurable structure on `W.euclideanSpan`. Declared explicitly because instance
search through `PiLp.borelSpace` and `euclidean.mixedSpace` times out when resolving
`MeasureSpace W.euclideanSpan`. -/
instance instBorelSpaceEuclideanSpan [Countable ι] (W : Submodule K (ι → K)) :
    BorelSpace W.euclideanSpan :=
  Subtype.borelSpace _

open scoped Classical in
/-- The canonical Euclidean Haar `MeasureSpace` on `W.euclideanSpan`. Declared explicitly so
`volume` resolves without hitting the `priority := 100` search depth of
`measureSpaceOfInnerProductSpace`. -/
instance instMeasureSpaceEuclideanSpan [Fintype ι] (W : Submodule K (ι → K)) :
    MeasureSpace W.euclideanSpan :=
  measureSpaceOfInnerProductSpace

open scoped Classical in
/-- The integral lattice of `W` spans `W.euclideanSpan` over `ℝ`: it is a full `ℤ`-lattice.
Note that `[Fintype ι]` is required in the statement because `IsZLattice ℝ W.integerLattice` takes
`[NormedAddCommGroup W.euclideanSpan]` via `PiLp.normedAddCommGroup`. -/
instance instIsZLatticeIntegerLattice [Fintype ι] (W : Submodule K (ι → K)) :
    IsZLattice ℝ W.integerLattice where
  span_top := by
    obtain ⟨b, J, hJ, hW⟩ := W.exists_pseudoBasis_integerPoints
    rw [← span_int_euclideanSpanBasisOfPseudoBasis b hJ hW]
    exact ZSpan.span_top _

open scoped Classical in
/-- The integral lattice of `W` is free over `ℤ` of rank `[K : ℚ] * finrank K W`. -/
theorem finrank_integerLattice [Finite ι] (W : Submodule K (ι → K)) :
    finrank ℤ W.integerLattice = finrank ℚ K * finrank K W := by
  cases nonempty_fintype ι
  rw [ZLattice.rank ℝ W.integerLattice, finrank_euclideanSpan]

end PseudoBasis

end EuclideanSpan

end Submodule

namespace TauCeti.NumberField.mixedEmbedding.euclidean

open scoped RealInnerProductSpace

/-- The linear equivalence `mixedSpace ℚ ≃ₗ[ℝ] ℝ` given by evaluation at `Rat.infinitePlace`. -/
private def mixedRatEquivReal : mixedSpace ℚ ≃ₗ[ℝ] ℝ :=
  haveI : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      (Subsingleton.elim w.1 Rat.infinitePlace ▸ Rat.isReal_infinitePlace)⟩
  { toFun x := x.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun r := (fun _ ↦ r, isEmptyElim)
    left_inv x := by
      ext w
      · exact congrArg x.1 (Subtype.ext (Subsingleton.elim Rat.infinitePlace w.1))
      · exact isEmptyElim w
    right_inv _ := rfl }

open scoped Classical in
/-- The canonical linear isometry identifying `euclidean.mixedSpace ℚ` with `ℝ` via the unique
infinite place of `ℚ`. -/
def mixedSpaceRatEquivReal : NumberField.mixedEmbedding.euclidean.mixedSpace ℚ ≃ₗᵢ[ℝ] ℝ :=
  { (NumberField.mixedEmbedding.euclidean.toMixed ℚ).toLinearEquiv.trans mixedRatEquivReal with
    norm_map' x := by
      let _ : Unique {w : InfinitePlace ℚ // w.IsReal} :=
        { default := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
          uniq w := Subtype.ext (Subsingleton.elim w.1 Rat.infinitePlace) }
      have _ : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
        ⟨fun w ↦ InfinitePlace.not_isReal_iff_isComplex.mpr w.2
          (Subsingleton.elim w.1 Rat.infinitePlace ▸ Rat.isReal_infinitePlace)⟩
      have hinner : ⟪x, x⟫ =
          ((NumberField.mixedEmbedding.euclidean.toMixed ℚ x).1
            ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩) ^ 2 := by
        rw [← TauCeti.NumberField.mixedEmbedding.mixedInner_toMixed,
          TauCeti.NumberField.mixedEmbedding.mixedInner_def, Fintype.sum_unique, Fintype.sum_empty,
          add_zero, sq]
        rfl
      rw [norm_eq_sqrt_real_inner x, hinner, Real.sqrt_sq_eq_abs, ← Real.norm_eq_abs]
      rfl }

open scoped Classical in
/-- `mixedSpaceRatEquivReal` sends the canonical embedding of `q : ℚ` to `(q : ℝ)`. -/
@[simp]
theorem mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding (q : ℚ) :
    mixedSpaceRatEquivReal
        ((NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ q)) =
      (q : ℝ) := by
  simp [mixedSpaceRatEquivReal, mixedRatEquivReal]

open scoped Classical in
/-- A point of `euclidean.mixedSpace ℚ` lies in `euclidean.integerLattice ℚ` if and only if its
image in `ℝ` under `mixedSpaceRatEquivReal` is an integer. -/
theorem mem_integerLattice_rat_iff (x : NumberField.mixedEmbedding.euclidean.mixedSpace ℚ) :
    x ∈ NumberField.mixedEmbedding.euclidean.integerLattice ℚ ↔
      ∃ z : ℤ, mixedSpaceRatEquivReal x = z := by
  have hmem :
      x ∈ NumberField.mixedEmbedding.euclidean.integerLattice ℚ ↔
        ∃ a : 𝓞 ℚ,
          mixedEmbedding ℚ a = NumberField.mixedEmbedding.euclidean.toMixed ℚ x := by
    simp [NumberField.mixedEmbedding.euclidean.integerLattice, ZLattice.comap]
  rw [hmem]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    have hx : x = (NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ a) := by
      apply (NumberField.mixedEmbedding.euclidean.toMixed ℚ).injective
      simpa using ha.symm
    refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
    rw [hx, mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding,
      RingOfIntegers.coe_eq_algebraMap, ← Rat.ringOfIntegersEquiv_apply_coe, Rat.cast_intCast]
  · rintro ⟨z, hz⟩
    refine ⟨Rat.ringOfIntegersEquiv.symm z, ?_⟩
    have hx : x =
        (NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ (z : ℚ)) := by
      apply mixedSpaceRatEquivReal.injective
      rw [hz, mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding, Rat.cast_intCast]
    rw [hx, ContinuousLinearEquiv.apply_symm_apply, Rat.ringOfIntegersEquiv_symm_apply_coe]

end TauCeti.NumberField.mixedEmbedding.euclidean

namespace Submodule

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

open scoped Classical in
private theorem map_euclideanSpan_rat [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    V.euclideanSpan.map
        ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal) :
          (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) →ₗ[ℝ] PiLp 2 fun _ : ι ↦ ℝ) =
      V.realSpan := by
  set E := LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal
  set f : (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) →ₗ[ℝ] PiLp 2 fun _ : ι ↦ ℝ := ↑E
  have hf : f = E.toLinearEquiv.toLinearMap := by
    ext x i
    simp [f]
  have hle : V.euclideanSpan.map f ≤ V.realSpan := by
    rw [map_le_iff_le_comap, euclideanSpan, span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hv' :
        f (WithLp.toLp 2 fun i ↦
            (NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ (v i))) =
          WithLp.toLp 2 fun i ↦ (v i : ℝ) := by
      ext1 i
      simp [f, E]
    simpa [hv'] using toLp_mem_realSpan hv
  have hdim : finrank ℝ (V.euclideanSpan.map f) = finrank ℝ V.realSpan := by
    rw [hf, LinearEquiv.finrank_map_eq E.toLinearEquiv, V.finrank_euclideanSpan,
      Module.finrank_self, one_mul, V.finrank_realSpan]
  exact eq_of_le_of_finrank_eq hle hdim

open scoped Classical in
/-- Over `ℚ`, `V.euclideanSpan` is canonically linearly isometric to `V.realSpan` coordinatewise
via `mixedSpaceRatEquivReal`. -/
def euclideanSpanEquivRealSpan [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    V.euclideanSpan ≃ₗᵢ[ℝ] V.realSpan :=
  (LinearIsometryEquiv.submoduleMap V.euclideanSpan
      (LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι ↦ mixedSpaceRatEquivReal)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_euclideanSpan_rat V))

open scoped Classical in
/-- Ambient coordinates of `V.euclideanSpanEquivRealSpan w`. -/
@[simp]
theorem coe_euclideanSpanEquivRealSpan_apply [Fintype ι] (V : Submodule ℚ (ι → ℚ))
    (w : V.euclideanSpan) (i : ι) :
    (V.euclideanSpanEquivRealSpan w : EuclideanSpace ℝ ι) i =
      mixedSpaceRatEquivReal ((w : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace ℚ) i) := by
  rw [euclideanSpanEquivRealSpan, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  simp

open scoped Classical in
/-- Over `ℚ`, pulling `V.intLattice` back along `V.euclideanSpanEquivRealSpan` recovers
`V.integerLattice`. -/
@[simp]
theorem comap_intLattice_euclideanSpanEquivRealSpan [Fintype ι] (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.comap ℝ V.intLattice V.euclideanSpanEquivRealSpan.toLinearMap = V.integerLattice := by
  ext w
  simp [ZLattice.comap, mem_integerLattice_rat_iff]

end Rat

end Submodule

namespace Matrix

open scoped Matrix NumberField

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The integral points of the `K`-kernel of an `𝓞 K`-matrix are precisely its `𝓞 K`-kernel. -/
@[simp]
theorem integerPoints_ker_mulVecLin {m : Type*} (A : Matrix m ι (𝓞 K)) :
    (LinearMap.ker (A.map (algebraMap (𝓞 K) K)).mulVecLin).integerPoints =
      LinearMap.ker A.mulVecLin := by
  ext z
  simp only [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff,
    Pi.zero_apply]
  refine forall_congr' fun i ↦ ?_
  have hcast : (((A *ᵥ z) i : 𝓞 K) : K) =
      (A.map (algebraMap (𝓞 K) K) *ᵥ fun j ↦ (z j : K)) i :=
    RingHom.map_mulVec (algebraMap (𝓞 K) K) A z i
  rw [← hcast, NumberField.RingOfIntegers.coe_eq_zero_iff]

end Matrix

end
