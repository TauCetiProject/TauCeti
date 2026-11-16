/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds
public import TauCeti.NumberTheory.NumberField.SubspaceIntegerPoints

import TauCeti.Algebra.Module.ZLattice.Covolume
import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
import TauCeti.LinearAlgebra.Pi
import TauCeti.MeasureTheory.Group.GeometryOfNumbers
import TauCeti.NumberTheory.Height.Arakelov.Comparison
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation

/-!
# Fixed-field Siegel's lemma in the Euclidean height

Let `K` be a number field of degree `D = [K : ℚ]` and discriminant `discr K`. For any nonzero
`K`-subspace `W` of `ι → K` of dimension `m`, there exists a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) whose absolute Euclidean height satisfies

```text
height2 z ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) *
              |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / m),
```

and hence, using `Γ(N / 2 + 1) ≤ (π * N / 4) ^ (N / 2)` (`Real.Gamma_div_two_add_one_le`),

```text
height2 z ≤ √m * |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / m).
```

Passing to the kernel of a finite family of nonzero linear forms `L : m → ι → K` with
`#m < #ι`, without any linear-independence hypothesis on the forms, gives Evertse and Ferretti's
fixed-field Siegel lemma: there exists a nonzero solution `x` with

```text
height2 x ≤ √(#ι) * |discr K| ^ (1 / (2 * D)) * (∏ i, height2 (L i)) ^ (1 / (#ι - #m)).
```

The proof applies Minkowski's shortest-vector bound (`ZLattice.exists_ne_zero_mem_norm_le`) inside
`W.euclideanSpan` to the image of `W.integerLattice` under the coordinatewise real-linear
automorphism scaling real places by `1` and complex places by `√2`. Because `W.euclideanSpan` is
stable under coordinatewise multiplication by `mixedSpace K`, this scaling has real determinant
`2 ^ (r₂ * m)`, cancelling the `2 ^ (-r₂ * m)` factor in Schmidt's covolume identity
(`Submodule.covolume_integerLattice`) while converting the ambient Euclidean norm squared into
the multiplicity-weighted sum `∑ w, w.mult * ∑ i, ‖w.embedding (z i)‖ ^ 2`. Weighted AM–GM and
integrality at finite places (`TauCeti.height2_le_sqrt_sum_mult_mul_sum_norm_sq_div`) then bound
`height2 z`.

## Main results

* `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_gamma_rpow`: the sharp Minkowski-ball
  form of Siegel's lemma for a nonzero subspace of `ι → K`.
* `Submodule.exists_ne_zero_mem_integerPoints_height2_le`: the `√(finrank K W)` bound for a
  nonzero integral point of a subspace.
* `Submodule.exists_ne_zero_mem_height2_le`: the `K`-vector form for a nonzero subspace.
* `Submodule.exists_ne_zero_mem_intPoints_height2_le`: the specialization to rational subspaces
  with solutions in `ℤ`.
* `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le`: fixed-field Siegel's lemma for `A *ᵥ z = 0`
  with integral solution `z : ι → 𝓞 K`, without row-independence or coordinate-ordering
  assumptions.
* `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le`: the specialization to rational matrices
  with integer solutions.
* `TauCeti.exists_ne_zero_height2_le`: fixed-field Siegel's lemma for a family of nonzero linear
  forms over a number field.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3.
-/

noncomputable section

open Complex MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators Matrix RealInnerProductSpace

section MultiplicityScaling

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- The element of `mixedSpace K` with coordinate `1` at every real place and `√2` at every complex
place. Multiplying a tuple coordinatewise by `multSqrt K` turns the ambient Euclidean squared norm
into the multiplicity-weighted sum `∑ w, w.mult * ∑ i, ‖w.embedding (x i)‖ ^ 2`. -/
private def multSqrt (K : Type*) [Field K] : mixedSpace K :=
  (fun _ ↦ 1, fun _ ↦ (√2 : ℂ))

open scoped Classical in
private theorem abs_algebraNorm_multSqrt :
    |Algebra.norm ℝ (multSqrt K)| = (2 : ℝ) ^ nrComplexPlaces K := by
  have hnorm : Algebra.norm ℝ (multSqrt K) = (2 : ℝ) ^ nrComplexPlaces K := by
    rw [mixedEmbedding.algebraNorm_apply]
    simp only [multSqrt, Finset.prod_const_one, one_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt zero_le_two, Finset.prod_const, Finset.card_univ]
  rw [hnorm, abs_of_pos (by positivity)]

open scoped Classical in
private theorem mixedInner_multSqrt_mul_self (u : mixedSpace K) :
    mixedInner K (multSqrt K * u) (multSqrt K * u) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * normAtPlace w u ^ 2 := by
  rw [mixedInner_self_eq_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  by_cases hw : w.IsReal
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw]
    simp [InfinitePlace.mult, hw, multSqrt]
  · have hwc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    rw [normAtPlace_apply_of_isComplex hwc, normAtPlace_apply_of_isComplex hwc]
    simp only [InfinitePlace.mult, hw, ↓reduceIte, Nat.cast_ofNat, Prod.snd_mul, Pi.mul_apply,
      multSqrt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow, Real.sq_sqrt zero_le_two]

open Classical in
/-- Coordinatewise multiplication by `c : mixedSpace K` on the ambient Euclidean Minkowski space. -/
private def mulMixedAmbient (c : mixedSpace K) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ]
      (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) where
  toFun x := WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (c * euclidean.toMixed K (x i))
  map_add' x y := by
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [mul_add]
  map_smul' r x := by
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [Algebra.mul_smul_comm]

private theorem mulMixedAmbient_apply (c : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    mulMixedAmbient c x i = (euclidean.toMixed K).symm (c * euclidean.toMixed K (x i)) := by
  simp [mulMixedAmbient]

private theorem mulMixedAmbient_mul (c₁ c₂ : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :
    mulMixedAmbient (c₁ * c₂) x = mulMixedAmbient c₁ (mulMixedAmbient c₂ x) := by
  ext1 i
  apply (euclidean.toMixed K).injective
  simp [mulMixedAmbient_apply, mul_assoc]

/-- `W.euclideanSpan` is closed under coordinatewise multiplication by any element of
`mixedSpace K`. -/
private theorem mulMixedAmbient_mem_euclideanSpan (W : Submodule K (ι → K)) (c : mixedSpace K) :
    ∀ x ∈ W.euclideanSpan, mulMixedAmbient c x ∈ W.euclideanSpan := by
  classical
  have hle : W.euclideanSpan ≤ W.euclideanSpan.comap (mulMixedAmbient c) := by
    rw [Submodule.euclideanSpan_le_iff]
    intro v hv
    rw [Submodule.mem_comap]
    have hc :
        c = ∑ j, (mixedEmbedding.latticeBasis K).repr c j •
          mixedEmbedding K (RingOfIntegers.basis K j) := by
      simpa only [mixedEmbedding.latticeBasis_apply, integralBasis_apply] using
        ((mixedEmbedding.latticeBasis K).sum_repr c).symm
    have hsum :
        mulMixedAmbient c
            (WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (mixedEmbedding K (v i))) =
          ∑ j, (mixedEmbedding.latticeBasis K).repr c j •
            WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm
              (mixedEmbedding K ((RingOfIntegers.basis K j : K) * v i)) := by
      ext1 i
      apply (euclidean.toMixed K).injective
      rw [mulMixedAmbient_apply, ContinuousLinearEquiv.apply_symm_apply, WithLp.ofLp_toLp,
        ContinuousLinearEquiv.apply_symm_apply, WithLp.ofLp_sum, Finset.sum_apply, map_sum]
      conv_lhs => rw [hc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [WithLp.ofLp_smul, Pi.smul_apply, map_smul, WithLp.ofLp_toLp,
        ContinuousLinearEquiv.apply_symm_apply, Algebra.smul_mul_assoc, map_mul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _
        (W.toLp_mem_euclideanSpan (W.smul_mem (RingOfIntegers.basis K j : K) hv))
  exact fun x hx ↦ hle hx

/-- Restriction of coordinatewise multiplication by `c : mixedSpace K` to `W.euclideanSpan`. -/
private def mulMixedSubmodule (W : Submodule K (ι → K)) (c : mixedSpace K) :
    W.euclideanSpan →ₗ[ℝ] W.euclideanSpan :=
  (mulMixedAmbient c).restrict (mulMixedAmbient_mem_euclideanSpan W c)

private theorem coe_mulMixedSubmodule (W : Submodule K (ι → K)) (c : mixedSpace K)
    (x : W.euclideanSpan) :
    (mulMixedSubmodule W c x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      mulMixedAmbient c (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :=
  rfl

private theorem mulMixedSubmodule_mul (W : Submodule K (ι → K)) (c₁ c₂ : mixedSpace K)
    (x : W.euclideanSpan) :
    mulMixedSubmodule W (c₁ * c₂) x = mulMixedSubmodule W c₁ (mulMixedSubmodule W c₂ x) := by
  apply Subtype.ext
  simp only [coe_mulMixedSubmodule, mulMixedAmbient_mul]

/-- The embedded `K`-basis vectors of `W` inside `W.euclideanSpan`. -/
private def basisVecEuclideanSpan [Fintype ι] (W : Submodule K (ι → K))
    (k : Fin (finrank K W)) : W.euclideanSpan :=
  ⟨WithLp.toLp 2 fun i ↦
      (euclidean.toMixed K).symm (mixedEmbedding K ((Module.finBasis K W k : ι → K) i)),
    W.toLp_mem_euclideanSpan (Module.finBasis K W k).2⟩

open Classical in
/-- The `ℝ`-linear map `(Fin (finrank K W) → mixedSpace K) →ₗ[ℝ] W.euclideanSpan` sending `z`
to the `mixedSpace K`-linear combination of the embedded `K`-basis vectors of `W`. -/
private def mixedSpaceToEuclideanSpan [Fintype ι] (W : Submodule K (ι → K)) :
    (Fin (finrank K W) → mixedSpace K) →ₗ[ℝ] W.euclideanSpan where
  toFun z := ∑ k : Fin (finrank K W), mulMixedSubmodule W (z k) (basisVecEuclideanSpan W k)
  map_add' z₁ z₂ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ Subtype.ext ?_
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [coe_mulMixedSubmodule, mulMixedAmbient_apply, add_mul]
  map_smul' r z := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Subtype.ext ?_
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [coe_mulMixedSubmodule, mulMixedAmbient_apply, Algebra.smul_mul_assoc]

private theorem mixedSpaceToEuclideanSpan_apply [Fintype ι] (W : Submodule K (ι → K))
    (z : Fin (finrank K W) → mixedSpace K) :
    mixedSpaceToEuclideanSpan W z =
      ∑ k : Fin (finrank K W), mulMixedSubmodule W (z k) (basisVecEuclideanSpan W k) :=
  rfl

/-- `mixedSpaceToEuclideanSpan W` is injective: extending each dual coordinate functional of
`Module.finBasis K W` to `ι → K` and pairing it coordinatewise recovers `z k₀`. -/
private theorem mixedSpaceToEuclideanSpan_injective [Fintype ι] (W : Submodule K (ι → K)) :
    Function.Injective (mixedSpaceToEuclideanSpan W) := by
  classical
  let b : Basis (Fin (finrank K W)) K W := Module.finBasis K W
  obtain ⟨π, hπ⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let f (k₀ : Fin (finrank K W)) : (ι → K) →ₗ[K] K := (b.coord k₀).comp π
  have hf (k₀ k : Fin (finrank K W)) : f k₀ (b k : ι → K) = if k = k₀ then 1 else 0 := by
    have hπb : π (b k : ι → K) = b k := LinearMap.congr_fun hπ (b k)
    simp [f, hπb, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [injective_iff_map_eq_zero]
  intro z hz
  ext1 k₀
  let extF : (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] mixedSpace K :=
    { toFun := fun x ↦
        ∑ i : ι, mixedEmbedding K (f k₀ (Pi.single i 1)) * euclidean.toMixed K (x i)
      map_add' := fun x y ↦ by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x ↦ by simp [Algebra.mul_smul_comm, Finset.smul_sum] }
  have h0 : extF (mixedSpaceToEuclideanSpan W z : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) = 0 :=
    by rw [hz, ZeroMemClass.coe_zero, map_zero]
  have hcoe : (mixedSpaceToEuclideanSpan W z : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
      ∑ k : Fin (finrank K W),
        (mulMixedSubmodule W (z k) (basisVecEuclideanSpan W k) :
          PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) := by
    rw [mixedSpaceToEuclideanSpan_apply, ← W.euclideanSpan.coe_subtype]
    exact map_sum W.euclideanSpan.subtype _ _
  have hterm (k : Fin (finrank K W)) :
      extF (mulMixedSubmodule W (z k) (basisVecEuclideanSpan W k) :
          PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) =
        if k = k₀ then z k else 0 := by
    simp only [extF, LinearMap.coe_mk, AddHom.coe_mk, coe_mulMixedSubmodule,
      mulMixedAmbient_apply, basisVecEuclideanSpan, ContinuousLinearEquiv.apply_symm_apply]
    have hdot :
        ∑ i : ι, mixedEmbedding K (f k₀ (Pi.single i 1)) *
            (z k * mixedEmbedding K ((b k : ι → K) i)) =
          z k * mixedEmbedding K (f k₀ (b k : ι → K)) := by
      have hb_exp : (b k : ι → K) = ∑ i : ι, (b k : ι → K) i • Pi.single i 1 := by
        ext1 j; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hb_exp, map_sum]
      simp only [map_smul, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hdot, hf k₀ k]
    split_ifs <;> simp
  rw [hcoe, map_sum] at h0
  simp_rw [hterm] at h0
  simpa using h0

/-- The `ℝ`-linear determinant of coordinatewise multiplication by `c` on `W.euclideanSpan` is
`(Algebra.norm ℝ c) ^ finrank K W`. -/
private theorem det_mulMixedSubmodule [Finite ι] (W : Submodule K (ι → K)) (c : mixedSpace K) :
    LinearMap.det (mulMixedSubmodule W c) = (Algebra.norm ℝ c) ^ finrank K W := by
  classical
  cases nonempty_fintype ι
  set m := finrank K W
  have hfin : finrank ℝ (Fin m → mixedSpace K) = finrank ℝ W.euclideanSpan := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mixedEmbedding.finrank, W.finrank_euclideanSpan, mul_comm]
  have hΦ_inj := mixedSpaceToEuclideanSpan_injective W
  have hΦ_bij : Function.Bijective (mixedSpaceToEuclideanSpan W) :=
    ⟨hΦ_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hΦ_inj⟩
  let eΦ : (Fin m → mixedSpace K) ≃ₗ[ℝ] W.euclideanSpan :=
    LinearEquiv.ofBijective (mixedSpaceToEuclideanSpan W) hΦ_bij
  have hconj :
      mulMixedSubmodule W c =
        (eΦ : (Fin m → mixedSpace K) →ₗ[ℝ] W.euclideanSpan) ∘ₗ
          (LinearMap.piMap fun _ : Fin m ↦ Algebra.lmul ℝ (mixedSpace K) c) ∘ₗ
          (eΦ.symm : W.euclideanSpan →ₗ[ℝ] (Fin m → mixedSpace K)) := by
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨z, rfl⟩ := eΦ.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp only [eΦ, LinearEquiv.ofBijective_apply, LinearMap.coe_piMap]
    rw [mixedSpaceToEuclideanSpan_apply, mixedSpaceToEuclideanSpan_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Pi.map_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mulMixedSubmodule_mul]
  rw [hconj, LinearMap.det_conj, LinearMap.det_piMap]
  simp [Algebra.norm_apply]

open Classical in
/-- For an integral point `z ∈ W.integerPoints`, the squared Euclidean norm of its `multSqrt K`
scaling equals the multiplicity-weighted sum `∑ w, w.mult * ∑ i, ‖w.embedding (z i)‖ ^ 2`. -/
private theorem norm_sq_mulMixedSubmodule_multSqrt [Fintype ι] (W : Submodule K (ι → K))
    (z : W.integerPoints) :
    ‖mulMixedSubmodule W (multSqrt K)
        (W.integerPointsEquivIntegerLattice z : W.euclideanSpan)‖ ^ 2 =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i : ι, ‖w.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, PiLp.inner_apply]
  have hterm (i : ι) :
      ⟪(mulMixedSubmodule W (multSqrt K)
          (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) :
          PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i,
        (mulMixedSubmodule W (multSqrt K)
          (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) :
          PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) i⟫ =
        ∑ w : InfinitePlace K, (w.mult : ℝ) * ‖w.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2 := by
    rw [coe_mulMixedSubmodule, mulMixedAmbient_apply,
      Submodule.coe_integerPointsEquivIntegerLattice_apply, WithLp.ofLp_toLp,
      ContinuousLinearEquiv.apply_symm_apply, ← mixedInner_toMixed,
      ContinuousLinearEquiv.apply_symm_apply, mixedInner_multSqrt_mul_self]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply, InfinitePlace.norm_embedding_eq]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]

end MultiplicityScaling

public section

namespace Submodule

section NumberField

variable {K ι : Type*} [Field K] [NumberField K] [Finite ι] [LinearOrder ι]

open Classical in
/-- **Fixed-field Siegel's lemma for a subspace (sharp Minkowski-ball constant).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) with
`height2 z ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) * |discr K| ^ (1 / (2 * D)) *
  W.subspaceHeight ^ (1 / m)`, where `D = [K : ℚ]`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_mul_gamma_rpow {W : Submodule K (ι → K)}
    (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        2 / √((finrank ℚ K : ℝ) * Real.pi) *
          Real.Gamma ((finrank ℚ K * finrank K W : ℝ) / 2 + 1) ^
            ((finrank ℚ K * finrank K W : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  cases nonempty_fintype ι
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  set D : ℕ := finrank ℚ K
  set m : ℕ := finrank K W
  set N : ℕ := D * m
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr finrank_pos
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr finrank_pos
  have hfin : finrank ℝ W.euclideanSpan = N := W.finrank_euclideanSpan
  have : Nontrivial W.euclideanSpan := by
    rw [← finrank_pos_iff (R := ℝ), hfin]
    exact Nat.mul_pos finrank_pos finrank_pos
  set T := mulMixedSubmodule W (multSqrt K)
  have hT_abs_det : |LinearMap.det T| = (2 : ℝ) ^ (nrComplexPlaces K * m) := by
    rw [det_mulMixedSubmodule, abs_pow, abs_algebraNorm_multSqrt, ← pow_mul]
  have hT_det : LinearMap.det T ≠ 0 := by
    rw [← abs_ne_zero, hT_abs_det]
    positivity
  -- Apply Minkowski's shortest-vector bound to the scaled lattice `T (W.integerLattice)`.
  let eT : W.euclideanSpan ≃L[ℝ] W.euclideanSpan :=
    (T.equivOfDetNeZero hT_det).toContinuousLinearEquiv
  let L' : Submodule ℤ W.euclideanSpan := ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap
  have hcov : ZLattice.covolume L' = (√|(discr K : ℝ)|) ^ m * W.subspaceHeight ^ D := by
    rw [ZLattice.covolume_comap_continuousLinearEquiv W.integerLattice eT.symm volume,
      W.covolume_integerLattice]
    have hdet_symm : |eT.symm.toLinearMap.det|⁻¹ = |LinearMap.det T| := by
      rw [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv, inv_inv]
      rfl
    rw [hdet_symm, hT_abs_det, mul_pow, ← pow_mul, inv_pow]
    dsimp only [D, m]
    field_simp
  -- Pull back a shortest nonzero vector of `L'` to an integral point `z ∈ W.integerPoints`.
  obtain ⟨x, hxL', hx0, hx_norm⟩ := ZLattice.exists_ne_zero_mem_norm_le L'
  have hwL : eT.symm x ∈ W.integerLattice := hxL'
  set z : W.integerPoints := W.integerPointsEquivIntegerLattice.symm ⟨eT.symm x, hwL⟩
  have hz_ne : (z : ι → 𝓞 K) ≠ 0 := by
    intro hz0
    apply hx0
    have h0 : (⟨eT.symm x, hwL⟩ : W.integerLattice) = 0 :=
      (W.integerPointsEquivIntegerLattice.symm.map_eq_zero_iff).mp (Subtype.ext hz0)
    exact eT.symm.injective ((congrArg Subtype.val h0).trans (map_zero eT.symm).symm)
  have hsum_eq :
      ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i : ι, ‖v.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2 =
        ‖x‖ ^ 2 := by
    have hzw : (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) = eT.symm x :=
      congrArg Subtype.val (W.integerPointsEquivIntegerLattice.apply_symm_apply ⟨eT.symm x, hwL⟩)
    have hTx : T (eT.symm x) = x := eT.apply_symm_apply x
    rw [← hTx, ← hzw]
    exact (norm_sq_mulMixedSubmodule_multSqrt W z).symm
  -- Rewrite `(covolume L') ^ (1 / (D * m))` and conclude via weighted AM–GM at infinite places.
  have hcov_rpow :
      ZLattice.covolume L' ^ ((N : ℝ)⁻¹) =
        |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ ((m : ℝ)⁻¹) := by
    rw [hcov, Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le _),
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul (Submodule.subspaceHeight_pos W).le, Nat.cast_mul]
    congr 1 <;> congr 1 <;> field_simp [hD.ne', hm.ne']
  refine ⟨z, z.2, hz_ne, ?_⟩
  rw [hfin, hcov_rpow] at hx_norm
  calc height2 (fun i ↦ ((z : ι → 𝓞 K) i : K))
      ≤ √((∑ v : InfinitePlace K,
            (v.mult : ℝ) * ∑ i : ι, ‖v.embedding ((z : ι → 𝓞 K) i : K)‖ ^ 2) / D) :=
        height2_le_sqrt_sum_mult_mul_sum_norm_sq_div (z : ι → 𝓞 K)
    _ = ‖x‖ / √(D : ℝ) := by
        rw [hsum_eq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (2 / √Real.pi * Real.Gamma ((N : ℝ) / 2 + 1) ^ ((N : ℝ)⁻¹) *
          (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ ((m : ℝ)⁻¹))) /
          √(D : ℝ) := div_le_div_of_nonneg_right hx_norm (Real.sqrt_nonneg _)
    _ = 2 / √((D : ℝ) * Real.pi) *
          Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) *
          W.subspaceHeight ^ ((m : ℝ)⁻¹) := by
        rw [Nat.cast_mul, Real.sqrt_mul hD.le]
        ring

/-- **Fixed-field Siegel's lemma for a subspace (integral point).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) with
`height2 z ≤ √m * |discr K| ^ (1 / (2 * [K : ℚ])) * W.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        √(finrank K W : ℝ) * |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨z, hzW, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le_mul_gamma_rpow hW
  refine ⟨z, hzW, hz0, hle.trans ?_⟩
  set D : ℕ := finrank ℚ K
  set m : ℕ := finrank K W
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr finrank_pos
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr finrank_pos
  have hN : (0 : ℝ) < D * m := mul_pos hD hm
  have hΓ : Real.Gamma ((D * m : ℝ) / 2 + 1) ≤ (Real.pi * ((D : ℝ) * m) / 4) ^ ((D * m : ℝ) / 2) :=
    by simpa [Nat.cast_mul] using
      Real.Gamma_div_two_add_one_le (Nat.mul_pos (finrank_pos (R := ℚ) (M := K)) finrank_pos)
  have h4 : √(4 : ℝ) = 2 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
    norm_num
  have hΓrpow :
      Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) ≤
        √((D : ℝ) * Real.pi) * √(m : ℝ) / 2 := by
    calc Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹)
        ≤ ((Real.pi * ((D : ℝ) * m) / 4) ^ ((D * m : ℝ) / 2)) ^ ((D * m : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Real.Gamma_pos_of_pos (by positivity)).le hΓ (by positivity)
      _ = (Real.pi * ((D : ℝ) * m) / 4) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1; field_simp [hN.ne']
      _ = √((D : ℝ) * Real.pi) * √(m : ℝ) / 2 := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), h4,
            mul_comm Real.pi, mul_assoc, mul_comm (m : ℝ) Real.pi, ← mul_assoc,
            Real.sqrt_mul (by positivity)]
  have hconst :
      2 / √((D : ℝ) * Real.pi) * Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) ≤ √(m : ℝ) := by
    calc 2 / √((D : ℝ) * Real.pi) * Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹)
        ≤ 2 / √((D : ℝ) * Real.pi) * (√((D : ℝ) * Real.pi) * √(m : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hΓrpow (by positivity)
      _ = √(m : ℝ) := by
          have hsq : √((D : ℝ) * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          field_simp [hsq]
  have hfac :
      0 ≤ |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ (m : ℝ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (Submodule.subspaceHeight_pos W).le _)
  calc 2 / √((D : ℝ) * Real.pi) * Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ (m : ℝ)⁻¹
      = (2 / √((D : ℝ) * Real.pi) * Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹)) *
          (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ (m : ℝ)⁻¹) := by ring
    _ ≤ √(m : ℝ) * (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ (m : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hconst hfac
    _ = √(m : ℝ) * |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ (m : ℝ)⁻¹ := by ring

/-- **Fixed-field Siegel's lemma for a subspace (`K`-vector form).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero vector `x ∈ W` with
`height2 x ≤ √m * |discr K| ^ (1 / (2 * [K : ℚ])) * W.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_height2_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ x ∈ W, x ≠ 0 ∧
      height2 x ≤
        √(finrank K W : ℝ) * |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  obtain ⟨z, hzW, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le hW
  exact ⟨fun i ↦ (z i : K), mem_integerPoints.mp hzW,
    mt RingOfIntegers.coe_tuple_eq_zero_iff.mp hz0, hle⟩

end NumberField

section Rat

variable {ι : Type*} [Finite ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the Euclidean height.**
Every nonzero subspace `V` of `ℚ^ι` of dimension `m` contains a nonzero integral point
`z ∈ V.intPoints` with `height2 z ≤ √m * V.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_intPoints_height2_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(finrank ℚ V : ℝ) * V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  obtain ⟨z, hzV, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le hV
  let w : V.intPoints := V.integerPointsEquivIntPoints ⟨z, hzV⟩
  have hw0 : (w : ι → ℤ) ≠ 0 := by
    intro h
    apply hz0
    have : (⟨z, hzV⟩ : V.integerPoints) = 0 :=
      (V.integerPointsEquivIntPoints.map_eq_zero_iff).mp (Subtype.ext h)
    exact congrArg Subtype.val this
  have hcoe : (fun i ↦ ((w : ι → ℤ) i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  refine ⟨w, w.2, hw0, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

end Submodule

namespace Matrix

section NumberField

variable {K m ι : Type*} [Field K] [NumberField K] [Fintype m] [Fintype ι]

/-- **Fixed-field Siegel's lemma for a linear system over a number field (integral solution).**
Let `A` be a matrix of `#m < #ι` nonzero linear forms in `#ι` variables over a number field `K`,
with no linear-independence assumption on its rows. Then `A *ᵥ z = 0` has a nonzero integral
solution `z : ι → 𝓞 K` with
`height2 z ≤ √(#ι) * |discr K| ^ (1 / (2 * [K : ℚ])) * (∏ i, height2 (A.row i)) ^ (1 / (#ι - #m))`.
-/
theorem exists_ne_zero_mulVec_eq_zero_height2_le {A : Matrix m ι K} (hA : ∀ i, A.row i ≠ 0)
    (hlt : Fintype.card m < Fintype.card ι) :
    ∃ z : ι → 𝓞 K, z ≠ 0 ∧ A *ᵥ (fun i ↦ (z i : K)) = 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        √(Fintype.card ι : ℝ) * |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  set W : Submodule K (ι → K) := LinearMap.ker A.mulVecLin
  have hrank : finrank K (LinearMap.range A.mulVecLin) + finrank K W = Fintype.card ι := by
    simpa [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrange_le : finrank K (LinearMap.range A.mulVecLin) ≤ Fintype.card m := by
    calc finrank K (LinearMap.range A.mulVecLin)
        ≤ finrank K (m → K) := Submodule.finrank_le _
      _ = Fintype.card m := Module.finrank_fintype_fun_eq_card K
  have hdiff_le : Fintype.card ι - Fintype.card m ≤ finrank K W := by omega
  have hdiff_pos : 0 < Fintype.card ι - Fintype.card m := Nat.sub_pos_of_lt hlt
  have hW_dim_pos : 0 < finrank K W := lt_of_lt_of_le hdiff_pos hdiff_le
  have hW_ne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW_dim_pos
    exact lt_irrefl 0 hW_dim_pos
  have hW_dim_le : finrank K W ≤ Fintype.card ι := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W
  obtain ⟨z, hzW, hz0, hle⟩ := W.exists_ne_zero_mem_integerPoints_height2_le hW_ne
  have hmul : A *ᵥ (fun i ↦ (z i : K)) = 0 := by
    simpa [W, Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] using hzW
  have hprod_ge_one : (1 : ℝ) ≤ ∏ i : m, height2 (A.row i) :=
    Finset.one_le_prod₀ fun i _ ↦ one_le_height2_of_ne_zero (hA i)
  have hH_le : W.subspaceHeight ≤ ∏ i : m, height2 (A.row i) :=
    Matrix.subspaceHeight_ker_mulVecLin_le_prod hA
  have hsqrt_le : √(finrank K W : ℝ) ≤ √(Fintype.card ι : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hW_dim_le)
  have hexp_le : (finrank K W : ℝ)⁻¹ ≤ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast hdiff_pos) (by exact_mod_cast hdiff_le)
  have hrpow_le :
      W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ ≤
        (∏ i : m, height2 (A.row i)) ^ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ :=
    calc W.subspaceHeight ^ (finrank K W : ℝ)⁻¹
        ≤ (∏ i : m, height2 (A.row i)) ^ (finrank K W : ℝ)⁻¹ :=
          Real.rpow_le_rpow (Submodule.subspaceHeight_pos W).le hH_le (by positivity)
      _ ≤ (∏ i : m, height2 (A.row i)) ^ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow_of_exponent_le hprod_ge_one hexp_le
  refine ⟨z, hz0, hmul, hle.trans ?_⟩
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hsqrt_le (Real.rpow_nonneg (abs_nonneg _) _))
    hrpow_le
    (Real.rpow_nonneg (Submodule.subspaceHeight_pos W).le _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _))

end NumberField

section Rat

variable {m ι : Type*} [Fintype m] [Fintype ι]

/-- **Siegel's lemma for a rational linear system, in the Euclidean height.**
For any matrix `A : Matrix m ι ℚ` of `#m < #ι` nonzero rows (without row independence), `A *ᵥ z = 0`
has a nonzero integer solution `z : ι → ℤ` with
`height2 z ≤ √(#ι) * (∏ i, height2 (A.row i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_int_mulVec_eq_zero_height2_le {A : Matrix m ι ℚ} (hA : ∀ i, A.row i ≠ 0)
    (hlt : Fintype.card m < Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ A *ᵥ (fun i ↦ (z i : ℚ)) = 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(Fintype.card ι : ℝ) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ := by
  obtain ⟨z, hz0, hmul, hle⟩ := exists_ne_zero_mulVec_eq_zero_height2_le hA hlt
  let w : ι → ℤ := fun i ↦ Rat.ringOfIntegersEquiv (z i)
  have hcoe : (fun i ↦ (w i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  have hw0 : w ≠ 0 := by
    intro h
    apply hz0
    ext1 i
    exact Rat.ringOfIntegersEquiv.injective (by simpa [w] using congrFun h i)
  refine ⟨w, hw0, hcoe.symm ▸ hmul, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

end Matrix

namespace TauCeti

variable {K m ι : Type*} [Field K] [NumberField K] [Fintype m] [Fintype ι]

/-- **Fixed-field Siegel's lemma (Evertse–Ferretti, Lemma 13.1).**
For any family `L : m → ι → K` of `#m < #ι` nonzero linear forms in `#ι` variables over a number
field `K`, without any linear-independence hypothesis on `L`, there exists a nonzero vector
`x : ι → K` annihilated by every `L i` whose absolute Euclidean height satisfies
`height2 x ≤ √(#ι) * |discr K| ^ (1 / (2 * [K : ℚ])) * (∏ i, height2 (L i)) ^ (1 / (#ι - #m))`.
-/
theorem exists_ne_zero_height2_le {L : m → ι → K} (hL : ∀ i, L i ≠ 0)
    (hlt : Fintype.card m < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ (∀ i, L i ⬝ᵥ x = 0) ∧
      height2 x ≤
        √(Fintype.card ι : ℝ) * |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          (∏ i, height2 (L i)) ^ ((Fintype.card ι - Fintype.card m : ℕ) : ℝ)⁻¹ := by
  obtain ⟨z, hz0, hmul, hle⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_height2_le (A := Matrix.of L) hL hlt
  refine ⟨fun i ↦ (z i : K), mt RingOfIntegers.coe_tuple_eq_zero_iff.mp hz0, ?_, hle⟩
  intro i
  simpa [Matrix.mulVec, Matrix.of_apply] using congrFun hmul i

end TauCeti

end

end
