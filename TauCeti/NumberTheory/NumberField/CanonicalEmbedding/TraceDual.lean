/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation
import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.NumberTheory.NumberField.InfinitePlace.Trace

/-!
# The Euclidean dual of an ideal lattice is its trace dual

The mixed space `mixedSpace K = ℝ^r₁ × ℂ^r₂` of a number field `K` carries two pairings: the
Euclidean pairing `mixedInner`, in which a complex coordinate counts once and which is positive
definite, and the trace form `Tr_{K/ℚ} (x y)`, which is defined on `K` and is not positive at a
complex place. The linear automorphism `traceToEuclidean K`, the identity on the real coordinates
and `z ↦ 2 conj z` on the complex coordinates, converts one into the other: for `x y : K`,

`mixedInner K (σ x) (traceToEuclidean K (σ y)) = Tr_{K/ℚ} (x y)`

(`mixedInner_mixedEmbedding_traceToEuclidean`), where `σ = mixedEmbedding K`.

Consequently the Euclidean dual `mixedDual K σ(I)` of the lattice of a fractional ideal `I` is the
lattice of its trace dual `I^∨ = FractionalIdeal.dual ℤ ℚ I`, which is `(I 𝔡)⁻¹` for the different
`𝔡` of `K` (Mathlib's `FractionalIdeal.dual_eq_mul_inv`), moved by `traceToEuclidean K`
(`mixedDual_idealLattice`). One complex coordinate of `traceToEuclidean K` has real determinant
`-4` (`det_traceToEuclidean`), so comparing covolumes gives
`covol σ(I^∨) = 4^(-r₂) covol σ(I)⁻¹` (`covolume_idealLattice_dual`). This is the form in which
the dual lattice enters the theta transformation of Hecke's proof of the functional equation of
the Dedekind zeta function.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.traceToEuclidean`: the identity on the real coordinates and
  `z ↦ 2 conj z` on the complex coordinates of the mixed space.

## Main statements

* `TauCeti.NumberField.mixedEmbedding.mixedInner_mixedEmbedding_traceToEuclidean`:
  `mixedInner K (σ x) (traceToEuclidean K (σ y)) = Tr_{K/ℚ} (x y)`.
* `TauCeti.NumberField.mixedEmbedding.det_traceToEuclidean`: its determinant is `(-4) ^ r₂`.
* `TauCeti.NumberField.mixedEmbedding.comap_mixedDual_idealLattice`,
  `TauCeti.NumberField.mixedEmbedding.mixedDual_idealLattice`: the Euclidean dual of `σ(I)` is
  `traceToEuclidean K` applied to `σ(I^∨)`.
* `TauCeti.NumberField.mixedEmbedding.covolume_idealLattice_dual`:
  `covol σ(I^∨) = (4 ^ r₂)⁻¹ * covol σ(I)⁻¹`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §5 and Chapter VII, §3.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ComplexConjugate nonZeroDivisors

namespace TauCeti.NumberField.mixedEmbedding

variable (K : Type*) [Field K]

/-! ### The change of pairing -/

/-- The linear automorphism of the mixed space that is the identity on the real coordinates and
`z ↦ 2 conj z` on the complex coordinates. It carries the trace form of `K` to the Euclidean
pairing: `mixedInner K (σ x) (traceToEuclidean K (σ y)) = Tr_{K/ℚ} (x y)`
(`mixedInner_mixedEmbedding_traceToEuclidean`). -/
noncomputable def traceToEuclidean : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr
    (ContinuousLinearEquiv.piCongrRight fun _ ↦
      Complex.conjCLE.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)))

variable {K}

@[simp]
theorem traceToEuclidean_apply_isReal (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (traceToEuclidean K x).1 w = x.1 w := by
  simp [traceToEuclidean]

@[simp]
theorem traceToEuclidean_apply_isComplex (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (traceToEuclidean K x).2 w = 2 * conj (x.2 w) := by
  simp [traceToEuclidean, Units.smul_def, Complex.real_smul]

variable [NumberField K]

open scoped Classical in
/-- **The Euclidean pairing against `traceToEuclidean` is the trace form**: for `x y : K`,
`mixedInner K (σ x) (traceToEuclidean K (σ y)) = Tr_{K/ℚ} (x y)`. -/
theorem mixedInner_mixedEmbedding_traceToEuclidean (x y : K) :
    mixedInner K (mixedEmbedding K x) (traceToEuclidean K (mixedEmbedding K y)) =
      Algebra.trace ℚ K (x * y) := by
  rw [← sum_mult_mul_re_embedding_eq_trace, sum_eq_sum_add_sum, mixedInner_def]
  congr 1 <;> refine Finset.sum_congr rfl fun w _ ↦ ?_
  · rw [mult_isReal, Nat.cast_one, one_mul, ← embedding_of_isReal_apply w.2, Complex.ofReal_re,
      map_mul]
    simp
  · simp only [mixedEmbedding_apply_isComplex, traceToEuclidean_apply_isComplex, map_mul,
      Complex.conj_conj, mult_isComplex, Nat.cast_ofNat]
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

variable (K)

open scoped Classical in
/-- The determinant of `traceToEuclidean K` is `(-4) ^ r₂`: each complex coordinate
`z ↦ 2 conj z` has real determinant `2 ^ 2 * (-1) = -4`. -/
theorem det_traceToEuclidean :
    LinearMap.det (traceToEuclidean K : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      (-4) ^ nrComplexPlaces K := by
  have h : (traceToEuclidean K : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.prodMap LinearMap.id (LinearMap.pi fun w ↦
        ((2 : ℝ) • Complex.conjAe.toLinearEquiv.toLinearMap) ∘ₗ LinearMap.proj w) := by
    refine LinearMap.ext fun x ↦ ?_
    ext w
    · simp
    · simp [Complex.real_smul]
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_pi, Finset.prod_const,
    LinearMap.det_smul, Complex.finrank_real_complex, Complex.det_conjAe, Finset.card_univ,
    nrComplexPlaces]
  norm_num

open scoped Classical in
/-- The absolute value of the determinant of `traceToEuclidean K` is `4 ^ r₂`. -/
theorem abs_det_traceToEuclidean :
    |LinearMap.det (traceToEuclidean K : mixedSpace K →ₗ[ℝ] mixedSpace K)| =
      4 ^ nrComplexPlaces K := by
  rw [det_traceToEuclidean, abs_pow, abs_neg, abs_of_pos four_pos]

/-! ### The dual of an ideal lattice -/

/-- Two points of the mixed space with the same Euclidean pairing against every vector of a basis
are equal. -/
private theorem eq_of_forall_mixedInner_eq {ι : Type*} (b : Basis ι ℝ (mixedSpace K))
    {u v : mixedSpace K} (h : ∀ i, mixedInner K (b i) u = mixedInner K (b i) v) : u = v := by
  classical
  have hf : (mixedInnerBilin K).flip (u - v) = 0 :=
    b.ext fun i ↦ by simp [map_sub, h]
  have h0 : mixedInner K (u - v) (u - v) = 0 := by
    rw [← mixedInnerBilin_apply, ← LinearMap.flip_apply, hf, LinearMap.zero_apply]
  obtain ⟨z, hz⟩ := (euclidean.toMixed K).surjective (u - v)
  rw [← hz, mixedInner_toMixed, inner_self_eq_zero] at h0
  rw [← sub_eq_zero, ← hz, h0, map_zero]

variable {K}

open scoped Classical in
/-- **The Euclidean dual of an ideal lattice is its trace dual**: pulled back along
`traceToEuclidean K`, the Euclidean dual `mixedDual K σ(I)` of the lattice of a fractional ideal
`I` is the lattice `σ(J)` of its trace dual `J = I^∨ = FractionalIdeal.dual ℤ ℚ I`. -/
theorem comap_mixedDual_idealLattice {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ZLattice.comap ℝ (mixedDual K (idealLattice K I)) (traceToEuclidean K).toLinearMap =
      idealLattice K J := by
  ext y
  simp only [ZLattice.mem_comap, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    mem_mixedDual, mem_idealLattice]
  constructor
  · intro h
    -- Read the integral pairings of `y` against the basis `σ(β)` of `σ(I)` as the coordinates of
    -- a point of `J` in the trace dual basis `β^∨`.
    let β := basisOfFractionalIdeal K I
    have hβ (i) : β i ∈ (I : Set K) :=
      (mem_span_basisOfFractionalIdeal K).mp (Submodule.subset_span (Set.mem_range_self i))
    choose n hn using fun i ↦ h _ ⟨β i, hβ i, rfl⟩
    refine ⟨∑ i, (n i : ℚ) • β.traceDual i, ?_, ?_⟩
    · have hspan : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K).restrictScalars ℤ = Submodule.span ℤ (Set.range β.traceDual) := by
        rw [FractionalIdeal.coe_dual _ _ I.ne_zero]
        refine Submodule.traceDual_span_of_basis ℤ _ β ?_
        ext x
        simp [β, mem_span_basisOfFractionalIdeal]
      have : ∑ i, (n i : ℚ) • β.traceDual i ∈ Submodule.span ℤ (Set.range β.traceDual) :=
        Submodule.sum_mem _ fun i _ ↦ by
          rw [Int.cast_smul_eq_zsmul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
      rw [← hspan] at this
      rwa [SetLike.mem_coe, hJ]
    · refine (traceToEuclidean K).injective
        (eq_of_forall_mixedInner_eq K (fractionalIdealLatticeBasis K I) fun i ↦ ?_)
      rw [fractionalIdealLatticeBasis_apply, mixedInner_mixedEmbedding_traceToEuclidean, hn i]
      simp [Finset.mul_sum, β]
  · rintro ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, hJ, FractionalIdeal.mem_dual I.ne_zero] at hx
    obtain ⟨n, hn⟩ := hx a ha
    refine ⟨n, ?_⟩
    rw [mixedInner_mixedEmbedding_traceToEuclidean, mul_comm, ← Algebra.traceForm_apply, ← hn]
    simp

open scoped Classical in
/-- **The Euclidean dual of an ideal lattice is its trace dual**: the Euclidean dual
`mixedDual K σ(I)` of the lattice of a fractional ideal `I` is the image under
`traceToEuclidean K` of the lattice `σ(J)` of its trace dual
`J = I^∨ = FractionalIdeal.dual ℤ ℚ I`. -/
theorem mixedDual_idealLattice {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    mixedDual K (idealLattice K I) =
      (idealLattice K J).map ((traceToEuclidean K).toLinearMap.restrictScalars ℤ) := by
  rw [← comap_mixedDual_idealLattice hJ, ZLattice.comap]
  exact (Submodule.map_comap_eq_of_surjective
    (f := (traceToEuclidean K).toLinearMap.restrictScalars ℤ) (traceToEuclidean K).surjective
    _).symm

open scoped Classical in
/-- **The covolume of the trace dual**: `covol σ(J) = (4 ^ r₂)⁻¹ * covol σ(I)⁻¹` for the trace
dual `J = I^∨ = FractionalIdeal.dual ℤ ℚ I` of a fractional ideal `I`. -/
theorem covolume_idealLattice_dual {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ZLattice.covolume (idealLattice K J) =
      (4 ^ nrComplexPlaces K : ℝ)⁻¹ * (ZLattice.covolume (idealLattice K I))⁻¹ := by
  rw [← comap_mixedDual_idealLattice hJ,
    ZLattice.covolume_comap_continuousLinearEquiv _ (traceToEuclidean K) MeasureTheory.volume,
    abs_det_traceToEuclidean, covolume_mixedDual]

end TauCeti.NumberField.mixedEmbedding
