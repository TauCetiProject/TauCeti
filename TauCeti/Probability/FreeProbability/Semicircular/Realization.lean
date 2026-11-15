/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.LinearAlgebra.Matrix.PosSemidef
public import TauCeti.Probability.FreeProbability.Fock.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Law

/-!
# Fock-space realizations of semicircle laws and semicircular systems

This file connects the Fock-space vacuum Wick formula and cumulant theory in
`TauCeti.Probability.FreeProbability.Fock.Basic` with analytic C⋆-algebraic semicircle laws and with
positive-semidefinite covariance kernels over `ℝ`:

1. **Real field operators via complexification.** Embedding a real inner product space `H`
   isometrically into its `L²` complexification `WithLp 2 (Complexification H)` yields bounded
   self-adjoint operators `FullFockSpace.realField h` on the complex Hilbert space
   `FullFockSpace ℂ (WithLp 2 (Complexification H))`. Unlike complex field operators, `realField`
   is genuinely `ℝ`-linear (`FullFockSpace.realFieldCLM`), isometric up to the factor `2`
   (`‖realField h‖ = 2 * ‖h‖`), and realizes the real Gram matrix `(⟪v i, v j⟫_ℝ : ℂ)` as the
   covariance of a self-adjoint semicircular system, with free independence equivalent to real
   orthogonality.
2. **Semicircle laws on full Fock space.** Because `FullFockSpace ℂ H` is unconditionally complete,
   `FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H` is a unital C⋆-algebra for every inner product space
   `H`. Under `FullFockSpace.vacuumState`, each shifted field operator `field ℂ h + c • 1` (and
   `realField h + c • 1`) has C⋆-algebraic law `semicircleReal c (‖h‖₊ ^ 2)`. Specializing to
   `FullFockSpace ℂ ℂ` gives a concrete noncommutative Fock-space realization of
   `semicircleReal c v` for every centre `c : ℝ` and variance `v : ℝ≥0`.
3. **Characterization of real semicircular covariances.** Combining `realField` with the Kolmogorov
   decomposition (`Matrix.PosSemidef.KolmogorovSpace`) realizes every positive-semidefinite real
   matrix `C : Matrix ι ι ℝ` (on an arbitrary index type `ι`) as the covariance of a self-adjoint
   semicircular system on a complex Fock space. Conversely, positivity of a functional
   `φ : A →ₚ[ℂ] ℂ` on any `StarOrderedRing` forces the covariance of any self-adjoint semicircular
   system to be symmetric and positive semidefinite, yielding exact Hilbert-space and C⋆-algebraic
   equivalences.

## Main definitions

* `TauCeti.FullFockSpace.realField`, `TauCeti.FullFockSpace.realFieldCLM`: self-adjoint real field
  operators on `FullFockSpace ℂ (WithLp 2 (Complexification H))` and their bundled `ℝ`-linear
  continuous map.

## Main results

* `TauCeti.FullFockSpace.isSemicircularSystem_realField`,
  `TauCeti.FullFockSpace.isFreelyIndependentElements_realField_iff`, and
  `TauCeti.FullFockSpace.isFreelyIndependent_adjoin_realField`: semicircular systems and freeness of
  real field operators.
* `TauCeti.FullFockSpace.law_vacuumState_field`,
  `TauCeti.FullFockSpace.law_vacuumState_realField`, and
  `TauCeti.FullFockSpace.law_vacuumState_field_sqrt_add_algebraMap`: C⋆-algebraic semicircle laws on
  full Fock space.
* `Matrix.PosSemidef.isSemicircularSystem_realField_kolmogorovFeature`: Kolmogorov–Fock realization
  of any positive-semidefinite matrix `C : Matrix ι ι ℝ`.
* `TauCeti.IsSemicircularSystem.posSemidef_of_isSelfAdjoint`,
  `TauCeti.posSemidef_iff_exists_hilbert_isSemicircularSystem`, and
  `TauCeti.posSemidef_iff_exists_cstar_isSemicircularSystem`: equivalence between real
  positive-semidefinite matrices and covariances of self-adjoint semicircular systems.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lectures 7, 8, and 11.
-/

public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder InnerProductSpace NNReal

namespace TauCeti

universe u v

namespace FullFockSpace

section RealField

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*}

/-- The self-adjoint *real field operator* on the complex Fock space
`FullFockSpace ℂ (WithLp 2 (Complexification H))` attached to a vector `h` in a real inner product
space `H`, defined via the isometric real inclusion `WithLp.complexificationOfRealₗᵢ H`. -/
def realField (h : H) :
    FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
      FullFockSpace ℂ (WithLp 2 (Complexification H)) :=
  field ℂ (WithLp.complexificationOfRealₗᵢ H h)

theorem realField_def (h : H) :
    realField h = field ℂ (WithLp.complexificationOfRealₗᵢ H h) :=
  (rfl)

@[simp]
theorem adjoint_realField (h : H) : (realField h).adjoint = realField h :=
  adjoint_field _

@[simp]
theorem star_realField (h : H) : star (realField h) = realField h :=
  star_field _

theorem isSelfAdjoint_realField (h : H) : IsSelfAdjoint (realField h) :=
  isSelfAdjoint_field _

@[simp]
theorem realField_zero : realField (0 : H) = 0 := by
  simp [realField_def]

@[simp]
theorem realField_add (h k : H) : realField (h + k) = realField h + realField k := by
  rw [realField_def, map_add, field_add, ← realField_def, ← realField_def]

@[simp]
theorem realField_neg (h : H) : realField (-h) = -realField h := by
  rw [realField_def, map_neg, field_neg, ← realField_def]

@[simp]
theorem realField_sub (h k : H) : realField (h - k) = realField h - realField k := by
  rw [realField_def, map_sub, field_sub, ← realField_def, ← realField_def]

@[simp]
theorem realField_smul (r : ℝ) (h : H) : realField (r • h) = r • realField h := by
  rw [realField_def, map_smul, ← Complex.coe_smul,
    field_smul_of_isSelfAdjoint (by simp [IsSelfAdjoint]), ← realField_def]
  ext x n
  simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply]
  exact Complex.coe_smul r (realField h x n)

@[simp]
theorem norm_realField (h : H) : ‖realField h‖ = 2 * ‖h‖ := by
  simp [realField_def]

theorem realField_injective : Function.Injective (realField (H := H)) := fun _ _ h =>
  (WithLp.complexificationOfRealₗᵢ H).injective (field_injective h)

@[simp]
theorem realField_eq_zero_iff {h : H} : realField h = 0 ↔ h = 0 :=
  ⟨fun hh => realField_injective (hh.trans realField_zero.symm), fun hh => hh ▸ realField_zero⟩

variable (H) in
/-- `FullFockSpace.realField` bundled as a continuous `ℝ`-linear map of operator norm at most `2`
into bounded operators on `FullFockSpace ℂ (WithLp 2 (Complexification H))`. -/
def realFieldCLM :
    H →L[ℝ]
      (FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
        FullFockSpace ℂ (WithLp 2 (Complexification H))) :=
  LinearMap.mkContinuous
    { toFun := realField
      map_add' := realField_add
      map_smul' := realField_smul }
    2 fun h => (norm_realField h).le

@[simp]
theorem realFieldCLM_apply (h : H) : realFieldCLM H h = realField h :=
  (rfl)

theorem vacuumState_realField (h : H) :
    vacuumState ℂ (WithLp 2 (Complexification H)) (realField h) = 0 :=
  vacuumState_field _

theorem vacuumState_realField_mul_realField (h k : H) :
    vacuumState ℂ (WithLp 2 (Complexification H)) (realField h * realField k) =
      (⟪h, k⟫_ℝ : ℂ) := by
  rw [realField_def, realField_def, vacuumState_field_mul_field,
    WithLp.inner_complexificationOfRealₗᵢ]

/-- Real field operators `realField (v i)` form a self-adjoint semicircular system on
`FullFockSpace ℂ (WithLp 2 (Complexification H))` with real Gram covariance `(⟪v i, v j⟫_ℝ : ℂ)`. -/
theorem isSemicircularSystem_realField (v : ι → H) :
    IsSemicircularSystem
      (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
      (fun i => realField (v i))
      (Matrix.of fun i j => (⟪v i, v j⟫_ℝ : ℂ)) := by
  have hcov :
      (Matrix.of fun i j =>
          ⟪WithLp.complexificationOfRealₗᵢ H (v i),
            WithLp.complexificationOfRealₗᵢ H (v j)⟫_ℂ) =
        Matrix.of fun i j => (⟪v i, v j⟫_ℝ : ℂ) := by
    ext i j
    exact WithLp.inner_complexificationOfRealₗᵢ (v i) (v j)
  simp_rw [realField_def]
  rw [← hcov]
  exact isSemicircularSystem_field (fun i => WithLp.complexificationOfRealₗᵢ H (v i))

/-- Every real field operator `realField h` is semicircular of variance `(‖h‖ ^ 2 : ℂ)` for the
complexified vacuum state. -/
theorem isSemicircular_realField (h : H) :
    IsSemicircular (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
      (realField h) (‖h‖ ^ 2 : ℂ) := by
  simpa [realField_def] using isSemicircular_field (𝕜 := ℂ) (WithLp.complexificationOfRealₗᵢ H h)

/-- Real field operators `realField (v i)` are freely independent for the vacuum state if and only
if the vectors `v i` are pairwise orthogonal in `H`. -/
theorem isFreelyIndependentElements_realField_iff {v : ι → H} :
    IsFreelyIndependentElements
        (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
        (fun i => realField (v i)) ↔
      ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0 := by
  simp_rw [realField_def, isFreelyIndependentElements_field_iff,
    WithLp.inner_complexificationOfRealₗᵢ, Complex.ofReal_eq_zero]

/-- Because `realField` operators are self-adjoint, their `⋆`-free independence is likewise
equivalent to pairwise orthogonality in `H`. -/
theorem isStarFreelyIndependentElements_realField_iff {v : ι → H} :
    IsStarFreelyIndependentElements
        (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
        (fun i => realField (v i)) ↔
      ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0 := by
  simp_rw [realField_def, isStarFreelyIndependentElements_field_iff,
    WithLp.inner_complexificationOfRealₗᵢ, Complex.ofReal_eq_zero]

/-- Unital complex subalgebras generated by `realField '' S i` for pairwise orthogonal subsets
`S i` of a real inner product space `H` are freely independent for the vacuum state. -/
theorem isFreelyIndependent_adjoin_realField {S : ι → Set H}
    (horth : ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_ℝ = 0) :
    IsFreelyIndependent
      (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
      fun i => Algebra.adjoin ℂ (realField '' S i) := by
  have himg (i : ι) :
      realField '' S i = field ℂ '' (WithLp.complexificationOfRealₗᵢ H '' S i) := by
    rw [← Set.image_comp]
    rfl
  simp_rw [himg]
  refine isFreelyIndependent_adjoin_field ?_
  rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [WithLp.inner_complexificationOfRealₗᵢ, horth hij x hx y hy, Complex.ofReal_zero]

end RealField

section SemicircleLaw

/-- Under the vacuum state on complex full Fock space, the self-adjoint field operator `field ℂ h`
has the centred semicircle law `semicircleReal 0 (‖h‖₊ ^ 2)`. -/
theorem law_vacuumState_field {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (h : H) :
    (vacuumState ℂ H).law (field ℂ h) = Probability.semicircleReal 0 (‖h‖₊ ^ 2) := by
  rw [PositiveLinearMap.law_eq_semicircleReal_iff _ (isSelfAdjoint_field h)]
  simpa using isSemicircular_field (𝕜 := ℂ) h

/-- Shifting `field ℂ h` by `c • 1` yields the semicircle law `semicircleReal c (‖h‖₊ ^ 2)` on
complex full Fock space. -/
theorem law_vacuumState_field_add_algebraMap {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (h : H) (c : ℝ) :
    (vacuumState ℂ H).law
        (field ℂ h + algebraMap ℝ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) c) =
      Probability.semicircleReal c (‖h‖₊ ^ 2) := by
  have hsc : IsSemicircular (vacuumState ℂ H).toLinearMap (field ℂ h)
      ((((‖h‖₊ ^ 2 : ℝ≥0) : ℝ) : ℂ)) := by
    simpa using isSemicircular_field (𝕜 := ℂ) h
  exact PositiveLinearMap.law_add_algebraMap_of_isSemicircular
    (vacuumState ℂ H) (isSelfAdjoint_field h) hsc c

/-- Under the vacuum state on complexified full Fock space, `realField h` has the centred semicircle
law `semicircleReal 0 (‖h‖₊ ^ 2)`. -/
theorem law_vacuumState_realField {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : H) :
    (vacuumState ℂ (WithLp 2 (Complexification H))).law (realField h) =
      Probability.semicircleReal 0 (‖h‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_field, LinearIsometry.nnNorm_map]

/-- Shifting `realField h` by `c • 1` yields the semicircle law `semicircleReal c (‖h‖₊ ^ 2)` on
complexified full Fock space. -/
theorem law_vacuumState_realField_add_algebraMap {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : H) (c : ℝ) :
    (vacuumState ℂ (WithLp 2 (Complexification H))).law
        (realField h +
          algebraMap ℝ
            (FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
              FullFockSpace ℂ (WithLp 2 (Complexification H))) c) =
      Probability.semicircleReal c (‖h‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_field_add_algebraMap, LinearIsometry.nnNorm_map]

/-- Explicit noncommutative Fock-space realization of the semicircle law `semicircleReal c v` for
every centre `c : ℝ` and variance `v : ℝ≥0` on the one-particle Fock space `FullFockSpace ℂ ℂ`. -/
theorem law_vacuumState_field_sqrt_add_algebraMap (c : ℝ) (v : ℝ≥0) :
    (vacuumState ℂ ℂ).law
        (field ℂ ((NNReal.sqrt v : ℝ) : ℂ) +
          algebraMap ℝ (FullFockSpace ℂ ℂ →L[ℂ] FullFockSpace ℂ ℂ) c) =
      Probability.semicircleReal c v := by
  have hv : ‖(((NNReal.sqrt v : ℝ) : ℂ))‖₊ ^ 2 = v := by
    ext
    simp
  rw [law_vacuumState_field_add_algebraMap, hv]

end SemicircleLaw

end FullFockSpace

end TauCeti

namespace Matrix.PosSemidef

open TauCeti TauCeti.FullFockSpace

/-- **Kolmogorov–Fock realization of a positive-semidefinite covariance matrix**: for any real
positive-semidefinite matrix `C : Matrix ι ι ℝ` (on an arbitrary index type `ι`), applying
`FullFockSpace.realField` to its canonical Kolmogorov feature vectors realizes
`C.map Complex.ofReal` as the covariance of a self-adjoint semicircular system on complex Fock
space. -/
theorem isSemicircularSystem_realField_kolmogorovFeature {ι : Type u} {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    IsSemicircularSystem
      (vacuumState ℂ (WithLp 2 (Complexification hC.KolmogorovSpace))).toLinearMap
      (fun i => realField (hC.kolmogorovFeature i))
      (C.map Complex.ofReal) := by
  have hcov :
      (Matrix.of fun i j => (⟪hC.kolmogorovFeature i, hC.kolmogorovFeature j⟫_ℝ : ℂ)) =
        C.map Complex.ofReal := by
    ext i j
    simp [hC.inner_kolmogorovFeature]
  rw [← hcov]
  exact isSemicircularSystem_realField hC.kolmogorovFeature

end Matrix.PosSemidef

namespace TauCeti

/-- If `s : ι → A` is a self-adjoint semicircular system with real covariance `C` for a positive
linear functional `φ : A →ₚ[ℂ] ℂ` on a `StarOrderedRing`, then `C` is symmetric and positive
semidefinite. -/
theorem IsSemicircularSystem.posSemidef_of_isSelfAdjoint {A ι : Type*} [Ring A] [PartialOrder A]
    [StarRing A] [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] {φ : A →ₚ[ℂ] ℂ}
    {s : ι → A} {C : Matrix ι ι ℝ}
    (h : IsSemicircularSystem φ.toLinearMap s (C.map Complex.ofReal))
    (hs : ∀ i, IsSelfAdjoint (s i)) :
    C.PosSemidef := by
  refine posSemidef_iff_finite_sum.{0, _, 0}.2 ⟨fun i j => ?_, fun {κ} _ v x => ?_⟩
  · let b : A := s i + Complex.I • s j
    have hb_star : star b = s i - Complex.I • s j := by
      simp [b, star_add, star_smul, (hs i).star_eq, (hs j).star_eq, sub_eq_add_neg]
    have hmul : star b * b =
        s i * s i + s j * s j + Complex.I • (s i * s j - s j * s i) := by
      have hII : (Complex.I • s j) * (Complex.I • s j) = -(s j * s j) := by
        rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
      rw [hb_star, sub_mul, mul_add, mul_add, mul_smul_comm, smul_mul_assoc, hII, smul_sub]
      abel
    have him : (φ (star b * b)).im = 0 :=
      (φ.map_nonneg (star_mul_self_nonneg b)).2.symm
    have hmul_im : (φ (star b * b)).im = C i j - C j i := by
      have h_ii : φ (s i * s i) = C i i := by simpa using h.apply_mul i i
      have h_jj : φ (s j * s j) = C j j := by simpa using h.apply_mul j j
      have h_ij : φ (s i * s j) = C i j := by simpa using h.apply_mul i j
      have h_ji : φ (s j * s i) = C j i := by simpa using h.apply_mul j i
      rw [hmul, map_add, map_add, LinearMapClass.map_smul, map_sub, h_ii, h_jj, h_ij, h_ji]
      simp
    simp only [star_trivial]
    linarith [him, hmul_im]
  · let b : A := ∑ p : κ, (x p : ℂ) • s (v p)
    have hb_star : star b = b := by
      simp [b, star_sum, star_smul, (hs _).star_eq]
    have hbb : star b * b =
        ∑ p : κ, ∑ q : κ, ((x p : ℂ) * (x q : ℂ)) • (s (v p) * s (v q)) := by
      rw [hb_star]
      simp only [b, sum_mul_sum, smul_mul_smul_comm]
    have hφ : φ (star b * b) =
        ((∑ p : κ, ∑ q : κ, star (x p) * C (v p) (v q) * x q : ℝ) : ℂ) := by
      have hmul (p q : κ) : φ (s (v p) * s (v q)) = C (v p) (v q) := by
        simpa using h.apply_mul (v p) (v q)
      rw [hbb, map_sum]
      simp only [map_sum, LinearMapClass.map_smul, hmul, smul_eq_mul, star_trivial,
        Complex.ofReal_sum, Complex.ofReal_mul]
      refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
      ring
    have hnonneg : 0 ≤ φ (star b * b) := φ.map_nonneg (star_mul_self_nonneg b)
    rw [hφ] at hnonneg
    exact Complex.zero_le_real.1 hnonneg

/-- A real matrix `C : Matrix ι ι ℝ` is positive semidefinite if and only if it is the covariance of
a self-adjoint semicircular system of bounded operators on some complex Hilbert space under a unit
vector state. -/
theorem posSemidef_iff_exists_hilbert_isSemicircularSystem {ι : Type u} (C : Matrix ι ι ℝ) :
    C.PosSemidef ↔
      ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
        (ξ : K) (s : ι → K →L[ℂ] K),
        ‖ξ‖ = 1 ∧ (∀ i, IsSelfAdjoint (s i)) ∧
          IsSemicircularSystem
            (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap s
            (C.map Complex.ofReal) := by
  refine ⟨fun hC => ?_, ?_⟩
  · refine ⟨FullFockSpace ℂ (WithLp 2 (Complexification hC.KolmogorovSpace)),
      inferInstance, inferInstance, inferInstance, FullFockSpace.vacuum,
      fun i => FullFockSpace.realField (hC.kolmogorovFeature i), FullFockSpace.norm_vacuum,
      fun i => FullFockSpace.isSelfAdjoint_realField _, ?_⟩
    rw [← FullFockSpace.vacuumState_def]
    exact hC.isSemicircularSystem_realField_kolmogorovFeature
  · rintro ⟨K, _, _, _, ξ, s, -, hs, hsys⟩
    exact hsys.posSemidef_of_isSelfAdjoint hs

/-- A real matrix `C : Matrix ι ι ℝ` is positive semidefinite if and only if it is the covariance of
a self-adjoint semicircular system in some unital C⋆-algebra under a positive linear functional. -/
theorem posSemidef_iff_exists_cstar_isSemicircularSystem {ι : Type u} (C : Matrix ι ι ℝ) :
    C.PosSemidef ↔
      ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
        (φ : A →ₚ[ℂ] ℂ) (s : ι → A),
        (∀ i, IsSelfAdjoint (s i)) ∧
          IsSemicircularSystem φ.toLinearMap s (C.map Complex.ofReal) := by
  refine ⟨fun hC => ?_, ?_⟩
  · exact ⟨FullFockSpace ℂ (WithLp 2 (Complexification hC.KolmogorovSpace)) →L[ℂ]
        FullFockSpace ℂ (WithLp 2 (Complexification hC.KolmogorovSpace)),
      inferInstance, inferInstance, inferInstance,
      FullFockSpace.vacuumState ℂ (WithLp 2 (Complexification hC.KolmogorovSpace)),
      fun i => FullFockSpace.realField (hC.kolmogorovFeature i),
      fun i => FullFockSpace.isSelfAdjoint_realField _,
      hC.isSemicircularSystem_realField_kolmogorovFeature⟩
  · rintro ⟨A, _, _, _, φ, s, hs, hsys⟩
    exact hsys.posSemidef_of_isSelfAdjoint hs

end TauCeti
