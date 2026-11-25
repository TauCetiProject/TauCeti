/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.RealField
public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.Probability.FreeProbability.Fock.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Law

/-!
# Fock-space realizations of semicircle laws and semicircular systems

This file connects the Fock-space vacuum Wick formula and cumulant theory in
`TauCeti.Probability.FreeProbability.Fock.Basic` and real field operators in
`TauCeti.Analysis.InnerProductSpace.FullFockSpace.RealField` with analytic C⋆-algebraic semicircle
laws and with positive-semidefinite covariance kernels over `ℝ`:

1. **Semicircular systems and freeness of real field operators.** Both `FullFockSpace.field ℂ` and
   `FullFockSpace.realField` are `ℝ`-linear (while `field ℂ` is not `ℂ`-linear because annihilation
   is conjugate-linear). Starting from a real inner product space `H`,
   `WithLp.complexificationOfRealₗᵢ H` embeds `H` isometrically into
   `WithLp 2 (Complexification H)`, and `FullFockSpace.realField` applies `FullFockSpace.field ℂ`
   to that inclusion (sending `h : H` to the bounded self-adjoint operator
   `field ℂ (WithLp.complexificationOfRealₗᵢ H h)` of norm `2 * ‖h‖` on
   `FullFockSpace ℂ (WithLp 2 (Complexification H))`). For a family `v : ι → H`, this realizes the
   real Gram matrix `(⟪v i, v j⟫_ℝ : ℂ)` as the covariance of a self-adjoint semicircular system,
   with free independence equivalent to real orthogonality.
2. **Semicircle laws on full Fock space.** Because `FullFockSpace ℂ H` is unconditionally complete,
   `FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H` is a unital C⋆-algebra for every inner product space
   `H`. Under `FullFockSpace.vacuumState`, each shifted field operator `field ℂ h + c • 1` (and
   `realField h + c • 1`) has C⋆-algebraic law `semicircleReal c (‖h‖₊ ^ 2)`. Specializing to
   `FullFockSpace ℂ ℂ` gives a concrete noncommutative Fock-space realization of
   `semicircleReal c v` for every centre `c : ℝ` and variance `v : ℝ≥0`.
3. **Characterization of real semicircular covariances.** Combining `realField` with the Kolmogorov
   decomposition (`Matrix.PosSemidef.KolmogorovSpace`) realizes every positive-semidefinite real
   matrix `C : Matrix ι ι ℝ` (on an arbitrary index type `ι`) as the covariance of a self-adjoint
   semicircular system on a complex Fock space. Combining this realization with the converse
   positivity theorem `TauCeti.IsSemicircularSystem.posSemidef_of_isSelfAdjoint` from
   `TauCeti.Probability.FreeProbability.Semicircular.System` yields exact Hilbert-space and
   C⋆-algebraic equivalences.

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
* `TauCeti.posSemidef_iff_exists_hilbert_isSemicircularSystem` and
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

open scoped ComplexOrder InnerProductSpace NNReal

namespace TauCeti

universe u v

namespace FullFockSpace

section RealField

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*}

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
    congr 1
    funext x
    exact realField_def x
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
