/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.RealField
public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.Probability.FreeProbability.Fock.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Law
import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Fock-space realizations of semicircle laws and semicircular systems

This file connects the Fock-space vacuum Wick formula and cumulant theory in
`TauCeti.Probability.FreeProbability.Fock.Basic` and real field operators in
`TauCeti.Analysis.InnerProductSpace.FullFockSpace.RealField` with analytic C⋆-algebraic semicircle
laws and with positive-semidefinite covariance kernels over `ℝ`, `ℂ`, and `[RCLike 𝕜]`:

1. **Semicircular systems and freeness of real field operators.** Both `FullFockSpace.field ℂ` and
   `FullFockSpace.realField` are `ℝ`-linear (while `field ℂ` is not `ℂ`-linear because annihilation
   is conjugate-linear). Starting from a real inner product space `H`,
   `WithLp.complexificationOfRealₗᵢ H` embeds `H` isometrically into
   `WithLp 2 (Complexification H)`, and `FullFockSpace.realField` applies `FullFockSpace.field ℂ`
   to that inclusion (sending `h : H` to the bounded self-adjoint operator
   `field ℂ (WithLp.complexificationOfRealₗᵢ H h)` of norm `2 * ‖h‖` on
   `FullFockSpace ℂ (WithLp 2 (Complexification H))`). For a family `v : ι → H`, this realizes the
   real Gram matrix `(⟪v i, v j⟫_ℝ : ℂ)` as the covariance of a self-adjoint semicircular system,
   with free independence of real-field and complexified creation subalgebras equivalent to real
   orthogonality.
2. **Semicircle laws on full Fock space.** Because `FullFockSpace ℂ H` is unconditionally complete,
   `FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H` is a unital C⋆-algebra for every inner product space
   `H`. Under `FullFockSpace.vacuumState`, each affine field operator `r • field ℂ h + c • 1` (and
   `r • realField h + c • 1`) has C⋆-algebraic law
   `semicircleReal c (Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2)`. Specializing to `FullFockSpace ℂ ℂ` gives
   a concrete noncommutative Fock-space realization of `semicircleReal c v` for every centre
   `c : ℝ` and variance `v : ℝ≥0`.
3. **Characterization of complex and real semicircular covariances.** Combining Fock field operators
   with the Kolmogorov–RKHS Gram realization (`Matrix.PosSemidef.exists_gram_eq`) and finite
   `EuclideanSpace` Gram realization (`Matrix.PosSemidef.exists_gram_euclideanSpace_eq`) realizes
   every positive-semidefinite matrix `C : Matrix ι ι 𝕜` (`[RCLike 𝕜]`) on full Fock space, and on
   `FullFockSpace 𝕜 (EuclideanSpace 𝕜 ι)` when `ι` is finite. Together with GNS `⋆`-moment
   positivity, this characterizes both complex Hermitian and real symmetric positive-semidefinite
   matrices of arbitrary index type as the covariances of self-adjoint semicircular systems on
   complex Hilbert spaces and unital C⋆-algebras.

## Main results

* `TauCeti.FullFockSpace.isSemicircularSystem_realField`,
  `TauCeti.FullFockSpace.isFreelyIndependentElements_realField_iff`,
  `TauCeti.FullFockSpace.isFreelyIndependent_adjoin_realField_iff`,
  `TauCeti.FullFockSpace.isFreelyIndependent_starAlgebra_adjoin_creation_complexifyL2_iff`, and
  `TauCeti.FullFockSpace.isFreelyIndependent_adjoin_realField_coe_iff`: semicircular systems and
  orthogonality equivalences on complexified full Fock space.
* `TauCeti.FullFockSpace.law_vacuumState_field`,
  `TauCeti.FullFockSpace.law_vacuumState_smul_field_add_algebraMap`,
  `TauCeti.FullFockSpace.law_vacuumState_realField`,
  `TauCeti.FullFockSpace.law_vacuumState_smul_realField_add_algebraMap`, and
  `TauCeti.FullFockSpace.law_vacuumState_field_sqrt_add_algebraMap`: C⋆-algebraic semicircle laws on
  full Fock space.
* `Matrix.PosSemidef.exists_isSemicircularSystem_field`,
  `Matrix.PosSemidef.exists_euclideanSpace_isSemicircularSystem_field`,
  `Matrix.PosSemidef.isSemicircularSystem_realField_kolmogorovFeature`, and
  `Matrix.PosSemidef.exists_euclideanSpace_isSemicircularSystem_realField`: Kolmogorov and
  `EuclideanSpace` Fock realizations of positive-semidefinite covariance matrices.
* `Matrix.posSemidef_iff_exists_hilbert_isSelfAdjoint_and_isSemicircularSystem`,
  `Matrix.posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem`,
  `TauCeti.posSemidef_iff_exists_hilbert_isSemicircularSystem`, and
  `TauCeti.posSemidef_iff_exists_cstar_isSemicircularSystem`: Hilbert-space and C⋆-algebraic
  characterizations of complex and real positive-semidefinite covariance matrices.

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

/-- Unital complex subalgebras generated by `realField '' S i` for subsets `S i` of a real inner
product space `H` are freely independent for the vacuum state if and only if the sets `S i` are
pairwise orthogonal. -/
theorem isFreelyIndependent_adjoin_realField_iff {S : ι → Set H} :
    IsFreelyIndependent
        (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
        (fun i => Algebra.adjoin ℂ (realField '' S i)) ↔
      ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_ℝ = 0 := by
  have himg (i : ι) :
      realField '' S i = field ℂ '' (WithLp.complexificationOfRealₗᵢ H '' S i) := by
    rw [← Set.image_comp, Function.comp_def]
    simp_rw [← realField_def]
  simp_rw [himg, isFreelyIndependent_adjoin_field_iff, Set.forall_mem_image,
    WithLp.inner_complexificationOfRealₗᵢ, Complex.ofReal_eq_zero]

/-- For real subspaces `S : ι → Submodule ℝ H`, the unital `⋆`-subalgebras generated by creation
operators on their complexifications `(S i).complexifyL2` are freely independent under the vacuum
state if and only if the subspaces `S i` are pairwise orthogonal (`S i ≤ (S j)ᗮ`). -/
theorem isFreelyIndependent_starAlgebra_adjoin_creation_complexifyL2_iff
    (S : ι → Submodule ℝ H) :
    IsFreelyIndependent (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
        (fun i => (StarAlgebra.adjoin ℂ
          (creation ℂ ''
            ((S i).complexifyL2 : Set (WithLp 2 (Complexification H))))).toSubalgebra) ↔
      Pairwise fun i j => S i ≤ (S j)ᗮ := by
  have horth (i j : ι) :
      (∀ z ∈ ((S i).complexifyL2 : Set (WithLp 2 (Complexification H))),
          ∀ w ∈ ((S j).complexifyL2 : Set (WithLp 2 (Complexification H))), ⟪z, w⟫_ℂ = 0) ↔
        S i ≤ (S j)ᗮ :=
    ((S i).complexifyL2.isOrtho_iff_inner_eq (V := (S j).complexifyL2)).symm.trans
      (Submodule.isOrtho_complexifyL2_iff.trans Submodule.isOrtho_iff_le)
  rw [isFreelyIndependent_starAlgebra_adjoin_creation_iff]
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ => horth i j

/-- For real subspaces `S : ι → Submodule ℝ H`, the unital subalgebras generated by `realField` on
`S i` are freely independent under the vacuum state if and only if the subspaces `S i` are pairwise
orthogonal (`S i ≤ (S j)ᗮ`). -/
theorem isFreelyIndependent_adjoin_realField_coe_iff (S : ι → Submodule ℝ H) :
    IsFreelyIndependent (vacuumState ℂ (WithLp 2 (Complexification H))).toLinearMap
        (fun i => Algebra.adjoin ℂ (realField '' (S i : Set H))) ↔
      Pairwise fun i j => S i ≤ (S j)ᗮ := by
  have horth (i j : ι) :
      (∀ x ∈ (S i : Set H), ∀ y ∈ (S j : Set H), ⟪x, y⟫_ℝ = 0) ↔ S i ≤ (S j)ᗮ :=
    ((S i).isOrtho_iff_inner_eq (V := S j)).symm.trans Submodule.isOrtho_iff_le
  rw [isFreelyIndependent_adjoin_realField_iff]
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ => horth i j

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

/-- Affine rescaling and shifting of a Fock field operator realizes `semicircleReal` with arbitrary
centre `c` and rescaled variance `Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2`. -/
theorem law_vacuumState_smul_field_add_algebraMap {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (h : H) (r c : ℝ) :
    (vacuumState ℂ H).law
        (r • field ℂ h + algebraMap ℝ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) c) =
      Probability.semicircleReal c (Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2) := by
  -- `ContinuousLinearMap.instSMul` and `Module.complexToReal` agree pointwise via `(r : ℂ) • ·`.
  convert PositiveLinearMap.law_smul_add_algebraMap_of_law_eq_semicircleReal
    (vacuumState ℂ H) (law_vacuumState_field h) r c using 3
  · rw [← Complex.coe_smul]
    ext x n
    simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply]
    exact (Complex.coe_smul r _).symm
  · rfl
  · simp

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

/-- Affine rescaling and shifting of `realField h` realizes `semicircleReal` with centre `c` and
variance `Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2`. -/
theorem law_vacuumState_smul_realField_add_algebraMap {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : H) (r c : ℝ) :
    (vacuumState ℂ (WithLp 2 (Complexification H))).law
        (r • realField h +
          algebraMap ℝ
            (FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
              FullFockSpace ℂ (WithLp 2 (Complexification H))) c) =
      Probability.semicircleReal c (Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_smul_field_add_algebraMap, LinearIsometry.nnNorm_map]

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

namespace Matrix

open TauCeti TauCeti.FullFockSpace

/-- Every positive-semidefinite matrix `C : Matrix ι ι 𝕜` of arbitrary index type `ι` over `𝕜`
(`ℝ` or `ℂ`) is the covariance of a Fock semicircular system of self-adjoint field operators over a
complete Hilbert space over `𝕜`. -/
theorem PosSemidef.exists_isSemicircularSystem_field {𝕜 : Type u} {ι : Type v}
    [RCLike 𝕜] {C : Matrix ι ι 𝕜} (hC : C.PosSemidef) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
      (_ : CompleteSpace H) (h : ι → H),
      IsSemicircularSystem (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (h i)) C := by
  obtain ⟨H, _, _, _, h, rfl⟩ := hC.exists_gram_eq
  exact ⟨H, inferInstance, inferInstance, inferInstance, h, isSemicircularSystem_field h⟩

/-- Every finite-index positive-semidefinite matrix `C : Matrix ι ι 𝕜` (`[RCLike 𝕜]`) is realized by
self-adjoint field operators on `FullFockSpace 𝕜 (EuclideanSpace 𝕜 ι)`. -/
theorem PosSemidef.exists_euclideanSpace_isSemicircularSystem_field {𝕜 : Type u} {ι : Type v}
    [RCLike 𝕜] [Fintype ι] {C : Matrix ι ι 𝕜} (hC : C.PosSemidef) :
    ∃ h : ι → EuclideanSpace 𝕜 ι,
      IsSemicircularSystem (vacuumState 𝕜 (EuclideanSpace 𝕜 ι)).toLinearMap
        (fun i => field 𝕜 (h i)) C := by
  obtain ⟨h, rfl⟩ := hC.exists_gram_euclideanSpace_eq
  exact ⟨h, isSemicircularSystem_field h⟩

/-- **Kolmogorov–Fock realization of a positive-semidefinite covariance matrix**: for any real
positive-semidefinite matrix `C : Matrix ι ι ℝ` (on an arbitrary index type `ι`), applying
`FullFockSpace.realField` to its canonical Kolmogorov feature vectors realizes
`C.map Complex.ofReal` as the covariance of a self-adjoint semicircular system on complex Fock
space. -/
theorem PosSemidef.isSemicircularSystem_realField_kolmogorovFeature {ι : Type u} {C : Matrix ι ι ℝ}
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

/-- Every finite-index real positive-semidefinite matrix `C : Matrix ι ι ℝ` is realized by
self-adjoint `realField` operators on the full Fock space over the complexification of
`EuclideanSpace ℝ ι`. -/
theorem PosSemidef.exists_euclideanSpace_isSemicircularSystem_realField {ι : Type u}
    [Fintype ι] {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ∃ x : ι → EuclideanSpace ℝ ι,
      IsSemicircularSystem
        (vacuumState ℂ (WithLp 2 (Complexification (EuclideanSpace ℝ ι)))).toLinearMap
        (fun i => realField (x i)) (C.map Complex.ofReal) := by
  obtain ⟨x, rfl⟩ := hC.exists_gram_euclideanSpace_eq
  have hgram : (Matrix.of fun i j => (⟪x i, x j⟫_ℝ : ℂ)) = (Matrix.gram ℝ x).map Complex.ofReal :=
    rfl
  exact ⟨x, hgram ▸ isSemicircularSystem_realField x⟩

/-- **Hilbert-space characterization of complex semicircular covariance matrices.** A complex matrix
`C : Matrix ι ι ℂ` of arbitrary index type `ι` is positive semidefinite if and only if `C` is the
covariance of a self-adjoint semicircular system of bounded operators on a complex Hilbert space
under a unit vector state. -/
theorem posSemidef_iff_exists_hilbert_isSelfAdjoint_and_isSemicircularSystem {ι : Type u}
    {C : Matrix ι ι ℂ} :
    C.PosSemidef ↔
      ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
        (ξ : K) (s : ι → K →L[ℂ] K),
        ‖ξ‖ = 1 ∧ (∀ i, IsSelfAdjoint (s i)) ∧
          IsSemicircularSystem
            (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap s C := by
  refine ⟨fun hC => ?_, fun ⟨K, _, _, _, ξ, s, _, hs, hsys⟩ =>
    hsys.posSemidef_complex_of_isSelfAdjoint hs⟩
  obtain ⟨H, _, _, _, h, hsys⟩ := hC.exists_isSemicircularSystem_field
  refine ⟨FullFockSpace ℂ H, inferInstance, inferInstance, inferInstance,
    vacuum, fun i => field ℂ (h i), norm_vacuum, fun i => isSelfAdjoint_field (h i), ?_⟩
  rwa [← vacuumState_def]

/-- **C⋆-algebraic characterization of complex semicircular covariance matrices.** A complex matrix
`C : Matrix ι ι ℂ` of arbitrary index type `ι` is positive semidefinite if and only if `C` is the
covariance of a self-adjoint semicircular system in a complex C⋆-probability space. -/
theorem posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem {ι : Type u}
    {C : Matrix ι ι ℂ} :
    C.PosSemidef ↔
      ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
        (φ : A →ₚ[ℂ] ℂ) (s : ι → A),
        (∀ i, IsSelfAdjoint (s i)) ∧ IsSemicircularSystem φ.toLinearMap s C := by
  refine ⟨fun hC => ?_, fun ⟨A, _, _, _, φ, s, hs, hsys⟩ =>
    hsys.posSemidef_complex_of_isSelfAdjoint hs⟩
  obtain ⟨H, _, _, _, h, hsys⟩ := hC.exists_isSemicircularSystem_field
  exact ⟨FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H,
    inferInstance, inferInstance, inferInstance, vacuumState ℂ H,
    fun i => field ℂ (h i), fun i => isSelfAdjoint_field (h i), hsys⟩

end Matrix

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
  rw [← Matrix.posSemidef_map_complex_ofReal_iff,
    Matrix.posSemidef_iff_exists_hilbert_isSelfAdjoint_and_isSemicircularSystem]

/-- A real matrix `C : Matrix ι ι ℝ` is positive semidefinite if and only if it is the covariance of
a self-adjoint semicircular system in some unital C⋆-algebra under a positive linear functional. -/
theorem posSemidef_iff_exists_cstar_isSemicircularSystem {ι : Type u} (C : Matrix ι ι ℝ) :
    C.PosSemidef ↔
      ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
        (φ : A →ₚ[ℂ] ℂ) (s : ι → A),
        (∀ i, IsSelfAdjoint (s i)) ∧
          IsSemicircularSystem φ.toLinearMap s (C.map Complex.ofReal) := by
  rw [← Matrix.posSemidef_map_complex_ofReal_iff,
    Matrix.posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem]

end TauCeti
