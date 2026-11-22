/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.NumberTheory.Height.Arakelov.Absolute
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Trace.Basic

/-!
# Siegel's lemma relative to a field extension

Let `F / K` be an extension of number fields of degree `r`, with `D = [K : ℚ]`, and let
`A : Matrix m ι F`. The `K`-rational solutions of `A x = 0`, that is the vectors `x : ι → K`
with `A *ᵥ (algebraMap K F ∘ x) = 0`, form the kernel `W` of the `K`-linear map
`A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F`. Writing each equation in coordinates
over a `K`-basis of `F` turns it into `r` equations over `K`, so `W` has codimension at most
`r · #m`. The coordinate equations depend on the basis and their heights are not controlled by
those of the rows of `A`. The height of `W` itself is controlled: its relative Arakelov height is
at most the product of the relative Arakelov heights of the rows of `A`
(`Matrix.relativeSubspaceArakelovHeight_ker_restrictScalars_comp_le_prod`), that is

`H₂(W) ≤ ∏ i, H₂(A i) ^ r`

in absolute heights, where the zero row counts as `1`. Feeding this into the Bombieri–Vaaler
kernel basis theorem over `K` gives Siegel's lemma for `K`-rational solutions of equations over
`F` (Bombieri–Gubler, Theorem 2.9.19): `W` has a `K`-basis `x 0, …, x (k - 1)` in `𝓞_K^ι` with

`∏ j, H(x j) ≤ (2 / π) ^ (k r₂ / D) |discr K| ^ (k / (2 D)) ∏ i, H₂(A i) ^ r`,

where `k = dim W` and `r₂` is the number of complex places of `K`
(`Matrix.exists_linearIndependent_mulVec_algebraMap_eq_zero_prod_absHeight_le`). When
`r · #m < #ι` there is a nonzero solution in `𝓞_K^ι` with

`H(x) ≤ (2 / π) ^ (r₂ / D) |discr K| ^ (1 / (2 D)) (∏ i, H₂(A i) ^ r) ^ (1 / (#ι - r · #m))`

(`Matrix.exists_ne_zero_mulVec_algebraMap_eq_zero_absHeight_le`).
This is the form of Siegel's lemma that produces auxiliary polynomials with coefficients in `K`
vanishing to a prescribed order at points of `F`.

The height bound is proved over the normal closure `L` of `F / K`. Let `b` be a `K`-basis of `F`
and `b'` its dual basis for the trace form. The coordinates of `y ∈ F` in `b'` are the traces
`Tr_{F/K}(y * b l)`, so `W` is the kernel of the matrix over `K` with rows
`j ↦ Tr_{F/K}(A i j * b l)`. Over `L`, the span of these rows is the span of the conjugate rows
`σ ∘ A i` for the `r` embeddings `σ : F →ₐ[K] L`: in one direction
`Tr_{F/K}(y) = ∑ σ, σ y`, in the other `σ y = ∑ l, Tr_{F/K}(y * b l) σ(b' l)`. Absolute heights of
subspaces do not change under extension of the base field
(`Submodule.subspaceHeight_span_image_algebraMap`), duality identifies the heights of a kernel and
of the row space (`Matrix.subspaceHeight_ker_mulVecLin`), the height of a span is at most the
product of the heights of the spanning vectors (`Submodule.subspaceHeight_span_range_le_prod`), and
conjugation preserves absolute heights (`RingHom.absoluteHeight2_comp`).

## Main results

* `Matrix.relativeSubspaceArakelovHeight_ker_restrictScalars_comp_le_prod` and
  `Matrix.subspaceHeight_ker_restrictScalars_comp_le`: the height of the space of `K`-rational
  solutions, in relative and absolute form.
* `Matrix.exists_linearIndependent_mulVec_algebraMap_eq_zero_prod_absHeight_le`: a basis of the
  `K`-rational solutions in `𝓞_K^ι` with bounded product of heights.
* `Matrix.exists_ne_zero_mulVec_algebraMap_eq_zero_absHeight_le`: a small nonzero `K`-rational
  solution when `[F : K] · #m < #ι`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.9, Theorem 2.9.19 and its proof.
-/

public section

noncomputable section

open Module NumberField NumberField.InfinitePlace Submodule TauCeti
open scoped Matrix

namespace Matrix

/-- `Pi.algebraMap` applies `algebraMap` coordinatewise. -/
private theorem pi_algebraMap_apply {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (v : ι → R) : Pi.algebraMap ι R A v = algebraMap R A ∘ v :=
  rfl

/-- The `K`-rational solutions of `A x = 0` are the kernel of
`A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F`. -/
private theorem mem_ker_restrictScalars_comp_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    {m ι : Type*} [Fintype ι] (A : Matrix m ι F) (x : ι → K) :
    x ∈ LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F) ↔
      A *ᵥ (fun i ↦ algebraMap K F (x i)) = 0 := by
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply, mulVecLin_apply,
    pi_algebraMap_apply, Function.comp_def]

section TraceRows

variable {F : Type*} [Field F] {m ι κ : Type*}

/-- The rows `j ↦ Tr_{F/K}(A i j * b l)`, indexed by `(i, l)`: the equations over `K` cut out by
the equations `A x = 0` over `F` on `K`-rational vectors. -/
private def traceRows (K : Type*) [Field K] [Algebra K F] (b : κ → F) (A : Matrix m ι F) :
    Matrix (m × κ) ι K :=
  of fun p j ↦ Algebra.trace K F (A p.1 j * b p.2)

variable {K : Type*} [Field K] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [Finite κ]

/-- Applied to a `K`-rational vector `x`, the trace rows read off the coordinates of `A x` in the
basis dual to `b` for the trace form. -/
private theorem traceRows_mulVec [Fintype ι] [DecidableEq κ] (b : Basis κ K F) (A : Matrix m ι F)
    (x : ι → K) :
    traceRows K b A *ᵥ x = fun p ↦
      ((Algebra.traceForm K F).dualBasis (traceForm_nondegenerate K F) b).repr
        ((A *ᵥ (algebraMap K F ∘ x)) p.1) p.2 := by
  ext ⟨i, l⟩
  simp only [mulVec, dotProduct, traceRows, of_apply, Function.comp_apply, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, LinearMap.BilinForm.dualBasis_repr_apply,
    Algebra.traceForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show A i j * algebraMap K F (x j) * b l = x j • (A i j * b l) by
    rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul, mul_comm]

/-- The trace rows cut out exactly the `K`-rational solutions of `A x = 0`. -/
private theorem ker_traceRows [Fintype ι] (b : Basis κ K F) (A : Matrix m ι F) :
    LinearMap.ker (traceRows K b A).mulVecLin =
      LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F) := by
  classical
  ext x
  rw [mem_ker_restrictScalars_comp_iff, LinearMap.mem_ker, mulVecLin_apply, traceRows_mulVec]
  set b' := (Algebra.traceForm K F).dualBasis (traceForm_nondegenerate K F) b
  simp only [funext_iff, Prod.forall, Pi.zero_apply, ← b'.forall_coord_eq_zero_iff,
    Basis.coord_apply, Function.comp_def]

/-- Over a field `L` in which the trace of `F / K` is the sum of the `K`-embeddings of `F`, the
trace rows and the conjugate rows `σ ∘ A i` span the same subspace of `ι → L`. -/
private theorem span_image_traceRows_eq (b : Basis κ K F) (A : Matrix m ι F) {L : Type*}
    [Field L] [Algebra K L] [Fintype (F →ₐ[K] L)]
    (htr : ∀ z, algebraMap K L (Algebra.trace K F z) = ∑ σ : F →ₐ[K] L, σ z) :
    span L (Pi.algebraMap ι K L '' span K (Set.range (traceRows K b A).row)) =
      span L (Set.range fun p : (F →ₐ[K] L) × m ↦ p.1 ∘ A p.2) := by
  classical
  have := Fintype.ofFinite κ
  set b' := (Algebra.traceForm K F).dualBasis (traceForm_nondegenerate K F) b
  have h₁ (i : m) (l : κ) : Pi.algebraMap ι K L ((traceRows K b A).row (i, l)) =
      ∑ σ : F →ₐ[K] L, σ (b l) • (σ ∘ A i) := by
    ext j
    simp [traceRows, pi_algebraMap_apply, htr, Finset.sum_apply, mul_comm]
  have h₂ (σ : F →ₐ[K] L) (i : m) : σ ∘ A i =
      ∑ l, σ (b' l) • Pi.algebraMap ι K L ((traceRows K b A).row (i, l)) := by
    ext j
    conv_lhs => rw [Function.comp_apply, ← LinearMap.BilinForm.sum_apply_smul_dualBasis
      (traceForm_nondegenerate K F) b (A i j)]
    simp [traceRows, pi_algebraMap_apply, Finset.sum_apply, b', Algebra.smul_def, mul_comm]
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · have : span K (Set.range (traceRows K b A).row) ≤
        ((span L (Set.range fun p : (F →ₐ[K] L) × m ↦ p.1 ∘ A p.2)).restrictScalars K).comap
          (Pi.algebraMap ι K L) := by
      refine span_le.2 ?_
      rintro _ ⟨⟨i, l⟩, rfl⟩
      rw [SetLike.mem_coe, mem_comap, restrictScalars_mem, h₁]
      exact sum_mem fun σ _ ↦ smul_mem _ _ (subset_span ⟨(σ, i), rfl⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact this hy
  · rintro _ ⟨⟨σ, i⟩, rfl⟩
    beta_reduce
    rw [SetLike.mem_coe, h₂ σ i]
    exact sum_mem fun l _ ↦ smul_mem _ _ (subset_span ⟨_, subset_span ⟨(i, l), rfl⟩, rfl⟩)

end TraceRows

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
  {m ι : Type*} [Fintype m] [Fintype ι] [LinearOrder ι]

/-- The height bound for the `K`-rational solutions when every row of `A` is nonzero. -/
private theorem relativeSubspaceArakelovHeight_ker_le_prod_of_ne_zero (A : Matrix m ι F)
    (hA : ∀ i, A i ≠ 0) :
    relativeSubspaceArakelovHeight
        (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F)) ≤
      ∏ i, arakelovMulHeight (A i) := by
  classical
  -- The heights are compared over the normal closure `L` of `F / K`, which contains the
  -- `[F : K]` conjugates of `F` and in which the trace is the sum of the conjugates.
  let L := IntermediateField.normalClosure K F (AlgebraicClosure F)
  have : NumberField L := NumberField.of_module_finite K L
  have hcard : Fintype.card (F →ₐ[K] L) = finrank K F := by
    rw [Fintype.card_congr (normalClosure.algHomEquiv K F (AlgebraicClosure F)), AlgHom.card]
  have htr (z : F) : algebraMap K L (Algebra.trace K F z) = ∑ σ : F →ₐ[K] L, σ z := by
    apply Subtype.val_injective
    rw [IntermediateField.coe_sum, IntermediateField.coe_algebraMap_apply,
      trace_eq_sum_embeddings (AlgebraicClosure F)]
    -- `normalClosure.algHomEquiv σ` is `σ` followed by the inclusion of `L`.
    exact (Fintype.sum_equiv (normalClosure.algHomEquiv K F (AlgebraicClosure F)) _ _
      fun _ ↦ rfl).symm
  have hσ (σ : F →ₐ[K] L) (y : ι → F) : height2 (σ ∘ y) = height2 y := by
    simpa [absoluteHeight2_eq] using (σ : F →+* L).absoluteHeight2_comp y
  set b := Module.finBasis K F
  rw [← ker_traceRows b, ← subspaceHeight_pow_finrank, subspaceHeight_ker_mulVecLin,
    ← subspaceHeight_span_image_algebraMap (L := L), span_image_traceRows_eq b A htr]
  have hprod : ∏ i, arakelovMulHeight (A i) =
      (∏ p : (F →ₐ[K] L) × m, height2 (p.1 ∘ A p.2)) ^ finrank ℚ K := by
    -- Each row contributes its `[F : K]` conjugates, all of the same height.
    have hconj (i : m) : ∏ σ : F →ₐ[K] L, height2 (σ ∘ A i) = height2 (A i) ^ finrank K F := by
      simp [hσ, hcard]
    rw [Fintype.prod_prod_type_right, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [hconj, arakelovMulHeight_of_ne_zero (hA i), ← pow_mul,
      ← Module.finrank_mul_finrank ℚ K F, mul_comm]
  rw [hprod]
  refine pow_le_pow_left₀ (subspaceHeight_pos _).le ?_ _
  exact subspaceHeight_span_range_le_prod fun p ↦ by
    simpa [funext_iff] using hA p.2

/-- **The height of the `K`-rational solutions of a linear system over `F`.** For an extension
`F / K` of number fields and `A : Matrix m ι F`, the space of `x : ι → K` with
`A *ᵥ (algebraMap K F ∘ x) = 0` has relative Arakelov height over `K` at most the product of the
relative Arakelov heights over `F` of the rows of `A`. In absolute heights this is
`H₂(W) ≤ ∏ i, H₂(A i) ^ [F : K]`, with the zero row counting as `1`. -/
theorem relativeSubspaceArakelovHeight_ker_restrictScalars_comp_le_prod (A : Matrix m ι F) :
    relativeSubspaceArakelovHeight
        (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F)) ≤
      ∏ i, arakelovMulHeight (A i) := by
  classical
  -- Zero rows impose no condition and have height one, so they can be discarded.
  let A' : Matrix {i // A i ≠ 0} ι F := A.submatrix Subtype.val id
  have hker : LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F) =
      LinearMap.ker (A'.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, mulVecLin_apply, funext_iff, Pi.zero_apply, Subtype.forall]
    refine forall_congr' fun i ↦ ?_
    by_cases h : A i = 0
    · simp [h, mulVec, dotProduct]
    · simp [h, mulVec, dotProduct, A']
  have hprod : ∏ i, arakelovMulHeight (A i) = ∏ i, arakelovMulHeight (A' i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i ↦ A i ≠ 0),
      Fintype.prod_eq_one (α := {i // ¬A i ≠ 0}) _ fun i ↦ by simp [not_not.1 i.property],
      mul_one]
    exact Fintype.prod_congr _ _ fun i ↦ congrArg _ (funext fun j ↦ by simp [A'])
  rw [hker, hprod]
  exact relativeSubspaceArakelovHeight_ker_le_prod_of_ne_zero A' fun i ↦ i.property

/-- **The absolute height of the `K`-rational solutions of a linear system over `F`**: it is at
most the `[K : ℚ]`-th root of the product of the relative Arakelov heights of the rows. -/
theorem subspaceHeight_ker_restrictScalars_comp_le (A : Matrix m ι F) :
    (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F)).subspaceHeight ≤
      (∏ i, arakelovMulHeight (A i)) ^ (finrank ℚ K : ℝ)⁻¹ := by
  rw [← Real.pow_rpow_inv_natCast (subspaceHeight_pos _).le (finrank_pos (R := ℚ) (M := K)).ne',
    subspaceHeight_pow_finrank]
  exact Real.rpow_le_rpow (relativeSubspaceArakelovHeight_pos _).le
    (relativeSubspaceArakelovHeight_ker_restrictScalars_comp_le_prod A) (by positivity)

omit [LinearOrder ι] in
open scoped Classical in
/-- **Siegel's lemma relative to a field extension, basis form** (Bombieri–Gubler, Theorem
2.9.19). Let `F / K` be an extension of number fields, `D = [K : ℚ]` and `r₂` the number of
complex places of `K`, and let `A : Matrix m ι F`. The space `W` of `x : ι → K` with
`A *ᵥ (algebraMap K F ∘ x) = 0` has a `K`-basis `x 0, …, x (k - 1)` in `𝓞_K^ι`, where
`k = dim W`, satisfying
`∏ j, H(x j) ≤ (2 / π) ^ (k r₂ / D) * |discr K| ^ (k / (2 D)) * (∏ i, H_F(A i)) ^ (1 / D)`,
with `H` the absolute projective sup height and `H_F` the relative Arakelov height over `F`. -/
theorem exists_linearIndependent_mulVec_algebraMap_eq_zero_prod_absHeight_le
    (A : Matrix m ι F) :
    ∃ x : Fin (finrank K (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ
        Pi.algebraMap ι K F))) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (Set.range fun j i ↦ (x j i : K)) =
        LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F) ∧
      (∀ j, A *ᵥ (fun i ↦ algebraMap K F (x j i)) = 0) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / Real.pi) ^ ((finrank K (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ
            Pi.algebraMap ι K F)) * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ
            Pi.algebraMap ι K F)) : ℝ) / (2 * finrank ℚ K)) *
          (∏ i, arakelovMulHeight (A i)) ^ (finrank ℚ K : ℝ)⁻¹ := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨x, hli, hspan, hmem, hle⟩ := (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ
    Pi.algebraMap ι K F)).exists_linearIndependent_integerPoints_prod_absHeight_le
  refine ⟨x, hli, hspan, fun j ↦ ?_, hle.trans ?_⟩
  · exact (mem_ker_restrictScalars_comp_iff A _).1 (mem_integerPoints.1 (hmem j))
  · exact mul_le_mul_of_nonneg_left (subspaceHeight_ker_restrictScalars_comp_le A)
      (by positivity)

omit [LinearOrder ι] in
open scoped Classical in
/-- **Siegel's lemma relative to a field extension** (Bombieri–Gubler, Theorem 2.9.19). Let
`F / K` be an extension of number fields, `D = [K : ℚ]` and `r₂` the number of complex places of
`K`, and let `A : Matrix m ι F` have fewer than `#ι / [F : K]` rows. Then `A x = 0` has a nonzero
solution `x ∈ 𝓞_K^ι` with
`H(x) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 D)) * (∏ i, H_F(A i)) ^ (1 / (D k))`,
where `k = #ι - [F : K] #m`, `H` is the absolute projective sup height and `H_F` the relative
Arakelov height over `F`. -/
theorem exists_ne_zero_mulVec_algebraMap_eq_zero_absHeight_le (A : Matrix m ι F)
    (hA : finrank K F * Fintype.card m < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun i ↦ algebraMap K F (x i)) = 0 ∧
      absoluteProjectiveTupleHeight (fun i ↦ (x i : K)) ≤
        (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (∏ i, arakelovMulHeight (A i)) ^
            ((finrank ℚ K * (Fintype.card ι - finrank K F * Fintype.card m : ℕ) : ℝ)⁻¹) := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  -- The `K`-rational solutions are the kernel of `[F : K] · #m` equations over `K`.
  have hk : Fintype.card ι - finrank K F * Fintype.card m ≤
      finrank K (LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F)) := by
    have := (traceRows K (Module.finBasis K F) A).rank_le_card_height
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm] at this
    rw [← ker_traceRows (Module.finBasis K F) A, finrank_ker_mulVecLin]
    omega
  set W := LinearMap.ker (A.mulVecLin.restrictScalars K ∘ₗ Pi.algebraMap ι K F)
  set k := Fintype.card ι - finrank K F * Fintype.card m
  have hk₀ : (0 : ℝ) < k := by
    rw [Nat.cast_pos]
    omega
  have hW : W ≠ ⊥ := fun h ↦ by
    rw [h, finrank_bot] at hk
    omega
  obtain ⟨z, hzW, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_absHeight_le hW
  refine ⟨z, hz0, (mem_ker_restrictScalars_comp_iff A _).1 (mem_integerPoints.1 hzW),
    hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  have hP : 0 ≤ ∏ i, arakelovMulHeight (A i) :=
    Finset.prod_nonneg fun i _ ↦ arakelovMulHeight_nonneg (A i)
  calc W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ ≤ W.subspaceHeight ^ (k : ℝ)⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le (one_le_subspaceHeight W)
          (inv_anti₀ hk₀ (Nat.cast_le.2 hk))
    _ ≤ ((∏ i, arakelovMulHeight (A i)) ^ (finrank ℚ K : ℝ)⁻¹) ^ (k : ℝ)⁻¹ :=
        Real.rpow_le_rpow (subspaceHeight_pos W).le (subspaceHeight_ker_restrictScalars_comp_le A)
          (inv_nonneg.2 hk₀.le)
    _ = _ := by rw [← Real.rpow_mul hP, mul_inv]

end Matrix
