/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Analysis.CStarAlgebra.State.Space

/-!
# Completely positive contractions into matrix algebras

This file supplies the operations on completely positive contractions (c.p.c. maps) into the
matrix algebras `M_k = CStarMatrix (Fin k) (Fin k) ℂ` that are used in matrix approximation
arguments for traces on C⋆-algebras.

* `CompletelyPositiveMap.conj`: conjugation `x ↦ c⋆ x c` by an element `c` of a C⋆-algebra is
  completely positive.
* `CompletelyPositiveMapClass.star_map_mul_map_le_of_norm_map_one_le`: the c.p.c.
  Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ φ(a⋆a)` for a completely positive map with
  `‖φ 1‖ ≤ 1` on a unital C⋆-algebra; `CompletelyPositiveMapClass.norm_map_one_le_one_iff`
  identifies `‖φ 1‖ ≤ 1` with contractivity, and
  `CompletelyPositiveMapClass.norm_apply_star_hom_le` shows that precomposing a c.p.c. map with a
  star homomorphism keeps it contractive.
* `CStarMatrix.blockDiagonalSingle`: the corner embedding of `M_{n i}` in `M_{Σ i, n i}`, and
  `CompletelyPositiveMap.blockDiagonal`: the block-diagonal sum `a ↦ diag(φ_i(a))` of completely
  positive maps into matrix algebras, with the trace formula
  `CompletelyPositiveMap.normalizedTrace_blockDiagonal_apply`, which weights the block `i` by
  `|n i| / |Σ i, n i|`, and contractivity `CompletelyPositiveMap.norm_blockDiagonal_map_one_le`.
* `CompletelyPositiveMap.compression`: the compression `T ↦ (⟪e i, T e j⟫)ᵢⱼ` of `B(H)` by a finite
  family of vectors, which is the map `T ↦ V⋆TV` for `V x = Σ xᵢ eᵢ`. It is unital when the family
  is orthonormal (`CompletelyPositiveMap.compression_map_one`), and its normalized trace is
  `n⁻¹ Σᵢ ⟪eᵢ, T eᵢ⟫` (`CompletelyPositiveMap.normalizedTrace_compression`). For an orthonormal
  basis of the range of a finite-rank projection `P` this is the compression `T ↦ PTP`.
* `CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt`: the **Choi–Effros factorization**.
  A completely positive map `φ` from a nonzero unital C⋆-algebra into a matrix algebra factors
  as `φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` and `ψ` unital completely positive. The general form
  `CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt_of_finite` allows any unital
  C⋆-algebra as codomain, provided `φ 1` has finite spectrum. Its key step is
  `CompletelyPositiveMap.map_mul_eq_zero_of_map_one_mul_eq_zero`: `φ 1 q = 0` implies
  `φ a q = 0` for every `a`.

For the factorization, let `p` be the support projection of `h` and `h⁺` the inverse of `h` on
the range of `p`, both obtained from the continuous functional calculus, which applies to any
function since the spectrum is finite. The Kadison–Schwarz inequality gives
`φ(a)⋆φ(a) ≤ ‖φ 1‖ ‖a‖² φ(1)`, so `φ(a)(1 - p) = 0`, and by symmetry `φ(a) = p φ(a) p`. The map
`ψ(a) = h⁺ φ(a) h⁺ + ω(a)(1 - p)` for a state `ω` is completely positive and unital, and
`h ψ(a) h = p φ(a) p = φ(a)`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2 (numbering cited), proof of
  Lemma 2.7.
* M.-D. Choi and E. G. Effros, *The completely positive lifting problem for C⋆-algebras*,
  Ann. of Math. 104 (1976), 585–609.
-/

public section

noncomputable section

open scoped CStarAlgebra InnerProductSpace ComplexOrder Matrix
open CStarMatrix (ofMatrix)

namespace CompletelyPositiveMap

section Conj

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Conjugation `x ↦ c⋆ x c` by an element `c` of a C⋆-algebra, as a completely positive map:
the quadratic form of the amplified matrix at `y` is that of the original matrix at `c y`. -/
def conj (c : B) : B →CP B where
  toLinearMap :=
    { toFun x := star c * x * c
      map_add' x y := by simp [mul_add, add_mul]
      map_smul' z x := by simp [mul_smul_comm, smul_mul_assoc] }
  map_cstarMatrix_nonneg' _ M hM := by
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun y => ?_
    simpa [CStarMatrix.map_apply, mul_assoc, star_mul] using
      CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM fun i => c * y i

/-- Evaluation of the conjugation map. -/
@[simp] theorem conj_apply (c x : B) : conj c x = star c * x * c := (rfl)

end Conj

end CompletelyPositiveMap

namespace CompletelyPositiveMapClass

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [FunLike F A B]
  [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

/-- A completely positive map on a unital C⋆-algebra is contractive exactly when `‖φ 1‖ ≤ 1`. -/
theorem norm_map_one_le_one_iff (φ : F) : ‖φ 1‖ ≤ 1 ↔ ∀ a, ‖φ a‖ ≤ ‖a‖ := by
  refine ⟨fun h a => (norm_apply_le φ a).trans (mul_le_of_le_one_left (norm_nonneg a) h),
    fun h => (h 1).trans ?_⟩
  nontriviality A
  exact CStarRing.norm_one.le

/-- **The c.p.c. Kadison–Schwarz inequality.** A completely positive map `φ` on a unital
C⋆-algebra with `‖φ 1‖ ≤ 1` satisfies `φ(a)⋆ φ(a) ≤ φ(a⋆a)`. -/
theorem star_map_mul_map_le_of_norm_map_one_le (φ : F) (h : ‖φ 1‖ ≤ 1) (a : A) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  refine (star_map_mul_map_le φ a).trans ?_
  have h0 : 0 ≤ φ (star a * a) := map_nonneg φ (star_mul_self_nonneg a)
  calc ‖φ 1‖ • φ (star a * a) ≤ (1 : ℝ) • φ (star a * a) :=
        smul_le_smul_of_nonneg_right h h0
    _ = φ (star a * a) := one_smul ℝ _

/-- Precomposing a contractive map with a star homomorphism between C⋆-algebras keeps it
contractive. -/
theorem norm_apply_star_hom_le {C G : Type*} [NonUnitalCStarAlgebra C] [FunLike G C A]
    [NonUnitalAlgHomClass G ℂ C A] [StarHomClass G C A] (φ : F) (h : ‖φ 1‖ ≤ 1) (θ : G)
    (c : C) : ‖φ (θ c)‖ ≤ ‖c‖ :=
  ((norm_map_one_le_one_iff φ).mp h (θ c)).trans (NonUnitalStarAlgHom.norm_apply_le θ c)

end CompletelyPositiveMapClass

namespace CStarMatrix

section BlockDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*} [∀ i, Fintype (n i)]
  {R B : Type*} [Monoid R] [NonUnitalNonAssocSemiring B] [StarAddMonoid B]
  [DistribMulAction R B]

variable (R B) in
/-- The corner embedding `x ↦ diag(0, …, x, …, 0)` of `CStarMatrix (n i) (n i) B` as the `i`-th
diagonal block of `CStarMatrix (Σ i, n i) (Σ i, n i) B`. -/
def blockDiagonalSingle (i : ι) :
    CStarMatrix (n i) (n i) B →⋆ₙₐ[R] CStarMatrix (Σ i, n i) (Σ i, n i) B where
  toFun x := ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)))
  map_smul' c x := by
    change ofMatrix (Matrix.blockDiagonal' (Pi.single i (c • ofMatrix.symm x))) =
      c • ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)))
    rw [Pi.single_smul, Matrix.blockDiagonal'_smul]
    rfl
  map_zero' := by
    change ofMatrix (Matrix.blockDiagonal' (Pi.single i (0 : Matrix (n i) (n i) B))) = 0
    rw [Pi.single_zero, Matrix.blockDiagonal'_zero]
    rfl
  map_add' x y := by
    change ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x + ofMatrix.symm y))) =
      ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x))) +
        ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm y)))
    rw [Pi.single_add, Matrix.blockDiagonal'_add]
    rfl
  map_mul' x y := by
    change ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x * ofMatrix.symm y))) =
      ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)) *
        Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm y)))
    rw [Pi.single_mul]
    exact congrArg ofMatrix (Matrix.blockDiagonal'_mul _ _)
  map_star' x := by
    change ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)ᴴ)) =
      ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)))ᴴ
    refine (congrArg ofMatrix (Matrix.blockDiagonal'_conjTranspose _)).trans ?_ |>.symm
    congr 2
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- The corner embedding places `x` as the block `i` of a block-diagonal matrix. -/
theorem blockDiagonalSingle_apply (i : ι) (x : CStarMatrix (n i) (n i) B) :
    blockDiagonalSingle R B i x =
      ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x))) :=
  (rfl)

/-- A block-diagonal matrix is the sum of its corner embeddings. -/
theorem sum_blockDiagonalSingle (x : ∀ i, CStarMatrix (n i) (n i) B) :
    ∑ i, blockDiagonalSingle R B i (x i) =
      ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i)) := by
  have h := map_sum (Matrix.blockDiagonal'AddMonoidHom n n B)
    (fun c => Pi.single c (ofMatrix.symm (x c))) Finset.univ
  simp only [Matrix.blockDiagonal'AddMonoidHom_apply, Finset.univ_sum_single] at h
  change ofMatrix (∑ c, Matrix.blockDiagonal' (Pi.single c (ofMatrix.symm (x c)))) = _
  rw [← h]

/-- The normalized trace of a block-diagonal matrix weights the normalized trace of the block `i`
by `|n i| / |Σ i, n i|`. -/
theorem normalizedTrace_blockDiagonal' (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    normalizedTrace (ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i))) =
      ∑ i, (Fintype.card (n i) / Fintype.card (Σ i, n i) : ℂ) * normalizedTrace (x i) := by
  simp only [normalizedTrace_def, Equiv.symm_apply_apply, Matrix.trace_blockDiagonal',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (Fintype.card (n i)) 0 with h | h
  · have := Fintype.card_eq_zero_iff.mp h
    simp [Matrix.trace]
  · field_simp

end BlockDiagonal

/-- A complex matrix has finite real spectrum. -/
theorem finite_spectrum_real {n : Type*} [Fintype n] [DecidableEq n] (x : CStarMatrix n n ℂ) :
    (spectrum ℝ x).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  refine Set.Finite.preimage (Complex.ofReal_injective.injOn) ?_
  have h := AlgEquiv.spectrum_eq (R := ℂ) (ofMatrixStarAlgEquiv (n := n) (A := ℂ)) (ofMatrix.symm x)
  rw [← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply] at h
  rw [h]
  exact Matrix.finite_spectrum _

end CStarMatrix

namespace CompletelyPositiveMap

section BlockDiagonal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*} [∀ i, Fintype (n i)]

/-- Evaluation of a finite sum of completely positive maps. -/
theorem sum_apply {B κ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (s : Finset κ) (φ : κ → A →CP B) (a : A) : (∑ i ∈ s, φ i) a = ∑ i ∈ s, φ i a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl

/-- The **block-diagonal sum** `a ↦ diag(φ_i(a))` of completely positive maps
`φ_i : A → M_{n i}`, a completely positive map into `M_{Σ i, n i}`: the sum of the compositions of
the `φ_i` with the corner embeddings. -/
def blockDiagonal (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) :
    A →CP CStarMatrix (Σ i, n i) (Σ i, n i) ℂ :=
  ∑ i, (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.blockDiagonalSingle ℂ ℂ i)).comp (φ i)

/-- The block-diagonal sum evaluates to the block-diagonal matrix `diag(φ_i(a))`. -/
theorem blockDiagonal_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) (a : A) :
    blockDiagonal φ a = ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (φ i a)) := by
  rw [blockDiagonal, sum_apply, ← CStarMatrix.sum_blockDiagonalSingle (R := ℂ)]
  simp only [comp_apply, CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap]

/-- The block `i` of the block-diagonal sum is `φ_i`. -/
theorem blockDiagonal_apply_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) (a : A) (i : ι)
    (j k : n i) : blockDiagonal φ a ⟨i, j⟩ ⟨i, k⟩ = φ i a j k := by
  rw [blockDiagonal_apply]
  exact Matrix.blockDiagonal'_apply_eq (fun i => ofMatrix.symm (φ i a)) i j k

/-- The normalized trace of the block-diagonal sum weights the trace of `φ_i` by
`|n i| / |Σ i, n i|`: for blocks of sizes `1` and `3` the weights are `1/4` and `3/4`. -/
theorem normalizedTrace_blockDiagonal_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) (a : A) :
    CStarMatrix.normalizedTrace (blockDiagonal φ a) =
      ∑ i, (Fintype.card (n i) / Fintype.card (Σ i, n i) : ℂ) *
        CStarMatrix.normalizedTrace (φ i a) := by
  rw [blockDiagonal_apply, CStarMatrix.normalizedTrace_blockDiagonal']

/-- A block-diagonal sum of contractive completely positive maps on a unital C⋆-algebra is
contractive. -/
theorem norm_blockDiagonal_map_one_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) (h : ∀ i, ‖φ i 1‖ ≤ 1) :
    ‖blockDiagonal φ 1‖ ≤ 1 := by
  classical
  have h0 : 0 ≤ blockDiagonal φ 1 := map_nonneg _ (zero_le_one (α := A))
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ h0, ← sub_nonneg]
  have h1 : (1 : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) =
      ∑ i, CStarMatrix.blockDiagonalSingle ℂ ℂ i 1 := by
    rw [CStarMatrix.sum_blockDiagonalSingle (R := ℂ)]
    exact (congrArg ofMatrix (Matrix.blockDiagonal'_one (α := ℂ))).symm
  rw [h1, blockDiagonal, sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [comp_apply, CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap, ← map_sub]
  have hi : 0 ≤ 1 - φ i 1 := sub_nonneg.mpr
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_nonneg _ (zero_le_one (α := A)))).mp (h i))
  exact map_nonneg (CStarMatrix.blockDiagonalSingle ℂ ℂ i) hi

end BlockDiagonal

section Compression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {n : Type*} [Fintype n]

/-- The **compression** of `B(H)` by a finite family of vectors `e : n → H`: the matrix
`(⟪e i, T e j⟫)ᵢⱼ`, which is the matrix of `V⋆TV` for `V x = Σ xᵢ eᵢ`. Its quadratic forms are those
of `T` at the vectors `Σ_a v_a e_a`, so it is completely positive. -/
def compression (e : n → H) : (H →L[ℂ] H) →CP CStarMatrix n n ℂ where
  toLinearMap :=
    { toFun T := ofMatrix (Matrix.of fun i j => ⟪e i, T (e j)⟫_ℂ)
      map_add' S T := by ext i j; simp
      map_smul' c T := by ext i j; simp }
  map_cstarMatrix_nonneg' k M hM := by
    rw [← map_le_map_iff (CStarMatrix.compStarAlgEquiv ℂ (Fin k) n ℂ), map_zero]
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun v => ?_
    have key := CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mp hM
      fun p => (∑ a, v (p, a) • e a : H)
    convert key using 1
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun q _ => ?_)
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_)
    rw [CStarMatrix.compStarAlgEquiv_apply, CStarMatrix.map_apply]
    simp [CStarMatrix.ofMatrix_apply]
    ring

/-- The entries of the compression are `⟪e i, T e j⟫`. -/
@[simp]
theorem compression_apply (e : n → H) (T : H →L[ℂ] H) (i j : n) :
    compression e T i j = ⟪e i, T (e j)⟫_ℂ :=
  (rfl)

/-- The compression by an orthonormal family is unital. -/
theorem compression_map_one [DecidableEq n] {e : n → H} (he : Orthonormal ℂ e) :
    compression e 1 = 1 := by
  ext i j
  rw [compression_apply, one_apply_eq_self, orthonormal_iff_ite.mp he i j]
  rfl

/-- The normalized trace of the compression `(⟪e i, T e j⟫)ᵢⱼ` is `n⁻¹ Σᵢ ⟪e i, T e i⟫`. For an
orthonormal basis of the range of a finite-rank projection `P` this is `Tr(TP) / Tr(P)`. -/
theorem normalizedTrace_compression (e : n → H) (T : H →L[ℂ] H) :
    CStarMatrix.normalizedTrace (compression e T) =
      (Fintype.card n : ℂ)⁻¹ * ∑ i, ⟪e i, T (e i)⟫_ℂ := by
  simp [CStarMatrix.normalizedTrace_eq_sum]

end Compression

section ChoiEffros

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- If `φ 1 q = 0` for a completely positive map `φ` on a unital C⋆-algebra, then `φ a q = 0` for
every `a`: by the Kadison–Schwarz inequality, `q⋆ φ(a)⋆ φ(a) q ≤ ‖φ 1‖ ‖a⋆a‖ q⋆ φ(1) q = 0`. -/
theorem map_mul_eq_zero_of_map_one_mul_eq_zero (φ : A →CP B) {q : B} (h : φ 1 * q = 0) (a : A) :
    φ a * q = 0 := by
  have hle : φ (star a * a) ≤ ‖star a * a‖ • φ 1 := by
    have h1 := OrderHomClass.mono φ (IsSelfAdjoint.le_algebraMap_norm_self (star a * a))
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, Complex.coe_smul] at h1
  have hKS : star (φ a) * φ a ≤ (‖φ 1‖ * ‖star a * a‖) • φ 1 := by
    refine (CompletelyPositiveMapClass.star_map_mul_map_le φ a).trans ?_
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left hle (norm_nonneg _)
  have h0 : star (φ a * q) * (φ a * q) ≤ 0 := by
    have h2 := star_left_conjugate_le_conjugate hKS q
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc (star q) (φ 1), h, mul_zero, smul_zero] at h2
    simpa [star_mul, mul_assoc] using h2
  exact star_mul_self_eq_zero.mp (le_antisymm h0 (star_mul_self_nonneg _))

omit [PartialOrder A] [StarOrderedRing A] in
/-- The support projection `p` of a positive element `x` with finite spectrum and the inverse `g`
of `x^{1/2}` on its range, as functions of `x`: `x^{1/2} g = g x^{1/2} = g x g = p`, and `1 - p`
is a projection annihilated by `x` and `x^{1/2}`. The spectrum is finite, so the continuous
functional calculus applies to the discontinuous functions `[t ≠ 0]` and `[t ≠ 0] t^{-1/2}`. -/
private theorem exists_support_projection {x : B} (hx : 0 ≤ x) (hfin : (spectrum ℝ x).Finite) :
    ∃ p g : B, IsSelfAdjoint p ∧ IsSelfAdjoint g ∧ CFC.sqrt x * g = p ∧ g * CFC.sqrt x = p ∧
      g * x * g = p ∧ CFC.sqrt x * (1 - p) = 0 ∧ x * (1 - p) = 0 ∧
      (1 - p) * (1 - p) = 1 - p := by
  have hspec : ∀ t ∈ spectrum ℝ x, 0 ≤ t := fun t ht => spectrum_nonneg_of_nonneg hx ht
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ x) := hfin.continuousOn f
  have hh : CFC.sqrt x = cfc Real.sqrt x := by rw [CFC.sqrt_eq_real_sqrt x hx, cfcₙ_eq_cfc]
  have hmul (f₁ f₂ : ℝ → ℝ) : cfc f₁ x * cfc f₂ x = cfc (fun t => f₁ t * f₂ t) x :=
    (cfc_mul _ _ x (hc _) (hc _)).symm
  set p := cfc (fun t : ℝ => if t = 0 then 0 else 1) x with hpdef
  set g := cfc (fun t : ℝ => if t = 0 then 0 else (Real.sqrt t)⁻¹) x with hgdef
  have hsg : CFC.sqrt x * g = p := by
    rw [hh, hgdef, hmul]
    refine cfc_congr fun t ht => ?_
    rcases (hspec t ht).eq_or_lt with h0 | h0
    · simp [← h0]
    · simp [h0.ne', (Real.sqrt_pos.mpr h0).ne']
  have hcomm : g * CFC.sqrt x = CFC.sqrt x * g := by
    rw [hh, hgdef, hmul, hmul]
    exact cfc_congr fun t _ => mul_comm _ _
  have hgxg : g * x * g = p := by
    conv_lhs => rw [← cfc_id' ℝ x]
    rw [hgdef, hmul, hmul]
    refine cfc_congr fun t ht => ?_
    rcases (hspec t ht).eq_or_lt with h0 | h0
    · simp [← h0]
    · have hs := Real.mul_self_sqrt h0.le
      have hs0 := (Real.sqrt_pos.mpr h0).ne'
      simp only [h0.ne', ite_false]
      field_simp
      linarith
  have hsp : CFC.sqrt x * p = CFC.sqrt x := by
    rw [hh, hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  have hxp : x * p = x := by
    conv_rhs => rw [← cfc_id' ℝ x]
    conv_lhs => rw [← cfc_id' ℝ x]
    rw [hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  have hpp : p * p = p := by
    rw [hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  refine ⟨p, g, cfc_predicate _ x, cfc_predicate _ x, hsg, hcomm.trans hsg, hgxg, ?_, ?_, ?_⟩
  · rw [mul_sub, mul_one, hsp, sub_self]
  · rw [mul_sub, mul_one, hxp, sub_self]
  · rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hpp]
    abel

/-- **The Choi–Effros factorization**, for a codomain in which `φ 1` has finite spectrum. A
completely positive map `φ` from a nonzero unital C⋆-algebra factors as `φ(a) = h ψ(a) h` with
`h = φ(1)^{1/2}` and `ψ` unital completely positive: `ψ(a) = h⁺ φ(a) h⁺ + ω(a)(1 - p)` for the
support projection `p` of `h`, the inverse `h⁺` of `h` on the range of `p`, and a state `ω`. -/
theorem exists_unital_eq_sqrt_mul_mul_sqrt_of_finite [Nontrivial A] (φ : A →CP B)
    (hφ : (spectrum ℝ (φ 1)).Finite) :
    ∃ ψ : A →CP B, ψ 1 = 1 ∧ ∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) := by
  obtain ⟨p, g, hpsa, hgsa, hsg, hgs, hgxg, hsp, hxp, hpp⟩ :=
    exists_support_projection (map_nonneg φ zero_le_one) hφ
  have hqsa : IsSelfAdjoint (1 - p) := (IsSelfAdjoint.one B).sub hpsa
  -- a state `ω` of `A`
  obtain ⟨f, hf⟩ := TauCeti.stateSpace_nonempty (A := A)
  obtain ⟨ω, -, hω⟩ := TauCeti.mem_stateSpace_iff_exists_positiveLinearMap.mp hf
  have hω1 : ω 1 = 1 := by
    rw [← (TauCeti.mem_stateSpace_iff_map_one.mp hf).2, ← hω]
    rfl
  let ψ : A →CP B := (conj g).comp φ + (conj (1 - p)).comp
    ((CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ B)).comp
      ω.toCompletelyPositiveMap)
  have hψ (a : A) : ψ a = g * φ a * g + ω a • (1 - p) := by
    change ((conj g).comp φ) a + ((conj (1 - p)).comp
      ((CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ B)).comp
        ω.toCompletelyPositiveMap)) a = _
    rw [comp_apply, comp_apply, comp_apply,
      CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap, StarAlgHom.ofId_apply,
      conj_apply, conj_apply, PositiveLinearMap.toCompletelyPositiveMap_apply, hgsa.star_eq,
      hqsa.star_eq, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hpp]
  refine ⟨ψ, ?_, fun a => ?_⟩
  · rw [hψ, hgxg, hω1, one_smul, add_sub_cancel]
  -- `φ a = p φ(a) p`, since `φ(a)(1 - p) = 0` and `(1 - p)φ(a) = (φ(a⋆)(1 - p))⋆ = 0`
  have hr := map_mul_eq_zero_of_map_one_mul_eq_zero φ hxp a
  have hl : (1 - p) * φ a = 0 := by
    have := map_mul_eq_zero_of_map_one_mul_eq_zero φ hxp (star a)
    rw [map_star φ a] at this
    simpa [star_mul, hqsa.star_eq] using congrArg star this
  rw [mul_sub, mul_one, sub_eq_zero] at hr
  rw [sub_mul, one_mul, sub_eq_zero] at hl
  calc φ a = p * φ a * p := by rw [← hl, ← hr]
    _ = CFC.sqrt (φ 1) * (g * φ a * g) * CFC.sqrt (φ 1) := by
      have e : CFC.sqrt (φ 1) * (g * φ a * g) * CFC.sqrt (φ 1) =
          CFC.sqrt (φ 1) * g * φ a * (g * CFC.sqrt (φ 1)) := by simp only [mul_assoc]
      rw [e, hsg, hgs]
    _ = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) := by
      rw [hψ, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hsp, zero_mul, smul_zero,
        add_zero]

/-- **The Choi–Effros factorization.** A completely positive map `φ` from a nonzero unital
C⋆-algebra into a matrix algebra factors as `φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` and `ψ`
unital completely positive. For `φ(a) = diag(a₁, 0)` on `ℂ²`, `h = e₁₁` and
`ψ(a) = diag(a₁, ω(a))` for a state `ω`. -/
theorem exists_unital_eq_sqrt_mul_mul_sqrt [Nontrivial A] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →CP CStarMatrix n n ℂ) :
    ∃ ψ : A →CP CStarMatrix n n ℂ, ψ 1 = 1 ∧ ∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) :=
  exists_unital_eq_sqrt_mul_mul_sqrt_of_finite φ (CStarMatrix.finite_spectrum_real _)

end ChoiEffros

end CompletelyPositiveMap
