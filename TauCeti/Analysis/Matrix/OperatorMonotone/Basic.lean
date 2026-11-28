/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Function
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import TauCeti.Analysis.Matrix.FunctionalCalculus
import TauCeti.Analysis.Matrix.Order
import TauCeti.LinearAlgebra.Matrix.Hermitian.Basic
import TauCeti.LinearAlgebra.Matrix.Block.Spectrum
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Matrix and operator monotone and convex functions

A real function `f` acts on a Hermitian matrix `A` through Mathlib's continuous functional
calculus `cfc f A`; since the spectrum of a matrix is finite, every `f` is continuous on it and
`cfc f A` is the spectral value. Square matrices are ordered by the Loewner order of
`open scoped MatrixOrder`, in which `A ≤ B` means that `B - A` is positive semidefinite.

* `TauCeti.IsMatrixMonotoneOn n f I`: for Hermitian `n × n` complex matrices `A ≤ B` with spectra
  in `I`, `cfc f A ≤ cfc f B`. `TauCeti.IsOperatorMonotoneOn f I`: this holds for every `n`.
* `TauCeti.IsMatrixConvexOn n f I`: for Hermitian `n × n` complex matrices `A`, `B` with spectra
  in `I` and `t ∈ [0, 1]`, `cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B`.
  `TauCeti.IsOperatorConvexOn f I`: this holds for every `n`, and
  `TauCeti.IsOperatorConcaveOn f I`: `-f` is operator convex on `I`.

## Main results

* `TauCeti.IsOperatorMonotoneOn.cfc_le_cfc`,
  `TauCeti.IsOperatorConvexOn.cfc_one_sub_smul_add_smul_le` and
  `TauCeti.IsOperatorConcaveOn.le_cfc_one_sub_smul_add_smul`: the operator notions apply to
  Hermitian matrices over any finite index type, not only `Fin n`.
* `TauCeti.IsMatrixMonotoneOn.of_le` and `TauCeti.IsMatrixConvexOn.of_le`: matrix monotonicity
  and convexity of order `n` imply those of every order `m ≤ n`, through the direct sum with a
  scalar `c ∈ I`.
* `TauCeti.isMatrixMonotoneOn_zero`, `TauCeti.isMatrixMonotoneOn_one_iff` and their convex
  counterparts: every function is matrix monotone and convex of order `0`; order `1` is scalar
  monotonicity on `I` and, when `I` is convex, scalar convexity on `I`. Hence an operator
  monotone function is monotone on `I` and an operator convex function is convex on a convex `I`.
* The cone properties: sums and nonnegative multiples of matrix and operator monotone, convex
  or concave functions are again so, and constants and the identity are all three.
* `TauCeti.IsOperatorMonotoneOn.comp`: if `g` is operator monotone on `I` and maps `I` into `J`,
  and `f` is operator monotone on `J`, then `f ∘ g` is operator monotone on `I`.
* `TauCeti.isOperatorMonotoneOn_of_tendsto`: a pointwise limit on `I`, along any nontrivial
  filter, of operator monotone functions on `I` is operator monotone on `I`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Section V.1,
  p. 112.
* R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press (1991),
  Definitions 6.6.33, p. 536, and 6.6.47, p. 544.
-/

public section

open Filter Matrix Set Topology
open scoped MatrixOrder ComplexOrder

namespace TauCeti

variable {m n : ℕ} {f g : ℝ → ℝ} {I J : Set ℝ}

/-! ### The definitions -/

/-- `f` is matrix monotone of order `n` on `I`: it preserves the Loewner order between Hermitian
`n × n` complex matrices with spectra in `I`. -/
def IsMatrixMonotoneOn (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ ⦃A B : Matrix (Fin n) (Fin n) ℂ⦄, A.IsHermitian → B.IsHermitian → spectrum ℝ A ⊆ I →
    spectrum ℝ B ⊆ I → A ≤ B → cfc f A ≤ cfc f B

/-- `f` is operator monotone on `I`: matrix monotone of every order on `I`. -/
def IsOperatorMonotoneOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ n, IsMatrixMonotoneOn n f I

/-- `f` is matrix convex of order `n` on `I`: for Hermitian `n × n` complex matrices `A` and `B`
with spectra in `I` and `t ∈ [0, 1]`,
`cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B`. -/
def IsMatrixConvexOn (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ ⦃A B : Matrix (Fin n) (Fin n) ℂ⦄, A.IsHermitian → B.IsHermitian → spectrum ℝ A ⊆ I →
    spectrum ℝ B ⊆ I → ∀ ⦃t : ℝ⦄, t ∈ Icc (0 : ℝ) 1 →
      cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B

/-- `f` is operator convex on `I`: matrix convex of every order on `I`. -/
def IsOperatorConvexOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ n, IsMatrixConvexOn n f I

/-- `f` is operator concave on `I`: `-f` is operator convex on `I`. -/
def IsOperatorConcaveOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  IsOperatorConvexOn (fun t ↦ -f t) I

/-- Unfolding `TauCeti.IsMatrixMonotoneOn`. -/
theorem isMatrixMonotoneOn_iff :
    IsMatrixMonotoneOn n f I ↔ ∀ ⦃A B : Matrix (Fin n) (Fin n) ℂ⦄, A.IsHermitian →
      B.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ B ⊆ I → A ≤ B → cfc f A ≤ cfc f B :=
  Iff.rfl

/-- Unfolding `TauCeti.IsOperatorMonotoneOn`. -/
theorem isOperatorMonotoneOn_iff : IsOperatorMonotoneOn f I ↔ ∀ n, IsMatrixMonotoneOn n f I :=
  Iff.rfl

/-- Unfolding `TauCeti.IsMatrixConvexOn`. -/
theorem isMatrixConvexOn_iff :
    IsMatrixConvexOn n f I ↔ ∀ ⦃A B : Matrix (Fin n) (Fin n) ℂ⦄, A.IsHermitian →
      B.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ B ⊆ I → ∀ ⦃t : ℝ⦄, t ∈ Icc (0 : ℝ) 1 →
        cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B :=
  Iff.rfl

/-- Unfolding `TauCeti.IsOperatorConvexOn`. -/
theorem isOperatorConvexOn_iff : IsOperatorConvexOn f I ↔ ∀ n, IsMatrixConvexOn n f I :=
  Iff.rfl

/-- Unfolding `TauCeti.IsOperatorConcaveOn`. -/
theorem isOperatorConcaveOn_iff :
    IsOperatorConcaveOn f I ↔ IsOperatorConvexOn (fun t ↦ -f t) I :=
  Iff.rfl

/-! ### Matrix monotone functions -/

namespace IsMatrixMonotoneOn

/-- The defining inequality of matrix monotonicity of order `n`, over any index type with `n`
elements. -/
private theorem cfc_le_cfc_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMatrixMonotoneOn n f I) (hι : Fintype.card ι = n) {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    (hAB : A ≤ B) : cfc f A ≤ cfc f B := by
  -- Reindex along `ι ≃ Fin n`: an algebra isomorphism, so it keeps the spectra.
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hι
  rw [← reindex_le_reindex_iff e, ← cfc_reindex, ← cfc_reindex]
  exact hf (hA.submatrix _) (hB.submatrix _)
    ((AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℂ e) A).trans_subset hAI)
    ((AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℂ e) B).trans_subset hBI)
    ((reindex_le_reindex_iff e).2 hAB)

/-- Matrix monotonicity on `I` implies matrix monotonicity on every subset of `I`. -/
theorem mono (hf : IsMatrixMonotoneOn n f I) (hJI : J ⊆ I) : IsMatrixMonotoneOn n f J :=
  fun _ _ hA hB hAJ hBJ hAB ↦ hf hA hB (hAJ.trans hJI) (hBJ.trans hJI) hAB

/-- Matrix monotonicity on `I` depends only on the values of the function on `I`. -/
theorem congr (hf : IsMatrixMonotoneOn n f I) (hfg : EqOn f g I) : IsMatrixMonotoneOn n g I :=
  fun A B hA hB hAI hBI hAB ↦ by
    rw [← cfc_congr (hfg.mono hAI), ← cfc_congr (hfg.mono hBI)]
    exact hf hA hB hAI hBI hAB

end IsMatrixMonotoneOn

/-- Every function is matrix monotone of order `0`, since there is a single `0 × 0` matrix. -/
@[simp]
theorem isMatrixMonotoneOn_zero (f : ℝ → ℝ) (I : Set ℝ) : IsMatrixMonotoneOn 0 f I :=
  fun A B _ _ _ _ _ ↦ (Subsingleton.elim (cfc f A) (cfc f B)).le

/-- Every function is matrix monotone of every order on the empty set: a Hermitian matrix with
empty spectrum is the `0 × 0` matrix. -/
@[simp]
theorem isMatrixMonotoneOn_empty (n : ℕ) (f : ℝ → ℝ) : IsMatrixMonotoneOn n f ∅ :=
  fun A B hA _ hAI _ _ ↦ by
    have : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := not_nontrivial_iff_subsingleton.1 fun _ ↦
      (ContinuousFunctionalCalculus.spectrum_nonempty A hA.isSelfAdjoint).ne_empty
        (subset_empty_iff.1 hAI)
    exact (Subsingleton.elim (cfc f A) (cfc f B)).le

/-- Constant functions are matrix monotone of every order on every set. -/
@[simp]
theorem isMatrixMonotoneOn_const (n : ℕ) (c : ℝ) (I : Set ℝ) :
    IsMatrixMonotoneOn n (fun _ ↦ c) I :=
  fun A B hA hB _ _ _ ↦ by rw [cfc_const c A hA.isSelfAdjoint, cfc_const c B hB.isSelfAdjoint]

/-- The identity is matrix monotone of every order on every set. -/
@[simp]
theorem isMatrixMonotoneOn_id (n : ℕ) (I : Set ℝ) : IsMatrixMonotoneOn n id I :=
  fun A B hA hB _ _ hAB ↦ by rwa [cfc_id ℝ A hA.isSelfAdjoint, cfc_id ℝ B hB.isSelfAdjoint]

/-- Matrix monotonicity of order `1` is monotonicity on `I`. -/
@[simp]
theorem isMatrixMonotoneOn_one_iff : IsMatrixMonotoneOn 1 f I ↔ MonotoneOn f I := by
  refine ⟨fun hf a ha b hb hab ↦ ?_, fun hf A B hA hB hAI hBI hAB ↦ ?_⟩
  · have h := hf (A := algebraMap ℝ _ a) (B := algebraMap ℝ _ b)
      (IsSelfAdjoint.algebraMap _ (.all a)).isHermitian
      (IsSelfAdjoint.algebraMap _ (.all b)).isHermitian
      (by simpa [spectrum.scalar_eq] using ha) (by simpa [spectrum.scalar_eq] using hb)
      (algebraMap_le_algebraMap.2 hab)
    rwa [cfc_algebraMap, cfc_algebraMap, algebraMap_le_algebraMap] at h
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, A = algebraMap ℝ _ a := ⟨_, hA.eq_algebraMap_re⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℝ, B = algebraMap ℝ _ b := ⟨_, hB.eq_algebraMap_re⟩
    rw [cfc_algebraMap, cfc_algebraMap, algebraMap_le_algebraMap] at *
    simp only [spectrum.scalar_eq, singleton_subset_iff] at hAI hBI
    exact hf hAI hBI hAB

namespace IsMatrixMonotoneOn

/-- Matrix monotonicity of order `n + 1` implies matrix monotonicity of order `n`, through the
direct sum with a `1 × 1` scalar `c ∈ I`. -/
theorem of_succ (hf : IsMatrixMonotoneOn (n + 1) f I) : IsMatrixMonotoneOn n f I := by
  intro A B hA hB hAI hBI hAB
  rcases I.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact isMatrixMonotoneOn_empty n f hA hB hAI hBI hAB
  set C : Matrix (Fin 1) (Fin 1) ℂ := algebraMap ℝ _ c
  have hC : C.IsHermitian := (IsSelfAdjoint.algebraMap _ (.all c)).isHermitian
  have hCI : spectrum ℝ C ⊆ I := by simpa [C, spectrum.scalar_eq] using hc
  have h := hf.cfc_le_cfc_of_card_eq (ι := Fin n ⊕ Fin 1) (by simp)
    (hA.fromBlocks conjTranspose_zero hC) (hB.fromBlocks conjTranspose_zero hC)
    (by rw [spectrum_fromBlocks_zero₂₁]; exact union_subset hAI hCI)
    (by rw [spectrum_fromBlocks_zero₂₁]; exact union_subset hBI hCI)
    (fromBlocks_le_fromBlocks_iff.2 ⟨hAB, le_rfl⟩)
  rw [cfc_fromBlocks_zero₁₂_zero₂₁ hA hC, cfc_fromBlocks_zero₁₂_zero₂₁ hB hC] at h
  exact (fromBlocks_le_fromBlocks_iff.1 h).1

/-- Matrix monotonicity of order `n` implies matrix monotonicity of every order `m ≤ n`. -/
theorem of_le (hf : IsMatrixMonotoneOn n f I) (hmn : m ≤ n) : IsMatrixMonotoneOn m f I := by
  induction n, hmn using Nat.le_induction with
  | base => exact hf
  | succ n _ ih => exact ih hf.of_succ

/-- A matrix monotone function of order `n` on `I` preserves the Loewner order between Hermitian
matrices with spectra in `I` over any index type with at most `n` elements. -/
theorem cfc_le_cfc_of_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMatrixMonotoneOn n f I) (hι : Fintype.card ι ≤ n) {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) :
    cfc f A ≤ cfc f B :=
  -- `B = A + (B - A)` is Hermitian, since `B - A` is positive semidefinite.
  (hf.of_le hι).cfc_le_cfc_of_card_eq rfl hA
    (add_sub_cancel A B ▸ hA.add (le_iff.1 hAB).isHermitian) hAI hBI hAB

/-- A matrix monotone function of order `n` preserves the Loewner order between Hermitian
`n × n` matrices with spectra in `I`. -/
theorem cfc_le_cfc (hf : IsMatrixMonotoneOn n f I) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) :
    cfc f A ≤ cfc f B :=
  hf.cfc_le_cfc_of_card_le (Fintype.card_fin n).le hA hAI hBI hAB

/-- A matrix monotone function of positive order on `I` is monotone on `I`. -/
theorem monotoneOn (hf : IsMatrixMonotoneOn n f I) (hn : n ≠ 0) : MonotoneOn f I :=
  isMatrixMonotoneOn_one_iff.1 (hf.of_le (Nat.one_le_iff_ne_zero.2 hn))

/-- The sum of two matrix monotone functions of order `n` on `I` is matrix monotone. -/
theorem add (hf : IsMatrixMonotoneOn n f I) (hg : IsMatrixMonotoneOn n g I) :
    IsMatrixMonotoneOn n (f + g) I :=
  fun A B hA hB hAI hBI hAB ↦ by
    simp only [Pi.add_def]
    rw [cfc_add (a := A) f g (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _),
      cfc_add (a := B) f g (B.finite_real_spectrum.continuousOn _)
        (B.finite_real_spectrum.continuousOn _)]
    exact add_le_add (hf hA hB hAI hBI hAB) (hg hA hB hAI hBI hAB)

/-- A nonnegative multiple of a matrix monotone function of order `n` on `I` is matrix
monotone. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsMatrixMonotoneOn n f I) :
    IsMatrixMonotoneOn n (fun x ↦ c • f x) I :=
  fun A B hA hB hAI hBI hAB ↦ by
    rw [cfc_smul c f A (A.finite_real_spectrum.continuousOn _),
      cfc_smul c f B (B.finite_real_spectrum.continuousOn _)]
    exact smul_le_smul_of_nonneg_left (hf hA hB hAI hBI hAB) hc

/-- **Composition.** If `g` is matrix monotone of order `n` on `I` and maps `I` into `J`, and `f`
is matrix monotone of order `n` on `J`, then `f ∘ g` is matrix monotone of order `n` on `I`. -/
theorem comp (hf : IsMatrixMonotoneOn n f J) (hg : IsMatrixMonotoneOn n g I)
    (hgIJ : MapsTo g I J) : IsMatrixMonotoneOn n (f ∘ g) I :=
  fun A B hA hB hAI hBI hAB ↦ by
    -- `cfc (f ∘ g) X = cfc f (cfc g X)`, and `cfc g X` is Hermitian with spectrum `g '' σ(X)`.
    have key : ∀ {X : Matrix (Fin n) (Fin n) ℂ}, X.IsHermitian → spectrum ℝ X ⊆ I →
        (cfc g X).IsHermitian ∧ spectrum ℝ (cfc g X) ⊆ J ∧ cfc (f ∘ g) X = cfc f (cfc g X) :=
      fun {X} hX hXI ↦ ⟨(cfc_predicate g X).isHermitian, by
        rw [cfc_map_spectrum g X hX.isSelfAdjoint (X.finite_real_spectrum.continuousOn _)]
        exact image_subset_iff.2 fun x hx ↦ hgIJ (hXI hx),
        cfc_comp f g X hX.isSelfAdjoint ((X.finite_real_spectrum.image g).continuousOn _)
          (X.finite_real_spectrum.continuousOn _)⟩
    obtain ⟨hA', hAJ, hAc⟩ := key hA hAI
    obtain ⟨hB', hBJ, hBc⟩ := key hB hBI
    rw [hAc, hBc]
    exact hf hA' hB' hAJ hBJ (hg hA hB hAI hBI hAB)

end IsMatrixMonotoneOn

/-- **Pointwise limits.** A pointwise limit on `I`, along a nontrivial filter, of matrix monotone
functions of order `n` on `I` is matrix monotone of order `n` on `I`. -/
theorem isMatrixMonotoneOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℝ → ℝ}
    (hF : ∀ k, IsMatrixMonotoneOn n (F k) I)
    (hlim : ∀ x ∈ I, Tendsto (fun k ↦ F k x) l (𝓝 (f x))) : IsMatrixMonotoneOn n f I :=
  -- The spectra are finite, so `cfc (F k) → cfc f` there; the Loewner order is closed.
  fun A B hA hB hAI hBI hAB ↦
    le_of_tendsto_of_tendsto'
      (tendsto_cfc_fun_of_finite_spectrum A.finite_real_spectrum fun t ht ↦ hlim t (hAI ht))
      (tendsto_cfc_fun_of_finite_spectrum B.finite_real_spectrum fun t ht ↦ hlim t (hBI ht))
      fun k ↦ hF k hA hB hAI hBI hAB

/-! ### Operator monotone functions -/

namespace IsOperatorMonotoneOn

/-- An operator monotone function is matrix monotone of every order. -/
theorem isMatrixMonotoneOn (hf : IsOperatorMonotoneOn f I) (n : ℕ) :
    IsMatrixMonotoneOn n f I :=
  hf n

/-- An operator monotone function on `I` preserves the Loewner order between Hermitian matrices
with spectra in `I`, over any finite index type. -/
theorem cfc_le_cfc {ι : Type*} [Fintype ι] [DecidableEq ι] (hf : IsOperatorMonotoneOn f I)
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I)
    (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) : cfc f A ≤ cfc f B :=
  (hf _).cfc_le_cfc_of_card_le le_rfl hA hAI hBI hAB

/-- Operator monotonicity on `I` implies operator monotonicity on every subset of `I`. -/
theorem mono (hf : IsOperatorMonotoneOn f I) (hJI : J ⊆ I) : IsOperatorMonotoneOn f J :=
  fun n ↦ (hf n).mono hJI

/-- Operator monotonicity on `I` depends only on the values of the function on `I`. -/
theorem congr (hf : IsOperatorMonotoneOn f I) (hfg : EqOn f g I) : IsOperatorMonotoneOn g I :=
  fun n ↦ (hf n).congr hfg

/-- An operator monotone function on `I` is monotone on `I`. -/
theorem monotoneOn (hf : IsOperatorMonotoneOn f I) : MonotoneOn f I :=
  isMatrixMonotoneOn_one_iff.1 (hf 1)

/-- The sum of two operator monotone functions on `I` is operator monotone. -/
theorem add (hf : IsOperatorMonotoneOn f I) (hg : IsOperatorMonotoneOn g I) :
    IsOperatorMonotoneOn (f + g) I :=
  fun n ↦ (hf n).add (hg n)

/-- A nonnegative multiple of an operator monotone function on `I` is operator monotone. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsOperatorMonotoneOn f I) :
    IsOperatorMonotoneOn (fun x ↦ c • f x) I :=
  fun n ↦ (hf n).smul hc

/-- **Composition.** If `g` is operator monotone on `I` and maps `I` into `J`, and `f` is operator
monotone on `J`, then `f ∘ g` is operator monotone on `I`. -/
theorem comp (hf : IsOperatorMonotoneOn f J) (hg : IsOperatorMonotoneOn g I)
    (hgIJ : MapsTo g I J) : IsOperatorMonotoneOn (f ∘ g) I :=
  fun n ↦ (hf n).comp (hg n) hgIJ

end IsOperatorMonotoneOn

/-- Constant functions are operator monotone on every set. -/
@[simp]
theorem isOperatorMonotoneOn_const (c : ℝ) (I : Set ℝ) : IsOperatorMonotoneOn (fun _ ↦ c) I :=
  fun n ↦ isMatrixMonotoneOn_const n c I

/-- The identity is operator monotone on every set. -/
@[simp]
theorem isOperatorMonotoneOn_id (I : Set ℝ) : IsOperatorMonotoneOn id I :=
  fun n ↦ isMatrixMonotoneOn_id n I

/-- **Pointwise limits.** A pointwise limit on `I`, along a nontrivial filter (for instance a
sequence along `atTop`), of operator monotone functions on `I` is operator monotone on `I`. -/
theorem isOperatorMonotoneOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℝ → ℝ}
    {f : ℝ → ℝ} {I : Set ℝ} (hF : ∀ k, IsOperatorMonotoneOn (F k) I)
    (hlim : ∀ x ∈ I, Tendsto (fun k ↦ F k x) l (𝓝 (f x))) :
    IsOperatorMonotoneOn f I :=
  fun n ↦ isMatrixMonotoneOn_of_tendsto (fun k ↦ hF k n) hlim

/-! ### Matrix convex functions -/

namespace IsMatrixConvexOn

/-- The defining inequality of matrix convexity of order `n`, over any index type with `n`
elements. -/
private theorem cfc_one_sub_smul_add_smul_le_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMatrixConvexOn n f I) (hι : Fintype.card ι = n) {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B := by
  -- Reindex along `ι ≃ Fin n`: an algebra isomorphism, so it keeps the spectra.
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hι
  have hlin : ∀ X Y : Matrix ι ι ℂ,
      reindex e e ((1 - t) • X + t • Y) = (1 - t) • reindex e e X + t • reindex e e Y :=
    fun X Y ↦ by ext; simp
  rw [← reindex_le_reindex_iff e, ← cfc_reindex, hlin, hlin, ← cfc_reindex, ← cfc_reindex]
  exact hf (hA.submatrix _) (hB.submatrix _)
    ((AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℂ e) A).trans_subset hAI)
    ((AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℂ e) B).trans_subset hBI) ht

/-- Matrix convexity on `I` implies matrix convexity on every subset of `I`. -/
theorem mono (hf : IsMatrixConvexOn n f I) (hJI : J ⊆ I) : IsMatrixConvexOn n f J :=
  fun _ _ hA hB hAJ hBJ _ ht ↦ hf hA hB (hAJ.trans hJI) (hBJ.trans hJI) ht

end IsMatrixConvexOn

/-- Every function is matrix convex of order `0`, since there is a single `0 × 0` matrix. -/
@[simp]
theorem isMatrixConvexOn_zero (f : ℝ → ℝ) (I : Set ℝ) : IsMatrixConvexOn 0 f I :=
  fun _ _ _ _ _ _ _ _ ↦ (Subsingleton.elim _ _).le

/-- Every function is matrix convex of every order on the empty set: a Hermitian matrix with
empty spectrum is the `0 × 0` matrix. -/
@[simp]
theorem isMatrixConvexOn_empty (n : ℕ) (f : ℝ → ℝ) : IsMatrixConvexOn n f ∅ :=
  fun A _ hA _ hAI _ _ _ ↦ by
    have : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := not_nontrivial_iff_subsingleton.1 fun _ ↦
      (ContinuousFunctionalCalculus.spectrum_nonempty A hA.isSelfAdjoint).ne_empty
        (subset_empty_iff.1 hAI)
    exact (Subsingleton.elim _ _).le

/-- Constant functions are matrix convex of every order on every set. -/
@[simp]
theorem isMatrixConvexOn_const (n : ℕ) (c : ℝ) (I : Set ℝ) :
    IsMatrixConvexOn n (fun _ ↦ c) I :=
  fun A B hA hB _ _ t _ ↦ by
    rw [cfc_const c _ ((hA.smul (.all (1 - t))).add (hB.smul (.all t))).isSelfAdjoint,
      cfc_const c A hA.isSelfAdjoint, cfc_const c B hB.isSelfAdjoint, ← add_smul, sub_add_cancel,
      one_smul]

/-- The identity is matrix convex of every order on every set. -/
@[simp]
theorem isMatrixConvexOn_id (n : ℕ) (I : Set ℝ) : IsMatrixConvexOn n id I :=
  fun A B hA hB _ _ t _ ↦ by
    rw [cfc_id ℝ _ ((hA.smul (.all (1 - t))).add (hB.smul (.all t))).isSelfAdjoint,
      cfc_id ℝ A hA.isSelfAdjoint, cfc_id ℝ B hB.isSelfAdjoint]

/-- On a convex set, matrix convexity of order `1` is convexity. -/
@[simp]
theorem isMatrixConvexOn_one_iff (hI : Convex ℝ I) : IsMatrixConvexOn 1 f I ↔ ConvexOn ℝ I f := by
  -- Real convex combinations of real scalars in the `1 × 1` matrices.
  have hlin : ∀ s u v : ℝ, (1 - s) • algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ) u +
      s • algebraMap ℝ _ v = algebraMap ℝ _ ((1 - s) • u + s • v) := by
    intro s u v
    simp only [Algebra.algebraMap_eq_smul_one, smul_smul, add_smul, smul_eq_mul]
  refine ⟨fun hf ↦ ⟨hI, fun a ha b hb s r hs hr hsr ↦ ?_⟩, fun hf A B hA hB hAI hBI t ht ↦ ?_⟩
  · obtain rfl : s = 1 - r := eq_sub_of_add_eq hsr
    have h := hf (A := algebraMap ℝ _ a) (B := algebraMap ℝ _ b)
      (IsSelfAdjoint.algebraMap _ (.all a)).isHermitian
      (IsSelfAdjoint.algebraMap _ (.all b)).isHermitian
      (by simpa [spectrum.scalar_eq] using ha) (by simpa [spectrum.scalar_eq] using hb)
      ⟨hr, by linarith⟩
    rwa [hlin, cfc_algebraMap, cfc_algebraMap, cfc_algebraMap, hlin,
      algebraMap_le_algebraMap] at h
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, A = algebraMap ℝ _ a := ⟨_, hA.eq_algebraMap_re⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℝ, B = algebraMap ℝ _ b := ⟨_, hB.eq_algebraMap_re⟩
    rw [hlin, cfc_algebraMap, cfc_algebraMap, cfc_algebraMap, hlin, algebraMap_le_algebraMap]
    simp only [spectrum.scalar_eq, singleton_subset_iff] at hAI hBI
    exact hf.2 hAI hBI (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)

namespace IsMatrixConvexOn

/-- Matrix convexity of order `n + 1` implies matrix convexity of order `n`, through the direct
sum with a `1 × 1` scalar `c ∈ I`. -/
theorem of_succ (hf : IsMatrixConvexOn (n + 1) f I) : IsMatrixConvexOn n f I := by
  intro A B hA hB hAI hBI t ht
  rcases I.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact isMatrixConvexOn_empty n f hA hB hAI hBI ht
  set C : Matrix (Fin 1) (Fin 1) ℂ := algebraMap ℝ _ c
  have hC : C.IsHermitian := (IsSelfAdjoint.algebraMap _ (.all c)).isHermitian
  have hCI : spectrum ℝ C ⊆ I := by simpa [C, spectrum.scalar_eq] using hc
  -- Convex combinations of block diagonal matrices with the same lower block `Z`.
  have hcomb : ∀ {p : Type} (X Y : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix p p ℂ),
      (1 - t) • fromBlocks X 0 0 Z + t • fromBlocks Y 0 0 Z =
        fromBlocks ((1 - t) • X + t • Y) 0 0 Z := fun X Y Z ↦ by
    rw [fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp [← add_smul]
  have h := hf.cfc_one_sub_smul_add_smul_le_of_card_eq (ι := Fin n ⊕ Fin 1) (by simp)
    (hA.fromBlocks conjTranspose_zero hC) (hB.fromBlocks conjTranspose_zero hC)
    (by rw [spectrum_fromBlocks_zero₂₁]; exact union_subset hAI hCI)
    (by rw [spectrum_fromBlocks_zero₂₁]; exact union_subset hBI hCI) ht
  rw [hcomb, cfc_fromBlocks_zero₁₂_zero₂₁ ((hA.smul (.all (1 - t))).add (hB.smul (.all t))) hC,
    cfc_fromBlocks_zero₁₂_zero₂₁ hA hC, cfc_fromBlocks_zero₁₂_zero₂₁ hB hC, hcomb] at h
  exact (fromBlocks_le_fromBlocks_iff.1 h).1

/-- Matrix convexity of order `n` implies matrix convexity of every order `m ≤ n`. -/
theorem of_le (hf : IsMatrixConvexOn n f I) (hmn : m ≤ n) : IsMatrixConvexOn m f I := by
  induction n, hmn using Nat.le_induction with
  | base => exact hf
  | succ n _ ih => exact ih hf.of_succ

/-- A matrix convex function of order `n` on `I` satisfies the convexity inequality for Hermitian
matrices with spectra in `I` over any index type with at most `n` elements. -/
theorem cfc_one_sub_smul_add_smul_le_of_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMatrixConvexOn n f I) (hι : Fintype.card ι ≤ n) {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B :=
  (hf.of_le hι).cfc_one_sub_smul_add_smul_le_of_card_eq rfl hA hB hAI hBI ht

/-- A matrix convex function of order `n` on `I` satisfies the convexity inequality
`cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B` for Hermitian `n × n` matrices
with spectra in `I` and `t ∈ [0, 1]`. -/
theorem cfc_one_sub_smul_add_smul_le (hf : IsMatrixConvexOn n f I)
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B :=
  hf.cfc_one_sub_smul_add_smul_le_of_card_le (Fintype.card_fin n).le hA hB hAI hBI ht

/-- A matrix convex function of positive order on a convex set `I` is convex on `I`. -/
theorem convexOn (hf : IsMatrixConvexOn n f I) (hn : n ≠ 0) (hI : Convex ℝ I) :
    ConvexOn ℝ I f :=
  (isMatrixConvexOn_one_iff hI).1 (hf.of_le (Nat.one_le_iff_ne_zero.2 hn))

/-- The sum of two matrix convex functions of order `n` on `I` is matrix convex. -/
theorem add (hf : IsMatrixConvexOn n f I) (hg : IsMatrixConvexOn n g I) :
    IsMatrixConvexOn n (f + g) I :=
  fun A B hA hB hAI hBI t ht ↦ by
    have hcfc : ∀ X : Matrix (Fin n) (Fin n) ℂ, cfc (f + g) X = cfc f X + cfc g X := fun X ↦
      cfc_add (a := X) f g (X.finite_real_spectrum.continuousOn _)
        (X.finite_real_spectrum.continuousOn _)
    rw [hcfc, hcfc, hcfc]
    calc cfc f ((1 - t) • A + t • B) + cfc g ((1 - t) • A + t • B)
        ≤ ((1 - t) • cfc f A + t • cfc f B) + ((1 - t) • cfc g A + t • cfc g B) :=
          add_le_add (hf hA hB hAI hBI ht) (hg hA hB hAI hBI ht)
      _ = (1 - t) • (cfc f A + cfc g A) + t • (cfc f B + cfc g B) := by module

/-- A nonnegative multiple of a matrix convex function of order `n` on `I` is matrix convex. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsMatrixConvexOn n f I) :
    IsMatrixConvexOn n (fun x ↦ c • f x) I :=
  fun A B hA hB hAI hBI t ht ↦ by
    have hcfc : ∀ X : Matrix (Fin n) (Fin n) ℂ, cfc (fun x ↦ c • f x) X = c • cfc f X :=
      fun X ↦ cfc_smul c f X (X.finite_real_spectrum.continuousOn _)
    rw [hcfc, hcfc, hcfc, smul_smul, smul_smul, mul_comm (1 - t), mul_comm t, ← smul_smul,
      ← smul_smul, ← smul_add]
    exact smul_le_smul_of_nonneg_left (hf hA hB hAI hBI ht) hc

end IsMatrixConvexOn

/-! ### Operator convex functions -/

namespace IsOperatorConvexOn

/-- An operator convex function is matrix convex of every order. -/
theorem isMatrixConvexOn (hf : IsOperatorConvexOn f I) (n : ℕ) : IsMatrixConvexOn n f I :=
  hf n

/-- An operator convex function on `I` satisfies the convexity inequality
`cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B` for Hermitian matrices with
spectra in `I` and `t ∈ [0, 1]`, over any finite index type. -/
theorem cfc_one_sub_smul_add_smul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsOperatorConvexOn f I) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cfc f ((1 - t) • A + t • B) ≤ (1 - t) • cfc f A + t • cfc f B :=
  (hf _).cfc_one_sub_smul_add_smul_le_of_card_le le_rfl hA hB hAI hBI ht

/-- Operator convexity on `I` implies operator convexity on every subset of `I`. -/
theorem mono (hf : IsOperatorConvexOn f I) (hJI : J ⊆ I) : IsOperatorConvexOn f J :=
  fun n ↦ (hf n).mono hJI

/-- An operator convex function on a convex set `I` is convex on `I`. -/
theorem convexOn (hf : IsOperatorConvexOn f I) (hI : Convex ℝ I) : ConvexOn ℝ I f :=
  (isMatrixConvexOn_one_iff hI).1 (hf 1)

/-- The sum of two operator convex functions on `I` is operator convex. -/
theorem add (hf : IsOperatorConvexOn f I) (hg : IsOperatorConvexOn g I) :
    IsOperatorConvexOn (f + g) I :=
  fun n ↦ (hf n).add (hg n)

/-- A nonnegative multiple of an operator convex function on `I` is operator convex. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsOperatorConvexOn f I) :
    IsOperatorConvexOn (fun x ↦ c • f x) I :=
  fun n ↦ (hf n).smul hc

end IsOperatorConvexOn

/-- Constant functions are operator convex on every set. -/
@[simp]
theorem isOperatorConvexOn_const (c : ℝ) (I : Set ℝ) : IsOperatorConvexOn (fun _ ↦ c) I :=
  fun n ↦ isMatrixConvexOn_const n c I

/-- The identity is operator convex on every set. -/
@[simp]
theorem isOperatorConvexOn_id (I : Set ℝ) : IsOperatorConvexOn id I :=
  fun n ↦ isMatrixConvexOn_id n I

/-! ### Operator concave functions -/

/-- `-f` is operator convex on `I` exactly when `f` is operator concave on `I`. -/
@[simp]
theorem isOperatorConvexOn_neg_iff :
    IsOperatorConvexOn (fun x ↦ -f x) I ↔ IsOperatorConcaveOn f I :=
  Iff.rfl

/-- `-f` is operator concave on `I` exactly when `f` is operator convex on `I`. -/
@[simp]
theorem isOperatorConcaveOn_neg_iff :
    IsOperatorConcaveOn (fun x ↦ -f x) I ↔ IsOperatorConvexOn f I := by
  simp only [isOperatorConcaveOn_iff, neg_neg]

namespace IsOperatorConcaveOn

/-- An operator concave function on `I` satisfies the concavity inequality
`(1 - t) • cfc f A + t • cfc f B ≤ cfc f ((1 - t) • A + t • B)` for Hermitian matrices with
spectra in `I` and `t ∈ [0, 1]`, over any finite index type. -/
theorem le_cfc_one_sub_smul_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsOperatorConcaveOn f I) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • cfc f A + t • cfc f B ≤ cfc f ((1 - t) • A + t • B) := by
  have h := IsOperatorConvexOn.cfc_one_sub_smul_add_smul_le hf hA hB hAI hBI ht
  rwa [cfc_neg, cfc_neg, cfc_neg, smul_neg, smul_neg, ← neg_add, neg_le_neg_iff] at h

/-- Operator concavity on `I` implies operator concavity on every subset of `I`. -/
theorem mono (hf : IsOperatorConcaveOn f I) (hJI : J ⊆ I) : IsOperatorConcaveOn f J :=
  IsOperatorConvexOn.mono hf hJI

/-- An operator concave function on a convex set `I` is concave on `I`. -/
theorem concaveOn (hf : IsOperatorConcaveOn f I) (hI : Convex ℝ I) : ConcaveOn ℝ I f :=
  neg_convexOn_iff.1 (IsOperatorConvexOn.convexOn hf hI)

/-- The sum of two operator concave functions on `I` is operator concave. -/
theorem add (hf : IsOperatorConcaveOn f I) (hg : IsOperatorConcaveOn g I) :
    IsOperatorConcaveOn (f + g) I := by
  have h : (fun x ↦ -(f + g) x) = (fun x ↦ -f x) + fun x ↦ -g x := by
    ext x
    exact neg_add (f x) (g x)
  rw [isOperatorConcaveOn_iff, h]
  exact IsOperatorConvexOn.add hf hg

/-- A nonnegative multiple of an operator concave function on `I` is operator concave. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsOperatorConcaveOn f I) :
    IsOperatorConcaveOn (fun x ↦ c • f x) I := by
  have h : (fun x ↦ -(c • f x)) = fun x ↦ c • -f x := by
    ext x
    simp
  rw [isOperatorConcaveOn_iff, h]
  exact IsOperatorConvexOn.smul hc hf

end IsOperatorConcaveOn

/-- Constant functions are operator concave on every set. -/
@[simp]
theorem isOperatorConcaveOn_const (c : ℝ) (I : Set ℝ) : IsOperatorConcaveOn (fun _ ↦ c) I :=
  isOperatorConvexOn_const (-c) I

/-- The identity is operator concave on every set. -/
@[simp]
theorem isOperatorConcaveOn_id (I : Set ℝ) : IsOperatorConcaveOn id I :=
  fun n A B hA hB _ _ t _ ↦ by
    have hX : ∀ {X : Matrix (Fin n) (Fin n) ℂ}, X.IsHermitian → cfc (fun x : ℝ ↦ -id x) X = -X :=
      fun hX ↦ by rw [cfc_neg, cfc_id ℝ _ hX.isSelfAdjoint]
    rw [hX ((hA.smul (.all (1 - t))).add (hB.smul (.all t))), hX hA, hX hB, smul_neg, smul_neg,
      neg_add]

end TauCeti
