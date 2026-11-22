/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Localization.NormTrace
import TauCeti.Analysis.InnerProductSpace.Gram.Projection
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Basic

/-!
# Hunter's theorem

Let `K` be a number field of degree `n`. The **`T₂` form** of `K` is the positive definite real
quadratic form `T₂(x) = ∑_σ ‖σ x‖ ^ 2`, the sum over the `n` complex embeddings `σ : K →+* ℂ`.
We realise it as the squared norm of the canonical embedding `t2Vector K x = (σ x)_σ`, placed in
the Euclidean space indexed by the complex embeddings; the real inner product of `t2Vector K 1`
with `t2Vector K x` is the trace `Tr x`, and `‖t2Vector K 1‖ ^ 2 = n`.

The Gram determinant of the `T₂` vectors of any `ℤ`-basis of the ring of integers is `|discr K|`
(`TauCeti.NumberField.det_gram_t2Vector`): the Gram matrix is `(conj M) Mᵀ` for the complex
embedding matrix `M`, whose determinant squares to the discriminant.

**Hunter's theorem** (`TauCeti.NumberField.hunter`) bounds the smallest `T₂` of a non-rational
algebraic integer. Let `Γ` be admissible in rank `n - 1`: every positive definite real symmetric
matrix `A` of size `n - 1` has a nonzero integer vector `x` with `xᵀ A x ≤ Γ (det A) ^ (1/(n-1))`.
Then `K` has an algebraic integer `θ ∉ ℚ` with `0 ≤ Tr θ ≤ n / 2` and
`T₂(θ) ≤ (Tr θ) ^ 2 / n + Γ (|discr K| / n) ^ (1/(n-1))`.

The proof works in the lattice `𝓞 K / ℤ`, of rank `n - 1`. The quadratic form
`Q(x) = T₂(x) - (Tr x) ^ 2 / n` is the squared norm of the projection of `t2Vector K x` away from
`t2Vector K 1`, so it vanishes on `ℤ` and descends to `𝓞 K / ℤ`. Complete `1` to a `ℤ`-basis
`(1, c₁, …, c_{n-1})` of `𝓞 K` (possible since `𝓞 K ∩ ℚ = ℤ` makes `𝓞 K / ℤ` torsion-free).
The Gram matrix `A` of `Q` in the `cᵢ` is the Schur complement of the corner `n` in the `T₂` Gram
matrix of the basis, so `n · det A = |discr K|` (`Matrix.det_gram_sumElim_unit`), and `A` is
positive definite. Admissibility gives `x ≠ 0` with `Q(∑ xᵢ cᵢ) ≤ Γ (|discr K| / n) ^ (1/(n-1))`.
Finally `θ ↦ ±θ + k` with `k ∈ ℤ` changes `Tr θ` to `±Tr θ + n k` and leaves `Q` unchanged, which
puts the trace in `[0, n/2]`.

The hypothesis on `Γ` is written out rather than named. In degree one it cannot hold: the empty
matrix is positive definite and has no nonzero integer vector. So the theorem needs no separate
hypothesis `2 ≤ n`.

## Main definitions

* `TauCeti.NumberField.t2Vector`: the canonical embedding `(σ x)_σ` of `x`, as a vector of the
  Euclidean space indexed by the complex embeddings.

## Main results

* `TauCeti.NumberField.norm_t2Vector_sq`: `‖t2Vector K x‖ ^ 2 = ∑_σ ‖σ x‖ ^ 2`.
* `TauCeti.NumberField.inner_t2Vector_one`: `⟪t2Vector K 1, t2Vector K x⟫ = Tr x`.
* `TauCeti.NumberField.ofReal_inner_t2Vector`: `⟪t2Vector K x, t2Vector K y⟫ = ∑_σ conj (σ x) σ y`.
* `TauCeti.NumberField.det_gram_t2Vector`: the `T₂` Gram determinant of a `ℤ`-basis of `𝓞 K` is
  `|discr K|`.
* `TauCeti.NumberField.hunter`: Hunter's theorem.

## References

* J. Martinet, *Méthodes géométriques dans la recherche des petits discriminants*, Séminaire de
  Théorie des Nombres, Paris 1983–84, Progr. Math. 59, Birkhäuser 1985, 147–179; corrected author
  version, Proposition 2.3, Theorem 2.6 and Corollary 2.9, and the trace reduction on p. 9.
* J. Hunter, *The minimum discriminants of quintic fields*, Proc. Glasgow Math. Assoc. 3 (1957),
  57–67, Theorem 1.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, Springer 1993, §6.4.1.
-/

public section

open Module Matrix NumberField
open scoped ComplexConjugate InnerProductSpace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The **`T₂` vector** of `x : K`: the canonical embedding `(σ x)_σ` of `x`, over the complex
embeddings `σ : K →+* ℂ`, viewed in the Euclidean space indexed by those embeddings. Its squared
norm is `T₂(x) = ∑_σ ‖σ x‖ ^ 2`, and the real inner product of two such vectors is the `T₂` form
`Re ∑_σ σ y * conj (σ x)`. -/
noncomputable def t2Vector : K →+ EuclideanSpace ℂ (K →+* ℂ) where
  toFun x := WithLp.toLp 2 (canonicalEmbedding K x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

variable {K}

@[simp]
theorem t2Vector_apply (x : K) (σ : K →+* ℂ) : t2Vector K x σ = σ x :=
  (rfl)

/-- The squared norm of the `T₂` vector of `x` is `T₂(x) = ∑_σ ‖σ x‖ ^ 2`. -/
theorem norm_t2Vector_sq (x : K) : ‖t2Vector K x‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

/-- The real inner product of the `T₂` vectors of `1` and `x` is the trace of `x`. -/
theorem inner_t2Vector_one (x : K) :
    ⟪t2Vector K 1, t2Vector K x⟫_ℝ = Algebra.trace ℚ K x := by
  have h := congr(Complex.re $(trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)))
  rw [Complex.re_sum, ← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ ↦ (φ x).re)
    (fun σ ↦ (σ x).re) fun _ ↦ by simp [RingHom.equivRatAlgHom_apply], eq_ratCast,
    Complex.ratCast_re] at h
  simp [PiLp.inner_apply, h]

/-- The squared norm of the `T₂` vector of `1` is the degree `[K : ℚ]`. -/
theorem norm_t2Vector_one_sq : ‖t2Vector K 1‖ ^ 2 = finrank ℚ K := by
  simp [norm_t2Vector_sq, NumberField.Embeddings.card]

/-- The `T₂` form is the complex sum `∑_σ conj (σ x) * σ y`, which is real because complex
conjugation permutes the embeddings. -/
theorem ofReal_inner_t2Vector (x y : K) :
    (⟪t2Vector K x, t2Vector K y⟫_ℝ : ℂ) = ∑ σ : K →+* ℂ, conj (σ x) * σ y := by
  set S := ∑ σ : K →+* ℂ, conj (σ x) * σ y
  have hS : conj S = S := by
    simp only [S, map_sum, map_mul, Complex.conj_conj]
    exact Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate K).toPerm _ _
      fun σ ↦ by simp
  have hre : ⟪t2Vector K x, t2Vector K y⟫_ℝ = S.re := by
    simp [S, PiLp.inner_apply, Complex.re_sum, mul_comm]
  rw [hre]
  exact Complex.conj_eq_iff_re.mp hS

/-- **The `T₂` Gram determinant.** For every `ℤ`-basis `b` of the ring of integers, the Gram
determinant of the `T₂` vectors of the `b i` is `|discr K|`. -/
theorem det_gram_t2Vector {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    (gram ℝ fun i ↦ t2Vector K (b i)).det = |(discr K : ℝ)| := by
  have hcard : Fintype.card ι = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← RingOfIntegers.rank K, finrank_eq_card_basis b]
  -- Enumerate the complex embeddings by `ι`, and let `M i k = e k (b i)`.
  let e : ι ≃ (K →+* ℂ) := Fintype.equivOfCardEq hcard
  let M : Matrix ι ι ℂ := of fun i k ↦ e k (b i)
  -- The determinant of the embedding matrix squares to the discriminant.
  have hM : M.det ^ 2 = (discr K : ℂ) := by
    have hdiscr : Algebra.discr ℚ (fun i ↦ (b i : K)) = (discr K : ℚ) := by
      rw [← NumberField.discr_eq_discr K b, ← eq_intCast (algebraMap ℤ ℚ),
        ← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K b]
      congr 1
      ext i
      simp [Basis.localizationLocalization_apply]
    have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (fun i ↦ (b i : K))
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    have hMe : Algebra.embeddingsMatrixReindex ℚ ℂ (fun i ↦ (b i : K))
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = M := by
      ext i k
      simp [M, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
        RingHom.equivRatAlgHom_apply]
    rw [hdiscr, eq_ratCast, Rat.cast_intCast, hMe] at h
    exact h.symm
  -- Over `ℂ`, the Gram matrix is `(conj M) Mᵀ`.
  have hG : Complex.ofRealHom.mapMatrix (gram ℝ fun i ↦ t2Vector K (b i)) =
      M.map (starRingEnd ℂ) * Mᵀ := by
    ext i j
    rw [RingHom.mapMatrix_apply, map_apply, gram_apply, Complex.ofRealHom_eq_coe,
      ofReal_inner_t2Vector, Matrix.mul_apply]
    simp only [M, map_apply, transpose_apply, of_apply]
    exact (e.sum_comp fun σ ↦ conj (σ (b i : K)) * σ (b j : K)).symm
  have hdet := congr_arg det hG
  rw [← RingHom.map_det, det_mul, det_transpose,
    show (M.map (starRingEnd ℂ)).det = conj M.det from (RingHom.map_det _ M).symm,
    Complex.ofRealHom_eq_coe, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow, hM,
    Complex.norm_intCast] at hdet
  exact_mod_cast hdet

variable (K) in
/-- The projection `t2Vector K x - (Tr x / n) • t2Vector K 1` of the `T₂` vector of `x` away from
the `T₂` vector of `1`, where `n = [K : ℚ]`. -/
private noncomputable def projT2 : K →+ EuclideanSpace ℂ (K →+* ℂ) :=
  AddMonoidHom.mk' (fun x ↦ t2Vector K x -
      ((Algebra.trace ℚ K x : ℝ) / finrank ℚ K) • t2Vector K 1)
    fun x y ↦ by simp only [map_add, Rat.cast_add, add_div, add_smul]; abel

private theorem projT2_apply (x : K) : projT2 K x =
    t2Vector K x - ((Algebra.trace ℚ K x : ℝ) / finrank ℚ K) • t2Vector K 1 :=
  (rfl)

/-- `T₂(x) = Q(x) + (Tr x) ^ 2 / n`, where `Q(x) = ‖projT2 K x‖ ^ 2`. -/
private theorem sum_norm_sq_eq_norm_projT2_sq_add (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 =
      ‖projT2 K x‖ ^ 2 + (Algebra.trace ℚ K x : ℝ) ^ 2 / finrank ℚ K := by
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  -- The scalar action on the Euclidean space is `WithLp`'s, which `rw` does not identify with
  -- the inner-product-space action reducibly; the term `real_inner_smul_right` unifies them.
  have hinner : ⟪t2Vector K x, ((Algebra.trace ℚ K x : ℝ) / finrank ℚ K) • t2Vector K 1⟫_ℝ =
      (Algebra.trace ℚ K x : ℝ) / finrank ℚ K * Algebra.trace ℚ K x :=
    (real_inner_smul_right (t2Vector K x) (t2Vector K 1) _).trans
      (by rw [real_inner_comm, inner_t2Vector_one])
  rw [projT2_apply, norm_sub_sq_real, norm_smul, mul_pow, norm_t2Vector_one_sq, hinner,
    norm_t2Vector_sq, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- `Q` vanishes on the integers. -/
private theorem projT2_intCast (k : ℤ) : projT2 K (k : K) = 0 := by
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  have hk : (k : K) = algebraMap ℚ K k := (map_intCast _ k).symm
  rw [projT2_apply, ← zsmul_one k, map_zsmul, zsmul_one, hk, Algebra.trace_algebraMap,
    nsmul_eq_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, mul_div_cancel_left₀ _ hn,
    Int.cast_smul_eq_zsmul, sub_self]

/-- The trace reduction: `s t + k n ∈ [0, n / 2]` for a sign `s` and an integer `k`. -/
private theorem exists_sign_mul_add_mul_mem (t : ℤ) {n : ℤ} (hn : 0 < n) :
    ∃ s k : ℤ, (s = 1 ∨ s = -1) ∧ 0 ≤ s * t + k * n ∧ 2 * (s * t + k * n) ≤ n := by
  have h1 := Int.emod_add_mul_ediv t n
  have h2 := Int.emod_nonneg t hn.ne'
  have h3 := Int.emod_lt_of_pos t hn
  by_cases h : 2 * (t % n) ≤ n
  · refine ⟨1, -(t / n), Or.inl rfl, ?_⟩
    have : 1 * t + -(t / n) * n = t % n := by linear_combination -h1
    rw [this]
    exact ⟨h2, h⟩
  · refine ⟨-1, t / n + 1, Or.inr rfl, ?_⟩
    have : -1 * t + (t / n + 1) * n = n - t % n := by linear_combination h1
    rw [this]
    constructor <;> omega

/-- The Gram matrix of `Q` in the basis `e (inr j)` of `𝓞 K / ℤ` has determinant `|discr K| / n`:
it is the Schur complement of the corner `n` in the `T₂` Gram matrix of the basis `e`. -/
private theorem det_gram_projT2 {e : Basis (Unit ⊕ Fin (finrank ℚ K - 1)) ℤ (𝓞 K)}
    (he : e (Sum.inl ()) = 1) :
    (gram ℝ fun j ↦ projT2 K (e (Sum.inr j) : K)).det = |(discr K : ℝ)| / finrank ℚ K := by
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  have hdet := det_gram_t2Vector e
  have hfam : (fun i ↦ t2Vector K (e i : K)) =
      Sum.elim (fun _ : Unit ↦ t2Vector K 1) fun j ↦ t2Vector K (e (Sum.inr j) : K) := by
    funext i
    rcases i with _ | j
    · simp [he]
    · rfl
  rw [hfam, det_gram_sumElim_unit, real_inner_self_eq_norm_sq, norm_t2Vector_one_sq] at hdet
  simp only [inner_t2Vector_one, ← projT2_apply] at hdet
  rw [eq_div_iff hn, mul_comm, hdet]

/-- **The trace reduction.** Replacing `θ₀` by `±θ₀ + k` with `k ∈ ℤ` puts its trace in `[0, n/2]`,
changes neither `Q` nor whether it is rational. -/
private theorem exists_trace_mem_and_norm_projT2_eq (θ₀ : 𝓞 K) :
    ∃ θ : 𝓞 K, 0 ≤ Algebra.trace ℚ K (θ : K) ∧
      Algebra.trace ℚ K (θ : K) ≤ (finrank ℚ K : ℚ) / 2 ∧
      ‖projT2 K (θ : K)‖ = ‖projT2 K (θ₀ : K)‖ ∧
      ((θ : K) ∈ Set.range (algebraMap ℚ K) → (θ₀ : K) ∈ Set.range (algebraMap ℚ K)) := by
  obtain ⟨s, k, hs, h0, h2⟩ := exists_sign_mul_add_mul_mem (Algebra.trace ℤ (𝓞 K) θ₀)
    (n := finrank ℚ K) (by exact_mod_cast finrank_pos)
  have hcoe : ((s • θ₀ + k : 𝓞 K) : K) = s • (θ₀ : K) + algebraMap ℚ K k := by simp
  have htr : Algebra.trace ℚ K ((s • θ₀ + k : 𝓞 K) : K) =
      ((s * Algebra.trace ℤ (𝓞 K) θ₀ + k * finrank ℚ K : ℤ) : ℚ) := by
    rw [hcoe, map_add, map_zsmul, Algebra.trace_algebraMap, ← Algebra.coe_trace_int]
    push_cast
    ring
  refine ⟨s • θ₀ + k, ?_, ?_, ?_, ?_⟩
  · rw [htr]
    exact_mod_cast h0
  · rw [htr, le_div_iff₀ two_pos]
    exact_mod_cast (by linarith : (s * Algebra.trace ℤ (𝓞 K) θ₀ + k * finrank ℚ K) * 2 ≤
      (finrank ℚ K : ℤ))
  · rw [hcoe, map_add, map_zsmul, map_intCast, projT2_intCast, add_zero]
    rcases hs with rfl | rfl <;> simp
  · rintro ⟨q, hq⟩
    refine ⟨s * (q - k), ?_⟩
    rw [map_mul, map_sub, hq, hcoe]
    rcases hs with rfl | rfl <;> simp

variable (K) in
/-- **Hunter's theorem.** Let `Γ` be admissible in rank `n - 1`, where `n = [K : ℚ]`: every
positive definite real symmetric matrix `A` of size `n - 1` has a nonzero integer vector `x` with
`xᵀ A x ≤ Γ (det A) ^ (1/(n-1))`. Then `K` has an algebraic integer `θ ∉ ℚ` with
`0 ≤ Tr θ ≤ n / 2` and `∑_σ ‖σ θ‖ ^ 2 ≤ (Tr θ) ^ 2 / n + Γ (|discr K| / n) ^ (1/(n-1))`.

In degree one the hypothesis on `Γ` fails (the empty matrix is positive definite and has no
nonzero integer vector), so the statement needs no hypothesis `2 ≤ n`. -/
theorem hunter {Γ : ℝ} (hΓ : ∀ A : Matrix (Fin (finrank ℚ K - 1)) (Fin (finrank ℚ K - 1)) ℝ,
      A.PosDef → ∃ x : Fin (finrank ℚ K - 1) → ℤ, x ≠ 0 ∧
        (fun i ↦ (x i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (x i : ℝ)) ≤
          Γ * A.det ^ (1 / ((finrank ℚ K : ℝ) - 1))) :
    ∃ θ : 𝓞 K, (θ : K) ∉ Set.range (algebraMap ℚ K) ∧
      0 ≤ Algebra.trace ℚ K (θ : K) ∧ Algebra.trace ℚ K (θ : K) ≤ (finrank ℚ K : ℚ) / 2 ∧
      ∑ σ : K →+* ℂ, ‖σ θ‖ ^ 2 ≤ (Algebra.trace ℚ K (θ : K) : ℝ) ^ 2 / finrank ℚ K +
        Γ * (|(discr K : ℝ)| / finrank ℚ K) ^ (1 / ((finrank ℚ K : ℝ) - 1)) := by
  -- Complete `1` to a basis `e` of `𝓞 K`; the `e (inr j)` form a basis of `𝓞 K / ℤ`, in which
  -- `Q` has the positive definite Gram matrix `A` of determinant `|discr K| / n`.
  obtain ⟨e, he⟩ := RingOfIntegers.exists_basis_inl_eq_one K
  set A := gram ℝ fun j ↦ projT2 K (e (Sum.inr j) : K)
  have hA : A.det = |(discr K : ℝ)| / finrank ℚ K := det_gram_projT2 he
  have hApos : A.PosDef := by
    rw [(posSemidef_gram ℝ _).posDef_iff_det_ne_zero, hA]
    have := discr_ne_zero K
    have : 0 < finrank ℚ K := finrank_pos
    positivity
  obtain ⟨x, hx0, hxA⟩ := hΓ A hApos
  -- The lattice vector `θ₀ = ∑ x j • e (inr j)` has `Q(θ₀) = xᵀ A x`.
  set θ₀ : 𝓞 K := ∑ j, x j • e (Sum.inr j)
  have hQ : ‖projT2 K (θ₀ : K)‖ ^ 2 =
      (fun i ↦ (x i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (x i : ℝ)) := by
    have h := star_dotProduct_gram_mulVec (𝕜 := ℝ) (fun j ↦ projT2 K (e (Sum.inr j) : K))
      (fun i ↦ (x i : ℝ)) (fun i ↦ (x i : ℝ))
    rw [star_trivial, real_inner_self_eq_norm_sq] at h
    rw [h]
    simp only [θ₀, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  -- Reduce the trace into `[0, n / 2]`.
  obtain ⟨θ, h0, h2, hnorm, hrat⟩ := exists_trace_mem_and_norm_projT2_eq θ₀
  refine ⟨θ, fun hθ ↦ ?_, h0, h2, ?_⟩
  · -- `θ₀` is not an integer, since its coordinates `x` in the basis `e` do not vanish.
    obtain ⟨m, hm⟩ := RingOfIntegers.exists_intCast_eq_of_coe_mem_range (hrat hθ)
    refine hx0 (funext fun j ↦ ?_)
    have h1 : e.repr θ₀ (Sum.inr j) = x j := by
      simp only [θ₀, map_sum, map_zsmul, Basis.repr_self]
      simp [Finsupp.single_apply]
    rw [← hm, ← zsmul_one, ← he, map_zsmul, Basis.repr_self] at h1
    simpa using h1.symm
  · rw [sum_norm_sq_eq_norm_projT2_sq_add, hnorm, hQ, ← hA]
    linarith

end TauCeti.NumberField
