/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Concavity of spectral functions

Let `Γ ⊆ ℝⁿ` be invariant under permutations of the coordinates and let `f : ℝⁿ → ℝ` be
symmetric on `Γ`. The *spectral function* of `f` sends a symmetric operator `T` on an
`n`-dimensional inner product space over `𝕜 ∈ {ℝ, ℂ}` to `f(λ(T))`, where `λ(T)` is the
decreasingly sorted eigenvalue vector of `T`; its *spectral domain* is the set of `T` with
`λ(T) ∈ Γ`. If `Γ` is convex and `f` is concave on `Γ`, then the spectral domain is convex and the
spectral function is concave on it. Neither openness of `Γ` nor any differentiability of `f` is
needed, and `Γ` need not be a cone.

The proof is by majorization. For `a, b ≥ 0`, the convexity of the Ky Fan sums
(`LinearMap.IsSymmetric.prefixSum_eigenvalues_smul_add_smul_le`) says that the prefix sums of
`d = λ(a • S + b • T)` are at most those of `y = a • λ(S) + b • λ(T)`, and the total sums agree
because both are the trace of `a • S + b • T`. A convex set invariant under swapping two
coordinates is closed under Robin Hood transfers (`Convex.robinHood_mem`), and a set closed under
these transfers that contains `y` contains every antitone `d` majorized by `y`
(`TauCeti.mem_of_prefixSum_le_of_sum_eq`). Applied to `Γ` this gives the convexity of the spectral
domain, and applied to the superlevel set `{μ ∈ Γ | c ≤ f μ}` at `c = a f(λ(S)) + b f(λ(T))` it
gives the concavity of the spectral function.

The operator statements are pointwise, for a convex combination `a • S + b • T`. For Hermitian
matrices, which form a real vector space, they are assembled into `ConcaveOn` on the real
submodule `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)`, with Mathlib's sorted eigenvalue vector
`Matrix.IsHermitian.eigenvalues₀`.

## Main results

* `LinearMap.IsSymmetric.eigenvalues_smul_add_smul_mem`: a convex permutation-invariant set
  containing `a • λ(S) + b • λ(T)`, for `a, b ≥ 0`, contains `λ(a • S + b • T)`.
* `LinearMap.IsSymmetric.le_apply_eigenvalues_smul_add_smul`: the concavity inequality
  `a f(λ(S)) + b f(λ(T)) ≤ f(λ(a • S + b • T))` for symmetric operators.
* `Matrix.concaveOn_spectralFunction`: the spectral function `A ↦ f(λ(A))` is concave on the
  Hermitian matrices with eigenvalue vector in `Γ`.
* `Matrix.convex_setOf_eigenvalues₀_mem`: the Hermitian matrices with eigenvalue vector in a
  convex permutation-invariant `Γ` form a convex set.

## References

* A. S. Lewis, *Convex analysis on the Hermitian matrices*, SIAM J. Optim. **6** (1996),
  164–177.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in *Global
  theory of minimal surfaces*, Clay Math. Proc. **2** (2005), 283–309, Theorem 1.4.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §II.1
  and §IV.2.
-/

public section

open Module Finset TauCeti

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E} {n : ℕ}

/-- **The eigenvalues of a positive combination are majorized by the combination of the
eigenvalues.** Let `K ⊆ ℝⁿ` be convex and invariant under permutations of the coordinates. If
`a, b ≥ 0` and `K` contains `a • λ(S) + b • λ(T)`, then `K` contains `λ(a • S + b • T)`. For
`a + b = 1` and `K` containing `λ(S)` and `λ(T)`, this is the convexity of the set of symmetric
operators with eigenvalue vector in `K`. -/
theorem eigenvalues_smul_add_smul_mem (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) (hKσ : ∀ σ : Equiv.Perm (Fin n), ∀ μ ∈ K, μ ∘ σ ∈ K)
    (hmem : a • hS.eigenvalues hn + b • hT.eigenvalues hn ∈ K) :
    ((hS.smul (RCLike.conj_ofReal a)).add (hT.smul (RCLike.conj_ofReal b))).eigenvalues hn ∈ K :=
  mem_of_prefixSum_le_of_sum_eq
    (fun _ hx _ _ _ hδ hδ' ↦ hK.robinHood_mem hx (hKσ _ _ hx) hδ hδ') hmem
    (eigenvalues_antitone _ hn)
    (fun k ↦ by
      simpa only [prefixSum_add, prefixSum_smul, smul_eq_mul] using
        hS.prefixSum_eigenvalues_smul_add_smul_le hT hn ha hb k)
    -- Both sums are the real part of the trace of `a • S + b • T`.
    (by
      rw [← re_trace_eq_sum_eigenvalues hn]
      simp only [map_add, map_smul, smul_eq_mul, RCLike.re_ofReal_mul, Pi.add_apply,
        Pi.smul_apply, sum_add_distrib, ← mul_sum, hS.re_trace_eq_sum_eigenvalues hn,
        hT.re_trace_eq_sum_eigenvalues hn])

/-- **Concavity of spectral functions**, operator form. Let `Γ ⊆ ℝⁿ` be invariant under
permutations of the coordinates and let `f` be concave on `Γ` (so `Γ` is convex) and symmetric
on `Γ`. If the eigenvalue vectors of the symmetric operators `S` and `T` lie in `Γ`, and
`a, b ≥ 0` with `a + b = 1`, then `a f(λ(S)) + b f(λ(T)) ≤ f(λ(a • S + b • T))`. The eigenvalue
vector of `a • S + b • T` lies in `Γ` by `LinearMap.IsSymmetric.eigenvalues_smul_add_smul_mem`. -/
theorem le_apply_eigenvalues_smul_add_smul (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {Γ : Set (Fin n → ℝ)}
    (hΓσ : ∀ σ : Equiv.Perm (Fin n), ∀ μ ∈ Γ, μ ∘ σ ∈ Γ) {f : (Fin n → ℝ) → ℝ}
    (hfσ : ∀ σ : Equiv.Perm (Fin n), ∀ μ ∈ Γ, f (μ ∘ σ) = f μ) (hf : ConcaveOn ℝ Γ f)
    (hSΓ : hS.eigenvalues hn ∈ Γ) (hTΓ : hT.eigenvalues hn ∈ Γ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * f (hS.eigenvalues hn) + b * f (hT.eigenvalues hn) ≤
      f (((hS.smul (RCLike.conj_ofReal a)).add (hT.smul (RCLike.conj_ofReal b))).eigenvalues hn) :=
  -- Apply the majorization to the superlevel set of `f` through the convex combination.
  (hS.eigenvalues_smul_add_smul_mem hT hn ha hb (hf.convex_ge _)
    (fun σ μ hμ ↦ ⟨hΓσ σ μ hμ.1, (hfσ σ μ hμ.1).symm ▸ hμ.2⟩)
    ⟨hf.1 hSΓ hTΓ ha hb hab,
      by simpa only [smul_eq_mul] using hf.2 hSΓ hTΓ ha hb hab⟩).2

end LinearMap.IsSymmetric

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- **Concavity of spectral functions** (Lewis 1996; Spruck 2005, Theorem 1.4). Let
`Γ ⊆ ℝⁿ`, for `n` the size of the matrices, be invariant under permutations of the coordinates,
and let `f` be concave on `Γ` and symmetric on `Γ`. Then the spectral function `A ↦ f(λ(A))`,
for `λ(A)` the decreasingly sorted eigenvalue vector, is concave on the real vector space of
Hermitian matrices `A` with `λ(A) ∈ Γ`. In particular this set of matrices is convex. -/
theorem concaveOn_spectralFunction {Γ : Set (Fin (Fintype.card ι) → ℝ)}
    (hΓσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ ∈ Γ, μ ∘ σ ∈ Γ)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hfσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ ∈ Γ, f (μ ∘ σ) = f μ)
    (hf : ConcaveOn ℝ Γ f) :
    ConcaveOn ℝ
      {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | A.property.isHermitian.eigenvalues₀ ∈ Γ}
      fun A ↦ f A.property.isHermitian.eigenvalues₀ := by
  -- The sorted eigenvalues of a combination of Hermitian matrices are those of the same
  -- combination of their Euclidean operators.
  have key (A B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) (a b : ℝ) :
      (a • A + b • B).property.isHermitian.eigenvalues₀ =
        (((isSymmetric_toEuclideanLin_iff.mpr A.property.isHermitian).smul
          (RCLike.conj_ofReal a)).add
          ((isSymmetric_toEuclideanLin_iff.mpr B.property.isHermitian).smul
            (RCLike.conj_ofReal b))).eigenvalues finrank_euclideanSpace := by
    rw [IsHermitian.eigenvalues₀]
    refine LinearMap.IsSymmetric.eigenvalues_congr ?_ _ _ _
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜) a, RCLike.real_smul_eq_coe_smul (K := 𝕜) b, map_add,
      map_smul, map_smul]
  refine ⟨fun A hA B hB a b ha hb hab ↦ ?_, fun A hA B hB a b ha hb hab ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, key]
    exact LinearMap.IsSymmetric.eigenvalues_smul_add_smul_mem _ _ _ ha hb hf.1 hΓσ
      (hf.1 hA hB ha hb hab)
  · simp only [smul_eq_mul, key]
    exact LinearMap.IsSymmetric.le_apply_eigenvalues_smul_add_smul _ _ _ hΓσ hfσ hf hA hB ha hb
      hab

/-- **Convexity of spectral domains.** For a convex set `Γ ⊆ ℝⁿ`, for `n` the size of the
matrices, invariant under permutations of the coordinates, the Hermitian matrices whose
decreasingly sorted eigenvalue vector lies in `Γ` form a convex subset of the real vector space
of Hermitian matrices. -/
theorem convex_setOf_eigenvalues₀_mem {Γ : Set (Fin (Fintype.card ι) → ℝ)} (hΓ : Convex ℝ Γ)
    (hΓσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ ∈ Γ, μ ∘ σ ∈ Γ) :
    Convex ℝ
      {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | A.property.isHermitian.eigenvalues₀ ∈ Γ} :=
  (concaveOn_spectralFunction hΓσ (fun _ _ _ ↦ rfl) (concaveOn_const 0 hΓ)).1

end Matrix
