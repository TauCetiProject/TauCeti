/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The von Neumann trace inequality and the Hoffman–Wielandt inequality

Let `T` and `S` be symmetric endomorphisms of an `n`-dimensional inner product space over `ℝ` or
`ℂ`, with eigenvalues `λ₀ ≥ ⋯ ≥ λₙ₋₁` and `μ₀ ≥ ⋯ ≥ μₙ₋₁` listed in decreasing order.

The diagonal `dₖ = Re⟪S eₖ, eₖ⟫` of `S` in an orthonormal basis `(eₖ)` is the image of the
spectrum `μ` under the doubly stochastic Schur weight matrix of `(eₖ)` and an eigenbasis of `S`.
Doubly stochastic averaging cannot increase a sorted pairing, so for every decreasing weight
sequence `c`,

`∑ₖ cₖ dₖ ≤ ∑ₖ cₖ μₖ`

(`LinearMap.IsSymmetric.sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues`, in the Schur–Horn
file).

Taking `(eₖ)` to be an eigenbasis of `T` and `c = λ` gives the **von Neumann trace inequality**
`Re tr (T S) ≤ ∑ᵢ λᵢ μᵢ`.

Expanding `∑ₖ ‖(T - S) eₖ‖² = ∑ᵢ λᵢ² - 2 Re tr (T S) + ∑ᵢ μᵢ²` then gives the
**Hoffman–Wielandt inequality**: the squared Euclidean distance between the sorted spectra is at
most the squared Frobenius distance between the operators,

`∑ᵢ (λᵢ - μᵢ)² ≤ ∑ₖ ‖T eₖ - S eₖ‖²`,

for every orthonormal basis `(eₖ)`.

## Main results

* `LinearMap.IsSymmetric.sum_eigenvalues_mul_re_inner_apply_self_le`: for `e` an eigenbasis of
  `T`, `∑ₖ λₖ Re⟪S eₖ, eₖ⟫ ≤ ∑ₖ λₖ μₖ`.
* `LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul_eigenvalues`: the von Neumann trace
  inequality `Re tr (T S) ≤ ∑ᵢ λᵢ μᵢ`.
* `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply`: the Hoffman–Wielandt
  inequality `∑ᵢ (λᵢ - μᵢ)² ≤ ∑ₖ ‖T eₖ - S eₖ‖²`.

## References

* J. von Neumann, *Some matrix-inequalities and metrization of matric-space*, Tomsk Univ. Rev. **1**
  (1937), 286–300.
* A. J. Hoffman, H. W. Wielandt, *The variation of the spectrum of a normal matrix*, Duke Math. J.
  **20** (1953), 37–39.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VI.4.
-/

public section

open Module (finrank)
open scoped InnerProductSpace Matrix

namespace LinearMap.IsSymmetric

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι] {T S : E →ₗ[𝕜] E} {n : ℕ}

/-- **The von Neumann trace core.** For symmetric `T` and `S`, pairing the eigenvalues of `T`
with the diagonal of `S` in an eigenbasis of `T` gives at most the sorted pairing
`∑ᵢ λᵢ(T) λᵢ(S)` of the two spectra. -/
theorem sum_eigenvalues_mul_re_inner_apply_self_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) :
    ∑ k, hT.eigenvalues hn k *
        RCLike.re ⟪S (hT.eigenvectorBasis hn k), hT.eigenvectorBasis hn k⟫_𝕜 ≤
      ∑ i, hT.eigenvalues hn i * hS.eigenvalues hn i :=
  hS.sum_mul_re_inner_apply_self_le_sum_mul_eigenvalues hn _ (hT.eigenvalues_antitone hn)

/-- **The von Neumann trace inequality.** For symmetric `T` and `S` with eigenvalues listed in
decreasing order, `Re tr (T S) ≤ ∑ᵢ λᵢ(T) λᵢ(S)`. -/
theorem re_trace_comp_le_sum_eigenvalues_mul_eigenvalues (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) :
    RCLike.re (trace 𝕜 E (T ∘ₗ S)) ≤ ∑ i, hT.eigenvalues hn i * hS.eigenvalues hn i := by
  refine le_of_eq_of_le ?_ (hT.sum_eigenvalues_mul_re_inner_apply_self_le hS hn)
  -- Compute the trace in an eigenbasis `(vₖ)` of `T`: `⟪vₖ, T (S vₖ)⟫ = λₖ ⟪vₖ, S vₖ⟫`.
  rw [trace_eq_sum_inner _ (hT.eigenvectorBasis hn), map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [comp_apply, ← hT, inner_re_symm (𝕜 := 𝕜) (S _)]
  simp [hT.apply_eigenvectorBasis, inner_smul_left]

/-- **The Hoffman–Wielandt inequality.** For symmetric `T` and `S` with eigenvalues listed in
decreasing order and every orthonormal basis `e`, the squared Euclidean distance between the two
spectra is at most the squared Frobenius distance `∑ₖ ‖T eₖ - S eₖ‖²` between the operators. -/
theorem sum_sq_eigenvalues_sub_le_sum_sq_norm_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis ι 𝕜 E) :
    ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2 ≤ ∑ k, ‖T (e k) - S (e k)‖ ^ 2 := by
  have hvN := hT.sum_eigenvalues_mul_re_inner_apply_self_le hS hn
  set v := hT.eigenvectorBasis hn
  set w := hS.eigenvectorBasis hn
  set l := hT.eigenvalues hn
  set m := hS.eigenvalues hn
  -- The Frobenius sums of `T - S` and of `S` may be computed in the eigenbases `v` and `w`.
  have hTS : ∑ k, ‖T (e k) - S (e k)‖ ^ 2 = ∑ k, ‖T (v k) - S (v k)‖ ^ 2 := by
    simpa using (T - S).sum_norm_apply_sq_eq_sum_norm_apply_sq e v
  have hS2 : ∑ k, ‖S (v k)‖ ^ 2 = ∑ k, m k ^ 2 := by
    rw [S.sum_norm_apply_sq_eq_sum_norm_apply_sq v w]
    simp [w, m, hS.apply_eigenvectorBasis, norm_smul]
  -- Expand `‖λₖ vₖ - S vₖ‖²`.
  have hexp (k : Fin n) :
      ‖T (v k) - S (v k)‖ ^ 2 = l k ^ 2 - 2 * (l k * RCLike.re ⟪S (v k), v k⟫_𝕜) +
        ‖S (v k)‖ ^ 2 := by
    rw [hT.apply_eigenvectorBasis, norm_sub_sq (𝕜 := 𝕜), inner_re_symm (𝕜 := 𝕜) _ (S _)]
    simp [v, l, norm_smul, inner_smul_right]
  rw [hTS, Finset.sum_congr rfl fun k _ ↦ hexp k]
  simp only [sub_sq, mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  linarith

end LinearMap.IsSymmetric
