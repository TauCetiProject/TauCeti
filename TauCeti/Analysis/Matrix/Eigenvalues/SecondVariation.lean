/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Smooth
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Calculus.Deriv.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Second variation of simple eigenvalues

Let `M : ℝ → Matrix n n 𝕜` be a curve of Hermitian matrices over `RCLike 𝕜`, twice differentiable
at `t₀`, and let `λᵢ (t) = (M t).eigenvalues₀ i` be simple at `t₀`, with unit eigenvector `u`.
Write `U` for the eigenvector unitary of `M t₀`, whose columns `uₖ` are eigenvectors for the
eigenvalues `λₖ`. **Hadamard's second variation formula** (`Matrix.hasDerivAt_deriv_eigenvalues₀`)
computes the second derivative

`λᵢ'' (t₀) = Re ⟪u, M'' (t₀) u⟫ + 2 ∑_{λₖ ≠ λᵢ} |⟪uₖ, M' (t₀) u⟫|² / (λᵢ - λₖ)`,

where `⟪uₖ, M' (t₀) u⟫` is the `k`-th coordinate of `M' (t₀) u` in the eigenbasis. Along a straight
line `A + t • B` of Hermitian matrices only the second term remains
(`Matrix.IsHermitian.hasDerivAt_deriv_eigenvalues₀_add_smul`): it is the Hessian of the simple
eigenvalue in the direction `B`. Each eigenvalue below `λᵢ` pushes it up and each eigenvalue above
pushes it down, with strength inversely proportional to the gap. This is the repulsion that, fed
into Itô's formula for the eigenvalues of a Hermitian matrix-valued Brownian motion, produces the
drift `∑_{j ≠ i} (λᵢ - λⱼ)⁻¹` of Dyson's eigenvalue equation.

## Implementation notes

A simple eigenvalue has a differentiable curve of eigenvectors through `u`, namely a scalar
multiple of `adjugate (λᵢ (t) - M t) *ᵥ u`: the adjugate of a singular matrix maps into its
kernel, and at `t₀` it acts on `u` by the nonzero product `∏_{k ≠ i} (λᵢ - λₖ)`. Along this curve
`w`, the first variation formula of `TauCeti.Analysis.Matrix.Eigenvalues.Smooth` writes `λᵢ'` as
the Rayleigh quotient `Re ⟪w, M' w⟫ / ⟪w, w⟫` near `t₀`, which is differentiated by the product
rule. Differentiating `M w = λᵢ w` at `t₀` gives `(λᵢ - M) w' = M' u - λᵢ' u`, which determines
the coordinates of `w'` in the eigenbasis off the eigenvalue `λᵢ`; the coordinate along `u` drops
out.

## References

* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §1.3.5
  (Hadamard's first and second variation formulas).
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), proof of Theorem 4.3.2 (derivatives of eigenvalues along matrix
  Brownian motion).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter II, §2.
-/

public section

noncomputable section

open Filter Topology

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-! ### Linear algebra at a simple eigenvalue -/

/-- At a simple eigenvalue `μ = A.eigenvalues₀ i` of a Hermitian matrix `A`, the adjugate of
`μ - A` multiplies an eigenvector for `μ` by the product of the gaps `μ - λₖ` to the eigenvalues
at the other indices. -/
private theorem adjugate_scalar_sub_mulVec_of_simple {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {i : Fin (Fintype.card n)} (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i)
    {u : n → 𝕜} (hu : A *ᵥ u = (hA.eigenvalues₀ i : 𝕜) • u) :
    adjugate (scalar n (hA.eigenvalues₀ i : 𝕜) - A) *ᵥ u =
      (∏ k ∈ Finset.univ.erase (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) i),
        ((hA.eigenvalues₀ i - hA.eigenvalues k : ℝ) : 𝕜)) • u := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set d := hA.eigenvalues
  set μ := hA.eigenvalues₀ i
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  -- In the eigenbasis, `μ - A` is the diagonal matrix of the gaps `μ - λₖ`.
  have hN : scalar n (μ : 𝕜) - A = U * diagonal (fun k ↦ ((μ - d k : ℝ) : 𝕜)) * star U := by
    have hD : diagonal (fun k ↦ ((μ - d k : ℝ) : 𝕜)) =
        (μ : 𝕜) • 1 - diagonal (RCLike.ofReal ∘ d) := by
      rw [smul_one_eq_diagonal, diagonal_sub]
      simp
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU',
      scalar_apply, ← smul_one_eq_diagonal]
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  -- Conjugation by a unitary commutes with the adjugate.
  have hadj : adjugate (scalar n (μ : 𝕜) - A) =
      U * adjugate (diagonal fun k ↦ ((μ - d k : ℝ) : 𝕜)) * star U := by
    rw [hN, adjugate_mul_distrib, adjugate_mul_distrib, adjugate_eq_det_smul_of_mul_eq_one hU,
      adjugate_eq_det_smul_of_mul_eq_one hU']
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← det_mul, hU', det_one, one_smul]
  -- The eigen-coordinates of `u` vanish off the simple index `e i`.
  have hc : ∀ k ≠ e i, (star U *ᵥ u) k = 0 := fun k hk ↦
    hA.star_eigenvectorUnitary_mulVec_apply_eq_zero hu <| by
      simpa [μ, d] using hA.eigenvalues_ne_eigenvalues_equivOfCardEq hi k hk
  have hdiag : adjugate (diagonal fun k ↦ ((μ - d k : ℝ) : 𝕜)) *ᵥ (star U *ᵥ u) =
      (∏ k ∈ Finset.univ.erase (e i), ((μ - d k : ℝ) : 𝕜)) • (star U *ᵥ u) := by
    ext k
    rw [adjugate_diagonal, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    obtain rfl | hk := eq_or_ne k (e i)
    · rfl
    · rw [hc k hk, mul_zero, mul_zero]
  rw [hadj, ← mulVec_mulVec, ← mulVec_mulVec, hdiag, mulVec_smul, mulVec_mulVec, hU', one_mulVec]

/-- Let `u` be an eigenvector of a Hermitian matrix `A` for the eigenvalue `μ`, and let `w'` solve
`(μ - A) w' = B u - b u`. Then `Re ⟪w', B u - b u⟫` is the sum of `|(Uᴴ B u)ₖ|² / (μ - λₖ)` over
the eigenvalues `λₖ ≠ μ`, where `U` is the eigenvector unitary of `A`. -/
private theorem re_star_dotProduct_sub_smul_eq_sum {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    {μ b : ℝ} {u w' : n → 𝕜} (hu : A *ᵥ u = (μ : 𝕜) • u)
    (hw' : B *ᵥ u - (b : 𝕜) • u = (μ : 𝕜) • w' - A *ᵥ w') :
    RCLike.re (star w' ⬝ᵥ (B *ᵥ u - (b : 𝕜) • u)) =
      ∑ k with hA.eigenvalues k ≠ μ,
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (B *ᵥ u)) k‖ ^ 2 /
          (μ - hA.eigenvalues k) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set d := hA.eigenvalues
  set v := B *ᵥ u - (b : 𝕜) • u
  set y := star U *ᵥ w'
  set z := star U *ᵥ (B *ᵥ u)
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have hUA : star U * A = diagonal (RCLike.ofReal ∘ d) * star U := by
    rw [← hA.star_eigenvectorUnitary_mul_mul_eigenvectorUnitary, Matrix.mul_assoc _ U, hU',
      Matrix.mul_one]
  -- The eigen-coordinates of `v`, read off from the equation for `w'` and from that of `u`.
  have hv₁ (k : n) : (star U *ᵥ v) k = ((μ - d k : ℝ) : 𝕜) * y k := by
    rw [hw', mulVec_sub, mulVec_smul, mulVec_mulVec, hUA, ← mulVec_mulVec, Pi.sub_apply,
      Pi.smul_apply, mulVec_diagonal, smul_eq_mul, Function.comp_apply]
    push_cast
    ring
  have hv₂ (k : n) (hk : d k ≠ μ) : (star U *ᵥ v) k = z k := by
    rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply,
      hA.star_eigenvectorUnitary_mulVec_apply_eq_zero hu hk, smul_zero, sub_zero]
  -- The unitary `U` preserves the inner product.
  have hinner : star w' ⬝ᵥ v = star y ⬝ᵥ (star U *ᵥ v) := by
    rw [star_mulVec, ← dotProduct_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose,
      mulVec_mulVec, ← star_eq_conjTranspose, hU', one_mulVec]
  rw [hinner, Finset.sum_filter, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs with hk
  · have hgap : ((μ - d k : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm hk)
    have hyk : y k = z k / ((μ - d k : ℝ) : 𝕜) := by
      rw [eq_div_iff hgap, mul_comm, ← hv₁, hv₂ k hk]
    rw [hv₂ k hk, Pi.star_apply, hyk, star_div₀, RCLike.star_def, RCLike.conj_ofReal,
      div_mul_eq_mul_div, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_div,
      RCLike.ofReal_re]
  · rw [hv₁, not_not.1 hk, sub_self, RCLike.ofReal_zero, zero_mul, mul_zero, map_zero]

/-! ### Curves of eigenvectors -/

variable {M : ℝ → Matrix n n 𝕜}

open scoped ComplexOrder in
/-- The first variation formula with an eigenvector that need not be normalized: at a simple
eigenvalue, the derivative of `t ↦ λᵢ (M t)` is the Rayleigh quotient
`Re ⟪w, M' w⟫ / ⟪w, w⟫` of the derivative of the family at any nonzero eigenvector `w`. -/
private theorem deriv_eigenvalues₀_eq_div (hM : ∀ t, (M t).IsHermitian) {t : ℝ}
    (hMd : ∀ a b, DifferentiableAt ℝ (fun s ↦ M s a b) t) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM t).eigenvalues₀ j ≠ (hM t).eigenvalues₀ i) {w : n → 𝕜}
    (hw : M t *ᵥ w = ((hM t).eigenvalues₀ i : 𝕜) • w) (hw0 : w ≠ 0) :
    deriv (fun s ↦ (hM s).eigenvalues₀ i) t =
      RCLike.re (star w ⬝ᵥ (of (fun a b ↦ deriv (fun s ↦ M s a b) t) *ᵥ w)) /
        RCLike.re (star w ⬝ᵥ w) := by
  obtain ⟨r, hr, hrw⟩ := RCLike.pos_iff_exists_ofReal.1 (dotProduct_star_self_pos_iff.2 hw0)
  set c : 𝕜 := (((Real.sqrt r)⁻¹ : ℝ) : 𝕜)
  have hcc : star c * c = ((r⁻¹ : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt hr.le]
  have hu : M t *ᵥ (c • w) = ((hM t).eigenvalues₀ i : 𝕜) • (c • w) := by
    rw [mulVec_smul, hw, smul_comm]
  have hu1 : star (c • w) ⬝ᵥ (c • w) = 1 := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, hcc, ← hrw,
      ← RCLike.ofReal_mul, inv_mul_cancel₀ hr.ne', RCLike.ofReal_one]
  rw [← fderiv_apply_one_eq_deriv, fderiv_eigenvalues₀_apply hM hMd hi hu hu1, ← hrw,
    RCLike.ofReal_re]
  simp only [fderiv_apply_one_eq_deriv, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [← mul_assoc, mul_comm c, hcc, RCLike.re_ofReal_mul, inv_mul_eq_div]

/-- Through a unit eigenvector `u` of a simple eigenvalue `λᵢ (t₀)` passes a curve `w` of
eigenvectors, `M t *ᵥ w t = λᵢ (t) • w t` for every `t`, which is differentiable at `t₀` when the
entries of `M` are. It is a fixed multiple of `adjugate (λᵢ (t) - M t) *ᵥ u`. -/
private theorem exists_eigenvector_curve (hM : ∀ t, (M t).IsHermitian) {t₀ : ℝ}
    (hMd : ∀ a b, DifferentiableAt ℝ (fun s ↦ M s a b) t₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM t₀).eigenvalues₀ j ≠ (hM t₀).eigenvalues₀ i) {u : n → 𝕜}
    (hu : M t₀ *ᵥ u = ((hM t₀).eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    ∃ w : ℝ → n → 𝕜, w t₀ = u ∧ DifferentiableAt ℝ w t₀ ∧
      ∀ t, M t *ᵥ w t = ((hM t).eigenvalues₀ i : 𝕜) • w t := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  set p : 𝕜 := ∏ k ∈ Finset.univ.erase (e i),
    (((hM t₀).eigenvalues₀ i - (hM t₀).eigenvalues k : ℝ) : 𝕜)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦ by
    have h := (hM t₀).eigenvalues_ne_eigenvalues_equivOfCardEq hi k (Finset.ne_of_mem_erase hk)
    rw [(hM t₀).eigenvalues_apply_equivOfCardEq] at h
    exact_mod_cast sub_ne_zero.2 (Ne.symm h)
  refine ⟨fun t ↦ p⁻¹ • (adjugate (scalar n ((hM t).eigenvalues₀ i : 𝕜) - M t) *ᵥ u), ?_, ?_,
    fun t ↦ ?_⟩
  · dsimp only
    rw [adjugate_scalar_sub_mulVec_of_simple (hM t₀) hi hu, smul_smul, inv_mul_cancel₀ hp,
      one_smul]
  · have hlam : DifferentiableAt ℝ (fun t ↦ (hM t).eigenvalues₀ i) t₀ :=
      (hasFDerivAt_eigenvalues₀ hM hMd hi hu hu1).differentiableAt
    -- Each entry of the adjugate is the determinant of a matrix with differentiable entries.
    have hadj (a b : n) : DifferentiableAt ℝ
        (fun t ↦ adjugate (scalar n ((hM t).eigenvalues₀ i : 𝕜) - M t) a b) t₀ := by
      have hK (k l : n) : DifferentiableAt ℝ (fun t ↦ ((scalar n ((hM t).eigenvalues₀ i : 𝕜) -
          M t).updateRow b (Pi.single a 1)) k l) t₀ := by
        simp only [updateRow_apply, Matrix.sub_apply, scalar_apply, diagonal_apply]
        split_ifs
        · exact differentiableAt_const _
        · exact (RCLike.ofRealCLM.differentiableAt.comp t₀ hlam).sub (hMd k l)
        · exact (differentiableAt_const _).sub (hMd k l)
      simpa only [adjugate_apply] using
        (hasDerivAt_det_of_entries_adjugate fun k l ↦ (hK k l).hasDerivAt).differentiableAt
    refine (differentiableAt_pi.2 fun a ↦ ?_).const_smul p⁻¹
    simp only [mulVec, dotProduct]
    exact DifferentiableAt.fun_sum fun b _ ↦ (hadj a b).mul_const (u b)
  · -- `λᵢ (t)` is a root of the characteristic polynomial, so `λᵢ (t) - M t` is singular and its
    -- adjugate maps into its kernel.
    set μ := (hM t).eigenvalues₀ i
    set v := adjugate (scalar n (μ : 𝕜) - M t) *ᵥ u
    have hdet : (scalar n (μ : 𝕜) - M t).det = 0 := by
      rw [← eval_charpoly, (hM t).charpoly_eq, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (e i)) (by simp [μ, e])
    have h0 : (scalar n (μ : 𝕜) - M t) *ᵥ v = 0 := by
      rw [mulVec_mulVec, mul_adjugate, hdet, zero_smul, zero_mulVec]
    rw [sub_mulVec, sub_eq_zero, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec,
      one_mulVec] at h0
    dsimp only
    rw [mulVec_smul, ← h0, smul_comm]

omit [DecidableEq n] in
/-- Differentiating the eigenvalue equation `M t *ᵥ w t = λ t • w t` at `t₀`, where `w t₀ = u`,
gives `M' (t₀) u - λ' (t₀) u = λ (t₀) w' - M t₀ w'`. -/
private theorem mulVec_sub_smul_eq_of_hasDerivAt {t₀ : ℝ}
    (hMd : ∀ a b, DifferentiableAt ℝ (fun s ↦ M s a b) t₀) {lam : ℝ → ℝ} {lam' : ℝ}
    (hlam : HasDerivAt lam lam' t₀) {w : ℝ → n → 𝕜} {w' u : n → 𝕜} (hw : HasDerivAt w w' t₀)
    (hw₀ : w t₀ = u) (hweig : ∀ t, M t *ᵥ w t = (lam t : 𝕜) • w t) :
    (of fun a b ↦ deriv (fun s ↦ M s a b) t₀) *ᵥ u - (lam' : 𝕜) • u =
      (lam t₀ : 𝕜) • w' - M t₀ *ᵥ w' := by
  have h := (hasDerivAt_mulVec_of_entries (fun a b ↦ (hMd a b).hasDerivAt) hw).sub
    (hlam.smul hw)
  -- The differentiated function vanishes identically.
  have h' : (of fun a b ↦ deriv (fun s ↦ M s a b) t₀) *ᵥ w t₀ + M t₀ *ᵥ w' -
      (lam t₀ • w' + lam' • w t₀) = 0 :=
    h.unique <| (hasDerivAt_const t₀ (0 : n → 𝕜)).congr_of_eventuallyEq <|
      Eventually.of_forall fun t ↦ by
        simp only [Pi.sub_apply, Pi.smul_apply', hweig t, RCLike.real_smul_eq_coe_smul (K := 𝕜),
          sub_self]
  rw [hw₀, RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜)] at h'
  linear_combination (exp := 1) h'

/-! ### The second variation formula -/

omit [DecidableEq n] in
/-- The derivative of `t ↦ Re ⟪w t, C t w t⟫` along a differentiable curve `w` of vectors and an
entrywise differentiable curve `C` of matrices. -/
private theorem hasDerivAt_re_star_dotProduct_mulVec {w : ℝ → n → 𝕜} {w' : n → 𝕜}
    {C : ℝ → Matrix n n 𝕜} {C' : Matrix n n 𝕜} {t : ℝ} (hw : HasDerivAt w w' t)
    (hC : ∀ a b, HasDerivAt (fun s ↦ C s a b) (C' a b) t) :
    HasDerivAt (fun s ↦ RCLike.re (star (w s) ⬝ᵥ (C s *ᵥ w s)))
      (RCLike.re (star w' ⬝ᵥ (C t *ᵥ w t)) + RCLike.re (star (w t) ⬝ᵥ (C' *ᵥ w t)) +
        RCLike.re (star (w t) ⬝ᵥ (C t *ᵥ w'))) t := by
  have h := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hw.star.dotProduct (hasDerivAt_mulVec_of_entries hC hw))
  simpa only [Function.comp_def, RCLike.reCLM_apply, dotProduct_add, map_add, add_assoc] using h

/-- **Hadamard's second variation formula.** Let `M` be a curve of Hermitian matrices whose
entries are differentiable near `t₀` and whose entrywise derivative `M'` is differentiable at
`t₀`, and let `u` be a unit eigenvector of `M t₀` for a simple ordered eigenvalue
`λᵢ = (M t₀).eigenvalues₀ i`. Then the derivative of `t ↦ (M t).eigenvalues₀ i` has derivative

`Re ⟪u, M'' (t₀) u⟫ + 2 ∑_{λₖ ≠ λᵢ} |(Uᴴ M' (t₀) u)ₖ|² / (λᵢ - λₖ)`

at `t₀`, where `U` is the eigenvector unitary of `M t₀` and `λₖ = (M t₀).eigenvalues k`. The
coordinate `(Uᴴ M' (t₀) u)ₖ` is `⟪uₖ, M' (t₀) u⟫` for the eigenvector `uₖ` in the `k`-th column
of `U`. -/
theorem hasDerivAt_deriv_eigenvalues₀ (hM : ∀ t, (M t).IsHermitian) {t₀ : ℝ}
    (hMd : ∀ᶠ t in 𝓝 t₀, ∀ a b, DifferentiableAt ℝ (fun s ↦ M s a b) t)
    (hM₂ : ∀ a b, DifferentiableAt ℝ (deriv fun s ↦ M s a b) t₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM t₀).eigenvalues₀ j ≠ (hM t₀).eigenvalues₀ i) {u : n → 𝕜}
    (hu : M t₀ *ᵥ u = ((hM t₀).eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    HasDerivAt (deriv fun t ↦ (hM t).eigenvalues₀ i)
      (RCLike.re (star u ⬝ᵥ (of (fun a b ↦ deriv (deriv fun s ↦ M s a b) t₀) *ᵥ u)) +
        2 * ∑ k with (hM t₀).eigenvalues k ≠ (hM t₀).eigenvalues₀ i,
          ‖(star ((hM t₀).eigenvectorUnitary : Matrix n n 𝕜) *ᵥ
            (of (fun a b ↦ deriv (fun s ↦ M s a b) t₀) *ᵥ u)) k‖ ^ 2 /
              ((hM t₀).eigenvalues₀ i - (hM t₀).eigenvalues k)) t₀ := by
  have hMd₀ := hMd.self_of_nhds
  set M' : ℝ → Matrix n n 𝕜 := fun t ↦ of fun a b ↦ deriv (fun s ↦ M s a b) t
  set lam' := deriv (fun t ↦ (hM t).eigenvalues₀ i) t₀
  have hB : (M' t₀).IsHermitian := by
    simpa only [fderiv_apply_one_eq_deriv] using isHermitian_fderiv_apply hM t₀ 1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  obtain ⟨w, hw₀, hwd, hweig⟩ := exists_eigenvector_curve hM hMd₀ hi hu hu1
  have hw' := hwd.hasDerivAt
  -- `λᵢ'` is the Rayleigh quotient of `M'` along `w`, near `t₀`.
  have hev : (deriv fun t ↦ (hM t).eigenvalues₀ i) =ᶠ[𝓝 t₀] fun t ↦
      RCLike.re (star (w t) ⬝ᵥ (M' t *ᵥ w t)) / RCLike.re (star (w t) ⬝ᵥ w t) := by
    have hsimple : ∀ᶠ t in 𝓝 t₀, ∀ j ≠ i, (hM t).eigenvalues₀ j ≠ (hM t).eigenvalues₀ i := by
      have hc (j : Fin (Fintype.card n)) :=
        continuousAt_eigenvalues₀ hM (fun a b ↦ (hMd₀ a b).continuousAt) j
      refine eventually_all.2 fun j ↦ ?_
      obtain rfl | hj := eq_or_ne j i
      · exact Eventually.of_forall fun _ h ↦ absurd rfl h
      · filter_upwards [((hc j).sub (hc i)).eventually_ne (sub_ne_zero.2 (hi j hj))] with t ht _
        exact sub_ne_zero.1 ht
    filter_upwards [hMd, hsimple, hwd.continuousAt.eventually_ne (hw₀ ▸ hu0)] with t hd hs hne
    exact deriv_eigenvalues₀_eq_div hM hd hs (hweig t) hne
  have hlam' : lam' = RCLike.re (star u ⬝ᵥ (M' t₀ *ᵥ u)) := by
    simpa only [hw₀, hu1, RCLike.one_re, div_one] using hev.self_of_nhds
  -- Differentiating `M w = λᵢ w` at `t₀` determines `w'` off the eigenvalue `λᵢ`.
  have hfirst := mulVec_sub_smul_eq_of_hasDerivAt hMd₀
    (hasFDerivAt_eigenvalues₀ hM hMd₀ hi hu hu1).differentiableAt.hasDerivAt hw' hw₀ hweig
  have hf := hasDerivAt_re_star_dotProduct_mulVec (C := M')
    (C' := of fun a b ↦ deriv (deriv fun s ↦ M s a b) t₀) hw' fun a b ↦ (hM₂ a b).hasDerivAt
  have hg := hasDerivAt_re_star_dotProduct_mulVec (C := fun _ ↦ 1) (C' := 0) hw' fun _ _ ↦
    hasDerivAt_const t₀ _
  simp only [one_mulVec, zero_mulVec, dotProduct_zero, map_zero, add_zero] at hg
  have hR := hf.div hg (by simp [hw₀, hu1])
  refine (hR.congr_of_eventuallyEq hev).congr_deriv ?_
  -- Assemble `λᵢ'' = Re ⟪u, M'' u⟫ + 2 Re ⟪w', M' u - λᵢ' u⟫` and evaluate the last term.
  have hS := re_star_dotProduct_sub_smul_eq_sum (hM t₀) hu hfirst
  rw [dotProduct_sub, dotProduct_smul, map_sub, smul_eq_mul, RCLike.re_ofReal_mul] at hS
  rw [hw₀, hu1, RCLike.one_re, one_pow, div_one, mul_one, ← hlam', ← hS,
    ← hB.star_dotProduct_mulVec_comm, star_dotProduct u (deriv w t₀)]
  simp only [RCLike.star_def, RCLike.conj_re]
  ring

/-- **Hadamard's second variation formula along a line.** If `u` is a unit eigenvector of a
Hermitian matrix `A` for a simple ordered eigenvalue `λᵢ = A.eigenvalues₀ i`, and `B` is
Hermitian, then the derivative of `t ↦ (A + t • B).eigenvalues₀ i` has derivative
`2 ∑_{λₖ ≠ λᵢ} |(Uᴴ B u)ₖ|² / (λᵢ - λₖ)` at `t = 0`, where `U` is the eigenvector unitary of `A`
and `λₖ = A.eigenvalues k`. -/
theorem IsHermitian.hasDerivAt_deriv_eigenvalues₀_add_smul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i) {u : n → 𝕜}
    (hu : A *ᵥ u = (hA.eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    HasDerivAt (deriv fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ i)
      (2 * ∑ k with hA.eigenvalues k ≠ hA.eigenvalues₀ i,
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (B *ᵥ u)) k‖ ^ 2 /
          (hA.eigenvalues₀ i - hA.eigenvalues k)) 0 := by
  have hM : ∀ t : ℝ, (A + t • B).IsHermitian := fun t ↦ hA.add (hB.smul (IsSelfAdjoint.all t))
  have hline (a b : n) (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (A + s • B) a b) (B a b) t := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, one_smul] using
      ((hasDerivAt_id' t).smul_const (B a b)).const_add (A a b)
  have hderiv (a b : n) : (deriv fun s : ℝ ↦ (A + s • B) a b) = fun _ ↦ B a b :=
    funext fun t ↦ (hline a b t).deriv
  have hB' : (of fun a b ↦ deriv (fun s : ℝ ↦ (A + s • B) a b) 0) = B := by
    ext a b
    rw [of_apply, hderiv]
  have hC : (of fun a b ↦ deriv (deriv fun s : ℝ ↦ (A + s • B) a b) 0) = 0 := by
    ext a b
    rw [of_apply, hderiv, deriv_const, Matrix.zero_apply]
  -- At `t = 0` the matrix `A + 0 • B` is `A`, with the same spectral data.
  have hspec : ∀ (X : Matrix n n 𝕜) (hX : X.IsHermitian), X = A →
      hX.eigenvalues₀ = hA.eigenvalues₀ ∧ hX.eigenvalues = hA.eigenvalues ∧
        (hX.eigenvectorUnitary : Matrix n n 𝕜) = hA.eigenvectorUnitary := by
    rintro X hX rfl
    exact ⟨rfl, rfl, rfl⟩
  have h0 : A + (0 : ℝ) • B = A := by rw [zero_smul, add_zero]
  obtain ⟨h₁, h₂, h₃⟩ := hspec _ (hM 0) h0
  have h := hasDerivAt_deriv_eigenvalues₀ hM
    (Eventually.of_forall fun t a b ↦ (hline a b t).differentiableAt)
    (fun a b ↦ by rw [hderiv]; exact differentiableAt_const _) (t₀ := 0) (i := i)
    (by rw [h₁]; exact hi) (u := u) (by rw [h₁, h0]; exact hu) hu1
  rwa [hB', hC, zero_mulVec, dotProduct_zero, map_zero, zero_add, h₁, h₂, h₃] at h

end Matrix
