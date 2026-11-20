/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Matrix.Spectrum

/-!
# Smoothness and first variation of simple eigenvalues

Let `M : E → Matrix n n 𝕜` be a family of Hermitian matrices over `RCLike 𝕜`, parametrized by a
real normed space `E`, whose entries are `C^k` at `x₀`. If the `i`-th ordered eigenvalue
`λᵢ = (M x₀).eigenvalues₀ i` is simple, then `x ↦ λᵢ (M x)` is `C^k` at `x₀`
(`Matrix.contDiffAt_eigenvalues₀`). If the entries are differentiable at `x₀`, the derivative is
given by **Hadamard's first variation formula** (`Matrix.hasFDerivAt_eigenvalues₀`)

`Dλᵢ (x₀) v = Re ⟪u, (DM (x₀) v) u⟫`

for every unit eigenvector `u` of `M x₀` with eigenvalue `λᵢ`. For the straight line `A + t • B`
of Hermitian matrices this reads `d/dt λᵢ (A + t • B) |_{t = 0} = Re ⟪u, B u⟫`
(`Matrix.IsHermitian.hasDerivAt_eigenvalues₀_add_smul`). These are the first-order inputs to the
Itô computation for the eigenvalues of matrix-valued diffusions: there the parameter is the vector
of real noise coordinates, and simplicity holds off the collision set.

The value `k = ω` is allowed, so analytic families have analytic simple eigenvalues. At a repeated
eigenvalue the ordered eigenvalues are in general only Lipschitz
(`Matrix.lipschitzWith_eigenvalues₀`): for `M t = diagonal ![t, -t]` the top eigenvalue is `|t|`.

## Implementation notes

The function `G (x, μ) = Re det (μ - M x)` is `C^k` because the determinant is a polynomial in the
entries, and its zeros in `μ` are the eigenvalues of `M x`. Conjugating by the eigenvector unitary
`U` of `M x₀` replaces `M x₀` by the diagonal matrix of its eigenvalues `d`, and Jacobi's adjugate
formula gives

`DG (x₀, λᵢ) (v, s) = ∏_{j ≠ i} (λᵢ - d j) * (s - Re (Uᴴ (DM (x₀) v) U)ᵢᵢ)`.

Simplicity makes the partial derivative in `μ` invertible, so over a complete parameter space the
implicit function theorem produces a `C^k` function `ψ` whose graph is the zero set of `G` near
`(x₀, λᵢ)`. Since `x ↦ λᵢ (M x)` is continuous and takes values in that zero set, it agrees with
`ψ` near `x₀`. Differentiating `G (x, λᵢ (M x)) = 0` then gives the first variation formula, and a
unit eigenvector of a simple eigenvalue is a unimodular multiple of the corresponding column of
`U`.

A general family factors as `x ↦ selfAdjointPart ℝ (M x)` through the finite-dimensional, hence
complete, space of matrices, where the self-adjoint part `(X + Xᴴ) / 2` is real-linear and
Hermitian-valued. Applying the above to the self-adjoint part and composing removes the
completeness of `E`, and needs only differentiability of the entries of `M` for the first
variation formula.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter II, §§1–2
  (analytic perturbation of simple eigenvalues).
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §1.3
  (Hadamard's first variation formula).
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), proof of Theorem 4.3.2 (derivatives of eigenvalues along matrix
  Brownian motion).
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace Matrix

variable {𝕜 n E : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The real characteristic function of a family -/

/-- The function `(x, μ) ↦ Re det (μ - M x)`. When `M x` is Hermitian its zeros in `μ` are the
eigenvalues of `M x`. -/
private def reDetScalarSub (M : E → Matrix n n 𝕜) (p : E × ℝ) : ℝ :=
  RCLike.re (scalar n (p.2 : 𝕜) - M p.1).det

/-- The determinant is a polynomial in the entries, so `(x, μ) ↦ Re det (μ - M x)` is as smooth as
the entries of `M`. -/
private theorem contDiffAt_reDetScalarSub {M : E → Matrix n n 𝕜} {x₀ : E} {k : ℕ∞ω}
    (hM : ∀ a b, ContDiffAt ℝ k (fun x ↦ M x a b) x₀) (μ : ℝ) :
    ContDiffAt ℝ k (reDetScalarSub M) (x₀, μ) := by
  have hentry (a b : n) :
      ContDiffAt ℝ k (fun p : E × ℝ ↦ (scalar n (p.2 : 𝕜) - M p.1) a b) (x₀, μ) := by
    simp only [Matrix.sub_apply, scalar_apply, diagonal_apply]
    refine ContDiffAt.sub ?_ (ContDiffAt.comp (x₀, μ) (hM a b) contDiffAt_fst)
    split_ifs
    · exact ((RCLike.ofRealCLM (K := 𝕜)).contDiff.comp contDiff_snd).contDiffAt
    · exact contDiffAt_const
  unfold reDetScalarSub
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  exact RCLike.reCLM.contDiff.contDiffAt.comp _
    (ContDiffAt.sum fun σ _ ↦ contDiffAt_const.mul (contDiffAt_prod fun a _ ↦ hentry _ _))

open scoped Matrix.Norms.Operator in
/-- The derivative of `t ↦ Re det (μ + t s - A t)` at `0`, by Jacobi's adjugate formula, for a
real curve `A` of matrices with entrywise derivative `A'`. -/
private theorem hasDerivAt_re_det_scalar_sub {A : ℝ → Matrix n n 𝕜} {A' : Matrix n n 𝕜}
    (hA : ∀ a b, HasDerivAt (fun t ↦ A t a b) (A' a b) 0) (μ s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ RCLike.re (scalar n ((μ + t * s : ℝ) : 𝕜) - A t).det)
      (RCLike.re ((scalar n (μ : 𝕜) - A 0).adjugate * (scalar n (s : 𝕜) - A')).trace) 0 := by
  have hB (a b : n) : HasDerivAt (fun t ↦ (scalar n ((μ + t * s : ℝ) : 𝕜) - A t) a b)
      ((scalar n (s : 𝕜) - A') a b) 0 := by
    simp only [Matrix.sub_apply, scalar_apply, diagonal_apply]
    refine HasDerivAt.sub ?_ (hA a b)
    split_ifs
    · have h := (((RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul_const
        (s : 𝕜)).const_add (μ : 𝕜)
      convert h using 1
      · ext t
        simp
      · simp
    · exact hasDerivAt_const _ _
  have hB' : HasDerivAt (fun t ↦ of.symm (scalar n ((μ + t * s : ℝ) : 𝕜) - A t))
      (of.symm (scalar n (s : 𝕜) - A')) 0 :=
    hasDerivAt_pi.2 fun a ↦ hasDerivAt_pi.2 fun b ↦ hB a b
  have h := ((differentiable_det (𝕜 := 𝕜) _).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    ((ofContinuousLinearEquiv ℝ).hasFDerivAt.comp_hasDerivAt 0 hB')
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe, coe_ofContinuousLinearEquiv,
    Equiv.apply_symm_apply] at h
  have h' := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt 0 (h.congr_deriv
    (fderiv_det_apply_adjugate _ _))
  simpa [Function.comp_def] using h'

/-- At an eigenvalue `d k₀` of a Hermitian matrix `M x₀` with eigenvalue list `d`, the derivative
of `(x, μ) ↦ Re det (μ - M x)` in the direction `(v, s)` is
`∏_{j ≠ k₀} (d k₀ - d j) * (s - Re (Uᴴ (DM (x₀) v) U) k₀ k₀)`, where `U` is the eigenvector
unitary. -/
private theorem fderiv_reDetScalarSub_apply {M : E → Matrix n n 𝕜} {x₀ : E}
    (hM₀ : (M x₀).IsHermitian) (hM : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) (k₀ : n)
    (hG : DifferentiableAt ℝ (reDetScalarSub M) (x₀, hM₀.eigenvalues k₀)) (v : E) (s : ℝ) :
    fderiv ℝ (reDetScalarSub M) (x₀, hM₀.eigenvalues k₀) (v, s) =
      (∏ j ∈ Finset.univ.erase k₀, (hM₀.eigenvalues k₀ - hM₀.eigenvalues j)) *
        (s - RCLike.re ((star (hM₀.eigenvectorUnitary : Matrix n n 𝕜) *
          of (fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v) * hM₀.eigenvectorUnitary) k₀ k₀)) := by
  set U := hM₀.eigenvectorUnitary
  set d := hM₀.eigenvalues
  set B : Matrix n n 𝕜 := of fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v
  -- Move along the line `t ↦ (x₀ + t • v, d k₀ + t * s)`, conjugated into the eigenbasis of `M x₀`.
  set A : ℝ → Matrix n n 𝕜 := fun t ↦ star (U : Matrix n n 𝕜) * M (x₀ + t • v) * U
  have hA (a b : n) : HasDerivAt (fun t ↦ A t a b) ((star (U : Matrix n n 𝕜) * B * U) a b) 0 := by
    have hline (k l : n) : HasDerivAt (fun t : ℝ ↦ M (x₀ + t • v) k l) (B k l) 0 := by
      simpa [B, Function.comp_def] using (hM k l).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀) (by simp)
    simp only [A, Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun l _ ↦
      (HasDerivAt.fun_sum fun k _ ↦ (hline k l).const_mul _).mul_const _
  have hcurve := hasDerivAt_re_det_scalar_sub hA (d k₀) s
  have hline : HasDerivAt (fun t : ℝ ↦ reDetScalarSub M ((x₀, d k₀) + t • (v, s)))
      (fderiv ℝ (reDetScalarSub M) (x₀, d k₀) (v, s)) 0 := by
    simpa [Function.comp_def] using hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const (v, s)).const_add (x₀, d k₀)) (by simp)
  have hfun : (fun t : ℝ ↦ RCLike.re (scalar n ((d k₀ + t * s : ℝ) : 𝕜) - A t).det) =
      fun t ↦ reDetScalarSub M ((x₀, d k₀) + t • (v, s)) := by
    funext t
    -- Conjugation by `U` does not change the characteristic polynomial.
    rw [← eval_charpoly, charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem U.2,
      Matrix.one_mul, eval_charpoly]
    simp [reDetScalarSub]
  rw [hline.unique (hfun ▸ hcurve)]
  -- At `t = 0` the conjugated matrix is diagonal, so its adjugate is diagonal, supported at `k₀`.
  have hA0 : scalar n (d k₀ : 𝕜) - A 0 = diagonal fun k ↦ ((d k₀ - d k : ℝ) : 𝕜) := by
    have h : A 0 = diagonal (RCLike.ofReal ∘ d) := by
      simpa [A] using hM₀.star_eigenvectorUnitary_mul_mul_eigenvectorUnitary
    rw [h, scalar_apply, diagonal_sub]
    simp
  rw [hA0, adjugate_diagonal, trace, Finset.sum_eq_single k₀]
  · simp only [diag_apply, diagonal_mul, Matrix.sub_apply, scalar_apply, diagonal_apply_eq]
    rw [← RCLike.ofReal_prod, RCLike.re_ofReal_mul]
    simp
  · intro k _ hk
    rw [diag_apply, diagonal_mul,
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hk, Finset.mem_univ k₀⟩) (by simp),
      zero_mul]
  · simp

/-! ### Simple eigenvalues -/

/-- Simplicity of the ordered eigenvalue `λᵢ` is simplicity of the matrix-indexed eigenvalue at the
matching index. -/
private theorem eigenvalues_ne_eigenvalues_equivOfCardEq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {i : Fin (Fintype.card n)} (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i) :
    ∀ k ≠ Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) i, hA.eigenvalues k ≠
      hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) i) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  intro k hk
  have hk' : e.symm k ≠ i := fun h ↦ hk (by rw [← h, e.apply_symm_apply])
  simpa [e, IsHermitian.eigenvalues] using hi _ hk'

/-- At a simple ordered eigenvalue `λᵢ`, the product `∏_{j ≠ i} (λᵢ - λⱼ)` over the remaining
matrix-indexed eigenvalues does not vanish. -/
private theorem prod_erase_sub_eigenvalues_ne_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {i : Fin (Fintype.card n)} (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i) :
    ∏ j ∈ Finset.univ.erase (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) i),
      (hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) i) -
        hA.eigenvalues j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j hj ↦ sub_ne_zero.2
    (eigenvalues_ne_eigenvalues_equivOfCardEq hA hi j (Finset.ne_of_mem_erase hj)).symm

/-! ### Smoothness and first variation -/

omit [DecidableEq n] in
/-- The coordinate form `∑ a b, conj (u a) * u b * L_{ab} v` of `⟪u, (L v) u⟫`. -/
private theorem sum_sum_smul_apply (u : n → 𝕜) (L : n → n → E →L[ℝ] 𝕜) (v : E) :
    (∑ a, ∑ b, (star (u a) * u b) • L a b) v = star u ⬝ᵥ (of (fun a b ↦ L a b v) *ᵥ u) := by
  simp only [sum_apply, smul_apply, smul_eq_mul,
    dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-! ### The core statements over a complete parameter space -/

section Complete

variable [CompleteSpace E] {M : E → Matrix n n 𝕜} {x₀ : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Every ordered eigenvalue of `M x` is a zero of `μ ↦ Re det (μ - M x)`. -/
private theorem reDetScalarSub_eigenvalues₀ (hM : ∀ x, (M x).IsHermitian) (x : E)
    (i : Fin (Fintype.card n)) : reDetScalarSub M (x, (hM x).eigenvalues₀ i) = 0 := by
  have hroot : ((hM x).eigenvalues₀ i : 𝕜) ∈ (M x).charpoly.roots := by
    rw [(hM x).roots_charpoly_eq_eigenvalues₀]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  rw [reDetScalarSub, ← eval_charpoly, ((Polynomial.mem_roots (charpoly_monic _).ne_zero).1
    hroot).eq_zero, map_zero]

/-- The implicit function theorem for a simple ordered eigenvalue of a `C^k` family over a complete
parameter space. -/
private theorem contDiffAt_eigenvalues₀_of_completeSpace (hM : ∀ x, (M x).IsHermitian) {k : ℕ∞ω}
    (hk : k ≠ 0) (hMk : ∀ a b, ContDiffAt ℝ k (fun x ↦ M x a b) x₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM x₀).eigenvalues₀ j ≠ (hM x₀).eigenvalues₀ i) :
    ContDiffAt ℝ k (fun x ↦ (hM x).eigenvalues₀ i) x₀ := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have he : (hM x₀).eigenvalues (e i) = (hM x₀).eigenvalues₀ i :=
    (hM x₀).eigenvalues_apply_equivOfCardEq i
  have hc := prod_erase_sub_eigenvalues_ne_zero (hM x₀) hi
  have hG := contDiffAt_reDetScalarSub hMk ((hM x₀).eigenvalues₀ i)
  -- The partial derivative in `μ` is multiplication by `∏_{j ≠ i} (λᵢ - λⱼ) ≠ 0`.
  have hpartial : fderiv ℝ (reDetScalarSub M) (x₀, (hM x₀).eigenvalues₀ i) ∘L
      ContinuousLinearMap.inr ℝ E ℝ = ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 _ hc) := by
    have h := fderiv_reDetScalarSub_apply (hM x₀) (fun a b ↦ (hMk a b).differentiableAt hk) (e i)
      (he ▸ hG.differentiableAt hk) 0
    have hz : (of fun (_ : n) (_ : n) ↦ (0 : 𝕜)) = 0 := by
      ext
      simp
    rw [he] at h
    ext
    simp [h, hz, e]
  have hinv : (fderiv ℝ (reDetScalarSub M) (x₀, (hM x₀).eigenvalues₀ i) ∘L
      ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := ⟨_, hpartial.symm⟩
  -- The continuous eigenvalue lies on the zero set of `G`, which is the graph of `ψ` near `x₀`.
  have hcont := continuousAt_eigenvalues₀ hM (fun a b ↦ (hMk a b).continuousAt) i
  have hiff := hG.eventually_apply_eq_iff_implicitFunction hk hinv
  have hev : (fun x ↦ (hM x).eigenvalues₀ i) =ᶠ[𝓝 x₀] hG.implicitFunction hk hinv := by
    filter_upwards [(continuousAt_id.prodMk hcont).eventually hiff] with x hx
    simp only [id] at hx
    exact (hx.1 (by rw [reDetScalarSub_eigenvalues₀, reDetScalarSub_eigenvalues₀])).symm
  exact (hG.contDiffAt_implicitFunction hk hinv).congr_of_eventuallyEq hev

/-- Hadamard's first variation formula for a `C¹` family over a complete parameter space, obtained
by differentiating `Re det (λᵢ (M x) - M x) = 0`. -/
private theorem hasFDerivAt_eigenvalues₀_of_completeSpace (hM : ∀ x, (M x).IsHermitian)
    (hM1 : ∀ a b, ContDiffAt ℝ 1 (fun x ↦ M x a b) x₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM x₀).eigenvalues₀ j ≠ (hM x₀).eigenvalues₀ i) {u : n → 𝕜}
    (hu : M x₀ *ᵥ u = ((hM x₀).eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    HasFDerivAt (fun x ↦ (hM x).eigenvalues₀ i)
      (RCLike.reCLM.comp (∑ a, ∑ b, (star (u a) * u b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have he : (hM x₀).eigenvalues (e i) = (hM x₀).eigenvalues₀ i :=
    (hM x₀).eigenvalues_apply_equivOfCardEq i
  have hc := prod_erase_sub_eigenvalues_ne_zero (hM x₀) hi
  have hG := (contDiffAt_reDetScalarSub hM1 ((hM x₀).eigenvalues₀ i)).differentiableAt one_ne_zero
  have hlam :=
    (contDiffAt_eigenvalues₀_of_completeSpace hM one_ne_zero hM1 hi).differentiableAt one_ne_zero
  -- Differentiate `G (x, λᵢ (M x)) = 0` at `x₀`.
  have hzero : fderiv ℝ (reDetScalarSub M) (x₀, (hM x₀).eigenvalues₀ i) ∘L
      (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ (fun x ↦ (hM x).eigenvalues₀ i) x₀) = 0 :=
    (hG.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).prodMk hlam.hasFDerivAt)).unique <|
      (hasFDerivAt_const 0 x₀).congr_of_eventuallyEq
        (Eventually.of_forall fun x ↦ by
          simpa only [Function.comp_apply, id] using reDetScalarSub_eigenvalues₀ hM x i)
  refine hlam.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  have h := fderiv_reDetScalarSub_apply (hM x₀) (fun a b ↦ (hM1 a b).differentiableAt one_ne_zero)
    (e i) (he ▸ hG) v (fderiv ℝ (fun x ↦ (hM x).eigenvalues₀ i) x₀ v)
  have h0 := DFunLike.congr_fun hzero v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at h0
  rw [he, h0] at h
  rw [← (hM x₀).star_dotProduct_mulVec_eq_of_simple
    (eigenvalues_ne_eigenvalues_equivOfCardEq (hM x₀) hi) (he ▸ hu) hu1] at h
  have h' := (mul_eq_zero.1 (by simpa using h.symm)).resolve_left (he ▸ hc)
  rw [sub_eq_zero] at h'
  rw [h', ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, sum_sum_smul_apply]

end Complete

/-! ### The universal Hermitian family -/

open scoped Matrix.Norms.Elementwise

/-- The `(a, b)` entry of the self-adjoint part `(X + Xᴴ) / 2` of a matrix `X`, as a continuous
real-linear functional. -/
private def selfAdjointPartEntry (a b : n) : Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  ContinuousLinearMap.proj b ∘L ContinuousLinearMap.proj a ∘L
    (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL ∘L selfAdjointPartL ℝ (Matrix n n 𝕜)

omit [DecidableEq n] in
private theorem contDiff_selfAdjointPart_apply {k : ℕ∞ω} (a b : n) :
    ContDiff ℝ k (fun X : Matrix n n 𝕜 ↦ (selfAdjointPart ℝ X : Matrix n n 𝕜) a b) :=
  (selfAdjointPartEntry (𝕜 := 𝕜) a b).contDiff

omit [Fintype n] [DecidableEq n] in
private theorem fderiv_selfAdjointPart_apply (a b : n) (X V : Matrix n n 𝕜) :
    fderiv ℝ (fun Y : Matrix n n 𝕜 ↦ (selfAdjointPart ℝ Y : Matrix n n 𝕜) a b) X V =
      (selfAdjointPart ℝ V : Matrix n n 𝕜) a b :=
  congrArg (· V) (selfAdjointPartEntry (𝕜 := 𝕜) a b).fderiv

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_selfAdjointPart (X : Matrix n n 𝕜) :
    (selfAdjointPart ℝ X : Matrix n n 𝕜).IsHermitian :=
  (selfAdjointPart ℝ X).2

private theorem eigenvalues₀_congr {A B : Matrix n n 𝕜} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst h
  rfl

/-! ### Smoothness and first variation -/

variable {M : E → Matrix n n 𝕜} {x₀ : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A Hermitian family is its own self-adjoint part. -/
private theorem eigenvalues₀_eq_comp_selfAdjointPart (hM : ∀ x, (M x).IsHermitian)
    (i : Fin (Fintype.card n)) :
    (fun x ↦ (hM x).eigenvalues₀ i) =
      (fun X ↦ (isHermitian_selfAdjointPart X).eigenvalues₀ i) ∘ M :=
  funext fun x ↦ congrFun (eigenvalues₀_congr
    ((hM x).isSelfAdjoint.coe_selfAdjointPart_apply ℝ).symm (hM x)
    (isHermitian_selfAdjointPart _)) i

/-- **Simple eigenvalues are as smooth as the family.** Let `M` be a family of Hermitian matrices
over a real normed space whose entries are `C^k` at `x₀`. If the ordered eigenvalue
`(M x₀).eigenvalues₀ i` is simple, then `x ↦ (M x).eigenvalues₀ i` is `C^k` at `x₀`. For `k = ω`
this is analyticity, and for `k = 0` it is continuity, which holds without simplicity
(`Matrix.continuousAt_eigenvalues₀`). -/
theorem contDiffAt_eigenvalues₀ (hM : ∀ x, (M x).IsHermitian) {k : ℕ∞ω}
    (hMk : ∀ a b, ContDiffAt ℝ k (fun x ↦ M x a b) x₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM x₀).eigenvalues₀ j ≠ (hM x₀).eigenvalues₀ i) :
    ContDiffAt ℝ k (fun x ↦ (hM x).eigenvalues₀ i) x₀ := by
  have hMk' : ContDiffAt ℝ k M x₀ := contDiffAt_pi.2 fun a ↦ contDiffAt_pi.2 fun b ↦ hMk a b
  rw [eigenvalues₀_eq_comp_selfAdjointPart hM i]
  refine ContDiffAt.comp x₀ ?_ hMk'
  obtain rfl | hk := eq_or_ne k 0
  · -- `C⁰` is continuity, which holds at repeated eigenvalues too.
    refine (contDiff_zero.2 (continuous_iff_continuousAt.2 fun X ↦ ?_)).contDiffAt
    exact continuousAt_eigenvalues₀ isHermitian_selfAdjointPart
      (fun a b ↦ (contDiff_selfAdjointPart_apply (k := 0) a b).continuous.continuousAt) i
  have hcongr := eigenvalues₀_congr ((hM x₀).isSelfAdjoint.coe_selfAdjointPart_apply ℝ).symm
    (hM x₀) (isHermitian_selfAdjointPart _)
  exact contDiffAt_eigenvalues₀_of_completeSpace isHermitian_selfAdjointPart hk
    (fun a b ↦ (contDiff_selfAdjointPart_apply a b).contDiffAt)
    (by simpa only [← hcongr] using hi)

/-- **Hadamard's first variation formula.** Let `M` be a family of Hermitian matrices over a real
normed space whose entries are differentiable at `x₀`, and let `u` be a unit eigenvector of `M x₀`
for a simple ordered eigenvalue `(M x₀).eigenvalues₀ i`. Then `x ↦ (M x).eigenvalues₀ i` has
derivative `v ↦ Re ⟪u, (DM (x₀) v) u⟫` at `x₀`, written in coordinates as
`Re ∑ a b, conj (u a) * u b * DM_{ab} (x₀) v`. -/
theorem hasFDerivAt_eigenvalues₀ (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM x₀).eigenvalues₀ j ≠ (hM x₀).eigenvalues₀ i) {u : n → 𝕜}
    (hu : M x₀ *ᵥ u = ((hM x₀).eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    HasFDerivAt (fun x ↦ (hM x).eigenvalues₀ i)
      (RCLike.reCLM.comp (∑ a, ∑ b, (star (u a) * u b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ := by
  have hcongr := eigenvalues₀_congr ((hM x₀).isSelfAdjoint.coe_selfAdjointPart_apply ℝ).symm
    (hM x₀) (isHermitian_selfAdjointPart _)
  have hcore := hasFDerivAt_eigenvalues₀_of_completeSpace isHermitian_selfAdjointPart
    (x₀ := M x₀) (fun a b ↦ (contDiff_selfAdjointPart_apply a b).contDiffAt) (i := i)
    (by simpa only [← hcongr] using hi) (u := u)
    (by simpa only [(hM x₀).isSelfAdjoint.coe_selfAdjointPart_apply ℝ, ← hcongr] using hu) hu1
  have hX : HasFDerivAt M
      (ContinuousLinearMap.pi fun a ↦ ContinuousLinearMap.pi fun b ↦
        fderiv ℝ (fun x ↦ M x a b) x₀) x₀ :=
    hasFDerivAt_pi.2 fun a ↦ hasFDerivAt_pi.2 fun b ↦ (hMd a b).hasFDerivAt
  rw [eigenvalues₀_eq_comp_selfAdjointPart hM i]
  refine (hcore.comp x₀ hX).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  -- The derivative of `M` is Hermitian, so it is its own self-adjoint part.
  have hD : (of fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v).IsHermitian := by
    refine IsHermitian.ext fun a b ↦ ?_
    have h : (fun x ↦ M x a b) = fun x ↦ (RCLike.conjCLE (K := 𝕜)) (M x b a) :=
      funext fun x ↦ by rw [RCLike.conjCLE_apply, ← RCLike.star_def, (hM x).apply]
    have h2 : HasFDerivAt (fun x ↦ (RCLike.conjCLE (K := 𝕜)) (M x b a))
        ((RCLike.conjCLE (K := 𝕜) : 𝕜 →L[ℝ] 𝕜).comp (fderiv ℝ (fun x ↦ M x b a) x₀)) x₀ :=
      (RCLike.conjCLE (K := 𝕜)).hasFDerivAt.comp x₀ (hMd b a).hasFDerivAt
    rw [of_apply, of_apply, h, h2.fderiv]
    simp [RCLike.star_def]
  -- The composite derivative is the derivative of the self-adjoint part at `DM (x₀) v`. It is
  -- unfolded with `change`, since the derivative of `M` is stated on arrays `n → n → 𝕜` and
  -- `ContinuousLinearMap.comp_apply` does not match it against matrices.
  change RCLike.re ((∑ a, ∑ b, (star (u a) * u b) •
    fderiv ℝ (fun X : Matrix n n 𝕜 ↦ (selfAdjointPart ℝ X : Matrix n n 𝕜) a b) (M x₀))
      (of fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v)) =
    RCLike.re ((∑ a, ∑ b, (star (u a) * u b) • fderiv ℝ (fun x ↦ M x a b) x₀) v)
  rw [sum_sum_smul_apply]
  refine congrArg RCLike.re ((sum_sum_smul_apply _ _ _).trans ?_)
  congr 2
  ext a b
  exact (fderiv_selfAdjointPart_apply a b _ _).trans
    (congrFun (congrFun (hD.isSelfAdjoint.coe_selfAdjointPart_apply ℝ) a) b)

/-- The derivative of a simple ordered eigenvalue in the direction `v` is `Re ⟪u, (DM (x₀) v) u⟫`
for any unit eigenvector `u`. -/
theorem fderiv_eigenvalues₀_apply (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, (hM x₀).eigenvalues₀ j ≠ (hM x₀).eigenvalues₀ i) {u : n → 𝕜}
    (hu : M x₀ *ᵥ u = ((hM x₀).eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) (v : E) :
    fderiv ℝ (fun x ↦ (hM x).eigenvalues₀ i) x₀ v =
      RCLike.re (star u ⬝ᵥ (of (fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v) *ᵥ u)) := by
  rw [(hasFDerivAt_eigenvalues₀ hM hMd hi hu hu1).fderiv, ContinuousLinearMap.comp_apply,
    RCLike.reCLM_apply, sum_sum_smul_apply]

/-- **Hadamard's first variation formula along a line.** If `u` is a unit eigenvector of a
Hermitian matrix `A` for a simple ordered eigenvalue `A.eigenvalues₀ i`, and `B` is Hermitian, then
`t ↦ (A + t • B).eigenvalues₀ i` has derivative `Re ⟪u, B u⟫` at `t = 0`. -/
theorem IsHermitian.hasDerivAt_eigenvalues₀_add_smul {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {i : Fin (Fintype.card n)}
    (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i) {u : n → 𝕜}
    (hu : A *ᵥ u = (hA.eigenvalues₀ i : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ i)
      (RCLike.re (star u ⬝ᵥ (B *ᵥ u))) 0 := by
  have hM : ∀ t : ℝ, (A + t • B).IsHermitian := fun t ↦ hA.add (hB.smul (IsSelfAdjoint.all t))
  have hline (a b : n) : HasDerivAt (fun t : ℝ ↦ (A + t • B) a b) (B a b) 0 := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (B a b)).const_add (A a b)
  have h0 : A + (0 : ℝ) • B = A := by rw [zero_smul, add_zero]
  have h := hasFDerivAt_eigenvalues₀ hM (fun a b ↦ (hline a b).differentiableAt) (i := i)
    (by simpa [h0] using hi) (u := u) (by simpa [h0] using hu) hu1
  have hB' : (of fun a b ↦ fderiv ℝ (fun t : ℝ ↦ (A + t • B) a b) 0 1) = B := by
    ext a b
    rw [of_apply, (hline a b).hasFDerivAt.fderiv]
    simp
  convert h.hasDerivAt using 1
  rw [ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, sum_sum_smul_apply, hB']

end Matrix
