/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# The eigenbasis of the asymptotic operator of a nondegenerate loop

Let `F` be a finite-dimensional complex inner product space, such as `ℂⁿ`, with its standard
complex structure `J₀ = I`, its Euclidean inner product `Re ⟪·, ·⟫` and its symplectic form
`ω₀ = Im ⟪·, ·⟫`. For a continuous loop `S` of real-linear maps of `F` that are infinitesimally
symplectic, `ω₀(S_t v, w) + ω₀(v, S_t w) = 0`, the *asymptotic operator*

`A ζ = J₀ (ζ' - S_t ζ)`

acts from `H¹(F)` to `H⁰(F)`, as `I • CircleSobolev.loopOperator T S`. In Floer theory it is the
operator acting on the loops of a cylindrical end asymptotic to a periodic orbit, written in a
unitary trivialization along the orbit, in which the almost complex structure is `J₀`; the
linearized Floer operator on the end is `∂s + A`. This file shows that `A` is diagonalizable with
real eigenvalues bounded away from `0` when the loop is nondegenerate.

* **Symmetry.** For the real inner product of `H⁰`, `⟪A a, b⟫ = ⟪a, A b⟫` for `a, b ∈ H¹(F)`
  (`CircleSobolev.real_inner_I_smul_loopOperator_comm`). The derivative term is symmetric by
  integration by parts on the circle (`CircleSobolev.inner_derivative_inclusion`), since `J₀ d/dt`
  multiplies the `n`-th Fourier coefficient by the real number `-2πn/T`. The zero-order term
  `-J₀ S_t` is a pointwise symmetric multiplication operator, and Parseval's identity
  (`CircleSobolev.real_inner_ofContinuousMap`) turns its inner products into integrals over the
  circle.
* **Eigenbasis.** Suppose the loop is nondegenerate, that is, `L_S ζ = ζ' - S ζ` is invertible
  (by `CircleSobolev.isInvertible_loopOperator_iff`, exactly when `ζ' = S ζ` has no nonzero
  periodic solution). Then `A` is invertible, and its inverse followed by the inclusion
  `H¹ → H⁰` is a compact (Rellich), symmetric and injective operator `K` on `H⁰`. The spectral
  theorem for compact self-adjoint operators
  (`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero`) gives a Hilbert basis
  of `H⁰` of eigenvectors of `K` with nonzero eigenvalues `μ`. They lie in `H¹` and are
  eigenvectors of `A` with eigenvalues `λ = μ⁻¹`, and `|λ| ≥ (‖K‖ + 1)⁻¹`
  (`CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`).
* **Classical eigenfunctions.** An element `a ∈ H¹(F)` with continuous representative `ζ` is an
  eigenvector of `A` for the eigenvalue `λ` exactly when `ζ' = S_t ζ - λ J₀ ζ` holds classically
  (`CircleSobolev.I_smul_loopOperator_eq_smul_iff`), that is, `J₀ (ζ' - S_t ζ) = λ ζ`.

In the eigenbasis the stationary cylinder operator `∂s + A` splits into the scalar operators
`d/ds + λ`, one for each eigenvalue, each invertible on the line because `λ ≠ 0`, with inverses
bounded uniformly by the spectral gap. This decomposition is the standard route to the
invertibility of `∂s + A` at a nondegenerate orbit; the operators on the cylinder are not
treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the self-adjoint operator `J₀ ∂_t + S` on `W^{1,2}(S¹)` and the
  invertibility of `∂_s + A` at a nondegenerate orbit).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

noncomputable section

open Complex Module.End

universe u

namespace TauCeti

namespace CircleSobolev

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] (S : C(AddCircle T, F →L[ℝ] F))

/-- **The asymptotic operator is symmetric.** If every `S_t` is infinitesimally symplectic for the
standard symplectic form `ω₀ = Im ⟪·, ·⟫`, then `A = J₀ (d/dt - S_t)` is symmetric for the real
inner product of `H⁰`: `⟪A a, b⟫ = ⟪a, A b⟫` for `a, b ∈ H¹`, both regarded in `H⁰`. -/
theorem real_inner_I_smul_loopOperator_comm
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (a b : CircleSobolev 1 F) :
    inner ℝ (I • loopOperator T S a) (inclusion zero_le_one b) =
      inner ℝ (inclusion zero_le_one a) (I • loopOperator T S b) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hmul (c : CircleSobolev 1 F) : I • mulLoop T (by norm_num) S c =
      ofContinuousMap T (I • ContinuousMap.applyContinuousLinearMap S
        (toContinuousMap T (by norm_num) c)) := by
    rw [mulLoop_apply, map_smul]
  have hinc (c : CircleSobolev 1 F) :
      inclusion zero_le_one c = ofContinuousMap T (toContinuousMap T (by norm_num) c) :=
    (ofContinuousMap_toContinuousMap T _ c).symm
  simp only [loopOperator_apply, smul_sub, inner_sub_left, inner_sub_right]
  congr 1
  · -- The derivative term, by integration by parts.
    simp [real_inner_eq_re_inner, inner_smul_left, inner_smul_right, inner_derivative_inclusion]
  · -- The zero-order term, by Parseval's identity and the pointwise symmetry of `J₀ S_t`.
    rw [hmul, hmul, hinc, hinc, real_inner_ofContinuousMap, real_inner_ofContinuousMap]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [ContinuousMap.smul_apply, ContinuousMap.applyContinuousLinearMap_apply,
      inner_smul_left, inner_smul_right, conj_I, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul,
      one_mul, zero_sub]
    linarith [hS x (toContinuousMap T (by norm_num) a x) (toContinuousMap T (by norm_num) b x)]

/-- **The orthonormal eigenbasis of the asymptotic operator at a nondegenerate loop.** Let every
`S_t` be infinitesimally symplectic for `ω₀ = Im ⟪·, ·⟫`, and let `ζ ↦ ζ' - S ζ` be invertible
from `H¹` to `H⁰`. Then `H⁰`, with its real inner product, has a Hilbert basis `b` of
eigenvectors of `A = J₀ (d/dt - S_t)`: each `b i` is the image of some `a i ∈ H¹` with
`A (a i) = λ i • b i`, and the real eigenvalues satisfy `c ≤ |λ i|` for a constant `c > 0`. -/
theorem exists_hilbertBasis_I_smul_loopOperator_eq_smul
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ (CircleSobolev 0 F)) (a : ι → CircleSobolev 1 F)
      (lam : ι → ℝ) (c : ℝ), 0 < c ∧ ∀ i, inclusion zero_le_one (a i) = b i ∧
        c ≤ |lam i| ∧ I • loopOperator T S (a i) = lam i • b i := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨e, he⟩ := hL
  -- `R x = L_S⁻¹ (-J₀ x)` inverts `A`, and `K = R` followed by the inclusion is compact.
  set R : CircleSobolev 0 F →L[ℝ] CircleSobolev 1 F :=
    (e.symm : CircleSobolev 0 F →L[ℝ] CircleSobolev 1 F) ∘L
      ((-I) • ContinuousLinearMap.id ℝ (CircleSobolev 0 F)) with hR
  set K : CircleSobolev 0 F →L[ℝ] CircleSobolev 0 F :=
    (inclusion (E := F) zero_le_one).restrictScalars ℝ ∘L R with hK
  have hLR (x) : I • loopOperator T S (R x) = x := by
    rw [hR, ContinuousLinearMap.comp_apply, ← he]
    simp [smul_smul]
  have hKc : IsCompactOperator K :=
    (isCompactOperator_inclusion (E := F) zero_lt_one).comp_clm R
  have hKs : (K : CircleSobolev 0 F →ₗ[ℝ] CircleSobolev 0 F).IsSymmetric := fun x y ↦ by
    have h := real_inner_I_smul_loopOperator_comm T S hS (R x) (R y)
    rw [hLR, hLR] at h
    simpa [hK] using h.symm
  have hKi : LinearMap.ker (K : CircleSobolev 0 F →ₗ[ℝ] CircleSobolev 0 F) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx ↦ ?_
    rw [← hLR x, show R x = 0 from inclusion_injective zero_le_one (by simpa [hK] using hx)]
    simp
  obtain ⟨s, b, nu, hb, hnu0, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero hKc hKs hKi
  -- An eigenvector `x` of `K` for `μ ≠ 0` is the image of `μ⁻¹ R x`, an eigenvector of `A` for
  -- `μ⁻¹`, and `|μ| ≤ ‖K‖` since `‖x‖ = 1`.
  refine ⟨s, b, fun i ↦ (nu i)⁻¹ • R i, fun i ↦ (nu i)⁻¹, (‖K‖ + 1)⁻¹, by positivity,
    fun i ↦ ⟨?_, ?_, ?_⟩⟩
  · have h : K i = nu i • (i : CircleSobolev 0 F) := (hev i).apply_eq_smul
    rw [hb]
    calc inclusion zero_le_one ((nu i)⁻¹ • R i) = (nu i)⁻¹ • K i :=
          (inclusion zero_le_one).map_smul_of_tower _ _
      _ = i := by rw [h, smul_smul, inv_mul_cancel₀ (hnu0 i), one_smul]
  · have h : K i = nu i • (i : CircleSobolev 0 F) := (hev i).apply_eq_smul
    have hn : ‖(i : CircleSobolev 0 F)‖ = 1 := by
      rw [← hb]
      exact b.orthonormal.1 i
    have hle : |nu i| ≤ ‖K‖ := by
      simpa [h, norm_smul, hn] using K.le_opNorm i
    rw [abs_inv]
    exact inv_anti₀ (abs_pos.2 (hnu0 i)) (by linarith)
  · rw [map_smul, smul_comm, hLR, hb]

/-- **Eigenvectors of the asymptotic operator are classical eigenfunctions.** An element `a` of
`H¹` with continuous representative `ζ` satisfies `A a = λ a` for `A = J₀ (d/dt - S_t)` exactly
when `ζ' = S_t ζ - λ J₀ ζ` holds classically, that is, `J₀ (ζ' - S_t ζ) = λ ζ`. For `λ = 0` this is
`CircleSobolev.loopOperator_eq_zero_iff`. -/
theorem I_smul_loopOperator_eq_smul_iff (a : CircleSobolev 1 F) (lam : ℝ) :
    I • loopOperator T S a = lam • inclusion zero_le_one a ↔ ∀ x : ℝ,
      HasDerivAt (fun y : ℝ ↦ toContinuousMap T (by norm_num) a y)
        (S x (toContinuousMap T (by norm_num) a x) -
          lam • I • toContinuousMap T (by norm_num) a x) x := by
  have := FiniteDimensional.completeSpace ℂ F
  -- `A a = λ a` is `L_{S'} a = 0` for the shifted loop `S' = S - λ J₀`.
  set S' : C(AddCircle T, F →L[ℝ] F) :=
    S - lam • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ F) with hS'
  have hL : loopOperator T S' a =
      loopOperator T S a + ((lam : ℂ) * I) • inclusion zero_le_one a := by
    -- `L_S` is linear in the loop, and multiplication by the constant loop `J₀` is `J₀`.
    rw [hS', loopOperator_sub, add_apply, mulLoop_smul, smul_apply, mulLoop_const_smul_id,
      mul_smul, Complex.coe_smul]
  -- Multiplying by `-J₀` turns `J₀ y = λ z` into `y + λ J₀ z = 0`.
  have hiff (y z : CircleSobolev 0 F) (c : ℂ) : I • y = c • z ↔ y + (c * I) • z = 0 := by
    constructor
    · intro h
      have hy : y = (-I) • (I • y) := by rw [smul_smul]; simp
      rw [hy, h, smul_smul, ← add_smul, show -I * c + c * I = 0 by ring, zero_smul]
    · intro h
      rw [eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, ← neg_smul]
      congr 1
      linear_combination (-c) * I_sq
  rw [← Complex.coe_smul, hiff, ← hL, loopOperator_eq_zero_iff]
  simp [hS']

end CircleSobolev

end TauCeti
