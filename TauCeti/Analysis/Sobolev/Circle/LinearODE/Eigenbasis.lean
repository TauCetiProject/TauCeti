/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
import Mathlib.Analysis.Real.Cardinality
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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
real eigenvalues bounded away from `0` when the loop is nondegenerate, and that any infinitesimally
symplectic loop becomes nondegenerate after some real shift `S - δ J₀`.

* **Symmetry.** For the real inner product of `H⁰`, `⟪A a, b⟫ = ⟪a, A b⟫` for `a, b ∈ H¹(F)`
  (`CircleSobolev.real_inner_I_smul_loopOperator_comm`), and shifting `S` by a real multiple of the
  constant loop `J₀` preserves infinitesimal symplecticity
  (`CircleSobolev.im_inner_sub_smul_const_I_add_eq_zero`). The derivative term is symmetric by
  integration by parts on the circle (`CircleSobolev.inner_derivative_inclusion`), since `J₀ d/dt`
  multiplies the `n`-th Fourier coefficient by the real number `-2πn/T`. The zero-order term
  `-J₀ S_t` is a pointwise symmetric multiplication operator, and Parseval's identity
  (`CircleSobolev.real_inner_ofContinuousMap`) turns its inner products into integrals over the
  circle.
* **Eigenbasis.** Suppose the loop is nondegenerate, that is, `L_S ζ = ζ' - S ζ` is invertible
  (by `CircleSobolev.isInvertible_loopOperator_iff`, exactly when `ζ' = S ζ` has no nonzero
  periodic solution). Then `A` is invertible, and the compact-resolvent spectral theorem
  (`ContinuousLinearMap.exists_hilbertBasis_forall_apply_eq_smul_of_isCompactOperator_inclusion`)
  applied to the compact inclusion `H¹ → H⁰` (Rellich) and `A` gives a Hilbert basis of `H⁰` of
  eigenvectors of `A` lying in `H¹`, with real eigenvalues uniformly bounded away from `0`
  (`CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`).
* **Invertible spectral shifts.** Because `H⁰(F)` is separable, `A` has only countably many real
  eigenvalues (`ContinuousLinearMap.countable_setOf_exists_ne_zero_apply_eq_smul`), while
  `loopOperator` is Fredholm of index zero; hence there always exists `δ : ℝ` for which
  `loopOperator T (S - δ • const (I • id))` is invertible
  (`CircleSobolev.exists_isInvertible_loopOperator_sub_smul_const_I_id`).
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

/-- Shifting an infinitesimally symplectic loop `S` by a real multiple of `I • id` preserves
infinitesimal symplecticity for `ω₀(v, w) = Im ⟪v, w⟫`. -/
theorem im_inner_sub_smul_const_I_add_eq_zero (T : ℝ) {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) (δ : ℝ)
    (t : AddCircle T) (v w : F) :
    (inner ℂ
        ((S - δ • ContinuousMap.const (AddCircle T) (I • ContinuousLinearMap.id ℝ F)) t v) w).im +
      (inner ℂ v
        ((S - δ • ContinuousMap.const (AddCircle T) (I • ContinuousLinearMap.id ℝ F)) t w)).im =
      0 := by
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, Complex.sub_im]
  have h1 : (inner ℂ (δ • I • v) w).im = -δ * (inner ℂ v w).re := by
    rw [← Complex.coe_smul, inner_smul_left, inner_smul_left]
    simp
  have h2 : (inner ℂ v (δ • I • w)).im = δ * (inner ℂ v w).re := by
    rw [← Complex.coe_smul, inner_smul_right, inner_smul_right]
    simp
  rw [h1, h2]
  linarith [hS t v w]

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

omit hT [FiniteDimensional ℂ F] in
/-- Real multiples of an infinitesimally symplectic loop are infinitesimally symplectic. -/
theorem inner_smul_apply_im_add_inner_smul_apply_im_eq_zero
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) (τ : ℝ) :
    ∀ t v w, (inner ℂ ((τ • S) t v) w).im + (inner ℂ v ((τ • S) t w)).im = 0 := by
  intro t v w
  simp only [ContinuousMap.smul_apply, smul_apply, ← Complex.coe_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  linear_combination τ * hS t v w

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
  obtain ⟨s, b, a, lam, c, hc, hinc, hgap, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_apply_eq_smul_of_isCompactOperator_inclusion
      (ι := (inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (A := I • loopOperator T S)
      (isCompactOperator_inclusion (E := F) zero_lt_one)
      (inclusion_injective zero_le_one)
      (real_inner_I_smul_loopOperator_comm T S hS)
      ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).2 hL)
  exact ⟨s, b, a, lam, c, hc, fun i ↦ ⟨hinc i, hgap i, hev i⟩⟩

/-- **Existence of an invertible spectral shift.** For any continuous loop `S` of infinitesimally
symplectic real-linear maps on `F`, there exists a real shift `δ` such that the shifted loop
operator `loopOperator T (S - δ • const (I • id))` is invertible. -/
theorem exists_isInvertible_loopOperator_sub_smul_const_I_id
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ∃ δ : ℝ, (loopOperator T
      (S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ F))).IsInvertible := by
  have := FiniteDimensional.completeSpace ℂ F
  have : TopologicalSpace.SeparableSpace F :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  have : TopologicalSpace.SeparableSpace (lp (fun _ : ℤ ↦ F) 2) := lp.separableSpace (by norm_num)
  have : TopologicalSpace.SeparableSpace (CircleSobolev 0 F) :=
    (toℓ2ₗᵢ (s := 0) (E := F)).symm.surjective.denseRange.separableSpace
      (toℓ2ₗᵢ (s := 0) (E := F)).symm.continuous
  have hcount := ContinuousLinearMap.countable_setOf_exists_ne_zero_apply_eq_smul
    (ι := (inclusion (E := F) zero_le_one).restrictScalars ℝ) (A := I • loopOperator T S)
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
  obtain ⟨δ, hδ⟩ := Set.nonempty_compl.2 fun h ↦ Cardinal.not_countable_real (h ▸ hcount)
  refine ⟨δ, (isFredholm_loopOperator T _).isInvertible_of_injective_of_index_eq_zero
    ((injective_iff_map_eq_zero _).2 fun a ha ↦ by_contra fun ha0 ↦ hδ ⟨a, ha0, sub_eq_zero.1 ?_⟩)
    (index_loopOperator T _)⟩
  simpa only [smul_apply, sub_apply, ha, smul_zero] using
    (congrArg (fun L ↦ L a) (I_smul_loopOperator_sub_smul_const_I T S δ)).symm

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
  set S' : C(AddCircle T, F →L[ℝ] F) :=
    S - lam • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ F) with hS'
  have hshift : I • loopOperator T S' a = I • loopOperator T S a - lam • inclusion zero_le_one a :=
    congrArg (fun L ↦ L a) (I_smul_loopOperator_sub_smul_const_I T S lam)
  rw [← sub_eq_zero, ← hshift, smul_eq_zero, or_iff_right I_ne_zero, loopOperator_eq_zero_iff]
  simp [hS']

end CircleSobolev

end TauCeti
