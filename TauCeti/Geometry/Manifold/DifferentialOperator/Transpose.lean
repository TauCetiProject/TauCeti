/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Probability.Density

/-!
# The formal transpose of a differential operator on a finite-dimensional space

Let `E` be a finite-dimensional real normed space and `μ` a measure on `E`. A linear operator
`D'` on the algebra `C^∞(E)` of smooth real functions is a *formal transpose* of `D` with respect
to `μ` (`TauCeti.IsFormalTranspose`) if

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all compactly supported smooth `f` and `g`. This is the bilinear integration-by-parts adjoint
of differential operators, which extends them to distributions by duality and, for a metric,
gives the formal adjoints entering Laplace-type operators such as `∇*∇`.

For a Haar measure `μ` (Lebesgue measure up to a constant) every differential operator `D` of
order at most `m`, in Grothendieck's sense of iterated commutators with multiplication operators
(`TauCeti.differentialOperators`), has a unique formal transpose that is itself a differential
operator, and this transpose again has order at most `m`. In coordinates
`D f = ∑_α c_α ∂^α f` it is `g ↦ ∑_α (-1)^|α| ∂^α (c_α g)`: multiplication operators are their own
transposes, a directional derivative `∂_v` has transpose `-∂_v` by integration by parts, and
transposition reverses composition. Uniqueness uses that a differential operator is determined by
its values on compactly supported functions, since it is local.

For a smooth positive density `ρ`, that is for the measure `ρ μ`, the transpose is
`g ↦ ρ⁻¹ Dᵗ (ρ g)`, where `Dᵗ` is the transpose for `μ` (`TauCeti.formalTranspose_withDensity`).

## Main definitions

* `TauCeti.IsFormalTranspose μ D D'`: `D'` is a formal transpose of `D` with respect to `μ`.
* `TauCeti.formalTranspose μ D`: the formal transpose of a differential operator `D`.

## Main results

* `TauCeti.exists_isFormalTranspose`: for a Haar measure, a differential operator of order at most
  `m` has a formal transpose that is a differential operator of order at most `m`.
* `TauCeti.IsFormalTranspose.eq_of_mem_differentialOperators`: formal transposes that are
  differential operators are unique.
* `TauCeti.formalTranspose_formalTranspose`, `TauCeti.formalTranspose_comp`: transposition is an
  involution and reverses composition.
* `TauCeti.formalTranspose_lineDerivation`, `TauCeti.formalTranspose_mulLeft`: the transposes of
  `∂_v` and of multiplication by a smooth function `c`; with
  `TauCeti.formalTranspose_mulLeft_comp_lineDerivation`, the transpose of `c ∂_v` is
  `-c ∂_v - ∂_v c`.
* `TauCeti.isFormalTranspose_withDensity_iff`, `TauCeti.formalTranspose_withDensity`: transposes
  for a smooth positive density.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer (the
  transpose `ᵗP` of a differential operator with smooth coefficients, characterized by
  integration by parts against test functions).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (differential operators as local operators).
-/

public section

noncomputable section

open MeasureTheory Filter Finset
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-! ### Formal transposes -/

section IsFormalTranspose

variable {D D' D₁ D₂ D₁' D₂' P P' Q Q' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

variable (μ) in
/-- `D'` is a **formal transpose** of the linear operator `D` on smooth functions with respect to
the measure `μ`: `∫ (D f) g dμ = ∫ f (D' g) dμ` for all compactly supported smooth `f` and `g`. -/
def IsFormalTranspose (D D' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Prop :=
  ∀ f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f → HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

/-- The defining property of a formal transpose. -/
theorem isFormalTranspose_iff :
    IsFormalTranspose μ D D' ↔ ∀ f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f →
      HasCompactSupport g → ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  Iff.rfl

/-- Formal transposition is symmetric: if `D'` is a formal transpose of `D`, then `D` is a formal
transpose of `D'`. -/
theorem IsFormalTranspose.symm (h : IsFormalTranspose μ D D') : IsFormalTranspose μ D' D :=
  fun f g hf hg ↦ by simpa only [mul_comm] using (h g f hg hf).symm

theorem isFormalTranspose_comm : IsFormalTranspose μ D D' ↔ IsFormalTranspose μ D' D :=
  ⟨IsFormalTranspose.symm, IsFormalTranspose.symm⟩

/-- The zero operator is its own formal transpose. -/
theorem isFormalTranspose_zero : IsFormalTranspose μ 0 0 :=
  fun _ _ _ _ ↦ by simp

/-- The identity is its own formal transpose. -/
theorem isFormalTranspose_id : IsFormalTranspose μ LinearMap.id LinearMap.id :=
  fun _ _ _ _ ↦ rfl

/-- Multiplication by a smooth function is its own formal transpose. -/
theorem isFormalTranspose_mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    IsFormalTranspose μ (LinearMap.mulLeft ℝ c) (LinearMap.mulLeft ℝ c) :=
  fun f g _ _ ↦ integral_congr_ae <| ae_of_all _ fun x ↦ by
    simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
    ring

/-- Formal transposition commutes with real scalar multiplication. -/
theorem IsFormalTranspose.smul (h : IsFormalTranspose μ D D') (r : ℝ) :
    IsFormalTranspose μ (r • D) (r • D') := fun f g hf hg ↦ by
  simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    mul_left_comm _ r, integral_const_mul, h f g hf hg]

/-- Formal transposition commutes with negation. -/
theorem IsFormalTranspose.neg (h : IsFormalTranspose μ D D') : IsFormalTranspose μ (-D) (-D') :=
  fun f g hf hg ↦ by
    simp only [LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply, neg_mul, mul_neg,
      integral_neg, h f g hf hg]

/-- **Transposition reverses composition**: if `P'` and `Q'` are formal transposes of `P` and
`Q`, then `Q' ∘ P'` is a formal transpose of `P ∘ Q`, provided `Q` and `P'` preserve compact
supports. -/
theorem IsFormalTranspose.comp (hP : IsFormalTranspose μ P P') (hQ : IsFormalTranspose μ Q Q')
    (hQs : ∀ f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f → HasCompactSupport (Q f))
    (hP's : ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport g → HasCompactSupport (P' g)) :
    IsFormalTranspose μ (P ∘ₗ Q) (Q' ∘ₗ P') := fun f g hf hg ↦ by
  rw [LinearMap.comp_apply, hP _ _ (hQs f hf) hg, hQ _ _ hf (hP's g hg), LinearMap.comp_apply]

variable [BorelSpace E]

/-- The product of a smooth function and a compactly supported smooth function is integrable. -/
private theorem integrable_mul_of_hasCompactSupport_right [IsFiniteMeasureOnCompacts μ]
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hg : HasCompactSupport g) :
    Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport hg.mul_left

private theorem integrable_mul_of_hasCompactSupport_left [IsFiniteMeasureOnCompacts μ]
    {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : HasCompactSupport f) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport hf.mul_right

/-- Formal transposition is additive, for a measure that is finite on compact sets. -/
theorem IsFormalTranspose.add [IsFiniteMeasureOnCompacts μ] (h₁ : IsFormalTranspose μ D₁ D₁')
    (h₂ : IsFormalTranspose μ D₂ D₂') : IsFormalTranspose μ (D₁ + D₂) (D₁' + D₂') :=
  fun f g hf hg ↦ by
    simp only [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, add_mul, mul_add]
    rw [integral_add (integrable_mul_of_hasCompactSupport_right _ hg)
        (integrable_mul_of_hasCompactSupport_right _ hg),
      integral_add (integrable_mul_of_hasCompactSupport_left hf _)
        (integrable_mul_of_hasCompactSupport_left hf _), h₁ f g hf hg, h₂ f g hf hg]

/-- Formal transposition commutes with subtraction. -/
theorem IsFormalTranspose.sub [IsFiniteMeasureOnCompacts μ] (h₁ : IsFormalTranspose μ D₁ D₁')
    (h₂ : IsFormalTranspose μ D₂ D₂') : IsFormalTranspose μ (D₁ - D₂) (D₁' - D₂') := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Formal transposition commutes with finite sums. -/
theorem IsFormalTranspose.sum [IsFiniteMeasureOnCompacts μ] {ι : Type*} (s : Finset ι)
    {D D' : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h : ∀ i ∈ s, IsFormalTranspose μ (D i) (D' i)) :
    IsFormalTranspose μ (∑ i ∈ s, D i) (∑ i ∈ s, D' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isFormalTranspose_zero
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj ↦ h j (mem_insert_of_mem hj))

variable [FiniteDimensional ℝ E]

/-- **Integration by parts**: for a Haar measure, the formal transpose of the directional
derivative `∂_v` is `-∂_v`. -/
theorem isFormalTranspose_lineDerivation [μ.IsAddHaarMeasure] (v : E) :
    IsFormalTranspose μ (lineDerivation ℝ v) (-lineDerivation ℝ v) := fun f g hf hg ↦ by
  have hf' : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  have hg' : ContDiff ℝ ∞ g := g.contMDiff.contDiff
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := v)
    (by simpa using integrable_mul_of_hasCompactSupport_right (lineDerivation ℝ v f) hg)
    (by simpa using integrable_mul_of_hasCompactSupport_left hf (lineDerivation ℝ v g))
    (integrable_mul_of_hasCompactSupport_left hf g)
    (fun x _ ↦ hf'.differentiable (by simp) x) (fun x _ ↦ hg'.differentiable (by simp) x)
  simp only [Derivation.coeFn_coe, LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply,
    lineDerivation_apply_apply, mul_neg, integral_neg, h, neg_neg]

omit [BorelSpace E] in
/-- **Transposition reverses composition** of differential operators: if `P'` and `Q'` are
formal transposes of `P` and `Q`, and `Q` and `P'` are differential operators, then `Q' ∘ P'` is a
formal transpose of `P ∘ Q`. -/
theorem IsFormalTranspose.comp_of_mem_differentialOperators {k l : ℕ}
    (hP : IsFormalTranspose μ P P') (hQ : IsFormalTranspose μ Q Q')
    (hQm : Q ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hP'm : P' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) :
    IsFormalTranspose μ (P ∘ₗ Q) (Q' ∘ₗ P') :=
  hP.comp hQ (fun _ ↦ hasCompactSupport_apply_of_mem_differentialOperators hQm)
    (fun _ ↦ hasCompactSupport_apply_of_mem_differentialOperators hP'm)

end IsFormalTranspose

/-! ### Existence for Haar measures -/

section Existence

variable [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- The monomial `∂^α` in the partial derivatives along a basis has a formal transpose that is a
differential operator of order at most `|α|`. -/
private theorem exists_isFormalTranspose_multiIndexDeriv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (α : ι → ℕ) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (∑ i, α i),
      IsFormalTranspose μ (multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
        (fun i j ↦ commute_lineDerivation (b i) (b j)) α) D' := by
  classical
  set d := fun i ↦ lineDerivation ℝ (b i)
  obtain ⟨N, hN⟩ : ∃ N, ∑ i, α i = N := ⟨_, rfl⟩
  induction N generalizing α with
  | zero =>
    obtain rfl : α = 0 := funext fun i ↦ by simpa using (sum_eq_zero_iff.mp hN) i (mem_univ i)
    refine ⟨1, ?_, ?_⟩
    · simpa using mem_differentialOperators_zero_iff.2 fun (_ _ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ↦ rfl
    · rw [multiIndexDeriv_zero]
      exact isFormalTranspose_id
  | succ N ih =>
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := α) (by omega)
    set β := Function.update α i (α i - 1)
    have hαβ : α = β + Pi.single i 1 := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same, β]
        omega
      · simp [β, hj]
    have hβ : ∑ j, β j = N := by
      have := congrArg (fun γ : ι → ℕ ↦ ∑ j, γ j) hαβ
      simp only [Pi.add_apply, sum_add_distrib, sum_pi_single', mem_univ, ite_true] at this
      omega
    obtain ⟨T, hTm, hT⟩ := ih β hβ
    refine ⟨-(d i : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ T, ?_, ?_⟩
    · rw [hN, add_comm N 1]
      exact comp_mem_differentialOperators (neg_mem (Derivation.mem_differentialOperators_one _))
        (hβ ▸ hTm)
    · rw [hαβ, multiIndexDeriv_add_single]
      exact hT.comp_of_mem_differentialOperators (isFormalTranspose_lineDerivation (b i))
        (Derivation.mem_differentialOperators_one _) (hβ ▸ hTm)

/-- **Existence of formal transposes.** For a Haar measure `μ`, a differential operator of order
at most `m` on `C^∞(E)` has a formal transpose with respect to `μ` that is again a differential
operator of order at most `m`. -/
theorem exists_isFormalTranspose {m : ℕ} {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m, IsFormalTranspose μ D D' := by
  classical
  set b := Module.finBasis ℝ E
  obtain ⟨c, rfl⟩ := b.mem_differentialOperators_iff_exists_eq_coordinateOperator.mp hD
  -- Write the coordinate expression as a sum of multiplication operators composed with monomials.
  set term : (Fin (Module.finrank ℝ E) → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ :=
    fun α ↦ LinearMap.mulLeft ℝ (c α) ∘ₗ multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
      (fun i j ↦ commute_lineDerivation (b i) (b j)) α
  have hsum : coordinateOperator (fun i ↦ lineDerivation ℝ (b i))
      (fun i j ↦ commute_lineDerivation (b i) (b j)) m c =
        ∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k, term α := by
    ext f x
    simp [term, coordinateOperator_apply, mul_comm]
  have hterm : ∀ k ∈ range (m + 1), ∀ α ∈ piAntidiag univ k,
      ∃ T ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m, IsFormalTranspose μ (term α) T := by
    intro k hk α hα
    rw [mem_piAntidiag] at hα
    obtain ⟨T, hTm, hT⟩ := exists_isFormalTranspose_multiIndexDeriv (μ := μ) b α
    refine ⟨T ∘ₗ LinearMap.mulLeft ℝ (c α), ?_, ?_⟩
    · refine differentialOperators_mono (show k + 0 ≤ m by simpa [Nat.lt_succ_iff] using hk) ?_
      exact comp_mem_differentialOperators (hα.1 ▸ hTm) (mulLeft_mem_differentialOperators_zero _)
    · exact (isFormalTranspose_mulLeft (c α)).comp hT
        (fun _ ↦ hasCompactSupport_apply_of_mem_differentialOperators
          (multiIndexDeriv_mem_differentialOperators _ _ α))
        (fun _ hg ↦ hg.mul_left)
  choose! T hTm hT using hterm
  refine ⟨∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k, T k α,
    sum_mem fun k hk ↦ sum_mem fun α hα ↦ hTm k hk α hα, ?_⟩
  rw [hsum]
  exact IsFormalTranspose.sum _ fun k hk ↦ IsFormalTranspose.sum _ fun α hα ↦ hT k hk α hα

end Existence

/-! ### Uniqueness -/

section Uniqueness

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace E] in
/-- A differential operator on `C^∞(E)` is determined by its values on compactly supported
functions: two differential operators agreeing there are equal, since they are local. -/
theorem eq_of_forall_hasCompactSupport_apply_eq {m₁ m₂ : ℕ}
    {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m₁)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m₂)
    (h : ∀ f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f → D₁ f = D₂ f) : D₁ = D₂ := by
  refine LinearMap.ext fun g ↦ ContMDiffMap.ext fun x ↦ ?_
  -- Cut `g` off by a bump function equal to one near `x`.
  let χ : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨χ, χ.contDiff.contMDiff⟩
  have hφg : ((φ * g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : E → ℝ) =ᶠ[𝓝 x] g := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coeFn_mk, hy, Pi.one_apply, one_mul]
  have hint : (𝓘(ℝ, E)).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  rw [← differentialOperators_apply_eq_of_eventuallyEq hD₁ hint hφg,
    ← differentialOperators_apply_eq_of_eventuallyEq hD₂ hint hφg,
    h _ (χ.hasCompactSupport.mul_right (f' := g))]

variable [BorelSpace E]

/-- **Uniqueness of formal transposes.** For a measure that is finite on compact sets and positive
on nonempty open sets, such as a Haar measure, two formal transposes of the same operator that are
differential operators are equal. -/
theorem IsFormalTranspose.eq_of_mem_differentialOperators [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {m₁ m₂ : ℕ} {D D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h₁ : IsFormalTranspose μ D D₁) (h₂ : IsFormalTranspose μ D D₂)
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m₁)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m₂) :
    D₁ = D₂ := by
  refine eq_of_forall_hasCompactSupport_apply_eq hD₁ hD₂ fun g hg ↦ ?_
  have hcont : Continuous fun x ↦ D₁ g x - D₂ g x :=
    (D₁ g).contMDiff.continuous.sub (D₂ g).contMDiff.continuous
  -- The difference `D₁ g - D₂ g` integrates to zero against every test function.
  have hae : ∀ᵐ x ∂μ, D₁ g x - D₂ g x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨φ, hφ.contMDiff⟩
    have hf : HasCompactSupport f := hφc
    have e₁ : ∫ x, D f x * g x ∂μ = ∫ x, φ x * D₁ g x ∂μ := h₁ f g hf hg
    have e₂ : ∫ x, D f x * g x ∂μ = ∫ x, φ x * D₂ g x ∂μ := h₂ f g hf hg
    have i₁ : Integrable (fun x ↦ φ x * D₁ g x) μ :=
      integrable_mul_of_hasCompactSupport_left hf (D₁ g)
    have i₂ : Integrable (fun x ↦ φ x * D₂ g x) μ :=
      integrable_mul_of_hasCompactSupport_left hf (D₂ g)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub i₁ i₂, ← e₁, ← e₂, sub_self]
  have hzero := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).mp hae
  exact ContMDiffMap.ext fun x ↦ sub_eq_zero.mp (congrFun hzero x)

end Uniqueness

/-! ### The formal transpose -/

section FormalTranspose

variable {m k l : ℕ} {D D' P Q : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

open Classical in
variable (μ) in
/-- The **formal transpose** `Dᵗ` of a linear operator `D` on `C^∞(E)` with respect to the
measure `μ`: a differential operator with `∫ (D f) g dμ = ∫ f (Dᵗ g) dμ` for all compactly
supported smooth `f` and `g`, if there is one, and `0` otherwise. For a Haar measure and a
differential operator `D` of order at most `m` it exists, is unique and has order at most `m`
(`TauCeti.isFormalTranspose_formalTranspose`, `TauCeti.IsFormalTranspose.formalTranspose_eq`,
`TauCeti.formalTranspose_mem_differentialOperators`). -/
def formalTranspose (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ :=
  if h : ∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) ∧ IsFormalTranspose μ D D' then h.choose else 0

/-- If `D` has a formal transpose that is a differential operator, then `formalTranspose μ D` is
one. -/
private theorem formalTranspose_spec
    (h : ∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) ∧ IsFormalTranspose μ D D') :
    (∃ m, formalTranspose μ D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) ∧ IsFormalTranspose μ D (formalTranspose μ D) := by
  classical
  rw [formalTranspose, dite_eq_left h]
  exact h.choose_spec

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- **Characterization of the formal transpose**: every formal transpose of `D` that is a
differential operator is `formalTranspose μ D`. -/
theorem IsFormalTranspose.formalTranspose_eq [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (h : IsFormalTranspose μ D D')
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    formalTranspose μ D = D' := by
  obtain ⟨⟨m, hm⟩, hT⟩ := formalTranspose_spec ⟨D', ⟨k, hD'⟩, h⟩
  exact hT.eq_of_mem_differentialOperators h hm hD'

variable [μ.IsAddHaarMeasure]

/-- For a Haar measure, the formal transpose of a differential operator is a formal transpose. -/
theorem isFormalTranspose_formalTranspose
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    IsFormalTranspose μ D (formalTranspose μ D) := by
  obtain ⟨D', hD', h⟩ := exists_isFormalTranspose (μ := μ) hD
  rw [h.formalTranspose_eq hD']
  exact h

/-- The formal transpose of a differential operator of order at most `m` has order at most `m`. -/
theorem formalTranspose_mem_differentialOperators
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    formalTranspose μ D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m := by
  obtain ⟨D', hD', h⟩ := exists_isFormalTranspose (μ := μ) hD
  rwa [h.formalTranspose_eq hD']

/-- Formal transposition is an involution on differential operators. -/
theorem formalTranspose_formalTranspose
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    formalTranspose μ (formalTranspose μ D) = D :=
  (isFormalTranspose_formalTranspose hD).symm.formalTranspose_eq hD

/-- Formal transposition reverses composition of differential operators. -/
theorem formalTranspose_comp
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) :
    formalTranspose μ (P ∘ₗ Q) = formalTranspose μ Q ∘ₗ formalTranspose μ P :=
  ((isFormalTranspose_formalTranspose hP).comp_of_mem_differentialOperators
    (isFormalTranspose_formalTranspose hQ) hQ
    (formalTranspose_mem_differentialOperators hP)).formalTranspose_eq
    (comp_mem_differentialOperators (formalTranspose_mem_differentialOperators hQ)
      (formalTranspose_mem_differentialOperators hP))

/-- Formal transposition is additive on differential operators. -/
theorem formalTranspose_add
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) :
    formalTranspose μ (P + Q) = formalTranspose μ P + formalTranspose μ Q :=
  ((isFormalTranspose_formalTranspose hP).add
    (isFormalTranspose_formalTranspose hQ)).formalTranspose_eq
    (add_mem (differentialOperators_mono le_sup_left (formalTranspose_mem_differentialOperators hP))
      (differentialOperators_mono (le_sup_right (a := k))
        (formalTranspose_mem_differentialOperators hQ)))

/-- Formal transposition commutes with real scalar multiplication. -/
theorem formalTranspose_smul (r : ℝ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    formalTranspose μ (r • D) = r • formalTranspose μ D :=
  ((isFormalTranspose_formalTranspose hD).smul r).formalTranspose_eq
    (Submodule.smul_mem _ r (formalTranspose_mem_differentialOperators hD))

/-- Multiplication by a smooth function is its own formal transpose. -/
@[simp]
theorem formalTranspose_mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    formalTranspose μ (LinearMap.mulLeft ℝ c) = LinearMap.mulLeft ℝ c :=
  (isFormalTranspose_mulLeft c).formalTranspose_eq (mulLeft_mem_differentialOperators_zero c)

/-- The formal transpose of the directional derivative `∂_v` is `-∂_v`. -/
@[simp]
theorem formalTranspose_lineDerivation (v : E) :
    formalTranspose μ (lineDerivation ℝ v) = -lineDerivation ℝ v :=
  (isFormalTranspose_lineDerivation v).formalTranspose_eq
    (neg_mem (Derivation.mem_differentialOperators_one _))

/-- The formal transpose of the first-order operator `c ∂_v` is `-c ∂_v - (∂_v c)`: on the line
with `c(x) = x`, the transpose of `x ∂` is `-x ∂ - 1`, not merely `-x ∂`. -/
theorem formalTranspose_mulLeft_comp_lineDerivation (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (v : E) :
    formalTranspose μ (LinearMap.mulLeft ℝ c ∘ₗ lineDerivation ℝ v) =
      -(LinearMap.mulLeft ℝ c ∘ₗ lineDerivation ℝ v) -
        LinearMap.mulLeft ℝ (lineDerivation ℝ v c) := by
  rw [formalTranspose_comp (mulLeft_mem_differentialOperators_zero c)
    (Derivation.mem_differentialOperators_one _), formalTranspose_lineDerivation,
    formalTranspose_mulLeft]
  ext g x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  simp only [ContMDiffMap.coe_neg, ContMDiffMap.coe_sub, ContMDiffMap.coe_add,
    ContMDiffMap.coe_mul, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

end FormalTranspose

/-! ### Densities -/

section Density

variable [BorelSpace E]

variable {D D' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

/-- **Formal transposes for a density.** Let `ρ` be a nonnegative unit of `C^∞(E)`, that is a
smooth positive density. Then `D'` is a formal transpose of `D` for the measure `ρ μ` if and only
if `ρ D' ρ⁻¹` is a formal transpose of `D` for `μ`. -/
theorem isFormalTranspose_withDensity_iff (ρ : (C^∞⟮𝓘(ℝ, E), E; ℝ⟯)ˣ)
    (hρ : ∀ x, 0 ≤ (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x) :
    IsFormalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x)) D D' ↔
      IsFormalTranspose μ D
        (LinearMap.mulLeft ℝ (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ D' ∘ₗ LinearMap.mulLeft ℝ ↑ρ⁻¹) := by
  have hρρ (x : E) : (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x * (↑ρ⁻¹ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x = 1 := by
    simpa only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_one, Pi.one_apply] using
      congrArg (fun φ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ ↦ φ x) ρ.mul_inv
  simp only [isFormalTranspose_iff, Probability.integral_withDensity_ofReal
    (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯).contMDiff.continuous.aemeasurable (ae_of_all _ hρ), smul_eq_mul,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  constructor
  · intro h f g hf hg
    have key := h f (↑ρ⁻¹ * g) hf hg.mul_left
    simp only [ContMDiffMap.coe_mul, Pi.mul_apply] at key
    calc ∫ x, D f x * g x ∂μ
        = ∫ x, (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x * (D f x * ((↑ρ⁻¹ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x * g x)) ∂μ := by
          congr 1 with x
          linear_combination (-(D f x * g x)) * hρρ x
      _ = _ := key
      _ = _ := by congr 1 with x; ring
  · intro h f g hf hg
    have key := h f (↑ρ * g) hf hg.mul_left
    simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Units.inv_mul_cancel_left] at key
    calc ∫ x, (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x * (D f x * g x) ∂μ
        = ∫ x, D f x * ((ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x * g x) ∂μ := by congr 1 with x; ring
      _ = _ := key
      _ = _ := by congr 1 with x; ring

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] {m : ℕ}

/-- **The formal transpose for a density.** For a Haar measure `μ` and a smooth positive density
`ρ`, the formal transpose of a differential operator `D` with respect to `ρ μ` is
`g ↦ ρ⁻¹ Dᵗ (ρ g)`, where `Dᵗ` is its formal transpose with respect to `μ`. -/
theorem formalTranspose_withDensity (ρ : (C^∞⟮𝓘(ℝ, E), E; ℝ⟯)ˣ)
    (hρ : ∀ x, 0 ≤ (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x)
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    formalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x)) D =
      LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ formalTranspose μ D ∘ₗ LinearMap.mulLeft ℝ ↑ρ := by
  -- Multiplication by `ρ` and by `ρ⁻¹` are inverse operators of order `0`.
  have hM : LinearMap.mulLeft ℝ (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑ρ⁻¹ =
      LinearMap.id := by
    rw [← LinearMap.mulLeft_mul, ρ.mul_inv, LinearMap.mulLeft_one]
  have hM' : LinearMap.mulLeft ℝ (↑ρ⁻¹ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑ρ =
      LinearMap.id := by
    rw [← LinearMap.mulLeft_mul, ρ.inv_mul, LinearMap.mulLeft_one]
  have hL : ∀ X : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      LinearMap.mulLeft ℝ (ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ X = X := by
    intro X
    rw [← LinearMap.comp_assoc, hM, LinearMap.id_comp]
  have hL' : ∀ X : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      LinearMap.mulLeft ℝ (↑ρ⁻¹ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑ρ ∘ₗ X = X := by
    intro X
    rw [← LinearMap.comp_assoc, hM', LinearMap.id_comp]
  have hm : ∀ u : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, LinearMap.mulLeft ℝ u ∈ differentialOperators ℝ
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
    mulLeft_mem_differentialOperators_zero
  have hR : IsFormalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) x))
      D (LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ formalTranspose μ D ∘ₗ LinearMap.mulLeft ℝ ↑ρ) := by
    rw [isFormalTranspose_withDensity_iff ρ hρ]
    simpa only [LinearMap.comp_assoc, hM, hL, LinearMap.comp_id] using
      isFormalTranspose_formalTranspose (μ := μ) hD
  have hRm : LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ formalTranspose μ D ∘ₗ LinearMap.mulLeft ℝ ↑ρ ∈
      differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
        (0 + (m + 0)) := comp_mem_differentialOperators (hm _)
    (comp_mem_differentialOperators (formalTranspose_mem_differentialOperators (μ := μ) hD)
      (hm _))
  obtain ⟨⟨k, hS⟩, hSt⟩ := formalTranspose_spec ⟨_, ⟨_, hRm⟩, hR⟩
  -- Both transposes for `ρ μ` conjugate to transposes for `μ`, which are unique.
  have key := ((isFormalTranspose_withDensity_iff ρ hρ).mp hSt).eq_of_mem_differentialOperators
    ((isFormalTranspose_withDensity_iff ρ hρ).mp hR)
    (comp_mem_differentialOperators (hm _) (comp_mem_differentialOperators hS (hm _)))
    (comp_mem_differentialOperators (hm _) (comp_mem_differentialOperators hRm (hm _)))
  have := congrArg (fun T ↦ LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ T ∘ₗ LinearMap.mulLeft ℝ ↑ρ) key
  simpa only [LinearMap.comp_assoc, hM', hL', LinearMap.comp_id] using this

end Density

end TauCeti
