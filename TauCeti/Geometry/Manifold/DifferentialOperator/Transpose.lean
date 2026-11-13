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
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Probability.Density

/-!
# The formal transpose of a differential operator

Let `M` be a real manifold and `μ` a measure on `M`. A linear operator `D'` on the algebra
`C^∞(M)` of smooth real functions is a *formal transpose* of `D` with respect to `μ`
(`TauCeti.IsFormalTranspose`) if

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all compactly supported smooth `f` and `g`. This is the bilinear integration-by-parts adjoint
of differential operators, which extends them to distributions by duality and, for a metric,
gives the formal adjoints entering Laplace-type operators such as `∇*∇`.

Formal transposes that are differential operators are unique when `M` is finite-dimensional and
`μ` is finite on compact sets and positive on nonempty open sets, since a differential operator is
local and hence determined by its values on compactly supported functions. On a
finite-dimensional real normed space `E` with a Haar measure `μ` (Lebesgue measure up to a
constant) every differential operator `D` of order at most `m`, in Grothendieck's sense of
iterated commutators with multiplication operators (`TauCeti.differentialOperators`), has a formal
transpose that is itself a differential operator, and this transpose again has order at most `m`.
In coordinates `D f = ∑_α c_α ∂^α f` it is `g ↦ ∑_α (-1)^|α| ∂^α (c_α g)`: multiplication
operators are their own transposes, a directional derivative `∂_v` has transpose `-∂_v` by
integration by parts, and transposition reverses composition.

For a smooth positive density `ρ`, that is for the measure `ρ μ`, the transpose is
`g ↦ ρ⁻¹ Dᵗ (ρ g)`, where `Dᵗ` is the transpose for `μ` (`TauCeti.formalTranspose_withDensity`).

## Main definitions

* `TauCeti.IsFormalTranspose μ D D'`: `D'` is a formal transpose of `D` with respect to `μ`.
* `TauCeti.formalTranspose μ D`: the formal transpose of a differential operator `D`.

## Main results

* `TauCeti.exists_isFormalTranspose`: for a Haar measure, a differential operator of order at most
  `m` has a formal transpose that is a differential operator of order at most `m`.
* `TauCeti.IsFormalTranspose.eq_of_mem_differentialOperators`: on a finite-dimensional manifold,
  formal transposes that are differential operators are unique.
* `TauCeti.isFormalTranspose_multiIndexDeriv`: the transpose of `∂^α` is `(-1)^|α| ∂^α`.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Formal transposes -/

section IsFormalTranspose

variable [MeasurableSpace M] {μ : Measure M}
  {D D' D₁ D₂ D₁' D₂' P P' Q Q' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}

variable (μ) in
/-- `D'` is a **formal transpose** of the linear operator `D` on smooth functions with respect to
the measure `μ`: `∫ (D f) g dμ = ∫ f (D' g) dμ` for all compactly supported smooth `f` and `g`. -/
def IsFormalTranspose (D D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) : Prop :=
  ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f → HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

/-- The defining property of a formal transpose. -/
theorem isFormalTranspose_iff :
    IsFormalTranspose μ D D' ↔ ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f →
      HasCompactSupport g → ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  Iff.rfl

/-- **Integration by parts** against a formal transpose, for compactly supported smooth `f` and
`g`. -/
theorem IsFormalTranspose.integral_mul_eq (h : IsFormalTranspose μ D D') {f g : C^∞⟮I, M; ℝ⟯}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  h f g hf hg

/-- Formal transposition is symmetric: if `D'` is a formal transpose of `D`, then `D` is a formal
transpose of `D'`. -/
@[symm]
theorem IsFormalTranspose.symm (h : IsFormalTranspose μ D D') : IsFormalTranspose μ D' D :=
  fun f g hf hg ↦ by simpa only [mul_comm] using (h g f hg hf).symm

theorem isFormalTranspose_comm : IsFormalTranspose μ D D' ↔ IsFormalTranspose μ D' D :=
  ⟨IsFormalTranspose.symm, IsFormalTranspose.symm⟩

/-- The zero operator is its own formal transpose. -/
@[simp]
theorem isFormalTranspose_zero : IsFormalTranspose μ (0 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) 0 :=
  fun _ _ _ _ ↦ by simp

/-- The identity is its own formal transpose. -/
@[simp]
theorem isFormalTranspose_id :
    IsFormalTranspose μ (LinearMap.id : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) LinearMap.id :=
  fun _ _ _ _ ↦ rfl

/-- The identity is its own formal transpose. -/
@[simp]
theorem isFormalTranspose_one : IsFormalTranspose μ (1 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) 1 :=
  isFormalTranspose_id

/-- Multiplication by a smooth function is its own formal transpose. -/
@[simp]
theorem isFormalTranspose_mulLeft (c : C^∞⟮I, M; ℝ⟯) :
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
    (hQs : ∀ f : C^∞⟮I, M; ℝ⟯, HasCompactSupport f → HasCompactSupport (Q f))
    (hP's : ∀ g : C^∞⟮I, M; ℝ⟯, HasCompactSupport g → HasCompactSupport (P' g)) :
    IsFormalTranspose μ (P ∘ₗ Q) (Q' ∘ₗ P') := fun f g hf hg ↦ by
  rw [LinearMap.comp_apply, hP _ _ (hQs f hf) hg, hQ _ _ hf (hP's g hg), LinearMap.comp_apply]

/-- **Transposition reverses composition** of differential operators: if `P'` and `Q'` are
formal transposes of `P` and `Q`, and `Q` and `P'` are differential operators, then `Q' ∘ P'` is a
formal transpose of `P ∘ Q`. -/
theorem IsFormalTranspose.comp_of_mem_differentialOperators [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [T2Space M] {k l : ℕ}
    (hP : IsFormalTranspose μ P P') (hQ : IsFormalTranspose μ Q Q')
    (hQm : Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hP'm : P' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ l) :
    IsFormalTranspose μ (P ∘ₗ Q) (Q' ∘ₗ P') :=
  hP.comp hQ (fun _ ↦ hasCompactSupport_apply_of_mem_differentialOperators hQm)
    (fun _ ↦ hasCompactSupport_apply_of_mem_differentialOperators hP'm)

variable [OpensMeasurableSpace M]

/-- The product of a smooth function and a compactly supported smooth function is integrable. -/
private theorem integrable_mul_of_hasCompactSupport_right [IsFiniteMeasureOnCompacts μ]
    (f : C^∞⟮I, M; ℝ⟯) {g : C^∞⟮I, M; ℝ⟯} (hg : HasCompactSupport g) :
    Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport hg.mul_left

private theorem integrable_mul_of_hasCompactSupport_left [IsFiniteMeasureOnCompacts μ]
    {f : C^∞⟮I, M; ℝ⟯} (hf : HasCompactSupport f) (g : C^∞⟮I, M; ℝ⟯) :
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
    {D D' : ι → C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h : ∀ i ∈ s, IsFormalTranspose μ (D i) (D' i)) :
    IsFormalTranspose μ (∑ i ∈ s, D i) (∑ i ∈ s, D' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj ↦ h j (mem_insert_of_mem hj))

end IsFormalTranspose

/-! ### Transposes of partial derivatives for Haar measures -/

section Haar

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **Integration by parts**: for a Haar measure, the formal transpose of the directional
derivative `∂_v` is `-∂_v`. -/
theorem isFormalTranspose_lineDerivation (v : E) :
    IsFormalTranspose μ (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
      (-lineDerivation ℝ v) := fun f g hf hg ↦ by
  have hf' : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  have hg' : ContDiff ℝ ∞ g := g.contMDiff.contDiff
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := v)
    (by simpa using integrable_mul_of_hasCompactSupport_right (lineDerivation ℝ v f) hg)
    (by simpa using integrable_mul_of_hasCompactSupport_left hf (lineDerivation ℝ v g))
    (integrable_mul_of_hasCompactSupport_left hf g)
    (fun x _ ↦ hf'.differentiable (by simp) x) (fun x _ ↦ hg'.differentiable (by simp) x)
  simp only [Derivation.coeFn_coe, LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply,
    lineDerivation_apply_apply, mul_neg, integral_neg, h, neg_neg]

/-- For a Haar measure, the formal transpose of the monomial `∂^α` in the partial derivatives
along a basis is `(-1)^|α| ∂^α`. -/
theorem isFormalTranspose_multiIndexDeriv {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (α : ι → ℕ) :
    IsFormalTranspose μ
      (multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
        (fun i j ↦ commute_lineDerivation (b i) (b j)) α)
      (((-1 : ℝ) ^ ∑ i, α i) • multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
        (fun i j ↦ commute_lineDerivation (b i) (b j)) α) := by
  classical
  set d := fun i ↦ lineDerivation ℝ (b i)
  set hd : ∀ i j, Commute (d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (d j) :=
    fun i j ↦ commute_lineDerivation (b i) (b j)
  obtain ⟨N, hN⟩ : ∃ N, ∑ i, α i = N := ⟨_, rfl⟩
  induction N generalizing α with
  | zero =>
    obtain rfl : α = 0 := funext fun i ↦ by simpa using (sum_eq_zero_iff.mp hN) i (mem_univ i)
    rw [hN, pow_zero, one_smul, multiIndexDeriv_zero]
    exact isFormalTranspose_one
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
    have h := (ih β hβ).comp_of_mem_differentialOperators (isFormalTranspose_lineDerivation (b i))
      (Derivation.mem_differentialOperators_one _)
      (Submodule.smul_mem _ _ (multiIndexDeriv_mem_differentialOperators d hd β))
    -- `∂_i` commutes with `∂^β`, so `-∂_i ∘ (-1)^|β| ∂^β = (-1)^|α| ∂^α`.
    have e₁ : multiIndexDeriv d hd α = multiIndexDeriv d hd β ∘ₗ d i := by
      rw [hαβ, multiIndexDeriv_add_single, Module.End.mul_eq_comp]
    have e₂ : ((-1 : ℝ) ^ ∑ j, α j) • multiIndexDeriv d hd α =
        (-(d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) ∘ₗ
          (((-1 : ℝ) ^ ∑ j, β j) • multiIndexDeriv d hd β) := by
      rw [hN, hαβ, add_comm β, multiIndexDeriv_add, multiIndexDeriv_single, pow_one,
        Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.neg_comp, hβ, pow_succ,
        mul_neg_one]
      exact (neg_smul ((-1 : ℝ) ^ N) ((d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ
        multiIndexDeriv d hd β)).trans (smul_neg _ _).symm
    rw [e₂, e₁]
    exact h

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
  set d := fun i ↦ lineDerivation ℝ (b i)
  set hd : ∀ i j, Commute (d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (d j) :=
    fun i j ↦ commute_lineDerivation (b i) (b j)
  -- Write the coordinate expression as a sum of multiplication operators composed with monomials.
  have hsum : coordinateOperator d hd m c = ∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k,
      LinearMap.mulLeft ℝ (c α) ∘ₗ multiIndexDeriv d hd α := by
    ext f x
    simp [coordinateOperator_apply, mul_comm]
  refine ⟨∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k,
    (((-1 : ℝ) ^ ∑ i, α i) • multiIndexDeriv d hd α) ∘ₗ LinearMap.mulLeft ℝ (c α),
    sum_mem fun k hk ↦ sum_mem fun α hα ↦ ?_, ?_⟩
  · rw [mem_piAntidiag] at hα
    refine differentialOperators_mono (show k + 0 ≤ m by simpa [Nat.lt_succ_iff] using hk) ?_
    exact comp_mem_differentialOperators
      (Submodule.smul_mem _ _ (hα.1 ▸ multiIndexDeriv_mem_differentialOperators d hd α))
      (mulLeft_mem_differentialOperators_zero _)
  · rw [hsum]
    exact IsFormalTranspose.sum _ fun k _ ↦ IsFormalTranspose.sum _ fun α _ ↦
      (isFormalTranspose_mulLeft (c α)).comp_of_mem_differentialOperators
        (isFormalTranspose_multiIndexDeriv b α) (multiIndexDeriv_mem_differentialOperators d hd α)
        (mulLeft_mem_differentialOperators_zero (c α))

end Haar

/-! ### Uniqueness -/

section Uniqueness

variable [MeasurableSpace M] {μ : Measure M} [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BorelSpace M]

/-- **Uniqueness of formal transposes.** On a finite-dimensional manifold, for a measure that is
finite on compact sets and positive on nonempty open sets, such as a Haar measure, two formal
transposes of the same operator that are differential operators are equal. -/
theorem IsFormalTranspose.eq_of_mem_differentialOperators [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {m₁ m₂ : ℕ} {D D₁ D₂ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h₁ : IsFormalTranspose μ D D₁) (h₂ : IsFormalTranspose μ D D₂)
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m₁)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m₂) :
    D₁ = D₂ := by
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  refine differentialOperators_eq_of_forall_hasCompactSupport_apply_eq hD₁ hD₂ fun g hg ↦ ?_
  have hcont : Continuous fun x ↦ D₁ g x - D₂ g x :=
    (D₁ g).contMDiff.continuous.sub (D₂ g).contMDiff.continuous
  -- The difference `D₁ g - D₂ g` integrates to zero against every test function.
  have hae : ∀ᵐ x ∂μ, D₁ g x - D₂ g x = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let f : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have hfφ : (f : M → ℝ) = φ := ContMDiffMap.coeFn_mk φ hφ
    have hf : HasCompactSupport f := hfφ ▸ hφc
    simp only [smul_eq_mul, mul_sub, ← hfφ]
    rw [integral_sub (integrable_mul_of_hasCompactSupport_left hf (D₁ g))
      (integrable_mul_of_hasCompactSupport_left hf (D₂ g)), ← h₁ f g hf hg, ← h₂ f g hf hg,
      sub_self]
  have hzero := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).mp hae
  exact ContMDiffMap.ext fun x ↦ sub_eq_zero.mp (congrFun hzero x)

end Uniqueness

/-! ### The formal transpose -/

section FormalTranspose

variable [MeasurableSpace M] {μ : Measure M} {m k l : ℕ}
  {D D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}

open Classical in
variable (μ) in
/-- The **formal transpose** `Dᵗ` of a linear operator `D` on `C^∞(M)` with respect to the
measure `μ`: a differential operator with `∫ (D f) g dμ = ∫ f (Dᵗ g) dμ` for all compactly
supported smooth `f` and `g`, if there is one, and `0` otherwise. On a finite-dimensional manifold
it is unique (`TauCeti.IsFormalTranspose.formalTranspose_eq`), and for a Haar measure on a
finite-dimensional space and a differential operator `D` of order at most `m` it exists and has
order at most `m` (`TauCeti.isFormalTranspose_formalTranspose`,
`TauCeti.formalTranspose_mem_differentialOperators`). -/
def formalTranspose (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  if h : ∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) ∧
    IsFormalTranspose μ D D' then h.choose else 0

/-- If `D` has a formal transpose that is a differential operator, then `formalTranspose μ D` is
one. -/
private theorem formalTranspose_spec
    (h : ∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) ∧
      IsFormalTranspose μ D D') :
    (∃ m, formalTranspose μ D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯
      C^∞⟮I, M; ℝ⟯ m) ∧ IsFormalTranspose μ D (formalTranspose μ D) := by
  classical
  rw [formalTranspose, dite_eq_left h]
  exact h.choose_spec

/-- If `D` has no formal transpose that is a differential operator, then `formalTranspose μ D`
is `0`. -/
private theorem formalTranspose_of_not_exists
    (h : ¬∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) ∧
      IsFormalTranspose μ D D') :
    formalTranspose μ D = 0 := by
  classical
  rw [formalTranspose, dite_eq_right_iff]
  exact fun h' ↦ absurd h' h

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BorelSpace M] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- **Characterization of the formal transpose**: every formal transpose of `D` that is a
differential operator is `formalTranspose μ D`. -/
theorem IsFormalTranspose.formalTranspose_eq (h : IsFormalTranspose μ D D')
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k) :
    formalTranspose μ D = D' := by
  obtain ⟨⟨m, hm⟩, hT⟩ := formalTranspose_spec ⟨D', ⟨k, hD'⟩, h⟩
  exact hT.eq_of_mem_differentialOperators h hm hD'

/-- The zero operator is its own formal transpose. -/
@[simp]
theorem formalTranspose_zero : formalTranspose μ (0 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) = 0 :=
  isFormalTranspose_zero.formalTranspose_eq (k := 0) (zero_mem _)

/-- The identity is its own formal transpose. -/
@[simp]
theorem formalTranspose_id :
    formalTranspose μ (LinearMap.id : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) = LinearMap.id :=
  isFormalTranspose_id.formalTranspose_eq (k := 0) <| by
    simpa only [LinearMap.mulLeft_one] using
      mulLeft_mem_differentialOperators_zero (R := ℝ) (1 : C^∞⟮I, M; ℝ⟯)

/-- The identity is its own formal transpose. -/
@[simp]
theorem formalTranspose_one : formalTranspose μ (1 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) = 1 :=
  formalTranspose_id

/-- Multiplication by a smooth function is its own formal transpose. -/
@[simp]
theorem formalTranspose_mulLeft (c : C^∞⟮I, M; ℝ⟯) :
    formalTranspose μ (LinearMap.mulLeft ℝ c) = LinearMap.mulLeft ℝ c :=
  (isFormalTranspose_mulLeft c).formalTranspose_eq (mulLeft_mem_differentialOperators_zero c)

/-- Formal transposition commutes with real scalar multiplication. -/
@[simp]
theorem formalTranspose_smul (r : ℝ) (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
    formalTranspose μ (r • D) = r • formalTranspose μ D := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [zero_smul, zero_smul, formalTranspose_zero]
  by_cases h : ∃ D', (∃ m, D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯
      C^∞⟮I, M; ℝ⟯ m) ∧ IsFormalTranspose μ D D'
  · obtain ⟨⟨m, hm⟩, hT⟩ := formalTranspose_spec h
    exact (hT.smul r).formalTranspose_eq (Submodule.smul_mem _ r hm)
  · -- A transpose of `r • D` would give the transpose `r⁻¹ • _` of `D`.
    rw [formalTranspose_of_not_exists h, smul_zero, formalTranspose_of_not_exists]
    rintro ⟨D', ⟨m, hm⟩, hD'⟩
    refine h ⟨r⁻¹ • D', ⟨m, Submodule.smul_mem _ _ hm⟩, ?_⟩
    simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hD'.smul r⁻¹

/-- Formal transposition commutes with negation. -/
@[simp]
theorem formalTranspose_neg (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
    formalTranspose μ (-D) = -formalTranspose μ D := by
  rw [← neg_one_smul ℝ D, formalTranspose_smul]
  exact neg_one_smul ℝ (formalTranspose μ D)

end FormalTranspose

section FormalTransposeHaar

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {m k l : ℕ} {D P Q : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

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

/-- Formal transposition commutes with subtraction of differential operators. -/
theorem formalTranspose_sub
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) :
    formalTranspose μ (P - Q) = formalTranspose μ P - formalTranspose μ Q := by
  rw [sub_eq_add_neg, formalTranspose_add hP (neg_mem hQ), formalTranspose_neg, sub_eq_add_neg]

/-- Formal transposition commutes with finite sums of differential operators. -/
theorem formalTranspose_sum {ι : Type*} (s : Finset ι) {m : ι → ℕ}
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hD : ∀ i ∈ s, D i ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (m i)) :
    formalTranspose μ (∑ i ∈ s, D i) = ∑ i ∈ s, formalTranspose μ (D i) :=
  (IsFormalTranspose.sum s fun i hi ↦
    isFormalTranspose_formalTranspose (hD i hi)).formalTranspose_eq
    (sum_mem fun i hi ↦ differentialOperators_mono (le_sup (f := m) hi)
      (formalTranspose_mem_differentialOperators (hD i hi)))

/-- The formal transpose of the directional derivative `∂_v` is `-∂_v`. -/
@[simp]
theorem formalTranspose_lineDerivation (v : E) :
    formalTranspose μ (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) =
      -lineDerivation ℝ v :=
  (isFormalTranspose_lineDerivation v).formalTranspose_eq
    (neg_mem (Derivation.mem_differentialOperators_one _))

/-- The formal transpose of the monomial `∂^α` in the partial derivatives along a basis is
`(-1)^|α| ∂^α`. -/
theorem formalTranspose_multiIndexDeriv {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (α : ι → ℕ) :
    formalTranspose μ (multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
        (fun i j ↦ commute_lineDerivation (b i) (b j)) α) =
      ((-1 : ℝ) ^ ∑ i, α i) • multiIndexDeriv (fun i ↦ lineDerivation ℝ (b i))
        (fun i j ↦ commute_lineDerivation (b i) (b j)) α :=
  (isFormalTranspose_multiIndexDeriv b α).formalTranspose_eq
    (Submodule.smul_mem _ _ (multiIndexDeriv_mem_differentialOperators _ _ α))

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

end FormalTransposeHaar

/-! ### Densities -/

section Density

variable [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M}
  {D D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}

/-- **Formal transposes for a density.** Let `ρ` be a nonnegative unit of `C^∞(M)`, that is a
smooth positive density. Then `D'` is a formal transpose of `D` for the measure `ρ μ` if and only
if `ρ D' ρ⁻¹` is a formal transpose of `D` for `μ`. -/
theorem isFormalTranspose_withDensity_iff (ρ : (C^∞⟮I, M; ℝ⟯)ˣ)
    (hρ : ∀ x, 0 ≤ (ρ : C^∞⟮I, M; ℝ⟯) x) :
    IsFormalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮I, M; ℝ⟯) x)) D D' ↔
      IsFormalTranspose μ D
        (LinearMap.mulLeft ℝ (ρ : C^∞⟮I, M; ℝ⟯) ∘ₗ D' ∘ₗ LinearMap.mulLeft ℝ ↑ρ⁻¹) := by
  have hρρ (x : M) : (ρ : C^∞⟮I, M; ℝ⟯) x * (↑ρ⁻¹ : C^∞⟮I, M; ℝ⟯) x = 1 := by
    simpa only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_one, Pi.one_apply] using
      congrArg (fun φ : C^∞⟮I, M; ℝ⟯ ↦ φ x) ρ.mul_inv
  simp only [isFormalTranspose_iff, Probability.integral_withDensity_ofReal
    (ρ : C^∞⟮I, M; ℝ⟯).contMDiff.continuous.aemeasurable (ae_of_all _ hρ), smul_eq_mul,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  constructor
  · intro h f g hf hg
    have key := h f (↑ρ⁻¹ * g) hf (by rw [ContMDiffMap.coe_mul]; exact hg.mul_left)
    simp only [ContMDiffMap.coe_mul, Pi.mul_apply] at key
    calc ∫ x, D f x * g x ∂μ
        = ∫ x, (ρ : C^∞⟮I, M; ℝ⟯) x * (D f x * ((↑ρ⁻¹ : C^∞⟮I, M; ℝ⟯) x * g x)) ∂μ := by
          congr 1 with x
          linear_combination (-(D f x * g x)) * hρρ x
      _ = _ := key
      _ = _ := by congr 1 with x; ring
  · intro h f g hf hg
    have key := h f (↑ρ * g) hf (by rw [ContMDiffMap.coe_mul]; exact hg.mul_left)
    simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Units.inv_mul_cancel_left] at key
    calc ∫ x, (ρ : C^∞⟮I, M; ℝ⟯) x * (D f x * g x) ∂μ
        = ∫ x, D f x * ((ρ : C^∞⟮I, M; ℝ⟯) x * g x) ∂μ := by congr 1 with x; ring
      _ = _ := key
      _ = _ := by congr 1 with x; ring

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BorelSpace M] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- **The formal transpose for a density.** For a smooth positive density `ρ`, the formal
transpose of `D` with respect to `ρ μ` is `g ↦ ρ⁻¹ Dᵗ (ρ g)`, where `Dᵗ` is its formal transpose
with respect to `μ`. -/
theorem formalTranspose_withDensity (ρ : (C^∞⟮I, M; ℝ⟯)ˣ) (hρ : ∀ x, 0 ≤ (ρ : C^∞⟮I, M; ℝ⟯) x)
    (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
    formalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮I, M; ℝ⟯) x)) D =
      LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ formalTranspose μ D ∘ₗ LinearMap.mulLeft ℝ ↑ρ := by
  -- Conjugation by multiplication by `ρ` is invertible and preserves differential operators.
  have hc (u : (C^∞⟮I, M; ℝ⟯)ˣ) (X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
      LinearMap.mulLeft ℝ (u : C^∞⟮I, M; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑u⁻¹ ∘ₗ X = X := by
    rw [← LinearMap.comp_assoc, ← LinearMap.mulLeft_mul, u.mul_inv, LinearMap.mulLeft_one,
      LinearMap.id_comp]
  have hc' (X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
      LinearMap.mulLeft ℝ (↑ρ⁻¹ : C^∞⟮I, M; ℝ⟯) ∘ₗ LinearMap.mulLeft ℝ ↑ρ ∘ₗ X = X := by
    simpa only [inv_inv] using hc ρ⁻¹ X
  have hM := hc ρ LinearMap.id
  have hM' := hc' LinearMap.id
  rw [LinearMap.comp_id] at hM hM'
  have hm (u : C^∞⟮I, M; ℝ⟯) {k : ℕ} {X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
      (hX : X ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
      (v : C^∞⟮I, M; ℝ⟯) :
      LinearMap.mulLeft ℝ u ∘ₗ X ∘ₗ LinearMap.mulLeft ℝ v ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (0 + (k + 0)) :=
    comp_mem_differentialOperators (mulLeft_mem_differentialOperators_zero u)
      (comp_mem_differentialOperators hX (mulLeft_mem_differentialOperators_zero v))
  have hiff (D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :=
    isFormalTranspose_withDensity_iff (μ := μ) (D := D) (D' := D') ρ hρ
  by_cases h : ∃ T, (∃ m, T ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯
      C^∞⟮I, M; ℝ⟯ m) ∧ IsFormalTranspose μ D T
  · obtain ⟨⟨m, hT⟩, hTt⟩ := formalTranspose_spec h
    have hR : IsFormalTranspose (μ.withDensity fun x ↦ ENNReal.ofReal ((ρ : C^∞⟮I, M; ℝ⟯) x))
        D (LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ formalTranspose μ D ∘ₗ LinearMap.mulLeft ℝ ↑ρ) := by
      rw [hiff]
      simpa only [LinearMap.comp_assoc, hM, hc, LinearMap.comp_id] using hTt
    obtain ⟨⟨k, hS⟩, hSt⟩ := formalTranspose_spec ⟨_, ⟨_, hm _ hT _⟩, hR⟩
    -- Both transposes for `ρ μ` conjugate to transposes for `μ`, which are unique.
    have key := ((hiff _).mp hSt).eq_of_mem_differentialOperators ((hiff _).mp hR) (hm _ hS _)
      (hm _ (hm _ hT _) _)
    have := congrArg (fun X ↦ LinearMap.mulLeft ℝ ↑ρ⁻¹ ∘ₗ X ∘ₗ LinearMap.mulLeft ℝ ↑ρ) key
    simpa only [LinearMap.comp_assoc, hM', hc', LinearMap.comp_id] using this
  · -- A transpose `S` for `ρ μ` would give the transpose `ρ S ρ⁻¹` for `μ`.
    rw [formalTranspose_of_not_exists h, LinearMap.zero_comp, LinearMap.comp_zero,
      formalTranspose_of_not_exists]
    rintro ⟨S, ⟨k, hS⟩, hSt⟩
    exact h ⟨_, ⟨_, hm _ hS _⟩, (hiff _).mp hSt⟩

end Density

end TauCeti
