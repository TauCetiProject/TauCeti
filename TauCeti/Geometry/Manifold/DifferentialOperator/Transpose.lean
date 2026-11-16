/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Formal transposes of differential operators on smooth functions

Let `μ` be a measure on a manifold `M`. A linear map `D'` of the smooth real functions `C^∞(M)` is
a *formal transpose* of `D` with respect to `μ` (`LinearMap.IsFormalTranspose D D' μ`) if

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all compactly supported smooth `f` and `g`. This is the integration-by-parts identity behind
weak formulations and the extension of differential operators to distributions: the distribution
`D T` is defined by `(D T)(g) = T (D' g)`. For real functions the transpose is also the formal
adjoint for the `L²(μ)` inner product. The model case is a derivative on `ℝⁿ` with Lebesgue
measure: integration by parts shows that `-∂ᵥ` is a formal transpose of `∂ᵥ`.

Differential operators are taken in Grothendieck's sense (`TauCeti.differentialOperators`):
operators all of whose `(m + 1)`-fold commutators with multiplication operators vanish. They are
local, and on a boundaryless manifold they preserve compact supports, which makes formal
transposes of differential operators reverse compositions. For a measure that is positive on open
sets and finite on compact sets of a Hausdorff σ-compact manifold, a differential operator has at
most one formal transpose that is a differential operator, and it has the same order and principal
symbol `ξ ↦ (-1) ^ m σ(ξ)`. Indeed, since multiplication operators are their own transposes, the
transpose of a commutator `[D, a]` is `-[D', a]`, so the `m`-fold commutators of `D'` are `(-1) ^ m`
times those of `D`.

On a finite-dimensional real vector space `E` with an additive Haar measure, every differential
operator of order at most `m` has a formal transpose of order at most `m`. The proof writes the
operator as a coordinate expression `∑_α c_α ∂^α` and uses that multiplication operators and the
derivatives `∂ᵥ` have formal transposes, which then exist for sums and compositions; no closed-form
coordinate formula for the transpose is stated here. The first-order case is made explicit: the
transpose of `a ∂ᵥ` is `-a ∂ᵥ - (∂ᵥ a)`, where
`(∂ᵥ a)` is multiplication by the derivative of `a`, so this zeroth-order term is not seen by the
principal symbol.

## Main definitions

* `LinearMap.IsFormalTranspose D D' μ`: `∫ (D f) g dμ = ∫ f (D' g) dμ` for compactly supported
  smooth `f` and `g`.

## Main results

* `LinearMap.IsFormalTranspose.symm`, `LinearMap.IsFormalTranspose.add`,
  `LinearMap.IsFormalTranspose.smul`, `LinearMap.IsFormalTranspose.comp`: formal transposition is
  symmetric, linear and reverses compositions of differential operators.
* `LinearMap.isFormalTranspose_self_of_mem_differentialOperators_zero`: operators of order zero,
  that is multiplication operators, are their own transposes.
* `LinearMap.IsFormalTranspose.smulCommutator`: the transpose of `[D, a]` is `-[D', a]`.
* `LinearMap.IsFormalTranspose.unique`: a formal transpose that is a differential operator is
  unique.
* `LinearMap.IsFormalTranspose.mem_differentialOperators`: the formal transpose of a differential
  operator of order at most `m` has order at most `m`.
* `LinearMap.IsFormalTranspose.smoothPrincipalSymbol_eq`: its principal symbol is `(-1) ^ m` times
  that of the operator.
* `LinearMap.isFormalTranspose_lineDerivation`: on a finite-dimensional vector space with an
  additive Haar measure, `-∂ᵥ` is the formal transpose of `∂ᵥ`.
* `LinearMap.exists_isFormalTranspose`: there, every differential operator of order at most `m`
  has a formal transpose of order at most `m`.
* `LinearMap.isFormalTranspose_lsmul_comp_lineDerivation`: the transpose of `a ∂ᵥ` is
  `-a ∂ᵥ - (∂ᵥ a)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983, for
  transposes of differential operators and the extension of differential operators to
  distributions.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open MeasureTheory Filter Set TauCeti
open scoped ContDiff Manifold Topology

noncomputable section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [MeasurableSpace M]

/-- A linear map `D'` of smooth functions is a **formal transpose** of `D` with respect to the
measure `μ` if `∫ (D f) g dμ = ∫ f (D' g) dμ` for all compactly supported smooth functions `f` and
`g`. -/
def IsFormalTranspose (D D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯)
    (μ : Measure M := by volume_tac) : Prop :=
  ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f → HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

variable {μ : Measure M} {D D' D₁ D₁' D₂ D₂' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}

theorem isFormalTranspose_iff :
    D.IsFormalTranspose D' μ ↔ ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport f → HasCompactSupport g →
      ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  Iff.rfl

namespace IsFormalTranspose

/-- The integration-by-parts identity of a formal transpose. -/
theorem integral_apply_mul (h : D.IsFormalTranspose D' μ) {f g : C^∞⟮I, M; ℝ⟯}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  h f g hf hg

/-- Formal transposition is symmetric. -/
theorem symm (h : D.IsFormalTranspose D' μ) : D'.IsFormalTranspose D μ := fun f g hf hg ↦
  calc ∫ x, D' f x * g x ∂μ = ∫ x, g x * D' f x ∂μ := by simp_rw [mul_comm]
    _ = ∫ x, D g x * f x ∂μ := (h g f hg hf).symm
    _ = ∫ x, f x * D g x ∂μ := by simp_rw [mul_comm]

end IsFormalTranspose

theorem isFormalTranspose_comm : D.IsFormalTranspose D' μ ↔ D'.IsFormalTranspose D μ :=
  ⟨.symm, .symm⟩

theorem isFormalTranspose_zero : (0 : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose 0 μ :=
  fun _ _ _ _ ↦ by simp

theorem isFormalTranspose_id :
    (LinearMap.id : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose LinearMap.id μ :=
  fun _ _ _ _ ↦ rfl

/-- Multiplication by a smooth function is its own formal transpose. -/
theorem isFormalTranspose_lsmul (a : C^∞⟮I, M; ℝ⟯) :
    (Algebra.lsmul ℝ ℝ C^∞⟮I, M; ℝ⟯ a).IsFormalTranspose (Algebra.lsmul ℝ ℝ C^∞⟮I, M; ℝ⟯ a) μ :=
  fun f g _ _ ↦ by
    simp only [Algebra.lsmul_coe, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply]
    congr 1
    ext x
    ring

/-- An operator of order zero on `C^∞(M)`, that is a multiplication operator, is its own formal
transpose. -/
theorem isFormalTranspose_self_of_mem_differentialOperators_zero
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 0) :
    D.IsFormalTranspose D μ := by
  have hD1 : D = Algebra.lsmul ℝ ℝ C^∞⟮I, M; ℝ⟯ (D 1) := LinearMap.ext fun f ↦ by
    simpa [mul_comm] using mem_differentialOperators_zero_iff.1 hD f 1
  rw [hD1]
  exact isFormalTranspose_lsmul _

namespace IsFormalTranspose

theorem smul (h : D.IsFormalTranspose D' μ) (c : ℝ) : (c • D).IsFormalTranspose (c • D') μ :=
  fun f g hf hg ↦ by
    simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      mul_left_comm (f _) c, integral_const_mul, h f g hf hg]

theorem neg (h : D.IsFormalTranspose D' μ) : (-D).IsFormalTranspose (-D') μ :=
  fun f g hf hg ↦ by simp [integral_neg, h f g hf hg]

section Integrable

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

private theorem integrable_mul (u : C^∞⟮I, M; ℝ⟯) {v : C^∞⟮I, M; ℝ⟯} (hv : HasCompactSupport v) :
    Integrable (fun x ↦ u x * v x) μ :=
  (u.contMDiff.continuous.mul v.contMDiff.continuous).integrable_of_hasCompactSupport hv.mul_left

theorem add (h₁ : D₁.IsFormalTranspose D₁' μ) (h₂ : D₂.IsFormalTranspose D₂' μ) :
    (D₁ + D₂).IsFormalTranspose (D₁' + D₂') μ := fun f g hf hg ↦ by
  simp only [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, add_mul, mul_add]
  rw [integral_add (integrable_mul _ hg) (integrable_mul _ hg),
    integral_add (by simpa only [mul_comm] using integrable_mul (μ := μ) (D₁' g) hf)
      (by simpa only [mul_comm] using integrable_mul (μ := μ) (D₂' g) hf),
    h₁ f g hf hg, h₂ f g hf hg]

theorem sub (h₁ : D₁.IsFormalTranspose D₁' μ) (h₂ : D₂.IsFormalTranspose D₂' μ) :
    (D₁ - D₂).IsFormalTranspose (D₁' - D₂') μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

end Integrable

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

/-- **Formal transposition reverses compositions.** If `D₁'` and `D₂'` are formal transposes of
`D₁` and `D₂`, and `D₂` and `D₁'` are differential operators, then `D₂' ∘ D₁'` is a formal transpose
of `D₁ ∘ D₂`. -/
theorem comp {k k' : ℕ} (h₁ : D₁.IsFormalTranspose D₁' μ) (h₂ : D₂.IsFormalTranspose D₂' μ)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hD₁' : D₁' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k') :
    (D₁ ∘ₗ D₂).IsFormalTranspose (D₂' ∘ₗ D₁') μ := fun f g hf hg ↦
  (h₁ _ g (hf.differentialOperators_apply hD₂) hg).trans
    (h₂ f _ hf (hg.differentialOperators_apply hD₁'))

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

/-- **The transpose of a commutator.** If `D'` is a formal transpose of `D`, both differential
operators, then `-[D', a]` is a formal transpose of the commutator `[D, a]` with multiplication by
`a`: multiplication operators are their own transposes and transposition reverses compositions. -/
theorem smulCommutator {k k' : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k')
    (a : C^∞⟮I, M; ℝ⟯) :
    (TauCeti.smulCommutator ℝ a D).IsFormalTranspose (-TauCeti.smulCommutator ℝ a D') μ := by
  have ha := lsmul_mem_differentialOperators_zero (R := ℝ) a
  have h' := (h.comp (isFormalTranspose_lsmul a) ha hD').sub
    ((isFormalTranspose_lsmul a).comp h hD ha)
  convert h' using 1 <;> ext f x <;> simp [sub_eq_neg_add]

/-- The transpose of an iterated commutator: `(-1) ^ j [⋯[D', a], …, a]` is a formal transpose of
`[⋯[D, a], …, a]`, with `j` commutators. -/
theorem smulCommutator_pow {k k' : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k')
    (a : C^∞⟮I, M; ℝ⟯) (j : ℕ) :
    ((TauCeti.smulCommutator ℝ a ^ j) D).IsFormalTranspose
      ((-1 : ℝ) ^ j • (TauCeti.smulCommutator ℝ a ^ j) D') μ := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have h' := ih.smulCommutator
      (smulCommutator_pow_mem_differentialOperators (differentialOperators_mono
        (Nat.le_add_right k j) hD) a)
      (Submodule.smul_mem _ _ (smulCommutator_pow_mem_differentialOperators
        (differentialOperators_mono (Nat.le_add_right k' j) hD') a)) a
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    convert h' using 1
    ext f x
    simp [pow_succ]

variable [SigmaCompactSpace M] [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

omit [BoundarylessManifold I M] in
/-- Two formal transposes of `D` agree on compactly supported functions: a continuous function
whose integrals against all compactly supported smooth functions vanish is zero. -/
private theorem apply_eq_of_hasCompactSupport (h₁ : D.IsFormalTranspose D₁ μ)
    (h₂ : D.IsFormalTranspose D₂ μ) {g : C^∞⟮I, M; ℝ⟯} (hg : HasCompactSupport g) :
    D₁ g = D₂ g := by
  have hcont : Continuous fun y ↦ D₁ g y - D₂ g y :=
    (D₁ g).contMDiff.continuous.sub (D₂ g).contMDiff.continuous
  have hae : ∀ᵐ y ∂μ, D₁ g y - D₂ g y = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    have hφg := (h₁ ⟨φ, hφ⟩ g hφc hg).symm.trans (h₂ ⟨φ, hφ⟩ g hφc hg)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub, sub_eq_zero]
    · exact hφg
    all_goals exact (hφ.continuous.mul (ContMDiffMap.contMDiff _).continuous)
      |>.integrable_of_hasCompactSupport hφc.mul_right
  ext y
  exact sub_eq_zero.1 (congr_fun ((hcont.ae_eq_iff_eq μ continuous_const).1 hae) y)

/-- **Uniqueness of formal transposes.** A differential operator has at most one formal transpose
that is a differential operator. -/
theorem unique {k₁ k₂ : ℕ} (h₁ : D.IsFormalTranspose D₁ μ) (h₂ : D.IsFormalTranspose D₂ μ)
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k₁)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k₂) :
    D₁ = D₂ := by
  ext g x
  -- Both transposes are local, so they may be evaluated on a compactly supported localization of
  -- `g` near `x`, where they agree.
  let χ : SmoothBumpFunction I x := Classical.arbitrary _
  let ψ : C^∞⟮I, M; ℝ⟯ := ⟨χ, χ.contMDiff⟩
  have hψ : HasCompactSupport (ψ * g : C^∞⟮I, M; ℝ⟯) := by
    rw [ContMDiffMap.coe_mul]
    exact χ.hasCompactSupport.mono (Function.support_mul_subset_left _ _)
  have hloc : ((ψ * g : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x] g :=
    χ.eventuallyEq_one.mono fun y hy ↦ by
      rw [ContMDiffMap.coe_mul]
      simp [ψ, hy]
  rw [← differentialOperators_apply_eq_of_eventuallyEq hD₁ BoundarylessManifold.isInteriorPoint
      hloc, ← differentialOperators_apply_eq_of_eventuallyEq hD₂
      BoundarylessManifold.isInteriorPoint hloc, apply_eq_of_hasCompactSupport h₁ h₂ hψ]

/-- **The order of a formal transpose.** A formal transpose of a differential operator of order at
most `m` that is a differential operator has order at most `m`. -/
theorem mem_differentialOperators {m k : ℕ} (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k) :
    D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  induction m generalizing D D' with
  | zero =>
    rwa [h.unique (isFormalTranspose_self_of_mem_differentialOperators_zero hD) hD' hD]
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun a ↦ ?_
    simpa using neg_mem <| ih (h.smulCommutator (differentialOperators_le_succ _ hD) hD' a)
      (smulCommutator_mem_differentialOperators hD a)
      (neg_mem (smulCommutator_mem_differentialOperators (differentialOperators_le_succ _ hD') a))

/-- **The principal symbol of a formal transpose.** If `D'` is a formal transpose of `D`, both
differential operators of order at most `m`, then `σ(D')(ξ) = (-1) ^ m σ(D)(ξ)`. -/
theorem smoothPrincipalSymbol_eq {m : ℕ}
    {D D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m}
    (h : (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ) {x : M}
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint D' ξ =
      (-1) ^ m * smoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint D ξ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  -- The `m`-fold commutators of `D` and `D'` with `f` have order zero, so they are their own
  -- transposes, and by uniqueness `(-1) ^ m [⋯[D', f], …, f] = [⋯[D, f], …, f]`.
  have hm : ∀ P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      (TauCeti.smulCommutator ℝ f ^ m) (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 0 := fun P ↦
    smulCommutator_pow_mem_differentialOperators (by simp) f
  have heq := (h.smulCommutator_pow D.2 D'.2 f m).unique
    (isFormalTranspose_self_of_mem_differentialOperators_zero (hm D))
    (Submodule.smul_mem _ _ (hm D')) (hm D)
  have heq' : (TauCeti.smulCommutator ℝ f ^ m) (D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) =
      (-1 : ℝ) ^ m • (TauCeti.smulCommutator ℝ f ^ m) (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) := by
    rw [← heq, smul_smul, ← mul_pow]
    simp
  rw [smoothPrincipalSymbol_mvfderiv, smoothPrincipalSymbol_mvfderiv, heq']
  simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end IsFormalTranspose

/-! ### Formal transposes on a finite-dimensional vector space -/

section Euclidean

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E}
  [ν.IsAddHaarMeasure]
  {P : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

/-- **Integration by parts.** For an additive Haar measure on a finite-dimensional real vector
space, `-∂ᵥ` is the formal transpose of the derivative `∂ᵥ` in the direction `v`. -/
theorem isFormalTranspose_lineDerivation (v : E) :
    (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (-(TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) ν := by
  intro f g hf hg
  have hdiff (u : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : ContDiff ℝ ∞ u := u.contMDiff.contDiff
  have hderiv (u : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Continuous fun x ↦ fderiv ℝ u x v :=
    ((hdiff u).continuous_fderiv (by simp)).clm_apply continuous_const
  simp only [LinearMap.neg_apply, Derivation.coeFn_coe, ContMDiffMap.coe_neg, Pi.neg_apply,
    lineDerivation_apply_apply, mul_neg, integral_neg]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((hderiv f).mul g.contMDiff.continuous).integrable_of_hasCompactSupport hg.mul_left)
    ((f.contMDiff.continuous.mul (hderiv g)).integrable_of_hasCompactSupport hf.mul_right)
    ((f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport
      hf.mul_right)
    (fun x _ ↦ (hdiff f).differentiable (by simp) x)
    (fun x _ ↦ (hdiff g).differentiable (by simp) x), neg_neg]

/-- The operators with a formal transpose, both differential operators of some order, form a
subalgebra of the endomorphisms of `C^∞(E)`. -/
private def transposable (ν : Measure E) [ν.IsAddHaarMeasure] :
    Subalgebra ℝ (Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) where
  carrier := {P | (∃ k, P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) ∧ ∃ P', (∃ k, P' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) ∧ P.IsFormalTranspose P' ν}
  mul_mem' := by
    rintro P Q ⟨⟨k, hP⟩, P', ⟨k', hP'⟩, h⟩ ⟨⟨l, hQ⟩, Q', ⟨l', hQ'⟩, h'⟩
    exact ⟨⟨k + l, comp_mem_differentialOperators hP hQ⟩, Q' * P',
      ⟨l' + k', comp_mem_differentialOperators hQ' hP'⟩, h.comp h' hQ hP'⟩
  add_mem' := by
    rintro P Q ⟨⟨k, hP⟩, P', ⟨k', hP'⟩, h⟩ ⟨⟨l, hQ⟩, Q', ⟨l', hQ'⟩, h'⟩
    exact ⟨⟨max k l, add_mem (differentialOperators_mono (le_max_left k l) hP)
        (differentialOperators_mono (le_max_right k l) hQ)⟩, P' + Q',
      ⟨max k' l', add_mem (differentialOperators_mono (le_max_left k' l') hP')
        (differentialOperators_mono (le_max_right k' l') hQ')⟩, h.add h'⟩
  algebraMap_mem' c := by
    have hc : algebraMap ℝ (Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) c ∈
        differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
      mem_differentialOperators_zero_iff.2 fun a f ↦ by simp
    exact ⟨⟨0, hc⟩, _, ⟨0, hc⟩, isFormalTranspose_self_of_mem_differentialOperators_zero hc⟩

/-- **Existence of formal transposes.** For an additive Haar measure on a finite-dimensional real
vector space `E`, every differential operator of order at most `m` on `C^∞(E)` has a formal
transpose, which is a differential operator of order at most `m`. -/
theorem exists_isFormalTranspose {m : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ P' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m,
      P.IsFormalTranspose P' ν := by
  -- `P` is a coordinate expression `∑_α c_α ∂^α`, built from multiplication operators and
  -- derivatives, all of which have formal transposes.
  let b := Module.finBasis ℝ E
  have hder (i : Fin (Module.finrank ℝ E)) :
      (TauCeti.lineDerivation ℝ (b i) : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∈ transposable ν :=
    ⟨⟨1, (TauCeti.lineDerivation ℝ (b i)).mem_differentialOperators_one⟩, _,
      ⟨1, neg_mem (TauCeti.lineDerivation ℝ (b i)).mem_differentialOperators_one⟩,
      isFormalTranspose_lineDerivation (b i)⟩
  have hmul (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
      (Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ c : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∈
        transposable ν :=
    ⟨⟨0, lsmul_mem_differentialOperators_zero c⟩, _, ⟨0, lsmul_mem_differentialOperators_zero c⟩,
      isFormalTranspose_lsmul c⟩
  have hα (α : Fin (Module.finrank ℝ E) → ℕ) :
      multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (b i))
        (fun i j ↦ TauCeti.commute_lineDerivation (b i) (b j)) α ∈ transposable ν :=
    multiIndexDeriv_mem (S := (transposable ν).toSubmonoid) _ _ hder α
  have hP_eq : P = ∑ k ∈ Finset.range (m + 1), ∑ α ∈ Finset.univ.piAntidiag k,
      Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (coordinateCoeff b.smoothCoord P α) *
        multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (b i))
          (fun i j ↦ TauCeti.commute_lineDerivation (b i) (b j)) α := by
    conv_lhs => rw [b.eq_coordinateOperator_coordinateCoeff hP]
    ext f : 1
    simp [mul_comm]
  obtain ⟨-, P', ⟨k, hP'⟩, h⟩ : P ∈ transposable ν := by
    rw [hP_eq]
    exact Subalgebra.sum_mem _ fun k _ ↦ Subalgebra.sum_mem _ fun α _ ↦ mul_mem (hmul _) (hα α)
  exact ⟨P', h.mem_differentialOperators hP hP', h⟩

/-- **The transpose of a first-order operator.** For a smooth function `a` and a direction `v`,
the formal transpose of `f ↦ a ∂ᵥ f` is `g ↦ -a ∂ᵥ g - (∂ᵥ a) g`. -/
theorem isFormalTranspose_lsmul_comp_lineDerivation (a : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (v : E) :
    LinearMap.IsFormalTranspose (Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a ∘ₗ
        (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯))
      (-(Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a ∘ₗ
        (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) -
        Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (TauCeti.lineDerivation ℝ v a)) ν := by
  have h := (isFormalTranspose_lsmul (μ := ν) a).comp (isFormalTranspose_lineDerivation v)
    (TauCeti.lineDerivation ℝ v).mem_differentialOperators_one
    (lsmul_mem_differentialOperators_zero a)
  convert h using 1
  ext f x
  simp [Derivation.leibniz]
  ring

end Euclidean

end LinearMap
