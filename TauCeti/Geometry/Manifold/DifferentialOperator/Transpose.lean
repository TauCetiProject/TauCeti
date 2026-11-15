/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The formal transpose of a differential operator

Let `E` be a finite-dimensional real normed space and `μ` a Haar measure on `E`, for instance
Lebesgue measure on `ℝⁿ`. A linear map `D'` of the algebra `C^∞(E)` of smooth real functions is a
*formal transpose* of a linear map `D` (`LinearMap.IsFormalTranspose D D' μ`) if

`∫ (D f) g dμ = ∫ f (D' g) dμ`

for all compactly supported smooth `f` and `g`. This is the integration by parts identity that
extends `D` to distributions by duality, and for real scalar functions it is also the formal
adjoint. This file shows that every differential operator `D` of order at most `m` on `C^∞(E)`,
in Grothendieck's sense of iterated commutators with multiplication operators
(`TauCeti.differentialOperators`), has a unique formal transpose among differential operators,
again of order at most `m`. In the coordinate form `D f = ∑_{|α| ≤ m} c_α ∂^α f` of
`Module.Basis.eq_coordinateOperator_coordinateCoeff`, it is `g ↦ ∑_{|α| ≤ m} (-1)^|α| ∂^α (c_α g)`.
The transpose does not depend on the choice of Haar measure, since any two are proportional.

## Main definitions

* `LinearMap.IsFormalTranspose D D' μ`: `D'` is a formal transpose of `D` for the measure `μ`.
* `TauCeti.formalTranspose`: the formal transpose, as an involutive linear equivalence of the
  differential operators of order at most `m`.

## Main results

* `TauCeti.isFormalTranspose_lineDerivation`: integration by parts, the transpose of the
  directional derivative `∂_v` is `-∂_v`.
* `LinearMap.IsFormalTranspose.self_of_mem_differentialOperators_zero`: an operator of order zero,
  multiplication by a smooth function, is its own transpose.
* `LinearMap.IsFormalTranspose.comp`: transposition reverses composition.
* `TauCeti.exists_isFormalTranspose`: every differential operator of order at most `m` has a
  formal transpose of order at most `m`.
* `LinearMap.IsFormalTranspose.eq_of_mem_differentialOperators`: the transpose is unique among
  differential operators.
* `TauCeti.isFormalTranspose_formalTranspose`, `TauCeti.formalTranspose_eq_iff`: the
  characterization of `TauCeti.formalTranspose` for every Haar measure, with
  `TauCeti.formalTranspose_comp` (`(P ∘ Q)ᵗ = Qᵗ ∘ Pᵗ`) and
  `TauCeti.formalTranspose_lineDerivation` (`∂_vᵗ = -∂_v`).
* `TauCeti.smoothPrincipalSymbol_formalTranspose`: the principal symbol of the transpose of an
  operator of order at most `m` is `(-1)^m` times its principal symbol.
* `TauCeti.isFormalTranspose_lsmul_comp_lineDerivation`: the transpose of `a ∂_v` is
  `g ↦ -a ∂_v g - (∂_v a) g`; for `a(x) = x` on `ℝ` the zeroth-order term is `-g`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (differentiation
  of distributions, defined through the transpose of differentiation on test functions).
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- A product of a smooth function with a compactly supported one is integrable. -/
private theorem integrable_mul_of_hasCompactSupport [OpensMeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hg : HasCompactSupport g) : Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport
    hg.mul_left

namespace LinearMap

/-- `D'` is a *formal transpose* of `D` for the measure `μ`: `∫ (D f) g dμ = ∫ f (D' g) dμ` for
all compactly supported smooth functions `f` and `g` on `E`. -/
def IsFormalTranspose (D D' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (μ : Measure E) :
    Prop :=
  ∀ f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f → HasCompactSupport g →
    ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ

variable {D D' D₁ D₂ D₁' D₂' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {μ : Measure E}

theorem isFormalTranspose_iff :
    D.IsFormalTranspose D' μ ↔ ∀ f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f →
      HasCompactSupport g → ∫ x, D f x * g x ∂μ = ∫ x, f x * D' g x ∂μ :=
  Iff.rfl

namespace IsFormalTranspose

/-- Transposition is symmetric. -/
theorem symm (h : D.IsFormalTranspose D' μ) : D'.IsFormalTranspose D μ := fun f g hf hg ↦ by
  simpa only [mul_comm] using (h g f hg hf).symm

theorem _root_.LinearMap.isFormalTranspose_comm :
    D.IsFormalTranspose D' μ ↔ D'.IsFormalTranspose D μ :=
  ⟨symm, symm⟩

theorem _root_.LinearMap.isFormalTranspose_id :
    (LinearMap.id : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      LinearMap.id μ :=
  fun _ _ _ _ ↦ rfl

theorem _root_.LinearMap.isFormalTranspose_zero :
    (0 : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose 0 μ :=
  fun _ _ _ _ ↦ by simp

theorem smul (h : D.IsFormalTranspose D' μ) (c : ℝ) : (c • D).IsFormalTranspose (c • D') μ :=
  fun f g hf hg ↦ by
    simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, mul_left_comm (f _) c, h f g hf hg]

theorem neg (h : D.IsFormalTranspose D' μ) : (-D).IsFormalTranspose (-D') μ :=
  fun f g hf hg ↦ by
    simp only [LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply, neg_mul, mul_neg,
      integral_neg, h f g hf hg]

/-- **Transposition reverses composition**, provided the inner operator and the transpose of
the outer one preserve compact supports, as differential operators do. -/
theorem comp {P P' Q Q' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hP : P.IsFormalTranspose P' μ) (hQ : Q.IsFormalTranspose Q' μ)
    (hQc : ∀ f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport f → HasCompactSupport (Q f))
    (hP'c : ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯, HasCompactSupport g → HasCompactSupport (P' g)) :
    (P ∘ₗ Q).IsFormalTranspose (Q' ∘ₗ P') μ :=
  fun f g hf hg ↦ (hP _ g (hQc f hf) hg).trans (hQ f _ hf (hP'c g hg))

/-- A formal transpose can be replaced by an equal operator. -/
theorem congr_right (h : D.IsFormalTranspose D₁ μ) (h₁₂ : D₁ = D₂) : D.IsFormalTranspose D₂ μ :=
  h₁₂ ▸ h

variable [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]

theorem add (h₁ : D₁.IsFormalTranspose D₁' μ) (h₂ : D₂.IsFormalTranspose D₂' μ) :
    (D₁ + D₂).IsFormalTranspose (D₁' + D₂') μ := fun f g hf hg ↦ by
  have hl (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :=
    integrable_mul_of_hasCompactSupport (μ := μ) (D f) hg
  have hr (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
      Integrable (fun x ↦ f x * D g x) μ := by
    simpa only [mul_comm] using integrable_mul_of_hasCompactSupport (μ := μ) (D g) hf
  simp only [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, add_mul, mul_add]
  rw [integral_add (hl D₁) (hl D₂), integral_add (hr D₁') (hr D₂'), h₁ f g hf hg,
    h₂ f g hf hg]

theorem sub (h₁ : D₁.IsFormalTranspose D₁' μ) (h₂ : D₂.IsFormalTranspose D₂' μ) :
    (D₁ - D₂).IsFormalTranspose (D₁' - D₂') μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

theorem sum {ι : Type*} (s : Finset ι) {D D' : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h : ∀ i ∈ s, (D i).IsFormalTranspose (D' i) μ) :
    (∑ i ∈ s, D i).IsFormalTranspose (∑ i ∈ s, D' i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LinearMap.isFormalTranspose_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

end IsFormalTranspose

end LinearMap

namespace TauCeti

open LinearMap

variable {D D' D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {μ : Measure E}

/-! ### Operators of order zero and directional derivatives -/

omit [MeasurableSpace E] in
/-- An operator of order zero on `C^∞(E)` is multiplication by its value on `1`. -/
private theorem apply_eq_mul_of_mem_differentialOperators_zero
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : D f = f * D 1 := by
  simpa using mem_differentialOperators_zero_iff.1 hD f 1

/-- An operator of order zero on `C^∞(E)`, that is multiplication by a smooth function, is its own
formal transpose. -/
theorem _root_.LinearMap.IsFormalTranspose.self_of_mem_differentialOperators_zero
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0) : D.IsFormalTranspose D μ := fun f g _ _ ↦ by
  rw [apply_eq_mul_of_mem_differentialOperators_zero hD f,
    apply_eq_mul_of_mem_differentialOperators_zero hD g]
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)

/-- Multiplication by a smooth function is its own formal transpose. -/
theorem isFormalTranspose_lsmul (a : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a).IsFormalTranspose
      (Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a) μ :=
  .self_of_mem_differentialOperators_zero (lsmul_mem_differentialOperators_zero a)

variable [FiniteDimensional ℝ E]

/-- If each of the pairwise commuting derivations `dᵢ` has formal transpose `-dᵢ`, then the
formal transpose of the monomial `∂^α = ∏ᵢ dᵢ ^ αᵢ` is `(-1)^|α| ∂^α`. -/
theorem isFormalTranspose_multiIndexDeriv {ι : Type*} [Fintype ι]
    (d : ι → Derivation ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (hd : ∀ i j, Commute (d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (d j))
    (hdt : ∀ i, (d i : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (-(d i : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) μ) (α : ι → ℕ) :
    (multiIndexDeriv d hd α).IsFormalTranspose
      ((-1 : ℝ) ^ (∑ i, α i) • multiIndexDeriv d hd α) μ := by
  classical
  -- Induction on `|α|`, splitting off one derivation `dᵢ` with `αᵢ ≠ 0`.
  induction h : ∑ i, α i generalizing α with
  | zero =>
    obtain rfl : α = 0 := funext fun i ↦ by
      simpa using (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i)
    simpa [Module.End.one_eq_id] using LinearMap.isFormalTranspose_id
  | succ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra! h'
      simp [h'] at h
    set β := α - Pi.single i 1
    have hαβ : α = β + Pi.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [β]; omega
      · simp [β, hj]
    have hβ : ∑ j, β j = n := by
      have := congrArg (fun γ : ι → ℕ ↦ ∑ j, γ j) hαβ
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
        ite_true] at this
      omega
    have hmem : multiIndexDeriv d hd β ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ n :=
      hβ ▸ multiIndexDeriv_mem_differentialOperators d hd β
    have hcomm : multiIndexDeriv d hd β * d i = d i * multiIndexDeriv d hd β := by
      rw [← multiIndexDeriv_add_single, add_comm, multiIndexDeriv_add, multiIndexDeriv_single,
        pow_one]
    -- `∂^α = ∂^β ∘ dᵢ`, whose transpose is `(-dᵢ) ∘ (-1)^|β| ∂^β`.
    rw [hαβ, multiIndexDeriv_add_single, Module.End.mul_eq_comp]
    refine ((ih β hβ).comp (hdt i)
      (fun f hf ↦ HasCompactSupport.apply_of_mem_differentialOperators hf
        (d i).mem_differentialOperators_one)
      (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg
        (Submodule.smul_mem _ _ hmem))).congr_right ?_
    rw [← Module.End.mul_eq_comp (multiIndexDeriv d hd β), hcomm]
    ext f x
    simp [pow_succ]

section Commutator

variable [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]

/-- The formal transpose of a commutator with multiplication by `f` is minus the commutator of the
transpose: `[D, f]ᵗ = -[Dᵗ, f]`. -/
theorem _root_.LinearMap.IsFormalTranspose.smulCommutator {k l : ℕ}
    (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (TauCeti.smulCommutator ℝ f D).IsFormalTranspose (-TauCeti.smulCommutator ℝ f D') μ := by
  have hf : Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ f ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
    lsmul_mem_differentialOperators_zero f
  have h₁ := h.comp (isFormalTranspose_lsmul (μ := μ) f)
    (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg hf)
    (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg hD')
  have h₂ := (isFormalTranspose_lsmul (μ := μ) f).comp h
    (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg hD)
    (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg hf)
  have e (P : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
      TauCeti.smulCommutator ℝ f P = P ∘ₗ Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ f -
        Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ f ∘ₗ P :=
    LinearMap.ext fun g ↦ by simp
  rw [e, e, neg_sub]
  exact h₁.sub h₂

/-- The iterated commutators of a transpose: `(ad_f^n D)ᵗ = (-1)^n ad_f^n Dᵗ`, where
`ad_f D = [D, f]`. -/
theorem _root_.LinearMap.IsFormalTranspose.smulCommutator_pow {k l : ℕ}
    (h : D.IsFormalTranspose D' μ)
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (n : ℕ) :
    ((TauCeti.smulCommutator ℝ f ^ n) D).IsFormalTranspose
      ((-1 : ℝ) ^ n • (TauCeti.smulCommutator ℝ f ^ n) D') μ := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hDn := smulCommutator_pow_mem_differentialOperators
      (differentialOperators_mono (Nat.le_add_right k n) hD) f
    have hD'n := Submodule.smul_mem _ ((-1 : ℝ) ^ n) (smulCommutator_pow_mem_differentialOperators
      (differentialOperators_mono (Nat.le_add_right l n) hD') f)
    rw [pow_succ', mul_apply_eq_comp]
    refine (ih.smulCommutator hDn hD'n f).congr_right ?_
    rw [mul_apply_eq_comp, map_smul, pow_succ, mul_neg_one]
    exact (neg_smul _ _).symm

end Commutator

variable [BorelSpace E]

/-- **Integration by parts.** For a Haar measure, the formal transpose of the directional
derivative `∂_v` is `-∂_v`. -/
theorem isFormalTranspose_lineDerivation [μ.IsAddHaarMeasure] (v : E) :
    (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (-lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) μ := by
  intro f g hf hg
  have hfd : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  have hgd : ContDiff ℝ ∞ g := g.contMDiff.contDiff
  have hcont (h : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Continuous fun x ↦ fderiv ℝ h x v :=
    (h.contMDiff.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  simp only [LinearMap.neg_apply, ContMDiffMap.coe_neg, Pi.neg_apply, Derivation.coeFn_coe,
    lineDerivation_apply_apply, mul_neg, integral_neg]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    ((hcont f).mul g.contMDiff.continuous |>.integrable_of_hasCompactSupport hg.mul_left)
    (f.contMDiff.continuous.mul (hcont g) |>.integrable_of_hasCompactSupport hf.mul_right)
    (f.contMDiff.continuous.mul g.contMDiff.continuous |>.integrable_of_hasCompactSupport
      hf.mul_right)
    (fun x _ ↦ hfd.differentiable (by simp) x) (fun x _ ↦ hgd.differentiable (by simp) x),
    neg_neg]

/-- The formal transpose of `a ∂_v` is `g ↦ -a ∂_v g - (∂_v a) g`. For `a(x) = x` on `ℝ` and
`v = 1`, the zeroth-order term is `-1`: transposition does not merely negate the leading
derivative. -/
theorem isFormalTranspose_lsmul_comp_lineDerivation [μ.IsAddHaarMeasure]
    (a : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (v : E) :
    (Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a ∘ₗ
        (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)).IsFormalTranspose
      (-(Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ a ∘ₗ
        (lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)) -
        Algebra.lsmul ℝ ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (lineDerivation ℝ v a)) μ := by
  refine ((isFormalTranspose_lsmul a).comp (isFormalTranspose_lineDerivation v)
    (fun f hf ↦ HasCompactSupport.apply_of_mem_differentialOperators hf
      (lineDerivation ℝ v).mem_differentialOperators_one)
    (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg
      (lsmul_mem_differentialOperators_zero a))).congr_right ?_
  ext g x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sub_apply, Algebra.lsmul_coe,
    smul_eq_mul, Derivation.coeFn_coe, Derivation.leibniz]
  simp only [ContMDiffMap.coe_neg, ContMDiffMap.coe_sub, ContMDiffMap.coe_add,
    ContMDiffMap.coe_mul, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

/-! ### Existence and uniqueness -/

/-- **Existence of the formal transpose.** For a Haar measure `μ`, every differential operator of
order at most `m` on `C^∞(E)` has a formal transpose which is again a differential operator of
order at most `m`. -/
theorem exists_isFormalTranspose [μ.IsAddHaarMeasure] {m : ℕ}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m,
      D.IsFormalTranspose D' μ := by
  set b := Module.finBasis ℝ E
  set d : Fin (Module.finrank ℝ E) → Derivation ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ :=
    fun i ↦ lineDerivation ℝ (b i)
  have hd : ∀ i j, Commute (d i : Module.End ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (d j) :=
    fun i j ↦ commute_lineDerivation (b i) (b j)
  set c := coordinateCoeff b.smoothCoord D
  -- The coefficient operators `f ↦ f c_α` have order zero.
  set M : (Fin (Module.finrank ℝ E) → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ :=
    fun α ↦
      (LinearMap.toSpanSingleton C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ (c α)).restrictScalars ℝ
  have hM (α) : M α ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
    LinearMap.restrictScalars_mem_differentialOperators_zero _
  refine ⟨∑ k ∈ Finset.range (m + 1), ∑ α ∈ Finset.piAntidiag Finset.univ k,
    ((-1 : ℝ) ^ (∑ i, α i) • multiIndexDeriv d hd α) ∘ₗ M α, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k hk ↦ Submodule.sum_mem _ fun α hα ↦ ?_
    rw [Finset.mem_piAntidiag] at hα
    refine differentialOperators_mono (show ∑ i, α i + 0 ≤ m by
      simpa [hα.1, Nat.lt_succ_iff] using hk) ?_
    exact comp_mem_differentialOperators
      (Submodule.smul_mem _ _ (multiIndexDeriv_mem_differentialOperators d hd α)) (hM α)
  · have hcoord : coordinateOperator d hd m c = ∑ k ∈ Finset.range (m + 1),
        ∑ α ∈ Finset.piAntidiag Finset.univ k, M α ∘ₗ multiIndexDeriv d hd α :=
      LinearMap.ext fun f ↦ by simp [M, LinearMap.sum_apply]
    rw [(b.eq_coordinateOperator_coordinateCoeff hD).trans hcoord]
    refine IsFormalTranspose.sum _ fun k _ ↦ IsFormalTranspose.sum _ fun α _ ↦ ?_
    exact (IsFormalTranspose.self_of_mem_differentialOperators_zero (hM α)).comp
      (isFormalTranspose_multiIndexDeriv d hd (fun i ↦ isFormalTranspose_lineDerivation _) α)
      (fun f hf ↦ HasCompactSupport.apply_of_mem_differentialOperators hf
        (multiIndexDeriv_mem_differentialOperators d hd α))
      (fun g hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg (hM α))

/-- **Uniqueness of the formal transpose.** For a Haar measure, two differential operators that
are formal transposes of the same operator are equal. -/
theorem _root_.LinearMap.IsFormalTranspose.eq_of_mem_differentialOperators [μ.IsAddHaarMeasure]
    {k l : ℕ} (h₁ : D.IsFormalTranspose D₁ μ) (h₂ : D.IsFormalTranspose D₂ μ)
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ l) :
    D₁ = D₂ := by
  refine eq_of_forall_hasCompactSupport_apply_eq hD₁ hD₂ fun g hg ↦ ?_
  -- On a compactly supported `g`, `D₁ g - D₂ g` integrates to zero against every test function.
  set u := D₁ g - D₂ g
  have hu : Continuous u := u.contMDiff.continuous
  have hae : (u : E → ℝ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable fun φ hφ hφc ↦ ?_
    let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨φ, hφ.contMDiff⟩
    have hf : HasCompactSupport f := hφc
    have hi (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
        Integrable (fun x ↦ φ x * D g x) μ :=
      (integrable_mul_of_hasCompactSupport (μ := μ) (D g) hf).congr
        (ae_of_all _ fun x ↦ mul_comm (D g x) (f x))
    have e₁ : ∫ x, φ x * D₁ g x ∂μ = ∫ x, D f x * g x ∂μ := (h₁ f g hf hg).symm
    have e₂ : ∫ x, φ x * D₂ g x ∂μ = ∫ x, D f x * g x ∂μ := (h₂ f g hf hg).symm
    simp only [u, ContMDiffMap.coe_sub, Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub (hi D₁) (hi D₂), e₁, e₂, sub_self]
  exact sub_eq_zero.1 (ContMDiffMap.coe_injective ((hu.ae_eq_iff_eq μ continuous_const).1 hae))

/-- The formal transpose for one Haar measure is a formal transpose for every Haar measure: any
two Haar measures on `E` are proportional. -/
theorem _root_.LinearMap.IsFormalTranspose.of_isAddHaarMeasure {ν : Measure E}
    [ν.IsAddHaarMeasure] (h : D.IsFormalTranspose D' ν) (μ : Measure E) [μ.IsAddHaarMeasure] :
    D.IsFormalTranspose D' μ := fun f g hf hg ↦ by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, h f g hf hg]

/-! ### The formal transpose -/

private theorem exists_isFormalTranspose_addHaar {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m,
      (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose D'
        (Measure.addHaar : Measure E) :=
  exists_isFormalTranspose D.2

/-- The formal transpose as a function, before linearity is established. -/
private def formalTransposeFun {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m :=
  ⟨(exists_isFormalTranspose_addHaar D).choose, (exists_isFormalTranspose_addHaar D).choose_spec.1⟩

private theorem isFormalTranspose_formalTransposeFun {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) (μ : Measure E) [μ.IsAddHaarMeasure] :
    (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (formalTransposeFun D) μ :=
  (exists_isFormalTranspose_addHaar D).choose_spec.2.of_isAddHaarMeasure μ

private theorem formalTransposeFun_eq {m k : ℕ}
    {D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m} (μ : Measure E) [μ.IsAddHaarMeasure]
    (h : (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose D' μ)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (formalTransposeFun D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) = D' :=
  (isFormalTranspose_formalTransposeFun D μ).eq_of_mem_differentialOperators h
    (formalTransposeFun D).2 hD'

variable (E) in
/-- The **formal transpose** of the differential operators of order at most `m` on `C^∞(E)`, for
Lebesgue measure or any other Haar measure on `E` (`TauCeti.isFormalTranspose_formalTranspose`):
the unique differential operator `Dᵗ` with `∫ (D f) g = ∫ f (Dᵗ g)` for all compactly supported
smooth `f` and `g` (`TauCeti.formalTranspose_eq_of_isFormalTranspose`). It is an involutive linear
equivalence. -/
def formalTranspose (m : ℕ) :
    differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m ≃ₗ[ℝ]
      differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m :=
  LinearEquiv.ofInvolutive
    { toFun := formalTransposeFun
      map_add' D₁ D₂ := Subtype.ext <| formalTransposeFun_eq Measure.addHaar
        ((isFormalTranspose_formalTransposeFun D₁ _).add
          (isFormalTranspose_formalTransposeFun D₂ _))
        (Submodule.add_mem _ (formalTransposeFun D₁).2 (formalTransposeFun D₂).2)
      map_smul' c D := Subtype.ext <| formalTransposeFun_eq Measure.addHaar
        ((isFormalTranspose_formalTransposeFun D _).smul c)
        (Submodule.smul_mem _ c (formalTransposeFun D).2) }
    fun D ↦ Subtype.ext <| formalTransposeFun_eq Measure.addHaar
      (isFormalTranspose_formalTransposeFun D _).symm D.2

/-- The formal transpose of `D` is a formal transpose of `D` for every Haar measure. -/
theorem isFormalTranspose_formalTranspose (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose
      (formalTranspose E m D) μ :=
  isFormalTranspose_formalTransposeFun D μ

/-- A differential operator that is a formal transpose of `D` for some Haar measure is the formal
transpose of `D`. -/
theorem formalTranspose_eq_of_isFormalTranspose (μ : Measure E) [μ.IsAddHaarMeasure] {m k : ℕ}
    {D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m}
    (h : (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose D' μ)
    (hD' : D' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (formalTranspose E m D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) = D' :=
  formalTransposeFun_eq μ h hD'

/-- A differential operator `D'` is the formal transpose of `D` exactly when it is a formal
transpose of `D` for a Haar measure. -/
theorem formalTranspose_eq_iff (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    {D D' : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m} :
    formalTranspose E m D = D' ↔
      (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯).IsFormalTranspose D' μ :=
  ⟨fun h ↦ h ▸ isFormalTranspose_formalTranspose μ D,
    fun h ↦ Subtype.ext (formalTranspose_eq_of_isFormalTranspose μ h D'.2)⟩

@[simp]
theorem formalTranspose_symm (m : ℕ) : (formalTranspose E m).symm = formalTranspose E m :=
  LinearEquiv.ext fun D ↦ (formalTranspose E m).symm_apply_eq.2 <| Subtype.ext <|
    formalTransposeFun_eq Measure.addHaar
      (isFormalTranspose_formalTransposeFun D _).symm D.2 |>.symm

@[simp]
theorem formalTranspose_formalTranspose {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    formalTranspose E m (formalTranspose E m D) = D := by
  conv_lhs => rw [← formalTranspose_symm]
  exact LinearEquiv.symm_apply_apply _ D

/-- An operator of order zero, multiplication by a smooth function, is its own formal transpose. -/
theorem formalTranspose_of_mem_differentialOperators_zero {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    (hD : (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∈
      differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0) :
    formalTranspose E m D = D :=
  (formalTranspose_eq_iff Measure.addHaar).2
    (IsFormalTranspose.self_of_mem_differentialOperators_zero hD)

/-- The formal transpose of the directional derivative `∂_v` is `-∂_v`. -/
theorem formalTranspose_lineDerivation (v : E) :
    (formalTranspose E 1 ⟨lineDerivation ℝ v, (lineDerivation ℝ v).mem_differentialOperators_one⟩ :
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) = -lineDerivation ℝ v :=
  formalTranspose_eq_of_isFormalTranspose Measure.addHaar (isFormalTranspose_lineDerivation v)
    (neg_mem (lineDerivation ℝ v).mem_differentialOperators_one)

/-- **Transposition reverses composition**: `(P ∘ Q)ᵗ = Qᵗ ∘ Pᵗ`. -/
theorem formalTranspose_comp {m k : ℕ}
    (P : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    (Q : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ k) :
    (formalTranspose E (m + k)
        ⟨(P : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ
          (Q : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯),
          comp_mem_differentialOperators P.2 Q.2⟩ :
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) =
      (formalTranspose E k Q : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) ∘ₗ
        (formalTranspose E m P : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :=
  formalTranspose_eq_of_isFormalTranspose Measure.addHaar
    ((isFormalTranspose_formalTranspose _ P).comp (isFormalTranspose_formalTranspose _ Q)
      (fun _ hf ↦ HasCompactSupport.apply_of_mem_differentialOperators hf Q.2)
      (fun _ hg ↦ HasCompactSupport.apply_of_mem_differentialOperators hg
        (formalTranspose E m P).2))
    (comp_mem_differentialOperators (formalTranspose E k Q).2 (formalTranspose E m P).2)

/-! ### The principal symbol of the transpose -/

/-- **The principal symbol of the transpose.** For an operator of order at most `m`,
`σ_geom(Dᵗ)(ξ) = (-1)^m σ_geom(D)(ξ)`. -/
theorem smoothPrincipalSymbol_formalTranspose {x : E} (hx : (𝓘(ℝ, E)).IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) (ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :
    smoothPrincipalSymbol 𝓘(ℝ, E) hx (formalTranspose E m D) ξ =
      (-1) ^ m * smoothPrincipalSymbol 𝓘(ℝ, E) hx D ξ := by
  -- Every covector is the differential of a linear function.
  let ℓ : E →L[ℝ] ℝ := ξ
  let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨ℓ, ℓ.contDiff.contMDiff⟩
  have hf : mvfderiv 𝓘(ℝ, E) f x = ξ := ContinuousLinearMap.ext fun v ↦ by
    rw [mvfderiv_eq_fderiv_apply]
    exact congrArg (· v) ℓ.fderiv
  rw [← hf, smoothPrincipalSymbol_mvfderiv, smoothPrincipalSymbol_mvfderiv]
  -- The `m`-fold commutators `A` and `A'` of `D` and `Dᵗ` have order zero, and `(-1)^m A'` is a
  -- transpose of `A`, which is its own transpose.
  set A := (smulCommutator ℝ f ^ m) (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
  set A' := (smulCommutator ℝ f ^ m)
    (formalTranspose E m D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
  have hA : A ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
    smulCommutator_pow_mem_differentialOperators (by simp) f
  have hA' : A' ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ 0 :=
    smulCommutator_pow_mem_differentialOperators (by simp) f
  have key : (-1 : ℝ) ^ m • A' = A :=
    ((isFormalTranspose_formalTranspose (Measure.addHaar : Measure E) D).smulCommutator_pow
      D.2 (formalTranspose E m D).2 f m).eq_of_mem_differentialOperators
      (IsFormalTranspose.self_of_mem_differentialOperators_zero hA)
      (Submodule.smul_mem _ _ hA') hA
  have hA'A : A' = (-1 : ℝ) ^ m • A := by
    rw [← key, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [hA'A]
  simp only [LinearMap.smul_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end TauCeti
