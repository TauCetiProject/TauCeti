/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# Differential operators on `C^∞(E)` do not enlarge wave front sets

Let `E` be a finite-dimensional real inner product space and `D` a differential operator of order
at most `m` on the smooth functions on `E`, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`). For a distribution `S` on an open set
`Ω ⊆ E`, the functional `φ ↦ S (D φ)` on test functions on `Ω` is again a distribution, and it is
microlocally smooth wherever `S` is
(`Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`).
In coordinates `D = ∑_{|α| ≤ m} c_α ∂^α` (`Module.Basis.eq_coordinateOperator_coordinateCoeff`), so
`φ ↦ S (D φ)` is built from `S` by multiplications by the smooth coefficients `c_α` and
differentiations, neither of which enlarges wave front sets.

## Main results

* `Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`:
  a differential operator on `C^∞(E)` acts on distributions by transposition without enlarging
  their wave front sets.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets).
-/

public section

noncomputable section

open Set Function TopologicalSpace LineDeriv
open scoped ContDiff Manifold Distributions Topology

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- The operator `D` on `C^∞(E)` does not enlarge supports and acts on the distributions on `Ω`
by transposition without enlarging their wave front sets: every `S` has a transpose `R` with
`R φ = S (D φ)` for every test function `φ`, microlocally smooth wherever `S` is. -/
private def HasMicrolocalTranspose (Ω : Opens E)
    (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Prop :=
  (∀ f, tsupport (D f) ⊆ tsupport f) ∧
    ∀ S : 𝓓'(Ω, ℂ), ∃ R : 𝓓'(Ω, ℂ),
      (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) ∧
        ∀ x ξ, S.IsMicrolocallySmoothAt x ξ → R.IsMicrolocallySmoothAt x ξ

namespace HasMicrolocalTranspose

private theorem id : HasMicrolocalTranspose Ω LinearMap.id :=
  ⟨fun _ ↦ subset_rfl, fun S ↦ ⟨S, fun φ ψ f hf hψ ↦ by
    rw [show ψ = φ from TestFunction.ext fun x ↦ by simp [hψ, ← hf]], fun _ _ h ↦ h⟩⟩

private theorem zero : HasMicrolocalTranspose Ω 0 :=
  ⟨fun _ ↦ by simp, fun S ↦ ⟨(0 : ℂ) • S, fun φ ψ f _ hψ ↦ by
    rw [show ψ = 0 from TestFunction.ext fun x ↦ by simp [hψ]]; simp,
    fun _ _ hS ↦ hS.smul 0⟩⟩

private theorem comp {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h₁ : HasMicrolocalTranspose Ω D₁) (h₂ : HasMicrolocalTranspose Ω D₂) :
    HasMicrolocalTranspose Ω (D₁ ∘ₗ D₂) := by
  refine ⟨fun f ↦ (h₁.1 _).trans (h₂.1 f), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := h₁.2 S
  obtain ⟨R, hR, hR'⟩ := h₂.2 R₁
  refine ⟨R, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ hR' x ξ (hR₁' x ξ hS)⟩
  -- The intermediate test function `D₂ φ`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  rw [hR φ χ f hf hχ, hR₁ χ ψ (D₂ f) hχ.symm hψ]

variable [FiniteDimensional ℝ E]

private theorem add {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h₁ : HasMicrolocalTranspose Ω D₁) (h₂ : HasMicrolocalTranspose Ω D₂) :
    HasMicrolocalTranspose Ω (D₁ + D₂) := by
  refine ⟨fun f ↦ (tsupport_add _ _).trans (union_subset (h₁.1 f) (h₂.1 f)), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := h₁.2 S
  obtain ⟨R₂, hR₂, hR₂'⟩ := h₂.2 S
  refine ⟨R₁ + R₂, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ (hR₁' x ξ hS).add (hR₂' x ξ hS)⟩
  obtain ⟨ψ₁, hψ₁⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₁ f).contMDiff) (hf ▸ h₁.1 f)
  obtain ⟨ψ₂, hψ₂⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  have hψ' : ψ = ψ₁ + ψ₂ := TestFunction.ext fun x ↦ by simp [hψ, hψ₁, hψ₂]
  simp [hR₁ φ ψ₁ f hf hψ₁, hR₂ φ ψ₂ f hf hψ₂, hψ']

private theorem sum {ι : Type*} (s : Finset ι)
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h : ∀ i ∈ s, HasMicrolocalTranspose Ω (D i)) :
    HasMicrolocalTranspose Ω (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (LinearMap.mulLeft ℝ c) := by
  have hc : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.1 c.contMDiff
  refine ⟨fun f ↦ tsupport_mul_subset_right, fun S ↦
    ⟨smulLeftCLM hc S, fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ hS.smulLeftCLM hc⟩⟩
  rw [smulLeftCLM_apply, show TestFunction.smulLeftCLM hc φ = ψ from
    TestFunction.ext fun x ↦ by simp [hψ, ← hf]]

private theorem lineDerivation (v : E) :
    HasMicrolocalTranspose Ω (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] _) := by
  refine ⟨fun f ↦ TauCeti.tsupport_lineDerivation_apply_subset v f, fun S ↦
    ⟨∂_{v} ((-1 : ℂ) • S), fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ (hS.smul (-1)).lineDerivOp v⟩⟩
  rw [lineDerivOp_apply_apply, show ψ = ∂_{v} φ from TestFunction.ext fun x ↦ by
    rw [hψ, TestFunction.lineDerivOp_apply_eq_fderiv, ← hf]
    exact TauCeti.lineDerivation_apply_apply v f x]
  simp

private theorem multiIndexDeriv {ι : Type*} [Fintype ι] (v : ι → E) (α : ι → ℕ) :
    HasMicrolocalTranspose Ω (TauCeti.multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) α) := by
  classical
  induction α using TauCeti.multiIndex_induction_add_single with
  | zero => simpa [Module.End.one_eq_id] using id
  | add_single α i ih =>
    rw [TauCeti.multiIndexDeriv_add_single, Module.End.mul_eq_comp]
    exact ih.comp (lineDerivation (v i))

private theorem coordinateOperator {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (m : ℕ)
    (c : (ι → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (TauCeti.coordinateOperator
      (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) m c) := by
  rw [TauCeti.coordinateOperator_eq_sum_mulLeft]
  exact sum _ fun k _ ↦ sum _ fun α _ ↦ (mulLeft (c α)).comp (multiIndexDeriv v α)

end HasMicrolocalTranspose

variable [FiniteDimensional ℝ E]

/-- **Differential operators act on distributions without enlarging wave front sets.** Let `D` be
a differential operator of order at most `m` on the smooth functions on `E`, in Grothendieck's
sense of iterated commutators with multiplication operators. For every distribution `S` on an open
set `Ω`, the functional `φ ↦ S (D φ)` on test functions on `Ω` is a distribution `R`, and `R` is
microlocally smooth at every point and direction at which `S` is. -/
theorem exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    (S : 𝓓'(Ω, ℂ)) :
    ∃ R : 𝓓'(Ω, ℂ), (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f →
      R φ = S ψ) ∧ ∀ x ξ, S.IsMicrolocallySmoothAt x ξ → R.IsMicrolocallySmoothAt x ξ := by
  classical
  have hD' := (Module.finBasis ℝ E).eq_coordinateOperator_coordinateCoeff hD
  exact (hD' ▸ HasMicrolocalTranspose.coordinateOperator _ m _).2 S

end Distribution
