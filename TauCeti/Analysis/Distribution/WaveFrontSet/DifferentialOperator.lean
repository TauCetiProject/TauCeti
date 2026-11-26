/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv

/-!
# Differential operators on `C^∞(E)` and wave front sets

Let `E` be a finite-dimensional real inner product space and `D` a differential operator of order
at most `m` on the smooth functions on `E`, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`). For a distribution `S` on an open set
`Ω ⊆ E`, the functional `φ ↦ S (D φ)` on test functions on `Ω` is again a distribution, and it is
microlocally smooth wherever `S` is
(`Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`).
It costs at most `m` orders of Sobolev regularity: it is microlocally `H^(s - m)` wherever `S` is
microlocally `H^s`, so that `WF_(s - m)(S ∘ D) ⊆ WF_s(S)`, and `H^(s - m)` near every point near
which `S` is `H^s`
(`Distribution.exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators`).
In coordinates `D = ∑_{|α| ≤ m} c_α ∂^α` (`Module.Basis.eq_coordinateOperator_coordinateCoeff`), so
`φ ↦ S (D φ)` is built from `S` by multiplications by the smooth coefficients `c_α`, which enlarge
neither wave front sets nor `H^s` wave front sets, and differentiations, which do not enlarge wave
front sets and cost one order of Sobolev regularity each.

## Main results

* `Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`:
  a differential operator on `C^∞(E)` acts on distributions by transposition without enlarging
  their wave front sets.
* `Distribution.exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators`:
  a differential operator of order at most `m` on `C^∞(E)` acts on distributions by transposition,
  costing at most `m` orders of microlocal and of local Sobolev regularity.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its behaviour under differential operators).
-/

public section

noncomputable section

open Set Function TopologicalSpace LineDeriv
open scoped ContDiff Manifold Distributions Topology

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

section Transpose

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The operator `D` on `C^∞(E)` does not enlarge supports and acts on the distributions on `Ω`
by transposition: every `S` has a transpose `R` with `R φ = S (D φ)` for every test function `φ`,
microlocally smooth wherever `S` is and microlocally `H^(s - k)` wherever `S` is microlocally
`H^s`. -/
private def HasMicrolocalTranspose (Ω : Opens E)
    (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (k : ℕ) : Prop :=
  (∀ f, tsupport (D f) ⊆ tsupport f) ∧
    ∀ S : 𝓓'(Ω, ℂ), ∃ R : 𝓓'(Ω, ℂ),
      (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) ∧
        (∀ x ξ, S.IsMicrolocallySmoothAt x ξ → R.IsMicrolocallySmoothAt x ξ) ∧
        ∀ s x ξ, S.IsMicrolocallySobolevAt s x ξ → R.IsMicrolocallySobolevAt (s - k) x ξ

namespace HasMicrolocalTranspose

private theorem mono {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {k k' : ℕ}
    (h : HasMicrolocalTranspose Ω D k) (hk : k ≤ k') : HasMicrolocalTranspose Ω D k' := by
  refine ⟨h.1, fun S ↦ ?_⟩
  obtain ⟨R, hR, hR', hR''⟩ := h.2 S
  exact ⟨R, hR, hR', fun s x ξ hS ↦ (hR'' s x ξ hS).mono (by gcongr)⟩

private theorem id : HasMicrolocalTranspose Ω LinearMap.id 0 :=
  ⟨fun _ ↦ subset_rfl, fun S ↦ ⟨S, fun φ ψ f hf hψ ↦ by
    rw [show ψ = φ from TestFunction.ext fun x ↦ by simp [hψ, ← hf]], fun _ _ h ↦ h,
    fun _ _ _ h ↦ by simpa using h⟩⟩

private theorem zero (k : ℕ) : HasMicrolocalTranspose Ω 0 k :=
  ⟨fun _ ↦ by simp, fun S ↦ ⟨(0 : ℂ) • S, fun φ ψ f _ hψ ↦ by
    rw [show ψ = 0 from TestFunction.ext fun x ↦ by simp [hψ]]; simp,
    fun _ _ hS ↦ hS.smul 0, fun _ _ _ hS ↦ (hS.smul 0).mono (sub_le_self _ k.cast_nonneg)⟩⟩

private theorem comp {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {k₁ k₂ : ℕ}
    (h₁ : HasMicrolocalTranspose Ω D₁ k₁) (h₂ : HasMicrolocalTranspose Ω D₂ k₂) :
    HasMicrolocalTranspose Ω (D₁ ∘ₗ D₂) (k₁ + k₂) := by
  refine ⟨fun f ↦ (h₁.1 _).trans (h₂.1 f), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁', hR₁''⟩ := h₁.2 S
  obtain ⟨R, hR, hR', hR''⟩ := h₂.2 R₁
  refine ⟨R, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ hR' x ξ (hR₁' x ξ hS),
    fun s x ξ hS ↦ by simpa [sub_sub] using hR'' _ x ξ (hR₁'' s x ξ hS)⟩
  -- The intermediate test function `D₂ φ`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  rw [hR φ χ f hf hχ, hR₁ χ ψ (D₂ f) hχ.symm hψ]

private theorem add {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {k : ℕ}
    (h₁ : HasMicrolocalTranspose Ω D₁ k) (h₂ : HasMicrolocalTranspose Ω D₂ k) :
    HasMicrolocalTranspose Ω (D₁ + D₂) k := by
  refine ⟨fun f ↦ (tsupport_add _ _).trans (union_subset (h₁.1 f) (h₂.1 f)), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁', hR₁''⟩ := h₁.2 S
  obtain ⟨R₂, hR₂, hR₂', hR₂''⟩ := h₂.2 S
  refine ⟨R₁ + R₂, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ (hR₁' x ξ hS).add (hR₂' x ξ hS),
    fun s x ξ hS ↦ (hR₁'' s x ξ hS).add (hR₂'' s x ξ hS)⟩
  obtain ⟨ψ₁, hψ₁⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₁ f).contMDiff) (hf ▸ h₁.1 f)
  obtain ⟨ψ₂, hψ₂⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  have hψ' : ψ = ψ₁ + ψ₂ := TestFunction.ext fun x ↦ by simp [hψ, hψ₁, hψ₂]
  simp [hR₁ φ ψ₁ f hf hψ₁, hR₂ φ ψ₂ f hf hψ₂, hψ']

private theorem sum {ι : Type*} (s : Finset ι)
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {k : ℕ}
    (h : ∀ i ∈ s, HasMicrolocalTranspose Ω (D i) k) :
    HasMicrolocalTranspose Ω (∑ i ∈ s, D i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero k
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (LinearMap.mulLeft ℝ c) 0 := by
  have hc : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.1 c.contMDiff
  refine ⟨fun f ↦ tsupport_mul_subset_right, fun S ↦
    ⟨smulLeftCLM hc S, fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ hS.smulLeftCLM hc,
      fun _ _ _ hS ↦ by simpa using hS.smulLeftCLM hc⟩⟩
  rw [smulLeftCLM_apply, show TestFunction.smulLeftCLM hc φ = ψ from
    TestFunction.ext fun x ↦ by simp [hψ, ← hf]]

private theorem lineDerivation (v : E) :
    HasMicrolocalTranspose Ω (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] _) 1 := by
  refine ⟨fun f ↦ TauCeti.tsupport_lineDerivation_apply_subset v f, fun S ↦
    ⟨∂_{v} ((-1 : ℂ) • S), fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ (hS.smul (-1)).lineDerivOp v,
      fun _ _ _ hS ↦ by simpa using (hS.smul (-1)).lineDerivOp v⟩⟩
  rw [lineDerivOp_apply_apply, show ψ = ∂_{v} φ from TestFunction.ext fun x ↦ by
    rw [hψ, TestFunction.lineDerivOp_apply_eq_fderiv, ← hf]
    exact TauCeti.lineDerivation_apply_apply v f x]
  simp

private theorem multiIndexDeriv {ι : Type*} [Fintype ι] (v : ι → E) (α : ι → ℕ) :
    HasMicrolocalTranspose Ω (TauCeti.multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) α) (∑ i, α i) := by
  classical
  induction α using TauCeti.multiIndex_induction_add_single with
  | zero => simpa [Module.End.one_eq_id] using id
  | add_single α i ih =>
    rw [TauCeti.multiIndexDeriv_add_single, Module.End.mul_eq_comp]
    convert ih.comp (lineDerivation (v i)) using 1
    simp [Finset.sum_add_distrib]

private theorem coordinateOperator {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (m : ℕ)
    (c : (ι → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (TauCeti.coordinateOperator
      (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) m c) m := by
  rw [TauCeti.coordinateOperator_eq_sum_mulLeft]
  refine sum _ fun k hk ↦ sum _ fun α hα ↦ ((mulLeft (c α)).comp (multiIndexDeriv v α)).mono ?_
  rw [Finset.mem_piAntidiag] at hα
  rw [zero_add, hα.1]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)

end HasMicrolocalTranspose

/-- A differential operator `D` of order at most `m` on `C^∞(E)` acts on the distributions on `Ω`
by transposition, with the regularity bounds of `HasMicrolocalTranspose`. -/
private theorem hasMicrolocalTranspose_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    HasMicrolocalTranspose Ω D m := by
  classical
  have hD' := (Module.finBasis ℝ E).eq_coordinateOperator_coordinateCoeff hD
  exact hD' ▸ HasMicrolocalTranspose.coordinateOperator _ m _

/-- **Differential operators shift Sobolev regularity by their order.** Let `D` be a differential
operator of order at most `m` on the smooth functions on `E`, in Grothendieck's sense of iterated
commutators with multiplication operators. For every distribution `S` on an open set `Ω`, the
functional `φ ↦ S (D φ)` on test functions on `Ω` is a distribution `R`, which is microlocally
`H^(s - m)` at every point and direction at which `S` is microlocally `H^s`, and `H^(s - m)` near
every point near which `S` is `H^s`. -/
theorem exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    (S : 𝓓'(Ω, ℂ)) :
    ∃ R : 𝓓'(Ω, ℂ), (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f →
      R φ = S ψ) ∧
      (∀ s x ξ, S.IsMicrolocallySobolevAt s x ξ → R.IsMicrolocallySobolevAt (s - m) x ξ) ∧
      ∀ s x, S.IsLocallySobolevAt s x → R.IsLocallySobolevAt (s - m) x := by
  obtain ⟨R, hR, -, hR'⟩ := (hasMicrolocalTranspose_of_mem_differentialOperators hD).2 S
  refine ⟨R, hR, hR', fun s x hS ↦ ?_⟩
  -- Local `H^s` regularity is microlocal `H^s` regularity in every nonzero direction.
  exact (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hS.mem).2 fun ξ _ ↦
    hR' s x ξ (hS.isMicrolocallySobolevAt ξ)

end Transpose

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
  -- Any Borel structure on `E` serves for the regularity bounds, which are not used here.
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨R, hR, hR', -⟩ := (hasMicrolocalTranspose_of_mem_differentialOperators hD).2 S
  exact ⟨R, hR, hR'⟩

end Distribution
