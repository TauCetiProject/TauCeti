/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Topology.Homotopy.AddCircle

/-!
# The contractible almost existence property

Let `σ` be a two-form on a manifold `M`, `W ⊆ M` and `F : M → ℝ`. The level `F⁻¹(c)` **carries a
closed characteristic contractible in `W`**
(`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic`) when the Hamiltonian vector field
`X_F` has a nonconstant `T`-periodic integral curve `γ`, `T > 0`, lying in `F⁻¹(c)`, whose loop
`ℝ/Tℤ → W` is contractible in `W`. On a regular level of a nondegenerate form such orbits trace
the closed leaves of the characteristic foliation, and they do not depend on the defining function
of the level up to reparametrization
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_homeomorph_isMIntegralCurve_comp`).

The level `F⁻¹(c)` has the **contractible almost existence property** in `W`
(`TauCeti.SmoothTwoForm.HasContractibleAlmostExistence`) when for some `ε > 0`, almost every
regular level `F⁻¹(c')` with `c' ∈ (c - ε, c + ε)` carries a closed characteristic contractible in
`W`. This is Definition 1.1 of Barraud, Damian, Humilière and Oancea, where `F` is a proper smooth
function on a symplectic manifold `W` and `F⁻¹(c)` is a regular level in the interior of `W`; here
`W` is a subset of an ambient manifold, and these standing assumptions are hypotheses of the
theorems that establish the property rather than part of its definition. By the Hofer–Zehnder
monotonicity argument, finiteness of the `π₁`-sensitive Hofer–Zehnder capacity
(`TauCeti.SmoothTwoForm.contractibleHZCapacity`) of `W` gives the property for every such level.

Closed characteristics survive every change of the Hamiltonian which rescales the Hamiltonian
vector field along the level by a nonzero constant
(`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.of_hamiltonianVectorField_eq_smul`):
the orbit is run at constant speed `a`, or backwards when `a < 0`, and its loop stays contractible.
In particular a closed characteristic on `F⁻¹(c)` is one on the level `φ(c)` of `φ ∘ F` whenever
`φ'(c) ≠ 0` (`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.comp`), which is how the
monotonicity argument passes from the Hamiltonians `φ ∘ F` competing for the capacity to the
levels of `F`. Rescaling the form by `a ≠ 0` changes neither notion
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleClosedCharacteristic_smul_iff`,
`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence_smul_iff`), and both are
monotone in `W`.

## Main definitions

* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic`: a level carries a closed
  characteristic contractible in `W`.
* `TauCeti.SmoothTwoForm.HasContractibleAlmostExistence`: the contractible almost existence
  property of a level.

## Main results

* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.of_hamiltonianVectorField_eq_smul`:
  closed characteristics are preserved by constant rescalings of the Hamiltonian vector field
  along the level.
* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.comp`: closed characteristics of
  `F⁻¹(c)` are closed characteristics of the level `φ(c)` of `φ ∘ F` when `φ'(c) ≠ 0`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence_smul_iff`: the property
  is conformally invariant.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 1.1.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (the almost existence theorem).
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ σ' : SmoothTwoForm I M} {W W' : Set M} {F G : M → ℝ} {c c' : ℝ}

/-! ### Closed characteristics contractible in `W` -/

variable (σ W F c) in
/-- The level `F⁻¹(c)` **carries a closed characteristic contractible in `W`**: the Hamiltonian
vector field of `F` has a nonconstant `T`-periodic integral curve with `T > 0`, contained in the
level, whose loop `ℝ/Tℤ → W` is contractible in `W`. -/
def HasContractibleClosedCharacteristic : Prop :=
  ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField F) ∧
    Periodic γ T ∧ (∃ t, γ t ≠ γ 0) ∧ (∀ t, F (γ t) = c) ∧
    ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t

theorem hasContractibleClosedCharacteristic_iff :
    σ.HasContractibleClosedCharacteristic W F c ↔
      ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField F) ∧
        Periodic γ T ∧ (∃ t, γ t ≠ γ 0) ∧ (∀ t, F (γ t) = c) ∧
        ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t :=
  Iff.rfl

/-- A closed characteristic contractible in `W` is contractible in every larger set. -/
theorem HasContractibleClosedCharacteristic.mono
    (h : σ.HasContractibleClosedCharacteristic W F c) (hW : W ⊆ W') :
    σ.HasContractibleClosedCharacteristic W' F c := by
  obtain ⟨T, γ, hT, hγ, hper, hne, hlev, g, hg, hgγ⟩ := h
  exact ⟨T, γ, hT, hγ, hper, hne, hlev,
    (⟨inclusion hW, continuous_inclusion hW⟩ : C(W, W')).comp g,
    hg.comp_right _, hgγ⟩

/-- **Closed characteristics under rescaled Hamiltonian vector fields.** Let the level `F⁻¹(c)`
lie in the level `G⁻¹(c')`, and let the Hamiltonian vector field of `G` for a second form `σ'` be
`a` times that of `F` along `F⁻¹(c)`, for a constant `a ≠ 0`. Then every closed characteristic of
`F⁻¹(c)` contractible in `W`, run at speed `a`, is one of `G⁻¹(c')`. -/
theorem HasContractibleClosedCharacteristic.of_hamiltonianVectorField_eq_smul
    (h : σ.HasContractibleClosedCharacteristic W F c) {a : ℝ} (ha : a ≠ 0)
    (hG : ∀ x, F x = c → G x = c')
    (hX : ∀ x, F x = c →
      σ'.hamiltonianVectorField G x = a • σ.hamiltonianVectorField F x) :
    σ'.HasContractibleClosedCharacteristic W G c' := by
  obtain ⟨T, γ, hT, hγ, -, ⟨t₀, ht₀⟩, hlev, g, hg, hgγ⟩ := h
  obtain ⟨g', hg', hgg'⟩ := hg.exists_addCircle_comp_mul hT.ne' ha
  have hgγ' (t : ℝ) : (g' t : M) = γ (t * a) := by rw [hgg', hgγ]
  refine ⟨T / |a|, fun t ↦ γ (t * a), div_pos hT (abs_pos.2 ha), fun t ↦ ?_, fun t ↦ ?_,
    ⟨t₀ / a, ?_⟩, fun t ↦ hG _ (hlev _), g', hg', hgγ'⟩
  · rw [hX _ (hlev _)]
    exact hγ.comp_mul a t
  · simp only [← hgγ', AddCircle.coe_add_period]
  · simpa [div_mul_cancel₀ _ ha] using ht₀

/-- **Closed characteristics under reparametrization of the energy.** If `φ` is differentiable at
`c` with `φ'(c) ≠ 0` and `F` is differentiable along `F⁻¹(c)`, then a closed characteristic of
`F⁻¹(c)` contractible in `W` is one of the level `φ(c)` of `φ ∘ F`, since
`X_{φ ∘ F} = φ'(c) X_F` along `F⁻¹(c)`. -/
theorem HasContractibleClosedCharacteristic.comp
    (h : σ.HasContractibleClosedCharacteristic W F c) {φ : ℝ → ℝ}
    (hφ : DifferentiableAt ℝ φ c) (hφ' : deriv φ c ≠ 0)
    (hF : ∀ x, F x = c → MDifferentiableAt I 𝓘(ℝ) F x) :
    σ.HasContractibleClosedCharacteristic W (φ ∘ F) (φ c) :=
  h.of_hamiltonianVectorField_eq_smul hφ' (fun x hx ↦ by simp [hx]) fun x hx ↦ by
    rw [hamiltonianVectorField_comp (hx ▸ hφ) (hF x hx), hx]

/-- **Conformal invariance of closed characteristics.** For a nondegenerate form on a
finite-dimensional manifold and `a ≠ 0`, the closed characteristics contractible in `W` of `aσ`
and of `σ` are the same: `X^{aσ}_F = a⁻¹ X^σ_F`. -/
theorem IsNondegenerate.hasContractibleClosedCharacteristic_smul_iff [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) {a : ℝ} (ha : a ≠ 0) :
    (a • σ).HasContractibleClosedCharacteristic W F c ↔
      σ.HasContractibleClosedCharacteristic W F c := by
  refine ⟨fun h ↦ h.of_hamiltonianVectorField_eq_smul ha (fun _ ↦ id) fun x _ ↦ ?_,
    fun h ↦ h.of_hamiltonianVectorField_eq_smul (inv_ne_zero ha) (fun _ ↦ id) fun x _ ↦ ?_⟩
  · rw [hσ.hamiltonianVectorField_smul ha, Pi.smul_apply, smul_inv_smul₀ ha]
  · rw [hσ.hamiltonianVectorField_smul ha, Pi.smul_apply]

/-! ### The contractible almost existence property -/

variable (σ W F c) in
/-- The level `F⁻¹(c)` has the **contractible almost existence property** in `W` when for some
`ε > 0`, almost every regular level `F⁻¹(c')` with `c' ∈ (c - ε, c + ε)` carries a closed
characteristic contractible in `W` (Barraud–Damian–Humilière–Oancea, Definition 1.1). -/
def HasContractibleAlmostExistence : Prop :=
  ∃ ε > 0, ∀ᵐ c' : ℝ, c' ∈ Ioo (c - ε) (c + ε) → IsRegularValue I 𝓘(ℝ) F c' →
    σ.HasContractibleClosedCharacteristic W F c'

theorem hasContractibleAlmostExistence_iff :
    σ.HasContractibleAlmostExistence W F c ↔
      ∃ ε > 0, ∀ᵐ c' : ℝ, c' ∈ Ioo (c - ε) (c + ε) → IsRegularValue I 𝓘(ℝ) F c' →
        σ.HasContractibleClosedCharacteristic W F c' :=
  Iff.rfl

/-- The contractible almost existence property in `W` implies it in every larger set. -/
theorem HasContractibleAlmostExistence.mono (h : σ.HasContractibleAlmostExistence W F c)
    (hW : W ⊆ W') : σ.HasContractibleAlmostExistence W' F c := by
  obtain ⟨ε, hε, hae⟩ := h
  exact ⟨ε, hε, hae.mono fun _ hc' hmem hreg ↦ (hc' hmem hreg).mono hW⟩

/-- **Conformal invariance of almost existence.** For a nondegenerate form on a
finite-dimensional manifold and `a ≠ 0`, a level has the contractible almost existence property
for `aσ` exactly when it has it for `σ`. -/
theorem IsNondegenerate.hasContractibleAlmostExistence_smul_iff [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) {a : ℝ} (ha : a ≠ 0) :
    (a • σ).HasContractibleAlmostExistence W F c ↔ σ.HasContractibleAlmostExistence W F c := by
  simp only [hasContractibleAlmostExistence_iff, hσ.hasContractibleClosedCharacteristic_smul_iff ha]

end SmoothTwoForm

end TauCeti
