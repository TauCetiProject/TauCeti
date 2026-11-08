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
import TauCeti.Geometry.Symplectic.Manifold.Rescale
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
* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristicOfPeriodLE`: a level carries a closed
  characteristic contractible in `W` of period at most `τ`.
* `TauCeti.SmoothTwoForm.HasContractibleAlmostExistence`: the contractible almost existence
  property of a level.

## Main results

* `TauCeti.SmoothTwoForm.hasContractibleClosedCharacteristicOfPeriodLE_of_isMIntegralCurve_smul`:
  a contractible periodic orbit of a rescaled Hamiltonian vector field, run at the compensating
  speed, is a closed characteristic, with the period rescaled accordingly.
* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.of_hamiltonianVectorField_eq_smul`:
  closed characteristics are preserved by constant rescalings of the Hamiltonian vector field
  along the level.
* `TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic.comp`: closed characteristics of
  `F⁻¹(c)` are closed characteristics of the level `φ(c)` of `φ ∘ F` when `φ'(c) ≠ 0`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence_smul_iff`: the property
  is conformally invariant.
* `TauCeti.SmoothTwoForm.HasContractibleAlmostExistence.exists_hasContractibleClosedCharacteristic`:
  when the nearby values are regular, almost existence gives closed characteristics on levels
  arbitrarily close to the given one.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleClosedCharacteristic_image_iff`: closed
  characteristics are invariant under symplectic diffeomorphisms, and by its variant
  `IsNondegenerate.hasContractibleClosedCharacteristic_image_iff_of_mpullback_eq_smul` under
  conformally symplectic ones.

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

/-! ### Closed characteristics of bounded period -/

variable (σ W F c) in
/-- The level `F⁻¹(c)` **carries a closed characteristic contractible in `W` of period at most
`τ`**: the Hamiltonian vector field of `F` has a nonconstant `T`-periodic integral curve with
`0 < T ≤ τ`, contained in the level, whose loop `ℝ/Tℤ → W` is contractible in `W`. A bound on the
period is what the Hofer–Zehnder monotonicity argument produces near a level, and what a limit of
closed characteristics on nearby levels needs. -/
def HasContractibleClosedCharacteristicOfPeriodLE (τ : ℝ) : Prop :=
  ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ T ≤ τ ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField F) ∧
    Periodic γ T ∧ (∃ t, γ t ≠ γ 0) ∧ (∀ t, F (γ t) = c) ∧
    ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t

theorem hasContractibleClosedCharacteristicOfPeriodLE_iff {τ : ℝ} :
    σ.HasContractibleClosedCharacteristicOfPeriodLE W F c τ ↔
      ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ T ≤ τ ∧ IsMIntegralCurve γ (σ.hamiltonianVectorField F) ∧
        Periodic γ T ∧ (∃ t, γ t ≠ γ 0) ∧ (∀ t, F (γ t) = c) ∧
        ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t :=
  Iff.rfl

/-- A level carries a closed characteristic contractible in `W` exactly when it carries one of
some bounded period. -/
theorem hasContractibleClosedCharacteristic_iff_exists_ofPeriodLE :
    σ.HasContractibleClosedCharacteristic W F c ↔
      ∃ τ, σ.HasContractibleClosedCharacteristicOfPeriodLE W F c τ := by
  refine ⟨fun ⟨T, γ, hT, h⟩ ↦ ⟨T, T, γ, hT, le_rfl, h⟩, fun ⟨_, T, γ, hT, _, h⟩ ↦ ⟨T, γ, hT, h⟩⟩

/-- A closed characteristic of bounded period is a closed characteristic. -/
theorem HasContractibleClosedCharacteristicOfPeriodLE.hasContractibleClosedCharacteristic
    {τ : ℝ} (h : σ.HasContractibleClosedCharacteristicOfPeriodLE W F c τ) :
    σ.HasContractibleClosedCharacteristic W F c :=
  hasContractibleClosedCharacteristic_iff_exists_ofPeriodLE.2 ⟨τ, h⟩

/-- A closed characteristic contractible in `W` of period at most `τ` is contractible in every
larger set and has period at most every `τ' ≥ τ`. -/
theorem HasContractibleClosedCharacteristicOfPeriodLE.mono {τ τ' : ℝ}
    (h : σ.HasContractibleClosedCharacteristicOfPeriodLE W F c τ) (hW : W ⊆ W') (hτ : τ ≤ τ') :
    σ.HasContractibleClosedCharacteristicOfPeriodLE W' F c τ' := by
  obtain ⟨T, γ, hT, hTτ, hγ, hper, hne, hlev, g, hg, hgγ⟩ := h
  exact ⟨T, γ, hT, hTτ.trans hτ, hγ, hper, hne, hlev,
    (⟨inclusion hW, continuous_inclusion hW⟩ : C(W, W')).comp g, hg.comp_right _, hgγ⟩

/-- **Rescaling a contractible periodic orbit.** Let `γ` be a nonconstant integral curve of
`a⁻¹ X_F`, `a ≠ 0`, lying in the level `F⁻¹(c)` and lifting a loop `ℝ/Tℤ → W`, `T > 0`, which is
contractible in `W`. Then `t ↦ γ (t a)` is a closed characteristic of `F⁻¹(c)` contractible in `W`
of period `T / |a|`. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_isMIntegralCurve_smul {T a : ℝ}
    {γ : ℝ → M} (hT : 0 < T) (ha : a ≠ 0)
    (hγ : IsMIntegralCurve γ (a⁻¹ • σ.hamiltonianVectorField F)) (hne : ∃ t, γ t ≠ γ 0)
    (hlev : ∀ t, F (γ t) = c)
    (hg : ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE W F c (T / |a|) := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨g, hg, hgγ⟩ := hg
  obtain ⟨g', hg', hgg'⟩ := hg.exists_addCircle_comp_mul hT.ne' ha
  have hgγ' (t : ℝ) : (g' t : M) = γ (t * a) := by rw [hgg', hgγ]
  have hγa := hγ.comp_mul a
  rw [smul_smul, mul_inv_cancel₀ ha, one_smul] at hγa
  refine ⟨T / |a|, fun t ↦ γ (t * a), div_pos hT (abs_pos.2 ha), le_rfl, hγa, fun t ↦ ?_,
    ⟨t₀ / a, ?_⟩, fun t ↦ hlev _, g', hg', hgγ'⟩
  · simp only [← hgγ', AddCircle.coe_add_period]
  · simpa [div_mul_cancel₀ _ ha] using ht₀

/-! ### Rescaling closed characteristics -/

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
  obtain ⟨T, γ, hT, hγ, -, hne, hlev, hg⟩ := h
  refine (hasContractibleClosedCharacteristicOfPeriodLE_of_isMIntegralCurve_smul hT ha
    (fun t ↦ ?_) hne (fun t ↦ hG _ (hlev t)) hg).hasContractibleClosedCharacteristic
  rw [Pi.smul_apply, hX _ (hlev t), inv_smul_smul₀ ha]
  exact hγ t

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

/-- **Almost existence gives nearby closed characteristics.** If a level `F⁻¹(c)` has the
contractible almost existence property in `W`, and every value in `(c - δ, c + δ)` is regular, then
some level `F⁻¹(c')` with `c' ∈ (c - δ, c + δ)` carries a closed characteristic contractible in
`W`. -/
theorem HasContractibleAlmostExistence.exists_hasContractibleClosedCharacteristic
    (h : σ.HasContractibleAlmostExistence W F c) {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ c' ∈ Ioo (c - δ) (c + δ), IsRegularValue I 𝓘(ℝ) F c') :
    ∃ c' ∈ Ioo (c - δ) (c + δ), σ.HasContractibleClosedCharacteristic W F c' := by
  obtain ⟨ε, hε, hae⟩ := h
  set η := min δ ε
  have hηδ : η ≤ δ := min_le_left δ ε
  have hηε : η ≤ ε := min_le_right δ ε
  -- Almost every value of the nonempty interval `(c - η, c + η)` gives such a level.
  obtain ⟨c', hc', h'⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := Ioo (c - η) (c + η))
    (by rw [Real.volume_Ioo, Ne, ENNReal.ofReal_eq_zero, not_le]; linarith [lt_min hδ hε])
    (ae_restrict_of_ae hae)
  have hcδ : c' ∈ Ioo (c - δ) (c + δ) := Ioo_subset_Ioo (by linarith) (by linarith) hc'
  have hcε : c' ∈ Ioo (c - ε) (c + ε) := Ioo_subset_Ioo (by linarith) (by linarith) hc'
  exact ⟨c', hcδ, h' hcε (hreg c' hcδ)⟩

/-- **Conformal invariance of almost existence.** For a nondegenerate form on a
finite-dimensional manifold and `a ≠ 0`, a level has the contractible almost existence property
for `aσ` exactly when it has it for `σ`. -/
theorem IsNondegenerate.hasContractibleAlmostExistence_smul_iff [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) {a : ℝ} (ha : a ≠ 0) :
    (a • σ).HasContractibleAlmostExistence W F c ↔ σ.HasContractibleAlmostExistence W F c := by
  simp only [hasContractibleAlmostExistence_iff, hσ.hasContractibleClosedCharacteristic_smul_iff ha]

/-! ### Invariance under symplectomorphisms -/

section Invariance

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- **Symplectomorphisms carry closed characteristics to closed characteristics.** If a
diffeomorphism `ψ : M → M₂` pulls a nondegenerate form `σ₂` back to `σ`, and `F` is differentiable
along its level `F⁻¹(c)`, then the image under `ψ` of a closed characteristic of `F⁻¹(c)`
contractible in `W` is a closed characteristic of the level `c` of `F ∘ ψ⁻¹`, contractible in
`ψ(W)`. -/
theorem HasContractibleClosedCharacteristic.image (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hF : ∀ x, F x = c → MDifferentiableAt I 𝓘(ℝ) F x)
    (h : σ.HasContractibleClosedCharacteristic W F c) :
    σ₂.HasContractibleClosedCharacteristic (ψ '' W) (F ∘ ψ.symm) c := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  obtain ⟨T, γ, hT, hγ, hper, ⟨t₀, ht₀⟩, hlev, g, hg, hgγ⟩ := h
  have hFψ : (F ∘ ψ.symm) ∘ ψ = F := funext fun x ↦ by simp
  refine ⟨T, ψ ∘ γ, hT, ?_, hper.comp ψ, ⟨t₀, fun h ↦ ht₀ (ψ.injective h)⟩,
    fun t ↦ by simp [hlev], (⟨fun x ↦ ⟨ψ x, mem_image_of_mem ψ x.2⟩, by fun_prop⟩ :
      C(W, ψ '' W)).comp g, hg.comp_right _, fun t ↦ by simp [hgγ]⟩
  refine hσ.isMIntegralCurve_comp_hamiltonianVectorField ψ.contMDiff hψ
    (fun _ ↦ (ψ.isInvertible_mfderiv (by simp)).surjective) (fun t ↦ ?_) (by rwa [hFψ])
  -- `F ∘ ψ⁻¹` is differentiable at `ψ (γ t)` because `F` is differentiable at `γ t`.
  have hFt := hF _ (hlev t)
  rw [← ψ.symm_apply_apply (γ t)] at hFt
  exact hFt.comp _ ((ψ.symm.contMDiff _).mdifferentiableAt (by simp))

/-- **Closed characteristics are symplectically invariant.** If a diffeomorphism `ψ : M → M₂`
pulls a nondegenerate form `σ₂` back to `σ`, and `F` is differentiable along its level `F⁻¹(c)`,
then the level `c` of `F ∘ ψ⁻¹` carries a closed characteristic contractible in `ψ(W)` exactly
when `F⁻¹(c)` carries one contractible in `W`. -/
theorem IsNondegenerate.hasContractibleClosedCharacteristic_image_iff
    (hσ₂ : σ₂.IsNondegenerate) (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hF : ∀ x, F x = c → MDifferentiableAt I 𝓘(ℝ) F x) :
    σ₂.HasContractibleClosedCharacteristic (ψ '' W) (F ∘ ψ.symm) c ↔
      σ.HasContractibleClosedCharacteristic W F c := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image hσ₂ ψ hψ hF⟩
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  have hF' (y : M₂) (hy : (F ∘ ψ.symm) y = c) : MDifferentiableAt I₂ 𝓘(ℝ) (F ∘ ψ.symm) y :=
    (hF _ hy).comp y ((ψ.symm.contMDiff _).mdifferentiableAt (by simp))
  have h' := h.image hσ ψ.symm (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ) hF'
  -- `Diffeomorph.symm` is involutive by definition.
  have hψ' : ψ.symm.symm = ψ := rfl
  have hFψ : (F ∘ ψ.symm) ∘ ψ = F := funext fun x ↦ by simp
  rwa [hψ', hFψ, ψ.symm_image_image] at h'

/-- **Closed characteristics are conformally invariant.** If a diffeomorphism `ψ : M → M₂` pulls a
nondegenerate form `σ₂` back to `aσ` for a constant `a ≠ 0`, and `F` is differentiable along its
level `F⁻¹(c)`, then the level `c` of `F ∘ ψ⁻¹` carries a closed characteristic contractible in
`ψ(W)` for `σ₂` exactly when `F⁻¹(c)` carries one contractible in `W` for `σ`. -/
theorem IsNondegenerate.hasContractibleClosedCharacteristic_image_iff_of_mpullback_eq_smul
    (hσ₂ : σ₂.IsNondegenerate) (ψ : M ≃ₘ⟮I, I₂⟯ M₂) {a : ℝ} (ha : a ≠ 0)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = a • σ)
    (hF : ∀ x, F x = c → MDifferentiableAt I 𝓘(ℝ) F x) :
    σ₂.HasContractibleClosedCharacteristic (ψ '' W) (F ∘ ψ.symm) c ↔
      σ.HasContractibleClosedCharacteristic W F c := by
  have haσ : (a • σ).IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  have hσ : σ.IsNondegenerate := (isNondegenerate_smul_iff a ha).1 haσ
  rw [hσ₂.hasContractibleClosedCharacteristic_image_iff ψ hψ hF,
    hσ.hasContractibleClosedCharacteristic_smul_iff ha]

end Invariance

end SmoothTwoForm

end TauCeti
