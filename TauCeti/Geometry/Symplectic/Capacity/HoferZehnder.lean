/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# The `π₁`-sensitive Hofer–Zehnder capacity

Let `σ` be a smooth two-form on a manifold `M` and `W ⊆ M`. A function `F : M → ℝ` is
**`HZ°`-admissible** for `W` (`TauCeti.SmoothTwoForm.IsContractibleHZAdmissible`) when

* `F` is smooth, nonnegative, and its support is compact and contained in the interior of `W`
  and in the interior of the manifold `M`;
* `F` vanishes on a nonempty open subset of `W` and attains its maximum on a nonempty open set;
* the Hamiltonian vector field `X_F` (`TauCeti.SmoothTwoForm.hamiltonianVectorField`, which
  satisfies `ι_{X_F} σ = dF` when `σ` is nondegenerate and `M` is finite-dimensional) has no
  **fast contractible** periodic orbits: every integral curve `γ` of `X_F` that is `T`-periodic
  for some `0 < T ≤ 1`, and whose loop `ℝ/Tℤ → W` is contractible in `W`, is constant.

The **`π₁`-sensitive Hofer–Zehnder capacity** of `W` is

`c°_HZ(W) = sup {max F | F is HZ°-admissible for W} ∈ [0, ∞]`

(`TauCeti.SmoothTwoForm.contractibleHZCapacity`). Only orbits that are contractible *in `W`*
are excluded, so `c°_HZ(W)` is at least the Hofer–Zehnder capacity, in which every fast
periodic orbit is excluded. A `T`-periodic orbit is also `kT`-periodic, so the condition
concerns all iterates of period at most `1`.

The definition makes sense for any two-form `σ`. When `σ` is nondegenerate and `M` is
finite-dimensional, the capacity is conformal, `c°_HZ(W, cσ) = c · c°_HZ(W, σ)` for `c > 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleHZCapacity_smul`), and invariant under
symplectomorphisms, `c°_HZ(ψ(W), σ₂) = c°_HZ(W, ψ^*σ₂)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleHZCapacity_image`). The conformality rests on
`X^{cσ}_{cF} = X^σ_F` (`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_smul_smul`),
so that `cF` is admissible for `cσ` exactly when `F` is admissible for `σ`. The invariance rests
on the naturality of Hamiltonian vector fields: a symplectomorphism `ψ` sends the periodic orbits
of `X_{F ∘ ψ}` to those of `X_F`, and their contracting homotopies in `W` to contracting
homotopies in `ψ(W)`. Unlike the Hofer–Zehnder capacity, `c°_HZ` is not monotone under arbitrary
inclusions `W ⊆ W'`: a loop in `W` may be contractible in `W'` without being contractible in `W`,
so an admissible Hamiltonian for `W` need not be admissible for `W'`.

Finiteness of `c°_HZ` is the hypothesis under which the Hofer–Zehnder–Struwe monotonicity
argument produces closed characteristics on almost every level of a family of hypersurfaces,
and upper bounds for it are what Floer-theoretic spectral invariants of cotangent bundles provide.

## Main definitions

* `TauCeti.SmoothTwoForm.IsContractibleHZAdmissible`: the admissible Hamiltonians.
* `TauCeti.SmoothTwoForm.contractibleHZCapacity`: the `π₁`-sensitive Hofer–Zehnder capacity.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleHZAdmissible_smul_smul_iff`: `cF` is
  admissible for `cσ` exactly when `F` is admissible for `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleHZCapacity_smul`: conformality.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleHZCapacity_image`: invariance under
  symplectomorphisms.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Sections 3.1 and 4.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 12.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1.
-/

public section

noncomputable section

open Set
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {W : Set M} {F : M → ℝ}

/-- A function `F` is **`HZ°`-admissible** for a subset `W` of a manifold with two-form `σ` when it
is smooth and nonnegative, its support is compact and lies in the interiors of `W` and of `M`, it
vanishes on a nonempty open subset of `W`, it attains its maximum on a nonempty open set, and its
Hamiltonian vector field has no nonconstant `T`-periodic orbit with `0 < T ≤ 1` whose loop is
contractible in `W`. These are the Hamiltonians whose maxima define the `π₁`-sensitive
Hofer–Zehnder capacity. On a closed manifold with `W = M` the support conditions are vacuous,
and the vanishing condition is what excludes positive constants. -/
structure IsContractibleHZAdmissible (σ : SmoothTwoForm I M) (W : Set M) (F : M → ℝ) : Prop where
  /-- An admissible Hamiltonian is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ) ∞ F
  /-- An admissible Hamiltonian has compact support. -/
  isCompact_tsupport : IsCompact (tsupport F)
  /-- An admissible Hamiltonian is supported in the interior of `W`. -/
  tsupport_subset_interior : tsupport F ⊆ interior W
  /-- An admissible Hamiltonian is supported away from the boundary of the manifold. -/
  tsupport_subset_interior_manifold : tsupport F ⊆ I.interior M
  /-- An admissible Hamiltonian is nonnegative. -/
  nonneg : ∀ x, 0 ≤ F x
  /-- An admissible Hamiltonian vanishes on a nonempty open subset of `W`. -/
  exists_isOpen_eqOn_zero : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ U ⊆ W ∧ EqOn F 0 U
  /-- An admissible Hamiltonian attains its maximum on a nonempty open set. -/
  exists_isOpen_isMaxOn : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, IsMaxOn F univ x
  /-- **No fast contractible periodic orbits.** A `T`-periodic orbit of the Hamiltonian vector
  field with `0 < T ≤ 1`, whose loop `ℝ/Tℤ → W` is contractible in `W`, is constant. -/
  eq_of_isMIntegralCurve : ∀ (T : ℝ) (γ : ℝ → M), 0 < T → T ≤ 1 →
    IsMIntegralCurve γ (σ.hamiltonianVectorField F) → Function.Periodic γ T →
    (∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t) → ∀ t, γ t = γ 0

variable (σ W) in
/-- The **`π₁`-sensitive Hofer–Zehnder capacity** `c°_HZ(W)` of a subset `W` of a manifold with a
two-form `σ`: the supremum, in `[0, ∞]`, of the maxima of the `HZ°`-admissible Hamiltonians
(`TauCeti.SmoothTwoForm.IsContractibleHZAdmissible`). -/
def contractibleHZCapacity : ℝ≥0∞ :=
  ⨆ (F : M → ℝ) (_ : σ.IsContractibleHZAdmissible W F), ENNReal.ofReal (⨆ x, F x)

variable (σ W) in
/-- The defining supremum of the `π₁`-sensitive Hofer–Zehnder capacity. -/
theorem contractibleHZCapacity_def :
    σ.contractibleHZCapacity W =
      ⨆ (F : M → ℝ) (_ : σ.IsContractibleHZAdmissible W F), ENNReal.ofReal (⨆ x, F x) :=
  (rfl)

/-- The maximum of an admissible Hamiltonian is a lower bound for the capacity. -/
theorem IsContractibleHZAdmissible.ofReal_iSup_le_contractibleHZCapacity
    (hF : σ.IsContractibleHZAdmissible W F) :
    ENNReal.ofReal (⨆ x, F x) ≤ σ.contractibleHZCapacity W :=
  le_iSup₂ (f := fun F (_ : σ.IsContractibleHZAdmissible W F) ↦ ENNReal.ofReal (⨆ x, F x)) F hF

/-- The capacity is at most `a` exactly when the maximum of every admissible Hamiltonian is. -/
theorem contractibleHZCapacity_le_iff {a : ℝ≥0∞} :
    σ.contractibleHZCapacity W ≤ a ↔
      ∀ F, σ.IsContractibleHZAdmissible W F → ENNReal.ofReal (⨆ x, F x) ≤ a :=
  iSup₂_le_iff

/-! ### Conformality -/

section Conformality

variable [FiniteDimensional ℝ E]

/-- Rescaling the form and an admissible Hamiltonian by the same `c > 0` gives an admissible
Hamiltonian. -/
private theorem IsContractibleHZAdmissible.smul_smul (hσ : σ.IsNondegenerate) {c : ℝ}
    (hc : 0 < c) (hF : σ.IsContractibleHZAdmissible W F) :
    (c • σ).IsContractibleHZAdmissible W (c • F) where
  contMDiff := (contDiff_const_smul c).comp_contMDiff hF.contMDiff
  isCompact_tsupport := hF.isCompact_tsupport.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_right (fun _ ↦ c) F)
  tsupport_subset_interior :=
    (tsupport_smul_subset_right (fun _ ↦ c) F).trans hF.tsupport_subset_interior
  tsupport_subset_interior_manifold :=
    (tsupport_smul_subset_right (fun _ ↦ c) F).trans hF.tsupport_subset_interior_manifold
  nonneg x := mul_nonneg hc.le (hF.nonneg x)
  exists_isOpen_eqOn_zero := by
    obtain ⟨U, hU, hUne, hUW, hzero⟩ := hF.exists_isOpen_eqOn_zero
    exact ⟨U, hU, hUne, hUW, fun x hx ↦ by simp [hzero hx]⟩
  exists_isOpen_isMaxOn := by
    obtain ⟨U, hU, hUne, hmax⟩ := hF.exists_isOpen_isMaxOn
    exact ⟨U, hU, hUne, fun x hx ↦ isMaxOn_iff.2 fun y hy ↦
      mul_le_mul_of_nonneg_left (isMaxOn_iff.1 (hmax x hx) y hy) hc.le⟩
  eq_of_isMIntegralCurve := by
    rw [hσ.hamiltonianVectorField_smul_smul hc.ne']
    exact hF.eq_of_isMIntegralCurve

/-- **Admissibility is conformal.** For a nondegenerate form `σ` and `c > 0`, `cF` is admissible
for `cσ` exactly when `F` is admissible for `σ`. -/
theorem IsNondegenerate.isContractibleHZAdmissible_smul_smul_iff (hσ : σ.IsNondegenerate)
    {c : ℝ} (hc : 0 < c) :
    (c • σ).IsContractibleHZAdmissible W (c • F) ↔ σ.IsContractibleHZAdmissible W F := by
  refine ⟨fun h ↦ ?_, IsContractibleHZAdmissible.smul_smul hσ hc⟩
  have h' := IsContractibleHZAdmissible.smul_smul (hσ.smul c hc.ne') (inv_pos.2 hc) h
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul] at h'

/-- **Conformality of the capacity.** For a nondegenerate form `σ` and `c > 0`,
`c°_HZ(W, cσ) = c · c°_HZ(W, σ)`. -/
theorem IsNondegenerate.contractibleHZCapacity_smul (hσ : σ.IsNondegenerate) {c : ℝ} (hc : 0 < c)
    (W : Set M) :
    (c • σ).contractibleHZCapacity W = ENNReal.ofReal c * σ.contractibleHZCapacity W := by
  -- The maximum of `c • F` is `c` times the maximum of `F`.
  have hmax (F : M → ℝ) :
      ENNReal.ofReal (⨆ x, (c • F) x) = ENNReal.ofReal c * ENNReal.ofReal (⨆ x, F x) := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Real.mul_iSup_of_nonneg hc.le,
      ENNReal.ofReal_mul hc.le]
  refine le_antisymm (contractibleHZCapacity_le_iff.2 fun F hF ↦ ?_) ?_
  · have hF' : F = c • (c⁻¹ • F) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [hF'] at hF ⊢
    rw [hmax]
    gcongr
    exact ((hσ.isContractibleHZAdmissible_smul_smul_iff hc).1 hF
      ).ofReal_iSup_le_contractibleHZCapacity
  · simp only [contractibleHZCapacity_def, ENNReal.mul_iSup]
    refine iSup₂_le fun F hF ↦ ?_
    rw [← hmax]
    exact ((hσ.isContractibleHZAdmissible_smul_smul_iff hc).2 hF
      ).ofReal_iSup_le_contractibleHZCapacity

end Conformality

/-! ### Invariance under symplectomorphisms -/

section Invariance

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- A symplectomorphism `ψ` carries an admissible Hamiltonian `F` for `W` to the admissible
Hamiltonian `F ∘ ψ⁻¹` for `ψ(W)`. -/
theorem IsContractibleHZAdmissible.comp_symm (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hF : σ.IsContractibleHZAdmissible W F) :
    σ₂.IsContractibleHZAdmissible (ψ '' W) (F ∘ ψ.symm) := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  -- `ψ⁻¹` carries the Hamiltonian vector field of `F ∘ ψ⁻¹` to that of `F`.
  have hX (y : M₂) : mfderiv I₂ I ψ.symm y (σ₂.hamiltonianVectorField (F ∘ ψ.symm) y) =
      σ.hamiltonianVectorField F (ψ.symm y) := by
    refine ψ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq (by simp) (fun x ↦ ?_) y
    have h := hσ.mfderiv_hamiltonianVectorField_comp hσ₂ ψ.contMDiff hψ
      (ψ.isInvertible_mfderiv (by simp) (x := x)).surjective (g := F ∘ ψ.symm)
      (((hF.contMDiff.comp ψ.symm.contMDiff) (ψ x)).mdifferentiableAt (by simp))
    have hFψ : (F ∘ ψ.symm) ∘ ψ = F := funext fun x ↦ by simp
    rwa [hFψ] at h
  have hsupp : tsupport (F ∘ ψ.symm) = ψ '' tsupport F := by
    rw [ψ.image_eq_preimage_symm, ← ψ.symm.coe_toHomeomorph,
      ← tsupport_comp_eq_preimage F ψ.symm.toHomeomorph]
  refine
    { contMDiff := hF.contMDiff.comp ψ.symm.contMDiff
      isCompact_tsupport := hsupp ▸ hF.isCompact_tsupport.image ψ.continuous
      tsupport_subset_interior := ?_
      tsupport_subset_interior_manifold := ?_
      nonneg := fun y ↦ hF.nonneg _
      exists_isOpen_eqOn_zero := ?_
      exists_isOpen_isMaxOn := ?_
      eq_of_isMIntegralCurve := ?_ }
  · rw [hsupp, ← ψ.coe_toHomeomorph, ← ψ.toHomeomorph.image_interior]
    exact image_mono hF.tsupport_subset_interior
  · rw [hsupp, ← Diffeomorph.image_interior (by simp) ψ]
    exact image_mono hF.tsupport_subset_interior_manifold
  · obtain ⟨U, hU, hUne, hUW, hzero⟩ := hF.exists_isOpen_eqOn_zero
    refine ⟨ψ '' U, ψ.toHomeomorph.isOpenMap U hU, hUne.image ψ, image_mono hUW, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simpa using hzero hx
  · obtain ⟨U, hU, hUne, hmax⟩ := hF.exists_isOpen_isMaxOn
    refine ⟨ψ '' U, ψ.toHomeomorph.isOpenMap U hU, hUne.image ψ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine isMaxOn_iff.2 fun y hy ↦ ?_
    simpa using isMaxOn_iff.1 (hmax x hx) (ψ.symm y) hy
  · rintro T γ hT hT1 hγ hper ⟨g, hg, hgγ⟩ t
    -- The curve `ψ⁻¹ ∘ γ` is a contractible periodic orbit of `F` in `W`, so it is constant.
    have hγ' : IsMIntegralCurve (ψ.symm ∘ γ) (σ.hamiltonianVectorField F) := by
      rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
      exact hγ.map_of_mfderiv_eq (fun s _ ↦ ψ.symm.mdifferentiable (by simp) (γ s))
        fun s _ ↦ hX (γ s)
    have hmem (y : ψ '' W) : ψ.symm y ∈ W := by
      obtain ⟨x, hx, hxy⟩ := y.2
      rwa [← hxy, ψ.symm_apply_apply]
    have h := hF.eq_of_isMIntegralCurve T (ψ.symm ∘ γ) hT hT1 hγ' (hper.comp _)
      ⟨(⟨fun y ↦ ⟨ψ.symm y, hmem y⟩, by fun_prop⟩ : C(ψ '' W, W)).comp g, hg.comp_right _,
        fun s ↦ by simp [hgγ]⟩ t
    exact ψ.symm.injective h

/-- **Symplectic invariance of the capacity.** If a diffeomorphism `ψ : M → M₂` pulls a
nondegenerate form `σ₂` back to `σ`, then `c°_HZ(ψ(W), σ₂) = c°_HZ(W, σ)` for every `W ⊆ M`. -/
theorem IsNondegenerate.contractibleHZCapacity_image (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (W : Set M) :
    σ₂.contractibleHZCapacity (ψ '' W) = σ.contractibleHZCapacity W := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  refine le_antisymm (contractibleHZCapacity_le_iff.2 fun F hF ↦ ?_)
    (contractibleHZCapacity_le_iff.2 fun F hF ↦ ?_)
  · have h := hF.comp_symm hσ ψ.symm
      (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ)
    -- `Diffeomorph.symm` is involutive by definition.
    have hψ' : ψ.symm.symm = ψ := rfl
    rw [hψ', ψ.symm_image_image] at h
    have hsup : ⨆ x, (F ∘ ψ) x = ⨆ y, F y := ψ.surjective.iSup_comp F
    exact hsup ▸ h.ofReal_iSup_le_contractibleHZCapacity
  · have hsup : ⨆ y, (F ∘ ψ.symm) y = ⨆ x, F x := ψ.symm.surjective.iSup_comp F
    exact hsup ▸ (hF.comp_symm hσ₂ ψ hψ).ofReal_iSup_le_contractibleHZCapacity

end Invariance

end SmoothTwoForm

end TauCeti
