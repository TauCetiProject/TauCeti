/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Basic.ENNReal.Real
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.Diffeomorph.Support
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# The relative `π₁`-sensitive Hofer–Zehnder capacity

Let `σ` be a smooth two-form on a manifold `M`, and let `V, Z ⊆ M`. A function `F : M → ℝ` is
**`(V, Z)`-admissible** (`TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`) when

* `F` is smooth, and its support is compact and contained in the interior of `V` and in the
  interior of the manifold `M`;
* `F` attains its maximum at every point of `Z`;
* the Hamiltonian vector field `X_F` has no **fast contractible** periodic orbits: every integral
  curve `γ` of `X_F` that is `T`-periodic for some `0 < T ≤ 1`, and whose loop `ℝ/Tℤ → M` is
  contractible in the whole manifold `M`, is constant.

The **relative `π₁`-sensitive Hofer–Zehnder capacity** of the pair `(V, Z)` is

`c°_HZ(V, Z) = sup {max F | F is (V, Z)-admissible} ∈ [0, ∞]`

(`TauCeti.SmoothTwoForm.relContractibleHZCapacity`). Barraud–Damian–Humilière–Oancea state the
definition for Hamiltonians `H = -F`, which are equal to their minimum on `Z`, and take the
supremum of `-min H`; the orbits of `X_{-F} = -X_F` are those of `X_F` run backwards, with the same
periods and the same free homotopy classes, so the two conventions give the same number. The
convention here is that of `TauCeti.SmoothTwoForm.contractibleHZCapacity`.

In contrast to the absolute capacity `c°_HZ(W)`, in which contractibility is tested in `W`
itself, contractibility of the orbits of a `(V, Z)`-admissible function is always tested in the
ambient manifold `M`. This makes the relative capacity monotone: for `V' ⊆ V` and `Z ⊆ Z'`,
every `(V', Z')`-admissible function is `(V, Z)`-admissible, so
`c°_HZ(V', Z') ≤ c°_HZ(V, Z)` (`TauCeti.SmoothTwoForm.relContractibleHZCapacity_mono`). When `σ`
is nondegenerate and `M` is finite-dimensional, the capacity is conformal,
`c°_HZ(V, Z; cσ) = c · c°_HZ(V, Z; σ)` for `c > 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_smul`), and it is invariant under
symplectomorphisms, `c°_HZ(ψ(V), ψ(Z); σ₂) = c°_HZ(V, Z; ψ^*σ₂)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_image`).

The relative capacity enters the proof of almost existence of contractible closed characteristics
near a hypersurface `Σ = ∂U` in a Liouville domain `W`: a homological criterion bounds
`c°_HZ(W, Z)` for a compact domain `Z` slightly inside `U` by a spectral invariant of symplectic
homology with DG coefficients, and, by the Hofer–Zehnder–Struwe argument, finiteness of this
relative capacity gives closed characteristics, contractible in `W`, on almost every level near
`Σ`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`: the `(V, Z)`-admissible Hamiltonians.
* `TauCeti.SmoothTwoForm.relContractibleHZCapacity`: the relative `π₁`-sensitive Hofer–Zehnder
  capacity.

## Main results

* `TauCeti.SmoothTwoForm.relContractibleHZCapacity_mono`: monotonicity in the pair.
* `TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_smul`: conformality.
* `TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_image`: invariance under
  symplectomorphisms.

## References

* V. L. Ginzburg, B. Z. Gürel, *Relative Hofer–Zehnder capacity and periodic orbits in twisted
  cotangent bundles*, Duke Math. J. 123 (2004), 1–47.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 5.3 and the remark following
  it.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.1.
-/

public section

noncomputable section

open Set
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {V Z : Set M} {F : M → ℝ}

/-- A function `F` is **`(V, Z)`-admissible** for a manifold with two-form `σ` when it is smooth,
its support is compact and lies in the interiors of `V` and of `M`, it attains its maximum at
every point of `Z`, and its Hamiltonian vector field has no nonconstant `T`-periodic orbit with
`0 < T ≤ 1` whose loop is contractible in `M`. These are the Hamiltonians whose maxima define the
relative `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ(V, Z)`. -/
structure IsRelContractibleHZAdmissible (σ : SmoothTwoForm I M) (V Z : Set M) (F : M → ℝ) :
    Prop where
  /-- An admissible Hamiltonian is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ) ∞ F
  /-- An admissible Hamiltonian has compact support. -/
  isCompact_tsupport : IsCompact (tsupport F)
  /-- An admissible Hamiltonian is supported in the interior of `V`. -/
  tsupport_subset_interior : tsupport F ⊆ interior V
  /-- An admissible Hamiltonian is supported away from the boundary of the manifold. -/
  tsupport_subset_interior_manifold : tsupport F ⊆ I.interior M
  /-- An admissible Hamiltonian attains its maximum at every point of `Z`. -/
  isMaxOn : ∀ z ∈ Z, IsMaxOn F univ z
  /-- **No fast contractible periodic orbits.** A `T`-periodic orbit of the Hamiltonian vector
  field with `0 < T ≤ 1`, whose loop `ℝ/Tℤ → M` is contractible in `M`, is constant. -/
  eq_of_isMIntegralCurve : ∀ (T : ℝ) (γ : ℝ → M), 0 < T → T ≤ 1 →
    IsMIntegralCurve γ (σ.hamiltonianVectorField F) → Function.Periodic γ T →
    (∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t) → ∀ t, γ t = γ 0

/-- **Admissibility is monotone in the pair.** A `(V, Z)`-admissible function is
`(V', Z')`-admissible whenever `V ⊆ V'` and `Z' ⊆ Z`. -/
theorem IsRelContractibleHZAdmissible.mono {V' Z' : Set M} (hV : V ⊆ V') (hZ : Z' ⊆ Z)
    (hF : σ.IsRelContractibleHZAdmissible V Z F) : σ.IsRelContractibleHZAdmissible V' Z' F where
  contMDiff := hF.contMDiff
  isCompact_tsupport := hF.isCompact_tsupport
  tsupport_subset_interior := hF.tsupport_subset_interior.trans (interior_mono hV)
  tsupport_subset_interior_manifold := hF.tsupport_subset_interior_manifold
  isMaxOn z hz := hF.isMaxOn z (hZ hz)
  eq_of_isMIntegralCurve := hF.eq_of_isMIntegralCurve

variable (σ V Z) in
/-- The **relative `π₁`-sensitive Hofer–Zehnder capacity** `c°_HZ(V, Z)` of a pair of subsets of a
manifold with a two-form `σ`: the supremum, in `[0, ∞]`, of the maxima of the `(V, Z)`-admissible
Hamiltonians (`TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`). -/
def relContractibleHZCapacity : ℝ≥0∞ :=
  ⨆ (F : M → ℝ) (_ : σ.IsRelContractibleHZAdmissible V Z F), ENNReal.ofReal (⨆ x, F x)

variable (σ V Z) in
/-- The defining supremum of the relative `π₁`-sensitive Hofer–Zehnder capacity. -/
theorem relContractibleHZCapacity_def :
    σ.relContractibleHZCapacity V Z =
      ⨆ (F : M → ℝ) (_ : σ.IsRelContractibleHZAdmissible V Z F), ENNReal.ofReal (⨆ x, F x) :=
  (rfl)

/-- The maximum of a `(V, Z)`-admissible Hamiltonian is a lower bound for the capacity. -/
theorem IsRelContractibleHZAdmissible.ofReal_iSup_le_relContractibleHZCapacity
    (hF : σ.IsRelContractibleHZAdmissible V Z F) :
    ENNReal.ofReal (⨆ x, F x) ≤ σ.relContractibleHZCapacity V Z :=
  le_iSup₂ (f := fun F (_ : σ.IsRelContractibleHZAdmissible V Z F) ↦ ENNReal.ofReal (⨆ x, F x))
    F hF

/-- The capacity is at most `a` exactly when the maximum of every `(V, Z)`-admissible Hamiltonian
is. -/
theorem relContractibleHZCapacity_le_iff {a : ℝ≥0∞} :
    σ.relContractibleHZCapacity V Z ≤ a ↔
      ∀ F, σ.IsRelContractibleHZAdmissible V Z F → ENNReal.ofReal (⨆ x, F x) ≤ a :=
  iSup₂_le_iff

/-- **Monotonicity of the relative capacity.** If `V' ⊆ V` and `Z ⊆ Z'`, then
`c°_HZ(V', Z') ≤ c°_HZ(V, Z)`: shrinking the support region or enlarging the set on which the
maximum is attained only removes admissible Hamiltonians. -/
theorem relContractibleHZCapacity_mono {V' Z' : Set M} (hV : V' ⊆ V) (hZ : Z ⊆ Z') :
    σ.relContractibleHZCapacity V' Z' ≤ σ.relContractibleHZCapacity V Z :=
  relContractibleHZCapacity_le_iff.2 fun _ hF ↦
    (hF.mono hV hZ).ofReal_iSup_le_relContractibleHZCapacity

/-! ### Conformality -/

section Conformality

variable [FiniteDimensional ℝ E]

/-- Rescaling the form and a `(V, Z)`-admissible Hamiltonian by the same `c > 0` gives a
`(V, Z)`-admissible Hamiltonian. -/
private theorem IsRelContractibleHZAdmissible.smul_smul (hσ : σ.IsNondegenerate) {c : ℝ}
    (hc : 0 < c) (hF : σ.IsRelContractibleHZAdmissible V Z F) :
    (c • σ).IsRelContractibleHZAdmissible V Z (c • F) where
  contMDiff := (contDiff_const_smul c).comp_contMDiff hF.contMDiff
  isCompact_tsupport := hF.isCompact_tsupport.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_right (fun _ ↦ c) F)
  tsupport_subset_interior :=
    (tsupport_smul_subset_right (fun _ ↦ c) F).trans hF.tsupport_subset_interior
  tsupport_subset_interior_manifold :=
    (tsupport_smul_subset_right (fun _ ↦ c) F).trans hF.tsupport_subset_interior_manifold
  isMaxOn z hz := isMaxOn_iff.2 fun y hy ↦
    mul_le_mul_of_nonneg_left (isMaxOn_iff.1 (hF.isMaxOn z hz) y hy) hc.le
  eq_of_isMIntegralCurve := by
    rw [hσ.hamiltonianVectorField_smul_smul hc.ne']
    exact hF.eq_of_isMIntegralCurve

/-- **Admissibility is conformal.** For a nondegenerate form `σ` and `c > 0`, `cF` is
`(V, Z)`-admissible for `cσ` exactly when `F` is `(V, Z)`-admissible for `σ`. -/
theorem IsNondegenerate.isRelContractibleHZAdmissible_smul_smul_iff (hσ : σ.IsNondegenerate)
    {c : ℝ} (hc : 0 < c) :
    (c • σ).IsRelContractibleHZAdmissible V Z (c • F) ↔ σ.IsRelContractibleHZAdmissible V Z F := by
  refine ⟨fun h ↦ ?_, IsRelContractibleHZAdmissible.smul_smul hσ hc⟩
  have h' := IsRelContractibleHZAdmissible.smul_smul (hσ.smul c hc.ne') (inv_pos.2 hc) h
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul] at h'

/-- **Conformality of the relative capacity.** For a nondegenerate form `σ` and `c > 0`,
`c°_HZ(V, Z; cσ) = c · c°_HZ(V, Z; σ)`. -/
theorem IsNondegenerate.relContractibleHZCapacity_smul (hσ : σ.IsNondegenerate) {c : ℝ}
    (hc : 0 < c) (V Z : Set M) :
    (c • σ).relContractibleHZCapacity V Z = ENNReal.ofReal c * σ.relContractibleHZCapacity V Z :=
  iSup₂_ofReal_iSup_eq_ofReal_mul hc fun _ ↦ hσ.isRelContractibleHZAdmissible_smul_smul_iff hc

end Conformality

/-! ### Invariance under symplectomorphisms -/

section Invariance

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- A symplectomorphism `ψ` carries a `(V, Z)`-admissible Hamiltonian `F` to the
`(ψ(V), ψ(Z))`-admissible Hamiltonian `F ∘ ψ⁻¹`. -/
theorem IsRelContractibleHZAdmissible.comp_symm (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hF : σ.IsRelContractibleHZAdmissible V Z F) :
    σ₂.IsRelContractibleHZAdmissible (ψ '' V) (ψ '' Z) (F ∘ ψ.symm) := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  refine
    { contMDiff := hF.contMDiff.comp ψ.symm.contMDiff
      isCompact_tsupport :=
        ψ.tsupport_comp_symm F ▸ hF.isCompact_tsupport.image ψ.continuous
      tsupport_subset_interior :=
        ψ.tsupport_comp_symm_subset_interior_image hF.tsupport_subset_interior
      tsupport_subset_interior_manifold :=
        ψ.tsupport_comp_symm_subset_interior_manifold (by simp) hF.tsupport_subset_interior_manifold
      isMaxOn := ?_
      eq_of_isMIntegralCurve := ?_ }
  · rintro _ ⟨z, hz, rfl⟩
    refine isMaxOn_iff.2 fun y hy ↦ ?_
    simpa using isMaxOn_iff.1 (hF.isMaxOn z hz) (ψ.symm y) hy
  · rintro T γ hT hT1 hγ hper ⟨g, hg, hgγ⟩ t
    -- The curve `ψ⁻¹ ∘ γ` is a periodic orbit of `F`, contractible in `M` through `ψ⁻¹ ∘ g`, so
    -- it is constant.
    have hγ' : IsMIntegralCurve (ψ.symm ∘ γ) (σ.hamiltonianVectorField F) :=
      hσ₂.comp_isMIntegralCurve_hamiltonianVectorField hσ ψ.symm.contMDiff
        (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ)
        (fun _ ↦ (ψ.symm.isInvertible_mfderiv (by simp)).surjective)
        (fun _ ↦ (hF.contMDiff _).mdifferentiableAt (by simp)) hγ
    have h := hF.eq_of_isMIntegralCurve T (ψ.symm ∘ γ) hT hT1 hγ' (hper.comp _)
      ⟨(⟨ψ.symm, ψ.symm.continuous⟩ : C(M₂, M)).comp g, hg.comp_right _,
        fun s ↦ by simp [hgγ]⟩ t
    exact ψ.symm.injective h

/-- **Symplectic invariance of the relative capacity.** If a diffeomorphism `ψ : M → M₂` pulls a
nondegenerate form `σ₂` back to `σ`, then `c°_HZ(ψ(V), ψ(Z); σ₂) = c°_HZ(V, Z; σ)` for all
`V, Z ⊆ M`. -/
theorem IsNondegenerate.relContractibleHZCapacity_image (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (V Z : Set M) :
    σ₂.relContractibleHZCapacity (ψ '' V) (ψ '' Z) = σ.relContractibleHZCapacity V Z := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  refine iSup₂_ofReal_iSup_eq_of_comp ψ.surjective ψ.symm.surjective
    (fun _ hF ↦ hF.comp_symm hσ₂ ψ hψ) fun G hG ↦ ?_
  have h := hG.comp_symm hσ ψ.symm (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ)
  -- `Diffeomorph.symm` is involutive by definition.
  have hψ' : ψ.symm.symm = ψ := rfl
  rwa [hψ', ψ.symm_image_image, ψ.symm_image_image] at h

end Invariance

end SmoothTwoForm

end TauCeti
