/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
import TauCeti.Basic.ENNReal.Real
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# The relative `π₁`-sensitive Hofer–Zehnder capacity

Let `σ` be a smooth two-form on a manifold `M`, and let `W, V, Z ⊆ M`. A function `F : M → ℝ` is
**`(V, Z)`-admissible in `W`** (`TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`) when

* `F` is smooth, nonnegative, and its support is compact and contained in the interior of `V`
  and in the interior of the manifold `M`, and `F` vanishes on a nonempty open subset of `V`
  (`TauCeti.IsHZNormalized`, the normalisation shared with the absolute capacity);
* `F` attains its maximum at every point of `Z`;
* the Hamiltonian vector field `X_F` has no **fast periodic orbits contractible in `W`**: every
  integral curve `γ` of `X_F` that is `T`-periodic for some `0 < T ≤ 1`, and whose loop
  `ℝ/Tℤ → W` is contractible in `W`, is constant.

The **relative `π₁`-sensitive Hofer–Zehnder capacity** of the pair `(V, Z)` in `W` is

`c°_HZ(V, Z) = sup {max F | F is (V, Z)-admissible in W} ∈ [0, ∞]`

(`TauCeti.SmoothTwoForm.relContractibleHZCapacity`). Barraud–Damian–Humilière–Oancea state the
definition for Hamiltonians `H = -F`, which are equal to their minimum on `Z`, and take the
supremum of `-min H`; the orbits of `X_{-F} = -X_F` are those of `X_F` run backwards, with the same
periods and the same free homotopy classes, so the two conventions give the same number. The
convention here is that of `TauCeti.SmoothTwoForm.contractibleHZCapacity`.

In the absolute capacity `c°_HZ(W)` contractibility is tested in the support region `W` itself.
In the relative capacity it is tested in a fixed set `W`, typically a domain in which `V` lies or
the whole manifold `M`, independently of `V`. This makes the relative capacity monotone: for
`V' ⊆ V`, `Z ⊆ Z'` and `W ⊆ W'`, every `(V', Z')`-admissible function in `W'` is
`(V, Z)`-admissible in `W`, since a loop contractible in `W` is contractible in `W'`, so
`c°_HZ(V', Z')` in `W'` is at most `c°_HZ(V, Z)` in `W`
(`TauCeti.SmoothTwoForm.relContractibleHZCapacity_mono`). For `V ⊆ W` it is bounded by the
absolute capacity `c°_HZ(W)` as soon as `Z` has nonempty interior
(`TauCeti.SmoothTwoForm.relContractibleHZCapacity_le_contractibleHZCapacity`). When `σ`
is nondegenerate and `M` is finite-dimensional, the capacity is conformal,
`c°_HZ(V, Z; cσ) = c · c°_HZ(V, Z; σ)` for `c > 0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_smul`), and it is invariant under
symplectomorphisms: `c°_HZ(ψ(V), ψ(Z); σ₂)` in `ψ(W)` is `c°_HZ(V, Z; ψ^*σ₂)` in `W`
(`TauCeti.SmoothTwoForm.IsNondegenerate.relContractibleHZCapacity_image`).

The relative capacity enters the proof of almost existence of contractible closed characteristics
near a hypersurface `Σ = ∂U` in a Liouville domain `W`: a homological criterion bounds
`c°_HZ(W, Z)`, with contractibility tested in `W`, for a compact domain `Z` slightly inside `U` by
a spectral invariant of symplectic homology with DG coefficients, and, by the
Hofer–Zehnder–Struwe argument, finiteness of this relative capacity gives closed characteristics,
contractible in `W`, on almost every level near `Σ`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`: the `(V, Z)`-admissible Hamiltonians in
  `W`.
* `TauCeti.SmoothTwoForm.relContractibleHZCapacity`: the relative `π₁`-sensitive Hofer–Zehnder
  capacity.

## Main results

* `TauCeti.SmoothTwoForm.relContractibleHZCapacity_mono`: monotonicity in the pair.
* `TauCeti.SmoothTwoForm.relContractibleHZCapacity_le_contractibleHZCapacity`: when `V ⊆ W` and
  `Z` has nonempty interior, `c°_HZ(V, Z)` in `W` is at most `c°_HZ(W)`.
* `TauCeti.SmoothTwoForm.exists_isRelContractibleHZAdmissible_lt_iSup`: a finite capacity is
  approximated by the maxima of admissible Hamiltonians.
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
  {σ : SmoothTwoForm I M} {W V Z : Set M} {F : M → ℝ}

/-- A function `F` is **`(V, Z)`-admissible in `W`** for a manifold with two-form `σ` when it is
smooth and nonnegative, its support is compact and lies in the interiors of `V` and of `M`, it
vanishes on a nonempty open subset of `V` (that is, it is normalised for `V`,
`TauCeti.IsHZNormalized`), it attains its maximum at every point of `Z`, and its Hamiltonian vector
field has no nonconstant `T`-periodic orbit with `0 < T ≤ 1` whose loop is contractible in `W`.
These are the Hamiltonians whose maxima define the relative `π₁`-sensitive Hofer–Zehnder capacity
`c°_HZ(V, Z)` in `W`. -/
structure IsRelContractibleHZAdmissible (σ : SmoothTwoForm I M) (W V Z : Set M) (F : M → ℝ) :
    Prop extends IsHZNormalized I V F where
  /-- An admissible Hamiltonian attains its maximum at every point of `Z`. -/
  isMaxOn : ∀ z ∈ Z, IsMaxOn F univ z
  /-- **No fast periodic orbits contractible in `W`.** A `T`-periodic orbit of the Hamiltonian
  vector field with `0 < T ≤ 1`, whose loop `ℝ/Tℤ → W` is contractible in `W`, is constant. -/
  eq_of_isMIntegralCurve : ∀ (T : ℝ) (γ : ℝ → M), 0 < T → T ≤ 1 →
    IsMIntegralCurve γ (σ.hamiltonianVectorField F) → Function.Periodic γ T →
    (∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = γ t) → ∀ t, γ t = γ 0

/-- **Admissibility is monotone.** A `(V, Z)`-admissible function in `W` is `(V', Z')`-admissible
in `W'` whenever `W' ⊆ W`, `V ⊆ V'` and `Z' ⊆ Z`: a loop contractible in `W'` is contractible in
`W`. -/
theorem IsRelContractibleHZAdmissible.mono {W' V' Z' : Set M} (hW : W' ⊆ W) (hV : V ⊆ V')
    (hZ : Z' ⊆ Z) (hF : σ.IsRelContractibleHZAdmissible W V Z F) :
    σ.IsRelContractibleHZAdmissible W' V' Z' F where
  toIsHZNormalized := hF.toIsHZNormalized.mono hV
  isMaxOn z hz := hF.isMaxOn z (hZ hz)
  eq_of_isMIntegralCurve T γ hT hT1 hγ hper := fun ⟨g, hg, hgγ⟩ ↦
    hF.eq_of_isMIntegralCurve T γ hT hT1 hγ hper
      ⟨(ContinuousMap.inclusion hW).comp g, hg.comp_right _, hgγ⟩

variable (σ W V Z) in
/-- The **relative `π₁`-sensitive Hofer–Zehnder capacity** `c°_HZ(V, Z)` in `W` of a pair of
subsets of a manifold with a two-form `σ`: the supremum, in `[0, ∞]`, of the maxima of the
`(V, Z)`-admissible Hamiltonians in `W` (`TauCeti.SmoothTwoForm.IsRelContractibleHZAdmissible`). -/
def relContractibleHZCapacity : ℝ≥0∞ :=
  ⨆ (F : M → ℝ) (_ : σ.IsRelContractibleHZAdmissible W V Z F), ENNReal.ofReal (⨆ x, F x)

variable (σ W V Z) in
/-- The defining supremum of the relative `π₁`-sensitive Hofer–Zehnder capacity. -/
theorem relContractibleHZCapacity_def :
    σ.relContractibleHZCapacity W V Z =
      ⨆ (F : M → ℝ) (_ : σ.IsRelContractibleHZAdmissible W V Z F), ENNReal.ofReal (⨆ x, F x) :=
  (rfl)

/-- The maximum of a `(V, Z)`-admissible Hamiltonian in `W` is a lower bound for the capacity. -/
theorem IsRelContractibleHZAdmissible.ofReal_iSup_le_relContractibleHZCapacity
    (hF : σ.IsRelContractibleHZAdmissible W V Z F) :
    ENNReal.ofReal (⨆ x, F x) ≤ σ.relContractibleHZCapacity W V Z :=
  le_iSup₂ (f := fun F (_ : σ.IsRelContractibleHZAdmissible W V Z F) ↦ ENNReal.ofReal (⨆ x, F x))
    F hF

/-- The capacity is at most `a` exactly when the maximum of every `(V, Z)`-admissible Hamiltonian
in `W` is. -/
theorem relContractibleHZCapacity_le_iff {a : ℝ≥0∞} :
    σ.relContractibleHZCapacity W V Z ≤ a ↔
      ∀ F, σ.IsRelContractibleHZAdmissible W V Z F → ENNReal.ofReal (⨆ x, F x) ≤ a :=
  iSup₂_le_iff

/-- **Monotonicity of the relative capacity.** If `W ⊆ W'`, `V' ⊆ V` and `Z ⊆ Z'`, then
`c°_HZ(V', Z')` in `W'` is at most `c°_HZ(V, Z)` in `W`: shrinking the support region, enlarging
the set on which the maximum is attained, or enlarging the set in which contractibility is tested
only removes admissible Hamiltonians. -/
theorem relContractibleHZCapacity_mono {W' V' Z' : Set M} (hW : W ⊆ W') (hV : V' ⊆ V)
    (hZ : Z ⊆ Z') : σ.relContractibleHZCapacity W' V' Z' ≤ σ.relContractibleHZCapacity W V Z :=
  relContractibleHZCapacity_le_iff.2 fun _ hF ↦
    (hF.mono hW hV hZ).ofReal_iSup_le_relContractibleHZCapacity

/-- A `(V, Z)`-admissible Hamiltonian in `W` is `HZ°`-admissible for `W` as soon as `V ⊆ W` and `Z`
has nonempty interior: it is supported in the interior of `W` and attains its maximum on the
interior of `Z`. -/
theorem IsRelContractibleHZAdmissible.isContractibleHZAdmissible
    (hF : σ.IsRelContractibleHZAdmissible W V Z F) (hV : V ⊆ W) (hZ : (interior Z).Nonempty) :
    σ.IsContractibleHZAdmissible W F where
  toIsHZNormalized := hF.toIsHZNormalized.mono hV
  exists_isOpen_isMaxOn :=
    ⟨interior Z, isOpen_interior, hZ, fun z hz ↦ hF.isMaxOn z (interior_subset hz)⟩
  eq_of_isMIntegralCurve := hF.eq_of_isMIntegralCurve

/-- **The relative capacity is bounded by the absolute one.** If `V ⊆ W` and `Z` has nonempty
interior, then `c°_HZ(V, Z)` in `W` is at most `c°_HZ(W)`. -/
theorem relContractibleHZCapacity_le_contractibleHZCapacity (hV : V ⊆ W)
    (hZ : (interior Z).Nonempty) :
    σ.relContractibleHZCapacity W V Z ≤ σ.contractibleHZCapacity W :=
  relContractibleHZCapacity_le_iff.2 fun _ hF ↦
    (hF.isContractibleHZAdmissible hV hZ).ofReal_iSup_le_contractibleHZCapacity

/-- The zero Hamiltonian is `(V, Z)`-admissible in `W` as soon as `V` contains a nonempty open set:
its Hamiltonian vector field vanishes, so its periodic orbits are constant. In particular the
admissible Hamiltonians of such a pair form a nonempty family. -/
theorem isRelContractibleHZAdmissible_zero (hV : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ U ⊆ V) :
    σ.IsRelContractibleHZAdmissible W V Z 0 where
  contMDiff := contMDiff_const
  isCompact_tsupport := by simp
  tsupport_subset_interior := by simp
  tsupport_subset_interior_manifold := by simp
  nonneg _ := le_rfl
  exists_isOpen_eqOn_zero := by
    obtain ⟨U, hU, hUne, hUV⟩ := hV
    exact ⟨U, hU, hUne, hUV, fun _ _ ↦ rfl⟩
  isMaxOn _ _ := isMaxOn_iff.2 fun _ _ ↦ le_rfl
  eq_of_isMIntegralCurve T γ _ _ hγ _ _ t := by
    have hX : σ.hamiltonianVectorField (0 : M → ℝ) = 0 := hamiltonianVectorField_const σ 0
    exact hγ.apply_eq_of_forall_eq_zero (fun u ↦ by rw [hX]; rfl) 0 t

/-- **Approximating a finite relative capacity.** If `V` contains a nonempty open set and
`c°_HZ(V, Z)` in `W` is finite, then for every `ε > 0` some `(V, Z)`-admissible Hamiltonian in `W`
has maximum greater than `c°_HZ(V, Z) - ε`. -/
theorem exists_isRelContractibleHZAdmissible_lt_iSup
    (hV : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ U ⊆ V)
    (hc : σ.relContractibleHZCapacity W V Z ≠ (∞ : ℝ≥0∞))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G, σ.IsRelContractibleHZAdmissible W V Z G ∧
      (σ.relContractibleHZCapacity W V Z).toReal - ε < ⨆ x, G x := by
  by_cases hneg : (σ.relContractibleHZCapacity W V Z).toReal - ε < 0
  · exact ⟨0, isRelContractibleHZAdmissible_zero hV, by simpa using hneg⟩
  have hlt : ENNReal.ofReal ((σ.relContractibleHZCapacity W V Z).toReal - ε) <
      σ.relContractibleHZCapacity W V Z := by
    calc ENNReal.ofReal ((σ.relContractibleHZCapacity W V Z).toReal - ε)
        < ENNReal.ofReal (σ.relContractibleHZCapacity W V Z).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      _ = σ.relContractibleHZCapacity W V Z := ENNReal.ofReal_toReal hc
  rw [relContractibleHZCapacity_def] at hlt
  obtain ⟨G, hG⟩ := lt_iSup_iff.1 hlt
  obtain ⟨hGadm, hGlt⟩ := lt_iSup_iff.1 hG
  exact ⟨G, hGadm, (ENNReal.ofReal_lt_ofReal_iff'.1 hGlt).1⟩

/-! ### Conformality -/

section Conformality

variable [FiniteDimensional ℝ E]

/-- Rescaling the form and a `(V, Z)`-admissible Hamiltonian in `W` by the same `c > 0` gives a
`(V, Z)`-admissible Hamiltonian in `W`. -/
private theorem IsRelContractibleHZAdmissible.smul_smul (hσ : σ.IsNondegenerate) {c : ℝ}
    (hc : 0 < c) (hF : σ.IsRelContractibleHZAdmissible W V Z F) :
    (c • σ).IsRelContractibleHZAdmissible W V Z (c • F) where
  toIsHZNormalized := hF.toIsHZNormalized.smul hc.le
  isMaxOn z hz := isMaxOn_iff.2 fun y hy ↦
    mul_le_mul_of_nonneg_left (isMaxOn_iff.1 (hF.isMaxOn z hz) y hy) hc.le
  eq_of_isMIntegralCurve := by
    rw [hσ.hamiltonianVectorField_smul_smul hc.ne']
    exact hF.eq_of_isMIntegralCurve

/-- **Admissibility is conformal.** For a nondegenerate form `σ` and `c > 0`, `cF` is
`(V, Z)`-admissible in `W` for `cσ` exactly when `F` is `(V, Z)`-admissible in `W` for `σ`. -/
theorem IsNondegenerate.isRelContractibleHZAdmissible_smul_smul_iff (hσ : σ.IsNondegenerate)
    {c : ℝ} (hc : 0 < c) :
    (c • σ).IsRelContractibleHZAdmissible W V Z (c • F) ↔
      σ.IsRelContractibleHZAdmissible W V Z F := by
  refine ⟨fun h ↦ ?_, IsRelContractibleHZAdmissible.smul_smul hσ hc⟩
  have h' := IsRelContractibleHZAdmissible.smul_smul (hσ.smul c hc.ne') (inv_pos.2 hc) h
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul] at h'

/-- **Conformality of the relative capacity.** For a nondegenerate form `σ` and `c > 0`,
`c°_HZ(V, Z; cσ) = c · c°_HZ(V, Z; σ)`, both in `W`. -/
theorem IsNondegenerate.relContractibleHZCapacity_smul (hσ : σ.IsNondegenerate) {c : ℝ}
    (hc : 0 < c) (W V Z : Set M) :
    (c • σ).relContractibleHZCapacity W V Z =
      ENNReal.ofReal c * σ.relContractibleHZCapacity W V Z :=
  iSup₂_ofReal_iSup_eq_ofReal_mul hc fun _ ↦ hσ.isRelContractibleHZAdmissible_smul_smul_iff hc

end Conformality

/-! ### Invariance under symplectomorphisms -/

section Invariance

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- A symplectomorphism `ψ` carries a `(V, Z)`-admissible Hamiltonian `F` in `W` to the
`(ψ(V), ψ(Z))`-admissible Hamiltonian `F ∘ ψ⁻¹` in `ψ(W)`. -/
theorem IsRelContractibleHZAdmissible.comp_symm (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hF : σ.IsRelContractibleHZAdmissible W V Z F) :
    σ₂.IsRelContractibleHZAdmissible (ψ '' W) (ψ '' V) (ψ '' Z) (F ∘ ψ.symm) := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  refine
    { toIsHZNormalized := hF.toIsHZNormalized.comp_symm ψ
      isMaxOn := ?_
      eq_of_isMIntegralCurve := ?_ }
  · rintro _ ⟨z, hz, rfl⟩
    refine isMaxOn_iff.2 fun y hy ↦ ?_
    simpa using isMaxOn_iff.1 (hF.isMaxOn z hz) (ψ.symm y) hy
  · rintro T γ hT hT1 hγ hper ⟨g, hg, hgγ⟩ t
    -- The curve `ψ⁻¹ ∘ γ` is a periodic orbit of `F`, contractible in `W` through `ψ⁻¹ ∘ g`, so
    -- it is constant.
    have hγ' : IsMIntegralCurve (ψ.symm ∘ γ) (σ.hamiltonianVectorField F) :=
      hσ₂.isMIntegralCurve_comp_hamiltonianVectorField hσ ψ.symm.contMDiff
        (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ)
        (fun _ ↦ (ψ.symm.isInvertible_mfderiv (by simp)).surjective)
        (fun _ ↦ (hF.contMDiff _).mdifferentiableAt (by simp)) hγ
    have hmem (y : ψ '' W) : ψ.symm y ∈ W := by
      obtain ⟨x, hx, hxy⟩ := y.2
      rwa [← hxy, ψ.symm_apply_apply]
    have h := hF.eq_of_isMIntegralCurve T (ψ.symm ∘ γ) hT hT1 hγ' (hper.comp _)
      ⟨(⟨fun y ↦ ⟨ψ.symm y, hmem y⟩, by fun_prop⟩ : C(ψ '' W, W)).comp g, hg.comp_right _,
        fun s ↦ by simp [hgγ]⟩ t
    exact ψ.symm.injective h

/-- **Symplectic invariance of the relative capacity.** If a diffeomorphism `ψ : M → M₂` pulls a
nondegenerate form `σ₂` back to `σ`, then `c°_HZ(ψ(V), ψ(Z); σ₂)` in `ψ(W)` equals
`c°_HZ(V, Z; σ)` in `W`, for all `W, V, Z ⊆ M`. -/
theorem IsNondegenerate.relContractibleHZCapacity_image (hσ₂ : σ₂.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I₂⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) (W V Z : Set M) :
    σ₂.relContractibleHZCapacity (ψ '' W) (ψ '' V) (ψ '' Z) =
      σ.relContractibleHZCapacity W V Z := by
  have hσ : σ.IsNondegenerate := hψ ▸ hσ₂.isNondegenerate_mpullback_of_isLocalDiffeomorph
    ψ.isLocalDiffeomorph
  refine iSup₂_ofReal_iSup_eq_of_comp ψ.surjective ψ.symm.surjective
    (fun _ hF ↦ hF.comp_symm hσ₂ ψ hψ) fun G hG ↦ ?_
  have h := hG.comp_symm hσ ψ.symm (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ)
  -- `Diffeomorph.symm` is involutive by definition.
  have hψ' : ψ.symm.symm = ψ := rfl
  rwa [hψ', ψ.symm_image_image, ψ.symm_image_image, ψ.symm_image_image] at h

end Invariance

end SmoothTwoForm

end TauCeti
