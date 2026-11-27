/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.EulerField
public import TauCeti.Geometry.Symplectic.Liouville.Completion
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.FiberBundle.Separation

/-!
# The unit codisc bundle is a Liouville domain

Let `M` be a compact smooth Riemannian manifold without boundary, with cotangent bundle
`T*M = TauCeti.CotangentBundle I M`, Liouville form `λ = p dq` and canonical symplectic form
`ω = -dλ`, which is nondegenerate (`TauCeti.CotangentBundle.isSymplectic_symplecticForm`). The
radial field `Z = p ∂_p`, the Euler vector field of the bundle, is the Liouville field of the
primitive `-λ` of `ω` (`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`).

The unit codisc bundle `D*M = {‖p‖ ≤ 1}` is compact, and it is the sublevel set of the norm of
covectors, which is continuous on `T*M` and smooth off the zero section. Along the fibre ray
`t ↦ t • z` the norm is `t ↦ |t| ‖z.2‖`, so the differential of the norm sends `Z` to `‖z.2‖`
(`TauCeti.CotangentBundle.mfderiv_norm_snd_vectorBundleEulerField`), which is `1 > 0` on the unit
cosphere bundle `S*M = {‖p‖ = 1}`. Hence `(D*M, -λ)` is a Liouville domain in `(T*M, ω)` with
Liouville field `p ∂_p` (`TauCeti.CotangentBundle.isLiouvilleDomain_codiscBundle`). It is the
Liouville domain on which the symplectic homology and the capacities of cotangent bundles are
computed; its boundary is `S*M`, of restricted contact type
(`TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`).

The flow of `p ∂_p` is the fibre dilation `p ↦ e^t p`, defined for all time, and it shrinks every
covector into `D*M`. So `T*M` is the completion of `D*M`
(`TauCeti.CotangentBundle.isLiouvilleCompletion_codiscBundle`): every covector outside `D*M` is
`e^t p` for exactly one unit covector `p` and one time `t > 0`.

Nearby choices of primitive, base or subset do not give Liouville domains:

* the primitive `λ` itself has differential `-ω`, so no set is a Liouville domain for `ω` with
  the primitive `λ` (`TauCeti.CotangentBundle.not_isLiouvilleDomain_liouvilleForm`);
* since `D*M` is compact exactly when `M` is, the codisc bundle of a noncompact manifold, such as
  `ℝ`, is not a Liouville domain (`TauCeti.CotangentBundle.not_isLiouvilleDomain_codiscBundle`);
* the backward flow `p ↦ e^(-t) p` of `p ∂_p` preserves every Liouville domain `W` for `-λ`, so
  `W` is star-shaped in the fibres and contains the zero covector below each of its points
  (`TauCeti.CotangentBundle.mk_smul_mem_of_isLiouvilleDomain`). Hence no nonempty set of nonzero
  covectors is such a Liouville domain
  (`TauCeti.CotangentBundle.not_isLiouvilleDomain_of_forall_snd_ne_zero`): not a shell
  `{a ≤ ‖p‖ ≤ b}`, `0 < a ≤ b` (`TauCeti.CotangentBundle.not_isLiouvilleDomain_shell`), nor a
  finite union of shells. For `a < b`, `p ∂_p` is transverse to the boundary of the shell, but
  along its inner boundary sphere `‖p‖ = a` it points into the shell.

## Main results

* `TauCeti.CotangentBundle.isLiouvilleDomain_codiscBundle`: `D*M` is a Liouville domain for the
  canonical symplectic form, with primitive `-λ`.
* `TauCeti.CotangentBundle.isLiouvilleCompletion_codiscBundle`: `T*M` is its completion.
* `TauCeti.CotangentBundle.not_isLiouvilleDomain_liouvilleForm`: `λ` is the primitive of no
  Liouville domain for `ω`.
* `TauCeti.CotangentBundle.not_isLiouvilleDomain_codiscBundle`: the codisc bundle of a noncompact
  manifold is not a Liouville domain.
* `TauCeti.CotangentBundle.mk_smul_mem_of_isLiouvilleDomain`: a Liouville domain for `-λ` is
  star-shaped in the fibres.
* `TauCeti.CotangentBundle.not_isLiouvilleDomain_of_forall_snd_ne_zero`,
  `TauCeti.CotangentBundle.not_isLiouvilleDomain_shell`: sets of nonzero covectors, such as shells,
  are not Liouville domains for `-λ`.

## References

* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (the unit codisc bundle as a Liouville domain).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

open Bundle
open scoped Manifold Topology

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

section Codisc

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]

/-- **The unit codisc bundle is a Liouville domain.** For a compact smooth Riemannian manifold
`M` without boundary, the unit codisc bundle `D*M` is a Liouville domain in `T*M` for the
canonical symplectic form `ω = -dλ`, with primitive `-λ`: its Liouville field, the radial field
`p ∂_p`, points strictly outwards along the unit cosphere bundle, the level `‖p‖ = 1` of the norm
of covectors. -/
theorem isLiouvilleDomain_codiscBundle [CompactSpace M] :
    IsLiouvilleDomain (symplecticForm I M) (-liouvilleForm I M) (codiscBundle I M) where
  isNondegenerate := isSymplectic_symplecticForm.isNondegenerate
  mextDeriv_eq := by
    rw [NegMemClass.coe_neg, mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv]
  isCompact := isCompact_codiscBundle
  subset_interior := by simp [ModelWithCorners.interior_eq_univ]
  exists_liouville_outward := by
    refine ⟨vectorBundleEulerField I, contMDiff_vectorBundleEulerField, ?_,
      fun z ↦ ‖z.snd‖, 1, continuous_norm_snd, Set.ext fun _ ↦ mem_codiscBundle, fun z hz ↦
        ⟨contMDiffAt_norm_snd_of_mem_cosphereBundle z hz, ?_⟩⟩
    · rw [NegMemClass.coe_neg, symplecticForm_interior_vectorBundleEulerField]
    · -- `mvfderiv` is `mfderiv` read in `ℝ`, and the norm of covectors sends `p ∂_p` to `‖p‖`.
      rw [mvfderiv_apply_eq_mfderiv_apply,
        mfderiv_norm_snd_vectorBundleEulerField (snd_ne_zero_of_mem_cosphereBundle hz)]
      exact (mem_cosphereBundle.1 hz).symm ▸ one_pos

/-- **The cotangent bundle is the completion of the unit codisc bundle.** For a compact smooth
Riemannian manifold `M` without boundary, `T*M` is a completion of the Liouville domain `D*M`: the
flow `p ↦ e^t p` of its Liouville field `p ∂_p` is defined for all time, and carries every
covector into `D*M`. -/
theorem isLiouvilleCompletion_codiscBundle [CompactSpace M] [T2Space M] :
    IsLiouvilleCompletion (symplecticForm I M) (-liouvilleForm I M) (codiscBundle I M) where
  toIsLiouvilleDomain := isLiouvilleDomain_codiscBundle
  exists_isCompleteVectorField := by
    have hc := isCompleteVectorField_vectorBundleEulerField (I := I)
      (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (F := E →L[ℝ] ℝ)
    refine ⟨vectorBundleEulerField I, ?_, hc, fun z ↦ ⟨-‖z.snd‖, ?_⟩⟩
    · rw [NegMemClass.coe_neg, symplecticForm_interior_vectorBundleEulerField]
    -- The flow line of `z` is the fibre ray `t ↦ e^t z`.
    rw [flowOf_vectorBundleEulerField, mem_codiscBundle, norm_smul_snd,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg, inv_mul_le_one₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp ‖z.snd‖]

end Codisc

/-! ### Sets that are not Liouville domains -/

/-- **The unit codisc bundle of a noncompact manifold is not a Liouville domain**, for any form and
primitive, since `D*M` is compact exactly when `M` is (`isCompact_codiscBundle_iff`). This applies
for instance to `M = ℝ`. -/
theorem not_isLiouvilleDomain_codiscBundle [FiniteDimensional ℝ E]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] [NoncompactSpace M]
    (ω : SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M))
    (α : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ 1) :
    ¬ IsLiouvilleDomain ω α (codiscBundle I M) := fun h ↦
  not_compactSpace_iff.2 ‹_› (isCompact_codiscBundle_iff.1 h.isCompact)

/-- **The Liouville form itself is not the primitive of a Liouville domain.** For a nonempty
manifold of positive dimension, no set is a Liouville domain for the canonical form `ω = -dλ` with
the primitive `λ`: its differential is `-ω`. The vector field `Z` with `ι_Z ω = λ` is `-p ∂_p`,
which points into the unit codisc bundle. -/
theorem not_isLiouvilleDomain_liouvilleForm [Nonempty M] [Nontrivial E]
    (W : Set (CotangentBundle I M)) :
    ¬ IsLiouvilleDomain (symplecticForm I M) (liouvilleForm I M) W := by
  have : Nonempty (CotangentBundle I M) := ⟨⟨Classical.arbitrary M, 0⟩⟩
  have := not_isLiouvilleDomain_neg_of_mextDeriv_eq (α := -liouvilleForm I M)
    (ω := symplecticForm I M)
    (by rw [NegMemClass.coe_neg, mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv]) W
  rwa [neg_neg] at this

variable [I.Boundaryless] [T2Space M]

/-- **A Liouville domain for `-λ` is star-shaped in the fibres.** If `W ⊆ T*M` is a Liouville domain
for the canonical form `ω = -dλ` with the primitive `-λ`, then with every covector `z` it contains
`s • z` for `0 ≤ s ≤ 1`, in particular the zero covector over the same point. The Liouville field
is `p ∂_p`, whose flow `p ↦ e^t p` is complete, and the backward flow preserves a Liouville
domain. -/
theorem mk_smul_mem_of_isLiouvilleDomain {W : Set (CotangentBundle I M)}
    (h : IsLiouvilleDomain (symplecticForm I M) (-liouvilleForm I M) W)
    {z : CotangentBundle I M} (hz : z ∈ W) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    (⟨z.proj, s • z.snd⟩ : CotangentBundle I M) ∈ W := by
  have hZ : RoughForm.interior (vectorBundleEulerField I) (symplecticForm I M).val =
      (-liouvilleForm I M).val := by
    rw [NegMemClass.coe_neg, symplecticForm_interior_vectorBundleEulerField]
  have hc := isCompleteVectorField_vectorBundleEulerField (I := I)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (F := E →L[ℝ] ℝ)
  -- For `s > 0`, the covector `s • z` is `z` flowed backwards for the time `-log s ≥ 0`.
  have hpos : ∀ s : ℝ, 0 < s → s ≤ 1 → (⟨z.proj, s • z.snd⟩ : CotangentBundle I M) ∈ W :=
    fun s hs hs₁ ↦ by
      have := h.flowOf_neg_mem hZ hc hz (t := -Real.log s)
        (neg_nonneg.2 (Real.log_nonpos hs.le hs₁))
      rwa [neg_neg, flowOf_vectorBundleEulerField, Real.exp_log hs] at this
  rcases hs₀.lt_or_eq with hs | rfl
  · exact hpos s hs hs₁
  -- For `s = 0`, the zero covector is the limit of the covectors `s • z` as `s → 0⁺`.
  have hcont : Continuous fun s : ℝ ↦ (⟨z.proj, s • z.snd⟩ : CotangentBundle I M) :=
    (FiberBundle.continuous_totalSpaceMk _ _ z.proj).comp (continuous_id.smul continuous_const)
  refine h.isClosed.mem_of_tendsto
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds : Filter.Tendsto _ (𝓝[>] (0 : ℝ)) _) ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs using hpos s hs.1 hs.2.le

/-- **A Liouville domain for `-λ` meets the zero section**: a nonempty set of nonzero covectors is
not a Liouville domain for the canonical form with the primitive `-λ`. This applies to every shell
`{a ≤ ‖p‖ ≤ b}` with `0 < a ≤ b`, and to every finite union of such shells. For `a < b`, the
Liouville field `p ∂_p` points into the shell along its inner boundary `‖p‖ = a`. -/
theorem not_isLiouvilleDomain_of_forall_snd_ne_zero {W : Set (CotangentBundle I M)}
    (hW : W.Nonempty) (h₀ : ∀ z ∈ W, z.snd ≠ 0) :
    ¬ IsLiouvilleDomain (symplecticForm I M) (-liouvilleForm I M) W := fun h ↦ by
  obtain ⟨z, hz⟩ := hW
  simpa using h₀ _ (mk_smul_mem_of_isLiouvilleDomain h hz le_rfl zero_le_one)

/-- **A shell of covectors is not a Liouville domain.** For a nonempty manifold of positive
dimension and `0 < a ≤ b`, the shell `{a ≤ ‖p‖ ≤ b}` in `T*M` is not a Liouville domain for the
canonical form with the primitive `-λ`. For `a < b`, the Liouville field `p ∂_p` is transverse to
both of its boundary components, but it points into the shell along the inner one `‖p‖ = a`. -/
theorem not_isLiouvilleDomain_shell [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Nonempty M] [Nontrivial E] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ¬ IsLiouvilleDomain (symplecticForm I M) (-liouvilleForm I M)
      {z : CotangentBundle I M | a ≤ ‖z.snd‖ ∧ ‖z.snd‖ ≤ b} := by
  refine not_isLiouvilleDomain_of_forall_snd_ne_zero ?_ fun z hz h0 ↦ ?_
  · -- A nonzero covector, normalized and scaled by `a`, has norm `a`.
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
    set z₀ : CotangentBundle I M := ⟨Classical.arbitrary M, g⟩
    -- The covector `z₀.snd` is `g` by definition of `z₀`.
    have hz₀ : z₀.snd ≠ 0 := fun h ↦ by
      rw [show g = 0 from h, zero_apply] at hg
      exact hv (norm_eq_zero.1 (RCLike.ofReal_eq_zero.1 hg.symm))
    refine ⟨⟨(normalize z₀).proj, a • (normalize z₀).snd⟩, ?_⟩
    rw [Set.mem_ofPred_eq, norm_smul_snd, Real.norm_of_nonneg ha.le, norm_snd_normalize hz₀,
      mul_one]
    exact ⟨le_rfl, hab⟩
  · rw [Set.mem_ofPred_eq, h0, (ContinuousLinearMap.opNorm_zero_iff _).2 rfl] at hz
    exact ha.not_ge hz.1

end CotangentBundle

end TauCeti
