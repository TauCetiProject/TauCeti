/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Trivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise

/-!
# Fibre dilations of the symplectization of a contact structure

Let `ξ` be a contact structure on a finite-dimensional manifold `M`, with no defining one-form or
coorientation chosen. Its symplectization is the complement `ξ⁰ ∖ 0` of the zero section in the
annihilator line `ξ⁰ ⊂ T*M`, with the tautological one-form `θ_z(v) = z(dπ v)`
(`TauCeti.IsContactDistribution.annihilatorLiouvilleForm`) and the symplectic form `dθ`.

For a nonzero real number `c`, multiplying the covectors of `ξ⁰` by `c` is a diffeomorphism
`δ_c` of the line bundle `ξ⁰` (`TauCeti.vectorBundleScalarDiffeomorph` for the constant function
`c`). This file proves that the symplectization is *homogeneous*:

* `δ_c` pulls `θ` back to `c θ`, and hence `dθ` back to `c dθ`
  (`IsContactDistribution.mpullback_vectorBundleScalarDiffeomorph_annihilatorLiouvilleForm`);
* `δ_c` maps `ξ⁰ ∖ 0` onto itself
  (`TauCeti.IsContactDistribution.vectorBundleScalarDiffeomorph_mem_annihilatorPunctured_iff`).

In particular the positive dilations `δ_(eˢ)`, `s ∈ ℝ`, multiply `θ` by `eˢ`, while the fibre
negation `δ_(-1)` pulls `θ` back to `-θ`.

When `ξ = ker α` for a one-form `α`, the trivialization `κ_α : (t, x) ↦ eᵗ α_x` of one half of
`ξ⁰ ∖ 0` (`TauCeti.SmoothForm.symplectizationToAnnihilator`) turns these dilations into explicit
maps of `ℝ × M`. For `c > 0`, `δ_c` is the translation `t ↦ t + log c` of the real coordinate
(`TauCeti.SmoothForm.vectorBundleScalarDiffeomorph_symplectizationToAnnihilator`), the time
`log c` map of the Liouville field `∂_t` of the symplectization form `eᵗ α`. For `c < 0`, `δ_c`
exchanges the halves of `α` and `-α`
(`TauCeti.SmoothForm.vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_neg`): when
`ξ` is coorientable the two halves of `ξ⁰ ∖ 0` are exchanged by `ℓ ↦ -ℓ`, which pulls `θ` back
to `-θ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold and its homogeneity).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization of a contact structure).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle

/-! ### Dilations in contact-form trivializations -/

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)} {α : SmoothForm I M ℝ 1}
  (hα : α.kerDistribution = ξ) {k : ℕ} (hD : IsContMDiffDistribution I ∞ k ξ)
  (hk : k + 1 = finrank ℝ E)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

/-- **Dilations in contact-form trivializations.** If `c α_x = a β_x` at the point `x` with
`a > 0`, then multiplying the covector `κ_α (t, x) = eᵗ α_x` by `c` gives the covector
`κ_β (t + log a, x) = e^(t + log a) β_x`. -/
theorem vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_smul_eq
    {β : SmoothForm I M ℝ 1} (hβ : β.kerDistribution = ξ) {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a)
    (p : ℝ × M) (h : c • α.val p.2 = a • β.val p.2) :
    letI := hD.annihilatorFiberBundle hk
    haveI := hD.annihilatorVectorBundle hk
    vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
        (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
        (fun _ ↦ hc) (α.symplectizationToAnnihilator hα p) =
      β.symplectizationToAnnihilator hβ (p.1 + Real.log a, p.2) :=
  letI := hD.annihilatorFiberBundle hk
  haveI := hD.annihilatorVectorBundle hk
  by
  rw [vectorBundleScalarDiffeomorph_apply]
  refine totalSpace_annihilatorSpace_ext (by simp) fun v ↦ ?_
  -- Both covectors lie over `p.2`, so `v` is a tangent vector at `p.2`.
  have key (w : TangentSpace I p.2) :
      c * (Real.exp p.1 * α.val p.2 ![w]) = Real.exp (p.1 + Real.log a) * β.val p.2 ![w] := by
    have hw : c * α.val p.2 ![w] = a * β.val p.2 ![w] := by
      simpa using congrArg (fun φ ↦ φ ![w]) h
    rw [Real.exp_add, Real.exp_log ha, mul_left_comm, hw]
    ring
  exact ((congrArg (c * ·) (symplectizationToAnnihilator_snd_apply hα p v)).trans (key v)).trans
    (symplectizationToAnnihilator_snd_apply hβ (p.1 + Real.log a, p.2) v).symm

/-- **Positive dilations are translations of the trivialized symplectization.** For `c > 0`,
multiplying the covector `κ_α (t, x) = eᵗ α_x` by `c` gives `κ_α (t + log c, x)`. -/
theorem vectorBundleScalarDiffeomorph_symplectizationToAnnihilator {c : ℝ} (hc : 0 < c)
    (p : ℝ × M) :
    letI := hD.annihilatorFiberBundle hk
    haveI := hD.annihilatorVectorBundle hk
    vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
        (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
        (fun _ ↦ hc.ne') (α.symplectizationToAnnihilator hα p) =
      α.symplectizationToAnnihilator hα (p.1 + Real.log c, p.2) :=
  vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_smul_eq hα hD hk hα hc.ne' hc p rfl

/-- **Negative dilations exchange the two halves of the trivialized symplectization.** For `c < 0`,
multiplying the covector `κ_α (t, x) = eᵗ α_x` by `c` gives the covector
`κ_(-α) (t + log(-c), x) = e^(t + log(-c)) (-α_x)` of the opposite half. -/
theorem vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_neg {c : ℝ} (hc : c < 0)
    (p : ℝ × M) :
    letI := hD.annihilatorFiberBundle hk
    haveI := hD.annihilatorVectorBundle hk
    vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
        (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
        (fun _ ↦ hc.ne) (α.symplectizationToAnnihilator hα p) =
      (-α).symplectizationToAnnihilator (kerDistribution_neg.trans hα)
        (p.1 + Real.log (-c), p.2) :=
  vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_smul_eq hα hD hk
    (kerDistribution_neg.trans hα) hc.ne (neg_pos.2 hc) p (by simp)

end SmoothForm

/-! ### Homogeneity of the tautological one-form -/

namespace IsContactDistribution

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [Nonempty M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}
  (hξ : IsContactDistribution I ∞ ξ)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

/-- **The tautological one-form is homogeneous.** Multiplying the covectors of the annihilator
line `ξ⁰` by a nonzero real number `c` pulls the tautological one-form `θ` back to `c θ`. -/
theorem mpullback_vectorBundleScalarDiffeomorph_annihilatorLiouvilleForm {c : ℝ} (hc : c ≠ 0) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothForm.mpullback _
        (vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
          (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
          fun _ ↦ hc).contMDiff hξ.annihilatorLiouvilleForm =
      c • hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  -- The inclusion `ξ⁰ → T*M` intertwines the dilations of `ξ⁰` and of `T*M`, and the dilation
  -- by `c` of `T*M` pulls the Liouville form back to `c λ`.
  rw [annihilatorLiouvilleForm_def, SmoothForm.mpullback_mpullback_of_comp_eq _
      (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
      (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
      (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
        (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (fun _ ↦ c) (contMDiff_const (n := ∞))
        fun _ ↦ hc).contMDiff
      (funext fun z ↦ by simp [annihilatorInclusion_apply]),
    mpullback_vectorBundleScalarDiffeomorph_liouvilleForm hc, map_smul]

/-- **The symplectic form of the symplectization is homogeneous.** Multiplying the covectors of
the annihilator line `ξ⁰` by a nonzero real number `c` pulls the symplectic form `dθ` back to
`c dθ`. -/
theorem mpullback_vectorBundleScalarDiffeomorph_mextDerivₗ_annihilatorLiouvilleForm {c : ℝ}
    (hc : c ≠ 0) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothForm.mpullback _
        (vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
          (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
          fun _ ↦ hc).contMDiff
        (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm) =
      c • mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  rw [← SmoothForm.mextDerivₗ_mpullback,
    mpullback_vectorBundleScalarDiffeomorph_annihilatorLiouvilleForm hξ hc, map_smul]

/-- **Dilations preserve the symplectization.** Multiplying a covector of the annihilator line
`ξ⁰` by a nonzero real number `c` gives a nonzero covector exactly when the covector is nonzero,
so the dilation by `c` maps `ξ⁰ ∖ 0` onto itself. -/
theorem vectorBundleScalarDiffeomorph_mem_annihilatorPunctured_iff {c : ℝ} (hc : c ≠ 0)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    vectorBundleScalarDiffeomorph (I := I) (F := Fin 1 → ℝ)
        (V := fun x : M ↦ annihilatorSpace I ξ x) (fun _ ↦ c) (contMDiff_const (n := ∞))
        (fun _ ↦ hc) z ∈ hξ.annihilatorPunctured ↔
      z ∈ hξ.annihilatorPunctured :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by simp [mem_annihilatorPunctured, hc]

end IsContactDistribution

end TauCeti
