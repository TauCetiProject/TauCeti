/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Integration by parts against a cutoff

On an oriented boundaryless manifold, a form `α` and a compactly supported C¹ function `φ`
satisfy `∫ dφ ∧ α = -∫ φ dα` if `α` is locally C¹ at every point of `tsupport φ` and `φ dα`
is integrable. Stokes applies to the globally C¹, compactly supported form `φ α`.
This permits forms whose regularity is only known near the support of the cutoff.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] {k : ℕ}

/-- **Integration by parts against a cutoff.** A `k`-form `α` on an oriented boundaryless
`(k + 1)`-manifold satisfies `∫ dφ ∧ α = -∫ φ dα` for every compactly supported C¹ function `φ`,
assuming `α` is locally C¹ at every point of `tsupport φ` and `φ dα` is integrable. The cast
identifies the degree `1 + k` of the wedge with `k + 1`. -/
theorem integralTopForm_mextDeriv_ofFunction_wedge_eq_neg
    (o : Manifold.Orientation I M (Fin (k + 1))) {α : RoughForm I M ℝ k} {φ : M → ℝ}
    (hα : ∀ x ∈ tsupport φ, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) 1
      (fun y ↦ Bundle.TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (α y)) x)
    (hφ : ContMDiff I 𝓘(ℝ) 1 φ) (hφc : HasCompactSupport φ)
    (hi : IntegrableTopForm (fun x ↦ φ x • mextDeriv α x)) :
    integralTopForm o (LinearEquiv.cast (R := ℝ) (M := fun q ↦ RoughForm I M ℝ q)
      (Nat.add_comm 1 k) ((mextDeriv (RoughForm.ofFunction I φ)).wedge α)) =
        -integralTopForm o (fun x ↦ φ x • mextDeriv α x) := by
  let η : RoughForm I M ℝ k := fun y ↦ φ y • α y
  have hη : IsSmoothForm I 1 η := by
    rw [isSmoothForm_def]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact hφ.contMDiffAt.smul_section (hα x hx)
    · apply ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ..)
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [η, hy, Bundle.zeroSection]
  have hηc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) η) :=
    hφc.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left φ (show M → E [⋀^Fin k]→L[ℝ] ℝ from α))
  have hcast {a b : ℕ} (h : a = b) (β : RoughForm I M ℝ a) (x : M)
      (v : Fin b → TangentSpace I x) :
      (LinearEquiv.cast (R := ℝ) (M := fun q ↦ RoughForm I M ℝ q) h β) x v =
        β x (v ∘ Fin.cast h) := by cases h; rfl
  have heq : LinearEquiv.cast (R := ℝ) (M := fun q ↦ RoughForm I M ℝ q)
      (Nat.add_comm 1 k) ((mextDeriv (RoughForm.ofFunction I φ)).wedge α) =
        mextDeriv η - (fun x ↦ φ x • mextDeriv α x) := by
    funext x
    ext v
    rw [hcast]
    by_cases hx : x ∈ tsupport φ
    · have hd := mextDeriv_fun_smul (hφ.mdifferentiableAt one_ne_zero)
        ((hα x hx).mdifferentiableAt one_ne_zero) v
      simp only [Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      exact (eq_sub_iff_add_eq.mpr hd.symm)
    · have hφx : ∀ᶠ y in 𝓝 x, φ y = 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hdφ : mextDeriv (RoughForm.ofFunction I φ) x = 0 := by
        rw [mextDeriv_congr_of_eventuallyEq (η := 0) (hφx.mono fun y hy ↦
          ContinuousAlternatingMap.ext fun w ↦ by simp [hy]), mextDeriv_zero, Pi.zero_apply]
      have hdη : mextDeriv η x = 0 := by
        rw [mextDeriv_congr_of_eventuallyEq (η := 0) (hφx.mono fun y hy ↦ by simp [η, hy]),
          mextDeriv_zero, Pi.zero_apply]
      rw [RoughForm.wedge_apply, hdφ]
      simp [hdη, image_eq_zero_of_notMem_tsupport hx]
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  rw [heq, integralTopForm_sub_of_integrable o
    (hη.continuous_mextDeriv.integrableTopForm (η.isCompact_tsupport_mextDeriv hηc) b) hi,
    integralTopForm_mextDeriv_eq_zero o hη hηc, zero_sub]

end TauCeti
