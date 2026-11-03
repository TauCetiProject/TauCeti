/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Lipschitz-small perturbations of the identity are diffeomorphisms

If `u : E → E` is `C^n`, `1 ≤ n`, and `K`-Lipschitz with `K < 1`, on a Banach space `E` over a
nontrivially normed field, then `x ↦ x + u x` is a `C^n` diffeomorphism of `E`
(`ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith`). It is a homeomorphism because it
approximates the identity (`ApproximatesLinearOn.toHomeomorph`), and its derivative `1 + Du` is
invertible everywhere, so its inverse is `C^n` (`Homeomorph.contDiff_symm`).

## Main results

* `ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith`: a `C^n` map `u` which is
  `K`-Lipschitz with `K < 1` makes `x ↦ x + u x` a `C^n` diffeomorphism.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **A Lipschitz-small perturbation of the identity is a diffeomorphism.** If `u : E → E` is
`C^n`, `1 ≤ n`, and `K`-Lipschitz with `K < 1`, on a Banach space `E`, then `x ↦ x + u x` is a
`C^n` diffeomorphism of `E`. -/
theorem exists_diffeomorph_apply_eq_add_of_lipschitzWith {n : WithTop ℕ∞} {u : E → E}
    (hu : ContDiff 𝕜 n u) (hn : 1 ≤ n) {K : ℝ≥0} (hlip : LipschitzWith K u) (hK : K < 1) :
    ∃ φ : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E, ∀ x, φ x = x + u x := by
  have hf : ApproximatesLinearOn (fun x ↦ x + u x)
      ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E) univ K := by
    rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
    convert hlip.lipschitzOnWith (s := univ) using 1
    ext x
    simp
  have hc : Subsingleton E ∨
      K < ‖(((ContinuousLinearEquiv.refl 𝕜 E).symm : E ≃L[𝕜] E) : E →L[𝕜] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · right
      simpa using hK
  -- The derivative `1 + Du a = 1 - (-Du a)` is a unit, since `‖Du a‖ ≤ K < 1`.
  have hnorm (a : E) : ‖-fderiv 𝕜 u a‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz 𝕜 hlip).trans_lt (by exact_mod_cast hK)
  have hf' (a : E) : HasFDerivAt (fun x ↦ x + u x)
      ((ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub _ (hnorm a)) : E ≃L[𝕜] E) :
        E →L[𝕜] E) a := by
    refine ((hasFDerivAt_id a).add
      (hu.differentiable (zero_lt_one.trans_le hn).ne' a).hasFDerivAt).congr_fderiv ?_
    ext v
    simp [sub_eq_add_neg]
  have hfd : ContDiff 𝕜 n (fun x ↦ x + u x) := contDiff_id.add hu
  let H := hf.toHomeomorph _ hc
  exact ⟨{ toEquiv := H.toEquiv
           contMDiff_toFun := contMDiff_iff_contDiff.2 hfd
           contMDiff_invFun := contMDiff_iff_contDiff.2 (H.contDiff_symm hf' hfd) },
    fun _ ↦ rfl⟩

end ContDiff
