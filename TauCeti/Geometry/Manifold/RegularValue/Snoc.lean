/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# Appending a function to a regular family

A point `x` is a regular point of a family `F = (F₁, …, F_k) : M → 𝕜ᵏ` of functions on a manifold
when the differentials `dF_i(x)` are independent. This file shows that appending a function `g`
keeps `x` regular as soon as the differential of `g` at `x` does not vanish on some vector of
`ker dF_x` (`TauCeti.IsRegularPoint.finSnoc`): the family `(F₁, …, F_k, g)` then has independent
differentials. This is how families of independent functions, such as involutive families on a
symplectic manifold, are enlarged one function at a time.
-/

public section

open scoped Manifold

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

namespace TauCeti

/-- **Appending a function to a regular family.** If `x` is a regular point of
`F = (F₁, …, F_k)` and the differential of `g` at `x` does not vanish on some vector of
`ker dF_x`, then `x` is a regular point of `(F₁, …, F_k, g)`. -/
theorem IsRegularPoint.finSnoc {F : M → Fin k → 𝕜} {g : M → 𝕜} {x : M}
    (hF : IsRegularPoint I 𝓘(𝕜, Fin k → 𝕜) F x) (hg : MDifferentiableAt I 𝓘(𝕜) g x)
    {w : TangentSpace I x} (hw : w ∈ (mfderiv I 𝓘(𝕜, Fin k → 𝕜) F x).ker)
    (hgw : mvfderiv I g x w ≠ 0) :
    IsRegularPoint I 𝓘(𝕜, Fin (k + 1) → 𝕜) (fun y ↦ Fin.snoc (α := fun _ ↦ 𝕜) (F y) (g y)) x := by
  have hFd := hF.mdifferentiableAt
  have hd := hFd.finSnoc hg
  have hFw : mvfderiv I F x w = 0 := by
    rw [← ker_mvfderiv] at hw
    exact hw
  rw [isRegularPoint_iff_surjective_mvfderiv] at hF ⊢
  intro t
  obtain ⟨v₀, hv₀⟩ := hF (Fin.init t)
  set c := (mvfderiv I g x w)⁻¹ * (t (Fin.last k) - mvfderiv I g x v₀)
  refine ⟨v₀ + c • w, funext fun i ↦ ?_⟩
  -- Read the `i`-th component of the derivative as the derivative of the `i`-th component.
  have hi := DFunLike.congr_fun (mvfderiv_apply hd i) (v₀ + c • w)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hi
  rw [← hi]
  clear hi
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last, map_add, map_smul, smul_eq_mul]
    -- The component `fun y ↦ g y` is `g` up to eta.
    rw [show mvfderiv I (fun y ↦ g y) = mvfderiv I g from rfl, mul_comm c,
      mul_inv_cancel_left₀ hgw]
    ring
  | cast j =>
    simp only [Fin.snoc_castSucc]
    rw [DFunLike.congr_fun (mvfderiv_apply hFd j), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, map_add, map_smul, hFw, hv₀]
    simp [Fin.init]

end TauCeti
