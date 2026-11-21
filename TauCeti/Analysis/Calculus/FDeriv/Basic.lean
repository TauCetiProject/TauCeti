/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Differentiability criteria

The derivative `fderiv 𝕜 f` is totalized: it is `0` where `f` is not differentiable. So a
nonzero derivative certifies differentiability, as `differentiableAt_of_deriv_ne_zero` does for
functions of one variable. Likewise, two differentiable independent linear combinations of two
scalar functions recover both functions as differentiable.

## Main results

* `TauCeti.differentiableAt_of_fderiv_ne_zero`: a function is differentiable wherever its
  derivative does not vanish.
* `TauCeti.differentiableAt_of_fderiv_surjective`: a function is differentiable wherever its
  derivative is surjective.
* `TauCeti.surjective_fderiv_iff_ne_zero_of_finrank_eq_one`: for a map into a one-dimensional
  space, surjectivity of `fderiv` is equivalent to `fderiv ≠ 0`.
* `TauCeti.differentiableAt_and_of_differentiableAt_comb`: if two combinations `a F + b G` and
  `c F + d G` with `a d - b c ≠ 0` are differentiable at a point, so are `F` and `G`.
* `Asymptotics.IsBigO.hasFDerivWithinAt_zero`, `Asymptotics.IsBigO.hasFDerivAt_zero`: a function
  dominated near a point by a function with zero value and zero derivative there has zero
  derivative there as well.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}

section Topological

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {f : E → F} {x : E}

/-- A function is differentiable wherever its totalized derivative does not vanish. -/
theorem differentiableAt_of_fderiv_ne_zero (h : fderiv 𝕜 f x ≠ 0) : DifferentiableAt 𝕜 f x := by
  by_contra hnd
  exact h (fderiv_zero_of_not_differentiableAt hnd)

/-- A function is differentiable wherever its totalized derivative is surjective. -/
theorem differentiableAt_of_fderiv_surjective (h : Function.Surjective (fderiv 𝕜 f x)) :
    DifferentiableAt 𝕜 f x := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · exact Subsingleton.elim (fun _ ↦ f x) f ▸ differentiableAt_const (f x)
  contrapose h
  rw [fderiv_zero_of_not_differentiableAt h]
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  exact fun hs ↦ hv (by simpa using (hs v).choose_spec.symm)

/-- For a map into a one-dimensional space, the totalized Fréchet derivative is surjective if and
only if it is nonzero. -/
theorem surjective_fderiv_iff_ne_zero_of_finrank_eq_one (hF : Module.finrank 𝕜 F = 1) :
    Function.Surjective (fderiv 𝕜 f x) ↔ fderiv 𝕜 f x ≠ 0 := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  refine ⟨fun hsurj hzero ↦ ?_, fun hne ↦
    _root_.surjective_of_ne_zero_of_finrank_eq_one (f := (fderiv 𝕜 f x : E →ₗ[𝕜] F)) hF
      fun h ↦ hne (ContinuousLinearMap.coe_injective h)⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hsurj y
  exact hy (by simpa [hzero] using hv.symm)

end Topological

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : E}

/-- If two combinations `a F + b G` and `c F + d G` with `a d - b c ≠ 0` are differentiable at a
point, then so are `F` and `G`: they are recovered by inverting the coefficient matrix. -/
theorem differentiableAt_and_of_differentiableAt_comb {F G : E → 𝕜} {a b c d : 𝕜}
    (hdet : a * d - b * c ≠ 0) (hA : DifferentiableAt 𝕜 (fun y ↦ a * F y + b * G y) x)
    (hB : DifferentiableAt 𝕜 (fun y ↦ c * F y + d * G y) x) :
    DifferentiableAt 𝕜 F x ∧ DifferentiableAt 𝕜 G x := by
  have hi : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 := mul_inv_cancel₀ hdet
  constructor
  · have : F = fun y ↦ (d / (a * d - b * c)) * (a * F y + b * G y) +
        (-b / (a * d - b * c)) * (c * F y + d * G y) := by
      funext y
      simp only [div_eq_mul_inv]
      linear_combination (-(F y)) * hi
    rw [this]
    exact (hA.const_mul _).add (hB.const_mul _)
  · have : G = fun y ↦ (-c / (a * d - b * c)) * (a * F y + b * G y) +
        (a / (a * d - b * c)) * (c * F y + d * G y) := by
      funext y
      simp only [div_eq_mul_inv]
      linear_combination (-(G y)) * hi
    rw [this]
    exact (hA.const_mul _).add (hB.const_mul _)

end TauCeti

section Domination

open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {g : E → G} {s : Set E} {x : E}

/-- **Domination preserves zero first jets.** If `f = O(g)` near `x` within a set `s` containing
`x`, and `g` has value `0` and derivative `0` at `x` within `s`, then `f` has derivative `0` at `x`
within `s`. -/
theorem Asymptotics.IsBigO.hasFDerivWithinAt_zero (h : f =O[𝓝[s] x] g)
    (hg : HasFDerivWithinAt g (0 : E →L[𝕜] G) s x) (hgx : g x = 0) (hx : x ∈ s) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x := by
  have hfx : f x = 0 := by
    obtain ⟨C, hC⟩ := h.bound
    simpa [hgx] using hC.self_of_nhdsWithin hx
  rw [hasFDerivWithinAt_iff_isLittleO] at hg ⊢
  simp only [hfx, hgx, sub_zero, zero_apply] at hg ⊢
  exact h.trans_isLittleO hg

/-- **Domination preserves zero first jets.** If `f = O(g)` near `x`, and `g` has value `0` and
derivative `0` at `x`, then `f` has derivative `0` at `x`. -/
theorem Asymptotics.IsBigO.hasFDerivAt_zero (h : f =O[𝓝 x] g)
    (hg : HasFDerivAt g (0 : E →L[𝕜] G) x) (hgx : g x = 0) : HasFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ] at hg ⊢
  exact (nhdsWithin_univ x ▸ h).hasFDerivWithinAt_zero hg hgx (Set.mem_univ x)

end Domination
