/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Derivatives of homogeneous polynomials above their degree

A continuous `k`-multilinear map `f`, restricted to the diagonal, is the homogeneous polynomial
`x ↦ f (x, …, x)` of degree `k`. Its iterated derivatives of every order above `k` vanish
identically (`ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_eq_zero`). The basic example is
the product `x ↦ ∏ⱼ ℓⱼ x` of `k` continuous linear maps with values in a normed commutative
algebra (`TauCeti.iteratedFDeriv_prod_eq_zero`), such as the symbol `∏ⱼ i ⟪ξ, vⱼ⟫` of the
directional derivative `∂_{v₁} ⋯ ∂_{vₖ}`, which is a polynomial of degree `k` in the frequency `ξ`.
-/

public section

variable {𝕜 E F A : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Derivatives of a homogeneous polynomial above its degree vanish.** The restriction
`x ↦ f (x, …, x)` of a continuous `k`-multilinear map `f` to the diagonal has vanishing iterated
derivatives of every order `N > k`. -/
theorem ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_eq_zero {k N : ℕ}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ E) F) (hN : k < N) :
    iteratedFDeriv 𝕜 N (fun x ↦ f fun _ ↦ x) = 0 := by
  -- The diagonal map `x ↦ (x, …, x)` is linear, and the derivatives of `f` itself vanish above
  -- its number `k` of arguments.
  let L : E →L[𝕜] (Fin k → E) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id 𝕜 E
  have hf : iteratedFDeriv 𝕜 N f = 0 := funext fun y ↦ norm_le_zero_iff.1 <|
    (f.norm_iteratedFDeriv_le N y).trans_eq <| by
      rw [Fintype.card_fin, Nat.descFactorial_eq_zero_iff_lt.2 hN]
      simp
  have hL : (fun x ↦ f fun _ ↦ x) = f ∘ L := funext fun x ↦ by simp [L]
  funext x
  rw [hL, L.iteratedFDeriv_comp_right f.contDiff x (i := N) (by exact_mod_cast le_top), hf]
  ext
  simp

namespace TauCeti

variable [NormedCommRing A] [NormedAlgebra 𝕜 A]

/-- **Derivatives of a product of linear maps above its degree vanish.** The product
`x ↦ ∏ⱼ ℓⱼ x` of `k` continuous linear maps `ℓⱼ : E →L[𝕜] A` into a normed commutative algebra
has vanishing iterated derivatives of every order `N > k`. -/
theorem iteratedFDeriv_prod_eq_zero {k N : ℕ} (ℓ : Fin k → E →L[𝕜] A) (hN : k < N) :
    iteratedFDeriv 𝕜 N (fun x ↦ ∏ j, ℓ j x) = 0 := by
  have h := ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) A).compContinuousLinearMap
    ℓ).iteratedFDeriv_comp_diagonal_eq_zero hN
  simpa using h

end TauCeti
