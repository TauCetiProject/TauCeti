/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The vector `H_λ` of a restricted root and the bracket `[E, θE]`

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀` and `𝔞` a subspace of its `-1`-eigenspace
`𝔭`. The Killing form `B` is positive definite on `𝔭`, hence nondegenerate on `𝔞`, so every linear
functional `λ` on `𝔞` is represented by a unique `H_λ ∈ 𝔞`: `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`
(`LieEquiv.IsCartanInvolution.restrictedRootVector`). For `λ ≠ 0`, `λ(H_λ) = B(H_λ, H_λ) > 0`.

When `𝔞` is maximal abelian in `𝔭` and `E ∈ 𝔤_λ`, the bracket `[E, θE]` lies in `𝔤_0 ∩ 𝔭 = 𝔞`, and
pairing it with `H ∈ 𝔞` gives `B([E, θE], H) = B(E, [θE, H]) = λ(H) B(E, θE)`, so
`[E, θE] = B(E, θE) H_λ` (Knapp, Ch. VI, Prop. 6.52). With `[H_λ, E] = λ(H_λ) E` and
`[H_λ, θE] = -λ(H_λ) θE`, this is the first step towards the copy of `𝔰𝔩₂(ℝ)` spanned by `E`, `θE`
and `H_λ`.

## Main definitions

* `LieEquiv.IsCartanInvolution.restrictedRootVector`: the vector `H_λ ∈ 𝔞` representing `λ` under
  the Killing form.

## Main results

* `LieEquiv.IsCartanInvolution.killingForm_restrictedRootVector`: `B(H_λ, H) = λ(H)`.
* `LieEquiv.IsCartanInvolution.apply_restrictedRootVector_pos`: `λ(H_λ) > 0` for `λ ≠ 0`.
* `LieEquiv.IsCartanInvolution.lie_apply_eq_smul_restrictedRootVector`:
  `[E, θE] = B(E, θE) H_λ` for `E ∈ 𝔤_λ`, `𝔞` maximal abelian in `𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.52.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv.IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- The Killing form restricted to a subspace of `𝔭` is positive definite. -/
theorem killingForm_restrict_pos (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP) (H : 𝔞)
    (hH : H ≠ 0) : 0 < (killingForm ℝ L).restrict 𝔞 H H :=
  hθ.killingForm_apply_self_pos_of_mem_cartanP (h𝔞 H.property)
    (by simpa using (Submodule.coe_eq_zero (x := H)).not.mpr hH)

/-- The Killing form restricted to a subspace of `𝔭` is nondegenerate. -/
theorem nondegenerate_killingForm_restrict (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP) :
    ((killingForm ℝ L).restrict 𝔞).Nondegenerate :=
  have := hθ.finiteDimensional
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (LinearMap.BilinForm.separatingLeft_of_anisotropic fun H hH ↦ by
      by_contra hne
      exact (hθ.killingForm_restrict_pos h𝔞 H hne).ne' hH)

/-- **The vector `H_λ` of a functional `λ` on `𝔞`**: for a Cartan involution `θ` and a subspace
`𝔞` of `𝔭`, the unique `H_λ ∈ 𝔞` with `B(H_λ, H) = λ(H)` for all `H ∈ 𝔞`, where `B` is the Killing
form. -/
noncomputable def restrictedRootVector (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)
    (μ : Dual ℝ 𝔞) : 𝔞 :=
  have := hθ.finiteDimensional
  ((killingForm ℝ L).restrict 𝔞).toDual (hθ.nondegenerate_killingForm_restrict h𝔞) |>.symm μ

variable (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

/-- `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`. -/
theorem killingForm_restrictedRootVector (μ : Dual ℝ 𝔞) (H : 𝔞) :
    killingForm ℝ L (hθ.restrictedRootVector h𝔞 μ) H = μ H := by
  have := hθ.finiteDimensional
  have := LinearMap.BilinForm.toDual_def (hθ.nondegenerate_killingForm_restrict h𝔞)
    (m := hθ.restrictedRootVector h𝔞 μ) (n := H)
  rw [restrictedRootVector, LinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- `H_λ` is characterized by `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`. -/
theorem eq_restrictedRootVector_iff (μ : Dual ℝ 𝔞) (X : 𝔞) :
    X = hθ.restrictedRootVector h𝔞 μ ↔ ∀ H : 𝔞, killingForm ℝ L X H = μ H := by
  refine ⟨fun h H ↦ h ▸ hθ.killingForm_restrictedRootVector h𝔞 μ H, fun h ↦ ?_⟩
  have := hθ.finiteDimensional
  rw [restrictedRootVector, LinearEquiv.eq_symm_apply]
  exact LinearMap.ext fun H ↦ (LinearMap.BilinForm.toDual_def _).trans (h H)

/-- `λ(H_λ) = B(H_λ, H_λ) > 0` for `λ ≠ 0`. -/
theorem apply_restrictedRootVector_pos {μ : Dual ℝ 𝔞} (hμ : μ ≠ 0) :
    0 < μ (hθ.restrictedRootVector h𝔞 μ) := by
  rw [← hθ.killingForm_restrictedRootVector h𝔞 μ]
  refine hθ.killingForm_restrict_pos h𝔞 _ fun h ↦ hμ ?_
  ext H
  rw [← hθ.killingForm_restrictedRootVector h𝔞 μ H, h]
  simp

/-- **`[E, θE] = B(E, θE) H_λ`** for `E ∈ 𝔤_λ`, when `𝔞` is maximal abelian in `𝔭`
(Knapp, Prop. 6.52). -/
theorem lie_apply_eq_smul_restrictedRootVector (h𝔞 : θ.IsMaximalAbelianInP 𝔞)
    {μ : Dual ℝ 𝔞} {E : L} (hE : E ∈ 𝔞.restrictedRootSpace μ) :
    ⁅E, θ E⁆ = killingForm ℝ L E (θ E) • (hθ.restrictedRootVector h𝔞.le_cartanP μ : L) := by
  have hθE := apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hE
  have h0 : ⁅E, θ E⁆ ∈ 𝔞.restrictedRootSpace 0 := by
    simpa using Submodule.lie_mem_restrictedRootSpace hE hθE
  have hp : ⁅E, θ E⁆ ∈ θ.cartanP := by
    rw [mem_cartanP, LieEquiv.map_lie, hθ.involutive E, ← lie_skew]
  have hX : ⁅E, θ E⁆ ∈ 𝔞 := h𝔞.restrictedRootSpace_zero_inf_cartanP ▸ ⟨h0, hp⟩
  have key : (⟨⁅E, θ E⁆, hX⟩ : 𝔞) =
      hθ.restrictedRootVector h𝔞.le_cartanP (killingForm ℝ L E (θ E) • μ) := by
    rw [eq_restrictedRootVector_iff]
    intro H
    have hH := (Submodule.mem_restrictedRootSpace.mp hθE) H
    rw [traceForm_apply_lie_apply, ← lie_skew, hH, LinearMap.neg_apply, neg_smul, neg_neg,
      map_smul, smul_eq_mul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  have hlin : hθ.restrictedRootVector h𝔞.le_cartanP (killingForm ℝ L E (θ E) • μ) =
      killingForm ℝ L E (θ E) • hθ.restrictedRootVector h𝔞.le_cartanP μ := by
    rw [restrictedRootVector, restrictedRootVector, map_smul]
  have := congrArg Subtype.val (key.trans hlin)
  simpa using this

end LieEquiv.IsCartanInvolution
