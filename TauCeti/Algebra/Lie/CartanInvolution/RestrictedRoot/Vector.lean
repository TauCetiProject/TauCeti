/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The vector `H_λ` of a restricted root and the bracket `[E, θE]`

Let `θ` be a Cartan involution of a Lie algebra `𝔤₀` over an ordered field `K` (for instance a real
Lie algebra) and `𝔞` a subspace of its `-1`-eigenspace `𝔭`. The Killing form `B` is positive
definite on `𝔭`, hence nondegenerate on `𝔞`, so `H ↦ B(H, ·)` is a linear equivalence from `𝔞` to
its dual (`LieEquiv.IsCartanInvolution.killingEquivDual`). Its inverse sends a functional `λ` on `𝔞`
to the unique `H_λ ∈ 𝔞` with `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`. For `λ ≠ 0`,
`λ(H_λ) = B(H_λ, H_λ) > 0`.

When `𝔞` is maximal abelian in `𝔭` and `E ∈ 𝔤_λ`, the bracket `[E, θE]` lies in `𝔤_0 ∩ 𝔭 = 𝔞`, and
pairing it with `H ∈ 𝔞` gives `B([E, θE], H) = B(E, [θE, H]) = λ(H) B(E, θE)`, so
`[E, θE] = B(E, θE) H_λ` (Knapp, Ch. VI, Prop. 6.52). With `[H_λ, E] = λ(H_λ) E` and
`[H_λ, θE] = -λ(H_λ) θE`, this is the first step towards the copy of `𝔰𝔩₂(ℝ)` spanned by `E`, `θE`
and `H_λ`.

## Main definitions

* `LieEquiv.IsCartanInvolution.killingEquivDual`: the linear equivalence `𝔞 ≃ Dual 𝔞` induced by
  the Killing form; `H_λ` is `(killingEquivDual hθ h𝔞).symm λ`.

## Main results

* `LieEquiv.IsCartanInvolution.killingForm_killingEquivDual_symm`: `B(H_λ, H) = λ(H)`.
* `LieEquiv.IsCartanInvolution.apply_killingEquivDual_symm_pos`: `λ(H_λ) > 0` for `λ ≠ 0`.
* `LieEquiv.IsCartanInvolution.lie_apply_eq_smul_killingEquivDual_symm`:
  `[E, θE] = B(E, θE) H_λ` for `E ∈ 𝔤_λ`, `𝔞` maximal abelian in `𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.52.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv.IsCartanInvolution

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}

/-- **The Killing form as an equivalence `𝔞 ≃ Dual 𝔞`**: for a Cartan involution `θ` and a
subspace `𝔞` of `𝔭`, the linear equivalence `H ↦ B(H, ·)` from `𝔞` to its dual, where `B` is the
Killing form. Its inverse sends a functional `λ` on `𝔞` to the unique `H_λ ∈ 𝔞` with
`B(H_λ, H) = λ(H)` for all `H ∈ 𝔞`. -/
noncomputable def killingEquivDual (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP) :
    𝔞 ≃ₗ[K] Dual K 𝔞 :=
  have := hθ.finiteDimensional
  ((killingForm K L).restrict 𝔞).toDual (hθ.nondegenerate_killingForm_restrict h𝔞)

variable (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)

/-- `killingEquivDual` sends `X ∈ 𝔞` to `B(X, ·)`. -/
@[simp]
theorem killingEquivDual_apply_apply (X H : 𝔞) :
    hθ.killingEquivDual h𝔞 X H = killingForm K L X H :=
  have := hθ.finiteDimensional
  LinearMap.BilinForm.toDual_def (hθ.nondegenerate_killingForm_restrict h𝔞)

/-- `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`. -/
@[simp]
theorem killingForm_killingEquivDual_symm (μ : Dual K 𝔞) (H : 𝔞) :
    killingForm K L ((hθ.killingEquivDual h𝔞).symm μ) H = μ H := by
  rw [← hθ.killingEquivDual_apply_apply h𝔞, LinearEquiv.apply_symm_apply]

/-- `H_λ` is characterized by `B(H_λ, H) = λ(H)` for `H ∈ 𝔞`. -/
theorem eq_killingEquivDual_symm_iff (μ : Dual K 𝔞) (X : 𝔞) :
    X = (hθ.killingEquivDual h𝔞).symm μ ↔ ∀ H : 𝔞, killingForm K L X H = μ H := by
  simp [LinearEquiv.eq_symm_apply, LinearMap.ext_iff]

/-- `λ(H_λ) = B(H_λ, H_λ) > 0` for `λ ≠ 0`. -/
theorem apply_killingEquivDual_symm_pos {μ : Dual K 𝔞} (hμ : μ ≠ 0) :
    0 < μ ((hθ.killingEquivDual h𝔞).symm μ) := by
  rw [← hθ.killingForm_killingEquivDual_symm h𝔞 μ]
  exact hθ.killingForm_restrict_pos h𝔞 _ ((LinearEquiv.map_ne_zero_iff _).mpr hμ)

/-- **`[E, θE] = B(E, θE) H_λ`** for `E ∈ 𝔤_λ`, when `𝔞` is maximal abelian in `𝔭`
(Knapp, Prop. 6.52). -/
theorem lie_apply_eq_smul_killingEquivDual_symm (h𝔞 : θ.IsMaximalAbelianInP 𝔞)
    {μ : Dual K 𝔞} {E : L} (hE : E ∈ 𝔞.restrictedRootSpace μ) :
    ⁅E, θ E⁆ =
      killingForm K L E (θ E) • ((hθ.killingEquivDual h𝔞.le_cartanP).symm μ : L) := by
  have hθE := apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hE
  have h0 : ⁅E, θ E⁆ ∈ 𝔞.restrictedRootSpace 0 := by
    simpa using Submodule.lie_mem_restrictedRootSpace hE hθE
  have hp : ⁅E, θ E⁆ ∈ θ.cartanP := by
    rw [mem_cartanP, LieEquiv.map_lie, hθ.involutive E, ← lie_skew]
  have hX : ⁅E, θ E⁆ ∈ 𝔞 := by
    rw [← h𝔞.restrictedRootSpace_zero_inf_cartanP]
    exact Submodule.mem_inf.mpr ⟨h0, hp⟩
  have key : (⟨⁅E, θ E⁆, hX⟩ : 𝔞) =
      (hθ.killingEquivDual h𝔞.le_cartanP).symm (killingForm K L E (θ E) • μ) := by
    rw [eq_killingEquivDual_symm_iff]
    intro H
    -- `killingForm K L` is the abbreviation `traceForm K L L`, so the invariance applies.
    have hH := (Submodule.mem_restrictedRootSpace.mp hθE) H
    rw [traceForm_apply_lie_apply, ← lie_skew, hH]
    simp [mul_comm]
  simpa using congrArg Subtype.val (key.trans (map_smul _ _ _))

end LieEquiv.IsCartanInvolution
