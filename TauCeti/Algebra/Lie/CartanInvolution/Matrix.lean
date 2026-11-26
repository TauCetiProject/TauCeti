/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Matrix.NegConjTranspose
public import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint

/-!
# Cartan involutions of matrix Lie algebras

Let `𝕜` be `ℝ` or `ℂ` and let `𝔤₀` be a real Lie subalgebra of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose. Then `θ X = -Xᴴ` is an involutive automorphism of `𝔤₀`, and it is a Cartan involution
exactly when the centre of `𝔤₀` is trivial; in particular it is a Cartan involution when `𝔤₀` is
semisimple (Knapp, Prop. 6.28).

The proof uses the real inner product `⟪X, Y⟫ = Re tr(X Yᴴ)` on matrices (`TauCeti.reTraceForm`):
for `X ∈ 𝔤₀` the adjoint of `ad X` for this inner product is `ad Xᴴ`, so
`-B(X, θ Y) = tr(ad X ∘ ad Yᴴ)` and `-B(X, θ X) = tr(ad X ∘ (ad X)*)`, which is nonnegative and
vanishes only when `ad X = 0`, that is, when `X` is central.

The applications to `𝔰𝔬(p, q)`, `𝔰𝔲(p, q)` and `𝔰𝔭(2n, ℝ)` are in
`TauCeti.Algebra.Lie.Orthogonal.Cartan`, `TauCeti.Algebra.Lie.IndefiniteUnitary.Cartan` and
`TauCeti.Algebra.Lie.Symplectic.Cartan`.

## Main results

* `TauCeti.reTraceForm_lie_apply`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`.
* `LieSubalgebra.reTraceForm`: the restriction of `⟪X, Y⟫` to a real Lie subalgebra, a
  positive-definite symmetric form (`LieSubalgebra.posDef_reTraceForm`) for which `ad X` has
  adjoint `ad Xᴴ` (`LieSubalgebra.isAdjointPair_reTraceForm_ad`).
* `LieSubalgebra.mem_fixedSubalgebra_restrictNegConjTranspose_iff`,
  `LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff`: for `θ X = -Xᴴ`, `𝔨` is the
  skew-Hermitian and `𝔭` the Hermitian elements of `𝔤₀`.
* `LieSubalgebra.killingForm_restrictNegConjTranspose`: `B(X, θ Y) = -tr(ad X ∘ ad Yᴴ)`.
* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_iff`: `X ↦ -Xᴴ` is a Cartan
  involution of a real Lie subalgebra closed under conjugate transpose exactly when its centre is
  trivial.
* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose`: it is a Cartan involution of a real
  Lie subalgebra with trivial radical (for instance a semisimple one) closed under conjugate
  transpose.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The adjoint of `ad X` for `Re tr(X Yᴴ)` is `ad Xᴴ`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`. -/
theorem reTraceForm_lie_apply (X Y Z : Matrix n n 𝕜) :
    reTraceForm 𝕜 n n ⁅X, Y⁆ Z = reTraceForm 𝕜 n n Y ⁅Xᴴ, Z⁆ := by
  simp only [reTraceForm_eq_frobenius_real_inner, frobenius_real_inner_eq_re_inner (𝕜 := 𝕜),
    frobenius_inner_lie_left]

end TauCeti

namespace LieSubalgebra

open TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (L : LieSubalgebra ℝ (Matrix n n 𝕜)) (hL : ∀ X ∈ L, Xᴴ ∈ L)

/-- The real inner product `⟪X, Y⟫ = Re tr(X Yᴴ)` (`TauCeti.reTraceForm`) restricted to a real
Lie subalgebra `L` of `𝔤𝔩_n(𝕜)`. -/
noncomputable def reTraceForm : LinearMap.BilinForm ℝ L :=
  (TauCeti.reTraceForm 𝕜 n n).compl₁₂ L.incl.toLinearMap L.incl.toLinearMap

@[simp]
theorem reTraceForm_apply (x y : L) :
    L.reTraceForm x y = TauCeti.reTraceForm 𝕜 n n (x : Matrix n n 𝕜) y := by
  simp [reTraceForm]

/-- `Re tr(X Yᴴ)` is symmetric on a real Lie subalgebra of `𝔤𝔩_n(𝕜)`. -/
theorem isSymm_reTraceForm : L.reTraceForm.IsSymm :=
  ⟨fun y z ↦ by
    rw [reTraceForm_apply, reTraceForm_apply]
    exact (TauCeti.isSymm_reTraceForm 𝕜 n n).eq y z⟩

/-- `Re tr(X Yᴴ)` is positive definite on a real Lie subalgebra of `𝔤𝔩_n(𝕜)`. -/
theorem posDef_reTraceForm : L.reTraceForm.toQuadraticMap.PosDef := fun y hy ↦ by
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply, reTraceForm_apply] using
    TauCeti.posDef_reTraceForm 𝕜 n n (y : Matrix n n 𝕜) (by simpa using hy)

/-- For `x` in `L` with `xᴴ` in `L`, the adjoint of `ad x` for `Re tr(X Yᴴ)` on `L` is `ad xᴴ`. -/
theorem isAdjointPair_reTraceForm_ad (x : L) (hx : (x : Matrix n n 𝕜)ᴴ ∈ L) :
    LinearMap.IsAdjointPair L.reTraceForm L.reTraceForm (ad ℝ L x) (ad ℝ L ⟨_, hx⟩) :=
  fun y z ↦ by
    simp only [ad_apply, reTraceForm_apply, LieSubalgebra.coe_bracket]
    exact reTraceForm_lie_apply _ _ _

/-- The fixed subalgebra `𝔨` of `θ X = -Xᴴ` consists of the skew-Hermitian elements. -/
theorem mem_fixedSubalgebra_restrictNegConjTranspose_iff {X : L} :
    X ∈ (L.restrictNegConjTranspose hL).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n 𝕜)ᴴ = -(X : Matrix n n 𝕜) := by
  simp [LieHom.mem_fixedSubalgebra, Subtype.ext_iff, neg_eq_iff_eq_neg]

/-- The `-1`-eigenspace `𝔭` of `θ X = -Xᴴ` consists of the Hermitian elements. -/
theorem mem_cartanP_restrictNegConjTranspose_iff {X : L} :
    X ∈ (L.restrictNegConjTranspose hL).cartanP ↔ (X : Matrix n n 𝕜)ᴴ = (X : Matrix n n 𝕜) := by
  simp [LieEquiv.mem_cartanP, Subtype.ext_iff]

/-- The Killing form twisted by `θ X = -Xᴴ` is minus the trace pairing of `ad X` and `ad Yᴴ`:
`B(X, θ Y) = -tr(ad X ∘ ad Yᴴ)`. -/
theorem killingForm_restrictNegConjTranspose (x y : L) :
    killingForm ℝ L x (L.restrictNegConjTranspose hL y) =
      -LinearMap.trace ℝ L (ad ℝ L x * ad ℝ L ⟨(y : Matrix n n 𝕜)ᴴ, hL _ y.property⟩) := by
  have hθ : L.restrictNegConjTranspose hL y = -⟨(y : Matrix n n 𝕜)ᴴ, hL _ y.property⟩ :=
    Subtype.ext (by simp)
  rw [hθ, map_neg, killingForm_apply_apply, ← Module.End.mul_eq_comp]

/-- For a real Lie subalgebra `L` closed under conjugate transpose, `B(X, -Xᴴ) < 0` for every
noncentral `X` in `L`. -/
private theorem killingForm_restrictNegConjTranspose_neg (x : L) (hx : x ∉ center ℝ L) :
    killingForm ℝ L x (L.restrictNegConjTranspose hL x) < 0 := by
  have hne : ad ℝ L x ≠ 0 := fun h ↦ hx (TauCeti.LieAlgebra.ad_eq_zero_iff.mp h)
  rw [killingForm_restrictNegConjTranspose, neg_lt_zero]
  have hadj := L.isAdjointPair_reTraceForm_ad x (hL _ x.property)
  exact (LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair _ L.isSymm_reTraceForm
    L.posDef_reTraceForm hadj).lt_of_ne'
    ((LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair _ L.isSymm_reTraceForm
      L.posDef_reTraceForm hadj).not.mpr hne)

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose, `X ↦ -Xᴴ` is a Cartan involution of `L` exactly when the centre of `L` is trivial. -/
theorem isCartanInvolution_restrictNegConjTranspose_iff :
    (L.restrictNegConjTranspose hL).IsCartanInvolution ↔ center ℝ L = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ LieEquiv.isCartanInvolution_iff.mpr
    ⟨L.restrictNegConjTranspose_involutive hL, fun x hx ↦
      killingForm_restrictNegConjTranspose_neg L hL x (by rwa [h, LieSubmodule.mem_bot])⟩⟩
  have := h.isSemisimple
  exact center_eq_bot ℝ L

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` with trivial radical (for
instance a semisimple one) closed under conjugate transpose, `X ↦ -Xᴴ` is a Cartan involution. -/
theorem isCartanInvolution_restrictNegConjTranspose [HasTrivialRadical ℝ L] :
    (L.restrictNegConjTranspose hL).IsCartanInvolution :=
  (L.isCartanInvolution_restrictNegConjTranspose_iff hL).mpr (center_eq_bot ℝ L)

end LieSubalgebra
