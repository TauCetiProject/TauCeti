/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.Algebra.Lie.Orthogonal.Killing
import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint

/-!
# Cartan involutions of matrix Lie algebras

Let `𝕜` be `ℝ` or `ℂ` and let `𝔤₀` be a real Lie subalgebra of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose. Then `θ X = -Xᴴ` is an involutive automorphism of `𝔤₀`, and it is a Cartan involution
exactly when the centre of `𝔤₀` is trivial; in particular it is a Cartan involution when `𝔤₀` is
semisimple (Knapp, Prop. 6.28).

The proof uses the real inner product `⟪X, Y⟫ = Re tr(X Yᴴ)` on matrices: for `X ∈ 𝔤₀` the adjoint
of `ad X` for this inner product is `ad Xᴴ`, so
`-B(X, θ X) = tr(ad X ∘ ad Xᴴ) = tr(ad X ∘ (ad X)*)`, which is nonnegative and vanishes only when
`ad X = 0`, that is, when `X` is central.

The indefinite orthogonal Lie algebras `𝔰𝔬(p, q)` are closed under transpose, so `θ X = -Xᵀ` is a
Cartan involution of `𝔰𝔬(p, q)` for `p + q ≥ 3`; on the real symplectic Lie algebra the
construction is Tau Ceti's `LieAlgebra.Symplectic.cartanInvolution`.

## Main definitions

* `TauCeti.negConjTransposeLieEquiv`: `X ↦ -Xᴴ` as an automorphism of the real Lie algebra
  `𝔤𝔩_n(𝕜)`.
* `TauCeti.reTraceForm`: the real inner product `(X, Y) ↦ Re tr(X Yᴴ)` on matrices.
* `TauCeti.restrictNegConjTranspose`: the restriction of `X ↦ -Xᴴ` to a real Lie subalgebra
  closed under conjugate transpose.

## Main results

* `TauCeti.reTraceForm_lie_apply`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`.
* `TauCeti.isCartanInvolution_restrictNegConjTranspose_iff`: `X ↦ -Xᴴ` is a Cartan involution of
  a real Lie subalgebra closed under conjugate transpose exactly when its centre is trivial.
* `TauCeti.isCartanInvolution_restrictNegConjTranspose`: it is a Cartan involution of a real
  Lie subalgebra with trivial radical (for instance a semisimple one) closed under conjugate
  transpose.
* `LieAlgebra.Orthogonal.isCartanInvolution_restrictNegConjTranspose_so'`: `X ↦ -Xᵀ` is a
  Cartan involution of `𝔰𝔬(p, q)` for `p + q ≥ 3`.
* `LieAlgebra.Symplectic.restrictNegConjTranspose_sp`: on `𝔰𝔭(2n, ℝ)` the construction is
  `LieAlgebra.Symplectic.cartanInvolution`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section GeneralLinear

variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Negative conjugate transpose `X ↦ -Xᴴ` as an automorphism of `𝔤𝔩_n(𝕜)` viewed as a real Lie
algebra. -/
def negConjTransposeLieEquiv : Matrix n n 𝕜 ≃ₗ⁅ℝ⁆ Matrix n n 𝕜 where
  toFun X := -Xᴴ
  invFun X := -Xᴴ
  map_add' X Y := by rw [conjTranspose_add, neg_add]
  map_smul' r X := by simp [conjTranspose_smul]
  map_lie' {X Y} := by
    simp only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, mul_neg, neg_mul, neg_neg,
      neg_sub]
  left_inv X := by simp
  right_inv X := by simp

variable {𝕜 n} in
/-- The matrix value of negative conjugate transpose. -/
@[simp]
theorem negConjTransposeLieEquiv_apply (X : Matrix n n 𝕜) :
    negConjTransposeLieEquiv 𝕜 n X = -Xᴴ :=
  (rfl)

/-- Negative conjugate transpose is its own inverse. -/
@[simp]
theorem negConjTransposeLieEquiv_symm :
    (negConjTransposeLieEquiv 𝕜 n).symm = negConjTransposeLieEquiv 𝕜 n :=
  (rfl)

/-- The real inner product `(X, Y) ↦ Re tr(X Yᴴ)` on `n × n` matrices over `𝕜`. -/
noncomputable def reTraceForm : LinearMap.BilinForm ℝ (Matrix n n 𝕜) :=
  LinearMap.mk₂ ℝ (fun X Y ↦ RCLike.re (X * Yᴴ).trace)
    (fun X X' Y ↦ by rw [add_mul, trace_add, map_add])
    (fun r X Y ↦ by rw [smul_mul_assoc, trace_smul, RCLike.smul_re, smul_eq_mul])
    (fun X Y Y' ↦ by rw [conjTranspose_add, mul_add, trace_add, map_add])
    (fun r X Y ↦ by
      rw [conjTranspose_smul, star_trivial, mul_smul_comm, trace_smul, RCLike.smul_re,
        smul_eq_mul])

variable {𝕜 n}

/-- The value of `reTraceForm`. -/
@[simp]
theorem reTraceForm_apply (X Y : Matrix n n 𝕜) :
    reTraceForm 𝕜 n X Y = RCLike.re (X * Yᴴ).trace :=
  (rfl)

variable (𝕜 n) in
/-- `Re tr(X Yᴴ)` is symmetric in `X` and `Y`. -/
theorem isSymm_reTraceForm : (reTraceForm 𝕜 n).IsSymm := by
  refine ⟨fun X Y ↦ ?_⟩
  rw [reTraceForm_apply, reTraceForm_apply, ← RCLike.conj_re, starRingEnd_apply,
    ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

open scoped ComplexOrder in
variable (𝕜 n) in
/-- `Re tr(X Xᴴ)` is positive for `X ≠ 0`. -/
theorem posDef_reTraceForm : (reTraceForm 𝕜 n).toQuadraticMap.PosDef := by
  intro X hX
  rw [LinearMap.BilinMap.toQuadraticMap_apply, reTraceForm_apply]
  have hpos : 0 < (X * Xᴴ).trace :=
    (posSemidef_self_mul_conjTranspose X).trace_nonneg.lt_of_ne'
      (trace_mul_conjTranspose_self_eq_zero_iff.not.mpr hX)
  exact (RCLike.pos_iff.mp hpos).1

/-- The adjoint of `ad X` for `Re tr(X Yᴴ)` is `ad Xᴴ`: `⟪[X, Y], Z⟫ = ⟪Y, [Xᴴ, Z]⟫`. -/
theorem reTraceForm_lie_apply (X Y Z : Matrix n n 𝕜) :
    reTraceForm 𝕜 n ⁅X, Y⁆ Z = reTraceForm 𝕜 n Y ⁅Xᴴ, Z⁆ := by
  simp only [reTraceForm_apply, Ring.lie_def, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, sub_mul, mul_sub, trace_sub, Matrix.mul_assoc]
  rw [trace_mul_comm X, Matrix.mul_assoc]

end GeneralLinear

section Subalgebra

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (L : LieSubalgebra ℝ (Matrix n n 𝕜)) (hL : ∀ X ∈ L, Xᴴ ∈ L)

/-- Negative conjugate transpose `X ↦ -Xᴴ` restricted to a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)`
closed under conjugate transpose. -/
def restrictNegConjTranspose : L ≃ₗ⁅ℝ⁆ L :=
  (negConjTransposeLieEquiv 𝕜 n).ofSubalgebras L L
    (LieSubalgebra.map_eq_self_of_involutive _ (fun X ↦ by simp) fun X hX ↦ by
      simpa using L.neg_mem (hL X hX))

/-- The matrix value of `restrictNegConjTranspose` is negative conjugate transpose. -/
@[simp]
theorem coe_restrictNegConjTranspose_apply (X : L) :
    (restrictNegConjTranspose L hL X : Matrix n n 𝕜) = -(X : Matrix n n 𝕜)ᴴ := by
  simp [restrictNegConjTranspose]

/-- `X ↦ -Xᴴ` is an involution. -/
theorem involutive_restrictNegConjTranspose :
    Function.Involutive (restrictNegConjTranspose L hL) :=
  fun X ↦ Subtype.ext (by simp)

/-- Applying `X ↦ -Xᴴ` twice gives back `X`. -/
@[simp]
theorem restrictNegConjTranspose_restrictNegConjTranspose (X : L) :
    restrictNegConjTranspose L hL (restrictNegConjTranspose L hL X) = X :=
  involutive_restrictNegConjTranspose L hL X

/-- The inverse of `X ↦ -Xᴴ` is itself. -/
@[simp]
theorem symm_restrictNegConjTranspose :
    (restrictNegConjTranspose L hL).symm = restrictNegConjTranspose L hL :=
  LieEquiv.ext fun X ↦ (restrictNegConjTranspose L hL).symm_apply_eq.mpr
    (involutive_restrictNegConjTranspose L hL X).symm

/-- For a real Lie subalgebra `L` closed under conjugate transpose, `B(X, -Xᴴ) < 0` for every
noncentral `X` in `L`. -/
private theorem killingForm_restrictNegConjTranspose_neg (x : L) (hx : x ∉ center ℝ L) :
    killingForm ℝ L x (restrictNegConjTranspose L hL x) < 0 := by
  let x' : L := ⟨(x : Matrix n n 𝕜)ᴴ, hL _ x.property⟩
  have hθ : restrictNegConjTranspose L hL x = -x' := Subtype.ext (by simp [x'])
  let P : LinearMap.BilinForm ℝ L :=
    (reTraceForm 𝕜 n).compl₁₂ L.toSubmodule.subtype L.toSubmodule.subtype
  have hP (y z : L) : P y z = reTraceForm 𝕜 n y z := rfl
  have hsymm : P.IsSymm := ⟨fun y z ↦ by simp only [hP]; exact (isSymm_reTraceForm 𝕜 n).eq y z⟩
  have hpos : P.toQuadraticMap.PosDef := fun y hy ↦ by
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply, hP] using
      posDef_reTraceForm 𝕜 n (y : Matrix n n 𝕜) (by simpa using hy)
  have hadj : LinearMap.IsAdjointPair P P (ad ℝ L x) (ad ℝ L x') := fun y z ↦ by
    simp only [ad_apply, hP, LieSubalgebra.coe_bracket]
    exact reTraceForm_lie_apply _ _ _
  have hne : ad ℝ L x ≠ 0 := by
    rwa [Ne, ← LieHom.mem_ker, ad_ker_eq_self_module_ker, self_module_ker_eq_center]
  rw [hθ, map_neg, killingForm_apply_apply, ← Module.End.mul_eq_comp, neg_lt_zero]
  exact (LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair P hsymm hpos hadj).lt_of_ne'
    ((LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair P hsymm hpos hadj).not.mpr hne)

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` closed under conjugate
transpose, `X ↦ -Xᴴ` is a Cartan involution of `L` exactly when the centre of `L` is trivial. -/
theorem isCartanInvolution_restrictNegConjTranspose_iff :
    (restrictNegConjTranspose L hL).IsCartanInvolution ↔ center ℝ L = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ LieEquiv.isCartanInvolution_iff.mpr
    ⟨involutive_restrictNegConjTranspose L hL, fun x hx ↦
      killingForm_restrictNegConjTranspose_neg L hL x (by rwa [h, LieSubmodule.mem_bot])⟩⟩
  have := h.isSemisimple
  exact center_eq_bot ℝ L

/-- **Knapp, Prop. 6.28.** For a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)` with trivial radical (for
instance a semisimple one) closed under conjugate transpose, `X ↦ -Xᴴ` is a Cartan involution. -/
theorem isCartanInvolution_restrictNegConjTranspose [HasTrivialRadical ℝ L] :
    (restrictNegConjTranspose L hL).IsCartanInvolution :=
  (isCartanInvolution_restrictNegConjTranspose_iff L hL).mpr (center_eq_bot ℝ L)

end Subalgebra

end TauCeti

namespace LieAlgebra.Orthogonal

open TauCeti

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The real indefinite orthogonal Lie algebra `𝔰𝔬(p, q)` is closed under conjugate transpose,
which over `ℝ` is the transpose. -/
theorem conjTranspose_mem_so' {X : Matrix (p ⊕ q) (p ⊕ q) ℝ} (hX : X ∈ so' p q ℝ) :
    Xᴴ ∈ so' p q ℝ := by
  rw [conjTranspose_eq_transpose_of_trivial]
  exact transpose_mem_so' hX

/-- **`X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔬(p, q)`** for `p + q ≥ 3`. -/
theorem isCartanInvolution_restrictNegConjTranspose_so'
    (hpq : 3 ≤ Fintype.card p + Fintype.card q) :
    (restrictNegConjTranspose (so' p q ℝ) fun _ ↦ conjTranspose_mem_so').IsCartanInvolution :=
  have := hasTrivialRadical_so' ℝ hpq
  isCartanInvolution_restrictNegConjTranspose _ _

end LieAlgebra.Orthogonal

namespace LieAlgebra.Symplectic

open TauCeti

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- On the real symplectic Lie algebra, `X ↦ -Xᴴ` is `LieAlgebra.Symplectic.cartanInvolution`. -/
theorem restrictNegConjTranspose_sp :
    restrictNegConjTranspose (sp l ℝ) (fun _ ↦ conjTranspose_mem_sp) =
      cartanInvolution l ℝ :=
  LieEquiv.ext fun X ↦ Subtype.ext <| by
    rw [coe_restrictNegConjTranspose_apply, coe_cartanInvolution,
      conjTranspose_eq_transpose_of_trivial]

end LieAlgebra.Symplectic
