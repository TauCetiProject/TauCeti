/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Group

/-!
# The semidirect product of translations and linear isometries

The affine isometry group of a seminormed space is the semidirect product of its additive
translation group and its linear isometry group. The action is the usual evaluation action,
and the multiplication convention is `(v, L) (w, K) = (v + L w, L K)`. The pair `(v, L)`
acts on a point `x` as `v + L x`.

`AffineIsometryEquiv.semidirectProductMulEquiv` extracts the image of zero and the linear
part. Its inverse constructs the corresponding affine isometry. The two factor inclusions
are respectively translations and linear isometries. Over a real inner product space this
is the Euclidean group decomposition into translations and orthogonal transformations.

This uses Mathlib's affine isometry and semidirect product carriers, without introducing a
second rigid-motion group.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3:
  Euclidean isometries and the Euclidean group.
-/

public section

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace AffineIsometryEquiv

/-- The affine isometry group is the semidirect product of translations and linear
isometries. The coordinates of `f` are `(f 0, f.linearIsometryEquiv)`. -/
def semidirectProductMulEquiv :
    (E ≃ᵃⁱ[𝕜] E) ≃*
      Multiplicative E ⋊[LinearIsometryEquiv.multiplicativeAutHom] (E ≃ₗᵢ[𝕜] E) where
  toFun f := ⟨Multiplicative.ofAdd (f 0), f.linearIsometryEquiv⟩
  invFun p := p.right.toAffineIsometryEquiv.trans (constVAdd 𝕜 E p.left.toAdd)
  left_inv f := by
    ext x
    simpa [add_comm] using (f.map_vadd (0 : E) x).symm
  right_inv p := by
    apply SemidirectProduct.ext
    · simp
    · apply LinearIsometryEquiv.ext
      intro x
      have h := (p.right.toAffineIsometryEquiv.trans (constVAdd 𝕜 E p.left.toAdd)).map_vsub x 0
      simpa using h
  map_mul' f g := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      simpa [add_comm] using f.map_vadd (0 : E) (g 0)
    · apply LinearIsometryEquiv.ext
      intro x
      have hf := f.map_vsub (g x) (g 0)
      have hg := g.map_vsub x 0
      have hfg := (f * g).map_vsub x 0
      simp only [vsub_eq_sub, sub_zero, coe_mul, Function.comp_apply] at hf hg hfg
      exact hfg.trans ((congrArg f.linearIsometryEquiv hg).trans hf).symm

/-- The translation coordinate is the image of zero. -/
@[simp]
theorem semidirectProductMulEquiv_left (f : E ≃ᵃⁱ[𝕜] E) :
    (semidirectProductMulEquiv f).left = Multiplicative.ofAdd (f 0) := (rfl)

/-- The linear coordinate is the linear part. -/
@[simp]
theorem semidirectProductMulEquiv_right (f : E ≃ᵃⁱ[𝕜] E) :
    (semidirectProductMulEquiv f).right = f.linearIsometryEquiv := (rfl)

/-- The rigid motion represented by `(v, L)` sends `x` to `v + L x`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_apply
    (p : Multiplicative E ⋊[LinearIsometryEquiv.multiplicativeAutHom] (E ≃ₗᵢ[𝕜] E)) (x : E) :
    semidirectProductMulEquiv.symm p x = p.left.toAdd + p.right x := (rfl)

/-- The first factor is the translation subgroup. -/
@[simp]
theorem semidirectProductMulEquiv_constVAdd (v : E) :
    semidirectProductMulEquiv (constVAdd 𝕜 E v) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  apply SemidirectProduct.ext
  · simp
  · ext x
    simpa using (constVAdd 𝕜 E v).map_vsub x 0

/-- The second factor is the linear isometry subgroup. -/
@[simp]
theorem semidirectProductMulEquiv_toAffineIsometryEquiv (L : E ≃ₗᵢ[𝕜] E) :
    semidirectProductMulEquiv L.toAffineIsometryEquiv = SemidirectProduct.inr L := by
  apply SemidirectProduct.ext <;> simp

end AffineIsometryEquiv
