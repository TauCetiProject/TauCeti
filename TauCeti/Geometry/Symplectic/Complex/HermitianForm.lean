/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Geometry.Symplectic.Hermitian
public import TauCeti.LinearAlgebra.BilinearForm.Complexification

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The induced Hermitian form on the `(1,0)`- and `(0,1)`-parts

Let `g` be a real bilinear form on `V` preserved by an almost complex structure `J`, and let
`h (x, y) = g_ℂ (conj x, y)` be its sesquilinear complexification
(`LinearMap.BilinForm.sesqComplexification`), the positive Hermitian form on `ℂ ⊗[ℝ] V` when `g`
is a Euclidean metric. This file computes `h` on the decomposition `1 ⊗ v = v^(1,0) + v^(0,1)` of
a real vector into its parts in the `i`- and `-i`-eigenspaces `W` and `W'` of the complexified
complex structure:

* conjugation exchanges the two parts, `conj v^(1,0) = v^(0,1)`;
* `W` and `W'` are `h`-orthogonal, and more generally eigenspaces of the complexified `J` for
  eigenvalues `z`, `w` with `conj z * w ≠ 1` are `h`-orthogonal;
* `h (v^(1,0), w^(1,0)) = (g (v, w) - i g (v, J w)) / 2`, so for symmetric `g`,
  `|v^(1,0)|² = h (v^(1,0), v^(1,0)) = g (v, v) / 2`.

On the complex vector space `(V, J)` the Hermitian form `g (v, w) - i g (v, J w)`, conjugate-linear
in its first argument, is therefore twice the pullback of `h|_W` along `v ↦ v^(1,0)`. For `g` the
metric `ω (·, J ·)` of a `J`-invariant symplectic form `ω`, this form is
`TauCeti.SymplecticForm.complexAssociatedForm`.

In the geometric convention for spinors, `Q (v) = -g (v, v)`, the isotropic subspace `W` carries
the exterior model `⋀ W` of the spinor module of `(V, g, J)`, and the restriction of `h` to `W`
is the Hermitian metric on `W` that induces a Hermitian metric on that model.

## Main results

* `TauCeti.AlmostComplexStructure.tmulConj_holomorphicPart` and
  `TauCeti.AlmostComplexStructure.tmulConj_antiholomorphicPart`: conjugation exchanges the parts.
* `TauCeti.AlmostComplexStructure.sesqComplexification_eq_zero_of_mem_eigenspace`: eigenspaces of
  the complexified `J` are `h`-orthogonal unless `conj z * w = 1`.
* `TauCeti.AlmostComplexStructure.sesqComplexification_eq_zero_of_mem_eigenspace_I_of_mem_neg_I`:
  `W` and `W'` are `h`-orthogonal.
* `TauCeti.AlmostComplexStructure.sesqComplexification_holomorphicPart_holomorphicPart`:
  `h (v^(1,0), w^(1,0)) = (g (v, w) - i g (v, J w)) / 2`.
* `TauCeti.AlmostComplexStructure.sesqComplexification_holomorphicPart_self`:
  `h (v^(1,0), v^(1,0)) = g (v, v) / 2`.
* `TauCeti.SymplecticForm.Invariant.complexAssociatedForm_eq_two_mul_sesqComplexification`: the
  Hermitian form of a `J`-invariant symplectic form is twice the pullback of `h` along
  `v ↦ v^(1,0)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5, for the Hermitian
  metric on the isotropic subspace of a complex structure.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1, for the
  Hermitian form of a compatible pair.
-/

public section

open LinearMap (BilinForm)
open Module.End
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {g : BilinForm ℝ V}

/-! ### `J`-invariant bilinear forms -/

/-- A bilinear form preserved by `J` is antisymmetric under moving `J` across:
`g (J v, w) = -g (v, J w)`. -/
theorem bilinForm_apply_left_eq_neg_apply_right (hgJ : ∀ v w, g (J v) (J w) = g v w) (v w : V) :
    g (J v) w = -g v (J w) := by
  have h := hgJ v (J w)
  rw [apply_apply, map_neg] at h
  linear_combination -h

/-- A symmetric bilinear form preserved by `J` pairs every vector `v` trivially with `J v`. -/
theorem bilinForm_apply_apply_self_eq_zero (hg : g.IsSymm) (hgJ : ∀ v w, g (J v) (J w) = g v w)
    (v : V) : g v (J v) = 0 := by
  have h := J.bilinForm_apply_left_eq_neg_apply_right hgJ v v
  rw [← hg.eq v (J v)] at h
  linarith

/-! ### Conjugation of the `(1,0)`- and `(0,1)`-parts -/

/-- Conjugation of the complexification maps the `(1,0)`-part of a real vector to its
`(0,1)`-part. -/
@[simp]
theorem tmulConj_holomorphicPart (v : V) :
    tmulConj V (J.holomorphicPart v) = J.antiholomorphicPart v := by
  rw [holomorphicPart_apply, antiholomorphicPart_apply, map_smulₛₗ, map_sub, map_smulₛₗ,
    tmulConj_tmul, tmulConj_tmul, map_one, map_inv₀, map_ofNat, Complex.conj_I]
  module

/-- Conjugation of the complexification maps the `(0,1)`-part of a real vector to its
`(1,0)`-part. -/
@[simp]
theorem tmulConj_antiholomorphicPart (v : V) :
    tmulConj V (J.antiholomorphicPart v) = J.holomorphicPart v := by
  rw [← tmulConj_holomorphicPart, tmulConj_tmulConj]

/-! ### Orthogonality of the eigenspaces -/

/-- **Eigenspaces of the complexified complex structure are orthogonal for the induced Hermitian
form** unless their eigenvalues satisfy `conj z * w = 1`: the complexification of `J` preserves
`h`, and scales `h (x, y)` by `conj z * w` on eigenvectors. -/
theorem sesqComplexification_eq_zero_of_mem_eigenspace (hgJ : ∀ v w, g (J v) (J w) = g v w)
    {z w : ℂ} (hzw : starRingEnd ℂ z * w ≠ 1) {x y : ℂ ⊗[ℝ] V}
    (hx : x ∈ eigenspace (J.toLinearMap.baseChange ℂ) z)
    (hy : y ∈ eigenspace (J.toLinearMap.baseChange ℂ) w) :
    g.sesqComplexification x y = 0 := by
  have h := g.sesqComplexification_baseChange_baseChange (f := J.toLinearMap) hgJ x y
  rw [mem_eigenspace_iff.mp hx, mem_eigenspace_iff.mp hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h
  have h' : (starRingEnd ℂ z * w - 1) * g.sesqComplexification x y = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hzw)

/-- **The `i`- and `-i`-eigenspaces of the complexified complex structure are orthogonal for the
induced Hermitian form.** -/
theorem sesqComplexification_eq_zero_of_mem_eigenspace_I_of_mem_neg_I
    (hgJ : ∀ v w, g (J v) (J w) = g v w) {x y : ℂ ⊗[ℝ] V}
    (hx : x ∈ eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
    (hy : y ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) :
    g.sesqComplexification x y = 0 :=
  J.sesqComplexification_eq_zero_of_mem_eigenspace hgJ
    (by rw [Complex.conj_I, neg_mul_neg, Complex.I_mul_I]; norm_num) hx hy

/-- The `(1,0)`-part of one real vector is orthogonal to the `(0,1)`-part of another for the
induced Hermitian form. -/
@[simp]
theorem sesqComplexification_holomorphicPart_antiholomorphicPart
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v w : V) :
    g.sesqComplexification (J.holomorphicPart v) (J.antiholomorphicPart w) = 0 :=
  J.sesqComplexification_eq_zero_of_mem_eigenspace_I_of_mem_neg_I hgJ
    (J.holomorphicPart_mem_eigenspace_baseChange_I v)
    (J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I w)

/-- The `(0,1)`-part of one real vector is orthogonal to the `(1,0)`-part of another for the
induced Hermitian form. -/
@[simp]
theorem sesqComplexification_antiholomorphicPart_holomorphicPart
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v w : V) :
    g.sesqComplexification (J.antiholomorphicPart v) (J.holomorphicPart w) = 0 :=
  J.sesqComplexification_eq_zero_of_mem_eigenspace hgJ
    (by rw [map_neg, Complex.conj_I, neg_neg, Complex.I_mul_I]; norm_num)
    (J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I v)
    (J.holomorphicPart_mem_eigenspace_baseChange_I w)

/-! ### The induced Hermitian form on the parts -/

/-- **The induced Hermitian form on `(1,0)`-parts**:
`h (v^(1,0), w^(1,0)) = (g (v, w) - i g (v, J w)) / 2`. -/
theorem sesqComplexification_holomorphicPart_holomorphicPart
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v w : V) :
    g.sesqComplexification (J.holomorphicPart v) (J.holomorphicPart w) =
      2⁻¹ * ((g v w : ℂ) - Complex.I * (g v (J w) : ℂ)) := by
  simp only [holomorphicPart_apply, map_smulₛₗ, map_sub, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.BilinForm.sesqComplexification_tmul_tmul, smul_eq_mul, map_one,
    map_inv₀,
    map_ofNat, Complex.conj_I, hgJ, J.bilinForm_apply_left_eq_neg_apply_right hgJ v w,
    Complex.ofReal_neg]
  linear_combination (-(2⁻¹ : ℂ) * 2⁻¹ * (g v w : ℂ)) * Complex.I_mul_I

/-- **The induced Hermitian form on `(0,1)`-parts**:
`h (v^(0,1), w^(0,1)) = (g (v, w) + i g (v, J w)) / 2`, the conjugate of its value on the
`(1,0)`-parts. -/
theorem sesqComplexification_antiholomorphicPart_antiholomorphicPart
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v w : V) :
    g.sesqComplexification (J.antiholomorphicPart v) (J.antiholomorphicPart w) =
      2⁻¹ * ((g v w : ℂ) + Complex.I * (g v (J w) : ℂ)) := by
  rw [← tmulConj_holomorphicPart, ← tmulConj_holomorphicPart,
    LinearMap.BilinForm.sesqComplexification_tmulConj_tmulConj,
    J.sesqComplexification_holomorphicPart_holomorphicPart hgJ]
  simp [Complex.conj_I, Complex.conj_ofReal, sub_eq_add_neg, map_ofNat]

/-- **The squared norm of the `(1,0)`-part** of a real vector is half the square of the vector:
`h (v^(1,0), v^(1,0)) = g (v, v) / 2`, that is `|v^(1,0)|² = |v|² / 2` for a Euclidean
metric `g`. -/
theorem sesqComplexification_holomorphicPart_self (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v : V) :
    g.sesqComplexification (J.holomorphicPart v) (J.holomorphicPart v) = 2⁻¹ * (g v v : ℂ) := by
  rw [J.sesqComplexification_holomorphicPart_holomorphicPart hgJ,
    J.bilinForm_apply_apply_self_eq_zero hg hgJ, Complex.ofReal_zero, mul_zero, sub_zero]

/-- **The squared norm of the `(0,1)`-part** of a real vector is half the square of the vector:
`h (v^(0,1), v^(0,1)) = g (v, v) / 2`. -/
theorem sesqComplexification_antiholomorphicPart_self (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) (v : V) :
    g.sesqComplexification (J.antiholomorphicPart v) (J.antiholomorphicPart v) =
      2⁻¹ * (g v v : ℂ) := by
  rw [J.sesqComplexification_antiholomorphicPart_antiholomorphicPart hgJ,
    J.bilinForm_apply_apply_self_eq_zero hg hgJ, Complex.ofReal_zero, mul_zero, add_zero]

end TauCeti.AlmostComplexStructure

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}
  {J : AlmostComplexStructure V}

/-- **The Hermitian form of a `J`-invariant symplectic form is twice the pullback of the induced
Hermitian form along `v ↦ v^(1,0)`**: with `g = ω (·, J ·)` and `h` its sesquilinear
complexification, `ω (v, J w) + i ω (v, w) = 2 h (v^(1,0), w^(1,0))`. -/
theorem Invariant.complexAssociatedForm_eq_two_mul_sesqComplexification (hinv : ω.Invariant J)
    (v w : V) :
    ω.complexAssociatedForm J v w =
      2 * (ω.associatedBilinForm J).sesqComplexification (J.holomorphicPart v)
        (J.holomorphicPart w) := by
  rw [J.sesqComplexification_holomorphicPart_holomorphicPart hinv.associatedBilinForm_invariant,
    complexAssociatedForm_apply, associatedBilinForm_apply_right_apply, associatedBilinForm_apply,
    Complex.ofReal_neg]
  ring

end TauCeti.SymplecticForm
