/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Points with values in a product of coefficient rings

Let `H` be a bialgebra over `k` and `R₁`, `R₂` commutative topological `k`-algebras. An algebra
map `H → R₁ × R₂` is the same as a pair of algebra maps `H → R₁` and `H → R₂` (Mathlib's
`AlgHom.prodEquiv`). This file shows that this identification is an isomorphism of topological
monoids for the convolution product and the point topology:
`WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)`. For a Hopf
algebra `H` it is an isomorphism of topological groups, the statement `G(R₁ × R₂) = G(R₁) × G(R₂)`
for the affine group scheme `G = Spec H`.

The forward map is the pair of coefficient changes along the two projections, so it is
multiplicative because `AlgHom.mapValue` is. Its continuity is that of the projections, and the
inverse is continuous because each value of the paired point is the pair of values.

The same holds for an arbitrary product `∀ i, R i` of coefficient algebras: the identification of
Mathlib's `AlgHom.piValueMulEquiv` is an isomorphism of topological monoids. Together with the
isomorphism of topological monoids of points induced by an isomorphism of topological coefficient
algebras, these transport a decomposition of a coefficient ring into a product to the points.

This is how the points of an algebraic group over the adele ring `𝔸_K = K_∞ × 𝔸_{K,f}` split into
archimedean and finite components, and those over the finite adeles into the components at a finite
set of places and the components away from it.

## Main declarations

* `TauCeti.PointTopology.prodContinuousMulEquiv`: points with values in `R₁ × R₂` are pairs of
  points, as topological monoids.
* `TauCeti.PointTopology.piContinuousMulEquiv`: points with values in `∀ i, R i` are families of
  points, as topological monoids.
* `ContinuousAlgEquiv.mapValueContinuousMulEquiv`: an isomorphism of topological coefficient
  algebras induces an isomorphism of topological monoids of points.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and the map (3.6.2) in the proof of Thm. 3.6, p. 7.
-/

public section

open WithConv

namespace TauCeti.PointTopology

variable {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

variable (k H R₁ R₂) in
/-- Points with values in a product `R₁ × R₂` of coefficient algebras are pairs of points, as
topological monoids for the convolution product and the point topology: a point is sent to its
images under the two projections, and a pair of points `(x, y)` to the point `h ↦ (x h, y h)`.
For a Hopf algebra `H` this is the isomorphism of topological groups `G(R₁ × R₂) ≃ G(R₁) × G(R₂)`.
-/
noncomputable def prodContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toFun x := (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv x := by
    simp only [AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.prod_comp, AlgHom.prod_fst_snd,
      AlgHom.id_comp, toConv_ofConv]
  right_inv p := by
    simp only [AlgHom.mapValue_apply, AlgHom.fst_prod, AlgHom.snd_prod, toConv_ofConv]
  map_mul' x y := by
    simp only [map_mul, Prod.mk_mul_mk]
  continuous_toFun :=
    (AlgHom.continuous_mapValue continuous_fst).prodMk (AlgHom.continuous_mapValue continuous_snd)
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    ((continuous_eval_ofConv h).comp continuous_fst).prodMk
      ((continuous_eval_ofConv h).comp continuous_snd)

@[simp]
theorem prodContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] R₁ × R₂)) :
    prodContinuousMulEquiv k H R₁ R₂ x =
      (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x) :=
  (rfl)

/-- The point paired from `(x, y)` takes the value `(x h, y h)` at `h`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    (prodContinuousMulEquiv k H R₁ R₂).symm p h = (p.1 h, p.2 h) :=
  (rfl)

section Pi

variable {ι : Type*} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)]
  [∀ i, TopologicalSpace (R i)]

variable (k H) in
/-- Points with values in a product `∀ i, R i` of coefficient algebras are families of points, as
topological monoids for the convolution product and the point topology: a point is sent to its
images under the projections, and a family of points `x` to the point `h ↦ (x i h)_i`. This is
Mathlib's `AlgHom.piValueMulEquiv` with its continuity in both directions. -/
noncomputable def piContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := AlgHom.piValueMulEquiv
  continuous_toFun := continuous_pi fun i ↦ continuous_withConv_iff.2 fun h ↦ by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, MulEquiv.coe_toEquiv,
      AlgHom.piValueMulEquiv_apply]
    exact (continuous_apply i).comp (continuous_eval_ofConv h)
  continuous_invFun := continuous_withConv_iff.2 fun h ↦ continuous_pi fun i ↦ by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm,
      AlgHom.piValueMulEquiv_symm_apply]
    exact (continuous_eval_ofConv h).comp (continuous_apply i)

@[simp]
theorem piContinuousMulEquiv_apply_apply (x : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) (h : H) :
    (piContinuousMulEquiv k H R x i).ofConv h = x.ofConv h i :=
  AlgHom.piValueMulEquiv_apply x i h

@[simp]
theorem piContinuousMulEquiv_symm_apply_apply (x : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piContinuousMulEquiv k H R).symm x).ofConv h i = (x i).ofConv h :=
  AlgHom.piValueMulEquiv_symm_apply x h i

end Pi

end TauCeti.PointTopology

section Equiv

variable {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

/-- An isomorphism `e : R₁ ≃A[k] R₂` of topological coefficient algebras induces, by
post-composition, an isomorphism of topological monoids of points
`WithConv (H →ₐ[k] R₁) ≃ₜ* WithConv (H →ₐ[k] R₂)`; it is Mathlib's `AlgEquiv.mapValueMulEquiv`
with its continuity in both directions. -/
noncomputable def ContinuousAlgEquiv.mapValueContinuousMulEquiv (e : R₁ ≃A[k] R₂) :
    WithConv (H →ₐ[k] R₁) ≃ₜ* WithConv (H →ₐ[k] R₂) where
  toMulEquiv := e.toAlgEquiv.mapValueMulEquiv
  continuous_toFun := by
    change Continuous fun x ↦ e.toAlgEquiv.mapValueMulEquiv x
    simp only [AlgEquiv.mapValueMulEquiv_apply]
    exact AlgHom.continuous_mapValue (H₁ := H) e.continuous
  continuous_invFun := by
    change Continuous fun x ↦ e.toAlgEquiv.mapValueMulEquiv.symm x
    simp only [AlgEquiv.mapValueMulEquiv_symm_apply]
    exact AlgHom.continuous_mapValue (H₁ := H) e.symm.continuous

@[simp]
theorem ContinuousAlgEquiv.mapValueContinuousMulEquiv_apply_apply (e : R₁ ≃A[k] R₂)
    (x : WithConv (H →ₐ[k] R₁)) (h : H) :
    (e.mapValueContinuousMulEquiv x).ofConv h = e (x.ofConv h) := by
  change (e.toAlgEquiv.mapValueMulEquiv x).ofConv h = _
  simp only [AlgEquiv.mapValueMulEquiv_apply, AlgHom.mapValue_apply, ofConv_toConv,
    AlgHom.comp_apply]
  rfl

@[simp]
theorem ContinuousAlgEquiv.mapValueContinuousMulEquiv_symm_apply_apply (e : R₁ ≃A[k] R₂)
    (x : WithConv (H →ₐ[k] R₂)) (h : H) :
    (e.mapValueContinuousMulEquiv.symm x).ofConv h = e.symm (x.ofConv h) := by
  change (e.toAlgEquiv.mapValueMulEquiv.symm x).ofConv h = _
  simp only [AlgEquiv.mapValueMulEquiv_symm_apply, AlgHom.mapValue_apply, ofConv_toConv,
    AlgHom.comp_apply]
  rfl

end Equiv
