/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.PointTopology.Group
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Convolution groups over products of coefficient algebras

For a `k`-bialgebra `H` and commutative topological `k`-algebras,
`TauCeti.PointTopology.prodContinuousMulEquiv` and `TauCeti.PointTopology.piContinuousMulEquiv`
show that the algebraic convolution equivalences `AlgHom.prodValueMulEquiv` and
`AlgHom.piValueMulEquiv` are multiplicative homeomorphisms (`≃ₜ*`) for the point topology, with
coordinates given by post-composition with the coefficient projections (and isomorphisms of
topological monoids, or of topological groups when `H` is a Hopf algebra, whenever the coefficient
algebras are topological semirings), and `TauCeti.PointTopology.piProdContinuousMulEquiv` is the
combined identification for `(∀ i, A i) × B`. Together with the isomorphism of topological monoids
of points induced by an isomorphism of topological coefficient algebras
(`ContinuousAlgEquiv.mapValueContinuousMulEquiv`), these transport a decomposition of a coefficient
ring into a product to the points.

This is how the points of an algebraic group over the adele ring `𝔸_K = K_∞ × 𝔸_{K,f}` split into
archimedean and finite components, and those over the finite adeles into the components at a finite
set of places and the components away from it.

## Main declarations

* `TauCeti.PointTopology.prodContinuousMulEquiv`: multiplicative homeomorphism between points with
  values in `R₁ × R₂` and pairs of points (an isomorphism of topological monoids, or topological
  groups when `H` is a Hopf algebra, if `R₁` and `R₂` are topological semirings).
* `TauCeti.PointTopology.piContinuousMulEquiv`: multiplicative homeomorphism between convolution
  points valued in `∀ i, R i` and `∀ i, WithConv (H →ₐ[k] R i)` (an isomorphism of topological
  monoids, or topological groups when `H` is a Hopf algebra, if each `R i` is a topological
  semiring).
* `TauCeti.PointTopology.piProdContinuousMulEquiv`: points with values in `(∀ i, A i) × B` are
  pairs of a family of points and a point, as topological monoids.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, §3, and the map (3.6.2) in the proof of Thm. 3.6.
-/

public section

open Topology WithConv

namespace TauCeti.PointTopology

variable {k H : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]

section BialgebraProd

variable {R₁ R₂ : Type*}
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

variable (k H R₁ R₂) in
/-- Multiplicative homeomorphism identifying points valued in `R₁ × R₂` with pairs of points via
the two projections, and sending `(x, y)` to `h ↦ (x h, y h)`. When `R₁` and `R₂` are topological
semirings, this is an isomorphism of topological monoids (and of topological groups when `H` is a
Hopf algebra). -/
noncomputable def prodContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toMulEquiv := AlgHom.prodValueMulEquiv
  continuous_toFun :=
    ((AlgHom.continuous_mapValue continuous_fst).prodMk
      (AlgHom.continuous_mapValue continuous_snd)).congr fun x ↦
      Prod.ext (AlgHom.prodValueMulEquiv_apply_fst x).symm
        (AlgHom.prodValueMulEquiv_apply_snd x).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (((continuous_eval_ofConv h).comp continuous_fst).prodMk
      ((continuous_eval_ofConv h).comp continuous_snd)).congr fun p ↦ by
        simp only [Function.comp_apply, MulEquiv.invFun_eq_symm,
          AlgHom.prodValueMulEquiv_symm_apply_ofConv]

@[simp]
theorem prodContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] R₁ × R₂)) :
    prodContinuousMulEquiv k H R₁ R₂ x =
      (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x) :=
  Prod.ext (AlgHom.prodValueMulEquiv_apply_fst x) (AlgHom.prodValueMulEquiv_apply_snd x)

/-- The point paired from `(x, y)` takes the value `(x h, y h)` at `h`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    (prodContinuousMulEquiv k H R₁ R₂).symm p h = (p.1 h, p.2 h) :=
  AlgHom.prodValueMulEquiv_symm_apply_ofConv p h

end BialgebraProd

section Pi

variable {ι : Type*} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)]
  [∀ i, TopologicalSpace (R i)]

variable (k H) in
/-- Points with values in a product `∀ i, R i` of coefficient algebras are families of points, as
topological monoids for the convolution product and the point topology: a point is sent to its
images under the projections, and a family of points `x` to the point `h ↦ (x i h)_i`. This is
`AlgHom.piValueMulEquiv` with its continuity in both directions. -/
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

variable (B : Type*) [CommSemiring B] [Algebra k B] [TopologicalSpace B]

variable (k H) in
/-- Points with values in a product `(∀ i, R i) × B` of coefficient algebras are pairs of a family
of points and a point, as topological monoids: `prodContinuousMulEquiv` followed by
`piContinuousMulEquiv` on the first factor. -/
noncomputable def piProdContinuousMulEquiv :
    WithConv (H →ₐ[k] (∀ i, R i) × B) ≃ₜ* (∀ i, WithConv (H →ₐ[k] R i)) × WithConv (H →ₐ[k] B) :=
  (prodContinuousMulEquiv k H _ B).trans
    ((piContinuousMulEquiv k H R).prodCongr (ContinuousMulEquiv.refl _))

theorem piProdContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] (∀ i, R i) × B)) :
    piProdContinuousMulEquiv k H R B x =
      (piContinuousMulEquiv k H R (AlgHom.mapValue (AlgHom.fst k (∀ i, R i) B) x),
        AlgHom.mapValue (AlgHom.snd k (∀ i, R i) B) x) := by
  simp [piProdContinuousMulEquiv, prodContinuousMulEquiv_apply]

@[simp]
theorem piProdContinuousMulEquiv_apply_fst (x : WithConv (H →ₐ[k] (∀ i, R i) × B)) (i : ι)
    (h : H) : ((piProdContinuousMulEquiv k H R B x).1 i).ofConv h = (x.ofConv h).1 i := by
  simp [piProdContinuousMulEquiv_apply]

@[simp]
theorem piProdContinuousMulEquiv_apply_snd (x : WithConv (H →ₐ[k] (∀ i, R i) × B)) (h : H) :
    (piProdContinuousMulEquiv k H R B x).2.ofConv h = (x.ofConv h).2 := by
  simp [piProdContinuousMulEquiv_apply]

/-- The point assembled from a family of points `p.1` and a point `p.2` takes the value
`((p.1 i h)_i, p.2 h)` at `h`. -/
@[simp]
theorem piProdContinuousMulEquiv_symm_apply_apply
    (p : (∀ i, WithConv (H →ₐ[k] R i)) × WithConv (H →ₐ[k] B)) (h : H) :
    ((piProdContinuousMulEquiv k H R B).symm p).ofConv h =
      (fun i ↦ (p.1 i).ofConv h, p.2.ofConv h) := by
  obtain ⟨x, rfl⟩ := (piProdContinuousMulEquiv k H R B).surjective p
  simp

end Pi

end TauCeti.PointTopology
