/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
public import TauCeti.Analysis.InnerProductSpace.KulkarniNomizu
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.LinearAlgebra.Multilinear.Basis
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Data.Fin.VecNotation

/-!
# Algebraic curvature tensors

A *four-tensor* on a real normed space `V` is a continuous real four-linear form on `V`,
`FourTensor V`. We write its value on `(u, v, z, w)` as `r ![u, v, z, w]`. With the convention
`r(u, v, z, w) = g(R(u, v)w, z)` for the curvature `R` of a Riemannian metric `g`, the curvature
four-tensor is antisymmetric in its first and in its last pair of arguments, symmetric under
interchanging the two pairs, and satisfies the first Bianchi identity
`r(u, v, z, w) + r(v, z, u, w) + r(z, u, v, w) = 0`. A four-tensor with these four symmetries is
an *algebraic curvature tensor*, `TauCeti.FourTensor.IsAlgebraicCurvature`, and these tensors form
the closed submodule `TauCeti.FourTensor.algebraicCurvatureSubmodule`. It is stable under pullback
by every continuous linear map, in particular under the orthogonal group of `V`, and pullback along
a continuous linear equivalence also reflects the curvature symmetries. With this sign
convention `r(u, v, u, v)` is positive on the round sphere.

On a finite-dimensional real inner product space the *Ricci contraction*
`Ric(u, v) = ∑ᵢ r(eᵢ, u, eᵢ, v)` and the *scalar contraction* `Scal = ∑ᵢ Ric(eᵢ, eᵢ)` do not depend
on the orthonormal basis `(eᵢ)`; they are defined through the metric trace
`LinearMap.BilinMap.metricTrace`. This matches `Ric(u, v) = tr(w ↦ R(w, u)v)`.

The Kulkarni–Nomizu product `LinearMap.BilinForm.kulkarniNomizu` of two bilinear forms becomes a
four-tensor `TauCeti.FourTensor.kulkarniNomizu` after reordering it to the convention above:
`(h ⊙ k)(u, v, z, w) = h(u, z) k(v, w) + h(v, w) k(u, z) - h(u, w) k(v, z) - h(v, z) k(u, w)`.
For symmetric factors it is an algebraic curvature tensor, and its Ricci contraction against the
inner product is computed from `LinearMap.BilinForm.sum_kulkarniNomizu_innerₗ`. Half the product
of the inner product with itself is the constant-curvature tensor
`TauCeti.FourTensor.constantCurvature`,
`r(u, v, z, w) = ⟪u, z⟫ ⟪v, w⟫ - ⟪u, w⟫ ⟪v, z⟫`, the curvature four-tensor of the unit sphere.
It is positive on `(u, v, u, v)`, where it is the Gram determinant, exactly for linearly
independent `u, v`, and it is invariant under linear isometries.
Its Ricci contraction is `(n - 1) g`, its scalar contraction is `n (n - 1)`, and `κ` times it is
the four-tensor of every curvature operator satisfying `R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)`, the
identity recorded by `Bundle.RiemannianMetric.IsConstantCurvatureTensor`.

A four-tensor `r` acts on bilinear forms by contracting its first and third slots,
`TauCeti.FourTensor.curvatureAction`: `r(h)(u, v) = ∑_pq h(eₚ, e_q) r(eₚ, u, e_q, v)` in any
orthonormal basis, with `r(g) = Ric(r)`. Contracting an algebraic curvature tensor against a
Kulkarni–Nomizu product `h ⊙ g` with the inner product in an orthonormal basis evaluates `r`, its
Ricci contraction and `r(h)` at arguments moved by `h♯ = bilinFormToEnd h`
(`TauCeti.FourTensor.sum_mul_kulkarniNomizu_innerₗ_last`,
`TauCeti.FourTensor.sum_mul_kulkarniNomizu_innerₗ_second_fourth`), and
`(h ⊙ g)(k) = tr(h♯ k♯) g + (tr k) h - ⟪h♯ k♯ ·, ·⟫ - ⟪k♯ h♯ ·, ·⟫` for symmetric `h` and `k`.

Given a family `b : ι → V` in a real inner product space, the rank-one coordinate four-tensors
`TauCeti.FourTensor.coordFourTensor b i j k l` evaluate `(u, v, z, w)` to
`⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫`, have operator norm `‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖`, pull
back naturally along linear isometries, and expand every four-tensor from its components in a
finite orthonormal basis (`TauCeti.FourTensor.sum_coordFourTensor_eq`). To any pair of vectors
`u, v : V`, `TauCeti.FourTensor.planeCurvature u v` attaches the rank-one algebraic curvature tensor
`(a, b, c, d) ↦ (⟪u, a⟫ ⟪v, b⟫ - ⟪u, b⟫ ⟪v, a⟫) (⟪u, c⟫ ⟪v, d⟫ - ⟪u, d⟫ ⟪v, c⟫)`, which represents
the curvature four-tensor of `S² × ℝⁿ⁻²` when `u, v` are orthonormal.

## Main definitions

* `TauCeti.FourTensor V`: continuous real four-linear forms on `V`.
* `TauCeti.FourTensor.IsAlgebraicCurvature`: the pair antisymmetries, pair interchange and the
  first Bianchi identity.
* `TauCeti.FourTensor.algebraicCurvatureSubmodule`: the submodule of algebraic curvature tensors.
* `TauCeti.FourTensor.ofLinearMap₄`, `TauCeti.FourTensor.toLinearMap₄`, and
  `TauCeti.FourTensor.toLinearMap₄Equiv`: currying four-tensors into four-fold linear forms and the
  finite-dimensional linear equivalence between them.
* `TauCeti.FourTensor.algebraicCurvatureLinearIsometryEquiv`: pullback of algebraic curvature
  tensors along linear isometric equivalences.
* `TauCeti.FourTensor.algebraicCurvaturePullback`: pullback of algebraic curvature tensors along a
  continuous linear map, as a continuous linear map.
* `TauCeti.FourTensor.ricci` and `TauCeti.FourTensor.scalar`: the Ricci and scalar contractions.
* `TauCeti.FourTensor.ricciSlice`: the bilinear form `(x, y) ↦ r(x, u, y, v)` whose metric trace
  is the Ricci contraction.
* `TauCeti.FourTensor.kulkarniNomizu`: the Kulkarni–Nomizu product of two bilinear forms, as a
  four-tensor.
* `TauCeti.FourTensor.constantCurvature`: the constant-curvature tensor of curvature `1`.
* `TauCeti.FourTensor.curvatureAction`: the action of a four-tensor on bilinear forms.
* `TauCeti.FourTensor.coordFourTensor`: the rank-one coordinate four-tensor
  `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫`.
* `TauCeti.FourTensor.planeCurvature`: the rank-one algebraic curvature four-tensor of a pair of
  vectors `u, v`.

## Main statements

* `TauCeti.FourTensor.abs_apply_le_norm_of_norm_eq_one`: evaluation on unit vectors is bounded
  by the operator norm.
* `TauCeti.FourTensor.IsAlgebraicCurvature.cyclic_last_eq_zero`: the first Bianchi identity in
  the last three arguments.
* `TauCeti.FourTensor.isClosed_algebraicCurvatureSubmodule`: the submodule is closed.
* `TauCeti.FourTensor.IsAlgebraicCurvature.compContinuousLinearMap`: pullback preserves algebraic
  curvature tensors.
* `TauCeti.FourTensor.isAlgebraicCurvature_compContinuousLinearMap_iff`,
  `TauCeti.FourTensor.comap_compContinuousLinearMapL_algebraicCurvatureSubmodule`, and
  `TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv`: linear/isometric equivalences
  identify algebraic curvature tensors.
* `TauCeti.FourTensor.ricci_apply`: the Ricci contraction `ricci r u v` is the metric trace of
  `ricciSlice r u v`.
* `TauCeti.FourTensor.ricci_apply_orthonormalBasis` and
  `TauCeti.FourTensor.scalar_apply_orthonormalBasis`: the contractions in an orthonormal basis.
* `TauCeti.FourTensor.ricci_compContinuousLinearMap_linearIsometryEquiv` and
  `TauCeti.FourTensor.scalar_compContinuousLinearMap_linearIsometryEquiv`: the contractions are
  equivariant under linear isometric equivalences.
* `TauCeti.FourTensor.ricci_kulkarniNomizu_innerₗ`: `Ric(h ⊙ g) = (n - 2) h + (tr h) g`.
* `TauCeti.FourTensor.constantCurvature_eq_half_smul_kulkarniNomizu`,
  `TauCeti.FourTensor.constantCurvature_apply_self_pos_iff`: the Kulkarni–Nomizu square formula
  and positivity of `r(u, v, u, v)` on linearly independent pairs.
* `TauCeti.FourTensor.constantCurvature_compContinuousLinearMap_linearIsometry`: linear isometries
  pull the constant-curvature tensor back to the constant-curvature tensor.
* `TauCeti.FourTensor.ricci_constantCurvature` and `TauCeti.FourTensor.scalar_constantCurvature`.
* `TauCeti.FourTensor.curvatureAction_apply_orthonormalBasis` and
  `TauCeti.FourTensor.curvatureAction_innerₗ`: basis independence of the action and `r(g) = Ric(r)`.
* `TauCeti.FourTensor.sum_mul_kulkarniNomizu_innerₗ_last`,
  `TauCeti.FourTensor.sum_mul_kulkarniNomizu_innerₗ_second_fourth`, and
  `TauCeti.FourTensor.curvatureAction_kulkarniNomizu_innerₗ`: contractions against `h ⊙ g`.
* `TauCeti.FourTensor.inner_eq_mul_constantCurvature`: a curvature operator of constant curvature
  `κ` has four-tensor `κ` times the constant-curvature tensor.
* `TauCeti.FourTensor.norm_coordFourTensor` and `TauCeti.FourTensor.sum_coordFourTensor_eq`:
  operator norm and orthonormal-basis coordinate expansion for `coordFourTensor`.
* `TauCeti.FourTensor.isAlgebraicCurvature_planeCurvature`,
  `TauCeti.FourTensor.ricci_planeCurvature`, and `TauCeti.FourTensor.scalar_planeCurvature`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 1.H.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace

noncomputable section

namespace TauCeti

/-- Real continuous four-linear forms on `V`, the carrier of algebraic curvature tensors. -/
abbrev FourTensor (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ V) ℝ

namespace FourTensor

section NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

section Linearity

variable (r : FourTensor V) (a b c d x y : V) (t : ℝ)

/-- A four-tensor is additive in its first argument. -/
theorem apply_add_first : r ![x + y, b, c, d] = r ![x, b, c, d] + r ![y, b, c, d] := by
  simpa only [Matrix.update_vec4_zero] using r.map_update_add ![x, b, c, d] 0 x y

/-- A four-tensor is additive in its second argument. -/
theorem apply_add_second : r ![a, x + y, c, d] = r ![a, x, c, d] + r ![a, y, c, d] := by
  simpa only [Matrix.update_vec4_one] using r.map_update_add ![a, x, c, d] 1 x y

/-- A four-tensor is additive in its third argument. -/
theorem apply_add_third : r ![a, b, x + y, d] = r ![a, b, x, d] + r ![a, b, y, d] := by
  simpa only [Matrix.update_vec4_two] using r.map_update_add ![a, b, x, d] 2 x y

/-- A four-tensor is additive in its fourth argument. -/
theorem apply_add_fourth : r ![a, b, c, x + y] = r ![a, b, c, x] + r ![a, b, c, y] := by
  simpa only [Matrix.update_vec4_three] using r.map_update_add ![a, b, c, x] 3 x y

/-- A four-tensor is homogeneous in its first argument. -/
theorem apply_smul_first : r ![t • x, b, c, d] = t * r ![x, b, c, d] := by
  simpa only [Matrix.update_vec4_zero, smul_eq_mul] using r.map_update_smul ![x, b, c, d] 0 t x

/-- A four-tensor is homogeneous in its second argument. -/
theorem apply_smul_second : r ![a, t • x, c, d] = t * r ![a, x, c, d] := by
  simpa only [Matrix.update_vec4_one, smul_eq_mul] using r.map_update_smul ![a, x, c, d] 1 t x

/-- A four-tensor is homogeneous in its third argument. -/
theorem apply_smul_third : r ![a, b, t • x, d] = t * r ![a, b, x, d] := by
  simpa only [Matrix.update_vec4_two, smul_eq_mul] using r.map_update_smul ![a, b, x, d] 2 t x

/-- A four-tensor is homogeneous in its fourth argument. -/
theorem apply_smul_fourth : r ![a, b, c, t • x] = t * r ![a, b, c, x] := by
  simpa only [Matrix.update_vec4_three, smul_eq_mul] using r.map_update_smul ![a, b, c, x] 3 t x

end Linearity

/-- The algebraic symmetries of a curvature four-tensor `r(u, v, z, w) = g(R(u, v)w, z)`:
antisymmetry in the first and in the last pair of arguments, symmetry under interchanging the two
pairs, and the first Bianchi identity. -/
structure IsAlgebraicCurvature (r : FourTensor V) : Prop where
  /-- Antisymmetry in the first pair of arguments. -/
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  /-- Antisymmetry in the last pair of arguments. -/
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  /-- Symmetry under interchanging the two pairs of arguments. -/
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]
  /-- The first Bianchi identity. -/
  cyclic_eq_zero : ∀ u v z w, r ![u, v, z, w] + r ![v, z, u, w] + r ![z, u, v, w] = 0

/-- Simultaneously swapping the first pair and the last pair of arguments leaves an algebraic
curvature tensor unchanged. -/
theorem IsAlgebraicCurvature.swap_first_last {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v z w : V) : r ![u, v, z, w] = r ![v, u, w, z] := by
  rw [hr.antisymm_first, hr.antisymm_last, neg_neg]

/-- Reversing all four arguments leaves an algebraic curvature tensor unchanged. -/
theorem IsAlgebraicCurvature.reverse {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v z w : V) : r ![u, v, z, w] = r ![w, z, v, u] := by
  rw [hr.swap_first_last, hr.swap_pairs]

/-- The first Bianchi identity in the last three arguments:
`r(u, v, z, w) + r(u, z, w, v) + r(u, w, v, z) = 0`. -/
theorem IsAlgebraicCurvature.cyclic_last_eq_zero {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (u v z w : V) : r ![u, v, z, w] + r ![u, z, w, v] + r ![u, w, v, z] = 0 := by
  rw [hr.reverse u v, hr.reverse u z, hr.reverse u w]
  linear_combination hr.cyclic_eq_zero w z v u

variable (V) in
/-- The submodule of algebraic curvature tensors. -/
def algebraicCurvatureSubmodule : Submodule ℝ (FourTensor V) where
  carrier := {r | IsAlgebraicCurvature r}
  zero_mem' := ⟨by simp, by simp, by simp, by simp⟩
  add_mem' {r q} hr hq := by
    refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
      simp only [add_apply]
    · rw [hr.antisymm_first, hq.antisymm_first, neg_add]
    · rw [hr.antisymm_last, hq.antisymm_last, neg_add]
    · rw [hr.swap_pairs, hq.swap_pairs]
    · linear_combination hr.cyclic_eq_zero u v z w + hq.cyclic_eq_zero u v z w
  smul_mem' c r hr := by
    refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
      simp only [smul_apply, smul_eq_mul]
    · rw [hr.antisymm_first, mul_neg]
    · rw [hr.antisymm_last, mul_neg]
    · rw [hr.swap_pairs]
    · linear_combination c * hr.cyclic_eq_zero u v z w

/-- Membership in `algebraicCurvatureSubmodule V` is `IsAlgebraicCurvature`. -/
@[simp]
theorem mem_algebraicCurvatureSubmodule {r : FourTensor V} :
    r ∈ algebraicCurvatureSubmodule V ↔ IsAlgebraicCurvature r :=
  Iff.rfl

/-- The algebraic curvature tensors form a closed subspace: each of their defining identities is
the vanishing of a continuous linear functional of the tensor. -/
theorem isClosed_algebraicCurvatureSubmodule :
    IsClosed (algebraicCurvatureSubmodule V : Set (FourTensor V)) := by
  have : (algebraicCurvatureSubmodule V : Set (FourTensor V)) =
      (⋂ u, ⋂ v, ⋂ z, ⋂ w, {r : FourTensor V | r ![u, v, z, w] = -r ![v, u, z, w]}) ∩
      (⋂ u, ⋂ v, ⋂ z, ⋂ w, {r : FourTensor V | r ![u, v, z, w] = -r ![u, v, w, z]}) ∩
      (⋂ u, ⋂ v, ⋂ z, ⋂ w, {r : FourTensor V | r ![u, v, z, w] = r ![z, w, u, v]}) ∩
      (⋂ u, ⋂ v, ⋂ z, ⋂ w,
        {r : FourTensor V | r ![u, v, z, w] + r ![v, z, u, w] + r ![z, u, v, w] = 0}) := by
    ext r
    simp only [SetLike.mem_coe, mem_algebraicCurvatureSubmodule, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨⟨⟨h.antisymm_first, h.antisymm_last⟩, h.swap_pairs⟩, h.cyclic_eq_zero⟩, fun h ↦
        ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [this]
  refine ((IsClosed.inter (IsClosed.inter ?_ ?_) ?_).inter ?_) <;>
    refine isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun z ↦
      isClosed_iInter fun w ↦ isClosed_eq ?_ ?_ <;>
    fun_prop

/-- Two four-tensors agree when they agree on every four-tuple `![u, v, z, w]`. -/
theorem ext_vec {r s : FourTensor V} (h : ∀ u v z w, r ![u, v, z, w] = s ![u, v, z, w]) :
    r = s :=
  ContinuousMultilinearMap.ext fun m ↦ by
    have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
    rw [hm]
    exact h (m 0) (m 1) (m 2) (m 3)

/-- A four-tensor has operator norm at most `C` once
`|r ![u, v, z, w]| ≤ C * ‖u‖ * ‖v‖ * ‖z‖ * ‖w‖` for all `u, v, z, w`. -/
theorem opNorm_le_bound_vec {r : FourTensor V} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u v z w, |r ![u, v, z, w]| ≤ C * ‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) : ‖r‖ ≤ C :=
  ContinuousMultilinearMap.opNorm_le_bound hC fun m ↦ by
    rw [Fin.prod_univ_four]
    have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
    conv_lhs => rw [hm]
    simpa only [Real.norm_eq_abs, mul_assoc] using h (m 0) (m 1) (m 2) (m 3)

/-- The pullback of a four-tensor by a continuous linear map `f` evaluates `r` on the images under
`f`. -/
theorem compContinuousLinearMap_apply_vec (r : FourTensor V) (f : W →L[ℝ] V) (a b c d : W) :
    (r.compContinuousLinearMap fun _ ↦ f) ![a, b, c, d] = r ![f a, f b, f c, f d] := by
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i; fin_cases i <;> rfl

/-- The pullback of an algebraic curvature tensor by a continuous linear map is an algebraic
curvature tensor. -/
theorem IsAlgebraicCurvature.compContinuousLinearMap {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (f : W →L[ℝ] V) :
    IsAlgebraicCurvature (r.compContinuousLinearMap fun _ ↦ f) := by
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [compContinuousLinearMap_apply_vec]
  · exact hr.antisymm_first _ _ _ _
  · exact hr.antisymm_last _ _ _ _
  · exact hr.swap_pairs _ _ _ _
  · exact hr.cyclic_eq_zero _ _ _ _

/-- The submodule of algebraic curvature tensors is stable under pullback by continuous linear
maps, in particular under the orthogonal group. -/
theorem compContinuousLinearMap_mem_algebraicCurvatureSubmodule {r : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) (f : W →L[ℝ] V) :
    r.compContinuousLinearMap (fun _ ↦ f) ∈ algebraicCurvatureSubmodule W :=
  IsAlgebraicCurvature.compContinuousLinearMap hr f

/-- Pulling back along a continuous linear equivalence preserves and reflects the curvature
symmetries. In particular a linear isometry `V ≃ₗᵢ[ℝ] T` identifies the algebraic curvature
tensors on a tangent space `T` with those on the model space `V`. -/
theorem isAlgebraicCurvature_compContinuousLinearMap_iff (e : W ≃L[ℝ] V) {r : FourTensor V} :
    IsAlgebraicCurvature (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) ↔
      IsAlgebraicCurvature r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compContinuousLinearMap _⟩
  convert h.compContinuousLinearMap (e.symm : V →L[ℝ] W) using 1
  ext m
  simp

/-- A continuous linear equivalence `e : W ≃L[ℝ] V` identifies the algebraic curvature tensors on
`V` with those on `W`: they are exactly the four-tensors whose pullback along `e` is one. -/
theorem comap_compContinuousLinearMapL_algebraicCurvatureSubmodule (e : W ≃L[ℝ] V) :
    (algebraicCurvatureSubmodule W).comap
        ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ (e : W →L[ℝ] V) :
          FourTensor V →L[ℝ] FourTensor W) : FourTensor V →ₗ[ℝ] FourTensor W) =
      algebraicCurvatureSubmodule V := by
  ext r
  exact isAlgebraicCurvature_compContinuousLinearMap_iff e

/-- Pullback of algebraic curvature tensors along `e : W ≃ₗᵢ[ℝ] V` as a `LinearIsometryEquiv`. -/
def algebraicCurvatureLinearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) :
    algebraicCurvatureSubmodule V ≃ₗᵢ[ℝ] algebraicCurvatureSubmodule W where
  toFun r := ⟨r.val.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V),
    compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.property (e : W →L[ℝ] V)⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun q := ⟨q.val.compContinuousLinearMap fun _ ↦ (e.symm : V →L[ℝ] W),
    compContinuousLinearMap_mem_algebraicCurvatureSubmodule q.property (e.symm : V →L[ℝ] W)⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  norm_map' r := r.val.norm_compContinuous_linearIsometryEquiv fun _ ↦ e

/-- Coercion of `algebraicCurvatureLinearIsometryEquiv` to `FourTensor`. -/
@[simp]
theorem coe_algebraicCurvatureLinearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : algebraicCurvatureSubmodule V) : (algebraicCurvatureLinearIsometryEquiv e r).val =
      r.val.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V) := (rfl)

/-- Evaluating a four-tensor on four unit vectors has absolute value at most `‖r‖`. -/
theorem abs_apply_le_norm_of_norm_eq_one (r : FourTensor V) {u v z w : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) : |r ![u, v, z, w]| ≤ ‖r‖ := by
  have h := r.le_opNorm ![u, v, z, w]
  rw [Real.norm_eq_abs, Fin.prod_univ_four] at h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hu, hv, hz, hw,
    mul_one] using h

/-- The pullback `r ↦ r(f ·, f ·, f ·, f ·)` of algebraic curvature tensors along a continuous
linear map `f : W →L[ℝ] V`, as a continuous linear map between the spaces of algebraic curvature
tensors. Along a linear isometry `V ≃ₗᵢ[ℝ] T` it transports curvature tensors on a tangent space
`T` to the fixed model space `V`. -/
def algebraicCurvaturePullback (f : W →L[ℝ] V) :
    algebraicCurvatureSubmodule V →L[ℝ] algebraicCurvatureSubmodule W :=
  ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ f).comp
    (algebraicCurvatureSubmodule V).subtypeL).codRestrict _ fun r ↦
      compContinuousLinearMap_mem_algebraicCurvatureSubmodule r.property f

/-- The pullback of `r` along `f` evaluates `r` on the images under `f`. -/
@[simp]
theorem coe_algebraicCurvaturePullback (f : W →L[ℝ] V) (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvaturePullback f r : FourTensor W) = r.val.compContinuousLinearMap fun _ ↦ f :=
  (rfl)

/-- Pullback along the identity is the identity. -/
@[simp]
theorem algebraicCurvaturePullback_id :
    algebraicCurvaturePullback (.id ℝ V) = .id ℝ (algebraicCurvatureSubmodule V) := by
  ext r m
  simp

/-- Pullback is contravariant: pulling back along `f` and then along `g` is pulling back along
`f ∘ g`. -/
theorem algebraicCurvaturePullback_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : W →L[ℝ] V) (g : U →L[ℝ] W) :
    algebraicCurvaturePullback (f.comp g) =
      (algebraicCurvaturePullback g).comp (algebraicCurvaturePullback f) := by
  ext r m
  simp

/-- Pulling back along a right inverse `g` of `f` undoes pulling back along `f`. -/
theorem algebraicCurvaturePullback_algebraicCurvaturePullback_of_comp_eq_id {f : W →L[ℝ] V}
    {g : V →L[ℝ] W} (h : f.comp g = .id ℝ V) (r : algebraicCurvatureSubmodule V) :
    algebraicCurvaturePullback g (algebraicCurvaturePullback f r) = r := by
  rw [← ContinuousLinearMap.comp_apply, ← algebraicCurvaturePullback_comp, h,
    algebraicCurvaturePullback_id, ContinuousLinearMap.id_apply]

/-- Curry a continuous four-tensor into a four-fold linear map. -/
def toLinearMap₄ : FourTensor V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun r := LinearMap.mk₂ ℝ (fun u v ↦ LinearMap.mk₂ ℝ (fun z w ↦ r ![u, v, z, w])
      (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
      (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..))
    (fun _ _ _ ↦ by ext; exact apply_add_first ..) (fun _ _ _ ↦ by ext; exact apply_smul_first ..)
    (fun _ _ _ ↦ by ext; exact apply_add_second ..) (fun _ _ _ ↦ by ext; exact apply_smul_second ..)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Evaluation of `toLinearMap₄ r` on four vectors. -/
@[simp] theorem toLinearMap₄_apply (r : FourTensor V) (u v z w : V) :
    toLinearMap₄ r u v z w = r ![u, v, z, w] := (rfl)

/-- Currying a four-tensor into a four-fold linear map is injective. -/
theorem toLinearMap₄_injective : Function.Injective (toLinearMap₄ (V := V)) := fun _ _ h ↦ by
  ext m; rw [← FinVec.etaExpand_eq m]; exact congr($h (m 0) (m 1) (m 2) (m 3))

/-- The bilinear form `(x, y) ↦ r(x, u, y, v)` whose metric trace is the Ricci contraction
(`TauCeti.FourTensor.ricci_apply`): the slice of `toLinearMap₄ r` with the second slot fixed to `u`
and the fourth to `v`. -/
def ricciSlice (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  ((toLinearMap₄ r).flip u).compr₂ (LinearMap.applyₗ v)

/-- Evaluation of `ricciSlice r u v` on `(x, y)` evaluates `r` on `(x, u, y, v)`, with `u` and `v`
fixed in the second and fourth slots. -/
@[simp]
theorem ricciSlice_apply (r : FourTensor V) (u v x y : V) :
    ricciSlice r u v x y = r ![x, u, y, v] := by
  rw [ricciSlice, LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.applyₗ_apply_apply,
    toLinearMap₄_apply]

end NormedSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a finite-dimensional space, the four-tensor of a curried four-linear form `T`:
`ofLinearMap₄ T ![a, b, c, d] = T a b c d`. Continuity is automatic in finite dimension. -/
def ofLinearMap₄ : (V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] FourTensor V where
  toFun T :=
    let f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 4 ↦ V) ℝ :=
      MultilinearMap.mk' (fun m ↦ T (m 0) (m 1) (m 2) (m 3))
        (fun m i x y ↦ by fin_cases i <;> simp)
        (fun m i c x ↦ by fin_cases i <;> simp)
    { f with cont := f.continuous_of_finiteDimensional }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `ofLinearMap₄ T` evaluates `T` on the four entries of the tuple. -/
@[simp]
theorem ofLinearMap₄_apply (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (m : Fin 4 → V) :
    ofLinearMap₄ T m = T (m 0) (m 1) (m 2) (m 3) :=
  (rfl)

/-- Currying and uncurrying a four-tensor recovers the original four-tensor. -/
@[simp] theorem ofLinearMap₄_toLinearMap₄ (r : FourTensor V) :
    ofLinearMap₄ (toLinearMap₄ r) = r := by
  ext m; rw [ofLinearMap₄_apply, toLinearMap₄_apply]; exact congrArg r (FinVec.etaExpand_eq m)

/-- Uncurrying and currying a four-fold linear form recovers the original form. -/
@[simp] theorem toLinearMap₄_ofLinearMap₄ (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    toLinearMap₄ (ofLinearMap₄ T) = T := by ext; rfl

/-- On a finite-dimensional space, currying identifies `FourTensor V` with four-fold linear maps,
inverse to `ofLinearMap₄`. -/
def toLinearMap₄Equiv : FourTensor V ≃ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  { toLinearMap₄ with
    invFun := ofLinearMap₄, left_inv := ofLinearMap₄_toLinearMap₄,
    right_inv := toLinearMap₄_ofLinearMap₄ }

/-- Applying `toLinearMap₄Equiv` agrees with `toLinearMap₄`. -/
@[simp] theorem toLinearMap₄Equiv_apply (r : FourTensor V) :
    toLinearMap₄Equiv r = toLinearMap₄ r := (rfl)

/-- The underlying linear map of `toLinearMap₄Equiv` is `toLinearMap₄`. -/
@[simp] theorem toLinearMap₄Equiv_toLinearMap :
    (toLinearMap₄Equiv (V := V)).toLinearMap = toLinearMap₄ := (rfl)

/-- The inverse of `toLinearMap₄Equiv` is `ofLinearMap₄`. -/
@[simp] theorem toLinearMap₄Equiv_symm_apply (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    toLinearMap₄Equiv.symm T = ofLinearMap₄ T := (rfl)

/-- The inverse of `toLinearMap₄Equiv` as a linear map is `ofLinearMap₄`. -/
@[simp] theorem toLinearMap₄Equiv_symm_toLinearMap :
    (toLinearMap₄Equiv (V := V)).symm.toLinearMap = ofLinearMap₄ := (rfl)

/-- The Kulkarni–Nomizu product of two bilinear forms as a four-tensor, in the curvature
convention `r(u, v, z, w) = g(R(u, v)w, z)`:
`(h ⊙ k)(u, v, z, w) = h(u, z) k(v, w) + h(v, w) k(u, z) - h(u, w) k(v, z) - h(v, z) k(u, w)`.
It is `LinearMap.BilinForm.kulkarniNomizu` with its last two arguments interchanged. -/
def kulkarniNomizu : BilinForm ℝ V →ₗ[ℝ] BilinForm ℝ V →ₗ[ℝ] FourTensor V :=
  LinearMap.BilinForm.kulkarniNomizu.compr₂ (-ofLinearMap₄)

/-- Evaluation of the Kulkarni–Nomizu four-tensor. -/
@[simp]
theorem kulkarniNomizu_apply (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] =
      h u z * k v w + h v w * k u z - h u w * k v z - h v z * k u w := by
  simp only [kulkarniNomizu, LinearMap.compr₂_apply, LinearMap.neg_apply, neg_apply,
    ofLinearMap₄_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    LinearMap.BilinForm.kulkarniNomizu_apply]
  ring

/-- The four-tensor `TauCeti.FourTensor.kulkarniNomizu h k` is
`LinearMap.BilinForm.kulkarniNomizu h k` with its last two arguments interchanged. -/
theorem kulkarniNomizu_apply_eq (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = LinearMap.BilinForm.kulkarniNomizu h k u v w z := by
  rw [kulkarniNomizu_apply, LinearMap.BilinForm.kulkarniNomizu_apply]

/-- The Kulkarni–Nomizu four-tensor is antisymmetric in its first pair of arguments. -/
theorem kulkarniNomizu_antisymm_first (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![v, u, z, w] := by
  simp only [kulkarniNomizu_apply_eq]
  exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first h k u v w z

/-- The Kulkarni–Nomizu four-tensor is antisymmetric in its last pair of arguments. -/
theorem kulkarniNomizu_antisymm_last (h k : BilinForm ℝ V) (u v z w : V) :
    kulkarniNomizu h k ![u, v, z, w] = -kulkarniNomizu h k ![u, v, w, z] := by
  simp only [kulkarniNomizu_apply_eq]
  exact LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k u v w z

/-- The Kulkarni–Nomizu product of two symmetric bilinear forms is an algebraic curvature
tensor. -/
theorem isAlgebraicCurvature_kulkarniNomizu {h k : BilinForm ℝ V} (hh : h.IsSymm)
    (hk : k.IsSymm) : IsAlgebraicCurvature (kulkarniNomizu h k) := by
  refine ⟨kulkarniNomizu_antisymm_first h k, kulkarniNomizu_antisymm_last h k,
    fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [kulkarniNomizu_apply_eq]
  · rw [hh.kulkarniNomizu_swap_pairs hk, LinearMap.BilinForm.kulkarniNomizu_antisymm_first,
      LinearMap.BilinForm.kulkarniNomizu_antisymm_last, neg_neg]
  · have := hh.kulkarniNomizu_cyclic_eq_zero hk u v z w
    rw [LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k u v z w,
      LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k v z u w,
      LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k z u v w] at this
    linear_combination -this

end FiniteDimensional

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Ricci contraction `Ric(u, v) = tr (x, y ↦ r(x, u, y, v))` of a four-tensor, the metric
trace over its first and third arguments. In an orthonormal basis it is
`∑ᵢ r(eᵢ, u, eᵢ, v)`, see `TauCeti.FourTensor.ricci_apply_orthonormalBasis`. -/
def ricci : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := LinearMap.mk₂ ℝ (fun u v ↦ LinearMap.BilinMap.metricTrace (ricciSlice r u v))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext
      simp only [ricciSlice_apply, LinearMap.add_apply, apply_add_second])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext
      simp only [ricciSlice_apply, LinearMap.smul_apply, apply_smul_second, smul_eq_mul])
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext
      simp only [ricciSlice_apply, LinearMap.add_apply, apply_add_fourth])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext
      simp only [ricciSlice_apply, LinearMap.smul_apply, apply_smul_fourth, smul_eq_mul])
  map_add' r q := by
    ext u v
    have h : ricciSlice (r + q) u v = ricciSlice r u v + ricciSlice q u v := by
      ext; simp only [ricciSlice_apply, LinearMap.add_apply, _root_.add_apply]
    simp only [LinearMap.mk₂_apply, LinearMap.add_apply, h, map_add]
  map_smul' c r := by
    ext u v
    have h : ricciSlice (c • r) u v = c • ricciSlice r u v := by
      ext; simp only [ricciSlice_apply, LinearMap.smul_apply, _root_.smul_apply]
    simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, RingHom.id_apply, h, map_smul]

/-- The Ricci contraction is the metric trace of the slice `(x, y) ↦ r(x, u, y, v)`. -/
theorem ricci_apply (r : FourTensor V) (u v : V) :
    ricci r u v = LinearMap.BilinMap.metricTrace (ricciSlice r u v) := by
  simp only [ricci, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk₂_apply]

/-- In every orthonormal basis `(eᵢ)`, the Ricci contraction is `∑ᵢ r(eᵢ, u, eᵢ, v)`. -/
theorem ricci_apply_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v : V) : ricci r u v = ∑ i, r ![b i, u, b i, v] := by
  rw [ricci_apply, LinearMap.BilinMap.metricTrace_eq_sum (ricciSlice r u v) b]
  simp only [ricciSlice_apply]

/-- The Ricci curvature of a vector `u` is `‖u‖²` times that of `‖u‖⁻¹ • u`, which is a unit
vector when `u ≠ 0`; for `u = 0` both sides vanish. -/
theorem ricci_apply_self_eq_norm_sq_mul (r : FourTensor V) (u : V) :
    ricci r u u = ‖u‖ ^ 2 * ricci r (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- The Ricci contraction of a four-tensor symmetric under pair interchange is symmetric. -/
theorem isSymm_ricci_of_swap_pairs {r : FourTensor V}
    (h : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) : (ricci r).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  simp only [ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_congr rfl fun i _ ↦ (h _ _ _ _).symm

/-- The Ricci contraction of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_ricci {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (ricci r).IsSymm := isSymm_ricci_of_swap_pairs hr.swap_pairs

/-- The Ricci contraction is equivariant under linear isometric equivalences: the Ricci contraction
of the pullback of `r` by `e` is the pullback of the Ricci contraction of `r`. -/
theorem ricci_compContinuousLinearMap_linearIsometryEquiv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V)
    (u v : W) :
    ricci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      ricci r (e u) (e v) := by
  -- The slice of the pulled-back tensor is the pullback of the slice.
  have h : ricciSlice (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
      u v = (ricciSlice r (e u) (e v)).compl₁₂ e.toLinearEquiv.toLinearMap
        e.toLinearEquiv.toLinearMap :=
    LinearMap.ext₂ fun x y ↦ by
      simp only [ricciSlice_apply, LinearMap.compl₁₂_apply, compContinuousLinearMap_apply_vec,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [ricci_apply, ricci_apply, h, LinearMap.BilinMap.metricTrace_compl₁₂_linearIsometryEquiv]

/-- The scalar contraction of a four-tensor: the metric trace of its Ricci contraction. -/
def scalar : FourTensor V →ₗ[ℝ] ℝ :=
  LinearMap.BilinMap.metricTrace ∘ₗ ricci

/-- The scalar contraction is the metric trace of the Ricci contraction. -/
theorem scalar_apply (r : FourTensor V) : scalar r = LinearMap.BilinMap.metricTrace (ricci r) :=
  (rfl)

/-- In every orthonormal basis `(eᵢ)`, the scalar contraction is `∑ᵢ ∑ⱼ r(eᵢ, eⱼ, eᵢ, eⱼ)`. -/
theorem scalar_apply_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) : scalar r = ∑ j, ∑ i, r ![b i, b j, b i, b j] := by
  simp only [scalar_apply, LinearMap.BilinMap.metricTrace_eq_sum _ b,
    ricci_apply_orthonormalBasis b]

/-- The scalar contraction is invariant under linear isometric equivalences. -/
theorem scalar_compContinuousLinearMap_linearIsometryEquiv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    scalar (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      scalar r := by
  have h : ricci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (ricci r).compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap :=
    LinearMap.ext₂ fun u v ↦ by
      rw [ricci_compContinuousLinearMap_linearIsometryEquiv, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [scalar_apply, scalar_apply, h, LinearMap.BilinMap.metricTrace_compl₁₂_linearIsometryEquiv]

/-- The Ricci contraction of the Kulkarni–Nomizu product of `h` with the inner product:
`Ric(h ⊙ g) = (n - 2) h + (tr h) g`. -/
theorem ricci_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    ricci (kulkarniNomizu h (innerₗ V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • h + LinearMap.BilinMap.metricTrace h • innerₗ V := by
  ext u v
  rw [ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  simp only [kulkarniNomizu_apply_eq, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    innerₗ_apply_apply]
  exact LinearMap.BilinForm.sum_kulkarniNomizu_innerₗ h _ u v

/-- The scalar contraction of the Kulkarni–Nomizu product of `h` with the inner product:
`Scal(h ⊙ g) = 2 (n - 1) tr h`. -/
theorem scalar_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    scalar (kulkarniNomizu h (innerₗ V)) =
      2 * ((Module.finrank ℝ V : ℝ) - 1) * LinearMap.BilinMap.metricTrace h := by
  rw [scalar_apply, ricci_kulkarniNomizu_innerₗ, map_add, map_smul, map_smul,
    LinearMap.BilinMap.metricTrace_inner, smul_eq_mul, smul_eq_mul]
  ring

variable (V) in
/-- The constant-curvature tensor of curvature `1`,
`r(u, v, z, w) = ⟪u, z⟫ ⟪v, w⟫ - ⟪u, w⟫ ⟪v, z⟫`: half the Kulkarni–Nomizu product of the inner
product with itself. It is the curvature four-tensor of the unit sphere, and `κ` times it is the
curvature four-tensor of a space of constant sectional curvature `κ`. -/
def constantCurvature : FourTensor V :=
  (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V)

/-- The constant-curvature tensor is half the Kulkarni–Nomizu square of the inner product. -/
theorem constantCurvature_eq_half_smul_kulkarniNomizu :
    constantCurvature V = (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V) :=
  (rfl)

/-- Evaluation of the constant-curvature tensor. -/
@[simp]
theorem constantCurvature_apply (u v z w : V) :
    constantCurvature V ![u, v, z, w] = ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ := by
  simp only [constantCurvature, smul_apply, kulkarniNomizu_apply,
    innerₗ_apply_apply, smul_eq_mul]
  ring

/-- The constant-curvature tensor is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_constantCurvature : IsAlgebraicCurvature (constantCurvature V) :=
  Submodule.smul_mem (algebraicCurvatureSubmodule V) _
    (isAlgebraicCurvature_kulkarniNomizu isSymm_innerₗ isSymm_innerₗ)

/-- On a pair `(u, v)`, the constant-curvature tensor is the Gram determinant
`‖u‖² ‖v‖² - ⟪u, v⟫²`. -/
theorem constantCurvature_apply_self (u v : V) :
    constantCurvature V ![u, v, u, v] = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by
  rw [constantCurvature_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm v u]
  ring

/-- On a linearly independent pair the constant-curvature tensor is positive: its value is the
determinant of the Gram matrix of the pair. -/
theorem constantCurvature_apply_self_pos {u v : V} (h : LinearIndependent ℝ ![u, v]) :
    0 < constantCurvature V ![u, v, u, v] := by
  have := (Matrix.posDef_gram_of_linearIndependent h).det_pos
  rw [Matrix.det_fin_two] at this
  simpa [Matrix.gram_apply] using this

/-- The constant-curvature tensor is positive on `(u, v, u, v)` exactly when `u` and `v` are
linearly independent. -/
theorem constantCurvature_apply_self_pos_iff {u v : V} :
    0 < constantCurvature V ![u, v, u, v] ↔ LinearIndependent ℝ ![u, v] := by
  refine ⟨fun h ↦ Matrix.linearIndependent_of_det_gram_ne_zero ?_, constantCurvature_apply_self_pos⟩
  rw [Matrix.det_fin_two]
  simpa [Matrix.gram_apply] using h.ne'

/-- A linear isometry pulls the constant-curvature tensor back to the constant-curvature
tensor. -/
@[simp]
theorem constantCurvature_compContinuousLinearMap_linearIsometry {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) :
    (constantCurvature V).compContinuousLinearMap (fun _ ↦ f.toContinuousLinearMap) =
      constantCurvature W := by
  refine ext_vec fun a b c d ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

/-- The Ricci contraction of the constant-curvature tensor is `(n - 1) g`. -/
theorem ricci_constantCurvature :
    ricci (constantCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • innerₗ V := by
  rw [constantCurvature, map_smul, ricci_kulkarniNomizu_innerₗ,
    LinearMap.BilinMap.metricTrace_inner, ← add_smul, smul_smul]
  congr 1
  ring

/-- The scalar contraction of the constant-curvature tensor is `n (n - 1)`. -/
theorem scalar_constantCurvature :
    scalar (constantCurvature V) = Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1) := by
  rw [constantCurvature, map_smul, scalar_kulkarniNomizu_innerₗ,
    LinearMap.BilinMap.metricTrace_inner, smul_eq_mul]
  ring

/-- A curvature operator of constant curvature `κ`, `R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)` as in
`Bundle.RiemannianMetric.IsConstantCurvatureTensor`, has four-tensor
`⟪R(u, v)w, z⟫ = κ r(u, v, z, w)`, with `r` the constant-curvature tensor: the sign of the
predicate and of the four-tensor agree. -/
theorem inner_eq_mul_constantCurvature {R : V → V → V → V} {κ : ℝ}
    (hR : ∀ w u v, R w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u)) (u v z w : V) :
    ⟪R u v w, z⟫_ℝ = κ * constantCurvature V ![u, v, z, w] := by
  rw [hR, constantCurvature_apply, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left]
  ring

/-! ### The action of a four-tensor on bilinear forms -/

private def curvatureActionFun (r : FourTensor V) (h : BilinForm ℝ V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun u v ↦ ∑ p, ∑ q, h (stdOrthonormalBasis ℝ V p)
      (stdOrthonormalBasis ℝ V q) *
        r ![stdOrthonormalBasis ℝ V p, u, stdOrthonormalBasis ℝ V q, v])
    (fun _ _ _ ↦ by simp only [apply_add_second, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      simp only [apply_smul_second, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun _ _ _ ↦ by simp only [apply_add_fourth, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      simp only [apply_smul_fourth, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- The action `h ↦ r(h)` of a four-tensor `r` on bilinear forms, contracting the first and
third slots of `r` against `h`: in an orthonormal basis `(eₚ)`,
`r(h)(u, v) = ∑_pq h(eₚ, e_q) r(eₚ, u, e_q, v)`
(`TauCeti.FourTensor.curvatureAction_apply_orthonormalBasis`). Contracting against the inner
product gives the Ricci contraction, `r(g) = Ric(r)`. -/
def curvatureAction : FourTensor V →ₗ[ℝ] BilinForm ℝ V →ₗ[ℝ] BilinForm ℝ V :=
  LinearMap.mk₂ ℝ curvatureActionFun
    (fun _ _ _ ↦ by
      ext; simp [curvatureActionFun, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      ext; simp only [curvatureActionFun, LinearMap.mk₂_apply, smul_apply, smul_eq_mul,
        LinearMap.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun _ _ _ ↦ by
      ext; simp [curvatureActionFun, add_mul, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      ext; simp only [curvatureActionFun, LinearMap.mk₂_apply, smul_eq_mul,
        LinearMap.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- **Basis independence** of `curvatureAction`: in every orthonormal basis `b`,
`r(h)(u, v) = ∑_pq h(b p, b q) r(b p, u, b q, v)`. -/
theorem curvatureAction_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (h : BilinForm ℝ V) (u v : V) :
    curvatureAction r h u v = ∑ p, ∑ q, h (b p) (b q) * r ![b p, u, b q, v] := by
  have hid : ∀ x y : V, ⟪(id : V → V) x, y⟫_ℝ = ⟪x, (id : V → V) y⟫_ℝ := fun _ _ ↦ rfl
  have key := (stdOrthonormalBasis ℝ V).sum_sum_inner_comp_eq_of_inner_eq b hid hid h
    (ricciSlice r u v)
  simp only [Real.inner_apply, ricciSlice_apply, id_eq] at key
  simp only [curvatureAction, curvatureActionFun, LinearMap.mk₂_apply]
  simpa only [mul_comm] using key

/-- Contracting a four-tensor against the inner product gives its Ricci contraction:
`r(g) = Ric(r)`. -/
@[simp]
theorem curvatureAction_innerₗ (r : FourTensor V) :
    curvatureAction r (innerₗ V) = ricci r := by
  classical
  let b := stdOrthonormalBasis ℝ V
  ext u v
  simp only [curvatureAction_apply_orthonormalBasis b, ricci_apply_orthonormalBasis b,
    innerₗ_apply_apply, orthonormal_iff_ite.mp b.orthonormal, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ### Contractions against Kulkarni–Nomizu products with the inner product -/

/-- Contracting the last two slots of an algebraic curvature tensor `r` against the
Kulkarni–Nomizu product `h ⊙ g` in an orthonormal basis `b`, where `h♯ = bilinFormToEnd h`:
`∑_pq r(a, c, b p, b q) (h ⊙ g)(x, y, b p, b q) = 2 (r(a, c, h♯ x, y) + r(a, c, x, h♯ y))`. -/
theorem sum_mul_kulkarniNomizu_innerₗ_last {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (h : BilinForm ℝ V) (a c x y : V) :
    (∑ p, ∑ q, r ![a, c, b p, b q] * kulkarniNomizu h (innerₗ V) ![x, y, b p, b q]) =
      2 * (r ![a, c, bilinFormToEnd h x, y] + r ![a, c, x, bilinFormToEnd h y]) := by
  set H := bilinFormToEnd h
  set B := toLinearMap₄ r a c
  have hexp : (∑ p, ∑ q, r ![a, c, b p, b q] * kulkarniNomizu h (innerₗ V) ![x, y, b p, b q]) =
      (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H x⟫_ℝ * ⟪b q, y⟫_ℝ) +
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, x⟫_ℝ * ⟪b q, H y⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, y⟫_ℝ * ⟪b q, H x⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H y⟫_ℝ * ⟪b q, x⟫_ℝ) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [B, H, toLinearMap₄_apply, kulkarniNomizu_apply, innerₗ_apply_apply,
      LinearMap.BilinForm.inner_bilinFormToEnd_right, real_inner_comm (b p) x,
      real_inner_comm (b p) y, real_inner_comm (b q) x, real_inner_comm (b q) y]
    ring
  simp only [hexp, b.sum_apply_mul_inner_mul_inner b]
  simp only [B, toLinearMap₄_apply]
  rw [hr.antisymm_last a c y, hr.antisymm_last a c (H y) x]
  ring

/-- Contracting the second and fourth slots of an algebraic curvature tensor `r` against the
Kulkarni–Nomizu product `h ⊙ g` of a symmetric form `h` in an orthonormal basis `b`:
`∑_pq r(a, b p, c, b q) (h ⊙ g)(x, b p, y, b q) =
  h(x, y) Ric(a, c) + ⟪x, y⟫ r(h)(a, c) - r(a, y, c, h♯ x) - r(a, h♯ y, c, x)`. -/
theorem sum_mul_kulkarniNomizu_innerₗ_second_fourth {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    {h : BilinForm ℝ V} (hh : h.IsSymm) (a c x y : V) :
    (∑ p, ∑ q, r ![a, b p, c, b q] * kulkarniNomizu h (innerₗ V) ![x, b p, y, b q]) =
      h x y * ricci r a c + ⟪x, y⟫_ℝ * curvatureAction r h a c -
        r ![a, y, c, bilinFormToEnd h x] - r ![a, bilinFormToEnd h y, c, x] := by
  classical
  set H := bilinFormToEnd h
  set B := (toLinearMap₄ r a).flip c
  have hB (p q : V) : B p q = r ![a, p, c, q] := by simp [B]
  have hexp : (∑ p, ∑ q, r ![a, b p, c, b q] * kulkarniNomizu h (innerₗ V) ![x, b p, y, b q]) =
      h x y * (∑ p, ∑ q, B (b p) (b q) * ⟪b p, b q⟫_ℝ) +
        ⟪x, y⟫_ℝ * (∑ p, ∑ q, h (b p) (b q) * r ![b p, a, b q, c]) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, y⟫_ℝ * ⟪b q, H x⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H y⟫_ℝ * ⟪b q, x⟫_ℝ) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [hB, H, kulkarniNomizu_apply, innerₗ_apply_apply,
      LinearMap.BilinForm.inner_bilinFormToEnd_right, real_inner_comm (b q) x]
    rw [hr.swap_first_last (b p), hh.eq (b p) y]
    ring
  have hdiag : (∑ p, ∑ q, B (b p) (b q) * ⟪b p, b q⟫_ℝ) = ricci r a c := by
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hB, ricci_apply_orthonormalBasis b]
    exact Finset.sum_congr rfl fun p _ ↦ hr.swap_first_last _ _ _ _
  rw [hexp, hdiag, ← curvatureAction_apply_orthonormalBasis, b.sum_apply_mul_inner_mul_inner b,
    b.sum_apply_mul_inner_mul_inner b, hB, hB]

/-- The action of a Kulkarni–Nomizu product with the inner product on a symmetric form: for
symmetric `h` and `k`, with `h♯ = bilinFormToEnd h` and `k♯ = bilinFormToEnd k`,
`(h ⊙ g)(k) = tr(h♯ k♯) g + (tr k) h - ⟪h♯ k♯ ·, ·⟫ - ⟪k♯ h♯ ·, ·⟫`. -/
theorem curvatureAction_kulkarniNomizu_innerₗ {h k : BilinForm ℝ V} (hh : h.IsSymm)
    (hk : k.IsSymm) :
    curvatureAction (kulkarniNomizu h (innerₗ V)) k =
      LinearMap.trace ℝ V (bilinFormToEnd h ∘ₗ bilinFormToEnd k) • innerₗ V +
        LinearMap.BilinMap.metricTrace k • h -
        (innerₗ V).comp (bilinFormToEnd h ∘ₗ bilinFormToEnd k) -
        (innerₗ V).comp (bilinFormToEnd k ∘ₗ bilinFormToEnd h) := by
  classical
  set b := stdOrthonormalBasis ℝ V
  set H := bilinFormToEnd h
  set K := bilinFormToEnd k
  ext u v
  have hexp : curvatureAction (kulkarniNomizu h (innerₗ V)) k u v =
      ⟪u, v⟫_ℝ * (∑ p, ∑ q, h (b p) (b q) * k (b p) (b q)) +
        h u v * (∑ p, ∑ q, k (b p) (b q) * ⟪b p, b q⟫_ℝ) -
        (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ) -
        (∑ p, ∑ q, h u (b q) * (k (b p) (b q) * ⟪b p, v⟫_ℝ)) := by
    rw [curvatureAction_apply_orthonormalBasis b]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [kulkarniNomizu_apply, innerₗ_apply_apply]
    rw [real_inner_comm u (b q)]
    ring
  have h3 : (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ) = ⟪H (K u), v⟫_ℝ := by
    calc (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ)
        = ∑ p, h.flip v (b p) * ⟪b p, K u⟫_ℝ := Finset.sum_congr rfl fun p _ ↦ by
          rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply, hk.eq (b p) u,
            LinearMap.BilinForm.inner_bilinFormToEnd_right]
      _ = ⟪H (K u), v⟫_ℝ := by
          rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply,
            LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have h4 : (∑ p, ∑ q, h u (b q) * (k (b p) (b q) * ⟪b p, v⟫_ℝ)) = ⟪K (H u), v⟫_ℝ := by
    have hq (q : Fin (Module.finrank ℝ V)) :
        (∑ p, k (b p) (b q) * ⟪b p, v⟫_ℝ) = ⟪b q, K v⟫_ℝ := by
      calc (∑ p, k (b p) (b q) * ⟪b p, v⟫_ℝ) = ∑ p, k.flip (b q) (b p) * ⟪b p, v⟫_ℝ :=
            Finset.sum_congr rfl fun p _ ↦ by rw [LinearMap.BilinForm.flip_apply]
        _ = ⟪b q, K v⟫_ℝ := by
            rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply,
              LinearMap.BilinForm.inner_bilinFormToEnd_right]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hq, b.sum_apply_mul_inner]
    rw [LinearMap.BilinForm.inner_bilinFormToEnd_left, hk.eq _ v,
      ← LinearMap.BilinForm.inner_bilinFormToEnd_right k v,
      LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have h2 : (∑ p, ∑ q, k (b p) (b q) * ⟪b p, b q⟫_ℝ) = LinearMap.BilinMap.metricTrace k := by
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, LinearMap.BilinMap.metricTrace_eq_sum k b]
  rw [hexp, h2, h3, h4, ← LinearMap.BilinForm.trace_bilinFormToEnd_comp_bilinFormToEnd b hh]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    innerₗ_apply_apply, smul_eq_mul, H, K]
  ring

end InnerProductSpace

section CoordFourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The rank-one four-tensor `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫` attached to four
vectors of a family `b`. -/
def coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) : FourTensor V :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
    ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)]

/-- Definition of `coordFourTensor` as the composition of `mkPiAlgebraFin` with four inner-product
functionals. -/
theorem coordFourTensor_def {ι : Type*} (b : ι → V) (i j k l : ι) :
    coordFourTensor b i j k l =
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
        ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)] :=
  (rfl)

/-- Evaluation of `coordFourTensor` on four vectors. -/
@[simp]
theorem coordFourTensor_apply {ι : Type*} (b : ι → V) (i j k l : ι) (u v z w : V) :
    coordFourTensor b i j k l ![u, v, z, w] =
      ⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ := by
  simp [coordFourTensor, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

/-- The operator norm of `coordFourTensor b i j k l` is `‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖`. -/
@[simp]
theorem norm_coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) :
    ‖coordFourTensor b i j k l‖ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ := by
  apply le_antisymm
  · refine ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).norm_compContinuousLinearMap_le
      ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)]).trans_eq ?_
    simp [Fin.prod_univ_four, innerSL_apply_norm, mul_assoc]
  · refine le_trans ?_ ((coordFourTensor b i j k l).ratio_le_opNorm ![b i, b j, b k, b l])
    rw [coordFourTensor_apply, Fin.prod_univ_four]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue, abs_of_nonneg (by positivity :
        0 ≤ ‖b i‖ ^ 2 * ‖b j‖ ^ 2 * ‖b k‖ ^ 2 * ‖b l‖ ^ 2)]
    set P := ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖
    have hsq : ‖b i‖ ^ 2 * ‖b j‖ ^ 2 * ‖b k‖ ^ 2 * ‖b l‖ ^ 2 = P * P := by simp only [P]; ring
    rw [hsq, mul_self_div_self]

/-- Every coordinate four-tensor of an orthonormal family has unit operator norm. -/
theorem norm_coordFourTensor_of_orthonormal {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (i j k l : ι) : ‖coordFourTensor b i j k l‖ = 1 := by
  simp [hb.1]

/-- Pulling back `coordFourTensor (f ∘ b)` along a linear isometry `f` gives `coordFourTensor b`. -/
@[simp]
theorem coordFourTensor_compContinuousLinearMap_linearIsometry {ι : Type*} (f : W →ₗᵢ[ℝ] V)
    (b : ι → W) (i j k l : ι) :
    (coordFourTensor (f ∘ b) i j k l).compContinuousLinearMap
      (fun _ ↦ f.toContinuousLinearMap) = coordFourTensor b i j k l := by
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

/-- Every four-tensor on `V` is the sum of its components in an orthonormal basis `b` against the
corresponding coordinate four-tensors `coordFourTensor b i j k l`. -/
theorem sum_coordFourTensor_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] • coordFourTensor b i j k l) = r := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ ↦ b.toBasis) fun v ↦ ?_
  have hv : (fun t : Fin 4 ↦ b.toBasis (v t)) = ![b (v 0), b (v 1), b (v 2), b (v 3)] := by
    funext t; fin_cases t <;> rfl
  simp only [ContinuousMultilinearMap.coe_coe, hv, sum_apply, smul_apply, coordFourTensor_apply,
    smul_eq_mul, orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end CoordFourTensor

section PlaneCurvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The rank-one algebraic curvature four-tensor attached to two vectors `u, v : V`, sending
`(a, b, c, d)` to `(⟪u, a⟫ ⟪v, b⟫ - ⟪u, b⟫ ⟪v, a⟫) (⟪u, c⟫ ⟪v, d⟫ - ⟪u, d⟫ ⟪v, c⟫)`. For an
orthonormal pair `u, v` this is the curvature four-tensor of `S² × ℝⁿ⁻²` along the two-plane
spanned by `u` and `v`. -/
def planeCurvature (u v : V) : FourTensor V :=
  coordFourTensor ![u, v] 0 1 0 1 - coordFourTensor ![u, v] 0 1 1 0 -
    coordFourTensor ![u, v] 1 0 0 1 + coordFourTensor ![u, v] 1 0 1 0

/-- Evaluation of the rank-one plane curvature tensor `planeCurvature u v`. -/
@[simp]
theorem planeCurvature_apply (u v a b c d : V) :
    planeCurvature u v ![a, b, c, d] =
      (⟪u, a⟫_ℝ * ⟪v, b⟫_ℝ - ⟪u, b⟫_ℝ * ⟪v, a⟫_ℝ) *
        (⟪u, c⟫_ℝ * ⟪v, d⟫_ℝ - ⟪u, d⟫_ℝ * ⟪v, c⟫_ℝ) := by
  simp only [planeCurvature, add_apply, sub_apply, coordFourTensor_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `planeCurvature u v` is symmetric in `u` and `v`. -/
theorem planeCurvature_comm (u v : V) : planeCurvature u v = planeCurvature v u := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, planeCurvature_apply]
  ring

/-- A degenerate pair `(u, u)` gives the zero plane curvature tensor. -/
@[simp]
theorem planeCurvature_self (u : V) : planeCurvature u u = 0 := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, zero_apply]
  ring

/-- Scaling the first vector scales `planeCurvature` quadratically. -/
theorem planeCurvature_smul_left (t : ℝ) (u v : V) :
    planeCurvature (t • u) v = (t ^ 2) • planeCurvature u v := by
  refine ext_vec fun a b c d ↦ ?_
  simp only [smul_apply, planeCurvature_apply, real_inner_smul_left, smul_eq_mul]
  ring

/-- Scaling the second vector scales `planeCurvature` quadratically. -/
theorem planeCurvature_smul_right (u : V) (t : ℝ) (v : V) :
    planeCurvature u (t • v) = (t ^ 2) • planeCurvature u v := by
  rw [planeCurvature_comm, planeCurvature_smul_left, planeCurvature_comm]

/-- `planeCurvature` vanishes when its first vector is zero. -/
@[simp]
theorem planeCurvature_zero_left (v : V) : planeCurvature 0 v = 0 := by
  simpa using planeCurvature_smul_left 0 0 v

/-- `planeCurvature` vanishes when its second vector is zero. -/
@[simp]
theorem planeCurvature_zero_right (u : V) : planeCurvature u 0 = 0 := by
  simpa using planeCurvature_smul_right u 0 0

/-- Negating the first vector leaves `planeCurvature` unchanged. -/
@[simp]
theorem planeCurvature_neg_left (u v : V) : planeCurvature (-u) v = planeCurvature u v := by
  simpa using planeCurvature_smul_left (-1) u v

/-- Negating the second vector leaves `planeCurvature` unchanged. -/
@[simp]
theorem planeCurvature_neg_right (u v : V) : planeCurvature u (-v) = planeCurvature u v := by
  simpa using planeCurvature_smul_right u (-1) v

/-- For every pair `u, v`, `planeCurvature u v` is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_planeCurvature (u v : V) :
    IsAlgebraicCurvature (planeCurvature u v) := by
  refine ⟨fun a b c d ↦ ?_, fun a b c d ↦ ?_, fun a b c d ↦ ?_, fun a b c d ↦ ?_⟩ <;>
    simp only [planeCurvature_apply] <;> ring

/-- On repeated arguments `(a, b, a, b)`, `planeCurvature u v` is a square. -/
theorem planeCurvature_apply_self (u v a b : V) :
    planeCurvature u v ![a, b, a, b] = (⟪u, a⟫_ℝ * ⟪v, b⟫_ℝ - ⟪u, b⟫_ℝ * ⟪v, a⟫_ℝ) ^ 2 := by
  rw [planeCurvature_apply, sq]

/-- `planeCurvature u v` has nonnegative sectional values on every pair of vectors. -/
theorem planeCurvature_apply_self_nonneg (u v a b : V) :
    0 ≤ planeCurvature u v ![a, b, a, b] := by
  rw [planeCurvature_apply_self]
  exact sq_nonneg _

/-- Pulling `planeCurvature (f u) (f v)` back along a linear isometry `f` gives
`planeCurvature u v`. -/
@[simp]
theorem planeCurvature_compContinuousLinearMap_linearIsometry {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : W →ₗᵢ[ℝ] V) (u v : W) :
    (planeCurvature (f u) (f v)).compContinuousLinearMap (fun _ ↦ f.toContinuousLinearMap) =
      planeCurvature u v := by
  refine ext_vec fun a b c d ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

/-- Zero-extending `planeCurvature u v` from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` produces
`planeCurvature` of the included vectors `(u, 0)` and `(v, 0)`. -/
theorem planeCurvature_compContinuousLinearMap_fstL {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] (u v : V) :
    (planeCurvature u v).compContinuousLinearMap (fun _ ↦ WithLp.fstL 2 ℝ V U) =
      planeCurvature (WithLp.toLp 2 (u, 0)) (WithLp.toLp 2 (v, 0)) := by
  refine ext_vec fun a b c d ↦ ?_
  rw [compContinuousLinearMap_apply_vec]
  simp

variable [FiniteDimensional ℝ V]

/-- The Ricci contraction of `planeCurvature u v`. -/
theorem ricci_planeCurvature (u v x y : V) :
    ricci (planeCurvature u v) x y =
      ‖u‖ ^ 2 * ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ - ⟪u, v⟫_ℝ * (⟪u, x⟫_ℝ * ⟪v, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪u, y⟫_ℝ) +
        ‖v‖ ^ 2 * ⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ V
  rw [ricci_apply_orthonormalBasis b]
  have expand (i : Fin (Module.finrank ℝ V)) :
      planeCurvature u v ![b i, x, b i, y] =
        (⟪u, b i⟫_ℝ ^ 2) * (⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ) -
          (⟪u, b i⟫_ℝ * ⟪b i, v⟫_ℝ) * (⟪u, x⟫_ℝ * ⟪v, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪u, y⟫_ℝ) +
          (⟪v, b i⟫_ℝ ^ 2) * (⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ) := by
    rw [planeCurvature_apply, real_inner_comm (b i) v]
    ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    b.sum_sq_inner_left, b.sum_inner_mul_inner]
  ring

/-- For an orthonormal pair `u, v`, `ricci (planeCurvature u v)` is the orthogonal projection form
onto `span {u, v}`: `(x, y) ↦ ⟪u, x⟫ ⟪u, y⟫ + ⟪v, x⟫ ⟪v, y⟫`. -/
theorem ricci_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) (x y : V) :
    ricci (planeCurvature u v) x y = ⟪u, x⟫_ℝ * ⟪u, y⟫_ℝ + ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [ricci_planeCurvature, hu, hv, horth]
  ring

/-- The scalar contraction of `planeCurvature u v` is `2 (‖u‖² ‖v‖² - ⟪u, v⟫²)`. -/
theorem scalar_planeCurvature (u v : V) :
    scalar (planeCurvature u v) = 2 * constantCurvature V ![u, v, u, v] := by
  set b := stdOrthonormalBasis ℝ V
  rw [scalar_apply, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  have expand (i : Fin (Module.finrank ℝ V)) :
      ricci (planeCurvature u v) (b i) (b i) =
        ‖u‖ ^ 2 * ⟪v, b i⟫_ℝ ^ 2 - 2 * ⟪u, v⟫_ℝ * (⟪u, b i⟫_ℝ * ⟪b i, v⟫_ℝ) +
          ‖v‖ ^ 2 * ⟪u, b i⟫_ℝ ^ 2 := by
    rw [ricci_planeCurvature, real_inner_comm (b i) v]
    ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    b.sum_sq_inner_left, b.sum_inner_mul_inner, constantCurvature_apply_self]
  ring

/-- For an orthonormal pair `u, v`, `scalar (planeCurvature u v) = 2`. -/
theorem scalar_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    scalar (planeCurvature u v) = 2 := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have horth : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [scalar_planeCurvature, constantCurvature_apply_self, hu, hv, horth]
  ring

end PlaneCurvature

end FourTensor

end TauCeti
