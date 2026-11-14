/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import TauCeti.Analysis.InnerProductSpace.KulkarniNomizu
public import TauCeti.Topology.Algebra.Module.FiniteDimension

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
`TauCeti.bilinFormTrace`. This matches `Ric(u, v) = tr(w ↦ R(w, u)v)`.

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
Its Ricci contraction is `(n - 1) g` and its scalar contraction is `n (n - 1)`, and `κ` times it
is the four-tensor of every curvature operator satisfying `R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)`,
the identity recorded by `Bundle.RiemannianMetric.IsConstantCurvatureTensor`.

## Main definitions

* `TauCeti.FourTensor V`: continuous real four-linear forms on `V`.
* `TauCeti.FourTensor.IsAlgebraicCurvature`: the pair antisymmetries, pair interchange and the
  first Bianchi identity.
* `TauCeti.FourTensor.algebraicCurvatureSubmodule`: the submodule of algebraic curvature tensors.
* `TauCeti.FourTensor.ofLinearMap₄`: on a finite-dimensional space, the four-tensor of a curried
  four-linear form.
* `TauCeti.FourTensor.ricci` and `TauCeti.FourTensor.scalar`: the Ricci and scalar contractions.
* `TauCeti.FourTensor.kulkarniNomizu`: the Kulkarni–Nomizu product of two bilinear forms, as a
  four-tensor.
* `TauCeti.FourTensor.constantCurvature`: the constant-curvature tensor of curvature `1`.

## Main statements

* `TauCeti.FourTensor.isClosed_algebraicCurvatureSubmodule`: the submodule is closed.
* `TauCeti.FourTensor.IsAlgebraicCurvature.compContinuousLinearMap`: pullback preserves algebraic
  curvature tensors.
* `TauCeti.FourTensor.isAlgebraicCurvature_compContinuousLinearMap_iff` and
  `TauCeti.FourTensor.comap_compContinuousLinearMapL_algebraicCurvatureSubmodule`: a continuous
  linear equivalence identifies the algebraic curvature tensors of the two spaces.
* `TauCeti.FourTensor.ricci_apply_orthonormalBasis` and
  `TauCeti.FourTensor.scalar_apply_orthonormalBasis`: the contractions in an orthonormal basis.
* `TauCeti.FourTensor.ricci_compContinuousLinearMap_linearIsometryEquiv` and
  `TauCeti.FourTensor.scalar_compContinuousLinearMap_linearIsometryEquiv`: the contractions are
  equivariant under linear isometric equivalences.
* `TauCeti.FourTensor.ricci_kulkarniNomizu_innerₗ`: `Ric(h ⊙ g) = (n - 2) h + (tr h) g`.
* `TauCeti.FourTensor.constantCurvature_apply_self_pos_iff`: `r(u, v, u, v) > 0` for the
  constant-curvature tensor exactly on a linearly independent pair.
* `TauCeti.FourTensor.constantCurvature_compContinuousLinearMap_linearIsometry`: linear isometries
  pull the constant-curvature tensor back to the constant-curvature tensor.
* `TauCeti.FourTensor.ricci_constantCurvature` and `TauCeti.FourTensor.scalar_constantCurvature`.
* `TauCeti.FourTensor.inner_eq_mul_constantCurvature`: a curvature operator of constant curvature
  `κ` has four-tensor `κ` times the constant-curvature tensor.

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

section Update

variable {V : Type*}

private theorem update_zero (a b c d x : V) :
    Function.update ![a, b, c, d] 0 x = ![x, b, c, d] := by
  funext i; fin_cases i <;> rfl

private theorem update_one (a b c d x : V) :
    Function.update ![a, b, c, d] 1 x = ![a, x, c, d] := by
  funext i; fin_cases i <;> rfl

private theorem update_two (a b c d x : V) :
    Function.update ![a, b, c, d] 2 x = ![a, b, x, d] := by
  funext i; fin_cases i <;> rfl

private theorem update_three (a b c d x : V) :
    Function.update ![a, b, c, d] 3 x = ![a, b, c, x] := by
  funext i; fin_cases i <;> rfl

end Update

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

section Linearity

variable (r : FourTensor V) (a b c d x y : V) (t : ℝ)

/-- A four-tensor is additive in its first argument. -/
theorem apply_add_first : r ![x + y, b, c, d] = r ![x, b, c, d] + r ![y, b, c, d] := by
  simpa only [update_zero] using r.map_update_add ![x, b, c, d] 0 x y

/-- A four-tensor is additive in its second argument. -/
theorem apply_add_second : r ![a, x + y, c, d] = r ![a, x, c, d] + r ![a, y, c, d] := by
  simpa only [update_one] using r.map_update_add ![a, x, c, d] 1 x y

/-- A four-tensor is additive in its third argument. -/
theorem apply_add_third : r ![a, b, x + y, d] = r ![a, b, x, d] + r ![a, b, y, d] := by
  simpa only [update_two] using r.map_update_add ![a, b, x, d] 2 x y

/-- A four-tensor is additive in its fourth argument. -/
theorem apply_add_fourth : r ![a, b, c, x + y] = r ![a, b, c, x] + r ![a, b, c, y] := by
  simpa only [update_three] using r.map_update_add ![a, b, c, x] 3 x y

/-- A four-tensor is homogeneous in its first argument. -/
theorem apply_smul_first : r ![t • x, b, c, d] = t * r ![x, b, c, d] := by
  simpa only [update_zero, smul_eq_mul] using r.map_update_smul ![x, b, c, d] 0 t x

/-- A four-tensor is homogeneous in its second argument. -/
theorem apply_smul_second : r ![a, t • x, c, d] = t * r ![a, x, c, d] := by
  simpa only [update_one, smul_eq_mul] using r.map_update_smul ![a, x, c, d] 1 t x

/-- A four-tensor is homogeneous in its third argument. -/
theorem apply_smul_third : r ![a, b, t • x, d] = t * r ![a, b, x, d] := by
  simpa only [update_two, smul_eq_mul] using r.map_update_smul ![a, b, x, d] 2 t x

/-- A four-tensor is homogeneous in its fourth argument. -/
theorem apply_smul_fourth : r ![a, b, c, t • x] = t * r ![a, b, c, x] := by
  simpa only [update_three, smul_eq_mul] using r.map_update_smul ![a, b, c, x] 3 t x

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
    exact ⟨fun h ↦ ⟨⟨⟨h.1, h.2⟩, h.3⟩, h.4⟩, fun h ↦ ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [this]
  refine ((IsClosed.inter (IsClosed.inter ?_ ?_) ?_).inter ?_) <;>
    refine isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun z ↦
      isClosed_iInter fun w ↦ isClosed_eq ?_ ?_ <;>
    fun_prop

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

/-- The bilinear form `(x, y) ↦ r(x, u, y, v)` whose metric trace is the Ricci contraction. -/
private def ricciSlice (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![x, u, y, v])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)

private theorem ricciSlice_apply (r : FourTensor V) (u v x y : V) :
    ricciSlice r u v x y = r ![x, u, y, v] :=
  (rfl)

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

/-- The Kulkarni–Nomizu product of two symmetric bilinear forms is an algebraic curvature
tensor. -/
theorem isAlgebraicCurvature_kulkarniNomizu {h k : BilinForm ℝ V} (hh : h.IsSymm)
    (hk : k.IsSymm) : IsAlgebraicCurvature (kulkarniNomizu h k) := by
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [kulkarniNomizu_apply_eq]
  · exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first h k u v w z
  · exact LinearMap.BilinForm.kulkarniNomizu_antisymm_last h k u v w z
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
  toFun r := LinearMap.mk₂ ℝ (fun u v ↦ bilinFormTrace (ricciSlice r u v))
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; ext; exact apply_add_second ..)
    (fun _ _ _ ↦ by rw [← map_smul]; congr 1; ext; exact apply_smul_second ..)
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; ext; exact apply_add_fourth ..)
    (fun _ _ _ ↦ by rw [← map_smul]; congr 1; ext; exact apply_smul_fourth ..)
  map_add' r q := by
    ext u v
    simp only [LinearMap.mk₂_apply, LinearMap.add_apply]
    rw [← map_add]
    -- `ricciSlice` is additive in the tensor by its definition.
    rfl
  map_smul' c r := by
    ext u v
    simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    -- `ricciSlice` is homogeneous in the tensor by its definition.
    rfl

/-- In every orthonormal basis `(eᵢ)`, the Ricci contraction is `∑ᵢ r(eᵢ, u, eᵢ, v)`. -/
theorem ricci_apply_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v : V) : ricci r u v = ∑ i, r ![b i, u, b i, v] :=
  bilinFormTrace_eq_sum (ricciSlice r u v) b

/-- The Ricci contraction of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_ricci {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (ricci r).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  simp only [ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_congr rfl fun i _ ↦ (hr.swap_pairs _ _ _ _).symm

/-- The Ricci contraction is equivariant under linear isometric equivalences: the Ricci contraction
of the pullback of `r` by `e` is the pullback of the Ricci contraction of `r`. -/
theorem ricci_compContinuousLinearMap_linearIsometryEquiv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V)
    (u v : W) :
    ricci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      ricci r (e u) (e v) := by
  let b := stdOrthonormalBasis ℝ W
  rw [ricci_apply_orthonormalBasis b, ricci_apply_orthonormalBasis (b.map e)]
  simp only [compContinuousLinearMap_apply_vec, OrthonormalBasis.map_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- The scalar contraction of a four-tensor: the metric trace of its Ricci contraction. -/
def scalar : FourTensor V →ₗ[ℝ] ℝ :=
  bilinFormTrace ∘ₗ ricci

/-- The scalar contraction is the metric trace of the Ricci contraction. -/
theorem scalar_apply (r : FourTensor V) : scalar r = bilinFormTrace (ricci r) :=
  (rfl)

/-- In every orthonormal basis `(eᵢ)`, the scalar contraction is `∑ᵢ ∑ⱼ r(eᵢ, eⱼ, eᵢ, eⱼ)`. -/
theorem scalar_apply_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) : scalar r = ∑ j, ∑ i, r ![b i, b j, b i, b j] := by
  simp only [scalar_apply, bilinFormTrace_eq_sum _ b, ricci_apply_orthonormalBasis b]

/-- The scalar contraction is invariant under linear isometric equivalences. -/
theorem scalar_compContinuousLinearMap_linearIsometryEquiv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    scalar (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      scalar r := by
  let b := stdOrthonormalBasis ℝ W
  rw [scalar_apply_orthonormalBasis b, scalar_apply_orthonormalBasis (b.map e)]
  simp only [compContinuousLinearMap_apply_vec, OrthonormalBasis.map_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- The Ricci contraction of the Kulkarni–Nomizu product of `h` with the inner product:
`Ric(h ⊙ g) = (n - 2) h + (tr h) g`. -/
theorem ricci_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    ricci (kulkarniNomizu h (innerₗ V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • h + bilinFormTrace h • innerₗ V := by
  ext u v
  rw [ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  simp only [kulkarniNomizu_apply_eq, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    innerₗ_apply_apply]
  exact LinearMap.BilinForm.sum_kulkarniNomizu_innerₗ h _ u v

/-- The scalar contraction of the Kulkarni–Nomizu product of `h` with the inner product:
`Scal(h ⊙ g) = 2 (n - 1) tr h`. -/
theorem scalar_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    scalar (kulkarniNomizu h (innerₗ V)) =
      2 * ((Module.finrank ℝ V : ℝ) - 1) * bilinFormTrace h := by
  rw [scalar_apply, ricci_kulkarniNomizu_innerₗ, map_add, map_smul, map_smul,
    bilinFormTrace_inner, smul_eq_mul, smul_eq_mul]
  ring

variable (V) in
/-- The constant-curvature tensor of curvature `1`,
`r(u, v, z, w) = ⟪u, z⟫ ⟪v, w⟫ - ⟪u, w⟫ ⟪v, z⟫`: half the Kulkarni–Nomizu product of the inner
product with itself. It is the curvature four-tensor of the unit sphere, and `κ` times it is the
curvature four-tensor of a space of constant sectional curvature `κ`. -/
def constantCurvature : FourTensor V :=
  (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V)

/-- Evaluation of the constant-curvature tensor. -/
@[simp]
theorem constantCurvature_apply (u v z w : V) :
    constantCurvature V ![u, v, z, w] = ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ := by
  simp only [constantCurvature, smul_apply, kulkarniNomizu_apply,
    innerₗ_apply_apply, smul_eq_mul]
  ring

/-- The constant-curvature tensor is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_constantCurvature : IsAlgebraicCurvature (constantCurvature V) :=
  have hg : LinearMap.BilinForm.IsSymm (innerₗ V) := ⟨fun v w ↦ real_inner_comm w v⟩
  Submodule.smul_mem (algebraicCurvatureSubmodule V) _
    (isAlgebraicCurvature_kulkarniNomizu hg hg)

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
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec]
  simp

/-- The Ricci contraction of the constant-curvature tensor is `(n - 1) g`. -/
theorem ricci_constantCurvature :
    ricci (constantCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • innerₗ V := by
  rw [constantCurvature, map_smul, ricci_kulkarniNomizu_innerₗ, bilinFormTrace_inner, ← add_smul,
    smul_smul]
  congr 1
  ring

/-- The scalar contraction of the constant-curvature tensor is `n (n - 1)`. -/
theorem scalar_constantCurvature :
    scalar (constantCurvature V) = Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1) := by
  rw [constantCurvature, map_smul, scalar_kulkarniNomizu_innerₗ, bilinFormTrace_inner,
    smul_eq_mul]
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

end InnerProductSpace

end FourTensor

end TauCeti
