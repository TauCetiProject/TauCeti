/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Algebra.Order.Star.Real
public import TauCeti.Analysis.InnerProductSpace.Gram.Pair
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.LinearAlgebra.BilinearForm.KulkarniNomizu

/-!
# Algebraic curvature tensors

A *four-tensor* on a real normed space `V` is a continuous four-linear form on `V`. With the
convention `r(u, v, z, w) = g(R(u, v)w, z)` for the curvature `R` of a Riemannian metric `g`, the
four-tensor `r` is antisymmetric in its first and in its last pair of arguments, symmetric under
interchanging the two pairs, and satisfies the first Bianchi identity
`r(u, v, z, w) + r(v, z, u, w) + r(z, u, v, w) = 0`. A four-tensor with these symmetries is an
*algebraic curvature tensor*. In this convention `r(u, v, u, v)` is the numerator of the sectional
curvature of the plane spanned by `u` and `v`, positive on the round sphere.

The algebraic curvature tensors form a closed subspace of the four-tensors. They are the
fibrewise objects on which pointwise curvature conditions (curvature cones, pinching) and the
reaction term of the curvature evolution under Ricci flow are stated, after identifying a tangent
space with a fixed model space by a linear isometry. This file sets up the carrier and its basic
structure:

* the pullback of four-tensors along continuous linear maps, which preserves algebraic curvature
  tensors, so a linear isometry identifies the algebraic curvature tensors of two spaces;
* the constant-curvature tensor `(u, v, z, w) ↦ ⟪u, z⟫⟪v, w⟫ - ⟪u, w⟫⟪v, z⟫`, half the
  Kulkarni–Nomizu square of the inner product, whose value on `(u, v, u, v)` is the Gram
  determinant of `u, v`, so that it has sectional curvature one;
* the Ricci contraction `Ric(u, v) = ∑ᵢ r(eᵢ, u, eᵢ, v)` and the scalar contraction, computed in
  any orthonormal basis `(eᵢ)`, and their values `(n - 1) g` and `n (n - 1)` on the
  constant-curvature tensor in dimension `n`.

## Main definitions

* `TauCeti.FourTensor V`: the continuous four-linear forms on `V`.
* `TauCeti.FourTensor.IsAlgebraicCurvature`: the curvature symmetries of a four-tensor.
* `TauCeti.algebraicCurvatureSubmodule V`: the subspace of algebraic curvature tensors.
* `TauCeti.FourTensor.pullback`: pulling a four-tensor back along a continuous linear map.
* `TauCeti.FourTensor.constCurvature V`: the algebraic curvature tensor of constant sectional
  curvature one.
* `TauCeti.FourTensor.ricciTensor` and `TauCeti.FourTensor.scalarCurvature`: the Ricci and scalar
  contractions.

## Main results

* `TauCeti.isClosed_algebraicCurvatureSubmodule`: the algebraic curvature tensors form a closed
  subspace.
* `TauCeti.FourTensor.isAlgebraicCurvature_pullback_iff`: pulling back along a continuous linear
  equivalence preserves and reflects the curvature symmetries.
* `TauCeti.FourTensor.constCurvature_apply_self_pos_iff`: the constant-curvature tensor is positive
  on `(u, v, u, v)` exactly for linearly independent `u, v`.
* `TauCeti.FourTensor.ricciTensor_apply` and `TauCeti.FourTensor.scalarCurvature_eq_sum`: the
  contractions in an arbitrary orthonormal basis.
* `TauCeti.FourTensor.ricciTensor_pullback`: the Ricci contraction is natural under linear
  isometries.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (with the last two arguments of the four-tensor exchanged).
-/

public section

noncomputable section

open LinearMap (BilinForm)
open scoped InnerProductSpace

namespace TauCeti

/-- The continuous four-linear forms on a real normed space `V`, the carrier of algebraic
curvature tensors. -/
abbrev FourTensor (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 4 => V) ℝ

namespace FourTensor

/-- Replacing the `i`-th entry of `![a, b, c, d]`, written out for the four positions. -/
private theorem update_vecCons {α : Type*} (a b c d x : α) :
    Function.update ![a, b, c, d] 0 x = ![x, b, c, d] ∧
      Function.update ![a, b, c, d] 1 x = ![a, x, c, d] ∧
      Function.update ![a, b, c, d] 2 x = ![a, b, x, d] ∧
      Function.update ![a, b, c, d] 3 x = ![a, b, c, x] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Linearity in each argument -/

section Linearity

variable (r : FourTensor V) (a b c d x y : V) (t : ℝ)

private theorem apply_add_first : r ![x + y, b, c, d] = r ![x, b, c, d] + r ![y, b, c, d] := by
  simpa only [(update_vecCons x b c d _).1] using r.map_update_add ![x, b, c, d] 0 x y

private theorem apply_add_second : r ![a, x + y, c, d] = r ![a, x, c, d] + r ![a, y, c, d] := by
  simpa only [(update_vecCons a x c d _).2.1] using r.map_update_add ![a, x, c, d] 1 x y

private theorem apply_add_third : r ![a, b, x + y, d] = r ![a, b, x, d] + r ![a, b, y, d] := by
  simpa only [(update_vecCons a b x d _).2.2.1] using r.map_update_add ![a, b, x, d] 2 x y

private theorem apply_add_fourth : r ![a, b, c, x + y] = r ![a, b, c, x] + r ![a, b, c, y] := by
  simpa only [(update_vecCons a b c x _).2.2.2] using r.map_update_add ![a, b, c, x] 3 x y

private theorem apply_smul_first : r ![t • x, b, c, d] = t * r ![x, b, c, d] := by
  simpa only [(update_vecCons x b c d _).1, smul_eq_mul] using
    r.map_update_smul ![x, b, c, d] 0 t x

private theorem apply_smul_second : r ![a, t • x, c, d] = t * r ![a, x, c, d] := by
  simpa only [(update_vecCons a x c d _).2.1, smul_eq_mul] using
    r.map_update_smul ![a, x, c, d] 1 t x

private theorem apply_smul_third : r ![a, b, t • x, d] = t * r ![a, b, x, d] := by
  simpa only [(update_vecCons a b x d _).2.2.1, smul_eq_mul] using
    r.map_update_smul ![a, b, x, d] 2 t x

private theorem apply_smul_fourth : r ![a, b, c, t • x] = t * r ![a, b, c, x] := by
  simpa only [(update_vecCons a b c x _).2.2.2, smul_eq_mul] using
    r.map_update_smul ![a, b, c, x] 3 t x

end Linearity

/-! ### The curvature symmetries -/

/-- A four-tensor `r` is an *algebraic curvature tensor* when it has the symmetries of
`r(u, v, z, w) = g(R(u, v)w, z)` for the curvature `R` of a Riemannian metric `g`: it is
antisymmetric in its first and in its last pair of arguments, symmetric under interchanging the
two pairs, and satisfies the first Bianchi identity. -/
structure IsAlgebraicCurvature (r : FourTensor V) : Prop where
  /-- Antisymmetry in the first pair of arguments. -/
  antisymm_first : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]
  /-- Antisymmetry in the last pair of arguments. -/
  antisymm_last : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]
  /-- Symmetry under interchanging the two pairs of arguments. -/
  swap_pairs : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]
  /-- The first Bianchi identity. -/
  bianchi : ∀ u v z w, r ![u, v, z, w] + r ![v, z, u, w] + r ![z, u, v, w] = 0

end FourTensor

open FourTensor

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The subspace of algebraic curvature tensors on `V`. -/
def algebraicCurvatureSubmodule : Submodule ℝ (FourTensor V) where
  carrier := {r | r.IsAlgebraicCurvature}
  zero_mem' := ⟨by simp, by simp, by simp, by simp⟩
  add_mem' {r q} hr hq := by
    refine ⟨fun u v z w => ?_, fun u v z w => ?_, fun u v z w => ?_, fun u v z w => ?_⟩
    · rw [add_apply, add_apply, hr.antisymm_first u v z w, hq.antisymm_first u v z w]
      ring
    · rw [add_apply, add_apply, hr.antisymm_last u v z w, hq.antisymm_last u v z w]
      ring
    · rw [add_apply, add_apply, hr.swap_pairs u v z w, hq.swap_pairs u v z w]
    · simp only [add_apply]
      linear_combination hr.bianchi u v z w + hq.bianchi u v z w
  smul_mem' t {r} hr := by
    refine ⟨fun u v z w => ?_, fun u v z w => ?_, fun u v z w => ?_, fun u v z w => ?_⟩
    · rw [smul_apply, smul_apply, hr.antisymm_first u v z w, smul_eq_mul, smul_eq_mul]
      ring
    · rw [smul_apply, smul_apply, hr.antisymm_last u v z w, smul_eq_mul, smul_eq_mul]
      ring
    · rw [smul_apply, smul_apply, hr.swap_pairs u v z w]
    · simp only [smul_apply, smul_eq_mul]
      linear_combination t * hr.bianchi u v z w

variable {V}

/-- Membership in `algebraicCurvatureSubmodule V` is the curvature-symmetry predicate. -/
@[simp]
theorem mem_algebraicCurvatureSubmodule {r : FourTensor V} :
    r ∈ algebraicCurvatureSubmodule V ↔ r.IsAlgebraicCurvature :=
  Iff.rfl

variable (V) in
/-- The algebraic curvature tensors form a closed subspace of the four-tensors: each curvature
symmetry is an equation between evaluations, which are continuous in the tensor. -/
theorem isClosed_algebraicCurvatureSubmodule :
    IsClosed (algebraicCurvatureSubmodule V : Set (FourTensor V)) := by
  have hev (m : Fin 4 → V) : Continuous fun r : FourTensor V => r m := continuous_eval_const m
  have hset : (algebraicCurvatureSubmodule V : Set (FourTensor V)) =
      ⋂ u : V, ⋂ v : V, ⋂ z : V, ⋂ w : V,
        ({r | r ![u, v, z, w] = -r ![v, u, z, w]} ∩ {r | r ![u, v, z, w] = -r ![u, v, w, z]} ∩
          {r | r ![u, v, z, w] = r ![z, w, u, v]} ∩
          {r | r ![u, v, z, w] + r ![v, z, u, w] + r ![z, u, v, w] = 0}) := by
    ext r
    simp only [SetLike.mem_coe, mem_algebraicCurvatureSubmodule, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun h u v z w => ⟨⟨⟨h.1 u v z w, h.2 u v z w⟩, h.3 u v z w⟩, h.4 u v z w⟩,
      fun h => ⟨fun u v z w => (h u v z w).1.1.1, fun u v z w => (h u v z w).1.1.2,
        fun u v z w => (h u v z w).1.2, fun u v z w => (h u v z w).2⟩⟩
  rw [hset]
  refine isClosed_iInter fun u => isClosed_iInter fun v => isClosed_iInter fun z =>
    isClosed_iInter fun w => ?_
  exact (((isClosed_eq (hev _) (hev _).neg).inter (isClosed_eq (hev _) (hev _).neg)).inter
    (isClosed_eq (hev _) (hev _))).inter
    (isClosed_eq (((hev _).add (hev _)).add (hev _)) continuous_const)

namespace FourTensor

variable {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Pullback along continuous linear maps -/

/-- The pullback `(f^* r)(u, v, z, w) = r(f u, f v, f z, f w)` of four-tensors along a continuous
linear map `f`. -/
def pullback (f : W →L[ℝ] V) : FourTensor V →L[ℝ] FourTensor W :=
  ContinuousMultilinearMap.compContinuousLinearMapL fun _ => f

/-- Evaluation of the pullback. -/
@[simp]
theorem pullback_apply (f : W →L[ℝ] V) (r : FourTensor V) (m : Fin 4 → W) :
    pullback f r m = r (fun i => f (m i)) :=
  (rfl)

/-- The pullback evaluated on four explicit vectors. -/
theorem pullback_apply_vecCons (f : W →L[ℝ] V) (r : FourTensor V) (u v z w : W) :
    pullback f r ![u, v, z, w] = r ![f u, f v, f z, f w] := by
  rw [pullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem pullback_id (r : FourTensor V) : pullback (ContinuousLinearMap.id ℝ V) r = r := by
  ext m
  simp

/-- Pulling back along a composition is pulling back twice. -/
theorem pullback_comp (f : X →L[ℝ] W) (g : W →L[ℝ] V) (r : FourTensor V) :
    pullback (g.comp f) r = pullback f (pullback g r) := by
  ext m
  simp

/-- The pullback of an algebraic curvature tensor is an algebraic curvature tensor. -/
theorem IsAlgebraicCurvature.pullback {r : FourTensor V} (hr : r.IsAlgebraicCurvature)
    (f : W →L[ℝ] V) : (pullback f r).IsAlgebraicCurvature where
  antisymm_first u v z w := by
    rw [pullback_apply_vecCons, pullback_apply_vecCons, hr.antisymm_first]
  antisymm_last u v z w := by
    rw [pullback_apply_vecCons, pullback_apply_vecCons, hr.antisymm_last]
  swap_pairs u v z w := by
    rw [pullback_apply_vecCons, pullback_apply_vecCons, hr.swap_pairs]
  bianchi u v z w := by
    simpa only [pullback_apply_vecCons] using hr.bianchi (f u) (f v) (f z) (f w)

/-- Pulling back along a continuous linear equivalence preserves and reflects the curvature
symmetries. In particular a linear isometry `V ≃ₗᵢ[ℝ] T` identifies the algebraic curvature
tensors on a tangent space `T` with those on the model space `V`. -/
theorem isAlgebraicCurvature_pullback_iff (e : W ≃L[ℝ] V) {r : FourTensor V} :
    (pullback (e : W →L[ℝ] V) r).IsAlgebraicCurvature ↔ r.IsAlgebraicCurvature := by
  refine ⟨fun h => ?_, fun h => h.pullback _⟩
  have := h.pullback (e.symm : V →L[ℝ] W)
  rwa [← pullback_comp, e.coe_comp_coe_symm, pullback_id] at this

/-- A continuous linear equivalence `e : W ≃L[ℝ] V` identifies the algebraic curvature tensors on
`V` with those on `W`: they are exactly the four-tensors whose pullback along `e` is one. -/
theorem comap_pullback_algebraicCurvatureSubmodule (e : W ≃L[ℝ] V) :
    (algebraicCurvatureSubmodule W).comap (pullback (e : W →L[ℝ] V) : FourTensor V →ₗ[ℝ] _) =
      algebraicCurvatureSubmodule V := by
  ext r
  exact isAlgebraicCurvature_pullback_iff e

/-! ### The constant-curvature tensor -/

section Inner

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable (V) in
/-- The algebraic curvature tensor of constant sectional curvature one,
`(u, v, z, w) ↦ ⟪u, z⟫⟪v, w⟫ - ⟪u, w⟫⟪v, z⟫`: the curvature four-tensor of the unit sphere. -/
def constCurvature : FourTensor V :=
  MultilinearMap.mkContinuous
    { toFun m := ⟪m 0, m 2⟫_ℝ * ⟪m 1, m 3⟫_ℝ - ⟪m 0, m 3⟫_ℝ * ⟪m 1, m 2⟫_ℝ
      -- The constructor quantifies over every `DecidableEq (Fin 4)` instance; replace it by the
      -- canonical one, on which `Function.update` at a numeral position computes.
      map_update_add' {_} m i x y := by
        obtain rfl : ‹DecidableEq (Fin 4)› = instDecidableEqFin 4 := Subsingleton.elim _ _
        fin_cases i <;> simp [inner_add_left, inner_add_right] <;> ring
      map_update_smul' {_} m i t x := by
        obtain rfl : ‹DecidableEq (Fin 4)› = instDecidableEqFin 4 := Subsingleton.elim _ _
        fin_cases i <;> simp [real_inner_smul_left, real_inner_smul_right] <;> ring }
    2 fun m => by
      simp only [MultilinearMap.coe_mk, Real.norm_eq_abs, Fin.prod_univ_four]
      have h (i j : Fin 4) : |⟪m i, m j⟫_ℝ| ≤ ‖m i‖ * ‖m j‖ := abs_real_inner_le_norm _ _
      calc |⟪m 0, m 2⟫_ℝ * ⟪m 1, m 3⟫_ℝ - ⟪m 0, m 3⟫_ℝ * ⟪m 1, m 2⟫_ℝ|
          ≤ |⟪m 0, m 2⟫_ℝ| * |⟪m 1, m 3⟫_ℝ| + |⟪m 0, m 3⟫_ℝ| * |⟪m 1, m 2⟫_ℝ| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_sub _ _
        _ ≤ ‖m 0‖ * ‖m 2‖ * (‖m 1‖ * ‖m 3‖) + ‖m 0‖ * ‖m 3‖ * (‖m 1‖ * ‖m 2‖) := by
            gcongr <;> exact h _ _
        _ = 2 * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by ring

/-- Evaluation of the constant-curvature tensor. -/
@[simp]
theorem constCurvature_apply (u v z w : V) :
    constCurvature V ![u, v, z, w] = ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ :=
  (rfl)

/-- The constant-curvature tensor is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_constCurvature : (constCurvature V).IsAlgebraicCurvature where
  antisymm_first u v z w := by simp only [constCurvature_apply]; ring
  antisymm_last u v z w := by simp only [constCurvature_apply]; ring
  swap_pairs u v z w := by
    simp only [constCurvature_apply, real_inner_comm u z, real_inner_comm v w,
      real_inner_comm u w, real_inner_comm v z]
    ring
  bianchi u v z w := by
    simp only [constCurvature_apply, real_inner_comm u v, real_inner_comm z u,
      real_inner_comm z v]
    ring

/-- The constant-curvature tensor is half the Kulkarni–Nomizu square `g ⊙ g` of the inner
product, read with its last two arguments exchanged: the Kulkarni–Nomizu product is written in
the convention `Rm(x, y, z, w) = ⟪R(x, y)z, w⟫`, while `r(u, v, z, w) = ⟪R(u, v)w, z⟫`. -/
theorem constCurvature_apply_eq_kulkarniNomizu (u v z w : V) :
    constCurvature V ![u, v, z, w] =
      BilinForm.kulkarniNomizu (innerₗ V) (innerₗ V) u v w z / 2 := by
  simp only [constCurvature_apply, BilinForm.kulkarniNomizu_apply, innerₗ_apply_apply]
  ring

/-- The constant-curvature tensor on `(u, v, u, v)` is the Gram determinant of `u, v`, the
squared area of the parallelogram they span: its sectional curvature is one. -/
theorem constCurvature_apply_self (u v : V) :
    constCurvature V ![u, v, u, v] = (Matrix.gram ℝ ![u, v]).det := by
  rw [constCurvature_apply, Matrix.real_det_gram_fin_two, real_inner_comm v u]
  ring

/-- The constant-curvature tensor is positive on `(u, v, u, v)` exactly when `u` and `v` are
linearly independent. -/
theorem constCurvature_apply_self_pos_iff {u v : V} :
    0 < constCurvature V ![u, v, u, v] ↔ LinearIndependent ℝ ![u, v] := by
  rw [constCurvature_apply_self, ← Matrix.posDef_gram_iff_linearIndependent]
  refine ⟨fun h => (Matrix.posSemidef_gram ℝ ![u, v]).posDef_iff_det_ne_zero.mpr h.ne',
    fun h => h.det_pos⟩

/-- A linear isometry pulls the constant-curvature tensor back to the constant-curvature
tensor. -/
@[simp]
theorem pullback_constCurvature (f : W →ₗᵢ[ℝ] V) :
    pullback f.toContinuousLinearMap (constCurvature V) = constCurvature W := by
  ext m
  simp [constCurvature]

end Inner

/-! ### Ricci and scalar contractions -/

section Contraction

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The bilinear form `(x, y) ↦ r(x, u, y, v)`, whose metric trace is the Ricci contraction. -/
private def ricciTensorIntegrand (r : FourTensor V) : V →ₗ[ℝ] V →ₗ[ℝ] BilinForm ℝ V :=
  LinearMap.mk₂ ℝ
    (fun u v => LinearMap.mk₂ ℝ (fun x y => r ![x, u, y, v])
      (fun _ _ _ => apply_add_first ..) (fun _ _ _ => apply_smul_first ..)
      (fun _ _ _ => apply_add_third ..) (fun _ _ _ => apply_smul_third ..))
    (fun _ _ _ => by ext; exact apply_add_second ..)
    (fun _ _ _ => by ext; exact apply_smul_second ..)
    (fun _ _ _ => by ext; exact apply_add_fourth ..)
    (fun _ _ _ => by ext; exact apply_smul_fourth ..)

/-- The Ricci contraction `Ric(u, v) = ∑ᵢ r(eᵢ, u, eᵢ, v)` of a four-tensor, the metric trace of
`(x, y) ↦ r(x, u, y, v)`. For the curvature four-tensor of a metric it is the Ricci tensor
`Ric(u, v) = tr(w ↦ R(w, u)v)`. -/
def ricciTensor : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := (ricciTensorIntegrand r).compr₂ bilinFormTrace
  map_add' r q := by
    ext u v
    simp [ricciTensorIntegrand, bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V),
      Finset.sum_add_distrib]
  map_smul' t r := by
    ext u v
    simp [ricciTensorIntegrand, bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V),
      Finset.mul_sum]

/-- The Ricci contraction in an arbitrary orthonormal basis. -/
theorem ricciTensor_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v : V) : ricciTensor r u v = ∑ i, r ![b i, u, b i, v] := by
  simp [ricciTensor, ricciTensorIntegrand, bilinFormTrace_eq_sum _ b]

/-- The Ricci contraction of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_ricciTensor {r : FourTensor V}
    (hr : r.IsAlgebraicCurvature) : (ricciTensor r).IsSymm := by
  refine ⟨fun u v => ?_⟩
  simp only [ricciTensor_apply (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_congr rfl fun i _ => hr.swap_pairs _ _ _ _

/-- The Ricci contraction is natural under linear isometries. -/
theorem ricciTensor_pullback (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) (u v : W) :
    ricciTensor (pullback (e : W →L[ℝ] V) r) u v = ricciTensor r (e u) (e v) := by
  let b := stdOrthonormalBasis ℝ W
  rw [ricciTensor_apply b, ricciTensor_apply (b.map e)]
  simp only [pullback_apply_vecCons, OrthonormalBasis.map_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The scalar contraction `Scal = ∑ᵢ Ric(eᵢ, eᵢ)` of a four-tensor, the metric trace of its
Ricci contraction. -/
def scalarCurvature : FourTensor V →ₗ[ℝ] ℝ :=
  bilinFormTrace ∘ₗ ricciTensor

/-- The scalar contraction in an arbitrary orthonormal basis. -/
theorem scalarCurvature_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) : scalarCurvature r = ∑ i, ∑ j, r ![b i, b j, b i, b j] := by
  simp only [scalarCurvature, LinearMap.comp_apply, bilinFormTrace_eq_sum _ b,
    ricciTensor_apply b]
  exact Finset.sum_comm

/-- The scalar contraction is invariant under linear isometries. -/
theorem scalarCurvature_pullback (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    scalarCurvature (pullback (e : W →L[ℝ] V) r) = scalarCurvature r := by
  let b := stdOrthonormalBasis ℝ W
  rw [scalarCurvature_eq_sum b, scalarCurvature_eq_sum (b.map e)]
  simp only [pullback_apply_vecCons, OrthonormalBasis.map_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The Ricci contraction of the constant-curvature tensor in dimension `n` is `(n - 1) g`. -/
theorem ricciTensor_constCurvature :
    ricciTensor (constCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • innerₗ V := by
  let b := stdOrthonormalBasis ℝ V
  have hu (u v : V) : ∑ i, ⟪b i, v⟫_ℝ * ⟪u, b i⟫_ℝ = ⟪u, v⟫_ℝ := by
    rw [← b.sum_inner_mul_inner u v]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  ext u v
  rw [ricciTensor_apply b]
  simp [Finset.sum_sub_distrib, hu]
  ring

/-- The scalar contraction of the constant-curvature tensor in dimension `n` is `n (n - 1)`. -/
theorem scalarCurvature_constCurvature :
    scalarCurvature (constCurvature V) = Module.finrank ℝ V * (Module.finrank ℝ V - 1) := by
  rw [scalarCurvature, LinearMap.comp_apply, ricciTensor_constCurvature, map_smul,
    bilinFormTrace_inner, smul_eq_mul, mul_comm]

end Contraction

end FourTensor

end TauCeti
