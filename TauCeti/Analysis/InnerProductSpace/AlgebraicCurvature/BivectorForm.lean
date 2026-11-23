/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
import Mathlib.Data.Fin.Tuple.Reflection
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Bilinear
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Bilinear forms on the exterior square and bivector-symmetric four-tensors

On a finite-dimensional real normed space `V`, `TauCeti.FourTensor.ofExteriorSquareBilin` pulls a
bilinear form `B` on `⋀[ℝ]^2 V` back to the pair-antisymmetric four-tensor
`ofExteriorSquareBilin B ![u, v, z, w] = B (u ∧ v) (z ∧ w)`.

This map is an injective linear embedding whose range is the space of pair-antisymmetric
four-tensors, and `ofExteriorSquareBilin B` is bivector-symmetric if and only if `B` is symmetric,
yielding the linear equivalence `TauCeti.FourTensor.bivectorSymmetricEquivSymmBilin` between
`bivectorSymmetricSubmodule V` and `LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)`. Pulling
`ofExteriorSquareBilin B` back along a continuous linear map `f : W →L[ℝ] V` precomposes both
slots of `B` with `exteriorPower.map 2 f.toLinearMap`.

## Main definitions

* `TauCeti.FourTensor.ofExteriorSquareBilin`: pullback of a bilinear form on `⋀[ℝ]^2 V` to
  `FourTensor V`.
* `TauCeti.FourTensor.bivectorSymmetricEquivSymmBilin`: linear equivalence between
  `bivectorSymmetricSubmodule V` and `LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)`.

## Main results

* `TauCeti.FourTensor.ofExteriorSquareBilin_apply`,
  `TauCeti.FourTensor.ofExteriorSquareBilin_antisymm_first`,
  `TauCeti.FourTensor.ofExteriorSquareBilin_antisymm_last`,
  `TauCeti.FourTensor.ofExteriorSquareBilin_injective`,
  `TauCeti.FourTensor.mem_range_ofExteriorSquareBilin_iff`,
  `TauCeti.FourTensor.isBivectorSymmetric_ofExteriorSquareBilin_iff`,
  `TauCeti.FourTensor.bivectorSymmetricEquivSymmBilin_apply_ιMulti`,
  `TauCeti.FourTensor.bivectorSymmetricEquivSymmBilin_symm_apply`, and
  `ContinuousLinearMap.ofExteriorSquareBilin_compContinuousLinearMap`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

open LinearMap (BilinForm)

noncomputable section

namespace TauCeti.FourTensor

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem isBivectorSymmetric_self_first {r : FourTensor V} (hr : IsBivectorSymmetric r)
    (x z w : V) : r ![x, x, z, w] = 0 := CharZero.eq_neg_self_iff.mp (hr.antisymm_first x x z w)

private theorem isBivectorSymmetric_self_last {r : FourTensor V} (hr : IsBivectorSymmetric r)
    (u v z : V) : r ![u, v, z, z] = 0 := CharZero.eq_neg_self_iff.mp (hr.antisymm_last u v z z)

private theorem isBivectorSymmetric_toLinearMap₄_isAlt {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (u v : V) : (toLinearMap₄ r u v).IsAlt := fun z ↦ by
  rw [toLinearMap₄_apply]; exact isBivectorSymmetric_self_last hr u v z

private def exteriorBilinOfBivectorSymmetric (r : bivectorSymmetricSubmodule V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  let hr := mem_bivectorSymmetricSubmodule.mp r.property
  (toLinearMap₄ r.val).exteriorSquareBilinear
    (fun _ _ _ ↦ by rw [toLinearMap₄_apply]; exact isBivectorSymmetric_self_first hr ..)
    (isBivectorSymmetric_toLinearMap₄_isAlt hr)

private theorem isSymm_exteriorBilinOfBivectorSymmetric (r : bivectorSymmetricSubmodule V) :
    (exteriorBilinOfBivectorSymmetric r).IsSymm :=
  ⟨fun a b ↦ (LinearMap.congr_fun₂ (LinearMap.flip_exteriorSquareBilinear (toLinearMap₄ r.val) _ _
    (fun _ _ _ _ ↦ by
      simpa only [toLinearMap₄_apply] using
        (mem_bivectorSymmetricSubmodule.mp r.property).swap_pairs ..)) a b).symm⟩

end NormedSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Pullback of a bilinear form on `⋀[ℝ]^2 V` to a four-tensor on `V`, defined by
`ofExteriorSquareBilin B ![u, v, z, w] = B (u ∧ v) (z ∧ w)`. -/
def ofExteriorSquareBilin : BilinForm ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] FourTensor V where
  toFun B := ofLinearMap₄ <| MultilinearMap.toBilinMap
    ((TauCeti.BilinForm.ofExteriorSquareDual.comp B).compMultilinearMap
      (exteriorPower.ιMulti ℝ 2).toMultilinearMap)
  map_add' _ _ := ext_vec fun _ _ _ _ ↦ by simp
  map_smul' _ _ := ext_vec fun _ _ _ _ ↦ by simp

/-- Evaluation of `ofExteriorSquareBilin B` on four vectors via pure wedges. -/
@[simp] theorem ofExteriorSquareBilin_apply (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorSquareBilin B ![u, v, z, w] =
      B (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) := by
  simp [ofExteriorSquareBilin]

/-- Every four-tensor pulled back from `⋀[ℝ]^2 V` is antisymmetric in its first pair. -/
theorem ofExteriorSquareBilin_antisymm_first (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorSquareBilin B ![u, v, z, w] = -ofExteriorSquareBilin B ![v, u, z, w] := by
  simp only [ofExteriorSquareBilin_apply, exteriorPower.ιMulti_two_swap v u, map_neg,
    LinearMap.neg_apply]

/-- Every four-tensor pulled back from `⋀[ℝ]^2 V` is antisymmetric in its last pair. -/
theorem ofExteriorSquareBilin_antisymm_last (B : BilinForm ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    ofExteriorSquareBilin B ![u, v, z, w] = -ofExteriorSquareBilin B ![u, v, w, z] := by
  simp only [ofExteriorSquareBilin_apply, exteriorPower.ιMulti_two_swap w z, map_neg]

/-- `ofExteriorSquareBilin` is injective. -/
theorem ofExteriorSquareBilin_injective : Function.Injective (ofExteriorSquareBilin (V := V)) :=
  fun _ _ h ↦ exteriorPower.linearMap_ext_ιMulti_two fun u v ↦
    exteriorPower.linearMap_ext_ιMulti_two fun z w ↦ by
      rw [← ofExteriorSquareBilin_apply, ← ofExteriorSquareBilin_apply, h]

/-- The range of `ofExteriorSquareBilin` consists of the pair-antisymmetric four-tensors. -/
theorem mem_range_ofExteriorSquareBilin_iff {r : FourTensor V} :
    r ∈ LinearMap.range (ofExteriorSquareBilin (V := V)) ↔
      (∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) ∧
        (∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨B, rfl⟩
    exact ⟨ofExteriorSquareBilin_antisymm_first B, ofExteriorSquareBilin_antisymm_last B⟩
  · refine ⟨(toLinearMap₄ r).exteriorSquareBilinear
      (fun x z w ↦ by rw [toLinearMap₄_apply]; exact CharZero.eq_neg_self_iff.mp (h₁ x x z w))
      (fun u v z ↦ by rw [toLinearMap₄_apply]; exact CharZero.eq_neg_self_iff.mp (h₂ u v z z)),
      ext_vec fun u v z w ↦ ?_⟩
    rw [ofExteriorSquareBilin_apply]
    exact (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti
      (toLinearMap₄ r) _ _ ![u, v] ![z, w]).trans (toLinearMap₄_apply r u v z w)

/-- `ofExteriorSquareBilin B` is bivector-symmetric if and only if `B` is symmetric. -/
@[simp] theorem isBivectorSymmetric_ofExteriorSquareBilin_iff {B : BilinForm ℝ (⋀[ℝ]^2 V)} :
    IsBivectorSymmetric (ofExteriorSquareBilin B) ↔ B.IsSymm := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨ofExteriorSquareBilin_antisymm_first B,
    ofExteriorSquareBilin_antisymm_last B, fun u v z w ↦ ?_⟩⟩
  · have hflip : B.flip = B :=
      exteriorPower.linearMap_ext_ιMulti_two fun u v ↦
        exteriorPower.linearMap_ext_ιMulti_two fun z w ↦ by
          rw [LinearMap.BilinForm.flip_apply, ← ofExteriorSquareBilin_apply,
            ← ofExteriorSquareBilin_apply]
          exact h.swap_pairs z w u v
    exact LinearMap.BilinForm.isSymm_iff.mpr (LinearMap.isSymm_iff_eq_flip.mpr hflip.symm)
  · simp only [ofExteriorSquareBilin_apply]
    exact h.eq _ _

/-- Linear equivalence from `bivectorSymmetricSubmodule V` to symmetric forms on `⋀[ℝ]^2 V`. -/
def bivectorSymmetricEquivSymmBilin :
    bivectorSymmetricSubmodule V ≃ₗ[ℝ] LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V) where
  toFun r := ⟨exteriorBilinOfBivectorSymmetric r,
    LinearMap.BilinForm.mem_symmSubmodule.mpr (isSymm_exteriorBilinOfBivectorSymmetric r)⟩
  invFun B := ⟨ofExteriorSquareBilin B.val,
    mem_bivectorSymmetricSubmodule.mpr (isBivectorSymmetric_ofExteriorSquareBilin_iff.mpr
      (LinearMap.BilinForm.mem_symmSubmodule.mp B.property))⟩
  map_add' _ _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun _ _ ↦ by
    simp [exteriorBilinOfBivectorSymmetric, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  map_smul' _ _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun _ _ ↦ by
    simp [exteriorBilinOfBivectorSymmetric, LinearMap.exteriorSquareBilinear_ιMulti_ιMulti]
  left_inv r := Subtype.ext <| toLinearMap₄_injective <| by
    ext u v z w; simp only [toLinearMap₄_apply, ofExteriorSquareBilin_apply]
    exact (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti
      (toLinearMap₄ r.val) _ _ ![u, v] ![z, w]).trans (toLinearMap₄_apply r.val u v z w)
  right_inv _ := Subtype.ext <| (LinearMap.exteriorSquareBilinear_eq_iff ..).mpr fun v w ↦ by
    rw [toLinearMap₄_apply, ofExteriorSquareBilin_apply, ← FinVec.etaExpand_eq v,
      ← FinVec.etaExpand_eq w]; rfl

/-- Evaluation of `bivectorSymmetricEquivSymmBilin` on pure wedges `u ∧ v` and `z ∧ w`. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_apply_ιMulti (r : bivectorSymmetricSubmodule V)
    (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin r).val (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![z, w]) = r.val ![u, v, z, w] :=
  (LinearMap.exteriorSquareBilinear_ιMulti_ιMulti (toLinearMap₄ r.val) _ _ ![u, v] ![z, w]).trans
    (toLinearMap₄_apply r.val u v z w)

/-- Evaluation of `bivectorSymmetricEquivSymmBilin.symm` on four vectors via pure wedges. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_symm_apply
    (B : LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin.symm B).val ![u, v, z, w] =
      B.val (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) :=
  ofExteriorSquareBilin_apply B.val u v z w

end FiniteDimensional

end TauCeti.FourTensor

namespace ContinuousLinearMap

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Pulling back `ofExteriorSquareBilin B` along `f : W →L[ℝ] V` precomposes both slots of `B`
with `exteriorPower.map 2 f.toLinearMap`. -/
theorem ofExteriorSquareBilin_compContinuousLinearMap (f : W →L[ℝ] V)
    (B : BilinForm ℝ (⋀[ℝ]^2 V)) :
    (ofExteriorSquareBilin B).compContinuousLinearMap (fun _ ↦ f) =
      ofExteriorSquareBilin (B.comp (exteriorPower.map 2 f.toLinearMap)
        (exteriorPower.map 2 f.toLinearMap)) := by
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec, ofExteriorSquareBilin_apply, ofExteriorSquareBilin_apply,
    LinearMap.BilinForm.comp_apply, exteriorPower.map_apply_ιMulti_two,
    exteriorPower.map_apply_ιMulti_two]
  rfl

end ContinuousLinearMap

