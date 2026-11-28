/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
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
    bivectorSymmetricSubmodule V ≃ₗ[ℝ] LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V) :=
  (LinearEquiv.ofBijective
    ((ofExteriorSquareBilin.domRestrict
        (LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V))).codRestrict
      (bivectorSymmetricSubmodule V) fun B ↦
        mem_bivectorSymmetricSubmodule.mpr (isBivectorSymmetric_ofExteriorSquareBilin_iff.mpr
          (LinearMap.BilinForm.mem_symmSubmodule.mp B.property)))
    ⟨fun _ _ h ↦ Subtype.ext <| ofExteriorSquareBilin_injective (congrArg Subtype.val h),
      fun r ↦ by
        have hr := mem_bivectorSymmetricSubmodule.mp r.property
        obtain ⟨B, hB⟩ := mem_range_ofExteriorSquareBilin_iff.mpr
          ⟨hr.antisymm_first, hr.antisymm_last⟩
        have hBsymm : B.IsSymm := isBivectorSymmetric_ofExteriorSquareBilin_iff.mp (hB ▸ hr)
        exact ⟨⟨B, LinearMap.BilinForm.mem_symmSubmodule.mpr hBsymm⟩, Subtype.ext hB⟩⟩).symm

/-- Evaluation of `bivectorSymmetricEquivSymmBilin.symm` on four vectors via pure wedges. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_symm_apply
    (B : LinearMap.BilinForm.symmSubmodule ℝ (⋀[ℝ]^2 V)) (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin.symm B).val ![u, v, z, w] =
      B.val (exteriorPower.ιMulti ℝ 2 ![u, v]) (exteriorPower.ιMulti ℝ 2 ![z, w]) :=
  ofExteriorSquareBilin_apply B.val u v z w

/-- Evaluation of `bivectorSymmetricEquivSymmBilin` on pure wedges `u ∧ v` and `z ∧ w`. -/
@[simp] theorem bivectorSymmetricEquivSymmBilin_apply_ιMulti (r : bivectorSymmetricSubmodule V)
    (u v z w : V) :
    (bivectorSymmetricEquivSymmBilin r).val (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![z, w]) = r.val ![u, v, z, w] := by
  rw [← bivectorSymmetricEquivSymmBilin_symm_apply, LinearEquiv.symm_apply_apply]

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
  simp only [compContinuousLinearMap_apply_vec, ofExteriorSquareBilin_apply,
    LinearMap.BilinForm.comp_apply, exteriorPower.map_apply_ιMulti_two, ContinuousLinearMap.coe_coe]

end ContinuousLinearMap

