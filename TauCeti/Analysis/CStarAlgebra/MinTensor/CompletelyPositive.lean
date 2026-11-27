/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.Stinespring.Basic

/-!
# Tensoring completely positive maps on the minimal tensor product

Let `φ : A → A'` be a completely positive map of C*-algebras and `B` a C*-algebra. Then
`φ ⊗ id : A ⊗[ℂ] B → A' ⊗[ℂ] B` is bounded for the minimal C*-norms, with
`‖(φ ⊗ id) x‖_min ≤ ‖φ‖ ‖x‖_min` (`TauCeti.minTensorNorm_rTensor_le`), and so extends to a bounded
linear map `TauCeti.MinTensorProduct.rTensorCP φ : A ⊗min B → A' ⊗min B` of norm at most `‖φ‖`.
The same holds for `id ⊗ ψ` (`TauCeti.MinTensorProduct.lTensorCP`) and for `φ ⊗ ψ`, with the
product bound `‖φ ⊗ ψ‖ ≤ ‖φ‖ ‖ψ‖` (`TauCeti.MinTensorProduct.mapCP`).

**Proof.** Represent `A'` and `B` faithfully, by `ι : A' → B(H)` and `ρ : B → B(F)`, so that the
minimal norm on `A' ⊗[ℂ] B` is the spatial norm of `ι ⊗ ρ`. Stinespring's theorem writes the
completely positive map `ι ∘ φ : A → B(H)` as `V† π(·) V` with `π : A → B(K)` a representation and
`‖V‖² = ‖ι ∘ φ‖`. Then `(ι ∘ φ) ⊗ ρ = (V ⊗ 1)† (π ⊗ ρ)(·) (V ⊗ 1)` on `A ⊗[ℂ] B`
(`TauCeti.spatialTensorLinearMap_map_eq_adjoint_comp`), and `‖(π ⊗ ρ) x‖ ≤ ‖x‖_min` since the
minimal norm dominates every spatial norm.

## Main declarations

* `TauCeti.minTensorNorm_rTensor_le`, `TauCeti.minTensorNorm_lTensor_le`,
  `TauCeti.minTensorNorm_map_le`: the norm bounds on `A ⊗[ℂ] B`.
* `TauCeti.MinTensorProduct.rTensorCP`, `TauCeti.MinTensorProduct.lTensorCP`,
  `TauCeti.MinTensorProduct.mapCP`: the extensions to the minimal tensor products, with their
  values on `A ⊗[ℂ] B`, their norm bounds and their functoriality (`rTensorCP_id`,
  `rTensorCP_comp`, `lTensorCP_id`, `lTensorCP_comp`, `mapCP_id`, `mapCP_comp`).

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.7.2–II.9.7.3.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped CStarAlgebra

namespace TauCeti

/-! ### The Stinespring form of a tensor product of operators -/

section Spatial

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {H K F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- If `φ a = V† π(a) V` for a representation `π : A → B(K)` and `V : H → K`, then for every
representation `ρ : B → B(F)` the spatial operator of `(φ ⊗ ρ) x` is
`(V ⊗ 1)† (π ⊗ ρ)(x) (V ⊗ 1)`. -/
theorem spatialTensorLinearMap_map_eq_adjoint_comp {φ : A →ₗ[ℂ] (H →L[ℂ] H)}
    {π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} {V : H →L[ℂ] K} (hφ : ∀ a, φ a = V.adjoint ∘L π a ∘L V)
    (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (x : A ⊗[ℂ] B) :
    spatialTensorLinearMap ℂ H F H F (TensorProduct.map φ (ρ : B →ₗ[ℂ] F →L[ℂ] F) x) =
      (mapLCompletion V (.id ℂ F)).adjoint ∘L π.spatialTensorHom ρ x ∘L
        mapLCompletion V (.id ℂ F) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  | tmul a b =>
    simp [spatialTensorLinearMap_tmul, adjoint_mapLCompletion, ← mapLCompletion_comp, hφ,
      ContinuousLinearMap.adjoint_id]

/-- For a completely positive map `φ : A → B(H)` and a representation `ρ : B → B(F)`, the spatial
operator of `(φ ⊗ ρ) x` has norm at most `‖φ‖ ‖x‖_min`. -/
theorem norm_spatialTensorLinearMap_map_le_mul_minTensorNorm [PartialOrder A]
    [StarOrderedRing A] (φ : A →CP (H →L[ℂ] H)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H F H F
        (TensorProduct.map φ.toLinearMap (ρ : B →ₗ[ℂ] F →L[ℂ] F) x)‖ ≤
      ‖φ.toContinuousLinearMap‖ * minTensorNorm A B x := by
  obtain ⟨K, _, _, _, π, V, -, hφ, hV, -⟩ := φ.stinespring_nonUnital
  rw [spatialTensorLinearMap_map_eq_adjoint_comp hφ ρ x, ← hV]
  have hW : ‖mapLCompletion V (.id ℂ F)‖ ≤ ‖V‖ :=
    (norm_mapLCompletion_le _ _).trans <| by
      simpa using mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg V)
  have hx := norm_spatialTensorHom_le_minTensorNorm π ρ x
  calc _ ≤ ‖(mapLCompletion V (.id ℂ F)).adjoint‖ * ‖π.spatialTensorHom ρ x‖ *
        ‖mapLCompletion V (.id ℂ F)‖ := by
        rw [mul_assoc]
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V‖ * minTensorNorm A B x * ‖V‖ := by
        rw [LinearIsometryEquiv.norm_map]
        have := minTensorNorm_nonneg x
        gcongr
    _ = ‖V‖ ^ 2 * minTensorNorm A B x := by ring

end Spatial

/-! ### The norm bounds on the algebraic tensor product -/

section Norm

variable {A A' B B' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B'] [PartialOrder A] [StarOrderedRing A]
  [PartialOrder A'] [StarOrderedRing A'] [PartialOrder B] [StarOrderedRing B] [PartialOrder B']
  [StarOrderedRing B']

omit [PartialOrder B] [StarOrderedRing B] in
/-- **Completely positive maps tensor boundedly on the minimal norm**: for a completely positive
`φ : A → A'`, `‖(φ ⊗ id) x‖_min ≤ ‖φ‖ ‖x‖_min`. -/
theorem minTensorNorm_rTensor_le (φ : A →CP A') (x : A ⊗[ℂ] B) :
    minTensorNorm A' B (φ.toLinearMap.rTensor B x) ≤
      ‖φ.toContinuousLinearMap‖ * minTensorNorm A B x := by
  obtain ⟨H, _, _, _, ι, hι, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A'
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B
  let ψ : A →CP (H →L[ℂ] H) := (ι : A' →CP (H →L[ℂ] H)).comp φ
  have hψ : ‖ψ.toContinuousLinearMap‖ ≤ ‖φ.toContinuousLinearMap‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a ↦ by
      rw [CompletelyPositiveMap.toContinuousLinearMap_apply, CompletelyPositiveMap.comp_apply]
      exact (NonUnitalStarAlgHom.norm_apply_le ι (φ a)).trans
        (by simpa using φ.toContinuousLinearMap.le_opNorm a)
  have hmap : TensorProduct.map (ι : A' →ₗ[ℂ] H →L[ℂ] H) (ρ : B →ₗ[ℂ] F →L[ℂ] F)
      (φ.toLinearMap.rTensor B x) = TensorProduct.map ψ.toLinearMap (ρ : B →ₗ[ℂ] F →L[ℂ] F) x := by
    simp [ψ, LinearMap.rTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rw [minTensorNorm_eq_norm_spatialTensorHom hι hρ, NonUnitalStarAlgHom.spatialTensorHom_apply,
    hmap]
  exact (norm_spatialTensorLinearMap_map_le_mul_minTensorNorm ψ ρ x).trans
    (mul_le_mul_of_nonneg_right hψ (minTensorNorm_nonneg x))

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder A'] [StarOrderedRing A'] in
/-- For a completely positive `ψ : B → B'`, `‖(id ⊗ ψ) x‖_min ≤ ‖ψ‖ ‖x‖_min`. -/
theorem minTensorNorm_lTensor_le (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    minTensorNorm A B' (ψ.toLinearMap.lTensor A x) ≤
      ‖ψ.toContinuousLinearMap‖ * minTensorNorm A B x := by
  rw [← minTensorNorm_comm, ← minTensorNorm_comm x, ← LinearMap.rTensor_comm]
  exact minTensorNorm_rTensor_le ψ _

/-- **Product bound**: for completely positive `φ : A → A'` and `ψ : B → B'`,
`‖(φ ⊗ ψ) x‖_min ≤ ‖φ‖ ‖ψ‖ ‖x‖_min`. -/
theorem minTensorNorm_map_le (φ : A →CP A') (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    minTensorNorm A' B' (TensorProduct.map φ.toLinearMap ψ.toLinearMap x) ≤
      ‖φ.toContinuousLinearMap‖ * ‖ψ.toContinuousLinearMap‖ * minTensorNorm A B x := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, mul_assoc]
  exact (minTensorNorm_rTensor_le φ _).trans
    (mul_le_mul_of_nonneg_left (minTensorNorm_lTensor_le ψ x) (norm_nonneg _))

end Norm

/-! ### The extensions to the minimal tensor products -/

namespace MinTensorProduct

open CStarTensorProduct

variable {A A' A'' B B' B'' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B']
  [NonUnitalCStarAlgebra B'']

section RTensor

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder A'] [StarOrderedRing A']
  [PartialOrder A''] [StarOrderedRing A'']

variable (B) in
/-- **`φ ⊗ id` on the minimal tensor product**: a completely positive `φ : A → A'` gives the
bounded linear map `MinTensorProduct A B → MinTensorProduct A' B` extending `φ ⊗ id`, of norm at
most `‖φ‖` (`TauCeti.MinTensorProduct.norm_rTensorCP_le`). -/
def rTensorCP (φ : A →CP A') : MinTensorProduct A B →L[ℂ] MinTensorProduct A' B :=
  extendLinear _
    ((LinearMap.ofClass (of (minCStarTensorNorm A' B))).comp (φ.toLinearMap.rTensor B))

private theorem norm_of_rTensor_le (φ : A →CP A') (x : A ⊗[ℂ] B) :
    ‖of (minCStarTensorNorm A' B) (φ.toLinearMap.rTensor B x)‖ ≤
      ‖φ.toContinuousLinearMap‖ * minCStarTensorNorm A B x := by
  rw [norm_of, minCStarTensorNorm_apply, minCStarTensorNorm_apply]
  exact minTensorNorm_rTensor_le φ x

@[simp]
theorem rTensorCP_of (φ : A →CP A') (x : A ⊗[ℂ] B) :
    rTensorCP B φ (of (minCStarTensorNorm A B) x) =
      of (minCStarTensorNorm A' B) (φ.toLinearMap.rTensor B x) :=
  extendLinear_of (norm_of_rTensor_le φ) x

theorem rTensorCP_of_tmul (φ : A →CP A') (a : A) (b : B) :
    rTensorCP B φ (of (minCStarTensorNorm A B) (a ⊗ₜ b)) =
      of (minCStarTensorNorm A' B) (φ a ⊗ₜ b) := by
  simp

/-- `‖φ ⊗ id‖ ≤ ‖φ‖` on the minimal tensor product. -/
theorem norm_rTensorCP_le (φ : A →CP A') :
    ‖rTensorCP B φ‖ ≤ ‖φ.toContinuousLinearMap‖ :=
  norm_extendLinear_le (norm_nonneg _) (norm_of_rTensor_le φ)

@[simp]
theorem rTensorCP_id : rTensorCP B (CompletelyPositiveMap.id A) = .id ℂ _ :=
  continuousLinearMap_ext fun a b ↦ by simp

theorem rTensorCP_comp (θ : A' →CP A'') (φ : A →CP A') :
    rTensorCP B (θ.comp φ) = rTensorCP B θ ∘L rTensorCP B φ :=
  continuousLinearMap_ext fun a b ↦ by simp

end RTensor

section LTensor

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder B'] [StarOrderedRing B']
  [PartialOrder B''] [StarOrderedRing B'']

variable (A) in
/-- **`id ⊗ ψ` on the minimal tensor product**: a completely positive `ψ : B → B'` gives the
bounded linear map `MinTensorProduct A B → MinTensorProduct A B'` extending `id ⊗ ψ`, of norm at
most `‖ψ‖` (`TauCeti.MinTensorProduct.norm_lTensorCP_le`). -/
def lTensorCP (ψ : B →CP B') : MinTensorProduct A B →L[ℂ] MinTensorProduct A B' :=
  extendLinear _
    ((LinearMap.ofClass (of (minCStarTensorNorm A B'))).comp (ψ.toLinearMap.lTensor A))

private theorem norm_of_lTensor_le (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    ‖of (minCStarTensorNorm A B') (ψ.toLinearMap.lTensor A x)‖ ≤
      ‖ψ.toContinuousLinearMap‖ * minCStarTensorNorm A B x := by
  rw [norm_of, minCStarTensorNorm_apply, minCStarTensorNorm_apply]
  exact minTensorNorm_lTensor_le ψ x

@[simp]
theorem lTensorCP_of (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    lTensorCP A ψ (of (minCStarTensorNorm A B) x) =
      of (minCStarTensorNorm A B') (ψ.toLinearMap.lTensor A x) :=
  extendLinear_of (norm_of_lTensor_le ψ) x

theorem lTensorCP_of_tmul (ψ : B →CP B') (a : A) (b : B) :
    lTensorCP A ψ (of (minCStarTensorNorm A B) (a ⊗ₜ b)) =
      of (minCStarTensorNorm A B') (a ⊗ₜ ψ b) := by
  simp

/-- `‖id ⊗ ψ‖ ≤ ‖ψ‖` on the minimal tensor product. -/
theorem norm_lTensorCP_le (ψ : B →CP B') :
    ‖lTensorCP A ψ‖ ≤ ‖ψ.toContinuousLinearMap‖ :=
  norm_extendLinear_le (norm_nonneg _) (norm_of_lTensor_le ψ)

@[simp]
theorem lTensorCP_id : lTensorCP A (CompletelyPositiveMap.id B) = .id ℂ _ :=
  continuousLinearMap_ext fun a b ↦ by simp

theorem lTensorCP_comp (θ : B' →CP B'') (ψ : B →CP B') :
    lTensorCP A (θ.comp ψ) = lTensorCP A θ ∘L lTensorCP A ψ :=
  continuousLinearMap_ext fun a b ↦ by simp

end LTensor

section Map

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder A'] [StarOrderedRing A']
  [PartialOrder B] [StarOrderedRing B] [PartialOrder B'] [StarOrderedRing B']
  [PartialOrder A''] [StarOrderedRing A''] [PartialOrder B''] [StarOrderedRing B'']

/-- **`φ ⊗ ψ` on the minimal tensor product**: completely positive `φ : A → A'` and
`ψ : B → B'` give the bounded linear map `MinTensorProduct A B → MinTensorProduct A' B'`
extending `φ ⊗ ψ`, of norm at most `‖φ‖ ‖ψ‖` (`TauCeti.MinTensorProduct.norm_mapCP_le`). -/
def mapCP (φ : A →CP A') (ψ : B →CP B') : MinTensorProduct A B →L[ℂ] MinTensorProduct A' B' :=
  extendLinear _
    ((LinearMap.ofClass (of (minCStarTensorNorm A' B'))).comp
      (TensorProduct.map φ.toLinearMap ψ.toLinearMap))

private theorem norm_of_map_le (φ : A →CP A') (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    ‖of (minCStarTensorNorm A' B') (TensorProduct.map φ.toLinearMap ψ.toLinearMap x)‖ ≤
      ‖φ.toContinuousLinearMap‖ * ‖ψ.toContinuousLinearMap‖ * minCStarTensorNorm A B x := by
  rw [norm_of, minCStarTensorNorm_apply, minCStarTensorNorm_apply]
  exact minTensorNorm_map_le φ ψ x

@[simp]
theorem mapCP_of (φ : A →CP A') (ψ : B →CP B') (x : A ⊗[ℂ] B) :
    mapCP φ ψ (of (minCStarTensorNorm A B) x) =
      of (minCStarTensorNorm A' B') (TensorProduct.map φ.toLinearMap ψ.toLinearMap x) :=
  extendLinear_of (norm_of_map_le φ ψ) x

theorem mapCP_of_tmul (φ : A →CP A') (ψ : B →CP B') (a : A) (b : B) :
    mapCP φ ψ (of (minCStarTensorNorm A B) (a ⊗ₜ b)) =
      of (minCStarTensorNorm A' B') (φ a ⊗ₜ ψ b) := by
  simp

/-- `‖φ ⊗ ψ‖ ≤ ‖φ‖ ‖ψ‖` on the minimal tensor product. -/
theorem norm_mapCP_le (φ : A →CP A') (ψ : B →CP B') :
    ‖mapCP φ ψ‖ ≤ ‖φ.toContinuousLinearMap‖ * ‖ψ.toContinuousLinearMap‖ :=
  norm_extendLinear_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_of_map_le φ ψ)

/-- `φ ⊗ ψ = (φ ⊗ id) ∘ (id ⊗ ψ)` on the minimal tensor product. -/
theorem mapCP_eq_rTensorCP_comp_lTensorCP (φ : A →CP A') (ψ : B →CP B') :
    mapCP φ ψ = rTensorCP B' φ ∘L lTensorCP A ψ :=
  continuousLinearMap_ext fun a b ↦ by simp

@[simp]
theorem mapCP_id : mapCP (CompletelyPositiveMap.id A) (CompletelyPositiveMap.id B) = .id ℂ _ :=
  continuousLinearMap_ext fun a b ↦ by simp

theorem mapCP_comp (φ' : A' →CP A'') (ψ' : B' →CP B'') (φ : A →CP A') (ψ : B →CP B') :
    mapCP (φ'.comp φ) (ψ'.comp ψ) = mapCP φ' ψ' ∘L mapCP φ ψ :=
  continuousLinearMap_ext fun a b ↦ by simp

/-- For a star homomorphism, `φ ⊗ ψ` is `TauCeti.MinTensorProduct.map`. -/
@[simp]
theorem mapCP_toCompletelyPositiveLinearMap_apply (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')
    (u : MinTensorProduct A B) :
    mapCP (φ : A →CP A') (ψ : B →CP B') u = map φ ψ u := by
  refine induction_on u (isClosed_eq (map_continuous _) (map_continuous _)) fun x ↦ ?_
  rw [mapCP_of, map_of]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.mapNonUnitalStarAlgHom_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Map

end MinTensorProduct

end TauCeti
