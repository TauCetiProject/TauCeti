/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Finite.Plus

/-!
# The plus-ring hypothesis of finite étale base change

Finite étale base change of Huber pairs (`Pair.completedTensor.isFiniteEtale_inl`) needs the plus
ring of the finite étale factor to be the integral closure of the image of the base plus ring.
Take `A = B = C = K` a complete Hausdorff Tate ring (for instance a complete Tate field) with two
rings of integral elements `K⁺₁ ⊊ K⁺₂` (for instance `K⁺₁ ⊊ K°`), the base and new base
`(K, K⁺₁)` and the finite factor `(K, K⁺₂)`. Every other hypothesis holds: the identity ring map is
finite and étale. The completed tensor product is `K` with plus ring `K⁺₂`, and the coprojection
from `(K, K⁺₁)` is the identity ring map, which is finite as a ring map but not as a morphism of
Huber pairs. For the bare identity this is `Pair.Hom.IsFinite.plus_eq_of_toRingHom_eq_id`.
-/

public section

open TauCeti.Huber

namespace TauCeti.Examples.FinitePairIdentityPlus

variable {K : Type*} [CommRing K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
  [IsTateRing K] [CompleteSpace K] [T2Space K] (S T : Pair K)

/-- The identity of `K` as a morphism of Huber pairs `(K, K⁺₁) → (K, K⁺₂)` for `K⁺₁ ≤ K⁺₂`. -/
def idHom (h : S.plus ≤ T.plus) : Pair.Hom S T where
  toRingHom := RingHom.id K
  continuous_toRingHom := continuous_id
  map_mem_plus _ ha := h ha

variable {S T} (hST : S.plus < T.plus)
include hST

/-- The ring map of the finite factor is finite and étale. -/
example : (idHom S T hST.le).toRingHom.Finite ∧ (idHom S T hST.le).toRingHom.Etale :=
  ⟨RingHom.Finite.id K, .of_bijective Function.bijective_id⟩

/-- The plus ring of the finite factor is not the integral closure of `K⁺₁`, so the identity
`(K, K⁺₁) → (K, K⁺₂)` is not finite étale. -/
example : ¬ (idHom S T hST.le).IsFiniteEtale := fun h ↦
  hST.ne (h.isFinite.plus_eq_of_toRingHom_eq_id rfl).symm

/-- The completed tensor product is `K` with plus ring `K⁺₂`. -/
example :
    (S.completedTensor K T).plus.map (CompletedTensor.rightUnitor K K).toRingHom = T.plus :=
  Pair.completedTensor.rightUnitor_plus_self hST.le

/-- Under the right unit, the coprojection from `(K, K⁺₁)` is the identity ring map. -/
example (x : K) : CompletedTensor.rightUnitor K K (CompletedTensor.inl K K K x) = x := by
  simp

/-- The ring map of the coprojection is finite. -/
example : (CompletedTensor.inl K K K).Finite :=
  RingHom.Finite.of_surjective _ fun x ↦
    ⟨CompletedTensor.rightUnitor K K x, by simp⟩

/-- The coprojection `(K, K⁺₁) → (K, K⁺₁) ⊗̂_K (K, K⁺₂)` is not finite as a morphism of Huber
pairs. -/
example : ¬ (Pair.completedTensor.inl K S T).IsFinite := fun h ↦
  hST.not_ge (Pair.completedTensor.plus_le_of_isFinite_inl_self h)

end TauCeti.Examples.FinitePairIdentityPlus
