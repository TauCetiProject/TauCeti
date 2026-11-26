/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality

/-!
# Integral points of a Hopf algebra

Let `O` be a commutative semiring with an algebra map to a commutative semiring `K`, and let `A`
be a Hopf `O`-algebra. The integral points of `A` are the image of `Hom_O(A, O)` in the points
`Hom_K(K ⊗[O] A, K)` of the base change `K ⊗[O] A` under base change of points along `O → K`.
When `O → K` is injective (`FaithfulSMul O K`), a point `g` of `K ⊗[O] A` is integral exactly when
its values `g (1 ⊗ a)` lie in the image of `O`.

## Main declarations

* `TauCeti.IntegralModel.integralPoints`: the integral points of a Hopf `O`-algebra, as a subgroup
  of the points of its base change to `K`.
* `TauCeti.IntegralModel.mem_integralPoints_iff_exists`,
  `TauCeti.IntegralModel.pointsBaseChange_mem_integralPoints`: the integral points are the base
  changes of the points of `A`.
* `TauCeti.IntegralModel.integralPoints_le_comap`: integral points are contravariant along Hopf
  maps.
* `TauCeti.IntegralModel.mem_integralPoints_iff`: the membership criterion when `O → K` is
  injective.
-/

public section

open TensorProduct

namespace TauCeti.IntegralModel

section IntegralPoints

variable (O K A : Type*) [CommSemiring O] [CommSemiring K] [Algebra O K] [Semiring A]
  [_root_.HopfAlgebra O A]

/-- The integral points of a Hopf `O`-algebra `A`, as a subgroup of the points
`Hom_K(K ⊗[O] A, K)` of its base change to `K`: the image of `Hom_O(A, O)` under base change of
points along `O → K` (`AlgHom.pointsBaseChange`). -/
noncomputable def integralPoints : Subgroup (WithConv (K ⊗[O] A →ₐ[K] K)) :=
  (AlgHom.pointsBaseChange (k := O) (A := A) K).range

/-- Unfolding lemma for `IntegralModel.integralPoints`. -/
theorem integralPoints_def :
    integralPoints O K A = (AlgHom.pointsBaseChange (k := O) (A := A) K).range :=
  (rfl)

variable {O K A}

/-- A point of the base change `K ⊗[O] A` is integral exactly when it is the base change of a
point of `A`. -/
theorem mem_integralPoints_iff_exists {g : WithConv (K ⊗[O] A →ₐ[K] K)} :
    g ∈ integralPoints O K A ↔
      ∃ f : WithConv (A →ₐ[O] O), AlgHom.pointsBaseChange (k := O) (A := A) K f = g := by
  rw [integralPoints_def, MonoidHom.mem_range]

/-- The base change of a point of `A` is an integral point. -/
@[simp]
theorem pointsBaseChange_mem_integralPoints (f : WithConv (A →ₐ[O] O)) :
    AlgHom.pointsBaseChange (k := O) (A := A) K f ∈ integralPoints O K A :=
  ⟨f, rfl⟩

/-- Integral points are contravariant in the Hopf algebra: a Hopf map `φ : A → A'` sends the
integral points of `A'` to integral points of `A` by precomposition with its scalar extension. -/
theorem integralPoints_le_comap {A' : Type*} [Semiring A'] [_root_.HopfAlgebra O A']
    (φ : A →ₐc[O] A') :
    integralPoints O K A' ≤ (integralPoints O K A).comap
      (BialgHom.mapDomain (A := K)
        (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨BialgHom.mapDomain φ x, (BialgHom.mapDomain_pointsBaseChange K φ x).symm⟩

end IntegralPoints

/-- When `O → K` is injective, a point of the base change `K ⊗[O] A` is integral exactly when its
values on `1 ⊗ a` lie in the image of `O` for every `a ∈ A`. -/
theorem mem_integralPoints_iff {O K : Type*} [CommSemiring O] [CommSemiring K] [Algebra O K]
    [FaithfulSMul O K] (A : Type*) [Semiring A] [_root_.HopfAlgebra O A]
    (g : WithConv (K ⊗[O] A →ₐ[K] K)) :
    g ∈ integralPoints O K A ↔ ∀ a : A, g (1 ⊗ₜ[O] a) ∈ (algebraMap O K).rangeS := by
  -- Transport `g` along the base-change point equivalence to a `K`-valued point of `A`.
  rw [integralPoints_def, AlgHom.pointsBaseChange_def, MonoidHom.range_comp,
    Subgroup.mem_map_equiv, MonoidHom.mem_range, ← MonoidHom.mem_mrange]
  -- Descend the coefficients of that point along the injective map `O → K`.
  rw [AlgHom.mem_mrange_mapValue_iff (FaithfulSMul.algebraMap_injective O K)]
  simp [Algebra.mem_bot]

end TauCeti.IntegralModel
