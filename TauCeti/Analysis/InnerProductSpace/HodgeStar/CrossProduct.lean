/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# The Hodge star of a wedge in odd dimension, and the cross product

Let `V` be an oriented real inner product space of odd dimension `2k + 1`. For `u : V`, the
composite `⋆ ∘ ε_u` of exterior multiplication `ε_u = u ∧ ·` with the Hodge star maps `⋀ᵏ V` to
itself. Since `⋆` is an isometric involution between `⋀ᵏ V` and `⋀ᵏ⁺¹ V` in this dimension, and
`ι_u (⋆x) = (-1) ^ k ⋆(u ∧ x)`, it satisfies

`⟪⋆(u ∧ x), y⟫ = (-1) ^ k ⟪x, ⋆(u ∧ y)⟫`

(`Orientation.inner_hodgeStar_wedgeLeft`): `⋆ ∘ ε_u` is self-adjoint for even `k` and skew-adjoint
for odd `k`.

In dimension three (`k = 1`) the map `v ↦ ⋆(u ∧ v)` on `⋀¹ V`, identified with `V`, is the cross
product `v ↦ u × v`: it is characterized by the triple product
`⟪⋆(u ∧ v), w⟫ = vol(u, v, w)` (`Orientation.inner_hodgeStar_wedgeLeft_ιMulti`), and it is
skew-adjoint. This is the pointwise form of `curl = ⋆ d` on one-forms.

## Main results

* `Orientation.inner_hodgeStar_wedgeLeft`: `⟪⋆(u ∧ x), y⟫ = (-1) ^ k ⟪x, ⋆(u ∧ y)⟫` on `⋀ᵏ V`
  in dimension `2k + 1`.
* `Orientation.adjoint_hodgeStar_comp_wedgeLeft`: equivalently, the adjoint of `⋆ ∘ ε_u` is
  `(-1) ^ k ⋆ ∘ ε_u`.
* `Orientation.inner_hodgeStar_wedgeLeft_ιMulti`: in dimension three,
  `⟪⋆(u ∧ v), w⟫ = vol(u, v, w)`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 (the Hodge star).
-/

public section

noncomputable section

open Module exteriorPower TauCeti
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace Orientation

section OddDimension

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **`⋆ ∘ ε_u` is `(-1) ^ k`-symmetric in dimension `2k + 1`**: for `x y ∈ ⋀ᵏ V`,
`⟪⋆(u ∧ x), y⟫ = (-1) ^ k ⟪x, ⋆(u ∧ y)⟫`. In dimension three this is the skew-symmetry
`⟪u × v, w⟫ = -⟪v, u × w⟫` of the cross product. -/
theorem inner_hodgeStar_wedgeLeft (u : V) {k : ℕ} (hk : k + 1 + k = finrank ℝ V)
    (x y : ⋀[ℝ]^k V) :
    ⟪o.hodgeStar hk (ExteriorAlgebra.wedgeLeft u k x), y⟫ =
      (-1 : ℝ) ^ k * ⟪x, o.hodgeStar hk (ExteriorAlgebra.wedgeLeft u k y)⟫ := by
  -- Write `y = ⋆z` with `z = ⋆y ∈ ⋀ᵏ⁺¹ V`; then `⟪⋆(u ∧ x), ⋆z⟫ = ⟪u ∧ x, z⟫ = ⟪x, ι_u z⟫`, and
  -- `ι_u (⋆y) = (-1) ^ k ⋆(u ∧ y)`.
  have hk' : k + (k + 1) = finrank ℝ V := by omega
  have hy : o.hodgeStar hk (o.hodgeStar hk' y) = y := by
    rw [o.hodgeStar_hodgeStar hk' hk, (Nat.even_mul_succ_self k).neg_one_pow, one_smul]
  conv_lhs => rw [← hy]
  rw [o.inner_hodgeStar_hodgeStar, inner_wedgeLeft_eq_inner_koszulDifferential,
    o.koszulDifferential_hodgeStar u hk' hk, real_inner_smul_right]

/-- The adjoint of `⋆ ∘ ε_u : ⋀ᵏ V → ⋀ᵏ V` in dimension `2k + 1` is `(-1) ^ k ⋆ ∘ ε_u`. -/
theorem adjoint_hodgeStar_comp_wedgeLeft (u : V) {k : ℕ} (hk : k + 1 + k = finrank ℝ V) :
    LinearMap.adjoint ((o.hodgeStar hk).toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeft u k) =
      (-1 : ℝ) ^ k • ((o.hodgeStar hk).toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeft u k) := by
  refine ((LinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    real_inner_smul_left, o.inner_hodgeStar_wedgeLeft u hk, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨k, rfl⟩, one_mul]

end OddDimension

section DimensionThree

variable [Fact (finrank ℝ V = 3)] (o : Orientation ℝ V (Fin 3))

/-- **The Hodge star of a wedge in dimension three is the cross product**: for vectors `u, v, w`
of an oriented three-dimensional inner product space, `⟪⋆(u ∧ v), w⟫ = vol(u, v, w)`, the
triple product. -/
theorem inner_hodgeStar_wedgeLeft_ιMulti (h : 1 + 1 + 1 = finrank ℝ V) (u v w : V) :
    ⟪o.hodgeStar h (ExteriorAlgebra.wedgeLeft u 1 (ιMulti ℝ 1 ![v])), ιMulti ℝ 1 ![w]⟫ =
      o.volumeForm ![u, v, w] := by
  have h3 : finrank ℝ V = 3 := Fact.out
  rw [inner_hodgeStar_apply, ExteriorAlgebra.wedgeLeft_ιMulti,
    wedgePairing_apply_eq_of_coe_mul_eq _ h _ _ (ιMulti ℝ _ (![u, v, w] ∘ finCongr h3)),
    volumeEquiv_ιMulti]
  · rw [Function.comp_assoc, ← finCongr_symm h3, Equiv.self_comp_symm, Function.comp_id]
  · simp only [ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_congr h3]
    simp [List.ofFn_succ, mul_assoc]

end DimensionThree

end Orientation
