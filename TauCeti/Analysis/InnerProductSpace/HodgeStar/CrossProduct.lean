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
# The Hodge star of a wedge, and the cross product

Let `V` be an oriented real inner product space of dimension `k + 1 + l`. For `u : V`, exterior
multiplication `ε_u = u ∧ ·` followed by the Hodge star gives maps `⋆ ∘ ε_u : ⋀ᵏ V → ⋀ˡ V` and
`⋆ ∘ ε_u : ⋀ˡ V → ⋀ᵏ V`. Since `⋆` is an isometry with `⋆⋆ = ±1`, and
`ι_u (⋆x) = ± ⋆(u ∧ x)`, they are adjoint up to sign:

`⟪⋆(u ∧ x), y⟫ = (-1) ^ (k * l) ⟪x, ⋆(u ∧ y)⟫`

(`Orientation.inner_hodgeStar_wedgeLeft`). In odd dimension `2k + 1` the map `⋆ ∘ ε_u` sends
`⋀ᵏ V` to itself, and it is self-adjoint for even `k` and skew-adjoint for odd `k`.

In dimension three (`k = l = 1`) the map `v ↦ ⋆(u ∧ v)` on `⋀¹ V`, identified with `V`, is the
cross product `v ↦ u × v`: it is characterized by the triple product
`⟪⋆(u ∧ v), w⟫ = vol(u, v, w)` (`Orientation.inner_hodgeStar_wedgeLeft_ιMulti`), and it is
skew-adjoint. This is the pointwise form of `curl = ⋆ d` on one-forms.

## Main results

* `Orientation.inner_hodgeStar_wedgeLeft`: `⟪⋆(u ∧ x), y⟫ = (-1) ^ (k * l) ⟪x, ⋆(u ∧ y)⟫` for
  `x ∈ ⋀ᵏ V` and `y ∈ ⋀ˡ V` in dimension `k + 1 + l`.
* `Orientation.adjoint_hodgeStar_comp_wedgeLeft`: in dimension `2k + 1`, the adjoint of
  `⋆ ∘ ε_u : ⋀ᵏ V → ⋀ᵏ V` is `(-1) ^ k ⋆ ∘ ε_u`.
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

section Adjoint

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **`⋆ ∘ ε_u` is adjoint to `⋆ ∘ ε_u` up to sign**: in dimension `k + 1 + l`, for `x ∈ ⋀ᵏ V` and
`y ∈ ⋀ˡ V`, `⟪⋆(u ∧ x), y⟫ = (-1) ^ (k * l) ⟪x, ⋆(u ∧ y)⟫`. In dimension three this is the
skew-symmetry `⟪u × v, w⟫ = -⟪v, u × w⟫` of the cross product. -/
theorem inner_hodgeStar_wedgeLeft (u : V) {k l : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hlk : l + 1 + k = finrank ℝ V) (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    ⟪o.hodgeStar hkl (ExteriorAlgebra.wedgeLeft u k x), y⟫ =
      (-1 : ℝ) ^ (k * l) * ⟪x, o.hodgeStar hlk (ExteriorAlgebra.wedgeLeft u l y)⟫ := by
  -- Write `y = ± ⋆z` with `z = ⋆y ∈ ⋀ᵏ⁺¹ V`; then `⟪⋆(u ∧ x), ⋆z⟫ = ⟪u ∧ x, z⟫ = ⟪x, ι_u z⟫`, and
  -- `ι_u (⋆y) = (-1) ^ l ⋆(u ∧ y)`.
  have hlk' : l + (k + 1) = finrank ℝ V := by omega
  have hy : o.hodgeStar hkl (o.hodgeStar hlk' y) = (-1 : ℝ) ^ (l * (k + 1)) • y :=
    o.hodgeStar_hodgeStar hlk' hkl y
  have hsign : (-1 : ℝ) ^ (l * (k + 1)) * (-1) ^ l = (-1) ^ (k * l) := by
    rw [← pow_add, show l * (k + 1) + l = k * l + 2 * l by ring, pow_add, pow_mul (-1 : ℝ) 2,
      neg_one_sq, one_pow, mul_one]
  calc ⟪o.hodgeStar hkl (ExteriorAlgebra.wedgeLeft u k x), y⟫
      = (-1 : ℝ) ^ (l * (k + 1)) * ⟪o.hodgeStar hkl (ExteriorAlgebra.wedgeLeft u k x),
          o.hodgeStar hkl (o.hodgeStar hlk' y)⟫ := by
        rw [hy, real_inner_smul_right, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    _ = (-1 : ℝ) ^ (k * l) * ⟪x, o.hodgeStar hlk (ExteriorAlgebra.wedgeLeft u l y)⟫ := by
        rw [o.inner_hodgeStar_hodgeStar, inner_wedgeLeft_eq_inner_koszulDifferential,
          o.koszulDifferential_hodgeStar u hlk' hlk, real_inner_smul_right, ← mul_assoc, hsign]

/-- The adjoint of `⋆ ∘ ε_u : ⋀ᵏ V → ⋀ᵏ V` in dimension `2k + 1` is `(-1) ^ k ⋆ ∘ ε_u`. -/
theorem adjoint_hodgeStar_comp_wedgeLeft (u : V) {k : ℕ} (hk : k + 1 + k = finrank ℝ V) :
    LinearMap.adjoint ((o.hodgeStar hk).toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeft u k) =
      (-1 : ℝ) ^ k • ((o.hodgeStar hk).toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeft u k) := by
  have hsign : (-1 : ℝ) ^ (k * k) = (-1) ^ k := by
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_one_pow, (h.mul_right k).neg_one_pow]
    · rw [h.neg_one_pow, (h.mul h).neg_one_pow]
  refine ((LinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    real_inner_smul_left, o.inner_hodgeStar_wedgeLeft u hk hk, hsign, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨k, rfl⟩, one_mul]

end Adjoint

section DimensionThree

variable [Fact (finrank ℝ V = 3)] (o : Orientation ℝ V (Fin 3))

/-- **The Hodge star of a wedge in dimension three is the cross product**: for vectors `u, v, w`
of an oriented three-dimensional inner product space, `⟪⋆(u ∧ v), w⟫ = vol(u, v, w)`, the
triple product. -/
theorem inner_hodgeStar_wedgeLeft_ιMulti (u v w : V) :
    ⟪o.hodgeStar (Fact.out : finrank ℝ V = 3).symm
        (ExteriorAlgebra.wedgeLeft u 1 (ιMulti ℝ 1 ![v])), ιMulti ℝ 1 ![w]⟫ =
      o.volumeForm ![u, v, w] := by
  have h3 : finrank ℝ V = 3 := Fact.out
  have h : 1 + 1 + 1 = finrank ℝ V := h3.symm
  rw [inner_hodgeStar_apply, ExteriorAlgebra.wedgeLeft_ιMulti,
    wedgePairing_apply_eq_of_coe_mul_eq _ h _ _ (ιMulti ℝ _ (![u, v, w] ∘ finCongr h3)),
    volumeEquiv_ιMulti]
  · rw [Function.comp_assoc, ← finCongr_symm h3, Equiv.self_comp_symm, Function.comp_id]
  · simp only [ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_congr h3]
    simp [List.ofFn_succ, mul_assoc]

end DimensionThree

end Orientation
