/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
public import TauCeti.RingTheory.KoszulComplex.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Wedge, contraction and the Hodge star

On a finite-dimensional real inner product space `V`, exterior multiplication `ε_u : x ↦ u ∧ x` by
a vector `u` and the contraction `ι_u` by the functional `⟪u, ·⟫` are adjoint for the inner
product of the exterior powers: `⟪u ∧ x, y⟫ = ⟪x, ι_u y⟫`. Here `ε_u` is
`TauCeti.ExteriorAlgebra.wedgeLeft u` and `ι_u` is the Koszul differential
`TauCeti.koszulDifferential (innerₗ V u)`, the contraction `⋀ᵏ⁺¹ V → ⋀ᵏ V`. Together with the
Koszul homotopy identity `TauCeti.wedgeLeft_comp_koszulDifferential_add`, read with
`φ = ⟪u, ·⟫`, this says that `ε_u ε_u* + ε_u* ε_u = ‖u‖²`.

On an oriented space the Hodge star intertwines the two operations up to sign: for `x ∈ ⋀ᵏ V`,
`ι_u (⋆x) = (-1) ^ k ⋆(u ∧ x)`, and for `x ∈ ⋀ᵏ⁺¹ V`, `⋆(ι_u x) = (-1) ^ k u ∧ ⋆x`. Consequently
the contraction is conjugate to exterior multiplication by the Hodge star: on `p`-forms of an
`m`-dimensional space, `ι_u = (-1) ^ (m (p + 1)) ⋆ ε_u ⋆`. These are the pointwise identities
behind the principal symbols of the exterior derivative `d`, its formal adjoint `d*` and the
Hodge Laplacian `d d* + d* d`: up to the factor `i`, the symbol of `d` is `ε_ξ`, that of `d*` is
the adjoint contraction `ι_ξ`, and the formula `d* = (-1) ^ (m (p + 1) + 1) ⋆ d ⋆` on `p`-forms has
the identity above as its symbol.

## Main results

* `TauCeti.inner_wedgeLeft_eq_inner_koszulDifferential`: `⟪u ∧ x, y⟫ = ⟪x, ι_u y⟫` in every
  degree, and `TauCeti.adjoint_wedgeLeft`: the adjoint of `ε_u` is `ι_u`.
* `Orientation.koszulDifferential_hodgeStar`: `ι_u (⋆x) = (-1) ^ k ⋆(u ∧ x)` for `x ∈ ⋀ᵏ V`.
* `Orientation.hodgeStar_koszulDifferential`: `⋆(ι_u x) = (-1) ^ k u ∧ ⋆x` for `x ∈ ⋀ᵏ⁺¹ V`.
* `Orientation.koszulDifferential_eq_smul_hodgeStar_wedgeLeft_hodgeStar`: on `⋀ᵏ⁺¹ V` with
  `m = finrank ℝ V`, `ι_u = (-1) ^ (m k) ⋆ ε_u ⋆`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 and §6.2.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

/-- **Wedging with a vector is adjoint to contracting with it**: for `u : V`, `x ∈ ⋀ⁿ V` and
`y ∈ ⋀ⁿ⁺¹ V`, `⟪u ∧ x, y⟫ = ⟪x, ι_u y⟫`, where `ι_u` is the contraction by `⟪u, ·⟫`. -/
theorem inner_wedgeLeft_eq_inner_koszulDifferential (u : V) (n : ℕ) (x : ⋀[ℝ]^n V)
    (y : ⋀[ℝ]^(n + 1) V) :
    ⟪ExteriorAlgebra.wedgeLeft u n x, y⟫ = ⟪x, koszulDifferential (innerₗ V u) n y⟫ := by
  -- On wedges of vectors both sides are Gram determinants, related by the Laplace expansion of
  -- `det ⟪(u, v₁, …, vₙ)ⱼ, wᵢ⟫` along the column of `u`.
  have key : (innerₗ (⋀[ℝ]^(n + 1) V)).comp (ExteriorAlgebra.wedgeLeft u n) =
      (innerₗ (⋀[ℝ]^n V)).compl₂ (koszulDifferential (innerₗ V u) n) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    simp [koszulDifferential_ιMulti, inner_ιMulti_ιMulti, Matrix.det_succ_column_zero,
      Fin.removeNth, Matrix.submatrix]
  exact LinearMap.congr_fun₂ key x y

/-- The adjoint of exterior multiplication by `u` is the contraction by `⟪u, ·⟫`. -/
theorem adjoint_wedgeLeft (u : V) (n : ℕ) :
    LinearMap.adjoint (ExteriorAlgebra.wedgeLeft u n) = koszulDifferential (innerₗ V u) n :=
  ((LinearMap.eq_adjoint_iff _ _).2 fun y x ↦ by
    rw [real_inner_comm, ← inner_wedgeLeft_eq_inner_koszulDifferential, real_inner_comm]).symm

end TauCeti

namespace Orientation

open TauCeti

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **Contraction of a Hodge star**: for `x ∈ ⋀ᵏ V`, `ι_u (⋆x) = (-1) ^ k ⋆(u ∧ x)`. -/
theorem koszulDifferential_hodgeStar (u : V) {k l : ℕ} (hkl : k + (l + 1) = finrank ℝ V)
    (hkl' : k + 1 + l = finrank ℝ V) (x : ⋀[ℝ]^k V) :
    koszulDifferential (innerₗ V u) l (o.hodgeStar hkl x) =
      (-1 : ℝ) ^ k • o.hodgeStar hkl' (ExteriorAlgebra.wedgeLeft u k x) := by
  -- Pairing with `y ∈ ⋀ˡ V`, both sides are volumes of top forms: `x ∧ (u ∧ y)` on the left and
  -- `(u ∧ x) ∧ y` on the right, and moving `u` past `x` costs `(-1) ^ k`.
  refine ext_inner_right ℝ fun y ↦ ?_
  set z : ⋀[ℝ]^(finrank ℝ V) V := ⟨_, by
    rw [← hkl']; exact (wedge ℝ V (k + 1) l (ExteriorAlgebra.wedgeLeft u k x) y).2⟩
  have hx : (x : _root_.ExteriorAlgebra ℝ V) * (_root_.ExteriorAlgebra.ι ℝ u * y) =
      (-1 : ℝ) ^ k • (_root_.ExteriorAlgebra.ι ℝ u * x * y) := by
    rw [_root_.ExteriorAlgebra.ι_mul_eq_involute_mul u (x : _root_.ExteriorAlgebra ℝ V),
      ExteriorAlgebra.involute_of_mem_exteriorPower x.2]
    simp [smul_smul, ← mul_pow, mul_assoc]
  -- Both inner products are now volumes of the same top form `z`, up to the sign.
  rw [real_inner_comm, ← inner_wedgeLeft_eq_inner_koszulDifferential, real_inner_comm,
    inner_hodgeStar_apply, real_inner_smul_left, inner_hodgeStar_apply,
    wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _ ((-1 : ℝ) ^ k • z) (by simp [z, hx]),
    wedgePairing_apply_eq_of_coe_mul_eq _ hkl' _ _ z (by simp [z])]
  simp

/-- **Hodge star of a contraction**: for `x ∈ ⋀ᵏ⁺¹ V`, `⋆(ι_u x) = (-1) ^ k u ∧ ⋆x`. -/
theorem hodgeStar_koszulDifferential (u : V) {k l : ℕ} (hkl : k + (l + 1) = finrank ℝ V)
    (hkl' : k + 1 + l = finrank ℝ V) (x : ⋀[ℝ]^(k + 1) V) :
    o.hodgeStar hkl (koszulDifferential (innerₗ V u) k x) =
      (-1 : ℝ) ^ k • ExteriorAlgebra.wedgeLeft u l (o.hodgeStar hkl' x) := by
  -- Apply `koszulDifferential_hodgeStar` to `⋆x` and cancel the two double stars.
  have hlk : l + (k + 1) = finrank ℝ V := by omega
  have hlk' : l + 1 + k = finrank ℝ V := by omega
  have h := congrArg (o.hodgeStar hkl)
    (o.koszulDifferential_hodgeStar u hlk hlk' (o.hodgeStar hkl' x))
  simp only [o.hodgeStar_hodgeStar hkl' hlk, map_smul, o.hodgeStar_hodgeStar hlk' hkl,
    smul_smul] at h
  rw [← smul_right_inj (pow_ne_zero ((k + 1) * l) (neg_ne_zero.2 (one_ne_zero (α := ℝ)))), h]
  -- It remains to compare the signs.
  simp only [smul_smul, ← pow_add]
  congr 2
  ring

/-- **The contraction is conjugate to exterior multiplication by the Hodge star**: on `⋀ᵏ⁺¹ V`,
`ι_u = (-1) ^ (m k) ⋆ ε_u ⋆` with `m = finrank ℝ V`. For `p = k + 1` the sign is
`(-1) ^ (m (p + 1))`, the pointwise form of `d* = (-1) ^ (m (p + 1) + 1) ⋆ d ⋆` on `p`-forms. -/
theorem koszulDifferential_eq_smul_hodgeStar_wedgeLeft_hodgeStar (u : V) {k l : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hlk : l + 1 + k = finrank ℝ V) (x : ⋀[ℝ]^(k + 1) V) :
    koszulDifferential (innerₗ V u) k x =
      (-1 : ℝ) ^ (finrank ℝ V * k) •
        o.hodgeStar hlk (ExteriorAlgebra.wedgeLeft u l (o.hodgeStar hkl x)) := by
  -- Apply `koszulDifferential_hodgeStar` to `⋆x` and cancel the double star on the left.
  have h := o.koszulDifferential_hodgeStar u (by omega : l + (k + 1) = finrank ℝ V) hlk
    (o.hodgeStar hkl x)
  rw [o.hodgeStar_hodgeStar hkl (by omega), map_smul] at h
  rw [← smul_right_inj (pow_ne_zero ((k + 1) * l) (neg_ne_zero.2 (one_ne_zero (α := ℝ)))), h,
    smul_smul, ← pow_add, ← hkl]
  -- The signs agree: `(k + 1) l + (k + 1 + l) k = l + 2 (k l + j)` where `k (k + 1) = 2 j`.
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have he : (k + 1) * l + (k + 1 + l) * k = l + 2 * (k * l + j) := by nlinarith [hj]
  simp [he, pow_add, pow_mul]

end Orientation
