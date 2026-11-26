/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Algebra.Module.Torsion.Snake

/-!
# Torsion of a commutative Lie group and its exponential lattice

For a preconnected commutative Lie group `G` the exponential is a surjective homomorphism
`lieExp : 𝔤 → G` with kernel `Λ`, so `0 → Λ → 𝔤 → G → 0` is a short exact sequence of abelian
groups. Multiplication by a nonzero integer `n` is bijective on the real vector space `𝔤`, so the
connecting map of the snake lemma (`TauCeti.torsionByδEquiv`) identifies the elements of `G`
killed by `n` with `Λ ⧸ nΛ`. The inverse sends the class of `λ ∈ Λ` to `exp(λ / n)`.

Torsion means killed by `n`, not of exact order `n`. For `n = m * k`, multiplication by `m` on
torsion corresponds to reduction of lattice classes from `Λ ⧸ mkΛ` to `Λ ⧸ kΛ`; in particular, for
`n = ℓ ^ r` these are the transition maps of the `ℓ`-adic Tate module.

## Main results

* `TauCeti.lieExpTorsionEquiv`: the elements of `G` killed by `n ≠ 0` are `Λ ⧸ nΛ`.
* `TauCeti.lieExpTorsionEquiv_symm_mk`: the inverse sends `[λ]` to `exp(λ / n)`.
* `TauCeti.lieExpTorsionEquiv_apply_eq_factor_of_eq_smul`: multiplication by `m` on torsion is
  reduction of lattice classes from `Λ ⧸ mkΛ` to `Λ ⧸ kΛ`.

The exponential lattice `TauCeti.lieExpLattice` is defined in
`TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic`. The Checks for `n = 1` and for the
circle are in `TauCeti.Examples.Geometry.Lie.Exponential.CircleTorsion`.
-/

public section

noncomputable section

namespace TauCeti

open scoped ContDiff Manifold Pointwise IsMulCommutative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The element `exp(λ / n)` is killed by `n`, for `λ ∈ Λ`. -/
theorem lieExp_inv_smul_mem_torsionBy (n : ℤ) (hn : n ≠ 0) (l : lieExpLattice (I := I) (G := G)) :
    Additive.ofMul (lieExp ((n : ℝ)⁻¹ • (l : LeftInvariantDerivation I G))) ∈
      Submodule.torsionBy ℤ (Additive G) n := by
  rw [Submodule.mem_torsionBy_iff, ← lieExpAddMonoidHom_apply, ← map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, smul_inv_smul₀ (Int.cast_ne_zero.mpr hn)]
  exact AddMonoidHom.mem_ker.1 l.property

variable [PreconnectedSpace G]

variable (I G) in
/-- **The `n`-torsion of a preconnected commutative Lie group is `Λ ⧸ nΛ`**, for `n ≠ 0`,
where `Λ` is the kernel of the exponential. It is the connecting isomorphism of multiplication by
`n` on `0 → Λ → 𝔤 → G → 0`; the inverse sends `[λ]` to `exp(λ / n)`
(`TauCeti.lieExpTorsionEquiv_symm_mk`). -/
def lieExpTorsionEquiv (n : ℤ) (hn : n ≠ 0) :
    Submodule.torsionBy ℤ (Additive G) n ≃ₗ[ℤ] QuotSMulTop n (lieExpLattice (I := I) (G := G)) :=
  -- `show` states the exactness with `Λ` itself, rather than `LinearMap.ker`, as the kernel
  torsionByδEquiv n (show Function.Exact (lieExpLattice (I := I) (G := G)).subtype
      (lieExpAddMonoidHom (I := I) (G := G)).toIntLinearMap from LinearMap.exact_subtype_ker_map _)
    (lieExpLattice (I := I) (G := G)).injective_subtype
    (by simpa only [Function.Surjective, AddMonoidHom.coe_toIntLinearMap] using
      lieExpAddMonoidHom_surjective_of_preconnectedSpace (I := I) (G := G)) <| by
      simpa only [← Int.cast_smul_eq_zsmul ℝ] using
        (Int.cast_ne_zero.mpr hn).isUnit.smul_bijective (β := LeftInvariantDerivation I G)

/-- **The characterization of the torsion isomorphism**: if `exp X = x` and `n • X = λ ∈ Λ`, then
`x` corresponds to the class of `λ`. -/
theorem lieExpTorsionEquiv_eq (n : ℤ) (hn : n ≠ 0) (x : Submodule.torsionBy ℤ (Additive G) n)
    {X : LeftInvariantDerivation I G} (hX : Additive.ofMul (lieExp X) = x)
    {l : lieExpLattice (I := I) (G := G)} (hl : (l : LeftInvariantDerivation I G) = n • X) :
    lieExpTorsionEquiv I G n hn x = Submodule.Quotient.mk l := by
  rw [lieExpTorsionEquiv, torsionByδEquiv_apply]
  exact torsionByδ_eq _ (lieExpLattice (I := I) (G := G)).injective_subtype _ x
    (y := X) (by rw [AddMonoidHom.coe_toIntLinearMap, lieExpAddMonoidHom_apply, hX]) hl

/-- **The inverse of the torsion isomorphism sends `[λ]` to `exp(λ / n)`.** -/
@[simp]
theorem lieExpTorsionEquiv_symm_mk (n : ℤ) (hn : n ≠ 0) (l : lieExpLattice (I := I) (G := G)) :
    ((lieExpTorsionEquiv I G n hn).symm (Submodule.Quotient.mk l) : Additive G) =
      Additive.ofMul (lieExp ((n : ℝ)⁻¹ • (l : LeftInvariantDerivation I G))) := by
  have hx : lieExpTorsionEquiv I G n hn ⟨_, lieExp_inv_smul_mem_torsionBy n hn l⟩ =
      Submodule.Quotient.mk l :=
    lieExpTorsionEquiv_eq n hn _ rfl <| by
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_inv_smul₀ (Int.cast_ne_zero.mpr hn)]
  rw [← hx, LinearEquiv.symm_apply_apply]

/-- Every element killed by `n ≠ 0` is `exp(λ / n)` for some `λ ∈ Λ`. -/
theorem exists_lieExp_inv_smul_eq_of_zsmul_eq_zero (n : ℤ) (hn : n ≠ 0) {g : G}
    (hg : n • Additive.ofMul g = 0) :
    ∃ l : lieExpLattice (I := I) (G := G),
      lieExp ((n : ℝ)⁻¹ • (l : LeftInvariantDerivation I G)) = g := by
  obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _
    (lieExpTorsionEquiv I G n hn ⟨Additive.ofMul g, (Submodule.mem_torsionBy_iff _ _).2 hg⟩)
  refine ⟨l, ?_⟩
  have h := lieExpTorsionEquiv_symm_mk (I := I) (G := G) n hn l
  rw [hl, LinearEquiv.symm_apply_apply] at h
  exact Additive.ofMul.injective h.symm

/-- **Transition maps.** Multiplication by `m` on the elements killed by `m * k` corresponds to
reduction of lattice classes from `Λ ⧸ mkΛ` to `Λ ⧸ kΛ`. For `m = ℓ` and `k = ℓ ^ (r - 1)` these
are the transition maps `[ℓ]` of the `ℓ`-adic Tate module. -/
theorem lieExpTorsionEquiv_apply_eq_factor_of_eq_smul (m k : ℤ) (hmk : m * k ≠ 0)
    (x : Submodule.torsionBy ℤ (Additive G) (m * k)) (y : Submodule.torsionBy ℤ (Additive G) k)
    (hy : (y : Additive G) = m • (x : Additive G)) :
    lieExpTorsionEquiv I G k (right_ne_zero_of_mul hmk) y =
      Submodule.factor (by rw [mul_smul]; exact Submodule.smul_le_self_of_tower m _)
        (lieExpTorsionEquiv I G (m * k) hmk x) := by
  rw [lieExpTorsionEquiv, lieExpTorsionEquiv, torsionByδEquiv_apply, torsionByδEquiv_apply]
  exact torsionByδ_apply_eq_factor_of_eq_smul _ _ _ x y hy

end TauCeti
