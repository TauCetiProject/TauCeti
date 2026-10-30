/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.OrthSum
public import TauCeti.Algebra.Module.ZLattice.Scaling
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic

/-!
# Functoriality of theta series

This file records how the theta series `Θ_L` and `θ_{γ+L}` of `ZLattice.thetaSeries` and
`ZLattice.thetaCoset` transform under the three basic operations on lattices.

* **Linear equivalences.** For a linear equivalence `e : F ≃ₗ[ℝ] E`, the pull-back
  `e⁻¹(L)` is in bijection with `L` through `e⁻¹`, so the theta series of `γ + e⁻¹(L)` is
  the sum over `v ∈ L` of `exp (π i ‖γ + e⁻¹ v‖² τ)`. This is the one reindexing from which
  isometry invariance and the scaling law follow.
* **Isometries.** When `e` is an isometry, `‖γ + e⁻¹ v‖ = ‖e γ + v‖`, so the theta series are
  invariant: `θ_{γ + e⁻¹(L)} = θ_{e γ + L}` and `Θ_{e⁻¹(L)} = Θ_L`.
* **Orthogonal direct sums.** In the `L²` product `WithLp 2 (E × F)`,
  `‖(x, y)‖² = ‖x‖² + ‖y‖²`, so each term of the theta series of `L ⊕ M` is the product of a term
  for `L` and a term for `M`, and the absolutely convergent series multiply:
  `θ_{(γ, δ) + (L ⊕ M)} = θ_{γ+L} · θ_{δ+M}` and `Θ_{L ⊕ M} = Θ_L · Θ_M`.
* **Scaling.** For `c ≠ 0`, `‖c γ + c v‖² = c² ‖γ + v‖²`, so
  `θ_{c γ + c L}(τ) = θ_{γ+L}(c² τ)` and `Θ_{c L}(τ) = Θ_L(c² τ)`, where `c² τ` is the action of
  the positive real `c²` on the upper half-plane.

The product formula is what makes `L ↦ Θ_L` multiplicative, for instance
`Θ_{E₈ ⊕ E₈} = Θ_{E₈}²`; the scaling formula relates, for example, `Θ_{√2 ℤ}(τ)` to `Θ_ℤ(2τ)`.

## Main statements

* `ZLattice.thetaCoset_comap_apply`: the theta series of a translate of the pull-back of `L` along
  a linear equivalence, as a sum over `L`.
* `ZLattice.thetaCoset_comap`, `ZLattice.thetaSeries_comap`: invariance under linear isometry
  equivalences.
* `ZLattice.thetaCoset_orthSum`, `ZLattice.thetaSeries_orthSum`: the theta series of an
  orthogonal direct sum is the product of the theta series of the summands.
* `ZLattice.thetaCoset_smul`, `ZLattice.thetaSeries_smul`: the theta series of `c • L` at `τ` is
  the theta series of `L` at `c² τ`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
-/

public section

open Complex WithLp
open scoped Real Pointwise UpperHalfPlane

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (L : Submodule ℤ E)

/-! ### Linear equivalences and isometries -/

/-- The theta series of a translate of the pull-back of `L` along a linear equivalence
`e : F ≃ₗ[ℝ] E`, reindexed as a sum over `L` through `e⁻¹`. -/
theorem thetaCoset_comap_apply (e : F ≃ₗ[ℝ] E) (γ : F) (τ : ℍ) :
    thetaCoset (ZLattice.comap ℝ L e.toLinearMap) γ τ =
      ∑' v : L, cexp (π * I * (‖γ + e.symm v‖ ^ 2 : ℝ) * τ) := by
  rw [thetaCoset_apply, ← (ZLattice.comap_equiv ℝ L e).toEquiv.tsum_eq]
  simp

/-- The theta series of translates are invariant under linear isometry equivalences:
`θ_{γ + e⁻¹(L)} = θ_{e γ + L}`. -/
@[simp]
theorem thetaCoset_comap (e : F ≃ₗᵢ[ℝ] E) (γ : F) :
    thetaCoset (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) γ = thetaCoset L (e γ) := by
  ext τ
  rw [thetaCoset_comap_apply, thetaCoset_apply]
  refine tsum_congr fun v ↦ ?_
  rw [← e.norm_map, map_add]
  simp

/-- Theta series are invariant under linear isometry equivalences: `Θ_{e⁻¹(L)} = Θ_L`. -/
@[simp]
theorem thetaSeries_comap (e : F ≃ₗᵢ[ℝ] E) :
    thetaSeries (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) = thetaSeries L := by
  simpa using thetaCoset_comap L e 0

/-! ### Scaling -/

/-- Scaling a lattice and a translation vector by `c ≠ 0` evaluates the theta series of the
translate at `c² τ`: `θ_{c γ + c L}(τ) = θ_{γ+L}(c² τ)`. -/
theorem thetaCoset_smul {c : ℝ} (hc : c ≠ 0) (γ : E) (τ : ℍ) :
    thetaCoset (c • L) (c • γ) τ =
      thetaCoset L γ ((⟨c ^ 2, by positivity⟩ : {x : ℝ // 0 < x}) • τ) := by
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹
  have he (v : E) : e.toLinearEquiv.symm v = c • v := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e, Units.smul_def, smul_smul, hc]
  -- `smul_eq_comap` pulls back along the coercion of `e` to a linear map, which is
  -- `e.toLinearEquiv.toLinearMap` by definition.
  have hL : c • L = ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap := smul_eq_comap L hc
  rw [hL, thetaCoset_comap_apply, thetaCoset_apply]
  refine tsum_congr fun v ↦ ?_
  rw [he, ← smul_add, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    UpperHalfPlane.coe_pos_real_smul, real_smul]
  push_cast
  congr 1
  ring

/-- Scaling a lattice by `c ≠ 0` evaluates its theta series at `c² τ`:
`Θ_{c L}(τ) = Θ_L(c² τ)`. -/
theorem thetaSeries_smul {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (c • L) τ =
      thetaSeries L ((⟨c ^ 2, by positivity⟩ : {x : ℝ // 0 < x}) • τ) := by
  simpa using thetaCoset_smul L hc 0 τ

/-! ### Orthogonal direct sums -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [DiscreteTopology L]
  (M : Submodule ℤ F) [DiscreteTopology M]

/-- The theta series of a translate of an orthogonal direct sum is the product of the theta
series of the translates of the summands: `θ_{(γ, δ) + (L ⊕ M)} = θ_{γ+L} · θ_{δ+M}`. -/
@[simp]
theorem thetaCoset_orthSum (x : WithLp 2 (E × F)) :
    thetaCoset (orthSum L M) x = thetaCoset L x.fst * thetaCoset M x.snd := by
  ext τ
  -- `L × M` is identified with `L ⊕ M` by `(v, w) ↦ (v, w)`.
  let e : L × M ≃ orthSum L M :=
    { toFun p := ⟨toLp 2 ((p.1 : E), (p.2 : F)), by simp⟩
      invFun v := (⟨v.1.fst, (mem_orthSum.mp v.2).1⟩, ⟨v.1.snd, (mem_orthSum.mp v.2).2⟩)
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Pi.mul_apply, thetaCoset_apply, thetaCoset_apply, thetaCoset_apply,
    tsum_mul_tsum_of_summable_norm (summable_thetaCoset L _ τ).norm
      (summable_thetaCoset M _ τ).norm, ← e.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  have he : ((e p : orthSum L M) : WithLp 2 (E × F)) = toLp 2 ((p.1 : E), (p.2 : F)) := rfl
  rw [← exp_add, prod_norm_sq_eq_of_L2, he]
  simp only [add_fst, add_snd, toLp_fst, toLp_snd]
  push_cast
  congr 1
  ring

/-- The theta series of an orthogonal direct sum is the product of the theta series of the
summands: `Θ_{L ⊕ M} = Θ_L · Θ_M`. -/
@[simp]
theorem thetaSeries_orthSum : thetaSeries (orthSum L M) = thetaSeries L * thetaSeries M := by
  simpa using thetaCoset_orthSum L M 0

end ZLattice
