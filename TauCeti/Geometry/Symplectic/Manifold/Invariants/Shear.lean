/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The symplectic shear of the plane

The shear `S(q, p) = (q + p, p)` of the plane `ℝ × ℝ` (`TauCeti.symplecticShear`) is the
transvection `x ↦ x + p(x) e₁` of Mathlib (`LinearEquiv.transvection`). It is a linear
symplectomorphism of the standard form `ω = dq ∧ dp`, that is `ω((q, p), (q', p')) = q p' - p q'`
(`TauCeti.stdSymplecticForm` on `ℝ × ℝ`)
(`TauCeti.isSymplectomorphism_symplecticShear`), and it generates a cyclic group `K` of linear
symplectomorphisms acting on `ℝ × ℝ`.

This group shows that the preserved metric cannot be dropped from the theorem that the fixed locus
of a group of symplectic isometries is a symplectic submanifold
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`):

* the fixed set of `K` is the line `ℝ × {0}`, at each of whose points the fixed tangent subspace is
  the same line (`TauCeti.fixedPoints_zpowers_symplecticShear`,
  `TauCeti.fixedPointsOfFinrank_zpowers_symplecticShear`), which is Lagrangian, not symplectic, for
  the constant form `ω` (`TauCeti.isLagrangian_fixedTangentSubspace_zpowers_symplecticShear`,
  `TauCeti.not_isSymplectic_fixedTangentSubspace_zpowers_symplecticShear`);
* no Riemannian metric `g` on `ℝ × ℝ`, smooth or not, is preserved by the differentials of `K`
  (`TauCeti.not_forall_inner_mfderiv_smul_zpowers_symplecticShear`), so the isometry hypothesis of
  that theorem fails for the Riemannian bundle structure given by any `g`.

The obstruction to an invariant metric is read off the derivative at the fixed point `0`, which is
`S` itself: `S` fixes `e₁` and sends `e₂` to `e₁ + e₂`, so a bilinear form `B` preserved by `S`
satisfies `B(e₁, e₂) = B(S e₁, S e₂) = B(e₁, e₁) + B(e₁, e₂)`, hence `B(e₁, e₁) = 0`
(`TauCeti.apply_one_zero_one_zero_eq_zero_of_symplecticShear`), and `B` is not positive definite.

## Main definitions

* `TauCeti.symplecticShear`: the shear `(q, p) ↦ (q + p, p)` of `ℝ × ℝ`.

## Main results

* `TauCeti.isSymplectomorphism_symplecticShear`: the shear preserves `ω = dq ∧ dp`.
* `TauCeti.fixedPoints_zpowers_symplecticShear`: the fixed set of the group it generates is the
  line `ℝ × {0}`.
* `TauCeti.isLagrangian_fixedTangentSubspace_zpowers_symplecticShear`: at every fixed point, the
  fixed tangent subspace is Lagrangian for `ω`.
* `TauCeti.not_forall_inner_mfderiv_smul_zpowers_symplecticShear`: no Riemannian metric is
  preserved by the differentials of the group.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
-/

public section

open Bundle MulAction Set
open scoped Manifold

noncomputable section

namespace TauCeti

/-- The shear `(q, p) ↦ (q + p, p)` of the plane `ℝ × ℝ`: the transvection `x ↦ x + x.2 • e₁`
along the first coordinate vector. -/
def symplecticShear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.transvection (show LinearMap.snd ℝ ℝ ℝ ((1 : ℝ), (0 : ℝ)) = 0 from rfl)

@[simp]
theorem symplecticShear_apply (x : ℝ × ℝ) : symplecticShear x = (x.1 + x.2, x.2) := by
  simp [symplecticShear, LinearMap.transvection.apply, Prod.ext_iff]

@[simp]
theorem symplecticShear_symm_apply (x : ℝ × ℝ) :
    symplecticShear.symm x = (x.1 - x.2, x.2) :=
  symplecticShear.symm_apply_eq.2 (by simp)

/-- **The shear is symplectic.** It preserves the standard form `ω = dq ∧ dp` of `ℝ × ℝ`. -/
theorem isSymplectomorphism_symplecticShear :
    SymplecticForm.IsSymplectomorphism stdSymplecticForm
      stdSymplecticForm symplecticShear :=
  SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by simp; ring

/-- The vectors of `ℝ × ℝ` fixed by the shear are those with second coordinate `0`. -/
theorem symplecticShear_apply_eq_self_iff {x : ℝ × ℝ} : symplecticShear x = x ↔ x.2 = 0 := by
  simp [Prod.ext_iff]

/-- **Bilinear forms invariant under the shear vanish on the fixed direction.** A bilinear form `B`
on `ℝ × ℝ` with `B (S u) (S w) = B u w` for the shear `S` satisfies `B e₁ e₁ = 0`, where
`e₁ = (1, 0)`; in particular no inner product on `ℝ × ℝ` is preserved by the shear. -/
theorem apply_one_zero_one_zero_eq_zero_of_symplecticShear {B : LinearMap.BilinForm ℝ (ℝ × ℝ)}
    (hB : ∀ u w, B (symplecticShear u) (symplecticShear w) = B u w) :
    B (1, 0) (1, 0) = 0 := by
  have h := hB (1, 0) (0, 1)
  simp only [symplecticShear_apply, add_zero, zero_add] at h
  rw [show ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) by simp, map_add] at h
  linarith

/-! ### The fixed set of the group generated by the shear -/

/-- **The fixed set of the shear.** The points of `ℝ × ℝ` fixed by the group generated by the shear
`(q, p) ↦ (q + p, p)` are those of the line `ℝ × {0}`. -/
theorem fixedPoints_zpowers_symplecticShear :
    fixedPoints (Subgroup.zpowers symplecticShear) (ℝ × ℝ) = {x | x.2 = 0} := by
  ext x
  simp only [mem_fixedPoints, Subtype.forall, Subgroup.smul_def, Subgroup.forall_mem_zpowers,
    ← mem_fixedBy]
  rw [mem_fixedBy_zpowers_iff_mem_fixedBy, mem_fixedBy, LinearEquiv.smul_def,
    symplecticShear_apply_eq_self_iff, mem_ofPred_eq]

/-- The vectors of `ℝ × ℝ` invariant under the group generated by the shear form the kernel of the
second projection. -/
theorem invariants_zpowers_symplecticShear :
    (Representation.ofDistribMulAction ℝ (Subgroup.zpowers symplecticShear) (ℝ × ℝ)).invariants =
      LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) := by
  ext x
  have := Set.ext_iff.1 fixedPoints_zpowers_symplecticShear x
  simp only [mem_fixedPoints, mem_ofPred_eq] at this
  simpa [Representation.mem_invariants] using this

/-- The line `ℝ × {0}` of vectors fixed by the shear is Lagrangian for `ω = dq ∧ dp`. -/
theorem isLagrangian_invariants_zpowers_symplecticShear :
    stdSymplecticForm.IsLagrangian
      (Representation.ofDistribMulAction ℝ (Subgroup.zpowers symplecticShear) (ℝ × ℝ)).invariants
      := by
  rw [invariants_zpowers_symplecticShear,
    show LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) = (⊤ : Submodule ℝ ℝ).prod ⊥ by ext; simp]
  exact SymplecticForm.isLagrangian_prod_top_bot

section Manifold

/-- The group generated by the shear acts on `ℝ × ℝ` by continuous linear maps. -/
local instance : ContinuousConstSMul (Subgroup.zpowers symplecticShear) (ℝ × ℝ) :=
  ⟨fun k ↦ (k : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)).toLinearMap.continuous_of_finiteDimensional⟩

/-- **The fixed tangent subspaces of the shear.** At a point of the line `ℝ × {0}`, the fixed
tangent subspace of the group generated by the shear is the line `ℝ × {0}` itself, the tangent
space `T_x (ℝ × ℝ)` being `ℝ × ℝ`. -/
theorem fixedTangentSubspace_zpowers_symplecticShear {x : ℝ × ℝ} (hx : x.2 = 0) :
    fixedTangentSubspace 𝓘(ℝ, ℝ × ℝ) (Subgroup.zpowers symplecticShear) x =
      LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) := by
  have h := map_fromTangentSpace_fixedTangentSubspace (K := Subgroup.zpowers symplecticShear)
    (show x ∈ fixedPoints _ (ℝ × ℝ) by rwa [fixedPoints_zpowers_symplecticShear])
  rw [invariants_zpowers_symplecticShear] at h
  -- The canonical identification `T_x (ℝ × ℝ) ≃ ℝ × ℝ` is the identity map `v ↦ v`.
  ext v
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · have := Submodule.mem_map_of_mem
      (f := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toLinearEquiv.toLinearMap) hv
    rw [h] at this
    exact this
  · rw [← h] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact hw

/-- **The fixed set of the shear has tangent dimension one.** The fixed set `ℝ × {0}` of the group
generated by the shear is the part of its fixed set at which the fixed tangent subspace has
dimension `1`. -/
theorem fixedPointsOfFinrank_zpowers_symplecticShear :
    fixedPointsOfFinrank 𝓘(ℝ, ℝ × ℝ) (Subgroup.zpowers symplecticShear) (ℝ × ℝ) 1 =
      {x | x.2 = 0} := by
  have h1 : Module.finrank ℝ (Representation.ofDistribMulAction ℝ
      (Subgroup.zpowers symplecticShear) (ℝ × ℝ)).invariants = 1 := by
    rw [invariants_zpowers_symplecticShear, LinearMap.ker_snd,
      LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]
  rw [← h1, fixedPointsOfFinrank_finrank_invariants, fixedPoints_zpowers_symplecticShear]

/-- **The fixed tangent subspaces of the shear are Lagrangian.** At every point of the fixed set
`ℝ × {0}` of the group generated by the shear, the fixed tangent subspace is Lagrangian for the
constant symplectic form `ω = dq ∧ dp`. So the fixed set of a group of linear symplectomorphisms
need not be a symplectic submanifold when the group preserves no metric. -/
theorem isLagrangian_fixedTangentSubspace_zpowers_symplecticShear {x : ℝ × ℝ} (hx : x.2 = 0) :
    ((SymplecticForm.isNondegenerate_constSmooth
        stdSymplecticForm).symplecticFormAt x).IsLagrangian
      (fixedTangentSubspace 𝓘(ℝ, ℝ × ℝ) (Subgroup.zpowers symplecticShear) x) := by
  -- `symplecticFormAt x` is `ω` on `T_x (ℝ × ℝ) = ℝ × ℝ`.
  rw [SymplecticForm.isNondegenerate_constSmooth_symplecticFormAt,
    fixedTangentSubspace_zpowers_symplecticShear hx, ← invariants_zpowers_symplecticShear]
  exact isLagrangian_invariants_zpowers_symplecticShear

/-- At every point of the fixed set of the group generated by the shear, the fixed tangent subspace
is not a symplectic subspace for `ω = dq ∧ dp`. -/
theorem not_isSymplectic_fixedTangentSubspace_zpowers_symplecticShear {x : ℝ × ℝ}
    (hx : x.2 = 0) :
    ¬ ((SymplecticForm.isNondegenerate_constSmooth
        stdSymplecticForm).symplecticFormAt x).IsSymplectic
      (fixedTangentSubspace 𝓘(ℝ, ℝ × ℝ) (Subgroup.zpowers symplecticShear) x) := by
  -- `symplecticFormAt x` is `ω` on `T_x (ℝ × ℝ) = ℝ × ℝ`.
  rw [SymplecticForm.isNondegenerate_constSmooth_symplecticFormAt,
    fixedTangentSubspace_zpowers_symplecticShear hx, ← invariants_zpowers_symplecticShear]
  intro hs
  have hbot := isLagrangian_invariants_zpowers_symplecticShear.isIsotropic.eq_bot_of_isSymplectic hs
  rw [invariants_zpowers_symplecticShear, Submodule.eq_bot_iff] at hbot
  simpa using hbot (1, 0) (by simp)

/-- **The shear preserves no Riemannian metric.** For every Riemannian metric `g` on the plane
`ℝ × ℝ`, smooth or not, the differentials of the group generated by the shear
`(q, p) ↦ (q + p, p)` do not all preserve `g`: already the differential of the shear at its fixed
point `0` does not. -/
theorem not_forall_inner_mfderiv_smul_zpowers_symplecticShear
    (g : RiemannianMetric (fun x : ℝ × ℝ ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ) x)) :
    ¬ ∀ (k : Subgroup.zpowers symplecticShear) (x : ℝ × ℝ)
        (u w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x),
      g.inner (k • x) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (k • ·) x u)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (k • ·) x w) =
        g.inner x u w := by
  intro h
  let k : Subgroup.zpowers symplecticShear := ⟨symplecticShear, Subgroup.mem_zpowers _⟩
  have hk : (fun y : ℝ × ℝ ↦ k • y) = symplecticShear.toContinuousLinearEquiv := by
    ext y <;> simp [k, Subgroup.smul_def]
  have h0 := apply_one_zero_one_zero_eq_zero_of_symplecticShear
    (B := (g.inner 0).toLinearMap₁₂) fun v w ↦ by
      have := h k 0 v w
      rw [hk, ContinuousLinearEquiv.mfderiv_eq] at this
      -- Every tangent space of `ℝ × ℝ` is `ℝ × ℝ`, so `g` at `k • 0 = 0` may be read at `0`.
      generalize hy : k • (0 : ℝ × ℝ) = y at this
      rw [smul_zero] at hy
      subst hy
      exact this
  have hne : ((1 : ℝ), (0 : ℝ)) ≠ 0 := by simp
  exact (g.pos 0 _ hne).ne' h0

end Manifold

end TauCeti
