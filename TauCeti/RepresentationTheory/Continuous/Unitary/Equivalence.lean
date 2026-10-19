/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Schur
public import TauCeti.RepresentationTheory.Continuous.Transport

/-!
# Equivalent irreducible unitary representations are unitarily equivalent

An equivalence of continuous representations is a linear equivalence intertwining the actions; it
need not respect the inner products. For finite-dimensional irreducible *unitary* representations
over an algebraically closed `RCLike` field it can always be rescaled to one that does, so the two
notions of equivalence coincide. Isometric transport preserves matrix coefficients when both
defining vectors move along the same map (`LinearIsometryEquiv.matrixCoeff_congr`).

This identifies equivalence classes of finite-dimensional irreducible unitary representations
with their unitary equivalence classes. It lets one choose representatives for the
finite-dimensional part of the unitary dual and transport their matrix coefficients while
preserving inner products.

## Main statements

* `ContRepresentation.exists_linearIsometryEquiv_congr_eq`: an equivalence between
  finite-dimensional irreducible unitary continuous representations can be replaced by a linear
  isometry equivalence transporting one onto the other.

The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

variable {𝕜 G V W : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

private local instance instCompleteSpaceUnitaryEquivalence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

/-- An equivalence between unitary continuous representations, with finite-dimensional irreducible
source, can be replaced by a linear isometry equivalence transporting the source onto the target.
The target is automatically finite-dimensional because it is equivalent to the source. -/
theorem exists_linearIsometryEquiv_congr_eq {π : ContRepresentation 𝕜 G V}
    {ρ : ContRepresentation 𝕜 G W} (hπu : IsUnitary π) (hρu : IsUnitary ρ)
    (hirr : π.toRepresentation.IsIrreducible) (φ : Equiv π ρ) :
    ∃ e : V ≃ₗᵢ[𝕜] W, ContinuousLinearEquiv.congr e.toContinuousLinearEquiv π = ρ := by
  let : FiniteDimensional 𝕜 W := φ.toLinearEquiv.finiteDimensional
  set T : V →L[𝕜] W := φ.toContIntertwiningMap.toContinuousLinearMap with hTdef
  have hT : ∀ g : G, T ∘L π g = ρ g ∘L T := fun g ↦ by
    rw [hTdef, ← φ.toContinuousLinearEquiv_toContinuousLinearMap]
    exact φ.isIntertwining g
  have hTapp : ∀ (g : G) (v : V), T (π g v) = ρ g (T v) := fun g v ↦ by
    simpa only [← φ.toContIntertwiningMap.toContinuousLinearMap_apply, ← hTdef] using
      φ.toContIntertwiningMap.isIntertwining g v
  -- The adjoint intertwines the other way, so `T† ∘ T` is a self-intertwiner of `π`
  have hadj : ∀ g : G, (ContinuousLinearMap.adjoint T) ∘L ρ g
      = π g ∘L ContinuousLinearMap.adjoint T := fun g ↦ by
    simpa only [ContinuousLinearMap.adjoint_comp, hπu.adjoint_eq_inv,
      hρu.adjoint_eq_inv, inv_inv] using
      (congrArg ContinuousLinearMap.adjoint (hT g⁻¹)).symm
  set Tadj : ContIntertwiningMap ρ π :=
    { toContinuousLinearMap := ContinuousLinearMap.adjoint T, isIntertwining' := hadj }
    with hTadjDef
  -- Project the field supplied in this local constructor before evaluating the composite.
  have hTadj : Tadj.toContinuousLinearMap = ContinuousLinearMap.adjoint T :=
    congrArg ContIntertwiningMap.toContinuousLinearMap hTadjDef
  -- Schur's lemma makes the composite intertwiner a scalar.
  obtain ⟨c, hc⟩ := π.exists_eq_smul_one_of_isIrreducible hirr
    (Tadj.comp φ.toContIntertwiningMap)
  have hcS : ∀ v : V, ContinuousLinearMap.adjoint T (T v) = c • v := fun v ↦ by
    simpa only [ContIntertwiningMap.toContinuousLinearMap_comp, hTadj, ← hTdef,
      ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_smul,
      smul_apply, ContIntertwiningMap.toContinuousLinearMap_one, one_apply_eq_self] using
      congrArg (fun f : ContIntertwiningMap π π ↦ f.toContinuousLinearMap v) hc
  have hinner : ∀ v : V, ((‖T v‖ : ℝ) : 𝕜) ^ 2 = (starRingEnd 𝕜) c * ((‖v‖ : ℝ) : 𝕜) ^ 2 := by
    intro v
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K,
      ← ContinuousLinearMap.adjoint_inner_left T v (T v), hcS v, inner_smul_left]
  have hnormSq : ∀ v : V, ‖T v‖ ^ 2 = ‖c‖ * ‖v‖ ^ 2 := fun v ↦ by
    simpa [norm_mul, norm_pow, RCLike.norm_ofReal] using congrArg norm (hinner v)
  -- Injectivity and the nonzero irreducible carrier make the scaling factor strictly positive.
  have : Nontrivial V := Representation.IsIrreducible.nontrivial hirr
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hv₀norm : (0 : ℝ) < ‖v₀‖ := norm_pos_iff.2 hv₀
  have hTinj : Function.Injective T := by
    intro x y hxy
    apply φ.toContinuousLinearEquiv.injective
    simpa only [φ.toContinuousLinearEquiv_apply,
      ← φ.toContIntertwiningMap.toContinuousLinearMap_apply, ← hTdef] using hxy
  have hTv₀ : (0 : ℝ) < ‖T v₀‖ := norm_pos_iff.2 fun h ↦
    hv₀ (hTinj (by simpa using h))
  have hcpos : 0 < ‖c‖ := (mul_pos_iff_of_pos_right (sq_pos_of_pos hv₀norm)).mp
    ((hnormSq v₀) ▸ sq_pos_of_pos hTv₀)
  have hnorm : ∀ v : V, ‖T v‖ = Real.sqrt ‖c‖ * ‖v‖ := fun v ↦ by
    rw [← Real.sqrt_sq (norm_nonneg (T v)), hnormSq v,
      Real.sqrt_mul (norm_nonneg c), Real.sqrt_sq (norm_nonneg v)]
  -- Rescaling by `1/√‖c‖` turns `T` into an isometry, which still intertwines
  have hsqrt : (0 : ℝ) < Real.sqrt ‖c‖ := Real.sqrt_pos.2 hcpos
  set b : 𝕜 := ((Real.sqrt ‖c‖ : ℝ) : 𝕜)⁻¹ with hb
  have hbne : b ≠ 0 := inv_ne_zero (by simpa using hsqrt.ne')
  have hbnorm : ‖b‖ = (Real.sqrt ‖c‖)⁻¹ := by
    rw [hb, norm_inv, RCLike.norm_ofReal, abs_of_pos hsqrt]
  let L : V ≃ₗ[𝕜] W :=
    φ.toContinuousLinearEquiv.toLinearEquiv.trans (LinearEquiv.smulOfNeZero 𝕜 W b hbne)
  have hL : ∀ v : V, L v = b • T v := fun v ↦ calc
    L v = b • φ.toContinuousLinearEquiv v := by
      simp only [L, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
    _ = b • φ.toContIntertwiningMap v :=
      congrArg (b • ·) (φ.toContinuousLinearEquiv_apply v)
    _ = b • T v := by
      rw [hTdef, ContIntertwiningMap.toContinuousLinearMap_apply]
  have hLnorm : ∀ v : V, ‖L v‖ = ‖v‖ := by
    intro v
    rw [hL, norm_smul, hbnorm, hnorm v, ← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
  set e : V ≃ₗᵢ[𝕜] W := ⟨L, hLnorm⟩
  have he : ∀ v : V, e v = b • T v := hL
  have key : ∀ (g : G) (v : V), e (π g v) = ρ g (e v) := fun g v ↦ by
    simp only [he, hTapp, map_smul]
  refine ⟨e, DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun x ↦ ?_⟩
  simp only [ContinuousLinearEquiv.congr_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, key, e.apply_symm_apply]

end ContRepresentation
