/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The covering map of a symplectic suspension

The map `TauCeti.SmoothMappingTorus.suspensionMk φ` sends `((s, t), x)` to `([s], [t, x])`.
It is a surjective smooth local diffeomorphism whose fibers are the orbits of the integer deck
transformations `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)`.

`TauCeti.SmoothMappingTorus.mfderiv_suspensionMk_apply` computes its differential, and
`TauCeti.SmoothMappingTorus.mpullback_suspensionMk_suspensionForm` identifies the pullback of the
suspension form `Ω = ds ∧ dt + σ_v` with the product form `ds ∧ dt + σ` on `(ℝ × ℝ) × M`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (the form `ds ∧ dt + ω_φ` on `ℝ × Y_φ`).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The covering map -/

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- The covering map `((s, t), x) ↦ ([s], [t, x])` of `(ℝ / ℤ) × Y_φ` by `(ℝ × ℝ) × M`. -/
def suspensionMk (p : (ℝ × ℝ) × M) : UnitAddCircle × SmoothMappingTorus φ :=
  ((p.1.1 : UnitAddCircle), mk φ p.1.2 p.2)

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
@[simp]
theorem suspensionMk_apply (s t : ℝ) (x : M) :
    suspensionMk φ ((s, t), x) = ((s : UnitAddCircle), mk φ t x) :=
  (rfl)

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
theorem suspensionMk_surjective : Surjective (suspensionMk φ) := by
  rintro ⟨θ, y⟩
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  exact ⟨((s, t), x), rfl⟩

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- Two points of `(ℝ × ℝ) × M` have the same image under `q` exactly when they differ by a
deck transformation `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)`. -/
theorem suspensionMk_eq_suspensionMk_iff {p p' : (ℝ × ℝ) × M} :
    suspensionMk φ p = suspensionMk φ p' ↔
      ∃ j k : ℤ, p' = (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) := by
  obtain ⟨⟨s, t⟩, x⟩ := p
  obtain ⟨⟨s', t'⟩, x'⟩ := p'
  have hs : ((s : UnitAddCircle) = s') ↔ ∃ j : ℤ, s' = s + j := by
    rw [eq_comm, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, mul_one]
    exact exists_congr fun j ↦ by constructor <;> intro h <;> linarith
  have ht : mk φ t x = mk φ t' x' ↔ ∃ k : ℤ, t' = t + k ∧ x' = (φ ^ (-k)) x := by
    rw [eq_comm, mk_eq_mk_iff]
  simp only [suspensionMk_apply, Prod.mk.injEq, hs, ht, Prod.mk_add_mk]
  constructor
  · rintro ⟨⟨j, hj⟩, k, hk, hx⟩
    exact ⟨j, k, ⟨hj, hk⟩, hx⟩
  · rintro ⟨j, k, ⟨hj, hk⟩, hx⟩
    exact ⟨⟨j, hj⟩, k, hk, hx⟩

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- The deck transformations `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)` preserve `q`. -/
theorem suspensionMk_deck (j k : ℤ) (p : (ℝ × ℝ) × M) :
    suspensionMk φ (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) = suspensionMk φ p :=
  ((suspensionMk_eq_suspensionMk_iff φ).2 ⟨j, k, rfl⟩).symm

theorem isLocalDiffeomorph_suspensionMk :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ (suspensionMk φ) := by
  -- Reassociating `(ℝ × ℝ) × M` as `ℝ × (ℝ × M)` is a diffeomorphism.
  -- Mathlib's `Diffeomorph.prodAssoc` requires the second and third factors to have the same
  -- model vector space; here they are `ℝ` and the arbitrary space `F`.
  have hfst : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ∞ (fun p : (ℝ × ℝ) × M ↦ p.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_fst
  have hsnd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ∞ (fun p : (ℝ × ℝ) × M ↦ p.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_fst
  let e : ((ℝ × ℝ) × M) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ).prod I, 𝓘(ℝ).prod (𝓘(ℝ).prod I)⟯ ℝ × (ℝ × M) :=
    { toEquiv := Equiv.prodAssoc ℝ ℝ M
      contMDiff_toFun := hfst.prodMk (hsnd.prodMk contMDiff_snd)
      contMDiff_invFun := (contMDiff_fst.prodMk_space (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd) }
  have hq : suspensionMk φ = Prod.map ((↑) : ℝ → UnitAddCircle) (uncurry (mk φ)) ∘ e := (rfl)
  rw [hq]
  exact fun p ↦ IsLocalDiffeomorphAt.comp (hf := e.isLocalDiffeomorph p)
    (hg := ((AddCircle.isLocalDiffeomorph_coe 1 ∞).prodMap (isLocalDiffeomorph_uncurry_mk φ)) (e p))

/-- The differential of `q` sends `a ∂_s + b ∂_t + v` at `((s, t), x)` to `a ∂_s` plus the image
of `(b, v)` under the differential of `(t, x) ↦ [t, x]`. -/
theorem mfderiv_suspensionMk_apply (s t : ℝ) (x : M) (u : ℝ × ℝ) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) ((s, t), x)
        ((Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v)) =
      (Manifold.tangentSpaceProdEquiv (suspensionMk φ ((s, t), x))).symm
        (u.1, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (u.2, v))) := by
  have h₀ : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (fun p : (ℝ × ℝ) × M ↦ p.1.1) ((s, t), x)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) F)) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasMFDerivAt.comp ((s, t), x) (hasMFDerivAt_fst _)
  have h₁ := (AddCircle.hasMFDerivAt_coe (1 : ℝ) s).comp ((s, t), x) h₀
  have h₂ : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod I) (fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2))
      ((s, t), x) (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) F)).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) F)) :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasMFDerivAt.comp ((s, t), x) (hasMFDerivAt_fst _)).prodMk
      (hasMFDerivAt_snd _)
  have h₃ := (((contMDiff_uncurry_mk φ (t, x)).mdifferentiableAt (by simp)).hasMFDerivAt).comp
    ((s, t), x) h₂
  have h : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ)
      ((s, t), x) _ := h₁.prodMk h₃
  rw [h.mfderiv, Manifold.tangentSpaceProdEquiv_symm_apply,
    Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  -- The derivative of `q` acts on `(u, v)` componentwise.
  rfl

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The form `Ω = ds ∧ dt + σ_v` of the suspension pulls back along `q` to the form `ds ∧ dt + σ`
of `(ℝ × ℝ) × M`. -/
theorem mpullback_suspensionMk_suspensionForm :
    SmoothForm.mpullback (suspensionMk φ) (isLocalDiffeomorph_suspensionMk φ).contMDiff
        (suspensionForm φ σ hσ) =
      (stdSymplecticForm (V := ℝ)).constSmooth.prod σ := by
  refine SmoothBundleForm.ext_eval₂ fun ⟨⟨s, t⟩, x⟩ V W ↦ ?_
  -- Write `V` and `W` through their components.
  obtain ⟨u, v, rfl⟩ : ∃ (u : ℝ × ℝ) (v : TangentSpace I x),
      (Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v) = V :=
    ⟨_, _, ContinuousLinearEquiv.symm_apply_apply _ V⟩
  obtain ⟨u', v', rfl⟩ : ∃ (u : ℝ × ℝ) (v : TangentSpace I x),
      (Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v) = W :=
    ⟨_, _, ContinuousLinearEquiv.symm_apply_apply _ W⟩
  rw [SmoothForm.eval₂_mpullback, mfderiv_suspensionMk_apply, mfderiv_suspensionMk_apply,
    suspensionMk_apply, eval₂_suspensionForm_mk, SmoothTwoForm.eval₂_prod,
    SymplecticForm.fromTangentSpace_constSmooth_apply, stdSymplecticForm_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply, Real.inner_apply]
  -- `NormedSpace.fromTangentSpace` is the identity of `ℝ × ℝ`.
  change u.1 * u'.2 - u'.1 * u.2 + _ = u.1 * u'.2 - u.2 * u'.1 + _
  ring

end TauCeti.SmoothMappingTorus
