/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Manifold.Diffeomorph.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod

/-!
# The covering map of a symplectic suspension

The map `((s, t), x) ↦ ([s], [t, x])` from `(ℝ × ℝ) × M` to the symplectic suspension
`(ℝ / ℤ) × Y_φ` is a surjective smooth local diffeomorphism. Its fibres are the orbits of
`((s, t), x) ↦ ((s + n, t + k), φ ^ (-k) x)` for integers `n` and `k`.

This file describes its differential and proves that it pulls the suspension form
`Ω = ds ∧ dt + σ_v` back to the product form `ds ∧ dt + σ`. These identities allow tensor
constructions on the product to descend to the suspension.

They also compute the orientation of the symplectic suspension. When `σ` is nondegenerate, the
symplectic orientation of `Ω` is `ds ∧ dt` followed by the symplectic orientation of the fibre: the
covering map is orientation preserving at every point from the product of the standard orientation
of the `(s, t)`-plane with the symplectic orientation of `(M, σ)` to the symplectic orientation of
`(X_φ, Ω)` (`TauCeti.SmoothMappingTorus.isOrientationPreservingAt_suspensionCover`). So a frame
`(∂_s, T, e₁, …, e₂ₙ)` at `([s], [t, x])` is positive for `Ω`, where `T` is the suspension vector
field and `(e₁, …, e₂ₙ)` is the image, under the differential of the fibre inclusion
`y ↦ [t, y]`, of a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` of `(T_x M, σ_x)`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301–354, Section 2.
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The covering map -/

/-- The covering map `((s, t), x) ↦ ([s], [t, x])` of the product `(ℝ / ℤ) × Y_φ` of a circle with
the mapping torus of `φ` by `(ℝ × ℝ) × M`. -/
def suspensionCover (p : (ℝ × ℝ) × M) : UnitAddCircle × SmoothMappingTorus φ :=
  ((p.1.1 : UnitAddCircle), mk φ p.1.2 p.2)

/-- The covering map sends `((s, t), x)` to `([s], [t, x])`. -/
@[simp]
theorem suspensionCover_apply (s t : ℝ) (x : M) :
    suspensionCover φ ((s, t), x) = ((s : UnitAddCircle), mk φ t x) :=
  (rfl)

/-- The covering map is surjective. -/
theorem suspensionCover_surjective : Surjective (suspensionCover φ) := by
  rintro ⟨θ, y⟩
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  exact ⟨((s, t), x), rfl⟩

/-- Two points of `(ℝ × ℝ) × M` have the same image under the covering map exactly when they
differ by a deck transformation `((s, t), x) ↦ ((s + n, t + k), φ ^ (-k) x)`. -/
theorem suspensionCover_eq_suspensionCover_iff {p p' : (ℝ × ℝ) × M} :
    suspensionCover φ p = suspensionCover φ p' ↔
      ∃ n k : ℤ, p = (p'.1 + ((n : ℝ), (k : ℝ)), (φ ^ (-k)) p'.2) := by
  obtain ⟨⟨s, t⟩, x⟩ := p
  obtain ⟨⟨s', t'⟩, x'⟩ := p'
  simp only [suspensionCover_apply, Prod.mk.injEq, mk_eq_mk_iff, Prod.mk_add_mk]
  constructor
  · rintro ⟨hs, k, ht, hx⟩
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hs.symm)
    exact ⟨n, k, ⟨by linarith [show (n : ℝ) = -s' + s by simpa using hn], ht⟩, hx⟩
  · rintro ⟨n, k, ⟨hs, ht⟩, hx⟩
    refine ⟨?_, k, ht, hx⟩
    rw [hs, QuotientAddGroup.eq]
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨-n, by rw [zsmul_eq_mul, mul_one]; push_cast; ring⟩

/-- Integer deck transformations preserve the suspension covering map. -/
theorem suspensionCover_deck (j k : ℤ) (p : (ℝ × ℝ) × M) :
    suspensionCover φ (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) = suspensionCover φ p :=
  (suspensionCover_eq_suspensionCover_iff φ).2 ⟨j, k, rfl⟩

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]

/-- The covering map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_suspensionCover :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞
      (suspensionCover φ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h : suspensionCover φ = Prod.map (↑) (uncurry (mk φ)) ∘
      Diffeomorph.prodAssocOfModels 𝓘(ℝ) 𝓘(ℝ) I ℝ ℝ M ∞ := by
    funext ⟨⟨s, t⟩, x⟩
    simp only [Function.comp_apply, Diffeomorph.prodAssocOfModels_apply,
      Prod.map_apply, suspensionCover_apply, Function.uncurry_apply_pair]
  rw [h]
  intro p
  exact ((Diffeomorph.prodAssocOfModels 𝓘(ℝ) 𝓘(ℝ) I ℝ ℝ M ∞).isLocalDiffeomorph p).comp _ _
    (IsLocalDiffeomorph.prodMap (AddCircle.isLocalDiffeomorph_coe 1 ∞)
      (isLocalDiffeomorph_uncurry_mk φ) _)

/-- The differential of the covering map in the coordinates `(s, t, x)`: it sends the tangent
vector `((a, b), v)` of `(ℝ × ℝ) × M` to `a ∂_s` plus the image of `(b, v)` under the differential
of `(t, x) ↦ [t, x]`. -/
theorem mfderiv_suspensionCover_apply (p : (ℝ × ℝ) × M)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p v =
      (Manifold.tangentSpaceProdEquiv (suspensionCover φ p)).symm
        ((NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).1,
          mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (p.1.2, p.2)
            ((Manifold.tangentSpaceProdEquiv (p.1.2, p.2)).symm
              ((NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).2,
                (Manifold.tangentSpaceProdEquiv p v).2))) := by
  have hs := (AddCircle.hasMFDerivAt_coe 1 p.1.1).comp p
    ((hasFDerivAt_fst.hasMFDerivAt).comp p (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I) p))
  have hpair : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod I)
      (fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2)) p
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) E)).prod
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) E)) :=
    ((hasFDerivAt_snd.hasMFDerivAt).comp p (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I) p)).prodMk
      (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I) p)
  have hmk := (((isLocalDiffeomorph_uncurry_mk φ (n := ∞)) (p.1.2, p.2)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p hpair
  have hd : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p
      _ := hs.prodMk hmk
  rw [hd.mfderiv]
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  rw [Manifold.tangentSpaceProdEquiv_symm_apply (I := 𝓘(ℝ)) (J := I) (p.1.2, p.2)]
  -- Tangent spaces of products and of the plane are the model spaces, so the composite
  -- derivative evaluates componentwise by definition.
  rfl

/-! ### The pulled back symplectic form -/

variable {φ} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The covering map pulls the form `Ω = ds ∧ dt + σ_v` of `(ℝ / ℤ) × Y_φ` back to the product form
`ds ∧ dt + σ` of `(ℝ × ℝ) × M`, whose first factor is the standard symplectic form of the plane. -/
theorem mpullback_suspensionCover_suspensionForm :
    SmoothForm.mpullback (suspensionCover φ) (isLocalDiffeomorph_suspensionCover φ).contMDiff
        (suspensionForm φ σ hσ) =
      (stdSymplecticForm (V := ℝ)).constSmooth.prod σ := by
  apply SmoothBundleForm.ext_eval₂
  intro p v w
  obtain ⟨⟨s, t⟩, x⟩ := p
  rw [SmoothForm.eval₂_mpullback, mfderiv_suspensionCover_apply, mfderiv_suspensionCover_apply,
    suspensionCover_apply, eval₂_suspensionForm_mk, SmoothTwoForm.eval₂_prod,
    SymplecticForm.fromTangentSpace_constSmooth_apply, stdSymplecticForm_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-! ### The orientation of the symplectic suspension -/

/-- **The orientation of a symplectic suspension.** For a nondegenerate `σ`, the covering map
`((s, t), x) ↦ ([s], [t, x])` is orientation preserving at every point, from the standard
orientation of the `(s, t)`-plane followed by the symplectic orientation of `(M, σ)` to the
symplectic orientation of `Ω = ds ∧ dt + σ_v` on `(ℝ / ℤ) × Y_φ`. -/
theorem isOrientationPreservingAt_suspensionCover [FiniteDimensional ℝ E]
    (hσn : σ.IsNondegenerate) {n : ℕ} (hn : Module.finrank ℝ E = n) (p : (ℝ × ℝ) × M) :
    Manifold.Orientation.IsOrientationPreservingAt
      ((Manifold.Orientation.model (I := 𝓘(ℝ, ℝ × ℝ)) (Module.Basis.finTwoProd ℝ).orientation
        (by simp)).prod (hσn.orientation hn))
      (((isNondegenerate_suspensionForm_iff (hσ := hσ)).2 hσn).orientation
        (by simp only [Module.finrank_prod, Module.finrank_self, hn]; omega))
      (suspensionCover φ) p := by
  have hstd := SymplecticForm.isNondegenerate_constSmooth (stdSymplecticForm (V := ℝ))
  have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [← SymplecticForm.orientation_stdSymplecticForm_real h2,
    ← SymplecticForm.orientation_constSmooth, ← hstd.orientation_prod hσn h2 hn]
  exact (hstd.prod hσn).isOrientationPreservingAt_orientation _ _ _
    (isLocalDiffeomorph_suspensionCover φ).contMDiff mpullback_suspensionCover_suspensionForm p

end TauCeti.SmoothMappingTorus
