/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Prod
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# Canonical cotangent forms of a product

Under the identification `Φ : T*(M × N) ≃ T*M × T*N` of
`TauCeti.CotangentBundle.prodDiffeomorph`, the Liouville form of a product is the sum of the
Liouville forms of the factors, pulled back along the two projections:

`Φ^* (pr₁^* λ_M + pr₂^* λ_N) = λ_(M × N)`
(`TauCeti.CotangentBundle.mpullback_prodDiffeomorph_liouvilleForm`).

Indeed `Φ` covers the identity of `M × N`, so the projections of `T*M` and `T*N` composed with
`pr₁ ∘ Φ` and `pr₂ ∘ Φ` are the components of the projection of `T*(M × N)`; and a covector on the
product evaluates a tangent vector as the sum of its two restrictions evaluated on the components.
Since exterior differentiation commutes with pullback, the canonical symplectic form `ω = -dλ` of
the product is the product of the canonical symplectic forms of the factors:

`Φ^* (pr₁^* ω_M + pr₂^* ω_N) = ω_(M × N)`
(`TauCeti.CotangentBundle.mpullback_prodDiffeomorph_symplecticForm`).

Both identities equivalently hold along the inverse diffeomorphism, where they read
`(Φ⁻¹)^* λ_(M × N) = pr₁^* λ_M + pr₂^* λ_N` and `(Φ⁻¹)^* ω_(M × N) = pr₁^* ω_M + pr₂^* ω_N`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

section Liouville

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- `Φ` covers the identity of `M × N`, so differentiating `π_M ∘ pr₁ ∘ Φ = pr₁ ∘ π` gives
`dπ_M ∘ d pr₁ ∘ dΦ = d pr₁ ∘ dπ`. -/
private theorem mfderiv_proj_fst_prodDiffeomorph (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ)) z) :
    mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
        (prodDiffeomorph I J M N z).1
        (mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Prod.fst (prodDiffeomorph I J M N z)
          (mfderiv ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ))
            ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (prodDiffeomorph I J M N) z v)) =
      mfderiv (I.prod J) I Prod.fst z.proj
        (mfderiv ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ)) (I.prod J)
          (π (E × F →L[ℝ] ℝ) (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ)) z v) := by
  have hπM := (contMDiff_proj (IB := I) (F := E →L[ℝ] ℝ) (n := ∞)
    (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).mdifferentiable (by simp)
    (prodDiffeomorph I J M N z).1
  have hπ := (contMDiff_proj (IB := I.prod J) (F := E × F →L[ℝ] ℝ) (n := ∞)
    (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ)).mdifferentiable (by simp) z
  have hΦ := (prodDiffeomorph I J M N).mdifferentiable (by simp) z
  have hfst : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Prod.fst (prodDiffeomorph I J M N z) :=
    mdifferentiableAt_fst
  have hfst' : MDifferentiableAt (I.prod J) I Prod.fst z.proj := mdifferentiableAt_fst
  have hcov : (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘ Prod.fst) ∘
      prodDiffeomorph I J M N = Prod.fst ∘ π (E × F →L[ℝ] ℝ)
        (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ) :=
    funext proj_prodDiffeomorph_fst
  rw [← mfderiv_comp_apply _ hπM hfst, ← mfderiv_comp_apply z (hπM.comp _ hfst) hΦ, hcov,
    mfderiv_comp_apply z hfst' hπ]

/-- `Φ` covers the identity of `M × N`, so differentiating `π_N ∘ pr₂ ∘ Φ = pr₂ ∘ π` gives
`dπ_N ∘ d pr₂ ∘ dΦ = d pr₂ ∘ dπ`. -/
private theorem mfderiv_proj_snd_prodDiffeomorph (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ)) z) :
    mfderiv (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J (π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ))
        (prodDiffeomorph I J M N z).2
        (mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Prod.snd (prodDiffeomorph I J M N z)
          (mfderiv ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ))
            ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (prodDiffeomorph I J M N) z v)) =
      mfderiv (I.prod J) J Prod.snd z.proj
        (mfderiv ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] ℝ)) (I.prod J)
          (π (E × F →L[ℝ] ℝ) (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ)) z v) := by
  have hπN := (contMDiff_proj (IB := J) (F := F →L[ℝ] ℝ) (n := ∞)
    (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ)).mdifferentiable (by simp)
    (prodDiffeomorph I J M N z).2
  have hπ := (contMDiff_proj (IB := I.prod J) (F := E × F →L[ℝ] ℝ) (n := ∞)
    (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ)).mdifferentiable (by simp) z
  have hΦ := (prodDiffeomorph I J M N).mdifferentiable (by simp) z
  have hsnd : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Prod.snd (prodDiffeomorph I J M N z) :=
    mdifferentiableAt_snd
  have hsnd' : MDifferentiableAt (I.prod J) J Prod.snd z.proj := mdifferentiableAt_snd
  have hcov : (π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) ∘ Prod.snd) ∘
      prodDiffeomorph I J M N = Prod.snd ∘ π (E × F →L[ℝ] ℝ)
        (fun p : M × N ↦ TangentSpace (I.prod J) p →L[ℝ] ℝ) :=
    funext proj_prodDiffeomorph_snd
  rw [← mfderiv_comp_apply _ hπN hsnd, ← mfderiv_comp_apply z (hπN.comp _ hsnd) hΦ, hcov,
    mfderiv_comp_apply z hsnd' hπ]

/-- **The Liouville form of a product is the sum of the Liouville forms of the factors.** The
identification `T*(M × N) ≃ T*M × T*N` pulls `pr₁^* λ_M + pr₂^* λ_N` back to `λ_(M × N)`. -/
@[simp]
theorem mpullback_prodDiffeomorph_liouvilleForm :
    SmoothForm.mpullback (prodDiffeomorph I J M N) (prodDiffeomorph I J M N).contMDiff
        (SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M) +
          SmoothForm.mpullback Prod.snd contMDiff_snd (liouvilleForm J N)) =
      liouvilleForm (I.prod J) (M × N) := by
  apply Subtype.ext
  funext z
  ext v
  rw [map_add, SmoothForm.add_toRoughForm, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  simp only [SmoothForm.mpullback_apply, liouvilleForm_apply]
  exact (congrArg₂ (· + ·) (congrArg _ (mfderiv_proj_fst_prodDiffeomorph z (v 0)))
    (congrArg _ (mfderiv_proj_snd_prodDiffeomorph z (v 0)))).trans
    (snd_apply_eq_prodDiffeomorph_add z _).symm

end Liouville

section Symplectic

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The pullback of the canonical symplectic form along a smooth map is minus the exterior
derivative of the pullback of the Liouville form. -/
private theorem mpullback_symplecticForm_eq_neg {X EX HX : Type*} [NormedAddCommGroup EX]
    [NormedSpace ℝ EX] [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X]
    [ChartedSpace HX X] [IsManifold IX ∞ X] (f : X → CotangentBundle I M)
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f) :
    SmoothForm.mpullback f hf (symplecticForm I M) =
      -mextDerivₗ IX 1 (SmoothForm.mpullback f hf (liouvilleForm I M)) := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, SmoothForm.mextDerivₗ_mpullback]

/-- On `T*M × T*N`, the sum of the pulled-back canonical symplectic forms is minus the exterior
derivative of the sum of the pulled-back Liouville forms. -/
private theorem add_mpullback_symplecticForm :
    SmoothForm.mpullback Prod.fst contMDiff_fst (symplecticForm I M) +
        SmoothForm.mpullback Prod.snd contMDiff_snd (symplecticForm J N) =
      -mextDerivₗ ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))) 1
        (SmoothForm.mpullback Prod.fst contMDiff_fst (liouvilleForm I M) +
          SmoothForm.mpullback Prod.snd contMDiff_snd (liouvilleForm J N)) := by
  have hfst : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Prod.fst : CotangentBundle I M × CotangentBundle J N → _) :=
    contMDiff_fst
  have hsnd : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ (Prod.snd : CotangentBundle I M × CotangentBundle J N → _) :=
    contMDiff_snd
  -- Term-mode steps: rewriting inside these large form types is expensive.
  exact (congrArg₂ (· + ·) (mpullback_symplecticForm_eq_neg (I := I) (M := M) _ hfst)
    (mpullback_symplecticForm_eq_neg (I := J) (M := N) _ hsnd)).trans
    ((neg_add _ _).symm.trans (congrArg Neg.neg (map_add _ _ _).symm))

/-- **The canonical symplectic form of a product is the product of the canonical symplectic forms
of the factors.** The identification `T*(M × N) ≃ T*M × T*N` pulls `pr₁^* ω_M + pr₂^* ω_N` back
to `ω_(M × N)`. -/
@[simp]
theorem mpullback_prodDiffeomorph_symplecticForm :
    SmoothForm.mpullback (prodDiffeomorph I J M N) (prodDiffeomorph I J M N).contMDiff
        (SmoothForm.mpullback Prod.fst contMDiff_fst (symplecticForm I M) +
          SmoothForm.mpullback Prod.snd contMDiff_snd (symplecticForm J N)) =
      symplecticForm (I.prod J) (M × N) := by
  -- Exterior differentiation commutes with pullback, so this follows from the Liouville identity.
  exact (congrArg _ (add_mpullback_symplecticForm (I := I) (J := J) (M := M) (N := N))).trans
    ((map_neg _ _).trans (congrArg Neg.neg ((SmoothForm.mextDerivₗ_mpullback _ _ 1 _).symm.trans
      (congrArg _ (mpullback_prodDiffeomorph_liouvilleForm (I := I) (J := J) (M := M)
        (N := N)))))) |>.trans symplecticForm_eq_neg_mextDerivₗ.symm

end Symplectic

end TauCeti.CotangentBundle
