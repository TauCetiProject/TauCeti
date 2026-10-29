/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth block almost complex structures

On `P × M`, combine a smooth almost complex structure on `P` with a jointly smooth family
of almost complex structures on `T_x M`, allowed to depend on both `p` and `x`. The result
acts diagonally under the canonical product tangent identification. In particular, for
`P = ℝ × ℝ` with its standard structure, it sends `(a, b, v)` to `(-b, a, J_(s,t,x) v)`.
This permits time-dependent vertical structures in symplectic suspensions without requiring
the monodromy to preserve one fixed almost complex structure.

The evaluation formula splits the associated quadratic form into horizontal and vertical
terms. Compatible vertical families therefore give a compatible block structure for the
product two-form. Equivariance under a product map reduces to equivariance of its two
blocks; for a translation and a monodromy map this is precisely the vertical seam equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (compatible almost complex structures).
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301–354 (block structures on suspensions).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  (J : SmoothAlmostComplexStructure I P)
  (K : ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2))
  (hK : ContMDiff (I.prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

private def prodFamilyEndomorphism (p : P × M) :
    TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p :=
  -- Product tangent fibres and the product of tangent fibres have the same model-space
  -- representation; the public evaluation lemma uses their canonical identification.
  (J.toEndomorphism p.1).prodMap (K p).toLinearMap.toContinuousLinearMap

include hK in
private theorem contMDiff_prodFamilyEndomorphism :
    ContMDiff (I.prod I') ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) ∞
      (fun p ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F) p
        (prodFamilyEndomorphism J K p)) := by
  apply (Manifold.contMDiff_hom_iff _).2
  intro V hV
  have hsplit := contMDiff_equivTangentBundleProd.comp hV
  have hhorizontal := J.contMDiff_apply contMDiff_fst hsplit.fst
  have hvertical := hK.clm_bundle_apply hsplit.snd
  exact contMDiff_equivTangentBundleProd_symm.comp (hhorizontal.prodMk hvertical)

/-- The smooth block structure on `P × M` with horizontal block `J` and a jointly smooth
vertical family `K_(p,x)`. The vertical block may depend on both coordinates. -/
def prodFamily : SmoothAlmostComplexStructure (I.prod I') (P × M) where
  toEndomorphism := ⟨prodFamilyEndomorphism J K, contMDiff_prodFamilyEndomorphism J K hK⟩
  square_neg := by
    intro p
    ext v
    exact Prod.ext (J.apply_apply p.1 v.1) ((K p).apply_apply v.2)

/-- A block structure acts separately on the two components of a product tangent vector. -/
@[simp]
theorem prodFamily_apply (p : P × M) (v : TangentSpace (I.prod I') p) :
    prodFamily J K hK p v = (Manifold.tangentSpaceProdEquiv p).symm
      (J p.1 (Manifold.tangentSpaceProdEquiv p v).1,
        K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  rfl

/-- The quadratic form of a product two-form and a block almost complex structure is the sum
of its horizontal and vertical quadratic forms. -/
theorem eval₂_prod_prodFamily (σ : SmoothTwoForm I P) (τ : SmoothTwoForm I' M)
    (p : P × M) (v : TangentSpace (I.prod I') p) :
    (σ.prod τ).eval₂ p v (prodFamily J K hK p v) =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (J p.1 (Manifold.tangentSpaceProdEquiv p v).1) +
      τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  rw [SmoothTwoForm.eval₂_prod, prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- If each block is tamed by its factor two-form, the block structure is tamed by the
product form. -/
theorem tames_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Tames J)
    (hτ : ∀ (p : P × M) (v : TangentSpace I' p.2), v ≠ 0 →
      0 < τ.eval₂ p.2 v (K p v)) :
    (σ.prod τ).Tames (prodFamily J K hK) := by
  rw [SmoothTwoForm.tames_iff] at hσ ⊢
  intro p v hv
  rw [eval₂_prod_prodFamily]
  have hσ0 : ∀ u : TangentSpace I p.1, 0 ≤ σ.eval₂ p.1 u (J p.1 u) := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]
    · exact (hσ p.1 u hu).le
  have hτ0 : ∀ w : TangentSpace I' p.2, 0 ≤ τ.eval₂ p.2 w (K p w) := by
    intro w
    by_cases hw : w = 0
    · subst w
      rw [← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]
    · exact (hτ p w hw).le
  by_cases hu : (Manifold.tangentSpaceProdEquiv p v).1 = 0
  · have hw : (Manifold.tangentSpaceProdEquiv p v).2 ≠ 0 := by
      intro hw
      apply hv
      exact (Manifold.tangentSpaceProdEquiv p).map_eq_zero_iff.1 (Prod.ext hu hw)
    exact add_pos_of_nonneg_of_pos (hσ0 _) (hτ p _ hw)
  · exact add_pos_of_pos_of_nonneg (hσ p.1 _ hu) (hτ0 _)

/-- Invariance of each block gives invariance of the product form. -/
theorem invariant_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Invariant J)
    (hτ : ∀ (p : P × M) (v w : TangentSpace I' p.2),
      τ.eval₂ p.2 (K p v) (K p w) = τ.eval₂ p.2 v w) :
    (σ.prod τ).Invariant (prodFamily J K hK) := by
  rw [SmoothTwoForm.invariant_iff] at hσ ⊢
  intro p v w
  simp only [SmoothTwoForm.eval₂_prod, prodFamily_apply,
    ContinuousLinearEquiv.apply_symm_apply, hσ p.1, hτ p]

/-- Compatible vertical families and a compatible horizontal block give a block structure
compatible with the product two-form. -/
theorem compatible_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Compatible J) (hτ : τ.IsNondegenerate)
    (hcompat : ∀ p : P × M, (hτ.symplecticFormAt p.2).Compatible (K p)) :
    (σ.prod τ).Compatible (prodFamily J K hK) := by
  refine ⟨invariant_prodFamily J K hK hσ.invariant ?_,
    tames_prodFamily J K hK hσ.tames ?_⟩
  · intro p v w
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
      (hcompat p).invariant_apply v w
  · intro p v hv
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
      (hcompat p).tames v hv

/-- A product map intertwines the block structure at a point precisely when its horizontal
differential intertwines `J` and its vertical differential intertwines the corresponding
members of `K`. In a suspension the second condition is the seam equation. -/
theorem mfderiv_prodMap_prodFamily_iff {f : P → P} {g : M → M} (p : P × M)
    (hf : MDifferentiableAt I I f p.1) (hg : MDifferentiableAt I' I' g p.2) :
    (∀ v : TangentSpace (I.prod I') p,
      mfderiv (I.prod I') (I.prod I') (Prod.map f g) p (prodFamily J K hK p v) =
        prodFamily J K hK (f p.1, g p.2)
          (mfderiv (I.prod I') (I.prod I') (Prod.map f g) p v)) ↔
      (∀ u : TangentSpace I p.1,
        mfderiv I I f p.1 (J p.1 u) = J (f p.1) (mfderiv I I f p.1 u)) ∧
      (∀ w : TangentSpace I' p.2,
        mfderiv I' I' g p.2 (K p w) = K (f p.1, g p.2) (mfderiv I' I' g p.2 w)) := by
  constructor
  · intro h
    constructor
    · intro u
      have hu := h ((Manifold.tangentSpaceProdEquiv p).symm (u, 0))
      simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
        Manifold.mfderiv_prodMap_apply hf hg] at hu
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (fun v ↦ (Manifold.tangentSpaceProdEquiv (f p.1, g p.2) v).1) hu
    · intro w
      have hw := h ((Manifold.tangentSpaceProdEquiv p).symm (0, w))
      simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
        Manifold.mfderiv_prodMap_apply hf hg] at hw
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (fun v ↦ (Manifold.tangentSpaceProdEquiv (f p.1, g p.2) v).2) hw
  · rintro ⟨hfJ, hgK⟩ v
    obtain ⟨v, rfl⟩ := (Manifold.tangentSpaceProdEquiv p).symm.surjective v
    simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
      Manifold.mfderiv_prodMap_apply hf hg]
    exact congrArg (Manifold.tangentSpaceProdEquiv (f p.1, g p.2)).symm
      (Prod.ext (hfJ v.1) (hgK v.2))

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {F H' M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I' p.2))
  (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

/-- For the standard horizontal block `J∂s = ∂t`, `J∂t = -∂s`, the quadratic form of
`ds ∧ dt + τ` is `a² + b² + τ(v, K v)`. The vertical family is arbitrary and may depend on
both time coordinates. -/
theorem eval₂_prod_prodFamily_standard (τ : SmoothTwoForm I' M) (p : (ℝ × ℝ) × M)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I') p) :
    ((stdSymplecticForm (V := ℝ)).constSmooth.prod τ).eval₂ p v
        (prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK p v) =
      (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).1 ^ 2 +
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).2 ^ 2 +
        τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  rw [eval₂_prod_prodFamily, SymplecticForm.fromTangentSpace_constSmooth_apply,
    AlmostComplexStructure.fromTangentSpace_constSmooth_apply, stdSymplecticForm_apply_product_self]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Under a translation of the time plane and a fibre diffeomorphism `g`, the standard block
structure is invariant exactly when its vertical family obeys the seam equation. Taking
`c = (0, 1)` and `g = φ.symm` gives the mapping-torus deck generator; taking `c = (1, 0)` and
`g = Diffeomorph.refl I' M ∞` gives the other time-circle generator. -/
theorem mfderiv_translation_prodFamily_iff (c : ℝ × ℝ) (g : M ≃ₘ⟮I', I'⟯ M)
    (p : (ℝ × ℝ) × M) :
    (∀ v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I') p,
      mfderiv (𝓘(ℝ, ℝ × ℝ).prod I') (𝓘(ℝ, ℝ × ℝ).prod I')
          (Prod.map (fun q ↦ q + c) g) p
          (prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK p v) =
        prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK (p.1 + c, g p.2)
          (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I') (𝓘(ℝ, ℝ × ℝ).prod I')
            (Prod.map (fun q ↦ q + c) g) p v)) ↔
      ∀ w : TangentSpace I' p.2,
        mfderiv I' I' g p.2 (K p w) = K (p.1 + c, g p.2) (mfderiv I' I' g p.2 w) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1 :=
    (differentiableAt_id.add_const c).mdifferentiableAt
  rw [mfderiv_prodMap_prodFamily_iff _ _ _ _ hf (g.mdifferentiable (by simp) p.2)]
  have hhorizontal : ∀ u : TangentSpace 𝓘(ℝ, ℝ × ℝ) p.1,
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1
          ((AlmostComplexStructure.product ℝ).constSmooth p.1 u) =
        (AlmostComplexStructure.product ℝ).constSmooth (p.1 + c)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1 u) := by
    intro u
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (p.1 + c)).injective
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply,
      AlmostComplexStructure.fromTangentSpace_constSmooth_apply]
  exact and_iff_right hhorizontal

end TauCeti.SmoothAlmostComplexStructure
