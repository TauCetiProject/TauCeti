/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Graph
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# The intrinsic normal bundle of the diagonal

The normal space of the diagonal is the ambient tangent space modulo the image of its actual
manifold differential. Its canonical comparison with the tangent space sends the class of
`(v, w)` to `w - v`, with inverse sending `u` to the class of `(0, u)`. These formulas use the
native identification of product tangent spaces and the existing quotient normal bundle.

No metric or positive-dimensionality assumption is needed.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §11 (the normal bundle of the diagonal).
-/

public noncomputable section

open Bundle Function Manifold TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The smooth diagonal embedding. The first projection is a smooth left inverse. -/
abbrev diagonal : SmoothEmbedding I (I.prod I) ∞ M (M × M) where
  toContMDiffMap := ⟨fun x ↦ (x, x), contMDiff_id.prodMk contMDiff_id⟩
  isSmoothEmbedding_toFun := _root_.ContMDiff.isSmoothEmbedding_graph
    (I := I) (J := I) (n := ∞) (f := _root_.id) contMDiff_id

/-- The diagonal embedding sends `x` to `(x, x)`. -/
@[simp]
theorem diagonal_apply (x : M) : diagonal (I := I) x = (x, x) := by
  rfl

/-- The function underlying the diagonal embedding is the diagonal map. -/
@[simp]
theorem coe_diagonal : (diagonal (I := I) : M → M × M) = fun x ↦ (x, x) :=
  funext diagonal_apply

/-- Under the native product tangent identification, the differential of the diagonal is diagonal.
-/
@[simp]
theorem mfderiv_diagonal (x : M) (v : TangentSpace I x) :
    mfderiv I (I.prod I) (diagonal (I := I) : M → M × M) x v =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (v, v) := by
  rw [tangentSpaceProdEquiv_symm_apply]
  rw [coe_diagonal]
  -- The target tangent space is a type synonym for the product model.
  erw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_id]
  simp only [mfderiv_id]
  rfl

/-- The tangent range of the actual diagonal differential consists of pairs of equal tangent
vectors, under the native product tangent identification. -/
theorem mem_diagonal_tangentRange_iff (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    v ∈ (diagonal (I := I) (M := M)).tangentRange x (by simp) ↔
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 =
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 := by
  constructor
  · rintro ⟨u, rfl⟩
    -- The tangent range records the underlying linear map of the differential.
    erw [mfderiv_diagonal, ContinuousLinearEquiv.apply_symm_apply]
  · intro h
    refine ⟨(tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1, ?_⟩
    -- Expose the same differential coercion before comparing native tangent components.
    erw [mfderiv_diagonal]
    apply (tangentSpaceProdEquiv (I := I) (J := I) (x, x)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl h

/-- The difference map on ambient tangent representatives vanishes on the diagonal tangent range.
-/
private theorem sub_eq_zero_of_mem_diagonal_tangentRange (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x))
    (hv : v ∈ (diagonal (I := I) (M := M)).tangentRange x (by simp)) :
    (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 = 0 := by
  obtain ⟨u, rfl⟩ := hv
  -- Membership gives a linear-map application of the differential; expose its CLM coercion.
  erw [mfderiv_diagonal, ContinuousLinearEquiv.apply_symm_apply, sub_self]

/-- The intrinsic normal-to-tangent map of the diagonal, descended from `w - v`. -/
private def diagonalNormalToTangentL (x : M) :
    (diagonal (I := I) (M := M)).NormalSpace x (by simp) →L[ℝ] TangentSpace I x :=
  (diagonal (I := I)).normalLiftL x (by simp)
    (((ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace I x)) -
      ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace I x)).comp
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) :
          TangentSpace (I.prod I) (x, x) →L[ℝ] TangentSpace I x × TangentSpace I x))
    (sub_eq_zero_of_mem_diagonal_tangentRange x)

/-- The normal-to-tangent map evaluates to the difference on the normal class of a representative.
-/
@[simp]
private theorem diagonalNormalToTangentL_normalClass (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    diagonalNormalToTangentL (I := I) x
      ((diagonal (I := I)).normalClass x (by simp) v) =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  exact (diagonal (I := I)).normalLiftL_normalClass x (by simp) _ _ v

/-- The inverse comparison sends `u` to the actual quotient class of `(0, u)`. -/
private def tangentToDiagonalNormalL (x : M) :
    TangentSpace I x →L[ℝ] (diagonal (I := I) (M := M)).NormalSpace x (by simp) :=
  ((diagonal (I := I)).normalClassL x (by simp)).comp
    (((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm :
      TangentSpace I x × TangentSpace I x →L[ℝ] TangentSpace (I.prod I) (x, x)).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace I x) (TangentSpace I x)))

/-- The inverse comparison is the normal class of the second-factor inclusion. -/
@[simp]
private theorem tangentToDiagonalNormalL_apply (x : M) (u : TangentSpace I x) :
    tangentToDiagonalNormalL (I := I) x u = (diagonal (I := I)).normalClass x (by simp)
      ((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (0, u)) := by
  simp only [tangentToDiagonalNormalL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe, normalClassL_apply]

/-- The intrinsic normal space of the smooth diagonal is canonically the tangent space. -/
def diagonalNormalEquiv (x : M) :
    (diagonal (I := I) (M := M)).NormalSpace x (by simp) ≃L[ℝ] TangentSpace I x :=
  ContinuousLinearEquiv.equivOfInverse (diagonalNormalToTangentL (I := I) x)
    (tangentToDiagonalNormalL (I := I) x)
    (by
      intro q
      obtain ⟨v, rfl⟩ := (diagonal (I := I)).normalClass_surjective x (by simp) q
      rw [diagonalNormalToTangentL_normalClass]
      erw [tangentToDiagonalNormalL_apply (I := I)]
      apply ((diagonal (I := I)).normalClass_eq_iff x (by simp) _ _).2
      refine ⟨-(tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1, ?_⟩
      -- The tangent range uses the underlying linear map of the differential.
      erw [mfderiv_diagonal]
      apply (tangentSpaceProdEquiv (I := I) (J := I) (x, x)).injective
      simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, Prod.sub_def]
      ext <;> simp)
    (by
      intro u
      erw [tangentToDiagonalNormalL_apply]
      rw [diagonalNormalToTangentL_normalClass, ContinuousLinearEquiv.apply_symm_apply,
        sub_zero])

/-- On the class of an ambient vector, the canonical equivalence is the difference of its two
native product tangent components. -/
@[simp]
theorem diagonalNormalEquiv_normalClass (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    diagonalNormalEquiv (I := I) x ((diagonal (I := I)).normalClass x (by simp) v) =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  exact diagonalNormalToTangentL_normalClass x v

/-- In any existing tangent trivialization, the comparison is the difference of the two
representative tangent coordinates. -/
theorem diagonalNormalEquiv_normalClass_tangentCoordinates (x₀ x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
      (diagonalNormalEquiv (I := I) x ((diagonal (I := I)).normalClass x (by simp) v)) =
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
          (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
          (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  rw [diagonalNormalEquiv_normalClass, map_sub]

/-- The inverse of the canonical equivalence is the quotient class of `(0, u)`. -/
@[simp]
theorem diagonalNormalEquiv_symm_apply (x : M) (u : TangentSpace I x) :
    (diagonalNormalEquiv (I := I) x).symm u =
      (diagonal (I := I)).normalClass x (by simp)
        ((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (0, u)) := by
  exact tangentToDiagonalNormalL_apply x u

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The quotient-to-tangent comparison is smooth for the existing intrinsic normal atlas. -/
theorem contMDiff_diagonalNormalEquiv :
    let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace E ((diagonal (I := I) (M := M)).NormalSpace · (by simp)) ↦
        TotalSpace.mk' E p.proj (diagonalNormalEquiv (I := I) p.proj p.2)) := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold (I.prod I) ((∞ : ℕ∞ω) + 1) (M × M) := by
    simpa using (inferInstance : IsManifold (I.prod I) ∞ (M × M))
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  rw [(diagonal (I := I) (M := M)).contMDiff_normalBundle_iff (P := E) (by simp)
    (by simp) (by simp [Module.finrank_prod])]
  have hlift := Bundle.Pullback.contMDiff_lift (F := E × E) (E := TangentSpace (I.prod I))
    (diagonal (I := I) (M := M))
    (diagonal (I := I) (M := M)).contMDiff
  have hsnd : ContMDiff (I.prod 𝓘(ℝ, E × E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace (E × E)
          ((diagonal (I := I) (M := M) : M → M × M) *ᵖ (TangentSpace (I.prod I))) ↦
        TotalSpace.mk' E p.proj
          (tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.2).2) := by
    apply ((contMDiff_snd.contMDiff_tangentMap
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp hlift).congr
    rintro ⟨x, v⟩
    simp only [Function.comp_apply, tangentMap_prodSnd]
    -- The product tangent equivalence identifies the native product tangent type synonym.
    erw [tangentSpaceProdEquiv_apply]
    rfl
  have hfst : ContMDiff (I.prod 𝓘(ℝ, E × E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace (E × E)
          ((diagonal (I := I) (M := M) : M → M × M) *ᵖ (TangentSpace (I.prod I))) ↦
        TotalSpace.mk' E p.proj
          (tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.2).1) := by
    apply ((contMDiff_fst.contMDiff_tangentMap
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp hlift).congr
    rintro ⟨x, v⟩
    simp only [Function.comp_apply, tangentMap_prodFst]
    -- The product tangent equivalence identifies the native product tangent type synonym.
    erw [tangentSpaceProdEquiv_apply]
    rfl
  apply (hsnd.sub_sectionAlong hfst).congr
  intro p
  simp only [Function.comp_apply]
  rw [(diagonal (I := I) (M := M)).normalQuotientMap_apply (K := E) (by simp) p]
  exact congrArg (fun v : TangentSpace I p.proj ↦ TotalSpace.mk' E p.proj v)
    (diagonalNormalEquiv_normalClass (I := I) p.proj p.2)

/-- The actual intrinsic normal bundle of the diagonal is smoothly and fibrewise linearly
isomorphic to the tangent bundle, including for a zero-dimensional model. -/
def diagonalNormalBundleDiffeomorph :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    TotalSpace E ((diagonal (I := I) (M := M)).NormalSpace · (by simp))
      ≃ₘ^∞⟮I.prod 𝓘(ℝ, E), I.prod 𝓘(ℝ, E)⟯ TangentBundle I M := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold (I.prod I) ((∞ : ℕ∞ω) + 1) (M × M) := by
    simpa using (inferInstance : IsManifold (I.prod I) ∞ (M × M))
  letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  letI := (diagonal (I := I) (M := M)).normalSpaceContMDiffVectorBundle (P := E) (m := ∞) (by simp)
    (by simp) (by simp [Module.finrank_prod])
  exact TauCeti.bundleDiffeomorph (diagonalNormalEquiv (I := I) (M := M))
    contMDiff_diagonalNormalEquiv

/-- On total spaces, the normal-bundle diffeomorphism acts by the canonical quotient comparison
and fixes the base point. -/
@[simp]
theorem diagonalNormalBundleDiffeomorph_apply
    (p : TotalSpace E ((diagonal (I := I) (M := M)).NormalSpace · (by simp))) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    diagonalNormalBundleDiffeomorph (I := I) p =
      TotalSpace.mk' E p.proj (diagonalNormalEquiv (I := I) p.proj p.2) := by
  simp only [diagonalNormalBundleDiffeomorph, TauCeti.bundleDiffeomorph_apply]

/-- The smooth inverse fixes the base point and takes the class of the second tangent factor.
-/
@[simp]
theorem diagonalNormalBundleDiffeomorph_symm_apply (p : TangentBundle I M) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    (diagonalNormalBundleDiffeomorph (I := I) (M := M)).symm p =
      TotalSpace.mk' E p.proj ((diagonal (I := I)).normalClass p.proj (by simp)
        ((tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj)).symm (0, p.2))) := by
  simp only [diagonalNormalBundleDiffeomorph, TauCeti.bundleDiffeomorph_symm_apply,
    diagonalNormalEquiv_symm_apply]

/-- The smooth comparison commutes with the original quotient map from the actual pullback of
the ambient tangent bundle; on representatives it is the tangent difference. -/
theorem diagonalNormalBundleDiffeomorph_normalQuotientMap
    (p : TotalSpace (E × E)
      ((diagonal (I := I) (M := M) : M → M × M) *ᵖ (TangentSpace (I.prod I)))) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    diagonalNormalBundleDiffeomorph (I := I)
        ((diagonal (I := I)).normalQuotientMap (K := E) (by simp) p) =
      TotalSpace.mk' E p.proj
        ((tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.2).2 -
          (tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.2).1) := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  rw [(diagonal (I := I) (M := M)).normalQuotientMap_apply (K := E) (by simp) p,
    diagonalNormalBundleDiffeomorph_apply]
  exact congrArg (fun v : TangentSpace I p.proj ↦ TotalSpace.mk' E p.proj v)
    (diagonalNormalEquiv_normalClass (I := I) p.proj p.2)

end FiniteDimensional

end TauCeti.SmoothEmbedding
