/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diagonal
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The tangent range of the actual diagonal differential consists of pairs of equal tangent
vectors, under the native product tangent identification. -/
theorem mem_diagonal_tangentRange_iff (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    v ∈ (diagonal (I := I) (M := M)).isImmersion.tangentRange x (by simp) ↔
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 =
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 := by
  rw [Manifold.IsImmersion.mem_tangentRange_iff]
  constructor
  · rintro ⟨u, rfl⟩
    rw [mfderiv_diagonal, ContinuousLinearEquiv.apply_symm_apply]
  · intro h
    refine ⟨(tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1, ?_⟩
    rw [mfderiv_diagonal]
    apply (tangentSpaceProdEquiv (I := I) (J := I) (x, x)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl h

/-- The difference map on ambient tangent representatives vanishes on the diagonal tangent range.
-/
private theorem sub_eq_zero_of_mem_diagonal_tangentRange (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x))
    (hv : v ∈ (diagonal (I := I) (M := M)).isImmersion.tangentRange x (by simp)) :
    (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 = 0 :=
  sub_eq_zero.2 ((mem_diagonal_tangentRange_iff x v).1 hv).symm

/-- The intrinsic normal-to-tangent map of the diagonal, descended from `w - v`. -/
private def diagonalNormalToTangentL (x : M) :
    (diagonal (I := I) (M := M)).isImmersion.NormalSpace x (by simp) →L[𝕜] TangentSpace I x :=
  (diagonal (I := I)).isImmersion.normalLiftL x (by simp)
    (((ContinuousLinearMap.snd 𝕜 (TangentSpace I x) (TangentSpace I x)) -
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x) (TangentSpace I x)).comp
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) :
          TangentSpace (I.prod I) (x, x) →L[𝕜] TangentSpace I x × TangentSpace I x))
    (sub_eq_zero_of_mem_diagonal_tangentRange x)

/-- The normal-to-tangent map evaluates to the difference on the normal class of a representative.
-/
@[simp]
private theorem diagonalNormalToTangentL_normalClass (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    diagonalNormalToTangentL (I := I) x
      ((diagonal (I := I)).isImmersion.normalClass x (by simp) v) =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  exact (diagonal (I := I)).isImmersion.normalLiftL_normalClass x (by simp) _ _ v

/-- The inverse comparison sends `u` to the actual quotient class of `(0, u)`. -/
private def tangentToDiagonalNormalL (x : M) :
    TangentSpace I x →L[𝕜] (diagonal (I := I) (M := M)).isImmersion.NormalSpace x (by simp) :=
  ((diagonal (I := I)).isImmersion.normalClassL x (by simp)).comp
    (((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm :
      TangentSpace I x × TangentSpace I x →L[𝕜] TangentSpace (I.prod I) (x, x)).comp
        (ContinuousLinearMap.inr 𝕜 (TangentSpace I x) (TangentSpace I x)))

/-- The inverse comparison is the normal class of the second-factor inclusion. -/
@[simp]
private theorem tangentToDiagonalNormalL_apply (x : M) (u : TangentSpace I x) :
    tangentToDiagonalNormalL (I := I) x u = (diagonal (I := I)).isImmersion.normalClass x (by simp)
      ((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (0, u)) := by
  unfold tangentToDiagonalNormalL
  -- The first composition meets tangent instances at `diagonal x` and `(x,x)`; `erw` exposes
  -- these instances to apply the composition and quotient evaluation lemmas.
  erw
      [ContinuousLinearMap.comp_apply, Manifold.IsImmersion.normalClassL_apply,
          ContinuousLinearMap.comp_apply]

/-- The intrinsic normal space of the smooth diagonal is canonically the tangent space. -/
def diagonalNormalEquiv (x : M) :
    (diagonal (I := I) (M := M)).isImmersion.NormalSpace x (by simp) ≃L[𝕜] TangentSpace I x :=
  have hleft : Function.LeftInverse (tangentToDiagonalNormalL (I := I) x)
      (diagonalNormalToTangentL (I := I) x) := by
    intro q
    obtain ⟨v, rfl⟩ := (diagonal (I := I)).isImmersion.normalClass_surjective x (by simp) q
    rw [diagonalNormalToTangentL_normalClass]
    -- The representative tangent types are written at `diagonal x` and `(x,x)`; `erw`
    -- identifies their model instances to apply the inverse evaluation formula.
    erw [tangentToDiagonalNormalL_apply (I := I)]
    apply ((diagonal (I := I)).isImmersion.normalClass_eq_iff x (by simp) _ _).2
    -- The quotient criterion and product reading use tangent fibres at `diagonal x` and
    -- `(x,x)`, respectively. `erw` identifies their model instances in the named range formula.
    erw [mem_diagonal_tangentRange_iff, map_sub, ContinuousLinearEquiv.apply_symm_apply]
    simp only [Prod.sub_def]
    abel
  have hright : Function.RightInverse (tangentToDiagonalNormalL (I := I) x)
      (diagonalNormalToTangentL (I := I) x) := by
    intro u
    -- The inverse obligation has the same two presentations of the ambient tangent fibre.
    erw [tangentToDiagonalNormalL_apply]
    -- The normal class uses the tangent space at `diagonal x`, while the representative is
    -- written at `(x,x)`; `erw` identifies the model instances after `diagonal_apply`.
    erw [diagonalNormalToTangentL_normalClass, ContinuousLinearEquiv.apply_symm_apply,
      sub_zero]
  ContinuousLinearEquiv.ofContinuousLinearMap (diagonalNormalToTangentL (I := I) x)
    (tangentToDiagonalNormalL (I := I) x) (ContinuousLinearMap.ext hright)
    (ContinuousLinearMap.ext hleft)

/-- On the class of an ambient vector, the canonical equivalence is the difference of its two
native product tangent components. -/
@[simp]
theorem diagonalNormalEquiv_normalClass (x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    diagonalNormalEquiv (I := I) x ((diagonal (I := I)).isImmersion.normalClass x (by simp) v) =
      (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  exact diagonalNormalToTangentL_normalClass x v

/-- In any existing tangent trivialization, the comparison is the difference of the two
representative tangent coordinates. -/
theorem diagonalNormalEquiv_normalClass_tangentCoordinates (x₀ x : M)
    (v : TangentSpace (I.prod I) (diagonal (I := I) x)) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
      (diagonalNormalEquiv (I := I) x ((diagonal (I := I)).isImmersion.normalClass x (by simp) v)) =
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).2 -
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v).1 := by
  rw [diagonalNormalEquiv_normalClass, map_sub]

/-- The inverse of the canonical equivalence is the quotient class of `(0, u)`. -/
@[simp]
theorem diagonalNormalEquiv_symm_apply (x : M) (u : TangentSpace I x) :
    (diagonalNormalEquiv (I := I) x).symm u =
      (diagonal (I := I)).isImmersion.normalClass x (by simp)
        ((tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm (0, u)) := by
  exact tangentToDiagonalNormalL_apply x u

/-- The splitting of the ambient tangent space into tangent directions followed by intrinsic
normal directions, using the canonical difference comparison. -/
def diagonalTangentNormalEquiv (x : M) :
    (TangentSpace I x × (diagonal (I := I) (M := M)).isImmersion.NormalSpace x (by simp))
      ≃L[𝕜] TangentSpace (I.prod I) (x, x) := by
  exact ((ContinuousLinearEquiv.refl 𝕜 (TangentSpace I x)).prodCongr
    (diagonalNormalEquiv (I := I) x)).trans
      (((ContinuousLinearEquiv.refl 𝕜 (TangentSpace I x)).skewProd
        (ContinuousLinearEquiv.refl 𝕜 (TangentSpace I x))
        (ContinuousLinearMap.id 𝕜 (TangentSpace I x))).trans
          (TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm)

/-- In native product tangent coordinates, the splitting sends `(a, q)` to `(a, a + φ q)`.
-/
@[simp]
theorem diagonalTangentNormalEquiv_apply (x : M) (a : TangentSpace I x)
    (q : (diagonal (I := I) (M := M)).isImmersion.NormalSpace x (by simp)) :
    TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I) (x, x)
      (diagonalTangentNormalEquiv (I := I) x (a, q)) =
        (a, a + diagonalNormalEquiv (I := I) x q) := by
  simp only [diagonalTangentNormalEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.skewProd_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.apply_symm_apply, add_comm]

-- Tangent maps of smooth maps are smooth since `∞ + 1 = ∞` in `ℕ∞ω`.
local instance : IsManifold I ((∞ : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)

/-- A tangent projection gives a smooth component of the pulled-back ambient tangent bundle. -/
private theorem contMDiff_diagonal_tangentRead {project : M × M → M}
    (hproject : ContMDiff (I.prod I) I ∞ project)
    (read : ∀ x : M, TangentSpace I x × TangentSpace I x → TangentSpace I x)
    (hread : ∀ (x : M) (v : TangentSpace (I.prod I) (x, x)),
      tangentMap (I.prod I) I project ⟨(x, x), v⟩ =
        TotalSpace.mk' E x (read x (tangentSpaceProdEquiv (I := I) (J := I) (x, x) v))) :
    ContMDiff (I.prod 𝓘(𝕜, E × E)) (I.prod 𝓘(𝕜, E)) ∞
      (fun p : TotalSpace (E × E)
          ((diagonal (I := I) (M := M) : M → M × M) *ᵖ (TangentSpace (I.prod I))) ↦
        TotalSpace.mk' E p.proj
          (read p.proj (tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.snd))) := by
  apply ((hproject.contMDiff_tangentMap (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).comp
    (Bundle.Pullback.contMDiff_lift (F := E × E) (E := TangentSpace (I.prod I))
      (diagonal (I := I) (M := M)) (diagonal (I := I) (M := M)).contMDiff)).congr
  rintro ⟨x, v⟩
  simp only [Function.comp_apply, Pullback.lift]
  -- The pullback fibre is at `diagonal x`; the named evaluation formula identifies its
  -- ambient tangent model with the one at `(x,x)` at default transparency.
  erw [diagonal_apply (I := I) x]
  exact (hread x v).symm


section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The quotient-to-tangent comparison is smooth for the existing intrinsic normal atlas. -/
theorem contMDiff_diagonalNormalEquiv :
    let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) ∞
      (fun p : TotalSpace E ((diagonal (I := I) (M := M)).isImmersion.NormalSpace · (by simp)) ↦
        TotalSpace.mk' E p.proj (diagonalNormalEquiv (I := I) p.proj p.snd)) := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  rw [(diagonal (I := I) (M := M)).contMDiff_normalBundle_iff (P := E) (by simp)
    (by simp) (by simp [Module.finrank_prod])]
  have hsnd := contMDiff_diagonal_tangentRead (I := I) (M := M) contMDiff_snd
    (fun _ v ↦ v.2) fun x v ↦ by
      rw [tangentMap_prodSnd]
      -- Reading the native tangent-product synonym needs its component instances unfolded.
      erw [tangentSpaceProdEquiv_apply]
  have hfst := contMDiff_diagonal_tangentRead (I := I) (M := M) contMDiff_fst
    (fun _ v ↦ v.1) fun x v ↦ by
      rw [tangentMap_prodFst]
      -- The first projection uses the same native product reading.
      erw [tangentSpaceProdEquiv_apply]
  apply (hsnd.sub_sectionAlong hfst).congr
  intro p
  simp only [Function.comp_apply]
  rw [(diagonal (I := I) (M := M)).normalQuotientMap_apply (K := E) (by simp) p]
  exact congrArg (fun v : TangentSpace I p.proj ↦ TotalSpace.mk' E p.proj v)
    (diagonalNormalEquiv_normalClass (I := I) p.proj p.snd)

/-- The actual intrinsic normal bundle of the diagonal is smoothly and fibrewise linearly
isomorphic to the tangent bundle, including for a zero-dimensional model. -/
def diagonalNormalBundleDiffeomorph :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    TotalSpace E ((diagonal (I := I) (M := M)).isImmersion.NormalSpace · (by simp))
      ≃ₘ^∞⟮I.prod 𝓘(𝕜, E), I.prod 𝓘(𝕜, E)⟯ TangentBundle I M := by
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
    (p : TotalSpace E ((diagonal (I := I) (M := M)).isImmersion.NormalSpace · (by simp))) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    diagonalNormalBundleDiffeomorph (I := I) p =
      TotalSpace.mk' E p.proj (diagonalNormalEquiv (I := I) p.proj p.snd) := by
  simp only [diagonalNormalBundleDiffeomorph, TauCeti.bundleDiffeomorph_apply]

/-- The smooth inverse fixes the base point and takes the class of the second tangent factor.
-/
@[simp]
theorem diagonalNormalBundleDiffeomorph_symm_apply (p : TangentBundle I M) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    (diagonalNormalBundleDiffeomorph (I := I) (M := M)).symm p =
      TotalSpace.mk' E p.proj ((diagonal (I := I)).isImmersion.normalClass p.proj (by simp)
        ((tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj)).symm (0, p.snd))) := by
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
        ((tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.snd).2 -
          (tangentSpaceProdEquiv (I := I) (J := I) (p.proj, p.proj) p.snd).1) := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  rw [(diagonal (I := I) (M := M)).normalQuotientMap_apply (K := E) (by simp) p,
    diagonalNormalBundleDiffeomorph_apply]
  exact congrArg (fun v : TangentSpace I p.proj ↦ TotalSpace.mk' E p.proj v)
    (diagonalNormalEquiv_normalClass (I := I) p.proj p.snd)

end FiniteDimensional

end TauCeti.SmoothEmbedding
