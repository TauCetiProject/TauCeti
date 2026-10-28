/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# The cotangent bundle of a product

The cotangent bundle of a product manifold is the product of the cotangent bundles:

`T*(M × N) ≃ T*M × T*N`

(`TauCeti.CotangentBundle.prodDiffeomorph`). A covector `p` at `(x, y)` goes to its restrictions
to the two factors, the covectors `p ∘ dι₁` at `x` and `p ∘ dι₂` at `y`, where `ι₁ = (·, y)` and
`ι₂ = (x, ·)` are the inclusions of the slices through `(x, y)`. Conversely, covectors `a` at `x`
and `b` at `y` go to `a ∘ d pr₁ + b ∘ d pr₂` at `(x, y)`. Both directions are stated through
differentials of the product maps, so they do not depend on how the tangent spaces of a product
are implemented.

The identification is a smooth diffeomorphism. Smoothness of the restriction map is the smoothness
of pulling covectors back along a family of maps,
`TauCeti.CotangentBundle.contMDiffAt_mk_comp_mfderiv_uncurry`, since the slice inclusion `ι₁`
depends on the point `y` of the second factor. The comparison of the Liouville and canonical
symplectic forms of `T*(M × N)` with those of the factors is in
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.Prod`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Restrict a covector on `M × N` at `(x, y)` to the two factors: the covectors `p ∘ dι₁` at `x`
and `p ∘ dι₂` at `y`, for the slice inclusions `ι₁ = (·, y)` and `ι₂ = (x, ·)`. -/
private def toProd (z : CotangentBundle (I.prod J) (M × N)) :
    CotangentBundle I M × CotangentBundle J N :=
  (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj.1
      (z.2 ∘L mfderiv I (I.prod J) (fun x : M ↦ (x, z.proj.2)) z.proj.1),
    TotalSpace.mk' (F →L[𝕜] 𝕜) z.proj.2
      (z.2 ∘L mfderiv J (I.prod J) (fun y : N ↦ (z.proj.1, y)) z.proj.2))

/-- Combine covectors `a` at `x` and `b` at `y` into the covector `a ∘ d pr₁ + b ∘ d pr₂` on
`M × N` at `(x, y)`. -/
private def ofProd (w : CotangentBundle I M × CotangentBundle J N) :
    CotangentBundle (I.prod J) (M × N) :=
  TotalSpace.mk' (E × F →L[𝕜] 𝕜) (w.1.proj, w.2.proj)
    (w.1.2 ∘L mfderiv (I.prod J) I Prod.fst (w.1.proj, w.2.proj) +
      w.2.2 ∘L mfderiv (I.prod J) J Prod.snd (w.1.proj, w.2.proj))

/-- A covector on `M × N` evaluates a tangent vector as the sum of its two restrictions evaluated
on the components of the vector. -/
private theorem snd_apply_eq_toProd_add (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace (I.prod J) z.proj) :
    z.2 v = (toProd z).1.2 (mfderiv (I.prod J) I Prod.fst z.proj v) +
      (toProd z).2.2 (mfderiv (I.prod J) J Prod.snd z.proj v) := by
  refine (congrArg z.2 ?_).trans (map_add z.2 _ _)
  -- A tangent vector of the product is the sum of its two slice components.
  rw [mfderiv_fst, mfderiv_snd, mfderiv_prod_left, mfderiv_prod_right]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

private theorem ofProd_toProd (z : CotangentBundle (I.prod J) (M × N)) :
    ofProd (toProd z) = z :=
  ext rfl fun v ↦ (snd_apply_eq_toProd_add z v).symm

private theorem toProd_ofProd (w : CotangentBundle I M × CotangentBundle J N) :
    toProd (ofProd w) = w := by
  -- The slice inclusions are right inverse to the projections, and the other projection kills
  -- each slice. After rewriting the derivatives, this is the evaluation of `inl`, `inr`, `fst`
  -- and `snd` on the product `E × F` of model spaces.
  refine Prod.ext (ext rfl fun v ↦ ?_) (ext rfl fun v ↦ ?_)
  · have h₁ : mfderiv (I.prod J) I Prod.fst (w.1.proj, w.2.proj)
        (mfderiv I (I.prod J) (fun x : M ↦ (x, w.2.proj)) w.1.proj v) = v := by
      rw [mfderiv_fst, mfderiv_prod_left]
      rfl
    have h₂ : mfderiv (I.prod J) J Prod.snd (w.1.proj, w.2.proj)
        (mfderiv I (I.prod J) (fun x : M ↦ (x, w.2.proj)) w.1.proj v) = 0 := by
      rw [mfderiv_snd, mfderiv_prod_left]
      rfl
    exact (congrArg₂ (fun a b ↦ w.1.2 a + w.2.2 b) h₁ h₂).trans (by rw [map_zero, add_zero])
  · have h₁ : mfderiv (I.prod J) I Prod.fst (w.1.proj, w.2.proj)
        (mfderiv J (I.prod J) (fun y : N ↦ (w.1.proj, y)) w.2.proj v) = 0 := by
      rw [mfderiv_fst, mfderiv_prod_right]
      rfl
    have h₂ : mfderiv (I.prod J) J Prod.snd (w.1.proj, w.2.proj)
        (mfderiv J (I.prod J) (fun y : N ↦ (w.1.proj, y)) w.2.proj v) = v := by
      rw [mfderiv_snd, mfderiv_prod_right]
      rfl
    exact (congrArg₂ (fun a b ↦ w.1.2 a + w.2.2 b) h₁ h₂).trans (by rw [map_zero, zero_add])

variable [IsManifold I 2 M] [IsManifold J 2 N]

private theorem contMDiff_toProd :
    ContMDiff ((I.prod J).prod 𝓘(𝕜, E × F →L[𝕜] 𝕜))
      ((I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)).prod (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜))) ∞
      (toProd (I := I) (J := J) (M := M) (N := N)) := by
  have hπ : ContMDiff ((I.prod J).prod 𝓘(𝕜, E × F →L[𝕜] 𝕜)) (I.prod J) ∞
      fun z : CotangentBundle (I.prod J) (M × N) ↦ z.proj :=
    contMDiff_proj _
  intro z
  -- The slice inclusions `(·, y)` and `(x, ·)` vary with the base point of the covector.
  refine ContMDiffAt.prodMk ?_ ?_
  · refine contMDiffAt_mk_comp_mfderiv_uncurry (Ψ := id) (n := ∞) (fun _ ↦ rfl) contMDiffAt_id
      (contMDiff_fst.comp hπ z) ?_ (by simp)
    exact (contMDiff_snd.prodMk (contMDiff_snd.comp (hπ.comp contMDiff_fst))).contMDiffAt
  · refine contMDiffAt_mk_comp_mfderiv_uncurry (Ψ := id) (n := ∞) (fun _ ↦ rfl) contMDiffAt_id
      (contMDiff_snd.comp hπ z) ?_ (by simp)
    exact ((contMDiff_fst.comp (hπ.comp contMDiff_fst)).prodMk contMDiff_snd).contMDiffAt

private theorem contMDiff_ofProd :
    ContMDiff ((I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)).prod (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)))
      ((I.prod J).prod 𝓘(𝕜, E × F →L[𝕜] 𝕜)) ∞
      (ofProd (I := I) (J := J) (M := M) (N := N)) := by
  have hπM : ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) I ∞ fun a : CotangentBundle I M ↦ a.proj :=
    contMDiff_proj _
  have hπN : ContMDiff (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) J ∞ fun b : CotangentBundle J N ↦ b.proj :=
    contMDiff_proj _
  have hbase : ContMDiff ((I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)).prod (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜))) (I.prod J) ∞
      fun w : CotangentBundle I M × CotangentBundle J N ↦ (w.1.proj, w.2.proj) :=
    (hπM.comp contMDiff_fst).prodMk (hπN.comp contMDiff_snd)
  -- Each summand pulls a covector on a factor back along the corresponding projection.
  exact ContMDiff.add_sectionAlong
    (contMDiff_mk_comp_mfderiv (Ψ := Prod.fst) (n := ∞) (fun _ ↦ rfl) contMDiff_fst hbase
      contMDiff_fst (by simp))
    (contMDiff_mk_comp_mfderiv (Ψ := Prod.snd) (n := ∞) (fun _ ↦ rfl) contMDiff_snd hbase
      contMDiff_snd (by simp))

variable (I J M N) in
/-- **The cotangent bundle of a product is the product of the cotangent bundles.** The smooth
diffeomorphism `T*(M × N) ≃ T*M × T*N` restricting a covector `p` at `(x, y)` to the covectors
`p ∘ dι₁` at `x` and `p ∘ dι₂` at `y`, for the slice inclusions `ι₁ = (·, y)` and `ι₂ = (x, ·)`.
Its inverse sends covectors `a` at `x` and `b` at `y` to `a ∘ d pr₁ + b ∘ d pr₂`. -/
def prodDiffeomorph :
    CotangentBundle (I.prod J) (M × N) ≃ₘ⟮(I.prod J).prod 𝓘(𝕜, E × F →L[𝕜] 𝕜),
      (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)).prod (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜))⟯
      CotangentBundle I M × CotangentBundle J N where
  toFun := toProd
  invFun := ofProd
  left_inv := ofProd_toProd
  right_inv := toProd_ofProd
  contMDiff_toFun := contMDiff_toProd
  contMDiff_invFun := contMDiff_ofProd

/-- The first component of `prodDiffeomorph z` lies over the first component of the base point
of `z`. -/
@[simp]
theorem proj_prodDiffeomorph_fst (z : CotangentBundle (I.prod J) (M × N)) :
    (prodDiffeomorph I J M N z).1.proj = z.proj.1 :=
  (rfl)

/-- The second component of `prodDiffeomorph z` lies over the second component of the base point
of `z`. -/
@[simp]
theorem proj_prodDiffeomorph_snd (z : CotangentBundle (I.prod J) (M × N)) :
    (prodDiffeomorph I J M N z).2.proj = z.proj.2 :=
  (rfl)

/-- The first component of `prodDiffeomorph z` evaluates a tangent vector `v` of `M` as `z`
evaluates its image under the differential of the slice inclusion `x ↦ (x, y)`. -/
theorem prodDiffeomorph_fst_snd_apply (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace I (prodDiffeomorph I J M N z).1.proj) :
    (prodDiffeomorph I J M N z).1.2 v =
      z.2 (mfderiv I (I.prod J) (fun x : M ↦ (x, z.proj.2)) z.proj.1 v) :=
  (rfl)

/-- The second component of `prodDiffeomorph z` evaluates a tangent vector `v` of `N` as `z`
evaluates its image under the differential of the slice inclusion `y ↦ (x, y)`. -/
theorem prodDiffeomorph_snd_snd_apply (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace J (prodDiffeomorph I J M N z).2.proj) :
    (prodDiffeomorph I J M N z).2.2 v =
      z.2 (mfderiv J (I.prod J) (fun y : N ↦ (z.proj.1, y)) z.proj.2 v) :=
  (rfl)

/-- The inverse of `prodDiffeomorph` lies over the pair of base points. -/
@[simp]
theorem proj_prodDiffeomorph_symm (w : CotangentBundle I M × CotangentBundle J N) :
    ((prodDiffeomorph I J M N).symm w).proj = (w.1.proj, w.2.proj) :=
  (rfl)

/-- The inverse of `prodDiffeomorph` combines covectors `a` at `x` and `b` at `y` into the
covector `a ∘ d pr₁ + b ∘ d pr₂` at `(x, y)`. -/
theorem prodDiffeomorph_symm_snd_apply (w : CotangentBundle I M × CotangentBundle J N)
    (v : TangentSpace (I.prod J) ((prodDiffeomorph I J M N).symm w).proj) :
    ((prodDiffeomorph I J M N).symm w).2 v =
      w.1.2 (mfderiv (I.prod J) I Prod.fst (w.1.proj, w.2.proj) v) +
        w.2.2 (mfderiv (I.prod J) J Prod.snd (w.1.proj, w.2.proj) v) :=
  (rfl)

/-- **`prodDiffeomorph` preserves the pairing of covectors with tangent vectors:** a covector `z`
on `M × N` evaluates a tangent vector `v` as the sum of its two restrictions evaluated on the
components `d pr₁ v` and `d pr₂ v`. -/
theorem snd_apply_eq_prodDiffeomorph_add (z : CotangentBundle (I.prod J) (M × N))
    (v : TangentSpace (I.prod J) z.proj) :
    z.2 v = (prodDiffeomorph I J M N z).1.2 (mfderiv (I.prod J) I Prod.fst z.proj v) +
      (prodDiffeomorph I J M N z).2.2 (mfderiv (I.prod J) J Prod.snd z.proj v) :=
  snd_apply_eq_toProd_add z v

end TauCeti.CotangentBundle
