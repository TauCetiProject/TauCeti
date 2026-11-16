/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Submersion.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Recognizing diffeomorphisms through submersions

A bijection commuting with two surjective `C^n` submersions out of a common boundaryless manifold is
a `C^n` diffeomorphism (`Equiv.diffeomorphOfSubmersions`). Unlike the dual immersion statement
(`Homeomorph.diffeomorphOfImmersions`), continuity of the bijection need not be assumed: smoothness
descends directly along a surjective submersion (`Manifold.IsSubmersion.contMDiff_comp_iff`).

In particular, two charted-space structures on the same topological space for which a given
surjective map from a boundaryless manifold is a `C^n` submersion are `C^n` diffeomorphic by the
identity (`ChartedSpace.diffeomorphOfSubmersions`), determine the same vertical tangent space
`ker (mfderiv p x)` for `n ≠ 0` (`ChartedSpace.ker_mfderiv_eq_of_isSubmersion`), and have the same
maximal atlas when both use the same model with corners and define `C^n` manifolds
(`ChartedSpace.maximalAtlas_eq_of_isSubmersion`).

## Main declarations

* `Equiv.diffeomorphOfSubmersions`: an equivalence commuting with two surjective `C^n` submersions
  out of a common boundaryless manifold is a `C^n` diffeomorphism.
* `ChartedSpace.diffeomorphOfSubmersions`: the identity is a `C^n` diffeomorphism between two
  charted-space structures on `N` making a surjective map `p : M → N` a `C^n` submersion.
* `ChartedSpace.ker_mfderiv_eq_of_isSubmersion`: two charted-space structures on `N` making a
  surjective map `p : M → N` a `C^n` submersion (`n ≠ 0`) yield the same kernel of `mfderiv p x`.
* `ChartedSpace.maximalAtlas_eq_of_isSubmersion`: two `C^n` manifold structures on `N` with the same
  model making a surjective map `p : M → N` a `C^n` submersion have the same maximal atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.29
  (characteristic property of surjective submersions) and Corollary 4.32 (uniqueness of smooth
  quotient structures).
-/

public section

open Function
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {K : ModelWithCorners 𝕜 V W}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [cP : ChartedSpace W P]
  {n : ℕ∞ω} {p : M → N} {q : M → P}

namespace Equiv

/-- A bijection commuting with two surjective `C^n` submersions out of a common boundaryless
manifold is a `C^n` diffeomorphism. Continuity of the bijection is not assumed; neither
finite-dimensionality nor separation is needed. -/
def diffeomorphOfSubmersions [I.Boundaryless] (e : N ≃ P)
    (hp : Manifold.IsSubmersion I J n p) (hps : Surjective p)
    (hq : Manifold.IsSubmersion I K n q) (hqs : Surjective q)
    (h : e ∘ p = q) : N ≃ₘ^n⟮J, K⟯ P where
  toEquiv := e
  contMDiff_toFun := (hp.contMDiff_comp_iff hps le_rfl).1 (h.symm ▸ hq.contMDiff)
  contMDiff_invFun := by
    refine (hq.contMDiff_comp_iff hqs le_rfl).1 ?_
    have h' : e.symm ∘ q = p := by
      ext x
      simpa only [comp_apply, e.symm_apply_apply] using congrArg e.symm (congrFun h x).symm
    exact h'.symm ▸ hp.contMDiff

/-- Recognizing smoothness through submersions preserves the underlying equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv [I.Boundaryless] (e : N ≃ P)
    (hp : Manifold.IsSubmersion I J n p) (hps : Surjective p)
    (hq : Manifold.IsSubmersion I K n q) (hqs : Surjective q) (h : e ∘ p = q) :
    (e.diffeomorphOfSubmersions hp hps hq hqs h).toEquiv = e :=
  (rfl)

/-- The diffeomorphism acts by the original equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_apply [I.Boundaryless] (e : N ≃ P)
    (hp : Manifold.IsSubmersion I J n p) (hps : Surjective p)
    (hq : Manifold.IsSubmersion I K n q) (hqs : Surjective q) (h : e ∘ p = q) (x : N) :
    e.diffeomorphOfSubmersions hp hps hq hqs h x = e x :=
  (rfl)

/-- The inverse diffeomorphism acts by the inverse equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply [I.Boundaryless] (e : N ≃ P)
    (hp : Manifold.IsSubmersion I J n p) (hps : Surjective p)
    (hq : Manifold.IsSubmersion I K n q) (hqs : Surjective q) (h : e ∘ p = q) (y : P) :
    (e.diffeomorphOfSubmersions hp hps hq hqs h).symm y = e.symm y :=
  (rfl)

end Equiv

namespace ChartedSpace

omit cN in
/-- Two charted-space structures on the same topological space are `C^n` diffeomorphic by the
identity whenever the same surjective map out of a boundaryless manifold is a `C^n` submersion for
both atlases. The two atlases are passed explicitly so both live on the same carrier. -/
def diffeomorphOfSubmersions [I.Boundaryless] (a : ChartedSpace G N) (b : ChartedSpace W N)
    (hps : Surjective p)
    (ha : letI := a; Manifold.IsSubmersion I J n p)
    (hb : letI := b; Manifold.IsSubmersion I K n p) :
    @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ J K N _ a N _ b n :=
  Equiv.diffeomorphOfSubmersions (cN := a) (cP := b) (Equiv.refl N) ha hps hb hps rfl

omit cN in
/-- The identity diffeomorphism between two submersion atlases fixes every point. -/
@[simp]
theorem diffeomorphOfSubmersions_apply [I.Boundaryless] (a : ChartedSpace G N)
    (b : ChartedSpace W N) (hps : Surjective p)
    (ha : letI := a; Manifold.IsSubmersion I J n p)
    (hb : letI := b; Manifold.IsSubmersion I K n p) (x : N) :
    diffeomorphOfSubmersions a b hps ha hb x = x :=
  (rfl)

omit cN in
/-- The inverse of the identity diffeomorphism between two submersion atlases fixes every point. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply [I.Boundaryless] (a : ChartedSpace G N)
    (b : ChartedSpace W N) (hps : Surjective p)
    (ha : letI := a; Manifold.IsSubmersion I J n p)
    (hb : letI := b; Manifold.IsSubmersion I K n p) (x : N) :
    (@Diffeomorph.symm 𝕜 _ _ _ _ _ _ _ _ _ _ _ J K N _ a N _ b n
      (diffeomorphOfSubmersions a b hps ha hb)) x = x :=
  (rfl)

private theorem mem_maximalAtlas_of_diffeomorph
    {N₁ N₂ : Type*} [TopologicalSpace N₁] [c₁ : ChartedSpace G N₁] [hm₁ : IsManifold J n N₁]
    [TopologicalSpace N₂] [c₂ : ChartedSpace G N₂] [hm₂ : IsManifold J n N₂]
    (e : N₁ ≃ₘ^n⟮J, J⟯ N₂) (φ : OpenPartialHomeomorph N₁ G) (ψ : OpenPartialHomeomorph N₂ G)
    (hsrc : ψ.source = e.symm ⁻¹' φ.source) (htgt : ψ.target = φ.target)
    (hto : ∀ x ∈ ψ.source, ψ x = φ (e.symm x)) (hinv : ∀ y ∈ ψ.target, ψ.symm y = e (φ.symm y))
    (hφ : φ ∈ IsManifold.maximalAtlas J n N₁) :
    ψ ∈ IsManifold.maximalAtlas J n N₂ := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn] at hφ ⊢
  exact ⟨(hφ.1.comp e.symm.contMDiff.contMDiffOn fun _ hx ↦ hsrc ▸ hx).congr hto,
    (e.contMDiff.comp_contMDiffOn (htgt.symm ▸ hφ.2)).congr hinv⟩

omit cN in
/-- **Uniqueness of smooth quotient structures.** Two `C^n` manifold structures on `N` with the same
model making a surjective map `p : M → N` from a boundaryless manifold a `C^n` submersion have the
same maximal atlas. -/
theorem maximalAtlas_eq_of_isSubmersion [I.Boundaryless] (a b : ChartedSpace G N)
    (hps : Surjective p)
    (hma : letI := a; IsManifold J n N) (hmb : letI := b; IsManifold J n N)
    (ha : letI := a; Manifold.IsSubmersion I J n p)
    (hb : letI := b; Manifold.IsSubmersion I J n p) :
    (letI := a; IsManifold.maximalAtlas J n N) = (letI := b; IsManifold.maximalAtlas J n N) := by
  ext φ
  exact ⟨mem_maximalAtlas_of_diffeomorph (c₁ := a) (hm₁ := hma) (c₂ := b) (hm₂ := hmb)
      (diffeomorphOfSubmersions a b hps ha hb) φ φ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl),
    mem_maximalAtlas_of_diffeomorph (c₁ := b) (hm₁ := hmb) (c₂ := a) (hm₂ := hma)
      (diffeomorphOfSubmersions b a hps hb ha) φ φ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)⟩

private theorem ker_mfderiv_of_diffeomorph
    {N₁ N₂ : Type*} [TopologicalSpace N₁] [c₁ : ChartedSpace G N₁]
    [TopologicalSpace N₂] [c₂ : ChartedSpace W N₂]
    (e : N₁ ≃ₘ^n⟮J, K⟯ N₂) (hn : n ≠ 0) (p₁ : M → N₁) (p₂ : M → N₂)
    (h : e ∘ p₁ = p₂) (x : M) :
    (mfderiv I J p₁ x).ker = (mfderiv I K p₂ x).ker := by
  rw [← h, e.mfderiv_diffeomorph_comp hn, ContinuousLinearMap.toLinearMap_comp]
  exact (LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective
    (e.isInvertible_mfderiv hn).injective)).symm

omit cN in
/-- Two charted-space structures on `N` making a surjective map `p : M → N` from a boundaryless
manifold a `C^n` submersion (`n ≠ 0`) determine the same vertical tangent space `ker (mfderiv p x)`
at every point `x : M`. -/
theorem ker_mfderiv_eq_of_isSubmersion [I.Boundaryless] (a : ChartedSpace G N)
    (b : ChartedSpace W N) (hps : Surjective p) (hn : n ≠ 0)
    (ha : letI := a; Manifold.IsSubmersion I J n p)
    (hb : letI := b; Manifold.IsSubmersion I K n p) (x : M) :
    (letI := a; mfderiv I J p x).ker = (letI := b; mfderiv I K p x).ker :=
  ker_mfderiv_of_diffeomorph (c₁ := a) (c₂ := b) (diffeomorphOfSubmersions a b hps ha hb) hn p p
    rfl x

end ChartedSpace
