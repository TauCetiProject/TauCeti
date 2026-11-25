/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The symplectic normal bundle as a smooth bundle of symplectic forms

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `N`, and let `f : M → N` be a
smooth embedding of a symplectic submanifold. At each point `x` the intrinsic normal space
`T_(f x) N / df_x (T_x M)` carries the normal symplectic form
`TauCeti.SmoothEmbedding.symplecticNormalForm`, under which two normal classes pair as their
symplectic representatives under `σ`. This file shows that these fibrewise forms make the
intrinsic normal bundle a smooth symplectic vector bundle, and that they are natural.

* **Smoothness.** The normal symplectic forms, read as continuous bilinear forms
  (`TauCeti.SmoothEmbedding.symplecticNormalFlat`), form a `C^m` section of the bundle of
  bilinear forms on the intrinsic normal bundle, for a `C^n` embedding with `m + 1 ≤ n`
  (`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalFlat`). The proof tests the section on
  two copies of a local normal frame: each evaluation is `σ` applied to the symplectic
  representatives of two frame sections, which are smooth ambient tangent fields along `f` by
  `TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative`. This is the symplectic
  counterpart of the induced Riemannian metric on the normal bundle
  (`TauCeti.SmoothEmbedding.normalContMDiffRiemannianMetric`).
* **Naturality.** Let `v : N → N'` carry `σ` to a nondegenerate form `τ` at `f x`, and let it
  restrict near `x` to a map `u` between symplectic submanifolds, `v ∘ f = g ∘ u`, whose
  differential at `x` is surjective. Then `dv` carries symplectic representatives to symplectic
  representatives
  (`TauCeti.SmoothEmbedding.symplecticNormalRepresentative_normalMap`), and the induced normal map
  `TauCeti.SmoothEmbedding.normalMap` is a linear symplectic map of the normal symplectic forms
  (`TauCeti.SmoothEmbedding.symplecticNormalForm_normalMap`). Without surjectivity of `du` this
  fails. The symplectic map `v(z) = (z / √2, z / √2)` from the plane `(ℝ², ω)` to `(ℝ⁴, ω ⊕ ω)`
  sends the origin, a zero-dimensional symplectic submanifold, to the origin of the symplectic
  plane `ℝ² × 0`. The normal map sends the class of `z` to the class of `(0, z / √2)`, so it
  halves the normal symplectic forms.

Together with the isotropy representation on the normal spaces of a fixed submanifold
(`TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`), these are the data on
which the local normal forms along fixed components of symplectic group actions are built: a
symplectic diffeomorphism restricting to a diffeomorphism between two fixed components induces
normal maps preserving their normal symplectic forms. No compactness of `M` and no closedness of
`σ` is used.

## Main definitions

* `TauCeti.SmoothEmbedding.symplecticNormalFlat`: the normal symplectic form at a point, as a
  continuous bilinear form on the normal space.

## Main results

* `TauCeti.SmoothEmbedding.symplecticNormalFlat_apply`: it evaluates as the normal symplectic
  form.
* `TauCeti.SmoothEmbedding.contMDiff_symplecticNormalFlat`: it is a `C^m` section of the bundle
  of bilinear forms on the intrinsic normal bundle.
* `TauCeti.SmoothEmbedding.symplecticNormalRepresentative_normalMap`: a symplectic map restricting
  to a map of symplectic submanifolds with surjective differential carries symplectic
  representatives to symplectic representatives.
* `TauCeti.SmoothEmbedding.symplecticNormalForm_normalMap`: its normal map preserves the normal
  symplectic forms.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 3.4 (the symplectic normal bundle).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Manifold Function Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothEmbedding

open SmoothTwoForm

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n : ℕ∞ω} {σ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}

/-! ### The normal symplectic form as a continuous bilinear form -/

section Flat

/-- The normal symplectic form of a symplectic submanifold embedding at `x`, as a continuous
bilinear form on the normal space: it pairs two normal classes as their symplectic representatives
under `σ`. -/
def symplecticNormalFlat (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    f.isImmersion.NormalSpace x hn →L[ℝ] f.isImmersion.NormalSpace x hn →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (f.symplecticNormalRepresentative h x hn)).comp
    ((σ.flat (f x)).comp (f.symplecticNormalRepresentative h x hn))

/-- The continuous normal symplectic form evaluates as the normal symplectic form. -/
@[simp]
theorem symplecticNormalFlat_apply (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0)
        (v w : f.isImmersion.NormalSpace x hn) :
    f.symplecticNormalFlat h x hn v w = f.symplecticNormalForm h x hn v w := by
  simp [symplecticNormalFlat]

end Flat

/-! ### Smoothness of the normal symplectic form -/

section Smooth

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] {m : ℕ∞ω}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The symplectic normal bundle is smooth.** For a `C^n` symplectic submanifold embedding with
`m + 1 ≤ n` and `m + 1 ≤ ∞` (so `m` is finite or `∞`, not analytic), the normal symplectic forms
are a `C^m` section of the bundle of bilinear forms on the intrinsic normal bundle. No
compactness, boundarylessness or normal framing is required. -/
theorem contMDiff_symplecticNormalFlat (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := ∞) (by simp)
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiff I (I.prod 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (P →L[ℝ] P →L[ℝ] ℝ)
        (E := fun x ↦ f.isImmersion.NormalSpace x hn →L[ℝ] f.isImmersion.NormalSpace x hn →L[ℝ] ℝ) x
        (f.symplecticNormalFlat h x hn)) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold J 1 N := .of_le (n := ∞) (by simp)
  have : IsManifold I (m + 1) M := .of_le hm'
  have : IsManifold J (m + 1) N := .of_le hm'
  have : ENat.LEInfty m := ⟨le_self_add.trans hm'⟩
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  intro x
  let e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  let b := Module.Basis.ofVectorSpace ℝ P
  -- The symplectic representatives of the frame sections are `C^m` tangent fields along `f`.
  have hrep (i) : ContMDiffOn I J.tangent m
      (fun y ↦ TotalSpace.mk' V (f y)
        (f.symplecticNormalRepresentative h y hn (e.localFrame b i y))) e.baseSet :=
    (f.contMDiff_symplecticNormalRepresentative h hn hm hm' hdim).comp_contMDiffOn
      (e.contMDiffOn_localFrame_baseSet m b i)
  -- Test the bilinear section on two copies of the local normal frame.
  have hform := TauCeti.Manifold.contMDiffOn_bilinear_of_localFrame (I := I) (n := m) b
    (e := e) subset_rfl (A := fun y ↦ f.symplecticNormalFlat h y hn) fun i j y hy ↦ by
    have hpair := (σ.contMDiffAt_eval₂ ((hrep i y hy).contMDiffAt
      (e.open_baseSet.mem_nhds hy)) ((hrep j y hy).contMDiffAt
      (e.open_baseSet.mem_nhds hy))).contMDiffWithinAt (s := e.baseSet)
    rw [Bundle.contMDiffWithinAt_totalSpace_iff] at hpair
    simpa [Trivial.fiberBundle_trivializationAt'] using hpair.2
  exact hform.contMDiffAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x))

end Smooth

/-! ### Naturality of the normal symplectic form -/

section Naturality

variable {E' V' H' G' M' N' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ V' G'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' ∞ N']
  {n' : ℕ∞ω} {τ : SmoothTwoForm J' N'} {hτ : τ.IsNondegenerate}
  (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n' M' N')
  (hf : hσ.HasSymplecticTangentImages I f) (hg : hτ.HasSymplecticTangentImages I' g)
  {u : M → M'} {v : N → N'} {x : M}

/-- **Symplectic maps carry symplectic representatives to symplectic representatives.** Let
`v : N → N'` be differentiable at `f x`, with differential carrying `σ` to `τ` there, and let it
restrict near `x` to a map `u` between symplectic submanifolds, `v ∘ f = g ∘ u`, whose
differential at `x` is surjective. Then the symplectic representative of the image of a normal
class `ν` under the normal map is the image under `dv` of the symplectic representative of
`ν`. -/
theorem symplecticNormalRepresentative_normalMap (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (hv : MDifferentiableAt J J' v (f x))
    (hvσ : ∀ a b, SmoothBundleForm.eval₂ τ (v (f x)) (mfderiv J J' v (f x) a)
      (mfderiv J J' v (f x) b) = SmoothBundleForm.eval₂ σ (f x) a b)
    (hsurj : Surjective (mfderiv I I' u x)) (ν : f.isImmersion.NormalSpace x hn) :
    g.symplecticNormalRepresentative hg (u x) hn' (f.normalMap g hn hn' h ν) =
      tangentSpaceCast J' (v (f x)) (g (u x))
        (mfderiv J J' v (f x) (f.symplecticNormalRepresentative hf x hn ν)) := by
  have hfx : v (f x) = g (u x) := h.eq_of_nhds
  refine (g.symplecticNormalRepresentative_eq_iff hg (u x) hn' _ _).2 ⟨?_, ?_⟩
  · -- `dv` maps the tangent space of `f` onto that of `g` and preserves the forms, so it maps
    -- the symplectic complement of the first into that of the second.
    refine SymplecticForm.mem_orthogonal_iff.2 fun t ht ↦ ?_
    rw [← f.map_tangentRange_mfderiv g hn hn' hv h hsurj] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    have hw := SymplecticForm.mem_orthogonal_iff.1
      (f.symplecticNormalRepresentative_mem_orthogonal hf x hn ν) t ht
    simp only [IsNondegenerate.symplecticFormAt_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hw ⊢
    rw [SmoothForm.eval₂_tangentSpaceCast τ hfx, hvσ, hw]
  · rw [← normalMap_normalClass, normalClass_symplecticNormalRepresentative]

/-- **Naturality of the normal symplectic form.** Let `v : N → N'` be differentiable at `f x`,
with differential carrying `σ` to `τ` there, and let it restrict near `x` to a map `u` between
symplectic submanifolds, `v ∘ f = g ∘ u`, whose differential at `x` is surjective. Then the
induced normal map is a linear symplectic map from the normal symplectic form of `f` at `x` to
that of `g` at `u x`. -/
theorem symplecticNormalForm_normalMap (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h : v ∘ f =ᶠ[𝓝 x] g ∘ u) (hv : MDifferentiableAt J J' v (f x))
    (hvσ : ∀ a b, SmoothBundleForm.eval₂ τ (v (f x)) (mfderiv J J' v (f x) a)
      (mfderiv J J' v (f x) b) = SmoothBundleForm.eval₂ σ (f x) a b)
    (hsurj : Surjective (mfderiv I I' u x)) (ν μ : f.isImmersion.NormalSpace x hn) :
    g.symplecticNormalForm hg (u x) hn' (f.normalMap g hn hn' h ν) (f.normalMap g hn hn' h μ) =
      f.symplecticNormalForm hf x hn ν μ := by
  have hfx : v (f x) = g (u x) := h.eq_of_nhds
  rw [symplecticNormalForm_apply, symplecticNormalForm_apply,
    f.symplecticNormalRepresentative_normalMap g hf hg hn hn' h hv hvσ hsurj,
    f.symplecticNormalRepresentative_normalMap g hf hg hn hn' h hv hvσ hsurj,
    SmoothForm.eval₂_tangentSpaceCast τ hfx, hvσ]

end Naturality

end TauCeti.SmoothEmbedding
