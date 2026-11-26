/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Levi
public import TauCeti.Geometry.Manifold.Distribution.Quotient
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The Levi form of a distribution as a bundle map

Let `D` be a `C^(n+1)` distribution of rank `k` on a manifold `M` of dimension `k + r`, over `ℝ`
or `ℂ`. Then `D` is a `C^(n+1)` vector bundle (`TauCeti.IsContMDiffDistribution.fiberBundle`), and
so is the quotient `TM ⧸ D` of the tangent bundle, of rank `r`
(`TauCeti.IsContMDiffDistribution.quotientPrebundle`). At each point `x` the Levi form
`L_D x : D x × D x → T_x M ⧸ D x`, `L_D x (V x, W x) = -[V, W] x mod D x`
(`TauCeti.distributionLeviForm`), is a bilinear map of finite-dimensional spaces. This file shows
that these bilinear maps depend smoothly on `x`, losing one derivative to the Lie bracket.

* **Sections.** For two sections `σ`, `τ` of `D` whose underlying vector fields are `C^(n+1)` on
  an open set `W`, the section `x ↦ L_D x (σ x, τ x)` of `TM ⧸ D`, which is the class of
  `-[σ, τ]` modulo `D` (`TauCeti.distributionLeviForm_apply`), is `C^n` on `W`
  (`TauCeti.contMDiffOn_distributionLeviForm`).
* **The bundle map.** Read as continuous bilinear maps
  (`TauCeti.distributionLeviFormL D x : D x →L D x →L T_x M ⧸ D x`), the Levi forms are a `C^n`
  section of the iterated Hom bundle `Hom(D, Hom(D, TM ⧸ D))`
  (`TauCeti.contMDiff_distributionLeviFormL`). This is tested on the local frames of `D` given by
  its trivializations, on which it reduces to the statement for sections.
* **Nondegeneracy.** Consequently the map `u ↦ L_D x (u, ·)` of total spaces
  `D → Hom(D, TM ⧸ D)` is `C^n`, and it is a `C^n` diffeomorphism of total spaces, that is a
  `C^n` isomorphism of vector bundles `D ≅ Hom(D, TM ⧸ D)`, exactly when the Levi form is
  nondegenerate at every point (`TauCeti.exists_bundleDiffeomorph_distributionLeviFormL_iff`).

A contact structure `ξ` (`TauCeti.IsContactDistribution`) is a hyperplane field, of rank
`dim M - 1`, whose Levi form is nondegenerate at every point. For it the quotient `L = TM ⧸ ξ` is
the contact line, a line bundle (`r = 1`), and the last statement says that the Levi form
identifies `ξ` with `Hom(ξ, L)` as smooth vector bundles: `L_ξ` is a nondegenerate `L`-valued
alternating form on `ξ`, smoothly in the base point
(`TauCeti.IsContactDistribution.exists_bundleDiffeomorph_distributionLeviFormL`).

## Main definitions

* `TauCeti.distributionLeviFormL D x`: the Levi form of `D` at `x` as a continuous bilinear map.

## Main results

* `TauCeti.contMDiffOn_distributionLeviForm`: the Levi form of two `C^(n+1)` sections of `D` is a
  `C^n` section of `TM ⧸ D`.
* `TauCeti.contMDiff_distributionLeviFormL`: the Levi form is a `C^n` section of
  `Hom(D, Hom(D, TM ⧸ D))`.
* `TauCeti.exists_bundleDiffeomorph_distributionLeviFormL_iff`: the Levi form is nondegenerate
  everywhere exactly when `u ↦ L_D (u, ·)` is a `C^n` bundle isomorphism `D ≅ Hom(D, TM ⧸ D)`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 1 (contact structures as maximally non-integrable hyperplane fields).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (vector bundles, local frames and bundle homomorphisms) and Chapter 19 (distributions).
-/

public section

noncomputable section

open Set Filter Function Bundle Module VectorField
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : ℕ∞ω} {k r : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

variable (D) in
/-- The **Levi form** of a distribution `D` at `x` (`TauCeti.distributionLeviForm`) as a continuous
bilinear map `D x →L D x →L T_x M ⧸ D x`. All three spaces are finite-dimensional, so every linear
map between them is continuous; this is the form in which the Levi forms are a section of the
Hom bundle `Hom(D, Hom(D, TM ⧸ D))`. -/
def distributionLeviFormL (x : M) : D x →L[𝕜] D x →L[𝕜] TangentSpace I x ⧸ D x :=
  haveI : FiniteDimensional 𝕜 (TangentSpace I x) := inferInstanceAs (FiniteDimensional 𝕜 E)
  (distributionLeviForm D x).toContinuousBilinearMap

/-- The continuous Levi form `TauCeti.distributionLeviFormL` takes the values of the Levi form. -/
@[simp]
theorem distributionLeviFormL_apply (x : M) (u v : D x) :
    distributionLeviFormL D x u v = distributionLeviForm D x u v :=
  (rfl)

/-- The continuous Levi form `u ↦ L_D x (u, ·)` is bijective onto the continuous linear maps
`D x →L T_x M ⧸ D x` exactly when the Levi form is nondegenerate, that is bijective onto the
linear maps. -/
theorem bijective_distributionLeviFormL_iff (x : M) :
    Bijective (distributionLeviFormL D x) ↔ Bijective (distributionLeviForm D x) := by
  have : FiniteDimensional 𝕜 (TangentSpace I x) := inferInstanceAs (FiniteDimensional 𝕜 E)
  have h : ⇑(distributionLeviFormL D x) =
      LinearMap.toContinuousLinearMap ∘ distributionLeviForm D x := by
    ext u v
    simp
  rw [h, (LinearEquiv.bijective _).of_comp_iff']

variable [IsRCLikeNormedField 𝕜] [IsManifold I (n + 1 + 1) M]

/-- **The Levi form of smooth sections is smooth.** Let `D` be a `C^(n+1)` distribution of rank
`k` on a manifold of dimension `k + r`. For two sections `σ` and `τ` of `D` whose underlying vector
fields are `C^(n+1)` on an open set `W`, the section `x ↦ L_D x (σ x, τ x)` of the quotient bundle
`TM ⧸ D` is `C^n` on `W`. It is the class of `-[σ, τ]` modulo `D`
(`TauCeti.distributionLeviForm_apply`). -/
theorem contMDiffOn_distributionLeviForm (hD : IsContMDiffDistribution I (n + 1) k D)
    (hr : k + r = finrank 𝕜 E) {W : Set M} (hW : IsOpen W) {σ τ : Π x : M, D x}
    (hσ : CMDiff[W] (n + 1) (T% fun x ↦ (σ x : TangentSpace I x)))
    (hτ : CMDiff[W] (n + 1) (T% fun x ↦ (τ x : TangentSpace I x))) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    ContMDiffOn I (I.prod 𝓘(𝕜, Fin r → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin r → 𝕜) (E := fun x ↦ TangentSpace I x ⧸ D x) x
        (distributionLeviForm D x (σ x) (τ x))) W := by
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  let : IsManifold I (minSmoothness 𝕜 2) M := by
    rwa [minSmoothness_of_isRCLikeNormedField]
  intro x hx
  have hσx := hσ.contMDiffAt (hW.mem_nhds hx)
  have hτx := hτ.contMDiffAt (hW.mem_nhds hx)
  -- The Lie bracket of the two fields is `C^n` at `x`.
  have hb : CMDiffAt n (T% (-mlieBracket I (fun y ↦ (σ y : TangentSpace I y))
      (fun y ↦ (τ y : TangentSpace I y)))) x := by
    have h := hσx.contMDiffWithinAt.mlieBracketWithin_vectorField (s := univ)
      hτx.contMDiffWithinAt uniqueMDiffOn_univ (mem_univ x) (m := n) (by simp)
    rw [mlieBracketWithin_univ] at h
    exact h.neg_section
  refine (((hD.contMDiff_totalSpace_mkQ hr).of_le le_self_add).contMDiffAt.comp x hb
    ).contMDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) hx
  have hσy := (hσ.contMDiffAt (hW.mem_nhds hy)).mdifferentiableAt (by simp)
  have hτy := (hτ.contMDiffAt (hW.mem_nhds hy)).mdifferentiableAt (by simp)
  have h := distributionLeviForm_apply hD le_add_self hσy hτy
    (.of_forall fun y ↦ (σ y).property) (.of_forall fun y ↦ (τ y).property)
  simp only [Function.comp_apply, h, Pi.neg_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_neg]

/-- **The Levi form is a smooth bundle map.** For a `C^(n+1)` distribution `D` of rank `k` on a
manifold of dimension `k + r`, the Levi forms `L_D x`, read as continuous bilinear maps
`D x →L D x →L T_x M ⧸ D x`, form a `C^n` section of the Hom bundle `Hom(D, Hom(D, TM ⧸ D))`. -/
theorem contMDiff_distributionLeviFormL (hD : IsContMDiffDistribution I (n + 1) k D)
    (hr : k + r = finrank 𝕜 E) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    ContMDiff I (I.prod 𝓘(𝕜, (Fin k → 𝕜) →L[𝕜] (Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))) n
      (fun x ↦ TotalSpace.mk' ((Fin k → 𝕜) →L[𝕜] (Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))
        (E := fun x ↦ D x →L[𝕜] D x →L[𝕜] TangentSpace I x ⧸ D x) x
        (distributionLeviFormL D x)) := by
  let := hD.fiberBundle
  let := hD.vectorBundle
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  let := (hD.quotientPrebundle hr).toVectorBundle
  have : ContMDiffVectorBundle (n + 1) (Fin k → 𝕜) (fun x ↦ D x) I := hD.contMDiffVectorBundle
  have : ContMDiffVectorBundle n (Fin k → 𝕜) (fun x ↦ D x) I := .of_le (le_self_add (b := 1))
  have : ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) I :=
    (hD.contMDiffVectorBundle_quotientPrebundle hr).of_le (le_self_add (b := 1))
  intro x₀
  let e := trivializationAt (Fin k → 𝕜) (fun x ↦ D x) x₀
  let eQ := trivializationAt (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) x₀
  let eH := trivializationAt ((Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))
    (fun x ↦ D x →L[𝕜] TangentSpace I x ⧸ D x) x₀
  let b := Pi.basisFun 𝕜 (Fin k)
  let u := e.baseSet ∩ eQ.baseSet ∩ eH.baseSet
  have hu : IsOpen u := (e.open_baseSet.inter eQ.open_baseSet).inter eH.open_baseSet
  have hx₀ : x₀ ∈ u := ⟨⟨mem_baseSet_trivializationAt _ _ x₀,
    mem_baseSet_trivializationAt _ _ x₀⟩, mem_baseSet_trivializationAt _ _ x₀⟩
  -- The local frame of `D` given by `e`, as vector fields, is `C^(n+1)` on `e.baseSet`.
  have hs (j : Fin k) : CMDiff[u] (n + 1)
      (T% fun x ↦ (e.localFrame b j x : TangentSpace I x)) :=
    (hD.contMDiff_totalSpace_inclusion.comp_contMDiffOn
      (e.contMDiffOn_localFrame_baseSet (n := n + 1) b j)).mono
      (inter_subset_left.trans inter_subset_left)
  -- Test the section on this frame twice, once for each argument of the Levi form.
  refine (Manifold.contMDiffOn_hom_of_localFrame (e := e) (e' := eH) (b := b) (f := id)
    contMDiffOn_id (fun x hx ↦ ⟨hx.1.1, hx.2⟩) (u := u) fun j ↦ ?_).contMDiffAt (hu.mem_nhds hx₀)
  refine Manifold.contMDiffOn_hom_of_localFrame (e := e) (e' := eQ) (b := b) (f := id)
    contMDiffOn_id (fun x hx ↦ hx.1) (u := u) fun i ↦ ?_
  exact (contMDiffOn_distributionLeviForm hD hr hu (hs j) (hs i)).congr fun x _ ↦ by simp

/-- **The Levi form is nondegenerate exactly when it is a bundle isomorphism.** For a `C^(n+1)`
distribution `D` of rank `k` on a manifold of dimension `k + r`, the map of total spaces
`D → Hom(D, TM ⧸ D)`, `(x, u) ↦ (x, L_D x (u, ·))`, is a `C^n` diffeomorphism, that is a `C^n`
isomorphism of vector bundles `D ≅ Hom(D, TM ⧸ D)`, exactly when the Levi form of `D` is
nondegenerate at every point. For a contact structure, of rank `dim M - 1`, this identifies the
contact distribution with the Hom bundle into its contact line. -/
theorem exists_bundleDiffeomorph_distributionLeviFormL_iff
    (hD : IsContMDiffDistribution I (n + 1) k D) (hr : k + r = finrank 𝕜 E) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    (∃ Φ : TotalSpace (Fin k → 𝕜) (fun x ↦ D x) ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin k → 𝕜),
        I.prod 𝓘(𝕜, (Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))⟯
        TotalSpace ((Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))
          (fun x ↦ D x →L[𝕜] TangentSpace I x ⧸ D x),
      ⇑Φ = fun p ↦ TotalSpace.mk' ((Fin k → 𝕜) →L[𝕜] (Fin r → 𝕜))
        (E := fun x ↦ D x →L[𝕜] TangentSpace I x ⧸ D x) p.proj
        (distributionLeviFormL D p.proj p.snd)) ↔
      ∀ x, Bijective (distributionLeviForm D x) := by
  let := hD.fiberBundle
  let := hD.vectorBundle
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  let := (hD.quotientPrebundle hr).toVectorBundle
  rw [exists_bundleDiffeomorph_iff,
    ← contMDiff_hom_bundle_iff (distributionLeviFormL D)]
  simp only [bijective_distributionLeviFormL_iff, contMDiff_distributionLeviFormL hD hr,
    true_and]

end TauCeti
