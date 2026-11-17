/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# Smoothness of the fibrewise Hilbert–Schmidt inner product on Hom bundles

Let `E₁` be a finite-rank `C^n` Riemannian vector bundle and `E₂` an arbitrary `C^n` Riemannian
vector bundle over a manifold `B`. Each fibre `E₁ z →L[ℝ] E₂ z` of the homomorphism bundle carries
the basis-independent Hilbert–Schmidt inner product `ContinuousLinearMap.hilbertSchmidtInner`.

This file proves that `hilbertSchmidtInner` varies `C^n`-smoothly with two `C^n` Hom-bundle fields
along a common base map `b : M → B`, within an arbitrary set and at any differentiability order
`n : ℕ∞ω`. Neither finite rank nor `ContMDiffVectorBundle` is needed on the target bundle `E₂`, and
no `IsManifold` assumption is needed on `M` or `B`. Taking `E₁ = TangentSpace I` on a `C^(n + 1)`
Riemannian manifold specializes directly to `E₂`-valued one-forms, supplying the smoothness of
`⟨η₁, η₂⟩_{HS}` used to integrate Dirichlet energies and prove formal adjunction of connections.

The proof evaluates both fields on a local `C^n` orthonormal frame of `E₁` constructed by
fibrewise Gram–Schmidt (`Bundle.Trivialization.contMDiffOn_orthonormalBasis`) and rewrites the sum
using `ContinuousLinearMap.hilbertSchmidtInner_eq_sum`.

## Main results

* `ContMDiffWithinAt.hilbertSchmidtInner`, `ContMDiffAt.hilbertSchmidtInner`,
  `ContMDiffOn.hilbertSchmidtInner`, and `ContMDiff.hilbertSchmidtInner`: `C^n` regularity of the
  fibrewise Hilbert–Schmidt inner product of Hom-bundle fields along a base map.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (fibre inner products on bundle homomorphisms).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), Section VI.6.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace Topology

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ z, NormedAddCommGroup (E₁ z)] [∀ z, InnerProductSpace ℝ (E₁ z)]
  [∀ z, FiniteDimensional ℝ (E₁ z)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F₁ E₁ IB] [IsContMDiffRiemannianBundle IB n F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ z, NormedAddCommGroup (E₂ z)] [∀ z, InnerProductSpace ℝ (E₂ z)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] [IsContMDiffRiemannianBundle IB n F₂ E₂]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {η₁ η₂ : Π m : M, E₁ (b m) →L[ℝ] E₂ (b m)} {s : Set M} {x : M}

/-- The fibrewise Hilbert–Schmidt inner product of two `C^n` Hom-bundle fields out of a finite-rank
`C^n` Riemannian bundle `E₁` into a `C^n` Riemannian bundle `E₂` along a common base map is `C^n`
within the same set. Neither finite rank nor smooth transitions are needed on `E₂`. -/
theorem ContMDiffWithinAt.hilbertSchmidtInner
    (hη₁ : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₁ m)) s x)
    (hη₂ : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₂ m)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n
      (fun m ↦ ContinuousLinearMap.hilbertSchmidtInner (η₁ m) (η₂ m)) s x := by
  classical
  have hb : ContMDiffWithinAt IM IB n b s x := (contMDiffWithinAt_totalSpace_iff.mp hη₁).1
  let : FiniteDimensional ℝ F₁ :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ E₁ (b x)).finiteDimensional
  let e := trivializationAt F₁ E₁ (b x)
  let c := Module.finBasis ℝ F₁
  let v : Fin (Module.finrank ℝ F₁) → ∀ z, E₁ z := fun i z ↦
    if hz : z ∈ e.baseSet then e.orthonormalBasis c ⟨z, hz⟩ i else 0
  have hbx : b x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ E₁ (b x)
  have hv (i) : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F₁)) n
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v i (b m))) s x :=
    ((e.contMDiffOn_orthonormalBasis c i).contMDiffAt
      (e.open_baseSet.mem_nhds hbx)).comp_contMDiffWithinAt x hb
  have hs := contMDiffWithinAt_finsetSum (t := Finset.univ) fun i _ ↦
    (hη₁.clm_bundle_apply (hv i)).inner_bundle (hη₂.clm_bundle_apply (hv i))
  have heq {z : B} (hz : z ∈ e.baseSet) (S T : E₁ z →L[ℝ] E₂ z) :
      ∑ i, ⟪S (v i z), T (v i z)⟫ = ContinuousLinearMap.hilbertSchmidtInner S T := by
    simpa only [v, hz, ↓reduceDIte] using
      (ContinuousLinearMap.hilbertSchmidtInner_eq_sum S T (e.orthonormalBasis c ⟨z, hz⟩)).symm
  exact hs.congr_of_eventuallyEq
    (Filter.eventually_of_mem
      (hb.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbx))
      fun m hm ↦ (heq hm (η₁ m) (η₂ m)).symm)
    (heq hbx (η₁ x) (η₂ x)).symm

/-- The fibrewise Hilbert–Schmidt inner product of two Hom-bundle fields `C^n` at a point along a
common base map is `C^n` there. -/
theorem ContMDiffAt.hilbertSchmidtInner
    (hη₁ : ContMDiffAt IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₁ m)) x)
    (hη₂ : ContMDiffAt IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₂ m)) x) :
    ContMDiffAt IM 𝓘(ℝ) n
      (fun m ↦ ContinuousLinearMap.hilbertSchmidtInner (η₁ m) (η₂ m)) x :=
  ContMDiffWithinAt.hilbertSchmidtInner hη₁ hη₂

/-- The fibrewise Hilbert–Schmidt inner product of two Hom-bundle fields `C^n` on a set along a
common base map is `C^n` on that set. -/
theorem ContMDiffOn.hilbertSchmidtInner
    (hη₁ : ContMDiffOn IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₁ m)) s)
    (hη₂ : ContMDiffOn IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₂ m)) s) :
    ContMDiffOn IM 𝓘(ℝ) n
      (fun m ↦ ContinuousLinearMap.hilbertSchmidtInner (η₁ m) (η₂ m)) s :=
  fun x hx ↦ (hη₁ x hx).hilbertSchmidtInner (hη₂ x hx)

/-- The fibrewise Hilbert–Schmidt inner product of two `C^n` Hom-bundle fields along a common base
map is `C^n`. -/
theorem ContMDiff.hilbertSchmidtInner
    (hη₁ : ContMDiff IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₁ m)))
    (hη₂ : ContMDiff IM (IB.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun z ↦ E₁ z →L[ℝ] E₂ z) (b m) (η₂ m))) :
    ContMDiff IM 𝓘(ℝ) n
      (fun m ↦ ContinuousLinearMap.hilbertSchmidtInner (η₁ m) (η₂ m)) :=
  fun x ↦ (hη₁ x).hilbertSchmidtInner (hη₂ x)

end
