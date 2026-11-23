/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Fibrewise operations on tangent endomorphisms

Reading an endomorphism of a tangent space in a trivialization of the tangent bundle is
conjugation by a linear isomorphism of that tangent space with the model space. So a binary
operation on endomorphisms of the model space that commutes with such conjugations, as algebraic
expressions in endomorphisms do, can be applied in every tangent fibre, and its regularity on
sections of `End(TM)` is read off its regularity on the model space.

## Main results

* `ContMDiffAt.comp₂_hom_bundle`: a binary operation on endomorphisms that commutes with
  conjugation, applied fibrewise to two `Cⁿ` families of tangent endomorphisms, is `Cⁿ` where the
  operation is.
-/

public section

open Bundle
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n : WithTop ℕ∞} {f : P → M}
  {A B : (q : P) → TangentSpace I (f q) →L[ℝ] TangentSpace I (f q)} {q₀ : P}

/-- **Regularity of fibrewise binary operations on tangent endomorphisms.** Let `g` be a binary
operation on `E →L[ℝ] E`, applied in every tangent fibre, that commutes with conjugation by every
identification `L` of a tangent space with `E`, as algebraic expressions in endomorphisms do. For
two families `A` and `B` of tangent endomorphisms along a map `f`, both `Cⁿ` at `q₀` as sections of
`End(TM)`, the family `g (A q, B q)` is `Cⁿ` at `q₀` when `g` is `Cⁿ` at every conjugate of
`(A q₀, B q₀)` by such an `L`: reading a fibre endomorphism in a trivialization of the tangent
bundle is such a conjugation. -/
theorem ContMDiffAt.comp₂_hom_bundle {g : (E →L[ℝ] E) × (E →L[ℝ] E) → E →L[ℝ] E}
    (hg : ∀ L : TangentSpace I (f q₀) ≃L[ℝ] E,
      ContDiffAt ℝ n g (L.conjContinuousAlgEquiv (A q₀), L.conjContinuousAlgEquiv (B q₀)))
    (hgL : ∀ (x : M) (L : TangentSpace I x ≃L[ℝ] E)
      (a b : TangentSpace I x →L[ℝ] TangentSpace I x),
      L.conjContinuousAlgEquiv (g (a, b)) =
        g (L.conjContinuousAlgEquiv a, L.conjContinuousAlgEquiv b))
    (hf : ContMDiffAt IP I n f q₀)
    (hA : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (A q)) q₀)
    (hB : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (B q)) q₀) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (g (A q, B q))) q₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf, ?_⟩
  let e := trivializationAt E (TangentSpace I) (f q₀)
  -- Reading a fibre endomorphism in the trivialization at `f q₀` is conjugation by an algebra
  -- isomorphism.
  have hconj {x : M} (hx : x ∈ e.baseSet) (C : TangentSpace I x →L[ℝ] TangentSpace I x) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (f q₀) x (f q₀) x C =
        (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv C :=
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx C
  have hx₀ : f q₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (f q₀)
  have hinner :=
    ((contMDiffAt_hom_bundle _).1 hA).2.prodMk_space ((contMDiffAt_hom_bundle _).1 hB).2
  refine (ContDiffAt.comp_contMDiffAt (g := g) (x := q₀) ?_ hinner).congr_of_eventuallyEq ?_
  · simp only [hconj hx₀]
    exact hg (e.continuousLinearEquivAt ℝ (f q₀) hx₀)
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx₀)] with q hq
  simp only [Function.comp_apply, hconj hq]
  exact (hconj hq (g (A q, B q))).trans (hgL _ (e.continuousLinearEquivAt ℝ (f q) hq) (A q) (B q))
