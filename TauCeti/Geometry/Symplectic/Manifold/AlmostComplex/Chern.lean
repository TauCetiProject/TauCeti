/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
public import TauCeti.Topology.VectorBundle.Complex.LinearPart
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import TauCeti.Geometry.Symplectic.Cayley.Basic
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The first Chern number of a symplectic manifold on spheres

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M`, for instance a symplectic form.
An almost complex structure `J` tamed by `σ` makes the tangent bundle a complex vector bundle
`(TM, J)`, and its clutching number on spheres is the first Chern number `c₁(TM, J)` on the second
homotopy group `π₂(M, x)` (`TauCeti.clutchingNumberHom`). This file shows that it does not depend
on `J`, and so defines the first Chern number of `σ` on spheres.

* **Independence of `J`.** If `J` and `K` are both tamed by `σ`, then `1 - K J` is invertible on
  every tangent space (`TauCeti.SmoothTwoForm.Tames.isUnit_one_sub_toEndomorphism_mul`, from the
  linear `TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul`): a vector with
  `K (J v) = v` has `K v = -J v`, and `σ(v, K v) = -σ(v, J v)` cannot be positive together with
  `σ(v, J v)` unless `v = 0`. So the complex-linear part `v ↦ (v - K (J v)) / 2` of the identity is
  an isomorphism of complex vector bundles `(TM, J) ≃ (TM, K)`
  (`TauCeti.Bundle.ContinuousComplexStructure.complexLinearPartEquiv`), and the clutching numbers of
  `(TM, J)` and `(TM, K)` agree (`TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`), for any
  complex model fibres and any smoothness levels at which `J` and `K` are regarded.
* **The first Chern number of `σ`.** On a Hausdorff σ-compact manifold every fiberwise
  nondegenerate two-form has a compatible, in particular tame, smooth almost complex structure
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`). The first Chern number of `σ` on
  `π₂(M, x)` (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`) is the clutching number
  homomorphism of `(TM, J)` for one such `J`, with model fibre `ℂⁿ`, `2n = dim M`. By independence
  it is the clutching number homomorphism of `(TM, J)` for every tame `J` and every complex model
  fibre (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`).
* **Complex manifolds.** On a complex manifold `M` modelled on `E`, if `σ` tames the complex
  structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, multiplication by `i`,
  then the complex vector bundle `(TM, i)` is the holomorphic tangent bundle: the identity of `E`
  on the fibres is complex linear, and continuous on total spaces
  (`TangentBundle.restrictScalarsHomeomorph`). So the first Chern number of `σ` is the
  clutching number homomorphism of the holomorphic tangent bundle
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`).

The first Chern number on spheres and the symplectic area of spheres
(`TauCeti.sphereIntegralHom`) are the two periods of capped Hamiltonian Floer theory: the grading
and the action of a capped periodic orbit change by `2 c₁(B)` and `ω(B)` when a sphere `B` is glued
to its cap. The first Chern number here is the clutching description on spheres; no comparison
with a cohomological first Chern class is made.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`: the first Chern number
  `π₂(M, x) → ℤ` of a fiberwise nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`: two almost complex structures tamed by the
  same two-form give the same clutching numbers.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`: the first Chern
  number is the clutching number homomorphism of the tangent bundle for any tame almost complex
  structure.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`: on a
  complex manifold, for a two-form taming the complex structure, it is the clutching number
  homomorphism of the holomorphic tangent bundle.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the space of tame complex structures and the first Chern class of a symplectic
  manifold) and Section 2.7 (the first Chern number of a symplectic bundle over a surface).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

noncomputable section

open Bundle Module Topology
open scoped ContDiff Manifold Topology.Homotopy

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J K : SmoothAlmostComplexStructure I M}

variable [FiniteDimensional ℝ E]
  (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [NormedAddCommGroup G'] [NormedSpace ℂ G']
  [FiniteDimensional ℂ G'] [Fact (finrank ℝ E = 2 * finrank ℂ G')]

/-- **Independence of the tame almost complex structure.** If `J` and `K` are both tamed by `σ`,
the tangent bundles `(TM, J)` and `(TM, K)` have the same clutching number homomorphism
`π₂(M, x) → ℤ`, for any complex model fibres `G` and `G'` and any smoothness levels `n` and `m` at
which `J` and `K` are regarded. -/
theorem Tames.clutchingNumberHom_eq (hJ : σ.Tames J) (hK : σ.Tames K) (n m : ℕ∞) (x : M) :
    clutchingNumberHom G' (K.toContMDiff m).toContinuousComplexStructure.Fiber x =
      clutchingNumberHom G (J.toContMDiff n).toContinuousComplexStructure.Fiber x := by
  refine Bundle.ContinuousComplexStructure.clutchingNumberHom_fiber_eq (fun y v hv ↦ ?_) G G' x
  -- On each tangent space, `1 - K J` is invertible because `J` and `K` are tamed by `σ`.
  have hunit := hJ.isUnit_one_sub_toEndomorphism_mul hK y
  apply (ContinuousLinearEquiv.unitsEquiv ℝ _ hunit.unit).injective
  simpa [sub_eq_zero] using hv.symm

namespace IsNondegenerate

variable [T2Space M] [SigmaCompactSpace M]

/-- The model space `E` of a manifold with a fiberwise nondegenerate two-form has even dimension,
so `ℂⁿ` with `n = dim E / 2` is a complex model fibre for its tangent bundle. -/
private theorem two_mul_finrank_euclideanSpace (h : σ.IsNondegenerate) (x : M) :
    finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) := by
  rw [finrank_euclideanSpace_fin, Nat.two_mul_div_two_of_even]
  exact ((exists_compatible h).choose.almostComplexStructureAt x).even_finrank_real

/-- The **first Chern number** `c₁ : π₂(M, x) → ℤ` of a fiberwise nondegenerate two-form `σ` on a
Hausdorff σ-compact manifold: the clutching number homomorphism of the tangent bundle, made a
complex vector bundle by an almost complex structure compatible with `σ`. It does not depend on
that structure, nor on the complex model fibre: it is the clutching number homomorphism for every
almost complex structure tamed by `σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`). -/
def firstChernHom (h : σ.IsNondegenerate) (x : M) : Additive (π_ 2 M x) →+ ℤ :=
  haveI : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace h x⟩
  clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
    ((exists_compatible h).choose.toContMDiff ⊤).toContinuousComplexStructure.Fiber x

/-- **The first Chern number from any tame almost complex structure.** The first Chern number of
`σ` on `π₂(M, x)` is the clutching number homomorphism of the tangent bundle `(TM, J)`, for every
almost complex structure `J` tamed by `σ` and every complex model fibre `G`. -/
theorem firstChernHom_eq_clutchingNumberHom (h : σ.IsNondegenerate) (hJ : σ.Tames J) (n : ℕ∞)
    (x : M) :
    h.firstChernHom x =
      clutchingNumberHom G (J.toContMDiff n).toContinuousComplexStructure.Fiber x := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace h x⟩
  exact Tames.clutchingNumberHom_eq _ _ hJ (exists_compatible h).choose_spec.tames n ⊤ x

/-- The first Chern number of `σ` on the class of a sphere `p` is the clutching number of `p` for
the tangent bundle `(TM, J)`, for every almost complex structure `J` tamed by `σ` and every
complex model fibre `G`. -/
theorem firstChernHom_apply_mk (h : σ.IsNondegenerate) (hJ : σ.Tames J) (n : ℕ∞) {x : M}
    (p : Ω^ (Fin 2) M x) :
    h.firstChernHom x (Additive.ofMul (Quotient.mk _ p)) =
      clutchingNumber G (J.toContMDiff n).toContinuousComplexStructure.Fiber p := by
  rw [firstChernHom_eq_clutchingNumberHom G h hJ n x, clutchingNumberHom_apply_mk]

end IsNondegenerate

end TauCeti.SmoothTwoForm

/-! ### Complex manifolds -/

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open SmoothAlmostComplexStructure
open scoped TauCeti.ComplexManifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The real dimension of a complex normed space is twice its complex dimension, so `E` is a
complex model fibre for the tangent bundle of a complex manifold modelled on `E`. -/
private local instance : Fact (finrank ℝ E = 2 * finrank ℂ E) := ⟨finrank_real_of_complex E⟩

/-- On a complex manifold, the fibre of the real tangent bundle with the complex structure `i` is
the fibre of the holomorphic tangent bundle, by the identity of `E`. -/
private def holomorphicTangentEquiv (n : ℕ∞) (x : M) :
    ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x ≃L[ℂ]
      TangentSpace 𝓘(ℂ, E) x :=
  let J := ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure
  { toFun v := (J.fiberEquiv x v : E)
    invFun v := (J.fiberEquiv x).symm v
    map_add' := map_add (J.fiberEquiv x)
    map_smul' z v := by
      -- In the fibre `z • v = re z • v + im z • J v`, and `J` is multiplication by `i` on `E`.
      set w : E := J.fiberEquiv x v
      have hJ : J x w = Complex.I • w :=
        ((ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply _ x w).trans
          (toContMDiff_apply _ n x w)).trans (ofComplexManifold_apply x w)
      exact (J.fiberEquiv_smul x z v).trans
        ((congrArg (z.re • w + z.im • ·) hJ).trans (Complex.re_smul_add_im_smul z w))
    left_inv v := (J.fiberEquiv x).symm_apply_apply v
    right_inv v := (J.fiberEquiv x).apply_symm_apply v
    continuous_toFun := (J.fiberEquiv x).continuous
    continuous_invFun := (J.fiberEquiv x).symm.continuous }

private theorem holomorphicTangentEquiv_apply (n : ℕ∞) (x : M)
    (v : ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x) :
    holomorphicTangentEquiv n x v =
      (((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.fiberEquiv x v : E) :=
  (rfl)

variable [FiniteDimensional ℂ E] [T2Space M] [SigmaCompactSpace M]

/-- **The first Chern number of a complex manifold.** If a fiberwise nondegenerate two-form `σ` on
a complex manifold `M` tames its complex structure (multiplication by `i` on the tangent spaces),
for instance a Kähler form, then its first Chern number on `π₂(M, x)` is the clutching number
homomorphism of the holomorphic tangent bundle of `M`. -/
theorem firstChernHom_eq_clutchingNumberHom_tangentSpace {σ : SmoothTwoForm 𝓘(ℝ, E) M}
    (h : σ.IsNondegenerate) (hJ : σ.Tames (ofComplexManifold E M)) (x : M) :
    h.firstChernHom x = clutchingNumberHom E (TangentSpace 𝓘(ℂ, E)) x := by
  set J := ((ofComplexManifold E M).toContMDiff ⊤).toContinuousComplexStructure
  rw [h.firstChernHom_eq_clutchingNumberHom E hJ ⊤ x]
  refine (clutchingNumberHom_eq_of_continuousLinearEquiv (holomorphicTangentEquiv ⊤) ?_ x).symm
  -- On total spaces the identification is the identity of the real tangent bundle, followed by
  -- the identity from the real onto the holomorphic tangent bundle.
  refine ((TangentBundle.restrictScalarsHomeomorph ℝ (𝕜' := ℂ) M).symm.continuous.comp
    (J.totalSpaceHomeomorph E).continuous).congr fun v ↦ ?_
  rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
    TangentBundle.restrictScalarsHomeomorph_symm_apply, holomorphicTangentEquiv_apply]
  -- The identifications `tangentSpaceCastModel` of tangent spaces with `E` are the identity by
  -- definition, and Mathlib states no evaluation lemma for them.
  rfl

end TauCeti.SmoothTwoForm.IsNondegenerate
