/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Vanishing of the derivative of a vector-valued function

For a function `g` from a manifold to a normed space `F`, Mathlib has two derivatives at `x`:
`mfderiv I 𝓘(𝕜, F) g x`, with values in the tangent space `TangentSpace 𝓘(𝕜, F) (g x)`, and
`mvfderiv I g x`, with values in `F` itself. They differ by the identification of the tangent space
with `F`, so one vanishes exactly when the other does.

## Main results

* `TauCeti.mvfderiv_comp_apply_of_differentiableAt`: the chain rule when the outer map is
  between normed spaces.
* `TauCeti.mvfderiv_scalar_comp`: the chain rule `d(φ ∘ g) = φ'(g x) • dg` for scalar `φ`.
* `ContinuousLinearMap.mvfderiv_comp_apply`: the chain rule when the outer map is continuous
  linear.
* `MDifferentiableAt.mvfderiv_prod_eq_add_apply`: the vector-valued derivative on a product
  is the sum of its partial derivatives.
* `TauCeti.fderiv_comp_graph_apply_of_mdifferentiableAt`: the chain rule along the graph of a
  manifold-valued map on a normed space.
* `TauCeti.mvfderiv_apply`: the derivative of a component of a function into a finite product is
  the component of its derivative.
* `mvfderiv_apply_eq_mfderiv_apply`: evaluating `mvfderiv` agrees with evaluating `mfderiv`.
* `TauCeti.mvfderiv_const_smul`: `mvfderiv` commutes with multiplication by a constant scalar.
* `TauCeti.mvfderiv_const_smul_field`: the same for a scalar in the base field, without a
  differentiability hypothesis.
* `Filter.EventuallyEq.mvfderiv_eq`: `mvfderiv` depends only on the germ of the function.
* `TauCeti.mvfderiv_apply_of_eventuallyEq_extChartAt`: a map with the germ of the extended chart
  at `x` has the identity as derivative at `x`.
* `TauCeti.mvfderiv_eq_zero_iff`: `mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0`.
* `TauCeti.injective_mvfderiv_iff`:
  `Function.Injective (mvfderiv I g x) ↔ Function.Injective (mfderiv I 𝓘(𝕜, F) g x)`.
* `TauCeti.mdifferentiableAt_of_mvfderiv_apply_ne_zero`: a function whose `mvfderiv` is nonzero on
  some tangent vector is differentiable there.
* `TauCeti.mfderiv_neg_eq_zero_iff`: `mfderiv I 𝓘(𝕜, F) (-g) x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0`.
-/

public section

open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The canonical model-space tangent identification preserves the underlying vector.
Use this equation explicitly: automatic simplification can change an equality's codomain
from the tangent fibre to the model, whose normed-space instances are distinct. -/
theorem _root_.NormedSpace.fromTangentSpace_apply (x : E) (v : TangentSpace 𝓘(𝕜, E) x) :
    NormedSpace.fromTangentSpace (𝕜 := 𝕜) x v = v := rfl

/-- The inverse model-space tangent identification preserves the underlying vector.
As with `fromTangentSpace_apply`, this equation is for explicit tangent/model conversions. -/
theorem _root_.NormedSpace.fromTangentSpace_symm_apply (x : E) (v : E) :
    (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm v = v := rfl

/-- For a normed vector-space target, evaluating `mvfderiv` agrees with evaluating
`mfderiv` under the canonical tangent-space identification. -/
@[simp] theorem _root_.mvfderiv_apply_eq_mfderiv_apply
    (f : M → F) (x : M) (v : TangentSpace I x) :
    mvfderiv I f x v = mfderiv I 𝓘(𝕜, F) f x v := by
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  exact NormedSpace.fromTangentSpace_apply _ _

/-- The derivative at `x` of a vector-valued function, read in the target space, depends only on
the germ of the function at `x`. -/
theorem _root_.Filter.EventuallyEq.mvfderiv_eq {f₁ f : M → F} {x : M} (hf : f₁ =ᶠ[𝓝 x] f) :
    mvfderiv I f₁ x = mvfderiv I f x := by
  ext v
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hf.mfderiv_eq]
  -- `tangentSpaceCast` identifies two tangent spaces of `F`, both of which are `F` itself.
  rfl

/-- A map into the model space with the germ of the extended chart at `x` has the identity as
derivative at `x`, a tangent vector at `x` being read as a vector of the model space. -/
theorem mvfderiv_apply_of_eventuallyEq_extChartAt [IsManifold I 1 M] {f : M → E} {x : M}
    (hf : f =ᶠ[𝓝 x] extChartAt I x) (v : TangentSpace I x) : mvfderiv I f x v = v := by
  rw [hf.mvfderiv_eq]
  simp only [mvfderiv, mfderiv_extChartAt_self]
  -- Both tangent identifications are the identity of `E` across type synonyms.
  rfl

/-- The chain rule for a vector-valued function on a manifold followed by a map between normed
spaces that is differentiable at the relevant point, evaluated on a tangent vector. -/
theorem mvfderiv_comp_apply_of_differentiableAt {g : M → F} {φ : F → F'} {x : M}
    (hφ : DifferentiableAt 𝕜 φ (g x)) (hg : MDiffAt g x) (v : TangentSpace I x) :
    mvfderiv I (φ ∘ g) x v = fderiv 𝕜 φ (g x) (mvfderiv I g x v) := by
  rw [mvfderiv_comp_apply x hφ.mdifferentiableAt hg, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply, mvfderiv_apply_eq_mfderiv_apply]

/-- The chain rule for a scalar function on a manifold followed by a scalar function
differentiable at the relevant point: the derivative is scaled by `φ'(g x)`. -/
theorem mvfderiv_scalar_comp {g : M → 𝕜} {φ : 𝕜 → 𝕜} {x : M} (hg : MDiffAt g x)
    (hφ : DifferentiableAt 𝕜 φ (g x)) :
    mvfderiv I (φ ∘ g) x = deriv φ (g x) • mvfderiv I g x := by
  ext v
  rw [mvfderiv_comp_apply_of_differentiableAt hφ hg, hφ.hasDerivAt.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_apply]
  -- Both sides are products of two scalars, the first read in the tangent space of `𝕜`.
  exact mul_comm _ _

/-- The chain rule for a vector-valued function on a manifold followed by a continuous linear map,
evaluated on a tangent vector: the derivative of `L ∘ g` is `L` applied to the derivative of `g`. -/
theorem _root_.ContinuousLinearMap.mvfderiv_comp_apply (L : F →L[𝕜] F') {g : M → F} {x : M}
    (hg : MDiffAt g x) (v : TangentSpace I x) :
    mvfderiv I (L ∘ g) x v = L (mvfderiv I g x v) := by
  rw [mvfderiv_comp_apply_of_differentiableAt L.differentiableAt hg, ContinuousLinearMap.fderiv]

/-- The vector-valued derivative on a product is the sum of its partial derivatives. -/
theorem _root_.MDifferentiableAt.mvfderiv_prod_eq_add_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {f : M × M' → F'} {p : M × M'}
    (hf : MDifferentiableAt (I.prod I') 𝓘(𝕜, F') f p)
    (v : TangentSpace (I.prod I') p) :
    mvfderiv (I.prod I') f p v =
      mvfderiv I (fun y ↦ f (y, p.2)) p.1 v.1 +
        mvfderiv I' (fun y ↦ f (p.1, y)) p.2 v.2 := by
  rcases p with ⟨x, y⟩
  have h := congrArg (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f (x, y)))
    (mfderiv_prod_eq_add_apply hf (v := v))
  simpa only [mvfderiv, ContinuousLinearMap.coe_comp, Function.comp_def,
    ContinuousLinearEquiv.coe_coe, map_add] using h

/-- The derivative of a graph map, evaluated in the product tangent space. -/
theorem _root_.MDifferentiableAt.mfderiv_prodMk_id_apply {u : F → M} {x : F}
    (hu : MDifferentiableAt 𝓘(𝕜, F) I u x) (v : TangentSpace 𝓘(𝕜, F) x) :
    mfderiv 𝓘(𝕜, F) (𝓘(𝕜, F).prod I) (fun y ↦ (y, u y)) x v =
      (v, mfderiv 𝓘(𝕜, F) I u x v) := by
  have h := mfderiv_prodMk mdifferentiableAt_id hu
  rw [mfderiv_id] at h
  -- The product tangent fibre and the pair of factor tangent fibres share the product model.
  -- Evaluating the bundled derivative equation records this identification explicitly.
  exact congrArg (fun L ↦ L v) h

/-- The chain rule along the graph of a manifold-valued map on a normed space, splitting the
result into the derivative in the domain variable and the derivative in the manifold variable. -/
theorem fderiv_comp_graph_apply_of_mdifferentiableAt {u : F → M} {f : F → M → F'} {x : F}
    (hu : MDifferentiableAt 𝓘(𝕜, F) I u x)
    (hf : MDifferentiableAt (𝓘(𝕜, F).prod I) 𝓘(𝕜, F') (Function.uncurry f) (x, u x)) (v : F) :
    fderiv 𝕜 (fun y ↦ f y (u y)) x v =
      fderiv 𝕜 (fun y ↦ f y (u x)) x v +
        mvfderiv I (f x) (u x) (mfderiv 𝓘(𝕜, F) I u x v) := by
  have hc := mvfderiv_comp_apply x hf (mdifferentiableAt_id.prodMk hu)
    ((NormedSpace.fromTangentSpace x).symm v)
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hc
  simp only [id_eq] at hc
  rw [hu.mfderiv_prodMk_id_apply] at hc
  -- Supply the graph vector in the product tangent fibre explicitly, rather than asking
  -- rewriting to match the product model against the pair of tangent fibres.
  have hs := hf.mvfderiv_prod_eq_add_apply
    (v := ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm v,
      mfderiv 𝓘(𝕜, F) I u x ((NormedSpace.fromTangentSpace x).symm v)))
  have hc := hc.trans hs
  rw [mvfderiv_eq_fderiv] at hc
  simp only [ContinuousLinearMap.coe_comp, Function.comp_def,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hc
  simpa only [NormedSpace.fromTangentSpace_symm_apply,
    Function.uncurry_apply_pair, id_eq] using hc

/-- The derivative of a vector-valued function, read in the target space, commutes with
multiplication by a constant scalar acting continuously on the target, such as a complex scalar on
a complex normed space regarded as a real one. -/
theorem mvfderiv_const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] {g : M → F} {x : M} (hg : MDiffAt g x) (c : R) :
    mvfderiv I (fun y ↦ c • g y) x = c • mvfderiv I g x := by
  have hcg : MDiffAt (fun y ↦ c • g y) x :=
    ((c • ContinuousLinearMap.id 𝕜 F).mdifferentiableAt (x := g x)).comp x hg
  rw [hcg.mvfderiv, hg.mvfderiv]
  have hd := hg.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.comp_def, id] at hd ⊢
  exact fderivWithin_const_smul I.uniqueDiffWithinAt_image hd c

/-- A version of `TauCeti.mvfderiv_const_smul` without differentiability hypothesis, for a scalar in
the base field: the derivative of a vector-valued function, read in the target space, commutes
with multiplication by any constant. -/
@[simp]
theorem mvfderiv_const_smul_field (g : M → F) (x : M) (c : 𝕜) :
    mvfderiv I (c • g) x = c • mvfderiv I g x := by
  by_cases hg : MDiffAt g x
  · exact mvfderiv_const_smul hg c
  rcases eq_or_ne c 0 with rfl | hc
  · simp [mvfderiv_zero]
  -- Neither `g` nor `c • g` is differentiable at `x`, so both derivatives vanish.
  have hcg : ¬MDiffAt (c • g) x := fun hcg ↦
    hg (by simpa [smul_smul, inv_mul_cancel₀ hc] using hcg.const_smul c⁻¹)
  simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hg,
    mfderiv_zero_of_not_mdifferentiableAt hcg]

/-- The derivative of a vector-valued function, read in the target space, vanishes exactly when
its manifold derivative does. -/
theorem mvfderiv_eq_zero_iff {g : M → F} {x : M} :
    mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [mvfderiv, h]⟩
  ext u
  simpa [mvfderiv] using congrArg (fun L ↦ L u) h

/-- The derivative of a vector-valued function, read in the target space, is injective if and only
if its manifold derivative is. -/
theorem injective_mvfderiv_iff {g : M → F} {x : M} :
    Function.Injective (mvfderiv I g x) ↔ Function.Injective (mfderiv I 𝓘(𝕜, F) g x) := by
  refine ⟨fun h v w hvw ↦ h (by rwa [mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply]), fun h v w hvw ↦ h ?_⟩
  rwa [← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_apply_eq_mfderiv_apply]

/-- A vector-valued function whose derivative does not vanish on some tangent vector is
differentiable there. -/
theorem mdifferentiableAt_of_mvfderiv_apply_ne_zero {g : M → F} {x : M} {v : TangentSpace I x}
    (h : mvfderiv I g x v ≠ 0) : MDifferentiableAt I 𝓘(𝕜, F) g x := by
  by_contra hnd
  simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd] at h

/-- The derivative of `-g` vanishes at `x` if and only if the derivative of `g` does. -/
@[simp]
theorem mfderiv_neg_eq_zero_iff {g : M → F} {x : M} :
    mfderiv I 𝓘(𝕜, F) (-g) x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0 := by
  rw [← mvfderiv_eq_zero_iff, mvfderiv_neg, neg_eq_zero, mvfderiv_eq_zero_iff]

/-- The derivative of a component of a function into a finite product of normed spaces is the
component of its derivative, at a point where the function is differentiable. This is the
manifold version of `fderiv_apply`. -/
theorem mvfderiv_apply {ι : Type*} [Fintype ι] {F'' : ι → Type*}
    [∀ i, NormedAddCommGroup (F'' i)] [∀ i, NormedSpace 𝕜 (F'' i)] {Φ : M → (i : ι) → F'' i}
    {x : M} (hΦ : MDifferentiableAt I 𝓘(𝕜, (i : ι) → F'' i) Φ x) (i : ι) :
    mvfderiv I (fun y ↦ Φ y i) x = (ContinuousLinearMap.proj i).comp (mvfderiv I Φ x) := by
  ext v
  have := mvfderiv_comp_apply_of_differentiableAt
    (ContinuousLinearMap.proj (R := 𝕜) (φ := F'') i).differentiableAt hΦ v
  -- The component `fun y ↦ Φ y i` is `proj i ∘ Φ` by definition of the projection.
  rwa [ContinuousLinearMap.fderiv] at this

end TauCeti
