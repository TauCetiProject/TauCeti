/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth linear multipliers

A smooth family `A x : F →L[𝕜] G` acts linearly on smooth vector-valued maps by
`f x ↦ A x (f x)`. This action does not enlarge closed support, and it preserves
closed support when every `A x` is injective.

Smoothness uses Mathlib's `ContMDiff.clm_apply`. Compact chart seminorm bounds
for this action are proved in `ContMDiffMap.Chart.CLMApply`.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

/-- Pointwise application of a smooth family of continuous linear maps, linear in
its vector-valued argument. -/
def clmApplyLinearMap (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯) :
    C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜] C^n⟮I, M; 𝓘(𝕜, G), G⟯ where
  toFun f := ⟨fun x ↦ A x (f x), A.contMDiff.clm_apply f.contMDiff⟩
  map_add' f g := by
    apply ContMDiffMap.coe_injective
    simp only [coeFn_mk, coe_add, Pi.add_apply]
    funext x
    exact map_add (A x) (f x) (g x)
  map_smul' c f := by
    apply ContMDiffMap.coe_injective
    simp only [coeFn_mk, coe_smul, Pi.smul_apply, RingHom.id_apply]
    funext x
    exact map_smul (A x) c (f x)

@[simp]
theorem clmApplyLinearMap_apply
    (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) :
    clmApplyLinearMap A f x = A x (f x) := (rfl)

/-- Multiplication by a smooth linear family does not enlarge closed support. -/
theorem tsupport_clmApplyLinearMap_subset
    (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    tsupport (clmApplyLinearMap A f) ⊆ tsupport f := by
  apply closure_mono
  exact Function.support_subset_iff'.mpr fun x hx ↦ by
    simp [Function.notMem_support.mp hx]

/-- An injective smooth linear family preserves exact closed supports. -/
theorem tsupport_clmApplyLinearMap
    (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
    (hA : ∀ x, Function.Injective (A x)) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    tsupport (clmApplyLinearMap A f) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp only [Function.mem_support, clmApplyLinearMap_apply]
  exact not_congr (map_eq_zero_iff (A x) (hA x))

end ContMDiffMap
