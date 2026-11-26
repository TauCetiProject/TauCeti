/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Naturality of time-dependent flows under related maps

Let `X` and `Y` be time-dependent vector fields on manifolds `M` and `M'`, and let `f : M → M'`
be a differentiable map relating them at all times: `df_x (X u x) = Y u (f x)`. Then `f` carries
the curves of the time-dependent flow of `X` to solutions of the equation of `Y`, and by uniqueness
of solutions it intertwines the two flows,

`f (φ^X_{s,t} x) = φ^Y_{s,t} (f x)`

(`MDifferentiable.apply_timeDependentFlowOf`), wherever the flow of `X` is defined. No
completeness is needed. As for autonomous flows
(`TauCeti.Geometry.Manifold.Flow.Related`), no inverse of `f` is needed.

For instance, when a group acts on `M` by maps `y ↦ g • y` whose differentials carry `X u` to
itself, every time map of the flow of `X` commutes with the action. This is how a Moser isotopy
built from invariant data is shown to be equivariant.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 9.6 (naturality of integral curves) and Theorem 9.48 (time-dependent flows).
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace MDifferentiable

open TauCeti

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M']
  {X : ℝ → (x : M) → TangentSpace I x} {Y : ℝ → (y : M') → TangentSpace I' y} {f : M → M'}
  {s t : ℝ} {x : M}

/-- **Time-dependent flows of related fields are intertwined.** Let `f` be a differentiable map
whose differential carries the field `X u` to the field `Y u` at every time `u`, with `X` and `Y`
jointly `C¹`. Wherever the time-dependent flow of `X` from time `s` to time `t` is defined at `x`,
`f` carries it to that of `Y`: `f (φ^X_{s,t} x) = φ^Y_{s,t} (f x)`. -/
theorem apply_timeDependentFlowOf (hf : MDifferentiable I I' f)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod I') I'.tangent 1
      (fun p : ℝ × M' ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I' M')))
    (hXY : ∀ u x, mfderiv I I' f x (X u x) = Y u (f x))
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    f (timeDependentFlowOf X s t x) = timeDependentFlowOf Y s t (f x) := by
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  -- On a common interval of existence, the image under `f` of the curve of the flow of `X` solves
  -- the equation of `Y`.
  have hγ (u : ℝ) (hu : u ∈ Ioo a b) :
      HasMFDerivAt 𝓘(ℝ, ℝ) I' (fun u ↦ f (timeDependentFlowOf X s u x)) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y u (f (timeDependentFlowOf X s u x)))) := by
    have hder : (mfderiv I I' f (timeDependentFlowOf X s u x)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (timeDependentFlowOf X s u x))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (Y u (f (timeDependentFlowOf X s u x))) := by
      rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
        ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
        ContinuousLinearMap.comp_toSpanSingleton, hXY]
    rw [← hder]
    exact (hf _).hasMFDerivAt.comp u (hasMFDerivAt_timeDependentFlowOf hX (hab u hu))
  have h' := timeDependentFlowOf_eq_of_hasMFDerivAt hY hγ hs ht
  rwa [timeDependentFlowOf_self, eq_comm] at h'

end MDifferentiable
