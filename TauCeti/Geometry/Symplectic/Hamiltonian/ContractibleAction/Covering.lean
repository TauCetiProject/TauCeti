/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Covering
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic

/-!
# Weak exactness descends along coverings

Let `p : M' → M` be a surjective covering map which is a `C²` local diffeomorphism, and let `φ`
be a two-form on `M`. If the pullback `p^* φ` is weakly exact (`TauCeti.IsWeaklyExact`), the
vanishing over every `C²` cylinder between two constant loops, then so is `φ`
(`TauCeti.IsWeaklyExact.of_mpullback`). The companion statement for the other formulation of the
area half of symplectic asphericity, vanishing on spheres, is
`TauCeti.VanishesOnSpheres.of_mpullback`.

The plane is simply connected, so a cylinder `w : ℝ × ℝ → M` lifts to a map `f : ℝ × ℝ → M'` with
`p ∘ f = w`, as smooth as `w` (`IsCoveringMap.exists_contMDiff_lift`), and the integral of `φ` over
`w` is that of `p^* φ` over `f`. The lift is again a cylinder between two constant loops: along
each end it is a lift of a constant map, and it is periodic since its translate is a lift of the
same map that agrees with it at one point, and two lifts through a covering map that agree at one
point of a connected space agree everywhere.

The main application is to a manifold `M` whose universal cover, or some covering space, carries a
primitive of the pulled back form, such as a torus with an invariant form, covered by a vector space
on which every constant two-form is exact.

## Main results

* `TauCeti.IsWeaklyExact.of_mpullback`: a form whose pullback along a covering local
  diffeomorphism is weakly exact is weakly exact.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (symplectically aspherical manifolds).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : M' → M} {φ : RoughForm I M F 2}

/-- **Weak exactness descends along coverings.** If `p` is a surjective covering map and a `C²`
local diffeomorphism, and the pullback `p^* φ` is weakly exact, then so is `φ`: a sphere in `M`,
a cylinder between two constant loops, lifts to a sphere in `M'` over which the two integrals
agree. -/
theorem IsWeaklyExact.of_mpullback (hcover : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hp : IsLocalDiffeomorph I' I 2 p) (h : IsWeaklyExact (TauCeti.mpullback I' I p φ)) :
    IsWeaklyExact φ := by
  rw [isWeaklyExact_iff] at h ⊢
  intro w x y hw
  obtain ⟨x', hx'⟩ := hsurj (w (0, 0))
  obtain ⟨f, hf, hpf, -⟩ := hcover.exists_contMDiff_lift hp hw.contMDiff (0, 0) hx'
  have hpf' (z : ℝ × ℝ) : p (f z) = w z := congrFun hpf z
  -- The lift is constant along each end of the cylinder, since the cylinder is.
  have hend (s : ℝ) (hs : ∀ t, w (s, t) = w (s, 0)) (t : ℝ) : f (s, t) = f (s, 0) :=
    congrFun (hcover.eq_of_comp_eq (A := ℝ) (g₁ := fun t ↦ f (s, t)) (g₂ := fun _ ↦ f (s, 0))
      (hf.continuous.comp (Continuous.prodMk_right s)) continuous_const
      (funext fun t ↦ by simp only [Function.comp_apply, hpf', hs]) 0 rfl) t
  have h₀ := hend 0 fun t ↦ by rw [hw.apply_zero, hw.apply_zero]
  have h₁ := hend 1 fun t ↦ by rw [hw.apply_one, hw.apply_one]
  -- The lift is periodic, since the cylinder is and the lift is periodic at `(0, 0)`.
  have hper : (fun z : ℝ × ℝ ↦ f (z.1, z.2 + 1)) = f :=
    hcover.eq_of_comp_eq (hf.continuous.comp (by fun_prop)) hf.continuous
      (funext fun z ↦ by simp only [Function.comp_apply, hpf', hw.apply_add_one]) (0, 0)
      (by simpa using h₀ 1)
  have hlift : IsLoopCylinder I' f (fun _ ↦ f (0, 0)) (fun _ ↦ f (1, 0)) :=
    { contMDiff := hf
      apply_add_one := fun z ↦ congrFun hper z
      apply_zero := h₀
      apply_one := h₁ }
  have := h hlift
  rwa [rectangleIntegral_mpullback φ (fun z _ ↦ (hp.contMDiff.mdifferentiable two_ne_zero) _)
    (fun z _ ↦ hf.mdifferentiable two_ne_zero z), hpf] at this

end TauCeti
