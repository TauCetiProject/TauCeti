/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Covering

/-!
# Vanishing on spheres descends along coverings

Let `p : M' → M` be a surjective covering map which is a smooth local diffeomorphism, and let `φ`
be a two-form on `M`. If the pullback `p^* φ` vanishes on spheres (`TauCeti.VanishesOnSpheres`),
then so does `φ` (`TauCeti.VanishesOnSpheres.of_mpullback`).

The plane is simply connected, so a smooth map `u : ℝ × ℝ → M` of the square that is constant on
each vertical edge and agrees on the two horizontal edges lifts to a map `f : ℝ × ℝ → M'` with
`p ∘ f = u`, as smooth as `u` (`IsCoveringMap.exists_contMDiff_lift`), and the integral of `φ` over
`u` is that of `p^* φ` over `f`. The lift is again such a map: on each edge along which `u` is
constant, or on which `u` takes the same values as on the opposite edge, the lift is a lift of the
same map as the corresponding constant map or opposite edge, and two lifts through a covering map
that agree at one point of a connected set agree on all of it.

## Main results

* `TauCeti.VanishesOnSpheres.of_mpullback`: a form whose pullback along a covering local
  diffeomorphism vanishes on spheres vanishes on spheres.
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

/-- **Vanishing on spheres descends along coverings.** If `p` is a surjective covering map and a
smooth local diffeomorphism, and the pullback `p^* φ` vanishes on spheres, then so does `φ`: a
smooth map of the square factoring through a sphere lifts to such a map into `M'`, over which the
two integrals agree. -/
theorem VanishesOnSpheres.of_mpullback (hcover : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hp : IsLocalDiffeomorph I' I ∞ p) (h : VanishesOnSpheres (TauCeti.mpullback I' I p φ)) :
    VanishesOnSpheres φ := by
  rw [vanishesOnSpheres_iff] at h ⊢
  intro u hu h₀ h₁ hper
  obtain ⟨x', hx'⟩ := hsurj (u (0, 0))
  obtain ⟨f, hf, hpf, -⟩ := hcover.exists_contMDiff_lift hp hu (0, 0) hx'
  have hpf' (z : ℝ × ℝ) : p (f z) = u z := congrFun hpf z
  have hI : IsPreconnected (Icc (0 : ℝ) 1) := isPreconnected_Icc
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  -- The lift is constant along the two collapsed edges, since the map is.
  have hend (s : ℝ) (hs : ∀ t ∈ Icc (0 : ℝ) 1, u (s, t) = u (s, 0)) :
      ∀ t ∈ Icc (0 : ℝ) 1, f (s, t) = f (s, 0) :=
    hcover.eqOn_of_comp_eqOn hI (g₁ := fun t ↦ f (s, t)) (g₂ := fun _ ↦ f (s, 0))
      (hf.continuous.comp (Continuous.prodMk_right s)).continuousOn continuousOn_const
      (fun t ht ↦ by simp only [Function.comp_apply, hpf', hs t ht]) h0I rfl
  have hf₀ := hend 0 h₀
  -- It agrees on the two identified edges, since it does at their common start.
  have hfper : ∀ s ∈ Icc (0 : ℝ) 1, f (s, 1) = f (s, 0) :=
    hcover.eqOn_of_comp_eqOn hI (g₁ := fun s ↦ f (s, 1)) (g₂ := fun s ↦ f (s, 0))
      (hf.continuous.comp (Continuous.prodMk_left 1)).continuousOn
      (hf.continuous.comp (Continuous.prodMk_left 0)).continuousOn
      (fun s hs ↦ by simp only [Function.comp_apply, hpf', hper s hs]) h0I
      (hf₀ 1 (right_mem_Icc.mpr zero_le_one))
  have := h f hf hf₀ (hend 1 h₁) hfper
  rwa [rectangleIntegral_mpullback φ (fun z _ ↦ (hp.contMDiff.mdifferentiable (by simp)) _)
    (fun z _ ↦ hf.mdifferentiable (by simp) z), hpf] at this

end TauCeti
