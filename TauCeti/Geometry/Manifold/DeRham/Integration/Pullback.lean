/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Integrals of pullbacks along maps that are not onto

Let `f : M → N` be a smooth proper map between oriented boundaryless manifolds of the same
dimension `n`, with `N` connected. If `f` misses a point `y`, then

`∫_M f^*φ = 0`

for every compactly supported smooth top form `φ` on `N`
(`TauCeti.integralTopForm_mpullback_eq_zero_of_not_surjective`). This is the vanishing of the
degree of a map that is not onto, stated without the degree: the image of the proper map `f` is
closed, so some neighbourhood of `y` misses it, and it supports a top form `θ` of integral one
(`TauCeti.exists_compactlySupportedClosedForms_integralTopForm_eq_one`). The form
`φ - (∫_N φ) θ` has integral zero, so on the connected manifold `N` it is the exterior derivative
of a compactly supported form
(`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`). Its pullback is then
a compactly supported exact form on `M`, whose integral vanishes by Stokes' theorem, while the
pullback of `θ` is zero because `θ` vanishes on the image of `f`.

Contrapositively, a proper map that pulls back some compactly supported top form to a form of
nonzero integral is onto (`TauCeti.surjective_of_integralTopForm_mpullback_ne_zero`). This is how
a positivity argument for the pulled back area form shows that a nonconstant pseudoholomorphic
map from a compact surface to a torus is onto.

## Main results

* `TauCeti.integralTopForm_mpullback_eq_zero_of_not_surjective`: the pullback of a compactly
  supported top form along a proper map that is not onto has integral zero.
* `TauCeti.surjective_of_integralTopForm_mpullback_ne_zero`: a proper map pulling back some
  compactly supported top form to one of nonzero integral is onto.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [BoundarylessManifold I' N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N] {n : ℕ}

/-- **Pullbacks along maps that are not onto integrate to zero.** Let `f : M → N` be a smooth
proper map between oriented boundaryless manifolds of the same dimension, with `N` connected.
If `f` is not onto, then the pullback of every compactly supported smooth top form on `N` has
integral zero over `M`. -/
theorem integralTopForm_mpullback_eq_zero_of_not_surjective
    (o : Manifold.Orientation I M (Fin n)) (o' : Manifold.Orientation I' N (Fin n)) {f : M → N}
    (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (hs : ¬Surjective f)
    {φ : SmoothForm I' N ℝ n} (hφ : φ ∈ compactlySupportedForms I' N n) :
    integralTopForm o (SmoothForm.mpullback f hf φ).1 = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y ∉ range f := by
    simpa only [Surjective, mem_range, not_forall] using hs
  -- A top form `θ` of integral one supported off the closed image of `f`.
  obtain ⟨θ, hθf, hθ⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o' y
    (hp.isClosedMap.isClosed_range.isOpen_compl.mem_nhds hy)
  have hθc := ((mem_compactlySupportedClosedForms I').mp θ.2).1
  -- `φ - (∫_N φ) θ` has integral zero, so it is exact with compact support.
  set c := integralTopForm o' φ.1
  have hex : φ + (-c) • θ.1 ∈ exactCompactlySupportedForms I' N n := by
    refine (mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o'
      (add_mem hφ (Submodule.smul_mem _ _ hθc))).2 ?_
    rw [Submodule.coe_add, Submodule.coe_smul, integralTopForm_add o'
      (φ.isSmoothForm.of_le (by simp)) ((θ.1.isSmoothForm.smul (-c)).of_le (by simp))
      ((mem_compactlySupportedForms I').mp hφ)
      (((mem_compactlySupportedForms I').mp hθc).of_isClosed_subset (isClosed_tsupport _)
        (RoughForm.tsupport_smul_subset _ _)),
      integralTopForm_smul, hθ]
    ring
  -- The pullback of `θ` vanishes, since `θ` vanishes on the image of `f`.
  have hθ0 : SmoothForm.mpullback f hf θ.1 = 0 := by
    refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    rw [SmoothForm.mpullback_apply, image_eq_zero_of_notMem_tsupport
      (fun hx ↦ hθf hx (mem_range_self x))]
    -- Both sides are the value of a zero alternating map.
    rfl
  have hpull : SmoothForm.mpullback f hf φ = SmoothForm.mpullback f hf (φ + (-c) • θ.1) := by
    rw [map_add, map_smul, hθ0, smul_zero, add_zero]
  rw [hpull]
  exact integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o
    (SmoothForm.mpullback_mem_exactCompactlySupportedForms f hf hp hex)

/-- **A map pulling back a form of nonzero integral is onto.** Let `f : M → N` be a smooth proper
map between oriented boundaryless manifolds of the same dimension, with `N` connected. If the
pullback of some compactly supported smooth top form on `N` has nonzero integral over `M`, then
`f` is onto. -/
theorem surjective_of_integralTopForm_mpullback_ne_zero
    (o : Manifold.Orientation I M (Fin n)) (o' : Manifold.Orientation I' N (Fin n)) {f : M → N}
    (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) {φ : SmoothForm I' N ℝ n}
    (hφ : φ ∈ compactlySupportedForms I' N n)
    (h : integralTopForm o (SmoothForm.mpullback f hf φ).1 ≠ 0) : Surjective f :=
  not_not.1 fun hs ↦ h (integralTopForm_mpullback_eq_zero_of_not_surjective o o' hf hp hs hφ)

end TauCeti
