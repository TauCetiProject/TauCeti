/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator

/-!
# Homotopy invariance of de Rham cohomology

Smoothly homotopic maps induce the same map on de Rham cohomology
(`TauCeti.deRhamCohomology.map_eq_of_homotopy`). A homotopy from `f` to `g` is a smooth map
`F : M × [0, 1] → M'` with `F (x, 0) = f x` and `F (x, 1) = g x`, where the cylinder
`M × [0, 1]` is a manifold over `I.prod (𝓡∂ 1)`. The source `M` may have boundary or corners.

Since `f` and `g` factor through `F` along the slice inclusions `x ↦ (x, 0)` and `x ↦ (x, 1)`,
functoriality reduces the statement to the cylinder itself: the two slice inclusions induce the
same map on cohomology (`TauCeti.deRhamCohomology.map_prodMk_left_zero_eq_map_prodMk_left_one`).
In positive degree this is the cochain-homotopy identity of the homotopy operator: for a closed
form `φ` on `M × [0, 1]`, `ι₁^* φ - ι₀^* φ = d (h φ)` (`TauCeti.mextDeriv_homotopyOperator`),
and `h φ` is again smooth. In degree zero a closed form is a locally constant function, which is
constant along each segment `{x} × [0, 1]`.

## Main declarations

* `TauCeti.deRhamCohomology.map_prodMk_left_zero_eq_map_prodMk_left_one`: the slice inclusions
  `x ↦ (x, 0)` and `x ↦ (x, 1)` of `M` into `M × [0, 1]` induce the same map on cohomology.
* `TauCeti.deRhamCohomology.map_eq_of_homotopy`: smoothly homotopic maps induce the same map on
  de Rham cohomology.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace deRhamCohomology

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']

/-- The slice inclusions `x ↦ (x, 0)` and `x ↦ (x, 1)` of a smooth manifold `M`, possibly with
boundary or corners, into the cylinder `M × [0, 1]` induce the same map on de Rham cohomology. -/
theorem map_prodMk_left_zero_eq_map_prodMk_left_one (k : ℕ) :
    map (I' := I.prod (𝓡∂ 1)) (fun x : M ↦ (x, (0 : Icc (0 : ℝ) 1)))
        (contMDiff_id.prodMk contMDiff_const) k =
      map (I' := I.prod (𝓡∂ 1)) (fun x : M ↦ (x, (1 : Icc (0 : ℝ) 1)))
        (contMDiff_id.prodMk contMDiff_const) k := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective (I.prod (𝓡∂ 1)) k c
  rw [map_mk, map_mk]
  cases k with
  | zero =>
    -- A closed `0`-form is locally constant, hence constant along `{x} × [0, 1]`.
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun x ↦ ?_))
    have hφ := ((mem_closedForms_zero_iff _ φ.1).mp φ.2).comp_continuous
      (Continuous.prodMk_right x : Continuous fun t : Icc (0 : ℝ) 1 ↦ (x, t))
    ext v
    simp only [closedForms.coe_mpullback, SmoothForm.mpullback_apply]
    calc _ = φ.1.1 (x, 0) 0 := congrArg _ (Subsingleton.elim _ _)
      _ = φ.1.1 (x, 1) 0 := hφ.apply_eq_of_preconnectedSpace 0 1
      _ = _ := congrArg _ (Subsingleton.elim _ _)
  | succ k =>
    -- `ι₁^* φ - ι₀^* φ` is the exterior derivative of the smooth form `h φ`. Smoothness of
    -- `h φ` is `IsSmoothForm.homotopyOperator` at `r = ⊤`, stated for a `C^(⊤ + 1)` manifold.
    have : IsManifold I ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
    rw [eq_comm, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff, exactForms_succ,
      SmoothForm.mextDerivLinearMap_real]
    refine ⟨⟨homotopyOperator φ.1.1,
      (IsSmoothForm.homotopyOperator φ.1.isSmoothForm).mem_smoothForms⟩, ?_⟩
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [mextDerivₗ_apply, mextDeriv_homotopyOperator (φ.1.isSmoothForm.of_le (by simp))
      ((mem_closedForms _ φ.1).mp φ.2)]
    simp

/-- **Homotopy invariance of de Rham cohomology.** If `F : M × [0, 1] → M'` is a smooth
homotopy from `f` to `g`, then `f` and `g` induce the same map on de Rham cohomology. The source
`M` may have boundary or corners. -/
theorem map_eq_of_homotopy {f g : M → M'} (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    {F : M × Icc (0 : ℝ) 1 → M'} (hF : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = g x) (k : ℕ) :
    map f hf k = map g hg k := by
  obtain rfl : F ∘ (fun x ↦ (x, 0)) = f := funext h₀
  obtain rfl : F ∘ (fun x ↦ (x, 1)) = g := funext h₁
  rw [map_comp (fun x ↦ (x, 0)) F (contMDiff_id.prodMk contMDiff_const) hF,
    map_comp (fun x ↦ (x, 1)) F (contMDiff_id.prodMk contMDiff_const) hF,
    map_prodMk_left_zero_eq_map_prodMk_left_one]

end deRhamCohomology

end TauCeti
