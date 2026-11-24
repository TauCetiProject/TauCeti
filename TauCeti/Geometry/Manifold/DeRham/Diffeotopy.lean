/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance

/-!
# Diffeotopies act trivially on de Rham cohomology

Let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of a manifold `M`, possibly with boundary or
corners. Its motion `(x, t) ↦ φ_t x` on the cylinder `M × [0, 1]`
(`TauCeti.Diffeotopy.cylinderMap`) is a smooth homotopy from the identity to the final
diffeomorphism `φ₁`, so by homotopy invariance (`TauCeti.deRhamCohomology.map_eq_of_homotopy`)
pullback along `φ₁` is the identity of `H^k_dR(M)` (`TauCeti.deRhamCohomology.map_final`). On
closed forms this says that `φ₁^* β - β` is exact for every closed form `β`
(`TauCeti.Diffeotopy.mpullback_final_sub_mem_exactForms`).

This is the triviality of the action of diffeomorphisms isotopic to the identity on de Rham
cohomology. It lets such diffeomorphisms be ignored when computing de Rham classes, for instance
the classes of the contractions `ι_X σ` of a two-form with vector fields pushed forward by them.

## Main results

* `TauCeti.deRhamCohomology.map_final`: the final diffeomorphism of a diffeotopy induces the
  identity on de Rham cohomology.
* `TauCeti.Diffeotopy.mpullback_final_sub_mem_exactForms`: for every closed form `β`, the
  difference `φ₁^* β - β` is exact.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82, 1982,
  Corollary 4.1.2 (homotopy invariance of de Rham cohomology).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Diffeotopies act trivially on de Rham cohomology.** The final diffeomorphism `φ₁` of a
smooth diffeotopy is smoothly homotopic to the identity through the motion `(x, t) ↦ φ_t x`, so
pullback along `φ₁` is the identity on `H^k_dR(M)`. -/
@[simp]
theorem deRhamCohomology.map_final (Φ : Diffeotopy I ∞ M) (k : ℕ) :
    deRhamCohomology.map Φ.final Φ.final.contMDiff k = LinearMap.id := by
  rw [← deRhamCohomology.map_id (I := I) (M := M) k]
  exact (deRhamCohomology.map_eq_of_homotopy contMDiff_id Φ.final.contMDiff
    Φ.contMDiff_cylinderMap (fun x ↦ congrFun Φ.cylinderMap_comp_zero x)
    (fun x ↦ congrFun Φ.cylinderMap_comp_one x) k).symm

/-- **The final map of a diffeotopy changes closed forms by exact forms.** For every closed form
`β`, the difference `φ₁^* β - β` between its pullback along the final diffeomorphism of a smooth
diffeotopy and `β` itself is exact. -/
theorem Diffeotopy.mpullback_final_sub_mem_exactForms (Φ : Diffeotopy I ∞ M) {k : ℕ}
    (β : closedForms I M k) :
    SmoothForm.mpullback Φ.final Φ.final.contMDiff β.val - β.val ∈ exactForms I M k := by
  have h := LinearMap.congr_fun (deRhamCohomology.map_final Φ k) (deRhamCohomology.mk I k β)
  rw [deRhamCohomology.map_mk, LinearMap.id_apply, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff] at h
  simpa only [Submodule.coe_sub, closedForms.coe_mpullback] using h

end TauCeti
