/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MeanZeroPrimitive
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.ConnectedComponent
import TauCeti.Geometry.Manifold.DifferentialForm.ParametricPrimitive

/-!
# Mean-zero primitives of smooth families of exact one-forms

Let `M` be a compact manifold with a finite measure `μ` charging every nonempty open set, such as
the Liouville measure of a symplectic form, and let `S = TauCeti.meanZeroPrimitive I μ` send an
exact one-form on `M` to its primitive with mean zero on every connected component. This file
shows that `S` depends smoothly on parameters: if `α_p`, for `p` in a boundaryless manifold `P`, is
a family of exact one-forms on `M` which is jointly `C^r` in the point and the parameter, that is,
`α_p` is the slice `v ↦ B_(x, p)(v, 0)` of a `C^r` one-form `B` on `M × P`, then

`(x, p) ↦ (S α_p)(x)`

is `C^r` on `M × P` (`TauCeti.contMDiff_meanZeroPrimitive`). Unlike an arbitrary choice of
primitives, which need not even be continuous in `p`, the mean-zero primitives are determined by
the forms, so this is a canonical jointly smooth family of primitives.

The proof combines two smooth constructions. The smooth selection of primitives
(`TauCeti.exists_contMDiff_eventuallyEq_sub`) gives a `C^r` function `F` on `M × P` which on each
slice differs from `S α_p` by a locally constant function. Subtracting from `F` its average over
the connected component of each point, which is `C^r` in the point and the parameter
(`ContMDiff.setAverage_connectedComponent`), gives a `C^r` function each of whose slices is still a
primitive of `α_p`, now with integral zero over every component. By the characterization of the
mean-zero primitive (`TauCeti.eq_meanZeroPrimitive_iff`) its slices are the `S α_p`.

Normalizing primitives in this way gives jointly smooth, componentwise normalized Hamiltonians
for smooth families of exact symplectic vector fields.

## Main results

* `TauCeti.contMDiff_meanZeroPrimitive`: the mean-zero primitives of a `C^r` family of exact
  one-forms form a `C^r` function of the point and the parameter.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 10.2 (Hamiltonian
  functions normalized to have mean zero).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [OpensMeasurableSpace M] [CompactSpace M]
  [T2Space M] {μ : Measure M} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {G HP : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ G HP} [IP.Boundaryless] {P : Type*} [TopologicalSpace P]
  [ChartedSpace HP P] [IsManifold IP ∞ P]

/-- **Mean-zero primitives depend smoothly on parameters.** Let `α_p`, for `p` in a boundaryless
manifold `P`, be exact one-forms on a compact manifold `M` which are the slices
`v ↦ B_(x, p)(v, 0)` of a `C^r` one-form `B` on `M × P`. Then their primitives with mean zero on
every connected component of `M` form a `C^r` function `(x, p) ↦ (S α_p)(x)` on `M × P`. -/
theorem contMDiff_meanZeroPrimitive {r : ℕ∞} {B : RoughForm (I.prod IP) (M × P) ℝ 1}
    (hB : IsSmoothForm (I.prod IP) r B) {α : P → exactForms I M 1}
    (hα : ∀ (p : P) (x : M) (v : E),
      ((α p : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) x ![v] = B (x, p) ![(v, (0 : G))]) :
    ContMDiff (I.prod IP) 𝓘(ℝ) r fun z : M × P ↦ meanZeroPrimitive I μ (α z.2) z.1 := by
  have : IsManifold I r M := .of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold IP r P := .of_le (n := ∞) (by exact_mod_cast le_top)
  -- The mean-zero primitives are primitives of the slices of `B`.
  have hS (p : P) : MDifferentiable I 𝓘(ℝ) (meanZeroPrimitive I μ (α p)) :=
    (meanZeroPrimitive I μ (α p)).contMDiff.mdifferentiable (by simp)
  have hSB (p : P) (x : M) (v : E) :
      mvfderiv I (meanZeroPrimitive I μ (α p)) x v = B (x, p) ![(v, (0 : G))] := by
    rw [← hα, ← mextDeriv_ofFunction_meanZeroPrimitive (μ := μ) (α p)]
    exact (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans (mextDeriv_ofFunction_apply _ x v).symm
  -- A jointly smooth family differing from them by locally constant functions. Its slices are
  -- therefore primitives too, and subtracting their componentwise averages normalizes them.
  obtain ⟨F, hF, hFS⟩ := exists_contMDiff_eventuallyEq_sub hB hS hSB
  have heq : (fun z : M × P ↦ meanZeroPrimitive I μ (α z.2) z.1) =
      fun z ↦ F z - ⨍ y in connectedComponent z.1, F (y, z.2) ∂μ := by
    funext ⟨x, p⟩
    have hFd : MDifferentiable I 𝓘(ℝ) fun y ↦ F (y, p) := fun y ↦ by
      obtain ⟨c, hc⟩ := hFS p y
      exact ((hS p y).sub mdifferentiableAt_const).congr_of_eventuallyEq hc
    refine meanZeroPrimitive_apply_eq_sub_setAverage hFd (funext fun y ↦ ?_) x
    obtain ⟨c, hc⟩ := hFS p y
    rw [mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (g := meanZeroPrimitive I μ (α p))
      (c := -c) (hc.mono fun _ h ↦ h.trans (sub_eq_add_neg _ _)),
      mextDeriv_ofFunction_meanZeroPrimitive]
  rw [heq]
  exact hF.sub hF.setAverage_connectedComponent

end TauCeti
