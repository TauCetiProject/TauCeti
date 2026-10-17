/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocallyConnectedBoundary

import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Boundary prevertices from an inverted coordinate

For an unbounded domain, a Riemann map need not extend as a finite-valued function at every
boundary parameter.  Inversion about an exterior point replaces it by a bounded holomorphic map
`g`, which can extend continuously to the real axis even when the original map `f` escapes to
infinity there.

This file reads the boundary behaviour of `f` directly from `g`.  A nonzero boundary value of `g`
gives a finite limit of `f`, while a zero is exactly a parameter at which `f` tends to infinity.
Consequently, distinct finite points of the original frontier have distinct real prevertices,
even when several accesses to infinity prevent the boundary extension from being globally
injective.  This is the boundary extraction needed before local side and end geometry can be
applied to polygonal domains with several vertices at infinity.

## Main results

* `TauCeti.tendsto_nhds_of_inverted_boundary_ne_zero`: a nonzero inverted boundary value gives
  the corresponding finite boundary limit.
* `TauCeti.tendsto_cobounded_iff_inverted_boundary_eq_zero`: zeros of the inverted coordinate
  are exactly the boundary parameters at which the original map escapes to infinity.
* `TauCeti.exists_injective_prevertices_of_inverted_boundary`: any injective family of finite
  frontier points has an injective family of real prevertices with the expected limits.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ}

/-- If the continuous inverted coordinate `g = (f - q)⁻¹` has a nonzero value at a real
boundary parameter, then `f` tends there to the corresponding finite point `q + (g x)⁻¹`. -/
theorem tendsto_nhds_of_inverted_boundary_ne_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) (hx : g x ≠ 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (q + (g x)⁻¹)) := by
  have hH : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
    ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hg : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (g x)) :=
    (hgc.mono hH).tendsto
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    (tendsto_const_nhds.add (hg.inv₀ hx))
  rw [hgf hz]
  simp

/-- If the continuous inverted coordinate `g = (f - q)⁻¹` vanishes at a real boundary
parameter and is nonzero in the upper half-plane, then `f` tends to infinity at that parameter. -/
theorem tendsto_cobounded_of_inverted_boundary_eq_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hx : g x = 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (cobounded ℂ) := by
  have hH : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
    ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hg : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 0) := by
    simpa only [hx] using (hgc.mono hH).tendsto
  have hg₀ : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hg, eventually_nhdsWithin_of_forall fun z hz => hgne z hz⟩
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg₀))
  simp only [Function.comp_apply]
  rw [hgf hz]
  simp

/-- A real boundary parameter is a prevertex at infinity exactly when the continuous inverted
coordinate vanishes there. -/
theorem tendsto_cobounded_iff_inverted_boundary_eq_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (cobounded ℂ) ↔ g x = 0 := by
  constructor
  · intro hf
    by_contra hx
    let _ : (𝓝[upperHalfPlaneSet] (x : ℂ)).NeBot :=
      Real.nhdsWithin_upperHalfPlaneSet_neBot x
    exact (tendsto_nhds_of_inverted_boundary_ne_zero hgc hgf hx).not_tendsto
      (Metric.disjoint_nhds_cobounded _) hf
  · exact tendsto_cobounded_of_inverted_boundary_eq_zero hgc hgf hgne

/-- Distinct finite frontier points of an unbounded domain have distinct real prevertices under a
continuous inverted boundary coordinate.  At each chosen prevertex, the original map tends to the
prescribed frontier point.

The equality `hgr` is the boundary-surjectivity conclusion supplied by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`. -/
theorem exists_injective_prevertices_of_inverted_boundary {U : Set ℂ} {q : ℂ}
    (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgr : insert 0 (g '' {z : ℂ | z.im = 0}) =
      frontier ((fun z : ℂ => (z - q)⁻¹) '' U))
    { ι : Type*} {v : ι → ℂ} (hv : Injective v) (hvU : ∀ i, v i ∈ frontier U) :
    ∃ a : ι → ℝ, Injective a ∧ ∀ i,
      g (a i) = (v i - q)⁻¹ ∧
        Tendsto f (𝓝[upperHalfPlaneSet] ((a i : ℝ) : ℂ)) (𝓝 (v i)) := by
  have hvq (i : ι) : v i - q ≠ 0 := fun hi =>
    hq (sub_eq_zero.mp hi ▸ frontier_subset_closure (hvU i))
  have htarget (i : ι) : (v i - q)⁻¹ ∈ g '' {z : ℂ | z.im = 0} := by
    have hmem : (v i - q)⁻¹ ∈
        frontier ((fun z : ℂ => (z - q)⁻¹) '' U) := by
      rw [frontier_image_inv_sub hUo hq hUb]
      exact mem_insert_of_mem _ ⟨v i, hvU i, rfl⟩
    rw [← hgr, mem_insert_iff] at hmem
    exact hmem.resolve_left (inv_ne_zero (hvq i))
  choose z hzR hzg using htarget
  let a : ι → ℝ := fun i => (z i).re
  have hza (i : ι) : ((a i : ℝ) : ℂ) = z i := by
    apply Complex.ext
    · rfl
    · simpa [a] using (hzR i).symm
  have hga (i : ι) : g (a i) = (v i - q)⁻¹ := by
    rw [hza]
    exact hzg i
  refine ⟨a, fun i j hij => hv ?_, fun i => ⟨hga i, ?_⟩⟩
  · have := congrArg g (congrArg ((↑) : ℝ → ℂ) hij)
    rw [hga i, hga j, inv_inj, sub_left_inj] at this
    exact this
  · have hne : g (a i) ≠ 0 := hga i ▸ inv_ne_zero (hvq i)
    simpa [hga i, add_comm] using
      tendsto_nhds_of_inverted_boundary_ne_zero (hgc _ (by simp)) hgf hne

end TauCeti
