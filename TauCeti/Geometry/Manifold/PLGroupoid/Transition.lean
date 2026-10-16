/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# PL chart transitions from ambient coordinate formulas

Charts on a polyhedron are often constructed by restricting maps defined on an ambient
coordinate space.  To prove compatibility of two such charts, it is enough to compose the
ambient formula for the inverse of the first chart with the ambient formula for the second.
This file performs the domain bookkeeping needed to turn that composition into membership in
the PL structure groupoid.

The source space and its ambient coordinate map are arbitrary.  In particular, the results apply
to barycentric coordinates on weak realizations of simplicial complexes, where the formulas are
usually established first on closed stars and then restricted to the open-star chart domains.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 1--2.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {A E H X : Type*}
  [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace X]
  {I : ModelWithCorners ℝ E H}

/-- Ambient formulas for the inverse of one chart and the forward direction of another
compose to a PL formula for their chart transition.

The inverse formula `g` is required on the model coordinates of the first chart's target.
The forward formula `f` may be established on the ambient coordinates of any set `D` containing
the second chart's source; this is the form used to restrict a closed-star formula to an open-star
chart.  No embedding or continuity hypothesis on the ambient coordinate map `q` is needed. -/
theorem isPLOn_chartTransition_of_coordinateFormulas
    (q : X → A) (c d : OpenPartialHomeomorph X H) (D : Set X)
    (g : E → A) (f : A → E)
    (hg : IsPLOn g (I.symm ⁻¹' c.target ∩ range I))
    (hf : IsPLOn f (q '' D)) (hd : d.source ⊆ D)
    (hg_eq : ∀ y ∈ c.target, g (I y) = q (c.symm y))
    (hf_eq : ∀ x ∈ d.source, f (q x) = I (d x)) :
    IsPLOn (I ∘ (c.symm.trans d) ∘ I.symm)
      (I.symm ⁻¹' (c.symm.trans d).source ∩ range I) := by
  let s := I.symm ⁻¹' (c.symm.trans d).source ∩ range I
  have hs : s ⊆ I.symm ⁻¹' c.target ∩ range I := by
    intro z hz
    have hsource := hz.1
    simp only [mfld_simps] at hsource
    refine ⟨?_, hz.2⟩
    exact hsource.1
  have hmap : MapsTo g s (q '' D) := by
    intro z hz
    have hzI : I (I.symm z) = z := I.right_inv hz.2
    have hsource := hz.1
    simp only [mfld_simps] at hsource
    refine ⟨c.symm (I.symm z), hd hsource.2, ?_⟩
    rw [← hg_eq (I.symm z) hsource.1, hzI]
  refine (hf.comp (hg.mono hs) hmap).congr ?_
  intro z hz
  have hzI : I (I.symm z) = z := I.right_inv hz.2
  have hsource := hz.1
  simp only [mfld_simps] at hsource
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
  have hg_z : g z = q (c.symm (I.symm z)) := by
    calc
      g z = g (I (I.symm z)) := congrArg g hzI.symm
      _ = q (c.symm (I.symm z)) := hg_eq (I.symm z) hsource.1
  rw [hg_z, hf_eq (c.symm (I.symm z)) hsource.2]

/-- Two charts whose forward and inverse maps have PL ambient coordinate formulas are compatible
for the PL structure groupoid.

This is symmetric in the two charts.  The first pair of formulas describes `c` on an ambient
set `C`, and the second pair describes `d` on `D`; only containment of the corresponding chart
sources is required.  The theorem applies the one-way transition result in both directions. -/
theorem chartTransition_mem_PLGroupoid_of_coordinateFormulas
    (q : X → A) (c d : OpenPartialHomeomorph X H)
    (C D : Set X) (hc : c.source ⊆ C) (hd : d.source ⊆ D)
    (cf : A → E) (cg : E → A) (df : A → E) (dg : E → A)
    (hcf : IsPLOn cf (q '' C))
    (hcg : IsPLOn cg (I.symm ⁻¹' c.target ∩ range I))
    (hdf : IsPLOn df (q '' D))
    (hdg : IsPLOn dg (I.symm ⁻¹' d.target ∩ range I))
    (hcf_eq : ∀ x ∈ c.source, cf (q x) = I (c x))
    (hcg_eq : ∀ y ∈ c.target, cg (I y) = q (c.symm y))
    (hdf_eq : ∀ x ∈ d.source, df (q x) = I (d x))
    (hdg_eq : ∀ y ∈ d.target, dg (I y) = q (d.symm y)) :
    c.symm.trans d ∈ PLGroupoid I := by
  rw [mem_PLGroupoid_iff]
  refine ⟨isPLOn_chartTransition_of_coordinateFormulas q c d D cg df hcg hdf hd hcg_eq hdf_eq,
    ?_⟩
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, ← OpenPartialHomeomorph.symm_source] using
      isPLOn_chartTransition_of_coordinateFormulas q d c C dg cf hdg hcf hc hdg_eq hcf_eq

/-- A charted space has a PL structure when every chart has forward and inverse PL formulas in a
common ambient coordinate space.

The forward formula may be proved on a set larger than the chart source.  Thus a chart assembled
from an open part of a compact polyhedron can reuse formulas established on the whole compact
piece.  Compatibility of every pair of charts then follows from
`chartTransition_mem_PLGroupoid_of_coordinateFormulas`. -/
theorem hasGroupoid_PLGroupoid_of_coordinateFormulas [ChartedSpace H X]
    (q : X → A)
    (h : ∀ c : OpenPartialHomeomorph X H, c ∈ atlas H X →
      ∃ C : Set X, ∃ f : A → E, ∃ g : E → A,
        c.source ⊆ C ∧
        IsPLOn f (q '' C) ∧
        IsPLOn g (I.symm ⁻¹' c.target ∩ range I) ∧
        (∀ x ∈ c.source, f (q x) = I (c x)) ∧
        ∀ y ∈ c.target, g (I y) = q (c.symm y)) :
    HasGroupoid X (PLGroupoid I) where
  compatible := by
    intro c d hc hd
    obtain ⟨C, cf, cg, hcC, hcf, hcg, hcf_eq, hcg_eq⟩ := h c hc
    obtain ⟨D, df, dg, hdD, hdf, hdg, hdf_eq, hdg_eq⟩ := h d hd
    exact chartTransition_mem_PLGroupoid_of_coordinateFormulas q c d C D hcC hdD
      cf cg df dg hcf hcg hdf hdg hcf_eq hcg_eq hdf_eq hdg_eq

end TauCeti
