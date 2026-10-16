/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Faces
public import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Intersection

/-!
# Regular points of Dirichlet faces

Equality faces indexed by distinct orbit centres meet in at most one point. In the interior of
the parameter interval of a face, every constraint from a different orbit centre is strict.
For a properly discontinuous isometric group action, the domain and its neighbour across that
face therefore cover a neighbourhood of each such point.

These results distinguish genuine sides from singleton equality faces and provide the local
two-tile structure needed to assemble a Dirichlet polygon. They apply to bounded sides, rays,
and complete geodesic sides without assuming finite area or global finite-sidedness. Elements
fixing the centre are excluded, and different elements with the same orbit centre are allowed.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open UpperHalfPlane Set
open scoped Pointwise

namespace TauCeti.UpperHalfPlane

variable {G : Type*}

section SMul

variable [SMul G ℍ]

/-- Faces with distinct orbit centres, neither equal to the initial centre, intersect in at
most one point. No proper discontinuity or group law is required. -/
theorem subsingleton_inter_dirichletFace {p : ℍ} {g h : G}
    (hg : g • p ≠ p) (hh : h • p ≠ p) (hgh : g • p ≠ h • p) :
    (dirichletFace p g ∩ dirichletFace p h).Subsingleton := by
  rw [dirichletFace_eq_inter_range_geodesicLine hg,
    dirichletFace_eq_inter_range_geodesicLine hh]
  intro z hz w hw
  exact subsingleton_inter_range_geodesicLine_perpBisector hg.symm hh.symm hgh
    ⟨hz.1.2, hz.2.2⟩ ⟨hw.1.2, hw.2.2⟩

/-- Inside a face's parameter interval, every constraint from a different orbit centre is
strict. Singleton faces have no such interior parameter. -/
theorem dist_lt_of_mem_dirichletFace_of_lt {p : ℍ} {g h : G} {s u t : ℝ}
    (hg : g • p ≠ p) (hh : h • p ≠ p) (hgh : g • p ≠ h • p)
    (hsu : s < u) (hut : u < t)
    (hs : geodesicLine (perpBisector p (g • p)) s ∈ dirichletFace p g)
    (ht : geodesicLine (perpBisector p (g • p)) t ∈ dirichletFace p g) :
    dist (geodesicLine (perpBisector p (g • p)) u) p <
      dist (geodesicLine (perpBisector p (g • p)) u) (h • p) := by
  have hne : range (geodesicLine (perpBisector p (g • p))) ≠
      range (geodesicLine (perpBisector p (h • p))) := by
    intro heq
    have hsub := subsingleton_inter_range_geodesicLine_perpBisector hg.symm hh.symm hgh
    have hmem (v : ℝ) : geodesicLine (perpBisector p (g • p)) v ∈
        range (geodesicLine (perpBisector p (g • p))) ∩
          range (geodesicLine (perpBisector p (h • p))) :=
      ⟨mem_range_self v, heq ▸ mem_range_self v⟩
    exact zero_ne_one (geodesicLine_injective _ (hsub (hmem 0) (hmem 1)))
  apply (mem_leftHalfPlane_perpBisector_iff hh.symm _).mp
  exact geodesicLine_mem_leftHalfPlane_of_mem_closure hsu hut
    ((mem_closure_leftHalfPlane_perpBisector_iff hh.symm _).mpr
      (mem_dirichletDomain.mp (mem_dirichletFace.mp hs).1 h))
    ((mem_closure_leftHalfPlane_perpBisector_iff hh.symm _).mpr
      (mem_dirichletDomain.mp (mem_dirichletFace.mp ht).1 h)) hne

end SMul

section Group

variable [Group G] [MulAction G ℍ] [IsIsometricSMul G ℍ] [ProperlyDiscontinuousSMul G ℍ]

/-- The domain and the adjacent translate cover a neighbourhood of every interior parameter
point of a nontrivial equality face. This includes unbounded faces and self-paired sides. -/
theorem mem_interior_union_smul_dirichletDomain_of_mem_dirichletFace_of_lt
    {p : ℍ} {g : G} {s u t : ℝ} (hg : g • p ≠ p) (hsu : s < u) (hut : u < t)
    (hs : geodesicLine (perpBisector p (g • p)) s ∈ dirichletFace p g)
    (ht : geodesicLine (perpBisector p (g • p)) t ∈ dirichletFace p g) :
    geodesicLine (perpBisector p (g • p)) u ∈
      interior (dirichletDomain G p ∪ g • dirichletDomain G p) := by
  apply TauCeti.mem_interior_union_smul_dirichletDomain g
  intro h hh hhg
  exact dist_lt_of_mem_dirichletFace_of_lt hg hh hhg.symm hsu hut hs ht

end Group

end TauCeti.UpperHalfPlane
