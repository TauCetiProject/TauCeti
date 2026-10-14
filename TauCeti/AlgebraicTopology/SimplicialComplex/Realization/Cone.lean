/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cone
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contraction of realized cones

If `{v}` is a face and adjoining `v` to every face gives another face, the weak realization
contracts onto `v`. The contraction is affine in barycentric coordinates and fixes
the apex throughout. No finiteness or local finiteness is needed: joint continuity follows
from the closed-simplex cylinder criterion in `Realization.Homotopy`.

This supplies actual nullhomotopies for maps into cones, rather than only vanishing homotopy
groups. In particular the realization of the combinatorial cone on any abstract simplicial
complex is contractible.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (cones and polyhedra).
-/

public section

noncomputable section

open Set

namespace AbstractSimplicialComplex

attribute [local instance] Classical.decEq

variable {ι : Type*} {K : AbstractSimplicialComplex ι} {v : ι}

/-- The affine contraction of a weak realized cone onto its apex, relative to the apex.
At time `t` the coordinate vector is `(1 - t) • x + t • single v 1`. -/
def coneContraction (h : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v) :
    (ContinuousMap.id (Realization K)).HomotopyRel
      (ContinuousMap.const (Realization K) (vertex K v)) {vertex K v} where
  toFun p := ⟨(1 - (p.1 : ℝ)) • p.2.1 + (p.1 : ℝ) • Finsupp.single v 1,
    mem_realization_iff.mpr ⟨insert v (carrier K p.2).1,
      h.insert_mem (carrier K p.2).2,
      StandardSimplex.smul_add_single_mem ⟨p.2.1, mem_convexHull_carrier K p.2⟩ v p.1⟩⟩
  continuous_toFun := by
    apply continuous_prod_iff_faceInclusion.mpr
    intro σ
    let g : unitInterval × StandardSimplex σ.1 → StandardSimplex (insert v σ.1) :=
      fun p => ⟨(1 - (p.1 : ℝ)) • p.2.1 + (p.1 : ℝ) • Finsupp.single v 1,
        p.2.smul_add_single_mem v p.1⟩
    have hg : Continuous g := by
      apply continuous_induced_rng.mpr
      apply continuous_pi
      intro w
      have hx : Continuous (fun x : StandardSimplex σ.1 => (x.1 : ι → ℝ)) :=
        continuous_induced_dom
      have hc : Continuous (fun p : unitInterval × StandardSimplex σ.1 => p.2.1 w) :=
        ((continuous_apply w).comp hx).comp continuous_snd
      have ht : Continuous (fun p : unitInterval × StandardSimplex σ.1 => (p.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hh : Continuous (fun p : unitInterval × StandardSimplex σ.1 =>
          (1 - (p.1 : ℝ)) * p.2.1 w + (p.1 : ℝ) * (Finsupp.single v 1) w) := by
        fun_prop
      exact hh.congr fun p => by simp [g, Finsupp.single_apply]
    exact ((continuous_faceInclusion K ⟨insert v σ.1, h.insert_mem σ.2⟩).comp hg).congr
      fun p => Subtype.ext (by simp [g, faceInclusion_val])
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    simp
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    apply Subtype.ext
    simp [vertex_val]

/-- The coordinate formula characterizing the cone contraction. -/
@[simp]
theorem coneContraction_val
    (h : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v)
    (t : unitInterval) (x : Realization K) :
    (coneContraction h (t, x) : ι →₀ ℝ) =
      (1 - (t : ℝ)) • x.1 + (t : ℝ) • Finsupp.single v 1 := (rfl)

/-- The contraction fixes the apex at every time. -/
@[simp]
theorem coneContraction_vertex
    (h : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v)
    (t : unitInterval) : coneContraction h (t, vertex K v) = vertex K v :=
  (coneContraction h).eq_fst t (Set.mem_singleton _)

/-- The weak realization of a cone is contractible, without any finiteness hypothesis. -/
theorem contractibleSpace_realization_of_isCone
    (h : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v) :
    ContractibleSpace (Realization K) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨vertex K v, ⟨(coneContraction h).toHomotopy⟩⟩

/-- The realization of the combinatorial cone on any abstract complex is contractible. -/
theorem contractibleSpace_realization_cone (K : AbstractSimplicialComplex ι) :
    ContractibleSpace (Realization (cone K)) :=
  contractibleSpace_realization_of_isCone (isCone_cone (inst := Classical.decEq _) K)

end AbstractSimplicialComplex
