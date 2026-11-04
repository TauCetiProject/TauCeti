/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Projective orbits of maximal dimension

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, acting
on a finite-dimensional representation `M`, and let `P(M)` be the projective space of lines in
`M`. The space `P(M)` is irreducible of dimension at most `dim M - 1`, so the orbit `O` of a line
`[m]` has `dim O ≤ dim M - 1`.

An orbit attaining this bound is **dense**: otherwise its closure would be a proper closed subset of
the irreducible space `P(M)`, of the same dimension as the orbit and hence of dimension strictly
less than `dim M - 1`. Being locally closed, a dense orbit is **open**.

Any two orbits attaining the bound **coincide**. If `[n]` lies outside the open dense orbit of
`[m]`, it lies in its boundary, and boundary orbits have strictly smaller dimension
(`TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt`). So `[n]` lies in the orbit
of `[m]`; as a closed point of that orbit it is the image of a rational point `g` of `G`, which
carries the line `k ∙ m` to `k ∙ n`.

These are statements about the full scheme-theoretic orbit images, including their nonclosed
points. No connectedness, smoothness or reducedness of `G` is needed. In the classification of
nilpotent orbits by weighted Dynkin diagrams they are the uniqueness step for the dense orbit of
the grade-zero centralizer of an `sl₂`-triple on the grade-two space, where the orbit of the
nilpositive element has full dimension because its tangent space is the whole grade-two space.

## Main results

* `TauCeti.Comodule.closure_range_projectiveOrbitMap_eq_univ`: an orbit of dimension `dim M - 1` is
  dense.
* `TauCeti.Comodule.isOpen_range_projectiveOrbitMap`: an orbit of dimension `dim M - 1` is open.
* `TauCeti.Comodule.exists_span_basePointsRepresentation_eq` and
  `TauCeti.Comodule.range_projectiveOrbitMap_eq`: two lines whose orbits have dimension
  `dim M - 1` are carried to each other by a rational point of `G`, and their scheme-theoretic
  projective orbits coincide.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3, orbits and their closures.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §3.5, for the dense orbit in the grade-two space of a nilpotent.
-/

public section

open AlgebraicGeometry Topology

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- **An orbit of maximal dimension is dense.** If the orbit of a line in `M` has dimension
`dim M - 1`, its closure is the whole projective space of lines in `M`. -/
theorem closure_range_projectiveOrbitMap_eq_univ (m : M) (hm : Module.IsUnimodular k m)
    (hdim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) + 1) :
    closure (Set.range (projectiveOrbitMap (H := H) m hm)) = Set.univ := by
  obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hm
  have : Nontrivial (Module.Dual k M) := ⟨⟨φ, 0, fun h ↦ by simp [h] at hφ⟩⟩
  by_contra hne
  -- The closure is a proper closed subset of the irreducible projective space, so its dimension,
  -- which is that of the orbit, is at most `dim M - 2`.
  have hlt := IsClosed.topologicalKrullDim_add_one_le isClosed_closure hne
  rw [topologicalKrullDim_closure_range_projectiveOrbitMap] at hlt
  have hP := SymmetricAlgebra.topologicalKrullDim_proj_add_one_le_finrank (Module.Dual k M) k
  rw [Subspace.dual_finrank_eq] at hP
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_range_projectiveOrbitMap_eq_natCast (H := H) m hm
  rw [hd] at hdim hlt
  have h := (add_le_add_left hlt 1).trans (hP.trans hdim)
  norm_cast at h
  omega

/-- **An orbit of maximal dimension is open.** If the orbit of a line in `M` has dimension
`dim M - 1`, it is an open subset of the projective space of lines in `M`. -/
theorem isOpen_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m)
    (hdim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) + 1) :
    IsOpen (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have h := isClosed_closure_diff_range_projectiveOrbitMap (H := H) m hm
  rwa [closure_range_projectiveOrbitMap_eq_univ m hm hdim, ← Set.compl_eq_univ_sdiff,
    isClosed_compl_iff] at h

/-- **Two orbits of maximal dimension are conjugate.** If the orbits of the lines through `m` and
`n` both have dimension `dim M - 1`, a rational point of `G` carries the line through `m` to the
line through `n`. -/
theorem exists_span_basePointsRepresentation_eq (m : M) (hm : Module.IsUnimodular k m)
    (n : M) (hn : Module.IsUnimodular k n)
    (hmdim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) + 1)
    (hndim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) n hn)) + 1) :
    ∃ g : WithConv (H →ₐ[k] k), k ∙ basePointsRepresentation M g m = k ∙ n := by
  set y := projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))
  -- The line `[n]` lies in the closure of the orbit of `[m]`. It cannot lie in the boundary,
  -- whose orbits have dimension smaller than `dim M - 1`.
  have hy : y ∈ Set.range (projectiveOrbitMap (H := H) m hm) := by
    by_contra hy
    have hlt := topologicalKrullDim_range_projectiveOrbitMap_lt hm hn
      ⟨closure_range_projectiveOrbitMap_eq_univ m hm hmdim ▸ Set.mem_univ y, hy⟩
    have hle := topologicalKrullDim_range_projectiveOrbitMap_add_one_le_finrank (H := H) m hm
    obtain ⟨a, ha⟩ := exists_topologicalKrullDim_range_projectiveOrbitMap_eq_natCast (H := H) m hm
    obtain ⟨b, hb⟩ := exists_topologicalKrullDim_range_projectiveOrbitMap_eq_natCast (H := H) n hn
    rw [ha, hb] at hlt
    rw [ha] at hle
    rw [hb] at hndim
    norm_cast at hlt hle hndim
    omega
  -- As a closed point of the orbit of `[m]`, the line `[n]` is a rational translate of `[m]`.
  obtain ⟨g, hg⟩ : y ∈ Set.range (fun g : WithConv (H →ₐ[k] k) ↦
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) := by
    rw [range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints]
    exact ⟨hy, projectiveOrbitMap_kernelPoint_mem_closedPoints n hn _⟩
  refine ⟨g, ?_⟩
  have h := (projectiveOrbitMap_kernelPoint_eq_iff_span_eq m hm n hn g 1).mp
    (by simpa [AlgHom.convOne_def] using hg)
  simpa using h

/-- **Two orbits of maximal dimension coincide.** If the orbits of the lines through `m` and `n`
both have dimension `dim M - 1`, their full scheme-theoretic orbit images in `P(M)` are equal. -/
theorem range_projectiveOrbitMap_eq (m : M) (hm : Module.IsUnimodular k m)
    (n : M) (hn : Module.IsUnimodular k n)
    (hmdim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) + 1)
    (hndim : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) n hn)) + 1) :
    Set.range (projectiveOrbitMap (H := H) m hm) =
      Set.range (projectiveOrbitMap (H := H) n hn) := by
  obtain ⟨g, hg⟩ := exists_span_basePointsRepresentation_eq m hm n hn hmdim hndim
  exact range_projectiveOrbitMap_eq_of_span_basePointsRepresentation_eq hm hn hg

end TauCeti.Comodule
