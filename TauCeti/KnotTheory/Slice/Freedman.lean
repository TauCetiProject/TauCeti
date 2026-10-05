/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.KnotGroup
public import TauCeti.KnotTheory.Slice.Basic

/-!
# Freedman's theorem: Alexander polynomial one knots are topologically slice

Kirby's problem 1.36 (L. Taylor) asks whether a knot with Alexander polynomial one is slice.
Smoothly the answer is no, but topologically it is yes: Freedman proved that such a knot bounds a
locally flat disc in `D⁴`, whose complement moreover has infinite cyclic fundamental group.

The hypothesis is stated through the knot group `π = π₁(S³ \ K)`, as in Freedman and Quinn,
Theorem 11.7B: the natural homomorphism `π → ℤ`, the abelianization, has perfect kernel. That
kernel is the commutator subgroup `π'`, so the condition is
`TauCeti.SmoothCircleEmbedding.HasPerfectCommutatorSubgroup`, saying `π'' = π'`. The abelian group
`π' / π''` is the Alexander module `H₁(X∞)` of the infinite cyclic cover of the complement, which a
Seifert matrix `V` presents over `ℤ[t, t⁻¹]` by the square matrix `tV - Vᵀ`. The module vanishes
exactly when its order ideal `(Δ)` is the unit ideal, so `π'' = π'` is equivalent to `Δ ≐ 1`, a
result Freedman and Quinn attribute to Crowell. Reading the hypothesis off the knot group keeps the
statement free of any choice of Seifert surface or diagram.

`TauCeti.FreedmanSliceTheorem` asserts that every knot in `S³` with perfect commutator subgroup is
topologically slice (`TauCeti.IsTopologicallySlice`). It is recorded as a proposition and not
proved. Both sides are exercised on the unknot: its knot group is infinite cyclic, so it has perfect
commutator subgroup (`TauCeti.hasPerfectCommutatorSubgroup_unknot`), and it is topologically slice
(`TauCeti.isTopologicallySlice_unknot`).

## Main definitions

* `TauCeti.FreedmanSliceTheorem`: a knot in `S³` whose knot group has perfect commutator subgroup,
  that is, whose Alexander polynomial is one, is topologically slice.

## Main results

* `TauCeti.FreedmanSliceTheorem.isTopologicallySlice`: applying the theorem to a knot.

## References

* M. Freedman, *The topology of four-dimensional manifolds*, J. Differential Geom. 17 (1982),
  357–453.
* M. Freedman and F. Quinn, *Topology of 4-Manifolds*, Princeton (1990), Theorem 11.7B and
  Section 12.3D.
* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.36, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
-/

public section

open Metric
open scoped Manifold EuclideanSpace

namespace TauCeti

/-- **Freedman's theorem that Alexander polynomial one knots are topologically slice.** Every knot
`K : S¹ → S³` whose knot group `π` has perfect commutator subgroup, `π'' = π'`, bounds a locally
flat disc in `D⁴`. For a knot in `S³` the condition `π'' = π'` says that the Alexander module
`π' / π''` vanishes, which is equivalent to the Alexander polynomial being one. -/
def FreedmanSliceTheorem : Prop :=
  ∀ K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    K.HasPerfectCommutatorSubgroup → IsTopologicallySlice K

/-- Freedman's theorem spelled out: every knot in `S³` with perfect commutator subgroup is
topologically slice. -/
theorem freedmanSliceTheorem_iff :
    FreedmanSliceTheorem ↔
      ∀ K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
        K.HasPerfectCommutatorSubgroup → IsTopologicallySlice K :=
  Iff.rfl

/-- By Freedman's theorem, a knot in `S³` with perfect commutator subgroup is topologically
slice. -/
theorem FreedmanSliceTheorem.isTopologicallySlice (h : FreedmanSliceTheorem)
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    (hK : K.HasPerfectCommutatorSubgroup) : IsTopologicallySlice K :=
  h K hK

end TauCeti
