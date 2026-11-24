/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# No global action coordinates over a compact base

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
onto a Hausdorff manifold `B` of dimension `n`, with period lattice `Λ_b ⊆ T*_b B`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration.periodLattice`).
**Action coordinates** on `B` are functions `a₁, …, aₙ` whose differentials span the period
lattice over the integers, `Λ_b = ℤ da₁(b) + ⋯ + ℤ daₙ(b)` (up to the normalization `2π`, which
rescales the `aᵢ`). They are the actions of global action-angle coordinates, which identify the
fibration with `a(B) × Tⁿ`.

Since `Λ_b` is a full lattice of rank `n` in the `n`-dimensional space `T*_b B`, any at most `n`
covectors whose integer span contains `Λ_b` are linearly independent
(`IsLagrangianTorusFibration.linearIndependent_of_periodLattice_le_closure`). In particular none
of them vanishes, so an action coordinate has no critical point
(`IsLagrangianTorusFibration.mvfderiv_ne_zero_of_periodLattice_le_closure`), and no local maximum
or minimum on a boundaryless base
(`IsLagrangianTorusFibration.not_isLocalExtr_of_periodLattice_le_closure`).

Every function on a nonempty compact boundaryless manifold has a critical point in the sense of
`TauCeti.criticalPoints` (`TauCeti.criticalPoints_nonempty`): a point where it attains its
minimum if it is continuous, and otherwise a point where it is not differentiable, at which its
`mfderiv` is zero by convention. Hence **a regular Lagrangian torus fibration over a nonempty
compact boundaryless base of positive dimension has no global action coordinates**
(`IsLagrangianTorusFibration.not_forall_periodLattice_le_closure_of_compactSpace`): its
period lattice is never spanned over `ℤ` by the differentials of at most `dim B` functions,
although it is spanned locally by the differentials of local action coordinates.

The basic example is the torus bundle `T*Tⁿ / Λ → Tⁿ` of the closed angle forms `dt_i` of the torus
`Tⁿ = ∀ i, AddCircle (p i)` (`TauCeti.torusTimeForm`), the model
`TauCeti.CotangentBundle.LatticeQuotient` of the coframe `dt_i`. It is a regular Lagrangian torus
fibration over the compact torus, so it has no global action coordinates
(`TauCeti.CotangentBundle.LatticeQuotient.not_forall_periodLattice_le_closure_torusTimeForm`). For
one angle this is the fibration `T² → S¹` of the torus with the symplectic form `dθ ∧ dφ`, built
from the closed angle form `dθ` of the base circle: its period lattice is spanned over `ℤ` by the
differential of no function on the circle.

## Main results

* `IsLagrangianTorusFibration.linearIndependent_of_periodLattice_le_closure`: at most `dim B`
  covectors whose integer span contains `Λ_b` are linearly independent.
* `IsLagrangianTorusFibration.not_isLocalExtr_of_periodLattice_le_closure`: action coordinates have
  no local extrema.
* `IsLagrangianTorusFibration.not_forall_periodLattice_le_closure_of_compactSpace`: there are no
  global action coordinates over a compact base.
* `TauCeti.CotangentBundle.LatticeQuotient.not_forall_periodLattice_le_closure_torusTimeForm`: the
  torus bundle of the angle forms of a torus has no global action coordinates.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (global action coordinates and the exactness of the period forms).
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}
  (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed)
  {ι : Type*} [Fintype ι]

include h

/-- **Covectors spanning the period lattice are independent.** If the period lattice `Λ_b` lies in
the integer span of at most `dim B` covectors `v i`, these covectors are linearly independent: they
span `T*_b B` over `ℝ`, because the full lattice `Λ_b` does, and there are at most as many of them
as its dimension. -/
theorem linearIndependent_of_periodLattice_le_closure {b : B} {v : ι → F →L[ℝ] ℝ}
    (hcard : Fintype.card ι ≤ finrank ℝ F)
    (hv : h.periodLattice hσc b ≤ AddSubgroup.closure (range v)) :
    LinearIndependent ℝ v :=
  IsZLattice.linearIndependent_of_le_span (L := (h.periodLattice hσc b).toIntSubmodule)
    (by rwa [ContinuousLinearMap.dual_finrank_eq])
    fun _ hα ↦ by
      rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
      exact hv hα

variable {a : B → ι → ℝ}

/-- **Action coordinates have no critical points.** If the period lattice `Λ_b` lies in the integer
span of the differentials at `b` of at most `dim B` functions `a i`, none of these differentials
vanishes at `b`. -/
theorem mvfderiv_ne_zero_of_periodLattice_le_closure {b : B}
    (hcard : Fintype.card ι ≤ finrank ℝ F)
    (ha : h.periodLattice hσc b ≤
      AddSubgroup.closure (range fun i ↦ mvfderiv J (fun y ↦ a y i) b)) (i : ι) :
    mvfderiv J (fun y ↦ a y i) b ≠ 0 :=
  (h.linearIndependent_of_periodLattice_le_closure hσc hcard ha).ne_zero i

/-- **Action coordinates have no local extrema.** On a boundaryless base, if the period lattice
`Λ_b` lies in the integer span of the differentials at `b` of at most `dim B` functions `a i`, then
no `a i` has a local maximum or minimum at `b`. -/
theorem not_isLocalExtr_of_periodLattice_le_closure [J.Boundaryless] {b : B}
    (hcard : Fintype.card ι ≤ finrank ℝ F)
    (ha : h.periodLattice hσc b ≤
      AddSubgroup.closure (range fun i ↦ mvfderiv J (fun y ↦ a y i) b)) (i : ι) :
    ¬ IsLocalExtr (fun y ↦ a y i) b := fun hextr ↦
  h.mvfderiv_ne_zero_of_periodLattice_le_closure hσc hcard ha i
    (mem_criticalPoints.1
      (hextr.mem_criticalPoints (I := J) BoundarylessManifold.isInteriorPoint))

/-- **No global action coordinates over a compact base.** Let `π : M → B` be a regular Lagrangian
torus fibration over a nonempty compact boundaryless manifold `B`. Then no functions `a i`, at least
one and at most `dim B` of them, have differentials whose integer span contains the period lattice
at every point of `B`. So the period lattice of such a fibration is never spanned over `ℤ` by the
differentials of at most `dim B` functions. -/
theorem not_forall_periodLattice_le_closure_of_compactSpace [J.Boundaryless] [CompactSpace B]
    [Nonempty B] [Nonempty ι] (hcard : Fintype.card ι ≤ finrank ℝ F) :
    ¬ ∀ b, h.periodLattice hσc b ≤
      AddSubgroup.closure (range fun i ↦ mvfderiv J (fun y ↦ a y i) b) := fun hall ↦ by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨b, hb⟩ := criticalPoints_nonempty (I := J) (f := fun y ↦ a y i)
  exact h.mvfderiv_ne_zero_of_periodLattice_le_closure hσc hcard (hall b) i
    (mem_criticalPoints.1 hb)

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

namespace TauCeti.CotangentBundle.LatticeQuotient

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- **The torus bundle of the angle forms of a torus has no global action coordinates.** Let
`Λ` be the lattice spanned by the closed angle forms `dt_i` of the torus
`Tⁿ = ∀ i, AddCircle (p i)`, a global coframe (`TauCeti.isLocalFrameOn_torusTimeForm`). The
torus bundle `T*Tⁿ / Λ → Tⁿ` is a regular Lagrangian torus fibration over the compact torus
(`TauCeti.CotangentBundle.LatticeQuotient.isLagrangianTorusFibration_proj`). For `n ≥ 1`, no
functions `a i` on `Tⁿ` have differentials whose integer span contains its period lattice at every
point. For a single angle this is the fibration `T² → S¹` with the symplectic
form `dθ ∧ dφ`. -/
theorem not_forall_periodLattice_le_closure_torusTimeForm [Nonempty ι]
    (a : (∀ i, AddCircle (p i)) → ι → ℝ) :
    ¬ ∀ b, (isLagrangianTorusFibration_proj (isLocalFrameOn_torusTimeForm p)
        (isClosed_torusTimeForm p)).periodLattice
          (isSymplectic_symplecticForm (isLocalFrameOn_torusTimeForm p)
            (isClosed_torusTimeForm p)).isClosed b ≤
        AddSubgroup.closure
          (range fun i ↦ mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ a y i) b) :=
  (isLagrangianTorusFibration_proj _ _).not_forall_periodLattice_le_closure_of_compactSpace _
    (by simp)

end TauCeti.CotangentBundle.LatticeQuotient
