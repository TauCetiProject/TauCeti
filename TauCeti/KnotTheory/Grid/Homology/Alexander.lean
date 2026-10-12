/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Homology.Unblocked

/-!
# The Alexander grading of unblocked grid homology

For a grid diagram `G` with an odd number of link components, the unblocked grid chain module
`GC⁻` is the internal direct sum of its Alexander pieces over the coefficient ring `R`, and the
unblocked grid differential `∂⁻` preserves the Alexander grading
(`TauCeti.OddComponentGridDiagram.alexanderChainMinusGrading`). The grading therefore descends to
the homology `ker ∂⁻ ⧸ im ∂⁻`, which is the unblocked grid homology `GH⁻`
(`TauCeti.GridDiagram.unblockedHomologyIso`): a class has Alexander degree `a` when it is the class
of a cycle all of whose monomials `V^e · x` have `A(x) - |e| = a`.

Each variable `V_c` has Alexander degree `-1` on `GC⁻`, on the concrete homology quotient, and
on Mathlib's categorical homology `GH⁻`. The grading on `GH⁻` is transported across the
cycle-quotient isomorphism. Its homogeneous pieces are modules over `R`, since the variables move
the Alexander grading. For a knot, every variable acts as `U`; the resulting degree rule for
`U` is in `Homology/KnotAlexander`.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderHomologyGrading`: the Alexander grading of
  `ker ∂⁻ ⧸ im ∂⁻`.
* `TauCeti.OddComponentGridDiagram.alexanderUnblockedHomologyGrading`: the corresponding
  grading of categorical `GH⁻`.

## Main results

* `TauCeti.OddComponentGridDiagram.mem_alexanderHomologyGrading_piece_iff`: a class has Alexander
  degree `a` exactly when it is the class of a cycle of Alexander degree `a`.
* `TauCeti.OddComponentGridDiagram.X_smul_mem_alexanderHomologyGrading_piece`: each variable
  `V_c` lowers the Alexander grading of grid homology by one.
* `TauCeti.OddComponentGridDiagram.X_smul_mem_alexanderUnblockedHomologyGrading_piece`: the
  same degree rule on categorical `GH⁻`.
* `TauCeti.OddComponentGridDiagram.unblockedHomologyEquivOfIntertwining_mem_piece`: if an
  equivalence intertwining two unblocked differentials preserves the Alexander grading of chains,
  the induced equivalence of `GH⁻` preserves the Alexander grading.

## References

The Alexander grading of `GH⁻` and the action of `U` in Alexander degree `-1` are those of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4; the definition of `τ`
from them is in Chapter 6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The Alexander grading of unblocked grid homology**: the grading of `ker ∂⁻ ⧸ im ∂⁻` induced
by the Alexander grading of `GC⁻`, which `∂⁻` preserves. Its degree-`a` piece consists of the
classes of the cycles of Alexander degree `a`. -/
noncomputable def alexanderHomologyGrading :
    InternalGrading R
      ((G.1.unblockedDifferential R).homology
        (G.1.unblockedDifferential_comp_self_eq_zero R)) :=
  (G.alexanderChainMinusGrading R).homology
    (G.isHomogeneous_unblockedDifferential_alexanderChainMinusGrading R)
    (G.1.unblockedDifferential_comp_self_eq_zero R)

variable {G R}

/-- A class in `ker ∂⁻ ⧸ im ∂⁻` has Alexander degree `a` exactly when it is the class of a cycle of
Alexander degree `a`. -/
theorem mem_alexanderHomologyGrading_piece_iff {a : ℤ}
    {y : (G.1.unblockedDifferential R).homology
      (G.1.unblockedDifferential_comp_self_eq_zero R)} :
    y ∈ (G.alexanderHomologyGrading R).piece a ↔
      ∃ z : LinearMap.ker (G.1.unblockedDifferential R),
        (z : GridChainMinus R n) ∈ G.alexanderChainMinusPiece R a ∧
          (G.1.unblockedDifferential R).homologyπ
            (G.1.unblockedDifferential_comp_self_eq_zero R) z = y := by
  rw [alexanderHomologyGrading, InternalGrading.mem_homology_piece_iff,
    alexanderChainMinusGrading_piece]

/-- **The variable `V_c` lowers the Alexander grading of grid homology by one.** -/
theorem X_smul_mem_alexanderHomologyGrading_piece (i : Fin n) {a : ℤ}
    {y : (G.1.unblockedDifferential R).homology
      (G.1.unblockedDifferential_comp_self_eq_zero R)}
    (hy : y ∈ (G.alexanderHomologyGrading R).piece a) :
    (X i : MvPolynomial (Fin n) R) • y ∈ (G.alexanderHomologyGrading R).piece (a - 1) := by
  rw [sub_eq_add_neg]
  refine (G.alexanderChainMinusGrading R).smul_mem_homology_piece _
    (G.1.unblockedDifferential_comp_self_eq_zero R) (fun p x hx ↦ ?_) hy
  rw [alexanderChainMinusGrading_piece] at hx ⊢
  exact G.X_smul_mem_alexanderChainMinusPiece i hx

variable (G R)

/-- The Alexander grading on the categorical unblocked grid homology, transported from the
cycle quotient. Its degree-`a` piece consists of the classes of Alexander-homogeneous cycles. -/
noncomputable def alexanderUnblockedHomologyGrading : InternalGrading R (G.1.unblockedHomology R) :=
  (G.alexanderHomologyGrading R).map
    ((G.1.unblockedHomologyIso R).symm.toLinearEquiv.restrictScalars R)

/-- A class of `GH⁻` is Alexander-homogeneous of degree `a` exactly when its image in the
cycle quotient is homogeneous of that degree. -/
@[simp]
theorem mem_alexanderUnblockedHomologyGrading_piece_iff (a : ℤ)
    (y : G.1.unblockedHomology R) :
    y ∈ (G.alexanderUnblockedHomologyGrading R).piece a ↔
      (G.1.unblockedHomologyIso R).hom y ∈ (G.alexanderHomologyGrading R).piece a := by
  exact InternalGrading.mem_map_piece_iff _ _ _ _

/-- A grid variable lowers the Alexander degree of a class of `GH⁻` by one. -/
theorem X_smul_mem_alexanderUnblockedHomologyGrading_piece (i : Fin n) {a : ℤ}
    {y : G.1.unblockedHomology R}
    (hy : y ∈ (G.alexanderUnblockedHomologyGrading R).piece a) :
    (X i : MvPolynomial (Fin n) R) • y ∈
      (G.alexanderUnblockedHomologyGrading R).piece (a - 1) := by
  rw [G.mem_alexanderUnblockedHomologyGrading_piece_iff R] at hy ⊢
  rw [map_smul]
  exact G.X_smul_mem_alexanderHomologyGrading_piece i hy

/-! ### Equivalences induced by intertwining maps -/

section Intertwining

variable (G' : OddComponentGridDiagram n)
  {σ σ' : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] (e : GridChainMinus R n ≃ₛₗ[σ] GridChainMinus R n)
  (he : ∀ c, G'.1.unblockedDifferential R (e c) = e (G.1.unblockedDifferential R c))

/-- If an equivalence intertwining two unblocked differentials preserves the Alexander grading of
chains, the induced equivalence of unblocked homologies preserves the Alexander grading. -/
theorem unblockedHomologyEquivOfIntertwining_mem_piece
    (hA : ∀ a c, c ∈ G.alexanderChainMinusPiece R a → e c ∈ G'.alexanderChainMinusPiece R a)
    {a : ℤ} {y : G.1.unblockedHomology R}
    (hy : y ∈ (G.alexanderUnblockedHomologyGrading R).piece a) :
    G.1.unblockedHomologyEquivOfIntertwining R G'.1 e he y ∈
      (G'.alexanderUnblockedHomologyGrading R).piece a := by
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff, mem_alexanderHomologyGrading_piece_iff]
    at hy ⊢
  obtain ⟨z, hz, hzy⟩ := hy
  obtain rfl : y = G.1.unblockedHomologyClass R z := by
    apply (ModuleCat.mono_iff_injective (G.1.unblockedHomologyIso R).hom).mp inferInstance
    rw [GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass, hzy]
  refine ⟨⟨e z, G.1.map_mem_ker_unblockedDifferential_of_intertwining R G'.1 e he z.2⟩,
    hA a _ hz, ?_⟩
  rw [GridDiagram.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass,
    GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass]

end Intertwining

end TauCeti.OddComponentGridDiagram
