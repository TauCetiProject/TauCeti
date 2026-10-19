/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.PL
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.PL

/-!
# Intrinsic stellar equivalence gives PL-homeomorphic polyhedra

Two simplicial complexes that are stellar equivalent after injective relabeling have
piecewise-linearly homeomorphic weak polyhedra. This is the intrinsic form of stellar invariance:
the complexes need not share the fresh vertices introduced by their stellar moves.

This result connects the intrinsic stellar equivalence used to define combinatorial spheres and
balls with the PL coordinate maps needed for their vertex-star charts. It combines the PL
homeomorphisms attached to finite stellar chains with descent through common vertex relabelings.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 1--2.
-/

public section

noncomputable section

open AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
  {K L : PreAbstractSimplicialComplex ι}

namespace StellarEquivalentUpToRelabeling

/-- Intrinsically stellar-equivalent finite complexes have PL-homeomorphic weak polyhedra.

Finiteness is required only for one complex; intrinsic stellar equivalence transports it to every
intermediate complex in the stellar chain. -/
theorem plHomeomorphic (h : StellarEquivalentUpToRelabeling K L)
    (hfin : K.faces.Finite) : PLHomeomorphic K L := by
  have hP : ∃ hKL : StellarEquivalentUpToRelabeling K L,
      ∀ hfin : K.faces.Finite, PLHomeomorphic K L := by
    refine h.induction_on
      (P := fun A B => ∃ hAB : StellarEquivalentUpToRelabeling A B,
        ∀ hfin : A.faces.Finite, PLHomeomorphic A B) ?_ ?_ ?_ ?_
    · intro A B e d he
      refine ⟨of_common_relabeling e d he, fun hA => ?_⟩
      exact PLHomeomorphic.of_common_relabeling (e := e) (d := d)
        (he.plHomeomorphic ((finite_faces_map_iff_of_injective e e.injective).mpr hA))
    · intro A
      exact ⟨.refl A, fun _ => PLHomeomorphic.refl A⟩
    · rintro A B ⟨hAB, ih⟩
      refine ⟨hAB.symm, fun hB => ?_⟩
      exact (ih ((finite_faces_iff hAB).mpr hB)).symm
    · rintro A B C ⟨hAB, ihAB⟩ ⟨hBC, ihBC⟩
      refine ⟨hAB.trans hBC, fun hA => ?_⟩
      exact (ihAB hA).trans (ihBC ((finite_faces_iff hAB).mp hA))
  exact hP.choose_spec hfin

end StellarEquivalentUpToRelabeling

/-! ### Combinatorial balls and spheres -/

/-- A combinatorial ball is PL-homeomorphic to a simplex of the prescribed dimension. -/
theorem IsCombinatorialBall.exists_plHomeomorphic_simplex
    {n : ℕ} (h : IsCombinatorialBall K n) :
    ∃ V : Finset ι, V.card = n + 1 ∧ PLHomeomorphic K (simplex V) := by
  have hfin := h.finite_faces
  obtain ⟨V, hV, hKV⟩ := isCombinatorialBall_iff.mp h
  exact ⟨V, hV, hKV.plHomeomorphic hfin⟩

/-- A combinatorial sphere is PL-homeomorphic to the boundary of a simplex of the prescribed
dimension. -/
theorem IsCombinatorialSphere.exists_plHomeomorphic_simplexBoundary
    {n : ℕ} (h : IsCombinatorialSphere K n) :
    ∃ V : Finset ι, V.card = n + 2 ∧ PLHomeomorphic K (simplexBoundary V) := by
  have hfin := h.finite_faces
  obtain ⟨V, hV, hKV⟩ := isCombinatorialSphere_iff.mp h
  exact ⟨V, hV, hKV.plHomeomorphic hfin⟩

end PreAbstractSimplicialComplex
