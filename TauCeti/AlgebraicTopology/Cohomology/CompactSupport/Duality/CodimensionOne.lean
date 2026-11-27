/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological
import TauCeti.CategoryTheory.Linear.Int
import TauCeti.Topology.Homotopy.HomotopyGroup.Basic

/-!
# Codimension-one homology of a closed simply connected manifold

A simply connected manifold admits a homological orientation. On a closed manifold, capping
with its fundamental class identifies codimension-one homology with first cohomology.
The latter vanishes for every abelian coefficient group by the degree-one Kronecker
isomorphism and the vanishing of first integral homology.

## References

* A. Hatcher, *Algebraic Topology*, Theorems 3.2 and 3.30.
-/

public section

open AlgebraicTopology CategoryTheory Limits Module

namespace TauCeti

/-- The codimension-one singular homology of a closed simply connected manifold without
boundary vanishes with coefficients in any abelian group. -/
theorem isZero_singularHomology_codim_one_of_simplyConnectedSpace
    {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]
    {q : ℕ} (hd : finrank ℝ E = q + 1) (L : ModuleCat ℤ) :
    IsZero (((singularHomologyFunctor (ModuleCat ℤ) q).obj L).obj (TopCat.of M)) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace (M := M) hd
  have h₁ := isZero_singularHomologyFunctor_ulift_of_subsingleton_homotopyGroup
    (X := TopCat.of M) (fun _ ↦ subsingleton_homotopyGroup_of_lt_two x) ℤ one_ne_zero
    (by decide : 1 < 2)
  have : Subsingleton (_ ⟶ L) := ⟨h₁.eq_of_src⟩
  have hc := ((TopCat.of M).singularKroneckerEquivOne
    (R := ModuleCat.of ℤ (ULift.{0} ℤ)) L).injective.subsingleton
  rw [ModuleCat.isZero_iff_subsingleton]
  refine @Function.Surjective.subsingleton _ _ _ ?_
    (o.bijective_singularCapAddHom_fundamentalClass hd L 1 q (Nat.add_comm ..)).2
  -- The two cohomology constructions use the module and preadditive ℤ-linear structures.
  convert hc using 2
  congr 1
  exact Subsingleton.elim _ _

end TauCeti
