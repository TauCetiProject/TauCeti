/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
public import TauCeti.RepresentationTheory.Symmetric.Standard

import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Check: Lie–Kolchin needs connectedness

The constant group scheme `S₃` over `ℂ` has solvable group of points
(`TauCeti.Examples.LieKolchinSymmetricThree.isSolvable`) and is not connected
(`TauCeti.Examples.LieKolchinSymmetricThree.not_connectedSpace`), and its two-dimensional standard
representation `TauCeti.standardRepresentation ℂ (Fin 3)`, on the sum-zero vectors of `ℂ[Fin 3]`
with `S₃` permuting the coordinates, is irreducible
(`TauCeti.isIrreducible_standardRepresentation_fin_three`) and has no nonzero weight vector
(`TauCeti.Examples.LieKolchinSymmetricThree.not_hasNonzeroWeightVector`): a nonzero weight vector
would be a common eigenvector of all of `S₃`, so it would span an invariant line in the plane,
contradicting irreducibility. So the conclusion of the Lie–Kolchin
theorem (`TauCeti.Comodule.hasNonzeroWeightVector_of_nonzeroJointWeight_commutator` and its
corollaries need a connected group) fails for this disconnected solvable group.
-/

public section

open Equiv TauCeti

noncomputable section

namespace TauCeti.Examples.LieKolchinSymmetricThree

/-- `S₃` is solvable, as is every permutation group on at most four points. -/
theorem isSolvable : Group.IsSolvable (Perm (Fin 3)) :=
  Equiv.Perm.isSolvable (by simp)

/-- The constant group scheme `S₃` over `ℂ` is not connected. -/
theorem not_connectedSpace :
    ¬ConnectedSpace (ConstantGroup.groupScheme ℂ (Perm (Fin 3))).X.left :=
  ConstantGroup.not_connectedSpace_groupScheme (G := Perm (Fin 3)) ℂ

/-- The two-dimensional standard representation of `S₃` over `ℂ` is irreducible. -/
example : (standardRepresentation ℂ (Fin 3)).IsIrreducible :=
  isIrreducible_standardRepresentation_fin_three (by norm_num)

/-- **The two-dimensional representation of `S₃` has no nonzero weight vector.** As a comodule over
the coordinate ring of the constant group `S₃` over `ℂ`, the sum-zero vectors of `ℂ[Fin 3]` have no
nonzero weight vector, although the group of points `S₃` is solvable: the constant group is not
connected. -/
theorem not_hasNonzeroWeightVector :
    letI := ConstantGroup.representationComodule ℂ (standardRepresentation ℂ (Fin 3))
    ¬Comodule.HasNonzeroWeightVector ℂ (ConstantGroup.coordinateRing ℂ (Perm (Fin 3)))
      (augmentationSubrepresentation ℂ (Perm (Fin 3)) (Fin 3)).toSubmodule := by
  let := ConstantGroup.representationComodule ℂ (standardRepresentation ℂ (Fin 3))
  rw [Comodule.hasNonzeroWeightVector_iff]
  rintro ⟨v, c, hv, -, hcoact⟩
  -- the point `σ` acts on the weight vector `v` through the scalar `σ(c)`
  have hline (σ : Perm (Fin 3)) : ∃ a : ℂ, standardRepresentation ℂ (Fin 3) σ v = a • v := by
    refine ⟨(ConstantGroup.toPoints ℂ _ σ).ofConv c, ?_⟩
    rw [← ConstantGroup.basePointsRepresentation_toPoints, Comodule.basePointsRepresentation_apply,
      Comodule.endOfPoint_tmul, hcoact]
    simp
  -- so `v` spans an invariant line, which irreducibility makes `⊥` or the whole plane
  rcases (isIrreducible_standardRepresentation_fin_three (k := ℂ) (by norm_num)).eq_bot_or_eq_top
    (Subrepresentation.spanSingleton v hline) with h | h
  · have hmem := Subrepresentation.self_mem_spanSingleton v hline
    rw [h, Subrepresentation.mem_bot] at hmem
    exact hv hmem
  · -- a line has dimension one, while the plane has dimension `3 - 1 = 2`
    have htop := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_spanSingleton, Subrepresentation.toSubmodule_top] at htop
    have hdim := finrank_span_singleton (K := ℂ) hv
    rw [htop, finrank_top, finrank_augmentationSubrepresentation] at hdim
    simp at hdim

end TauCeti.Examples.LieKolchinSymmetricThree
