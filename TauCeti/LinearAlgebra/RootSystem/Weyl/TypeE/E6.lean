/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.GroupTheory.Coxeter.Restriction
import TauCeti.GroupTheory.Perm.Coxeter
import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.HighestRoot
import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient

/-!
# The Weyl group of type `E₆` has order `51840`

Every finite reduced crystallographic root system over `ℚ` with a base of Cartan type `E₆` has a
Weyl group of order `51840 = 2⁷ · 3⁴ · 5 = 72 · 6!`.

The Weyl group is an invariant of the Cartan type
(`TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`), so the order is computed on the pinned
rational model `TauCeti.DynkinType.rationalRootSystem` of type `E₆`, by orbit and stabilizer at
its highest root `θ`, the root at index `35`
(`TauCeti.DynkinType.highestRoot_e6SimplyConnectedBase`).

* **The orbit.** The system is irreducible and simply laced, so its Weyl group is transitive on the
  roots: the orbit of `θ` consists of all `72` roots
  (`RootPairing.Base.orbit_root_eq_range_of_isSimplyLaced`).
* **The stabilizer.** In the fundamental-weight coordinates of the model, `θ` is the fundamental
  weight `ω₂`: it pairs to `1` with the simple coroot `α₂^∨` and to `0` with the other five. So `θ`
  is dominant, and its stabilizer is the standard parabolic subgroup of the Coxeter system
  `TauCeti.weylCoxeterSystem` on the simple roots orthogonal to it
  (`RootPairing.parabolic_wallIndices_eq_stabilizer`). In the Bourbaki numbering these are
  `α₁, α₃, α₄, α₅, α₆`, a chain of type `A₅`. Along it the Coxeter matrix of `E₆` restricts to
  `CoxeterMatrix.A 5`, the Coxeter matrix of the symmetric group `S₆` on its adjacent
  transpositions (`TauCeti.permCoxeterSystem`), so `CoxeterSystem.parabolicHom` embeds `S₆` into
  the Weyl group with image that parabolic subgroup (`CoxeterSystem.parabolicHom_injective`,
  `CoxeterSystem.range_parabolicHom`). The stabilizer therefore has order `6! = 720`.

Hence the Weyl group has order `72 · 720 = 51840`.

## Main results

* `RootPairing.card_weylGroup_of_hasCartanType_E6`: **every finite reduced crystallographic root
  system over `ℚ` with a base of Cartan type `E₆` has Weyl group of order `51840`.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.12 and Plate V.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Sections 1.10, 1.12 and 2.11.
* S. Fomin and N. Reading, *Root systems and generalized associahedra*, arXiv:math/0505518v3,
  Lecture 2, §2.5, Figure 2.8.
-/

public section

namespace TauCeti.DynkinType

open RootPairing MulAction

local notation "P₆" => E6.rationalRootSystem valid_E6
local notation "b₆" => E6.rationalBase valid_E6

/-- The index of the highest root of `E₆` in the pinned root tables, the last positive root
(`TauCeti.DynkinType.highestRoot_e6SimplyConnectedBase`). -/
private def e6Theta : Fin E6.numRoots := ⟨35, by decide⟩

/-- The Bourbaki-numbered simple roots `α₁, α₃, α₄, α₅, α₆` of `E₆`, the walls through the highest
root, listed along their `A₅` chain. -/
private def e6WallNode (m : Fin 5) : Fin E6.rank := Fin.cast rank_E6.symm (![0, 2, 3, 4, 5] m)

/-- The walls through the highest root, as simple roots of the pinned rational base. -/
private noncomputable def e6Wall (m : Fin 5) : (b₆).support :=
  E6.simpleSupportEquiv valid_E6 (e6WallNode m)

/-- In the fundamental-weight coordinates of the pinned datum the highest root of `E₆` is `ω₂`. -/
private lemma root_e6Theta (k : Fin E6.rank) :
    (E6.simplyConnectedRootDatum valid_E6).root e6Theta k = if (k : ℕ) = 1 then 1 else 0 := by
  rw [simplyConnectedRootDatum_E6, e6SimplyConnectedRootDatum_root]
  -- `e6Theta` is the index `35` of the table, read in `Fin E6.numRoots`
  refine (congrFun e6Root_apply_35 k).trans ?_
  fin_cases k <;> rfl

/-- **The highest root of `E₆` is the fundamental weight `ω₂`:** it pairs to `1` with the simple
coroot `α₂^∨` and to `0` with the other five. -/
private lemma coroot'_simpleSupportEquiv_root_e6Theta (k : Fin E6.rank) :
    (P₆).coroot' (E6.simpleSupportEquiv valid_E6 k) ((P₆).root e6Theta) =
      if (k : ℕ) = 1 then 1 else 0 := by
  rw [LinearMap.flip_apply, toLinearMap_rationalRootSystem, coe_simpleSupportEquiv,
    coroot_rationalRootSystem_simpleIndex, dotProduct_single, mul_one, root_rationalRootSystem,
    root_e6Theta]
  split_ifs <;> simp

/-- The highest root of `E₆` is dominant. -/
private lemma root_e6Theta_mem_dominantChamber : (P₆).root e6Theta ∈ dominantChamber P₆ b₆ := by
  refine (mem_dominantChamber_iff_forall_equiv P₆ b₆ (E6.simpleSupportEquiv valid_E6) _).mpr
    fun k ↦ ?_
  rw [coroot'_simpleSupportEquiv_root_e6Theta]
  split_ifs <;> norm_num

/-- The walls through the highest root of `E₆` are the simple roots `α₁, α₃, α₄, α₅, α₆`. -/
private lemma wallIndices_root_e6Theta :
    (P₆).wallIndices b₆ ((P₆).root e6Theta) = Set.range e6Wall := by
  ext i
  obtain ⟨k, rfl⟩ := (E6.simpleSupportEquiv valid_E6).surjective i
  simp only [mem_wallIndices, coroot'_simpleSupportEquiv_root_e6Theta, Set.mem_range, e6Wall,
    (E6.simpleSupportEquiv valid_E6).injective.eq_iff, ite_eq_right_iff, one_ne_zero, imp_false]
  revert k
  decide

/-- Along the `A₅` chain of walls the Coxeter matrix of the `E₆` base is that of `A₅`. -/
private lemma coxeterMatrix_A_eq_coxeterMatrixOfBase_e6Wall (i j : Fin 5) :
    CoxeterMatrix.A (6 - 1) i j = coxeterMatrixOfBase P₆ b₆ (e6Wall i) (e6Wall j) := by
  rw [coxeterMatrixOfBase_eq_coxeterMatrix_reindex _ (E6.cartanMatrix_rationalBase_symm valid_E6),
    CoxeterMatrix.reindex_apply, Equiv.symm_symm]
  simp only [e6Wall, Equiv.symm_apply_apply, coxeterMatrix_E6]
  fin_cases i <;> fin_cases j <;> rfl

/-- The stabilizer of the highest root of `E₆` is a copy of the symmetric group `S₆`, of order
`720`. -/
private lemma card_stabilizer_root_e6Theta :
    Nat.card (stabilizer (P₆).weylGroup ((P₆).root e6Theta)) = 720 := by
  rw [← parabolic_wallIndices_eq_stabilizer P₆ b₆ root_e6Theta_mem_dominantChamber,
    wallIndices_root_e6Theta, ← CoxeterSystem.range_parabolicHom (permCoxeterSystem 6)
      coxeterMatrix_A_eq_coxeterMatrixOfBase_e6Wall,
    ← Nat.card_congr (MonoidHom.ofInjective (CoxeterSystem.parabolicHom_injective
      (permCoxeterSystem 6) coxeterMatrix_A_eq_coxeterMatrixOfBase_e6Wall)).toEquiv,
    Nat.card_perm, Nat.card_fin]
  rfl

/-- The Weyl group of the pinned rational root system of type `E₆` has order `51840`, the `72`
roots in the orbit of the highest root times the `6!` elements of its stabilizer. -/
private theorem card_weylGroup_rationalRootSystem_E6 : Nat.card (P₆).weylGroup = 51840 := by
  have hsl : (b₆).cartanMatrix.IsSimplyLaced :=
    ((E6.hasCartanType_rationalRootSystem valid_E6).isSimplyLaced_iff).mpr (.inl isSimplyLaced_E6)
  rw [(b₆).card_weylGroup_eq_card_mul_card_stabilizer_of_isSimplyLaced hsl e6Theta,
    card_stabilizer_root_e6Theta, Nat.card_fin, numRoots_E6]

end TauCeti.DynkinType

namespace RootPairing

open TauCeti TauCeti.DynkinType

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N) [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- **The Weyl group of type `E₆` has order `51840`**: every finite reduced crystallographic root
system over `ℚ` with a base of Cartan type `E₆` has Weyl group of order `51840 = 2⁷ · 3⁴ · 5`. -/
theorem card_weylGroup_of_hasCartanType_E6 (h : HasCartanType P b .E6) :
    Nat.card P.weylGroup = 51840 := by
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b (E6.rationalBase valid_E6) .E6 h
    (E6.hasCartanType_rationalRootSystem valid_E6)
  rw [Nat.card_congr e.toEquiv, card_weylGroup_rationalRootSystem_E6]

end RootPairing
