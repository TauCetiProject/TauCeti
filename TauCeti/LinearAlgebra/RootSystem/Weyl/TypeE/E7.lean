/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.GroupTheory.Coxeter.Restriction
import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient
import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeD.Basic

/-!
# The Weyl group of type `E₇` has order `2903040`

Every finite reduced crystallographic root system over `ℚ` with a base of Cartan type `E₇` has a
Weyl group of order `2903040 = 2¹⁰ · 3⁴ · 5 · 7 = 126 · 2⁵ · 6!`.

The Weyl group is an invariant of the Cartan type
(`TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`), so the order is computed on the pinned
rational model `TauCeti.DynkinType.rationalRootSystem` of type `E₇`, by orbit and stabilizer at
its highest root `θ`, the root at index `62`
(`TauCeti.DynkinType.highestRoot_e7SimplyConnectedBase`).

* **The orbit.** The system is irreducible and simply laced, so its Weyl group is transitive on the
  roots: the orbit of `θ` consists of all `126` roots
  (`RootPairing.Base.orbit_root_eq_range_of_isSimplyLaced`).
* **The stabilizer.** In the fundamental-weight coordinates of the model, `θ` is the fundamental
  weight `ω₁`: it pairs to `1` with the simple coroot `α₁^∨` and to `0` with the other six. So `θ`
  is dominant, and its stabilizer is the standard parabolic subgroup of the Coxeter system
  `TauCeti.weylCoxeterSystem` on the simple roots orthogonal to it
  (`RootPairing.parabolic_wallIndices_eq_stabilizer`). In the Bourbaki numbering these are
  `α₂, …, α₇`, of type `D₆`: read as `α₇, α₆, α₅, α₄, α₃, α₂`, they follow the Bourbaki numbering
  of `D₆`, with `α₂` the second branch node at `α₄`. Along them the Coxeter matrix of `E₇`
  restricts to `CoxeterMatrix.D 6`, the Coxeter matrix of the Bourbaki-numbered Coxeter system
  `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem` of the pinned datum of type `D₆`, so
  `CoxeterSystem.parabolicHom` embeds that Weyl group into the Weyl group of `E₇` with image the
  parabolic subgroup (`CoxeterSystem.parabolicHom_injective`, `CoxeterSystem.range_parabolicHom`).
  That Weyl group is the Weyl group of the rational model of type `D₆`
  (`TauCeti.weylGroupBaseChangeEquiv`), so the stabilizer has order `2⁵ · 6! = 23040`
  (`RootPairing.card_weylGroup_of_hasCartanType_D`).

Hence the Weyl group has order `126 · 23040 = 2903040`.

## Main results

* `RootPairing.card_weylGroup_of_hasCartanType_E7`: **every finite reduced crystallographic root
  system over `ℚ` with a base of Cartan type `E₇` has Weyl group of order `2903040`.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.11 and Plate VI.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Sections 1.10, 1.12 and 2.11.
* S. Fomin and N. Reading, *Root systems and generalized associahedra*, arXiv:math/0505518v3,
  Lecture 2, §2.5, Figure 2.8.
-/

public section

namespace TauCeti.DynkinType

open RootPairing MulAction

local notation "P₇" => E7.rationalRootSystem valid_E7
local notation "b₇" => E7.rationalBase valid_E7

/-- The index of the highest root of `E₇` in the pinned root tables, the last positive root
(`TauCeti.DynkinType.highestRoot_e7SimplyConnectedBase`). -/
private def e7Theta : Fin E7.numRoots := ⟨62, by decide⟩

/-- The Bourbaki-numbered simple roots `α₇, α₆, α₅, α₄, α₃, α₂` of `E₇`, the walls through the
highest root, listed along the Bourbaki numbering of `D₆`. -/
private def e7WallNode (m : Fin (D 6).rank) : Fin E7.rank :=
  Fin.cast rank_E7.symm (![6, 5, 4, 3, 2, 1] (Fin.cast (rank_D 6) m))

/-- The walls through the highest root, as simple roots of the pinned rational base. -/
private noncomputable def e7Wall (m : Fin (D 6).rank) : (b₇).support :=
  E7.simpleSupportEquiv valid_E7 (e7WallNode m)

/-- In the fundamental-weight coordinates of the pinned datum the highest root of `E₇` is `ω₁`. -/
private lemma root_e7Theta (k : Fin E7.rank) :
    (E7.simplyConnectedRootDatum valid_E7).root e7Theta k = if (k : ℕ) = 0 then 1 else 0 := by
  rw [simplyConnectedRootDatum_E7, e7SimplyConnectedRootDatum_root]
  -- `e7Theta` is the index `62` of the table, read in `Fin E7.numRoots`
  refine (congrFun e7Root_apply_62 k).trans ?_
  fin_cases k <;> rfl

/-- **The highest root of `E₇` is the fundamental weight `ω₁`:** it pairs to `1` with the simple
coroot `α₁^∨` and to `0` with the other six. -/
private lemma coroot'_simpleSupportEquiv_root_e7Theta (k : Fin E7.rank) :
    (P₇).coroot' (E7.simpleSupportEquiv valid_E7 k) ((P₇).root e7Theta) =
      if (k : ℕ) = 0 then 1 else 0 := by
  rw [LinearMap.flip_apply, toLinearMap_rationalRootSystem, coe_simpleSupportEquiv,
    coroot_rationalRootSystem_simpleIndex, dotProduct_single, mul_one, root_rationalRootSystem,
    root_e7Theta]
  split_ifs <;> simp

/-- The highest root of `E₇` is dominant. -/
private lemma root_e7Theta_mem_dominantChamber : (P₇).root e7Theta ∈ dominantChamber P₇ b₇ := by
  refine (mem_dominantChamber_iff_forall_equiv P₇ b₇ (E7.simpleSupportEquiv valid_E7) _).mpr
    fun k ↦ ?_
  rw [coroot'_simpleSupportEquiv_root_e7Theta]
  split_ifs <;> norm_num

/-- The walls through the highest root of `E₇` are the simple roots `α₂, …, α₇`. -/
private lemma wallIndices_root_e7Theta :
    (P₇).wallIndices b₇ ((P₇).root e7Theta) = Set.range e7Wall := by
  ext i
  obtain ⟨k, rfl⟩ := (E7.simpleSupportEquiv valid_E7).surjective i
  simp only [mem_wallIndices, coroot'_simpleSupportEquiv_root_e7Theta, Set.mem_range, e7Wall,
    (E7.simpleSupportEquiv valid_E7).injective.eq_iff, ite_eq_right_iff, one_ne_zero, imp_false]
  revert k
  decide

/-- Along the `D₆` subdiagram of walls the Coxeter matrix of the `E₇` base is that of `D₆`. -/
private lemma coxeterMatrix_D_eq_coxeterMatrixOfBase_e7Wall (i j : Fin (D 6).rank) :
    (D 6).coxeterMatrix i j = coxeterMatrixOfBase P₇ b₇ (e7Wall i) (e7Wall j) := by
  rw [coxeterMatrixOfBase_eq_coxeterMatrix_reindex _ (E7.cartanMatrix_rationalBase_symm valid_E7),
    CoxeterMatrix.reindex_apply, Equiv.symm_symm, coxeterMatrix_D (by norm_num)]
  simp only [e7Wall, Equiv.symm_apply_apply, coxeterMatrix_E7]
  fin_cases i <;> fin_cases j <;> rfl

/-- The stabilizer of the highest root of `E₇` is a copy of the Weyl group of `D₆`, of order
`2⁵ · 6! = 23040`. -/
private lemma card_stabilizer_root_e7Theta :
    Nat.card (stabilizer (P₇).weylGroup ((P₇).root e7Theta)) = 23040 := by
  have hD : (D 6).Valid := valid_D.mpr (by norm_num)
  rw [← parabolic_wallIndices_eq_stabilizer P₇ b₇ root_e7Theta_mem_dominantChamber,
    wallIndices_root_e7Theta, ← CoxeterSystem.range_parabolicHom
      (simplyConnectedWeylCoxeterSystem (D 6) hD) coxeterMatrix_D_eq_coxeterMatrixOfBase_e7Wall,
    ← Nat.card_congr (MonoidHom.ofInjective (CoxeterSystem.parabolicHom_injective
      (simplyConnectedWeylCoxeterSystem (D 6) hD)
      coxeterMatrix_D_eq_coxeterMatrixOfBase_e7Wall)).toEquiv,
    Nat.card_congr (weylGroupBaseChangeEquiv ℚ _
      (toLinearMap_simplyConnectedRootDatum_apply_apply (D 6) hD)).toEquiv,
    ← rationalRootSystem_def,
    card_weylGroup_of_hasCartanType_D (by norm_num) ((D 6).hasCartanType_rationalRootSystem hD)]
  rfl

/-- The Weyl group of the pinned rational root system of type `E₇` has order `2903040`, the `126`
roots in the orbit of the highest root times the `2⁵ · 6!` elements of its stabilizer. -/
private theorem card_weylGroup_rationalRootSystem_E7 : Nat.card (P₇).weylGroup = 2903040 := by
  have hsl : (b₇).cartanMatrix.IsSimplyLaced :=
    ((E7.hasCartanType_rationalRootSystem valid_E7).isSimplyLaced_iff).mpr (.inl isSimplyLaced_E7)
  rw [(b₇).card_weylGroup_eq_card_mul_card_stabilizer_of_isSimplyLaced hsl e7Theta,
    card_stabilizer_root_e7Theta, Nat.card_fin, numRoots_E7]

end TauCeti.DynkinType

namespace RootPairing

open TauCeti TauCeti.DynkinType

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N) [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- **The Weyl group of type `E₇` has order `2903040`**: every finite reduced crystallographic root
system over `ℚ` with a base of Cartan type `E₇` has Weyl group of order
`2903040 = 2¹⁰ · 3⁴ · 5 · 7`. -/
theorem card_weylGroup_of_hasCartanType_E7 (h : HasCartanType P b .E7) :
    Nat.card P.weylGroup = 2903040 := by
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b (E7.rationalBase valid_E7) .E7 h
    (E7.hasCartanType_rationalRootSystem valid_E7)
  rw [Nat.card_congr e.toEquiv, card_weylGroup_rationalRootSystem_E7]

end RootPairing
