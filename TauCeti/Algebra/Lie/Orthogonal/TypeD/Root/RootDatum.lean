/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Classification

/-!
# The roots of the split even orthogonal Lie algebra as a type-D root datum

The roots of the split even orthogonal Lie algebra relative to its diagonal Cartan are already
classified in coordinate form as `εᵢ - εⱼ`, `εᵢ + εⱼ`, and `-εᵢ - εⱼ`. This file indexes those
functionals by the full root enumeration of the pinned simply connected type-`D` root datum.

For a classical root vector `x`, the corresponding Cartan functional has diagonal coordinates
`x`. Evaluating it on the numbered Cartan generator associated to a simple root `αⱼ` therefore
gives the dot product `x · αⱼ`. These are exactly the fundamental-weight coordinates used by the
pinned root datum. The resulting enumeration is injective and exhausts every nonzero concrete
root.

## Main declarations

* `TauCeti.TypeDStd.typeDRootWeight`: the concrete Cartan root indexed by a root of the pinned
  type-`D` datum.
* `TauCeti.TypeDStd.typeDRootWeight_apply_cartanGenerator`: its coordinates on the numbered
  Cartan generators are the coordinates of the corresponding abstract root.
* `TauCeti.TypeDStd.rootSpace_typeDDiagonalCartan_ne_bot_iff_eq_typeDRootWeight`: every nonzero
  root of the concrete diagonal Cartan occurs exactly in this enumeration.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §12.1.
-/

public section

namespace TauCeti.TypeDStd

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- The concrete diagonal-Cartan functional indexed by the `k`-th root of the pinned type-`D`
root datum. Its diagonal coordinates are the corresponding classical root vector. -/
noncomputable def typeDRootWeight (n : ℕ) (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) :
    Module.Dual K (typeDDiagonalCartan K (Fin n)) :=
  typeDWeightEquiv (fun i => (DynkinType.typeDRootEquiv n hn k).1 i)

/-- The concrete root indexed by `k`, evaluated on the `j`-th numbered Cartan generator, is the
`j`-th fundamental-weight coordinate of the `k`-th root of the pinned type-`D` datum. -/
theorem typeDRootWeight_apply_cartanGenerator (n : ℕ) (hn : 4 ≤ n)
    [CharZero K]
    (k : Fin (2 * n * (n - 1))) (j : Fin n) :
    typeDRootWeight (K := K) n hn k
        ⟨cartanGenerator n hn j, cartanGenerator_mem_typeDDiagonalCartan n hn j⟩ =
      ((DynkinType.typeDSimplyConnectedRootDatum n hn).root k j : K) := by
  rw [typeDRootWeight, typeDWeightEquiv_apply,
    DynkinType.root_typeDSimplyConnectedRootDatum]
  simp only [val_cartanGenerator, typeDDiagonalMatrix_apply,
    typeDDiagonalValue_inl, eq_self, ite_true]
  norm_cast

/-- Distinct roots of the pinned type-`D` datum give distinct concrete Cartan functionals. -/
theorem typeDRootWeight_injective (n : ℕ) (hn : 4 ≤ n) [CharZero K] :
    Function.Injective (typeDRootWeight (K := K) n hn) := by
  intro k l hkl
  apply (DynkinType.typeDRootEquiv n hn).injective
  apply Subtype.ext
  apply_fun (typeDWeightEquiv (K := K)).symm at hkl
  have hcast :
      (fun i => ((DynkinType.typeDRootEquiv n hn k).1 i : K)) =
        fun i => ((DynkinType.typeDRootEquiv n hn l).1 i : K) := by
    simpa only [typeDRootWeight, LinearEquiv.symm_apply_apply] using hkl
  funext i
  exact_mod_cast congrFun hcast i

/-- Every functional in the concrete type-`D` root enumeration is nonzero. -/
theorem typeDRootWeight_ne_zero (n : ℕ) (hn : 4 ≤ n)
    [CharZero K] (k : Fin (2 * n * (n - 1))) :
    typeDRootWeight (K := K) n hn k ≠ 0 := by
  intro hk
  have hcoord := congrArg (typeDWeightEquiv (K := K)).symm hk
  have hzero : (fun i => ((DynkinType.typeDRootEquiv n hn k).1 i : K)) = 0 := by
    simpa only [typeDRootWeight, LinearEquiv.symm_apply_apply, map_zero] using hcoord
  have hsquare := (DynkinType.typeDRootEquiv n hn k).2
  have hroot : (DynkinType.typeDRootEquiv n hn k).1 = 0 := by
    funext i
    have hi : ((DynkinType.typeDRootEquiv n hn k).1 i : K) = 0 := by
      simpa using congrFun hzero i
    exact_mod_cast hi
  rw [hroot, dotProduct_zero] at hsquare
  norm_num at hsquare

private theorem typeDRootWeight_eq_typeDWeightSub_of_val_eq
    (n : ℕ) (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) {i j : Fin n}
    (hk : (DynkinType.typeDRootEquiv n hn k).1 = Pi.single i 1 - Pi.single j 1) :
    typeDRootWeight (K := K) n hn k = typeDWeightSub i j := by
  apply (typeDWeightEquiv (K := K)).symm.injective
  simp only [typeDRootWeight, LinearEquiv.symm_apply_apply, typeDWeightSub_def, map_sub,
    typeDWeightEquiv_symm_epsilon]
  funext a
  simp [hk, Pi.single_apply]

private theorem typeDRootWeight_eq_typeDWeightAdd_of_val_eq
    (n : ℕ) (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) {i j : Fin n}
    (hk : (DynkinType.typeDRootEquiv n hn k).1 = Pi.single i 1 + Pi.single j 1) :
    typeDRootWeight (K := K) n hn k = typeDWeightAdd i j := by
  apply (typeDWeightEquiv (K := K)).symm.injective
  simp only [typeDRootWeight, LinearEquiv.symm_apply_apply, typeDWeightAdd_def, map_add,
    typeDWeightEquiv_symm_epsilon]
  funext a
  simp [hk, Pi.single_apply]

private theorem typeDRootWeight_eq_neg_typeDWeightAdd_of_val_eq
    (n : ℕ) (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) {i j : Fin n}
    (hk : (DynkinType.typeDRootEquiv n hn k).1 = -(Pi.single i 1 + Pi.single j 1)) :
    typeDRootWeight (K := K) n hn k = -typeDWeightAdd i j := by
  apply (typeDWeightEquiv (K := K)).symm.injective
  simp only [typeDRootWeight, LinearEquiv.symm_apply_apply, map_neg, typeDWeightAdd_def,
    map_add, typeDWeightEquiv_symm_epsilon]
  funext a
  simp [hk, Pi.single_apply]

/-- Every root in the pinned type-`D` enumeration has a nontrivial root space in the concrete
split orthogonal Lie algebra. -/
theorem rootSpace_typeDRootWeight_ne_bot (n : ℕ) (hn : 4 ≤ n)
    [IsDomain K] [CharZero K] (k : Fin (2 * n * (n - 1))) :
    LieAlgebra.rootSpace (typeDDiagonalCartan K (Fin n))
      (typeDRootWeight n hn k) ≠ ⊥ := by
  apply (rootSpace_typeDDiagonalCartan_ne_bot_iff
    (by norm_num : (2 : K) ≠ 0) _ (typeDRootWeight_ne_zero n hn k)).mpr
  obtain ⟨i, j, hij, hk | hk | hk⟩ :=
    DynkinType.TypeDRoot.exists_eq_single_sub_or_add_or_neg_add
      (DynkinType.typeDRootEquiv n hn k)
  · exact ⟨i, j, hij, Or.inl (typeDRootWeight_eq_typeDWeightSub_of_val_eq n hn k hk)⟩
  · exact ⟨i, j, hij,
      Or.inr (Or.inl (typeDRootWeight_eq_typeDWeightAdd_of_val_eq n hn k hk))⟩
  · exact ⟨i, j, hij,
      Or.inr (Or.inr (typeDRootWeight_eq_neg_typeDWeightAdd_of_val_eq n hn k hk))⟩

private theorem exists_typeDRootWeight_eq_typeDWeightSub
    (n : ℕ) (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ k, typeDRootWeight (K := K) n hn k = typeDWeightSub i j := by
  let x : DynkinType.TypeDRoot n :=
    ⟨Pi.single i 1 - Pi.single j 1, by
      simp [dotProduct_sub, dotProduct_single, hij]⟩
  obtain ⟨k, hk⟩ := (DynkinType.typeDRootEquiv n hn).surjective x
  refine ⟨k, typeDRootWeight_eq_typeDWeightSub_of_val_eq n hn k ?_⟩
  exact congrArg Subtype.val hk

private theorem exists_typeDRootWeight_eq_typeDWeightAdd
    (n : ℕ) (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ k, typeDRootWeight (K := K) n hn k = typeDWeightAdd i j := by
  let x : DynkinType.TypeDRoot n :=
    ⟨Pi.single i 1 + Pi.single j 1, by
      simp [dotProduct_add, dotProduct_single, hij]⟩
  obtain ⟨k, hk⟩ := (DynkinType.typeDRootEquiv n hn).surjective x
  refine ⟨k, typeDRootWeight_eq_typeDWeightAdd_of_val_eq n hn k ?_⟩
  exact congrArg Subtype.val hk

private theorem exists_typeDRootWeight_eq_neg_typeDWeightAdd
    (n : ℕ) (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ k, typeDRootWeight (K := K) n hn k = -typeDWeightAdd i j := by
  let x : DynkinType.TypeDRoot n :=
    ⟨-(Pi.single i 1 + Pi.single j 1), by
      rw [neg_dotProduct_neg]
      simp [dotProduct_add, dotProduct_single, hij]⟩
  obtain ⟨k, hk⟩ := (DynkinType.typeDRootEquiv n hn).surjective x
  refine ⟨k, typeDRootWeight_eq_neg_typeDWeightAdd_of_val_eq n hn k ?_⟩
  exact congrArg Subtype.val hk

/-- **The nonzero roots of the concrete split diagonal Cartan are exactly the roots of the pinned
type-`D` root datum.** The index on the right is the datum's full root index, and
`typeDRootWeight_apply_cartanGenerator` identifies its fundamental-weight coordinates. -/
theorem rootSpace_typeDDiagonalCartan_ne_bot_iff_eq_typeDRootWeight
    (n : ℕ) (hn : 4 ≤ n) (chi : Module.Dual K (typeDDiagonalCartan K (Fin n)))
    [IsDomain K] [CharZero K] (hchi : chi ≠ 0) :
    LieAlgebra.rootSpace (typeDDiagonalCartan K (Fin n)) chi ≠ ⊥ ↔
      ∃ k, chi = typeDRootWeight n hn k := by
  constructor
  · intro hroot
    obtain ⟨i, j, hij, hchi | hchi | hchi⟩ :=
      (rootSpace_typeDDiagonalCartan_ne_bot_iff
        (by norm_num : (2 : K) ≠ 0) chi hchi).mp hroot
    · obtain ⟨k, hk⟩ := exists_typeDRootWeight_eq_typeDWeightSub (K := K) n hn hij
      exact ⟨k, hchi.trans hk.symm⟩
    · obtain ⟨k, hk⟩ := exists_typeDRootWeight_eq_typeDWeightAdd (K := K) n hn hij
      exact ⟨k, hchi.trans hk.symm⟩
    · obtain ⟨k, hk⟩ := exists_typeDRootWeight_eq_neg_typeDWeightAdd (K := K) n hn hij
      exact ⟨k, hchi.trans hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact rootSpace_typeDRootWeight_ne_bot (K := K) n hn k

end TauCeti.TypeDStd
