/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Symmetry

/-!
# Irreducible rigidity and simple-root orbits of based automorphisms

Let `P` be an irreducible finite reduced crystallographic root system over a characteristic-zero
integral domain, `b` a base of `P`, and `σ : P.Aut` an automorphism carrying `b.support` into itself
(`∀ i ∈ b.support, σ.indexEquiv i ∈ b.support`, equivalently `σ ∈ b.basedAut` by
`RootPairing.Base.mem_basedAut_iff_forall_mem_support`). Restricting `σ.indexEquiv` to `b.support`
gives a Cartan-matrix symmetry `RootPairing.Base.supportPerm b hσ ∈ matrixSymmetryGroup
b.cartanMatrix`. Since `P` is irreducible, its Cartan matrix is connected and of finite type, so the
matrix-symmetry theorems of `TauCeti.LinearAlgebra.RootSystem.FiniteType.Symmetry` classify the
action of `σ` on the simple roots:

1. **Multiple-edge rigidity.** If `b.cartanMatrix` is not simply laced (`Bₙ` for `2 ≤ n`, `Cₙ` for
   `3 ≤ n`, `F₄`, or `G₂`), then `b.basedAut = ⊥`
   (`RootPairing.Base.basedAut_eq_bot_of_not_isSimplyLaced`) and `σ = 1`
   (`RootPairing.eq_one_of_not_isSimplyLaced` and
   `RootPairing.indexEquiv_eq_self_of_multiple_edge`).
2. **Simply-laced simple-orbit dichotomy.** If `b.cartanMatrix` is simply laced, then either the
   roots within each simple `σ`-orbit are pairwise orthogonal (`P.pairing i j = 0` for
   `i ∈ b.support` and `j ∈ P.orbitIndices σ i` with `i ≠ j`), matching Stembridge's folding
   condition as introduced in `TauCeti.LinearAlgebra.RootSystem.OrbitSum`, or `b` reindexes onto
   `DynkinType.A (2 * n)` (`1 ≤ n`) with `σ` reversing the chain of simple roots
   (`RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even`). In that exceptional even-`A` reversal
   case, the adjacent middle pair `{e.symm ⟨n - 1, _⟩, e.symm ⟨n, _⟩}` is the unique non-orthogonal
   simple orbit and has Cartan pairing `-1`
   (`RootPairing.Base.pairing_ne_zero_of_mem_orbitIndices_of_typeA_even_iff`,
   `RootPairing.Base.pairingIn_middle_eq_neg_one_of_typeA_even`, and
   `RootPairing.Base.pairing_middle_eq_neg_one_of_typeA_even`).

## Main results

* `RootPairing.Base.mem_orbitIndices_iff_sameCycle_supportPerm`: two simple roots lie in the same
  `P.orbitIndices σ`-orbit exactly when they lie in the same cycle of `b.supportPerm hσ`.
* `RootPairing.Base.basedAut_eq_bot_of_not_isSimplyLaced`,
  `RootPairing.eq_one_of_not_isSimplyLaced`, and
  `RootPairing.indexEquiv_eq_self_of_multiple_edge`: any based automorphism of an irreducible
  non-simply-laced root system is trivial.
* `RootPairing.simpleOrbit_pairingIn_eq_zero_or_typeA_even` and
  `RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even`: the simply-laced dichotomy between
  pairwise orthogonality within each simple `σ`-orbit and chain reversal of `A₂ₙ` (`1 ≤ n`).
* `RootPairing.Base.pairing_ne_zero_of_mem_orbitIndices_of_typeA_even_iff`,
  `RootPairing.Base.pairingIn_middle_eq_neg_one_of_typeA_even`, and
  `RootPairing.Base.pairing_middle_eq_neg_one_of_typeA_even`: in the `A₂ₙ` reversal case, the middle
  pair is the unique non-orthogonal simple orbit and pairs to `-1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5, Proposition 16 and §4.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1, condition (1).
-/

public section

open TauCeti

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

namespace Base

/-- Two simple roots lie in the same cycle of `b.supportPerm hσ` exactly when one belongs to the
root orbit `P.orbitIndices σ` of the other. -/
theorem mem_orbitIndices_iff_sameCycle_supportPerm [Finite ι] (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i j : b.support) :
    (j : ι) ∈ P.orbitIndices σ i ↔ (b.supportPerm hσ).SameCycle i j := by
  rw [mem_orbitIndices, sameCycle_supportPerm_iff_sameCycle]

/-! ## Non-simply-laced rigidity -/

/-- **If an irreducible finite reduced crystallographic root system has a non-simply-laced Cartan
matrix, its based automorphism group is trivial.** -/
theorem basedAut_eq_bot_of_not_isSimplyLaced [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] (b : P.Base)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : b.basedAut = ⊥ := by
  have : Nonempty ι := nonempty_of_isIrreducible P
  exact b.basedAut_eq_bot_of_matrixSymmetryGroup_eq_bot <|
    (isFiniteType_cartanMatrix b).matrixSymmetryGroup_eq_bot_of_not_isSimplyLaced
      (connected_diagramGraph_cartanMatrix b) hmultiple

end Base

/-- **A based automorphism of an irreducible finite reduced crystallographic root system over a
characteristic-zero domain is the identity whenever the Cartan matrix is not simply laced.** -/
theorem eq_one_of_not_isSimplyLaced (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : σ = 1 :=
  Subgroup.mem_bot.mp <|
    (b.basedAut_eq_bot_of_not_isSimplyLaced hmultiple).le
      (b.mem_basedAut_iff_forall_mem_support.mpr hσ)

/-- **A based automorphism of an irreducible finite reduced crystallographic root system over a
characteristic-zero domain fixes every root index if the Cartan matrix is not simply laced.** -/
theorem indexEquiv_eq_self_of_multiple_edge (P : RootPairing ι R M N) [Finite ι] [CharZero R]
    [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : ∀ i : ι, σ.indexEquiv i = i := by
  rw [eq_one_of_not_isSimplyLaced P b σ hσ hmultiple]
  exact fun _ ↦ rfl

/-! ## Simply-laced simple-orbit dichotomy and the even-`A` middle pair -/

/-- **Integral simple-orbit dichotomy for irreducible simply-laced root systems.** Either the roots
within each simple `σ`-orbit satisfy `P.pairingIn ℤ i j = 0` for distinct indices `i ≠ j`, or `b`
reindexes onto `DynkinType.A (2 * n)` (`1 ≤ n`) with `σ` reversing the numbered simple roots. -/
theorem simpleOrbit_pairingIn_eq_zero_or_typeA_even (P : RootPairing ι R M N) [Finite ι]
    [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    [P.IsIrreducible] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairingIn ℤ i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j : b.support, b.cartanMatrix i j =
          (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        (∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) := by
  have : Nonempty ι := nonempty_of_isIrreducible P
  rcases (isFiniteType_cartanMatrix b).orbit_apply_eq_zero_or_typeA_even
      (connected_diagramGraph_cartanMatrix b) hsimply
      (b.supportPerm_mem_matrixSymmetryGroup hσ) with horth | ⟨n, hn1, e, he, hrev⟩
  · left
    intro i hi j hjorb hne
    have hj : j ∈ b.support :=
      Eq.mp ((mem_orbitIndices.mp hjorb).apply_eq_of_apply_eq (f := (· ∈ b.support))
        fun z ↦ propext (b.indexEquiv_mem_support_iff hσ z)) hi
    have hcyc : (b.supportPerm hσ).SameCycle ⟨i, hi⟩ ⟨j, hj⟩ :=
      (b.mem_orbitIndices_iff_sameCycle_supportPerm hσ ⟨i, hi⟩ ⟨j, hj⟩).mp hjorb
    rw [← b.cartanMatrixIn_def ℤ ⟨i, hi⟩ ⟨j, hj⟩]
    exact horth ⟨i, hi⟩ ⟨j, hj⟩ hcyc (fun heq ↦ hne (congrArg Subtype.val heq))
  · right
    refine ⟨n, hn1, e, he, fun i j hij ↦ ?_⟩
    have hj : j = b.supportPerm hσ i :=
      Subtype.ext (hij.symm.trans (b.coe_supportPerm_apply hσ i).symm)
    rw [hj, hrev i]

/-- **In an irreducible simply-laced finite crystallographic root system, the roots within each
simple `σ`-orbit are pairwise orthogonal, except for the diagram reversal of even type `A₂ₙ`
(`1 ≤ n`).** In the exceptional case, `b.cartanMatrix` reindexes onto
`(DynkinType.A (2 * n)).cartanMatrix` along an equivalence `e : b.support ≃ Fin (2 * n)` under which
`σ` reverses the node labels. -/
theorem simpleOrbit_pairing_eq_zero_or_typeA_even (P : RootPairing ι R M N) [Finite ι]
    [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    [P.IsIrreducible] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j : b.support, b.cartanMatrix i j =
          (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        (∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) := by
  refine (simpleOrbit_pairingIn_eq_zero_or_typeA_even P b σ hσ hsimply).imp (fun horth ↦ ?_) id
  intro i hi j hj hne
  rw [← P.algebraMap_pairingIn ℤ i j, horth i hi j hj hne, map_zero]

namespace Base

/-- **In the even-`A₂ₙ` reversal case (`1 ≤ n`), the adjacent middle pair
`{e.symm ⟨n - 1, _⟩, e.symm ⟨n, _⟩}` is the unique non-orthogonal simple `σ`-orbit.** -/
theorem pairing_ne_zero_of_mem_orbitIndices_of_typeA_even_iff [Finite ι] [CharZero R]
    [P.IsCrystallographic] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)
    {i j : b.support} (hj : (j : ι) ∈ P.orbitIndices σ i) (hne : i ≠ j) :
    P.pairing (i : ι) (j : ι) ≠ 0 ↔
      (i = e.symm ⟨n - 1, by omega⟩ ∧ j = e.symm ⟨n, by omega⟩) ∨
        (i = e.symm ⟨n, by omega⟩ ∧ j = e.symm ⟨n - 1, by omega⟩) := by
  have hcyc_supp : (b.supportPerm hσ).SameCycle i j :=
    (b.mem_orbitIndices_iff_sameCycle_supportPerm hσ i j).mp hj
  have hcyc_A : (graphPermA (2 * n)).SameCycle (e i) (e j) :=
    hcyc_supp.map fun z ↦ by
      rw [graphPermA_apply]
      exact hrev z (b.supportPerm hσ z) (b.coe_supportPerm_apply hσ z).symm
  have hcartan : P.pairing (i : ι) (j : ι) ≠ 0 ↔ b.cartanMatrix i j ≠ 0 :=
    b.cartanMatrix_apply_eq_zero_iff_pairing.symm.not
  rw [hcartan, he i j,
    DynkinType.cartanMatrix_A_even_ne_zero_of_sameCycle_graphPermA_iff hn hcyc_A
      (e.injective.ne hne)]
  simp only [_root_.Equiv.eq_symm_apply]

/-- **The adjacent middle simple roots of `A₂ₙ` (`1 ≤ n`) have integral Cartan pairing `-1`.** -/
theorem pairingIn_middle_eq_neg_one_of_typeA_even [P.IsCrystallographic] (b : P.Base)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.pairingIn ℤ (e.symm ⟨n - 1, by omega⟩ : ι) (e.symm ⟨n, by omega⟩ : ι) = -1 := by
  have hmid := he (e.symm ⟨n - 1, by omega⟩) (e.symm ⟨n, by omega⟩)
  rw [cartanMatrix, cartanMatrixIn_def] at hmid
  rw [hmid]
  simp only [_root_.Equiv.apply_symm_apply, DynkinType.cartanMatrix_A, CartanMatrix.A,
    Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The adjacent middle simple roots of `A₂ₙ` (`1 ≤ n`) have scalar pairing `-1`.** -/
theorem pairing_middle_eq_neg_one_of_typeA_even [P.IsCrystallographic] (b : P.Base)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.pairing (e.symm ⟨n - 1, by omega⟩ : ι) (e.symm ⟨n, by omega⟩ : ι) = -1 := by
  rw [← P.algebraMap_pairingIn ℤ, b.pairingIn_middle_eq_neg_one_of_typeA_even hn e he, map_neg,
    map_one]

end Base

end RootPairing
