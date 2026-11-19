/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
import TauCeti.Algebra.CharP.Lemmas

/-!
# The positive-degree cyclic quotient of a Dynkin preprojective algebra

Let `Π = Π_k(Q)` be the additive preprojective algebra of an orientation `Q` of the diagram of a
valid simply-laced Dynkin type `t` over a field `k`, graded by path length. This file proves that
the cyclic quotient `Π / [Π, Π]` vanishes in every degree `d ≥ 3` exactly when the characteristic
of `k` is not a bad prime of `t` (`TauCeti.DynkinType.IsBadPrime`): never for type `A`, `2` for
type `D`, `2` and `3` for `E₆` and `E₇`, and `2`, `3` and `5` for `E₈`.

The cyclic quotient is the zeroth Hochschild homology of `Π`. Liu and Wang identify its
degree-`(q + 2)` piece with the Hochschild cohomology `HH^{2,q}` of the two-dimensional Ginzburg
algebra of `Q`, so the vanishing in degrees `d ≥ 3` is the vanishing of `HH^{2,q}` for `q > 0`
which controls the `A∞` deformations of the zigzag algebra of the diagram.

The theorem assembles the type-by-type results. In good characteristic every piece of positive
degree consists of sums of commutators: for type `A` over every commutative ring, for type `D`
when `2` is a unit, and for `E₆`, `E₇`, `E₈` when `2`, `3` (and `5` for `E₈`) are units. In each
bad characteristic an explicit closed walk survives: a degree-four walk through an induced `D₄`
in characteristic two, a degree-six walk through an induced `E₆` in characteristic three, and a
degree-ten walk of `E₈` in characteristic five.

## Main results

* `TauCeti.preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime`: for a valid simply-laced
  Dynkin type `t`, every orientation of its diagram and every field `k`, the pieces of degree
  `d ≥ 3` of the preprojective algebra are spanned by commutators exactly when `ringChar k` is not
  a bad prime of `t`.

## References

* T. Schedler, *Zeroth Hochschild homology of preprojective algebras over the integers*,
  https://arxiv.org/abs/0704.3278, Theorem 13.1.1, for the torsion of the cyclic quotient of a
  Dynkin preprojective algebra over the integers.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Corollary 3.4 and Proposition 3.2, for the role of the
  cyclic quotient in the deformation theory of zigzag algebras.
-/

public section

namespace TauCeti

open DoubledQuiver

variable (k : Type*) [Field k]

/-- Every piece of path degree at least three of the preprojective algebra of the orientation `o`
of `G` is spanned by commutators. -/
private abbrev CyclicVanishes {n : ℕ} (G : SimpleGraph (Fin n)) (o : Orientation G) : Prop :=
  ∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
    commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))

variable {k}

/-- A class of degree at least three outside the commutators, in the preprojective algebras of all
orientations of a graph equal to `H`, refutes the vanishing for every orientation of `H`. The
type-`E` classes are stated for the graphs `diagramGraph (CartanMatrix.E n)` and
`zigzagE8Graph`, which are equal but not definitionally equal to `diagramGraph t.cartanMatrix`. -/
private theorem not_cyclicVanishes_of_eq {n d : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G = H)
    (o : Orientation H) (hd : 3 ≤ d)
    (h : ∀ o : Orientation G, ∃ z, z ∈ preprojectiveGrade k (OrientedQuiver G o) d ∧
      z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) :
    ¬ CyclicVanishes k H o := by
  subst hGH
  obtain ⟨z, hz, hz0⟩ := h o
  exact fun hv => hz0 (hv d hd hz)

/-- The vanishing of every piece of positive degree modulo commutators, for all orientations of a
graph equal to `H`, gives `CyclicVanishes` for every orientation of `H`. -/
private theorem cyclicVanishes_of_eq {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G = H)
    (o : Orientation H)
    (h : ∀ (o : Orientation G) (d : ℕ), 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) :
    CyclicVanishes k H o := by
  subst hGH
  exact fun d hd => h o d (by omega)

/-- The criterion for `Dₙ`, `n ≥ 4`: the bad characteristic is two. -/
private theorem cyclicVanishes_D_iff {n : ℕ} (hn : 4 ≤ n)
    (o : Orientation (diagramGraph (DynkinType.D n).cartanMatrix)) :
    CyclicVanishes k _ o ↔ ringChar k ≠ 2 :=
  ⟨fun h h2 => not_cyclicVanishes_of_eq rfl o (d := 4) (by norm_num)
      (exists_mem_preprojectiveGrade_D_four_notMem_commutatorSubmodule k hn
        (haveI := ringChar.of_eq h2; CharP.ofNat_eq_zero k 2)) h,
    fun h2 => cyclicVanishes_of_eq rfl o fun o _ hd =>
      preprojectiveGrade_D_le_commutatorSubmodule k o (isUnit_ofNat_of_ringChar_ne Nat.prime_two h2)
        hd⟩

/-- Characteristic two and characteristic three are bad for `Eₙ`, `n ≥ 6`. -/
private theorem not_cyclicVanishes_E {n : ℕ} (hn : 6 ≤ n) {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : CartanMatrix.E n = C) (o : Orientation (diagramGraph C))
    (h : ringChar k = 2 ∨ ringChar k = 3) : ¬ CyclicVanishes k _ o := by
  rcases h with h2 | h3
  · exact not_cyclicVanishes_of_eq (congrArg diagramGraph hC) o (d := 4) (by norm_num) fun o =>
      exists_mem_preprojectiveGrade_E_four_notMem_commutatorSubmodule k (by omega)
        (haveI := ringChar.of_eq h2; CharP.ofNat_eq_zero k 2) o
  · have := ringChar.of_eq h3
    exact not_cyclicVanishes_of_eq (congrArg diagramGraph hC) o (d := 6) (by norm_num) fun o =>
      exists_mem_preprojectiveGrade_E_six_notMem_commutatorSubmodule k hn o

/-- The criterion for `E₆`: the bad characteristics are two and three. -/
private theorem cyclicVanishes_E6_iff (o : Orientation (diagramGraph DynkinType.E6.cartanMatrix)) :
    CyclicVanishes k _ o ↔ ¬ (ringChar k = 2 ∨ ringChar k = 3) :=
  ⟨fun h hp => not_cyclicVanishes_E le_rfl DynkinType.cartanMatrix_E6.symm o hp h,
    fun hp => cyclicVanishes_of_eq rfl o fun o _ hd =>
      preprojectiveGrade_E6_le_commutatorSubmodule k o
        (isUnit_ofNat_of_ringChar_ne Nat.prime_two fun h => hp (.inl h))
        (isUnit_ofNat_of_ringChar_ne Nat.prime_three fun h => hp (.inr h)) hd⟩

/-- The criterion for `E₇`: the bad characteristics are two and three. -/
private theorem cyclicVanishes_E7_iff (o : Orientation (diagramGraph DynkinType.E7.cartanMatrix)) :
    CyclicVanishes k _ o ↔ ¬ (ringChar k = 2 ∨ ringChar k = 3) :=
  ⟨fun h hp => not_cyclicVanishes_E (by norm_num) DynkinType.cartanMatrix_E7.symm o hp h,
    fun hp => cyclicVanishes_of_eq rfl o fun o _ hd =>
      preprojectiveGrade_E7_le_commutatorSubmodule k o
        (isUnit_ofNat_of_ringChar_ne Nat.prime_two fun h => hp (.inl h))
        (isUnit_ofNat_of_ringChar_ne Nat.prime_three fun h => hp (.inr h)) hd⟩

/-- The criterion for `E₈`: the bad characteristics are two, three and five. -/
private theorem cyclicVanishes_E8_iff (o : Orientation (diagramGraph DynkinType.E8.cartanMatrix)) :
    CyclicVanishes k _ o ↔ ¬ (ringChar k = 2 ∨ ringChar k = 3 ∨ ringChar k = 5) := by
  refine ⟨fun h hp => ?_, fun hp => cyclicVanishes_of_eq zigzagE8Graph_eq_diagramGraph o
    fun o _ hd => preprojectiveGrade_E8_le_commutatorSubmodule k o
      (isUnit_ofNat_of_ringChar_ne Nat.prime_two fun h => hp (.inl h))
      (isUnit_ofNat_of_ringChar_ne Nat.prime_three fun h => hp (.inr (.inl h)))
      (isUnit_ofNat_of_ringChar_ne Nat.prime_five fun h => hp (.inr (.inr h))) hd⟩
  rcases hp with h2 | h3 | h5
  · exact not_cyclicVanishes_E (by norm_num) DynkinType.cartanMatrix_E8.symm o (.inl h2) h
  · exact not_cyclicVanishes_E (by norm_num) DynkinType.cartanMatrix_E8.symm o (.inr h3) h
  · exact not_cyclicVanishes_of_eq zigzagE8Graph_eq_diagramGraph o (d := 10) (by norm_num)
      (fun o => exists_mem_preprojectiveGrade_E8_ten_notMem_commutatorSubmodule k
        (haveI := ringChar.of_eq h5; CharP.ofNat_eq_zero k 5) o) h

/-- **The positive-degree cyclic quotient of a Dynkin preprojective algebra.** For a valid
simply-laced Dynkin type `t`, every orientation `o` of its diagram and every field `k`, every
element of path degree `d ≥ 3` of the preprojective algebra `Π_k(Q_o)` is a sum of commutators,
that is `(Π / [Π, Π])_d = 0` for all `d ≥ 3`, exactly when the characteristic of `k` is not a bad
prime of `t`. -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff_not_isBadPrime {t : DynkinType}
    (ht : t.Valid) (hs : t.IsSimplyLaced) (o : Orientation (diagramGraph t.cartanMatrix)) :
    (∀ d, 3 ≤ d → preprojectiveGrade k (OrientedQuiver (diagramGraph t.cartanMatrix) o) d ≤
      commutatorSubmodule k
        (preprojectiveAlgebra k (OrientedQuiver (diagramGraph t.cartanMatrix) o))) ↔
      ¬ t.IsBadPrime (ringChar k) := by
  cases t with
  | A n =>
    simpa using fun d hd => preprojectiveGrade_A_le_commutatorSubmodule k o (by omega : 0 < d)
  | D n =>
    rw [DynkinType.isBadPrime_D]
    exact cyclicVanishes_D_iff (DynkinType.valid_D.mp ht) o
  | E6 =>
    rw [DynkinType.isBadPrime_E6]
    exact cyclicVanishes_E6_iff o
  | E7 =>
    rw [DynkinType.isBadPrime_E7]
    exact cyclicVanishes_E7_iff o
  | E8 =>
    rw [DynkinType.isBadPrime_E8]
    exact cyclicVanishes_E8_iff o
  | B n | C n | F4 | G2 => simp at hs

end TauCeti
