/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Cycle
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Classification of positive-degree cyclic quotients of preprojective algebras

Let `G` be a connected finite simple graph, `o` an orientation of `G`, and `k` a commutative
coefficient ring. The cyclic quotient `Π / [Π, Π]` of either the signless preprojective algebra
`Π⁺_k(G)` or the additive preprojective algebra `Π_k(OrientedQuiver G o)` inherits the path-length
grading from the doubled path algebra, and its positive-degree pieces control cyclic traces of
closed walks and, in the Koszul-dual picture of Liu and Wang, second Hochschild cohomology classes
of Ginzburg and zigzag algebras.

This file assembles the type-specific `A`, `D`, and `E` calculations, the bad-characteristic
necklace witnesses, the affine tree representations, and the cycle-shift representations into the
complete classification of when the positive-degree cyclic quotient vanishes:

1. **Good characteristic on Dynkin diagrams** (`CommRing k`): if `G` is isomorphic to the
   underlying simple graph of a standard Dynkin diagram `t` and every bad prime of `t` (`none` in
   type `A`, `2` in type `D`, `2, 3` in `E₆` and `E₇`, `2, 3, 5` in `E₈`) is invertible in `k`,
   then every positive-degree homogeneous piece (`d ≥ 1`) of both `Π⁺_k(G)` and
   `Π_k(OrientedQuiver G o)` lies in the commutator submodule.
2. **Bad characteristic on valid Dynkin diagrams** (`CommRing k`, `Nontrivial k`): if `t` is a
   valid Dynkin diagram, `p` is a bad prime of `t`, and `(p : k) = 0`, then both `Π⁺_k(G)` and
   `Π_k(OrientedQuiver G o)` have a homogeneous element outside the commutator submodule in path
   degree `4` (`p = 2`), `6` (`p = 3`), or `10` (`p = 5`).
3. **Connected non-Dynkin graphs** (`CommRing k`, `Nontrivial k`): if `G` is connected and not
   isomorphic to the diagram of any valid Dynkin type, then `G` is either a non-Dynkin tree
   (containing an affine `D̃ₙ`, `Ẽ₆`, `Ẽ₇`, or `Ẽ₈` copy, giving a witness in degree `4`, `6`, `8`,
   or `12`) or fails to be acyclic (containing a simple cycle of length `m ≥ 3`, giving a witness
   in degree `m ≥ 3`), so both `Π⁺_k(G)` and `Π_k(OrientedQuiver G o)` have a nonzero cyclic class
   in some path degree `d ≥ 3`.
4. **Complete dichotomy over a field** (`Field k`): for a connected finite simple graph `G`, the
   cyclic quotient of `Π_k(OrientedQuiver G o)` (or of `Π⁺_k(G)`) vanishes in all degrees `d ≥ 3`
   — equivalently, in all positive degrees `d ≥ 1` — if and only if `G` is isomorphic to the
   diagram of a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad prime of `t`.

## Main definitions and results

* `TauCeti.IsBadPrime`: the preprojective bad-prime predicate on `DynkinType × ℕ` (`2` for `D`,
  `2, 3` for `E₆, E₇`, `2, 3, 5` for `E₈`, and `False` otherwise).
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: positive-degree vanishing on any
  graph isomorphic to a Dynkin diagram when its bad primes are units in `k`.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: nonzero cyclic
  classes in degree `4`, `6`, or `10` at a vanishing bad prime.
* `exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`
  and
  `exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso`:
  nonzero cyclic classes in degree `d ≥ 3` for every connected non-Dynkin finite simple graph.
* `TauCeti.preprojective_cyclicQuotient_vanishes_iff` and
  `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_iff`: **the complete field-valued
  vanishing characterization in path degrees `d ≥ 3`**, with positive-degree (`0 < d`) companions
  `TauCeti.forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff` and
  `TauCeti.forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff`.

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 218
  (2008), https://arxiv.org/abs/0704.3278, for the torsion primes (`2` in `D`, `2, 3` in `E₆, E₇`,
  `2, 3, 5` in `E₈`) in the zeroth Hochschild homology of ADE preprojective algebras and the
  infinite-type nonvanishing.
* P. Etingof and E. Rains, *Central extensions of preprojective algebras, the quantum Heisenberg
  algebra, and 2-dimensional complex reflection groups*, Moscow Math. J. 6 (2006),
  https://arxiv.org/abs/math/0503393, for the dual central-extension filtration in good and bad
  characteristics.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Section 3, for the application to zigzag algebras.
* R. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246 (2001),
  https://arxiv.org/abs/math/0002060, Section 3, for the signless comparison on bipartite graphs.
-/

public section

namespace TauCeti

open _root_.SimpleGraph DoubledQuiver

/-! ### Bad primes of simply-laced Dynkin diagrams -/

/-- **Bad primes for positive-degree cyclic quotients of preprojective algebras.**
For simply-laced Dynkin types these are `none` in type `A`, `2` in type `D`, `2` and `3` in `E₆`
and `E₇`, and `2`, `3`, and `5` in `E₈`. Non-simply-laced types (`B`, `C`, `F₄`, `G₂`) are mapped
to `False`: their unweighted `diagramGraph` forgets edge multiplicities and is a path graph of type
`A`, so this predicate records the preprojective bad primes of unweighted ADE diagrams rather than
root-system torsion primes of multiply-laced types. -/
def IsBadPrime (t : DynkinType) (p : ℕ) : Prop :=
  match t with
  | .A _ | .B _ | .C _ | .F4 | .G2 => False
  | .D _ => p = 2
  | .E6 | .E7 => p = 2 ∨ p = 3
  | .E8 => p = 2 ∨ p = 3 ∨ p = 5

instance : DecidableRel IsBadPrime := fun t p =>
  match t with
  | .A _ | .B _ | .C _ | .F4 | .G2 => inferInstanceAs (Decidable False)
  | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))

@[simp] theorem isBadPrime_A (n p : ℕ) : ¬ IsBadPrime (.A n) p := id
@[simp] theorem isBadPrime_B (n p : ℕ) : ¬ IsBadPrime (.B n) p := id
@[simp] theorem isBadPrime_C (n p : ℕ) : ¬ IsBadPrime (.C n) p := id
@[simp] theorem isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p := id
@[simp] theorem isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p := id
@[simp] theorem isBadPrime_D (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_E6 (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E7 (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E8 (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl

/-- Every bad prime of a Dynkin diagram is a prime number (`2`, `3`, or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) : Nat.Prime p := by
  cases t <;> simp only [isBadPrime_A, isBadPrime_B, isBadPrime_C, isBadPrime_F4, isBadPrime_G2,
    isBadPrime_D, isBadPrime_E6, isBadPrime_E7, isBadPrime_E8] at h
  all_goals rcases h with rfl | rfl | rfl <;> decide

/-- Only simply-laced Dynkin types have bad primes under `IsBadPrime`. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- Zero is never a bad prime; in particular `ringChar k` is never bad in characteristic zero. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 :=
  fun h => Nat.not_prime_zero h.prime

/-- No prime larger than `5` is bad for any Dynkin diagram. -/
theorem not_isBadPrime_of_gt_five {t : DynkinType} {p : ℕ} (hp : 5 < p) : ¬ IsBadPrime t p := by
  cases t <;> simp <;> omega

/-! ### Graph-isomorphism and bipartiteness transport helpers -/

section Transport

variable {k : Type*} [CommRing k]

private theorem signlessGrade_le_commutator_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (hH : signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  intro x hx
  let E := signlessPreprojectiveAlgebraEquiv k e
  have hEx := hH ((signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade k e).mpr hx)
  simpa only [E, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hEx

private theorem exists_signlessGrade_notMem_commutator_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) {d : ℕ}
    (hH : ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_contra! hG
  obtain ⟨x, hx, hx0⟩ := hH
  exact hx0 (signlessGrade_le_commutator_of_iso e.symm (fun y hy => hG y hy) hx)

private theorem exists_preprojectiveGrade_notMem_commutator_of_isBipartite {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hb : G.IsBipartite)
    (o : Orientation G) {d : ℕ}
    (hG : ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_contra! ho
  obtain ⟨x, hx, hx0⟩ := hG
  exact hx0 (((hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mp fun y hy => ho y hy) hx)

private theorem diagramGraph_nonSimplyLaced_iso_A :
    (∀ n, Nonempty (diagramGraph (DynkinType.B n).cartanMatrix ≃g
        diagramGraph (DynkinType.A n).cartanMatrix)) ∧
      (∀ n, Nonempty (diagramGraph (DynkinType.C n).cartanMatrix ≃g
        diagramGraph (DynkinType.A n).cartanMatrix)) ∧
      Nonempty (diagramGraph DynkinType.F4.cartanMatrix ≃g
        diagramGraph (DynkinType.A 4).cartanMatrix) ∧
      Nonempty (diagramGraph DynkinType.G2.cartanMatrix ≃g
        diagramGraph (DynkinType.A 2).cartanMatrix) := by
  have isoOfEq {m : ℕ} {G₁ G₂ : SimpleGraph (Fin m)} (h : G₁ = G₂) : Nonempty (G₁ ≃g G₂) :=
    h ▸ ⟨SimpleGraph.Iso.refl⟩
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_⟩
  · simpa only [DynkinType.rank_B, DynkinType.cartanMatrix_B, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using isoOfEq (G₁ := diagramGraph (CartanMatrix.B n)) <| by
      ext i j
      rw [diagramGraph_adj, diagramGraph_adj]
      simp [CartanMatrix.B, CartanMatrix.A, Fin.ext_iff]
      omega
  · simpa only [DynkinType.rank_C, DynkinType.cartanMatrix_C, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using isoOfEq (G₁ := diagramGraph (CartanMatrix.C n)) <| by
      ext i j
      rw [diagramGraph_adj, diagramGraph_adj]
      simp [CartanMatrix.C, CartanMatrix.A, Fin.ext_iff]
      omega
  · simpa only [DynkinType.rank_F4, DynkinType.cartanMatrix_F4, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using isoOfEq (G₁ := diagramGraph CartanMatrix.F₄) <| by
      ext i j
      rw [diagramGraph_adj, diagramGraph_adj]
      fin_cases i <;> fin_cases j <;> decide
  · simpa only [DynkinType.rank_G2, DynkinType.cartanMatrix_G2, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using
      isoOfEq (G₁ := diagramGraph CartanMatrix.G₂.transpose) <| by
      ext i j
      rw [diagramGraph_adj, diagramGraph_adj]
      fin_cases i <;> fin_cases j <;> decide

end Transport

/-! ### Good-characteristic vanishing on Dynkin diagrams -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

/-- **Good-characteristic vanishing for signless preprojective algebras of Dynkin diagrams.**
If `G` is isomorphic to the underlying graph of a standard Dynkin diagram `t` and every bad prime
of `t` is invertible in `k`, then every positive-degree homogeneous piece of `Π⁺_k(G)` lies in the
commutator submodule. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) (hgood : ∀ p, IsBadPrime t p → IsUnit (p : k))
    {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨hB, hC, ⟨fF4⟩, ⟨fG2⟩⟩ := diagramGraph_nonSimplyLaced_iso_A
  cases t with
  | A n =>
    exact signlessGrade_le_commutator_of_iso e
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | B n =>
    obtain ⟨f⟩ := hB n
    exact signlessGrade_le_commutator_of_iso (e.trans f)
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | C n =>
    obtain ⟨f⟩ := hC n
    exact signlessGrade_le_commutator_of_iso (e.trans f)
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | F4 =>
    exact signlessGrade_le_commutator_of_iso (e.trans fF4)
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | G2 =>
    exact signlessGrade_le_commutator_of_iso (e.trans fG2)
      (signlessPreprojectiveGrade_A_le_commutatorSubmodule k hd)
  | D n =>
    exact signlessGrade_le_commutator_of_iso e
      (signlessPreprojectiveGrade_D_le_commutatorSubmodule k (hgood 2 (by simp)) hd)
  | E6 =>
    exact signlessGrade_le_commutator_of_iso e
      (signlessPreprojectiveGrade_E6_le_commutatorSubmodule k
        (hgood 2 (by simp)) (hgood 3 (by simp)) hd)
  | E7 =>
    exact signlessGrade_le_commutator_of_iso e
      (signlessPreprojectiveGrade_E7_le_commutatorSubmodule k
        (hgood 2 (by simp)) (hgood 3 (by simp)) hd)
  | E8 =>
    have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
        signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
          commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
      rintro H rfl
      exact signlessPreprojectiveGrade_E8_le_commutatorSubmodule k
        (hgood 2 (by simp)) (hgood 3 (by simp)) (hgood 5 (by simp)) hd
    exact signlessGrade_le_commutator_of_iso e (key _ zigzagE8Graph_eq_diagramGraph)

/-- **Good-characteristic vanishing for oriented preprojective algebras of Dynkin diagrams.**
If `G` is isomorphic to the underlying graph of a standard Dynkin diagram `t` and every bad prime
of `t` is invertible in `k`, then for every orientation `o` of `G` and every `d > 0`, the degree-`d`
piece of `Π_k(OrientedQuiver G o)` lies in the commutator submodule. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix)
    (hgood : ∀ p, IsBadPrime t p → IsUnit (p : k)) (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mpr
    (signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e hgood hd)

end GoodCharacteristic

/-! ### Bad-characteristic nonvanishing on valid Dynkin diagrams -/

section BadCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

private theorem exists_signlessGrade_E_notMem_of_eq {n d : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : C = CartanMatrix.E n)
    (hE : ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph (CartanMatrix.E n))) d,
      x ∉ commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E n))))) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph C)) d,
      x ∉ commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
  subst hC
  exact exists_signlessGrade_notMem_commutator_of_iso SimpleGraph.Iso.refl hE

variable [Nontrivial k]

private theorem exists_signlessGrade_E_two_or_three {V : Type*} [Finite V] {G : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] {n : ℕ} (hn : 6 ≤ n) {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : C = CartanMatrix.E n) (e : G ≃g diagramGraph C) {p : ℕ} (h23 : p = 2 ∨ p = 3)
    (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
        x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rcases h23 with rfl | rfl
  · exact ⟨4, by simp, exists_signlessGrade_notMem_commutator_of_iso e
      (exists_signlessGrade_E_notMem_of_eq k hC
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule
          k (by omega) (by simpa using hp)))⟩
  · exact ⟨6, by simp, exists_signlessGrade_notMem_commutator_of_iso e
      (exists_signlessGrade_E_notMem_of_eq k hC
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule
          k hn (by simpa using hp)))⟩

/-- **At a vanishing bad prime, the signless preprojective algebra of a valid Dynkin diagram has a
nonzero cyclic class in degree `4`, `6`, or `10`.** Specifically, `p = 2` produces a witness in
degree `4` (`Dₙ` with `n ≥ 4`, `E₆`, `E₇`, `E₈`), `p = 3` in degree `6` (`E₆`, `E₇`, `E₈`), and
`p = 5` in degree `10` (`E₈`). -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    {p : ℕ} (hbad : IsBadPrime t p) (hp : (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
        x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  cases t with
  | A _ | B _ | C _ | F4 | G2 => simp at hbad
  | D n =>
    obtain rfl : p = 2 := by simpa using hbad
    exact ⟨4, by simp, exists_signlessGrade_notMem_commutator_of_iso e
      (exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule
        k (DynkinType.valid_D.mp ht) (by simpa using hp))⟩
  | E6 =>
    exact exists_signlessGrade_E_two_or_three k (by decide) DynkinType.cartanMatrix_E6 e
      (by simpa using hbad) hp
  | E7 =>
    exact exists_signlessGrade_E_two_or_three k (by decide) DynkinType.cartanMatrix_E7 e
      (by simpa using hbad) hp
  | E8 =>
    rcases (by simpa [or_assoc] using hbad : (p = 2 ∨ p = 3) ∨ p = 5) with h23 | rfl
    · exact exists_signlessGrade_E_two_or_three k (by decide) DynkinType.cartanMatrix_E8 e h23 hp
    · have key : ∀ H : SimpleGraph (Fin 8), zigzagE8Graph = H →
          ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) 10,
            x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
        rintro H rfl
        exact ⟨_, signlessWord_E8_cyclicWord_mem_grade_ten k,
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k (by simpa using hp)⟩
      exact ⟨10, by simp,
        exists_signlessGrade_notMem_commutator_of_iso e (key _ zigzagE8Graph_eq_diagramGraph)⟩

/-- **At a vanishing bad prime, the preprojective algebra of every orientation of a valid Dynkin
diagram has a nonzero cyclic class in degree `4`, `6`, or `10`.** -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) {p : ℕ} (hbad : IsBadPrime t p) (hp : (p : k) = 0)
    (o : Orientation G) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
        x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  obtain ⟨d, hd, hx⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hbad hp
  exact ⟨d, hd, exists_preprojectiveGrade_notMem_commutator_of_isBipartite hb o hx⟩

/-! ### Nonzero cyclic classes of connected non-Dynkin graphs -/

/-- **Every connected non-Dynkin finite simple graph has a nonzero cyclic class of path degree at
least three in its signless preprojective algebra** over every nontrivial commutative ring. -/
theorem
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [inst : ∀ i, Fintype (G.neighborSet i)]
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  by_cases hac : G.IsAcyclic
  · classical
    let _ := Fintype.ofFinite V
    have hinst : inst = fun v => Subtype.fintype (Membership.mem (G.neighborSet v)) :=
      Subsingleton.elim _ _
    cases hinst
    have htree : G.IsTree := ⟨hG, hac⟩
    obtain ⟨d, hd, hx⟩ :=
      htree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hD
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact ⟨d, hd3, hx⟩
  · exact exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac

/-- **Every connected non-Dynkin finite simple graph has a nonzero cyclic class of path degree at
least three in the additive preprojective algebra of every orientation** over every nontrivial
commutative ring. Notice that `G` need not be bipartite here (for instance on odd cycles). -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  by_cases hac : G.IsAcyclic
  · obtain ⟨d, hd3, hx⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
        k hG hD
    exact ⟨d, hd3, exists_preprojectiveGrade_notMem_commutator_of_isBipartite hac.isBipartite o hx⟩
  · exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic k hac o

end BadCharacteristic

/-! ### Complete vanishing theorems over a field -/

section Field

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [Field k]

private theorem isUnit_of_isBadPrime_of_not_ringChar {t : DynkinType}
    (hchar : ¬ IsBadPrime t (ringChar k)) (p : ℕ) (hp : IsBadPrime t p) :
    IsUnit (p : k) := by
  refine isUnit_iff_ne_zero.mpr fun hp0 => hchar ?_
  rwa [CharP.ringChar_of_prime_eq_zero hp.prime hp0]

/-- **The positive-degree cyclic quotient dichotomy for signless preprojective algebras.**
For a connected finite simple graph `G` and a field `k`, every homogeneous piece of path degree
`d ≥ 3` of `Π⁺_k(G)` lies in `[Π⁺_k(G), Π⁺_k(G)]` if and only if `G` is isomorphic to the diagram of
a valid simply-laced Dynkin type `t` and `ringChar k` is not a bad prime of `t`. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hvan => ?_, fun ⟨t, _, _, ⟨e⟩, hchar⟩ d hd => ?_⟩
  · have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
      by_contra fun hnotD => by
      obtain ⟨d, hd3, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
          k hG hnotD
      exact hx0 (hvan d hd3 hx)
    obtain ⟨t₀, ht₀, ⟨e₀⟩⟩ := hD
    obtain ⟨t, hsl, hval, ⟨f⟩⟩ := t₀.exists_isSimplyLaced_diagramGraph_iso
    have ht : t.Valid := hval ht₀
    let e : G ≃g diagramGraph t.cartanMatrix := e₀.trans f
    refine ⟨t, ht, hsl, ⟨e⟩, fun hbad => ?_⟩
    obtain ⟨d, hd, x, hx, hx0⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
        k ht e hbad ringChar.Nat.cast_ringChar
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx0 (hvan d hd3 hx)
  · exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e
      (isUnit_of_isBadPrime_of_not_ringChar k hchar) (by omega)

/-- **The positive-degree cyclic quotient theorem for preprojective algebras.**
For a connected finite simple graph `G`, an orientation `o` of `G`, and a field `k`, the cyclic
quotient `Π / [Π, Π]` of `Π = preprojectiveAlgebra k (OrientedQuiver G o)` vanishes in all path
degrees `d ≥ 3` if and only if `G` is isomorphic to the diagram of a valid simply-laced Dynkin
type `t` and `ringChar k` is not a bad prime of `t` (`none` in type `A`, `2` in type `D`, `2, 3`
in `E₆, E₇`, `2, 3, 5` in `E₈`). -/
theorem preprojective_cyclicQuotient_vanishes_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hvan => ?_, fun ⟨t, _, _, ⟨e⟩, hchar⟩ d hd => ?_⟩
  · have hD : ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      by_contra hnotD
      obtain ⟨d, hd3, x, hx, hx0⟩ :=
        exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_exists_dynkinType_iso
          k hG hnotD o
      exact hx0 (hvan d hd3 hx)
    obtain ⟨t₀, _, ⟨e₀⟩⟩ := hD
    have hb : G.IsBipartite :=
      (e₀.isAcyclic_iff.mpr t₀.isAcyclic_diagramGraph_cartanMatrix).isBipartite
    exact (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp fun d hd =>
      (hb.preprojectiveGrade_le_commutatorSubmodule_iff k o d).mp (hvan d hd)
  · exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e
      (isUnit_of_isBadPrime_of_not_ringChar k hchar) o (by omega)

/-- **Vanishing of all positive-degree pieces (`0 < d`) of the signless cyclic quotient** has the
same ADE-and-good-characteristic criterion as vanishing in degrees `d ≥ 3`: degrees `1` and `2`
never create additional obstructions on a connected finite simple graph. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 0 < d → signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hvan => (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp
    fun d hd => hvan d (by omega), fun ⟨t, _, _, ⟨e⟩, hchar⟩ d hd => ?_⟩
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k e
    (isUnit_of_isBadPrime_of_not_ringChar k hchar) hd

/-- **Vanishing of all positive-degree pieces (`0 < d`) of the oriented preprojective cyclic
quotient** has the same ADE-and-good-characteristic criterion as vanishing in degrees `d ≥ 3`. -/
theorem forall_pos_preprojectiveGrade_le_commutatorSubmodule_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d → preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun hvan => (preprojective_cyclicQuotient_vanishes_iff k hG o).mp
    fun d hd => hvan d (by omega), fun ⟨t, _, _, ⟨e⟩, hchar⟩ d hd => ?_⟩
  exact preprojectiveGrade_le_commutatorSubmodule_of_iso k e
    (isUnit_of_isBadPrime_of_not_ringChar k hchar) o hd

end Field

end TauCeti
