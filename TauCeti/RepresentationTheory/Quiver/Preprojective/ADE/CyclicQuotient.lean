/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicFive
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CharacteristicThree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.NonDynkin

/-!
# Vanishing of positive-degree cyclic quotients of preprojective algebras

Let `G` be a finite connected simple graph and `o` an orientation of `G` over a field `k`. This
file proves that the cyclic quotient `Π / [Π, Π]` of the additive preprojective algebra
`Π = Π_k(OrientedQuiver G o)` vanishes in all path degrees `d ≥ 3` — equivalently, in all positive
path degrees `d > 0` — if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t` (`TauCeti.IsBadPrime`):

* type `Aₙ`: no bad primes;
* type `Dₙ` (`n ≥ 4`): `p = 2`;
* types `E₆` and `E₇`: `p ∈ {2, 3}`;
* type `E₈`: `p ∈ {2, 3, 5}`.

The proof combines three ingredients over general commutative rings before specializing to a field:

1. **Good-characteristic ADE vanishing:** when `G ≃g diagramGraph t.cartanMatrix` for a simply-laced
   `t` and every bad prime of `t` is invertible in `k`, the normal-form calculations for types `A`,
   `D` and `E` transport along `TauCeti.signlessPreprojectiveAlgebraEquiv` and bipartite sign
   rescaling to place every positive-degree piece inside the commutator submodule.
2. **Bad-characteristic ADE classes:** over any nontrivial commutative ring in which a bad prime of
   a valid type `t` vanishes, induced `D₄` (`p = 2`, degree `4`), induced `E₆` (`p = 3`, degree
   `6`), and `E₈` (`p = 5`, degree `10`) necklace functionals produce homogeneous elements outside
   the commutator submodule.
3. **Connected non-Dynkin graphs:** by
   `TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient.NonDynkin`, every connected
   non-Dynkin graph has a nonzero cyclic class in some degree `d ≥ 3` over any nontrivial
   commutative ring.

## Main definitions

* `TauCeti.IsBadPrime`: the bad-prime predicate on `DynkinType` and `ℕ`.

## Main results

* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_iso`: positive-degree vanishing over a
  commutative ring in which every bad prime of `t` is a unit.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime` and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime`: nonzero cyclic
  classes in degrees `4`, `6` or `10` when a bad prime vanishes in `k`.
* `TauCeti.preprojective_cyclicQuotient_vanishes_iff` and
  `TauCeti.signlessPreprojective_cyclicQuotient_vanishes_iff`: **the complete vanishing dichotomy
  in degrees `d ≥ 3` (and in degrees `d > 0`) for connected finite simple graphs over a field.**

## References

* T. Schedler, *Hochschild homology of preprojective algebras over the integers*, Adv. Math. 214
  (2007), Theorem 13.1.1, https://arxiv.org/abs/math/0703488.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Math. Res. Lett. 14 (2007), https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1, Proposition 3.2 and Corollary 3.4, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

/-! ### Bad primes of finite Dynkin types -/

section BadPrime

/-- The primes that are bad for the positive-degree cyclic quotient of the preprojective algebra of
a finite Dynkin type (Schedler, Theorem 13.1.1; Liu--Wang, Theorem 1.1): `2` in type `D`, `2` and
`3` in types `E₆` and `E₇`, `2`, `3` and `5` in type `E₈`, and none in type `A` or in the
non-simply-laced types. Characteristic zero (`p = 0`) is never bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .D _, p => p = 2
  | .E6, p => p = 2 ∨ p = 3
  | .E7, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5
  | .A _, _ | .B _, _ | .C _, _ | .F4, _ | .G2, _ => False

instance : DecidableRel IsBadPrime := fun t p =>
  match t with
  | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))
  | .A _ | .B _ | .C _ | .F4 | .G2 => inferInstanceAs (Decidable False)

@[simp]
theorem not_isBadPrime_A (n p : ℕ) : ¬ IsBadPrime (.A n) p := by
  simp [IsBadPrime]

@[simp]
theorem not_isBadPrime_B (n p : ℕ) : ¬ IsBadPrime (.B n) p := by
  simp [IsBadPrime]

@[simp]
theorem not_isBadPrime_C (n p : ℕ) : ¬ IsBadPrime (.C n) p := by
  simp [IsBadPrime]

@[simp]
theorem isBadPrime_D_iff (n p : ℕ) : IsBadPrime (.D n) p ↔ p = 2 := by
  simp [IsBadPrime]

@[simp]
theorem isBadPrime_E6_iff (p : ℕ) : IsBadPrime .E6 p ↔ p = 2 ∨ p = 3 := by
  simp [IsBadPrime]

@[simp]
theorem isBadPrime_E7_iff (p : ℕ) : IsBadPrime .E7 p ↔ p = 2 ∨ p = 3 := by
  simp [IsBadPrime]

@[simp]
theorem isBadPrime_E8_iff (p : ℕ) : IsBadPrime .E8 p ↔ p = 2 ∨ p = 3 ∨ p = 5 := by
  simp [IsBadPrime]

@[simp]
theorem not_isBadPrime_F4 (p : ℕ) : ¬ IsBadPrime .F4 p := by
  simp [IsBadPrime]

@[simp]
theorem not_isBadPrime_G2 (p : ℕ) : ¬ IsBadPrime .G2 p := by
  simp [IsBadPrime]

/-- Every bad prime is a prime number (`2`, `3` or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) : p.Prime := by
  cases t <;> simp only [IsBadPrime] at h
  · subst h; exact Nat.prime_two
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · decide

/-- Only simply-laced Dynkin types have bad primes. -/
theorem IsBadPrime.isSimplyLaced {t : DynkinType} {p : ℕ} (h : IsBadPrime t p) :
    t.IsSimplyLaced := by
  cases t <;> simp_all

/-- Characteristic zero is never a bad prime for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ IsBadPrime t 0 := fun h =>
  Nat.not_prime_zero h.prime

/-- `1` is never a bad prime for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ IsBadPrime t 1 := fun h =>
  Nat.not_prime_one h.prime

/-- No integer strictly larger than `5` (in particular, no prime `p ≥ 7`) is bad for any Dynkin
type. -/
theorem not_isBadPrime_of_gt_five {t : DynkinType} {p : ℕ} (hp : 5 < p) : ¬ IsBadPrime t p := by
  cases t <;> simp [IsBadPrime] <;> omega

/-- Over a nontrivial semiring `R`, the ring characteristic of `R` is a bad prime for `t` if and
only if some bad prime of `t` casts to `0` in `R`. -/
theorem isBadPrime_ringChar_iff (R : Type*) [NonAssocSemiring R] [Nontrivial R] (t : DynkinType) :
    IsBadPrime t (ringChar R) ↔ ∃ p, IsBadPrime t p ∧ (p : R) = 0 := by
  refine ⟨fun h => ⟨ringChar R, h, CharP.cast_eq_zero R (ringChar R)⟩, ?_⟩
  rintro ⟨p, hp, hp0⟩
  rwa [CharP.ringChar_of_prime_eq_zero hp.prime hp0]

/-- Over a field `k`, every bad prime of `t` is invertible in `k` if and only if `ringChar k` is
not a bad prime for `t`. -/
theorem forall_isBadPrime_imp_isUnit_iff (k : Type*) [Field k] (t : DynkinType) :
    (∀ p, IsBadPrime t p → IsUnit (p : k)) ↔ ¬ IsBadPrime t (ringChar k) := by
  rw [isBadPrime_ringChar_iff]
  push Not
  refine forall₂_congr fun p _ => ?_
  exact isUnit_iff_ne_zero

end BadPrime

/-! ### Good-characteristic vanishing for ADE diagrams -/

section GoodCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

private theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_diagramGraph
    {t : DynkinType} (hsl : t.IsSimplyLaced)
    (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver (diagramGraph t.cartanMatrix)))
    (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver (diagramGraph t.cartanMatrix)) (ofPath x) ∈
      commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  cases t with
  | A n => exact signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k x hx
  | D n =>
    exact signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k (hunit 2 (by simp)) x hx
  | E6 =>
    exact signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k
      (hunit 2 (by simp)) (hunit 3 (by simp)) x hx
  | E7 =>
    exact signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k
      (hunit 2 (by simp)) (hunit 3 (by simp)) x hx
  | E8 =>
    have key : ∀ G : SimpleGraph (Fin 8), zigzagE8Graph = G →
        ∀ y : Quiver.TotalPath (DoubledQuiver G), 0 < y.2.2.length →
          signlessPreprojectiveMk k (DoubledQuiver G) (ofPath y) ∈
            commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
      rintro G rfl
      exact signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k
        (hunit 2 (by simp)) (hunit 3 (by simp)) (hunit 5 (by simp))
    exact key _ zigzagE8Graph_eq_diagramGraph x hx
  | B _ | C _ | F4 | G2 => simp at hsl

/-- If `G` is isomorphic to the diagram of a simply-laced Dynkin type `t` whose bad primes are
units in `k`, then every positive-length path of `DoubledQuiver G` maps into the commutator
submodule of `Π⁺(G)`. -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (x : Quiver.TotalPath (DoubledQuiver G)) (hx : 0 < x.2.2.length) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let φ := signlessPreprojectiveAlgebraEquiv k e
  have himg : φ (signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x)) ∈
      commutatorSubmodule k
        (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
    rw [signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk, pathAlgebraEquiv_ofPath]
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_diagramGraph k hsl hunit _
      (by rwa [Prefunctor.length_mapTotalPath])
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm himg

/-- If `G` is isomorphic to the diagram of a simply-laced Dynkin type `t` whose bad primes are
units in `k`, then every positive-degree piece of `Π⁺(G)` lies in the commutator submodule. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k hsl e hunit) hd

/-- If `G` is isomorphic to the diagram of a simply-laced Dynkin type `t` whose bad primes are
units in `k`, then the commutator submodule of `Π⁺(G)` equals the augmentation kernel. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := DoubledQuiver G) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k hsl e hunit)

/-- Over a nontrivial commutative ring in which every bad prime of a simply-laced Dynkin type `t`
is a unit, the cyclic quotient of `Π⁺(G)` for `G ≃g diagramGraph t.cartanMatrix` has rank `t.rank`.
-/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_of_iso [Nontrivial k]
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (hsl : t.IsSimplyLaced) (e : G ≃g diagramGraph t.cartanMatrix)
    (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k)) :
    Module.finrank k (cyclicQuotient k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) =
      t.rank := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k hsl e hunit),
    ← Nat.card_congr (vertexEquiv G), Nat.card_congr e.toEquiv, Nat.card_fin]

/-- If `G` is isomorphic to the diagram of a simply-laced Dynkin type `t` whose bad primes are
units in `k`, then every positive-length path in the doubled quiver of `OrientedQuiver G o` maps
into the commutator submodule of `Π_k(OrientedQuiver G o)`. -/
theorem preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} (hsl : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (o : Orientation G) (x : Quiver.TotalPath (_root_.Quiver.Symmetrify (OrientedQuiver G o)))
    (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver G o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact hb.coloringBool.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k hsl e hunit) x hx

/-- If `G` is isomorphic to the diagram of a simply-laced Dynkin type `t` whose bad primes are
units in `k`, then every positive-degree piece of `Π_k(OrientedQuiver G o)` lies in the commutator
submodule. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_iso
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} (hsl : t.IsSimplyLaced)
    (e : G ≃g diagramGraph t.cartanMatrix) (hunit : ∀ p, IsBadPrime t p → IsUnit (p : k))
    (o : Orientation G) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_ofPath_mem_commutatorSubmodule_of_iso k hsl e hunit o) hd

end GoodCharacteristic

/-! ### Bad-characteristic classes for ADE diagrams -/

section BadCharacteristic

attribute [local instance] SimpleGraph.neighborSetFintypeOfFinite

variable (k : Type*) [CommRing k]

private theorem exists_signless_notMem_of_eq {n d : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    (hG : G₁ = G₂)
    (h : ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G₁),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G₁) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G₁))) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G₂),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G₂) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G₂)) := by
  subst hG
  exact h

variable [Nontrivial k]

private theorem exists_signless_badPrime_diagramGraph {t : DynkinType} (ht : t.Valid)
    (hb : ∃ p, IsBadPrime t p ∧ (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ),
      ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix)),
        z ∈ signlessPreprojectiveGrade k (DoubledQuiver (diagramGraph t.cartanMatrix)) d ∧
          z ∉ commutatorSubmodule k
            (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  rcases hb with ⟨p, hp, hp0⟩
  cases t with
  | A _ | B _ | C _ | F4 | G2 => simp at hp
  | D n =>
    obtain rfl : p = 2 := by simpa using hp
    exact ⟨4, by simp, exists_mem_signlessPreprojectiveGrade_D_four_notMem_commutatorSubmodule k
      (DynkinType.valid_D.mp ht) (by simpa using hp0)⟩
  | E6 =>
    rcases isBadPrime_E6_iff p |>.mp hp with rfl | rfl
    · exact ⟨4, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E6.symm)
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
    · exact ⟨6, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E6.symm)
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
  | E7 =>
    rcases isBadPrime_E7_iff p |>.mp hp with rfl | rfl
    · exact ⟨4, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E7.symm)
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
    · exact ⟨6, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E7.symm)
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
  | E8 =>
    rcases isBadPrime_E8_iff p |>.mp hp with rfl | rfl | rfl
    · exact ⟨4, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E8.symm)
        (exists_mem_signlessPreprojectiveGrade_E_four_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
    · exact ⟨6, by simp, exists_signless_notMem_of_eq k
        (congrArg diagramGraph DynkinType.cartanMatrix_E8.symm)
        (exists_mem_signlessPreprojectiveGrade_E_six_notMem_commutatorSubmodule k
          (by omega) (by simpa using hp0))⟩
    · exact ⟨10, by simp, exists_signless_notMem_of_eq k zigzagE8Graph_eq_diagramGraph
        ⟨signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3],
          signlessWord_E8_cyclicWord_mem_grade_ten k,
          signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k (by simpa using hp0)⟩⟩

/-- If `G` is isomorphic to the diagram of a valid Dynkin type `t` and some bad prime of `t` casts
to `0` in a nontrivial commutative ring `k`, then `Π⁺(G)` has a homogeneous element of degree `4`,
`6` or `10` outside the commutator submodule. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)]
    {t : DynkinType} (ht : t.Valid) (e : G ≃g diagramGraph t.cartanMatrix)
    (hb : ∃ p, IsBadPrime t p ∧ (p : k) = 0) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨d, hd, z, hz_grade, hz_comm⟩ := exists_signless_badPrime_diagramGraph k ht hb
  let φ := signlessPreprojectiveAlgebraEquiv k e.symm
  refine ⟨d, hd, φ z,
    (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k e.symm).mpr hz_grade,
    fun hmem => hz_comm ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hmem

/-- If `G` is isomorphic to the diagram of a valid Dynkin type `t` and some bad prime of `t` casts
to `0` in a nontrivial commutative ring `k`, then for every orientation `o` of `G` the
preprojective algebra `Π_k(OrientedQuiver G o)` has a homogeneous element of degree `4`, `6` or
`10` outside the commutator submodule. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime
    {V : Type*} [Finite V] {G : SimpleGraph V} {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) (hb : ∃ p, IsBadPrime t p ∧ (p : k) = 0)
    (o : Orientation G) :
    ∃ d ∈ ({4, 6, 10} : Finset ℕ), ∃ z : preprojectiveAlgebra k (OrientedQuiver G o),
      z ∈ preprojectiveGrade k (OrientedQuiver G o) d ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨d, hd, z, hz_grade, hz_comm⟩ :=
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e hb
  have hbG : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  let C := hbG.coloringBool
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨d, hd, E z, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hz_grade,
    fun hmem => hz_comm ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm hmem

end BadCharacteristic

/-! ### The vanishing dichotomy over a field -/

section Field

variable (k : Type*) [Field k] {V : Type*} [Finite V] {G : SimpleGraph V}

/-- **The positive-degree cyclic quotient of a signless preprojective algebra.** For a connected
finite simple graph `G` over a field `k`, every graded piece of `Π⁺(G)` of path degree `d ≥ 3` lies
in the commutator submodule if and only if `G` is isomorphic to the diagram of a valid simply-laced
Dynkin type `t` and `ringChar k` is not a bad prime for `t`. -/
theorem signlessPreprojective_cyclicQuotient_vanishes_iff
    [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 3 ≤ d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ s : DynkinType, s.Valid ∧ Nonempty (G ≃g diagramGraph s.cartanMatrix) := by
      by_contra hnot
      obtain ⟨d, hd3, x, hx_grade, hx_comm⟩ :=
        hG.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot
      exact hx_comm (hvan d hd3 hx_grade)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ := (G.exists_valid_isSimplyLaced_dynkinType_iso_iff).mpr hD
    refine ⟨t, ht, hsl, ⟨e⟩, fun hb => ?_⟩
    obtain ⟨d, hd, x, hx_grade, hx_comm⟩ :=
      exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e
        ((isBadPrime_ringChar_iff k t).mp hb)
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx_comm (hvan d hd3 hx_grade)
  · rintro ⟨t, _, hsl, ⟨e⟩, hnb⟩ d hd3
    exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e
      ((forall_isBadPrime_imp_isUnit_iff k t).mpr hnb) (by omega)

/-- For a connected finite simple graph `G` over a field `k`, all positive-degree pieces (`d > 0`)
of `Π⁺(G)` lie in the commutator submodule under the exact same condition as the pieces of degree
`d ≥ 3`. -/
theorem forall_pos_signlessPreprojectiveGrade_le_commutatorSubmodule_iff
    [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ d : ℕ, 0 < d →
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h => (signlessPreprojective_cyclicQuotient_vanishes_iff k hG).mp
    fun d hd => h d (by omega), ?_⟩
  rintro ⟨t, _, hsl, ⟨e⟩, hnb⟩ d hd
  exact signlessPreprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e
    ((forall_isBadPrime_imp_isUnit_iff k t).mpr hnb) hd

/-- **The positive-degree cyclic quotient of a preprojective algebra** (Schedler, Theorem 13.1.1;
Liu--Wang, Corollary 3.4). Let `o` orient a finite connected simple graph `G` over a field `k`.
Every element of `Π = Π_k(OrientedQuiver G o)` of path degree `d ≥ 3` lies in the commutator
submodule `[Π, Π]` — so `(Π / [Π, Π])_d = 0` for all `d ≥ 3` — if and only if `G` is isomorphic to
`diagramGraph t.cartanMatrix` for a valid simply-laced Dynkin type `t` and `ringChar k` is not a
bad prime for `t`. -/
theorem preprojective_cyclicQuotient_vanishes_iff (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 3 ≤ d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  constructor
  · intro hvan
    have hD : ∃ s : DynkinType, s.Valid ∧ Nonempty (G ≃g diagramGraph s.cartanMatrix) := by
      by_contra hnot
      obtain ⟨d, hd3, x, hx_grade, hx_comm⟩ :=
        hG.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule (k := k) hnot o
      exact hx_comm (hvan d hd3 hx_grade)
    obtain ⟨t, ht, hsl, ⟨e⟩⟩ := (G.exists_valid_isSimplyLaced_dynkinType_iso_iff).mpr hD
    refine ⟨t, ht, hsl, ⟨e⟩, fun hb => ?_⟩
    obtain ⟨d, hd, x, hx_grade, hx_comm⟩ :=
      exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_isBadPrime k ht e
        ((isBadPrime_ringChar_iff k t).mp hb) o
    have hd3 : 3 ≤ d := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      omega
    exact hx_comm (hvan d hd3 hx_grade)
  · rintro ⟨t, _, hsl, ⟨e⟩, hnb⟩ d hd3
    exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e
      ((forall_isBadPrime_imp_isUnit_iff k t).mpr hnb) o (by omega)

/-- For any orientation `o` of a connected finite simple graph `G` over a field `k`, all
positive-degree pieces (`d > 0`) of `Π_k(OrientedQuiver G o)` lie in the commutator submodule under
the exact same condition as the pieces of degree `d ≥ 3`. -/
theorem forall_pos_preprojectiveGrade_orientedQuiver_le_commutatorSubmodule_iff
    (hG : G.Connected) (o : Orientation G) :
    (∀ d : ℕ, 0 < d →
      preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o))) ↔
      ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
        Nonempty (G ≃g diagramGraph t.cartanMatrix) ∧ ¬ IsBadPrime t (ringChar k) := by
  refine ⟨fun h => (preprojective_cyclicQuotient_vanishes_iff k hG o).mp
    fun d hd => h d (by omega), ?_⟩
  rintro ⟨t, _, hsl, ⟨e⟩, hnb⟩ d hd
  exact preprojectiveGrade_le_commutatorSubmodule_of_iso k hsl e
    ((forall_isBadPrime_imp_isUnit_iff k t).mpr hnb) o hd

end Field

end TauCeti
