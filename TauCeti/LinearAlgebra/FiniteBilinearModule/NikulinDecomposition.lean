/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Relations
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.SmallRelations
public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
import TauCeti.Algebra.Group.Primary.Generators
import TauCeti.GroupTheory.Torsion

/-!
# Generator decompositions of finite quadratic modules

Nikulin's Proposition 1.8.1 writes every nondegenerate finite quadratic module as an orthogonal sum
of his generators: the odd cyclic modules `q_θ^{(p)}(p^k)`, the dyadic cyclic modules
`q_θ^{(2)}(2^k)`, and the rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)`. This file records
such a decomposition as data: a list of generator labels together with an isometry onto the
orthogonal sum of their modules.

The labels are the terms of `TauCeti.FiniteQuadraticModule.NikulinGenerator`. Each label names its
prime, rank, standard minimal-rank realization determinant `realizationDet` (and unit part
`realizationUnit`), and module, and the admissible labels, those with positive exponent and a unit
parameter, are exactly the labels whose module is nondegenerate and nontrivial. Labels are not
invariants: the same module has many decompositions, since `q_1^{(2)}(2) ≅ q_5^{(2)}(2)` and
`u^{(2)}(2) ⊕ u^{(2)}(2) ≅ v^{(2)}(2) ⊕ v^{(2)}(2)` (Nikulin's Proposition 1.8.2).

A decomposition records the order, Gauss-sum invariant, `p`-adic realization determinant product,
and generator rank (`AddGroup.rank`) of the module and of its `p`-primary components. It restricts
to the `p`-primary component: the generators with prime `p` decompose the `p`-primary component,
which is how quantities attached to the `p`-adic part of a discriminant form, such as the
determinant of a `p`-adic lattice realizing it, are read off a decomposition.

## Main definitions

* `TauCeti.FiniteQuadraticModule.NikulinGenerator`: the labels of Nikulin's generators, with
  their primes `NikulinGenerator.prime`, ranks `NikulinGenerator.rank`, realization determinants
  `NikulinGenerator.realizationDet` and unit parts `NikulinGenerator.realizationUnit`, modules
  `NikulinGenerator.toFiniteQuadraticModule` and the admissibility predicate
  `NikulinGenerator.IsAdmissible`.
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`: the orthogonal sum of the modules
  of a list of labels.
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGeneratorsAppendIsometry`,
  `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGeneratorsOfFnIsometry` and
  `TauCeti.FiniteQuadraticModule.primaryComponentOrthogonalSumNikulinGeneratorsIsometry`:
  the isometries splitting the orthogonal sum over a concatenation, identifying the sum over
  `List.ofFn f` with the orthogonal sum `pi`, and identifying the `p`-primary component of the sum
  with the sum of the generators of prime `p`.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition`: a list of admissible labels together with
  an isometry onto the orthogonal sum of their modules.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.primaryComponent`: the decomposition of the
  `p`-primary component by the generators with prime `p`.

## Main results

* `TauCeti.FiniteQuadraticModule.NikulinGenerator.isAdmissible_iff`: a label is admissible exactly
  when its module is nondegenerate and nontrivial.
* `TauCeti.FiniteQuadraticModule.nonempty_nikulinDecomposition_iff`: a finite quadratic module has
  a generator decomposition exactly when it is nondegenerate.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.natCard_eq`,
  `TauCeti.FiniteQuadraticModule.NikulinDecomposition.gaussSign_eq`,
  `TauCeti.FiniteQuadraticModule.NikulinDecomposition.rank_primaryComponent` and
  `TauCeti.FiniteQuadraticModule.NikulinDecomposition.rank_eq`: the order, Gauss-sum invariant, and
  generator ranks of a decomposed module.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.hasCyclicTwoSummand_of_mem`: a
  decomposition containing `q_θ^{(2)}(2)` witnesses `HasCyclicTwoSummand`.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_orthogonalSumNikulinGenerators_of_perm`: the
  orthogonal sum does not depend on the order of the labels.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.8.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

/-! ## Generator labels -/

/-- **Labels of Nikulin's generators** (Nikulin, Proposition 1.8.1): the odd cyclic module
`q_θ^{(p)}(p^k)` for an odd prime `p`, the dyadic cyclic module `q_θ^{(2)}(2^k)` for `k ≥ 1`, and
the two dyadic rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)`. A label is admissible
(`NikulinGenerator.IsAdmissible`) when its exponent is positive and its parameter `θ` is a unit at
its prime. -/
inductive NikulinGenerator where
  /-- The odd cyclic generator `q_θ^{(p)}(p^k)` on `ℤ/p^k`, with `b(x, y) = θxy/p^k`. -/
  | oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ)
  /-- The dyadic cyclic generator `q_θ^{(2)}(2^k)` on `ℤ/2^k`, with `q(x) = θx²/2^{k+1}`. -/
  | dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ)
  /-- The rank-two generator `u^{(2)}(2^k)` on `(ℤ/2^k)²`, with `q(x) = x₁x₂/2^k`. -/
  | dyadicU (k : ℕ)
  /-- The rank-two generator `v^{(2)}(2^k)` on `(ℤ/2^k)²`, with `q(x) = (x₁² + x₁x₂ + x₂²)/2^k`. -/
  | dyadicV (k : ℕ)

namespace NikulinGenerator

/-- The prime at which a generator is primary: `p` for `q_θ^{(p)}(p^k)` and `2` for the dyadic
generators. -/
def prime : NikulinGenerator → ℕ
  | oddCyclic p _ _ _ _ => p
  | dyadicCyclic _ _ _ => 2
  | dyadicU _ => 2
  | dyadicV _ => 2

@[simp]
theorem prime_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).prime = p := (rfl)

@[simp]
theorem prime_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) : (dyadicCyclic k hk θ).prime = 2 := (rfl)

@[simp]
theorem prime_dyadicU (k : ℕ) : (dyadicU k).prime = 2 := (rfl)

@[simp]
theorem prime_dyadicV (k : ℕ) : (dyadicV k).prime = 2 := (rfl)

/-- The prime of a generator is prime. -/
theorem prime_prime (g : NikulinGenerator) : g.prime.Prime := by
  cases g with
  | oddCyclic p k hp hodd θ => exact hp
  | _ => exact Nat.prime_two

/-- A label is **admissible** when its exponent is positive and its parameter is a unit at its
prime; by `NikulinGenerator.isAdmissible_iff` these are exactly the labels whose module is
nondegenerate and nontrivial. -/
def IsAdmissible : NikulinGenerator → Prop
  | oddCyclic p k _ _ θ => 0 < k ∧ ¬ (p : ℤ) ∣ θ
  | dyadicCyclic _ _ θ => Odd θ
  | dyadicU k => 0 < k
  | dyadicV k => 0 < k

@[simp]
theorem isAdmissible_oddCyclic_iff (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).IsAdmissible ↔ 0 < k ∧ ¬ (p : ℤ) ∣ θ := Iff.rfl

@[simp]
theorem isAdmissible_dyadicCyclic_iff (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).IsAdmissible ↔ Odd θ := Iff.rfl

@[simp]
theorem isAdmissible_dyadicU_iff (k : ℕ) : (dyadicU k).IsAdmissible ↔ 0 < k := Iff.rfl

@[simp]
theorem isAdmissible_dyadicV_iff (k : ℕ) : (dyadicV k).IsAdmissible ↔ 0 < k := Iff.rfl

/-- The finite quadratic module of a generator label: `oddCyclic (p^k)`, `dyadicCyclic k`,
`dyadicU k` or `dyadicV k`. -/
@[expose] noncomputable def toFiniteQuadraticModule : NikulinGenerator → FiniteQuadraticModule.{0}
  | oddCyclic p k _ hodd θ => FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ
  | dyadicCyclic k hk θ =>
      haveI : NeZero k := ⟨hk.ne'⟩
      FiniteQuadraticModule.dyadicCyclic k θ
  | dyadicU k => FiniteQuadraticModule.dyadicU k
  | dyadicV k => FiniteQuadraticModule.dyadicV k

@[simp]
theorem toFiniteQuadraticModule_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).toFiniteQuadraticModule =
      FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).toFiniteQuadraticModule =
      haveI : NeZero k := ⟨hk.ne'⟩
      FiniteQuadraticModule.dyadicCyclic k θ := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicU (k : ℕ) :
    (dyadicU k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicU k := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicV (k : ℕ) :
    (dyadicV k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicV k := (rfl)

/-- The order of the module of `q_θ^{(p)}(p^k)` is `p^k`. -/
theorem natCard_toFiniteQuadraticModule_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p)
    (θ : ℤ) : Nat.card (oddCyclic p k hp hodd θ).toFiniteQuadraticModule = p ^ k :=
  natCard_oddCyclic _ hodd.pow θ

/-- The order of the module of `q_θ^{(2)}(2^k)` is `2^k`. -/
theorem natCard_toFiniteQuadraticModule_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    Nat.card (dyadicCyclic k hk θ).toFiniteQuadraticModule = 2 ^ k :=
  haveI : NeZero k := ⟨hk.ne'⟩
  natCard_dyadicCyclic k θ

/-- The order of the module of `u^{(2)}(2^k)` is `2^k · 2^k`. -/
theorem natCard_toFiniteQuadraticModule_dyadicU (k : ℕ) :
    Nat.card (dyadicU k).toFiniteQuadraticModule = 2 ^ k * 2 ^ k :=
  natCard_dyadicU k

/-- The order of the module of `v^{(2)}(2^k)` is `2^k · 2^k`. -/
theorem natCard_toFiniteQuadraticModule_dyadicV (k : ℕ) :
    Nat.card (dyadicV k).toFiniteQuadraticModule = 2 ^ k * 2 ^ k :=
  natCard_dyadicV k

/-- The module of a generator is a `p`-group for its prime `p`: its order is a power of `p`. -/
theorem isAddPGroup_toFiniteQuadraticModule (g : NikulinGenerator) :
    IsAddPGroup g.prime g.toFiniteQuadraticModule := by
  cases g with
  | oddCyclic p k hp hodd θ =>
    exact IsAddPGroup.of_card (natCard_toFiniteQuadraticModule_oddCyclic p k hp hodd θ)
  | dyadicCyclic k hk θ =>
    exact IsAddPGroup.of_card (natCard_toFiniteQuadraticModule_dyadicCyclic k hk θ)
  | dyadicU k =>
    exact IsAddPGroup.of_card
      ((natCard_toFiniteQuadraticModule_dyadicU k).trans (pow_add 2 k k).symm)
  | dyadicV k =>
    exact IsAddPGroup.of_card
      ((natCard_toFiniteQuadraticModule_dyadicV k).trans (pow_add 2 k k).symm)

/-- **Admissible labels are exactly the nondegenerate nontrivial generators.** -/
theorem isAdmissible_iff (g : NikulinGenerator) :
    g.IsAdmissible ↔
      g.toFiniteQuadraticModule.IsNondegenerate ∧ Nontrivial g.toFiniteQuadraticModule := by
  rw [← Finite.one_lt_card_iff_nontrivial]
  cases g with
  | oddCyclic p k hp hodd θ =>
    rw [natCard_toFiniteQuadraticModule_oddCyclic, toFiniteQuadraticModule_oddCyclic,
      isNondegenerate_oddCyclic_iff, isAdmissible_oddCyclic_iff, Nat.cast_pow]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    rw [IsCoprime.pow_left_iff hk, ← Nat.prime_iff_prime_int.mp hp |>.coprime_iff_not_dvd]
    exact ⟨fun h ↦ ⟨h.2, Nat.one_lt_pow hk.ne' hp.one_lt⟩, fun h ↦ ⟨hk, h.1⟩⟩
  | dyadicCyclic k hk θ =>
    rw [natCard_toFiniteQuadraticModule_dyadicCyclic, toFiniteQuadraticModule_dyadicCyclic,
      isNondegenerate_dyadicCyclic_iff, isAdmissible_dyadicCyclic_iff]
    exact ⟨fun h ↦ ⟨h, Nat.one_lt_two_pow hk.ne'⟩, And.left⟩
  | dyadicU k =>
    rw [natCard_toFiniteQuadraticModule_dyadicU, isAdmissible_dyadicU_iff, ← pow_add,
      Nat.one_lt_two_pow_iff]
    simp only [toFiniteQuadraticModule_dyadicU, isNondegenerate_dyadicU, true_and]
    omega
  | dyadicV k =>
    rw [natCard_toFiniteQuadraticModule_dyadicV, isAdmissible_dyadicV_iff, ← pow_add,
      Nat.one_lt_two_pow_iff]
    simp only [toFiniteQuadraticModule_dyadicV, isNondegenerate_dyadicV, true_and]
    omega

/-- The module of an admissible generator is nondegenerate. -/
theorem IsAdmissible.isNondegenerate {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.toFiniteQuadraticModule.IsNondegenerate :=
  (g.isAdmissible_iff.mp hg).1

/-- The module of an admissible generator is nontrivial. -/
theorem IsAdmissible.nontrivial {g : NikulinGenerator} (hg : g.IsAdmissible) :
    Nontrivial g.toFiniteQuadraticModule :=
  (g.isAdmissible_iff.mp hg).2

/-- The module of a generator is its own primary component at its prime. -/
theorem primaryComponent_toFiniteQuadraticModule_eq_top (g : NikulinGenerator) {p : ℕ}
    (hp : g.prime = p) : AddCommGroup.primaryComponent g.toFiniteQuadraticModule p = ⊤ :=
  hp ▸ isAddPGroup_iff_primaryComponent_eq_top.mp g.isAddPGroup_toFiniteQuadraticModule

/-- The module of a generator has trivial primary component at every other prime. -/
theorem primaryComponent_toFiniteQuadraticModule_eq_bot (g : NikulinGenerator) {p : ℕ}
    (hp : p.Prime) (hgp : g.prime ≠ p) :
    AddCommGroup.primaryComponent g.toFiniteQuadraticModule p = ⊥ :=
  g.isAddPGroup_toFiniteQuadraticModule.primaryComponent_eq_bot g.prime_prime hp hgp

/-- The minimal lattice rank (`1` for cyclic generators, `2` for `u` and `v`). For an admissible
generator (`IsAdmissible`), this is both the rank of the standard minimal-rank `p`-adic lattice
attached to the label `g` and `AddGroup.rank g.toFiniteQuadraticModule`
(`NikulinGenerator.IsAdmissible.rank_toFiniteQuadraticModule`). -/
def rank : NikulinGenerator → ℕ
  | .oddCyclic _ _ _ _ _ => 1
  | .dyadicCyclic _ _ _ => 1
  | .dyadicU _ => 2
  | .dyadicV _ => 2

@[simp]
theorem rank_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).rank = 1 := (rfl)

@[simp]
theorem rank_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).rank = 1 := (rfl)

@[simp]
theorem rank_dyadicU (k : ℕ) : (dyadicU k).rank = 2 := (rfl)

@[simp]
theorem rank_dyadicV (k : ℕ) : (dyadicV k).rank = 2 := (rfl)

theorem rank_pos : ∀ g : NikulinGenerator, 0 < g.rank
  | .oddCyclic _ _ _ _ _ => Nat.one_pos
  | .dyadicCyclic _ _ _ => Nat.one_pos
  | .dyadicU _ => Nat.zero_lt_two
  | .dyadicV _ => Nat.zero_lt_two

/-- The formal realization determinant expression assigned to a generator label: `θ · p^k` for
`oddCyclic`, `θ · 2^k` for `dyadicCyclic`, `-4^k` for `dyadicU`, and `3 · 4^k` for `dyadicV`.
When the label is admissible (`IsAdmissible`), this is the Gram determinant of the standard
minimal-rank `p`-adic lattice attached to the label `g` (`⟨θ · p^k⟩` for `oddCyclic`, `⟨θ · 2^k⟩`
for `dyadicCyclic`, `2^k · U` for `dyadicU`, and `2^k · !![2, 1; 1, 2]` for `dyadicV`). -/
def realizationDet : NikulinGenerator → ℤ
  | .oddCyclic p k _ _ θ => θ * (p : ℤ) ^ k
  | .dyadicCyclic k _ θ => θ * 2 ^ k
  | .dyadicU k => -(4 ^ k)
  | .dyadicV k => 3 * 4 ^ k

@[simp]
theorem realizationDet_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).realizationDet = θ * (p : ℤ) ^ k := (rfl)

@[simp]
theorem realizationDet_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).realizationDet = θ * 2 ^ k := (rfl)

@[simp]
theorem realizationDet_dyadicU (k : ℕ) : (dyadicU k).realizationDet = -(4 ^ k) := (rfl)

@[simp]
theorem realizationDet_dyadicV (k : ℕ) : (dyadicV k).realizationDet = 3 * 4 ^ k := (rfl)

/-- The formal cofactor of the group order in `realizationDet`: `θ` for cyclic labels, `-1` for
`dyadicU`, and `3` for `dyadicV`. When the label is admissible (`IsAdmissible`), this integer is
coprime to `g.prime` (`NikulinGenerator.IsAdmissible.isCoprime_prime_realizationUnit`), giving the
`p`-adic unit part of the standard label-dependent minimal realization determinant. -/
def realizationUnit : NikulinGenerator → ℤ
  | .oddCyclic _ _ _ _ θ => θ
  | .dyadicCyclic _ _ θ => θ
  | .dyadicU _ => -1
  | .dyadicV _ => 3

@[simp]
theorem realizationUnit_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).realizationUnit = θ := (rfl)

@[simp]
theorem realizationUnit_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).realizationUnit = θ := (rfl)

@[simp]
theorem realizationUnit_dyadicU (k : ℕ) : (dyadicU k).realizationUnit = -1 := (rfl)

@[simp]
theorem realizationUnit_dyadicV (k : ℕ) : (dyadicV k).realizationUnit = 3 := (rfl)

private theorem two_pow_mul_two_pow (k : ℕ) : 2 ^ k * 2 ^ k = 4 ^ k := by
  rw [← mul_pow]
  norm_num

/-- The formal determinant expression `g.realizationDet` factors as `g.realizationUnit` times the
order of `g.toFiniteQuadraticModule`. -/
theorem realizationDet_eq_realizationUnit_mul_natCard (g : NikulinGenerator) :
    g.realizationDet = g.realizationUnit * (Nat.card g.toFiniteQuadraticModule : ℤ) := by
  cases g with
  | oddCyclic p k hp hodd θ => simp
  | dyadicCyclic k hk θ => simp
  | dyadicU k => simp [two_pow_mul_two_pow]
  | dyadicV k => simp [two_pow_mul_two_pow]

/-- For an admissible generator, `realizationUnit` is coprime to `g.prime` in `ℤ`. -/
theorem IsAdmissible.isCoprime_prime_realizationUnit {g : NikulinGenerator} (hg : g.IsAdmissible) :
    IsCoprime (g.prime : ℤ) g.realizationUnit := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      exact (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr
        ((isAdmissible_oddCyclic_iff p k hp hodd θ).mp hg).2
  | dyadicCyclic k hk θ =>
      obtain ⟨m, rfl⟩ := (isAdmissible_dyadicCyclic_iff k hk θ).mp hg
      exact ⟨-m, 1, by simp only [prime_dyadicCyclic, realizationUnit_dyadicCyclic]; ring⟩
  | dyadicU _ =>
      exact ⟨0, -1, by norm_num [prime_dyadicU, realizationUnit_dyadicU]⟩
  | dyadicV _ =>
      exact ⟨-1, 1, by norm_num [prime_dyadicV, realizationUnit_dyadicV]⟩

/-- For any list of admissible generators of prime `p`, the product of their `realizationUnit`s
is coprime to `p` in `ℤ`. -/
theorem isCoprime_prod_realizationUnit_of_forall {p : ℕ} {gs : List NikulinGenerator}
    (hadm : ∀ g ∈ gs, g.IsAdmissible) (hprime : ∀ g ∈ gs, g.prime = p) :
    IsCoprime (p : ℤ) (gs.map NikulinGenerator.realizationUnit).prod := by
  induction gs with
  | nil => exact isCoprime_one_right
  | cons g gs ih =>
      rw [List.map_cons, List.prod_cons]
      have hg : IsCoprime (p : ℤ) g.realizationUnit :=
        hprime g List.mem_cons_self ▸ (hadm g List.mem_cons_self).isCoprime_prime_realizationUnit
      exact hg.mul_right
        (ih (fun g' hg' ↦ hadm g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' ↦ hprime g' (List.mem_cons_of_mem g hg')))

/-- Every admissible generator has nonzero realization determinant. -/
theorem IsAdmissible.realizationDet_ne_zero {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.realizationDet ≠ 0 := by
  rw [realizationDet_eq_realizationUnit_mul_natCard]
  refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro h0
  have hcop := hg.isCoprime_prime_realizationUnit
  rw [h0, isCoprime_zero_right] at hcop
  exact (Nat.prime_iff_prime_int.mp g.prime_prime).not_isUnit hcop

/-- For an admissible generator, the minimal number of generators `AddGroup.rank` of its finite
quadratic module equals `g.rank` (`1` for cyclic generators, `2` for `u` and `v`). -/
theorem IsAdmissible.rank_toFiniteQuadraticModule {g : NikulinGenerator} (hg : g.IsAdmissible) :
    AddGroup.rank g.toFiniteQuadraticModule = g.rank := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      rw [toFiniteQuadraticModule_oddCyclic, rank_oddCyclic,
        AddGroup.rank_congr
          (AddEquiv.refl _ : FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ ≃+ ZMod (p ^ k))]
      exact AddGroup.rank_zmod_prime_pow hp ((isAdmissible_oddCyclic_iff p k hp hodd θ).mp hg).1
  | dyadicCyclic k hk θ =>
      have : NeZero k := ⟨hk.ne'⟩
      rw [toFiniteQuadraticModule_dyadicCyclic, rank_dyadicCyclic,
        AddGroup.rank_congr
          (AddEquiv.refl _ : FiniteQuadraticModule.dyadicCyclic k θ ≃+ ZMod (2 ^ k))]
      exact AddGroup.rank_zmod_prime_pow Nat.prime_two hk
  | dyadicU k =>
      have hk : 0 < k := (isAdmissible_dyadicU_iff k).mp hg
      rw [toFiniteQuadraticModule_dyadicU, rank_dyadicU,
        AddGroup.rank_congr
          (AddEquiv.refl _ : FiniteQuadraticModule.dyadicU k ≃+ ZMod (2 ^ k) × ZMod (2 ^ k))]
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hk hk
  | dyadicV k =>
      have hk : 0 < k := (isAdmissible_dyadicV_iff k).mp hg
      rw [toFiniteQuadraticModule_dyadicV, rank_dyadicV,
        AddGroup.rank_congr
          (AddEquiv.refl _ : FiniteQuadraticModule.dyadicV k ≃+ ZMod (2 ^ k) × ZMod (2 ^ k))]
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hk hk

end NikulinGenerator

/-! ## Orthogonal sums of generators -/

/-- **The orthogonal sum of the modules of a list of generator labels**, the head summand first;
the empty list gives the zero module. -/
@[expose] noncomputable def orthogonalSumNikulinGenerators :
    List NikulinGenerator → FiniteQuadraticModule.{0}
  | [] => ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ)))
  | g :: gs => g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs)

/-- The orthogonal sum of the empty list of generators is the zero module. -/
instance : Unique (orthogonalSumNikulinGenerators []) :=
  inferInstanceAs (Unique PUnit)

@[simp]
theorem orthogonalSumNikulinGenerators_nil :
    orthogonalSumNikulinGenerators [] =
      ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ))) := (rfl)

@[simp]
theorem orthogonalSumNikulinGenerators_cons (g : NikulinGenerator) (gs : List NikulinGenerator) :
    orthogonalSumNikulinGenerators (g :: gs) =
      g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs) := (rfl)

/-- The order of an orthogonal sum of generators is the product of the orders of the generators. -/
theorem natCard_orthogonalSumNikulinGenerators (gs : List NikulinGenerator) :
    Nat.card (orthogonalSumNikulinGenerators gs) =
      (gs.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod := by
  induction gs with
  | nil => exact Nat.card_unique
  | cons g gs ih => rw [orthogonalSumNikulinGenerators_cons, Nat.card_prod, ih]; simp

/-- An orthogonal sum of generators is nondegenerate exactly when every summand is. -/
theorem isNondegenerate_orthogonalSumNikulinGenerators_iff (gs : List NikulinGenerator) :
    (orthogonalSumNikulinGenerators gs).IsNondegenerate ↔
      ∀ g ∈ gs, g.toFiniteQuadraticModule.IsNondegenerate := by
  induction gs with
  | nil =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    exact FiniteBilinearModule.isNondegenerate_of_injective _ (Function.injective_of_subsingleton _)
  | cons g gs ih =>
    rw [orthogonalSumNikulinGenerators_cons, isNondegenerate_prod, ih, List.forall_mem_cons]

/-- An orthogonal sum of admissible generators is nondegenerate. -/
theorem isNondegenerate_orthogonalSumNikulinGenerators {gs : List NikulinGenerator}
    (h : ∀ g ∈ gs, g.IsAdmissible) : (orthogonalSumNikulinGenerators gs).IsNondegenerate :=
  (isNondegenerate_orthogonalSumNikulinGenerators_iff gs).mpr fun g hg ↦ (h g hg).isNondegenerate

/-- The Gauss-sum invariant of an orthogonal sum of nondegenerate generators is the sum of their
invariants. -/
theorem gaussSign_orthogonalSumNikulinGenerators {gs : List NikulinGenerator}
    (h : ∀ g ∈ gs, g.toFiniteQuadraticModule.IsNondegenerate) :
    (orthogonalSumNikulinGenerators gs).gaussSign =
      (gs.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum := by
  induction gs with
  | nil => exact gaussSign_eq_zero_of_subsingleton _
  | cons g gs ih =>
    rw [List.forall_mem_cons] at h
    rw [orthogonalSumNikulinGenerators_cons,
      gaussSign_prod h.1 ((isNondegenerate_orthogonalSumNikulinGenerators_iff gs).mpr h.2),
      ih h.2, List.map_cons, List.sum_cons]

/-- **The orthogonal sum over a concatenation of lists** is the orthogonal product of the two
orthogonal sums, by reassociating the summands of the first list. -/
noncomputable def orthogonalSumNikulinGeneratorsAppendIsometry :
    (gs hs : List NikulinGenerator) → Isometry (orthogonalSumNikulinGenerators (gs ++ hs))
      ((orthogonalSumNikulinGenerators gs).prod (orthogonalSumNikulinGenerators hs))
  | [], _ =>
    (QuadraticMap.IsometryEquiv.uniqueProd (orthogonalSumNikulinGenerators []).quadratic _).symm
  | _ :: gs, hs =>
    ((QuadraticMap.IsometryEquiv.refl _).prod
      (orthogonalSumNikulinGeneratorsAppendIsometry gs hs)).trans
        (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm

/-- `orthogonalSumNikulinGeneratorsAppendIsometry` puts an empty first list in front as the zero
module. Not a simp lemma: simp first rewrites `[] ++ hs` in the type of the isometry. -/
theorem orthogonalSumNikulinGeneratorsAppendIsometry_nil_apply (hs : List NikulinGenerator)
    (x : orthogonalSumNikulinGenerators hs) :
    orthogonalSumNikulinGeneratorsAppendIsometry [] hs x = (default, x) :=
  QuadraticMap.IsometryEquiv.uniqueProd_symm_apply _ _ x

/-- `orthogonalSumNikulinGeneratorsAppendIsometry` keeps the head summand of the first list in
front. Not a simp lemma: simp first rewrites `g :: gs ++ hs` in the type of the isometry. -/
theorem orthogonalSumNikulinGeneratorsAppendIsometry_cons_apply (g : NikulinGenerator)
    (gs hs : List NikulinGenerator) (x : orthogonalSumNikulinGenerators (g :: gs ++ hs)) :
    orthogonalSumNikulinGeneratorsAppendIsometry (g :: gs) hs x =
      ((x.1, (orthogonalSumNikulinGeneratorsAppendIsometry gs hs x.2).1),
        (orthogonalSumNikulinGeneratorsAppendIsometry gs hs x.2).2) := by
  -- Unfold the head summand, which `IsometryEquiv.refl` leaves in place.
  change (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm
    (x.1, orthogonalSumNikulinGeneratorsAppendIsometry gs hs x.2) = _
  exact QuadraticMap.IsometryEquiv.prodAssoc_symm_apply _ _ _ _

/-- **The orthogonal sum of the labels `f 0, …, f (n - 1)`** is the orthogonal sum `pi` of the
family of their modules, by moving the head summand into the coordinate `0`. -/
noncomputable def orthogonalSumNikulinGeneratorsOfFnIsometry :
    {n : ℕ} → (f : Fin n → NikulinGenerator) →
      Isometry (orthogonalSumNikulinGenerators (List.ofFn f))
        (pi fun i ↦ (f i).toFiniteQuadraticModule)
  | 0, f =>
    (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators (List.ofFn_zero (f := f)))).trans
      Isometry.ofSubsingleton
  | _ + 1, f =>
    (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators (List.ofFn_succ (f := f)))).trans <|
      ((QuadraticMap.IsometryEquiv.refl _).prod
        (orthogonalSumNikulinGeneratorsOfFnIsometry fun i ↦ f i.succ)).trans
      (QuadraticMap.IsometryEquiv.consPi fun i ↦ (f i).toFiniteQuadraticModule.quadratic)

theorem orthogonalSumNikulinGeneratorsOfFnIsometry_succ {n : ℕ}
    (f : Fin (n + 1) → NikulinGenerator) :
    orthogonalSumNikulinGeneratorsOfFnIsometry f =
      (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators (List.ofFn_succ (f := f)))).trans
        (((QuadraticMap.IsometryEquiv.refl _).prod
          (orthogonalSumNikulinGeneratorsOfFnIsometry fun i ↦ f i.succ)).trans
        (QuadraticMap.IsometryEquiv.consPi fun i ↦ (f i).toFiniteQuadraticModule.quadratic)) :=
  (rfl)

/-- **The orthogonal sum of generators does not depend on their order.** -/
theorem nonempty_isometry_orthogonalSumNikulinGenerators_of_perm {gs hs : List NikulinGenerator}
    (h : gs.Perm hs) :
    Nonempty
      (Isometry (orthogonalSumNikulinGenerators gs) (orthogonalSumNikulinGenerators hs)) := by
  induction h with
  | nil => exact ⟨.refl _⟩
  | cons g _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(QuadraticMap.IsometryEquiv.refl _).prod e⟩
  | swap g g' gs => exact ⟨QuadraticMap.IsometryEquiv.prodLeftComm _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁.trans e₂⟩

/-- **The `p`-primary component of an orthogonal sum of generators** is the orthogonal sum of the
generators whose prime is `p`: split the primary component of `g ⊕ S` into those of `g` and of
`S`, and keep `g` exactly when its prime is `p`. -/
noncomputable def primaryComponentOrthogonalSumNikulinGeneratorsIsometry {p : ℕ}
    (hp : p.Prime) :
    (gs : List NikulinGenerator) →
      Isometry ((orthogonalSumNikulinGenerators gs).primaryComponent p)
        (orthogonalSumNikulinGenerators (gs.filter fun g ↦ g.prime = p))
  | [] =>
    haveI : Subsingleton ((orthogonalSumNikulinGenerators []).primaryComponent p) :=
      inferInstanceAs (Subsingleton (AddCommGroup.primaryComponent
        (orthogonalSumNikulinGenerators []) p))
    haveI : Subsingleton (orthogonalSumNikulinGenerators ([].filter fun g ↦ g.prime = p)) :=
      inferInstanceAs (Subsingleton (orthogonalSumNikulinGenerators []))
    Isometry.ofSubsingleton
  | g :: gs =>
    let s := primaryComponentProdIsometry g.toFiniteQuadraticModule
      (orthogonalSumNikulinGenerators gs) p
    let e := primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp gs
    if hg : g.prime = p then
      -- The generator is its own `p`-primary component, and it is kept by the filter.
      (s.trans (((g.toFiniteQuadraticModule.restrictCongr
        (g.primaryComponent_toFiniteQuadraticModule_eq_top hg)).trans
          g.toFiniteQuadraticModule.restrictTopIsometry).prod e)).trans
        (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators
          (List.filter_cons_of_pos (by simpa using hg))).symm)
    else
      -- The generator has trivial `p`-primary component, and it is dropped by the filter.
      -- The carrier of `A.restrict H` is `↥H`, so the restriction to `⊥` is trivial.
      haveI : Unique (g.toFiniteQuadraticModule.restrict ⊥) :=
        (inferInstance : Unique (⊥ : AddSubgroup g.toFiniteQuadraticModule))
      (((s.trans ((g.toFiniteQuadraticModule.restrictCongr
        (g.primaryComponent_toFiniteQuadraticModule_eq_bot hp hg)).prod e)).trans
          (QuadraticMap.IsometryEquiv.uniqueProd _ _))).trans
        (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators
          (List.filter_cons_of_neg (by simpa using hg))).symm)

/-- On a generator of prime `p`, `primaryComponentOrthogonalSumNikulinGeneratorsIsometry`
keeps the generator as its own `p`-primary component. -/
theorem primaryComponentOrthogonalSumNikulinGeneratorsIsometry_cons_of_prime_eq {p : ℕ}
    (hp : p.Prime) {g : NikulinGenerator} (gs : List NikulinGenerator) (hg : g.prime = p) :
    primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp (g :: gs) =
      ((primaryComponentProdIsometry g.toFiniteQuadraticModule
        (orthogonalSumNikulinGenerators gs) p).trans
          (((g.toFiniteQuadraticModule.restrictCongr
            (g.primaryComponent_toFiniteQuadraticModule_eq_top hg)).trans
              g.toFiniteQuadraticModule.restrictTopIsometry).prod
            (primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp gs))).trans
        (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators
          (List.filter_cons_of_pos (by simpa using hg))).symm) := by
  rw [primaryComponentOrthogonalSumNikulinGeneratorsIsometry]
  exact dite_eq_left_of_eq_true (eq_true hg)

/-- On a generator of another prime,
`primaryComponentOrthogonalSumNikulinGeneratorsIsometry` drops the generator, whose
`p`-primary component is trivial. -/
theorem primaryComponentOrthogonalSumNikulinGeneratorsIsometry_cons_of_prime_ne {p : ℕ}
    (hp : p.Prime) {g : NikulinGenerator} (gs : List NikulinGenerator) (hg : g.prime ≠ p) :
    haveI : Unique (g.toFiniteQuadraticModule.restrict ⊥) :=
      (inferInstance : Unique (⊥ : AddSubgroup g.toFiniteQuadraticModule))
    primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp (g :: gs) =
      (((primaryComponentProdIsometry g.toFiniteQuadraticModule
        (orthogonalSumNikulinGenerators gs) p).trans
          ((g.toFiniteQuadraticModule.restrictCongr
            (g.primaryComponent_toFiniteQuadraticModule_eq_bot hp hg)).prod
            (primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp gs))).trans
          (QuadraticMap.IsometryEquiv.uniqueProd _ _)).trans
        (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators
          (List.filter_cons_of_neg (by simpa using hg))).symm) := by
  rw [primaryComponentOrthogonalSumNikulinGeneratorsIsometry]
  exact dite_eq_right_of_eq_false (eq_false hg)

/-- A single Nikulin generator is canonically isometric to its singleton orthogonal sum. -/
noncomputable def singletonNikulinGeneratorIsometry (g : NikulinGenerator) :
    g.toFiniteQuadraticModule.Isometry (orthogonalSumNikulinGenerators [g]) :=
  (QuadraticMap.IsometryEquiv.prodUnique g.toFiniteQuadraticModule.quadratic
    (orthogonalSumNikulinGenerators []).quadratic).symm

/-- If every generator in `gs` has prime `p`, their orthogonal sum is an additive `p`-group. -/
theorem isAddPGroup_orthogonalSumNikulinGenerators {p : ℕ} {gs : List NikulinGenerator}
    (h : ∀ g ∈ gs, g.prime = p) :
    IsAddPGroup p (orthogonalSumNikulinGenerators gs) := by
  induction gs with
  | nil =>
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  | cons g gs ih =>
      rw [orthogonalSumNikulinGenerators_cons]
      have hg : IsAddPGroup p g.toFiniteQuadraticModule :=
        h g List.mem_cons_self ▸ g.isAddPGroup_toFiniteQuadraticModule
      exact IsAddPGroup.prod hg (ih fun g' hg' ↦ h g' (List.mem_cons_of_mem g hg'))

/-- For a list of admissible `p`-primary generators, the generator rank `AddGroup.rank` of their
orthogonal sum is the sum of their individual ranks (`1` for cyclic, `2` for `u` and `v`). -/
theorem rank_orthogonalSumNikulinGenerators_of_prime {p : ℕ}
    {gs : List NikulinGenerator} (hadm : ∀ g ∈ gs, g.IsAdmissible)
    (hprime : ∀ g ∈ gs, g.prime = p) :
    AddGroup.rank (orthogonalSumNikulinGenerators gs) = (gs.map NikulinGenerator.rank).sum := by
  induction gs with
  | nil =>
      exact AddGroup.rank_eq_zero_iff.mpr inferInstance
  | cons g gs ih =>
      have hp : p.Prime := hprime g List.mem_cons_self ▸ g.prime_prime
      have hgP : IsAddPGroup p g.toFiniteQuadraticModule :=
        hprime g List.mem_cons_self ▸ g.isAddPGroup_toFiniteQuadraticModule
      have hgsP : IsAddPGroup p (orthogonalSumNikulinGenerators gs) :=
        isAddPGroup_orthogonalSumNikulinGenerators fun g' hg' ↦
          hprime g' (List.mem_cons_of_mem g hg')
      rw [orthogonalSumNikulinGenerators_cons, List.map_cons, List.sum_cons,
        hgP.rank_prod hp hgsP,
        (hadm g List.mem_cons_self).rank_toFiniteQuadraticModule,
        ih (fun g' hg' ↦ hadm g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' ↦ hprime g' (List.mem_cons_of_mem g hg'))]

/-! ## Generator decompositions -/

/-- **A generator decomposition** of a finite quadratic module (Nikulin, Proposition 1.8.1): a list
of admissible generator labels together with an isometry onto the orthogonal sum of their modules.
A module has one exactly when it is nondegenerate (`nonempty_nikulinDecomposition_iff`); it is not
unique, not even up to reordering the labels. -/
structure NikulinDecomposition (A : FiniteQuadraticModule.{u}) where
  /-- The generator labels. -/
  generators : List NikulinGenerator
  /-- Every label is admissible, so every summand is nondegenerate and nontrivial. -/
  isAdmissible : ∀ g ∈ generators, g.IsAdmissible
  /-- The module is isometric to the orthogonal sum of the generators. -/
  isometry : Isometry A (orthogonalSumNikulinGenerators generators)

namespace NikulinDecomposition

variable {A : FiniteQuadraticModule.{u}}

/-- A module with a generator decomposition is nondegenerate. -/
theorem isNondegenerate (D : NikulinDecomposition A) : A.IsNondegenerate :=
  Isometry.isNondegenerate D.isometry.symm
    (isNondegenerate_orthogonalSumNikulinGenerators D.isAdmissible)

/-- The order of a decomposed module is the product of the orders of its generators. -/
theorem natCard_eq (D : NikulinDecomposition A) :
    Nat.card A = (D.generators.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod :=
  (Nat.card_congr D.isometry.toLinearEquiv.toEquiv).trans
    (natCard_orthogonalSumNikulinGenerators D.generators)

/-- The Gauss-sum invariant of a decomposed module is the sum of the invariants of its
generators. -/
theorem gaussSign_eq (D : NikulinDecomposition A) :
    A.gaussSign = (D.generators.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum :=
  D.isometry.gaussSign_eq.trans
    (gaussSign_orthogonalSumNikulinGenerators fun g hg ↦ (D.isAdmissible g hg).isNondegenerate)

/-- Transport of a generator decomposition along an isometry. -/
noncomputable def map {B : FiniteQuadraticModule.{v}} (D : NikulinDecomposition A)
    (e : Isometry A B) :
    NikulinDecomposition B where
  generators := D.generators
  isAdmissible := D.isAdmissible
  isometry := e.symm.trans D.isometry

@[simp]
theorem map_generators {B : FiniteQuadraticModule.{v}} (D : NikulinDecomposition A)
    (e : Isometry A B) : (D.map e).generators = D.generators := (rfl)

/-- **The decomposition of a primary component.** The generators of a decomposition of `A` whose
prime is `p` decompose the `p`-primary component of `A`. -/
@[expose] noncomputable def primaryComponent (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    NikulinDecomposition (A.primaryComponent p) where
  generators := D.generators.filter fun g ↦ g.prime = p
  isAdmissible g hg := D.isAdmissible g (List.mem_of_mem_filter hg)
  isometry := (D.isometry.restrictPrimaryComponent p).trans
    (primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp D.generators)

@[simp]
theorem primaryComponent_generators (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    (D.primaryComponent hp).generators = D.generators.filter fun g ↦ g.prime = p := (rfl)

/-- The isometry of the decomposition of a primary component restricts the isometry of `D` to the
primary component and then splits off the generators of prime `p`. -/
@[simp]
theorem primaryComponent_isometry_apply (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime)
    (x : A.primaryComponent p) :
    (D.primaryComponent hp).isometry x =
      primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp D.generators
        (D.isometry.restrictPrimaryComponent p x) := (rfl)

/-- The empty Nikulin decomposition of a trivial finite quadratic module. -/
noncomputable def ofSubsingleton (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    NikulinDecomposition A where
  generators := []
  isAdmissible _ h := nomatch h
  isometry := Isometry.ofSubsingleton

/-- The empty Nikulin decomposition of a subsingleton module has empty generator list. -/
@[simp]
theorem ofSubsingleton_generators (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    (ofSubsingleton A).generators = [] := (rfl)

/-- The single-generator Nikulin decomposition of an admissible generator's module. -/
noncomputable def singleton (g : NikulinGenerator) (hg : g.IsAdmissible) :
    NikulinDecomposition g.toFiniteQuadraticModule where
  generators := [g]
  isAdmissible g' hg' := by
    rw [List.mem_singleton] at hg'
    subst hg'
    exact hg
  isometry := singletonNikulinGeneratorIsometry g

/-- The singleton Nikulin decomposition has generator list `[g]`. -/
@[simp]
theorem singleton_generators (g : NikulinGenerator) (hg : g.IsAdmissible) :
    (singleton g hg).generators = [g] := (rfl)

/-- Concatenate two Nikulin decompositions to decompose an orthogonal direct sum. -/
noncomputable def prod {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    NikulinDecomposition (A.prod B) where
  generators := DA.generators ++ DB.generators
  isAdmissible g hg := by
    rcases List.mem_append.mp hg with hA | hB
    · exact DA.isAdmissible g hA
    · exact DB.isAdmissible g hB
  isometry := (DA.isometry.prod DB.isometry).trans
    (orthogonalSumNikulinGeneratorsAppendIsometry DA.generators DB.generators).symm

/-- The product of two Nikulin decompositions concatenates their generator lists. -/
@[simp]
theorem prod_generators {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    (DA.prod DB).generators = DA.generators ++ DB.generators := (rfl)

/-- Bundle a `Fin n`-indexed orthogonal sum of admissible `NikulinGenerator`s as a
`NikulinDecomposition`. -/
noncomputable def ofPi {n : ℕ} (g : Fin n → NikulinGenerator)
    (hg : ∀ i, (g i).IsAdmissible) :
    NikulinDecomposition (pi fun i ↦ (g i).toFiniteQuadraticModule) where
  generators := List.ofFn g
  isAdmissible g' hg' := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg'
    exact hg i
  isometry := (orthogonalSumNikulinGeneratorsOfFnIsometry g).symm

/-- The generator list of `NikulinDecomposition.ofPi` is `List.ofFn g`. -/
@[simp]
theorem ofPi_generators {n : ℕ} (g : Fin n → NikulinGenerator)
    (hg : ∀ i, (g i).IsAdmissible) :
    (ofPi g hg).generators = List.ofFn g := (rfl)

/-- For prime `p`, the order of `A.primaryComponent p` is the product of the orders of the
`p`-primary generators in `D`. -/
theorem natCard_primaryComponent_eq (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    Nat.card (A.primaryComponent p) =
      ((D.generators.filter fun g ↦ g.prime = p).map
        fun g ↦ Nat.card g.toFiniteQuadraticModule).prod :=
  (D.primaryComponent hp).natCard_eq

/-- At any prime `p`, the product of `realizationDet` across the `p`-primary generators of `D`
equals the product of their `realizationUnit`s times `Nat.card (A.primaryComponent p)`. -/
theorem prod_realizationDet_filter_eq (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationUnit).prod *
        (Nat.card (A.primaryComponent p) : ℤ) := by
  rw [D.natCard_primaryComponent_eq hp, Nat.cast_list_prod, List.map_map, ← List.prod_map_mul]
  congr 1
  exact List.map_congr_left fun g _ ↦ g.realizationDet_eq_realizationUnit_mul_natCard

/-- The product of `realizationUnit` across the `p`-primary generators of `D` is coprime to `p`. -/
theorem isCoprime_prod_realizationUnit_filter (D : NikulinDecomposition A) (p : ℕ) :
    IsCoprime (p : ℤ)
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationUnit).prod :=
  NikulinGenerator.isCoprime_prod_realizationUnit_of_forall
    (fun g hg ↦ D.isAdmissible g (List.mem_of_mem_filter hg))
    (fun _ hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2)

/-- The product of `realizationDet` across the `p`-primary generators of `D` is nonzero. -/
theorem prod_realizationDet_filter_ne_zero (D : NikulinDecomposition A) (p : ℕ) :
    ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod ≠ 0 := by
  refine List.prod_ne_zero ?_
  intro h0
  obtain ⟨g, hg, hg0⟩ := List.mem_map.mp h0
  exact (D.isAdmissible g (List.mem_of_mem_filter hg)).realizationDet_ne_zero hg0

/-- **Primary generator rank from a Nikulin decomposition**: for prime `p`, the minimal number of
generators `AddGroup.rank (A.primaryComponent p)` equals the sum of `g.rank` (`1` on cyclic
generators, `2` on `u` and `v`) over the `p`-primary generators of `D`. In particular this weighted
count depends only on `A` and `p`, not on the choice of decomposition `D`. -/
theorem rank_primaryComponent (D : NikulinDecomposition A) {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (A.primaryComponent p) =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  rw [AddGroup.rank_congr (D.primaryComponent hp).isometry.toLinearEquiv.toAddEquiv]
  exact rank_orthogonalSumNikulinGenerators_of_prime (D.primaryComponent hp).isAdmissible
    fun g hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2

/-- **Total length `l(A)` from a Nikulin decomposition**: the minimal number of generators
`AddGroup.rank A` is the supremum over prime factors of `Nat.card A` of the `p`-primary generator
rank sums read off `D`. -/
theorem rank_eq (D : NikulinDecomposition A) :
    AddGroup.rank A =
      (Nat.card A).primeFactors.sup fun p ↦
        ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  rw [AddGroup.rank_eq_sup_primaryComponents A]
  refine Finset.sup_congr rfl fun p hp ↦ ?_
  exact D.rank_primaryComponent (Nat.prime_of_mem_primeFactors hp)

end NikulinDecomposition

/-- **Nikulin's generator decomposition** (Proposition 1.8.1): a finite quadratic module has a
generator decomposition exactly when it is nondegenerate. -/
theorem nonempty_nikulinDecomposition_iff {A : FiniteQuadraticModule.{u}} :
    Nonempty (NikulinDecomposition A) ↔ A.IsNondegenerate := by
  refine ⟨fun ⟨D⟩ ↦ D.isNondegenerate, fun hA ↦ ?_⟩
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
    exists_isometry_prod_pi_generators A hA
  -- Write each odd prime power `m i` as `p i ^ n i`.
  choose p n hp hn hpn using fun i ↦ (isPrimePow_nat_iff (m i)).mp (hmθ i).1
  have hodd (i : Fin a) : Odd (p i) := (Nat.odd_pow_iff (hn i).ne').mp (hpn i ▸ hm i)
  let odd (i : Fin a) : NikulinGenerator := .oddCyclic (p i) (n i) (hp i) (hodd i) (θ i)
  let cyc (i : Fin b) : NikulinGenerator := .dyadicCyclic (k i + 1) (Nat.succ_pos _) (η i)
  let us (i : Fin c) : NikulinGenerator := .dyadicU (ku i + 1)
  let vs (i : Fin d) : NikulinGenerator := .dyadicV (kv i + 1)
  let gs := List.ofFn odd ++ (List.ofFn cyc ++ (List.ofFn us ++ List.ofFn vs))
  have hadm : ∀ g ∈ gs, g.IsAdmissible := by
    simp only [gs, List.mem_append, List.mem_ofFn]
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · rw [NikulinGenerator.isAdmissible_oddCyclic_iff]
      refine ⟨hn i, fun hdvd ↦ ?_⟩
      -- A prime dividing `θ i` would divide `gcd(m i, θ i) = 1`.
      have hcop : IsCoprime (p i : ℤ) (θ i) :=
        (IsCoprime.pow_left_iff (hn i)).mp (by exact_mod_cast hpn i ▸ (hmθ i).2)
      exact (Nat.prime_iff_prime_int.mp (hp i)).not_isUnit
        (hcop.isUnit_of_dvd' (dvd_refl _) hdvd)
    · exact (NikulinGenerator.isAdmissible_dyadicCyclic_iff _ _ _).mpr (hη i)
    · exact (NikulinGenerator.isAdmissible_dyadicU_iff _).mpr (Nat.succ_pos _)
    · exact (NikulinGenerator.isAdmissible_dyadicV_iff _).mpr (Nat.succ_pos _)
  -- The labels of the odd generators name the modules of the native decomposition.
  have eodd (i : Fin a) : Isometry (oddCyclic (m i) (hm i) (θ i)) (odd i).toFiniteQuadraticModule :=
    Isometry.ofEq <| by
      have key : ∀ (m' : ℕ) (hm' : Odd m'), p i ^ n i = m' →
          oddCyclic m' hm' (θ i) = oddCyclic (p i ^ n i) (hodd i).pow (θ i) := by
        rintro _ _ rfl
        rfl
      exact key _ _ (hpn i)
  let e₁ := orthogonalSumNikulinGeneratorsAppendIsometry (List.ofFn odd)
    (List.ofFn cyc ++ (List.ofFn us ++ List.ofFn vs))
  let e₂ := orthogonalSumNikulinGeneratorsAppendIsometry (List.ofFn cyc)
    (List.ofFn us ++ List.ofFn vs)
  let e₃ := orthogonalSumNikulinGeneratorsAppendIsometry (List.ofFn us) (List.ofFn vs)
  let o₁ := orthogonalSumNikulinGeneratorsOfFnIsometry odd
  let o₂ := orthogonalSumNikulinGeneratorsOfFnIsometry cyc
  let o₃ := orthogonalSumNikulinGeneratorsOfFnIsometry us
  let o₄ := orthogonalSumNikulinGeneratorsOfFnIsometry vs
  -- The modules of the dyadic labels are the dyadic modules of the native decomposition by
  -- definition, so only the odd summands need `eodd`.
  exact ⟨⟨gs, hadm, f.symm.trans <|
    ((QuadraticMap.IsometryEquiv.pi eodd).prod (QuadraticMap.IsometryEquiv.refl _)).trans <|
      (e₁.trans (o₁.prod (e₂.trans (o₂.prod (e₃.trans (o₃.prod o₄)))))).symm⟩⟩

/-- **Choose a Nikulin generator decomposition** for any nondegenerate finite quadratic module
(Nikulin, Proposition 1.8.1). -/
noncomputable def NikulinDecomposition.ofIsNondegenerate {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) : NikulinDecomposition A :=
  Classical.choice (nonempty_nikulinDecomposition_iff.mpr hA)

/-! ## Cyclic order-two dyadic summands -/

/-- If a `NikulinDecomposition` of `A` contains `.dyadicCyclic 1 hk θ`, then `A` has a cyclic
order-two dyadic summand. -/
theorem NikulinDecomposition.hasCyclicTwoSummand_of_mem {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {hk : 0 < 1} {θ : ℤ}
    (hmem : NikulinGenerator.dyadicCyclic 1 hk θ ∈ D.generators) :
    HasCyclicTwoSummand A := by
  obtain ⟨gs₁, gs₂, hsplit⟩ := List.append_of_mem hmem
  have hθ : Odd θ :=
    (NikulinGenerator.isAdmissible_dyadicCyclic_iff 1 hk θ).mp (D.isAdmissible _ hmem)
  rw [hasCyclicTwoSummand_def]
  refine ⟨θ, (orthogonalSumNikulinGenerators gs₁).prod (orthogonalSumNikulinGenerators gs₂),
    hθ, ⟨?_⟩⟩
  exact D.isometry.trans
    ((Isometry.ofEq (congrArg orthogonalSumNikulinGenerators hsplit)).trans
      ((orthogonalSumNikulinGeneratorsAppendIsometry gs₁
        (NikulinGenerator.dyadicCyclic 1 hk θ :: gs₂)).trans
        (QuadraticMap.IsometryEquiv.prodLeftComm
          (orthogonalSumNikulinGenerators gs₁).quadratic
          (dyadicCyclic 1 θ).quadratic
          (orthogonalSumNikulinGenerators gs₂).quadratic)))

/-! ## Non-uniqueness of decompositions -/

/-- Standard single-generator decomposition `[q_θ^{(2)}(2)]` of `dyadicCyclic 1 θ` (`θ` odd). -/
noncomputable def nikulinDecompositionDyadicCyclicOne {θ : ℤ} (hθ : Odd θ) :
    NikulinDecomposition (dyadicCyclic 1 θ) :=
  (NikulinDecomposition.singleton (.dyadicCyclic 1 Nat.one_pos θ)
      ((NikulinGenerator.isAdmissible_dyadicCyclic_iff 1 Nat.one_pos θ).mpr hθ)).map
    (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicCyclic 1 Nat.one_pos θ))

/-- The generator list of `nikulinDecompositionDyadicCyclicOne` is
`[.dyadicCyclic 1 Nat.one_pos θ]`. -/
@[simp]
theorem nikulinDecompositionDyadicCyclicOne_generators {θ : ℤ} (hθ : Odd θ) :
    (nikulinDecompositionDyadicCyclicOne hθ).generators = [.dyadicCyclic 1 Nat.one_pos θ] := by
  simp [nikulinDecompositionDyadicCyclicOne]

/-- Alternative single-generator decomposition `[q_{5θ}^{(2)}(2)]` of `dyadicCyclic 1 θ` (`θ` odd)
via Nikulin's relation `q_θ^{(2)}(2) ≅ q_{5θ}^{(2)}(2)` (`dyadicCyclicOneIsometryFiveMul`). -/
noncomputable def nikulinDecompositionDyadicCyclicOneFive {θ : ℤ} (hθ : Odd θ) :
    NikulinDecomposition (dyadicCyclic 1 θ) :=
  have h5 : Odd (5 : ℤ) := by norm_num [Int.odd_iff]
  (nikulinDecompositionDyadicCyclicOne (h5.mul hθ)).map (dyadicCyclicOneIsometryFiveMul θ).symm

/-- The generator list of `nikulinDecompositionDyadicCyclicOneFive` is
`[.dyadicCyclic 1 Nat.one_pos (5 * θ)]`. -/
@[simp]
theorem nikulinDecompositionDyadicCyclicOneFive_generators {θ : ℤ} (hθ : Odd θ) :
    (nikulinDecompositionDyadicCyclicOneFive hθ).generators =
      [.dyadicCyclic 1 Nat.one_pos (5 * θ)] := by
  simp [nikulinDecompositionDyadicCyclicOneFive]

/-- Standard two-generator decomposition `[u^{(2)}(2^k), u^{(2)}(2^k)]` of
`(dyadicU k).prod (dyadicU k)` (`k > 0`). -/
noncomputable def nikulinDecompositionDyadicUProdSelf {k : ℕ} (hk : 0 < k) :
    NikulinDecomposition ((dyadicU k).prod (dyadicU k)) :=
  let U : NikulinDecomposition (dyadicU k) :=
    (NikulinDecomposition.singleton (.dyadicU k)
        ((NikulinGenerator.isAdmissible_dyadicU_iff k).mpr hk)).map
      (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicU k))
  U.prod U

/-- The generator list of `nikulinDecompositionDyadicUProdSelf` is `[.dyadicU k, .dyadicU k]`. -/
@[simp]
theorem nikulinDecompositionDyadicUProdSelf_generators {k : ℕ} (hk : 0 < k) :
    (nikulinDecompositionDyadicUProdSelf hk).generators = [.dyadicU k, .dyadicU k] := by
  simp [nikulinDecompositionDyadicUProdSelf]

/-- Alternative two-generator decomposition `[v^{(2)}(2^k), v^{(2)}(2^k)]` of
`(dyadicU k).prod (dyadicU k)` (`k > 0`) via `u^{(2)}(2^k)^2 ≅ v^{(2)}(2^k)^2`
(`dyadicUProdSelfIsometryDyadicVProdSelf`). -/
noncomputable def nikulinDecompositionDyadicUProdSelfAsV {k : ℕ} (hk : 0 < k) :
    NikulinDecomposition ((dyadicU k).prod (dyadicU k)) :=
  let V : NikulinDecomposition (dyadicV k) :=
    (NikulinDecomposition.singleton (.dyadicV k)
        ((NikulinGenerator.isAdmissible_dyadicV_iff k).mpr hk)).map
      (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicV k))
  (V.prod V).map (dyadicUProdSelfIsometryDyadicVProdSelf k).symm

/-- The generator list of `nikulinDecompositionDyadicUProdSelfAsV` is
`[.dyadicV k, .dyadicV k]`. -/
@[simp]
theorem nikulinDecompositionDyadicUProdSelfAsV_generators {k : ℕ} (hk : 0 < k) :
    (nikulinDecompositionDyadicUProdSelfAsV hk).generators = [.dyadicV k, .dyadicV k] := by
  simp [nikulinDecompositionDyadicUProdSelfAsV]

end TauCeti.FiniteQuadraticModule
