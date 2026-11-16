/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.PrimePowerRank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.GaussSum
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Nikulin's primary generators as decomposition labels

Nikulin's Proposition 1.8.1 decomposes every nondegenerate finite quadratic module into an
orthogonal sum of primary generators belonging to four standard families:

* the odd-prime cyclic modules `q_θ^{(p)}(p^k)` on `ℤ/p^k` (`p` an odd prime, `k ≥ 1`, `p ∤ θ`);
* the dyadic cyclic modules `q_θ^{(2)}(2^k)` on `ℤ/2^k` (`k ≥ 1`, `θ` odd);
* the dyadic hyperbolic rank-two modules `u^{(2)}(2^k)` on `(ℤ/2^k)²` (`k ≥ 1`);
* the dyadic norm-two rank-two modules `v^{(2)}(2^k)` on `(ℤ/2^k)²` (`k ≥ 1`).

This file packages these four generator families into an explicit inductive label type
`TauCeti.FiniteQuadraticModule.NikulinGenerator`, equips each label with its admissibility
condition, prime, exponent, additive generator rank, bundled `FiniteQuadraticModule`, and minimal
`p`-adic realization Gram determinant, and constructs the orthogonal sum
`TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators` of any finite list of labels.

## Main definitions

* `TauCeti.FiniteQuadraticModule.NikulinGenerator`: syntactic labels for Nikulin's four families of
  primary generators.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.IsAdmissible`: positive exponent and unit
  coefficient parameter, characterizing nontrivial nondegenerate generators.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.prime`,
  `TauCeti.FiniteQuadraticModule.NikulinGenerator.exponent`, and
  `TauCeti.FiniteQuadraticModule.NikulinGenerator.rank`: the prime `p`, exponent `k`, and additive
  generator rank (`1` or `2`) of a label.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.toFiniteQuadraticModule`: the concrete finite
  quadratic module attached to a generator label.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.realizationDet`: the Gram determinant of the
  minimal `p`-adic lattice realizing the generator (`θ·p^k`, `θ·2^k`, `-4^k`, or `3·4^k`).
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`: the iterated orthogonal sum of a
  `List NikulinGenerator`.

## Main results

* `TauCeti.FiniteQuadraticModule.NikulinGenerator.natCard_toFiniteQuadraticModule`: every generator
  has order `g.prime ^ (g.rank * g.exponent)`.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.isNondegenerate_toFiniteQuadraticModule_iff`:
  among positive-exponent labels, nondegeneracy is equivalent to `IsAdmissible`.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.rank_toFiniteQuadraticModule`: an admissible
  generator has `AddGroup.rank` equal to `g.rank`.
* `TauCeti.FiniteQuadraticModule.NikulinGenerator.ordProj_natAbs_realizationDet`: for an admissible
  generator, the `g.prime`-part of `|g.realizationDet|` equals the order of its module.
* `TauCeti.FiniteQuadraticModule.piToOrthogonalSumNikulinGeneratorsIsometry`: converts a `Fin n`
  orthogonal family `pi` of generators into `orthogonalSumNikulinGenerators (List.ofFn f)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1, Theorem 1.9.1, and Proposition 1.11.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- **Nikulin's primary generators** (Nikulin, Proposition 1.8.1): the odd cyclic module
`q_θ^{(p)}(p^k)` for an odd prime `p`, the dyadic cyclic module `q_θ^{(2)}(2^k)` for `k ≥ 1`, and
the two dyadic rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)`, represented as labels for an
orthogonal decomposition. -/
inductive NikulinGenerator : Type where
  | oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ)
  | dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ)
  | dyadicU (k : ℕ)
  | dyadicV (k : ℕ)
  deriving DecidableEq

namespace NikulinGenerator

/-- Positive exponent and unit parameter: the labels whose attached finite quadratic module is
nondegenerate and nontrivial. -/
def IsAdmissible : NikulinGenerator → Prop
  | .oddCyclic p k _ _ θ => 0 < k ∧ ¬ (p : ℤ) ∣ θ
  | .dyadicCyclic _ _ θ => Odd θ
  | .dyadicU k => 0 < k
  | .dyadicV k => 0 < k

@[simp]
theorem isAdmissible_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).IsAdmissible ↔ 0 < k ∧ ¬ (p : ℤ) ∣ θ := (Iff.rfl)

@[simp]
theorem isAdmissible_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).IsAdmissible ↔ Odd θ := (Iff.rfl)

@[simp]
theorem isAdmissible_dyadicU (k : ℕ) : (dyadicU k).IsAdmissible ↔ 0 < k := (Iff.rfl)

@[simp]
theorem isAdmissible_dyadicV (k : ℕ) : (dyadicV k).IsAdmissible ↔ 0 < k := (Iff.rfl)

instance instDecidableIsAdmissible : ∀ g : NikulinGenerator, Decidable g.IsAdmissible
  | .oddCyclic p k _ _ θ => inferInstanceAs (Decidable (0 < k ∧ ¬ (p : ℤ) ∣ θ))
  | .dyadicCyclic _ _ θ => inferInstanceAs (Decidable (Odd θ))
  | .dyadicU k => inferInstanceAs (Decidable (0 < k))
  | .dyadicV k => inferInstanceAs (Decidable (0 < k))

/-- The prime at which a Nikulin generator is primary. -/
def prime : NikulinGenerator → ℕ
  | .oddCyclic p _ _ _ _ => p
  | .dyadicCyclic _ _ _ => 2
  | .dyadicU _ => 2
  | .dyadicV _ => 2

@[simp]
theorem prime_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).prime = p := (rfl)

@[simp]
theorem prime_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).prime = 2 := (rfl)

@[simp]
theorem prime_dyadicU (k : ℕ) : (dyadicU k).prime = 2 := (rfl)

@[simp]
theorem prime_dyadicV (k : ℕ) : (dyadicV k).prime = 2 := (rfl)

/-- The prime attached to any Nikulin generator is prime. -/
theorem prime_prime : ∀ g : NikulinGenerator, g.prime.Prime
  | .oddCyclic _ _ hp _ _ => hp
  | .dyadicCyclic _ _ _ => Nat.prime_two
  | .dyadicU _ => Nat.prime_two
  | .dyadicV _ => Nat.prime_two

/-- The prime-power exponent `k` of a Nikulin generator (`p^k` or `2^k`). -/
def exponent : NikulinGenerator → ℕ
  | .oddCyclic _ k _ _ _ => k
  | .dyadicCyclic k _ _ => k
  | .dyadicU k => k
  | .dyadicV k => k

@[simp]
theorem exponent_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).exponent = k := (rfl)

@[simp]
theorem exponent_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).exponent = k := (rfl)

@[simp]
theorem exponent_dyadicU (k : ℕ) : (dyadicU k).exponent = k := (rfl)

@[simp]
theorem exponent_dyadicV (k : ℕ) : (dyadicV k).exponent = k := (rfl)

/-- Every admissible generator has positive exponent. -/
theorem exponent_pos : ∀ {g : NikulinGenerator}, g.IsAdmissible → 0 < g.exponent
  | .oddCyclic _ _ _ _ _, hg => hg.1
  | .dyadicCyclic _ hk _, _ => hk
  | .dyadicU _, hg => hg
  | .dyadicV _, hg => hg

/-- The additive generator rank of a Nikulin generator: `1` on cyclic generators and `2` on the
rank-two dyadic planes `u` and `v`. -/
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

/-- Every generator label has positive formal rank (`1` or `2`). -/
theorem rank_pos : ∀ g : NikulinGenerator, 0 < g.rank
  | .oddCyclic _ _ _ _ _ => Nat.one_pos
  | .dyadicCyclic _ _ _ => Nat.one_pos
  | .dyadicU _ => Nat.two_pos
  | .dyadicV _ => Nat.two_pos

/-- The bundled `FiniteQuadraticModule` attached to a generator label. Marked `@[expose]` so its
underlying carrier and quadratic form reduce definitionally in `Isometry` types. -/
@[expose] noncomputable def toFiniteQuadraticModule : NikulinGenerator → FiniteQuadraticModule.{0}
  | .oddCyclic p k _ hodd θ => FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ
  | .dyadicCyclic k hk θ =>
      letI : NeZero k := ⟨hk.ne'⟩
      FiniteQuadraticModule.dyadicCyclic k θ
  | .dyadicU k => FiniteQuadraticModule.dyadicU k
  | .dyadicV k => FiniteQuadraticModule.dyadicV k

@[simp]
theorem toFiniteQuadraticModule_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).toFiniteQuadraticModule =
      FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).toFiniteQuadraticModule =
      (letI : NeZero k := ⟨hk.ne'⟩; FiniteQuadraticModule.dyadicCyclic k θ) := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicU (k : ℕ) :
    (dyadicU k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicU k := (rfl)

@[simp]
theorem toFiniteQuadraticModule_dyadicV (k : ℕ) :
    (dyadicV k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicV k := (rfl)

/-- **The Gram determinant of the minimal `p`-adic realization of a generator** (Nikulin,
Theorem 1.9.1): `θ·p^k` for `q_θ^{(p)}(p^k)`, `θ·2^k` for `q_θ^{(2)}(2^k)`, `-4^k` for
`u^{(2)}(2^k) = 2^k·U`, and `3·4^k` for `v^{(2)}(2^k) = 2^k·!![2, 1; 1, 2]`. -/
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

/-- The cardinality of the finite quadratic module of `g` is `g.prime ^ (g.rank * g.exponent)`. -/
@[simp]
theorem natCard_toFiniteQuadraticModule :
    ∀ g : NikulinGenerator, Nat.card g.toFiniteQuadraticModule = g.prime ^ (g.rank * g.exponent)
  | .oddCyclic _ _ _ _ _ => by simp
  | .dyadicCyclic k hk _ => by
      let _ : NeZero k := ⟨hk.ne'⟩
      simp
  | .dyadicU k => by simp [two_mul, pow_add]
  | .dyadicV k => by simp [natCard_dyadicV, two_mul, pow_add]

/-- Every admissible generator has cardinality strictly greater than `1`. -/
theorem one_lt_natCard_toFiniteQuadraticModule {g : NikulinGenerator} (hg : g.IsAdmissible) :
    1 < Nat.card g.toFiniteQuadraticModule := by
  rw [g.natCard_toFiniteQuadraticModule]
  exact Nat.one_lt_pow (Nat.mul_pos g.rank_pos (exponent_pos hg)).ne' g.prime_prime.one_lt

/-- For a generator of positive exponent, the attached finite quadratic module is nondegenerate if
and only if the generator is admissible. -/
theorem isNondegenerate_toFiniteQuadraticModule_iff {g : NikulinGenerator}
    (hk : 0 < g.exponent) :
    g.toFiniteQuadraticModule.IsNondegenerate ↔ g.IsAdmissible := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      simp only [exponent_oddCyclic] at hk
      rw [toFiniteQuadraticModule_oddCyclic, isNondegenerate_oddCyclic_iff, Nat.cast_pow,
        IsCoprime.pow_left_iff hk, (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd,
        isAdmissible_oddCyclic]
      exact ⟨fun h ↦ ⟨hk, h⟩, And.right⟩
  | dyadicCyclic k hk' θ =>
      let _ : NeZero k := ⟨hk'.ne'⟩
      simp
  | dyadicU k =>
      simp only [exponent_dyadicU] at hk
      simp [hk, isNondegenerate_dyadicU]
  | dyadicV k =>
      simp only [exponent_dyadicV] at hk
      simp [hk, isNondegenerate_dyadicV]

/-- Every admissible generator produces a nondegenerate finite quadratic module. -/
theorem isNondegenerate_toFiniteQuadraticModule {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.toFiniteQuadraticModule.IsNondegenerate :=
  (isNondegenerate_toFiniteQuadraticModule_iff (exponent_pos hg)).mpr hg

/-- For an admissible generator, the additive generator rank `AddGroup.rank` of its finite
quadratic module coincides with `g.rank`. -/
theorem rank_toFiniteQuadraticModule {g : NikulinGenerator} (hg : g.IsAdmissible) :
    AddGroup.rank g.toFiniteQuadraticModule = g.rank := by
  cases g with
  | oddCyclic p k hp _ θ =>
      rw [isAdmissible_oddCyclic] at hg
      exact (AddGroup.rank_zmod (p ^ k)).trans (by simp [hp.ne_one, hg.1.ne'])
  | dyadicCyclic k hk _ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      exact (AddGroup.rank_zmod (2 ^ k)).trans (by simp [hk.ne'])
  | dyadicU k =>
      rw [isAdmissible_dyadicU] at hg
      have hne : 2 ^ k ≠ 1 := (Nat.one_lt_pow hg.ne' Nat.one_lt_two).ne'
      exact AddGroup.rank_zmod_prod_self hne
  | dyadicV k =>
      rw [isAdmissible_dyadicV] at hg
      have hne : 2 ^ k ≠ 1 := (Nat.one_lt_pow hg.ne' Nat.one_lt_two).ne'
      exact AddGroup.rank_zmod_prod_self hne

/-- The minimal realization Gram determinant of an admissible generator is nonzero. -/
theorem realizationDet_ne_zero {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.realizationDet ≠ 0 := by
  cases g with
  | oddCyclic p k hp _ θ =>
      rw [isAdmissible_oddCyclic] at hg
      have hθ : θ ≠ 0 := fun h0 ↦ hg.2 (h0 ▸ dvd_zero _)
      exact mul_ne_zero hθ (pow_ne_zero k (Nat.cast_ne_zero.mpr hp.ne_zero))
  | dyadicCyclic k _ θ =>
      rw [isAdmissible_dyadicCyclic] at hg
      have hθ : θ ≠ 0 := by
        rintro rfl
        obtain ⟨t, ht⟩ := hg
        omega
      exact mul_ne_zero hθ (pow_ne_zero k (by norm_num))
  | dyadicU k =>
      exact neg_ne_zero.mpr (pow_ne_zero k (by norm_num))
  | dyadicV k =>
      exact mul_ne_zero (by norm_num) (pow_ne_zero k (by norm_num))

private theorem ordProj_mul_pow_of_not_dvd {p a m : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    ordProj[p] (a * p ^ m) = p ^ m := by
  have ha0 : a ≠ 0 := fun h0 ↦ ha (h0 ▸ dvd_zero p)
  rw [Nat.ordProj_mul p ha0 (pow_ne_zero m hp.ne_zero),
    Nat.factorization_eq_zero_of_not_dvd ha, pow_zero, one_mul,
    Nat.ordProj_self_pow hp]

/-- For an admissible generator `g`, the `g.prime`-primary part of `|g.realizationDet|` equals the
cardinality of `g.toFiniteQuadraticModule`. -/
theorem ordProj_natAbs_realizationDet {g : NikulinGenerator} (hg : g.IsAdmissible) :
    ordProj[g.prime] g.realizationDet.natAbs = Nat.card g.toFiniteQuadraticModule := by
  rw [g.natCard_toFiniteQuadraticModule]
  cases g with
  | oddCyclic p k hp _ θ =>
      rw [isAdmissible_oddCyclic] at hg
      have hndvd : ¬ p ∣ θ.natAbs := fun hd ↦ hg.2 (Int.ofNat_dvd_left.mpr hd)
      simp only [prime_oddCyclic, realizationDet_oddCyclic, rank_oddCyclic, exponent_oddCyclic,
        one_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact ordProj_mul_pow_of_not_dvd hp hndvd
  | dyadicCyclic k _ θ =>
      rw [isAdmissible_dyadicCyclic] at hg
      have hndvd : ¬ 2 ∣ θ.natAbs := by
        intro hd
        have h2 : (2 : ℤ) ∣ θ := Int.ofNat_dvd_left.mpr hd
        obtain ⟨t, rfl⟩ := hg
        omega
      simp only [prime_dyadicCyclic, realizationDet_dyadicCyclic, rank_dyadicCyclic,
        exponent_dyadicCyclic, one_mul, Int.natAbs_mul, Int.natAbs_pow]
      exact ordProj_mul_pow_of_not_dvd Nat.prime_two hndvd
  | dyadicU k =>
      have h4 : (-(4 : ℤ) ^ k).natAbs = 1 * 2 ^ (2 * k) := by
        rw [Int.natAbs_neg, Int.natAbs_pow, one_mul, pow_mul]
        rfl
      simp only [prime_dyadicU, realizationDet_dyadicU, rank_dyadicU, exponent_dyadicU, h4]
      exact ordProj_mul_pow_of_not_dvd Nat.prime_two (by decide)
  | dyadicV k =>
      have h4 : (3 * (4 : ℤ) ^ k).natAbs = 3 * 2 ^ (2 * k) := by
        rw [Int.natAbs_mul, Int.natAbs_pow, pow_mul]
        rfl
      simp only [prime_dyadicV, realizationDet_dyadicV, rank_dyadicV, exponent_dyadicV, h4]
      exact ordProj_mul_pow_of_not_dvd Nat.prime_two (by decide)

end NikulinGenerator

/-! ## Orthogonal sums of generator lists -/

/-- The orthogonal sum of a finite list of Nikulin generators; the empty list gives the zero
quadratic module on `PUnit`. Marked `@[expose]` so its carrier and quadratic form reduce
definitionally in `Isometry` types. -/
@[expose] noncomputable def orthogonalSumNikulinGenerators :
    List NikulinGenerator → FiniteQuadraticModule.{0}
  | [] => ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ)))
  | g :: gs => g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs)

@[simp]
theorem orthogonalSumNikulinGenerators_nil :
    orthogonalSumNikulinGenerators [] =
      ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ))) := (rfl)

@[simp]
theorem orthogonalSumNikulinGenerators_cons (g : NikulinGenerator) (gs : List NikulinGenerator) :
    orthogonalSumNikulinGenerators (g :: gs) =
      g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs) := (rfl)

instance instUniqueOrthogonalSumNikulinGeneratorsNil :
    Unique (orthogonalSumNikulinGenerators []) :=
  inferInstanceAs (Unique PUnit.{1})

/-- The cardinality of an orthogonal sum of generators is the product of the generator orders. -/
@[simp]
theorem natCard_orthogonalSumNikulinGenerators :
    ∀ gs : List NikulinGenerator,
      Nat.card (orthogonalSumNikulinGenerators gs) =
        (gs.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod
  | [] => Nat.card_unique
  | g :: gs => by
      rw [orthogonalSumNikulinGenerators_cons, List.map_cons, List.prod_cons,
        ← natCard_orthogonalSumNikulinGenerators gs]
      exact Nat.card_prod g.toFiniteQuadraticModule (orthogonalSumNikulinGenerators gs)

/-- An orthogonal sum of admissible generators is nondegenerate. -/
theorem isNondegenerate_orthogonalSumNikulinGenerators :
    ∀ {gs : List NikulinGenerator}, (∀ g ∈ gs, g.IsAdmissible) →
      (orthogonalSumNikulinGenerators gs).IsNondegenerate
  | [], _ =>
      FiniteBilinearModule.isNondegenerate_of_radical_eq_bot _
        (eq_bot_iff.mpr fun x _ ↦ AddSubgroup.mem_bot.mpr (Subsingleton.elim x 0))
  | g :: gs, hgs => by
      rw [orthogonalSumNikulinGenerators_cons, isNondegenerate_prod]
      exact ⟨NikulinGenerator.isNondegenerate_toFiniteQuadraticModule (hgs g List.mem_cons_self),
        isNondegenerate_orthogonalSumNikulinGenerators fun g' hg' ↦
          hgs g' (List.mem_cons_of_mem g hg')⟩

/-- The Gauss-sum invariant of an orthogonal sum of admissible generators is the sum of the
Gauss-sum invariants of the individual generators. -/
theorem gaussSign_orthogonalSumNikulinGenerators :
    ∀ {gs : List NikulinGenerator}, (∀ g ∈ gs, g.IsAdmissible) →
      (orthogonalSumNikulinGenerators gs).gaussSign =
        (gs.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum
  | [], _ => by
      let _ : Subsingleton (dyadicU 0) := inferInstanceAs (Subsingleton (ZMod 1 × ZMod 1))
      simpa using
        (Isometry.ofSubsingleton :
          Isometry (orthogonalSumNikulinGenerators []) (dyadicU 0)).gaussSign_eq.trans
          (gaussSign_dyadicU 0)
  | g :: gs, hgs => by
      have hg : g.IsAdmissible := hgs g List.mem_cons_self
      have hgs' : ∀ g' ∈ gs, g'.IsAdmissible :=
        fun g' hg' ↦ hgs g' (List.mem_cons_of_mem g hg')
      rw [orthogonalSumNikulinGenerators_cons,
        gaussSign_prod (NikulinGenerator.isNondegenerate_toFiniteQuadraticModule hg)
          (isNondegenerate_orthogonalSumNikulinGenerators hgs'),
        gaussSign_orthogonalSumNikulinGenerators hgs', List.map_cons, List.sum_cons]

/-- Appending two generator lists corresponds to taking the orthogonal product of their orthogonal
sums. -/
noncomputable def orthogonalSumNikulinGeneratorsAppendIsometry :
    ∀ gs₁ gs₂ : List NikulinGenerator,
      Isometry (orthogonalSumNikulinGenerators (gs₁ ++ gs₂))
        ((orthogonalSumNikulinGenerators gs₁).prod (orthogonalSumNikulinGenerators gs₂))
  | [], _ => (QuadraticMap.IsometryEquiv.uniqueProd _ _).symm
  | _ :: gs₁, gs₂ =>
      ((QuadraticMap.IsometryEquiv.refl _).prod
        (orthogonalSumNikulinGeneratorsAppendIsometry gs₁ gs₂)).trans
        (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm

/-- The orthogonal sum of a singleton list `[g]` is isometric to `g.toFiniteQuadraticModule`. -/
noncomputable def orthogonalSumNikulinGeneratorsSingletonIsometry (g : NikulinGenerator) :
    Isometry (orthogonalSumNikulinGenerators [g]) g.toFiniteQuadraticModule :=
  QuadraticMap.IsometryEquiv.prodUnique _ _

/-- The orthogonal sum of a two-element list `[g₁, g₂]` is isometric to the binary orthogonal
product `g₁.toFiniteQuadraticModule.prod g₂.toFiniteQuadraticModule`. -/
noncomputable def orthogonalSumNikulinGeneratorsPairIsometry (g₁ g₂ : NikulinGenerator) :
    Isometry (orthogonalSumNikulinGenerators [g₁, g₂])
      (g₁.toFiniteQuadraticModule.prod g₂.toFiniteQuadraticModule) :=
  (QuadraticMap.IsometryEquiv.refl _).prod (orthogonalSumNikulinGeneratorsSingletonIsometry g₂)

/-- Splitting a member `g ∈ gs` out of a generator list identifies `orthogonalSumNikulinGenerators`
of `gs` with `g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators (gs.erase g))`. -/
noncomputable def orthogonalSumNikulinGeneratorsEraseIsometry (g : NikulinGenerator) :
    ∀ {gs : List NikulinGenerator}, g ∈ gs →
      Isometry (orthogonalSumNikulinGenerators gs)
        (g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators (gs.erase g)))
  | [], hg => nomatch hg
  | h :: gs, hg => by
      by_cases hgh : h = g
      · subst hgh
        rw [List.erase_cons_head]
        exact QuadraticMap.IsometryEquiv.refl _
      · have hbeq : ¬ (h == g) = true := by simpa using hgh
        rw [List.erase_cons_tail hbeq]
        have hg' : g ∈ gs := List.mem_of_ne_of_mem (Ne.symm hgh) hg
        exact ((QuadraticMap.IsometryEquiv.refl _).prod
          (orthogonalSumNikulinGeneratorsEraseIsometry g hg')).trans
          (QuadraticMap.IsometryEquiv.prodLeftComm _ _ _)

/-- An orthogonal family `pi` indexed by `Fin n` of Nikulin generators is isometric to the list
orthogonal sum `orthogonalSumNikulinGenerators (List.ofFn f)`. -/
noncomputable def piToOrthogonalSumNikulinGeneratorsIsometry :
    ∀ {n : ℕ} (f : Fin n → NikulinGenerator),
      Isometry (pi fun i ↦ (f i).toFiniteQuadraticModule)
        (orthogonalSumNikulinGenerators (List.ofFn f))
  | 0, f => by
      rw [List.ofFn_zero]
      exact Isometry.ofSubsingleton
  | _ + 1, f =>
      ((QuadraticMap.IsometryEquiv.consPi _).symm.trans
        ((QuadraticMap.IsometryEquiv.refl _).prod
          (piToOrthogonalSumNikulinGeneratorsIsometry fun i ↦ f i.succ))).trans
        (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators (List.ofFn_succ (f := f)).symm))

end TauCeti.FiniteQuadraticModule
