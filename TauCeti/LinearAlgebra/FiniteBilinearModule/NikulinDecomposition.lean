/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Relations
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.SmallRelations
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Int
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Bundled Nikulin generator decompositions of finite quadratic modules

Every nondegenerate finite quadratic module is isometric to an orthogonal sum of Nikulin's primary
generators (`TauCeti.FiniteQuadraticModule.exists_isometry_prod_pi_generators`):
* `q_θ^{(p)}(p^k)` on `ℤ/p^k` for an odd prime `p`, `k ≥ 1`, and `p ∤ θ`;
* `q_θ^{(2)}(2^k)` on `ℤ/2^k` for `k ≥ 1` and odd `θ`;
* `u^{(2)}(2^k)` and `v^{(2)}(2^k)` on `(ℤ/2^k)²` for `k ≥ 1`.

This file packages those four families into a single inductive label type
`TauCeti.FiniteQuadraticModule.NikulinGenerator`, forms finite orthogonal sums
`TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`, and bundles an admissible generator
list together with an isometry as `TauCeti.FiniteQuadraticModule.NikulinDecomposition`.

From any `D : NikulinDecomposition A`, one reads off:
* the `p`-primary decomposition `D.primaryComponent hp` obtained by filtering `D.generators` to
  generators of prime `p`;
* the group order `Nat.card A`, the `p`-primary order `Nat.card (A.primaryComponent p)`, and the
  Milgram Gauss-sum sign `A.gaussSign`;
* the minimal `p`-adic realization determinant product, factored into a `p`-adic unit times
  `Nat.card (A.primaryComponent p)`;
* the generator ranks `AddGroup.rank (A.primaryComponent p)` (additive across `p`-primary summands)
  and `AddGroup.rank A` (their maximum across primes).

Because Nikulin's generators satisfy small-exponent and dyadic relations, decompositions into
admissible generators are not unique; explicit distinct decompositions of `dyadicCyclic 1 1` and
`(dyadicU k).prod (dyadicU k)` are recorded alongside the quadratic separation of `dyadicU 1` and
`dyadicV 1`.

## Main definitions and results

* `TauCeti.FiniteQuadraticModule.NikulinGenerator`: labels for Nikulin's primary generators, with
  `IsAdmissible`, `prime`, `rank`, `toFiniteQuadraticModule`, `realizationDet`, and
  `realizationUnit`.
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`: orthogonal sum of a generator
  list, with `primaryComponentOrthogonalSumNikulinGeneratorsIsometry` identifying its `p`-primary
  component with the filtered sublist.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition`: bundled admissible generator decomposition,
  with `NikulinDecomposition.ofIsNondegenerate` and `nonempty_nikulinDecomposition_iff`.
* `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`: existence of an orthogonal summand
  `q_θ^{(2)}(2)` with `θ` odd.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1–1.8.2 and §1.9.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

/-! ## Labels for Nikulin's primary generators -/

/-- **Nikulin's primary generators** (Nikulin, Proposition 1.8.1): the odd cyclic module
`q_θ^{(p)}(p^k)` for an odd prime `p`, the dyadic cyclic module `q_θ^{(2)}(2^k)` for `k ≥ 1`, and
the two dyadic rank-two modules `u^{(2)}(2^k)` and `v^{(2)}(2^k)`, as labels for a decomposition. -/
inductive NikulinGenerator where
  /-- Odd cyclic generator `q_θ^{(p)}(p^k)` on `ℤ/p^k`. -/
  | oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ)
  /-- Dyadic cyclic generator `q_θ^{(2)}(2^k)` on `ℤ/2^k` (`k ≥ 1`). -/
  | dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ)
  /-- Dyadic hyperbolic generator `u^{(2)}(2^k)` on `(ℤ/2^k)²`. -/
  | dyadicU (k : ℕ)
  /-- Dyadic elliptic generator `v^{(2)}(2^k)` on `(ℤ/2^k)²`. -/
  | dyadicV (k : ℕ)

namespace NikulinGenerator

/-- Positive exponent and unit parameter: the generators whose associated finite quadratic modules
are nondegenerate and nontrivial. -/
def IsAdmissible : NikulinGenerator → Prop
  | .oddCyclic p k _ _ θ => 0 < k ∧ ¬ (p : ℤ) ∣ θ
  | .dyadicCyclic _ _ θ => Odd θ
  | .dyadicU k => 0 < k
  | .dyadicV k => 0 < k

@[simp]
theorem isAdmissible_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).IsAdmissible ↔ 0 < k ∧ ¬ (p : ℤ) ∣ θ := by
  rfl

@[simp]
theorem isAdmissible_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).IsAdmissible ↔ Odd θ := by
  rfl

@[simp]
theorem isAdmissible_dyadicU (k : ℕ) : (dyadicU k).IsAdmissible ↔ 0 < k := by
  rfl

@[simp]
theorem isAdmissible_dyadicV (k : ℕ) : (dyadicV k).IsAdmissible ↔ 0 < k := by
  rfl

instance : DecidablePred IsAdmissible
  | .oddCyclic p k hp hodd θ => decidable_of_iff' _ (isAdmissible_oddCyclic p k hp hodd θ)
  | .dyadicCyclic k hk θ =>
      decidable_of_iff (θ % 2 = 1) (Int.odd_iff.symm.trans (isAdmissible_dyadicCyclic k hk θ).symm)
  | .dyadicU k => decidable_of_iff' _ (isAdmissible_dyadicU k)
  | .dyadicV k => decidable_of_iff' _ (isAdmissible_dyadicV k)

/-- The prime at which a generator is primary. -/
def prime : NikulinGenerator → ℕ
  | .oddCyclic p _ _ _ _ => p
  | .dyadicCyclic _ _ _ => 2
  | .dyadicU _ => 2
  | .dyadicV _ => 2

@[simp]
theorem prime_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).prime = p := by
  rfl

@[simp]
theorem prime_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).prime = 2 := by
  rfl

@[simp]
theorem prime_dyadicU (k : ℕ) : (dyadicU k).prime = 2 := by
  rfl

@[simp]
theorem prime_dyadicV (k : ℕ) : (dyadicV k).prime = 2 := by
  rfl

/-- Every Nikulin generator is primary at a prime number. -/
theorem prime_prime : ∀ g : NikulinGenerator, g.prime.Prime
  | .oddCyclic _ _ hp _ _ => hp
  | .dyadicCyclic _ _ _ => Nat.prime_two
  | .dyadicU _ => Nat.prime_two
  | .dyadicV _ => Nat.prime_two

/-- The rank of the minimal `p`-adic lattice realizing a generator (`1` for cyclic generators, `2`
for `u` and `v`). For admissible generators this equals `AddGroup.rank` of the finite quadratic
module (`NikulinGenerator.IsAdmissible.rank_toFiniteQuadraticModule`). -/
def rank : NikulinGenerator → ℕ
  | .oddCyclic _ _ _ _ _ => 1
  | .dyadicCyclic _ _ _ => 1
  | .dyadicU _ => 2
  | .dyadicV _ => 2

@[simp]
theorem rank_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).rank = 1 := by
  rfl

@[simp]
theorem rank_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).rank = 1 := by
  rfl

@[simp]
theorem rank_dyadicU (k : ℕ) : (dyadicU k).rank = 2 := by
  rfl

@[simp]
theorem rank_dyadicV (k : ℕ) : (dyadicV k).rank = 2 := by
  rfl

theorem rank_pos : ∀ g : NikulinGenerator, 0 < g.rank
  | .oddCyclic _ _ _ _ _ => Nat.one_pos
  | .dyadicCyclic _ _ _ => Nat.one_pos
  | .dyadicU _ => Nat.zero_lt_two
  | .dyadicV _ => Nat.zero_lt_two

/-- The finite quadratic module associated to a generator: `oddCyclic (p ^ k)`, `dyadicCyclic k`,
`dyadicU k`, or `dyadicV k`. -/
@[expose] noncomputable def toFiniteQuadraticModule : NikulinGenerator → FiniteQuadraticModule.{0}
  | .oddCyclic p k _ hodd θ => FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ
  | .dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      FiniteQuadraticModule.dyadicCyclic k θ
  | .dyadicU k => FiniteQuadraticModule.dyadicU k
  | .dyadicV k => FiniteQuadraticModule.dyadicV k

@[simp]
theorem toFiniteQuadraticModule_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).toFiniteQuadraticModule =
      FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ := by
  rfl

@[simp]
theorem toFiniteQuadraticModule_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).toFiniteQuadraticModule =
      @FiniteQuadraticModule.dyadicCyclic k ⟨hk.ne'⟩ θ := by
  rfl

@[simp]
theorem toFiniteQuadraticModule_dyadicU (k : ℕ) :
    (dyadicU k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicU k := by
  rfl

@[simp]
theorem toFiniteQuadraticModule_dyadicV (k : ℕ) :
    (dyadicV k).toFiniteQuadraticModule = FiniteQuadraticModule.dyadicV k := by
  rfl

/-- **The Gram determinant of the minimal `p`-adic realization of a generator**: `θ · p^k` for
`q_θ^{(p)}(p^k)`, `θ · 2^k` for `q_θ^{(2)}(2^k)`, `-4^k` for `u^{(2)}(2^k)` (`2^k · U`), and
`3 · 4^k` for `v^{(2)}(2^k)` (`2^k · !![2, 1; 1, 2]`). -/
def realizationDet : NikulinGenerator → ℤ
  | .oddCyclic p k _ _ θ => θ * (p : ℤ) ^ k
  | .dyadicCyclic k _ θ => θ * 2 ^ k
  | .dyadicU k => -(4 ^ k)
  | .dyadicV k => 3 * 4 ^ k

@[simp]
theorem realizationDet_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).realizationDet = θ * (p : ℤ) ^ k := by
  rfl

@[simp]
theorem realizationDet_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).realizationDet = θ * 2 ^ k := by
  rfl

@[simp]
theorem realizationDet_dyadicU (k : ℕ) : (dyadicU k).realizationDet = -(4 ^ k) := by
  rfl

@[simp]
theorem realizationDet_dyadicV (k : ℕ) : (dyadicV k).realizationDet = 3 * 4 ^ k := by
  rfl

/-- The unit part of `realizationDet` after dividing out the group order `p^k` or `4^k`. -/
def realizationUnit : NikulinGenerator → ℤ
  | .oddCyclic _ _ _ _ θ => θ
  | .dyadicCyclic _ _ θ => θ
  | .dyadicU _ => -1
  | .dyadicV _ => 3

@[simp]
theorem realizationUnit_oddCyclic (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (θ : ℤ) :
    (oddCyclic p k hp hodd θ).realizationUnit = θ := by
  rfl

@[simp]
theorem realizationUnit_dyadicCyclic (k : ℕ) (hk : 0 < k) (θ : ℤ) :
    (dyadicCyclic k hk θ).realizationUnit = θ := by
  rfl

@[simp]
theorem realizationUnit_dyadicU (k : ℕ) : (dyadicU k).realizationUnit = -1 := by
  rfl

@[simp]
theorem realizationUnit_dyadicV (k : ℕ) : (dyadicV k).realizationUnit = 3 := by
  rfl

/-- The minimal realization determinant factors into `realizationUnit` times the order of the
generator's finite quadratic module. -/
theorem realizationDet_eq_realizationUnit_mul_natCard (g : NikulinGenerator) :
    g.realizationDet = g.realizationUnit * (Nat.card g.toFiniteQuadraticModule : ℤ) := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      simp [natCard_oddCyclic]
  | dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      simp [natCard_dyadicCyclic]
  | dyadicU k =>
      have h4 : (4 : ℤ) ^ k = (2 : ℤ) ^ k * (2 : ℤ) ^ k := by
        rw [← mul_pow]
        norm_num
      simp only [realizationDet_dyadicU, realizationUnit_dyadicU, toFiniteQuadraticModule_dyadicU,
        natCard_dyadicU, h4]
      push_cast
      ring
  | dyadicV k =>
      have h4 : (4 : ℤ) ^ k = (2 : ℤ) ^ k * (2 : ℤ) ^ k := by
        rw [← mul_pow]
        norm_num
      simp only [realizationDet_dyadicV, realizationUnit_dyadicV, toFiniteQuadraticModule_dyadicV,
        natCard_dyadicV, h4]
      push_cast
      ring

/-- Every generator's finite quadratic module is an additive `g.prime`-group. -/
theorem isAddPGroup_toFiniteQuadraticModule (g : NikulinGenerator) :
    IsAddPGroup g.prime g.toFiniteQuadraticModule := by
  cases g with
  | oddCyclic p k _ _ _ =>
      exact IsAddPGroup.zmod_prime_pow p k
  | dyadicCyclic k _ _ =>
      exact IsAddPGroup.zmod_prime_pow 2 k
  | dyadicU k =>
      exact IsAddPGroup.prod (IsAddPGroup.zmod_prime_pow 2 k) (IsAddPGroup.zmod_prime_pow 2 k)
  | dyadicV k =>
      exact IsAddPGroup.prod (IsAddPGroup.zmod_prime_pow 2 k) (IsAddPGroup.zmod_prime_pow 2 k)

/-- Admissibility is equivalent to nondegeneracy together with nontriviality of the associated
finite quadratic module. -/
theorem isAdmissible_iff (g : NikulinGenerator) :
    g.IsAdmissible ↔
      g.toFiniteQuadraticModule.IsNondegenerate ∧ Nontrivial g.toFiniteQuadraticModule := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      rw [isAdmissible_oddCyclic, toFiniteQuadraticModule_oddCyclic, isNondegenerate_oddCyclic_iff]
      have hnt : Nontrivial (FiniteQuadraticModule.oddCyclic (p ^ k) hodd.pow θ) ↔ 0 < k := by
        rw [← Finite.one_lt_card_iff_nontrivial, natCard_oddCyclic]
        exact ⟨fun h ↦ Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at h,
          fun hk ↦ Nat.one_lt_pow hk.ne' hp.one_lt⟩
      rw [hnt, @and_comm (IsCoprime _ _)]
      refine and_congr_right fun hk ↦ ?_
      have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rw [Nat.cast_pow, ← isRelPrime_iff_isCoprime, IsRelPrime.pow_left_iff hk,
        isRelPrime_iff_isCoprime, hp'.coprime_iff_not_dvd]
  | dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      rw [isAdmissible_dyadicCyclic, toFiniteQuadraticModule_dyadicCyclic,
        isNondegenerate_dyadicCyclic_iff]
      have hnt : Nontrivial (FiniteQuadraticModule.dyadicCyclic k θ) := by
        rw [← Finite.one_lt_card_iff_nontrivial, natCard_dyadicCyclic]
        exact Nat.one_lt_pow hk.ne' Nat.one_lt_two
      exact (and_iff_left hnt).symm
  | dyadicU k =>
      rw [isAdmissible_dyadicU, toFiniteQuadraticModule_dyadicU,
        and_iff_right (isNondegenerate_dyadicU k), ← Finite.one_lt_card_iff_nontrivial,
        natCard_dyadicU]
      exact ⟨fun hk ↦ one_lt_mul_of_lt_of_le (Nat.one_lt_pow hk.ne' Nat.one_lt_two)
        (Nat.one_le_pow k 2 Nat.zero_lt_two),
        fun h ↦ Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at h⟩
  | dyadicV k =>
      rw [isAdmissible_dyadicV, toFiniteQuadraticModule_dyadicV,
        and_iff_right (isNondegenerate_dyadicV k), ← Finite.one_lt_card_iff_nontrivial,
        natCard_dyadicV]
      exact ⟨fun hk ↦ one_lt_mul_of_lt_of_le (Nat.one_lt_pow hk.ne' Nat.one_lt_two)
        (Nat.one_le_pow k 2 Nat.zero_lt_two),
        fun h ↦ Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at h⟩

theorem IsAdmissible.isNondegenerate {g : NikulinGenerator} (hg : g.IsAdmissible) :
    g.toFiniteQuadraticModule.IsNondegenerate :=
  ((isAdmissible_iff g).mp hg).1

theorem IsAdmissible.nontrivial {g : NikulinGenerator} (hg : g.IsAdmissible) :
    Nontrivial g.toFiniteQuadraticModule :=
  ((isAdmissible_iff g).mp hg).2

/-- For an admissible generator, `realizationUnit` is coprime to `g.prime` in `ℤ`. -/
theorem IsAdmissible.isCoprime_prime_realizationUnit {g : NikulinGenerator} (hg : g.IsAdmissible) :
    IsCoprime (g.prime : ℤ) g.realizationUnit := by
  cases g with
  | oddCyclic p k hp _ θ =>
      exact (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hg.2
  | dyadicCyclic _ _ θ =>
      obtain ⟨m, rfl⟩ := hg
      exact ⟨-m, 1, by simp [prime, realizationUnit]; ring⟩
  | dyadicU _ =>
      exact ⟨0, -1, by norm_num [prime, realizationUnit]⟩
  | dyadicV _ =>
      exact ⟨-1, 1, by norm_num [prime, realizationUnit]⟩

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
  | oddCyclic p k hp _ θ =>
      exact AddGroup.rank_zmod_prime_pow hp hg.1
  | dyadicCyclic k hk θ =>
      exact AddGroup.rank_zmod_prime_pow Nat.prime_two hk
  | dyadicU k =>
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hg hg
  | dyadicV k =>
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hg hg

end NikulinGenerator

/-! ## Orthogonal sums of generator lists -/

/-- The orthogonal sum of a finite list of Nikulin generators; the empty list gives the zero module
on `PUnit`. -/
@[expose] noncomputable def orthogonalSumNikulinGenerators :
    List NikulinGenerator → FiniteQuadraticModule.{0}
  | [] => ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ)))
  | g :: gs => g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs)

@[simp]
theorem orthogonalSumNikulinGenerators_nil :
    orthogonalSumNikulinGenerators [] =
      ofQuadraticMap (0 : QuadraticMap ℤ PUnit.{1} (AddCircle (1 : ℚ))) := by
  rfl

@[simp]
theorem orthogonalSumNikulinGenerators_cons (g : NikulinGenerator) (gs : List NikulinGenerator) :
    orthogonalSumNikulinGenerators (g :: gs) =
      g.toFiniteQuadraticModule.prod (orthogonalSumNikulinGenerators gs) := by
  rfl

instance : Subsingleton (orthogonalSumNikulinGenerators []) :=
  inferInstanceAs (Subsingleton PUnit.{1})

noncomputable instance : Unique (orthogonalSumNikulinGenerators []) :=
  uniqueOfSubsingleton 0

/-- An orthogonal sum of Nikulin generators is nondegenerate iff every summand in the list is
nondegenerate. -/
@[simp]
theorem isNondegenerate_orthogonalSumNikulinGenerators_iff (gs : List NikulinGenerator) :
    (orthogonalSumNikulinGenerators gs).IsNondegenerate ↔
      ∀ g ∈ gs, g.toFiniteQuadraticModule.IsNondegenerate := by
  induction gs with
  | nil =>
      refine ⟨(fun _ _ h ↦ nomatch h), fun _ ↦ ?_⟩
      exact (orthogonalSumNikulinGenerators
        []).toFiniteBilinearModule.isNondegenerate_iff_injective.mpr fun x y _ ↦
        Subsingleton.elim x y
  | cons g gs ih =>
      rw [orthogonalSumNikulinGenerators_cons, isNondegenerate_prod, ih, List.forall_mem_cons]

/-- The order of an orthogonal sum of Nikulin generators is the product of the orders of its
summands. -/
theorem natCard_orthogonalSumNikulinGenerators (gs : List NikulinGenerator) :
    Nat.card (orthogonalSumNikulinGenerators gs) =
      (gs.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod := by
  induction gs with
  | nil =>
      exact @Nat.card_unique (orthogonalSumNikulinGenerators []) _ _
  | cons g gs ih =>
      rw [orthogonalSumNikulinGenerators_cons, List.map_cons, List.prod_cons, Nat.card_prod, ih]

/-- The Gauss-sum invariant `gaussSign` is additive across an orthogonal sum of nondegenerate
Nikulin generators. -/
theorem gaussSign_orthogonalSumNikulinGenerators {gs : List NikulinGenerator}
    (hgs : ∀ g ∈ gs, g.toFiniteQuadraticModule.IsNondegenerate) :
    (orthogonalSumNikulinGenerators gs).gaussSign =
      (gs.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum := by
  induction gs with
  | nil =>
      exact gaussSign_eq_zero_of_subsingleton (orthogonalSumNikulinGenerators [])
  | cons g gs ih =>
      have hg : g.toFiniteQuadraticModule.IsNondegenerate := hgs g List.mem_cons_self
      have htail : ∀ g' ∈ gs, g'.toFiniteQuadraticModule.IsNondegenerate :=
        fun g' hg' ↦ hgs g' (List.mem_cons_of_mem g hg')
      have hnd : (orthogonalSumNikulinGenerators gs).IsNondegenerate :=
        (isNondegenerate_orthogonalSumNikulinGenerators_iff gs).mpr htail
      rw [orthogonalSumNikulinGenerators_cons, gaussSign_prod hg hnd, List.map_cons, List.sum_cons,
        ih htail]

/-- Concatenating two generator lists corresponds to taking the orthogonal product of their
orthogonal sums. -/
noncomputable def orthogonalSumNikulinGeneratorsAppendIsometry
    (gs₁ gs₂ : List NikulinGenerator) :
    (orthogonalSumNikulinGenerators (gs₁ ++ gs₂)).Isometry
      ((orthogonalSumNikulinGenerators gs₁).prod (orthogonalSumNikulinGenerators gs₂)) := by
  induction gs₁ with
  | nil =>
      exact (QuadraticMap.IsometryEquiv.uniqueProd
        (orthogonalSumNikulinGenerators []).quadratic
        (orthogonalSumNikulinGenerators gs₂).quadratic).symm
  | cons g gs₁ ih =>
      exact ((QuadraticMap.IsometryEquiv.refl g.toFiniteQuadraticModule.quadratic).prod ih).trans
        (QuadraticMap.IsometryEquiv.prodAssoc g.toFiniteQuadraticModule.quadratic
          (orthogonalSumNikulinGenerators gs₁).quadratic
          (orthogonalSumNikulinGenerators gs₂).quadratic).symm

/-- A single Nikulin generator is canonically isometric to its singleton orthogonal sum. -/
noncomputable def singletonNikulinGeneratorIsometry (g : NikulinGenerator) :
    g.toFiniteQuadraticModule.Isometry (orthogonalSumNikulinGenerators [g]) :=
  ((QuadraticMap.IsometryEquiv.uniqueProd (orthogonalSumNikulinGenerators []).quadratic
    g.toFiniteQuadraticModule.quadratic).symm).trans
    (QuadraticMap.IsometryEquiv.prodComm (orthogonalSumNikulinGenerators []).quadratic
      g.toFiniteQuadraticModule.quadratic)

/-- If every generator in `gs` has prime `p`, their orthogonal sum is an additive `p`-group. -/
theorem isAddPGroup_orthogonalSumNikulinGenerators {p : ℕ} {gs : List NikulinGenerator}
    (h : ∀ g ∈ gs, g.prime = p) :
    IsAddPGroup p (orthogonalSumNikulinGenerators gs) := by
  induction gs with
  | nil =>
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  | cons g gs ih =>
      have hg : IsAddPGroup p g.toFiniteQuadraticModule :=
        h g List.mem_cons_self ▸ g.isAddPGroup_toFiniteQuadraticModule
      exact IsAddPGroup.prod hg (ih fun g' hg' ↦ h g' (List.mem_cons_of_mem g hg'))

/-- For a list of admissible `p`-primary generators (`p` prime), the generator rank `AddGroup.rank`
of their orthogonal sum is the sum of their individual ranks (`1` for cyclic, `2` for `u` and
`v`). -/
theorem rank_orthogonalSumNikulinGenerators_of_prime {p : ℕ} (hp : p.Prime)
    {gs : List NikulinGenerator} (hadm : ∀ g ∈ gs, g.IsAdmissible)
    (hprime : ∀ g ∈ gs, g.prime = p) :
    AddGroup.rank (orthogonalSumNikulinGenerators gs) = (gs.map NikulinGenerator.rank).sum := by
  induction gs with
  | nil =>
      exact AddGroup.rank_eq_zero_iff.mpr inferInstance
  | cons g gs ih =>
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

/-- For prime `p`, the `p`-primary component of an orthogonal sum of Nikulin generators is isometric
to the orthogonal sum of the sublist of generators with `g.prime = p`. -/
noncomputable def primaryComponentOrthogonalSumNikulinGeneratorsIsometry {p : ℕ} (hp : p.Prime) :
    ∀ gs : List NikulinGenerator,
      ((orthogonalSumNikulinGenerators gs).primaryComponent p).Isometry
        (orthogonalSumNikulinGenerators (gs.filter fun g ↦ g.prime = p))
  | [] =>
      let _ : Subsingleton ((orthogonalSumNikulinGenerators []).primaryComponent p) :=
        inferInstanceAs (Subsingleton (AddCommGroup.primaryComponent PUnit.{1} p))
      (Isometry.ofSubsingleton :
        ((orthogonalSumNikulinGenerators []).primaryComponent p).Isometry
          (orthogonalSumNikulinGenerators []))
  | g :: gs =>
      let ih := primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp gs
      let split := primaryComponentProdIsometry g.toFiniteQuadraticModule
        (orthogonalSumNikulinGenerators gs) p
      if hgp : g.prime = p then
        have hgP : IsAddPGroup p g.toFiniteQuadraticModule :=
          hgp ▸ g.isAddPGroup_toFiniteQuadraticModule
        have hfilt : (g :: gs).filter (fun g' ↦ g'.prime = p) =
            g :: gs.filter (fun g' ↦ g'.prime = p) := by
          simp [hgp]
        split.trans (((primaryComponentIsometrySelfOfIsAddPGroup hgP).prod ih).trans
          (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators hfilt.symm)))
      else
        have hsub : Subsingleton (g.toFiniteQuadraticModule.primaryComponent p) :=
          subsingleton_primaryComponent_of_isAddPGroup_of_ne hp g.prime_prime (Ne.symm hgp)
            g.isAddPGroup_toFiniteQuadraticModule
        let _ : Unique (g.toFiniteQuadraticModule.primaryComponent p) :=
          @uniqueOfSubsingleton _ hsub 0
        have hfilt : (g :: gs).filter (fun g' ↦ g'.prime = p) =
            gs.filter (fun g' ↦ g'.prime = p) := by
          simp [hgp]
        split.trans (((QuadraticMap.IsometryEquiv.refl _).prod ih).trans
          ((QuadraticMap.IsometryEquiv.uniqueProd _ _).trans
            (Isometry.ofEq (congrArg orthogonalSumNikulinGenerators hfilt.symm))))

/-! ## Bundled generator decompositions -/

/-- **A Nikulin generator decomposition** of a finite quadratic module: a list of admissible
primary generators together with an isometry onto their orthogonal sum. -/
structure NikulinDecomposition (A : FiniteQuadraticModule.{u}) where
  /-- The primary generators, as labels. -/
  generators : List NikulinGenerator
  /-- Each generator in the list is nondegenerate and nontrivial. -/
  admissible : ∀ g ∈ generators, g.IsAdmissible
  /-- The module is isometric to the orthogonal sum of `generators`. -/
  isometry : A.Isometry (orthogonalSumNikulinGenerators generators)

private noncomputable def piNikulinGeneratorsIsometry :
    ∀ {n : ℕ} (g : Fin n → NikulinGenerator),
      (pi fun i ↦ (g i).toFiniteQuadraticModule).Isometry
        (orthogonalSumNikulinGenerators (List.ofFn g))
  | 0, g =>
      let _ : Subsingleton (orthogonalSumNikulinGenerators (List.ofFn g)) := by
        rw [List.ofFn_zero]
        infer_instance
      Isometry.ofSubsingleton
  | n + 1, g =>
      (QuadraticMap.IsometryEquiv.consPi
        (fun i : Fin (n + 1) ↦ (g i).toFiniteQuadraticModule.quadratic)).symm.trans
        (((QuadraticMap.IsometryEquiv.refl _).prod
          (piNikulinGeneratorsIsometry fun i ↦ g i.succ)).trans
          (Isometry.ofEq
            (congrArg orthogonalSumNikulinGenerators (List.ofFn_succ (f := g)).symm)))

private theorem exists_oddCyclic_nikulinGenerator {m : ℕ} (hm : Odd m) {θ : ℤ}
    (hmθ : IsPrimePow m ∧ IsCoprime (m : ℤ) θ) :
    ∃ g : NikulinGenerator, g.IsAdmissible ∧
      oddCyclic m hm θ = g.toFiniteQuadraticModule := by
  obtain ⟨p, e, hp, he, hpe⟩ := (isPrimePow_nat_iff m).mp hmθ.1
  have hpodd : Odd p := by
    refine hp.odd_of_ne_two ?_
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hm
      (even_iff_two_dvd.mpr (hpe ▸ dvd_pow_self 2 he.ne'))
  have hpndvd : ¬ ((p : ℤ) ∣ θ) := fun hdiv ↦ by
    have hpm : (p : ℤ) ∣ (m : ℤ) := by
      rw [← hpe, Nat.cast_pow]
      exact dvd_pow_self (p : ℤ) he.ne'
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (hmθ.2.isUnit_of_dvd' hpm hdiv)
  refine ⟨.oddCyclic p e hp hpodd θ, ⟨he, hpndvd⟩, ?_⟩
  simp [← hpe]

private theorem nonempty_nikulinDecomposition_of_isNondegenerate {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) : Nonempty (NikulinDecomposition A) := by
  classical
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨e₀⟩⟩ :=
    exists_isometry_prod_pi_generators A hA
  choose gOdd hgOddAdm hOddEq using
    fun i : Fin a ↦ exists_oddCyclic_nikulinGenerator (hm i) (hmθ i)
  let gDyadicCyc : Fin b → NikulinGenerator :=
    fun i ↦ .dyadicCyclic (k i + 1) (Nat.succ_pos (k i)) (η i)
  let gU : Fin c → NikulinGenerator := fun i ↦ .dyadicU (ku i + 1)
  let gV : Fin d → NikulinGenerator := fun i ↦ .dyadicV (kv i + 1)
  let isoOdd : (pi fun i ↦ oddCyclic (m i) (hm i) (θ i)).Isometry
      (orthogonalSumNikulinGenerators (List.ofFn gOdd)) :=
    (QuadraticMap.IsometryEquiv.pi fun i ↦ Isometry.ofEq (hOddEq i)).trans
      (piNikulinGeneratorsIsometry gOdd)
  let isoCyc : (pi fun i ↦ dyadicCyclic (k i + 1) (η i)).Isometry
      (orthogonalSumNikulinGenerators (List.ofFn gDyadicCyc)) :=
    piNikulinGeneratorsIsometry gDyadicCyc
  let isoU : (pi fun i ↦ dyadicU (ku i + 1)).Isometry
      (orthogonalSumNikulinGenerators (List.ofFn gU)) :=
    piNikulinGeneratorsIsometry gU
  let isoV : (pi fun i ↦ dyadicV (kv i + 1)).Isometry
      (orthogonalSumNikulinGenerators (List.ofFn gV)) :=
    piNikulinGeneratorsIsometry gV
  let gs := List.ofFn gOdd ++ (List.ofFn gDyadicCyc ++ (List.ofFn gU ++ List.ofFn gV))
  refine ⟨{
    generators := gs
    admissible := ?_
    isometry := e₀.symm.trans
      ((isoOdd.prod (isoCyc.prod (isoU.prod isoV))).trans
        (((QuadraticMap.IsometryEquiv.refl _).prod
          (((QuadraticMap.IsometryEquiv.refl _).prod
            (orthogonalSumNikulinGeneratorsAppendIsometry _ _).symm).trans
            (orthogonalSumNikulinGeneratorsAppendIsometry _ _).symm)).trans
          (orthogonalSumNikulinGeneratorsAppendIsometry _ _).symm)) }⟩
  intro g hg
  simp only [gs, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hgOddAdm i
  · exact hη i
  · exact Nat.succ_pos (ku i)
  · exact Nat.succ_pos (kv i)

/-- **Every nondegenerate finite quadratic module admits an admissible Nikulin generator
decomposition** (Nikulin, Proposition 1.8.1). -/
noncomputable def NikulinDecomposition.ofIsNondegenerate {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) : NikulinDecomposition A :=
  Classical.choice (nonempty_nikulinDecomposition_of_isNondegenerate hA)

/-- A finite quadratic module admits a `NikulinDecomposition` if and only if it is
nondegenerate. -/
theorem nonempty_nikulinDecomposition_iff (A : FiniteQuadraticModule.{u}) :
    Nonempty (NikulinDecomposition A) ↔ A.IsNondegenerate :=
  ⟨fun ⟨D⟩ ↦ D.isometry.isNondegenerate_iff.mpr
      ((isNondegenerate_orthogonalSumNikulinGenerators_iff D.generators).mpr
        fun g hg ↦ (D.admissible g hg).isNondegenerate),
    nonempty_nikulinDecomposition_of_isNondegenerate⟩

namespace NikulinDecomposition

/-- The empty Nikulin decomposition of a trivial finite quadratic module. -/
noncomputable def zero (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    NikulinDecomposition A where
  generators := []
  admissible _ h := nomatch h
  isometry := Isometry.ofSubsingleton

/-- Transport a `NikulinDecomposition` along an isometry. -/
noncomputable def ofIsometry {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (D : NikulinDecomposition B) : NikulinDecomposition A where
  generators := D.generators
  admissible := D.admissible
  isometry := f.trans D.isometry

/-- Concatenate two Nikulin decompositions to decompose an orthogonal direct sum. -/
noncomputable def prod {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    NikulinDecomposition (A.prod B) where
  generators := DA.generators ++ DB.generators
  admissible g hg := by
    rcases List.mem_append.mp hg with hA | hB
    · exact DA.admissible g hA
    · exact DB.admissible g hB
  isometry := (DA.isometry.prod DB.isometry).trans
    (orthogonalSumNikulinGeneratorsAppendIsometry DA.generators DB.generators).symm

/-- Filtering a `NikulinDecomposition` to generators with `g.prime = p` yields a
`NikulinDecomposition` of the `p`-primary component `A.primaryComponent p`. -/
noncomputable def primaryComponent {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) : NikulinDecomposition (A.primaryComponent p) where
  generators := D.generators.filter fun g ↦ g.prime = p
  admissible g hg := D.admissible g (List.mem_of_mem_filter hg)
  isometry := (D.isometry.primaryComponent p).trans
    (primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp D.generators)

@[simp]
theorem primaryComponent_generators {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) :
    (D.primaryComponent hp).generators = D.generators.filter fun g ↦ g.prime = p := by
  rfl

/-- Any module admitting a `NikulinDecomposition` is nondegenerate. -/
theorem isNondegenerate {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) :
    A.IsNondegenerate :=
  (nonempty_nikulinDecomposition_iff A).mp ⟨D⟩

/-- The order of `A` is the product of the orders of the generators in `D`. -/
theorem natCard_eq {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) :
    Nat.card A = (D.generators.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod := by
  rw [Nat.card_congr D.isometry.toLinearEquiv.toEquiv, natCard_orthogonalSumNikulinGenerators]

/-- For prime `p`, the order of `A.primaryComponent p` is the product of the orders of the
`p`-primary generators in `D`. -/
theorem natCard_primaryComponent_eq {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) :
    Nat.card (A.primaryComponent p) =
      ((D.generators.filter fun g ↦ g.prime = p).map
        fun g ↦ Nat.card g.toFiniteQuadraticModule).prod :=
  (D.primaryComponent hp).natCard_eq

/-- At any prime `p`, the product of `realizationDet` across the `p`-primary generators of `D`
equals the product of their `realizationUnit`s times `Nat.card (A.primaryComponent p)`. -/
theorem prod_realizationDet_filter_eq {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) :
    ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationUnit).prod *
        (Nat.card (A.primaryComponent p) : ℤ) := by
  rw [D.natCard_primaryComponent_eq hp]
  induction (D.generators.filter fun g ↦ g.prime = p) with
  | nil =>
      simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul,
        g.realizationDet_eq_realizationUnit_mul_natCard]
      rw [ih]
      ring

/-- The product of `realizationUnit` across the `p`-primary generators of `D` is coprime to `p`. -/
theorem isCoprime_prod_realizationUnit_filter {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) (p : ℕ) :
    IsCoprime (p : ℤ)
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationUnit).prod := by
  have h : ∀ {gs : List NikulinGenerator},
      (∀ g ∈ gs, g.IsAdmissible ∧ g.prime = p) →
      IsCoprime (p : ℤ) (gs.map NikulinGenerator.realizationUnit).prod := by
    intro gs hgs
    induction gs with
    | nil => exact isCoprime_one_right
    | cons g gs ih =>
        obtain ⟨hadm, rfl⟩ := hgs g List.mem_cons_self
        exact hadm.isCoprime_prime_realizationUnit.mul_right
          (ih fun g' hg' ↦ hgs g' (List.mem_cons_of_mem g hg'))
  exact h fun g hg ↦
    ⟨D.admissible g (List.mem_of_mem_filter hg), of_decide_eq_true (List.mem_filter.mp hg).2⟩

/-- The product of `realizationDet` across the `p`-primary generators of `D` is nonzero. -/
theorem prod_realizationDet_filter_ne_zero {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) (p : ℕ) :
    ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod ≠ 0 := by
  refine List.prod_ne_zero ?_
  intro h0
  obtain ⟨g, hg, hg0⟩ := List.mem_map.mp h0
  exact (D.admissible g (List.mem_of_mem_filter hg)).realizationDet_ne_zero hg0

/-- The Gauss-sum invariant `A.gaussSign` equals the sum of `gaussSign` over `D.generators`. -/
theorem gaussSign_eq {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) :
    A.gaussSign = (D.generators.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum := by
  rw [D.isometry.gaussSign_eq, gaussSign_orthogonalSumNikulinGenerators
    (fun g hg ↦ (D.admissible g hg).isNondegenerate)]

/-- **Primary generator rank from a Nikulin decomposition**: for prime `p`, the minimal number of
generators `AddGroup.rank (A.primaryComponent p)` equals the sum of `g.rank` (`1` on cyclic
generators, `2` on `u` and `v`) over the `p`-primary generators of `D`. In particular this weighted
count depends only on `A` and `p`, not on the choice of decomposition `D`. -/
theorem rank_primaryComponent {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (A.primaryComponent p) =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  rw [AddGroup.rank_congr (D.primaryComponent hp).isometry.toLinearEquiv.toAddEquiv]
  exact rank_orthogonalSumNikulinGenerators_of_prime hp (D.primaryComponent hp).admissible
    fun g hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2

/-- **Total length `l(A)` from a Nikulin decomposition**: the minimal number of generators
`AddGroup.rank A` is the supremum over prime factors of `Nat.card A` of the `p`-primary generator
rank sums read off `D`. -/
theorem rank_eq {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) :
    AddGroup.rank A =
      (Nat.card A).primeFactors.sup fun p ↦
        ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  rw [AddGroup.rank_eq_sup_primaryComponents A]
  refine Finset.sup_congr rfl fun p hp ↦ ?_
  exact D.rank_primaryComponent (Nat.prime_of_mem_primeFactors hp)

end NikulinDecomposition

/-! ## Cyclic order-two dyadic summands -/

/-- **Nikulin's dyadic condition-(4) predicate**: `A` splits off a cyclic dyadic summand
`q_θ^{(2)}(2)` for some odd integer `θ`. -/
def HasCyclicTwoSummand (A : FiniteQuadraticModule.{u}) : Prop :=
  ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
    Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A'))

/-- `HasCyclicTwoSummand` is invariant under quadratic isometry. -/
theorem Isometry.hasCyclicTwoSummand_iff {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) :
    HasCyclicTwoSummand A ↔ HasCyclicTwoSummand B :=
  ⟨fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.symm.trans g⟩⟩,
    fun ⟨θ, A', hθ, ⟨g⟩⟩ ↦ ⟨θ, A', hθ, ⟨f.trans g⟩⟩⟩

/-- If a `NikulinDecomposition` of `A` contains `.dyadicCyclic 1 hk θ`, then `A` has a cyclic
order-two dyadic summand. -/
theorem NikulinDecomposition.hasCyclicTwoSummand_of_mem {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {hk : 0 < 1} {θ : ℤ}
    (hmem : NikulinGenerator.dyadicCyclic 1 hk θ ∈ D.generators) :
    HasCyclicTwoSummand A := by
  obtain ⟨gs₁, gs₂, hsplit⟩ := List.append_of_mem hmem
  have hθ : Odd θ := D.admissible _ hmem
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

/-! ## Non-uniqueness of decompositions and quadratic-vs-bilinear separation -/

/-- Standard single-generator decomposition `[q_1^{(2)}(2)]` of `dyadicCyclic 1 1`. -/
noncomputable def nikulinDecompositionDyadicCyclicOne :
    NikulinDecomposition (dyadicCyclic 1 1) where
  generators := [.dyadicCyclic 1 Nat.one_pos 1]
  admissible g hg := by
    rw [List.mem_singleton] at hg
    subst hg
    exact odd_one
  isometry := singletonNikulinGeneratorIsometry (.dyadicCyclic 1 Nat.one_pos 1)

/-- Alternative single-generator decomposition `[q_5^{(2)}(2)]` of `dyadicCyclic 1 1` via Nikulin's
relation `q_1^{(2)}(2) ≅ q_5^{(2)}(2)` (`dyadicCyclicOneIsometryFiveMul`). -/
noncomputable def nikulinDecompositionDyadicCyclicOneFive :
    NikulinDecomposition (dyadicCyclic 1 1) where
  generators := [.dyadicCyclic 1 Nat.one_pos 5]
  admissible g hg := by
    rw [List.mem_singleton] at hg
    subst hg
    exact ⟨2, by ring⟩
  isometry := (dyadicCyclicOneIsometryFiveMul 1).trans
    (singletonNikulinGeneratorIsometry (.dyadicCyclic 1 Nat.one_pos 5))

/-- Standard two-generator decomposition `[u^{(2)}(2^k), u^{(2)}(2^k)]` of
`(dyadicU k).prod (dyadicU k)` (`k > 0`). -/
noncomputable def nikulinDecompositionDyadicUProdSelf {k : ℕ} (hk : 0 < k) :
    NikulinDecomposition ((dyadicU k).prod (dyadicU k)) :=
  let U : NikulinDecomposition (dyadicU k) :=
    { generators := [.dyadicU k]
      admissible := fun g hg ↦ by
        rw [List.mem_singleton] at hg
        subst hg
        exact hk
      isometry := singletonNikulinGeneratorIsometry (.dyadicU k) }
  U.prod U

/-- Alternative two-generator decomposition `[v^{(2)}(2^k), v^{(2)}(2^k)]` of
`(dyadicU k).prod (dyadicU k)` (`k > 0`) via `u^{(2)}(2^k)^2 ≅ v^{(2)}(2^k)^2`
(`dyadicUProdSelfIsometryDyadicVProdSelf`). -/
noncomputable def nikulinDecompositionDyadicUProdSelfAsV {k : ℕ} (hk : 0 < k) :
    NikulinDecomposition ((dyadicU k).prod (dyadicU k)) :=
  let V : NikulinDecomposition (dyadicV k) :=
    { generators := [.dyadicV k]
      admissible := fun g hg ↦ by
        rw [List.mem_singleton] at hg
        subst hg
        exact hk
      isometry := singletonNikulinGeneratorIsometry (.dyadicV k) }
  NikulinDecomposition.ofIsometry (dyadicUProdSelfIsometryDyadicVProdSelf k) (V.prod V)

/-- Although `dyadicU 1` and `dyadicV 1` have isometric polar bilinear pairings
(`dyadicUOneBilinearIsometryDyadicVOne`), they are **not** isometric as finite quadratic modules:
their Gauss-sum invariants in `ℤ/8` are `0` and `4`. -/
theorem not_nonempty_isometry_dyadicU_one_dyadicV_one :
    ¬ Nonempty ((dyadicU 1).Isometry (dyadicV 1)) := by
  rintro ⟨f⟩
  have hsign := f.gaussSign_eq
  rw [gaussSign_eq_zero_of_isMetabolic (isMetabolic_dyadicU 1), gaussSign_dyadicV] at hsign
  exact absurd hsign (by decide)

end TauCeti.FiniteQuadraticModule
