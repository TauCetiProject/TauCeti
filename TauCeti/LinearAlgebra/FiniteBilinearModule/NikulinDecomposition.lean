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
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Int
import TauCeti.Algebra.Group.Primary.Generators
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
* the product of Gram determinants of the standard minimal-rank `p`-adic lattices attached to the
  generator labels, factored into a `p`-adic unit times `Nat.card (A.primaryComponent p)`;
* the generator ranks `AddGroup.rank (A.primaryComponent p)` (additive across `p`-primary summands)
  and `AddGroup.rank A` (their maximum across primes).

Because Nikulin's generators satisfy small-exponent and dyadic relations, decompositions into
admissible generators are not unique; explicit distinct decompositions of `dyadicCyclic 1 θ`
(`θ` odd) and `(dyadicU k).prod (dyadicU k)` (`k > 0`) are recorded at the end of this file.

## Main definitions and results

* `TauCeti.FiniteQuadraticModule.NikulinGenerator`: labels for Nikulin's primary generators, with
  `IsAdmissible`, `prime`, `rank`, `toFiniteQuadraticModule`, `realizationDet`, and
  `realizationUnit`.
* `TauCeti.FiniteQuadraticModule.orthogonalSumNikulinGenerators`: orthogonal sum of a generator
  list, with `primaryComponentOrthogonalSumNikulinGeneratorsIsometry` identifying its `p`-primary
  component with the filtered sublist.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition`: bundled admissible generator decomposition,
  with `NikulinDecomposition.zero`, `NikulinDecomposition.singleton`,
  `NikulinDecomposition.ofIsometry`, `NikulinDecomposition.prod`, `NikulinDecomposition.ofPi`,
  `NikulinDecomposition.ofIsNondegenerate`, and `nonempty_nikulinDecomposition_iff`.
* `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`: existence of an orthogonal summand
  `q_θ^{(2)}(2)` with `θ` odd (the dyadic alternative in Nikulin, Theorem 1.10.1(4)).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1–1.8.2, Theorem 1.9.1, and Theorem 1.10.1.
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

/-- The formal generator rank assigned to a label: `1` for cyclic labels and `2` for `u` and `v`.
When the label is admissible (`IsAdmissible`), this is the rank of the standard minimal-rank
`p`-adic lattice attached to the label `g` and equals `AddGroup.rank g.toFiniteQuadraticModule`
(`NikulinGenerator.IsAdmissible.rank_toFiniteQuadraticModule`). -/
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
noncomputable def toFiniteQuadraticModule : NikulinGenerator → FiniteQuadraticModule.{0}
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

/-- The formal realization determinant expression assigned to a generator label: `θ · p^k` for
`oddCyclic`, `θ · 2^k` for `dyadicCyclic`, `-4^k` for `dyadicU`, and `3 · 4^k` for `dyadicV`.
When the label is admissible (`IsAdmissible`), this is the Gram determinant of the standard
minimal-rank `p`-adic lattice attached to the label `g` (`⟨θ · p^k⟩` for `oddCyclic`, `⟨θ · 2^k⟩`
for `dyadicCyclic`, `2^k · U` for `dyadicU`, and `2^k · !![2, 1; 1, 2]` for `dyadicV`). The integer
determinant depends on the chosen cyclic label `θ`, and for `dyadicCyclic 1 θ` the minimal `2`-adic
realization is not unique up to isometry (`q_1^{(2)}(2) ≅ q_5^{(2)}(2)` admits both `⟨2⟩` and
`⟨10⟩`). -/
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

private theorem two_pow_mul_two_pow (k : ℕ) : 2 ^ k * 2 ^ k = 4 ^ k := by
  rw [← mul_pow]
  norm_num

/-- The formal determinant expression `g.realizationDet` factors as `g.realizationUnit` times the
order of `g.toFiniteQuadraticModule`. For admissible labels, this separates the `p`-adic unit part
of the standard label-dependent minimal realization determinant from the primary group order. -/
theorem realizationDet_eq_realizationUnit_mul_natCard (g : NikulinGenerator) :
    g.realizationDet = g.realizationUnit * (Nat.card g.toFiniteQuadraticModule : ℤ) := by
  cases g with
  | oddCyclic p k hp hodd θ =>
      simp [natCard_oddCyclic]
  | dyadicCyclic k hk θ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      simp [natCard_dyadicCyclic]
  | dyadicU k =>
      simp [natCard_dyadicU, two_pow_mul_two_pow]
  | dyadicV k =>
      simp [natCard_dyadicV, two_pow_mul_two_pow]

/-- Every generator's finite quadratic module is an additive `g.prime`-group. -/
theorem isAddPGroup_toFiniteQuadraticModule (g : NikulinGenerator) :
    IsAddPGroup g.prime g.toFiniteQuadraticModule := by
  cases g with
  | oddCyclic p k _ _ _ =>
      rw [prime_oddCyclic, toFiniteQuadraticModule_oddCyclic]
      exact IsAddPGroup.zmod_pow p k
  | dyadicCyclic k hk _ =>
      let _ : NeZero k := ⟨hk.ne'⟩
      rw [prime_dyadicCyclic, toFiniteQuadraticModule_dyadicCyclic]
      exact IsAddPGroup.zmod_pow 2 k
  | dyadicU k =>
      rw [prime_dyadicU, toFiniteQuadraticModule_dyadicU]
      exact IsAddPGroup.prod (IsAddPGroup.zmod_pow 2 k) (IsAddPGroup.zmod_pow 2 k)
  | dyadicV k =>
      rw [prime_dyadicV, toFiniteQuadraticModule_dyadicV]
      exact IsAddPGroup.prod (IsAddPGroup.zmod_pow 2 k) (IsAddPGroup.zmod_pow 2 k)

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
        natCard_dyadicU, two_pow_mul_two_pow]
      exact ⟨fun hk ↦ Nat.one_lt_pow hk.ne' (by norm_num),
        fun h ↦ Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at h⟩
  | dyadicV k =>
      rw [isAdmissible_dyadicV, toFiniteQuadraticModule_dyadicV,
        and_iff_right (isNondegenerate_dyadicV k), ← Finite.one_lt_card_iff_nontrivial,
        natCard_dyadicV, two_pow_mul_two_pow]
      exact ⟨fun hk ↦ Nat.one_lt_pow hk.ne' (by norm_num),
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
      rw [toFiniteQuadraticModule_oddCyclic, rank_oddCyclic]
      exact AddGroup.rank_zmod_prime_pow hp hg.1
  | dyadicCyclic k hk θ =>
      rw [toFiniteQuadraticModule_dyadicCyclic, rank_dyadicCyclic]
      exact AddGroup.rank_zmod_prime_pow Nat.prime_two hk
  | dyadicU k =>
      rw [toFiniteQuadraticModule_dyadicU, rank_dyadicU]
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hg hg
  | dyadicV k =>
      rw [toFiniteQuadraticModule_dyadicV, rank_dyadicV]
      exact AddGroup.rank_prod_zmod_prime_pow Nat.prime_two hg hg

end NikulinGenerator

/-! ## Orthogonal sums of generator lists -/

/-- The orthogonal sum of a finite list of Nikulin generators; the empty list gives the zero module
on `PUnit`. -/
noncomputable def orthogonalSumNikulinGenerators :
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

/-- For prime `p`, the `p`-primary component of an orthogonal sum of Nikulin generators is isometric
to the orthogonal sum of the sublist of generators with `g.prime = p`. -/
noncomputable def primaryComponentOrthogonalSumNikulinGeneratorsIsometry {p : ℕ} (hp : p.Prime) :
    ∀ gs : List NikulinGenerator,
      ((orthogonalSumNikulinGenerators gs).primaryComponent p).Isometry
        (orthogonalSumNikulinGenerators (gs.filter fun g ↦ g.prime = p))
  | [] =>
      let _ : Subsingleton ((orthogonalSumNikulinGenerators []).primaryComponent p) :=
        inferInstanceAs (Subsingleton (AddCommGroup.primaryComponent
          (orthogonalSumNikulinGenerators []) p))
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
          subsingleton_primaryComponent_of_isAddPGroup_of_coprime
            ((Nat.coprime_primes hp g.prime_prime).mpr (Ne.symm hgp))
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

namespace NikulinDecomposition

/-- The empty Nikulin decomposition of a trivial finite quadratic module. -/
noncomputable def zero (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    NikulinDecomposition A where
  generators := []
  admissible _ h := nomatch h
  isometry := Isometry.ofSubsingleton

/-- The empty Nikulin decomposition has empty generator list. -/
@[simp]
theorem zero_generators (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    (zero A).generators = [] := by
  rfl

/-- The single-generator Nikulin decomposition of an admissible generator's module. -/
noncomputable def singleton (g : NikulinGenerator) (hg : g.IsAdmissible) :
    NikulinDecomposition g.toFiniteQuadraticModule where
  generators := [g]
  admissible g' hg' := by
    rw [List.mem_singleton] at hg'
    subst hg'
    exact hg
  isometry := singletonNikulinGeneratorIsometry g

/-- The singleton Nikulin decomposition has generator list `[g]`. -/
@[simp]
theorem singleton_generators (g : NikulinGenerator) (hg : g.IsAdmissible) :
    (singleton g hg).generators = [g] := by
  rfl

/-- Transport a `NikulinDecomposition` along an isometry. -/
noncomputable def ofIsometry {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (D : NikulinDecomposition B) : NikulinDecomposition A where
  generators := D.generators
  admissible := D.admissible
  isometry := f.trans D.isometry

/-- Transporting a `NikulinDecomposition` along an isometry preserves its generator list. -/
@[simp]
theorem ofIsometry_generators {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (D : NikulinDecomposition B) :
    (ofIsometry f D).generators = D.generators := by
  rfl

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

/-- The product of two Nikulin decompositions concatenates their generator lists. -/
@[simp]
theorem prod_generators {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    (DA.prod DB).generators = DA.generators ++ DB.generators := by
  rfl

end NikulinDecomposition

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

/-- Bundle a `Fin n`-indexed orthogonal sum of admissible `NikulinGenerator`s as a
`NikulinDecomposition`. -/
noncomputable def NikulinDecomposition.ofPi {n : ℕ} (g : Fin n → NikulinGenerator)
    (hg : ∀ i, (g i).IsAdmissible) :
    NikulinDecomposition (pi fun i ↦ (g i).toFiniteQuadraticModule) where
  generators := List.ofFn g
  admissible g' hg' := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg'
    exact hg i
  isometry := piNikulinGeneratorsIsometry g

/-- The generator list of `NikulinDecomposition.ofPi` is `List.ofFn g`. -/
@[simp]
theorem NikulinDecomposition.ofPi_generators {n : ℕ} (g : Fin n → NikulinGenerator)
    (hg : ∀ i, (g i).IsAdmissible) :
    (NikulinDecomposition.ofPi g hg).generators = List.ofFn g := by
  rfl

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
  let dOdd : NikulinDecomposition (pi fun i ↦ oddCyclic (m i) (hm i) (θ i)) :=
    .ofIsometry (QuadraticMap.IsometryEquiv.pi fun i ↦ Isometry.ofEq (hOddEq i))
      (.ofPi gOdd hgOddAdm)
  let dCyc : NikulinDecomposition (pi fun i ↦ dyadicCyclic (k i + 1) (η i)) :=
    .ofPi (fun i ↦ .dyadicCyclic (k i + 1) (Nat.succ_pos (k i)) (η i)) hη
  let dU : NikulinDecomposition (pi fun i ↦ dyadicU (ku i + 1)) :=
    .ofPi (fun i ↦ .dyadicU (ku i + 1)) fun i ↦ Nat.succ_pos (ku i)
  let dV : NikulinDecomposition (pi fun i ↦ dyadicV (kv i + 1)) :=
    .ofPi (fun i ↦ .dyadicV (kv i + 1)) fun i ↦ Nat.succ_pos (kv i)
  exact ⟨.ofIsometry e₀.symm (dOdd.prod (dCyc.prod (dU.prod dV)))⟩

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

/-- Filtering a `NikulinDecomposition` to generators with `g.prime = p` yields a
`NikulinDecomposition` of the `p`-primary component `A.primaryComponent p`. -/
noncomputable def primaryComponent {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)
    {p : ℕ} (hp : p.Prime) : NikulinDecomposition (A.primaryComponent p) where
  generators := D.generators.filter fun g ↦ g.prime = p
  admissible g hg := D.admissible g (List.mem_of_mem_filter hg)
  isometry := (D.isometry.primaryComponent p).trans
    (primaryComponentOrthogonalSumNikulinGeneratorsIsometry hp D.generators)

/-- The `p`-primary decomposition filters `D.generators` to those with `g.prime = p`. -/
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
  rw [D.natCard_primaryComponent_eq hp, Nat.cast_list_prod, List.map_map, ← List.prod_map_mul]
  congr 1
  exact List.map_congr_left fun g _ ↦ g.realizationDet_eq_realizationUnit_mul_natCard

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
  exact rank_orthogonalSumNikulinGenerators_of_prime (D.primaryComponent hp).admissible
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

/-- Existence of a cyclic order-two dyadic orthogonal summand `q_θ^{(2)}(2)` (`θ` odd): this is
the dyadic alternative in Nikulin, Theorem 1.10.1(4), and the obstruction to uniqueness of the
minimal `2`-adic lattice realization in Nikulin, Theorem 1.9.1. -/
def HasCyclicTwoSummand (A : FiniteQuadraticModule.{u}) : Prop :=
  ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
    Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A'))

/-- Unfolding lemma for `HasCyclicTwoSummand`: `A` splits off a cyclic dyadic summand
`q_θ^{(2)}(2)` for some odd integer `θ`. -/
theorem hasCyclicTwoSummand_def (A : FiniteQuadraticModule.{u}) :
    HasCyclicTwoSummand A ↔
      ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
        Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A')) :=
  Iff.rfl

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

/-- A finite quadratic module has a cyclic order-two dyadic summand if and only if it contains an
element `x` with `2 • x = 0` and `q(x) + q(x) ≠ 0`. -/
theorem hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    (A : FiniteQuadraticModule.{u}) :
    HasCyclicTwoSummand A ↔ ∃ x : A, 2 • x = 0 ∧ A.quadratic x + A.quadratic x ≠ 0 := by
  constructor
  · rintro ⟨θ, A', hθ, ⟨f⟩⟩
    let e : dyadicCyclic 1 θ := (1 : ZMod (2 ^ 1))
    have h2 : (2 : ℕ) • (e, (0 : A')) = 0 := Prod.ext (ZMod.natCast_self 2) (nsmul_zero 2)
    refine ⟨f.symm (e, 0), by rw [← map_nsmul, h2, map_zero], ?_⟩
    rw [f.symm.map_app, prod_quadratic, map_zero, add_zero]
    exact dyadicCyclic_one_quadratic_add_self_ne_zero hθ
  · rintro ⟨x, hx, hq⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hq
    have hordx : addOrderOf x = 2 := by
      simpa using addOrderOf_eq_prime_pow (p := 2) (n := 0) (hp := ⟨Nat.prime_two⟩)
        (by simpa using hx0) (by simpa using hx)
    have hpair : A.toFiniteBilinearModule.pairing x x = -(A.quadratic x + A.quadratic x) := by
      rw [← A.polar_eq_pairing, QuadraticMap.polar, ← two_nsmul, hx, map_zero]
      abel
    have hpair0 : A.toFiniteBilinearModule.pairing x x ≠ 0 := by
      rw [hpair]
      exact neg_ne_zero.mpr hq
    have h2pair : 2 • A.toFiniteBilinearModule.pairing x x = 0 := by
      rw [← map_nsmul, hx, map_zero]
    have hordp : addOrderOf (A.toFiniteBilinearModule.pairing x x) = 2 := by
      simpa using addOrderOf_eq_prime_pow (p := 2) (n := 0) (hp := ⟨Nat.prime_two⟩)
        (by simpa using hpair0) (by simpa using h2pair)
    let H := AddSubgroup.zmultiples x
    have hHnd : (A.restrict H).IsNondegenerate := by
      rw [IsNondegenerate, restrict_toFiniteBilinearModule]
      exact (A.toFiniteBilinearModule.isNondegenerate_restrict_zmultiples_iff x).mpr
        (hordp.trans hordx.symm)
    have hcardH : Nat.card (A.restrict H) = 2 ^ 1 := by
      simpa [H] using (Nat.card_zmultiples x).trans hordx
    have _ : IsAddCyclic (A.restrict H) := inferInstanceAs (IsAddCyclic H)
    obtain ⟨θ, hθ, ⟨fH⟩⟩ := exists_dyadicCyclic_isometry (A.restrict H) (k := 1) hcardH hHnd
    let B := A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)
    obtain ⟨n, ⟨eB⟩⟩ := Finite.exists_equiv_fin B
    have _ : Small.{0} B := small_of_injective eB.injective
    let e : Shrink.{0} B ≃ B := (equivShrink B).symm
    let _ : AddCommGroup (Shrink.{0} B) := e.addCommGroup
    let _ : Finite (Shrink.{0} B) := e.finite_iff.mpr inferInstance
    let eAdd : Shrink.{0} B ≃+ B := e.addEquiv
    let A' : FiniteQuadraticModule.{0} :=
      ofQuadraticMap (B.quadratic.comp eAdd.toIntLinearEquiv.toLinearMap)
    have fB : Isometry A' B :=
      { toLinearEquiv := eAdd.toIntLinearEquiv
        map_app' := fun _ ↦ rfl }
    exact ⟨θ, A', hθ,
      ⟨((fH.prod fB).trans (A.restrictProdOrthogonalComplementIsometry hHnd)).symm⟩⟩

/-- A module with a cyclic order-two dyadic summand has an element `x` with `2 • x = 0` and
`q(x) + q(x) ≠ 0`. -/
theorem HasCyclicTwoSummand.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    {A : FiniteQuadraticModule.{u}} (hA : HasCyclicTwoSummand A) :
    ∃ x : A, 2 • x = 0 ∧ A.quadratic x + A.quadratic x ≠ 0 :=
  (hasCyclicTwoSummand_iff_exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero A).mp hA

/-- Every nondegenerate `q_θ^{(2)}(2)` (`θ` odd) has a cyclic order-two dyadic summand. -/
theorem hasCyclicTwoSummand_dyadicCyclic_one {θ : ℤ} (hθ : Odd θ) :
    HasCyclicTwoSummand (dyadicCyclic 1 θ) :=
  ⟨θ, orthogonalSumNikulinGenerators [], hθ,
    ⟨(QuadraticMap.IsometryEquiv.uniqueProd _ _).symm.trans (.prodComm _ _)⟩⟩

/-- For every `k`, `u^{(2)}(2^k)` has no cyclic order-two dyadic summand. -/
theorem not_hasCyclicTwoSummand_dyadicU (k : ℕ) : ¬ HasCyclicTwoSummand (dyadicU k) := by
  intro h
  obtain ⟨⟨a, b⟩, hx2, hq⟩ := h.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
  have ha : a + a = 0 := congrArg Prod.fst ((two_nsmul _).symm.trans (hx2 : (2 : ℕ) • (a, b) = 0))
  exact hq (by rw [dyadicU_quadratic (k := k) (a, b), ← map_add, ← add_mul, ha, zero_mul, map_zero])

/-- For every `k`, `v^{(2)}(2^k)` has no cyclic order-two dyadic summand. -/
theorem not_hasCyclicTwoSummand_dyadicV (k : ℕ) : ¬ HasCyclicTwoSummand (dyadicV k) := by
  intro h
  obtain ⟨⟨a, b⟩, hx2, hq⟩ := h.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
  have h2 := Prod.mk.inj ((two_nsmul (a, b)).symm.trans (hx2 : (2 : ℕ) • (a, b) = 0))
  have hsum : (a ^ 2 + a * b + b ^ 2) + (a ^ 2 + a * b + b ^ 2) = 0 := by
    linear_combination (a + b) * h2.1 + b * h2.2
  exact hq (by rw [dyadicV_quadratic (k := k) (a, b), ← map_add, hsum, map_zero])

/-! ## Non-uniqueness of decompositions -/

/-- Standard single-generator decomposition `[q_θ^{(2)}(2)]` of `dyadicCyclic 1 θ` (`θ` odd). -/
noncomputable def nikulinDecompositionDyadicCyclicOne {θ : ℤ} (hθ : Odd θ) :
    NikulinDecomposition (dyadicCyclic 1 θ) :=
  NikulinDecomposition.ofIsometry
    (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicCyclic 1 Nat.one_pos θ).symm)
    (NikulinDecomposition.singleton (.dyadicCyclic 1 Nat.one_pos θ)
      ((NikulinGenerator.isAdmissible_dyadicCyclic 1 Nat.one_pos θ).mpr hθ))

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
  NikulinDecomposition.ofIsometry (dyadicCyclicOneIsometryFiveMul θ)
    (nikulinDecompositionDyadicCyclicOne (h5.mul hθ))

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
    NikulinDecomposition.ofIsometry
      (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicU k).symm)
      (NikulinDecomposition.singleton (.dyadicU k)
        ((NikulinGenerator.isAdmissible_dyadicU k).mpr hk))
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
    NikulinDecomposition.ofIsometry
      (Isometry.ofEq (NikulinGenerator.toFiniteQuadraticModule_dyadicV k).symm)
      (NikulinDecomposition.singleton (.dyadicV k)
        ((NikulinGenerator.isAdmissible_dyadicV k).mpr hk))
  NikulinDecomposition.ofIsometry (dyadicUProdSelfIsometryDyadicVProdSelf k) (V.prod V)

/-- The generator list of `nikulinDecompositionDyadicUProdSelfAsV` is
`[.dyadicV k, .dyadicV k]`. -/
@[simp]
theorem nikulinDecompositionDyadicUProdSelfAsV_generators {k : ℕ} (hk : 0 < k) :
    (nikulinDecompositionDyadicUProdSelfAsV hk).generators = [.dyadicV k, .dyadicV k] := by
  simp [nikulinDecompositionDyadicUProdSelfAsV]

end TauCeti.FiniteQuadraticModule
