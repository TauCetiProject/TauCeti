/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.GCD

/-!
# Frobenius order data and Lusztig's modified symmetrizable datum

At a root of unity `ζ` whose square `ζ²` has multiplicative order `L ≥ 1`, the simple root
parameters `ζᵢ = ζ^(dᵢ)` of a symmetrizable Cartan datum have `ζᵢ²` of node-dependent order
`ℓᵢ = L / gcd(L, dᵢ)`, the least positive exponent `m` with `ζ^(2 m dᵢ) = 1`. When `L` is not
coprime to every `dᵢ`, the exponents `ℓᵢ` may vary across the diagram; Lusztig's quantum Frobenius
homomorphism lands in the algebra attached to the **modified datum** `(A*, d*)` with entries
`aᵢⱼ* = ℓⱼ aᵢⱼ / ℓᵢ`, symmetrizer `dᵢ* = ℓᵢ² dᵢ`, and target parameters `ζᵢ* = ζ^(dᵢ ℓᵢ²)`
satisfying `(ζᵢ*)² = 1` (and hence `ζᵢ* ∈ {1, -1}` in a ring without zero divisors). The modified
Cartan matrix `A*` still equals `A` whenever the orders `ℓᵢ` are constant, and differs from `A`
only when `ℓᵢ` varies across an edge.

This file develops the matrix, arithmetic, graph and root-of-unity theory of these Frobenius order
data for an arbitrary `TauCeti.SymmetrizableDatum`:

* the Frobenius orders `ℓᵢ = L / gcd(L, dᵢ)` (`TauCeti.SymmetrizableDatum.frobeniusOrder`) and
  their characterization as the multiplicative order of `ζ^(2 dᵢ)` and least positive solution of
  `ζ^(2 m dᵢ) = 1`;
* the target root-of-unity parameters `ζᵢ* = ζ^(dᵢ ℓᵢ²)`
  (`TauCeti.SymmetrizableDatum.frobeniusTarget`), which satisfy `(ζᵢ*)² = 1` whenever
  `ζ^(2 L) = 1` (and `ζᵢ* ∈ {1, -1}` in a ring without zero divisors);
* the integrality `(ℓᵢ : ℤ) ∣ ℓⱼ aᵢⱼ` for every symmetrizable generalized Cartan matrix, with no
  finite-type hypothesis
  (`TauCeti.SymmetrizableDatum.frobeniusOrder_dvd_frobeniusOrder_mul_cartan`), and the resulting
  modified `SymmetrizableDatum` (`TauCeti.SymmetrizableDatum.modifiedDatum`) with symmetrized
  matrix `(dᵢ* aᵢⱼ*) = (ℓᵢ ℓⱼ dᵢ aᵢⱼ)`;
* **nondivisibility** (`TauCeti.SymmetrizableDatum.Nondivisible`), where `L` is coprime to every
  `dᵢ` so `ℓᵢ = L` and `A* = A`, and **Lusztig's conditions**
  (`TauCeti.SymmetrizableDatum.LusztigConditions`), requiring a bipartite diagram (no odd cycle) and
  `1 - aᵢⱼ ≤ ℓᵢ` whenever `i ≠ j` and `2 ≤ ℓⱼ`;
* **symmetrizer rescaling and reduction to the normalized symmetrizer**: writing `d = c · d_norm`
  with `c = gcdᵢ dᵢ` and `L' = L / gcd(L, c) = ord((ζ^c)²)`, the Frobenius orders `ℓᵢ`, the
  modified Cartan matrix `A*`, the target parameters `ζᵢ*`, and Lusztig's conditions for `(A, d)`
  at `(ζ, L)` agree with those for `(A, d_norm)` at `(ζ^c, L')`, while `L` is nondivisible for `d`
  on a nonempty index type if and only if `gcd(L, c) = 1` and `L'` is nondivisible for `d_norm`.

The accompanying lattice construction `(X*, Y*)` on a `TauCeti.CartanDatum` is in
`TauCeti.QuantumGroups.Frobenius.ModifiedDatum`, and the finite-type preservation and same-vs-dual
dichotomy are in `TauCeti.QuantumGroups.Frobenius.FiniteType`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §2.2.4, §35.1.
* K. McGerty, *Generalized `q`-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007),
  116–131 (arXiv:math/0601511), §4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2015), 610–673 (arXiv:1402.0964), Definition 2.3.
-/

public section

namespace TauCeti

namespace SymmetrizableDatum

variable {I J I' : Type*} (A : SymmetrizableDatum I)

/-! ### Frobenius orders -/

/-- The **Frobenius order** `ℓᵢ = L / gcd(L, dᵢ)` at node `i` for a parameter order `L`. When `ζ²`
has multiplicative order `L`, this is the multiplicative order of `ζ^(2 dᵢ)`. -/
def frobeniusOrder (L : ℕ) (i : I) : ℕ :=
  L / Nat.gcd L (A.symmetrizer i)

lemma frobeniusOrder_def (L : ℕ) (i : I) :
    A.frobeniusOrder L i = L / Nat.gcd L (A.symmetrizer i) := (rfl)

@[simp]
lemma frobeniusOrder_zero (i : I) : A.frobeniusOrder 0 i = 0 := by
  simp [frobeniusOrder_def]

@[simp]
lemma frobeniusOrder_one (i : I) : A.frobeniusOrder 1 i = 1 := by
  simp [frobeniusOrder_def]

lemma frobeniusOrder_mul_gcd (L : ℕ) (i : I) :
    A.frobeniusOrder L i * Nat.gcd L (A.symmetrizer i) = L :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left L (A.symmetrizer i))

lemma frobeniusOrder_dvd (L : ℕ) (i : I) : A.frobeniusOrder L i ∣ L :=
  ⟨Nat.gcd L (A.symmetrizer i), (A.frobeniusOrder_mul_gcd L i).symm⟩

/-- `L` divides `dᵢ ℓᵢ`, since `dᵢ ℓᵢ = L · (dᵢ / gcd(L, dᵢ))`. -/
lemma dvd_symmetrizer_mul_frobeniusOrder (L : ℕ) (i : I) :
    L ∣ A.symmetrizer i * A.frobeniusOrder L i := by
  refine ⟨A.symmetrizer i / Nat.gcd L (A.symmetrizer i), ?_⟩
  have hd := Nat.div_mul_cancel (Nat.gcd_dvd_right L (A.symmetrizer i))
  calc A.symmetrizer i * A.frobeniusOrder L i
      = (A.symmetrizer i / Nat.gcd L (A.symmetrizer i) * Nat.gcd L (A.symmetrizer i)) *
          A.frobeniusOrder L i := by rw [hd]
    _ = (A.frobeniusOrder L i * Nat.gcd L (A.symmetrizer i)) *
          (A.symmetrizer i / Nat.gcd L (A.symmetrizer i)) := by ring
    _ = L * (A.symmetrizer i / Nat.gcd L (A.symmetrizer i)) := by rw [A.frobeniusOrder_mul_gcd]

lemma frobeniusOrder_pos {L : ℕ} (hL : 0 < L) (i : I) : 0 < A.frobeniusOrder L i :=
  Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L (A.symmetrizer i)))
    (Nat.gcd_pos_of_pos_left (A.symmetrizer i) hL)

lemma frobeniusOrder_ne_zero {L : ℕ} (hL : 0 < L) (i : I) : A.frobeniusOrder L i ≠ 0 :=
  (A.frobeniusOrder_pos hL i).ne'

lemma frobeniusOrder_le {L : ℕ} (hL : 0 < L) (i : I) : A.frobeniusOrder L i ≤ L :=
  Nat.le_of_dvd hL (A.frobeniusOrder_dvd L i)

lemma frobeniusOrder_eq_self_iff {L : ℕ} (hL : 0 < L) (i : I) :
    A.frobeniusOrder L i = L ↔ Nat.Coprime L (A.symmetrizer i) := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [frobeniusOrder_def, h.gcd_eq_one, Nat.div_one]⟩
  have hm := A.frobeniusOrder_mul_gcd L i
  rw [h] at hm
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_of_mul_eq_mul_left hL (hm.trans (mul_one L).symm))

lemma frobeniusOrder_eq_one_iff {L : ℕ} (hL : 0 < L) (i : I) :
    A.frobeniusOrder L i = 1 ↔ L ∣ A.symmetrizer i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hm := A.frobeniusOrder_mul_gcd L i
    rw [h, one_mul] at hm
    rw [← hm]
    exact Nat.gcd_dvd_right L (A.symmetrizer i)
  · rw [frobeniusOrder_def, Nat.gcd_eq_left h, Nat.div_self hL]

lemma frobeniusOrder_of_symmetrizer_eq_one {i : I} (hi : A.symmetrizer i = 1) (L : ℕ) :
    A.frobeniusOrder L i = L := by
  simp [frobeniusOrder_def, hi]

/-! ### Multiplicative orders and target root-of-unity parameters -/

section MonoidTarget

variable {M : Type*} [Monoid M]

/-- In any monoid, the multiplicative order of `ζ^(2 dᵢ)` is the Frobenius order of `ord(ζ²)`. -/
theorem orderOf_pow_two_mul_symmetrizer (ζ : M) (i : I) :
    orderOf (ζ ^ (2 * A.symmetrizer i)) = A.frobeniusOrder (orderOf (ζ ^ 2)) i := by
  rw [pow_mul, orderOf_pow' (ζ ^ 2) (A.symmetrizer_ne_zero i), frobeniusOrder_def]

/-- The **target parameter** `ζᵢ* = ζ^(dᵢ ℓᵢ²)` of the quantum Frobenius homomorphism at node `i`.
When `ζ^(2 L) = 1`, its square is `1`, so in a ring without zero divisors it is `1` or `-1`. -/
def frobeniusTarget (ζ : M) (L : ℕ) (i : I) : M :=
  ζ ^ (A.symmetrizer i * A.frobeniusOrder L i ^ 2)

lemma frobeniusTarget_def (ζ : M) (L : ℕ) (i : I) :
    A.frobeniusTarget ζ L i = ζ ^ (A.symmetrizer i * A.frobeniusOrder L i ^ 2) := (rfl)

/-- If `ζ^(2 L) = 1`, then `(ζᵢ*)² = 1` at every node `i`. -/
theorem frobeniusTarget_sq_eq_one {ζ : M} {L : ℕ} (hζ : ζ ^ (2 * L) = 1) (i : I) :
    A.frobeniusTarget ζ L i ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := A.dvd_symmetrizer_mul_frobeniusOrder L i
  have hexp : A.symmetrizer i * A.frobeniusOrder L i ^ 2 * 2 =
      2 * L * (k * A.frobeniusOrder L i) := by
    calc A.symmetrizer i * A.frobeniusOrder L i ^ 2 * 2
        = (A.symmetrizer i * A.frobeniusOrder L i) * A.frobeniusOrder L i * 2 := by ring
      _ = (L * k) * A.frobeniusOrder L i * 2 := by rw [hk]
      _ = 2 * L * (k * A.frobeniusOrder L i) := by ring
  rw [frobeniusTarget_def, ← pow_mul, hexp, pow_mul, hζ, one_pow]

/-- If `ζ^L = 1` (for instance when `ζ` has odd order `L`), every target parameter `ζᵢ*` is `1`. -/
theorem frobeniusTarget_eq_one_of_pow_eq_one {ζ : M} {L : ℕ} (hζ : ζ ^ L = 1) (i : I) :
    A.frobeniusTarget ζ L i = 1 := by
  obtain ⟨k, hk⟩ := A.dvd_symmetrizer_mul_frobeniusOrder L i
  have hexp : A.symmetrizer i * A.frobeniusOrder L i ^ 2 = L * (k * A.frobeniusOrder L i) := by
    calc A.symmetrizer i * A.frobeniusOrder L i ^ 2
        = (A.symmetrizer i * A.frobeniusOrder L i) * A.frobeniusOrder L i := by ring
      _ = L * (k * A.frobeniusOrder L i) := by rw [hk]; ring
  rw [frobeniusTarget_def, hexp, pow_mul, hζ, one_pow]

end MonoidTarget

section PrimitiveRoots

variable {M : Type*} [CommMonoid M]

/-- If `ζ²` is a primitive `L`-th root of unity, then `ζ^(2 dᵢ)` has order `ℓᵢ`. -/
theorem orderOf_pow_two_mul_symmetrizer_of_isPrimitiveRoot {ζ : M} {L : ℕ}
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) :
    orderOf (ζ ^ (2 * A.symmetrizer i)) = A.frobeniusOrder L i := by
  rw [A.orderOf_pow_two_mul_symmetrizer, ← hζ.eq_orderOf]

/-- If `ζ²` is a primitive `L`-th root of unity, then `ζ^(2 dᵢ)` is a primitive `ℓᵢ`-th root of
unity. -/
theorem isPrimitiveRoot_pow_two_mul_symmetrizer {ζ : M} {L : ℕ}
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) :
    IsPrimitiveRoot (ζ ^ (2 * A.symmetrizer i)) (A.frobeniusOrder L i) := by
  rw [IsPrimitiveRoot.iff_orderOf, A.orderOf_pow_two_mul_symmetrizer_of_isPrimitiveRoot hζ]

/-- If `ζ²` is a primitive `L`-th root of unity, then `ζ^(2 m dᵢ) = 1` precisely when `ℓᵢ ∣ m`. -/
theorem pow_two_mul_symmetrizer_eq_one_iff {ζ : M} {L : ℕ}
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) (m : ℕ) :
    ζ ^ (2 * m * A.symmetrizer i) = 1 ↔ A.frobeniusOrder L i ∣ m := by
  rw [mul_right_comm 2 m, pow_mul, ← orderOf_dvd_iff_pow_eq_one,
    A.orderOf_pow_two_mul_symmetrizer_of_isPrimitiveRoot hζ]

/-- For `L > 0` and `ζ²` a primitive `L`-th root of unity, `ℓᵢ` is the least positive exponent `m`
with `ζ^(2 m dᵢ) = 1`. -/
theorem isLeast_pow_two_mul_symmetrizer_eq_one {ζ : M} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) :
    IsLeast {m : ℕ | 0 < m ∧ ζ ^ (2 * m * A.symmetrizer i) = 1} (A.frobeniusOrder L i) := by
  refine ⟨⟨A.frobeniusOrder_pos hL i,
      (A.pow_two_mul_symmetrizer_eq_one_iff hζ i _).mpr dvd_rfl⟩, ?_⟩
  rintro m ⟨hm, hpow⟩
  exact Nat.le_of_dvd hm ((A.pow_two_mul_symmetrizer_eq_one_iff hζ i m).mp hpow)

/-- If `ζ²` is a primitive `L`-th root of unity, then `(ζᵢ*)² = 1` at every node `i`. -/
theorem frobeniusTarget_sq_eq_one_of_isPrimitiveRoot {ζ : M} {L : ℕ}
    (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) :
    A.frobeniusTarget ζ L i ^ 2 = 1 :=
  A.frobeniusTarget_sq_eq_one (by rw [pow_mul]; exact hζ.pow_eq_one) i

end PrimitiveRoots

section DomainTarget

/-- In a ring without zero divisors, if `ζ^(2 L) = 1`, then each target parameter `ζᵢ*` lies in
`{1, -1}`. -/
theorem frobeniusTarget_eq_one_or_neg_one {R : Type*} [Ring R] [NoZeroDivisors R]
    {ζ : R} {L : ℕ} (hζ : ζ ^ (2 * L) = 1) (i : I) :
    A.frobeniusTarget ζ L i = 1 ∨ A.frobeniusTarget ζ L i = -1 :=
  sq_eq_one_iff.mp (A.frobeniusTarget_sq_eq_one hζ i)

/-- In a commutative ring without zero divisors, if `ζ²` is a primitive `L`-th root of unity, then
each target parameter `ζᵢ*` lies in `{1, -1}`. -/
theorem frobeniusTarget_eq_one_or_neg_one_of_isPrimitiveRoot {R : Type*} [CommRing R]
    [NoZeroDivisors R] {ζ : R} {L : ℕ} (hζ : IsPrimitiveRoot (ζ ^ 2) L) (i : I) :
    A.frobeniusTarget ζ L i = 1 ∨ A.frobeniusTarget ζ L i = -1 :=
  sq_eq_one_iff.mp (A.frobeniusTarget_sq_eq_one_of_isPrimitiveRoot hζ i)

end DomainTarget

/-! ### Integrality and Lusztig's modified symmetrizable datum -/

/-- **Integrality of the modified Cartan matrix.** For every symmetrizable generalized Cartan
matrix `A` and every `L : ℕ`, `ℓᵢ` divides `ℓⱼ aᵢⱼ` in `ℤ` with no finite-type hypothesis, so that
`(ℓⱼ aᵢⱼ) / ℓᵢ` is an exact integer quotient. -/
theorem frobeniusOrder_dvd_frobeniusOrder_mul_cartan (L : ℕ) (i j : I) :
    (A.frobeniusOrder L i : ℤ) ∣ A.frobeniusOrder L j * A.cartan i j := by
  -- `gcd(L, dⱼ)` divides both `L |aᵢⱼ|` and `dⱼ |aⱼᵢ| = dᵢ |aᵢⱼ|`, hence `gcd(L, dᵢ) |aᵢⱼ|`.
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  set g : I → ℕ := fun k ↦ Nat.gcd L (A.symmetrizer k)
  have hgi_pos : 0 < g i := Nat.gcd_pos_of_pos_left (A.symmetrizer i) hL
  have hsymm_abs : A.symmetrizer i * (A.cartan i j).natAbs =
      A.symmetrizer j * (A.cartan j i).natAbs := by
    have h := congrArg Int.natAbs (A.symmetrizes i j)
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h
  have hdvd_nat : g j ∣ g i * (A.cartan i j).natAbs := by
    rw [← Nat.gcd_mul_right L (A.cartan i j).natAbs (A.symmetrizer i)]
    refine Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left L _) _) ?_
    rw [hsymm_abs]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right L _) _
  have hdvd_int : (g j : ℤ) ∣ (g i : ℤ) * A.cartan i j := by
    refine dvd_trans (Int.ofNat_dvd.mpr hdvd_nat) ?_
    rw [Nat.cast_mul]
    exact mul_dvd_mul_left (g i : ℤ) Int.natAbs_dvd_self
  obtain ⟨k, hk⟩ := hdvd_int
  refine ⟨k, mul_left_cancel₀ (Int.natCast_ne_zero.mpr hgi_pos.ne') ?_⟩
  have hLi : (A.frobeniusOrder L i : ℤ) * g i = L := by exact_mod_cast A.frobeniusOrder_mul_gcd L i
  have hLj : (A.frobeniusOrder L j : ℤ) * g j = L := by exact_mod_cast A.frobeniusOrder_mul_gcd L j
  linear_combination (A.frobeniusOrder L j : ℤ) * hk + k * (hLj - hLi)

private lemma frobeniusOrder_mul_ediv_cartan (L : ℕ) (i j : I) :
    (A.frobeniusOrder L i : ℤ) *
      (((A.frobeniusOrder L j : ℤ) * A.cartan i j) / A.frobeniusOrder L i) =
      A.frobeniusOrder L j * A.cartan i j :=
  Int.mul_ediv_cancel' (A.frobeniusOrder_dvd_frobeniusOrder_mul_cartan L i j)

private lemma ediv_cartan_eq_zero_iff {L : ℕ} (hL : 0 < L) (i j : I) :
    ((A.frobeniusOrder L j : ℤ) * A.cartan i j) / A.frobeniusOrder L i = 0 ↔
      A.cartan i j = 0 := by
  have hlj : (A.frobeniusOrder L j : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (A.frobeniusOrder_ne_zero hL j)
  have hij := A.frobeniusOrder_mul_ediv_cartan L i j
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by simp [h0]⟩
  rw [h0, mul_zero, eq_comm, mul_eq_zero] at hij
  exact hij.resolve_left hlj

/-- **Lusztig's modified symmetrizable datum** `(A*, d*)` at parameter order `L > 0`, with Cartan
entries `aᵢⱼ* = (ℓⱼ aᵢⱼ) / ℓᵢ` and symmetrizer `dᵢ* = ℓᵢ² dᵢ`. -/
def modifiedDatum (L : ℕ) (hL : 0 < L) : SymmetrizableDatum I where
  cartan := Matrix.of fun i j ↦ (A.frobeniusOrder L j * A.cartan i j) / A.frobeniusOrder L i
  isGeneralizedCartan :=
    { diag i := by
        have hli : (A.frobeniusOrder L i : ℤ) ≠ 0 :=
          Int.natCast_ne_zero.mpr (A.frobeniusOrder_ne_zero hL i)
        simp [A.isGeneralizedCartan.diag, Int.mul_ediv_cancel_left _ hli]
      offDiag_nonpos i j hij := by
        have hli : (0 : ℤ) < A.frobeniusOrder L i :=
          Int.natCast_pos.mpr (A.frobeniusOrder_pos hL i)
        have hle : (A.frobeniusOrder L j : ℤ) * A.cartan i j ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
            (A.isGeneralizedCartan.offDiag_nonpos i j hij)
        simp only [Matrix.of_apply]
        exact nonpos_of_mul_nonpos_right ((A.frobeniusOrder_mul_ediv_cartan L i j).trans_le hle) hli
      zero_comm i j := by
        simp only [Matrix.of_apply, A.ediv_cartan_eq_zero_iff hL]
        exact A.isGeneralizedCartan.zero_comm i j }
  symmetrizer i := A.frobeniusOrder L i ^ 2 * A.symmetrizer i
  symmetrizer_pos i := by
    have := A.frobeniusOrder_pos hL i
    have := A.symmetrizer_pos i
    positivity
  symmetrizes i j := by
    have hij := A.frobeniusOrder_mul_ediv_cartan L i j
    have hji := A.frobeniusOrder_mul_ediv_cartan L j i
    simp only [Matrix.of_apply, Nat.cast_mul, Nat.cast_pow]
    linear_combination
      (A.frobeniusOrder L i : ℤ) * (A.symmetrizer i : ℤ) * hij -
        (A.frobeniusOrder L j : ℤ) * (A.symmetrizer j : ℤ) * hji +
        (A.frobeniusOrder L i : ℤ) * (A.frobeniusOrder L j : ℤ) * A.symmetrizes i j

@[simp]
lemma modifiedDatum_cartan_apply (L : ℕ) (hL : 0 < L) (i j : I) :
    (A.modifiedDatum L hL).cartan i j =
      ((A.frobeniusOrder L j : ℤ) * A.cartan i j) / A.frobeniusOrder L i := (rfl)

@[simp]
lemma modifiedDatum_symmetrizer_apply (L : ℕ) (hL : 0 < L) (i : I) :
    (A.modifiedDatum L hL).symmetrizer i = A.frobeniusOrder L i ^ 2 * A.symmetrizer i := (rfl)

/-- Clearing the denominator of the modified Cartan entry: `ℓᵢ aᵢⱼ* = ℓⱼ aᵢⱼ`. -/
lemma frobeniusOrder_mul_modifiedDatum_cartan (L : ℕ) (hL : 0 < L) (i j : I) :
    (A.frobeniusOrder L i : ℤ) * (A.modifiedDatum L hL).cartan i j =
      A.frobeniusOrder L j * A.cartan i j :=
  A.frobeniusOrder_mul_ediv_cartan L i j

/-- **Lusztig's modified inner product `i ∘ j = ℓᵢ ℓⱼ (i · j)`.** Entry `(i, j)` of the symmetrized
matrix of the modified datum is `ℓᵢ ℓⱼ` times entry `(i, j)` of the original symmetrized matrix. -/
theorem symmetrizedMatrix_modifiedDatum_apply (L : ℕ) (hL : 0 < L) (i j : I) :
    (A.modifiedDatum L hL).symmetrizedMatrix i j =
      A.frobeniusOrder L i * A.frobeniusOrder L j * A.symmetrizedMatrix i j := by
  have hij := A.frobeniusOrder_mul_modifiedDatum_cartan L hL i j
  rw [symmetrizedMatrix_apply, symmetrizedMatrix_apply, modifiedDatum_symmetrizer_apply]
  push_cast
  linear_combination (A.frobeniusOrder L i : ℤ) * (A.symmetrizer i : ℤ) * hij

/-- The target parameter `ζᵢ*` is `ζ` raised to the modified symmetrizer `dᵢ* = ℓᵢ² dᵢ`. -/
theorem frobeniusTarget_eq_pow_modifiedDatum_symmetrizer {M : Type*} [Monoid M] (ζ : M)
    (L : ℕ) (hL : 0 < L) (i : I) :
    A.frobeniusTarget ζ L i = ζ ^ (A.modifiedDatum L hL).symmetrizer i := by
  rw [frobeniusTarget_def, modifiedDatum_symmetrizer_apply, mul_comm]

@[simp]
theorem modifiedDatum_one : A.modifiedDatum 1 zero_lt_one = A := by
  ext i j <;> simp

/-- An entry of the modified Cartan matrix vanishes if and only if the corresponding entry of the
original Cartan matrix vanishes. -/
theorem modifiedDatum_cartan_eq_zero_iff (L : ℕ) (hL : 0 < L) (i j : I) :
    (A.modifiedDatum L hL).cartan i j = 0 ↔ A.cartan i j = 0 :=
  A.ediv_cartan_eq_zero_iff hL i j

/-- Modifying the datum preserves its underlying diagram graph. -/
@[simp]
theorem diagramGraph_modifiedDatum_cartan (L : ℕ) (hL : 0 < L) :
    diagramGraph (A.modifiedDatum L hL).cartan = diagramGraph A.cartan := by
  ext i j
  simp only [diagramGraph_adj, ne_eq, modifiedDatum_cartan_eq_zero_iff]

/-- Modifying the datum preserves indecomposability of the Cartan matrix. -/
@[simp]
theorem isIndecomposable_modifiedDatum_cartan_iff [Finite I] (L : ℕ) (hL : 0 < L) :
    (A.modifiedDatum L hL).cartan.IsIndecomposable ↔ A.cartan.IsIndecomposable := by
  simp only [Matrix.isIndecomposable_iff_reflTransGen, ne_eq, modifiedDatum_cartan_eq_zero_iff]

/-- When all Frobenius orders `ℓᵢ` are equal, the modified Cartan matrix equals the original Cartan
matrix `A`. -/
theorem modifiedDatum_cartan_eq_of_frobeniusOrder_eq {L : ℕ} (hL : 0 < L)
    (h : ∀ i j, A.frobeniusOrder L i = A.frobeniusOrder L j) :
    (A.modifiedDatum L hL).cartan = A.cartan := by
  ext i j
  have hli : (A.frobeniusOrder L i : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (A.frobeniusOrder_ne_zero hL i)
  rw [modifiedDatum_cartan_apply, h j i, Int.mul_ediv_cancel_left _ hli]

/-! ### Compatibility with restriction, reindexing and direct sums -/

@[simp]
lemma frobeniusOrder_restrict (f : J ↪ I) (L : ℕ) (j : J) :
    (A.restrict f).frobeniusOrder L j = A.frobeniusOrder L (f j) := by
  simp [frobeniusOrder_def]

@[simp]
theorem modifiedDatum_restrict (f : J ↪ I) (L : ℕ) (hL : 0 < L) :
    (A.restrict f).modifiedDatum L hL = (A.modifiedDatum L hL).restrict f := by
  ext <;> simp

@[simp]
lemma frobeniusOrder_reindex (e : I ≃ I') (L : ℕ) (i : I') :
    (A.reindex e).frobeniusOrder L i = A.frobeniusOrder L (e.symm i) := by
  simp [frobeniusOrder_def]

@[simp]
theorem modifiedDatum_reindex (e : I ≃ I') (L : ℕ) (hL : 0 < L) :
    (A.reindex e).modifiedDatum L hL = (A.modifiedDatum L hL).reindex e := by
  ext <;> simp

@[simp]
theorem frobeniusOrder_sum (A' : SymmetrizableDatum J) (L : ℕ) :
    (A.sum A').frobeniusOrder L = Sum.elim (A.frobeniusOrder L) (A'.frobeniusOrder L) := by
  funext x
  cases x <;> simp [frobeniusOrder_def]

@[simp]
theorem modifiedDatum_sum (A' : SymmetrizableDatum J) (L : ℕ) (hL : 0 < L) :
    (A.sum A').modifiedDatum L hL = (A.modifiedDatum L hL).sum (A'.modifiedDatum L hL) := by
  ext x y
  · cases x <;> cases y <;> simp
  · cases x <;> simp

/-! ### Nondivisibility and Lusztig's conditions -/

/-- Parameter order `L` is **nondivisible** for `A` if `L` is coprime to every symmetrizer entry
`dᵢ`. In that case `ℓᵢ = L` for every `i` and `A* = A`. -/
def Nondivisible (L : ℕ) : Prop :=
  ∀ i, Nat.Coprime L (A.symmetrizer i)

lemma nondivisible_def (L : ℕ) :
    A.Nondivisible L ↔ ∀ i, Nat.Coprime L (A.symmetrizer i) := .rfl

theorem Nondivisible.frobeniusOrder_eq {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.Nondivisible L) (i : I) :
    A.frobeniusOrder L i = L := by
  rw [frobeniusOrder_def, (h i).gcd_eq_one, Nat.div_one]

theorem nondivisible_iff_forall_frobeniusOrder_eq {L : ℕ} (hL : 0 < L) :
    A.Nondivisible L ↔ ∀ i, A.frobeniusOrder L i = L :=
  forall_congr' fun i ↦ (A.frobeniusOrder_eq_self_iff hL i).symm

theorem Nondivisible.modifiedDatum_cartan {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.Nondivisible L) (hL : 0 < L) :
    (A.modifiedDatum L hL).cartan = A.cartan :=
  A.modifiedDatum_cartan_eq_of_frobeniusOrder_eq hL fun i j ↦ by
    rw [h.frobeniusOrder_eq i, h.frobeniusOrder_eq j]

theorem Nondivisible.modifiedDatum_symmetrizer {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.Nondivisible L) (hL : 0 < L) (i : I) :
    (A.modifiedDatum L hL).symmetrizer i = L ^ 2 * A.symmetrizer i := by
  rw [modifiedDatum_symmetrizer_apply, h.frobeniusOrder_eq i]

/-- For a normalized simply-laced datum (`dᵢ = 1` for all `i`), every `L` is nondivisible. -/
theorem nondivisible_of_symmetrizer_eq_one (hd : ∀ i, A.symmetrizer i = 1) (L : ℕ) :
    A.Nondivisible L :=
  fun i ↦ by rw [hd i]; exact Nat.coprime_one_right L

/-- For a normalized simply-laced datum (`dᵢ = 1` for all `i`) and every `L > 0`, the modified
Cartan matrix equals `A`. -/
theorem modifiedDatum_cartan_of_symmetrizer_eq_one (hd : ∀ i, A.symmetrizer i = 1)
    {L : ℕ} (hL : 0 < L) :
    (A.modifiedDatum L hL).cartan = A.cartan :=
  (A.nondivisible_of_symmetrizer_eq_one hd L).modifiedDatum_cartan hL

/-- **Lusztig's root-of-unity conditions** on `A` at parameter order `L` (Lusztig 1993, §35.1.2;
McGerty 2007, §4): the diagram of `A` is bipartite (equivalently, every closed walk — in particular
every cycle — has even length) and `1 - aᵢⱼ ≤ ℓᵢ` whenever `i ≠ j` and `2 ≤ ℓⱼ`. -/
def LusztigConditions (L : ℕ) : Prop :=
  (diagramGraph A.cartan).IsBipartite ∧
    ∀ i j, i ≠ j → 2 ≤ A.frobeniusOrder L j → 1 - A.cartan i j ≤ A.frobeniusOrder L i

lemma lusztigConditions_def (L : ℕ) :
    A.LusztigConditions L ↔
      (diagramGraph A.cartan).IsBipartite ∧
        ∀ i j, i ≠ j → 2 ≤ A.frobeniusOrder L j → 1 - A.cartan i j ≤ A.frobeniusOrder L i := .rfl

theorem LusztigConditions.isBipartite {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.LusztigConditions L) :
    (diagramGraph A.cartan).IsBipartite :=
  h.1

theorem LusztigConditions.one_sub_cartan_le {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.LusztigConditions L) {i j : I}
    (hij : i ≠ j) (hj : 2 ≤ A.frobeniusOrder L j) :
    1 - A.cartan i j ≤ A.frobeniusOrder L i :=
  h.2 i j hij hj

/-- Under Lusztig's conditions, every closed walk (in particular every cycle) in the diagram of `A`
has even length. -/
theorem LusztigConditions.even_length_walk {A : SymmetrizableDatum I} {L : ℕ}
    (h : A.LusztigConditions L) {v : I} (c : (diagramGraph A.cartan).Walk v v) :
    Even c.length :=
  SimpleGraph.isBipartite_iff_forall_walk_even_length.mp h.isBipartite v c

/-! ### Symmetrizer rescaling and reduction to the normalized symmetrizer -/

/-- When `dᵢ ∣ dⱼ`, the Frobenius order `ℓᵢ` factors as `ℓⱼ · gcd(ℓᵢ, dⱼ / dᵢ)`. -/
theorem frobeniusOrder_eq_mul_gcd_of_dvd_symmetrizer {i j : I}
    (hd : A.symmetrizer i ∣ A.symmetrizer j) (L : ℕ) :
    A.frobeniusOrder L i =
      A.frobeniusOrder L j *
        Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  have hgi : 0 < Nat.gcd L (A.symmetrizer i) := Nat.gcd_pos_of_pos_left _ hL
  have hgj : Nat.gcd L (A.symmetrizer j) =
      Nat.gcd L (A.symmetrizer i) *
        Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    rw [Nat.gcd_mul_right_div_gcd, frobeniusOrder_def]
  refine Nat.eq_of_mul_eq_mul_right hgi ?_
  calc A.frobeniusOrder L i * Nat.gcd L (A.symmetrizer i)
      = L := A.frobeniusOrder_mul_gcd L i
    _ = A.frobeniusOrder L j * Nat.gcd L (A.symmetrizer j) := (A.frobeniusOrder_mul_gcd L j).symm
    _ = A.frobeniusOrder L j *
          Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i) *
          Nat.gcd L (A.symmetrizer i) := by rw [hgj]; ring

/-- When `dᵢ ∣ dⱼ`, the Frobenius order `ℓⱼ` divides `ℓᵢ`. -/
theorem frobeniusOrder_dvd_of_dvd_symmetrizer {i j : I}
    (hd : A.symmetrizer i ∣ A.symmetrizer j) (L : ℕ) :
    A.frobeniusOrder L j ∣ A.frobeniusOrder L i :=
  ⟨Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i),
    A.frobeniusOrder_eq_mul_gcd_of_dvd_symmetrizer hd L⟩

/-- **Ratio of short-root and long-root Frobenius orders.** When `dᵢ ∣ dⱼ` and `L > 0`, the ratio
`ℓᵢ / ℓⱼ` equals both `gcd(L, dⱼ) / gcd(L, dᵢ)` and `gcd(L / gcd(L, dᵢ), dⱼ / dᵢ)`, hence divides
`dⱼ / dᵢ`. -/
theorem frobeniusOrder_div_eq_of_dvd_symmetrizer {i j : I}
    (hd : A.symmetrizer i ∣ A.symmetrizer j) {L : ℕ} (hL : 0 < L) :
    A.frobeniusOrder L i / A.frobeniusOrder L j =
        Nat.gcd L (A.symmetrizer j) / Nat.gcd L (A.symmetrizer i) ∧
      A.frobeniusOrder L i / A.frobeniusOrder L j =
        Nat.gcd (L / Nat.gcd L (A.symmetrizer i)) (A.symmetrizer j / A.symmetrizer i) := by
  have hlj : 0 < A.frobeniusOrder L j := A.frobeniusOrder_pos hL j
  have hgi : 0 < Nat.gcd L (A.symmetrizer i) := Nat.gcd_pos_of_pos_left _ hL
  have hratio : A.frobeniusOrder L i / A.frobeniusOrder L j =
      Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i) := by
    conv_lhs => rw [A.frobeniusOrder_eq_mul_gcd_of_dvd_symmetrizer hd L]
    exact Nat.mul_div_right _ hlj
  have hgj : Nat.gcd L (A.symmetrizer j) / Nat.gcd L (A.symmetrizer i) =
      Nat.gcd (A.frobeniusOrder L i) (A.symmetrizer j / A.symmetrizer i) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    rw [Nat.gcd_mul_right_div_gcd, ← frobeniusOrder_def, Nat.mul_div_right _ hgi]
  exact ⟨hratio.trans hgj.symm, hratio⟩

section Rescale

/-- Rescaling the symmetrizer of a datum by a factor `c` and replacing `L` by `L / gcd(L, c)`
leaves every Frobenius order unchanged. This applies both to global normalization and componentwise
on each indecomposable summand. -/
theorem frobeniusOrder_eq_of_symmetrizer_eq_mul {A' : SymmetrizableDatum I} {c : ℕ}
    (hd : ∀ i, A.symmetrizer i = c * A'.symmetrizer i) (L : ℕ) (i : I) :
    A'.frobeniusOrder (L / Nat.gcd L c) i = A.frobeniusOrder L i := by
  rw [frobeniusOrder_def, frobeniusOrder_def, hd i, Nat.gcd_mul_right_div_gcd,
    Nat.div_div_eq_div_mul]

/-- Rescaling the symmetrizer by `c` and replacing `(ζ, L)` by `(ζ^c, L / gcd(L, c))` leaves every
target parameter `ζᵢ*` unchanged. -/
theorem frobeniusTarget_eq_of_symmetrizer_eq_mul {M : Type*} [Monoid M] {A' : SymmetrizableDatum I}
    {c : ℕ} (hd : ∀ i, A.symmetrizer i = c * A'.symmetrizer i) (ζ : M) (L : ℕ) (i : I) :
    A'.frobeniusTarget (ζ ^ c) (L / Nat.gcd L c) i = A.frobeniusTarget ζ L i := by
  rw [frobeniusTarget_def, frobeniusTarget_def,
    A.frobeniusOrder_eq_of_symmetrizer_eq_mul hd L i, ← pow_mul, ← mul_assoc, ← hd i]

/-- Rescaling the symmetrizer by `c` and replacing `L` by `L / gcd(L, c)` leaves the modified Cartan
matrix unchanged. -/
theorem modifiedDatum_cartan_eq_of_symmetrizer_eq_mul {A' : SymmetrizableDatum I}
    (hcart : A'.cartan = A.cartan) {c : ℕ}
    (hd : ∀ i, A.symmetrizer i = c * A'.symmetrizer i) {L : ℕ} (hL : 0 < L) :
    (A'.modifiedDatum (L / Nat.gcd L c)
      (Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L c))
        (Nat.gcd_pos_of_pos_left c hL))).cartan =
      (A.modifiedDatum L hL).cartan := by
  ext i j
  simp [hcart, A.frobeniusOrder_eq_of_symmetrizer_eq_mul hd L]

/-- Rescaling the symmetrizer by `c` and replacing `L` by `L / gcd(L, c)` preserves Lusztig's
conditions. -/
theorem lusztigConditions_iff_of_symmetrizer_eq_mul {A' : SymmetrizableDatum I}
    (hcart : A'.cartan = A.cartan) {c : ℕ}
    (hd : ∀ i, A.symmetrizer i = c * A'.symmetrizer i) (L : ℕ) :
    A'.LusztigConditions (L / Nat.gcd L c) ↔ A.LusztigConditions L := by
  simp only [lusztigConditions_def, hcart, A.frobeniusOrder_eq_of_symmetrizer_eq_mul hd L]

end Rescale

section NormalizeSymmetrizer

variable [Fintype I]

/-- The **reduced parameter order** `L' = L / gcd(L, gcdᵢ dᵢ)` associated to the normalized
symmetrizer `d_norm = d / gcdᵢ dᵢ`. When `ζ²` has order `L` and `I` is nonempty, `(ζ^c)²` has
order `L'` for `c = gcdᵢ dᵢ`. -/
def reducedOrder (L : ℕ) : ℕ :=
  L / Nat.gcd L (Finset.univ.gcd A.symmetrizer)

lemma reducedOrder_def (L : ℕ) :
    A.reducedOrder L = L / Nat.gcd L (Finset.univ.gcd A.symmetrizer) := (rfl)

lemma reducedOrder_pos {L : ℕ} (hL : 0 < L) : 0 < A.reducedOrder L :=
  Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L _)) (Nat.gcd_pos_of_pos_left _ hL)

lemma reducedOrder_dvd (L : ℕ) : A.reducedOrder L ∣ L :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left L _)

/-- On a nonempty index type, `ord((ζ^c)²) = L'` for `c = gcdᵢ dᵢ` and `L = ord(ζ²)`. -/
theorem orderOf_pow_gcd_symmetrizer_sq [Nonempty I] {M : Type*} [Monoid M] (ζ : M) :
    orderOf ((ζ ^ Finset.univ.gcd A.symmetrizer) ^ 2) = A.reducedOrder (orderOf (ζ ^ 2)) := by
  rw [← pow_mul, mul_comm _ 2, pow_mul, orderOf_pow' (ζ ^ 2) A.gcd_symmetrizer_pos.ne',
    reducedOrder_def]

/-- If `ζ²` is a primitive `L`-th root of unity on a nonempty index type, then `(ζ^c)²` is a
primitive `L'`-th root of unity for `c = gcdᵢ dᵢ`. -/
theorem isPrimitiveRoot_pow_gcd_symmetrizer_sq [Nonempty I] {M : Type*} [CommMonoid M]
    {ζ : M} {L : ℕ} (hζ : IsPrimitiveRoot (ζ ^ 2) L) :
    IsPrimitiveRoot ((ζ ^ Finset.univ.gcd A.symmetrizer) ^ 2) (A.reducedOrder L) := by
  rw [IsPrimitiveRoot.iff_orderOf, A.orderOf_pow_gcd_symmetrizer_sq, ← hζ.eq_orderOf]

/-- `gcd(L, dᵢ) = gcd(L, c) · gcd(L', d_norm,i)` for `c = gcdⱼ dⱼ` and `L' = L / gcd(L, c)`. -/
theorem gcd_symmetrizer_eq (L : ℕ) (i : I) :
    Nat.gcd L (A.symmetrizer i) =
      Nat.gcd L (Finset.univ.gcd A.symmetrizer) *
        Nat.gcd (A.reducedOrder L) (A.normalizeSymmetrizer.symmetrizer i) := by
  rw [A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i, Nat.gcd_mul_right_div_gcd,
    reducedOrder_def]

/-- **Invariance of Frobenius orders under normalization of the symmetrizer:**
`ℓᵢ(L', d_norm) = ℓᵢ(L, d)`. -/
@[simp]
theorem frobeniusOrder_normalizeSymmetrizer (L : ℕ) (i : I) :
    A.normalizeSymmetrizer.frobeniusOrder (A.reducedOrder L) i = A.frobeniusOrder L i :=
  A.frobeniusOrder_eq_of_symmetrizer_eq_mul A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer L i

/-- **Invariance of the modified Cartan matrix under normalization of the symmetrizer.** -/
@[simp]
theorem modifiedDatum_normalizeSymmetrizer_cartan {L : ℕ} (hL : 0 < L) :
    (A.normalizeSymmetrizer.modifiedDatum (A.reducedOrder L) (A.reducedOrder_pos hL)).cartan =
      (A.modifiedDatum L hL).cartan := by
  ext i j
  simp

/-- The modified symmetrizer of `A` at `L` is `gcdⱼ dⱼ` times the modified symmetrizer of
`A.normalizeSymmetrizer` at `L'`. -/
theorem modifiedDatum_symmetrizer_eq_gcd_mul {L : ℕ} (hL : 0 < L) (i : I) :
    (A.modifiedDatum L hL).symmetrizer i =
      Finset.univ.gcd A.symmetrizer *
        (A.normalizeSymmetrizer.modifiedDatum (A.reducedOrder L)
          (A.reducedOrder_pos hL)).symmetrizer i := by
  simp only [modifiedDatum_symmetrizer_apply, frobeniusOrder_normalizeSymmetrizer]
  rw [mul_left_comm, ← A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i]

/-- **Invariance of the target parameters `ζᵢ*` under normalization of the symmetrizer:**
`ζᵢ*(ζ^c, L', d_norm) = ζᵢ*(ζ, L, d)`. -/
@[simp]
theorem frobeniusTarget_normalizeSymmetrizer {M : Type*} [Monoid M] (ζ : M) (L : ℕ) (i : I) :
    A.normalizeSymmetrizer.frobeniusTarget (ζ ^ Finset.univ.gcd A.symmetrizer)
      (A.reducedOrder L) i = A.frobeniusTarget ζ L i :=
  A.frobeniusTarget_eq_of_symmetrizer_eq_mul A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer ζ L i

/-- **Invariance of Lusztig's conditions under normalization of the symmetrizer.** -/
@[simp]
theorem lusztigConditions_normalizeSymmetrizer_iff (L : ℕ) :
    A.normalizeSymmetrizer.LusztigConditions (A.reducedOrder L) ↔ A.LusztigConditions L :=
  A.lusztigConditions_iff_of_symmetrizer_eq_mul A.normalizeSymmetrizer_cartan
    A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer L

/-- On a nonempty index type, `L` is nondivisible for `d` if and only if `gcd(L, gcdᵢ dᵢ) = 1` and
the reduced order `L'` is nondivisible for `d_norm`. -/
theorem nondivisible_iff_coprime_gcd_and_normalizeSymmetrizer [Nonempty I] (L : ℕ) :
    A.Nondivisible L ↔
      Nat.Coprime L (Finset.univ.gcd A.symmetrizer) ∧
        A.normalizeSymmetrizer.Nondivisible (A.reducedOrder L) := by
  refine ⟨fun h ↦ ?_, fun ⟨hcop, hnorm⟩ i ↦ ?_⟩
  · obtain ⟨i₀⟩ := ‹Nonempty I›
    have hcop : Nat.Coprime L (Finset.univ.gcd A.symmetrizer) :=
      (h i₀).of_dvd_right (A.gcd_symmetrizer_dvd i₀)
    have hred : A.reducedOrder L = L := by
      rw [reducedOrder_def, hcop.gcd_eq_one, Nat.div_one]
    refine ⟨hcop, fun i ↦ ?_⟩
    rw [hred]
    exact (h i).of_dvd_right ⟨Finset.univ.gcd A.symmetrizer,
      (A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i).trans (mul_comm _ _)⟩
  · have hred : A.reducedOrder L = L := by
      rw [reducedOrder_def, hcop.gcd_eq_one, Nat.div_one]
    rw [A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i]
    exact hcop.mul_right (hred ▸ hnorm i)

end NormalizeSymmetrizer

end SymmetrizableDatum

end TauCeti
