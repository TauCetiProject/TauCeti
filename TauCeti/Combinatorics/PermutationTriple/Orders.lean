/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType
public import TauCeti.GroupTheory.TriangleGroup.PermutationRepresentation
import Mathlib.Tactic.Linarith

/-!
# Dividing and exact orders of permutation triples

A permutation triple `t` of degree `n` can be attached to three natural numbers `a, b, c` in
three ways, which sources on triangle groups and dessins tend to conflate:

* **dividing orders**: `t.σ0 ^ a = 1`, `t.σ1 ^ b = 1` and `t.σinf ^ c = 1`. This is the hypothesis
  under which `t` is a permutation representation of the triangle group `Δ(a, b, c)`
  (`TauCeti.TriangleGroup.toPerm`), whose image is then the whole monodromy group of `t`
  (`TauCeti.TriangleGroup.range_toPerm`);
* **exact orders**: `t.orderTriple = (a, b, c)`, the `abc` datum of a three-point cover.
* **surjective monodromy**: the triangle group representation has range equal to the monodromy
  group of `t`.

Exact orders are dividing orders, and a triple has dividing orders `(a, b, c)` exactly when its
order triple divides `(a, b, c)` componentwise.

The file then records necessary conditions for a connected triple of degree `n` with given orders
to exist. Each entry of the order triple is the least common multiple of a partition of `n`.
A permutation whose order divides `a ≠ 0` has cycles of length at most `a`, so it has at least
`n / a` cycles; summing over the three components bounds the Euler characteristic from below:

`n * (1 / a + 1 / b + 1 / c - 1) ≤ χ(t)`.

For a connected triple `χ(t) ≤ 2`, so `n * (1 / a + 1 / b + 1 / c - 1) ≤ 2`. When
`1 / a + 1 / b + 1 / c > 1` (the spherical case) this bounds the degree `n`; in the Euclidean and
hyperbolic cases it is no condition at all. None of these conditions is claimed to be sufficient.

## Main results

* `TauCeti.PermutationTriple.hasDividingOrders_iff_orderTriple_dvd`: dividing orders are
  multiples of the order triple.
* `TauCeti.PermutationTriple.HasExactOrders.hasDividingOrders`: exact orders are dividing orders.
* `TauCeti.PermutationTriple.hasSurjectiveMonodromy_iff`: the dividing relations automatically
  give a representation surjective onto the monodromy group.
* `TauCeti.PermutationTriple.exists_partition_lcm_eq_orderTriple`: each component order is the
  least common multiple of a partition of the degree; by `Equiv.Perm.exists_orderOf_eq_iff` these
  are exactly the orders of the permutations of `n` points.
* `TauCeti.PermutationTriple.natCast_mul_inv_add_inv_add_inv_sub_one_le_eulerChar`: the lower
  bound on the Euler characteristic by dividing orders.
* `TauCeti.PermutationTriple.IsConnected.natCast_mul_inv_add_inv_add_inv_sub_one_le_two`: the
  resulting constraint on a connected triple.
* `TauCeti.PermutationTriple.IsConnected.natCast_le_of_one_lt_inv_add_inv_add_inv`: the degree
  bound in the spherical case.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §2.4 and §4.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n a b c : ℕ} (t : PermutationTriple n)

/-! ### Dividing and exact orders -/

/-- The component orders of `t` divide `(a, b, c)`. -/
def HasDividingOrders (t : PermutationTriple n) (a b c : ℕ) : Prop :=
  t.σ0 ^ a = 1 ∧ t.σ1 ^ b = 1 ∧ t.σinf ^ c = 1

/-- The component orders of `t` are exactly `(a, b, c)`. -/
def HasExactOrders (t : PermutationTriple n) (a b c : ℕ) : Prop :=
  t.orderTriple = (a, b, c)

/-- The triangle group representation of `t` has image its monodromy group. The witnessing
power relations are part of this condition, since the representation requires them. -/
def HasSurjectiveMonodromy (t : PermutationTriple n) (a b c : ℕ) : Prop :=
  ∃ (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1),
    (TriangleGroup.toPerm t ha hb hc).range = t.monodromyGroup

/-- Dividing orders are the three power relations. -/
@[simp] theorem hasDividingOrders_iff : t.HasDividingOrders a b c ↔
    t.σ0 ^ a = 1 ∧ t.σ1 ^ b = 1 ∧ t.σinf ^ c = 1 := Iff.rfl

/-- Exact orders agree with the order triple. -/
@[simp] theorem hasExactOrders_iff : t.HasExactOrders a b c ↔
    t.orderTriple = (a, b, c) := Iff.rfl

/-- Dividing orders are precisely the multiples of the component orders. -/
theorem hasDividingOrders_iff_orderTriple_dvd : t.HasDividingOrders a b c ↔
    t.orderTriple.1 ∣ a ∧ t.orderTriple.2.1 ∣ b ∧ t.orderTriple.2.2 ∣ c := by
  simp only [hasDividingOrders_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf, orderOf_dvd_iff_pow_eq_one]

/-- A triple with exact orders `(a, b, c)` has dividing orders `(a, b, c)`. In particular every
triple has dividing orders its own order triple. -/
theorem HasExactOrders.hasDividingOrders (h : t.HasExactOrders a b c) :
    t.HasDividingOrders a b c := by
  rw [hasDividingOrders_iff_orderTriple_dvd, (t.hasExactOrders_iff).mp h]
  exact ⟨dvd_rfl, dvd_rfl, dvd_rfl⟩

/-- Every triple has dividing orders given by its own order triple. -/
theorem hasDividingOrders_orderTriple :
    t.HasDividingOrders t.orderTriple.1 t.orderTriple.2.1 t.orderTriple.2.2 := by
  rw [hasDividingOrders_iff_orderTriple_dvd]
  exact ⟨dvd_rfl, dvd_rfl, dvd_rfl⟩

/-- Surjectivity onto the monodromy group follows from the dividing relations. -/
@[simp] theorem hasSurjectiveMonodromy_iff : t.HasSurjectiveMonodromy a b c ↔
    t.HasDividingOrders a b c := by
  constructor
  · rintro ⟨ha, hb, hc, _⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨ha, hb, hc, TriangleGroup.range_toPerm t ha hb hc⟩

/-- Each component order of a degree-`n` triple is the least common multiple of a partition
of `n`. -/
theorem exists_partition_lcm_eq_orderTriple :
    (∃ p : n.Partition, p.parts.lcm = t.orderTriple.1) ∧
      (∃ p : n.Partition, p.parts.lcm = t.orderTriple.2.1) ∧
      ∃ p : n.Partition, p.parts.lcm = t.orderTriple.2.2 := by
  have key (σ : Perm (Fin n)) : ∃ p : n.Partition, p.parts.lcm = orderOf σ := by
    have h := (Equiv.Perm.exists_orderOf_eq_iff (α := Fin n) (k := orderOf σ)).mp
      ⟨σ, rfl⟩
    rw [Nat.card_fin] at h
    exact h
  simp only [orderTriple_σ0, orderTriple_σ1, orderTriple_σinf]
  exact ⟨key t.σ0, key t.σ1, key t.σinf⟩

/-- Each prescribed exact order is the least common multiple of a partition of the degree. -/
theorem exists_partition_lcm_eq_of_orderTriple_eq (h : t.HasExactOrders a b c) :
    (∃ p : n.Partition, p.parts.lcm = a) ∧ (∃ p : n.Partition, p.parts.lcm = b) ∧
      ∃ p : n.Partition, p.parts.lcm = c := by
  simpa only [(t.hasExactOrders_iff).mp h, Prod.fst, Prod.snd] using
    t.exists_partition_lcm_eq_orderTriple

/-! ### The Euler characteristic bound -/

/-- **The Euler characteristic is bounded below by dividing orders.** If the components of a
degree-`n` triple have orders dividing `a`, `b` and `c`, then
`n * (1 / a + 1 / b + 1 / c - 1) ≤ χ(t)`. A zero order imposes no condition and contributes no
term, since `(0 : ℚ)⁻¹ = 0`. -/
theorem natCast_mul_inv_add_inv_add_inv_sub_one_le_eulerChar
    (h : t.HasDividingOrders a b c) :
    (n : ℚ) * ((a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1) ≤ t.eulerChar := by
  -- A component whose order divides `k ≠ 0` has cycles of length at most `k`, so at least
  -- `n / k` of them.
  have key {σ : Perm (Fin n)} {k : ℕ} (hk : σ ^ k = 1) : (n : ℚ) * (k : ℚ)⁻¹ ≤ orbitCount σ := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hn : n ≤ k * orbitCount σ := by
      simpa using σ.card_le_orderOf_mul_orbitCount.trans
        (Nat.mul_le_mul_right _ (orderOf_le_of_pow_eq_one hk0 hk))
    rw [mul_inv_le_iff₀ (by exact_mod_cast hk0), mul_comm]
    exact_mod_cast hn
  have h0 := key h.1
  have h1 := key h.2.1
  have hinf := key h.2.2
  rw [eulerChar_def]
  push_cast
  linarith

variable {t}

/-- **The orbifold constraint on a connected triple.** If the components of a connected
degree-`n` triple have orders dividing `a`, `b` and `c`, then
`n * (1 / a + 1 / b + 1 / c - 1) ≤ 2`. -/
theorem IsConnected.natCast_mul_inv_add_inv_add_inv_sub_one_le_two (ht : t.IsConnected)
    (h : t.HasDividingOrders a b c) :
    (n : ℚ) * ((a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1) ≤ 2 :=
  (t.natCast_mul_inv_add_inv_add_inv_sub_one_le_eulerChar h).trans
    (by exact_mod_cast ht.eulerChar_le_two)

/-- **The degree bound in the spherical case.** If `1 / a + 1 / b + 1 / c > 1` and the components
of a connected degree-`n` triple have orders dividing `a`, `b` and `c`, then
`n ≤ 2 / (1 / a + 1 / b + 1 / c - 1)`. -/
theorem IsConnected.natCast_le_of_one_lt_inv_add_inv_add_inv (ht : t.IsConnected)
    (h : t.HasDividingOrders a b c)
    (habc : 1 < (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹) :
    (n : ℚ) ≤ 2 / ((a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ - 1) := by
  rw [le_div_iff₀ (sub_pos.2 habc)]
  exact ht.natCast_mul_inv_add_inv_add_inv_sub_one_le_two h

end PermutationTriple

end TauCeti
