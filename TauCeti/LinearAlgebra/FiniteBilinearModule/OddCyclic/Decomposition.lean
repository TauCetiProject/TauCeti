/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Splitting
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Orthogonal decomposition of nondegenerate quadratic modules of odd order

Every nondegenerate finite quadratic module of odd order is an orthogonal sum of Nikulin's odd
cyclic generators `q_θ^{(p)}(p^k)`: cyclic groups of odd prime-power order `p^k` with the
quadratic form `q(x) = θ(p^k + 1)x²/(2p^k)` of the pairing `b(x, y) = θxy/p^k`, for `θ`
prime to `p`.

The decomposition splits off one cyclic summand at a time. In a nondegenerate module `A` and for
an odd prime `p` dividing `#A`, let `x` have the largest order `p^k` among elements of `p`-power
order. Since `b(x, ·)` is a character of order `p^k`, some `y` has `p^{k-1} b(x, y) ≠ 0`, and `y`
may be replaced by its `p`-primary part. One of `x`, `y` and `x + y` then has
`p^{k-1} b(z, z) ≠ 0`, because

```text
b(x + y, x + y) = b(x, x) + 2 b(x, y) + b(y, y)
```

and `2` is invertible on the `p`-torsion of `ℚ/ℤ`. For such a `z` the self-pairing `b(z, z)` has
the same order `p^k` as `z`, so the cyclic subgroup `⟨z⟩` is nondegenerate and splits off
orthogonally. Its orthogonal complement is nondegenerate of smaller order, and `⟨z⟩` is an odd
cyclic module by the cyclic classification.

At `p = 2` the argument fails at the last step, and indeed the forms `u^{(2)}(2^k)` and
`v^{(2)}(2^k)` have no nondegenerate cyclic subgroup: the `2`-primary part needs the rank-two
generators as well.

## Main declarations

* `TauCeti.FiniteBilinearModule.exists_isNondegenerate_restrict_zmultiples`: a nondegenerate
  finite bilinear module whose order is divisible by an odd prime `p` has an element of order
  `p^k`, `k ≥ 1`, generating a nondegenerate cyclic subgroup.
* `TauCeti.FiniteQuadraticModule.exists_isometry_pi_oddCyclic`: a nondegenerate finite quadratic
  module of odd order is isometric to an orthogonal sum of odd cyclic modules of prime-power order
  with coefficients prime to that order.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti

universe u

namespace FiniteBilinearModule

variable {A : FiniteBilinearModule.{u}}

/-- The pairing is `ℕ`-linear in its first argument. -/
private theorem pairing_nsmul_left (n : ℕ) (x y : A) :
    A.pairing (n • x) y = n • A.pairing x y := by
  rw [A.pairing_comm, map_nsmul, A.pairing_comm]

/-- If `p^{k+1}` kills `z` but not `p^k b(z, z)`, then `z` has order `p^{k+1}` and generates a
nondegenerate cyclic subgroup. -/
private theorem addOrderOf_eq_and_isNondegenerate_of_pairing {p k : ℕ} [Fact p.Prime] {z : A}
    (hz : p ^ (k + 1) • z = 0) (hzz : p ^ k • A.pairing z z ≠ 0) :
    addOrderOf z = p ^ (k + 1) ∧ (A.restrict (zmultiples z)).IsNondegenerate := by
  have horder : addOrderOf z = p ^ (k + 1) := addOrderOf_eq_prime_pow
    (fun h ↦ hzz (by rw [← map_nsmul, h, map_zero])) hz
  refine ⟨horder, (A.isNondegenerate_restrict_zmultiples_iff z).2 ?_⟩
  rw [horder]
  exact addOrderOf_eq_prime_pow hzz (by rw [← map_nsmul, hz, map_zero])

/-- An element `y` can be replaced by an element of `p`-power order with the same pairing against
a given `x` killed by `p^k`: write `#⟨y⟩ = p^e r` with `p ∤ r` and take the multiple of `y` by an
inverse of `r` modulo `p^k`. -/
private theorem exists_pairing_eq_of_addOrderOf_eq_prime_pow {p k : ℕ} [hp : Fact p.Prime]
    {x : A} (hx : p ^ k • x = 0) (y : A) :
    ∃ y' : A, (∃ e, addOrderOf y' = p ^ e) ∧ A.pairing x y' = A.pairing x y := by
  obtain ⟨e, r, hr, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (addOrderOf_pos y).ne' p
    hp.out.one_lt.ne'
  obtain ⟨s, t, hst⟩ : IsCoprime (r : ℤ) ((p ^ k : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hr).symm)
  refine ⟨(s * r) • y, ?_, ?_⟩
  · -- `p^e` kills `(s r) • y`, so its order is a power of `p`.
    have hdvd : addOrderOf ((s * r) • y) ∣ p ^ e := by
      rw [← Int.natCast_dvd_natCast, addOrderOf_dvd_iff_zsmul_eq_zero, smul_smul,
        show ((p ^ e : ℕ) : ℤ) * (s * r) = s * (addOrderOf y : ℤ) by rw [hn]; push_cast; ring,
        mul_zsmul, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero]
    obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    exact ⟨e', he'⟩
  · -- `s r ≡ 1` modulo `p^k`, which kills `b(x, y)`.
    have hpk : ((p ^ k : ℕ) : ℤ) • A.pairing x y = 0 := by
      rw [natCast_zsmul, ← pairing_nsmul_left, hx, pairing_zero_left]
    rw [map_zsmul, show s * r = 1 - t * ((p ^ k : ℕ) : ℤ) by rw [← hst]; ring, sub_smul,
      one_smul, mul_smul, hpk, smul_zero, sub_zero]

/-- For an odd prime `p`, if `p^{k+1}` kills `x` and `y` but not `p^k b(x, y)`, then one of `x`,
`y` and `x + y` has `p^k b(z, z) ≠ 0`, since `b(x + y, x + y) = b(x, x) + 2 b(x, y) + b(y, y)`. -/
private theorem exists_nsmul_pairing_self_ne_zero {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : A}
    (hx : p ^ (k + 1) • x = 0) (hy : p ^ (k + 1) • y = 0) (hxy : p ^ k • A.pairing x y ≠ 0) :
    ∃ z : A, p ^ (k + 1) • z = 0 ∧ p ^ k • A.pairing z z ≠ 0 := by
  by_cases h₁ : p ^ k • A.pairing x x = 0
  · by_cases h₂ : p ^ k • A.pairing y y = 0
    · refine ⟨x + y, by rw [nsmul_add, hx, hy, add_zero], fun h ↦ hxy ?_⟩
      rw [pairing_add_left, map_add, map_add, A.pairing_comm y x, nsmul_add, nsmul_add,
        nsmul_add, h₁, h₂, zero_add, add_zero, ← two_nsmul] at h
      -- `p^k b(x, y)` is killed by `2` and by `p`, which are coprime.
      refine (nsmul_eq_zero_iff_of_coprime (m := 2) (n := p) ?_).1 ⟨h, ?_⟩
      · exact (Nat.coprime_primes Nat.prime_two hp).2 hp2.symm
      · rw [← mul_nsmul', ← pow_succ', ← pairing_nsmul_left, hx, pairing_zero_left]
    · exact ⟨y, hy, h₂⟩
  · exact ⟨x, hx, h₁⟩

/-- **A nondegenerate cyclic summand of odd prime-power order.** In a nondegenerate finite bilinear
module whose order is divisible by an odd prime `p`, some element of order `p^k`, `k ≥ 1`,
generates a cyclic subgroup on which the pairing is nondegenerate.

The hypothesis `p ≠ 2` is necessary: in `u^{(2)}(2)`, the hyperbolic pairing on `(ℤ/2)²`, every
element is isotropic, so no cyclic subgroup is nondegenerate. -/
theorem exists_isNondegenerate_restrict_zmultiples {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hA : A.IsNondegenerate) (hpA : p ∣ Nat.card A) :
    ∃ z : A, ∃ k, 0 < k ∧ addOrderOf z = p ^ k ∧ (A.restrict (zmultiples z)).IsNondegenerate := by
  classical
  have : Fintype A := Fintype.ofFinite A
  -- Choose `x` of the largest order `p^k` among elements of `p`-power order.
  obtain ⟨x, hxS, hmax⟩ := (Finset.univ.filter fun x : A ↦ ∃ k, addOrderOf x = p ^ k)
    |>.exists_max_image addOrderOf ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, 0, by simp⟩⟩
  obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hxS).2
  have hkill : ∀ y : A, (∃ e, addOrderOf y = p ^ e) → p ^ k • y = 0 := by
    rintro y ⟨e, he⟩
    have hle : p ^ e ≤ p ^ k :=
      he ▸ hk ▸ hmax y (Finset.mem_filter.2 ⟨Finset.mem_univ _, e, he⟩)
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, he]
    exact Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle)
  -- By Cauchy's theorem there is an element of order `p`, so `k ≥ 1`.
  obtain ⟨y₀, hy₀⟩ := exists_prime_addOrderOf_dvd_card' p hpA
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hk0 ↦ hp.out.one_lt.ne' ?_
    have := hkill y₀ ⟨1, by rw [hy₀, pow_one]⟩
    rw [hk0, pow_zero, one_smul] at this
    rw [← hy₀, this, addOrderOf_zero]
  have hxk : p ^ (k + 1) • x = 0 := by rw [← hk, addOrderOf_nsmul_eq_zero]
  -- The character `b(x, ·)` has order `p^{k+1}`, so `p^k b(x, y) ≠ 0` for some `y`, which may
  -- be taken of `p`-power order.
  obtain ⟨y, hy⟩ : ∃ y, p ^ k • A.pairing x y ≠ 0 := by
    by_contra! h
    refine nsmul_ne_zero_of_lt_addOrderOf (pow_ne_zero _ hp.out.ne_zero)
      (hk ▸ Nat.pow_lt_pow_right hp.out.one_lt k.lt_succ_self) ?_
    exact IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ hA fun y ↦ by
      rw [pairing_nsmul_left, h y]
  obtain ⟨y', hy'p, hxy'⟩ := exists_pairing_eq_of_addOrderOf_eq_prime_pow hxk y
  rw [← hxy'] at hy
  obtain ⟨z, hz, hzz⟩ := exists_nsmul_pairing_self_ne_zero hp.out hp2 hxk (hkill y' hy'p) hy
  obtain ⟨horder, hnd⟩ := addOrderOf_eq_and_isNondegenerate_of_pairing hz hzz
  exact ⟨z, k + 1, k.succ_pos, horder, hnd⟩

end FiniteBilinearModule

namespace FiniteQuadraticModule

/-- **Nikulin's decomposition of nondegenerate quadratic modules of odd order.** A nondegenerate
finite quadratic module of odd order is isometric to an orthogonal sum of odd cyclic modules
`q_θ^{(p)}(p^k)`, each of odd prime-power order `m = p^k` with coefficient `θ` prime to `m`. -/
theorem exists_isometry_pi_oddCyclic (A : FiniteQuadraticModule.{u}) (hA : A.IsNondegenerate)
    (hodd : Odd (Nat.card A)) :
    ∃ (n : ℕ) (m : Fin n → ℕ) (hm : ∀ i, Odd (m i)) (θ : Fin n → ℤ),
      (∀ i, IsPrimePow (m i) ∧ IsCoprime (m i : ℤ) (θ i)) ∧
        Nonempty (Isometry (pi fun i ↦ oddCyclic (m i) (hm i) (θ i)) A) := by
  induction hN : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  rcases eq_or_ne N 1 with rfl | hN1
  · -- The trivial module is the empty orthogonal sum.
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 hN).1
    refine ⟨0, Fin.elim0, fun i ↦ i.elim0, Fin.elim0, fun i ↦ i.elim0, ⟨?_⟩⟩
    exact { toLinearEquiv := LinearEquiv.ofSubsingleton _ _
            map_app' x := by simp [Subsingleton.elim x 0] }
  -- Split off a nondegenerate cyclic summand `C = ⟨z⟩` of odd prime-power order.
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (hN ▸ hodd).not_two_dvd_nat hpN
  obtain ⟨z, k, hk, hz, hzA⟩ :=
    A.toFiniteBilinearModule.exists_isNondegenerate_restrict_zmultiples hp2 hA (hN ▸ hpN)
  have hzA' : (A.restrict (zmultiples z)).IsNondegenerate := by
    rwa [IsNondegenerate, restrict_toFiniteBilinearModule]
  let e := A.restrictProdOrthogonalComplementIsometry hzA'
  set C := A.restrict (zmultiples z)
  set D := A.restrict (A.toFiniteBilinearModule.orthogonalComplement (zmultiples z)) with hD
  have hDnd : D.IsNondegenerate := by
    rw [hD, IsNondegenerate, restrict_toFiniteBilinearModule]
    exact hA.isNondegenerate_restrict_orthogonalComplement hzA
  have hcard : Nat.card C * Nat.card D = N := by
    rw [← Nat.card_prod, ← hN]
    exact Nat.card_congr e.toLinearEquiv.toEquiv
  have hCcard : Nat.card C = p ^ k := (Nat.card_zmultiples z).trans hz
  have hCDodd : Odd (Nat.card C * Nat.card D) := hcard ▸ hN ▸ hodd
  have hCodd : Odd (Nat.card C) := (Nat.odd_mul.1 hCDodd).1
  -- The complement is nondegenerate of smaller odd order, so the induction hypothesis applies.
  have hDlt : Nat.card D < N := by
    rw [← hcard]
    refine lt_mul_left Nat.card_pos ?_
    rw [hCcard]
    exact Nat.one_lt_pow hk.ne' hp.one_lt
  obtain ⟨n, m, hm, θ, hmθ, ⟨f⟩⟩ :=
    ih _ hDlt D hDnd (Nat.odd_mul.1 hCDodd).2 rfl
  have : IsAddCyclic C := inferInstanceAs (IsAddCyclic (zmultiples z))
  obtain ⟨θ₀, hθ₀, ⟨g⟩⟩ := exists_oddCyclic_isometry C hCodd hzA'
  refine ⟨n + 1, Fin.cons (Nat.card C) m, Fin.cases hCodd hm, Fin.cons θ₀ θ,
    Fin.cases ⟨hCcard ▸ hp.isPrimePow.pow hk.ne', hθ₀⟩ hmθ, ⟨?_⟩⟩
  exact (QuadraticMap.IsometryEquiv.consPi _).symm.trans ((g.prod f).trans e)

end FiniteQuadraticModule

end TauCeti
