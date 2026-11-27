/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import TauCeti.RingTheory.DedekindDomain.SelmerGroup

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.NumberField

/-!
# The height of a square class

Let `R` be a Dedekind domain with fraction field `K`. The `v`-adic valuation of a unit `u` of `K`
changes by an even number when `u` is multiplied by a square, so its parity is a function of the
square class `[u] ∈ Kˣ ⧸ (Kˣ)²`. The **odd support** of `[u]` is the finite set of height-one
primes `v` of `R` at which `ord_v u` is odd, and the **height** of `[u]` is the product of the
absolute norms of these primes,
```
H([u]) = ∏_{v : ord_v u odd} N v.
```
For `R = ℤ` the classes are represented by the squarefree integers `n`, and `H([n]) = |n|`; this is
the height by which quadratic twists of an elliptic curve are ordered in arithmetic statistics. It
is not the norm of a representative, nor the discriminant of `K(√u)`.

Since the odd support of a product is the symmetric difference of the odd supports, the classes of
height one, those with every valuation even, are exactly the Selmer group `K(∅, 2)` of Mathlib's
`IsDedekindDomain.selmerGroup`, and two classes have the same odd support exactly when their
quotient lies in `K(∅, 2)`. When the residue rings of `R` are finite, a class of height at most `X`
has its odd support among the finitely many primes of norm at most `X`, so if moreover `K(∅, 2)` is
finite, only finitely many classes have height at most `X`: the height has the **Northcott
property**. Over the ring of integers of a number field the residue rings are finite and `K(∅, 2)`
is finite, by the class number theorem and Dirichlet's unit theorem.

## Main definitions

* `TauCeti.oddSupport R u`: the height-one primes of `R` at which the unit `u` has odd valuation.
* `TauCeti.SquareClassGroup.oddSupport R t`: the odd support of a square class.
* `TauCeti.SquareClassGroup.height R t`: the product of the absolute norms of the odd-support
  primes of a square class.

## Main results

* `TauCeti.oddSupport_finite`, `TauCeti.oddSupport_mul`, `TauCeti.oddSupport_mul_sq`: the odd
  support is finite, turns products into symmetric differences and ignores square factors.
* `TauCeti.oddSupport_eq_empty_iff_mk_mem_selmerGroup` and
  `TauCeti.oddSupport_eq_oddSupport_iff_mk_div_mem_selmerGroup`: a unit has empty odd support iff
  its class lies in `K(∅, 2)`, and the fibres of the odd support are the cosets of `K(∅, 2)`.
* `TauCeti.SquareClassGroup.height_eq_one_iff`: a class has height one iff its odd support is
  empty, and `TauCeti.SquareClassGroup.height_squareClass_eq_one_iff_mk_mem_selmerGroup` reads this
  as membership in `K(∅, 2)`.
* `TauCeti.SquareClassGroup.northcott_height`: if `R` has finite quotients and `K(∅, 2)` is
  finite, the height is Northcott.
* `TauCeti.SquareClassGroup.instNorthcottHeightRingOfIntegers`: the height on the square classes
  of a number field is Northcott.

## References

* M. Bhargava, Z. Klagsbrun, R. J. Lemke Oliver, A. Shnidman, *Three-isogeny Selmer groups and
  ranks of abelian varieties in quadratic twist families over a number field*, Duke Math. J. 168
  (2019), §2, where the quadratic twists over a number field are ordered by this height.
* A. Burungale, Y. Tian, *A rank zero p-converse to a theorem of Gross–Zagier, Kolyvagin and
  Rubin*, Ann. of Math. 203 (2026), Proposition 1.3.
-/

public section

namespace TauCeti

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The odd support of a unit -/

/-- The **odd support** of a unit `u` of the fraction field of a Dedekind domain `R`: the
height-one primes `v` of `R` at which the `v`-adic valuation of `u` is odd. -/
def oddSupport (u : Kˣ) : Set (HeightOneSpectrum R) :=
  {v | Odd (Multiplicative.toAdd (v.valuationOfNeZero u))}

variable {R}

/-- A prime lies in the odd support of a unit iff the unit has odd valuation there. -/
@[simp]
theorem mem_oddSupport {u : Kˣ} {v : HeightOneSpectrum R} :
    v ∈ oddSupport R u ↔ Odd (Multiplicative.toAdd (v.valuationOfNeZero u)) :=
  Iff.rfl

/-- The odd support of a unit is finite: it consists of primes at which the valuation is not
trivial. -/
theorem oddSupport_finite (u : Kˣ) : (oddSupport R u).Finite := by
  refine (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := R) u.ne_zero).subset
    fun v hv ↦ ?_
  rw [Set.mem_ofPred_eq, ne_eq, ← HeightOneSpectrum.valuationOfNeZero_eq_one_iff]
  intro h
  rw [mem_oddSupport, h, toAdd_one] at hv
  exact Int.not_odd_zero hv

/-- The odd support of a product is the symmetric difference of the odd supports. -/
theorem oddSupport_mul (u w : Kˣ) :
    oddSupport R (u * w) = symmDiff (oddSupport R u) (oddSupport R w) := by
  ext v
  simp only [Set.mem_symmDiff, mem_oddSupport, map_mul, toAdd_mul, Int.odd_iff]
  omega

/-- The unit `1` has empty odd support. -/
@[simp]
theorem oddSupport_one : oddSupport R (1 : Kˣ) = ∅ := by
  ext v
  simp

/-- A unit and its inverse have the same odd support. -/
@[simp]
theorem oddSupport_inv (u : Kˣ) : oddSupport R u⁻¹ = oddSupport R u := by
  ext v
  simp only [mem_oddSupport, map_inv, toAdd_inv, Int.odd_iff]
  omega

/-- A square has empty odd support. -/
@[simp]
theorem oddSupport_sq (y : Kˣ) : oddSupport R (y ^ 2) = ∅ := by
  ext v
  simp only [mem_oddSupport, map_pow, toAdd_pow, nsmul_eq_mul, Nat.cast_ofNat,
    Set.mem_empty_iff_false, iff_false]
  exact Int.not_odd_iff_even.mpr (even_two_mul _)

/-- Multiplying a unit by a square does not change its odd support. -/
@[simp]
theorem oddSupport_mul_sq (u y : Kˣ) : oddSupport R (u * y ^ 2) = oddSupport R u := by
  rw [oddSupport_mul, oddSupport_sq, ← Set.bot_eq_empty, symmDiff_bot]

/-- A unit has empty odd support exactly when its class in `Kˣ ⧸ (Kˣ)²` lies in the Selmer group
`K(∅, 2)`, the classes whose valuations are all even. -/
theorem oddSupport_eq_empty_iff_mk_mem_selmerGroup (u : Kˣ) :
    oddSupport R u = ∅ ↔
      (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := ∅) (n := 2) := by
  refine Set.eq_empty_iff_forall_notMem.trans ⟨fun h v _ ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff, Nat.cast_ofNat, ← even_iff_two_dvd,
      ← Int.not_odd_iff_even]
    exact h v
  · have := h v (Set.notMem_empty v)
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff, Nat.cast_ofNat,
      ← even_iff_two_dvd] at this
    exact Int.not_odd_iff_even.mpr this hv

/-- **The fibres of the odd support are the cosets of `K(∅, 2)`**: two units have the same odd
support exactly when the class of their quotient lies in the Selmer group `K(∅, 2)`. -/
theorem oddSupport_eq_oddSupport_iff_mk_div_mem_selmerGroup (u w : Kˣ) :
    oddSupport R u = oddSupport R w ↔
      (QuotientGroup.mk (u / w) : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := ∅) (n := 2) := by
  rw [← oddSupport_eq_empty_iff_mk_mem_selmerGroup, div_eq_mul_inv, oddSupport_mul,
    oddSupport_inv, ← Set.bot_eq_empty, symmDiff_eq_bot]

/-- Units with the same square class have the same odd support. -/
theorem oddSupport_eq_of_squareClass_eq {u w : Kˣ} (h : squareClass u = squareClass w) :
    oddSupport R u = oddSupport R w := by
  obtain ⟨y, hy⟩ := (squareClass_eq_iff_isSquare_mul u w).mp h
  have hsq : oddSupport R (u * w) = ∅ := by rw [hy, ← sq, oddSupport_sq]
  rwa [oddSupport_mul, ← Set.bot_eq_empty, symmDiff_eq_bot] at hsq

/-! ### The odd support and height of a square class -/

namespace SquareClassGroup

variable (R)

/-- The **odd support** of a square class `t ∈ Kˣ ⧸ (Kˣ)²`: the height-one primes of `R` at which
a representative of `t` has odd valuation. -/
def oddSupport (t : SquareClassGroup K) : Set (HeightOneSpectrum R) :=
  Quotient.liftOn' t (fun u : Additive Kˣ ↦ TauCeti.oddSupport R u.toMul)
    fun a b hab ↦ oddSupport_eq_of_squareClass_eq <| by
      rw [squareClass_def, squareClass_def, ofMul_toMul, ofMul_toMul]
      exact QuotientAddGroup.eq.mpr (QuotientAddGroup.leftRel_apply.mp hab)

variable {R}

/-- The odd support of the square class of a unit is the odd support of the unit. -/
@[simp]
theorem oddSupport_squareClass (u : Kˣ) :
    (squareClass u).oddSupport R = TauCeti.oddSupport R u := by
  rw [squareClass_def, oddSupport, QuotientAddGroup.mk, Quotient.liftOn'_mk'', toMul_ofMul]

/-- The odd support of a square class is finite. -/
theorem oddSupport_finite (t : SquareClassGroup K) : (t.oddSupport R).Finite := by
  rw [← squareClass_toMul_out t, oddSupport_squareClass]
  exact TauCeti.oddSupport_finite _

/-- The trivial square class has empty odd support. -/
@[simp]
theorem oddSupport_zero : (0 : SquareClassGroup K).oddSupport R = ∅ := by
  rw [← squareClass_one, oddSupport_squareClass, TauCeti.oddSupport_one]

/-- The odd support of a sum of square classes is the symmetric difference of the odd supports. -/
@[simp]
theorem oddSupport_add (s t : SquareClassGroup K) :
    (s + t).oddSupport R = symmDiff (s.oddSupport R) (t.oddSupport R) := by
  rw [← squareClass_toMul_out s, ← squareClass_toMul_out t, ← squareClass_mul,
    oddSupport_squareClass, oddSupport_squareClass, oddSupport_squareClass, TauCeti.oddSupport_mul]

variable (R)

/-- The **height** of a square class `t ∈ Kˣ ⧸ (Kˣ)²`: the product of the absolute norms of the
primes of its odd support, `H(t) = ∏_{v : ord_v t odd} N v`. It is positive when the residue rings
of `R` are finite (`height_pos`); otherwise a prime with infinite residue ring has absolute norm
`0`, and so do the classes with that prime in their odd support. -/
noncomputable def height (t : SquareClassGroup K) : ℕ :=
  ∏ᶠ v ∈ t.oddSupport R, Ideal.absNorm v.asIdeal

variable {R}

/-- The height of the square class of a unit is the product of the absolute norms of the primes
at which the unit has odd valuation. -/
theorem height_squareClass (u : Kˣ) :
    height R (squareClass u) = ∏ᶠ v ∈ TauCeti.oddSupport R u, Ideal.absNorm v.asIdeal := by
  rw [height, oddSupport_squareClass]

/-- The height is the product of the absolute norms over the finite odd support. -/
theorem height_eq_prod (t : SquareClassGroup K) :
    height R t = ∏ v ∈ (t.oddSupport_finite (R := R)).toFinset, Ideal.absNorm v.asIdeal :=
  finprod_mem_eq_finite_toFinset_prod _ _

/-- The trivial square class has height one. -/
@[simp]
theorem height_zero : height R (0 : SquareClassGroup K) = 1 := by
  rw [height, oddSupport_zero, finprod_mem_empty]

/-- **The height of a sum of square classes**: `H(s + t) · g² = H(s) · H(t)`, where `g` is the
product of the absolute norms of the primes in both odd supports. -/
theorem height_add_mul_sq (s t : SquareClassGroup K) :
    height R (s + t) * (∏ᶠ v ∈ s.oddSupport R ∩ t.oddSupport R, Ideal.absNorm v.asIdeal) ^ 2 =
      height R s * height R t := by
  have hs := s.oddSupport_finite (R := R)
  have ht := t.oddSupport_finite (R := R)
  rw [height, height, height, oddSupport_add, ← finprod_mem_union_inter hs ht, sq, ← mul_assoc,
    ← finprod_mem_union (disjoint_symmDiff_inf _ _) ((hs.union ht).subset symmDiff_le_sup)
      (hs.inter_of_left _)]
  have hunion : symmDiff (s.oddSupport R) (t.oddSupport R) ∪ s.oddSupport R ∩ t.oddSupport R =
      s.oddSupport R ∪ t.oddSupport R :=
    symmDiff_sup_inf _ _
  rw [hunion]

/-- A square class has height one exactly when its odd support is empty. -/
theorem height_eq_one_iff (t : SquareClassGroup K) : height R t = 1 ↔ t.oddSupport R = ∅ := by
  rw [height_eq_prod, Finset.prod_eq_one_iff, ← (t.oddSupport_finite (R := R)).toFinset_eq_empty,
    Finset.eq_empty_iff_forall_notMem]
  refine forall_congr' fun v ↦ ?_
  have := Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
  tauto

/-- **The square classes of height one are the Selmer group `K(∅, 2)`.** -/
theorem height_squareClass_eq_one_iff_mk_mem_selmerGroup (u : Kˣ) :
    height R (squareClass u) = 1 ↔
      (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := ∅) (n := 2) := by
  rw [height_eq_one_iff, oddSupport_squareClass, oddSupport_eq_empty_iff_mk_mem_selmerGroup]

/-- If `K(∅, 2)` is finite, only finitely many square classes have empty odd support. -/
private theorem finite_setOf_oddSupport_eq_empty
    [Finite (selmerGroup (R := R) (K := K) (S := ∅) (n := 2))] :
    {t : SquareClassGroup K | t.oddSupport R = ∅}.Finite := by
  refine ((selmerGroup (R := R) (K := K) (S := ∅) (n := 2) : Set _).toFinite.image
    fun x ↦ (quotientRangePowMonoidHomEquiv x).toAdd).subset fun t ht ↦ ?_
  rw [← squareClass_toMul_out t] at ht ⊢
  rw [Set.mem_ofPred_eq, oddSupport_squareClass, oddSupport_eq_empty_iff_mk_mem_selmerGroup] at ht
  exact ⟨_, ht, by simp only [quotientRangePowMonoidHomEquiv_mk, toAdd_ofAdd]⟩

variable [Ring.HasFiniteQuotients R]

/-- Every square class has positive height. -/
theorem height_pos (t : SquareClassGroup K) : 0 < height R t := by
  rw [height_eq_prod]
  exact Finset.prod_pos fun v _ ↦ (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' one_pos

/-- The absolute norm of every prime of the odd support is at most the height. -/
theorem absNorm_le_height {t : SquareClassGroup K} {v : HeightOneSpectrum R}
    (hv : v ∈ t.oddSupport R) : Ideal.absNorm v.asIdeal ≤ height R t := by
  refine Nat.le_of_dvd (height_pos t) ?_
  rw [height_eq_prod]
  exact Finset.dvd_prod_of_mem _ ((t.oddSupport_finite (R := R)).mem_toFinset.mpr hv)

/-- **The height of a square class is Northcott**: if `R` has finite residue rings and the
Selmer group `K(∅, 2)` is finite, only finitely many square classes have height at most any given
bound. -/
theorem northcott_height [Finite (selmerGroup (R := R) (K := K) (S := ∅) (n := 2))] :
    Northcott (height R : SquareClassGroup K → ℕ) := by
  -- The odd support of a class of bounded height lies among the finitely many primes of bounded
  -- norm, and the classes with a given odd support form a coset of `K(∅, 2)`.
  refine ⟨fun X ↦ ?_⟩
  -- The odd supports of the classes of height at most `X` are sets of primes of norm at most `X`.
  have himage : ((oddSupport R : SquareClassGroup K → _) '' {t | height R t ≤ X}).Finite := by
    refine (Ring.HasFiniteQuotients.finite_cardQuot_heightOneSpectrum_le (S := R) X
      ).finite_subsets.subset ?_
    rintro _ ⟨t, ht, rfl⟩ v hv
    rw [Set.mem_ofPred_eq, ← Ideal.absNorm_of_ne_bot v.ne_bot]
    exact (absNorm_le_height hv).trans ht
  -- The classes with the odd support of `t₀` are the translates by `t₀` of those with empty
  -- odd support.
  refine Set.Finite.of_finite_fibers _ himage ?_
  rintro _ ⟨t₀, -, rfl⟩
  refine ((finite_setOf_oddSupport_eq_empty (R := R)).preimage
    (Equiv.addRight t₀).injective.injOn).subset ?_
  rintro t ⟨-, ht⟩
  rw [Set.mem_preimage, Equiv.coe_addRight, Set.mem_ofPred_eq, oddSupport_add, ← Set.bot_eq_empty,
    symmDiff_eq_bot]
  exact ht

/-- **The height of a square class of a number field is Northcott**: a number field has only
finitely many square classes of height at most any given bound. -/
instance instNorthcottHeightRingOfIntegers (F : Type*) [Field F] [NumberField F] :
    Northcott (height (NumberField.RingOfIntegers F) : SquareClassGroup F → ℕ) :=
  have := finite_selmerGroup_of_numberField F ∅ 2 Set.finite_empty
  northcott_height

end SquareClassGroup

end TauCeti
