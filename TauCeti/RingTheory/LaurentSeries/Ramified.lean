/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Prime
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.Data.Rat.NumDenDvd
public import TauCeti.RingTheory.HahnSeries.EmbDomain

/-!
# Ramified levels of Laurent series

For a positive integer `n`, the Laurent series ring `R⸨X⸩` in a variable `u` embeds into the
Hahn series `HahnSeries ℚ R` with rational exponents by `u ↦ t ^ (1 / n)`: the coefficient of
`u ^ k` becomes the coefficient of `t ^ (k / n)`. Its image, the level-`n` copy of `R⸨X⸩`, consists
of the Hahn series all of whose exponents have denominator dividing `n`. For `n ∣ m` the levels
are related by the substitution `u_n ↦ u_m ^ (m / n)`, which is the exponent expansion
`X ↦ X ^ d` of Laurent series. Over a field, the Puiseux series field is the union of these
levels.

Both maps are `HahnSeries.embDomain` along an additive order embedding of exponent groups,
`k ↦ k / n` from `ℤ` to `ℚ` and `k ↦ d * k` from `ℤ` to `ℤ`. They are algebra homomorphisms for
the default `R`-algebra structures on `R⸨X⸩` and `HahnSeries ℚ R`, those inherited from `R⟦X⟧`
through `HahnSeries.powerSeriesAlgebra`. Mathlib's `HahnSeries.embDomainAlgHom` is stated for
the coefficientwise structure `HahnSeries.instAlgebra` instead, which is propositionally but not
definitionally equal to it, so the algebra maps here are assembled from the ring-level
`embDomain` lemmas.

## Main definitions

* `LaurentSeries.expand R d`: the `R`-algebra map `R⸨X⸩ → R⸨X⸩` substituting `X ↦ X ^ d`.
* `LaurentSeries.ramifiedEmbedding R n`: the `R`-algebra map `R⸨X⸩ → HahnSeries ℚ R` substituting
  `X ↦ t ^ (1 / n)`.

## Main results

* `LaurentSeries.coeff_expand_mul`, `LaurentSeries.coeff_expand_of_not_dvd`: the coefficients
  of `expand R d f`.
* `LaurentSeries.mem_range_expand_iff`: a Laurent series is in the image of `X ↦ X ^ d` exactly
  when all its exponents are divisible by `d`.
* `LaurentSeries.expand_coe`: `expand` extends `PowerSeries.expand`.
* `LaurentSeries.coeff_ramifiedEmbedding_intCast_div`,
  `LaurentSeries.coeff_ramifiedEmbedding_of_not_den_dvd`: the coefficients of the level-`n`
  embedding.
* `LaurentSeries.mem_range_ramifiedEmbedding_iff`: the level-`n` image consists of the Hahn
  series whose exponents all have denominator dividing `n`.
* `LaurentSeries.ramifiedEmbedding_comp_expand`: for `m = n * d`, the transition map
  `X ↦ X ^ d` from level `n` to level `m` commutes with the embeddings.
* `LaurentSeries.range_ramifiedEmbedding_le_iff`: level `n` is contained in level `m` exactly
  when `n ∣ m`.
* `LaurentSeries.range_ramifiedEmbedding_inf`: the intersection of levels `n` and `m` is level
  `gcd n m`.

The signature `LaurentSeries.expand (d : ℕ+)` follows the one proposed for Mathlib in
mathlib4 PR #42313.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace LaurentSeries

variable (R : Type*) [CommSemiring R]

/-! ### Expansion `X ↦ X ^ d` -/

/-- Multiplication by a positive integer as an order embedding of `ℤ`. -/
private def mulOrderEmbedding (d : ℕ+) : ℤ ↪o ℤ :=
  OrderEmbedding.ofStrictMono (fun k ↦ (d : ℤ) * k)
    (strictMono_mul_left_of_pos (by exact_mod_cast d.pos))

private theorem mulOrderEmbedding_apply (d : ℕ+) (k : ℤ) : mulOrderEmbedding d k = d * k :=
  rfl

/-- The substitution `X ↦ X ^ d` in Laurent series, sending the coefficient of `X ^ k` to the
coefficient of `X ^ (d * k)`. -/
noncomputable def expand (d : ℕ+) : R⸨X⸩ →ₐ[R] R⸨X⸩ where
  toFun := embDomain (mulOrderEmbedding d)
  map_one' := embDomain_one _ (mul_zero _)
  map_mul' := embDomain_mul _ fun _ _ ↦ mul_add _ _ _
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
  commutes' r := by simp [algebraMap_apply', mulOrderEmbedding_apply]

variable {R}

private theorem expand_apply (d : ℕ+) (f : R⸨X⸩) :
    expand R d f = embDomain (mulOrderEmbedding d) f :=
  rfl

/-- The coefficient of `X ^ (d * k)` in `expand R d f` is the coefficient of `X ^ k` in `f`. -/
@[simp]
theorem coeff_expand_mul (d : ℕ+) (f : R⸨X⸩) (k : ℤ) :
    (expand R d f).coeff ((d : ℤ) * k) = f.coeff k :=
  embDomain_coeff (f := mulOrderEmbedding d)

/-- The coefficients of `expand R d f` at exponents not divisible by `d` vanish. -/
theorem coeff_expand_of_not_dvd (d : ℕ+) (f : R⸨X⸩) {k : ℤ} (hk : ¬ (d : ℤ) ∣ k) :
    (expand R d f).coeff k = 0 :=
  embDomain_of_notMem_range fun ⟨j, hj⟩ ↦ hk ⟨j, hj.symm⟩

/-- Expansion sends the monomial `r X ^ k` to `r X ^ (d * k)`. -/
@[simp]
theorem expand_single (d : ℕ+) (k : ℤ) (r : R) :
    expand R d (single k r) = single ((d : ℤ) * k) r :=
  embDomain_single

/-- The support of `expand R d f` is the support of `f` multiplied by `d`. -/
theorem support_expand (d : ℕ+) (f : R⸨X⸩) :
    (expand R d f).support = (fun k : ℤ ↦ (d : ℤ) * k) '' f.support :=
  support_embDomain _ f

/-- Expansion multiplies the order by `d`. -/
@[simp]
theorem orderTop_expand (d : ℕ+) (f : R⸨X⸩) :
    (expand R d f).orderTop = (d : ℕ) • f.orderTop := by
  rw [expand_apply, orderTop_embDomain]
  cases f.orderTop with
  | top =>
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero d.ne_zero
    simp [hk, succ_nsmul]
  | coe k => simp [mulOrderEmbedding_apply, ← WithTop.coe_nsmul]

/-- Expansion is injective. -/
theorem expand_injective (d : ℕ+) : Function.Injective (expand R d) :=
  embDomain_injective

/-- A Laurent series is in the image of `X ↦ X ^ d` exactly when all its exponents are divisible
by `d`. -/
theorem mem_range_expand_iff (d : ℕ+) {f : R⸨X⸩} :
    f ∈ (expand R d).range ↔ ∀ k ∈ f.support, (d : ℤ) ∣ k := by
  rw [AlgHom.mem_range, ← Set.mem_range, funext (expand_apply d), mem_range_embDomain_iff]
  refine forall₂_congr fun k _ ↦ ?_
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨j, hj.symm⟩, fun ⟨j, hj⟩ ↦ ⟨j, hj.symm⟩⟩

variable (R) in
/-- Expansion by `1` is the identity. -/
@[simp]
theorem expand_one : expand R 1 = AlgHom.id R R⸨X⸩ := by
  ext f k
  simpa using coeff_expand_mul 1 f k

/-- Expanding by `e` and then by `d` is expanding by `d * e`. -/
theorem expand_expand (d e : ℕ+) (f : R⸨X⸩) :
    expand R d (expand R e f) = expand R (d * e) f := by
  rw [expand_apply, expand_apply, expand_apply, embDomain_embDomain]
  congr 1
  ext k
  simp [mulOrderEmbedding_apply, mul_assoc]

/-- On power series, expansion of Laurent series is Mathlib's `PowerSeries.expand`. -/
theorem expand_coe {R : Type*} [CommRing R] (d : ℕ+) (f : R⟦X⟧) :
    expand R d (f : R⸨X⸩) = (PowerSeries.expand (d : ℕ) d.ne_zero f : R⸨X⸩) := by
  ext k
  rw [PowerSeries.coeff_coe]
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rw [coeff_expand_mul, PowerSeries.coeff_coe, Int.natAbs_mul, Int.natAbs_natCast,
      PowerSeries.coeff_expand_mul]
    have hd : (0 : ℤ) < d := by exact_mod_cast d.pos
    simp [mul_neg_iff, hd.not_gt]
  · rw [coeff_expand_of_not_dvd d _ hk]
    split_ifs with h
    · rfl
    rw [PowerSeries.coeff_expand_of_not_dvd]
    rintro ⟨c, hc⟩
    exact hk ⟨c, by omega⟩

/-! ### Ramified levels in rational exponents -/

/-- Division by a positive integer as an order embedding `ℤ ↪o ℚ`. -/
private def divOrderEmbedding (n : ℕ+) : ℤ ↪o ℚ :=
  OrderEmbedding.ofStrictMono (fun k ↦ (k : ℚ) / n)
    fun _ _ h ↦ div_lt_div_of_pos_right (by exact_mod_cast h) (by exact_mod_cast n.pos)

private theorem divOrderEmbedding_apply (n : ℕ+) (k : ℤ) : divOrderEmbedding n k = k / n :=
  rfl

variable (R) in
/-- The level-`n` embedding of Laurent series into Hahn series with rational exponents,
substituting `X ↦ t ^ (1 / n)`: the coefficient of `X ^ k` becomes the coefficient of
`t ^ (k / n)`. -/
noncomputable def ramifiedEmbedding (n : ℕ+) : R⸨X⸩ →ₐ[R] HahnSeries ℚ R where
  toFun := embDomain (divOrderEmbedding n)
  map_one' := embDomain_one _ (by simp [divOrderEmbedding_apply])
  map_mul' := embDomain_mul _ fun _ _ ↦ by simp [divOrderEmbedding_apply, add_div]
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
  commutes' r := by simp [algebraMap_apply', divOrderEmbedding_apply]

private theorem ramifiedEmbedding_apply (n : ℕ+) (f : R⸨X⸩) :
    ramifiedEmbedding R n f = embDomain (divOrderEmbedding n) f :=
  rfl

/-- The coefficient of `t ^ (k / n)` in the level-`n` image of `f` is the coefficient of `X ^ k`
in `f`. -/
@[simp]
theorem coeff_ramifiedEmbedding_intCast_div (n : ℕ+) (f : R⸨X⸩) (k : ℤ) :
    (ramifiedEmbedding R n f).coeff ((k : ℚ) / n) = f.coeff k :=
  embDomain_coeff (f := divOrderEmbedding n)

/-- The coefficients of the level-`n` image of `f` vanish at exponents whose denominator does not
divide `n`. -/
theorem coeff_ramifiedEmbedding_of_not_den_dvd (n : ℕ+) (f : R⸨X⸩) {q : ℚ}
    (hq : ¬ q.den ∣ n) : (ramifiedEmbedding R n f).coeff q = 0 := by
  refine embDomain_of_notMem_range fun ⟨k, hk⟩ ↦ hq ?_
  exact (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mpr ⟨k, hk.symm⟩

/-- The level-`n` embedding sends the monomial `r X ^ k` to `r t ^ (k / n)`. -/
@[simp]
theorem ramifiedEmbedding_single (n : ℕ+) (k : ℤ) (r : R) :
    ramifiedEmbedding R n (single k r) = single ((k : ℚ) / n) r :=
  embDomain_single

/-- The support of the level-`n` image of `f` is the support of `f` divided by `n`. -/
theorem support_ramifiedEmbedding (n : ℕ+) (f : R⸨X⸩) :
    (ramifiedEmbedding R n f).support = (fun k : ℤ ↦ (k : ℚ) / n) '' f.support :=
  support_embDomain _ f

/-- The order of the level-`n` image of `f` is the order of `f` divided by `n`. -/
@[simp]
theorem orderTop_ramifiedEmbedding (n : ℕ+) (f : R⸨X⸩) :
    (ramifiedEmbedding R n f).orderTop = f.orderTop.map fun k : ℤ ↦ (k : ℚ) / n :=
  orderTop_embDomain

/-- The level-`n` embedding is injective. -/
theorem ramifiedEmbedding_injective (n : ℕ+) : Function.Injective (ramifiedEmbedding R n) :=
  embDomain_injective

/-- The level-`n` image consists of the Hahn series all of whose exponents have denominator
dividing `n`. -/
theorem mem_range_ramifiedEmbedding_iff (n : ℕ+) {x : HahnSeries ℚ R} :
    x ∈ (ramifiedEmbedding R n).range ↔ ∀ q ∈ x.support, q.den ∣ n := by
  rw [AlgHom.mem_range, ← Set.mem_range, funext (ramifiedEmbedding_apply n),
    mem_range_embDomain_iff]
  refine forall₂_congr fun q _ ↦ ?_
  rw [Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, hk.symm⟩, fun ⟨k, hk⟩ ↦ ⟨k, hk.symm⟩⟩

/-- The transition map `X ↦ X ^ d` from level `n` to level `n * d` commutes with the embeddings
into rational exponents. -/
@[simp]
theorem ramifiedEmbedding_expand (n d : ℕ+) (f : R⸨X⸩) :
    ramifiedEmbedding R (n * d) (expand R d f) = ramifiedEmbedding R n f := by
  rw [ramifiedEmbedding_apply, ramifiedEmbedding_apply, expand_apply, embDomain_embDomain]
  congr 1
  ext k
  have hd : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
  simp only [RelEmbedding.trans_apply, mulOrderEmbedding_apply, divOrderEmbedding_apply,
    PNat.mul_coe, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp

/-- `ramifiedEmbedding_expand` as an equality of algebra maps. -/
theorem ramifiedEmbedding_comp_expand (n d : ℕ+) :
    (ramifiedEmbedding R (n * d)).comp (expand R d) = ramifiedEmbedding R n :=
  AlgHom.ext (ramifiedEmbedding_expand n d)

/-- For `n ∣ m`, level `n` is contained in level `m`. -/
theorem range_ramifiedEmbedding_le_of_dvd {n m : ℕ+} (h : n ∣ m) :
    (ramifiedEmbedding R n).range ≤ (ramifiedEmbedding R m).range := fun _ hx ↦
  (mem_range_ramifiedEmbedding_iff m).mpr fun q hq ↦
    ((mem_range_ramifiedEmbedding_iff n).mp hx q hq).trans (PNat.dvd_iff.mp h)

/-- Over a nontrivial ring, level `n` is contained in level `m` exactly when `n ∣ m`. -/
theorem range_ramifiedEmbedding_le_iff [Nontrivial R] {n m : ℕ+} :
    (ramifiedEmbedding R n).range ≤ (ramifiedEmbedding R m).range ↔ n ∣ m := by
  refine ⟨fun h ↦ ?_, range_ramifiedEmbedding_le_of_dvd⟩
  have hmem : single ((n : ℚ)⁻¹) (1 : R) ∈ (ramifiedEmbedding R m).range :=
    h ⟨single 1 1, by simp⟩
  have := (mem_range_ramifiedEmbedding_iff m).mp hmem ((n : ℚ)⁻¹) (by simp)
  rw [Rat.inv_natCast_den_of_pos n.pos] at this
  exact PNat.dvd_iff.mpr this

/-- The intersection of levels `n` and `m` is level `gcd n m`. -/
theorem range_ramifiedEmbedding_inf (n m : ℕ+) :
    (ramifiedEmbedding R n).range ⊓ (ramifiedEmbedding R m).range =
      (ramifiedEmbedding R (n.gcd m)).range := by
  ext x
  simp only [Algebra.mem_inf, mem_range_ramifiedEmbedding_iff, PNat.gcd_coe, Nat.dvd_gcd_iff]
  exact forall₂_and.symm

end LaurentSeries
