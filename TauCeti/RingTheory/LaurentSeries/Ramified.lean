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
* `LaurentSeries.contract`: the exponent-congruence component of a Laurent series.
* `LaurentSeries.ramifiedEmbedding R n`: the `R`-algebra map `R⸨X⸩ → HahnSeries ℚ R` substituting
  `X ↦ t ^ (1 / n)`.

## Main results

* `LaurentSeries.coeff_expand_mul`, `LaurentSeries.coeff_expand_of_not_dvd`,
  `LaurentSeries.coeff_expand_of_lt_mul_order`: the coefficients of `expand R d f`.
* `LaurentSeries.mem_range_expand_iff`: a Laurent series is in the image of `X ↦ X ^ d` exactly
  when all its exponents are divisible by `d`.
* `LaurentSeries.expand_coe`: `expand` extends `PowerSeries.expand`.
* `FiniteField.LaurentSeries.expand_card`: over a finite field with `q` elements, the expansion
  `X ↦ X ^ q` of a Laurent series is its `q`-th power.
* `LaurentSeries.sum_single_mul_expand_contract`: reconstruction from congruence components.
* `LaurentSeries.contract_eq_of_sum_eq`: uniqueness of the congruence components.
* `LaurentSeries.contract_expand_mul`: `contract d (expand d g * h) r = g * contract d h r`.
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

/-- The coefficients of `expand R d f` below `d` times the order of `f` vanish. -/
theorem coeff_expand_of_lt_mul_order (d : ℕ+) {f : R⸨X⸩} {k : ℤ} (hk : k < d * f.order) :
    (expand R d f).coeff k = 0 := by
  by_cases hd : (d : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_expand_mul]
    exact coeff_eq_zero_of_lt_order (lt_of_mul_lt_mul_left hk (by exact_mod_cast d.pos.le))
  · exact coeff_expand_of_not_dvd d f hd

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

/-- Over a finite field with `q` elements, the expansion `X ↦ X ^ q` of a Laurent series is its
`q`-th power. The modulus is given as a positive natural number `d` with `d = q`. -/
theorem _root_.FiniteField.LaurentSeries.expand_card {K : Type*} [Field K] [Fintype K] (d : ℕ+)
    (hd : (d : ℕ) = Fintype.card K) (f : K⸨X⸩) : expand K d f = f ^ Fintype.card K := by
  rw [← single_order_mul_powerSeriesPart f]
  simp [-single_order_mul_powerSeriesPart, expand_coe, FiniteField.PowerSeries.expand_card,
    mul_pow, single_pow, hd]

/-! ### Contraction by exponent congruence classes -/

/-- The `r`-th exponent-congruence component of a Laurent series. Its coefficient at `k` is the
coefficient of the original series at `d * k + r`. -/
noncomputable def contract {S : Type*} [Zero S] (d : ℕ+) (f : S⸨X⸩) (r : Fin d) : S⸨X⸩ :=
  ofSuppBddBelow (fun k : ℤ ↦ f.coeff ((d : ℤ) * k + r)) <| by
    refine ⟨min 0 f.order, ?_⟩
    intro k hk
    rw [Function.mem_support] at hk
    by_contra hle
    have hklt : k < min 0 f.order := lt_of_not_ge hle
    have hkneg : k < 0 := hklt.trans_le (min_le_left _ _)
    have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast r.val.zero_le
    have hrlt : (r : ℤ) < d := by exact_mod_cast r.isLt
    have hdpos : (0 : ℤ) < d := by exact_mod_cast d.pos
    have hindex : (d : ℤ) * k + r < f.order := by
      have : (d : ℤ) * k + r ≤ k := by nlinarith
      exact this.trans_lt (hklt.trans_le (min_le_right _ _))
    exact hk (coeff_eq_zero_of_lt_order hindex)

/-- The coefficient formula for an exponent-congruence component. -/
@[simp]
theorem coeff_contract {S : Type*} [Zero S] (d : ℕ+) (f : S⸨X⸩) (r : Fin d) (k : ℤ) :
    (contract d f r).coeff k = f.coeff ((d : ℤ) * k + r) := (rfl)

/-- Contraction is additive. -/
@[simp]
theorem contract_add {S : Type*} [AddMonoid S] (d : ℕ+) (f g : S⸨X⸩) (r : Fin d) :
    contract d (f + g) r = contract d f r + contract d g r := by
  ext k
  simp

/-- Every congruence component of the zero series is zero. -/
@[simp]
theorem contract_zero {S : Type*} [Zero S] (d : ℕ+) (r : Fin d) :
    contract d (0 : S⸨X⸩) r = 0 := by
  ext k
  simp

/-- Contraction commutes with scalar multiplication. -/
@[simp]
theorem contract_smul {M S : Type*} [Zero S] [SMulZeroClass M S] (d : ℕ+) (c : M) (f : S⸨X⸩)
    (r : Fin d) : contract d (c • f) r = c • contract d f r := by
  ext k
  simp

/-- Contraction commutes with finite sums. -/
@[simp]
theorem contract_sum {ι S : Type*} [AddCommMonoid S] (d : ℕ+) (s : Finset ι) (f : ι → S⸨X⸩)
    (r : Fin d) : contract d (∑ i ∈ s, f i) r = ∑ i ∈ s, contract d (f i) r := by
  ext k
  simp

/-- The congruence components of a monomial: `X ^ m` contributes to component `r` exactly when
`m ≡ r` modulo `d`, and then as the monomial of exponent `(m - r) / d`. -/
@[simp]
theorem contract_single {S : Type*} [Zero S] (d : ℕ+) (m : ℤ) (a : S) (r : Fin d) :
    contract d (single m a) r = if (d : ℤ) ∣ m - r then single ((m - r) / d) a else 0 := by
  ext k
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast d.ne_zero
  rw [coeff_contract, coeff_single]
  by_cases hdvd : (d : ℤ) ∣ m - r
  · rw [ite_eq_left hdvd, coeff_single]
    obtain ⟨j, hj⟩ := hdvd
    rw [hj, Int.mul_ediv_cancel_left _ hd]
    by_cases hk : k = j
    · rw [ite_eq_left (by rw [hk]; linear_combination -hj), ite_eq_left hk]
    · rw [ite_eq_right hk, ite_eq_right]
      exact fun h ↦ hk (mul_left_cancel₀ hd (by linear_combination h + hj))
  · rw [ite_eq_right hdvd, coeff_zero, ite_eq_right]
    intro h
    exact hdvd ⟨k, by linear_combination -h⟩

/-- The congruence components of `1` vanish except at residue zero. -/
@[simp]
theorem contract_one {S : Type*} [Zero S] [One S] (d : ℕ+) (r : Fin d) :
    contract d (1 : S⸨X⸩) r = if r = 0 then 1 else 0 := by
  rw [← single_zero_one, contract_single]
  by_cases hr : r = 0
  · subst hr
    simp
  · have hr0 : (0 : ℤ) < r := by
      have : (r : ℕ) ≠ 0 := Fin.val_ne_zero_iff.mpr hr
      omega
    have hrd : (r : ℤ) < d := by exact_mod_cast r.isLt
    have hdvd : ¬ (d : ℤ) ∣ 0 - r := by
      rw [zero_sub, dvd_neg]
      exact fun h ↦ hr0.ne' (Int.eq_zero_of_dvd_of_nonneg_of_lt hr0.le hrd h)
    rw [ite_eq_right hdvd, ite_eq_right hr]

/-- At exponent `d * k + r`, a sum of expanded congruence components recovers coefficient `k`
of component `r`. -/
theorem coeff_sum_single_mul_expand {A : Type*} [CommSemiring A] (d : ℕ+)
    (g : Fin d → A⸨X⸩) (r : Fin d) (k : ℤ) :
    (∑ s : Fin d, single (s : ℤ) 1 * expand A d (g s)).coeff ((d : ℤ) * k + r) =
      (g r).coeff k := by
  simp only [coeff_sum, coeff_single_mul, one_mul]
  rw [Finset.sum_eq_single r]
  · convert coeff_expand_mul d (g r) k using 1
    simp
  · intro s _ hsr
    apply coeff_expand_of_not_dvd
    intro hdiv
    have hmod := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.emod_eq_zero_of_dvd hdiv)
    simp only [Int.mul_add_emod_self_left] at hmod
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast r.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast s.isLt)] at hmod
    exact hsr (Fin.ext (by exact_mod_cast hmod.symm))
  · simp

/-- A Laurent series is the sum of its expanded exponent-congruence components. -/
theorem sum_single_mul_expand_contract {A : Type*} [CommSemiring A] (d : ℕ+) (f : A⸨X⸩) :
    ∑ r : Fin d, single (r : ℤ) 1 * expand A d (contract d f r) = f := by
  ext z
  let r : Fin d := ⟨z.natMod d, Int.natMod_lt d.ne_zero⟩
  have hr : (r : ℤ) = z % d := by
    simp only [r, Int.natMod]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast d.ne_zero))
  have hz : (d : ℤ) * (z / d) + r = z := by
    rw [hr, add_comm, Int.emod_add_mul_ediv]
  rw [← hz, coeff_sum_single_mul_expand, coeff_contract, hz]

/-- The components in an expansion by exponent congruence classes are unique. -/
theorem contract_eq_of_sum_eq {A : Type*} [CommSemiring A] (d : ℕ+) (g : Fin d → A⸨X⸩)
    (f : A⸨X⸩) (h : ∑ r : Fin d, single (r : ℤ) 1 * expand A d (g r) = f) (r : Fin d) :
    contract d f r = g r := by
  ext k
  rw [coeff_contract, ← h, coeff_sum_single_mul_expand]

/-- Multiplication by an expanded series passes through the exponent-congruence components. -/
@[simp]
theorem contract_expand_mul {A : Type*} [CommSemiring A] (d : ℕ+) (g h : A⸨X⸩) (r : Fin d) :
    contract d (expand A d g * h) r = g * contract d h r := by
  refine contract_eq_of_sum_eq d (fun s ↦ g * contract d h s) _ ?_ r
  conv_rhs => rw [← sum_single_mul_expand_contract d h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, mul_left_comm]

/-- The congruence components of an expanded series: `expand A d g` lies in the residue-zero
component, where it contracts back to `g`. -/
@[simp]
theorem contract_expand {A : Type*} [CommSemiring A] (d : ℕ+) (g : A⸨X⸩) (r : Fin d) :
    contract d (expand A d g) r = if r = 0 then g else 0 := by
  simpa using contract_expand_mul d g 1 r

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
