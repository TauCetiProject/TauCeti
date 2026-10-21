/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

/-!
# The van der Put basis of continuous functions on `ℤ_p`

For `n : ℕ` let `ℓ(n) = (p.digits n).length` be the number of base-`p` digits of `n`, so that
`ℓ(0) = 0` and `p ^ (ℓ(n) - 1) ≤ n < p ^ ℓ(n)` for `n > 0`. The `n`-th van der Put function is
the indicator of the ball `n + p ^ ℓ(n) ℤ_p`, that is of the `x` whose truncation modulo
`p ^ ℓ(n)` is `n`; for `n = 0` this is the constant function `1`. Deleting the leading digit of
`n > 0` gives `n⁻ = n % p ^ (ℓ(n) - 1)`, and the `n`-th van der Put coefficient of a function
`f` on `ℤ_p` is `f 0` for `n = 0` and `f n - f n⁻` for `n > 0`.

Van der Put's theorem says that for a complete ultrametric normed group `E`, a continuous
`f : ℤ_[p] → E` is the uniformly convergent sum of its van der Put terms, its coefficients tend to
zero, and its sup norm is the sup norm of its coefficients. Conversely every null sequence of
coefficients defines a continuous function. Together, the coefficients give an isometric
isomorphism `C(ℤ_[p], E) ≃ₗᵢ C₀(ℕ, E)`, linear over any scalars acting continuously on `E`.

Unlike Mahler's theorem (`PadicInt.mahlerEquiv`), this needs no `ℤ_[p]`-module structure on `E`,
and its basis functions are locally constant. The proof rests on the telescoping identity
`∑_{n < p ^ k} e_n(x) a_n(f) = f (x mod p ^ k)` (`PadicInt.sum_vanDerPutTerm_vanDerPutCoeff_apply`)
and on the biorthogonality of terms and coefficients (`PadicInt.vanDerPutCoeff_vanDerPutTerm`).

## Main definitions

* `PadicInt.vanDerPutTerm a n`: the function equal to `a` on `n + p ^ ℓ(n) ℤ_p` and to `0` off it.
* `PadicInt.vanDerPutCoeff f n`: the `n`-th van der Put coefficient of `f : ℤ_[p] → E`.
* `PadicInt.vanDerPutSeries a`: the sum of the van der Put terms with coefficients `a`.
* `PadicInt.vanDerPutEquiv S E`: the isometric isomorphism `C(ℤ_[p], E) ≃ₗᵢ[S] C₀(ℕ, E)`.

## Main results

* `PadicInt.sum_vanDerPutTerm_vanDerPutCoeff_apply`: the partial sums over `n < p ^ k` of the van
  der Put expansion of any function evaluate it at the truncations modulo `p ^ k`.
* `PadicInt.vanDerPutCoeff_vanDerPutTerm`: the coefficients of a single term.
* `PadicInt.tendsto_vanDerPutCoeff`, `PadicInt.norm_vanDerPutCoeff_le`: the coefficients of a
  continuous function tend to zero and are bounded by its sup norm.
* `PadicInt.hasSum_vanDerPut`: **van der Put's theorem**, the expansion of a continuous function.
* `PadicInt.vanDerPutCoeff_id`: the coefficients of the identity of `ℤ_[p]` are the leading
  digit parts `n - n⁻`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), 13–59.
* W. H. Schikhof, *Ultrametric Calculus*, Cambridge University Press, 1984, §62.

The definitions and the proof of the isometry are modelled on Mathlib's treatment of the Mahler
basis in `Mathlib.NumberTheory.Padics.MahlerBasis` (`PadicInt.mahlerTerm`, `PadicInt.mahlerSeries`
and `PadicInt.mahlerEquiv`).
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

section Term

variable {E : Type*} [TopologicalSpace E] [Zero E]

/-- The `n`-th van der Put term with value `a`: the locally constant function on `ℤ_[p]` equal to
`a` at the `x` whose truncation modulo `p ^ ℓ` is `n`, and to `0` elsewhere, where
`ℓ = (p.digits n).length` is the number of base-`p` digits of `n`. These `x` form the ball
`n + p ^ ℓ ℤ_[p]` (`PadicInt.vanDerPutTerm_apply_eq_ite_norm_sub_le`); for `n = 0` it is all of
`ℤ_[p]`. -/
noncomputable def vanDerPutTerm (a : E) (n : ℕ) : C(ℤ_[p], E) where
  toFun x := if x.appr (p.digits n).length = n then a else 0
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun m : ℕ ↦ if m = n then a else 0)).comp
      (continuous_appr _)

/-- The defining formula of `vanDerPutTerm`. -/
theorem vanDerPutTerm_apply (a : E) (n : ℕ) (x : ℤ_[p]) :
    vanDerPutTerm a n x = if x.appr (p.digits n).length = n then a else 0 :=
  (rfl)

/-- The `n`-th van der Put term is supported on the closed ball of radius `p ^ (-ℓ)` around `n`,
`ℓ` the number of base-`p` digits of `n`. -/
theorem vanDerPutTerm_apply_eq_ite_norm_sub_le (a : E) (n : ℕ) (x : ℤ_[p]) :
    vanDerPutTerm a n x =
      if ‖x - n‖ ≤ (p : ℝ) ^ (-((p.digits n).length : ℤ)) then a else 0 := by
  rw [vanDerPutTerm_apply]
  exact if_congr (appr_eq_iff_norm_sub_le x (Nat.lt_base_pow_length_digits hp.out.one_lt)) rfl rfl

/-- The value of the `n`-th van der Put term at a natural number `m`. -/
theorem vanDerPutTerm_natCast (a : E) (n m : ℕ) :
    vanDerPutTerm a n (m : ℤ_[p]) = if m % p ^ (p.digits n).length = n then a else 0 := by
  rw [vanDerPutTerm_apply, appr_natCast]

/-- The `0`-th van der Put term is constant. -/
@[simp]
theorem vanDerPutTerm_zero_right (a : E) :
    vanDerPutTerm (p := p) a 0 = ContinuousMap.const ℤ_[p] a := by
  ext x
  simp [vanDerPutTerm_apply]

/-- The van der Put term with value `0` vanishes. -/
@[simp]
theorem vanDerPutTerm_zero_left (n : ℕ) : vanDerPutTerm (p := p) (0 : E) n = 0 := by
  ext x
  simp [vanDerPutTerm_apply]

/-- The `n`-th van der Put term takes the value `a` at `n`. -/
@[simp]
theorem vanDerPutTerm_natCast_self (a : E) (n : ℕ) : vanDerPutTerm (p := p) a n n = a := by
  rw [vanDerPutTerm_natCast, Nat.mod_eq_of_lt (Nat.lt_base_pow_length_digits hp.out.one_lt),
    ite_eq_left rfl]

end Term

section TermAlgebra

variable {E : Type*} [TopologicalSpace E]

/-- The van der Put term is additive in its value. -/
@[simp]
theorem vanDerPutTerm_add [AddZeroClass E] [ContinuousAdd E] (a b : E) (n : ℕ) :
    vanDerPutTerm (p := p) (a + b) n = vanDerPutTerm a n + vanDerPutTerm b n := by
  ext x
  simp only [vanDerPutTerm_apply, ContinuousMap.add_apply]
  split_ifs <;> simp

/-- The van der Put term commutes with negation of its value. -/
@[simp]
theorem vanDerPutTerm_neg [NegZeroClass E] [ContinuousNeg E] (a : E) (n : ℕ) :
    vanDerPutTerm (p := p) (-a) n = -vanDerPutTerm a n := by
  ext x
  simp only [vanDerPutTerm_apply, ContinuousMap.neg_apply]
  split_ifs <;> simp

/-- The van der Put term commutes with scalar multiplication of its value. -/
@[simp]
theorem vanDerPutTerm_smul {S : Type*} [Zero E] [SMulZeroClass S E] [ContinuousConstSMul S E]
    (c : S) (a : E) (n : ℕ) :
    vanDerPutTerm (p := p) (c • a) n = c • vanDerPutTerm a n := by
  ext x
  simp only [vanDerPutTerm_apply, ContinuousMap.smul_apply]
  split_ifs <;> simp

end TermAlgebra

section Coeff

variable {E : Type*}

/-- The `n`-th van der Put coefficient of a function `f` on `ℤ_[p]`: `f 0` for `n = 0`, and
`f n - f n⁻` for `n > 0`, where `n⁻ = n % p ^ Nat.log p n` is `n` with its leading base-`p` digit
deleted. -/
noncomputable def vanDerPutCoeff [Sub E] (f : ℤ_[p] → E) (n : ℕ) : E :=
  if n = 0 then f 0 else f n - f (n % p ^ Nat.log p n : ℕ)

/-- The `0`-th van der Put coefficient is the value at `0`. -/
@[simp]
theorem vanDerPutCoeff_zero [Sub E] (f : ℤ_[p] → E) : vanDerPutCoeff f 0 = f 0 :=
  ite_eq_left rfl

/-- For `n ≠ 0`, the `n`-th van der Put coefficient is `f n - f n⁻`. -/
theorem vanDerPutCoeff_of_ne_zero [Sub E] (f : ℤ_[p] → E) {n : ℕ} (hn : n ≠ 0) :
    vanDerPutCoeff f n = f n - f (n % p ^ Nat.log p n : ℕ) :=
  ite_eq_right hn

/-- The van der Put coefficients are additive in the function. -/
@[simp]
theorem vanDerPutCoeff_add [SubtractionCommMonoid E] (f g : ℤ_[p] → E) (n : ℕ) :
    vanDerPutCoeff (f + g) n = vanDerPutCoeff f n + vanDerPutCoeff g n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [vanDerPutCoeff_of_ne_zero _ hn, Pi.add_apply, add_sub_add_comm]

/-- The van der Put coefficients commute with negation of the function. -/
@[simp]
theorem vanDerPutCoeff_neg [SubtractionCommMonoid E] (f : ℤ_[p] → E) (n : ℕ) :
    vanDerPutCoeff (-f) n = -vanDerPutCoeff f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [vanDerPutCoeff_of_ne_zero _ hn, Pi.neg_apply, neg_sub_neg, neg_sub]

/-- The van der Put coefficients commute with subtraction of functions. -/
@[simp]
theorem vanDerPutCoeff_sub [SubtractionCommMonoid E] (f g : ℤ_[p] → E) (n : ℕ) :
    vanDerPutCoeff (f - g) n = vanDerPutCoeff f n - vanDerPutCoeff g n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [vanDerPutCoeff_of_ne_zero _ hn, Pi.sub_apply, sub_sub_sub_comm]

/-- The van der Put coefficients commute with scalar multiplication of the function. -/
@[simp]
theorem vanDerPutCoeff_smul {S : Type*} [AddGroup E] [DistribSMul S E] (c : S) (f : ℤ_[p] → E)
    (n : ℕ) : vanDerPutCoeff (c • f) n = c • vanDerPutCoeff f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [vanDerPutCoeff_of_ne_zero _ hn, Pi.smul_apply, smul_sub]

/-- The van der Put coefficient of a nonzero `n` is a difference of values at two natural
numbers congruent modulo `p ^ Nat.log p n`. -/
private theorem vanDerPutCoeff_of_ne_zero_eq_sub_appr [Sub E] (f : ℤ_[p] → E) {n : ℕ} (hn : n ≠ 0) :
    vanDerPutCoeff f n = f n - f ((n : ℤ_[p]).appr (Nat.log p n) : ℕ) := by
  rw [vanDerPutCoeff_of_ne_zero f hn, appr_natCast]

/-- **The telescoping identity.** For any function `f` on `ℤ_[p]`, the partial sum over `n < p ^ k`
of its van der Put expansion at `x` is the value of `f` at the truncation of `x` modulo `p ^ k`. -/
theorem sum_vanDerPutTerm_vanDerPutCoeff_apply [AddCommGroup E] [TopologicalSpace E] (f : ℤ_[p] → E)
    (x : ℤ_[p]) (k : ℕ) :
    ∑ n ∈ Finset.range (p ^ k), vanDerPutTerm (vanDerPutCoeff f n) n x = f (x.appr k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.out.pos k.le_succ
    rw [← Finset.sum_range_add_sum_Ico _ hpk, ih]
    -- On `p ^ k ≤ n < p ^ (k + 1)`, the `n`-th term is `f n - f (n % p ^ k)` when
    -- `x mod p ^ (k + 1) = n`, and `0` otherwise.
    have hterm : ∀ n ∈ Finset.Ico (p ^ k) (p ^ (k + 1)),
        vanDerPutTerm (vanDerPutCoeff f n) n x =
          if x.appr (k + 1) = n then f n - f (n % p ^ k : ℕ) else 0 := by
      intro n hn
      obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ico.mp hn
      have hn0 : n ≠ 0 := (pow_pos hp.out.pos k).trans_le hn₁ |>.ne'
      have hlog : Nat.log p n = k := Nat.log_eq_of_pow_le_of_lt_pow hn₁ hn₂
      rw [vanDerPutTerm_apply, Nat.length_digits p n hp.out.one_lt hn0, hlog,
        vanDerPutCoeff_of_ne_zero f hn0, hlog]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with h
    · rw [appr_mod_pow x k.le_succ]
      abel
    · -- The truncation modulo `p ^ (k + 1)` is below `p ^ k`, so it is the truncation modulo
      -- `p ^ k`.
      have hlt : x.appr (k + 1) < p ^ k := by
        by_contra hge
        exact h (Finset.mem_Ico.mpr ⟨not_lt.mp hge, appr_lt x (k + 1)⟩)
      rw [add_zero, ← appr_mod_pow x k.le_succ, Nat.mod_eq_of_lt hlt]

/-- **Biorthogonality**: the van der Put coefficients of the `m`-th van der Put term with value `a`
are `a` at `m` and `0` elsewhere. -/
@[simp]
theorem vanDerPutCoeff_vanDerPutTerm [AddGroup E] [TopologicalSpace E] (a : E) (m n : ℕ) :
    vanDerPutCoeff (vanDerPutTerm (p := p) a m) n = if n = m then a else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 := vanDerPutTerm_natCast (p := p) a m 0
    rw [Nat.cast_zero, Nat.zero_mod] at h0
    rw [vanDerPutCoeff_zero, h0]
  rw [vanDerPutCoeff_of_ne_zero _ hn, vanDerPutTerm_natCast, vanDerPutTerm_natCast]
  set L := Nat.log p n
  have hnL : n < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n
  have hLn : p ^ L ≤ n := Nat.pow_log_le_self p hn
  have hmod : n % p ^ L < p ^ L := Nat.mod_lt _ (pow_pos hp.out.pos L)
  rcases le_or_gt (p.digits m).length L with hm | hm
  · -- The term is constant along `n ≡ n⁻ [MOD p ^ L]`, and `m < p ^ L ≤ n`.
    have hmn : m ≠ n := ((Nat.lt_base_pow_length_digits hp.out.one_lt).trans_le
      ((Nat.pow_le_pow_right hp.out.pos hm).trans hLn)).ne
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p hm), sub_self, ite_eq_right hmn.symm]
  · -- Here `m` has at least as many digits as `n`, so `n⁻ < p ^ L ≤ m`.
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    have hLm : p ^ L ≤ m := by
      rw [Nat.length_digits p m hp.out.one_lt hm0, Nat.lt_succ_iff] at hm
      exact (Nat.pow_le_pow_right hp.out.pos hm).trans (Nat.pow_log_le_self p hm0)
    have hpow : p ^ (L + 1) ≤ p ^ (p.digits m).length := Nat.pow_le_pow_right hp.out.pos hm
    rw [Nat.mod_eq_of_lt (hnL.trans_le hpow),
      Nat.mod_eq_of_lt (hmod.trans_le (Nat.pow_le_pow_right hp.out.pos hm.le)),
      ite_eq_right (hmod.trans_le hLm).ne, sub_zero]

end Coeff

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The sup norm of a van der Put term is the norm of its value. -/
@[simp]
theorem norm_vanDerPutTerm (a : E) (n : ℕ) :
    ‖vanDerPutTerm (p := p) a n‖ = ‖a‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg a)).mpr fun x ↦ ?_) ?_
  · rw [vanDerPutTerm_apply]
    split_ifs <;> simp
  · simpa using (vanDerPutTerm (p := p) a n).norm_coe_le_norm n

/-- The van der Put coefficients of a continuous function tend to zero: `n` and `n⁻` are
congruent modulo `p ^ Nat.log p n`, and `f` is uniformly continuous. -/
theorem tendsto_vanDerPutCoeff (f : C(ℤ_[p], E)) :
    Tendsto (vanDerPutCoeff f) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hδ
  refine ⟨p ^ k, fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := (pow_pos hp.out.pos k).trans_le hn |>.ne'
  rw [dist_zero_right, vanDerPutCoeff_of_ne_zero_eq_sub_appr _ hn0, ← dist_eq_norm]
  exact hf ((dist_eq_norm _ _).trans_lt ((norm_sub_appr_le_of_le _
    ((Nat.le_log_iff_pow_le hp.out.one_lt hn0).mpr hn)).trans_lt hk))

/-- Over an ultrametric group, the van der Put coefficients of a continuous function are bounded by
its sup norm. -/
theorem norm_vanDerPutCoeff_le [IsUltrametricDist E] (f : C(ℤ_[p], E)) (n : ℕ) :
    ‖vanDerPutCoeff f n‖ ≤ ‖f‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using f.norm_coe_le_norm 0
  rw [vanDerPutCoeff_of_ne_zero f hn, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (f.norm_coe_le_norm _) ((norm_neg _).trans_le (f.norm_coe_le_norm _)))

end Seminormed

section Normed

variable {S E : Type*} [NormedAddCommGroup E]

variable [IsUltrametricDist E] [CompleteSpace E]

section Series

variable {a : ℕ → E}

/-- The van der Put series `x ↦ ∑ n, e_n(x) a n` with coefficients `a`. -/
noncomputable def vanDerPutSeries (a : ℕ → E) : C(ℤ_[p], E) :=
  ∑' n, vanDerPutTerm (a n) n

/-- A van der Put series whose coefficients tend to zero converges uniformly. -/
theorem hasSum_vanDerPutSeries (ha : Tendsto a atTop (𝓝 0)) :
    HasSum (fun n ↦ vanDerPutTerm (a n) n) (vanDerPutSeries (p := p) a) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [norm_vanDerPutTerm, Nat.cofinite_eq_atTop] using ha

/-- A convergent van der Put series is evaluated pointwise. -/
theorem vanDerPutSeries_apply (ha : Tendsto a atTop (𝓝 0)) (x : ℤ_[p]) :
    vanDerPutSeries a x = ∑' n, vanDerPutTerm (a n) n x :=
  (ContinuousMap.hasSum_apply (hasSum_vanDerPutSeries ha) x).tsum_eq.symm

/-- The van der Put coefficients of a convergent van der Put series are its coefficients. -/
theorem vanDerPutCoeff_vanDerPutSeries (ha : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    vanDerPutCoeff (vanDerPutSeries (p := p) a) n = a n := by
  have h (x : ℤ_[p]) : HasSum (fun m ↦ vanDerPutTerm (a m) m x) (vanDerPutSeries a x) :=
    ContinuousMap.hasSum_apply (hasSum_vanDerPutSeries ha) x
  have hsum : HasSum (fun m ↦ vanDerPutCoeff (vanDerPutTerm (p := p) (a m) m) n)
      (vanDerPutCoeff (vanDerPutSeries (p := p) a) n) := by
    unfold vanDerPutCoeff
    split_ifs
    exacts [h 0, (h _).sub (h _)]
  simp_rw [vanDerPutCoeff_vanDerPutTerm] at hsum
  refine hsum.unique ?_
  convert hasSum_ite_eq n (a n) using 2 with m
  rcases eq_or_ne m n with rfl | hm
  · simp
  · simp [hm, hm.symm]

/-- **Van der Put's theorem**: a continuous function on `ℤ_[p]` with values in a complete
ultrametric normed group is the uniformly convergent sum of its van der Put terms. -/
theorem hasSum_vanDerPut (f : C(ℤ_[p], E)) :
    HasSum (fun n ↦ vanDerPutTerm (vanDerPutCoeff f n) n) f := by
  convert hasSum_vanDerPutSeries (tendsto_vanDerPutCoeff f) using 1
  ext x
  -- Along `N = p ^ k`, the partial sums at `x` are `f (x mod p ^ k)`, which tend to `f x`.
  have hpow : Tendsto (fun k ↦ p ^ k) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ (Nat.lt_pow_self hp.out.one_lt).le) tendsto_id
  have hser := ((ContinuousMap.hasSum_apply
    (hasSum_vanDerPutSeries (tendsto_vanDerPutCoeff f)) x).tendsto_sum_nat).comp hpow
  refine tendsto_nhds_unique ?_ hser
  simp_rw [Function.comp_def, sum_vanDerPutTerm_vanDerPutCoeff_apply]
  exact (f.continuous.tendsto x).comp (tendsto_appr x)

end Series

/-- A continuous function is the van der Put series of its van der Put coefficients. -/
theorem vanDerPutSeries_vanDerPutCoeff (f : C(ℤ_[p], E)) :
    vanDerPutSeries (vanDerPutCoeff f) = f :=
  (hasSum_vanDerPut f).tsum_eq

variable (S E) in
/-- **Van der Put's theorem**, as an isometric isomorphism between the continuous functions on
`ℤ_[p]` with values in a complete ultrametric normed group `E` and the null sequences in `E`,
sending a function to its van der Put coefficients. It is linear over any scalars `S` acting
continuously on `E`. -/
noncomputable def vanDerPutEquiv [Semiring S] [Module S E] [ContinuousConstSMul S E] :
    C(ℤ_[p], E) ≃ₗᵢ[S] C₀(ℕ, E) where
  toFun f := ZeroAtInftyContinuousMap.mkOfDiscrete (vanDerPutCoeff f)
    (Nat.cofinite_eq_atTop ▸ tendsto_vanDerPutCoeff f)
  invFun a := vanDerPutSeries a
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp
  left_inv f := by simpa using vanDerPutSeries_vanDerPutCoeff f
  right_inv a := ZeroAtInftyContinuousMap.ext fun n ↦ by
    simpa using vanDerPutCoeff_vanDerPutSeries (Nat.cofinite_eq_atTop ▸ a.tendsto_cofinite) n
  norm_map' f := by
    simp only [LinearEquiv.coe_mk, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine le_antisymm (BoundedContinuousFunction.norm_le_of_nonempty.mpr fun n ↦ ?_) ?_
    · simpa using norm_vanDerPutCoeff_le f n
    conv_lhs => rw [← vanDerPutSeries_vanDerPutCoeff f]
    refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n ↦ ?_)
    rw [norm_vanDerPutTerm]
    refine le_trans (le_of_eq ?_) (BoundedContinuousFunction.norm_coe_le_norm _ n)
    simp

variable [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- The coordinates of `vanDerPutEquiv S E f` are the van der Put coefficients of `f`. -/
@[simp]
theorem vanDerPutEquiv_apply (f : C(ℤ_[p], E)) (n : ℕ) :
    vanDerPutEquiv S E f n = vanDerPutCoeff f n :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _) n

/-- The inverse of `vanDerPutEquiv S E` sums the van der Put series. -/
theorem vanDerPutEquiv_symm_apply (a : C₀(ℕ, E)) :
    (vanDerPutEquiv S E).symm a = vanDerPutSeries (p := p) a :=
  (rfl)

/-- The van der Put series of the coordinate vector `single n a` is the van der Put term
`vanDerPutTerm a n`. -/
@[simp]
theorem vanDerPutEquiv_symm_single (n : ℕ) (a : E) :
    (vanDerPutEquiv S E).symm (ZeroAtInftyContinuousMap.single n a) =
      vanDerPutTerm (p := p) a n := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext m
  rw [vanDerPutEquiv_apply, vanDerPutCoeff_vanDerPutTerm,
    ZeroAtInftyContinuousMap.single_apply]

end Normed

/-- The van der Put coefficients of the identity of `ℤ_[p]`: for `n > 0`, the `n`-th coefficient
is `n - n⁻`, the leading base-`p` digit of `n` times `p ^ Nat.log p n`. -/
theorem vanDerPutCoeff_id {n : ℕ} (hn : n ≠ 0) :
    vanDerPutCoeff (fun x : ℤ_[p] ↦ x) n =
      ((n / p ^ Nat.log p n * p ^ Nat.log p n : ℕ) : ℤ_[p]) := by
  rw [vanDerPutCoeff_of_ne_zero _ hn, sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod']

/-- At `p = 3`, the integer `7` has base-`3` digits `2 1`, so the corresponding van der Put
coefficient of the identity is `7 - 1 = 2 * 3`. -/
example : vanDerPutCoeff (fun x : ℤ_[3] ↦ x) 7 = 6 := by
  have : Nat.log 3 7 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [vanDerPutCoeff_id (by norm_num), this]
  norm_num

end PadicInt
