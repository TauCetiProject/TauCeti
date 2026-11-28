/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.Isocrystal.StandardBlock
public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Valuation.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Rat.MinRatio
import TauCeti.FieldTheory.IsAlgClosed.FrobeniusFixedPoints
import TauCeti.LinearAlgebra.LinearEquiv.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Iterate
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# Existence of cyclic standard-block sub-isocrystals

Over `k((π))` with `k` algebraically closed of characteristic `p > 0` and
`σ = LaurentSeries.coefficientFrobenius p f` (`f > 0`), every nontrivial finite-dimensional
`σ`-semilinear system `(V, Φ)` with `Φ` injective contains a coprime cyclic standard block
`D(s, r)` via a Frobenius-equivariant `k((π))`-linear embedding
(`TauCeti.exists_injective_intertwines_standardBlock`).

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
* K. S. Kedlaya, *Slope filtrations revisited*, Doc. Math. 10 (2005), 447–525, §4.5
  (4.5.3–4.5.8, pp. 497–499).
-/

public section

open Finset Function Module
open scoped LaurentSeries PowerSeries

namespace TauCeti

/-! ### Finding a simple standard-block sub-isocrystal -/

section SubBlock

private noncomputable def companionMatrixMap {k : Type*} [Field k] {p f : ℕ} [Fact p.Prime]
    [CharP k p] (n : ℕ) (b₀ : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₛₗ[_root_.iterateFrobenius k p f] (Fin (n + 1) → k) where
  toFun d := Fin.cases (b₀ 0 * d (Fin.last n) ^ p ^ f)
    (fun j ↦ d j.castSucc ^ p ^ f + b₀ j.succ * d (Fin.last n) ^ p ^ f)
  map_add' x y := by
    have : ExpChar k p := expChar_prime k p
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    · simp only [Fin.cases_zero, Fin.cases_succ, Pi.add_apply, add_pow_char_pow]
      ring
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    · simp only [Fin.cases_zero, Fin.cases_succ, Pi.smul_apply, smul_eq_mul, mul_pow,
        _root_.iterateFrobenius_def]
      ring

@[simp]
private theorem companionMatrixMap_apply_zero {k : Type*} [Field k] {p f : ℕ} [Fact p.Prime]
    [CharP k p] (n : ℕ) (b₀ : Fin (n + 1) → k) (d : Fin (n + 1) → k) :
    companionMatrixMap (p := p) (f := f) n b₀ d 0 = b₀ 0 * d (Fin.last n) ^ p ^ f := by
  simp [companionMatrixMap]

@[simp]
private theorem companionMatrixMap_apply_succ {k : Type*} [Field k] {p f : ℕ} [Fact p.Prime]
    [CharP k p] (n : ℕ) (b₀ : Fin (n + 1) → k) (d : Fin (n + 1) → k) (j : Fin n) :
    companionMatrixMap (p := p) (f := f) n b₀ d j.succ =
      d j.castSucc ^ p ^ f + b₀ j.succ * d (Fin.last n) ^ p ^ f := by
  simp [companionMatrixMap]

private theorem companionMatrixMap_iterate_single_zero {k : Type*} [Field k] {p f : ℕ}
    [Fact p.Prime] [CharP k p] (n : ℕ) (b₀ : Fin (n + 1) → k) :
    (companionMatrixMap (p := p) (f := f) n b₀)^[n + 1] (Pi.single 0 1) = b₀ := by
  have hcast : ∀ m (hm : m ≤ n),
      (companionMatrixMap (p := p) (f := f) n b₀)^[m] (Pi.single 0 1) =
        Pi.single ⟨m, Nat.lt_succ_of_le hm⟩ (1 : k) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iterate_succ_apply', ih (Nat.le_of_succ_le hm)]
      ext i
      have hne_last :
          (Fin.last n : Fin (n + 1)) ≠ ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ := by
        simp [Fin.ext_iff]; omega
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [Pi.single_eq_of_ne hne_last,
          zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero), Fin.ext_iff]
      · simp [Pi.single_eq_of_ne hne_last,
          zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero),
          Pi.single_apply, Fin.ext_iff, apply_ite (· ^ p ^ f)]
  rw [iterate_succ_apply', hcast n le_rfl]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Fin.last]
  · simp [Fin.last, Fin.ext_iff, Nat.ne_of_lt j.isLt,
      zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)]

private theorem exists_companion_powerSeries_coeffs {k : Type*} [Field k] {p f : ℕ}
    [Fact p.Prime] [CharP k p] [IsAlgClosed k] (hf : f ≠ 0) (n : ℕ)
    (b : Fin (n + 1) → k⟦X⟧) (hb : ∃ i, PowerSeries.constantCoeff (b i) ≠ 0) :
    ∃ d : ℕ → Fin (n + 1) → k,
      d 0 ≠ 0 ∧
      companionMatrixMap (p := p) (f := f) n (fun i ↦ PowerSeries.constantCoeff (b i)) (d 0) =
        d 0 ∧
      ∀ t, companionMatrixMap (p := p) (f := f) n
          (fun i ↦ PowerSeries.constantCoeff (b i)) (d (t + 1)) - d (t + 1) =
        fun i ↦ -∑ u ∈ Finset.range (t + 1),
          (b i).coeff (u + 1) * _root_.iterateFrobenius k p f (d (t - u) (Fin.last n)) := by
  let σk := _root_.iterateFrobenius k p f
  let Ψ := companionMatrixMap (p := p) (f := f) n fun i ↦ PowerSeries.constantCoeff (b i)
  have hΨ_ne : Ψ^[finrank k (Fin (n + 1) → k)] (Pi.single 0 1) ≠ 0 := by
    rw [Module.finrank_pi, Fintype.card_fin, companionMatrixMap_iterate_single_zero]
    exact fun h ↦ hb.choose_spec (congrFun h hb.choose)
  obtain ⟨d₀, hd₀_ne, hd₀_fix⟩ :=
    LinearMap.exists_ne_zero_isFixedPt_of_iterate_ne_zero_iterateFrobenius hf hΨ_ne
  have hsurj := LinearMap.surjective_sub_id_of_iterateFrobenius hf Ψ
  let res : (t : ℕ) → (∀ u < t, Fin (n + 1) → k) → (Fin (n + 1) → k)
    | 0, _ => 0
    | t + 1, prev => fun i ↦ ∑ u ∈ Finset.range (t + 1),
      (b i).coeff (u + 1) * σk (prev (t - u) (by omega) (Fin.last n))
  let step : (t : ℕ) → (∀ u < t, Fin (n + 1) → k) → (Fin (n + 1) → k)
    | 0, _ => d₀
    | t + 1, prev => Classical.choose (hsurj (-res (t + 1) prev))
  let d : ℕ → Fin (n + 1) → k := WellFounded.fix Nat.lt_wfRel.wf step
  have hd_zero : d 0 = d₀ := WellFounded.fix_eq Nat.lt_wfRel.wf step 0
  refine ⟨d, hd_zero ▸ hd₀_ne, hd_zero ▸ hd₀_fix.eq, fun t ↦ ?_⟩
  have hfix : d (t + 1) = step (t + 1) (fun u _ ↦ d u) :=
    WellFounded.fix_eq Nat.lt_wfRel.wf step (t + 1)
  rw [hfix]
  exact Classical.choose_spec (hsurj (-res (t + 1) fun u _ ↦ d u))

private theorem exists_powerSeries_companion_solution {k : Type*} [Field k] {p f : ℕ}
    [Fact p.Prime] [CharP k p] [IsAlgClosed k] (hf : f ≠ 0) (n : ℕ)
    (b : Fin (n + 1) → k⟦X⟧) (hb : ∃ i, PowerSeries.constantCoeff (b i) ≠ 0) :
    ∃ x : Fin (n + 1) → k⟦X⟧,
      (∃ i, x i ≠ 0) ∧
      x 0 = b 0 * PowerSeries.map (_root_.iterateFrobenius k p f) (x (Fin.last n)) ∧
      ∀ j : Fin n, x j.succ = PowerSeries.map (_root_.iterateFrobenius k p f) (x j.castSucc) +
        b j.succ * PowerSeries.map (_root_.iterateFrobenius k p f) (x (Fin.last n)) := by
  -- Assemble the recursively constructed `X^t` coefficients into power series `x i` and match
  -- degree-0 and degree-`(t + 1)` terms in the companion system.
  let σk := _root_.iterateFrobenius k p f
  obtain ⟨d, hd0_ne, hd0_fix, hd_succ⟩ := exists_companion_powerSeries_coeffs hf n b hb
  let x : Fin (n + 1) → k⟦X⟧ := fun i ↦ PowerSeries.mk fun t ↦ d t i
  have hmul_coeff (i : Fin (n + 1)) (t : ℕ) :
      (b i * PowerSeries.map σk (x (Fin.last n))).coeff (t + 1) =
        PowerSeries.constantCoeff (b i) * σk (d (t + 1) (Fin.last n)) +
          ∑ u ∈ Finset.range (t + 1), (b i).coeff (u + 1) * σk (d (t - u) (Fin.last n)) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun u v ↦ (b i).coeff u * (PowerSeries.map σk (x (Fin.last n))).coeff v),
      Finset.sum_range_succ']
    simp only [Nat.sub_zero, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_mk, x]
    rw [add_comm]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun u _ ↦ by rw [Nat.add_sub_add_right])
  have hdt (idx : Fin (n + 1)) (t : ℕ) : d (t + 1) idx =
      companionMatrixMap (p := p) (f := f) n (fun i ↦ PowerSeries.constantCoeff (b i))
        (d (t + 1)) idx +
      ∑ u ∈ Finset.range (t + 1), (b idx).coeff (u + 1) * σk (d (t - u) (Fin.last n)) := by
    have ht := congrFun (hd_succ t) idx
    simp only [Pi.sub_apply] at ht
    linear_combination -ht
  refine ⟨x, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hd0_ne
    exact ⟨i, fun hxi ↦ hi (by simpa [x] using congrArg (PowerSeries.coeff 0) hxi)⟩
  · ext (_ | t)
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk _),
        PowerSeries.coeff_map, PowerSeries.coeff_mk]
      have h0 := (congrFun hd0_fix 0).symm
      simpa [x, σk, _root_.iterateFrobenius_def] using h0
    · rw [PowerSeries.coeff_mk, hmul_coeff 0 t, hdt 0 t]
      simp [σk, _root_.iterateFrobenius_def]
  · intro j
    ext (_ | t)
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff, map_add, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk (x j.castSucc)),
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map σk (x (Fin.last n))),
        PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hs := (congrFun hd0_fix j.succ).symm
      simpa [x, σk, _root_.iterateFrobenius_def] using hs
    · rw [PowerSeries.coeff_mk, map_add, hmul_coeff j.succ t, hdt j.succ t]
      simp [σk, _root_.iterateFrobenius_def, x, add_assoc]

private theorem exists_min_slope_coeffs {k : Type*} [Field k] {n : ℕ}
    {a : Fin (n + 1) → LaurentSeries k} (ha0 : a 0 ≠ 0) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧
      ∃ b : Fin (n + 1) → k⟦X⟧,
        (∃ i, PowerSeries.constantCoeff (b i) ≠ 0) ∧
        ∀ i : Fin (n + 1), (b i : LaurentSeries k) =
          HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 *
            _root_.LaurentSeries.expand k r (-a i) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hS0 : (0 : Fin (n + 1)) ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ 0, ha0⟩
  obtain ⟨i₀, hi₀, s, r, hcop, hord_eq, hord_le⟩ :=
    Rat.exists_min_div_coprime ⟨0, hS0⟩ (fun i ↦ (a i).order)
      (fun i ↦ (n + 1 - i.val : ℤ)) (fun i _ ↦ by omega)
  have hi₀_ne : a i₀ ≠ 0 := (Finset.mem_filter.1 hi₀).2
  let B_ser : Fin (n + 1) → LaurentSeries k := fun i ↦
    HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 * _root_.LaurentSeries.expand k r (-a i)
  have hB_mem (i : Fin (n + 1)) : B_ser i ∈ Set.range (HahnSeries.ofPowerSeries ℤ k) := by
    rw [TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff]
    intro m hm
    by_cases hi : a i = 0
    · simp [B_ser, hi]
    · rw [HahnSeries.coeff_single_mul, one_mul]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [_root_.LaurentSeries.order_expand, HahnSeries.order_neg]
      linarith [hord_le i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)]
  choose b hb using hB_mem
  refine ⟨s, r, hcop, b, ⟨i₀, ?_⟩, fun i ↦ hb i⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h0 : (b i₀ : LaurentSeries k).coeff 0 = (B_ser i₀).coeff 0 :=
    congrArg (fun g : LaurentSeries k ↦ g.coeff 0) (hb i₀)
  rw [PowerSeries.coeff_coe, ite_eq_right (fun h ↦ absurd h (lt_irrefl _)),
    Int.natAbs_zero] at h0
  rw [h0]
  simp only [B_ser, HahnSeries.coeff_single_mul, one_mul, zero_sub, neg_mul, neg_neg]
  have hord_neg : (-a i₀).order = (a i₀).order := HahnSeries.order_neg
  rw [show s * ((n : ℤ) + 1 - i₀.val) = (r : ℤ) * (-a i₀).order by rw [hord_neg, hord_eq],
    _root_.LaurentSeries.coeff_expand_mul]
  exact HahnSeries.coeff_order_eq_zero.not.2 (neg_ne_zero.2 hi₀_ne)

private theorem exists_laurent_companion_solution {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k] {n : ℕ} (s : ℤ) (r : ℕ+)
    (a : Fin (n + 1) → LaurentSeries k) (b : Fin (n + 1) → k⟦X⟧)
    (hb0 : ∃ i, PowerSeries.constantCoeff (b i) ≠ 0)
    (hb : ∀ i : Fin (n + 1), (b i : LaurentSeries k) =
      HahnSeries.single (-s * (n + 1 - i.val : ℤ)) 1 * _root_.LaurentSeries.expand k r (-a i)) :
    ∃ z : Fin (n + 1) → LaurentSeries k,
      (∃ i, z i ≠ 0) ∧
      HahnSeries.single s 1 * z 0 =
        _root_.LaurentSeries.expand k r (-a 0) *
          LaurentSeries.coefficientFrobenius p f (z (Fin.last n)) ∧
      ∀ j : Fin n, HahnSeries.single s 1 * z j.succ =
        LaurentSeries.coefficientFrobenius p f (z j.castSucc) +
          _root_.LaurentSeries.expand k r (-a j.succ) *
            LaurentSeries.coefficientFrobenius p f (z (Fin.last n)) := by
  let σ := LaurentSeries.coefficientFrobenius (k := k) p f
  obtain ⟨x, ⟨i₁, hi₁⟩, hx0, hxs⟩ :=
    exists_powerSeries_companion_solution f.ne_zero n b hb0
  let z : Fin (n + 1) → LaurentSeries k :=
    fun i ↦ HahnSeries.single (-s * (i.val : ℤ)) 1 * (x i : LaurentSeries k)
  refine ⟨z, ⟨i₁, mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero)
    ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 hi₁)⟩, ?_, ?_⟩
  · have hx0' : (x 0 : LaurentSeries k) = (b 0 : LaurentSeries k) * σ (x (Fin.last n)) := by
      have h := congrArg (HahnSeries.ofPowerSeries ℤ k) hx0
      rwa [map_mul, HahnSeries.ofPowerSeries_apply,
        ← LaurentSeries.coefficientFrobenius_coe (p := p) (f : ℕ)] at h
    rw [hb 0] at hx0'
    have hx0'' := congrArg (HahnSeries.single s 1 * ·) hx0'
    simp only [z, σ, Fin.val_zero, Nat.cast_zero, mul_zero, HahnSeries.single_zero_one, one_mul,
      sub_zero, map_mul, LaurentSeries.coefficientFrobenius_single, one_pow] at hx0'' ⊢
    rw [hx0'']
    simp only [← mul_assoc, HahnSeries.single_mul_single, one_mul]
    rw [mul_comm (HahnSeries.single (s + -s * (n + 1 : ℤ)) 1), Fin.val_last, mul_assoc,
      show s + -s * (n + 1 : ℤ) = -s * (n : ℤ) by ring, ← mul_assoc]
  · intro j
    have hxs' : (x j.succ : LaurentSeries k) =
        σ (x j.castSucc) + (b j.succ : LaurentSeries k) * σ (x (Fin.last n)) := by
      have h := congrArg (HahnSeries.ofPowerSeries ℤ k) (hxs j)
      rwa [map_add, map_mul, HahnSeries.ofPowerSeries_apply,
        ← LaurentSeries.coefficientFrobenius_coe (p := p) (f : ℕ),
        ← LaurentSeries.coefficientFrobenius_coe (p := p) (f : ℕ)] at h
    rw [hb j.succ] at hxs'
    have hxs'' := congrArg (HahnSeries.single (-s * (j.val : ℤ)) 1 * ·) hxs'
    have hlhs : HahnSeries.single s 1 * z j.succ =
        HahnSeries.single (-s * (j.val : ℤ)) 1 * (x j.succ : LaurentSeries k) := by
      simp only [z, Fin.val_succ, Nat.cast_add, Nat.cast_one, ← mul_assoc,
        HahnSeries.single_mul_single, one_mul]
      rw [show s + -s * ((j.val : ℤ) + 1) = -s * (j.val : ℤ) by ring]
    rw [hlhs, hxs'', mul_add]
    congr 1
    · simp only [z, σ, Fin.val_castSucc, map_mul, LaurentSeries.coefficientFrobenius_single,
        one_pow]
    · simp only [σ, Fin.val_succ, Nat.cast_add, Nat.cast_one, map_mul,
        LaurentSeries.coefficientFrobenius_single, one_pow, z, Fin.val_last, ← mul_assoc,
        HahnSeries.single_mul_single, one_mul]
      rw [mul_comm (HahnSeries.single _ 1), mul_assoc,
        show -s * (j.val : ℤ) + -s * ((n : ℤ) + 1 - (↑j + 1)) = -s * (n : ℤ) by ring,
        ← mul_assoc]

private theorem cyclicShiftEquiv_laurent_companion {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    {Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V}
    {v₀ : V} {n : ℕ} {a : Fin (n + 1) → LaurentSeries k}
    (hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0)
    (s : ℤ) (r : ℕ+) (z : Fin (n + 1) → LaurentSeries k)
    (hz0 : HahnSeries.single s 1 * z 0 =
      _root_.LaurentSeries.expand k r (-a 0) *
        LaurentSeries.coefficientFrobenius p f (z (Fin.last n)))
    (hzs : ∀ j : Fin n, HahnSeries.single s 1 * z j.succ =
      LaurentSeries.coefficientFrobenius p f (z j.castSucc) +
        _root_.LaurentSeries.expand k r (-a j.succ) *
          LaurentSeries.coefficientFrobenius p f (z (Fin.last n))) :
    (fun l ↦ Φ (∑ i : Fin (n + 1), _root_.LaurentSeries.contract r (z i) l • Φ^[i.val] v₀)) =
      (LinearEquiv.cyclicShift (LaurentSeries k) V TauCeti.LaurentSeries.unitX r ^ s)
        (fun l ↦ ∑ i : Fin (n + 1), _root_.LaurentSeries.contract r (z i) l • Φ^[i.val] v₀) := by
  -- Expand both `l ↦ Φ (w l)` and `(S_V ^ s) w` in the orbit basis `Φ^[i] v₀`, rewriting
  -- `Φ^[n + 1] v₀` via `hrel` and matching coefficients using `hz0` and `hzs`.
  let L := LaurentSeries k
  let σ := LaurentSeries.coefficientFrobenius (k := k) p f
  have hcontract (g : L) (l : Fin r) :
      _root_.LaurentSeries.contract r (σ g) l = σ (_root_.LaurentSeries.contract r g l) := by
    ext m; simp [σ]
  set S_V := LinearEquiv.cyclicShift L V TauCeti.LaurentSeries.unitX r
  let smulVec : (Fin r → L) → V → (Fin r → V) := fun g v l ↦ g l • v
  let y : Fin (n + 1) → Fin r → L := fun i l ↦ _root_.LaurentSeries.contract r (z i) l
  let termLast : Fin (n + 1) → (Fin r → V) := fun j ↦ smulVec (_root_.LaurentSeries.contract r
    (_root_.LaurentSeries.expand k r (-a j) * σ (z (Fin.last n)))) (Φ^[j.val] v₀)
  let termS : Fin (n + 1) → (Fin r → V) := fun j ↦
    smulVec (_root_.LaurentSeries.contract r (HahnSeries.single s 1 * z j)) (Φ^[j.val] v₀)
  have hT_eq : (fun l ↦ Φ (∑ i : Fin (n + 1), y i l • Φ^[i.val] v₀)) = ∑ i : Fin (n + 1),
      smulVec (_root_.LaurentSeries.contract r (σ (z i))) (Φ^[i.val + 1] v₀) := by
    ext l
    simp only [smulVec, σ, map_sum, Finset.sum_apply, map_smulₛₗ, RingHom.coe_coe,
      ← iterate_succ_apply' Φ, Nat.succ_eq_add_one, y, hcontract]
  have hS_eq : (S_V ^ s) (fun l ↦ ∑ i : Fin (n + 1), y i l • Φ^[i.val] v₀) =
      ∑ j : Fin (n + 1), termS j := by
    have hw_vec : (fun l ↦ ∑ i : Fin (n + 1), y i l • Φ^[i.val] v₀) =
        ∑ i : Fin (n + 1), smulVec (y i) (Φ^[i.val] v₀) := by ext l; simp [smulVec]
    rw [hw_vec, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearEquiv.cyclicShift_zpow_smul TauCeti.LaurentSeries.unitX r s (y i) (Φ^[i.val] v₀)]
    exact congrArg (smulVec · (Φ^[i.val] v₀)) (_root_.LaurentSeries.cyclicShift_zpow_contract r s _)
  have hΦlast : Φ^[n + 1] v₀ = ∑ j : Fin (n + 1), (-a j) • Φ^[j.val] v₀ := by
    rw [eq_neg_of_add_eq_zero_left hrel, ← Finset.sum_neg_distrib]; simp [neg_smul]
  have hlast_split : smulVec (_root_.LaurentSeries.contract r (σ (z (Fin.last n))))
      (∑ j : Fin (n + 1), (-a j) • Φ^[j.val] v₀) = ∑ j : Fin (n + 1), termLast j := by
    ext l; simp only [smulVec, termLast, Finset.smul_sum, Finset.sum_apply, smul_smul,
      mul_comm (-a _), _root_.LaurentSeries.contract_expand_mul]
  have hterm0 : termLast 0 = termS 0 := by dsimp only [termLast, termS]; rw [Fin.val_zero, hz0]
  have hterm_succ (j : Fin n) :
      smulVec (_root_.LaurentSeries.contract r (σ (z j.castSucc))) (Φ^[j.val + 1] v₀) +
        termLast j.succ = termS j.succ := by
    ext l; simp only [smulVec, termLast, termS, σ, Pi.add_apply, ← add_smul, Fin.val_succ]
    rw [← _root_.LaurentSeries.contract_add, ← hzs j]
  rw [hT_eq, hS_eq, Fin.sum_univ_castSucc, Fin.val_last, hΦlast, hlast_split,
    Fin.sum_univ_succ, Fin.sum_univ_succ, add_left_comm, ← Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hterm0 (Finset.sum_congr rfl fun j _ ↦ hterm_succ j)

private theorem eigenvector_of_laurent_companion_solution {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    {Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V}
    {v₀ : V} {n : ℕ}
    (hli : LinearIndependent (LaurentSeries k) fun i : Fin (n + 1) ↦ Φ^[i.val] v₀)
    {a : Fin (n + 1) → LaurentSeries k}
    (hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0)
    (s : ℤ) (r : ℕ+) (z : Fin (n + 1) → LaurentSeries k) (hz_ne : ∃ i, z i ≠ 0)
    (hz0 : HahnSeries.single s 1 * z 0 =
      _root_.LaurentSeries.expand k r (-a 0) *
        LaurentSeries.coefficientFrobenius p f (z (Fin.last n)))
    (hzs : ∀ j : Fin n, HahnSeries.single s 1 * z j.succ =
      LaurentSeries.coefficientFrobenius p f (z j.castSucc) +
        _root_.LaurentSeries.expand k r (-a j.succ) *
          LaurentSeries.coefficientFrobenius p f (z (Fin.last n))) :
    ∃ w₀ : V, w₀ ≠ 0 ∧
      Φ^[r] w₀ = (HahnSeries.single 1 1 : LaurentSeries k) ^ s • w₀ := by
  let L := LaurentSeries k
  let y : Fin (n + 1) → Fin r → L := fun i l ↦ _root_.LaurentSeries.contract r (z i) l
  let w : Fin r → V := fun l ↦ ∑ i : Fin (n + 1), y i l • Φ^[i.val] v₀
  have hl₀ : ∃ l₀, w l₀ ≠ 0 := by
    obtain ⟨i₁, hi₁⟩ := hz_ne
    have hcontract : ∃ l₀, y i₁ l₀ ≠ 0 := by
      by_contra! hall
      apply hi₁
      rw [← _root_.LaurentSeries.sum_single_mul_expand_contract r (z i₁)]
      exact Finset.sum_eq_zero fun l _ ↦ by simp [y, hall l]
    obtain ⟨l₀, hl₀⟩ := hcontract
    exact ⟨l₀, fun hw0 ↦ hl₀ (Fintype.linearIndependent_iff.1 hli (fun i ↦ y i l₀) hw0 i₁)⟩
  obtain ⟨l₀, hl₀⟩ := hl₀
  let S_V := LinearEquiv.cyclicShift L V TauCeti.LaurentSeries.unitX r
  let T : (Fin r → V) → (Fin r → V) := fun u l ↦ Φ (u l)
  have hTw : T w = (S_V ^ s) w := cyclicShiftEquiv_laurent_companion hrel s r z hz0 hzs
  have hcomm : Function.Commute T ⇑(S_V ^ s) := fun u ↦
    LinearEquiv.map_comp_cyclicShift_zpow Φ TauCeti.LaurentSeries.unitX
      (by rw [TauCeti.LaurentSeries.val_unitX, RingHom.coe_coe,
        LaurentSeries.coefficientFrobenius_X p f]) r s u
  have hTiter : ∀ m : ℕ, T^[m] w = (S_V ^ s)^[m] w := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih => rw [iterate_succ_apply', ih, hcomm.iterate_right m w, hTw, ← iterate_succ_apply]
  have hT_coord (m : ℕ) (l : Fin r) : T^[m] w l = Φ^[m] (w l) := by
    induction m with
    | zero => simp
    | succ m ih => rw [iterate_succ_apply']; dsimp only [T]; rw [ih, ← iterate_succ_apply' Φ]
  refine ⟨w l₀, hl₀, ?_⟩
  have hr_eq := congrFun (hTiter r) l₀
  rw [hT_coord r l₀, ← pow_apply_eq_iterate (S_V ^ s) (r : ℕ), ← zpow_natCast, ← zpow_mul,
    mul_comm s (r : ℤ), LinearEquiv.cyclicShift_zpow_mul_rank, Pi.smul_apply,
    Units.val_zpow_eq_zpow_val, TauCeti.LaurentSeries.val_unitX] at hr_eq
  exact hr_eq

private theorem exists_eigenvector_of_minimal_relation {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    {Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V}
    {v₀ : V} {n : ℕ}
    (hli : LinearIndependent (LaurentSeries k) fun i : Fin (n + 1) ↦ Φ^[i.val] v₀)
    {a : Fin (n + 1) → LaurentSeries k}
    (hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0) (ha0 : a 0 ≠ 0) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧ ∃ w₀ : V, w₀ ≠ 0 ∧
      Φ^[r] w₀ = (HahnSeries.single 1 1 : LaurentSeries k) ^ s • w₀ := by
  obtain ⟨s, r, hcop, b, hb0, hb⟩ := exists_min_slope_coeffs ha0
  obtain ⟨z, hz_ne, hz0, hzs⟩ :=
    exists_laurent_companion_solution (p := p) (f := f) s r a b hb0 hb
  obtain ⟨w₀, hw₀, hΦw₀⟩ :=
    eigenvector_of_laurent_companion_solution hli hrel s r z hz_ne hz0 hzs
  exact ⟨s, r, hcop, w₀, hw₀, hΦw₀⟩

private theorem cyclicBlockHom_intertwines {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L} {s : ℤ} {r : ℕ+} {v₀ : V}
    (hv₀ : Φ^[r] v₀ = π ^ s • v₀) (x : Fin r → L) :
    Fintype.linearCombination L (fun j : Fin r ↦ Φ^[j.val] v₀)
        (standardBlockFrobenius σ π s r x) =
      Φ (Fintype.linearCombination L (fun j : Fin r ↦ Φ^[j.val] v₀) x) := by
  have hrec (j : Fin r) :
      Φ^[j.val + 1] v₀ =
        (if j.val + 1 = r then π ^ s else 1) • Φ^[(finRotate r j : ℕ)] v₀ := by
    rw [Fin.coe_finRotate_eq_ite]
    split_ifs with hj
    · simpa [hj] using hv₀
    · simp
  refine intertwines_standardBlockFrobenius_of_single _ (fun j ↦ ?_) x
  simp only [Fintype.linearCombination_apply_single, one_smul, ← iterate_succ_apply' Φ]
  exact hrec j

/-- **Existence of a simple standard-block sub-isocrystal.** Every nontrivial finite-dimensional
`σ`-semilinear system `(V, Φ)` over `k((π))` with `Φ` injective contains a coprime cyclic block
`D(s, r)` via a Frobenius-equivariant `k((π))`-linear embedding
(Kedlaya 2005, §4.5, 4.5.3–4.5.8). -/
theorem exists_injective_intertwines_standardBlock {p : ℕ} [Fact p.Prime] {f : ℕ+}
    {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V] [Nontrivial V]
    {Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V}
    (hΦ : Injective Φ) :
    ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧
      ∃ ι : (Fin r → LaurentSeries k) →ₗ[LaurentSeries k] V,
        Injective ι ∧
        ∀ x, ι (standardBlockFrobenius (LaurentSeries.coefficientFrobenius (k := k) p f)
          (HahnSeries.single 1 1) s r x) = Φ (ι x) := by
  have : RingHomSurjective (LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k) :=
    ⟨(LaurentSeries.coefficientFrobenius (k := k) p f).surjective⟩
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨n, a, hli, hrel, ha0⟩ := LinearMap.exists_minimal_orbit_relation hΦ hv₀
  obtain ⟨s, r, hcop, w₀, hw₀, hΦw₀⟩ :=
    exists_eigenvector_of_minimal_relation hli hrel ha0
  let ι := Fintype.linearCombination (LaurentSeries k) fun j : Fin r ↦ Φ^[j.val] w₀
  have hinter : ∀ x, ι (standardBlockFrobenius (LaurentSeries.coefficientFrobenius (k := k) p f)
      (HahnSeries.single 1 1) s r x) = Φ (ι x) :=
    fun x ↦ cyclicBlockHom_intertwines hΦw₀ x
  have hstab : ∀ x ∈ LinearMap.ker ι,
      standardBlockFrobenius (LaurentSeries.coefficientFrobenius (k := k) p f)
        (HahnSeries.single 1 1) s r x ∈ LinearMap.ker ι := fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢; rw [hinter x, hx, map_zero]
  have hker_ne_top : LinearMap.ker ι ≠ ⊤ := fun htop ↦ by
    have hmem : Pi.single 0 1 ∈ LinearMap.ker ι := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply_single, Fin.val_zero, iterate_zero,
      id_eq, one_smul] at hmem
    exact hw₀ hmem
  have hgen : ∀ x : LaurentSeries k, x ≠ 0 →
      ∃ n : ℤ, Valued.v x = Valued.v (HahnSeries.single (1 : ℤ) (1 : k)) ^ n := fun x hx ↦
    ⟨x.order, by
      rw [TauCeti.LaurentSeries.valuation_eq_exp_neg_order hx,
        _root_.LaurentSeries.valuation_single_zpow, ← WithZero.exp_zsmul]
      congr 1
      simp⟩
  have hker_bot : LinearMap.ker ι = ⊥ :=
    (eq_bot_or_eq_top_of_standardBlockFrobenius_stable
      (LaurentSeries.coefficientFrobenius (k := k) p f)
      (HahnSeries.single 1 1) (HahnSeries.single_ne_zero one_ne_zero)
      (LaurentSeries.coefficientFrobenius_X p f) Valued.v
      (LaurentSeries.valuation_coefficientFrobenius p f)
      LaurentSeries.valuation_single_one_ne_one hgen hcop hstab).resolve_right hker_ne_top
  exact ⟨s, r, hcop, ι, LinearMap.ker_eq_bot.1 hker_bot, hinter⟩

end SubBlock

end TauCeti
