/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.CoefficientField
import Mathlib.RingTheory.Localization.NormTrace
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.RingTheory.PowerSeries.Trunc
import TauCeti.RingTheory.Trace.Quotient

/-!
# The trace near an unramified place

Let `F' / k'` be a finite separable extension of the algebraic function field `F / k`, and let
`P'` be a place of `F'` over the place `P` of `F`. Classically, `Tr_{F'/F}` decomposes as the sum
`∑_{Q' ∣ P} Tr_{F'_{Q'}/F_P}` of the traces of the completions over `P` (Stichtenoth,
Section IV.2). This file proves two completion-free consequences, for functions `z` that are regular
at `P'` and vanish to order at least `e(Q' ∣ P) · m` at every other place `Q'` over `P`, so that
the local traces at those places are negligible to order `m`.

* **Local degree one.** If `e(P' ∣ P) = f(P' ∣ P) = 1`, the completions at `P'` and at `P`
  coincide and the trace is, near `P'`, the identity: `ord_{P'} (Tr_{F'/F} z - z) ≥ m`.
* **Unramified over a rational place.** If `P` is rational with uniformizer `t` and
  `e(P' ∣ P) = 1`, so that the completion at `P'` is `F'_{P'}((t))` with `F'_{P'}` separable over
  `k`, the trace acts on expansions coefficientwise:
  `Tr_{F'/F} z ≡ ∑_{i < m} Tr_{F'_{P'}/k} (aᵢ) tⁱ` to order `m`, where `∑ aᵢ tⁱ` is the expansion
  of `z` at `P'`. In residue form, `res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)` for
  every `v` regular at the other places over `P`.

These identify the local components of a cotrace of Weil differentials with those of the
differential it comes from, at places of arbitrary degree.

Both proofs work in the local model `𝒪'_P ⊇ 𝒪_P`, the integral closure of the valuation ring of
`P` in `F'`, which is finite and free over `𝒪_P`. Let `x` be a uniformizer of `P` and reduce
modulo `x ^ m`: the trace of `𝒪'_P ⧸ x ^ m` over `𝒪_P ⧸ x ^ m` is the reduction of the trace
(`TauCeti.Algebra.trace_quotient_map_mk`). By weak approximation some `w` is congruent to `1` at
`P'` and to `0` at the other places over `P`, to order `m`; multiplication by its class is a
projection onto the summand of `𝒪'_P ⧸ x ^ m` belonging to `P'`, through which `z` acts. When
`e = f = 1` that summand is free of rank one with basis the class of `w`, and the class of `z` is
`a • w` for an `a ∈ 𝒪_P` congruent to `z` at `P'`, so the trace of `z` is `a` modulo `x ^ m`
(`TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`). Over a rational place with `e = 1`,
the summand is free with basis functions whose expansions at `P'` are constant to order `m` and
run over a `k`-basis `βⱼ` of `F'_{P'}`; on it `z` acts by the matrix `∑ᵢ [aᵢ] xⁱ`, where `[aᵢ]`
is the matrix of multiplication by `aᵢ` in the basis `βⱼ`, whose trace is `∑ᵢ Tr (aᵢ) xⁱ`
(`TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`).

## Main results

* `TauCeti.Place.exists_sub_algebraMap_mem_filtration`: at a place with `e = f = 1`, every
  regular function of `F'` is congruent to a regular function of `F` to any prescribed order.
* `TauCeti.Place.algebraMap_trace_sub_mem_filtration`: at a place with `e = f = 1`, the trace is
  the identity to order `m` near `P'`.
* `TauCeti.Place.trace_sub_sum_mem_filtration`: at an unramified place over a rational place, the
  trace acts on expansions as the coefficientwise trace of `F'_{P'} / k`, to order `m`.
* `TauCeti.Place.residue_trace`: in that situation,
  `res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2 and Remark 4.3.7.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §2 and §4.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

namespace Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F) (P' : Place k' F')

/-- The image in `F'` of a uniformizer of the place below has order `e(P' ∣ P)` at `P'`. -/
private theorem ord_algebraMap_uniformizer {x : F} (hx : (P'.restrict k F).ord x = 1) :
    P'.ord (algebraMap F F' x) = ramificationIdx F P' := by
  rw [ord_algebraMap_restrict k F P', hx, mul_one]

/-- **Expansion at a place of local degree one**: if `e(P' ∣ P) = f(P' ∣ P) = 1`, every function
regular at `P'` is congruent to a function of `F` regular at `P`, to any prescribed order `n`. -/
theorem exists_sub_algebraMap_mem_filtration (he : ramificationIdx F P' = 1)
    (hf : relativeDegree k F P' = 1) (n : ℕ) {z : F'} (hz : z ∈ P'.integers) :
    ∃ a ∈ (P'.restrict k F).integers, z - algebraMap F F' a ∈ P'.filtration n := by
  set P := P'.restrict k F
  obtain ⟨x, hx⟩ := P.exists_isUniformizer
  have hxo : P.ord x = 1 := P.isUniformizer_iff_ord_eq_one.mp hx
  have hxi : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hx'0 : algebraMap F F' x ≠ 0 := (map_ne_zero _).mpr hx.ne_zero
  have hx'o : P'.ord (algebraMap F F' x) = 1 := by
    rw [ord_algebraMap_uniformizer k F P' hxo, he, Nat.cast_one]
  -- `f(P' ∣ P) = 1` makes the residue fields equal.
  have hsurj : Function.Surjective (algebraMap P.ResidueField P'.ResidueField) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (relativeDegree_def k F P' ▸ hf)).2
  induction n with
  | zero => exact ⟨0, zero_mem _, by simpa [mem_filtration_zero_iff] using hz⟩
  | succ n ih =>
    obtain ⟨a, ha, han⟩ := ih
    -- Divide the remainder by `x ^ n` and match its residue with a residue from below.
    have hpow : algebraMap F F' x ^ n ∈ P'.filtration n := by
      simpa [P'.ord_pow, hx'o] using P'.mem_filtration_ord (algebraMap F F' x ^ n)
    have hy : (z - algebraMap F F' a) / algebraMap F F' x ^ n ∈ P'.integers := by
      have hinv : (algebraMap F F' x ^ n)⁻¹ ∈ P'.filtration (-n) := by
        simpa [P'.ord_inv, P'.ord_pow, hx'o] using
          P'.mem_filtration_ord (algebraMap F F' x ^ n)⁻¹
      simpa [div_eq_mul_inv, mem_filtration_zero_iff] using P'.mul_mem_filtration han hinv
    obtain ⟨r, hr⟩ := hsurj (IsLocalRing.residue P'.integers ⟨_, hy⟩)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective r
    rw [IsLocalRing.ResidueField.algebraMap_residue, residue_eq_iff_sub_mem_filtration_one,
      coe_algebraMap_integers] at hr
    refine ⟨a + c * x ^ n, add_mem ha (mul_mem c.2 (pow_mem hxi n)), ?_⟩
    have hrem := P'.mul_mem_filtration hpow (neg_mem hr)
    rw [neg_sub, mul_sub, mul_div_cancel₀ _ (pow_ne_zero n hx'0)] at hrem
    rw [Nat.cast_succ]
    convert hrem using 1
    simp only [map_add, map_mul, map_pow]
    ring

/-- By weak approximation, some `w` is congruent to `y` at `P'` and to `0` at the other places over
`P`, to order `e(Q' ∣ P) · m` at each place `Q'` over `P`. -/
private theorem exists_sub_mem_filtration_and_forall_mem_filtration (y : F') (m : ℕ) :
    ∃ w : F', w - y ∈ P'.filtration (ramificationIdx F P' * m) ∧
      ∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
        w ∈ Q'.filtration (ramificationIdx F Q' * m) := by
  classical
  have := (finite_setOf_restrict_eq (k' := k') (F' := F') k F (P'.restrict k F)).to_subtype
  obtain ⟨w, hw⟩ := exists_forall_ord_sub_eq
    (P := fun Q' : {Q' : Place k' F' | Q'.restrict k F = P'.restrict k F} ↦ (Q' : Place k' F'))
    Subtype.val_injective (fun Q' ↦ if (Q' : Place k' F') = P' then y else 0)
    (fun Q' ↦ ramificationIdx F (Q' : Place k' F') * m)
  have hwfil (Q' : Place k' F') (hQ' : Q'.restrict k F = P'.restrict k F) :
      w - (if Q' = P' then y else 0) ∈ Q'.filtration (ramificationIdx F Q' * m) := by
    have := Q'.mem_filtration_ord (w - if Q' = P' then y else 0)
    rwa [hw ⟨Q', hQ'⟩] at this
  exact ⟨w, by simpa using hwfil P' rfl, fun Q' hQ' hne ↦ by simpa [hne] using hwfil Q' hQ'⟩

variable {k F} in
/-- An integral function vanishing to order `m` at a place lies in the `m`-th power of the ideal
generated by a uniformizer. -/
private theorem mem_span_pow_of_mem_filtration {P : Place k F} {x : P.integers}
    (hx : P.ord (x : F) = 1) {m : ℕ} {c : P.integers} (hc : (c : F) ∈ P.filtration m) :
    c ∈ Ideal.span {x ^ m} := by
  have hx0 : (x : F) ≠ 0 := by
    rintro h
    rw [h, ord_zero] at hx
    omega
  rw [Ideal.mem_span_singleton']
  have hcx : (c : F) * (x : F) ^ (-(m : ℤ)) ∈ P.integers := by
    have h2 : (x : F) ^ (-(m : ℤ)) ∈ P.filtration (-m) := by
      simpa [P.ord_zpow, hx] using P.mem_filtration_ord ((x : F) ^ (-(m : ℤ)))
    simpa using P.mul_mem_filtration hc h2
  refine ⟨⟨_, hcx⟩, Subtype.ext ?_⟩
  simp [zpow_neg, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx0)]

/-- A uniformizer of the place below has order `e(Q' ∣ P)` at every place `Q'` above it. -/
private theorem zpow_mem_filtration {P : Place k F} {x : F} (hx : P.ord x = 1)
    {Q' : Place k' F'} (hQ' : Q'.restrict k F = P) (j : ℤ) :
    algebraMap F F' x ^ j ∈ Q'.filtration (ramificationIdx F Q' * j) := by
  have := Q'.mem_filtration_ord (algebraMap F F' x ^ j)
  rwa [Q'.ord_zpow, ord_algebraMap_restrict k F Q', hQ', hx, mul_one, mul_comm] at this

variable [Algebra.IsIntegral k k']

/-- An element of the local model `𝒪'_P` vanishing to order `e(Q' ∣ P) · m` at every place `Q'` over
`P` lies in `x ^ m 𝒪'_P`, for a uniformizer `x` of `P`. -/
private theorem mem_map_span_pow_of_forall_mem_filtration (hF' : IsFunctionField k' F')
    {P : Place k F} {x : P.integers} (hx : P.ord (x : F) = 1) (m : ℕ)
    (s : integralClosure P.integers F')
    (hs : ∀ Q' : Place k' F', Q'.restrict k F = P →
      (s : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    s ∈ (Ideal.span {x ^ m}).map (algebraMap P.integers (integralClosure P.integers F')) := by
  have hx0 : algebraMap F F' x ≠ 0 := (map_ne_zero _).mpr fun h ↦ by
    rw [h, ord_zero] at hx
    omega
  have hs' : (s : F') * algebraMap F F' x ^ (-(m : ℤ)) ∈ integralClosure P.integers F' :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      have := Q'.mul_mem_filtration (hs Q' hQ') (zpow_mem_filtration k F hx hQ' (-m))
      rwa [mul_neg, add_neg_cancel, mem_filtration_zero_iff] at this
  have hs_eq : s = algebraMap P.integers (integralClosure P.integers F') (x ^ m) * ⟨_, hs'⟩ := by
    refine Subtype.ext ?_
    simp only [map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
      zpow_neg, zpow_natCast]
    rw [IsScalarTower.algebraMap_apply P.integers F F', mul_left_comm,
      ValuationSubring.algebraMap_apply, mul_inv_cancel₀ (pow_ne_zero m hx0), mul_one]
  rw [hs_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))

/-- Conversely, an element of `x ^ m 𝒪'_P` vanishes to order `e(Q' ∣ P) · m` at every place `Q'`
over `P`. -/
private theorem mem_filtration_of_mem_map_span_pow (hF' : IsFunctionField k' F')
    {P : Place k F} {x : P.integers} (hx : P.ord (x : F) = 1) {m : ℕ}
    {s : integralClosure P.integers F'}
    (hs : s ∈ (Ideal.span {x ^ m}).map (algebraMap P.integers (integralClosure P.integers F')))
    {Q' : Place k' F'} (hQ' : Q'.restrict k F = P) :
    (s : F') ∈ Q'.filtration (ramificationIdx F Q' * m) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hs
  obtain ⟨s', rfl⟩ := hs
  have := Q'.mul_mem_filtration (Q'.mem_filtration_zero_iff.mpr
    ((isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s'.2 Q' hQ'))
    (zpow_mem_filtration k F hx hQ' m)
  simpa [IsScalarTower.algebraMap_apply P.integers F F'] using this

variable [Algebra.IsSeparable F F']

/-- **The trace is the identity near a place of local degree one.** Let `P'` be a place of `F'`
over `P` with `e(P' ∣ P) = f(P' ∣ P) = 1`. If `z` is regular at `P'` and vanishes to order at
least `e(Q' ∣ P) · m` at every other place `Q'` of `F'` over `P`, then `Tr_{F'/F} z` is congruent
to `z` at `P'` to order `m`. -/
theorem algebraMap_trace_sub_mem_filtration (hF' : IsFunctionField k' F')
    (he : ramificationIdx F P' = 1) (hf : relativeDegree k F P' = 1) (m : ℕ) {z : F'}
    (hz : z ∈ P'.integers)
    (hzQ : ∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
      z ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    algebraMap F F' (Algebra.trace F F' z) - z ∈ P'.filtration m := by
  classical
  set P := P'.restrict k F with hPdef
  -- The local model `𝒪'_P`, finite and free over `𝒪_P`.
  let S := integralClosure P.integers F'
  have : Module.Free P.integers S := .of_basis (integralClosureFinBasis F' P)
  have := isLocalization_integralClosure F' P
  have hreg (s : S) (Q' : Place k' F') (hQ' : Q'.restrict k F = P) : (s : F') ∈ Q'.integers :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s.2 Q' hQ'
  have hint {s : F'} (hP' : s ∈ P'.integers) (hs : ∀ Q' : Place k' F', Q'.restrict k F = P →
      Q' ≠ P' → s ∈ Q'.filtration (ramificationIdx F Q' * m)) : s ∈ S :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      by_cases h : Q' = P'
      · exact h ▸ hP'
      · exact Q'.mem_filtration_zero_iff.mp (Q'.filtration_antitone (by positivity) (hs Q' hQ' h))
  let zS : S := ⟨z, hint hz hzQ⟩
  -- A uniformizer `x` of `P`; it is also one at `P'`.
  obtain ⟨x, hx⟩ := P.exists_isUniformizer
  have hxo : P.ord x = 1 := P.isUniformizer_iff_ord_eq_one.mp hx
  let xR : P.integers := ⟨x, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  -- `z` is congruent at `P'` to some `a ∈ 𝒪_P`; it remains to see that so is its trace.
  obtain ⟨a, ha, hza⟩ := exists_sub_algebraMap_mem_filtration k F P' he hf m hz
  suffices hkey : Algebra.trace P.integers S zS - ⟨a, ha⟩ ∈ Ideal.span {xR ^ m} by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hkey
    have htr : Algebra.trace F F' z = algebraMap P.integers F (Algebra.trace P.integers S zS) :=
      Algebra.trace_localization P.integers P.integers⁰ (Sₘ := F') zS
    have hr' : Algebra.trace F F' z - a = (r : F) * x ^ m := by
      rw [htr]
      exact (congrArg Subtype.val hr).symm
    have hrm : algebraMap F F' ((r : F) * x ^ m) ∈ P'.filtration m := by
      have := P'.mul_mem_filtration ((P'.mem_filtration_zero_iff).mpr
        ((mem_integers_restrict_iff k F P' _).mp r.2)) (zpow_mem_filtration k F hxo rfl m)
      simpa [he] using this
    rw [← sub_add_sub_cancel _ (algebraMap F F' a), ← map_sub, hr']
    exact add_mem hrm (by simpa using neg_mem hza)
  -- Work modulo `I = (x ^ m)`.
  set I : Ideal P.integers := Ideal.span {xR ^ m} with hI
  -- `w ≡ 1` at `P'` and `w ≡ 0` at the other places over `P`, to order `m`.
  obtain ⟨w, hw1, hw0⟩ := exists_sub_mem_filtration_and_forall_mem_filtration k F P' 1 m
  rw [he, Nat.cast_one, one_mul] at hw1
  have hwP : w ∈ P'.integers := by
    have := add_mem (P'.filtration_antitone (Nat.cast_nonneg m) hw1)
      (P'.mem_filtration_zero_iff.mpr P'.integers.one_mem)
    rwa [sub_add_cancel, mem_filtration_zero_iff] at this
  let wS : S := ⟨w, hint hwP hw0⟩
  -- A product of an element small at `P'` and one small at the other places lies in `I 𝒪'_P`.
  have hprod (u v : S) (hu : (u : F') ∈ P'.filtration m)
      (hv : ∀ Q' : Place k' F', Q'.restrict k F = P → Q' ≠ P' →
        (v : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
      u * v ∈ I.map (algebraMap P.integers S) := by
    refine mem_map_span_pow_of_forall_mem_filtration k F hF' hxo m _ fun Q' hQ' ↦ ?_
    by_cases h : Q' = P'
    · subst h
      simpa [he] using Q'.mul_mem_filtration hu (Q'.mem_filtration_zero_iff.mpr (hreg v Q' hQ'))
    · simpa using Q'.mul_mem_filtration (Q'.mem_filtration_zero_iff.mpr (hreg u Q' hQ'))
        (hv Q' hQ' h)
  -- Modulo `I 𝒪'_P`, an element `b` congruent at `P'` to `c ∈ 𝒪_P` acts on `w` as `c`.
  have hact (b : S) (c : P.integers) (hbc : (b : F') - algebraMap F F' c ∈ P'.filtration m) :
      b * wS - algebraMap P.integers S c * wS ∈ I.map (algebraMap P.integers S) := by
    rw [← sub_mul]
    exact hprod _ wS (by simpa [IsScalarTower.algebraMap_apply P.integers F F'] using hbc) hw0
  -- So the class of `w` is an idempotent of rank one, and its trace is `1` modulo `I`.
  have htrw : Algebra.trace P.integers S wS - 1 ∈ I := by
    refine Algebra.trace_sub_one_mem_of_mul_self_sub_mem ?_ (fun b ↦ ?_) (fun c hc ↦ ?_)
    · simpa using hact wS 1 (by simpa using hw1)
    · obtain ⟨c, hc, hbc⟩ := exists_sub_algebraMap_mem_filtration k F P' he hf m (hreg b P' rfl)
      exact ⟨⟨c, hc⟩, by simpa [mul_comm wS] using hact b ⟨c, hc⟩ hbc⟩
    · -- `c = c w - c (w - 1)` vanishes to order `m` at `P'`, hence at `P`, so `c ∈ I`.
      have h2 : algebraMap F F' c * (w - 1) ∈ P'.filtration m := by
        simpa using P'.mul_mem_filtration (P'.mem_filtration_zero_iff.mpr
          ((mem_integers_restrict_iff k F P' _).mp c.2)) hw1
      have hcw := mem_filtration_of_mem_map_span_pow k F hF' hxo hc (Q' := P') rfl
      rw [he, Nat.cast_one, one_mul] at hcw
      have hc' : algebraMap F F' c ∈ P'.filtration m := by
        convert sub_mem hcw h2 using 1
        simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, wS,
          IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply]
        ring
      refine mem_span_pow_of_mem_filtration hxo ?_
      rcases eq_or_ne (c : F) 0 with h | h
      · simp [h]
      rw [mem_filtration_iff_le_ord _ h]
      have := (P'.mem_filtration_iff_le_ord ((map_ne_zero _).mpr h)).mp hc'
      rwa [ord_algebraMap_restrict k F P', he, Nat.cast_one, one_mul] at this
  -- The class of `z` is `a` times the class of `w`, so its trace is `a` modulo `I`.
  have hzw : zS - algebraMap P.integers S ⟨a, ha⟩ * wS ∈ I.map (algebraMap P.integers S) := by
    have h1 : zS - zS * wS ∈ I.map (algebraMap P.integers S) := by
      rw [show zS - zS * wS = (1 - wS) * zS by ring]
      exact hprod _ _ (by simpa using neg_mem hw1) hzQ
    simpa using add_mem h1 (hact zS ⟨a, ha⟩ hza)
  have hlin : Algebra.trace P.integers S (zS - algebraMap P.integers S ⟨a, ha⟩ * wS) +
      ⟨a, ha⟩ * (Algebra.trace P.integers S wS - 1) =
        Algebra.trace P.integers S zS - ⟨a, ha⟩ := by
    rw [map_sub, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hlin]
  exact add_mem (Algebra.trace_mem_of_mem_map hzw) (I.mul_mem_left _ htrw)


/-! ### The trace at an unramified place over a rational place -/

section Expansion

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
variable [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (P' : Place k F') [Algebra.IsSeparable k P'.ResidueField]
variable {P : Place k F} (hPP' : P'.restrict k F = P) {t : F} (ht : P.ord t = 1)
  (ht' : P'.ord (algebraMap F F' t) = 1)

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

include hPP' ht ht' in
/-- **The trace commutes with expansions at an unramified place over a rational place.** Let `P`
be a rational place of `F` with uniformizer `t`, and let `P'` be a place of `F'` over `P` at which
`t` is still a uniformizer, that is `e(P' ∣ P) = 1`, with residue field `F'_{P'}` separable over
`k`. If `z` is regular at `P'` and vanishes to order at least `e(Q' ∣ P) · m` at every other place
`Q'` over `P`, then, to order `m` at `P`,

`Tr_{F'/F} z ≡ ∑_{i < m} Tr_{F'_{P'}/k} (aᵢ) tⁱ`,

where `∑ aᵢ tⁱ` is the expansion of `z` at `P'` with coefficients in `F'_{P'}`.

Classically, the completion of `F'` at `P'` is `F'_{P'}((t))`, whose trace over `k((t))` is the
coefficientwise trace, and the hypothesis on `z` makes the local traces at the other places over
`P` negligible to order `m`. -/
theorem trace_sub_sum_mem_filtration (hF' : IsFunctionField k F') (hP : P.degree = 1) (m : ℕ)
    (z : P'.integers) (hzQ : ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' →
      (z : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    Algebra.trace F F' z - ∑ i : Fin m, algebraMap k F (Algebra.trace k P'.ResidueField
      (PowerSeries.coeff i (P'.powerSeriesExpansionResidueField ht' z))) * t ^ (i : ℕ) ∈
        P.filtration m := by
  -- Outline: in the local model `S = 𝒪'_P`, modulo `I = (t ^ m)`, apply
  -- `Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem` with `w = W ≡ 1` at `P'`, the basis
  -- `b j` of lifts of a `k`-basis `β j` of `F'_{P'}` with constant expansions, and the matrix
  -- `a j l = ∑ᵢ [cᵢ]ⱼₗ tⁱ` of multiplication by the expansion coefficients `cᵢ` of `z`. Each of
  -- its five hypotheses is a membership in `I S`, checked at `P'` on truncated expansions
  -- (`hfilt`) and at the other places over `P` by smallness (`Small`).
  classical
  subst hPP'
  set P := P'.restrict k F with hPdef
  have he : ramificationIdx F P' = 1 := by
    have h := ord_algebraMap_restrict k F P' t
    rw [ht', ← hPdef, ht, mul_one] at h
    exact_mod_cast h.symm
  have : FiniteDimensional k P'.ResidueField := P'.finiteDimensional_residueField hF'
  -- The local model `𝒪'_P`, finite and free over `𝒪_P`.
  let S := integralClosure P.integers F'
  have : Module.Free P.integers S := .of_basis (integralClosureFinBasis F' P)
  have := isLocalization_integralClosure F' P
  have hreg (s : S) (Q' : Place k F') (hQ' : Q'.restrict k F = P) : (s : F') ∈ Q'.integers :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s.2 Q' hQ'
  -- Functions vanishing to order `e(Q' ∣ P) · m` at the places `Q' ≠ P'` over `P`.
  let Small (y : F') : Prop := ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' →
    y ∈ Q'.filtration (ramificationIdx F Q' * m)
  have hint {y : F'} (hy : y ∈ P'.integers) (hs : Small y) : y ∈ S :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      by_cases h : Q' = P'
      · exact h ▸ hy
      · exact Q'.mem_filtration_zero_iff.mp (Q'.filtration_antitone (by positivity) (hs Q' hQ' h))
  have hsmall_mul {y : F'} (hy : Small y) (s : S) : Small (y * s) := fun Q' hQ' h ↦ by
    simpa using Q'.mul_mem_filtration (hy Q' hQ' h)
      (Q'.mem_filtration_zero_iff.mpr (hreg s Q' hQ'))
  have hsmall_mul' (s : S) {y : F'} (hy : Small y) : Small (s * y) := by
    simpa only [mul_comm] using hsmall_mul hy s
  have hsmall_sub {y y' : F'} (hy : Small y) (hy' : Small y') : Small (y - y') :=
    fun Q' hQ' h ↦ sub_mem (hy Q' hQ' h) (hy' Q' hQ' h)
  have hsmall_sum {n : ℕ} {y : Fin n → F'} (hy : ∀ i, Small (y i)) : Small (∑ i, y i) :=
    fun Q' hQ' h ↦ sum_mem fun i _ ↦ hy i Q' hQ' h
  -- Work modulo `I = (t ^ m)`; membership in `I 𝒪'_P` is read off at the places over `P`.
  let xR : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  set I : Ideal P.integers := Ideal.span {xR ^ m} with hI
  have hIS (s : S) (h1 : (s : F') ∈ P'.filtration m) (h2 : Small s) :
      s ∈ I.map (algebraMap P.integers S) := by
    refine mem_map_span_pow_of_forall_mem_filtration k F hF' (x := xR) ht m s fun Q' hQ' ↦ ?_
    by_cases h : Q' = P'
    · subst h
      simpa [he] using h1
    · exact h2 Q' hQ' h
  -- Expansions at `P'`, as a ring homomorphism on `𝒪'_P`.
  set E := P'.powerSeriesExpansionResidueField ht'
  let ιS : S →+* P'.integers :=
    { toFun := fun s ↦ ⟨s, hreg s P' rfl⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  let Φ : S →+* PowerSeries P'.ResidueField := E.toRingHom.comp ιS
  have hΦ (s : S) : Φ s = E ⟨s, hreg s P' rfl⟩ := rfl
  have hfiltE (y : P'.integers) : (y : F') ∈ P'.filtration m ↔ PowerSeries.trunc m (E y) = 0 := by
    rw [PowerSeries.trunc_eq_zero_iff_le_order,
      mem_filtration_iff_le_order_powerSeriesExpansionResidueField]
  have hfilt (s : S) : (s : F') ∈ P'.filtration m ↔ PowerSeries.trunc m (Φ s) = 0 :=
    hfiltE ⟨s, hreg s P' rfl⟩
  have hΦk (c : k) : Φ (algebraMap P.integers S (algebraMap k P.integers c)) =
      PowerSeries.C (algebraMap k P'.ResidueField c) := by
    have h : (⟨_, hreg (algebraMap P.integers S (algebraMap k P.integers c)) P' rfl⟩ :
        P'.integers) = algebraMap k P'.integers c := Subtype.ext (by
      rw [coe_algebraMap_constants]
      simp [IsScalarTower.algebraMap_apply P.integers F F', coe_algebraMap_constants,
        ← IsScalarTower.algebraMap_apply k F F'])
    rw [hΦ, h, AlgHom.commutes, PowerSeries.algebraMap_apply]
  have hΦt : Φ (algebraMap P.integers S xR) = PowerSeries.X := by
    rw [hΦ, ← powerSeriesExpansionResidueField_uniformizer P' ht']
    congr 1
  -- Lifts with prescribed expansion to order `m`, small at the other places over `P`.
  have hlift (g : PowerSeries P'.ResidueField) :
      ∃ s : S, Small s ∧ PowerSeries.trunc m (Φ s) = PowerSeries.trunc m g := by
    obtain ⟨y, hy⟩ := P'.exists_trunc_powerSeriesExpansionResidueField_eq ht' g m
    obtain ⟨w, hw, hwQ⟩ := exists_sub_mem_filtration_and_forall_mem_filtration k F P' (y : F') m
    rw [he, Nat.cast_one, one_mul] at hw
    have hwint : w ∈ P'.integers := by
      have := add_mem (P'.filtration_antitone (Nat.cast_nonneg m) hw)
        (P'.mem_filtration_zero_iff.mpr y.2)
      rwa [sub_add_cancel, mem_filtration_zero_iff] at this
    refine ⟨⟨w, hint hwint hwQ⟩, hwQ, ?_⟩
    have hdiff := (hfiltE (⟨w, hwint⟩ - y)).mp (by simpa using hw)
    rw [map_sub, map_sub, sub_eq_zero] at hdiff
    rw [hΦ, ← hy]
    exact hdiff
  -- A basis of `F'_{P'}` over `k`, lifted to functions with constant expansions to order `m`.
  let β := Module.finBasis k P'.ResidueField
  choose b hbS hbt using fun j ↦ hlift (PowerSeries.C (β j))
  obtain ⟨W, hWS, hWt⟩ := hlift 1
  have hW1 : (W : F') - 1 ∈ P'.filtration m := by
    have := (hfilt (W - 1)).mpr (by rw [map_sub Φ, map_one, map_sub, hWt, sub_self])
    simpa using this
  have hWmul (y : F') (hy : y ∈ P'.integers) : (W : F') * y - y ∈ P'.filtration m := by
    simpa [sub_mul] using P'.mul_mem_filtration hW1 (P'.mem_filtration_zero_iff.mpr hy)
  -- The truncated expansion of `∑ⱼ (∑ᵢ cᵢⱼ tⁱ) bⱼ` is `∑ᵢ (∑ⱼ cᵢⱼ βⱼ) Xⁱ`.
  have htrunc_sum (c : Fin (Module.finrank k P'.ResidueField) → Fin m → k) :
      PowerSeries.trunc m (Φ (∑ j, algebraMap P.integers S
        (∑ i : Fin m, algebraMap k P.integers (c j i) * xR ^ (i : ℕ)) * b j)) =
      PowerSeries.trunc m (∑ i : Fin m, PowerSeries.C (∑ j, c j i • β j) *
        PowerSeries.X ^ (i : ℕ)) := by
    have hj (j) : PowerSeries.trunc m (Φ (algebraMap P.integers S
        (∑ i : Fin m, algebraMap k P.integers (c j i) * xR ^ (i : ℕ)) * b j)) =
        PowerSeries.trunc m ((∑ i : Fin m, PowerSeries.C (algebraMap k P'.ResidueField (c j i)) *
          PowerSeries.X ^ (i : ℕ)) * PowerSeries.C (β j)) := by
      rw [map_mul, ← PowerSeries.trunc_mul_trunc, hbt j, PowerSeries.trunc_mul_trunc]
      simp only [map_sum, map_mul, map_pow, hΦk, hΦt]
    rw [map_sum, map_sum, Finset.sum_congr rfl fun j _ ↦ hj j, ← map_sum]
    congr 1
    ext n
    rw [PowerSeries.coeff_sum_C_mul_X_pow, map_sum]
    simp_rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_sum_C_mul_X_pow]
    split_ifs with hn
    · simp [Algebra.smul_def]
    · simp
  have htrunc_self (φ : PowerSeries P'.ResidueField) : PowerSeries.trunc m φ =
      PowerSeries.trunc m (∑ i : Fin m, PowerSeries.C (PowerSeries.coeff i φ) *
        PowerSeries.X ^ (i : ℕ)) := by
    ext n
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow]
    split_ifs <;> rfl
  have hcoe (r : P.integers) : algebraMap P.integers F' r = algebraMap F F' r := by
    rw [IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply]
  have hsmallR (r : P.integers) {y : F'} (hy : Small y) : Small (algebraMap P.integers F' r * y) :=
    by simpa using hsmall_mul' (algebraMap P.integers S r) hy
  have hmapfilt {r : F} (hr : r ∈ P.filtration m) : algebraMap F F' r ∈ P'.filtration m := by
    rcases eq_or_ne r 0 with rfl | h0
    · simp
    rw [mem_filtration_iff_le_ord _ h0] at hr
    rw [mem_filtration_iff_le_ord _ ((map_ne_zero _).mpr h0), ord_algebraMap_restrict k F P', he]
    simpa using hr
  -- The data of `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`.
  let zS : S := ⟨z, hint z.2 hzQ⟩
  have hΦz : Φ zS = E z := rfl
  set c : Fin m → P'.ResidueField := fun i ↦ PowerSeries.coeff i (E z) with hc
  let M : Fin m → Fin (Module.finrank k P'.ResidueField) →
    Fin (Module.finrank k P'.ResidueField) → k := fun i j l ↦ β.repr (c i * β j) l
  let a : Fin (Module.finrank k P'.ResidueField) → Fin (Module.finrank k P'.ResidueField) →
    P.integers := fun j l ↦ ∑ i : Fin m, algebraMap k P.integers (M i j l) * xR ^ (i : ℕ)
  have hwb (j) : W * b j - b j ∈ I.map (algebraMap P.integers S) :=
    hIS _ (by push_cast; exact hWmul _ (hreg (b j) P' rfl))
      (by push_cast; exact hsmall_sub (hsmall_mul' W (hbS j)) (hbS j))
  have hspan (s : S) : ∃ cs : Fin (Module.finrank k P'.ResidueField) → P.integers,
      W * s - ∑ j, algebraMap P.integers S (cs j) * b j ∈ I.map (algebraMap P.integers S) := by
    let cs : Fin (Module.finrank k P'.ResidueField) → P.integers := fun j ↦
      ∑ i : Fin m, algebraMap k P.integers (β.repr (PowerSeries.coeff i (Φ s)) j) * xR ^ (i : ℕ)
    refine ⟨cs, hIS _ ?_ ?_⟩
    · have h2 := (hfilt (s - ∑ j, algebraMap P.integers S (cs j) * b j)).mpr (by
        rw [map_sub, map_sub, htrunc_sum, htrunc_self (Φ s), sub_eq_zero]
        simp only [β.sum_repr])
      have h1 := hWmul _ (hreg s P' rfl)
      convert add_mem h1 h2 using 1
      push_cast
      ring
    · push_cast
      exact hsmall_sub (hsmall_mul hWS s) (hsmall_sum fun j ↦ hsmallR _ (hbS j))
  have hindep (cs : Fin (Module.finrank k P'.ResidueField) → P.integers)
      (hcs : ∑ j, algebraMap P.integers S (cs j) * b j ∈ I.map (algebraMap P.integers S))
      (j) : cs j ∈ I := by
    have h := mem_filtration_of_mem_map_span_pow k F hF' (x := xR) ht hcs (Q' := P') rfl
    rw [he, Nat.cast_one, one_mul] at h
    -- Replace each `cs j` by its truncated expansion at `P`.
    let τ := fun j ↦ P.truncatedExpansion hP ht m (cs j)
    let r := fun j ↦ ∑ i : Fin m, algebraMap k P.integers (τ j i) * xR ^ (i : ℕ)
    have hτ (j) : ((cs j - r j : P.integers) : F) ∈ P.filtration m := by
      simpa [r, xR, coe_algebraMap_constants] using
        P.sub_sum_truncatedExpansion_mem_filtration hP ht m (cs j)
    have hr : ((∑ j, algebraMap P.integers S (r j) * b j : S) : F') ∈ P'.filtration m := by
      have hd : ((∑ j, algebraMap P.integers S (cs j - r j) * b j : S) : F') ∈
          P'.filtration m := by
        push_cast
        refine sum_mem fun j _ ↦ ?_
        simpa [hcoe] using P'.mul_mem_filtration (hmapfilt (hτ j))
          (P'.mem_filtration_zero_iff.mpr (hreg (b j) P' rfl))
      convert sub_mem h hd using 1
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      push_cast
      ring
    have hzero := (hfilt _).mp hr
    rw [htrunc_sum] at hzero
    have hτ0 (i : Fin m) (j) : τ j i = 0 := by
      have hi := congrArg (Polynomial.coeff · (i : ℕ)) hzero
      simp only [PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow, i.2, ↓reduceIte,
        ↓reduceDIte, Polynomial.coeff_zero] at hi
      exact Fintype.linearIndependent_iff.mp β.linearIndependent (fun j ↦ τ j i) hi j
    have hcs : ((cs j : P.integers) : F) ∈ P.filtration m := by
      simpa [r, hτ0] using hτ j
    exact mem_span_pow_of_mem_filtration ht hcs
  have hz : zS * W - zS ∈ I.map (algebraMap P.integers S) :=
    hIS _ (by push_cast; rw [mul_comm]; exact hWmul _ z.2)
      (by push_cast; exact hsmall_sub (hsmall_mul hzQ W) hzQ)
  have hzb (j) : zS * b j - ∑ l, algebraMap P.integers S (a j l) * b l ∈
      I.map (algebraMap P.integers S) := by
    refine hIS _ ((hfilt _).mpr ?_) ?_
    · rw [map_sub, map_sub, htrunc_sum (fun l i ↦ M i j l), map_mul, ← PowerSeries.trunc_mul_trunc,
        hbt j, PowerSeries.trunc_mul_trunc, hΦz, sub_eq_zero]
      ext n
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow,
        PowerSeries.coeff_mul_C]
      split_ifs with hn
      · simp only [M, β.sum_repr, hc]
      · rfl
    · push_cast
      exact hsmall_sub (hsmall_mul hzQ (b j)) (hsmall_sum fun l ↦ hsmallR _ (hbS l))
  have key := Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem hwb hspan hindep hz hzb
  -- The diagonal of `a` is the trace of the coefficients.
  have hdiag : ∑ j, a j j = ∑ i : Fin m,
      algebraMap k P.integers (Algebra.trace k P'.ResidueField (c i)) * xR ^ (i : ℕ) := by
    simp only [a, M]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, Algebra.trace_eq_matrix_trace β, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [hdiag] at key
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp key
  have htr : Algebra.trace F F' z = algebraMap P.integers F (Algebra.trace P.integers S zS) :=
    Algebra.trace_localization P.integers P.integers⁰ (Sₘ := F') zS
  have hq' := congrArg (fun u : P.integers ↦ (u : F)) hq
  push_cast at hq'
  have htm : t ^ m ∈ P.filtration m := by
    have := P.mem_filtration_ord (t ^ m)
    rwa [P.ord_pow, ht, mul_one] at this
  have heq : ((Algebra.trace P.integers S zS : P.integers) : F) - ∑ i : Fin m, algebraMap k F
      (Algebra.trace k P'.ResidueField (PowerSeries.coeff i (E z))) * t ^ (i : ℕ) =
      (q : F) * t ^ m := by
    rw [hq']
  rw [htr, ValuationSubring.algebraMap_apply, heq]
  simpa using P.mul_mem_filtration (P.mem_filtration_zero_iff.mpr q.2) htm

include hPP' ht ht' in
/-- **Residues commute with the trace at an unramified place over a rational place.** Let `P` be
a rational place of `F` with uniformizer `t`, and let `P'` be a place of `F'` over `P` at which `t`
is still a uniformizer, with residue field `F'_{P'}` separable over `k`. For a function `v` regular
at every other place of `F'` over `P`,

`res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)`.

This is the residue form of `TauCeti.Place.trace_sub_sum_mem_filtration`. -/
theorem residue_trace (hF' : IsFunctionField k F') (hP : P.degree = 1) {v : F'}
    (hv : ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' → v ∈ Q'.integers) :
    P.residue hP ht (Algebra.trace F F' v) = P'.traceResidue ht' v := by
  set n := (-P'.ord v).toNat
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  -- `t ^ (n + 1) v` is regular at `P'` and vanishes to order `e(Q' ∣ P) (n + 1)` at the others.
  have hz : algebraMap F F' t ^ (n + 1) * v ∈ P'.integers := by
    have h1 : algebraMap F F' t ^ (n + 1) ∈ P'.filtration (-P'.ord v) :=
      P'.filtration_antitone (by rw [P'.ord_pow, ht']; omega) (P'.mem_filtration_ord _)
    rw [← mem_filtration_zero_iff]
    simpa using P'.mul_mem_filtration h1 (P'.mem_filtration_ord v)
  have hzQ (Q' : Place k F') (hQ' : Q'.restrict k F = P) (hne : Q' ≠ P') :
      algebraMap F F' t ^ (n + 1) * v ∈ Q'.filtration (ramificationIdx F Q' * (n + 1 : ℕ)) := by
    have h := zpow_mem_filtration k F ht hQ' ((n + 1 : ℕ) : ℤ)
    rw [zpow_natCast] at h
    simpa using Q'.mul_mem_filtration h (Q'.mem_filtration_zero_iff.mpr (hv Q' hQ' hne))
  have hT := trace_sub_sum_mem_filtration P' hPP' ht ht' hF' hP (n + 1) ⟨_, hz⟩ hzQ
  have htr : Algebra.trace F F' (algebraMap F F' t ^ (n + 1) * v) =
      t ^ (n + 1) * Algebra.trace F F' v := by
    rw [← map_pow, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [htr] at hT
  -- The truncated expansion of `t ^ (n + 1) Tr v` at `P` is the trace of that of `t ^ (n + 1) v`.
  have hint : t ^ (n + 1) * Algebra.trace F F' v ∈ P.integers := by
    have hsum : ∑ i : Fin (n + 1), algebraMap k F (Algebra.trace k P'.ResidueField
        (PowerSeries.coeff i (P'.powerSeriesExpansionResidueField ht' ⟨_, hz⟩))) *
          t ^ (i : ℕ) ∈ P.integers :=
      sum_mem fun i _ ↦ mul_mem (by rw [← coe_algebraMap_constants]; exact SetLike.coe_mem _)
        (pow_mem (P.mem_integers_iff_ord_nonneg.mpr (by omega)) _)
    have := add_mem (P.mem_filtration_zero_iff.mp (P.filtration_antitone (by omega) hT)) hsum
    rwa [sub_add_cancel] at this
  rw [P.residue_eq_coeff_powerSeriesExpansion hP ht n hint,
    P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩,
    (P.truncatedExpansion_eq_iff hP ht (n + 1) ⟨_, hint⟩ _).mpr hT, traceResidue_apply,
    P'.residueResidueField_eq_coeff_powerSeriesExpansionResidueField ht' n hz]

end Expansion

end Place

end TauCeti
