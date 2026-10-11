/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
import Mathlib.RingTheory.Localization.NormTrace
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.RingTheory.Trace.Quotient

/-!
# The trace at a place of local degree one

Let `F' / k'` be a finite separable extension of the algebraic function field `F / k`, and let
`P'` be a place of `F'` over the place `P` of `F` with `e(P' ∣ P) = f(P' ∣ P) = 1`, so that,
classically, the completions of `F'` at `P'` and of `F` at `P` coincide. Then the trace
`Tr_{F'/F}` is, near `P'`, the identity: if `z` is regular at `P'` and vanishes to order at least
`e(Q' ∣ P) · m` at every other place `Q'` over `P`, then

`ord_{P'} (Tr_{F'/F} z - z) ≥ m`.

This is the completion-free form of the decomposition `Tr_{F'/F} = ∑_{Q' ∣ P} Tr_{F'_{Q'}/F_P}`
of the trace into local traces (Stichtenoth, Section IV.2): the local trace at `P'` is the identity,
and the hypothesis on `z` kills the local traces at the other places over `P` to order `m`. It is
what identifies the local components of a cotrace with those of the differential it comes from.

The proof works in the local model `𝒪'_P ⊇ 𝒪_P`, the integral closure of the valuation ring of `P`
in `F'`, which is finite and free over `𝒪_P`. Let `x` be a uniformizer of `P` and reduce modulo
`x ^ m`: the trace of `𝒪'_P ⧸ x ^ m` over `𝒪_P ⧸ x ^ m` is the reduction of the trace
(`TauCeti.Algebra.trace_quotient_map_mk`). By weak approximation some `w` is congruent to `1` at
`P'` and to `0` at the other places over `P`, to order `m`; its class is an idempotent, and the
class of `z` is `a • w` for an `a ∈ 𝒪_P` congruent to `z` at `P'`, which exists because
`e = f = 1`. Multiplication by the class of `w` is a projection onto a free module of rank one, so
over the local ring `𝒪_P ⧸ x ^ m` its trace is `1`
(`TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`), and the trace of `z` is `a` modulo
`x ^ m`.

## Main results

* `TauCeti.Place.exists_sub_algebraMap_mem_filtration`: at a place with `e = f = 1`, every
  regular function of `F'` is congruent to a regular function of `F` to any prescribed order.
* `TauCeti.Place.algebraMap_trace_sub_mem_filtration`: the trace is the identity to order `m`
  near `P'`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
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

/-- By weak approximation, some `w` is congruent to `1` at `P'` and to `0` at the other places over
`P`, to order `e(Q' ∣ P) · m` at each place `Q'` over `P`. -/
private theorem exists_sub_one_mem_filtration_and_forall_mem_filtration (m : ℕ) :
    ∃ w : F', w - 1 ∈ P'.filtration (ramificationIdx F P' * m) ∧
      ∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
        w ∈ Q'.filtration (ramificationIdx F Q' * m) := by
  classical
  have := (finite_setOf_restrict_eq (k' := k') (F' := F') k F (P'.restrict k F)).to_subtype
  obtain ⟨w, hw⟩ := exists_forall_ord_sub_eq
    (P := fun Q' : {Q' : Place k' F' | Q'.restrict k F = P'.restrict k F} ↦ (Q' : Place k' F'))
    Subtype.val_injective (fun Q' ↦ if (Q' : Place k' F') = P' then 1 else 0)
    (fun Q' ↦ ramificationIdx F (Q' : Place k' F') * m)
  have hwfil (Q' : Place k' F') (hQ' : Q'.restrict k F = P'.restrict k F) :
      w - (if Q' = P' then 1 else 0) ∈ Q'.filtration (ramificationIdx F Q' * m) := by
    have := Q'.mem_filtration_ord (w - if Q' = P' then 1 else 0)
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
  -- For `m = 0` the ideal is the unit ideal.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  -- Work modulo `I = (x ^ m)`; the quotient `𝒪_P ⧸ I` is local.
  set I : Ideal P.integers := Ideal.span {xR ^ m} with hI
  have hItop : I ≠ ⊤ := by
    rw [Ne, hI, Ideal.span_singleton_eq_top, isUnit_pow_iff (by omega),
      P.isUnit_iff_ord_eq_zero hx.ne_zero]
    simp [xR, hxo]
  have : Nontrivial (P.integers ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (P.integers ⧸ I) :=
    .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- `w ≡ 1` at `P'` and `w ≡ 0` at the other places over `P`, to order `m`.
  obtain ⟨w, hw1, hw0⟩ := exists_sub_one_mem_filtration_and_forall_mem_filtration k F P' m
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

end Place

end TauCeti
