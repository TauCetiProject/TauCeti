/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.RingTheory.AlgebraicIndependent.Automorphism
import TauCeti.RingTheory.Valuation.FrobeniusElement

/-!
# Frobenius-type automorphisms of discretely valued field extensions

Let `K → L` be a compatible extension of valued fields (`ValuativeExtension K L`) and let
`σ : L ≃ₐ[K] L` be a `K`-algebra automorphism satisfying a Frobenius congruence
`v_L(σ(z) − z^q) < 1` on the valuation ring `𝒪[L]` for some `q > 0`.

By `Valuation.exists_le_one_and_residue_eq_pow` and `Valuation.one_lt_map_of_one_lt`, any such `σ`
automatically preserves `𝒪[L]` in both directions, restricts to an `𝒪[K]`-algebra automorphism of
`𝒪[L]`, and induces the `q`-th power map on the residue field `𝓀[L]`. When `K` and `L` are
discretely valued and the value-group map `mapValueGroupWithZero K L` is surjective, uniformizer
expansions yield three structural consequences:

* **Fixed field (`eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one`):** if `𝓀[K]` is
  finite of cardinality `q`, `𝒪[K]` is `𝓂[K]`-adically precomplete, and `𝒪[L]` is `𝓂[L]`-adically
  Hausdorff, then `{x : L | σ x = x} = Set.range (algebraMap K L)`.
* **Existence of transcendental elements (`exists_transcendental_of_valuation_sub_pow_lt_one`):**
  if `q > 1`, `𝒪[L]` is `𝓂[L]`-adically precomplete, and `𝓀[L]` is infinite, diagonalizing the
  powers `σ^m` on `𝒪[L]` produces an element of `L` with infinite `σ`-orbit, hence transcendental
  over `K` in every characteristic.
* **Frobenius eigenvector equation (`exists_apply_eq_mul_of_sub_one_mem_maximalIdeal`):** if
  `q > 1`, `𝒪[L]` is `𝓂[L]`-adically complete, and `𝓀[L]` is algebraically closed, then for every
  principal unit `u ∈ 1 + 𝓂[K]` there exists `y ∈ L \ {0}` with `σ(y) = u y` via Artin–Schreier-type
  Henselian approximation along powers of a uniformizer.

## Main definitions

* `ValuativeExtension.integerAlgEquivOfMemInteger`: restriction of `σ : L ≃ₐ[K] L` to
  `𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]` when `σ` preserves `𝒪[L]`.

## Main results

* `ValuativeExtension.mem_integer_iff_of_valuation_sub_pow_lt_one`: a ring endomorphism
  satisfying `v(σ z − z^q) < 1` on `𝒪[L]` (`q ≠ 0`) preserves and reflects membership in `𝒪[L]`.
* `ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one`:
  the fixed field of a `#𝓀[K]`-Frobenius automorphism is the image of `K`.
* `ValuativeExtension.exists_transcendental_of_valuation_sub_pow_lt_one`: existence of
  elements of `L` transcendental over `K`.
* `ValuativeExtension.exists_apply_eq_mul_of_sub_one_mem_maximalIdeal`: solvability of
  `σ(y) = u y` for principal units `u ∈ 1 + 𝓂[K]`.

## References

* M. Chen, *Composantes connexes géométriques d'espaces de modules de groupes `p`-divisibles*,
  Ann. Sci. Éc. Norm. Supér. (4) 47 (2014), 723–764, Proposition 2.0.3.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
-/

public section
noncomputable section

open scoped Polynomial
open ValuativeRel TauCeti

namespace ValuativeExtension

section IntegerAlgEquiv

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- A ring endomorphism of `L` satisfying `v(τ z − z^q) < 1` on `𝒪[L]` for `q ≠ 0` preserves and
reflects membership in `𝒪[L]`. -/
theorem mem_integer_iff_of_valuation_sub_pow_lt_one {R : Type*} [FunLike R L L]
    [RingHomClass R L L] {τ : R} {q : ℕ} (hq : q ≠ 0)
    (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (τ z - z ^ q) < 1) (z : L) :
    τ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  refine ⟨fun hτz ↦ ?_, fun hz ↦ (Valuation.exists_le_one_and_residue_eq_pow (valuation L)
    hcongr hz).1⟩
  exact le_of_not_gt fun hz ↦
    not_lt_of_ge hτz (Valuation.one_lt_map_of_one_lt (valuation L) hq hcongr hz)

/-- Restriction of a `K`-algebra automorphism `σ : L ≃ₐ[K] L` preserving `𝒪[L]` in both directions
to an `𝒪[K]`-algebra automorphism of `𝒪[L]`. -/
def integerAlgEquivOfMemInteger (σ : L ≃ₐ[K] L) (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) :
    𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] where
  toFun x := ⟨σ x.1, (hσ x.1).2 x.2⟩
  invFun x := ⟨σ.symm x.1, (hσ (σ.symm x.1)).1 (by rw [σ.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)
  commutes' r := Subtype.ext (by
    simp only [coe_algebraMap_integerRing]
    exact σ.commutes (r : K))

@[simp]
theorem coe_integerAlgEquivOfMemInteger_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) (x : 𝒪[L]) :
    (integerAlgEquivOfMemInteger σ hσ x : L) = σ (x : L) :=
  (rfl)

@[simp]
theorem coe_integerAlgEquivOfMemInteger_symm_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) (x : 𝒪[L]) :
    ((integerAlgEquivOfMemInteger σ hσ).symm x : L) = σ.symm (x : L) :=
  (rfl)

theorem coe_integerAlgEquivOfMemInteger_pow_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) (n : ℕ) (x : 𝒪[L]) :
    ((integerAlgEquivOfMemInteger σ hσ ^ n) x : L) = (σ ^ n) (x : L) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      coe_integerAlgEquivOfMemInteger_apply, ih]

/-- On `𝒪[L]`, `integerAlgEquivOfMemInteger σ hσ x - x ^ q` belongs to the maximal ideal `𝓂[L]`. -/
theorem integerAlgEquivOfMemInteger_sub_pow_mem_maximalIdeal (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) {q : ℕ}
    (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1) (x : 𝒪[L]) :
    integerAlgEquivOfMemInteger σ hσ x - x ^ q ∈ 𝓂[L] :=
  (valuation L).mem_maximalIdeal_iff.2 (hcongr x.1 x.2)

/-- Reduction modulo `𝓂[L]` intertwines `integerAlgEquivOfMemInteger σ hσ` with the `q`-th power map
on `𝓀[L]`. -/
theorem residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) {q : ℕ}
    (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L] (integerAlgEquivOfMemInteger σ hσ x) =
      IsLocalRing.residue 𝒪[L] x ^ q := by
  let φ := IsLocalRing.residue 𝒪[L]
  have hmem := integerAlgEquivOfMemInteger_sub_pow_mem_maximalIdeal σ hσ hcongr x
  have h0 : φ (integerAlgEquivOfMemInteger σ hσ x - x ^ q) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hmem
  rwa [φ.map_sub, φ.map_pow, sub_eq_zero] at h0

/-- Reduction modulo `𝓂[L]` intertwines the `n`-th power of `integerAlgEquivOfMemInteger σ hσ` with
the `q^n`-th power map on `𝓀[L]`. -/
theorem residue_integerAlgEquivOfMemInteger_pow_of_valuation_sub_pow_lt_one (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪[L] ↔ z ∈ 𝒪[L]) {q : ℕ}
    (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1) (n : ℕ) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L] ((integerAlgEquivOfMemInteger σ hσ ^ n) x) =
      IsLocalRing.residue 𝒪[L] x ^ q ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply,
      residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one σ hσ hcongr, ih, ← pow_mul,
      ← pow_succ]

/-- If `v(σ z − z^q) < 1` for all `z ∈ 𝒪[L]` (`q ≠ 0`), then `v((σ^n) z − z^{q^n}) < 1` for every
`n : ℕ` and `z ∈ 𝒪[L]`. -/
theorem valuation_pow_sub_pow_lt_one_of_valuation_sub_pow_lt_one (σ : L ≃ₐ[K] L) {q : ℕ}
    (hq : q ≠ 0) (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1) (n : ℕ) {z : L}
    (hz : z ∈ 𝒪[L]) :
    valuation L ((σ ^ n) z - z ^ q ^ n) < 1 := by
  have hσ := mem_integer_iff_of_valuation_sub_pow_lt_one (τ := σ) hq hcongr
  let z₀ : 𝒪[L] := ⟨z, hz⟩
  let φ := IsLocalRing.residue 𝒪[L]
  have hmem : (integerAlgEquivOfMemInteger σ hσ ^ n) z₀ - z₀ ^ q ^ n ∈ 𝓂[L] := by
    refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
    rw [φ.map_sub, φ.map_pow, sub_eq_zero]
    exact residue_integerAlgEquivOfMemInteger_pow_of_valuation_sub_pow_lt_one σ hσ hcongr n z₀
  have hv := (valuation L).mem_maximalIdeal_iff.1 hmem
  rwa [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow,
    coe_integerAlgEquivOfMemInteger_pow_apply] at hv

end IntegerAlgEquiv

section DiscretelyValued

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- **Fixed field of a Frobenius-type automorphism.** Let `K → L` be an extension of discretely
valued fields with surjective value-group map, `𝓀[K]` finite, `𝒪[K]` `𝓂[K]`-adically precomplete,
and `𝒪[L]` `𝓂[L]`-adically Hausdorff. For any `σ : L ≃ₐ[K] L` satisfying
`v_L(σ z − z^{#𝓀[K]}) < 1` on `𝒪[L]`, an element of `L` is fixed by `σ` if and only if it belongs
to the image of `K`. -/
theorem eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one [Finite 𝓀[K]]
    [IsDiscreteValuationRing 𝒪[K]] [IsPrecomplete 𝓂[K] 𝒪[K]]
    [IsDiscreteValuationRing 𝒪[L]] [IsHausdorff 𝓂[L] 𝒪[L]]
    (hsurj : Function.Surjective (mapValueGroupWithZero K L)) (σ : L ≃ₐ[K] L)
    (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ Nat.card 𝓀[K]) < 1) (x : L) :
    σ x = x ↔ x ∈ Set.range (algebraMap K L) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hq : Nat.card 𝓀[K] ≠ 0 := Nat.card_pos.ne'
    have hσ := mem_integer_iff_of_valuation_sub_pow_lt_one (τ := σ) hq hcongr
    let σ₀ := integerAlgEquivOfMemInteger σ hσ
    have hint : ∀ x₀ : 𝒪[L], σ₀ x₀ = x₀ → ∃ c : 𝒪[K], algebraMap 𝒪[K] 𝒪[L] c = x₀ := by
      intro x₀ hx₀
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
      let π : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖ
      have hπ : Irreducible π :=
        irreducible_algebraMap_of_mapValueGroupWithZero_surjective hsurj hϖ
      let φ := IsLocalRing.residue 𝒪[L]
      have hstep : ∀ y : {z : 𝒪[L] // σ₀ z = z},
          ∃ (b : 𝒪[K]) (y' : {z : 𝒪[L] // σ₀ z = z}),
            y.1 - algebraMap 𝒪[K] 𝒪[L] b = π * y'.1 := by
        intro y
        have hres_pow : φ y.1 ^ Nat.card 𝓀[K] = φ y.1 := by
          have h := residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one σ hσ hcongr y.1
          rwa [y.2, eq_comm] at h
        obtain ⟨rbar, hrbar⟩ :=
          (FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap
            (K := 𝓀[K]) (L := 𝓀[L]) (φ y.1)).1 hres_pow
        obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective rbar
        rw [residueField_algebraMap_residue] at hrbar
        have hdiff_mem : y.1 - algebraMap 𝒪[K] 𝒪[L] b ∈ 𝓂[L] := by
          refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
          rw [φ.map_sub, hrbar, sub_self]
        rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hdiff_mem
        obtain ⟨y₁, hy₁⟩ := hdiff_mem
        have hy₁_fix : σ₀ y₁ = y₁ := by
          apply mul_left_cancel₀ hπ.ne_zero
          calc π * σ₀ y₁
              = σ₀ (π * y₁) := by rw [map_mul, σ₀.commutes ϖ]
            _ = σ₀ (y.1 - algebraMap 𝒪[K] 𝒪[L] b) := by rw [← hy₁]
            _ = y.1 - algebraMap 𝒪[K] 𝒪[L] b := by rw [map_sub, y.2, σ₀.commutes b]
            _ = π * y₁ := hy₁
        exact ⟨b, ⟨y₁, hy₁_fix⟩, hy₁⟩
      choose bFn nextFn hFn using hstep
      let seq : ℕ → {z : 𝒪[L] // σ₀ z = z} := Nat.rec ⟨x₀, hx₀⟩ fun _ s ↦ nextFn s
      let a : ℕ → 𝒪[K] := fun k ↦ ∑ i ∈ Finset.range k, ϖ ^ i * bFn (seq i)
      have ha_cauchy : AdicCompletion.IsAdicCauchy 𝓂[K] 𝒪[K] a := by
        refine (AdicCompletion.isAdicCauchy_iff 𝓂[K] 𝒪[K] a).2 fun k ↦ ?_
        rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
        simp only [a, Finset.sum_range_succ, sub_add_cancel_left]
        rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.neg_mem_iff,
          Ideal.mem_span_singleton]
        exact ⟨bFn (seq k), rfl⟩
      have hx_approx : ∀ k : ℕ, x₀ - algebraMap 𝒪[K] 𝒪[L] (a k) = π ^ k * (seq k).1 := by
        intro k
        induction k with
        | zero =>
          simp only [a, seq, Finset.range_zero, Finset.sum_empty, map_zero, sub_zero, pow_zero,
            one_mul]
          rfl
        | succ k ih =>
          have hsum : algebraMap 𝒪[K] 𝒪[L] (a (k + 1)) =
              algebraMap 𝒪[K] 𝒪[L] (a k) + π ^ k * algebraMap 𝒪[K] 𝒪[L] (bFn (seq k)) := by
            simp only [a, Finset.sum_range_succ, map_add, map_mul, map_pow, π]
          calc x₀ - algebraMap 𝒪[K] 𝒪[L] (a (k + 1))
              = (x₀ - algebraMap 𝒪[K] 𝒪[L] (a k)) -
                  π ^ k * algebraMap 𝒪[K] 𝒪[L] (bFn (seq k)) := by
                rw [hsum, sub_add_eq_sub_sub]
            _ = π ^ k * ((seq k).1 - algebraMap 𝒪[K] 𝒪[L] (bFn (seq k))) := by
                rw [ih, ← mul_sub]
            _ = π ^ k * (π * (seq (k + 1)).1) := by rw [hFn (seq k)]
            _ = π ^ (k + 1) * (seq (k + 1)).1 := by rw [pow_succ, mul_assoc]
      obtain ⟨c, hc⟩ := IsPrecomplete.prec inferInstance ha_cauchy
      refine ⟨c, (IsHausdorff.eq_iff_smodEq (I := 𝓂[L])).2 fun k ↦ ?_⟩
      rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
      have hdecomp : algebraMap 𝒪[K] 𝒪[L] c - x₀ =
          -(algebraMap 𝒪[K] 𝒪[L] (a k - c)) - (x₀ - algebraMap 𝒪[K] 𝒪[L] (a k)) := by
        rw [map_sub]
        ring
      rw [hdecomp]
      refine Ideal.sub_mem _ (Submodule.neg_mem _ ?_) ?_
      · have hck : a k - c ∈ 𝓂[K] ^ k := by
          have h := hc k
          rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at h
        have hm : algebraMap 𝒪[K] 𝒪[L] (a k - c) ∈ (𝓂[K] ^ k).map (algebraMap 𝒪[K] 𝒪[L]) :=
          Ideal.mem_map_of_mem _ hck
        rwa [Ideal.map_pow,
          map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective hsurj] at hm
      · rw [hx_approx k, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨(seq k).1, rfl⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, map_zero _⟩
    obtain ⟨d, hd⟩ := mapValueGroupWithZero_surjective_iff.1 hsurj x
    have hvd : valuation L (algebraMap K L d) = valuation L x := ((valuation L).veq_iff_eq).1 hd
    have hdL0 : algebraMap K L d ≠ 0 := fun h0 ↦
      hx0 (((valuation L).zero_iff).1 (hvd.symm.trans (by rw [h0, map_zero])))
    have hz1 : x / algebraMap K L d ∈ 𝒪[L] := by
      rw [Valuation.mem_integer_iff, map_div₀, hvd, div_self ((valuation L).ne_zero_iff.2 hx0)]
    have hz_fix : σ₀ ⟨x / algebraMap K L d, hz1⟩ = ⟨x / algebraMap K L d, hz1⟩ :=
      Subtype.ext (by
        rw [coe_integerAlgEquivOfMemInteger_apply, map_div₀, hx, σ.commutes])
    obtain ⟨c, hc⟩ := hint ⟨x / algebraMap K L d, hz1⟩ hz_fix
    refine ⟨(c : K) * d, ?_⟩
    have hc' : algebraMap K L (c : K) = x / algebraMap K L d := by
      rw [← coe_algebraMap_integerRing, hc]
    rw [map_mul, hc', div_mul_cancel₀ _ hdL0]
  · rintro ⟨c, rfl⟩
    exact σ.commutes c

/-- **Existence of transcendental elements.** Let `K → L` be an extension of discretely valued
fields with surjective value-group map, `𝒪[L]` `𝓂[L]`-adically precomplete, and `𝓀[L]` infinite. If
`σ : L ≃ₐ[K] L` satisfies `v_L(σ z − z^q) < 1` on `𝒪[L]` for some `q > 1`, then `L` contains an
element transcendental over `K`. -/
theorem exists_transcendental_of_valuation_sub_pow_lt_one
    [IsDiscreteValuationRing 𝒪[K]] [IsDiscreteValuationRing 𝒪[L]]
    [IsPrecomplete 𝓂[L] 𝒪[L]] [Infinite 𝓀[L]]
    (hsurj : Function.Surjective (mapValueGroupWithZero K L)) (σ : L ≃ₐ[K] L) {q : ℕ}
    (hq : 1 < q) (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1) :
    ∃ x : L, Transcendental K x := by
  classical
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hσ := mem_integer_iff_of_valuation_sub_pow_lt_one (τ := σ) hq0 hcongr
  let σ₀ := integerAlgEquivOfMemInteger σ hσ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let π : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖ
  have hπ : Irreducible π := irreducible_algebraMap_of_mapValueGroupWithZero_surjective hsurj hϖ
  have hπ_fix : ∀ m : ℕ, (σ₀ ^ m) π = π := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, σ₀.commutes]
  let φ := IsLocalRing.residue 𝒪[L]
  have hd_exists : ∀ m : ℕ, m ≠ 0 → ∃ d : 𝒪[L], (σ₀ ^ m) d - d ∉ 𝓂[L] := by
    intro m hm
    have hP0 : (Polynomial.X ^ q ^ m - Polynomial.X : 𝓀[L][X]) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero (Nat.one_lt_pow hm hq)
    have hnot_all : ¬ ∀ u : 𝓀[L], u ^ q ^ m = u := fun hall ↦
      hP0 (Polynomial.eq_zero_of_infinite_isRoot _
        (Set.infinite_univ.mono fun u _ ↦ by
          simp [Polynomial.IsRoot, sub_eq_zero, hall u]))
    obtain ⟨u, hu⟩ := not_forall.1 hnot_all
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective u
    refine ⟨d, fun hmem ↦ hu ?_⟩
    have h0 : φ ((σ₀ ^ m) d - d) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [φ.map_sub,
      residue_integerAlgEquivOfMemInteger_pow_of_valuation_sub_pow_lt_one σ hσ hcongr,
      sub_eq_zero] at h0
    exact h0
  let d : ℕ → 𝒪[L] := fun m ↦ if hm : m = 0 then 0 else (hd_exists m hm).choose
  have hd_spec : ∀ {m : ℕ} (hm : m ≠ 0), (σ₀ ^ m) (d m) - d m ∉ 𝓂[L] := by
    intro m hm
    simpa [d, hm] using (hd_exists m hm).choose_spec
  let s : ℕ → 𝒪[L] :=
    Nat.rec 0 fun m sm ↦
      if m = 0 then 0
      else if π ^ (m + 1) ∣ (σ₀ ^ m) sm - sm then sm + π ^ m * d m else sm
  have hs_cauchy : AdicCompletion.IsAdicCauchy 𝓂[L] 𝒪[L] s := by
    refine (AdicCompletion.isAdicCauchy_iff 𝓂[L] 𝒪[L] s).2 fun m ↦ ?_
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [pow_zero]
    · dsimp only [s]
      simp only [hm, ↓reduceIte]
      split_ifs with hdvd
      · rw [sub_add_cancel_left, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
          Ideal.neg_mem_iff, Ideal.mem_span_singleton]
        exact ⟨d m, rfl⟩
      · rw [sub_self]
        exact Ideal.zero_mem _
  have hs_not_dvd : ∀ {m : ℕ}, m ≠ 0 → ¬ (π ^ (m + 1) ∣ (σ₀ ^ m) (s (m + 1)) - s (m + 1)) := by
    intro m hm
    dsimp only [s]
    simp only [hm, ↓reduceIte]
    split_ifs with hdvd
    · intro hdvd'
      have hterm : ((σ₀ ^ m) (s m + π ^ m * d m) - (s m + π ^ m * d m)) -
          ((σ₀ ^ m) (s m) - s m) = π ^ m * ((σ₀ ^ m) (d m) - d m) := by
        rw [map_add, map_mul, map_pow, hπ_fix m]
        ring
      have hdvd_diff : π ^ (m + 1) ∣ π ^ m * ((σ₀ ^ m) (d m) - d m) :=
        hterm ▸ dvd_sub hdvd' hdvd
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)] at hdvd_diff
      exact hd_spec hm (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton.2 hdvd_diff)
    · exact hdvd
  obtain ⟨x₀, hx₀⟩ := IsPrecomplete.prec inferInstance hs_cauchy
  refine ⟨(x₀ : L), transcendental_of_forall_pow_algEquiv_ne_self σ fun m hm hfix ↦ ?_⟩
  have hfix₀ : (σ₀ ^ m) x₀ = x₀ :=
    Subtype.ext ((coe_integerAlgEquivOfMemInteger_pow_apply σ hσ m x₀).trans hfix)
  have hmem : s (m + 1) - x₀ ∈ Ideal.span {π ^ (m + 1)} := by
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    have h := hx₀ (m + 1)
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at h
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
  apply hs_not_dvd hm
  refine ⟨(σ₀ ^ m) w - w, ?_⟩
  calc (σ₀ ^ m) (s (m + 1)) - s (m + 1)
      = (σ₀ ^ m) (s (m + 1) - x₀) - (s (m + 1) - x₀) := by
        rw [map_sub, hfix₀, sub_sub_sub_cancel_right]
    _ = (σ₀ ^ m) (π ^ (m + 1) * w) - π ^ (m + 1) * w := by rw [hw]
    _ = π ^ (m + 1) * ((σ₀ ^ m) w - w) := by
        rw [map_mul, map_pow, hπ_fix m, mul_sub]

/-- **Frobenius eigenvector equation for principal units.** Let `K → L` be an extension of
discretely valued fields with surjective value-group map, `𝒪[L]` `𝓂[L]`-adically complete, and
`𝓀[L]` algebraically closed. If `σ : L ≃ₐ[K] L` satisfies `v_L(σ z − z^q) < 1` on `𝒪[L]` for some
`q > 1`, then for every `u ∈ 𝒪[K]` with `u − 1 ∈ 𝓂[K]` there exists `y ∈ L \ {0}` such that
`σ y = u y`. -/
theorem exists_apply_eq_mul_of_sub_one_mem_maximalIdeal
    [IsDiscreteValuationRing 𝒪[K]] [IsDiscreteValuationRing 𝒪[L]]
    [IsAdicComplete 𝓂[L] 𝒪[L]] [IsAlgClosed 𝓀[L]]
    (hsurj : Function.Surjective (mapValueGroupWithZero K L)) (σ : L ≃ₐ[K] L) {q : ℕ}
    (hq : 1 < q) (hcongr : ∀ z : L, z ∈ 𝒪[L] → valuation L (σ z - z ^ q) < 1)
    {u : 𝒪[K]} (hu : u - 1 ∈ 𝓂[K]) :
    ∃ y : L, y ≠ 0 ∧ σ y = algebraMap K L (u : K) * y := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hσ := mem_integer_iff_of_valuation_sub_pow_lt_one (τ := σ) hq0 hcongr
  let σ₀ := integerAlgEquivOfMemInteger σ hσ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let π : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖ
  have hπ : Irreducible π := irreducible_algebraMap_of_mapValueGroupWithZero_surjective hsurj hϖ
  let u' : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] u
  let φ := IsLocalRing.residue 𝒪[L]
  have hu'_mem : u' - 1 ∈ 𝓂[L] := by
    rw [← map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective hsurj]
    have hmap : algebraMap 𝒪[K] 𝒪[L] (u - 1) = u' - 1 := by simp [u']
    exact hmap ▸ Ideal.mem_map_of_mem _ hu
  have hu'_res : φ u' = 1 := by
    have h0 : φ (u' - 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu'_mem
    rwa [φ.map_sub, φ.map_one, sub_eq_zero] at h0
  have hstep : ∀ (k : ℕ) (y : 𝒪[L]),
      σ₀ y - u' * y ∈ Ideal.span {π ^ (k + 1)} →
        ∃ z : 𝒪[L], σ₀ (y + π ^ (k + 1) * z) - u' * (y + π ^ (k + 1) * z) ∈
          Ideal.span {π ^ (k + 2)} := by
    intro k y hy
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hy
    let P : 𝓀[L][X] := Polynomial.X ^ q - (Polynomial.X - Polynomial.C (φ r))
    have hdeg_lt : (Polynomial.X - Polynomial.C (φ r) : 𝓀[L][X]).degree <
        (Polynomial.X ^ q : 𝓀[L][X]).degree := by
      calc (Polynomial.X - Polynomial.C (φ r) : 𝓀[L][X]).degree
          ≤ max (Polynomial.X : 𝓀[L][X]).degree (Polynomial.C (φ r)).degree :=
            Polynomial.degree_sub_le _ _
        _ ≤ 1 := max_le Polynomial.degree_X_le (Polynomial.degree_C_le.trans zero_le_one)
        _ < q := by exact_mod_cast hq
        _ = (Polynomial.X ^ q : 𝓀[L][X]).degree := (Polynomial.degree_X_pow q).symm
    have hPdeg : P.degree ≠ 0 := by
      dsimp only [P]
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hdeg_lt, Polynomial.degree_X_pow]
      exact_mod_cast hq0
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root P hPdeg
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective ξ
    refine ⟨z, ?_⟩
    have hcalc : σ₀ (y + π ^ (k + 1) * z) - u' * (y + π ^ (k + 1) * z) =
        π ^ (k + 1) * (r + σ₀ z - u' * z) := by
      have hπ_fix : σ₀ π = π := σ₀.commutes ϖ
      rw [map_add, map_mul, map_pow, hπ_fix]
      calc σ₀ y + π ^ (k + 1) * σ₀ z - u' * (y + π ^ (k + 1) * z)
          = (σ₀ y - u' * y) + π ^ (k + 1) * (σ₀ z - u' * z) := by ring
        _ = π ^ (k + 1) * (r + σ₀ z - u' * z) := by rw [hr]; ring
    rw [hcalc]
    have herr_mem : r + σ₀ z - u' * z ∈ 𝓂[L] := by
      refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
      have hroot : φ z ^ q - (φ z - φ r) = 0 := by
        simpa [P, Polynomial.IsRoot] using hξ
      rw [φ.map_sub, φ.map_add, φ.map_mul,
        residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one σ hσ hcongr, hu'_res,
        one_mul]
      linear_combination hroot
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at herr_mem
    obtain ⟨r', hr'⟩ := herr_mem
    rw [hr', ← mul_assoc, ← pow_succ, Ideal.mem_span_singleton]
    exact ⟨r', rfl⟩
  have hinit : σ₀ 1 - u' * 1 ∈ Ideal.span {π ^ 1} := by
    rw [pow_one, ← hπ.maximalIdeal_eq, map_one, mul_one, ← Ideal.neg_mem_iff, neg_sub]
    exact hu'_mem
  let stSeq : (k : ℕ) → {y : 𝒪[L] // σ₀ y - u' * y ∈ Ideal.span {π ^ (k + 1)}} :=
    Nat.rec ⟨1, hinit⟩ fun k s ↦
      ⟨s.1 + π ^ (k + 1) * (hstep k s.1 s.2).choose, (hstep k s.1 s.2).choose_spec⟩
  let f : ℕ → 𝒪[L] := fun n ↦
    match n with
    | 0 => 1
    | k + 1 => (stSeq k).1
  have hf_cauchy : AdicCompletion.IsAdicCauchy 𝓂[L] 𝒪[L] f := by
    refine (AdicCompletion.isAdicCauchy_iff 𝓂[L] 𝒪[L] f).2 fun n ↦ ?_
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    cases n with
    | zero => simp [f, pow_zero]
    | succ k =>
      dsimp only [f, stSeq]
      rw [sub_add_cancel_left, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.neg_mem_iff, Ideal.mem_span_singleton]
      exact ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ := IsPrecomplete.prec inferInstance hf_cauchy
  have hy₀_one : 1 - y₀ ∈ 𝓂[L] := by
    have h := hy₀ 1
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, pow_one] at h
  have hy₀_ne : (y₀ : L) ≠ 0 := by
    intro h0
    have hy0' : y₀ = 0 := Subtype.ext h0
    rw [hy0', sub_zero] at hy₀_one
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[L]).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hy₀_one isUnit_one)
  have hy₀_eq : σ₀ y₀ = u' * y₀ := by
    refine (IsHausdorff.eq_iff_smodEq (I := 𝓂[L])).2 fun n ↦ ?_
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    cases n with
    | zero => simp [pow_zero]
    | succ k =>
      have hdiff : f (k + 1) - y₀ ∈ 𝓂[L] ^ (k + 1) := by
        have h := hy₀ (k + 1)
        rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at h
      have herr_k : σ₀ (f (k + 1)) - u' * f (k + 1) ∈ 𝓂[L] ^ (k + 1) := by
        rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
        exact (stSeq k).2
      have hsigma_diff : σ₀ (f (k + 1) - y₀) ∈ 𝓂[L] ^ (k + 1) := by
        rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow] at hdiff ⊢
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hdiff
        have hπ_fix : σ₀ π = π := σ₀.commutes ϖ
        rw [hw, map_mul, map_pow, hπ_fix, Ideal.mem_span_singleton]
        exact ⟨σ₀ w, rfl⟩
      have hdecomp : σ₀ y₀ - u' * y₀ =
          (σ₀ (f (k + 1)) - u' * f (k + 1)) - σ₀ (f (k + 1) - y₀) + u' * (f (k + 1) - y₀) := by
        rw [map_sub]
        ring
      rw [hdecomp]
      exact Ideal.add_mem _ (Ideal.sub_mem _ herr_k hsigma_diff)
        (Ideal.mul_mem_left _ u' hdiff)
  refine ⟨(y₀ : L), hy₀_ne, ?_⟩
  have hcoe := congrArg Subtype.val hy₀_eq
  rwa [coe_integerAlgEquivOfMemInteger_apply, Subring.coe_mul, coe_algebraMap_integerRing] at hcoe

end DiscretelyValued

end ValuativeExtension
