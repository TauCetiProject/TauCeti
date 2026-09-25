/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.QuadraticCharacter
public import TauCeti.NumberTheory.NumberField.Cyclotomic.GaussSum
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The conductor of a multiquadratic field

The conductor of an abelian number field is the least level `m` of a cyclotomic field `ℚ(ζ_m)`
containing it. This file computes it for quadratic and multiquadratic fields. For a fundamental
discriminant `D`, a square root of `D` lies in `ℚ(ζ_m)` exactly when `|D| ∣ m`; so the conductor
of `ℚ(√D)` is `|D|`. For squarefree integers `d₁, …, dₙ`, the multiquadratic field
`ℚ(√d₁, …, √dₙ)` lies in `ℚ(ζ_m)` exactly when the least common multiple of the
`|fundamentalDiscriminant dᵢ|` divides `m`, so that least common multiple is its conductor.

The containment direction uses `TauCeti.Multiquadratic.mem_of_sq_eq_of_isFundamentalDiscriminant`;
the minimality direction uses
`IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`.

For the classical argument see D. A. Cox, *Primes of the Form x² + ny²*, §3.B, and
K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6.

## Main results

* `TauCeti.Multiquadratic.natAbs_dvd_of_adjoin_sqrt_le_cyclotomic`: inside a cyclotomic field of
  level `n` with `|D| ∣ n`, a cyclotomic subfield of level `m ∣ n` containing `ℚ(√D)` has
  `|D| ∣ m`.
* `TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_dvd`: a square root of a fundamental
  discriminant `D` lies in `ℚ(ζ_m)` if and only if `|D| ∣ m`.
* `TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd`: a square root
  of a squarefree integer `d` lies in `ℚ(ζ_m)` if and only if `|fundamentalDiscriminant d| ∣ m`.
* `TauCeti.Multiquadratic.adjoin_range_le_adjoin_simple_iff_lcm_dvd`: `ℚ(√d₁, …, √dₙ) ⊆ ℚ(ζ_m)` if
  and only if the least common multiple of the `|fundamentalDiscriminant dᵢ|` divides `m`.
-/

public section

open IntermediateField Polynomial

namespace TauCeti.Multiquadratic

/-- **A cyclotomic subfield containing `ℚ(√D)` has level divisible by `|D|`.** Let `K` be a
cyclotomic field of level `n` and `D` a fundamental discriminant with `|D| ∣ n`. If the cyclotomic
subfield `F` of `K` at a level `m ∣ n` contains a square root of `D`, then `|D| ∣ m`. -/
theorem natAbs_dvd_of_adjoin_sqrt_le_cyclotomic {n m : ℕ} [NeZero n] {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hDn : D.natAbs ∣ n) (hmn : m ∣ n) (F : IntermediateField ℚ K)
    [IsCyclotomicExtension {m} ℚ F] {x : K} (hx : x ^ 2 = (D : K)) (hfield : ℚ⟮x⟯ ≤ F) :
    D.natAbs ∣ m := by
  let _ : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  let _ : NeZero m := ⟨fun h => NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hmn))⟩
  let _ : NeZero (Monoid.exponent (ZMod n)ˣ : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := (ZMod n)ˣ)⟩
  let _ : IsGalois ℚ F := IsCyclotomicExtension.isGalois {m} ℚ F
  let _ : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  -- The Gauss sum `g` of `χ_D`, formed with a primitive `|D|`-th root of unity of `K`.
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ K ^ (n / D.natAbs)) D.natAbs := by
    simpa only [Nat.div_div_self hDn (NeZero.ne n)] using
      (IsCyclotomicExtension.zeta_spec n ℚ K).pow_of_dvd
        (Nat.div_ne_zero_iff_of_dvd hDn |>.mpr ⟨NeZero.ne n, NeZero.ne _⟩)
        (Nat.div_dvd_of_dvd hDn)
  set g := DirichletCharacter.gaussSumOfPrimitiveRoot (fundamentalDiscriminantChar D hD) hζ
  have hg : g ^ 2 = (D : K) := gaussSumOfPrimitiveRoot_fundamentalDiscriminantChar_sq hD hζ
  -- Every automorphism fixing `F` fixes `x = ±g`, so `χ_D` lifted to level `n` kills it.
  set χ := (DirichletCharacter.changeLevel hDn (fundamentalDiscriminantChar D hD)).ringHomComp
    (Int.castRingHom ℂ)
  have hχ : χ ∈ IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n K ℂ F := by
    rw [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
    intro σ hσ
    have hσx : σ x = x :=
      (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ x (hfield (mem_adjoin_simple_self ℚ x))
    have hσg : σ ∈ MulAction.stabilizer Gal(K/ℚ) g := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rcases eq_or_eq_neg_of_sq_eq_sq g x (hg.trans hx.symm) with h | h
      · rw [h, hσx]
      · rw [h, map_neg, hσx]
    rw [DirichletCharacter.mem_stabilizer_gaussSumOfPrimitiveRoot_iff_changeLevel _
      (isPrimitive_fundamentalDiscriminantChar hD) hDn] at hσg
    simp only [χ, MulChar.ringHomComp_apply, hσg, map_one]
  -- The conductor of the lifted primitive character is `|D|`.
  have hcond :=
    (IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      n K ℂ F hmn χ).mp hχ
  rwa [DirichletCharacter.conductor_ringHomComp _ _ Int.cast_injective,
    DirichletCharacter.conductor_changeLevel, isPrimitive_fundamentalDiscriminantChar hD] at hcond

variable {L : Type*} [Field L] [CharZero L] {m : ℕ} {ζ : L}

/-- **The conductor of a quadratic field.** Let `D` be a fundamental discriminant and `ζ` a
primitive `m`-th root of unity, `0 < m`, in a field of characteristic zero. A square root of `D`
lies in `ℚ(ζ)` if and only if `|D| ∣ m`. Thus `ℚ(ζ_|D|)` is the least cyclotomic field
containing `ℚ(√D)`. -/
theorem mem_adjoin_simple_iff_natAbs_dvd (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) {x : L} (hx : x ^ 2 = (D : L)) :
    x ∈ ℚ⟮ζ⟯ ↔ D.natAbs ∣ m := by
  refine ⟨fun hxζ => ?_, fun hdvd =>
    mem_of_sq_eq_of_isFundamentalDiscriminant hm hζ (mem_adjoin_simple_self ℚ ζ) hD hdvd hx⟩
  let _ : NeZero m := ⟨hm.ne'⟩
  -- Write `x = p(ζ)` for a rational polynomial `p`.
  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral hm).tower_top
  rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic hζint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hxζ
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hxζ
  -- A primitive `m`-th root of unity `μ` in the cyclotomic field `E` of level `m |D|`.
  set n := m * D.natAbs
  let _ : NeZero n := ⟨Nat.mul_ne_zero hm.ne' (Int.natAbs_ne_zero.mpr hD.ne_zero)⟩
  let E := CyclotomicField n ℚ
  let _ : IsCyclotomicExtension {n} ℚ E := CyclotomicField.isCyclotomicExtension n ℚ
  have hμ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ E ^ D.natAbs) m := by
    simpa only [n, Nat.mul_div_cancel _ (Int.natAbs_pos.mpr hD.ne_zero)] using
      (IsCyclotomicExtension.zeta_spec n ℚ E).pow_of_dvd
        (Int.natAbs_ne_zero.mpr hD.ne_zero) (dvd_mul_left _ _)
  set μ := IsCyclotomicExtension.zeta n ℚ E ^ D.natAbs
  let _ : IsCyclotomicExtension {m} ℚ ℚ⟮μ⟯ := hμ.intermediateField_adjoin_isCyclotomicExtension ℚ
  -- `ζ` and `μ` share the minimal polynomial `Φ_m`, so `p(μ)` is again a square root of `D`.
  have hminpoly : minpoly ℚ ζ = minpoly ℚ μ := by
    rw [← cyclotomic_eq_minpoly_rat hζ hm, ← cyclotomic_eq_minpoly_rat hμ hm]
  have hroot : aeval μ (p ^ 2 - C (D : ℚ)) = 0 := by
    refine aeval_eq_zero_of_dvd_aeval_eq_zero ?_ (minpoly.aeval ℚ μ)
    rw [← hminpoly]
    exact minpoly.dvd ℚ ζ (by simp [hx])
  have hy : aeval μ p ^ 2 = (D : E) := by
    simpa [sub_eq_zero] using hroot
  have hymem : aeval μ p ∈ ℚ⟮μ⟯ := by
    rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic
      (hμ.isIntegral hm).tower_top.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]
    exact AlgHom.mem_range_self _ p
  exact natAbs_dvd_of_adjoin_sqrt_le_cyclotomic hD (dvd_mul_left _ _) (dvd_mul_right _ _)
    ℚ⟮μ⟯ hy (adjoin_simple_le_iff.mpr hymem)

/-- **The conductor of the quadratic field of a squarefree integer.** Let `d` be squarefree and
`ζ` a primitive `m`-th root of unity, `0 < m`, in a field of characteristic zero. A square root of
`d` lies in `ℚ(ζ)` if and only if `|fundamentalDiscriminant d| ∣ m`. -/
theorem mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m) {d : ℤ} (hd : Squarefree d) {x : L} (hx : x ^ 2 = (d : L)) :
    x ∈ ℚ⟮ζ⟯ ↔ (fundamentalDiscriminant d).natAbs ∣ m := by
  refine ⟨fun hxζ => ?_, fun hdvd =>
    mem_of_sq_eq_of_squarefree hm hζ (mem_adjoin_simple_self ℚ ζ) hd hdvd hx⟩
  obtain ⟨c, -, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  refine (mem_adjoin_simple_iff_natAbs_dvd hm hζ
    (isFundamentalDiscriminant_fundamentalDiscriminant hd) (x := c * x) ?_).mp
    (mul_mem (intCast_mem _ c) hxζ)
  rw [← hcd, mul_pow, hx]
  push_cast
  ring

/-- **The conductor of a multiquadratic field.** Let `d₁, …, dₙ` be squarefree integers with
square roots `r i` in a field of characteristic zero, and let `ζ` be a primitive `m`-th root of
unity, `0 < m`. Then `ℚ(r 1, …, r n) ⊆ ℚ(ζ)` if and only if the least common multiple of the
`|fundamentalDiscriminant dᵢ|` divides `m`. -/
theorem adjoin_range_le_adjoin_simple_iff_lcm_dvd {ι : Type*} [Fintype ι] (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m) {d : ι → ℤ} (hd : ∀ i, Squarefree (d i)) {r : ι → L}
    (hr : ∀ i, r i ^ 2 = (d i : L)) :
    adjoin ℚ (Set.range r) ≤ ℚ⟮ζ⟯ ↔
      Finset.univ.lcm (fun i => (fundamentalDiscriminant (d i)).natAbs) ∣ m := by
  simp only [adjoin_le_iff, Set.range_subset_iff, SetLike.mem_coe, Finset.lcm_dvd_iff,
    Finset.mem_univ, true_implies,
    fun i => mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hm hζ (hd i) (hr i)]

/-- **Worked example: the conductor of `ℚ(√-3)` is `3`.** -/
example (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m) {x : L} (hx : x ^ 2 = -3) :
    x ∈ ℚ⟮ζ⟯ ↔ 3 ∣ m := by
  simpa [fundamentalDiscriminant_of_mod_four_eq_one] using
    mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hm hζ
      (d := -3) Int.prime_three.neg.squarefree (by rw [hx]; norm_num)

/-- **Worked example: the conductor of `ℚ(√2, √3)` is `24`.** The fundamental discriminants of
`2` and `3` are `8` and `12`, whose least common multiple is `24`. -/
example (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m) {x y : L} (hx : x ^ 2 = 2) (hy : y ^ 2 = 3) :
    ℚ⟮x, y⟯ ≤ ℚ⟮ζ⟯ ↔ 24 ∣ m := by
  have h2 : x ∈ ℚ⟮ζ⟯ ↔ 8 ∣ m := by
    simpa [fundamentalDiscriminant_of_mod_four_ne_one] using
      mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hm hζ
        (d := 2) (Int.prime_two.squarefree) (by rw [hx]; norm_num)
  have h3 : y ∈ ℚ⟮ζ⟯ ↔ 12 ∣ m := by
    simpa [fundamentalDiscriminant_of_mod_four_ne_one] using
      mem_adjoin_simple_iff_natAbs_fundamentalDiscriminant_dvd hm hζ
        (d := 3) (Int.prime_three.squarefree) (by rw [hy]; norm_num)
  rw [adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
    SetLike.mem_coe, h2, h3, ← Nat.lcm_dvd_iff]
  norm_num

end TauCeti.Multiquadratic
