/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.FrickePartner
public import TauCeti.Algebra.Module.ZLattice.Milgram
public import TauCeti.LinearAlgebra.IntegralLattice.RationalInvariants
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.Real.Irrational

/-!
# The signed discriminant of a lattice and its Kronecker character

Let `L` be a `ℤ`-submodule of a real inner product space `E`, with discriminant group
`A_L = L^∨ ⧸ (L ∩ L^∨)` (`ZLattice.DiscriminantGroup L`). The *signed discriminant* of `L` is
```text
D_L = (-1) ^ (finrank ℝ E / 2) * |A_L|
```
(`ZLattice.signedDiscr L`). The definition is unguarded: when `A_L` is infinite, `Nat.card A_L = 0`
gives `D_L = 0`, and when `L` is an integral full lattice of rank `n = finrank ℝ E`, `|A_L|` is the
positive integer `det L = covolume L ^ 2`, so `D_L = (-1) ^ ⌊n / 2⌋ det L` is nonzero with sign
`(-1) ^ ⌊n / 2⌋`.

In even rank `2k`, this is the signed determinant `D_L = (-1)^k det L` of Hecke and Schoeneberg.
Because `⌊n / 2⌋` and `C(n, 2)` have the same parity in every rank `n` (`Nat.even_choose_two_iff`),
`(-1) ^ ⌊n / 2⌋` also equals the quadratic-form sign `(-1) ^ (n (n - 1) / 2)` in all dimensions:
for every integral full lattice `L`, the rational square class of `D_L` is the signed discriminant
`RegularFormClass.signedDiscr` of the ambient rational quadratic form of `ratModel hL`
(`ZLattice.IsIntegral.signedDiscr_rationalFormClass_ratModel`).

For an even full lattice `L` of even rank `2k`, `D_L` is a nonzero discriminant congruent to `0` or
`1` modulo `4` (`ZLattice.IsEven.signedDiscr_modEq_zero_or_one`), so it defines the quadratic
Dirichlet character `TauCeti.kroneckerChar R (signedDiscr L) _ _` of modulus `|D_L| = det L`, whose
value at `-1` is `(-1)^k` (`ZLattice.IsEven.kroneckerChar_signedDiscr_neg_one`). Every integer
coprime to `level L` is coprime to `D_L` (`ZLattice.isCoprime_signedDiscr_of_isCoprime_level`).
In even rank, scaling `L` by `√m` multiplies `D_L` by the square `(m^k)²`, and the product of `D_L`
with the signed discriminant of its Fricke partner `√(level L) • L^∨` is the square
`(level L ^ k)²`; consequently both operations preserve the conductor and primitive character of
`(D_L / ·)`.

At the non-integral boundary, for any `c : ℝ` with `c²` irrational — in particular for
`c = 2 ^ (1 / 4 : ℝ)` — the rank-one lattice `c ℤ ⊆ ℝ` has dual `c⁻¹ ℤ` meeting `c ℤ` only at `0`,
so its discriminant group and every quotient `L^∨ ⧸ (L^∨ ∩ a L^∨ ∩ L)` are infinite and `D_L = 0`.

## Main definitions

* `ZLattice.signedDiscr L`: the signed discriminant `(-1) ^ (finrank ℝ E / 2) * |A_L|`.

## Main statements

* `ZLattice.signedDiscr_comap`, `ZLattice.signedDiscr_orthSum_of_even_left`: isometry invariance of
  `D_L`, and multiplicativity `D_{L ⊕ M} = D_L * D_M` when at least one summand has even ambient
  dimension.
* `ZLattice.IsIntegral.signedDiscr_cast`, `ZLattice.IsIntegral.signedDiscr_ne_zero`,
  `ZLattice.IsEven.signedDiscr_eq_one_of_isUnimodular`: for integral full lattices
  `D_L = (-1) ^ ⌊n / 2⌋ det L ≠ 0`, and `D_L = 1` for even unimodular full lattices.
* `ZLattice.IsIntegral.signedDiscr_sqrt_smul`,
  `ZLattice.IsIntegral.mul_signedDiscr_sqrt_level_smul_dual`: `D_{√m • L} = mⁿ D_L` and
  `D_L * D_{√N • L^∨} = Nⁿ`.
* `ZLattice.IsIntegral.signedDiscr_rationalFormClass_ratModel`,
  `TauCeti.IntegralLattice.signedDiscr_realModel`: comparisons with the rational and real models.
* `ZLattice.isCoprime_signedDiscr_of_isCoprime_level`,
  `ZLattice.IsEven.signedDiscr_modEq_zero_or_one`,
  `ZLattice.IsEven.kroneckerChar_signedDiscr_neg_one`,
  `ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_sqrt_level_smul_dual`: arithmetic properties
  of `D_L` and its Kronecker character `(D_L / ·)`.
* `ZLattice.inf_dual_span_two_rpow_one_quarter`,
  `ZLattice.infinite_discriminantGroup_span_two_rpow_one_quarter`,
  `ZLattice.signedDiscr_span_two_rpow_one_quarter`: the non-integral rank-one boundary example
  `2 ^ (1 / 4 : ℝ) • ℤ ⊆ ℝ`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS, 1997, Chapter 10.
* B. Schoeneberg, *Das Verhalten von mehrfachen Thetareihen bei Modulsubstitutionen*, Math. Ann.
  116 (1939), 511–523.
-/

public section

open Module Submodule
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Definition and general properties of the signed discriminant -/

/-- The **signed discriminant** `D_L = (-1) ^ ⌊finrank ℝ E / 2⌋ * |L^∨ ⧸ (L ∩ L^∨)|` of a lattice
`L` in a real inner product space `E`. For an integral full lattice of rank `2k`, this is
`(-1)^k det L`; when `L^∨ ⧸ (L ∩ L^∨)` is infinite, `Nat.card` vanishes and `signedDiscr L = 0`. -/
noncomputable def signedDiscr (L : Submodule ℤ E) : ℤ :=
  (-1) ^ (finrank ℝ E / 2) * Nat.card (DiscriminantGroup L)

theorem signedDiscr_def (L : Submodule ℤ E) :
    signedDiscr L = (-1) ^ (finrank ℝ E / 2) * Nat.card (DiscriminantGroup L) :=
  (rfl)

/-- In an ambient space of even dimension `2k`, `signedDiscr L = (-1)^k * |A_L|`. -/
theorem signedDiscr_of_finrank_eq (L : Submodule ℤ E) {k : ℕ} (hk : finrank ℝ E = 2 * k) :
    signedDiscr L = (-1) ^ k * Nat.card (DiscriminantGroup L) := by
  rw [signedDiscr_def, hk, Nat.mul_div_right k two_pos]

/-- The natural absolute value of the signed discriminant is the order of the discriminant group. -/
@[simp]
theorem natAbs_signedDiscr (L : Submodule ℤ E) :
    (signedDiscr L).natAbs = Nat.card (DiscriminantGroup L) := by
  rw [signedDiscr_def, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow,
    one_mul, Int.natAbs_natCast]

/-- The absolute value of the signed discriminant is the order of the discriminant group. -/
@[simp]
theorem abs_signedDiscr (L : Submodule ℤ E) :
    |signedDiscr L| = Nat.card (DiscriminantGroup L) := by
  rw [← Int.natCast_natAbs, natAbs_signedDiscr]

/-- The signed discriminant vanishes if and only if the discriminant group is infinite. -/
@[simp]
theorem signedDiscr_eq_zero_iff {L : Submodule ℤ E} :
    signedDiscr L = 0 ↔ Infinite (DiscriminantGroup L) := by
  rw [← Int.natAbs_eq_zero, natAbs_signedDiscr, Nat.card_eq_zero,
    or_iff_right (@not_isEmpty_of_nonempty (DiscriminantGroup L) ⟨0⟩)]

/-- For a unimodular lattice, `signedDiscr L = (-1) ^ ⌊finrank ℝ E / 2⌋`. -/
theorem IsUnimodular.signedDiscr_eq_neg_one_pow {L : Submodule ℤ E} (h : IsUnimodular L) :
    signedDiscr L = (-1) ^ (finrank ℝ E / 2) := by
  rw [signedDiscr_def, h.card_discriminantGroup_eq_one, Nat.cast_one, mul_one]

/-- Every submodule of a zero-dimensional space has signed discriminant `1`. -/
@[simp]
theorem signedDiscr_of_subsingleton [Subsingleton E] (L : Submodule ℤ E) : signedDiscr L = 1 := by
  have hu : IsUnimodular L := isUnimodular_iff_eq_dual.mpr (Subsingleton.elim _ _)
  rw [hu.signedDiscr_eq_neg_one_pow, Module.finrank_zero_of_subsingleton, Nat.zero_div, pow_zero]

/-- The signed discriminant is invariant under linear isometry equivalences. -/
@[simp]
theorem signedDiscr_comap (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) :
    signedDiscr (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) = signedDiscr L := by
  rw [signedDiscr_def, signedDiscr_def, card_discriminantGroup_comap,
    e.toLinearEquiv.finrank_eq]

/-- **Multiplicativity of the signed discriminant under orthogonal direct sums** when the first
ambient space has even dimension. Some parity hypothesis is required: for `ℤ ⊕ ℤ ⊆ ℝ²`,
`D_{ℤ ⊕ ℤ} = -1` while `D_ℤ * D_ℤ = 1 * 1 = 1`. -/
theorem signedDiscr_orthSum_of_even_left [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) (hE : Even (finrank ℝ E)) :
    signedDiscr (orthSum L M) = signedDiscr L * signedDiscr M := by
  obtain ⟨k, hk⟩ := hE
  have hdim : finrank ℝ (WithLp 2 (E × F)) = 2 * k + finrank ℝ F := by
    rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, Module.finrank_prod, hk, two_mul]
  rw [signedDiscr_def, signedDiscr_of_finrank_eq L (hk.trans (two_mul k).symm), signedDiscr_def,
    hdim, Nat.mul_add_div two_pos, pow_add, card_discriminantGroup_orthSum]
  push_cast
  ring

/-- **Multiplicativity of the signed discriminant under orthogonal direct sums** when the second
ambient space has even dimension. -/
theorem signedDiscr_orthSum_of_even_right [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) (hF : Even (finrank ℝ F)) :
    signedDiscr (orthSum L M) = signedDiscr L * signedDiscr M := by
  obtain ⟨k, hk⟩ := hF
  have hdim : finrank ℝ (WithLp 2 (E × F)) = finrank ℝ E + 2 * k := by
    rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, Module.finrank_prod, hk, two_mul]
  rw [signedDiscr_def, signedDiscr_def, signedDiscr_of_finrank_eq M (hk.trans (two_mul k).symm),
    hdim, add_comm (finrank ℝ E), Nat.mul_add_div two_pos, pow_add,
    card_discriminantGroup_orthSum]
  push_cast
  ring

/-! ### Full integral, unimodular, scaled, and Fricke-partner lattices -/

section FullLattice

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- The signed discriminant of an integral full lattice is nonzero. -/
theorem IsIntegral.signedDiscr_ne_zero (h : IsIntegral L) : signedDiscr L ≠ 0 := by
  borelize E
  have := h.finite_discriminantGroup
  rw [Ne, signedDiscr_eq_zero_iff, not_infinite_iff_finite]
  exact inferInstance

/-- The sign of the signed discriminant of an integral full lattice is
`(-1) ^ ⌊finrank ℝ E / 2⌋`. -/
theorem IsIntegral.sign_signedDiscr (h : IsIntegral L) :
    (signedDiscr L).sign = (-1) ^ (finrank ℝ E / 2) := by
  borelize E
  have := h.finite_discriminantGroup
  have hpos : (0 : ℤ) < Nat.card (DiscriminantGroup L) := Nat.cast_pos.mpr Nat.card_pos
  rw [signedDiscr_def, Int.sign_mul, Int.sign_eq_one_of_pos hpos, mul_one]
  rcases Nat.even_or_odd' (finrank ℝ E / 2) with ⟨m, hm | hm⟩ <;>
    simp [hm, pow_add, pow_mul]

/-- Cast to `ℝ`, the signed discriminant of an integral full lattice is
`(-1) ^ ⌊finrank ℝ E / 2⌋ * det L`. -/
theorem IsIntegral.signedDiscr_cast [MeasurableSpace E] [BorelSpace E] (h : IsIntegral L) :
    (signedDiscr L : ℝ) = (-1) ^ (finrank ℝ E / 2) * det L := by
  rw [signedDiscr_def, h.det_eq_card_discriminantGroup]
  push_cast
  rfl

/-- In any `ℤ`-basis `b` of an integral full lattice `L`, the signed discriminant is
`(-1) ^ ⌊finrank ℝ E / 2⌋` times the determinant of the integral Gram matrix of `b`. -/
theorem IsIntegral.signedDiscr_eq_neg_one_pow_mul_det_toMatrix (h : IsIntegral L)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    signedDiscr L =
      (-1) ^ (finrank ℝ E / 2) * (LinearMap.BilinForm.toMatrix b h.integralForm).det := by
  rw [signedDiscr_def, h.det_toMatrix_integralForm b]

/-- **An even unimodular full lattice has signed discriminant `1`**, since its rank is divisible
by `4` (`ZLattice.IsEven.four_dvd_finrank_of_level_dvd_two`). -/
theorem IsEven.signedDiscr_eq_one_of_isUnimodular (h : IsEven L) (hU : IsUnimodular L) :
    signedDiscr L = 1 := by
  obtain ⟨m, hm⟩ := h.four_dvd_finrank_of_level_dvd_two
    (by rw [h.level_eq_one_iff.mpr hU]; exact one_dvd 2)
  rw [hU.signedDiscr_eq_neg_one_pow, show finrank ℝ E / 2 = 2 * m by omega, pow_mul, neg_one_sq,
    one_pow]

/-- Scaling an integral full lattice `L` of rank `n` by `√m` (`m ≠ 0`) multiplies its signed
discriminant by `mⁿ`. -/
theorem IsIntegral.signedDiscr_sqrt_smul (h : IsIntegral L) {m : ℕ} (hm : m ≠ 0) :
    signedDiscr (√(m : ℝ) • L) = (m : ℤ) ^ finrank ℝ E * signedDiscr L := by
  rw [signedDiscr_def, signedDiscr_def, h.card_discriminantGroup_sqrt_smul hm]
  push_cast
  ring

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The `ℤ`-span of an orthonormal basis indexed by `ι` has signed discriminant
`(-1) ^ ⌊|ι| / 2⌋`. -/
theorem signedDiscr_span_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    signedDiscr (span ℤ (Set.range b)) = (-1) ^ (Fintype.card ι / 2) := by
  rw [(isUnimodular_span_orthonormalBasis b).signedDiscr_eq_neg_one_pow,
    Module.finrank_eq_card_basis b.toBasis]

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- For an orthonormal basis `b` indexed by `ι` and `m ≠ 0`, the scaled cubic lattice `√m • ℤ b`
has signed discriminant `(-1) ^ ⌊|ι| / 2⌋ * m ^ |ι|`. In particular `√2 • ℤ²` has signed
discriminant `-4`. -/
theorem signedDiscr_sqrt_smul_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {m : ℕ} (hm : m ≠ 0) :
    signedDiscr (√(m : ℝ) • span ℤ (Set.range b)) =
      (-1) ^ (Fintype.card ι / 2) * (m : ℤ) ^ Fintype.card ι := by
  have := b.toBasis.finiteDimensional_of_finite
  have hu := isUnimodular_span_orthonormalBasis b
  rw [← b.coe_toBasis] at hu ⊢
  rw [hu.isIntegral.signedDiscr_sqrt_smul hm, hu.signedDiscr_eq_neg_one_pow,
    Module.finrank_eq_card_basis b.toBasis, mul_comm]

/-- **Fricke partner product identity.** For an integral full lattice `L` of rank `n` and level `N`,
the signed discriminants of `L` and of its Fricke partner `√N • L^∨` multiply to `Nⁿ`. -/
theorem IsIntegral.mul_signedDiscr_sqrt_level_smul_dual (h : IsIntegral L) :
    signedDiscr L * signedDiscr (√(level L : ℝ) • dual L) = (level L : ℤ) ^ finrank ℝ E := by
  have hsign : ((-1 : ℤ) ^ (finrank ℝ E / 2)) * (-1) ^ (finrank ℝ E / 2) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc signedDiscr L * signedDiscr (√(level L : ℝ) • dual L)
      = ((-1 : ℤ) ^ (finrank ℝ E / 2) * (-1) ^ (finrank ℝ E / 2)) *
          ↑(Nat.card (DiscriminantGroup L) *
            Nat.card (DiscriminantGroup (√(level L : ℝ) • dual L))) := by
        rw [signedDiscr_def, signedDiscr_def, Nat.cast_mul]
        ring
    _ = (level L : ℤ) ^ finrank ℝ E := by
        rw [hsign, one_mul, h.mul_card_discriminantGroup_sqrt_level_smul_dual, Nat.cast_pow]

/-- In even ambient dimension, the product of the signed discriminants of an integral full lattice
and of its Fricke partner is an integer square. -/
theorem IsIntegral.isSquare_mul_signedDiscr_sqrt_level_smul_dual (h : IsIntegral L)
    (hE : Even (finrank ℝ E)) :
    IsSquare (signedDiscr L * signedDiscr (√(level L : ℝ) • dual L)) := by
  obtain ⟨k, hk⟩ := hE
  rw [h.mul_signedDiscr_sqrt_level_smul_dual, hk, pow_add]
  exact ⟨(level L : ℤ) ^ k, rfl⟩

/-! ### Comparison with the rational and real models -/

/-- The signed discriminant of an integral full lattice agrees with the signed determinant of its
rational model. -/
theorem IsIntegral.signedDiscr_eq_ratModel (hL : IsIntegral L) :
    signedDiscr L = (-1) ^ (finrank ℤ (ratModel hL) / 2) * (ratModel hL).determinant := by
  rw [finrank_ratModel, hL.determinant_ratModel_eq_card_discriminantGroup, signedDiscr_def]

/-- **Rational square-class bridge.** For any integral full lattice `L` (in even or odd dimension),
the signed discriminant `RegularFormClass.signedDiscr` of the ambient rational quadratic form of
`ratModel hL` is the square class of `signedDiscr L` in `ℚˣ`. -/
theorem IsIntegral.signedDiscr_rationalFormClass_ratModel (hL : IsIntegral L) :
    TauCeti.RegularFormClass.signedDiscr (ratModel hL).rationalFormClass =
      TauCeti.squareClass
        (Units.mk0 (signedDiscr L : ℚ) (by exact_mod_cast hL.signedDiscr_ne_zero)) := by
  have hu : ((-1 : ℚˣ) ^ (finrank ℝ E / 2)) * (ratModel hL).determinantUnit =
      Units.mk0 (signedDiscr L : ℚ) (by exact_mod_cast hL.signedDiscr_ne_zero) := by
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      TauCeti.IntegralLattice.coe_determinantUnit, Units.val_mk0,
      hL.determinant_ratModel_eq_card_discriminantGroup, signedDiscr_def]
    push_cast
    rfl
  rw [TauCeti.IntegralLattice.signedDiscr_rationalFormClass, finrank_ratModel,
    ← TauCeti.squareClass_pow, Nat.neg_one_pow_choose_two, ← TauCeti.squareClass_mul, hu]

/-! ### Level coprimality and the Kronecker character -/

/-- Any natural number coprime to `level L` is coprime to `|signedDiscr L|`. -/
theorem coprime_natAbs_signedDiscr_of_coprime_level {a : ℕ} (ha : a.Coprime (level L)) :
    a.Coprime (signedDiscr L).natAbs := by
  rw [natAbs_signedDiscr]
  exact coprime_card_discriminantGroup_of_coprime_level ha

/-- **Every integer coprime to `level L` is coprime to `signedDiscr L`.** -/
theorem isCoprime_signedDiscr_of_isCoprime_level {d : ℤ} (hd : IsCoprime d (level L)) :
    IsCoprime d (signedDiscr L) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, natAbs_signedDiscr,
    ← Nat.coprime_iff_gcd_eq_one]
  refine coprime_card_discriminantGroup_of_coprime_level ?_
  rw [Nat.coprime_iff_gcd_eq_one, ← Int.natAbs_natCast (level L), ← Int.gcd_eq_natAbs_gcd_natAbs]
  exact Int.isCoprime_iff_gcd_eq_one.mp hd

/-- **The signed discriminant of an even full lattice of even rank is a discriminant**, congruent
to `0` or `1` modulo `4`. -/
theorem IsEven.signedDiscr_modEq_zero_or_one (hL : IsEven L) (hE : Even (finrank ℝ E)) :
    signedDiscr L ≡ 0 [ZMOD 4] ∨ signedDiscr L ≡ 1 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hE
  rw [signedDiscr_of_finrank_eq L (hk.trans (two_mul k).symm)]
  exact hL.neg_one_pow_mul_card_discriminantGroup_modEq_zero_or_one (hk.trans (two_mul k).symm)

/-- **Parity of the Kronecker character of an even lattice.** For an even full lattice `L` of rank
`2k`, the Kronecker character `(D_L / ·)` takes the value `(-1)^k` at `-1`. -/
theorem IsEven.kroneckerChar_signedDiscr_neg_one (R : Type*) [CommRing R] (hL : IsEven L)
    {k : ℕ} (hk : finrank ℝ E = 2 * k) :
    TauCeti.kroneckerChar R (signedDiscr L)
        (hL.signedDiscr_modEq_zero_or_one ⟨k, hk.trans (two_mul k)⟩)
        hL.isIntegral.signedDiscr_ne_zero (-1) = (-1) ^ k := by
  rw [TauCeti.kroneckerChar_neg_one, hL.isIntegral.sign_signedDiscr, hk,
    Nat.mul_div_right k two_pos, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The signed discriminant of `√m • L` (`m ≠ 0`) for an integral full lattice `L` is nonzero. -/
theorem IsIntegral.signedDiscr_sqrt_smul_ne_zero (h : IsIntegral L) {m : ℕ} (hm : m ≠ 0) :
    signedDiscr (√(m : ℝ) • L) ≠ 0 := by
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))⟩
  exact (h.sqrt_smul m).signedDiscr_ne_zero

/-- For an even full lattice `L` of even rank and `m ≠ 0`, `signedDiscr (√m • L)` is congruent to
`0` or `1` modulo `4`. -/
theorem IsEven.signedDiscr_sqrt_smul_modEq_zero_or_one (hL : IsEven L) (hE : Even (finrank ℝ E))
    {m : ℕ} (hm : m ≠ 0) :
    signedDiscr (√(m : ℝ) • L) ≡ 0 [ZMOD 4] ∨ signedDiscr (√(m : ℝ) • L) ≡ 1 [ZMOD 4] := by
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))⟩
  exact (hL.sqrt_smul m).signedDiscr_modEq_zero_or_one hE

/-- In even ambient dimension, scaling an even full lattice `L` by `√m` (`m ≠ 0`) preserves the
conductor of its Kronecker character `(D_L / ·)`. -/
theorem IsEven.conductor_kroneckerChar_signedDiscr_sqrt_smul (R : Type*) [CommRing R]
    (hL : IsEven L) (hE : Even (finrank ℝ E)) {m : ℕ} (hm : m ≠ 0) :
    (TauCeti.kroneckerChar R (signedDiscr (√(m : ℝ) • L))
      (hL.signedDiscr_sqrt_smul_modEq_zero_or_one hE hm)
      (hL.isIntegral.signedDiscr_sqrt_smul_ne_zero hm)).conductor =
      (TauCeti.kroneckerChar R (signedDiscr L)
        (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).conductor := by
  obtain ⟨k, hk⟩ := hE
  refine TauCeti.conductor_kroneckerChar_eq_of_isSquare_mul _ _ _ _ ?_
  rw [hL.isIntegral.signedDiscr_sqrt_smul hm, hk, pow_add]
  exact ⟨(m : ℤ) ^ k * signedDiscr L, by ring⟩

/-- In even ambient dimension, scaling an even full lattice `L` by `√m` (`m ≠ 0`) preserves the
primitive character values of `(D_L / ·)` at every integer `a`. -/
theorem IsEven.primitiveCharacter_kroneckerChar_signedDiscr_sqrt_smul_apply
    (R : Type*) [CommRing R] [Nontrivial R] (hL : IsEven L) (hE : Even (finrank ℝ E))
    {m : ℕ} (hm : m ≠ 0) (a : ℤ) :
    (TauCeti.kroneckerChar R (signedDiscr (√(m : ℝ) • L))
      (hL.signedDiscr_sqrt_smul_modEq_zero_or_one hE hm)
      (hL.isIntegral.signedDiscr_sqrt_smul_ne_zero hm)).primitiveCharacter a =
      (TauCeti.kroneckerChar R (signedDiscr L)
        (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter a := by
  obtain ⟨k, hk⟩ := hE
  refine TauCeti.primitiveCharacter_kroneckerChar_apply_of_isSquare_mul _ _ _ _ ?_ a
  rw [hL.isIntegral.signedDiscr_sqrt_smul hm, hk, pow_add]
  exact ⟨(m : ℤ) ^ k * signedDiscr L, by ring⟩

/-- The signed discriminant of the Fricke partner `√(level L) • L^∨` of an integral full lattice is
nonzero. -/
theorem IsIntegral.signedDiscr_sqrt_level_smul_dual_ne_zero (h : IsIntegral L) :
    signedDiscr (√(level L : ℝ) • dual L) ≠ 0 := by
  have : NeZero √(level L : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr h.level_pos)⟩
  exact isIntegral_sqrt_level_smul_dual.signedDiscr_ne_zero

/-- In even ambient dimension, the signed discriminant of the Fricke partner `√(level L) • L^∨` of
an integral full lattice is congruent to `0` or `1` modulo `4`. -/
theorem IsIntegral.signedDiscr_sqrt_level_smul_dual_modEq_zero_or_one (h : IsIntegral L)
    (hE : Even (finrank ℝ E)) :
    signedDiscr (√(level L : ℝ) • dual L) ≡ 0 [ZMOD 4] ∨
      signedDiscr (√(level L : ℝ) • dual L) ≡ 1 [ZMOD 4] := by
  have : NeZero √(level L : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr h.level_pos)⟩
  exact (isEven_sqrt_level_smul_dual L).signedDiscr_modEq_zero_or_one hE

/-- **Fricke invariance of the Kronecker conductor.** For an even full lattice `L` of even rank and
level `N`, the Kronecker characters of `L` and of its Fricke partner `√N • L^∨` have the same
conductor. -/
theorem IsEven.conductor_kroneckerChar_signedDiscr_sqrt_level_smul_dual (R : Type*) [CommRing R]
    (hL : IsEven L) (hE : Even (finrank ℝ E)) :
    (TauCeti.kroneckerChar R (signedDiscr (√(level L : ℝ) • dual L))
      (hL.isIntegral.signedDiscr_sqrt_level_smul_dual_modEq_zero_or_one hE)
      hL.isIntegral.signedDiscr_sqrt_level_smul_dual_ne_zero).conductor =
      (TauCeti.kroneckerChar R (signedDiscr L)
        (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).conductor :=
  (TauCeti.conductor_kroneckerChar_eq_of_isSquare_mul _ _ _ _
    (hL.isIntegral.isSquare_mul_signedDiscr_sqrt_level_smul_dual hE)).symm

/-- **Fricke invariance of the primitive Kronecker character.** For an even full lattice `L` of even
rank and level `N`, the primitive Kronecker characters of `L` and of its Fricke partner `√N • L^∨`
agree at every integer `a`. -/
theorem IsEven.primitiveCharacter_kroneckerChar_signedDiscr_sqrt_level_smul_dual_apply
    (R : Type*) [CommRing R] [Nontrivial R] (hL : IsEven L) (hE : Even (finrank ℝ E)) (a : ℤ) :
    (TauCeti.kroneckerChar R (signedDiscr (√(level L : ℝ) • dual L))
      (hL.isIntegral.signedDiscr_sqrt_level_smul_dual_modEq_zero_or_one hE)
      hL.isIntegral.signedDiscr_sqrt_level_smul_dual_ne_zero).primitiveCharacter a =
      (TauCeti.kroneckerChar R (signedDiscr L)
        (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter a :=
  (TauCeti.primitiveCharacter_kroneckerChar_apply_of_isSquare_mul _ _ _ _
    (hL.isIntegral.isSquare_mul_signedDiscr_sqrt_level_smul_dual hE) a).symm

end FullLattice

/-! ### Non-integral rank-one boundary examples -/

section NonIntegralBoundary

/-- When `c²` is irrational, `signedDiscr (c ℤ) = 0`. -/
theorem signedDiscr_span_singleton_of_irrational_sq {c : ℝ} (hc : Irrational (c ^ 2)) :
    signedDiscr (span ℤ {c} : Submodule ℤ ℝ) = 0 :=
  signedDiscr_eq_zero_iff.mpr (infinite_discriminantGroup_span_singleton_of_irrational_sq hc)

/-- **Non-integral boundary check:** `L = 2 ^ (1 / 4) ℤ ⊆ ℝ` meets its dual `2 ^ (-1 / 4) ℤ` only
at `0`. -/
theorem inf_dual_span_two_rpow_one_quarter :
    (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)} : Submodule ℤ ℝ) ⊓
      dual (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)}) = ⊥ :=
  inf_dual_span_singleton_eq_bot_of_irrational_sq TauCeti.irrational_two_rpow_one_quarter_sq

/-- **Non-integral boundary check:** `L = 2 ^ (1 / 4) ℤ ⊆ ℝ` has infinite discriminant group. -/
theorem infinite_discriminantGroup_span_two_rpow_one_quarter :
    Infinite (DiscriminantGroup (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)} : Submodule ℤ ℝ)) :=
  infinite_discriminantGroup_span_singleton_of_irrational_sq
    TauCeti.irrational_two_rpow_one_quarter_sq

/-- **Non-integral boundary check:** for `L = 2 ^ (1 / 4) ℤ ⊆ ℝ` and every `a : ℝ`, the quotient
`L^∨ ⧸ (L^∨ ∩ a L^∨ ∩ L)` is infinite. -/
theorem infinite_quotient_smul_dual_inf_span_two_rpow_one_quarter (a : ℝ) :
    Infinite (dual (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)} : Submodule ℤ ℝ) ⧸
      ((a • dual (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)})) ⊓
        span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)}).submoduleOf
        (dual (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)}))) :=
  infinite_quotient_smul_dual_inf_of_irrational_sq TauCeti.irrational_two_rpow_one_quarter_sq a

/-- **Non-integral boundary check:** `L = 2 ^ (1 / 4) ℤ ⊆ ℝ` has `signedDiscr L = 0`. -/
theorem signedDiscr_span_two_rpow_one_quarter :
    signedDiscr (span ℤ {(2 : ℝ) ^ ((1 : ℝ) / 4)} : Submodule ℤ ℝ) = 0 :=
  signedDiscr_span_singleton_of_irrational_sq TauCeti.irrational_two_rpow_one_quarter_sq

end NonIntegralBoundary

end ZLattice

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The signed discriminant of the real model of a positive definite rational lattice `M` is
`(-1) ^ ⌊finrank ℤ M / 2⌋ * M.determinant`. -/
@[simp]
theorem signedDiscr_realModel (M : IntegralLattice V) (hM : M.IsPosDef) :
    ZLattice.signedDiscr (M.realModel hM) = (-1) ^ (Module.finrank ℤ M / 2) * M.determinant := by
  rw [ZLattice.signedDiscr_def, RealModelSpace.finrank_eq, M.natCard_discriminantGroup_realModel hM,
    hM.determinant_eq_card_discriminantGroup]

end TauCeti.IntegralLattice
