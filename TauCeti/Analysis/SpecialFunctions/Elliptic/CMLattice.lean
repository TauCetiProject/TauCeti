/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.QuadraticOrder.ComplexEmbedding
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Pair
import TauCeti.Analysis.SpecialFunctions.Elliptic.Torsion

/-!
# Normalised pointed lattices and CM lattices

Let `d` be a natural number and `ω = (1 + √-d) / 2 ∈ ℂ` (`TauCeti.cmOmega d`), with
`√-d = i √d`; for `d ≡ 3 mod 4`, `ℤ[ω] = ℤ + ℤ ω` is the order of discriminant `-d` of
`K = ℚ(√-d)`, its ring of integers when `d` is squarefree. This file sets up the
lattices with complex multiplication by `ℤ[ω]` that carry a marked point of order two and are
scaled at that point, as used in the theory of the theta functions of CM elliptic curves.

* A *normalised pointed lattice* `(Λ, t, a₁)` (`PeriodPair.IsNormalizedPointed`) is a lattice `Λ`,
  a point `t` of order two (`t ∉ Λ`, `2 t ∈ Λ`) and `a₁ ∈ ℂ` with `g₂(Λ) = 12 ℘(t)² - 4` and
  `a₁² = 12 ℘(t)`. Since `℘'' = 6 ℘² - g₂ / 2`, the first condition says `℘''(t) = 2`.
* A *CM point* `t` of `Λ` (`PeriodPair.IsCMPoint`) is a point of order two of a lattice stable
  under `ω` such that neither `ω t` nor `conj(ω) t` lies in `Λ`: for `d ≡ 7 mod 8` the prime `2`
  splits in `K`, and `t` is the point of order two that neither prime above `2` annihilates.
* A *CM lattice* (`PeriodPair.IsCMLattice`) is a normalised pointed lattice whose point is a
  CM point.

All three conditions depend only on the lattice of the period pair
(`PeriodPair.IsCMLattice.of_lattice_eq`).

## Main results

* `PeriodPair.exists_isCMPoint`: every lattice stable under `ω` has a CM point.
* `PeriodPair.IsCMPoint.sub_mem_lattice`: for `d ≡ 7 mod 8`, a CM point is unique modulo the
  lattice; CM points exist only for `d ≡ 3 mod 4`
  (`PeriodPair.mod_four_eq_three_of_cmOmega_mul_mem`).
* `PeriodPair.IsCMPoint.g₂_ne_twelve_mul_weierstrassP_sq`: at a CM point `℘''(t) ≠ 0`, in the
  form `g₂ ≠ 12 ℘(t)²`.
* `PeriodPair.exists_isCMLattice_smul`: every lattice stable under `ω` has a complex multiple that
  is the lattice of a CM lattice; in particular CM lattices exist for every `d ≡ 3 mod 4`
  (`PeriodPair.exists_isCMLattice`).
* `PeriodPair.IsCMLattice.pow_four_eq_one`: for `d ≡ 7 mod 8`, if `c Λ_C = Λ_D` for two CM
  lattices `C` and `D`, then `c⁴ = 1`.
* `PeriodPair.complexOrder_le_leftOrder_of_cmOmega_mul_mem`: a lattice stable under `ω` is a
  module over the embedded quadratic order `TauCeti.QuadraticOrder.complexOrder (-d)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1.
* The normalisation at a point of order two follows the files `src/Lib/CM/GoodReduction.lean`
  and `src/Lib/CM/FiniteLattices.lean` of grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic PBC), declarations `New.CMLattice`,
  `New.QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal` and
  `New.CMLattice.pow_four_eq_one_of_mul_mem_iff`; the statements and proofs here are written
  independently.
-/

public section

noncomputable section

open Complex

namespace TauCeti

/-- The number `ω = (1 + √-d) / 2 ∈ ℂ`, with `√-d = i √d`. For `d ≡ 3 mod 4` it generates the
order of discriminant `-d` of `ℚ(√-d)` over `ℤ` (`TauCeti.cmOmega_eq_complexGenerator_add`), the
ring of integers when `d` is squarefree. -/
def cmOmega (d : ℕ) : ℂ := (1 + (√(d : ℝ) : ℂ) * I) / 2

variable {d : ℕ}

/-- The defining complex expression for `ω`. -/
theorem cmOmega_def : cmOmega d = (1 + (√(d : ℝ) : ℂ) * I) / 2 := (rfl)

/-- The real part of `ω` is `1 / 2`. -/
@[simp] theorem re_cmOmega : (cmOmega d).re = 1 / 2 := by
  simp [cmOmega]

/-- The imaginary part of `ω` is `√d / 2`. -/
@[simp] theorem im_cmOmega : (cmOmega d).im = √(d : ℝ) / 2 := by
  simp [cmOmega]

/-- `ω + conj(ω) = 1`. -/
theorem cmOmega_add_conj : cmOmega d + (starRingEnd ℂ) (cmOmega d) = 1 := by
  apply Complex.ext <;> norm_num

/-- `ω conj(ω) = (d + 1) / 4`. -/
theorem cmOmega_mul_conj : cmOmega d * (starRingEnd ℂ) (cmOmega d) = ((d : ℂ) + 1) / 4 := by
  have hs : ((√(d : ℝ) : ℝ) : ℂ) ^ 2 = d := by
    rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), ofReal_natCast]
  have hc : (starRingEnd ℂ) (cmOmega d) = (1 - (√(d : ℝ) : ℂ) * I) / 2 := by
    simp [cmOmega, map_div₀, map_ofNat, sub_eq_add_neg]
  rw [hc, cmOmega]
  linear_combination hs / 4 - ((√(d : ℝ) : ℂ) ^ 2 / 4) * I_sq

/-- `ω` is a root of `X² - X + (d + 1) / 4`. -/
theorem cmOmega_sq : cmOmega d ^ 2 = cmOmega d - ((d : ℂ) + 1) / 4 := by
  rw [← cmOmega_mul_conj]
  linear_combination cmOmega d * (cmOmega_add_conj (d := d))

/-- `ω = (-d + √-d) / 2 + (d + 1) / 2`: up to an integer when `d` is odd, `ω` is the generator
`TauCeti.QuadraticOrder.complexGenerator (-d)` of the embedded quadratic order. -/
theorem cmOmega_eq_complexGenerator_add :
    cmOmega d = QuadraticOrder.complexGenerator (-d) + ((d : ℂ) + 1) / 2 := by
  rw [cmOmega, QuadraticOrder.complexGenerator_def]
  push_cast
  rw [neg_neg]
  ring

end TauCeti

namespace PeriodPair

open TauCeti

variable (L : PeriodPair) {d : ℕ} {t a₁ : ℂ}

/-- `(L, t, a₁)` is a **normalised pointed lattice**: `t` is a point of order two of the lattice
`Λ` of `L`, scaled so that `g₂(Λ) = 12 ℘(t)² - 4` (that is, `℘''(t) = 2`), and
`a₁² = 12 ℘(t)`. -/
structure IsNormalizedPointed (t a₁ : ℂ) : Prop where
  notMem : t ∉ L.lattice
  two_mul_mem : 2 * t ∈ L.lattice
  g₂_eq : L.g₂ = 12 * ℘[L] t ^ 2 - 4
  a₁_sq : a₁ ^ 2 = 12 * ℘[L] t

/-- `t` is a **CM point** of the lattice `Λ` of `L` for `ω = (1 + √-d) / 2`: the lattice is stable
under multiplication by `ω`, `2 t ∈ Λ`, and neither `ω t` nor `conj(ω) t` lies in `Λ`. For
`d ≡ 7 mod 8` such a point is unique modulo `Λ` (`PeriodPair.IsCMPoint.sub_mem_lattice`). -/
structure IsCMPoint (d : ℕ) (t : ℂ) : Prop where
  cmOmega_mul_mem {l : ℂ} : l ∈ L.lattice → cmOmega d * l ∈ L.lattice
  two_mul_mem : 2 * t ∈ L.lattice
  cmOmega_mul_notMem : cmOmega d * t ∉ L.lattice
  conj_cmOmega_mul_notMem : (starRingEnd ℂ) (cmOmega d) * t ∉ L.lattice

/-- `(L, t, a₁)` is a **CM lattice** for `ω = (1 + √-d) / 2`: a normalised pointed lattice whose
point `t` is a CM point. -/
structure IsCMLattice (d : ℕ) (t a₁ : ℂ) : Prop where
  isNormalizedPointed : L.IsNormalizedPointed t a₁
  isCMPoint : L.IsCMPoint d t

variable {L}

/-! ### Dependence on the lattice only -/

/-- Being a normalised pointed lattice depends only on the lattice of the period pair. -/
theorem IsNormalizedPointed.of_lattice_eq {L' : PeriodPair} (h : L.IsNormalizedPointed t a₁)
    (hL : L.lattice = L'.lattice) : L'.IsNormalizedPointed t a₁ where
  notMem := hL ▸ h.notMem
  two_mul_mem := hL ▸ h.two_mul_mem
  g₂_eq := by rw [g₂, ← G_eq_of_lattice_eq hL, ← weierstrassP_eq_of_lattice_eq hL]; exact h.g₂_eq
  a₁_sq := by rw [← weierstrassP_eq_of_lattice_eq hL]; exact h.a₁_sq

/-- Being a CM point depends only on the lattice of the period pair. -/
theorem IsCMPoint.of_lattice_eq {L' : PeriodPair} (h : L.IsCMPoint d t)
    (hL : L.lattice = L'.lattice) : L'.IsCMPoint d t where
  cmOmega_mul_mem hl := hL ▸ h.cmOmega_mul_mem (hL ▸ hl)
  two_mul_mem := hL ▸ h.two_mul_mem
  cmOmega_mul_notMem := hL ▸ h.cmOmega_mul_notMem
  conj_cmOmega_mul_notMem := hL ▸ h.conj_cmOmega_mul_notMem

/-- Being a CM lattice depends only on the lattice of the period pair. -/
theorem IsCMLattice.of_lattice_eq {L' : PeriodPair} (h : L.IsCMLattice d t a₁)
    (hL : L.lattice = L'.lattice) : L'.IsCMLattice d t a₁ :=
  ⟨h.isNormalizedPointed.of_lattice_eq hL, h.isCMPoint.of_lattice_eq hL⟩

/-! ### Arithmetic of `ω` on the points of order two -/

/-- A lattice stable under `ω` is stable under `conj(ω) = 1 - ω`. -/
private theorem conj_cmOmega_mul_mem_of_forall (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice)
    {l : ℂ} (hl : l ∈ L.lattice) : (starRingEnd ℂ) (cmOmega d) * l ∈ L.lattice := by
  convert sub_mem hl (hL l hl) using 1
  linear_combination l * (cmOmega_add_conj (d := d))

/-- If a lattice is stable under `ω`, then `ω` is an algebraic integer, so
`ω conj(ω) = (d + 1) / 4` is an integer `n` and `d ≡ 3 mod 4`. -/
private theorem exists_natCast_eq_cmOmega_mul_conj
    (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice) :
    ∃ n : ℕ, (n : ℂ) = cmOmega d * (starRingEnd ℂ) (cmOmega d) ∧ 4 * n = d + 1 := by
  have hω : IsIntegral ℤ (cmOmega d) :=
    L.isIntegral_of_mem_leftOrder_lattice (Submodule.mem_leftOrder_iff.mpr hL)
  have hω' : IsIntegral ℤ ((starRingEnd ℂ) (cmOmega d)) :=
    L.isIntegral_of_mem_leftOrder_lattice
      (Submodule.mem_leftOrder_iff.mpr fun _ ↦ conj_cmOmega_mul_mem_of_forall hL)
  have hq : IsIntegral ℤ ((((d + 1 : ℕ) / 4 : ℚ)) : ℂ) := by
    have := hω.mul hω'
    rw [cmOmega_mul_conj] at this
    simpa using this
  rw [isIntegral_ratCast_iff, IsIntegrallyClosed.isIntegral_iff (R := ℤ)] at hq
  obtain ⟨n, hn⟩ := hq
  simp only [eq_intCast] at hn
  have h4 : (4 * n : ℚ) = d + 1 := by rw [hn]; push_cast; ring
  norm_cast at h4
  lift n to ℕ using by omega
  refine ⟨n, ?_, by omega⟩
  rw [cmOmega_mul_conj]
  have h4' : (4 * n : ℂ) = d + 1 := by exact_mod_cast h4
  linear_combination h4' / 4

/-- A lattice stable under `ω` forces `d ≡ 3 mod 4`: the multiplier `ω` is an algebraic
integer, so `ω conj(ω) = (d + 1) / 4` is an integer. -/
theorem mod_four_eq_three_of_cmOmega_mul_mem
    (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice) : d % 4 = 3 := by
  obtain ⟨n, -, h4⟩ := exists_natCast_eq_cmOmega_mul_conj hL
  omega

namespace IsCMPoint

variable (h : L.IsCMPoint d t)
include h

/-- The lattice of a CM point is stable under `conj(ω) = 1 - ω`. -/
theorem conj_cmOmega_mul_mem {l : ℂ} (hl : l ∈ L.lattice) :
    (starRingEnd ℂ) (cmOmega d) * l ∈ L.lattice :=
  conj_cmOmega_mul_mem_of_forall (fun _ ↦ h.cmOmega_mul_mem) hl

/-- A CM point lies outside the lattice. -/
theorem notMem : t ∉ L.lattice := fun ht ↦ h.cmOmega_mul_notMem (h.cmOmega_mul_mem ht)

end IsCMPoint

/-- If `ω conj(ω) = (d + 1) / 4` is even, it kills every half-period of a lattice. -/
private theorem cmOmega_mul_conj_mul_mem_of_even {n : ℕ}
    (hn : (n : ℂ) = cmOmega d * (starRingEnd ℂ) (cmOmega d)) (he : Even n) {z : ℂ}
    (hz : 2 * z ∈ L.lattice) : cmOmega d * ((starRingEnd ℂ) (cmOmega d) * z) ∈ L.lattice := by
  obtain ⟨m, rfl⟩ := he
  rw [← mul_assoc, ← hn]
  convert L.lattice.smul_mem (m : ℤ) hz using 1
  rw [zsmul_eq_mul]
  push_cast
  ring

/-- If a lattice is stable under `ω` and `ω conj(ω)` is even, then on a half-period `z` the
endomorphism `ω` is idempotent: `ω (ω z) - ω z ∈ Λ`. -/
private theorem cmOmega_mul_cmOmega_mul_sub_mem_of_even {n : ℕ}
    (hn : (n : ℂ) = cmOmega d * (starRingEnd ℂ) (cmOmega d)) (he : Even n) {z : ℂ}
    (hz : 2 * z ∈ L.lattice) : cmOmega d * (cmOmega d * z) - cmOmega d * z ∈ L.lattice := by
  convert neg_mem (cmOmega_mul_conj_mul_mem_of_even hn he hz) using 1
  linear_combination cmOmega d * z * (cmOmega_add_conj (d := d))

/-- The same for `conj(ω)`: `conj(ω) (conj(ω) z) - conj(ω) z ∈ Λ`. -/
private theorem conj_cmOmega_mul_conj_cmOmega_mul_sub_mem_of_even {n : ℕ}
    (hn : (n : ℂ) = cmOmega d * (starRingEnd ℂ) (cmOmega d)) (he : Even n) {z : ℂ}
    (hz : 2 * z ∈ L.lattice) :
    (starRingEnd ℂ) (cmOmega d) * ((starRingEnd ℂ) (cmOmega d) * z) -
      (starRingEnd ℂ) (cmOmega d) * z ∈ L.lattice := by
  convert neg_mem (cmOmega_mul_conj_mul_mem_of_even hn he hz) using 1
  linear_combination (starRingEnd ℂ) (cmOmega d) * z * (cmOmega_add_conj (d := d))

/-! ### Existence and uniqueness of the CM point -/

/-- **Existence of the CM point.** Every lattice stable under `ω = (1 + √-d) / 2` has a point of
order two that neither `ω` nor `conj(ω)` sends into the lattice. -/
theorem exists_isCMPoint (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice) :
    ∃ t, L.IsCMPoint d t := by
  have hω'L {l : ℂ} (hl : l ∈ L.lattice) : (starRingEnd ℂ) (cmOmega d) * l ∈ L.lattice :=
    conj_cmOmega_mul_mem_of_forall hL hl
  obtain ⟨x, hx, hωx⟩ := L.exists_two_mul_mem_mul_notMem (cmOmega_add_conj (d := d))
  obtain ⟨n, hn, -⟩ := exists_natCast_eq_cmOmega_mul_conj hL
  rcases Nat.even_or_odd n with he | ho
  · -- `d ≡ 7 mod 8`: `ω` is idempotent on half-periods; take `t = ω x + conj(ω) y`
    obtain ⟨y, hy, hω'y⟩ := L.exists_two_mul_mem_mul_notMem (α := (starRingEnd ℂ) (cmOmega d))
      (by rw [Complex.conj_conj, add_comm]; exact cmOmega_add_conj)
    have h2t : 2 * (cmOmega d * x + (starRingEnd ℂ) (cmOmega d) * y) ∈ L.lattice := by
      convert add_mem (hL _ hx) (hω'L hy) using 1
      ring
    refine ⟨cmOmega d * x + (starRingEnd ℂ) (cmOmega d) * y,
      ⟨hL _, h2t, fun h ↦ hωx ?_, fun h ↦ hω'y ?_⟩⟩
    · have := sub_mem h (add_mem (cmOmega_mul_cmOmega_mul_sub_mem_of_even hn he hx)
        (cmOmega_mul_conj_mul_mem_of_even hn he hy))
      convert this using 1
      ring
    · have h₁ := cmOmega_mul_conj_mul_mem_of_even hn he hx
      have := sub_mem h (add_mem (by rwa [mul_left_comm] at h₁)
        (conj_cmOmega_mul_conj_cmOmega_mul_sub_mem_of_even hn he hy))
      convert this using 1
      ring
  · -- `d ≡ 3 mod 8`: `ω conj(ω) = 2 m + 1` is odd, so a half-period killed by `conj(ω)` is
    -- killed by `ω conj(ω) - 2 m = 1`
    obtain ⟨m, rfl⟩ := ho
    refine ⟨x, ⟨hL _, hx, hωx, fun h ↦ hωx (hL _ ?_)⟩⟩
    convert sub_mem (hL _ h) (L.lattice.smul_mem (m : ℤ) hx) using 1
    rw [zsmul_eq_mul, ← mul_assoc, ← hn]
    push_cast
    ring

/-- **Uniqueness of the CM point.** For `d ≡ 7 mod 8`, two CM points of the same lattice are
congruent modulo the lattice. -/
theorem IsCMPoint.sub_mem_lattice (hd : d % 8 = 7) {t' : ℂ} (h : L.IsCMPoint d t)
    (h' : L.IsCMPoint d t') : t - t' ∈ L.lattice := by
  obtain ⟨n, hn, h4⟩ := exists_natCast_eq_cmOmega_mul_conj fun _ ↦ h.cmOmega_mul_mem
  have he : Even n := by rw [Nat.even_iff]; omega
  have hω₁ : cmOmega d + (starRingEnd ℂ) (cmOmega d) = 1 := cmOmega_add_conj
  by_contra hs
  have hx : 2 * (cmOmega d * t) ∈ L.lattice := by
    convert h.cmOmega_mul_mem h.two_mul_mem using 1
    ring
  rcases L.mem_lattice_or_sub_mem_lattice_of_two_mul_mem hx h.two_mul_mem h'.two_mul_mem
      h.notMem h'.notMem hs with h₀ | h₁ | h₂ | h₃
  · exact h.cmOmega_mul_notMem h₀
  · -- `ω t ≡ t` gives `conj(ω) t ∈ Λ`
    refine h.conj_cmOmega_mul_notMem ?_
    convert neg_mem h₁ using 1
    linear_combination t * hω₁
  · -- `ω t ≡ t'` gives `ω t' ≡ ω² t ≡ ω t ≡ t'`, so `conj(ω) t' ∈ Λ`
    refine h'.conj_cmOmega_mul_notMem ?_
    convert sub_mem (sub_mem (h.cmOmega_mul_mem h₂)
      (cmOmega_mul_cmOmega_mul_sub_mem_of_even hn he h.two_mul_mem)) h₂ using 1
    linear_combination t' * hω₁
  · -- `conj(ω) t ≡ t'` gives `conj(ω) t' ≡ conj(ω)² t ≡ conj(ω) t ≡ t'`, so `ω t' ∈ Λ`
    refine h'.cmOmega_mul_notMem ?_
    have h₃' : t' - (starRingEnd ℂ) (cmOmega d) * t ∈ L.lattice := by
      convert h₃ using 1
      linear_combination -t * hω₁
    convert neg_mem (sub_mem (add_mem (h.conj_cmOmega_mul_mem h₃')
      (conj_cmOmega_mul_conj_cmOmega_mul_sub_mem_of_even hn he h.two_mul_mem)) h₃') using 1
    linear_combination t' * hω₁

/-! ### Scaling -/

/-- Rescaling a lattice by `c` carries its CM points to CM points. -/
theorem IsCMPoint.smul (h : L.IsCMPoint d t) (c : ℂˣ) : (c • L).IsCMPoint d (c * t) where
  cmOmega_mul_mem {l} hl := by
    rw [lattice_smul, Submodule.mem_map] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    rw [LinearMap.mulLeft_apply, mul_left_comm, mul_mem_lattice_smul_iff]
    exact h.cmOmega_mul_mem hl₀
  two_mul_mem := by
    rw [mul_left_comm, mul_mem_lattice_smul_iff]
    exact h.two_mul_mem
  cmOmega_mul_notMem := by
    rw [mul_left_comm, mul_mem_lattice_smul_iff]
    exact h.cmOmega_mul_notMem
  conj_cmOmega_mul_notMem := by
    rw [mul_left_comm, mul_mem_lattice_smul_iff]
    exact h.conj_cmOmega_mul_notMem

/-- **`℘''` does not vanish at a CM point**, in the form `g₂ ≠ 12 ℘(t)²` (recall
`℘'' = 6 ℘² - g₂ / 2`). The associated point on the Weierstrass curve is nonsingular and
has zero `y`-coordinate, so the partial derivative in `x` cannot vanish. -/
theorem IsCMPoint.g₂_ne_twelve_mul_weierstrassP_sq (h : L.IsCMPoint d t) :
    L.g₂ ≠ 12 * ℘[L] t ^ 2 := by
  have hns := (WeierstrassCurve.Affine.nonsingular_iff _ _).mp (L.nonsingular_weierstrassP h.notMem)
  have hd := (L.derivWeierstrassP_eq_zero_iff t).mpr h.two_mul_mem
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    weierstrassCurve_a₄, hd] at hns
  rcases hns.2 with hx | hy
  · intro hg
    exact hx (by rw [hg]; ring)
  · exact False.elim (hy (by ring))

/-! ### Normalised multiples and the rigidity of the scaling -/

/-- **Every lattice stable under `ω` has a normalised multiple**: some `c • L` carries a point `t`
and a number `a₁` making it a CM lattice. -/
theorem exists_isCMLattice_smul (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice) :
    ∃ (c : ℂˣ) (t a₁ : ℂ), (c • L).IsCMLattice d t a₁ := by
  obtain ⟨t₀, ht₀⟩ := L.exists_isCMPoint hL
  set e := 12 * ℘[L] t₀ ^ 2 - L.g₂
  have he : e ≠ 0 := sub_ne_zero.mpr ht₀.g₂_ne_twelve_mul_weierstrassP_sq.symm
  set c₀ := (e / 4) ^ ((4 : ℕ)⁻¹ : ℂ)
  have hc₀ : c₀ ^ 4 = e / 4 := cpow_nat_inv_pow _ four_ne_zero
  have hc₀0 : c₀ ≠ 0 := by
    rintro h0
    rw [h0, zero_pow four_ne_zero] at hc₀
    exact he (by linear_combination -4 * hc₀)
  set c := Units.mk0 c₀ hc₀0
  have hct : (c • L).IsCMPoint d (c * t₀) := ht₀.smul c
  refine ⟨c, c * t₀, (12 * ℘[c • L] (c * t₀)) ^ ((2 : ℕ)⁻¹ : ℂ), ⟨⟨hct.notMem, hct.two_mul_mem,
    ?_, cpow_nat_inv_pow _ two_ne_zero⟩, hct⟩⟩
  rw [g₂_smul, weierstrassP_smul, Units.val_mk0]
  field_simp
  linear_combination 4 * hc₀

/-- **CM lattices exist** for every `d ≡ 3 mod 4`: the lattice `ℤ ω + ℤ` is stable under `ω`, and
has a normalised multiple. -/
theorem exists_isCMLattice (hd : d % 4 = 3) :
    ∃ (L : PeriodPair) (t a₁ : ℂ), L.IsCMLattice d t a₁ := by
  have him : 0 < (cmOmega d).im := by
    rw [im_cmOmega]
    exact div_pos (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))) two_pos
  set τ : UpperHalfPlane := ⟨cmOmega d, him⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hsq : cmOmega d * cmOmega d = cmOmega d - k := by
    rw [← sq, cmOmega_sq]
    have : ((d : ℂ) + 1) = 4 * k := by exact_mod_cast hk
    rw [this]
    ring
  obtain ⟨c, t, a₁, h⟩ := τ.periodPair.exists_isCMLattice_smul (d := d) fun l hl ↦ by
    obtain ⟨m, n, rfl⟩ := mem_lattice.mp hl
    refine mem_lattice.mpr ⟨m + n, -(m * k), ?_⟩
    simp only [UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂, τ]
    push_cast
    linear_combination (-(m : ℂ)) * hsq
  exact ⟨_, t, a₁, h⟩

/-- **The scaling of a CM lattice is rigid.** For `d ≡ 7 mod 8`, if `c Λ_C = Λ_D` for CM lattices
`C = (L, t, a₁)` and `D = (L', t', a₁')`, then `c⁴ = 1`: multiplication by `c` carries the CM point
of `C` to that of `D` modulo `Λ_D`, and the normalisation `℘''(t) = 2` scales by `c⁻⁴`. -/
theorem IsCMLattice.pow_four_eq_one (hd : d % 8 = 7) {L' : PeriodPair} {t' a₁' : ℂ}
    (hC : L.IsCMLattice d t a₁) (hD : L'.IsCMLattice d t' a₁') {c : ℂˣ}
    (hc : (c • L).lattice = L'.lattice) : (c : ℂ) ^ 4 = 1 := by
  have hct : L'.IsCMPoint d (c * t) := (hC.isCMPoint.smul c).of_lattice_eq hc
  have hsub : c * t - t' ∈ L'.lattice := hct.sub_mem_lattice hd hD.isCMPoint
  have h℘ : ℘[L'] t' = ℘[L] t / (c : ℂ) ^ 2 := by
    -- Subtract the lattice element `c * t - t'` to apply periodicity at `c * t`.
    rw [show t' = c * t - (c * t - t') by ring, L'.weierstrassP_sub_coe _ ⟨_, hsub⟩,
      ← weierstrassP_eq_of_lattice_eq hc, weierstrassP_smul]
  have hg : L'.g₂ = L.g₂ / (c : ℂ) ^ 4 := by
    rw [← g₂_smul, g₂, g₂, G_eq_of_lattice_eq hc]
  have h₁ := hC.isNormalizedPointed.g₂_eq
  have h₂ := hD.isNormalizedPointed.g₂_eq
  rw [hg, h℘, h₁] at h₂
  have hc0 : (c : ℂ) ≠ 0 := c.ne_zero
  field_simp at h₂
  linear_combination h₂ / 4

/-- A lattice stable under `ω` is a module over the embedded quadratic order
`ℤ[(-d + √-d) / 2] = ℤ[ω]` of discriminant `-d` (where `d ≡ 3 mod 4` holds automatically). -/
theorem complexOrder_le_leftOrder_of_cmOmega_mul_mem
    (hL : ∀ l ∈ L.lattice, cmOmega d * l ∈ L.lattice)
    (hD : (-d : ℤ) % 4 = 0 ∨ (-d : ℤ) % 4 = 1) :
    QuadraticOrder.complexOrder (-d) (by simp) hD ≤ L.lattice.leftOrder := by
  intro x hx
  rw [Submodule.mem_leftOrder_iff]
  intro l hl
  obtain ⟨m, k, rfl⟩ := (QuadraticOrder.mem_complexOrder_iff _ _ _).mp hx
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d + 1 = 2 * j :=
    ⟨(d + 1) / 2, by have := mod_four_eq_three_of_cmOmega_mul_mem hL; omega⟩
  have hg : QuadraticOrder.complexGenerator (-d) = cmOmega d - j := by
    rw [cmOmega_eq_complexGenerator_add]
    have : ((d : ℂ) + 1) = 2 * j := by exact_mod_cast hj
    rw [this]
    ring
  rw [hg]
  convert add_mem (L.lattice.smul_mem (m - k * j : ℤ) hl)
    (L.lattice.smul_mem k (hL l hl)) using 1
  rw [zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

end PeriodPair
