/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.HilbertClassPolynomial
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ComplexLattice
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.RingClassField
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Complex multiplication of period lattices and singular moduli

Let `n > 0` with `-n ≡ 0, 1 mod 4`, and let `O_{-n} = QuadraticOrder.complexOrder (-n)` be the
imaginary quadratic order of discriminant `-n` embedded in `ℂ`. This file proves the complex-lattice
dictionary of complex multiplication connecting binary quadratic forms, period lattices, singular
moduli, Picard groups, and ring class fields:

1. **Exact multiplier orders of form roots**: for every positive definite form `f ∈ posDef n`, the
   left order of `(root f).periodPair.lattice = ℤ · root f + ℤ` is the embedded quadratic order of
   discriminant `f.primPart.discrim` (`leftOrder_periodPair_root_eq_complexOrder_primPart`); in
   particular it equals `O_{-n}` if and only if `f` is primitive
   (`leftOrder_periodPair_root_eq_complexOrder_iff_isPrimitive`). Conversely, a point `τ ∈ ℍ` has
   `(ℤ τ + ℤ).leftOrder = O_{-n}` if and only if `τ = root f` for a primitive positive definite form
   `f` of discriminant `-n` (`leftOrder_lattice_periodPair_eq_complexOrder_iff`).
2. **Homothety classes, Picard group, and ring class Galois group**: sending a proper class `[f]` to
   the homothety class `PeriodPair.HomothetyClass.mk (root f).periodPair` identifies
   `PosDefProperClass n`, `Pic (QuadraticOrder.numberFieldOrder (-n))`, and `Gal(H_O / K)` with the
   homothety classes of complex lattices whose left order is `O_{-n}`
   (`cmHomothetyClassEquivPosDefProperClass`, `cmHomothetyClassEquivPic`,
   `cmHomothetyClassEquivGal`). Under `PeriodPair.HomothetyClass.j`, these classes map bijectively
   onto the roots of `hilbertClassPolynomial n`
   (`PeriodPair.HomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`), and a
   complex elliptic curve `E` has `E.periodLattice.leftOrder = O_{-n}` if and only if `E.j` is a
   root of `hilbertClassPolynomial n`
   (`WeierstrassCurve.leftOrder_periodLattice_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`).
3. **Uniqueness of the CM order from a singular modulus**: because `j` separates homothety classes
   and `complexOrder D` determines `D`, a singular modulus uniquely determines the discriminant of
   its CM order (`eq_of_singularModulus_eq`, `eq_of_isRoot_hilbertClassPolynomial`), so Hilbert
   class polynomials of distinct discriminants are coprime in `ℂ[X]`
   (`isCoprime_hilbertClassPolynomial_of_ne`).
4. **Canonical CM points `τ_D` and conductor-`f` points `f τ_D`**: for `D < 0` with
   `D ≡ 0, 1 mod 4`, `cmPoint D` (`i √(-D) / 2` when `D ≡ 0 mod 4`, `(3 + i √(-D)) / 2` when
   `D ≡ 1 mod 4`) satisfies the monic quadratic `τ_D² + B τ_D + C = 0` with `B ∈ {0, -3}`
   (`cmPoint_quadratic`), spans the lattice `complexOrder D` (`lattice_periodPair_cmPoint`), has
   left order `complexOrder D`, and has real `j`-invariant equal to the principal singular modulus
   (`j_cmPoint_neg_natCast`, `im_j_cmPoint_neg_natCast`). Its multiple
   `cmPointOfConductor D hD0 f = f · τ_D` spans `complexOrder (f² D)` and has left order
   `complexOrder (f² D)` (`leftOrder_lattice_periodPair_cmPointOfConductor`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.posDefProperClassToHomothetyClass`: sends a proper class `[f]` to
  the homothety class of `(root f).periodPair`.
* `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivPosDefProperClass`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivPic`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivGal`: bijections from homothety classes of
  complex lattices with left order `complexOrder (-n)` to `PosDefProperClass n`, `Pic(O_{-n})`, and
  `Gal(H_O / ℚ(√(-n)))`.
* `TauCeti.BinaryQuadraticForm.cmTraceCoeff`, `TauCeti.BinaryQuadraticForm.cmNormCoeff`,
  `TauCeti.BinaryQuadraticForm.cmForm`, `TauCeti.BinaryQuadraticForm.cmPoint`,
  `TauCeti.BinaryQuadraticForm.cmPointOfConductor`: the canonical CM point `τ_D`, its monic
  defining form, and the conductor-`f` point `f · τ_D`.

## Main results

* `TauCeti.BinaryQuadraticForm.leftOrder_periodPair_root_eq_complexOrder_primPart`,
  `TauCeti.BinaryQuadraticForm.leftOrder_periodPair_root_eq_complexOrder_iff_isPrimitive`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_eq_complexOrder_iff`: exact multiplier
  orders of form roots and characterization of CM upper-half-plane points.
* `PeriodPair.HomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`,
  `WeierstrassCurve.leftOrder_periodLattice_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`:
  complex elliptic curves and lattice classes have CM by `O_{-n}` iff `j` is a root of
  `hilbertClassPolynomial n`.
* `TauCeti.BinaryQuadraticForm.eq_of_singularModulus_eq`,
  `TauCeti.BinaryQuadraticForm.eq_of_isRoot_hilbertClassPolynomial`,
  `TauCeti.BinaryQuadraticForm.isCoprime_hilbertClassPolynomial_of_ne`: uniqueness of the CM
  discriminant from a singular modulus and coprimality of Hilbert class polynomials.
* `TauCeti.BinaryQuadraticForm.cmPoint_quadratic`,
  `TauCeti.BinaryQuadraticForm.lattice_periodPair_cmPoint`,
  `TauCeti.BinaryQuadraticForm.j_cmPoint_neg_natCast`,
  `TauCeti.BinaryQuadraticForm.im_j_cmPoint_neg_natCast`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_cmPointOfConductor`: properties of
  `τ_D` and `f · τ_D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, §10–11, and §13.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1–2.
* B. H. Gross and D. B. Zagier, *On singular moduli*, J. Reine Angew. Math. **355** (1985),
  191–220, §1.
-/

public noncomputable section

open Complex MulAction Polynomial QuadraticAlgebra
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-! ### Exact multiplier orders of roots of positive definite forms -/

section RootLeftOrder

variable {n : ℕ} [NeZero n]

/-- **Exact multiplier order for a primitive positive definite form**: if `f ∈ posDef n` is
primitive, the left order of `ℤ · root f + ℤ` is `QuadraticOrder.complexOrder (-n)`. -/
theorem leftOrder_periodPair_root_of_isPrimitive (f : posDef n) (hfprim : f.1.IsPrimitive) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) := by
  apply le_antisymm _ (complexOrder_le_leftOrder_periodPair_root f)
  intro x hx
  have hrel : (f.1.a : ℂ) * (root f : ℂ) ^ 2 + f.1.b * (root f : ℂ) + f.1.c = 0 :=
    (eq_root_iff f (root f)).mp rfl
  obtain ⟨m, k, rfl⟩ :=
    (UpperHalfPlane.mem_leftOrder_lattice_periodPair_iff_of_quadratic hrel
      hfprim.exists_linearCombination_eq_one).mp hx
  set O := QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
    ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one)
  have hθ : (f.1.a : ℂ) * (root f : ℂ) ∈ O := by
    have hmem : (f.1.a : ℂ) * (root f : ℂ) ∈
        f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          (mem_posDef.mp f.2).1 := by
      rw [complexOrderIdeal_eq_lattice_smul_periodPair_root]
      simpa only [PeriodPair.smul_ω₁, Units.val_mk0, periodPair_ω₁] using
        (Units.mk0 (f.1.a : ℂ) (Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne') •
          (root f).periodPair).ω₁_mem_lattice
    exact complexOrderIdeal_le_complexOrder f.1 (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) (mem_posDef.mp f.2).1 hmem
  exact add_mem (O.intCast_mem m) (mul_mem (O.intCast_mem k) hθ)

/-- If `f ∈ posDef n` is primitive, the left order of `f.1.complexOrderIdeal (-n)` is
`QuadraticOrder.complexOrder (-n)`. -/
theorem leftOrder_complexOrderIdeal_of_isPrimitive (f : posDef n) (hfprim : f.1.IsPrimitive) :
    (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) := by
  rw [leftOrder_complexOrderIdeal_posDef, leftOrder_periodPair_root_of_isPrimitive f hfprim]

/-- The primitive part of any positive definite form has strictly negative discriminant. -/
theorem primPart_discrim_neg_of_posDef (f : posDef n) : f.1.primPart.discrim < 0 := by
  obtain ⟨hfdisc, hfa⟩ := mem_posDef.mp f.2
  have hf0 : f.1 ≠ 0 := fun h ↦ by simp [h] at hfa
  have hc : 0 < (f.1.content : ℤ) ^ 2 :=
    sq_pos_of_pos (Nat.cast_pos.mpr ((f.1.content_pos_iff).mpr hf0))
  have hdisc := f.1.discrim_eq_content_sq_mul
  rw [hfdisc] at hdisc
  have hneg : (f.1.content : ℤ) ^ 2 * f.1.primPart.discrim < 0 := by
    rw [← hdisc]
    exact Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))
  exact neg_of_mul_neg_right hneg hc.le

/-- **Exact multiplier order of any positive definite form**: for `f ∈ posDef n` (not necessarily
primitive), `(root f).periodPair.lattice.leftOrder` is `complexOrder f.1.primPart.discrim`. -/
theorem leftOrder_periodPair_root_eq_complexOrder_primPart (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder f.1.primPart.discrim (primPart_discrim_neg_of_posDef f).le
        f.1.primPart.discrim_emod_four_eq_zero_or_one := by
  obtain ⟨_, hfa⟩ := mem_posDef.mp f.2
  have hf0 : f.1 ≠ 0 := fun h ↦ by simp [h] at hfa
  have hcpos : 0 < f.1.content := (f.1.content_pos_iff).mpr hf0
  have hdneg : f.1.primPart.discrim < 0 := primPart_discrim_neg_of_posDef f
  set m : ℕ := (-f.1.primPart.discrim).toNat
  have hm_eq : (m : ℤ) = -f.1.primPart.discrim := Int.toNat_of_nonneg (by omega)
  have hm_pos : 0 < m := by omega
  have : NeZero m := ⟨hm_pos.ne'⟩
  have hg_disc : f.1.primPart.discrim = -m := by omega
  have ha_mul : (f.1.content : ℤ) * f.1.primPart.a = f.1.a := by
    rw [primPart_a, mul_comm, Int.ediv_mul_cancel f.1.content_dvd_a]
  have hb_mul : (f.1.content : ℤ) * f.1.primPart.b = f.1.b := by
    rw [primPart_b, mul_comm, Int.ediv_mul_cancel f.1.content_dvd_b]
  have hc_mul : (f.1.content : ℤ) * f.1.primPart.c = f.1.c := by
    rw [primPart_c, mul_comm, Int.ediv_mul_cancel f.1.content_dvd_c]
  have hg_a : 0 < f.1.primPart.a :=
    pos_of_mul_pos_right (ha_mul.symm ▸ hfa) (Nat.cast_nonneg _)
  let g : posDef m := ⟨f.1.primPart, mem_posDef.mpr ⟨hg_disc, hg_a⟩⟩
  have hroot : root f = root g := by
    rw [eq_root_iff]
    have hrel := (eq_root_iff f (root f)).mp rfl
    have hfac : (f.1.content : ℂ) * ((g.1.a : ℂ) * (root f : ℂ) ^ 2 + g.1.b * (root f : ℂ) +
        g.1.c) = 0 := by
      change (f.1.content : ℂ) * ((f.1.primPart.a : ℂ) * (root f : ℂ) ^ 2 +
        f.1.primPart.b * (root f : ℂ) + f.1.primPart.c) = 0
      rw [← ha_mul, ← hb_mul, ← hc_mul] at hrel
      push_cast at hrel
      linear_combination hrel
    exact (mul_eq_zero.mp hfac).resolve_left (Nat.cast_ne_zero.mpr hcpos.ne')
  rw [hroot, leftOrder_periodPair_root_of_isPrimitive g (f.1.isPrimitive_primPart hf0)]
  exact (QuadraticOrder.complexOrder_eq_iff (Int.neg_neg_of_pos (Nat.cast_pos.mpr hm_pos))
    (hg_disc ▸ f.1.primPart.discrim_emod_four_eq_zero_or_one) hdneg
    f.1.primPart.discrim_emod_four_eq_zero_or_one).mpr hg_disc.symm

/-- **Primitivity criterion via the multiplier order**: for `f ∈ posDef n`, the left order of
`ℤ · root f + ℤ` equals `complexOrder (-n)` if and only if `f` is primitive. -/
theorem leftOrder_periodPair_root_eq_complexOrder_iff_isPrimitive (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ↔
      f.1.IsPrimitive := by
  refine ⟨fun h ↦ ?_, leftOrder_periodPair_root_of_isPrimitive f⟩
  rw [leftOrder_periodPair_root_eq_complexOrder_primPart] at h
  have hd : f.1.primPart.discrim = -n :=
    (QuadraticOrder.complexOrder_eq_iff (primPart_discrim_neg_of_posDef f)
      f.1.primPart.discrim_emod_four_eq_zero_or_one
      (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n)))
      ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one)).mp h
  have hsq := f.1.discrim_eq_content_sq_mul
  rw [(mem_posDef.mp f.2).1, hd] at hsq
  have hne : (-(n : ℤ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hc2 : (f.1.content : ℤ) ^ 2 = 1 :=
    mul_right_cancel₀ hne (by linear_combination -hsq)
  have hc1 : f.1.content = 1 := by
    have : f.1.content ^ 2 = 1 := by exact_mod_cast hc2
    nlinarith
  exact (f.1.isPrimitive_iff).mpr hc1

/-- For `f ∈ posDef n`, the left order of `f.1.complexOrderIdeal (-n)` equals `complexOrder (-n)`
if and only if `f` is primitive. -/
theorem leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive (f : posDef n) :
    (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ↔
      f.1.IsPrimitive := by
  rw [leftOrder_complexOrderIdeal_posDef,
    leftOrder_periodPair_root_eq_complexOrder_iff_isPrimitive]

/-- An integral quadratic relation `a τ² + b τ + c = 0` satisfied by `τ ∈ ℍ` with `a ≠ 0` has
strictly negative discriminant `b² - 4 a c < 0`. -/
theorem discrim_neg_of_quadratic_upperHalfPlane {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0) :
    (⟨a, b, c⟩ : BinaryQuadraticForm ℤ).discrim < 0 := by
  have him := congrArg Complex.im hrel
  have hre := congrArg Complex.re hrel
  simp only [sq, add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, coe_re, coe_im,
    add_re, mul_re, sub_zero, zero_im, zero_re] at him hre
  have him' : (2 * (a : ℝ) * τ.re + b) * τ.im = 0 := by linear_combination him
  have h2ax : 2 * (a : ℝ) * τ.re + b = 0 := (mul_eq_zero.mp him').resolve_right τ.im_ne_zero
  have hdiscR : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) = -(4 * (a : ℝ) ^ 2 * τ.im ^ 2) := by
    push_cast
    linear_combination (2 * (a : ℝ) * τ.re + b) * h2ax - 4 * (a : ℝ) * hre
  have : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hnegR : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) < 0 := by
    rw [hdiscR]
    have hpos : 0 < 4 * (a : ℝ) ^ 2 * τ.im ^ 2 := by positivity
    linarith
  rw [discrim_def, discrim]
  exact_mod_cast hnegR

/-- **Analytic-algebraic characterization of CM upper-half-plane points**: for `n > 0` with
`-n ≡ 0, 1 mod 4`, the multiplier order of `ℤ τ + ℤ` is `complexOrder (-n)` if and only if
`τ = root f` for a primitive positive definite form `f` of discriminant `-n`. -/
theorem leftOrder_lattice_periodPair_eq_complexOrder_iff
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) {τ : ℍ} :
    τ.periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn ↔
      ∃ f : ↥(posDef n ⊓ primitiveForms (-n)),
        root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩ = τ := by
  constructor
  · intro hleft
    have hne : τ.periodPair.lattice.leftOrder ≠ ⊥ := by
      rw [hleft]
      intro hbot
      have hmem : QuadraticOrder.complexGenerator (-n) ∈ (⊥ : Subalgebra ℤ ℂ) :=
        hbot ▸ QuadraticOrder.complexGenerator_mem_complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn
      obtain ⟨m, hm⟩ := Algebra.mem_bot.mp hmem
      have him := congrArg Complex.im hm
      simp only [Algebra.algebraMap_eq_smul_one, zsmul_one, intCast_im] at him
      exact (QuadraticOrder.im_complexGenerator_pos
        (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n)))).ne him
    obtain ⟨a, b, c, ha, hrel⟩ := UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff.mp hne
    let f₀ : BinaryQuadraticForm ℤ := ⟨a, b, c⟩
    have hd₀ : f₀.discrim < 0 := discrim_neg_of_quadratic_upperHalfPlane ha.ne' hrel
    set m : ℕ := (-f₀.discrim).toNat
    have hm_eq : (m : ℤ) = -f₀.discrim := Int.toNat_of_nonneg (by omega)
    have hm_pos : 0 < m := by omega
    have : NeZero m := ⟨hm_pos.ne'⟩
    let fp : posDef m := ⟨f₀, mem_posDef.mpr ⟨by omega, ha⟩⟩
    have hroot₀ : τ = root fp := (eq_root_iff fp τ).mpr hrel
    have hprim_ord := leftOrder_periodPair_root_eq_complexOrder_primPart fp
    rw [← hroot₀, hleft] at hprim_ord
    have hd_prim : f₀.primPart.discrim = -n :=
      ((QuadraticOrder.complexOrder_eq_iff
        (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) hn
        (primPart_discrim_neg_of_posDef fp)
        f₀.primPart.discrim_emod_four_eq_zero_or_one).mp hprim_ord).symm
    have hf₀_ne : f₀ ≠ 0 := fun h ↦ ha.ne' (by simpa [f₀] using congrArg BinaryQuadraticForm.a h)
    have hc_pos : 0 < f₀.content := (f₀.content_pos_iff).mpr hf₀_ne
    have ha' : (f₀.content : ℤ) * f₀.primPart.a = a := by
      simpa only [primPart_a, mul_comm] using Int.ediv_mul_cancel f₀.content_dvd_a
    have hb' : (f₀.content : ℤ) * f₀.primPart.b = b := by
      simpa only [primPart_b, mul_comm] using Int.ediv_mul_cancel f₀.content_dvd_b
    have hc' : (f₀.content : ℤ) * f₀.primPart.c = c := by
      simpa only [primPart_c, mul_comm] using Int.ediv_mul_cancel f₀.content_dvd_c
    have hg_a : 0 < f₀.primPart.a :=
      pos_of_mul_pos_right (ha'.symm ▸ ha) (Nat.cast_nonneg _)
    let g : ↥(posDef n ⊓ primitiveForms (-n)) :=
      ⟨f₀.primPart, (mem_posDef_inf_primitiveForms n).mpr
        ⟨hd_prim, hg_a, f₀.isPrimitive_primPart hf₀_ne⟩⟩
    refine ⟨g, ?_⟩
    symm
    rw [eq_root_iff]
    have hfac : (f₀.content : ℂ) * ((f₀.primPart.a : ℂ) * (τ : ℂ) ^ 2 + f₀.primPart.b * (τ : ℂ) +
        f₀.primPart.c) = 0 := by
      rw [← ha', ← hb', ← hc'] at hrel
      push_cast at hrel
      linear_combination hrel
    exact (mul_eq_zero.mp hfac).resolve_left (Nat.cast_ne_zero.mpr hc_pos.ne')
  · rintro ⟨f, rfl⟩
    exact leftOrder_periodPair_root_of_isPrimitive
      ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩
      ((mem_posDef_inf_primitiveForms n).mp f.2).2.2

end RootLeftOrder

/-! ### Homothety classes of CM lattices, Picard group, and ring class Galois group -/

section CMDictionary

variable (n : ℕ) [NeZero n]

/-- Proper equivalence of forms preserves the homothety class of `(root f).periodPair`. -/
private theorem homothetyClass_periodPair_root_eq_of_orbitRel
    {f g : ↥(posDef n ⊓ primitiveForms (-n))} (h : orbitRel SL(2, ℤ) _ f g) :
    PeriodPair.HomothetyClass.mk (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩).periodPair =
      PeriodPair.HomothetyClass.mk
        (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩).periodPair := by
  obtain ⟨γ, rfl⟩ := mem_orbit_iff.mp h
  rw [← UpperHalfPlane.mk_homothetyClass_periodPair_smul γ
    (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩), ← root_smul]
  congr 3

/-- **Complex-lattice homothety class of a proper form class**: sends `[f] ∈ PosDefProperClass n`
to the homothety class of `(root f).periodPair` (equivalently, of `f.complexOrderIdeal (-n)`). -/
def posDefProperClassToHomothetyClass : PosDefProperClass n → PeriodPair.HomothetyClass :=
  Quotient.lift (fun f ↦ PeriodPair.HomothetyClass.mk
    (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩).periodPair)
    fun _ _ ↦ homothetyClass_periodPair_root_eq_of_orbitRel n

/-- Evaluation of `posDefProperClassToHomothetyClass` on a representative form. -/
@[simp] theorem posDefProperClassToHomothetyClass_mk (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    posDefProperClassToHomothetyClass n (Quotient.mk _ f) =
      PeriodPair.HomothetyClass.mk
        (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩).periodPair :=
  (rfl)

/-- The `j`-invariant of `posDefProperClassToHomothetyClass n q` is `singularModulus n q`. -/
@[simp] theorem j_posDefProperClassToHomothetyClass (q : PosDefProperClass n) :
    (posDefProperClassToHomothetyClass n q).j = singularModulus n q := by
  induction q using Quotient.inductionOn with | h f
  rw [posDefProperClassToHomothetyClass_mk, PeriodPair.HomothetyClass.j_mk_periodPair,
    singularModulus_mk]

variable {n} in
/-- `posDefProperClassToHomothetyClass` is injective: distinct proper classes give non-homothetic
complex lattices. -/
theorem posDefProperClassToHomothetyClass_injective :
    Function.Injective (posDefProperClassToHomothetyClass n) := fun _ _ h ↦
  singularModulus_injective
    (by simpa only [j_posDefProperClassToHomothetyClass] using
      congrArg PeriodPair.HomothetyClass.j h)

/-- Every homothety class in the image of `posDefProperClassToHomothetyClass n` has left order
`QuadraticOrder.complexOrder (-n)`. -/
theorem leftOrder_posDefProperClassToHomothetyClass
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n) :
    (posDefProperClassToHomothetyClass n q).leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn := by
  induction q using Quotient.inductionOn with | h f
  rw [posDefProperClassToHomothetyClass_mk, PeriodPair.HomothetyClass.leftOrder_mk]
  exact leftOrder_periodPair_root_of_isPrimitive
    ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩
    ((mem_posDef_inf_primitiveForms n).mp f.2).2.2

/-- **Image of `posDefProperClassToHomothetyClass`**: a homothety class of complex period lattices
lies in the image of `PosDefProperClass n` if and only if its left order is `complexOrder (-n)`. -/
theorem mem_range_posDefProperClassToHomothetyClass_iff
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) {x : PeriodPair.HomothetyClass} :
    x ∈ Set.range (posDefProperClassToHomothetyClass n) ↔
      x.leftOrder = QuadraticOrder.complexOrder (-n)
        (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn := by
  constructor
  · rintro ⟨q, rfl⟩
    exact leftOrder_posDefProperClassToHomothetyClass n hn q
  · intro hx
    obtain ⟨τ, rfl⟩ := PeriodPair.HomothetyClass.mk_periodPair_surjective x
    rw [PeriodPair.HomothetyClass.leftOrder_mk,
      leftOrder_lattice_periodPair_eq_complexOrder_iff hn] at hx
    obtain ⟨f, rfl⟩ := hx
    exact ⟨Quotient.mk _ f, rfl⟩

/-- **Bijection between CM lattice homothety classes and proper classes of forms**: homothety
classes of period pairs with left order `complexOrder (-n)` correspond bijectively to
`PosDefProperClass n`. -/
def cmHomothetyClassEquivPosDefProperClass (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃
      PosDefProperClass n :=
  ((Equiv.ofInjective (posDefProperClassToHomothetyClass n)
    posDefProperClassToHomothetyClass_injective).trans
    (Equiv.subtypeEquivRight
      fun _ ↦ mem_range_posDefProperClassToHomothetyClass_iff n hn)).symm

/-- Inverse evaluation of `cmHomothetyClassEquivPosDefProperClass` is
`posDefProperClassToHomothetyClass`. -/
@[simp] theorem coe_cmHomothetyClassEquivPosDefProperClass_symm
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n) :
    (((cmHomothetyClassEquivPosDefProperClass n hn).symm q) : PeriodPair.HomothetyClass) =
      posDefProperClassToHomothetyClass n q := by
  simp [cmHomothetyClassEquivPosDefProperClass]

/-- Applying `posDefProperClassToHomothetyClass` after `cmHomothetyClassEquivPosDefProperClass`
recovers the underlying homothety class. -/
@[simp] theorem posDefProperClassToHomothetyClass_cmHomothetyClassEquivPosDefProperClass
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    posDefProperClassToHomothetyClass n (cmHomothetyClassEquivPosDefProperClass n hn x) = x.1 := by
  simpa only [coe_cmHomothetyClassEquivPosDefProperClass_symm] using
    congrArg Subtype.val ((cmHomothetyClassEquivPosDefProperClass n hn).symm_apply_apply x)

/-- **Bijection between CM lattice homothety classes and the Picard group** of the quadratic order
of discriminant `-n`. -/
def cmHomothetyClassEquivPic (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃
      GlobalNumberFields.Pic (QuadraticOrder.numberFieldOrder (-n : ℤ) hn) :=
  (cmHomothetyClassEquivPosDefProperClass n hn).trans (posDefProperClassEquivPic n hn)

/-- `cmHomothetyClassEquivPic` sends a CM homothety class to the Picard class of its corresponding
proper form class. -/
theorem cmHomothetyClassEquivPic_apply (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    cmHomothetyClassEquivPic n hn x =
      posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) :=
  posDefProperClassEquivPic_apply n hn (cmHomothetyClassEquivPosDefProperClass n hn x)

/-- **Bijection between CM lattice homothety classes and the ring class Galois group**
`Gal(H_O / ℚ(√(-n)))`. -/
def cmHomothetyClassEquivGal (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃
      Gal(ClassFieldTheory.ringClassField (QuadraticOrder.numberFieldOrder (-n) hn) /
        QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
  (cmHomothetyClassEquivPosDefProperClass n hn).trans (posDefProperClassEquivGal n hn)

/-- `cmHomothetyClassEquivGal` sends a CM homothety class to the ring class Artin symbol of its
corresponding proper form class. -/
theorem cmHomothetyClassEquivGal_apply (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    cmHomothetyClassEquivGal n hn x =
      posDefProperClassEquivGal n hn (cmHomothetyClassEquivPosDefProperClass n hn x) :=
  (rfl)

/-- The number of homothety classes of complex period lattices with left order
`complexOrder (-n)` equals `#Pic(O_{-n})`. -/
theorem nat_card_cmHomothetyClass (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    Nat.card {x : PeriodPair.HomothetyClass //
        x.leftOrder = QuadraticOrder.complexOrder (-n)
          (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} =
      Nat.card (GlobalNumberFields.Pic (QuadraticOrder.numberFieldOrder (-n) hn)) :=
  Nat.card_congr (cmHomothetyClassEquivPic n hn)

end CMDictionary

end TauCeti.BinaryQuadraticForm

namespace PeriodPair.HomothetyClass

open TauCeti TauCeti.BinaryQuadraticForm

/-- **Hilbert class polynomial characterization on homothety classes**: a homothety class `x` of
complex period lattices has left order `complexOrder (-n)` if and only if `x.j` is a root of
`hilbertClassPolynomial n`. -/
theorem leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial (x : PeriodPair.HomothetyClass)
    (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    x.leftOrder = QuadraticOrder.complexOrder (-n)
        (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn ↔
      (hilbertClassPolynomial n).IsRoot x.j := by
  rw [← mem_range_posDefProperClassToHomothetyClass_iff n hn, isRoot_hilbertClassPolynomial_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, (j_posDefProperClassToHomothetyClass n q).symm⟩
  · rintro ⟨q, hq⟩
    refine ⟨q, j_injective ?_⟩
    rwa [j_posDefProperClassToHomothetyClass]

end PeriodPair.HomothetyClass

namespace TauCeti.BinaryQuadraticForm

/-- A point `τ ∈ ℍ` has `(ℤ τ + ℤ).leftOrder = complexOrder (-n)` if and only if `j(τ)` is a root
of `hilbertClassPolynomial n`. -/
theorem leftOrder_lattice_periodPair_eq_complexOrder_iff_isRoot_hilbertClassPolynomial (n : ℕ)
    [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) {τ : ℍ} :
    τ.periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn ↔
      (hilbertClassPolynomial n).IsRoot (ModularForm.j τ) := by
  simpa only [PeriodPair.HomothetyClass.leftOrder_mk,
    PeriodPair.HomothetyClass.j_mk_periodPair] using
    PeriodPair.HomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial
      (PeriodPair.HomothetyClass.mk τ.periodPair) n hn

end TauCeti.BinaryQuadraticForm

namespace WeierstrassCurve

open TauCeti TauCeti.BinaryQuadraticForm

/-- **CM characterization for complex Weierstrass elliptic curves**: for an elliptic curve `E / ℂ`
and `n > 0` with `-n ≡ 0, 1 mod 4`, the period lattice of `E` has multiplier order
`complexOrder (-n)` if and only if `E.j` is a root of `hilbertClassPolynomial n`. -/
theorem leftOrder_periodLattice_eq_complexOrder_iff_isRoot_hilbertClassPolynomial
    (E : WeierstrassCurve ℂ) [E.IsElliptic] (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    E.periodLattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn ↔
      (hilbertClassPolynomial n).IsRoot E.j := by
  obtain ⟨L, C, hu, rfl⟩ := E.exists_periodPair_variableChange_smul_eq
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩, variableChange_j]
  simpa only [PeriodPair.HomothetyClass.leftOrder_mk, PeriodPair.HomothetyClass.j_mk] using
    (PeriodPair.HomothetyClass.mk L).leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial n
      hn

end WeierstrassCurve

namespace TauCeti.BinaryQuadraticForm

/-! ### Uniqueness of the CM discriminant from a singular modulus -/

section Uniqueness

/-- **A singular modulus uniquely determines the discriminant of its CM order**: if
`singularModulus m q₁ = singularModulus n q₂`, then `m = n`. -/
theorem eq_of_singularModulus_eq {m n : ℕ} [NeZero m] [NeZero n]
    {q₁ : PosDefProperClass m} {q₂ : PosDefProperClass n}
    (h : singularModulus m q₁ = singularModulus n q₂) : m = n := by
  obtain ⟨f₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨f₂, rfl⟩ := Quotient.exists_rep q₂
  have hm : (-m : ℤ) % 4 = 0 ∨ (-m : ℤ) % 4 = 1 :=
    ((mem_posDef_inf_primitiveForms m).mp f₁.2).1 ▸ f₁.1.discrim_emod_four_eq_zero_or_one
  have hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1 :=
    ((mem_posDef_inf_primitiveForms n).mp f₂.2).1 ▸ f₂.1.discrim_emod_four_eq_zero_or_one
  have hx : posDefProperClassToHomothetyClass m (Quotient.mk _ f₁) =
      posDefProperClassToHomothetyClass n (Quotient.mk _ f₂) := by
    apply PeriodPair.HomothetyClass.j_injective
    simpa only [j_posDefProperClassToHomothetyClass] using h
  have hord := congrArg PeriodPair.HomothetyClass.leftOrder hx
  rw [leftOrder_posDefProperClassToHomothetyClass m hm,
    leftOrder_posDefProperClassToHomothetyClass n hn] at hord
  have hneg : -(m : ℤ) = -(n : ℤ) :=
    (QuadraticOrder.complexOrder_eq_iff
      (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos m))) hm
      (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) hn).mp hord
  omega

/-- **Hilbert class polynomials of distinct discriminants share no roots**: if `z ∈ ℂ` is a root of
both `hilbertClassPolynomial m` and `hilbertClassPolynomial n`, then `m = n`. -/
theorem eq_of_isRoot_hilbertClassPolynomial {m n : ℕ} [NeZero m] [NeZero n] {z : ℂ}
    (hm : (hilbertClassPolynomial m).IsRoot z) (hn : (hilbertClassPolynomial n).IsRoot z) :
    m = n := by
  obtain ⟨q₁, rfl⟩ := (isRoot_hilbertClassPolynomial_iff m).mp hm
  obtain ⟨q₂, hq₂⟩ := (isRoot_hilbertClassPolynomial_iff n).mp hn
  exact eq_of_singularModulus_eq hq₂.symm

/-- **Hilbert class polynomials of distinct discriminants are coprime** in `ℂ[X]`. -/
theorem isCoprime_hilbertClassPolynomial_of_ne {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ≠ n) :
    IsCoprime (hilbertClassPolynomial m) (hilbertClassPolynomial n) := by
  have := Fintype.ofFinite (PosDefProperClass m)
  have := Fintype.ofFinite (PosDefProperClass n)
  rw [hilbertClassPolynomial_eq_prod, hilbertClassPolynomial_eq_prod]
  refine IsCoprime.prod_left fun q₁ _ ↦ IsCoprime.prod_right fun q₂ _ ↦ ?_
  refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_
  exact (sub_ne_zero.mpr fun heq ↦ hmn (eq_of_singularModulus_eq heq)).isUnit

end Uniqueness

/-! ### Canonical CM point `τ_D` and conductor-`f` CM point `f · τ_D` -/

section CanonicalCMPoint

/-- Middle coefficient `B ∈ {0, -3}` of the canonical monic quadratic `τ_D² + B τ_D + C = 0`
satisfied by the canonical CM point `τ_D` (`0` when `D ≡ 0 mod 4`, `-3` when `D ≡ 1 mod 4`). -/
def cmTraceCoeff (D : ℤ) : ℤ :=
  if D % 4 = 0 then 0 else -3

/-- Constant term `C = (B² - D) / 4` of the canonical monic quadratic `τ_D² + B τ_D + C = 0`. -/
def cmNormCoeff (D : ℤ) : ℤ :=
  ((cmTraceCoeff D) ^ 2 - D) / 4

/-- `cmTraceCoeff D` is always `0` or `-3`. -/
theorem cmTraceCoeff_eq_zero_or_neg_three (D : ℤ) :
    cmTraceCoeff D = 0 ∨ cmTraceCoeff D = -3 := by
  unfold cmTraceCoeff
  split_ifs <;> simp

/-- The monic binary quadratic form `x² + cmTraceCoeff D · x y + cmNormCoeff D · y²` whose root is
the canonical CM point `τ_D`. -/
def cmForm (D : ℤ) : BinaryQuadraticForm ℤ :=
  ⟨1, cmTraceCoeff D, cmNormCoeff D⟩

/-- Leading coefficient of `cmForm D`. -/
@[simp] theorem cmForm_a (D : ℤ) : (cmForm D).a = 1 := (rfl)

/-- Middle coefficient of `cmForm D`. -/
@[simp] theorem cmForm_b (D : ℤ) : (cmForm D).b = cmTraceCoeff D := (rfl)

/-- Last coefficient of `cmForm D`. -/
@[simp] theorem cmForm_c (D : ℤ) : (cmForm D).c = cmNormCoeff D := (rfl)

/-- For `D ≡ 0, 1 mod 4`, `4 ∣ (cmTraceCoeff D)² - D`. -/
private theorem four_dvd_cmTraceCoeff_sq_sub {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (4 : ℤ) ∣ (cmTraceCoeff D) ^ 2 - D := by
  rw [cmTraceCoeff]
  rcases hD with h0 | h1
  · simp only [h0, ↓reduceIte]
    omega
  · have hne : D % 4 ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    omega

/-- For `D ≡ 0, 1 mod 4`, `cmForm D` has discriminant `D`. -/
theorem discrim_cmForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmForm D).discrim = D := by
  have h4 := Int.mul_ediv_cancel' (four_dvd_cmTraceCoeff_sq_sub hD)
  rw [discrim_def, discrim, cmForm_a, cmForm_b, cmForm_c, cmNormCoeff]
  linear_combination -h4

/-- `cmForm D` is primitive. -/
theorem isPrimitive_cmForm (D : ℤ) : (cmForm D).IsPrimitive :=
  isPrimitive_of_linearCombination_eq_one _ 1 0 0 (by simp)

/-- For `n > 0` with `-n ≡ 0, 1 mod 4`, `cmForm (-n)` is primitive positive definite of
discriminant `-n`. -/
theorem cmForm_mem_posDef_inf_primitiveForms (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    cmForm (-n) ∈ posDef n ⊓ primitiveForms (-n) :=
  (mem_posDef_inf_primitiveForms n).mpr ⟨discrim_cmForm hn, by simp, isPrimitive_cmForm _⟩

/-- **Canonical CM point `τ_D ∈ ℍ`** of negative discriminant `D < 0`: `i √(-D) / 2` when
`D ≡ 0 mod 4`, and `(3 + i √(-D)) / 2` when `D ≢ 0 mod 4` (in particular for `D ≡ 1 mod 4`). -/
def cmPoint (D : ℤ) (hD0 : D < 0) : ℍ :=
  ⟨⟨-(cmTraceCoeff D : ℝ) / 2, √(-(D : ℝ)) / 2⟩,
    half_pos (Real.sqrt_pos.mpr (neg_pos.mpr (Int.cast_lt_zero.mpr hD0)))⟩

/-- Real part of `cmPoint D hD0`. -/
@[simp] theorem re_cmPoint (D : ℤ) (hD0 : D < 0) :
    (cmPoint D hD0).re = -(cmTraceCoeff D : ℝ) / 2 := (rfl)

/-- Imaginary part of `cmPoint D hD0`. -/
@[simp] theorem im_cmPoint (D : ℤ) (hD0 : D < 0) :
    (cmPoint D hD0).im = √(-(D : ℝ)) / 2 := (rfl)

/-- Complex value of `cmPoint D hD0`. -/
theorem coe_cmPoint (D : ℤ) (hD0 : D < 0) :
    (cmPoint D hD0 : ℂ) = (-(cmTraceCoeff D : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  simp [← (cmPoint D hD0).re_add_im, add_div, mul_div_right_comm]

/-- When `D % 4 = 0`, `cmPoint D hD0 = i √(-D) / 2`. -/
theorem coe_cmPoint_of_emod_four_eq_zero {D : ℤ} (hD0 : D < 0) (h0 : D % 4 = 0) :
    (cmPoint D hD0 : ℂ) = (√(-(D : ℝ)) : ℂ) * I / 2 := by
  simp [coe_cmPoint, cmTraceCoeff, h0]

/-- When `D % 4 = 1`, `cmPoint D hD0 = (3 + i √(-D)) / 2`. -/
theorem coe_cmPoint_of_emod_four_eq_one {D : ℤ} (hD0 : D < 0) (h1 : D % 4 = 1) :
    (cmPoint D hD0 : ℂ) = (3 + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  have hne : D % 4 ≠ 0 := by omega
  simp only [coe_cmPoint, cmTraceCoeff, hne, ↓reduceIte]
  norm_num

/-- **Monic integral quadratic satisfied by `τ_D`**: for `D < 0` with `D ≡ 0, 1 mod 4`,
`τ_D² + cmTraceCoeff D · τ_D + cmNormCoeff D = 0`. -/
theorem cmPoint_quadratic {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0 : ℂ) ^ 2 + cmTraceCoeff D * (cmPoint D hD0 : ℂ) + cmNormCoeff D = 0 := by
  have h4 : (4 : ℂ) * (cmNormCoeff D : ℂ) = (cmTraceCoeff D : ℂ) ^ 2 - D := by
    exact_mod_cast Int.mul_ediv_cancel' (four_dvd_cmTraceCoeff_sq_sub hD)
  have hsqrt : ((√(-(D : ℝ)) : ℂ) * I) ^ 2 = D := by
    have hs : (√(-(D : ℝ)) : ℂ) * (√(-(D : ℝ)) : ℂ) = -(D : ℂ) := by
      rw [← ofReal_mul, Real.mul_self_sqrt (neg_nonneg.mpr (Int.cast_nonpos.mpr hD0.le))]
      push_cast
      ring
    linear_combination (I * I) * hs - I_mul_I * (D : ℂ)
  rw [coe_cmPoint]
  linear_combination (hsqrt + h4) / 4

/-- `cmPoint D hD0` differs from `QuadraticOrder.complexGenerator D` by the integer
`(D + cmTraceCoeff D) / 2`. -/
theorem coe_cmPoint_eq_complexGenerator_sub {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0 : ℂ) =
      QuadraticOrder.complexGenerator D - (((D + cmTraceCoeff D) / 2 : ℤ) : ℂ) := by
  have hdiv : (2 : ℤ) ∣ D + cmTraceCoeff D := by
    rw [cmTraceCoeff]
    rcases hD with h0 | h1
    · simp only [h0, ↓reduceIte]
      omega
    · have hne : D % 4 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega
  have h2 : (2 : ℂ) * (((D + cmTraceCoeff D) / 2 : ℤ) : ℂ) = (D : ℂ) + cmTraceCoeff D := by
    exact_mod_cast Int.mul_ediv_cancel' hdiv
  rw [coe_cmPoint, QuadraticOrder.complexGenerator_def]
  linear_combination h2 / 2

/-- **The period lattice `ℤ · τ_D + ℤ` equals `complexOrder D`** on the nose. -/
theorem lattice_periodPair_cmPoint {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0).periodPair.lattice =
      Subalgebra.toSubmodule (QuadraticOrder.complexOrder D hD0.le hD) := by
  ext z
  rw [PeriodPair.mem_lattice, Subalgebra.mem_toSubmodule, QuadraticOrder.mem_complexOrder_iff]
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one, coe_cmPoint_eq_complexGenerator_sub hD0 hD]
  set q : ℤ := (D + cmTraceCoeff D) / 2
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨n - m * q, m, by push_cast; ring⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨k, m + k * q, by push_cast; ring⟩

/-- **The multiplier order of `ℤ · τ_D + ℤ` is `complexOrder D`.** -/
theorem leftOrder_lattice_periodPair_cmPoint {D : ℤ} (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0).periodPair.lattice.leftOrder = QuadraticOrder.complexOrder D hD0.le hD := by
  rw [lattice_periodPair_cmPoint hD0 hD, Subalgebra.leftOrder_toSubmodule]

/-- `UpperHalfPlane.quadraticOrder` at `cmPoint D hD0` agrees with `complexOrder D`. -/
theorem quadraticOrder_cmPoint {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0).quadraticOrder (cmPoint_quadratic hD0 hD) =
      QuadraticOrder.complexOrder D hD0.le hD := by
  rw [← UpperHalfPlane.leftOrder_lattice_periodPair_eq_quadraticOrder,
    leftOrder_lattice_periodPair_cmPoint]

/-- At `D = -n`, `cmPoint (-n)` is the root of `cmForm (-n)`. -/
theorem cmPoint_neg_natCast_eq_root_cmForm (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    cmPoint (-n) (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) =
      root ⟨cmForm (-n), inf_le_left (b := primitiveForms (-n))
        (cmForm_mem_posDef_inf_primitiveForms n hn)⟩ := by
  rw [eq_root_iff]
  simpa only [cmForm_a, cmForm_b, cmForm_c, Int.cast_one, one_mul] using
    cmPoint_quadratic (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) hn

/-- `cmForm (-n)` is properly `SL(2, ℤ)`-equivalent to `principalForm (-n)`. -/
theorem exists_smul_principalForm_eq_cmForm (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    ∃ γ : SL(2, ℤ), γ • principalForm (-n) = cmForm (-n) := by
  let fp : posDef n :=
    ⟨principalForm (-n), inf_le_left (b := primitiveForms (-n))
      (principalForm_mem_posDef_inf_primitiveForms n hn)⟩
  let fc : posDef n :=
    ⟨cmForm (-n), inf_le_left (b := primitiveForms (-n))
      (cmForm_mem_posDef_inf_primitiveForms n hn)⟩
  have hlat_p : fp.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (discrim_principalForm hn) = (root fp).periodPair.lattice := by
    have h := complexOrderIdeal_eq_lattice_smul_periodPair_root fp
    have hu : Units.mk0 (fp.1.a : ℂ) (Int.cast_ne_zero.mpr (mem_posDef.mp fp.2).2.ne') = 1 := by
      ext
      simp [fp]
    simpa only [hu, one_smul] using h
  have hlat_eq : (root fp).periodPair.lattice = ((1 : ℂˣ) • (root fc).periodPair).lattice := by
    rw [one_smul, ← cmPoint_neg_natCast_eq_root_cmForm n hn, lattice_periodPair_cmPoint _ hn,
      ← hlat_p]
    apply le_antisymm
    · exact complexOrderIdeal_le_complexOrder _ _ _ _
    · rw [QuadraticOrder.complexOrder_toSubmodule, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact (mem_complexOrderIdeal_iff _ _ _ _).mpr ⟨1, 0, by simp [fp]⟩
      · have hgen := congrArg
          (complexEmbedding (Int.cast_nonpos.mpr (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))))
          (generator_eq_idealGenerator_add (principalForm (-n)) (-n) (discrim_principalForm hn))
        simp only [QuadraticOrder.complexEmbedding_generator, map_add, map_intCast,
          complexEmbedding_idealGenerator, zsmul_eq_mul, mul_one, principalForm_b] at hgen
        refine (mem_complexOrderIdeal_iff _ _ _ _).mpr ⟨((-n + (-n) % 2) / 2), 1, ?_⟩
        rw [hgen]
        simp only [fp, principalForm_a, principalForm_b, Int.cast_one, mul_one, one_mul]
        ring
  obtain ⟨γ, hγ, -⟩ :=
    UpperHalfPlane.exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq hlat_eq
  refine ⟨γ, ?_⟩
  rw [← root_smul] at hγ
  exact congrArg Subtype.val (root_injective hγ)

/-- **The `j`-invariant of `cmPoint (-n)` is the principal singular modulus**, hence a root of
`hilbertClassPolynomial n`. -/
theorem j_cmPoint_neg_natCast (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    ModularForm.j (cmPoint (-n) (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n)))) =
      singularModulus n (Quotient.mk _
        ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩) := by
  obtain ⟨γ, hγ⟩ := exists_smul_principalForm_eq_cmForm n hn
  rw [cmPoint_neg_natCast_eq_root_cmForm n hn, singularModulus_mk]
  have hsub : (⟨cmForm (-n), inf_le_left (b := primitiveForms (-n))
      (cmForm_mem_posDef_inf_primitiveForms n hn)⟩ : posDef n) =
      γ • ⟨principalForm (-n), inf_le_left (b := primitiveForms (-n))
        (principalForm_mem_posDef_inf_primitiveForms n hn)⟩ :=
    Subtype.ext hγ.symm
  rw [hsub, root_smul, ModularForm.j_smul_SL2Z]

/-- **`j(τ_D)` is real** for every discriminant `D = -n` (`n > 0`, `-n ≡ 0, 1 mod 4`). -/
theorem im_j_cmPoint_neg_natCast (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    (ModularForm.j (cmPoint (-n) (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))))).im =
      0 := by
  rw [j_cmPoint_neg_natCast n hn, im_singularModulus_eq_zero_iff hn,
    posDefProperClassToPic_principalForm, one_pow]

/-- **CM point `f · τ_D ∈ ℍ` for the order of conductor `f`**: multiplying `cmPoint D hD0` by a
positive integer `f` stays in `ℍ`. -/
def cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] : ℍ :=
  ⟨(f : ℂ) * (cmPoint D hD0 : ℂ), by
    have hf : (0 : ℝ) < f := Nat.cast_pos.mpr (NeZero.pos f)
    have him : 0 < (cmPoint D hD0).im := (cmPoint D hD0).im_pos
    simpa [mul_im, coe_im] using mul_pos hf him⟩

/-- Coercion of `cmPointOfConductor D hD0 f` to `ℂ` is `f · τ_D`. -/
@[simp] theorem coe_cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f : ℂ) = (f : ℂ) * (cmPoint D hD0 : ℂ) :=
  (rfl)

/-- **The period lattice `ℤ · (f τ_D) + ℤ` equals `complexOrder (f² D)`**. -/
theorem lattice_periodPair_cmPointOfConductor {D : ℤ} (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).periodPair.lattice =
      Subalgebra.toSubmodule (QuadraticOrder.complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0.le)
        (QuadraticOrder.mul_sq_emod_four_eq_zero_or_one hD f)) := by
  ext z
  rw [PeriodPair.mem_lattice, Subalgebra.mem_toSubmodule,
    QuadraticOrder.mem_complexOrder_mul_sq_iff hD0.le hD f]
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one, coe_cmPointOfConductor,
    coe_cmPoint_eq_complexGenerator_sub hD0 hD]
  set q : ℤ := (D + cmTraceCoeff D) / 2
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨n - m * f * q, m, by push_cast; ring⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨k, m + k * f * q, by push_cast; ring⟩

/-- **The multiplier order of `ℤ · (f τ_D) + ℤ` is `complexOrder (f² D)`**, the embedded order of
conductor `f`. -/
theorem leftOrder_lattice_periodPair_cmPointOfConductor {D : ℤ} (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0.le)
        (QuadraticOrder.mul_sq_emod_four_eq_zero_or_one hD f) := by
  rw [lattice_periodPair_cmPointOfConductor hD0 hD f, Subalgebra.leftOrder_toSubmodule]

end CanonicalCMPoint

/-! ### Concrete discriminants -/

section Examples

/-- At discriminant `-4`, `cmPoint (-4)` is `i` (`Complex.I`). -/
theorem coe_cmPoint_neg_four : (cmPoint (-4) (by decide) : ℂ) = I := by
  rw [coe_cmPoint_of_emod_four_eq_zero (by decide) (by decide)]
  have h4 : √(-((-4 : ℤ) : ℝ)) = 2 := by
    rw [show -((-4 : ℤ) : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  push_cast
  ring

/-- At discriminant `-3`, `cmPoint (-3)` is `(3 + i √3) / 2`. -/
theorem coe_cmPoint_neg_three :
    (cmPoint (-3) (by decide) : ℂ) = (3 + (√(3 : ℝ) : ℂ) * I) / 2 := by
  rw [coe_cmPoint_of_emod_four_eq_one (by decide) (by decide)]
  norm_num

/-- At discriminant `-4` and any positive conductor `f`, `cmPointOfConductor (-4) _ f` is `f · i`.
-/
theorem coe_cmPointOfConductor_neg_four (f : ℕ) [NeZero f] :
    (cmPointOfConductor (-4) (by decide) f : ℂ) = (f : ℂ) * I := by
  rw [coe_cmPointOfConductor, coe_cmPoint_neg_four]

end Examples

end TauCeti.BinaryQuadraticForm
