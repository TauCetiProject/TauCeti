/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Endomorphism
public import TauCeti.NumberTheory.BinaryQuadraticForm.HilbertClassPolynomial
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ComplexLattice
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.RingClassField
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Complex scalar multiplication of period lattices and singular moduli

Let `n > 0` with `-n ≡ 0, 1 mod 4`, and let `O_{-n} = QuadraticOrder.complexOrder (-n)` be the
imaginary quadratic order of discriminant `-n` in `ℂ`. This file proves the complex-lattice
dictionary connecting binary quadratic forms, period-lattice scalar multiplier orders
(`Submodule.leftOrder`), singular moduli, Picard groups, and ring class fields (no comparison with
algebraic elliptic-curve endomorphisms is asserted here):

1. **Exact multiplier orders of form roots**: for `f ∈ posDef n`, `(ℤ · root f + ℤ).leftOrder` is
   `complexOrder f.primPart.discrim`
   (`leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart`) and equals `O_{-n}` iff
   `f` is primitive (`leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive`);
   conversely, `τ ∈ ℍ` has `(ℤ τ + ℤ).leftOrder = O_{-n}` iff `τ = root f` for a primitive positive
   definite form `f` of discriminant `-n` (`leftOrder_lattice_periodPair_eq_complexOrder_iff`).
2. **Homothety classes, Picard group, and ring class Galois group**: sending `[f]` to
   `PeriodPair.HomothetyClass.mk (root f).periodPair` identifies `PosDefProperClass n`,
   `Pic (QuadraticOrder.numberFieldOrder (-n))`, and `Gal(H_O / K)` with homothety classes of
   lattices having left order `O_{-n}` (`cmHomothetyClassEquivPosDefProperClass`,
   `cmHomothetyClassEquivPic`, `cmHomothetyClassEquivGal`). Under `HomothetyClass.j`, these map
   onto the roots of `hilbertClassPolynomial n`, and an elliptic curve `E / ℂ` has period-lattice
   scalar multiplier order `E.periodLattice.leftOrder = O_{-n}` iff `E.j` is a root of
   `hilbertClassPolynomial n`
   (`WeierstrassCurve.leftOrder_periodLattice_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`).
3. **Discriminant uniqueness**: a singular modulus uniquely determines the discriminant of its CM
   order (`eq_of_singularModulus_eq`), so Hilbert class polynomials of distinct discriminants are
   coprime in `ℂ[X]` (`isCoprime_hilbertClassPolynomial_of_ne`).
4. **Canonical CM points `τ_D` and `f · τ_D`**: for `D < 0`, `cmPoint D` (`i √(-D) / 2` if
   `D ≡ 0 mod 4`, `(3 + i √(-D)) / 2` if `D ≢ 0 mod 4`, following D. H. Shin) has real `j`-invariant
   (`im_j_cmPoint`), and for `D ≡ 0, 1 mod 4` satisfies `τ_D² + B τ_D + C = 0`, spans
   `complexOrder D`, and has principal singular modulus `j(τ_{-n})` (`j_cmPoint_neg_natCast`). Its
   multiple `cmPointOfConductor D hD0 f = f · τ_D` spans the index-`f` suborder
   `complexOrder (f² D) = ℤ + ℤ · f ω_D` (of conductor `f` when `D` is fundamental) with left order
   `complexOrder (f² D)` (`leftOrder_lattice_periodPair_cmPointOfConductor`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.posDefProperClassToHomothetyClass`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivPosDefProperClass`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivPic`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivGal`: map and bijections between CM lattice
  homothety classes, `PosDefProperClass n`, `Pic(O_{-n})`, and `Gal(H_O / ℚ(√(-n)))`.
* `TauCeti.BinaryQuadraticForm.cmTraceCoeff`, `TauCeti.BinaryQuadraticForm.cmNormCoeff`,
  `TauCeti.BinaryQuadraticForm.cmForm`, `TauCeti.BinaryQuadraticForm.cmPoint`,
  `TauCeti.BinaryQuadraticForm.cmPointOfConductor`: `τ_D`, its monic form, and `f · τ_D`.

## Main results

* `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_eq_complexOrder_iff`: multiplier orders
  of form roots and CM upper-half-plane points.
* `PeriodPair.HomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`,
  `WeierstrassCurve.leftOrder_periodLattice_eq_complexOrder_iff_isRoot_hilbertClassPolynomial`:
  period-lattice scalar multiplier order `O_{-n}` iff `j` is a root of `hilbertClassPolynomial n`.
* `TauCeti.BinaryQuadraticForm.eq_of_singularModulus_eq`,
  `TauCeti.BinaryQuadraticForm.isCoprime_hilbertClassPolynomial_of_ne`: discriminant uniqueness and
  coprimality of Hilbert class polynomials.
* `TauCeti.BinaryQuadraticForm.cmPoint_quadratic`,
  `TauCeti.BinaryQuadraticForm.lattice_periodPair_cmPoint`,
  `TauCeti.BinaryQuadraticForm.j_cmPoint_neg_natCast`, `TauCeti.BinaryQuadraticForm.im_j_cmPoint`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_cmPointOfConductor`: properties of
  `τ_D` and `f · τ_D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, §10–11, and §13.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1–2.
* B. H. Gross and D. B. Zagier, *On singular moduli*, J. Reine Angew. Math. **355** (1985),
  191–220, §1.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§4–5, for the
  canonical CM point normalization `τ_D` with trace coefficient `B ∈ {0, -3}`.
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
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive (f : posDef n)
    (hfprim : f.1.IsPrimitive) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) := by
  refine le_antisymm (fun x hx ↦ ?_) (complexOrder_le_leftOrder_lattice_periodPair_root f)
  obtain ⟨m, k, rfl⟩ :=
    (UpperHalfPlane.mem_leftOrder_lattice_periodPair_iff_of_quadratic_of_linearCombination_eq_one
      ((eq_root_iff f (root f)).mp rfl) hfprim.exists_linearCombination_eq_one).mp hx
  set O := QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
    ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one)
  exact add_mem (O.intCast_mem m) (mul_mem (O.intCast_mem k)
    (complexOrderIdeal_le_complexOrder f.1 (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (mem_posDef.mp f.2).1 (a_mul_root_mem_complexOrderIdeal f)))

/-- If `f ∈ posDef n` is primitive, the left order of `f.1.complexOrderIdeal (-n)` is
`QuadraticOrder.complexOrder (-n)`. -/
theorem leftOrder_complexOrderIdeal_of_isPrimitive (f : posDef n) (hfprim : f.1.IsPrimitive) :
    (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) := by
  rw [leftOrder_complexOrderIdeal_posDef,
    leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive f hfprim]

/-- **Exact multiplier order of any positive definite form**: for `f ∈ posDef n` (not necessarily
primitive), `(root f).periodPair.lattice.leftOrder` is `complexOrder f.1.primPart.discrim`. -/
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder f.1.primPart.discrim (discrim_primPart_neg_of_posDef f).le
        f.1.primPart.discrim_emod_four_eq_zero_or_one := by
  obtain ⟨_, hfa⟩ := mem_posDef.mp f.2
  have hf0 : f.1 ≠ 0 := fun h ↦ by simp [h] at hfa
  have hdneg := discrim_primPart_neg_of_posDef f
  set m : ℕ := (-f.1.primPart.discrim).toNat
  have : NeZero m := ⟨by omega⟩
  have hg_disc : f.1.primPart.discrim = -m := by omega
  let g : posDef m := ⟨f.1.primPart, mem_posDef.mpr ⟨hg_disc, (a_primPart_pos_iff f.1).mpr hfa⟩⟩
  rw [← root_eq_root_of_eq_primPart (f := f) (g := g) rfl,
    leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive g
      (f.1.isPrimitive_primPart hf0)]
  exact QuadraticOrder.complexOrder_eq_iff.mpr hg_disc.symm

/-- **Primitivity criterion via the multiplier order**: for `f ∈ posDef n`, the left order of
`ℤ · root f + ℤ` equals `complexOrder (-n)` if and only if `f` is primitive. -/
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ↔
      f.1.IsPrimitive := by
  refine ⟨fun h ↦ ?_, leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive f⟩
  have hd : f.1.primPart.discrim = -n := QuadraticOrder.complexOrder_eq_iff.mp
    ((leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart f).symm.trans h)
  have hsq := f.1.discrim_eq_content_sq_mul
  rw [(mem_posDef.mp f.2).1, hd] at hsq
  have hne : (-(n : ℤ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hc2z : (f.1.content : ℤ) ^ 2 = 1 := mul_right_cancel₀ hne
    (show (f.1.content : ℤ) ^ 2 * -(n : ℤ) = 1 * -(n : ℤ) by linear_combination -hsq)
  have : f.1.content ^ 2 = 1 := by exact_mod_cast hc2z
  exact f.1.isPrimitive_iff.mpr (by nlinarith)

/-- For `f ∈ posDef n`, the left order of `f.1.complexOrderIdeal (-n)` equals `complexOrder (-n)`
if and only if `f` is primitive. -/
theorem leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive (f : posDef n) :
    (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ↔
      f.1.IsPrimitive := by
  rw [leftOrder_complexOrderIdeal_posDef,
    leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive]

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
    -- Since `complexOrder (-n) ≠ ⊥`, `τ` satisfies an integral quadratic `a τ² + b τ + c = 0`.
    have hne : τ.periodPair.lattice.leftOrder ≠ ⊥ := hleft ▸ QuadraticOrder.complexOrder_ne_bot
      (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) hn
    obtain ⟨a, b, c, ha, hrel⟩ := UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff.mp hne
    let f₀ : BinaryQuadraticForm ℤ := ⟨a, b, c⟩
    have hd₀ : f₀.discrim < 0 := discrim_neg_of_quadratic_upperHalfPlane ha.ne' hrel
    set m : ℕ := (-f₀.discrim).toNat
    have : NeZero m := ⟨by omega⟩
    let fp : posDef m := ⟨f₀, mem_posDef.mpr ⟨by omega, ha⟩⟩
    have hroot₀ : τ = root fp := (eq_root_iff fp τ).mpr hrel
    -- Dividing `f₀` by its content gives a primitive form of discriminant `-n` with the same root.
    have hprim_ord := leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart fp
    rw [← hroot₀, hleft] at hprim_ord
    have hd_prim : f₀.primPart.discrim = -n :=
      (QuadraticOrder.complexOrder_eq_iff.mp hprim_ord).symm
    have hf₀_ne : f₀ ≠ 0 := fun h ↦ ha.ne' (by simpa [f₀] using congrArg BinaryQuadraticForm.a h)
    exact ⟨⟨f₀.primPart, (mem_posDef_inf_primitiveForms n).mpr
      ⟨hd_prim, (a_primPart_pos_iff f₀).mpr ha, f₀.isPrimitive_primPart hf₀_ne⟩⟩,
      (root_eq_root_of_eq_primPart (f := fp) rfl).trans hroot₀.symm⟩
  · rintro ⟨f, rfl⟩
    exact leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive
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
  rw [← PeriodPair.HomothetyClass.mk_periodPair_smul γ
    (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩), ← root_smul]
  exact congrArg (fun z : ℍ ↦ PeriodPair.HomothetyClass.mk z.periodPair)
    (congrArg root (Subtype.ext ((SubMulAction.val_smul γ g).trans
      (SubMulAction.val_smul γ _).symm)))

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
        (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩).periodPair := (rfl)

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
  exact leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive
    ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩
    ((mem_posDef_inf_primitiveForms n).mp f.2).2.2

/-- **Image of `posDefProperClassToHomothetyClass`**: a homothety class of complex period lattices
lies in the image of `PosDefProperClass n` if and only if its left order is `complexOrder (-n)`. -/
theorem mem_range_posDefProperClassToHomothetyClass_iff
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) {x : PeriodPair.HomothetyClass} :
    x ∈ Set.range (posDefProperClassToHomothetyClass n) ↔
      x.leftOrder = QuadraticOrder.complexOrder (-n)
        (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn := by
  refine ⟨fun ⟨q, hq⟩ ↦ hq ▸ leftOrder_posDefProperClassToHomothetyClass n hn q, fun hx ↦ ?_⟩
  obtain ⟨τ, rfl⟩ := PeriodPair.HomothetyClass.mk_periodPair_surjective x
  rw [PeriodPair.HomothetyClass.leftOrder_mk,
    leftOrder_lattice_periodPair_eq_complexOrder_iff hn] at hx
  obtain ⟨f, rfl⟩ := hx
  exact ⟨Quotient.mk _ f, rfl⟩

/-- **Bijection between CM lattice homothety classes and proper classes of forms**: homothety
classes of period pairs with left order `complexOrder (-n)` correspond bijectively to
`PosDefProperClass n`. -/
def cmHomothetyClassEquivPosDefProperClass (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃ PosDefProperClass n :=
  ((Equiv.ofInjective (posDefProperClassToHomothetyClass n)
    posDefProperClassToHomothetyClass_injective).trans
    (Equiv.subtypeEquivRight fun _ ↦ mem_range_posDefProperClassToHomothetyClass_iff n hn)).symm

/-- Inverse evaluation of `cmHomothetyClassEquivPosDefProperClass` is
`posDefProperClassToHomothetyClass`. -/
@[simp] theorem coe_cmHomothetyClassEquivPosDefProperClass_symm
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n) :
    (((cmHomothetyClassEquivPosDefProperClass n hn).symm q) : PeriodPair.HomothetyClass) =
      posDefProperClassToHomothetyClass n q := by simp [cmHomothetyClassEquivPosDefProperClass]

/-- Forward evaluation of `cmHomothetyClassEquivPosDefProperClass` on the homothety class of `q`
recovers `q`. -/
@[simp] theorem cmHomothetyClassEquivPosDefProperClass_posDefProperClassToHomothetyClass
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n)
    (hq : (posDefProperClassToHomothetyClass n q).leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn) :
    cmHomothetyClassEquivPosDefProperClass n hn ⟨posDefProperClassToHomothetyClass n q, hq⟩ = q :=
  (cmHomothetyClassEquivPosDefProperClass n hn).symm.injective <| by
    rw [Equiv.symm_apply_apply]; ext1
    exact (coe_cmHomothetyClassEquivPosDefProperClass_symm n hn q).symm

/-- Applying `posDefProperClassToHomothetyClass` after `cmHomothetyClassEquivPosDefProperClass`
recovers the underlying homothety class. -/
@[simp] theorem posDefProperClassToHomothetyClass_cmHomothetyClassEquivPosDefProperClass
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    posDefProperClassToHomothetyClass n (cmHomothetyClassEquivPosDefProperClass n hn x) = x.1 := by
  simpa only [coe_cmHomothetyClassEquivPosDefProperClass_symm] using
    congrArg Subtype.val ((cmHomothetyClassEquivPosDefProperClass n hn).symm_apply_apply x)

/-- **Bijection between CM lattice homothety classes and the Picard group** of the quadratic order
of discriminant `-n`. -/
def cmHomothetyClassEquivPic (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃
      @GlobalNumberFields.Pic (QuadraticAlgebra ℚ (-((n : ℤ) : ℚ)) 0)
        (inferInstanceAs (Field (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
        (inferInstanceAs (NumberField (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
        (QuadraticOrder.numberFieldOrder (-n : ℤ) hn) :=
  (cmHomothetyClassEquivPosDefProperClass n hn).trans (posDefProperClassEquivPic n hn)

/-- `cmHomothetyClassEquivPic` sends a CM homothety class to the Picard class of its corresponding
proper form class. -/
@[simp] theorem cmHomothetyClassEquivPic_apply (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    cmHomothetyClassEquivPic n hn x =
      posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) :=
  posDefProperClassEquivPic_apply n hn (cmHomothetyClassEquivPosDefProperClass n hn x)

/-- Inverse evaluation of `cmHomothetyClassEquivPic` maps a Picard class to the homothety class of
its corresponding proper form class. -/
@[simp] theorem coe_cmHomothetyClassEquivPic_symm (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (c : @GlobalNumberFields.Pic (QuadraticAlgebra ℚ (-((n : ℤ) : ℚ)) 0)
      (inferInstanceAs (Field (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
      (inferInstanceAs (NumberField (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
      (QuadraticOrder.numberFieldOrder (-n : ℤ) hn)) :
    (((cmHomothetyClassEquivPic n hn).symm c) : PeriodPair.HomothetyClass) =
      posDefProperClassToHomothetyClass n ((posDefProperClassEquivPic n hn).symm c) :=
  coe_cmHomothetyClassEquivPosDefProperClass_symm n hn ((posDefProperClassEquivPic n hn).symm c)

/-- **Bijection between CM lattice homothety classes and the ring class Galois group**
`Gal(H_O / ℚ(√(-n)))`. -/
def cmHomothetyClassEquivGal (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} ≃
      Gal(ClassFieldTheory.ringClassField (QuadraticOrder.numberFieldOrder (-n) hn) /
        QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
  (cmHomothetyClassEquivPosDefProperClass n hn).trans (posDefProperClassEquivGal n hn)

-- Not `@[simp]`: `Rat.intCast_neg` rewrites `((-n : ℤ) : ℚ)` in `DFunLike.coe`'s codomain.
/-- `cmHomothetyClassEquivGal` sends a CM homothety class to the ring class Artin symbol of its
corresponding proper form class. -/
theorem cmHomothetyClassEquivGal_apply (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (x : {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    cmHomothetyClassEquivGal n hn x =
      posDefProperClassEquivGal n hn (cmHomothetyClassEquivPosDefProperClass n hn x) := (rfl)

-- Not `@[simp]`: `Rat.intCast_neg` rewrites `((-n : ℤ) : ℚ)` in `Equiv.symm`'s codomain.
/-- Inverse evaluation of `cmHomothetyClassEquivGal` maps an Artin element to the homothety class of
its corresponding proper form class. -/
theorem coe_cmHomothetyClassEquivGal_symm (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (σ : Gal(ClassFieldTheory.ringClassField
      (QuadraticOrder.numberFieldOrder (-n) hn)/QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) :
    (((cmHomothetyClassEquivGal n hn).symm σ) : PeriodPair.HomothetyClass) =
      posDefProperClassToHomothetyClass n ((posDefProperClassEquivGal n hn).symm σ) :=
  coe_cmHomothetyClassEquivPosDefProperClass_symm n hn ((posDefProperClassEquivGal n hn).symm σ)

/-- The number of homothety classes of complex period lattices with left order
`complexOrder (-n)` equals `#Pic(O_{-n})`. -/
theorem nat_card_cmHomothetyClass (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    Nat.card {x : PeriodPair.HomothetyClass // x.leftOrder = QuadraticOrder.complexOrder (-n)
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
  exact ⟨fun ⟨q, h⟩ ↦ ⟨q, h ▸ (j_posDefProperClassToHomothetyClass n q).symm⟩,
    fun ⟨q, hq⟩ ↦ ⟨q, j_injective ((j_posDefProperClassToHomothetyClass n q).trans hq)⟩⟩

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

/-- **Period-lattice multiplier-order characterization for complex Weierstrass elliptic curves**:
for an elliptic curve `E / ℂ` and `n > 0` with `-n ≡ 0, 1 mod 4`, the period-lattice scalar
multiplier order `E.periodLattice.leftOrder` equals `complexOrder (-n)` if and only if `E.j` is a
root of `hilbertClassPolynomial n`. -/
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
  obtain ⟨f₁, rfl⟩ := Quotient.exists_rep q₁; obtain ⟨f₂, rfl⟩ := Quotient.exists_rep q₂
  have hm : (-m : ℤ) % 4 = 0 ∨ (-m : ℤ) % 4 = 1 :=
    ((mem_posDef_inf_primitiveForms m).mp f₁.2).1 ▸ f₁.1.discrim_emod_four_eq_zero_or_one
  have hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1 :=
    ((mem_posDef_inf_primitiveForms n).mp f₂.2).1 ▸ f₂.1.discrim_emod_four_eq_zero_or_one
  have hx : posDefProperClassToHomothetyClass m (Quotient.mk _ f₁) =
      posDefProperClassToHomothetyClass n (Quotient.mk _ f₂) :=
    PeriodPair.HomothetyClass.j_injective
      (by simpa only [j_posDefProperClassToHomothetyClass] using h)
  have hord := congrArg PeriodPair.HomothetyClass.leftOrder hx
  rw [leftOrder_posDefProperClassToHomothetyClass m hm,
    leftOrder_posDefProperClassToHomothetyClass n hn] at hord
  have := QuadraticOrder.complexOrder_eq_iff.mp hord; omega

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
  have := Fintype.ofFinite (PosDefProperClass m); have := Fintype.ofFinite (PosDefProperClass n)
  rw [hilbertClassPolynomial_eq_prod, hilbertClassPolynomial_eq_prod]
  exact IsCoprime.prod_left fun q₁ _ ↦ IsCoprime.prod_right fun q₂ _ ↦
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun heq ↦ hmn (eq_of_singularModulus_eq heq)).isUnit

end Uniqueness

/-! ### Canonical CM point `τ_D` and rescaled CM point `f · τ_D` -/

section CanonicalCMPoint

/-- Middle coefficient `B ∈ {0, -3}` of `cmForm D`: `0` when `D ≡ 0 mod 4`, and `-3` whenever
`D ≢ 0 mod 4` (in particular when `D ≡ 1 mod 4`). -/
def cmTraceCoeff (D : ℤ) : ℤ := if D % 4 = 0 then 0 else -3

/-- Definitional expansion of `cmTraceCoeff`. -/
theorem cmTraceCoeff_def (D : ℤ) : cmTraceCoeff D = if D % 4 = 0 then 0 else -3 := (rfl)

/-- When `D % 4 = 0`, `cmTraceCoeff D = 0`. -/
theorem cmTraceCoeff_of_emod_four_eq_zero {D : ℤ} (h : D % 4 = 0) : cmTraceCoeff D = 0 := by
  simp [cmTraceCoeff, h]

/-- When `D % 4 ≠ 0`, `cmTraceCoeff D = -3`. -/
theorem cmTraceCoeff_of_emod_four_ne_zero {D : ℤ} (h : D % 4 ≠ 0) : cmTraceCoeff D = -3 := by
  simp [cmTraceCoeff, h]

/-- When `D % 4 = 1`, `cmTraceCoeff D = -3`. -/
theorem cmTraceCoeff_of_emod_four_eq_one {D : ℤ} (h : D % 4 = 1) : cmTraceCoeff D = -3 :=
  cmTraceCoeff_of_emod_four_ne_zero (by omega)

/-- `cmTraceCoeff D` is always `0` or `-3`. -/
theorem cmTraceCoeff_eq_zero_or_neg_three (D : ℤ) :
    cmTraceCoeff D = 0 ∨ cmTraceCoeff D = -3 := by
  unfold cmTraceCoeff; split_ifs <;> simp

/-- Integer quotient `((cmTraceCoeff D)² - D) / 4`; exact when `D ≡ 0, 1 mod 4`
(`four_mul_cmNormCoeff`), giving the constant term of `τ_D² + B τ_D + C = 0` for `D < 0`. -/
def cmNormCoeff (D : ℤ) : ℤ := ((cmTraceCoeff D) ^ 2 - D) / 4

/-- Definitional expansion of `cmNormCoeff`. -/
theorem cmNormCoeff_def (D : ℤ) : cmNormCoeff D = ((cmTraceCoeff D) ^ 2 - D) / 4 := (rfl)

/-- When `D % 4 = 0`, `cmNormCoeff D = -D / 4`. -/
theorem cmNormCoeff_of_emod_four_eq_zero {D : ℤ} (h : D % 4 = 0) : cmNormCoeff D = -D / 4 := by
  simp [cmNormCoeff, cmTraceCoeff_of_emod_four_eq_zero h]

/-- When `D % 4 ≠ 0`, `cmNormCoeff D = (9 - D) / 4`. -/
theorem cmNormCoeff_of_emod_four_ne_zero {D : ℤ} (h : D % 4 ≠ 0) :
    cmNormCoeff D = (9 - D) / 4 := by
  rw [cmNormCoeff, cmTraceCoeff_of_emod_four_ne_zero h]; norm_num

/-- When `D % 4 = 1`, `cmNormCoeff D = (9 - D) / 4`. -/
theorem cmNormCoeff_of_emod_four_eq_one {D : ℤ} (h : D % 4 = 1) : cmNormCoeff D = (9 - D) / 4 :=
  cmNormCoeff_of_emod_four_ne_zero (by omega)

/-- For `D ≡ 0, 1 mod 4`, `4 * cmNormCoeff D = (cmTraceCoeff D)² - D`. -/
theorem four_mul_cmNormCoeff {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    4 * cmNormCoeff D = (cmTraceCoeff D) ^ 2 - D := by
  refine Int.mul_ediv_cancel' ?_
  rcases hD with h0 | h1
  · rw [cmTraceCoeff_of_emod_four_eq_zero h0]; omega
  · rw [cmTraceCoeff_of_emod_four_eq_one h1]; omega

/-- Monic form `x² + cmTraceCoeff D · x y + cmNormCoeff D · y²` (totalized on `ℤ`); has
discriminant `D` when `D ≡ 0, 1 mod 4`, and is positive definite with root `τ_D` when `D < 0`. -/
def cmForm (D : ℤ) : BinaryQuadraticForm ℤ := ⟨1, cmTraceCoeff D, cmNormCoeff D⟩

/-- Leading coefficient of `cmForm D`. -/
@[simp] theorem cmForm_a (D : ℤ) : (cmForm D).a = 1 := (rfl)

/-- Middle coefficient of `cmForm D`. -/
@[simp] theorem cmForm_b (D : ℤ) : (cmForm D).b = cmTraceCoeff D := (rfl)

/-- Last coefficient of `cmForm D`. -/
@[simp] theorem cmForm_c (D : ℤ) : (cmForm D).c = cmNormCoeff D := (rfl)

/-- For `D ≡ 0, 1 mod 4`, `cmForm D` has discriminant `D`. -/
theorem discrim_cmForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) : (cmForm D).discrim = D := by
  have h4 := four_mul_cmNormCoeff hD
  rw [discrim_def, discrim, cmForm_a, cmForm_b, cmForm_c]; linear_combination -h4

/-- `cmForm D` is primitive. -/
theorem isPrimitive_cmForm (D : ℤ) : (cmForm D).IsPrimitive :=
  isPrimitive_of_linearCombination_eq_one _ 1 0 0 (by simp)

/-- For `n > 0` with `-n ≡ 0, 1 mod 4`, `cmForm (-n)` is primitive positive definite of
discriminant `-n`. -/
theorem cmForm_mem_posDef_inf_primitiveForms (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    cmForm (-n) ∈ posDef n ⊓ primitiveForms (-n) :=
  (mem_posDef_inf_primitiveForms n).mpr ⟨discrim_cmForm hn, by simp, isPrimitive_cmForm _⟩

/-- **Canonical CM point `τ_D ∈ ℍ`** for `D < 0`: `i √(-D) / 2` when `D ≡ 0 mod 4`, and
`(3 + i √(-D)) / 2` when `D ≢ 0 mod 4` (in particular for `D ≡ 1 mod 4`). -/
def cmPoint (D : ℤ) (hD0 : D < 0) : ℍ :=
  ⟨⟨-(cmTraceCoeff D : ℝ) / 2, √(-(D : ℝ)) / 2⟩,
    half_pos (Real.sqrt_pos.mpr (neg_pos.mpr (Int.cast_lt_zero.mpr hD0)))⟩

/-- Real part of `cmPoint D hD0`. -/
@[simp] theorem re_cmPoint (D : ℤ) (hD0 : D < 0) :
    (cmPoint D hD0).re = -(cmTraceCoeff D : ℝ) / 2 := (rfl)

/-- Imaginary part of `cmPoint D hD0`. -/
@[simp] theorem im_cmPoint (D : ℤ) (hD0 : D < 0) : (cmPoint D hD0).im = √(-(D : ℝ)) / 2 := (rfl)

/-- Complex value of `cmPoint D hD0`. -/
theorem coe_cmPoint (D : ℤ) (hD0 : D < 0) :
    (cmPoint D hD0 : ℂ) = (-(cmTraceCoeff D : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  simp [← (cmPoint D hD0).re_add_im, add_div, mul_div_right_comm]

/-- When `D % 4 = 0`, `cmPoint D hD0 = i √(-D) / 2`. -/
theorem coe_cmPoint_of_emod_four_eq_zero {D : ℤ} (hD0 : D < 0) (h0 : D % 4 = 0) :
    (cmPoint D hD0 : ℂ) = (√(-(D : ℝ)) : ℂ) * I / 2 := by
  simp [coe_cmPoint, cmTraceCoeff_of_emod_four_eq_zero h0]

/-- When `D % 4 = 1`, `cmPoint D hD0 = (3 + i √(-D)) / 2`. -/
theorem coe_cmPoint_of_emod_four_eq_one {D : ℤ} (hD0 : D < 0) (h1 : D % 4 = 1) :
    (cmPoint D hD0 : ℂ) = (3 + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  rw [coe_cmPoint, cmTraceCoeff_of_emod_four_eq_one h1]; norm_num

/-- **Monic integral quadratic satisfied by `τ_D`** for `D < 0` with `D ≡ 0, 1 mod 4`. -/
theorem cmPoint_quadratic {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0 : ℂ) ^ 2 + cmTraceCoeff D * (cmPoint D hD0 : ℂ) + cmNormCoeff D = 0 := by
  have h4 : (4 : ℂ) * (cmNormCoeff D : ℂ) = (cmTraceCoeff D : ℂ) ^ 2 - D := by
    exact_mod_cast four_mul_cmNormCoeff hD
  have hs : (√(-(D : ℝ)) : ℂ) * (√(-(D : ℝ)) : ℂ) = -(D : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (neg_nonneg.mpr (Int.cast_nonpos.mpr hD0.le))]
    push_cast; ring
  have hsqrt : ((√(-(D : ℝ)) : ℂ) * I) ^ 2 = D := by
    linear_combination (I * I) * hs - I_mul_I * (D : ℂ)
  rw [coe_cmPoint]; linear_combination (hsqrt + h4) / 4

/-- `cmPoint D hD0` equals `QuadraticOrder.complexGenerator D - (D + cmTraceCoeff D) / 2`. -/
theorem coe_cmPoint_eq_complexGenerator_sub {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0 : ℂ) =
      QuadraticOrder.complexGenerator D - (((D + cmTraceCoeff D) / 2 : ℤ) : ℂ) := by
  have hdiv : (2 : ℤ) ∣ D + cmTraceCoeff D := by
    rcases hD with h0 | h1
    · rw [cmTraceCoeff_of_emod_four_eq_zero h0]; omega
    · rw [cmTraceCoeff_of_emod_four_eq_one h1]; omega
  have h2 : (2 : ℂ) * (((D + cmTraceCoeff D) / 2 : ℤ) : ℂ) = (D : ℂ) + cmTraceCoeff D := by
    exact_mod_cast Int.mul_ediv_cancel' hdiv
  rw [coe_cmPoint, QuadraticOrder.complexGenerator_def]; linear_combination h2 / 2

/-- **The period lattice `ℤ · τ_D + ℤ` equals `complexOrder D`** on the nose. -/
theorem lattice_periodPair_cmPoint {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (cmPoint D hD0).periodPair.lattice =
      Subalgebra.toSubmodule (QuadraticOrder.complexOrder D hD0.le hD) := by
  ext z
  rw [PeriodPair.mem_lattice, Subalgebra.mem_toSubmodule, QuadraticOrder.mem_complexOrder_iff]
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one, coe_cmPoint_eq_complexGenerator_sub hD0 hD]
  set q : ℤ := (D + cmTraceCoeff D) / 2
  exact ⟨fun ⟨m, n, h⟩ ↦ ⟨n - m * q, m, by rw [← h]; push_cast; ring⟩,
    fun ⟨m, k, h⟩ ↦ ⟨k, m + k * q, by rw [h]; push_cast; ring⟩⟩

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

/-- For `D ≡ 0, 1 mod 4`, `cmForm D` is properly `SL(2, ℤ)`-equivalent to `principalForm D`. -/
theorem exists_smul_principalForm_eq_cmForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ γ : SL(2, ℤ), γ • principalForm D = cmForm D := by
  rcases hD with h0 | h1
  · refine ⟨1, ?_⟩
    have h2 : D % 2 = 0 := by omega
    ext <;> simp [cmTraceCoeff_of_emod_four_eq_zero h0, cmNormCoeff_of_emod_four_eq_zero h0, h2]
  · refine ⟨_root_.ModularGroup.T ^ (2 : ℤ), ?_⟩
    have h2 : D % 2 = 1 := by omega
    rw [T_zpow_smul]
    ext <;> simp [cmTraceCoeff_of_emod_four_eq_one h1, cmNormCoeff_of_emod_four_eq_one h1, h2]
    omega

/-- **The `j`-invariant of `cmPoint (-n)` is the principal singular modulus**, hence a root of
`hilbertClassPolynomial n`. -/
theorem j_cmPoint_neg_natCast (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    ModularForm.j (cmPoint (-n) (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n)))) =
      singularModulus n (Quotient.mk _
        ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩) := by
  obtain ⟨γ, hγ⟩ := exists_smul_principalForm_eq_cmForm hn
  rw [cmPoint_neg_natCast_eq_root_cmForm n hn, singularModulus_mk]
  let p : posDef n := ⟨principalForm (-n), inf_le_left (b := primitiveForms (-n))
    (principalForm_mem_posDef_inf_primitiveForms n hn)⟩
  have hsub : (⟨cmForm (-n), inf_le_left (b := primitiveForms (-n))
      (cmForm_mem_posDef_inf_primitiveForms n hn)⟩ : posDef n) = γ • p :=
    Subtype.ext (hγ.symm.trans (SubMulAction.val_smul γ p).symm)
  rw [hsub, root_smul, ModularForm.j_smul_SL2Z]

/-- **`j(τ_D)` is real** for every `D < 0`. -/
theorem im_j_cmPoint {D : ℤ} (hD0 : D < 0) : (ModularForm.j (cmPoint D hD0)).im = 0 := by
  have hJT : J • cmPoint D hD0 = _root_.ModularGroup.T ^ cmTraceCoeff D • cmPoint D hD0 := by
    apply UpperHalfPlane.ext
    rw [coe_J_smul, modular_T_zpow_smul, coe_vadd, coe_cmPoint, map_div₀, map_add, map_neg,
      map_intCast, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
    push_cast; ring
  exact Complex.conj_eq_iff_im.mp
    ((ModularForm.j_J_smul (cmPoint D hD0)).symm.trans (by rw [hJT, ModularForm.j_smul_SL2Z]))

/-- **Rescaled CM point `f · τ_D ∈ ℍ`** (`f > 0`): spans the suborder `complexOrder (f² D)` of
index `f` in `complexOrder D` for `D ≡ 0, 1 mod 4` (conductor `f` when `D` is fundamental). -/
def cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] : ℍ :=
  ⟨(f : ℂ) * (cmPoint D hD0 : ℂ), by
    simpa [mul_im, coe_im] using
      mul_pos (Nat.cast_pos.mpr (NeZero.pos f)) (cmPoint D hD0).im_pos⟩

/-- Coercion of `cmPointOfConductor D hD0 f` to `ℂ` is `f · τ_D`. -/
@[simp] theorem coe_cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f : ℂ) = (f : ℂ) * (cmPoint D hD0 : ℂ) := (rfl)

/-- Real part of `cmPointOfConductor D hD0 f`. -/
@[simp] theorem re_cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).re = -(f : ℝ) * (cmTraceCoeff D : ℝ) / 2 := by
  rw [← coe_re, coe_cmPointOfConductor]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, coe_re, re_cmPoint]; ring

/-- Imaginary part of `cmPointOfConductor D hD0 f`. -/
@[simp] theorem im_cmPointOfConductor (D : ℤ) (hD0 : D < 0) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).im = (f : ℝ) * √(-(D : ℝ)) / 2 := by
  rw [← coe_im, coe_cmPointOfConductor]
  simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, coe_im, im_cmPoint]; ring

/-- At `f = 1`, `cmPointOfConductor D hD0 1` equals `cmPoint D hD0`. -/
@[simp] theorem cmPointOfConductor_one (D : ℤ) (hD0 : D < 0) :
    cmPointOfConductor D hD0 1 = cmPoint D hD0 := by ext1; simp

/-- **Monic integral quadratic satisfied by `f · τ_D`** for `D < 0` with `D ≡ 0, 1 mod 4`. -/
theorem cmPointOfConductor_quadratic {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f : ℂ) ^ 2 +
      (((f : ℤ) * cmTraceCoeff D : ℤ) : ℂ) * (cmPointOfConductor D hD0 f : ℂ) +
      (((f : ℤ) ^ 2 * cmNormCoeff D : ℤ) : ℂ) = 0 := by
  rw [coe_cmPointOfConductor]; push_cast
  linear_combination (f : ℂ) ^ 2 * cmPoint_quadratic hD0 hD

/-- **The period lattice `ℤ · (f τ_D) + ℤ` equals `complexOrder (f² D)`**. -/
theorem lattice_periodPair_cmPointOfConductor {D : ℤ} (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).periodPair.lattice =
      Subalgebra.toSubmodule (QuadraticOrder.complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0.le)
        (QuadraticOrder.sq_mul_emod_four_eq_zero_or_one hD f)) := by
  ext z
  rw [PeriodPair.mem_lattice, Subalgebra.mem_toSubmodule,
    QuadraticOrder.mem_complexOrder_sq_mul_iff hD0.le hD f]
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one, coe_cmPointOfConductor,
    coe_cmPoint_eq_complexGenerator_sub hD0 hD]
  set q : ℤ := (D + cmTraceCoeff D) / 2
  exact ⟨fun ⟨m, n, h⟩ ↦ ⟨n - m * f * q, m, by rw [← h]; push_cast; ring⟩,
    fun ⟨m, k, h⟩ ↦ ⟨k, m + k * f * q, by rw [h]; push_cast; ring⟩⟩

/-- **The multiplier order of `ℤ · (f τ_D) + ℤ` is `complexOrder (f² D)`**, the suborder of index
`f` in `complexOrder D` (and of conductor `f` when `D` is a negative fundamental discriminant). -/
theorem leftOrder_lattice_periodPair_cmPointOfConductor {D : ℤ} (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0.le)
        (QuadraticOrder.sq_mul_emod_four_eq_zero_or_one hD f) := by
  rw [lattice_periodPair_cmPointOfConductor hD0 hD f, Subalgebra.leftOrder_toSubmodule]

/-- `UpperHalfPlane.quadraticOrder` at `cmPointOfConductor D hD0 f` agrees with
`complexOrder (f² D)`. -/
theorem quadraticOrder_cmPointOfConductor {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) [NeZero f] :
    (cmPointOfConductor D hD0 f).quadraticOrder (cmPointOfConductor_quadratic hD0 hD f) =
      QuadraticOrder.complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0.le)
        (QuadraticOrder.sq_mul_emod_four_eq_zero_or_one hD f) := by
  rw [← UpperHalfPlane.leftOrder_lattice_periodPair_eq_quadraticOrder]
  exact leftOrder_lattice_periodPair_cmPointOfConductor hD0 hD f

end CanonicalCMPoint

/-! ### Concrete discriminants -/

section Examples

/-- At discriminant `-4`, `cmPoint (-4)` is `i` (`Complex.I`). -/
theorem coe_cmPoint_neg_four : (cmPoint (-4) (by decide) : ℂ) = I := by
  rw [coe_cmPoint_of_emod_four_eq_zero (by decide) (by decide)]
  rw [show -((-4 : ℤ) : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  push_cast; ring

/-- At discriminant `-3`, `cmPoint (-3)` is `(3 + i √3) / 2`. -/
theorem coe_cmPoint_neg_three :
    (cmPoint (-3) (by decide) : ℂ) = (3 + (√(3 : ℝ) : ℂ) * I) / 2 := by
  rw [coe_cmPoint_of_emod_four_eq_one (by decide) (by decide)]; norm_num

/-- At discriminant `-4` and any positive `f`, `cmPointOfConductor (-4) _ f` is `f · i`. -/
theorem coe_cmPointOfConductor_neg_four (f : ℕ) [NeZero f] :
    (cmPointOfConductor (-4) (by decide) f : ℂ) = (f : ℂ) * I := by
  rw [coe_cmPointOfConductor, coe_cmPoint_neg_four]

end Examples

end TauCeti.BinaryQuadraticForm
