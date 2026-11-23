/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.ComplexMultiplication
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ComplexLattice
public import TauCeti.NumberTheory.QuadraticOrder.ComplexFractionalIdeal
import TauCeti.Algebra.Algebra.Operations

/-!
# The ideal-class action on CM lattices

Let `n > 0` with `-n ≡ 0, 1 mod 4`, let `K = ℚ(√(-n))`, let `O` be the quadratic order of
discriminant `-n` and let `ι : K → ℂ` be the complex embedding `QuadraticAlgebra.complexEmbedding`
sending `√(-n)` to `i √n`. A fractional ideal `𝔞` of `O` gives the `ℤ`-submodule `ι(𝔞)` of `ℂ`
(`TauCeti.QuadraticOrder.complexFractionalIdeal`), which sends the ideal of a form to its complex
submodule (`complexFractionalIdeal_fractionalIdeal`).

For an invertible ideal `𝔞`, `ι(𝔞)` is a period lattice
(`exists_periodPair_lattice_eq_complexFractionalIdeal`) with multiplier order `O`
(`leftOrder_lattice_eq_complexOrder_of_lattice_eq`), whose homothety class is the CM class attached
to the Picard class `[𝔞]` by the dictionary `cmHomothetyClassEquivPic`
(`mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq`,
`cmHomothetyClassEquivPic_mk_of_lattice_eq`). So `Pic(O)` acts on the homothety classes of
lattices with multiplier order `O` by multiplication of lattices,

```text
[𝔞] • [Λ] = [ι(𝔞) Λ]
```

(`coe_smul_of_lattice_eq_mul`, the product being a period lattice by
`exists_periodPair_lattice_eq_complexFractionalIdeal_mul`), and this action is simply transitive
(`instIsPretransitivePicCMHomothetyClass`, `stabilizer_pic_eq_bot`). Since `j` determines the
homothety class, the CM `j`-values of discriminant `-n`, the roots of the Hilbert class polynomial,
are exactly the `j`-invariants of the lattices `ι(𝔞)` of the invertible ideals `𝔞` of `O`
(`isRoot_hilbertClassPolynomial_iff_exists_lattice_eq`), and `[𝔞]` sends `j(Λ)` to `j(ι(𝔞) Λ)`.

The action is the one through which the reciprocity law of complex multiplication describes the
Artin action on the ring class field; that comparison is not made here.

## Main definitions

* `TauCeti.BinaryQuadraticForm.instMulActionPicCMHomothetyClass`: the action of `Pic(O)` on
  homothety classes of lattices with multiplier order `O`.

## Main results

* `TauCeti.BinaryQuadraticForm.mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq`,
  `TauCeti.BinaryQuadraticForm.cmHomothetyClassEquivPic_mk_of_lattice_eq`: the homothety class of
  `ι(𝔞)` corresponds to `[𝔞]`.
* `TauCeti.BinaryQuadraticForm.coe_smul_of_lattice_eq_mul`: `[𝔞] • [Λ] = [ι(𝔞) Λ]`.
* `TauCeti.BinaryQuadraticForm.instIsPretransitivePicCMHomothetyClass`,
  `TauCeti.BinaryQuadraticForm.stabilizer_pic_eq_bot`: the action is simply transitive.
* `TauCeti.BinaryQuadraticForm.isRoot_hilbertClassPolynomial_iff_exists_lattice_eq`: the CM
  `j`-values are the `j`-invariants of the lattices of invertible ideals.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §10 and §11.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1,
  Proposition 1.2 (stated there with the inverse convention `[𝔞] • [Λ] = [𝔞⁻¹ Λ]`).
-/

public section
noncomputable section

open QuadraticAlgebra FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields QuadraticOrder

/-- The complex lattice of the fractional ideal of a form is the complex submodule of the form. -/
@[simp] theorem complexFractionalIdeal_fractionalIdeal (f : BinaryQuadraticForm ℤ) {D : ℤ}
    (hD0 : D ≤ 0) (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    complexFractionalIdeal hD0 (f.fractionalIdeal D hf) = f.complexOrderIdeal D hD0 hf := by
  rw [complexFractionalIdeal_def, fractionalIdeal_restrictScalars, complexOrderIdeal_def]

section PicAction

variable (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)

/-- Every invertible ideal of the order of discriminant `-n` has, up to a positive rational factor,
the ideal of a primitive positive definite form `g`, so its complex lattice is a rescaling of
`ℤ · root g + ℤ`, and its Picard class is the class of `g`. -/
private theorem exists_complexFractionalIdeal_eq_lattice_smul
    (I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) :
    ∃ (g : ↥(posDef n ⊓ primitiveForms (-n))) (c : ℂˣ),
      complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) =
        (c • (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.property⟩).periodPair).lattice ∧
      (numberFieldOrder (-n : ℤ) hn).mkPic I = posDefProperClassToPic n hn (Quotient.mk _ g) := by
  obtain ⟨f, hf, hp, ha, -, u, -, -, hI⟩ :=
    exists_pos_primitive_form_invertibleFractionalIdeal_eq (-n : ℤ) hn I
  let g : ↥(posDef n ⊓ primitiveForms (-n)) :=
    ⟨f, (mem_posDef_inf_primitiveForms n).mpr ⟨hf, ha, hp⟩⟩
  have hn0 : ((-n : ℤ) : ℚ) ≤ 0 :=
    Int.cast_nonpos.mpr (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
  have hu0 : complexEmbedding hn0 (u : QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) ≠ 0 :=
    (_root_.map_ne_zero _).mpr u.ne_zero
  refine ⟨g, Units.mk0 _ hu0 * Units.mk0 (f.a : ℂ) (Int.cast_ne_zero.mpr ha.ne'), ?_, ?_⟩
  · rw [hI, Units.val_mul, coe_toPrincipalIdeal, coe_invertibleFractionalIdeal,
      complexFractionalIdeal_spanSingleton_mul, complexFractionalIdeal_fractionalIdeal,
      mul_smul, PeriodPair.lattice_smul _ (Units.mk0 _ hu0)]
    exact congrArg (Submodule.map _)
      (complexOrderIdeal_eq_lattice_smul_periodPair_root
        ⟨f, inf_le_left (b := primitiveForms (-n)) g.property⟩)
  · rw [hI, map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul, posDefProperClassToPic_mk,
      picClass_def]

/-- **The complex lattice of an invertible ideal is a period lattice.** -/
theorem exists_periodPair_lattice_eq_complexFractionalIdeal
    (I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) :
    ∃ L : PeriodPair, L.lattice = complexFractionalIdeal
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) := by
  obtain ⟨g, c, h, -⟩ := exists_complexFractionalIdeal_eq_lattice_smul n hn I
  exact ⟨_, h.symm⟩

/-- **The CM class of an invertible ideal.** If `L` has the complex lattice `ι(𝔞)` of an
invertible ideal `𝔞` of the order of discriminant `-n`, and `q` is the proper class of forms with
Picard class `[𝔞]`, then the homothety class of `L` is the CM class of `q`. -/
theorem mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq
    {I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals} {L : PeriodPair}
    (hL : L.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
    {q : PosDefProperClass n} (hq : posDefProperClassToPic n hn q =
      (numberFieldOrder (-n : ℤ) hn).mkPic I) :
    PeriodPairHomothetyClass.mk L = posDefProperClassToHomothetyClass n q := by
  obtain ⟨g, c, h, hc⟩ := exists_complexFractionalIdeal_eq_lattice_smul n hn I
  rw [posDefProperClassToPic_injective n hn (hq.trans hc), posDefProperClassToHomothetyClass_mk,
    PeriodPairHomothetyClass.mk_eq_of_lattice_eq (hL.trans h), PeriodPairHomothetyClass.mk_smul]

/-- The lattice of an invertible ideal of the order of discriminant `-n` has multiplier order
`complexOrder (-n)`. -/
theorem leftOrder_lattice_eq_complexOrder_of_lattice_eq
    {I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals} {L : PeriodPair}
    (hL : L.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0))) :
    L.lattice.leftOrder = complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn := by
  obtain ⟨q, hq⟩ := posDefProperClassToPic_surjective n hn ((numberFieldOrder (-n : ℤ) hn).mkPic I)
  rw [← PeriodPairHomothetyClass.leftOrder_mk,
    mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq n hn hL hq]
  exact leftOrder_posDefProperClassToHomothetyClass n hn q

/-- **The CM dictionary on ideal lattices**: `cmHomothetyClassEquivPic` sends the homothety class
of the complex lattice `ι(𝔞)` of an invertible ideal `𝔞` to the Picard class `[𝔞]`. -/
theorem cmHomothetyClassEquivPic_mk_of_lattice_eq
    {I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals} {L : PeriodPair}
    (hL : L.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0))) :
    cmHomothetyClassEquivPic n hn ⟨PeriodPairHomothetyClass.mk L,
      (PeriodPairHomothetyClass.leftOrder_mk L).trans
        (leftOrder_lattice_eq_complexOrder_of_lattice_eq n hn hL)⟩ =
      (numberFieldOrder (-n : ℤ) hn).mkPic I := by
  obtain ⟨q, hq⟩ := posDefProperClassToPic_surjective n hn ((numberFieldOrder (-n : ℤ) hn).mkPic I)
  rw [cmHomothetyClassEquivPic_apply]
  refine Eq.trans (congrArg (posDefProperClassToPic n hn) ?_) hq
  rw [← cmHomothetyClassEquivPosDefProperClass_posDefProperClassToHomothetyClass n hn q
    (leftOrder_posDefProperClassToHomothetyClass n hn q)]
  exact congrArg _ (Subtype.ext (mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq n hn hL hq))

/-- **The ideal-class action on CM lattices.** `Pic(O)` acts on the homothety classes of period
lattices with multiplier order `O = complexOrder (-n)`, transported from its regular action through
the dictionary `cmHomothetyClassEquivPic`. The class `[𝔞]` sends `[Λ]` to `[ι(𝔞) Λ]`
(`coe_smul_of_lattice_eq_mul`). -/
instance instMulActionPicCMHomothetyClass :
    MulAction (Pic (numberFieldOrder (-n : ℤ) hn))
      {x : PeriodPairHomothetyClass // x.leftOrder =
        complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} :=
  -- `β` restates the codomain of `cmHomothetyClassEquivPic`, written there with `-((n : ℤ) : ℚ)`,
  -- in the definitionally equal form `((-n : ℤ) : ℚ)` that carries the group structure used here
  Equiv.mulAction (β := Pic (numberFieldOrder (-n : ℤ) hn)) _ (cmHomothetyClassEquivPic n hn)

/-- The CM dictionary is equivariant for the ideal-class action: the Picard class of `c • x` is
`c` times the Picard class of `x`. -/
@[simp] theorem posDefProperClassToPic_cmHomothetyClassEquivPosDefProperClass_smul
    (c : Pic (numberFieldOrder (-n : ℤ) hn))
    (x : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn (c • x)) =
      c * posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) := by
  rw [Equiv.smul_def (β := Pic (numberFieldOrder (-n : ℤ) hn)) (cmHomothetyClassEquivPic n hn),
    ← cmHomothetyClassEquivPic_apply, ← cmHomothetyClassEquivPic_apply]
  exact (cmHomothetyClassEquivPic n hn).apply_symm_apply _

/-- A CM homothety class is determined by its Picard class. -/
private theorem eq_of_posDefProperClassToPic_eq
    {x y : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}}
    (h : posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) =
      posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn y)) : x = y :=
  (cmHomothetyClassEquivPosDefProperClass n hn).injective (posDefProperClassToPic_injective n hn h)

/-- **The ideal-class action is transitive.** -/
instance instIsPretransitivePicCMHomothetyClass :
    MulAction.IsPretransitive (Pic (numberFieldOrder (-n : ℤ) hn))
      {x : PeriodPairHomothetyClass // x.leftOrder =
        complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn} := by
  refine ⟨fun x y ↦ ⟨posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn y) *
    (posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x))⁻¹,
    eq_of_posDefProperClassToPic_eq n hn ?_⟩⟩
  rw [posDefProperClassToPic_cmHomothetyClassEquivPosDefProperClass_smul, inv_mul_cancel_right]

/-- **The ideal-class action is free**: every stabilizer is trivial. -/
theorem stabilizer_pic_eq_bot
    (x : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
    MulAction.stabilizer (Pic (numberFieldOrder (-n : ℤ) hn)) x = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc ↦ ?_
  have h := congrArg
    (fun y ↦ posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn y))
    (MulAction.mem_stabilizer_iff.mp hc)
  simp only [posDefProperClassToPic_cmHomothetyClassEquivPosDefProperClass_smul] at h
  exact mul_eq_right.mp h

/-- A lattice with multiplier order `O` is a rescaling of the complex lattice of an invertible ideal
`𝔍` of `O` whose Picard class corresponds to the homothety class of the lattice. -/
private theorem exists_lattice_eq_map_mulLeft_complexFractionalIdeal
    {x : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}} {L : PeriodPair}
    (hx : (x : PeriodPairHomothetyClass) = PeriodPairHomothetyClass.mk L) :
    ∃ (J : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) (c : ℂˣ),
      posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) =
        (numberFieldOrder (-n : ℤ) hn).mkPic J ∧
      L.lattice = (complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (J : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0))).map
          (LinearMap.mulLeft ℤ (c : ℂ)) := by
  obtain ⟨J, hJ⟩ := (numberFieldOrder (-n : ℤ) hn).mkPic_surjective
    (posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x))
  obtain ⟨LJ, hLJ⟩ := exists_periodPair_lattice_eq_complexFractionalIdeal n hn J
  have hmk := (mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq n hn hLJ hJ.symm).trans
    ((posDefProperClassToHomothetyClass_cmHomothetyClassEquivPosDefProperClass n hn x).trans hx)
  obtain ⟨c, hc⟩ := PeriodPair.homothetic_def.mp (PeriodPairHomothetyClass.mk_eq_mk_iff.mp hmk)
  exact ⟨J, c, hJ.symm, by rw [hc, PeriodPair.lattice_smul, hLJ]⟩

/-- If the lattice `Λ` lies in the CM class `x`, then for every invertible ideal `𝔞` of `O` there
are an invertible ideal `𝔍` with Picard class corresponding to `x` and a period lattice of lattice
`ι(𝔞𝔍)` whose rescaling by some `c` is `ι(𝔞) Λ`. -/
private theorem exists_lattice_smul_eq_complexFractionalIdeal_mul
    (I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals)
    {x : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}} {L : PeriodPair}
    (hx : (x : PeriodPairHomothetyClass) = PeriodPairHomothetyClass.mk L) :
    ∃ (J : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) (c : ℂˣ)
      (LIJ : PeriodPair),
      posDefProperClassToPic n hn (cmHomothetyClassEquivPosDefProperClass n hn x) =
        (numberFieldOrder (-n : ℤ) hn).mkPic J ∧
      LIJ.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((I * J : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) :
          FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) ∧
      (c • LIJ).lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) * L.lattice := by
  obtain ⟨J, c, hJ, hc⟩ := exists_lattice_eq_map_mulLeft_complexFractionalIdeal n hn hx
  obtain ⟨LIJ, hLIJ⟩ := exists_periodPair_lattice_eq_complexFractionalIdeal n hn (I * J)
  refine ⟨J, c, LIJ, hJ, hLIJ, ?_⟩
  rw [PeriodPair.lattice_smul, hLIJ, hc, Submodule.mul_map_mulLeft, Units.val_mul,
    complexFractionalIdeal_mul]

/-- **The product of an ideal lattice and a CM lattice is a period lattice**: if `Λ` has multiplier
order `O`, then `ι(𝔞) Λ` is a period lattice for every invertible ideal `𝔞` of `O`. -/
theorem exists_periodPair_lattice_eq_complexFractionalIdeal_mul
    (I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) {L : PeriodPair}
    (hL : L.lattice.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn) :
    ∃ L' : PeriodPair, L'.lattice = complexFractionalIdeal
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) * L.lattice := by
  obtain ⟨-, c, LIJ, -, -, h⟩ := exists_lattice_smul_eq_complexFractionalIdeal_mul n hn I
    (x := ⟨PeriodPairHomothetyClass.mk L, (PeriodPairHomothetyClass.leftOrder_mk L).trans hL⟩) rfl
  exact ⟨c • LIJ, h⟩

/-- **The ideal-class action is multiplication of lattices**: if `x = [Λ]` and `Λ'` is the product
`ι(𝔞) Λ` of the complex lattice of an invertible ideal `𝔞` with `Λ`, then `[𝔞] • x = [Λ']`. -/
theorem coe_smul_of_lattice_eq_mul
    {I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals}
    {x : {x : PeriodPairHomothetyClass // x.leftOrder =
      complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}} {L L' : PeriodPair}
    (hx : (x : PeriodPairHomothetyClass) = PeriodPairHomothetyClass.mk L)
    (hL' : L'.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) * L.lattice) :
    (((numberFieldOrder (-n : ℤ) hn).mkPic I • x : {x : PeriodPairHomothetyClass //
      x.leftOrder = complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn}) :
        PeriodPairHomothetyClass) = PeriodPairHomothetyClass.mk L' := by
  obtain ⟨J, c, LIJ, hJ, hLIJ, h⟩ := exists_lattice_smul_eq_complexFractionalIdeal_mul n hn I hx
  have hq : posDefProperClassToPic n hn
      (cmHomothetyClassEquivPosDefProperClass n hn ((numberFieldOrder (-n : ℤ) hn).mkPic I • x)) =
        (numberFieldOrder (-n : ℤ) hn).mkPic (I * J) := by
    rw [posDefProperClassToPic_cmHomothetyClassEquivPosDefProperClass_smul, hJ, map_mul]
  rw [PeriodPairHomothetyClass.mk_eq_of_lattice_eq (hL'.trans h.symm),
    PeriodPairHomothetyClass.mk_smul,
    mk_eq_posDefProperClassToHomothetyClass_of_lattice_eq n hn hLIJ hq,
    posDefProperClassToHomothetyClass_cmHomothetyClassEquivPosDefProperClass]

/-- **CM `j`-values are `j`-invariants of ideal lattices.** A complex number is a root of the
Hilbert class polynomial of discriminant `-n` if and only if it is the `j`-invariant of the complex
lattice `ι(𝔞)` of an invertible ideal `𝔞` of the order of discriminant `-n`. -/
theorem isRoot_hilbertClassPolynomial_iff_exists_lattice_eq {z : ℂ} :
    (hilbertClassPolynomial n).IsRoot z ↔
      ∃ (I : (numberFieldOrder (-n : ℤ) hn).invertibleProperFractionalIdeals) (L : PeriodPair),
        L.lattice = complexFractionalIdeal (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          (I : FractionalIdeal _ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) ∧
        L.weierstrassCurve.j = z := by
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := PeriodPairHomothetyClass.j_surjective z
    obtain ⟨L, rfl⟩ := PeriodPairHomothetyClass.mk_surjective x
    have hL := (PeriodPairHomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial
      _ n hn).mpr hz
    obtain ⟨J, c, -, hc⟩ := exists_lattice_eq_map_mulLeft_complexFractionalIdeal n hn
      (x := ⟨PeriodPairHomothetyClass.mk L, hL⟩) rfl
    obtain ⟨LJ, hLJ⟩ := exists_periodPair_lattice_eq_complexFractionalIdeal n hn J
    refine ⟨J, LJ, hLJ, ?_⟩
    rw [← PeriodPairHomothetyClass.j_mk,
      PeriodPairHomothetyClass.mk_eq_of_lattice_eq (L := L) (L' := c • LJ)
        (by rw [hc, PeriodPair.lattice_smul, hLJ]), PeriodPairHomothetyClass.mk_smul]
  · rintro ⟨I, L, hL, rfl⟩
    rw [← PeriodPairHomothetyClass.j_mk,
      ← PeriodPairHomothetyClass.leftOrder_eq_complexOrder_iff_isRoot_hilbertClassPolynomial _ n hn,
      PeriodPairHomothetyClass.leftOrder_mk]
    exact leftOrder_lattice_eq_complexOrder_of_lattice_eq n hn hL

end PicAction

end TauCeti.BinaryQuadraticForm
