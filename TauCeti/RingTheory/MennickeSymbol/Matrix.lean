/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.RingTheory.MennickeSymbol.Dedekind
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Coprime

/-!
# Mennicke pairs as first rows of congruence matrices

Let `A` be a commutative ring and `I` an ideal of `A`. Write `GL₂(A, I)` and `SL₂(A, I)` for the
principal congruence subgroups of level `I`, the kernels of reduction modulo `I` on `GL₂(A)` and
`SL₂(A)`. The first row `(a, b)` of a matrix `[[a, b], [c, d]]` of `GL₂(A, I)` is a Mennicke pair
at level `I`: `a ≡ 1` and `b ≡ 0` modulo `I`, and `(a, b)` is unimodular since `a d - b c` is a
unit. This file studies the resulting first-row maps `GL₂(A, I) → W(A, I)` and
`SL₂(A, I) → W(A, I)`; they carry a Mennicke symbol `[b/a]` to a function `g ↦ [b/a]` on
matrices, which Kubota and Bass–Milnor–Serre show to be a homomorphism over a Dedekind domain.

* **Surjectivity, already on `SL₂(A, I)`.** If `u a + v b = 1`, the matrix
  `[[a, b], [(a - 1) v, u + b v]]` has determinant `1`, lower-left entry in `I` and lower-right
  entry `≡ 1` modulo `I` (since `u ≡ 1` modulo `I`), so it completes `(a, b)` inside
  `SL₂(A, I)`.
* **Fibres.** Two matrices of `GL₂(A, I)` have the same first row exactly when they differ, on
  the left, by a matrix of `GL₂(A, I)` with first row `(1, 0)`: a lower triangular matrix
  `[[1, 0], [t, u]]` with `t ∈ I` and `u` a unit congruent to `1` modulo `I`. In `SL₂(A, I)` the
  unit `u` is `1` and these are the lower transvections with parameter in `I`. Hence the first
  row identifies the right cosets of these stabilizers with `W(A, I)`, with no preferred choice
  of completion.
* **Mennicke symbols on matrices.** For a Mennicke symbol `s`, transposition inverts the value
  on matrices: `[c/a] = [b/a]⁻¹` for `[[a, b], [c, d]] ∈ GL₂(A, I)`, over every commutative
  ring. Over a Dedekind domain the value can also be read off the second row:
  `[b/a] = [c/d]`.

## Main definitions

* `Ideal.MennickePair.ofGL`, `Ideal.MennickePair.ofSL`: the first-row maps from `GL₂(A, I)` and
  `SL₂(A, I)` to `W(A, I)`.
* `Ideal.MennickePair.toSL`: an explicit Bézout completion of a Mennicke pair in `SL₂(A, I)`.
* `Ideal.MennickePair.stabilizerGL`, `Ideal.MennickePair.stabilizerSL`: the matrices of
  `GL₂(A, I)` and `SL₂(A, I)` with first row `(1, 0)`.
* `Ideal.MennickePair.rightCosetEquivGL`, `Ideal.MennickePair.rightCosetEquivSL`: the right
  cosets of these stabilizers correspond to the Mennicke pairs.

## Main results

* `Ideal.MennickePair.ofSL_toSL`, `Ideal.MennickePair.ofSL_surjective`,
  `Ideal.MennickePair.ofGL_surjective`: every Mennicke pair is the first row of a matrix of
  `SL₂(A, I)`.
* `Ideal.MennickePair.mem_stabilizerGL_iff`, `Ideal.MennickePair.mem_stabilizerSL_iff`: the
  stabilizers are the lower triangular matrices `[[1, 0], [t, u]]` with `t ∈ I` and
  `u ≡ 1` modulo `I`, and `u = 1` in `SL₂(A, I)`.
* `Ideal.MennickePair.ofGL_eq_ofGL_iff`, `Ideal.MennickePair.ofSL_eq_ofSL_iff`: two matrices have
  the same first row exactly when they lie in one right coset of the stabilizer.
* `Ideal.IsMennickeSymbol.map_ofGL_eq_inv_of_transpose`: transposition inverts the value of a
  Mennicke symbol on `GL₂(A, I)`.
* `Ideal.IsMennickeSymbol.map_ofGL_eq_of_row_one`: over a Dedekind domain, the value on
  `[[a, b], [c, d]]` is also `[c/d]`.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), 59–137, Lemma 5.3, p. 101, and
  §6, pp. 103–105.
-/

public section

open Matrix (GeneralLinearGroup SpecialLinearGroup)

namespace Ideal

variable {A : Type*} [CommRing A] {I : Ideal A}

namespace MennickePair

/-! ### The first-row maps -/

/-- The **first row** `(a, b)` of a matrix `[[a, b], [c, d]]` of `GL₂(A)` congruent to `1` modulo
`I`, as a Mennicke pair at level `I`. -/
def ofGL (g : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    MennickePair I where
  fst := (g : GL (Fin 2) A) 0 0
  snd := (g : GL (Fin 2) A) 0 1
  fst_sub_one_mem := by
    simpa using (GeneralLinearGroup.mem_ker_map_quotientMk_iff I).1 g.property 0 0
  snd_mem := by simpa using (GeneralLinearGroup.mem_ker_map_quotientMk_iff I).1 g.property 0 1
  isCoprime := GeneralLinearGroup.isCoprime_row _ 0

@[simp]
theorem ofGL_fst (g : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    (ofGL g).fst = (g : GL (Fin 2) A) 0 0 :=
  (rfl)

@[simp]
theorem ofGL_snd (g : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    (ofGL g).snd = (g : GL (Fin 2) A) 0 1 :=
  (rfl)

/-- The **first row** `(a, b)` of a matrix `[[a, b], [c, d]]` of `SL₂(A)` congruent to `1` modulo
`I`, as a Mennicke pair at level `I`. -/
def ofSL (g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    MennickePair I where
  fst := (g : SpecialLinearGroup (Fin 2) A) 0 0
  snd := (g : SpecialLinearGroup (Fin 2) A) 0 1
  fst_sub_one_mem := by
    simpa using SpecialLinearGroup.mem_ker_map_quotientMk_iff.1 g.property 0 0
  snd_mem := by simpa using SpecialLinearGroup.mem_ker_map_quotientMk_iff.1 g.property 0 1
  isCoprime := SpecialLinearGroup.isCoprime_row _ 0

@[simp]
theorem ofSL_fst (g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    (ofSL g).fst = (g : SpecialLinearGroup (Fin 2) A) 0 0 :=
  (rfl)

@[simp]
theorem ofSL_snd (g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    (ofSL g).snd = (g : SpecialLinearGroup (Fin 2) A) 0 1 :=
  (rfl)

/-- The first row of a matrix of `SL₂(A, I)` is its first row as a matrix of `GL₂(A, I)`. -/
@[simp]
theorem ofGL_kerMapToGL
    (g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    ofGL (SpecialLinearGroup.kerMapToGL _ g) = ofSL g := by
  ext <;> simp

@[simp]
theorem ofGL_one : ofGL (1 : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) =
    .one := by
  ext <;> simp

@[simp]
theorem ofSL_one : ofSL (1 : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) =
    .one := by
  rw [← ofGL_kerMapToGL, _root_.map_one, ofGL_one]

/-- The first row of a product `g k` only depends on the first row of `g`. -/
theorem ofGL_mul_eq_of_ofGL_eq {g g' : (GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk I)).ker} (h : ofGL g = ofGL g') (k : (GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk I)).ker) : ofGL (g * k) = ofGL (g' * k) := by
  have h₀ : (g : GL (Fin 2) A) 0 0 = (g' : GL (Fin 2) A) 0 0 := congrArg fst h
  have h₁ : (g : GL (Fin 2) A) 0 1 = (g' : GL (Fin 2) A) 0 1 := congrArg snd h
  ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h₀, h₁]

/-! ### Surjectivity: the Bézout completion -/

/-- An **explicit Bézout completion** of a Mennicke pair `(a, b)`: with `u a + v b = 1` chosen,
the matrix `[[a, b], [(a - 1) v, u + b v]]`, which lies in `SL₂(A)` and is congruent to `1`
modulo `I`. -/
noncomputable def toSL (p : MennickePair I) :
    (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker :=
  let u := p.isCoprime.choose
  let v := p.isCoprime.choose_spec.choose
  have huv : u * p.fst + v * p.snd = 1 := p.isCoprime.choose_spec.choose_spec
  let M : SpecialLinearGroup (Fin 2) A := ⟨!![p.fst, p.snd; (p.fst - 1) * v, u + p.snd * v], by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  ⟨M, SpecialLinearGroup.mem_ker_map_quotientMk_iff.2 fun i j ↦ by
    fin_cases i <;> fin_cases j
    · simpa [M] using p.fst_sub_one_mem
    · simpa [M] using p.snd_mem
    · simpa [M] using I.mul_mem_right v p.fst_sub_one_mem
    · -- `u + b v - 1 = -u (a - 1)`, since `u a + v b = 1`
      simpa [M, show u + p.snd * v - 1 = -(u * (p.fst - 1)) by linear_combination huv] using
        I.mul_mem_left u p.fst_sub_one_mem⟩

/-- The Bézout completion of `(a, b)` has first row `(a, b)`. -/
@[simp]
theorem ofSL_toSL (p : MennickePair I) : ofSL p.toSL = p := by
  ext <;> simp [toSL]

/-- **Every Mennicke pair is a first row in `SL₂(A, I)`.** -/
theorem ofSL_surjective : Function.Surjective (ofSL (I := I)) :=
  fun p ↦ ⟨p.toSL, ofSL_toSL p⟩

/-- **Every Mennicke pair is a first row in `GL₂(A, I)`.** -/
theorem ofGL_surjective : Function.Surjective (ofGL (I := I)) :=
  fun p ↦ ⟨SpecialLinearGroup.kerMapToGL _ p.toSL, by rw [ofGL_kerMapToGL, ofSL_toSL]⟩

/-! ### Fibres: the stabilizers of the base pair -/

variable (I) in
/-- The matrices of `GL₂(A, I)` with first row `(1, 0)`, the stabilizer of the base pair: the
lower triangular matrices `[[1, 0], [t, u]]` with `t ∈ I` and `u` a unit congruent to `1`
modulo `I` (`Ideal.MennickePair.mem_stabilizerGL_iff`). -/
def stabilizerGL : Subgroup (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker where
  carrier := {k | ofGL k = .one}
  mul_mem' {k k'} hk hk' := by
    rw [Set.mem_ofPred_eq, ofGL_mul_eq_of_ofGL_eq (hk.trans ofGL_one.symm), one_mul]
    exact hk'
  one_mem' := ofGL_one
  inv_mem' {k} hk := by
    rw [Set.mem_ofPred_eq, ← one_mul k⁻¹, ← ofGL_mul_eq_of_ofGL_eq (hk.trans ofGL_one.symm),
      mul_inv_cancel, ofGL_one]

@[simp]
theorem mem_stabilizerGL {k : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    k ∈ stabilizerGL I ↔ ofGL k = .one :=
  Iff.rfl

/-- The stabilizer of the base pair in `GL₂(A, I)` consists of the lower triangular matrices
`[[1, 0], [t, u]]` with `t ∈ I` and `u` a unit congruent to `1` modulo `I`. -/
theorem mem_stabilizerGL_iff
    {k : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    k ∈ stabilizerGL I ↔ ∃ t ∈ I, ∃ u : Aˣ, (u : A) - 1 ∈ I ∧
      ((k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, 0; t, u] := by
  have hk := (GeneralLinearGroup.mem_ker_map_quotientMk_iff I).1 k.property
  rw [mem_stabilizerGL, MennickePair.ext_iff, ofGL_fst, ofGL_snd, one_fst, one_snd]
  constructor
  · rintro ⟨h₀, h₁⟩
    -- the determinant of `[[1, 0], [t, d]]` is the lower-right entry `d`, which is thus a unit
    have hdet : ((GeneralLinearGroup.det (k : GL (Fin 2) A) : Aˣ) : A) =
        (k : GL (Fin 2) A) 1 1 := by
      rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      simp [h₀, h₁]
    refine ⟨(k : GL (Fin 2) A) 1 0, by simpa using hk 1 0,
      GeneralLinearGroup.det (k : GL (Fin 2) A), by simpa [hdet] using hk 1 1, ?_⟩
    rw [hdet, ← h₀, ← h₁]
    exact Matrix.eta_fin_two _
  · rintro ⟨t, -, u, -, h⟩
    simp [h]

/-- **Right cosets of the stabilizer in `GL₂(A, I)`**: two matrices of `GL₂(A, I)` lie in one right
coset of the stabilizer of the base pair exactly when they have the same first row. -/
theorem rightRel_stabilizerGL_iff
    {g h : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    QuotientGroup.rightRel (stabilizerGL I) g h ↔ ofGL g = ofGL h := by
  rw [QuotientGroup.rightRel_apply, mem_stabilizerGL]
  constructor
  · intro hgh
    rw [← inv_mul_cancel_right h g, ofGL_mul_eq_of_ofGL_eq (hgh.trans ofGL_one.symm), one_mul]
  · intro hgh
    rw [ofGL_mul_eq_of_ofGL_eq hgh.symm, mul_inv_cancel, ofGL_one]

/-- **Fibres of the first-row map on `GL₂(A, I)`**: two matrices have the same first row exactly
when they differ, on the left, by an element of the stabilizer of the base pair. -/
theorem ofGL_eq_ofGL_iff {g h : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    ofGL g = ofGL h ↔ h * g⁻¹ ∈ stabilizerGL I := by
  rw [← rightRel_stabilizerGL_iff, QuotientGroup.rightRel_apply]

variable (I) in
/-- The matrices of `SL₂(A, I)` with first row `(1, 0)`, the stabilizer of the base pair: the
lower transvections `[[1, 0], [t, 1]]` with `t ∈ I` (`Ideal.MennickePair.mem_stabilizerSL_iff`). -/
def stabilizerSL : Subgroup (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker :=
  (stabilizerGL I).comap (SpecialLinearGroup.kerMapToGL _)

@[simp]
theorem mem_stabilizerSL {k : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    k ∈ stabilizerSL I ↔ ofSL k = .one := by
  rw [stabilizerSL, Subgroup.mem_comap, mem_stabilizerGL, ofGL_kerMapToGL]

/-- The stabilizer of the base pair in `SL₂(A, I)` consists of the lower transvections
`[[1, 0], [t, 1]]` with `t ∈ I`. -/
theorem mem_stabilizerSL_iff
    {k : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    k ∈ stabilizerSL I ↔ ∃ t ∈ I,
      (k : SpecialLinearGroup (Fin 2) A) = SpecialLinearGroup.transvection one_ne_zero t := by
  rw [mem_stabilizerSL, MennickePair.ext_iff, ofSL_fst, ofSL_snd, one_fst, one_snd]
  constructor
  · rintro ⟨h₀, h₁⟩
    -- `[[1, 0], [t, d]]` has determinant `d`, so `d = 1`
    have hdet := (k : SpecialLinearGroup (Fin 2) A).det_coe
    rw [Matrix.det_fin_two, h₀, h₁, one_mul, zero_mul, sub_zero] at hdet
    refine ⟨(k : SpecialLinearGroup (Fin 2) A) 1 0, by
      simpa using SpecialLinearGroup.mem_ker_map_quotientMk_iff.1 k.property 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, h₀, h₁, hdet]
  · rintro ⟨t, -, h⟩
    simp [h, SpecialLinearGroup.transvection_coe]

/-- **Right cosets of the stabilizer in `SL₂(A, I)`**: two matrices of `SL₂(A, I)` lie in one right
coset of the stabilizer of the base pair exactly when they have the same first row. -/
theorem rightRel_stabilizerSL_iff
    {g h : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    QuotientGroup.rightRel (stabilizerSL I) g h ↔ ofSL g = ofSL h := by
  rw [QuotientGroup.rightRel_apply, stabilizerSL, Subgroup.mem_comap, _root_.map_mul,
    _root_.map_inv, ← QuotientGroup.rightRel_apply, rightRel_stabilizerGL_iff, ofGL_kerMapToGL,
    ofGL_kerMapToGL]

/-- **Fibres of the first-row map on `SL₂(A, I)`**: two matrices have the same first row exactly
when they differ, on the left, by a lower transvection with parameter in `I`. -/
theorem ofSL_eq_ofSL_iff {g h : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker} :
    ofSL g = ofSL h ↔ h * g⁻¹ ∈ stabilizerSL I := by
  rw [← rightRel_stabilizerSL_iff, QuotientGroup.rightRel_apply]

variable (I) in
/-- **The right cosets of the stabilizer in `GL₂(A, I)` are the Mennicke pairs**: the first row
identifies `stabilizerGL I \ GL₂(A, I)` with `W(A, I)`. -/
noncomputable def rightCosetEquivGL :
    Quotient (QuotientGroup.rightRel (stabilizerGL I)) ≃ MennickePair I :=
  (Quotient.congrRight fun _ _ ↦ rightRel_stabilizerGL_iff).trans
    (Setoid.quotientKerEquivOfRightInverse ofGL (fun p ↦ SpecialLinearGroup.kerMapToGL _ p.toSL)
      fun p ↦ by rw [ofGL_kerMapToGL, ofSL_toSL])

@[simp]
theorem rightCosetEquivGL_mk (g : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    rightCosetEquivGL I (_root_.Quotient.mk _ g) = ofGL g :=
  (rfl)

@[simp]
theorem rightCosetEquivGL_symm_apply (p : MennickePair I) :
    (rightCosetEquivGL I).symm p = _root_.Quotient.mk _ (SpecialLinearGroup.kerMapToGL _ p.toSL) :=
  (rfl)

variable (I) in
/-- **The right cosets of the stabilizer in `SL₂(A, I)` are the Mennicke pairs**: the first row
identifies `stabilizerSL I \ SL₂(A, I)` with `W(A, I)`. -/
noncomputable def rightCosetEquivSL :
    Quotient (QuotientGroup.rightRel (stabilizerSL I)) ≃ MennickePair I :=
  (Quotient.congrRight fun _ _ ↦ rightRel_stabilizerSL_iff).trans
    (Setoid.quotientKerEquivOfRightInverse ofSL toSL ofSL_toSL)

@[simp]
theorem rightCosetEquivSL_mk (g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) :
    rightCosetEquivSL I (_root_.Quotient.mk _ g) = ofSL g :=
  (rfl)

@[simp]
theorem rightCosetEquivSL_symm_apply (p : MennickePair I) :
    (rightCosetEquivSL I).symm p = _root_.Quotient.mk _ p.toSL :=
  (rfl)

end MennickePair

/-! ### Mennicke symbols on matrices -/

namespace IsMennickeSymbol

variable {C : Type*} [Group C] {s : MennickePair I → C}

open MennickePair in
/-- **Transposition inverts a Mennicke symbol on matrices**: if `h = gᵀ` in `GL₂(A, I)`, then the
value of `s` on the first row of `h` is the inverse of its value on the first row of `g`, that is
`[c/a] = [b/a]⁻¹` for `g = [[a, b], [c, d]]`. -/
theorem map_ofGL_eq_inv_of_transpose (hs : IsMennickeSymbol s)
    {g h : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker}
    (hgh : ((h : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).transpose) :
    s (ofGL h) = (s (ofGL g))⁻¹ := by
  have h₀ : (h : GL (Fin 2) A) 0 0 = (g : GL (Fin 2) A) 0 0 := by
    simpa using congrFun (congrFun hgh 0) 0
  have h₁ : (h : GL (Fin 2) A) 0 1 = (g : GL (Fin 2) A) 1 0 := by
    simpa using congrFun (congrFun hgh 0) 1
  refine eq_inv_of_mul_eq_one_right (hs.map_mul_map_eq_one (d := (g : GL (Fin 2) A) 1 1)
    (by simp [h₀]) ?_)
  rw [ofGL_fst, ofGL_snd, ofGL_snd, h₁]
  exact GeneralLinearGroup.isUnit_mul_sub_mul _

open MennickePair in
/-- **The value of a Mennicke symbol from the second row of a matrix.** Over a Dedekind domain,
the value of a Mennicke symbol on the first row of `[[a, b], [c, d]] ∈ GL₂(A, I)` equals its value
on the pair `(d, c)`: `[b/a] = [c/d]`. -/
theorem map_ofGL_eq_of_row_one [IsDedekindDomain A] (hs : IsMennickeSymbol s)
    (g : (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker) {p : MennickePair I}
    (hfst : p.fst = (g : GL (Fin 2) A) 1 1) (hsnd : p.snd = (g : GL (Fin 2) A) 1 0) :
    s (ofGL g) = s p := by
  refine hs.map_eq_of_isUnit_mul_sub_mul ?_
  rw [ofGL_fst, ofGL_snd, hfst, hsnd]
  exact GeneralLinearGroup.isUnit_mul_sub_mul _

end IsMennickeSymbol

end Ideal
