/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# Scalar extension of isometry classes and their discriminants

Extension of scalars along a field extension `K → L` carries a diagonal presentation to the
presentation of the same rank whose weights are the images of the original weights. That operation
descends to isometry classes as `TauCeti.RegularFormClass.baseChange`, and the discriminant
commutes with it: the discriminant of an extended class is the image of the original discriminant
under the functorial map on square-class groups induced by the field homomorphism.

Everything here is about field extensions in characteristic different from two. That restriction is
not an artefact: `QuadraticForm.baseChange` is only defined when two is invertible in the base
field, and `TauCeti.RegularFormClass.discr` is only defined over a field in which two is
invertible, so both hypotheses are needed already to state the results.

These results let invariants computed over a global field be read after passing to any such field
extension, in particular to the completions of a number field.

## Main definitions

* `TauCeti.RegularFormPresentation.baseChange`: the presentation whose weights are the images of
  the original weights.
* `TauCeti.RegularFormClass.baseChange`: scalar extension of isometry classes.

## Main results

* `TauCeti.presentedFormBaseChange`: extending a presented form presents the extended weights.
* `TauCeti.RegularFormClass.rank_baseChange`, `TauCeti.RegularFormClass.baseChange_add` and
  `TauCeti.RegularFormClass.baseChange_mul`: scalar extension preserves the rank and commutes with
  the orthogonal sum and the tensor product of classes.
* `TauCeti.RegularFormClass.baseChange_self` and
  `TauCeti.RegularFormClass.baseChange_baseChange`: scalar extension along the identity is the
  identity, and iterated scalar extension along a tower is scalar extension along the composite.
* `TauCeti.RegularFormClass.baseChange_hyperbolicClass`: scalar extension preserves the hyperbolic
  class.
* `QuadraticForm.formClass_baseChange`: the class of an extended form is the extension of its
  class.
* `QuadraticForm.discr_formClass_baseChange_eq_zero`: a form acquires square discriminant over a
  field containing a square root of its discriminant.
* `TauCeti.RegularFormClass.discr_baseChange`: the discriminant commutes with scalar extension.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-! ### Scalar extension of presentations -/

variable (L) in
/-- The presentation obtained by mapping every weight into the extension field `L`. The rank is
unchanged. -/
def RegularFormPresentation.baseChange (p : RegularFormPresentation K) :
    RegularFormPresentation L :=
  ⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩

variable (L) in
/-- Mapping the weights into `L` leaves the rank unchanged. -/
@[simp]
theorem RegularFormPresentation.fst_baseChange (p : RegularFormPresentation K) :
    (RegularFormPresentation.baseChange L p).1 = p.1 := (rfl)

variable (L) in
/-- Every weight of the mapped presentation is the image of the weight of `p` at the same index,
read through `TauCeti.RegularFormPresentation.fst_baseChange`. -/
@[simp]
theorem RegularFormPresentation.baseChange_apply (p : RegularFormPresentation K)
    (i : Fin (RegularFormPresentation.baseChange L p).1) :
    (RegularFormPresentation.baseChange L p).2 i =
      Units.map (algebraMap K L).toMonoidHom
        (p.2 (Fin.cast (RegularFormPresentation.fst_baseChange L p) i)) := (rfl)

variable (L) in
/-- The weight product of a mapped presentation is the image of the original weight product. -/
-- Not a `simp` lemma: `RegularFormPresentation.baseChange_apply` rewrites inside the product, so
-- the left-hand side below is not in `simp`-normal form and `simpNF` rejects the attribute.
theorem RegularFormPresentation.prod_baseChange (p : RegularFormPresentation K) :
    (∏ i, (RegularFormPresentation.baseChange L p).2 i) =
      Units.map (algebraMap K L).toMonoidHom (∏ i, p.2 i) := by
  rw [map_prod]
  exact Fintype.prod_equiv (finCongr (RegularFormPresentation.fst_baseChange L p)) _ _ (by simp)

/-- Mapping the weights into the base field itself leaves a presentation unchanged. -/
@[simp]
theorem RegularFormPresentation.baseChange_self (p : RegularFormPresentation K) :
    RegularFormPresentation.baseChange K p = p := by
  refine RegularFormPresentation.ext rfl fun i ↦ Units.ext ?_
  simp

variable (L M) in
/-- Mapping the weights into `L` and then into `M` is mapping them into `M` in one step. -/
@[simp]
theorem RegularFormPresentation.baseChange_baseChange (p : RegularFormPresentation K) :
    RegularFormPresentation.baseChange M (RegularFormPresentation.baseChange L p) =
      RegularFormPresentation.baseChange M p := by
  refine RegularFormPresentation.ext rfl fun i ↦ Units.ext ?_
  rw [RegularFormPresentation.baseChange_apply, RegularFormPresentation.baseChange_apply,
    RegularFormPresentation.baseChange_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    IsScalarTower.algebraMap_apply K L M]
  -- Both sides now read the weight of `p` at the same index, identified once through the two
  -- ranks of the iterated extension and once through the rank of the composite extension.
  exact congrArg (fun j : Fin p.1 ↦ algebraMap L M (algebraMap K L (p.2 j : K))) (Fin.ext rfl)

variable (L) in
/-- Mapping the weights into `L` fixes the rank-one presentation with weight one. -/
@[simp]
theorem RegularFormPresentation.baseChange_one :
    RegularFormPresentation.baseChange L (RegularFormPresentation.one (K := K)) =
      RegularFormPresentation.one := by
  refine RegularFormPresentation.ext (by simp) fun i ↦ ?_
  simp

variable (L) in
/-- Mapping the weights into `L` commutes with concatenation of presentations. -/
@[simp]
theorem RegularFormPresentation.baseChange_append (p q : RegularFormPresentation K) :
    RegularFormPresentation.baseChange L (p.append q) =
      (RegularFormPresentation.baseChange L p).append
        (RegularFormPresentation.baseChange L q) := by
  have h₁ : (RegularFormPresentation.baseChange L (p.append q)).1 = p.1 + q.1 := by simp
  have hrank : (RegularFormPresentation.baseChange L (p.append q)).1 =
      ((RegularFormPresentation.baseChange L p).append
        (RegularFormPresentation.baseChange L q)).1 := by simp
  refine RegularFormPresentation.ext hrank fun i ↦ ?_
  -- Read the index as one of the two concatenated halves of `Fin (p.1 + q.1)`.
  have hi : i = Fin.cast h₁.symm (Fin.cast h₁ i) := by simp
  rw [hi]
  generalize Fin.cast h₁ i = j
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) j
  · have hindex : Fin.cast hrank (Fin.cast h₁.symm (Fin.castAdd q.1 a)) =
        Fin.cast (RegularFormPresentation.fst_append (RegularFormPresentation.baseChange L p)
            (RegularFormPresentation.baseChange L q)).symm
          (Fin.castAdd (RegularFormPresentation.baseChange L q).1
            (Fin.cast (RegularFormPresentation.fst_baseChange L p).symm a)) := by
      apply Fin.ext
      simp
    rw [hindex, RegularFormPresentation.append_apply_castAdd,
      RegularFormPresentation.baseChange_apply, RegularFormPresentation.baseChange_apply]
    simp [RegularFormPresentation.append_apply_castAdd]
  · have hindex : Fin.cast hrank (Fin.cast h₁.symm (Fin.natAdd p.1 b)) =
        Fin.cast (RegularFormPresentation.fst_append (RegularFormPresentation.baseChange L p)
            (RegularFormPresentation.baseChange L q)).symm
          (Fin.natAdd (RegularFormPresentation.baseChange L p).1
            (Fin.cast (RegularFormPresentation.fst_baseChange L q).symm b)) := by
      apply Fin.ext
      simp
    rw [hindex, RegularFormPresentation.append_apply_natAdd,
      RegularFormPresentation.baseChange_apply, RegularFormPresentation.baseChange_apply]
    simp [RegularFormPresentation.append_apply_natAdd]

variable (L) in
/-- Mapping the weights into `L` commutes with the tensor product of presentations. -/
@[simp]
theorem RegularFormPresentation.baseChange_tmul (p q : RegularFormPresentation K) :
    RegularFormPresentation.baseChange L (p.tmul q) =
      (RegularFormPresentation.baseChange L p).tmul
        (RegularFormPresentation.baseChange L q) := by
  have h₁ : (RegularFormPresentation.baseChange L (p.tmul q)).1 = p.1 * q.1 := by simp
  have hrank : (RegularFormPresentation.baseChange L (p.tmul q)).1 =
      ((RegularFormPresentation.baseChange L p).tmul
        (RegularFormPresentation.baseChange L q)).1 := by simp
  refine RegularFormPresentation.ext hrank fun i ↦ ?_
  -- Read the index as a pair of indices of the two factors.
  have hi : i = Fin.cast h₁.symm
      (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast h₁ i))) := by
    rw [Equiv.apply_symm_apply]; simp
  rw [hi]
  generalize finProdFinEquiv.symm (Fin.cast h₁ i) = ab
  obtain ⟨a, b⟩ := ab
  have hindex : Fin.cast hrank (Fin.cast h₁.symm (finProdFinEquiv (a, b))) =
      Fin.cast (RegularFormPresentation.fst_tmul (RegularFormPresentation.baseChange L p)
          (RegularFormPresentation.baseChange L q)).symm
        (finProdFinEquiv
          (Fin.cast (RegularFormPresentation.fst_baseChange L p).symm a,
            Fin.cast (RegularFormPresentation.fst_baseChange L q).symm b)) := by
    apply Fin.ext
    simp
  rw [hindex, RegularFormPresentation.tmul_apply, RegularFormPresentation.baseChange_apply,
    RegularFormPresentation.baseChange_apply]
  simp [RegularFormPresentation.tmul_apply]

/-! ### Scalar extension of presented forms -/

variable [Invertible (2 : K)]

/-- The canonical coordinate equivalence identifies scalar extension of a presented form with
the presentation obtained by mapping every weight into the larger field. -/
def presentedFormBaseChange (p : RegularFormPresentation K) :
    ((presentedForm p).baseChange L).IsometryEquiv
      (presentedForm (RegularFormPresentation.baseChange L p)) := by
  let e := _root_.QuadraticForm.baseChangeWeightedSumSquares (A := L)
    fun i ↦ (p.2 i : K)
  have hK : presentedForm p =
      QuadraticMap.weightedSumSquares K fun i ↦ (p.2 i : K) := by
    simp only [presentedForm_eq_weightedSumSquares, QuadraticMap.weightedSumSquares,
      Units.smul_def]
  have hL : presentedForm (RegularFormPresentation.baseChange L p) =
      QuadraticMap.weightedSumSquares L fun i ↦ algebraMap K L (p.2 i : K) := by
    simp only [RegularFormPresentation.baseChange, presentedForm_eq_weightedSumSquares,
      QuadraticMap.weightedSumSquares, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Units.smul_def]
    -- The two sums are indexed by `Fin (RegularFormPresentation.baseChange L p).1` and by
    -- `Fin p.1`, which are the same type once the mapped presentation is unfolded.
    rfl
  refine { toLinearEquiv := e.toLinearEquiv, map_app' := ?_ }
  intro x
  rw [hL, hK]
  exact e.map_app' x

/-- The presentation base-change isometry uses the canonical linear equivalence distributing
the tensor product over the finite coordinate space. -/
@[simp]
theorem presentedFormBaseChange_apply (p : RegularFormPresentation K)
    (x : L ⊗[K] (Fin p.1 → K)) (i : Fin (RegularFormPresentation.baseChange L p).1) :
    presentedFormBaseChange (L := L) p x i =
      TensorProduct.piScalarRightHom K L L (Fin p.1) x
        (Fin.cast (RegularFormPresentation.fst_baseChange L p) i) := by
  rw [presentedFormBaseChange]
  exact congrFun (_root_.QuadraticForm.baseChangeWeightedSumSquares_apply
    (A := L) (fun i ↦ (p.2 i : K)) x) _

/-! ### Scalar extension of isometry classes -/

variable (L) in
/-- **Scalar extension of isometry classes**: the class over `L` presented by the images of the
weights of any presentation over `K`. -/
def RegularFormClass.baseChange : RegularFormClass K → RegularFormClass L :=
  Quotient.map (RegularFormPresentation.baseChange L) fun p q h ↦ by
    have hp : (presentedForm (RegularFormPresentation.baseChange L p)).Equivalent
        ((presentedForm p).baseChange L) := ⟨(presentedFormBaseChange (L := L) p).symm⟩
    have hq : ((presentedForm q).baseChange L).Equivalent
        (presentedForm (RegularFormPresentation.baseChange L q)) :=
      ⟨presentedFormBaseChange (L := L) q⟩
    exact hp.trans ((QuadraticMap.Equivalent.baseChange h L).trans hq)

variable (L) in
/-- Scalar extension of classes is computed on presentations by mapping the weights. -/
@[simp]
theorem RegularFormClass.baseChange_mk (p : RegularFormPresentation K) :
    RegularFormClass.baseChange L (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (RegularFormPresentation.baseChange L p) :=
  (rfl)

/-- Scalar extension along the identity extension is the identity. -/
@[simp]
theorem RegularFormClass.baseChange_self (x : RegularFormClass K) :
    RegularFormClass.baseChange K x = x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormPresentation.baseChange_self]

variable (L M) in
/-- Scalar extension along a tower `K → L → M` is scalar extension along the composite. Two is
assumed invertible in `L` because extension of scalars out of `L` is only defined then. -/
@[simp]
theorem RegularFormClass.baseChange_baseChange [Invertible (2 : L)] (x : RegularFormClass K) :
    RegularFormClass.baseChange M (RegularFormClass.baseChange L x) =
      RegularFormClass.baseChange M x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormClass.baseChange_mk,
    RegularFormClass.baseChange_mk, RegularFormPresentation.baseChange_baseChange]

variable (L) in
/-- Scalar extension preserves the rank of a class. -/
@[simp]
theorem RegularFormClass.rank_baseChange (x : RegularFormClass K) :
    RegularFormClass.rank (RegularFormClass.baseChange L x) = RegularFormClass.rank x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormClass.rank_mk, RegularFormClass.rank_mk,
    RegularFormPresentation.fst_baseChange]

variable (L) in
/-- Scalar extension commutes with the orthogonal sum of classes. -/
@[simp]
theorem RegularFormClass.baseChange_add (x y : RegularFormClass K) :
    RegularFormClass.baseChange L (x + y) =
      RegularFormClass.baseChange L x + RegularFormClass.baseChange L y := by
  refine Quotient.inductionOn₂ x y fun p q ↦ ?_
  rw [RegularFormClass.mk_add_mk, RegularFormClass.baseChange_mk, RegularFormClass.baseChange_mk,
    RegularFormClass.baseChange_mk, RegularFormClass.mk_add_mk,
    RegularFormPresentation.baseChange_append]

variable (L) in
/-- Scalar extension takes the rank-zero class to the rank-zero class. -/
@[simp]
theorem RegularFormClass.baseChange_zero :
    RegularFormClass.baseChange L (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, RegularFormClass.baseChange_mk, RegularFormClass.zero_def]
  refine congrArg _ (RegularFormPresentation.ext (by simp) fun i ↦ ?_)
  exact (Fin.cast (by simp) i : Fin 0).elim0

-- Not `@[simp]`: `RegularFormClass K` is a semiring in downstream modules, where
-- `nsmul_eq_mul` rewrites the left-hand side and makes this declaration fail `simpNF`.
/-- Scalar extension preserves finite orthogonal sums. -/
theorem RegularFormClass.baseChange_nsmul (n : ℕ) (x : RegularFormClass K) :
    RegularFormClass.baseChange L (n • x) =
      n • RegularFormClass.baseChange L x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, RegularFormClass.baseChange_add, ih]

variable (L) in
/-- Scalar extension takes the multiplicative unit to the multiplicative unit. -/
@[simp]
theorem RegularFormClass.baseChange_one :
    RegularFormClass.baseChange L (1 : RegularFormClass K) = 1 := by
  rw [RegularFormClass.one_def, RegularFormClass.baseChange_mk, RegularFormClass.one_def,
    RegularFormPresentation.baseChange_one]

/-- Base change preserves the hyperbolic class. -/
@[simp]
theorem RegularFormClass.baseChange_hyperbolicClass :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.baseChange L (hyperbolicClass K) = hyperbolicClass L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [hyperbolicClass_def, hyperbolicClass_def, RegularFormClass.baseChange_mk]
  refine congrArg _ (RegularFormPresentation.ext
    (RegularFormPresentation.fst_baseChange L _) fun i ↦ ?_)
  rw [RegularFormPresentation.baseChange_apply]
  apply Units.ext
  generalize Fin.cast (RegularFormPresentation.fst_baseChange L _) i = j
  fin_cases j <;> simp

variable [Invertible (2 : L)]

variable (L) in
/-- Scalar extension commutes with the tensor product of classes. -/
@[simp]
theorem RegularFormClass.baseChange_mul (x y : RegularFormClass K) :
    RegularFormClass.baseChange L (x * y) =
      RegularFormClass.baseChange L x * RegularFormClass.baseChange L y := by
  refine Quotient.inductionOn₂ x y fun p q ↦ ?_
  rw [RegularFormClass.mk_mul_mk, RegularFormClass.baseChange_mk, RegularFormClass.baseChange_mk,
    RegularFormClass.baseChange_mk, RegularFormClass.mk_mul_mk,
    RegularFormPresentation.baseChange_tmul]

/-! ### Scalar extension of the discriminant -/

variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The discriminant commutes with scalar extension of isometry classes**: extending an isometry
class to `L` pushes its discriminant forward along the induced map of square-class groups. -/
@[simp]
theorem RegularFormClass.discr_baseChange (x : RegularFormClass K) :
    RegularFormClass.discr (RegularFormClass.baseChange L x) =
      (algebraMap K L).squareClassMap (RegularFormClass.discr x) := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormClass.discr_mk, RegularFormClass.discr_mk,
    RingHom.squareClassMap_apply, RegularFormPresentation.prod_baseChange]

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- The class of a form extended to `L` is the scalar extension of its class. -/
@[simp]
theorem formClass_baseChange (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ) =
      RegularFormClass.baseChange L (formClass Q hQ) := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.baseChange_mk,
    formClass_mk _ _ _ ((hp.baseChange L).trans ⟨presentedFormBaseChange p⟩)]

/-- If the discriminant of a regular form is the class of `d`, then the form has square
discriminant after scalar extension to a field containing a square root of `d`. -/
theorem discr_formClass_baseChange_eq_zero (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    {d : Kˣ} (hd : RegularFormClass.discr (formClass Q hQ) = squareClass d) {s : L}
    (hs : s * s = algebraMap K L d) :
    RegularFormClass.discr (formClass (Q.baseChange L) (Nondegenerate.baseChange hQ)) = 0 := by
  rw [formClass_baseChange Q hQ, RegularFormClass.discr_baseChange, hd,
    RingHom.squareClassMap_apply, squareClass_eq_zero_iff]
  exact isSquare_units_val_iff.mp ⟨s, by simpa using hs.symm⟩

end QuadraticForm
