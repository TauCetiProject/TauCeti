/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Subtraction-free rational functions

`TauCeti.Qsf K` consists of ratios of nonzero polynomials with natural coefficients,
viewed inside the fraction field of `MvPolynomial K ℤ`. Its auxiliary addition is
ordinary addition of rational functions. These expressions are the universal
coefficients used to specialize normalized cluster mutations.

`Qsf.evalEquiv` is the universal property for every coefficient semifield, including
ones with idempotent addition. Evaluation is defined only on positive fractions;
it does not require a map from the ambient rational-function field.

The construction uses Mathlib's `IsFractionRing` inclusion, `MvPolynomial.eval₂Hom`
and the multiplicative extension `WithZero.lift'`.

The construction follows Fomin and Zelevinsky, *Cluster algebras IV: Coefficients*,
Definition 2.1 and the universal semifield of §2.
-/

public section

noncomputable section

namespace TauCeti

namespace Qsf

variable {K : Type*}

/-- Embed natural-coefficient polynomials in the integral rational-function field. -/
def polynomialMap (K : Type*) :
    MvPolynomial K ℕ →+* FractionRing (MvPolynomial K ℤ) :=
  (algebraMap _ _).comp (MvPolynomial.map (Nat.castRingHom ℤ))

/-- Natural-coefficient polynomials retain their coefficients in the rational-function field. -/
theorem polynomialMap_injective (K : Type*) : Function.Injective (polynomialMap K) :=
  (IsFractionRing.injective (MvPolynomial K ℤ) _).comp
    (MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective)

@[simp]
theorem polynomialMap_eq_zero_iff (p : MvPolynomial K ℕ) : polynomialMap K p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ (polynomialMap_injective K)

@[simp]
theorem polynomialMap_X (i : K) : polynomialMap K (MvPolynomial.X i) =
    algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.X i) := by
  simp [polynomialMap]

/-- Ratios of positive polynomials form a subgroup of the units of the rational-function field. -/
def fractionSubgroup (K : Type*) : Subgroup (FractionRing (MvPolynomial K ℤ))ˣ where
  carrier := {u | ∃ p q : MvPolynomial K ℕ,
    p ≠ 0 ∧ q ≠ 0 ∧ (u : FractionRing (MvPolynomial K ℤ)) =
      polynomialMap K p / polynomialMap K q}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro a b ⟨p, q, hp, hq, ha⟩ ⟨r, s, hr, hs, hb⟩
    exact ⟨p * r, q * s, mul_ne_zero hp hr, mul_ne_zero hq hs,
      by simp [ha, hb, div_mul_div_comm]⟩
  inv_mem' := by
    rintro a ⟨p, q, hp, hq, ha⟩
    exact ⟨q, p, hq, hp, by simp [ha]⟩

end Qsf

/-- The coefficient semifield of nonzero subtraction-free rational functions in variables `K`. -/
abbrev Qsf (K : Type*) : Type _ := ↥(Qsf.fractionSubgroup K)

namespace Qsf

variable {K : Type*}

instance : Coe (Qsf K) (FractionRing (MvPolynomial K ℤ)) := ⟨fun f => f.val.val⟩

/-- The inclusion of subtraction-free rational functions is injective. -/
theorem coe_injective : Function.Injective (fun f : Qsf K =>
    (f : FractionRing (MvPolynomial K ℤ))) :=
  fun _ _ h => Subtype.ext (Units.ext h)

@[ext]
theorem ext {f g : Qsf K}
    (h : (f : FractionRing (MvPolynomial K ℤ)) = g) : f = g :=
  coe_injective h

@[simp]
theorem coe_one : ((1 : Qsf K) : FractionRing (MvPolynomial K ℤ)) = 1 := (rfl)

@[simp]
theorem coe_mul (f g : Qsf K) :
    ((f * g : Qsf K) : FractionRing (MvPolynomial K ℤ)) = f * g := (rfl)

/-- Every subtraction-free function has a positive numerator and denominator. -/
theorem exists_fraction (f : Qsf K) : ∃ p q : MvPolynomial K ℕ,
    p ≠ 0 ∧ q ≠ 0 ∧ (f : FractionRing (MvPolynomial K ℤ)) =
      polynomialMap K p / polynomialMap K q :=
  f.property

/-- Form a subtraction-free rational function from nonzero natural-coefficient polynomials. -/
def ofFraction (p q : MvPolynomial K ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : Qsf K :=
  ⟨Units.mk0 (polynomialMap K p / polynomialMap K q) (by simp [hp, hq]),
    p, q, hp, hq, rfl⟩

@[simp]
theorem coe_ofFraction (p q : MvPolynomial K ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (ofFraction p q hp hq : FractionRing (MvPolynomial K ℤ)) =
      polynomialMap K p / polynomialMap K q :=
  (rfl)

/-- Equality of positive fractions is equality after cross multiplication in `ℕ[K]`. -/
theorem ofFraction_eq_iff (p q r s : MvPolynomial K ℕ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ofFraction p q hp hq = ofFraction r s hr hs ↔ p * s = r * q := by
  rw [← coe_injective.eq_iff, coe_ofFraction, coe_ofFraction,
    div_eq_div_iff (by simpa using hq) (by simpa using hs), ← map_mul, ← map_mul]
  exact (polynomialMap_injective K).eq_iff

private theorem add_fraction_eq (p q r s : MvPolynomial K ℕ)
    (hq : q ≠ 0) (hs : s ≠ 0) :
    polynomialMap K p / polynomialMap K q + polynomialMap K r / polynomialMap K s =
      polynomialMap K (p * s + r * q) / polynomialMap K (q * s) := by
  simpa only [map_add, map_mul, mul_comm] using
    div_add_div (polynomialMap K p) (polynomialMap K r)
      ((polynomialMap_eq_zero_iff q).not.mpr hq)
      ((polynomialMap_eq_zero_iff s).not.mpr hs)

private theorem add_representation (f g : Qsf K) :
    ∃ p q : MvPolynomial K ℕ, p ≠ 0 ∧ q ≠ 0 ∧
      (f : FractionRing (MvPolynomial K ℤ)) + g = polynomialMap K p / polynomialMap K q := by
  obtain ⟨p, q, hp, hq, hf⟩ := exists_fraction f
  obtain ⟨r, s, hr, hs, hg⟩ := exists_fraction g
  have hnum : p * s + r * q ≠ 0 := by
    intro h
    apply mul_ne_zero hp hs
    ext d
    have hd := congrArg (fun t : MvPolynomial K ℕ => t.coeff d) h
    exact (Nat.add_eq_zero_iff.mp (by simpa using hd)).1
  exact ⟨p * s + r * q, q * s, hnum, mul_ne_zero hq hs,
    by rw [hf, hg, add_fraction_eq p q r s hq hs]⟩

instance : Add (Qsf K) where
  add f g :=
    ⟨Units.mk0 ((f : FractionRing (MvPolynomial K ℤ)) + g) (by
      obtain ⟨p, q, hp, hq, h⟩ := add_representation f g
      rw [h]
      exact div_ne_zero ((polynomialMap_eq_zero_iff p).not.mpr hp)
        ((polynomialMap_eq_zero_iff q).not.mpr hq)), by exact add_representation f g⟩

@[simp]
theorem coe_add (f g : Qsf K) :
    ((f + g : Qsf K) : FractionRing (MvPolynomial K ℤ)) = f + g :=
  (rfl)

instance : CoefficientSemifield (Qsf K) where
  add_assoc f g h := coe_injective (by simp [add_assoc])
  add_comm f g := coe_injective (by simp [add_comm])
  left_distrib f g h := coe_injective (by simp [mul_add])
  right_distrib f g h := coe_injective (by simp [add_mul])

/-- The universal variable indexed by `i`. -/
def X (i : K) : Qsf K := ofFraction (MvPolynomial.X i) 1 (by simp) one_ne_zero

@[simp]
theorem coe_X (i : K) : (X i : FractionRing (MvPolynomial K ℤ)) =
    algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.X i) := by
  simp [X]

/-- Inclusion of subtraction-free functions, extended by zero, into the rational-function field. -/
def toFractionRing (K : Type*) : WithZero (Qsf K) →+* FractionRing (MvPolynomial K ℤ) :=
  { WithZero.lift'
      ({ toFun := fun f => (f : FractionRing (MvPolynomial K ℤ))
         map_one' := coe_one
         map_mul' := coe_mul } : Qsf K →* FractionRing (MvPolynomial K ℤ)) with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      all_goals simp [← WithZero.coe_add, WithZero.lift'_zero] }

@[simp]
theorem toFractionRing_coe (f : Qsf K) :
    toFractionRing K (f : WithZero (Qsf K)) = (f : FractionRing (MvPolynomial K ℤ)) :=
  (rfl)

/-- Adjoining zero does not identify distinct subtraction-free functions. -/
theorem toFractionRing_injective (K : Type*) : Function.Injective (toFractionRing K) := by
  intro a b
  induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
  · simp
  · simp [eq_comm]
  · simp
  · intro h
    exact congrArg WithZero.coe (coe_injective h)

section Evaluation

variable {P : Type*} [CoefficientSemifield P]

/-- Evaluate natural-coefficient polynomials using auxiliary addition and an adjoined zero. -/
def polynomialEval (y : K → P) : MvPolynomial K ℕ →+* WithZero P :=
  MvPolynomial.eval₂Hom (Nat.castRingHom _) (fun i => (y i : WithZero P))

@[simp]
theorem polynomialEval_X (y : K → P) (i : K) :
    polynomialEval y (MvPolynomial.X i) = (y i : WithZero P) := by
  simp [polynomialEval]

/-- A positive polynomial never vanishes at a point of a coefficient semifield. -/
@[simp]
theorem polynomialEval_eq_zero_iff (y : K → P) (p : MvPolynomial K ℕ) :
    polynomialEval y p = 0 ↔ p = 0 := by
  have hadd (a b : WithZero P) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
    induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
    all_goals simp [← WithZero.coe_add]
  have hn (n : ℕ) : (n : WithZero P) = 0 ↔ n = 0 := by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.cast_succ, hadd]
  refine ⟨?_, fun h => by simp [h]⟩
  induction p using MvPolynomial.induction_on with
  | C n =>
    intro h
    have hz : n = 0 := (hn n).mp (by simpa [polynomialEval] using h)
    simp [hz]
  | add p q hp hq =>
    rw [map_add, hadd]
    intro h
    simp [hp h.1, hq h.2]
  | mul_X p i hp =>
    intro h
    have hzero : polynomialEval y p = 0 := by simpa using h
    simp [hp hzero]

private theorem fraction_eval_eq (y : K → P) {p q r s : MvPolynomial K ℕ}
    (hq : q ≠ 0) (hs : s ≠ 0)
    (h : polynomialMap K p / polynomialMap K q = polynomialMap K r / polynomialMap K s) :
    polynomialEval y p / polynomialEval y q = polynomialEval y r / polynomialEval y s := by
  have hcross : p * s = r * q := (polynomialMap_injective K) <| by
    simpa only [map_mul] using
      (div_eq_div_iff ((polynomialMap_eq_zero_iff q).not.mpr hq)
        ((polynomialMap_eq_zero_iff s).not.mpr hs)).mp h
  apply (div_eq_div_iff ((polynomialEval_eq_zero_iff y q).not.mpr hq)
    ((polynomialEval_eq_zero_iff y s).not.mpr hs)).mpr
  simpa only [map_mul] using congrArg (polynomialEval y) hcross

private theorem exists_evaluation (y : K → P) :
    ∃ f : CoefficientSemifieldHom (Qsf K) P,
      ∀ (p q : MvPolynomial K ℕ) (hp : p ≠ 0) (hq : q ≠ 0),
        (f (ofFraction p q hp hq) : WithZero P) = polynomialEval y p / polynomialEval y q := by
  -- Choose a fraction only to construct the function; cross multiplication removes the choice.
  let num (f : Qsf K) := (exists_fraction f).choose
  let den (f : Qsf K) := (exists_fraction f).choose_spec.choose
  have hrep (f : Qsf K) : num f ≠ 0 ∧ den f ≠ 0 ∧
      (f : FractionRing (MvPolynomial K ℤ)) = polynomialMap K (num f) / polynomialMap K (den f) :=
    (exists_fraction f).choose_spec.choose_spec
  let e (f : Qsf K) : P := WithZero.unzero (x := polynomialEval y (num f) /
    polynomialEval y (den f)) (by simp only [ne_eq, div_eq_zero_iff,
      polynomialEval_eq_zero_iff, not_or]; exact ⟨(hrep f).1, (hrep f).2.1⟩)
  have he (f : Qsf K) (p q : MvPolynomial K ℕ) (hq : q ≠ 0)
      (hf : (f : FractionRing (MvPolynomial K ℤ)) = polynomialMap K p / polynomialMap K q) :
      (e f : WithZero P) = polynomialEval y p / polynomialEval y q := by
    exact (WithZero.coe_unzero _).trans
      (fraction_eval_eq y (hrep f).2.1 hq ((hrep f).2.2.symm.trans hf))
  have hmul (f g : Qsf K) : e (f * g) = e f * e g := by
    obtain ⟨p, q, hp, hq, hf⟩ := exists_fraction f
    obtain ⟨r, s, hr, hs, hg⟩ := exists_fraction g
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, he f p q hq hf, he g r s hs hg,
      he (f * g) (p * r) (q * s) (mul_ne_zero hq hs)
        (by simp only [coe_mul, hf, hg, map_mul, div_mul_div_comm])]
    simp only [map_mul, div_mul_div_comm]
  have hadd (f g : Qsf K) : e (f + g) = e f + e g := by
    obtain ⟨p, q, hp, hq, hf⟩ := exists_fraction f
    obtain ⟨r, s, hr, hs, hg⟩ := exists_fraction g
    have hab : ((f + g : Qsf K) : FractionRing (MvPolynomial K ℤ)) =
        polynomialMap K (p * s + r * q) / polynomialMap K (q * s) := by
      rw [coe_add, hf, hg, add_fraction_eq p q r s hq hs]
    apply WithZero.coe_injective
    rw [WithZero.coe_add, he f p q hq hf, he g r s hs hg,
      he (f + g) (p * s + r * q) (q * s) (mul_ne_zero hq hs) hab]
    simpa only [map_add, map_mul, mul_comm] using
      (div_add_div (polynomialEval y p) (polynomialEval y r)
        ((polynomialEval_eq_zero_iff y q).not.mpr hq)
        ((polynomialEval_eq_zero_iff y s).not.mpr hs)).symm
  refine ⟨{ toFun := e, map_mul' := hmul, map_add' := hadd, map_one' := ?_ }, ?_⟩
  · apply WithZero.coe_injective
    simpa using he 1 1 1 one_ne_zero (by simp)
  · intro p q hp hq
    exact he _ p q hq (coe_ofFraction p q hp hq)

/-- The homomorphism that substitutes `y i` for each universal variable, using auxiliary sums. -/
def eval (y : K → P) : CoefficientSemifieldHom (Qsf K) P := by
  exact (exists_evaluation y).choose

/-- Evaluation of a positive fraction is the ratio of the two auxiliary polynomial values. -/
@[simp]
theorem eval_ofFraction (y : K → P) (p q : MvPolynomial K ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (eval y (ofFraction p q hp hq) : WithZero P) = polynomialEval y p / polynomialEval y q :=
  (exists_evaluation y).choose_spec p q hp hq

@[simp]
theorem eval_X (y : K → P) (i : K) : eval y (X i) = y i := by
  apply WithZero.coe_injective
  simp only [X, eval_ofFraction, polynomialEval_X, map_one, div_one]

end Evaluation

/-- Evaluating a natural polynomial in the universal variables recovers its ambient image. -/
@[simp]
theorem toFractionRing_polynomialEval (p : MvPolynomial K ℕ) :
    toFractionRing K (polynomialEval (X : K → Qsf K) p) = polynomialMap K p := by
  have h : (toFractionRing K).comp (polynomialEval (X : K → Qsf K)) = polynomialMap K := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [polynomialEval]
    · intro i
      simp
  exact DFunLike.congr_fun h p

section UniversalProperty

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Homomorphisms from the universal semifield are determined by their values on variables. -/
@[ext]
theorem hom_ext {f g : CoefficientSemifieldHom (Qsf K) P}
    (h : ∀ i, f (X i) = g (X i)) : f = g := by
  have hpoly (p : MvPolynomial K ℕ) (hp : p ≠ 0) :
      polynomialEval (X : K → Qsf K) p = (ofFraction p 1 hp one_ne_zero : WithZero (Qsf K)) := by
    apply toFractionRing_injective K
    simp
  have hcomp : f.withZeroMap.comp (polynomialEval (X : K → Qsf K)) =
      g.withZeroMap.comp (polynomialEval (X : K → Qsf K)) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [polynomialEval]
    · intro i
      simp [h i]
  have heq (p : MvPolynomial K ℕ) (hp : p ≠ 0) :
      f (ofFraction p 1 hp one_ne_zero) = g (ofFraction p 1 hp one_ne_zero) := by
    apply WithZero.coe_injective
    simpa only [RingHom.comp_apply, hpoly p hp, CoefficientSemifieldHom.withZeroMap_coe] using
      DFunLike.congr_fun hcomp p
  apply CoefficientSemifieldHom.ext
  intro a
  obtain ⟨p, q, hp, hq, ha⟩ := exists_fraction a
  have hfrac : a = ofFraction p 1 hp one_ne_zero / ofFraction q 1 hq one_ne_zero := by
    apply coe_injective
    simpa [div_eq_mul_inv] using ha
  simp [hfrac, heq p hp, heq q hq]

/-- The universal property: assigning variables is equivalent to a coefficient homomorphism. -/
def evalEquiv : (K → P) ≃ CoefficientSemifieldHom (Qsf K) P where
  toFun := eval
  invFun f i := f (X i)
  left_inv y := funext (eval_X y)
  right_inv f := hom_ext fun i => eval_X (fun j => f (X j)) i

@[simp]
theorem evalEquiv_apply (y : K → P) : evalEquiv y = eval y := (rfl)

@[simp]
theorem evalEquiv_symm_apply (f : CoefficientSemifieldHom (Qsf K) P) (i : K) :
    evalEquiv.symm f i = f (X i) := (rfl)

/-- Coefficient specialization commutes with universal evaluation. -/
@[simp]
theorem comp_eval (f : CoefficientSemifieldHom P Q) (y : K → P) :
    f.comp (eval y) = eval (f ∘ y) := by
  apply hom_ext
  intro i
  simp

@[simp]
theorem eval_X_self : eval (X : K → Qsf K) = CoefficientSemifieldHom.id (Qsf K) := by
  apply hom_ext
  intro i
  simp

end UniversalProperty

/-! ### Checks -/

-- Cancellation of a subtraction-free expression survives every coefficient specialization.
example {P : Type*} [CoefficientSemifield P] (y : Fin 2 → P) :
    eval y ((X 0 ^ 2 + X 0 * X 1) / (X 0 + X 1)) = y 0 := by
  simp only [map_div, map_add, map_pow, map_mul, eval_X]
  apply div_eq_iff_eq_mul.mpr
  simp [pow_two, mul_add]

-- With no variables, auxiliary addition still distinguishes positive rational constants.
example : (1 + 1 : Qsf Empty) ≠ 1 := by
  intro h
  have he := congrArg (fun f : Qsf Empty => (f : FractionRing (MvPolynomial Empty ℤ))) h
  simp only [coe_add, coe_one] at he
  exact one_ne_zero (add_left_cancel (he.trans (add_zero 1).symm))

end Qsf

end TauCeti
