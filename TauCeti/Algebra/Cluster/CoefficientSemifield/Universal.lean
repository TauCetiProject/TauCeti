/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero
public import TauCeti.Algebra.MvPolynomial.ZeroSumFree
public import TauCeti.RingTheory.Localization.TotalQuotient
public import TauCeti.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The universal subtraction-free coefficient semifield

`QsfZero K` is the localization of the natural-coefficient polynomials at all nonzero
polynomials. Its units form the coefficient semifield `Qsf K`. Evaluation into any
zero-sum-free semifield extends through the localization because positive polynomials
evaluated at units cannot vanish. Restriction to units gives evaluation into any
coefficient semifield after adjoining zero to the target.

The comparison with the rational-function field over the integers recovers the usual
interpretation as ratios of nonzero natural-coefficient polynomials. The universal
coefficient semifield is described in Fomin and Zelevinsky, *Cluster algebras IV:
Coefficients*, §2.
-/

public section

noncomputable section

namespace TauCeti

/-- Subtraction-free rational functions in variables `K`, including zero. -/
abbrev QsfZero (K : Type*) := TotalQuotient (MvPolynomial K ℕ)

/-- The universal coefficient semifield on the variable type `K`. -/
abbrev Qsf (K : Type*) := (QsfZero K)ˣ

namespace QsfZero

variable {K : Type*}

/-- A variable in the total quotient semiring. -/
def X (i : K) : QsfZero K :=
  algebraMap (MvPolynomial K ℕ) (QsfZero K) (MvPolynomial.X i)

@[simp]
theorem algebraMap_X (i : K) :
    algebraMap (MvPolynomial K ℕ) (QsfZero K) (MvPolynomial.X i) = X i := (rfl)

@[simp]
theorem X_ne_zero (i : K) : X i ≠ 0 := by
  rw [← algebraMap_X]
  exact (map_eq_zero_iff _ (TotalQuotient.algebraMap_injective (MvPolynomial K ℕ))).not.mpr
    (MvPolynomial.X_ne_zero i)

section Evaluation

variable {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]

private theorem eval₂Hom_isUnit (y : K → Sˣ) (p : regularElements (MvPolynomial K ℕ)) :
    IsUnit (MvPolynomial.eval₂Hom (Nat.castRingHom S) (fun i => (y i : S)) p) :=
  isUnit_iff_ne_zero.mpr fun h =>
    (mem_regularElements (R := MvPolynomial K ℕ).mp p.property).ne_zero <|
    (MvPolynomial.eval₂Hom_units_eq_zero_iff (Nat.castRingHom S)
      (fun n => (TauCeti.natCast_eq_zero_iff (n := n)).mp) y (p : MvPolynomial K ℕ)).mp h

/-- Evaluate at units in a zero-sum-free semifield. -/
def eval (y : K → Sˣ) : QsfZero K →+* S :=
  IsLocalization.lift (eval₂Hom_isUnit y)

@[simp]
theorem eval_algebraMap (y : K → Sˣ) (p : MvPolynomial K ℕ) :
    eval y (algebraMap (MvPolynomial K ℕ) (QsfZero K) p) =
      MvPolynomial.eval₂Hom (Nat.castRingHom S) (fun i => (y i : S)) p :=
  IsLocalization.lift_eq _ _

@[simp]
theorem eval_X (y : K → Sˣ) (i : K) : eval y (X i) = (y i : S) := by
  simp [← algebraMap_X]

/-- Evaluation computes the ratio of the two polynomial values. -/
theorem eval_mk' (y : K → Sˣ) (p : MvPolynomial K ℕ) (q : regularElements (MvPolynomial K ℕ)) :
    eval y (IsLocalization.mk' (QsfZero K) p q) =
      MvPolynomial.eval₂Hom (Nat.castRingHom S) (fun i => (y i : S)) p /
        MvPolynomial.eval₂Hom (Nat.castRingHom S) (fun i => (y i : S)) q := by
  rw [TotalQuotient.map_mk'_eq_div, eval_algebraMap, eval_algebraMap]

end Evaluation

/-- A semiring homomorphism out of `QsfZero K` is determined by its values on the variables. -/
@[ext]
theorem hom_ext {S : Type*} [CommSemiring S] {f g : QsfZero K →+* S}
    (h : ∀ i, f (X i) = g (X i)) : f = g := by
  apply IsLocalization.ringHom_ext (regularElements (MvPolynomial K ℕ))
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · exact h

/-- Evaluation at the variable generators is the identity. -/
@[simp]
theorem eval_X_left : eval (fun i => Units.mk0 (X i) (X_ne_zero i)) = RingHom.id (QsfZero K) := by
  apply hom_ext
  intro i
  simp

/-- Assigning units in a zero-sum-free semifield to the variables is equivalent to giving a
semiring homomorphism out of `QsfZero K`. -/
def evalEquiv {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] :
    (K → Sˣ) ≃ (QsfZero K →+* S) where
  toFun := eval
  invFun f i := Units.map f.toMonoidHom (Units.mk0 (X i) (X_ne_zero i))
  left_inv y := funext fun i => Units.ext (eval_X y i)
  right_inv f := hom_ext fun i => by simp

@[simp]
theorem evalEquiv_apply {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] (y : K → Sˣ) :
    evalEquiv y = eval y := (rfl)

@[simp]
theorem val_evalEquiv_symm_apply {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    (f : QsfZero K →+* S) (i : K) : ((evalEquiv.symm f i : Sˣ) : S) = f (X i) := by
  change (Units.map f.toMonoidHom (Units.mk0 (X i) (X_ne_zero i)) : S) = f (X i)
  simp

/-- Applying a semiring map after evaluation evaluates at the images of the assigned units. -/
@[simp]
theorem comp_eval {S T : Type*} [Semifield S] [Semifield T] [Subsingleton (AddUnits S)]
    [Subsingleton (AddUnits T)] (f : S →+* T) (y : K → Sˣ) :
    f.comp (eval y) = eval (Units.map f.toMonoidHom ∘ y) := by
  apply hom_ext
  intro i
  simp

section FractionField

/-- Map natural-coefficient polynomials into the integral rational-function field. -/
def polynomialMap (K : Type*) :
    MvPolynomial K ℕ →+* FractionRing (MvPolynomial K ℤ) :=
  (algebraMap _ _).comp (MvPolynomial.map (Nat.castRingHom ℤ))

/-- The coefficientwise polynomial map into the integral fraction field is injective. -/
theorem polynomialMap_injective (K : Type*) : Function.Injective (polynomialMap K) :=
  (IsFractionRing.injective (MvPolynomial K ℤ) _).comp
    (MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective)

@[simp]
theorem polynomialMap_apply (p : MvPolynomial K ℕ) :
    polynomialMap K p =
      algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) p) := (rfl)

/-- The comparison with the rational-function field with integer coefficients. -/
def toFractionRing (K : Type*) : QsfZero K →+* FractionRing (MvPolynomial K ℤ) :=
  IsLocalization.map (FractionRing (MvPolynomial K ℤ)) (MvPolynomial.map (Nat.castRingHom ℤ))
    (by
      intro r hr
      rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => (mem_regularElements (R := MvPolynomial K ℕ).mp hr).ne_zero
        (MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective (by simpa using h)))

@[simp]
theorem toFractionRing_algebraMap (p : MvPolynomial K ℕ) :
    toFractionRing K (algebraMap (MvPolynomial K ℕ) (QsfZero K) p) =
      algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) p) :=
  IsLocalization.map_eq (S := QsfZero K) _ _

/-- Distinct subtraction-free functions stay distinct in the rational-function field. -/
theorem toFractionRing_injective (K : Type*) : Function.Injective (toFractionRing K) := by
  exact IsLocalization.lift_injective_of_injective _ (polynomialMap_injective K)

@[simp]
theorem toFractionRing_X (i : K) :
    toFractionRing K (X i) = algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.X i) := by
  rw [← algebraMap_X, toFractionRing_algebraMap, MvPolynomial.map_X]

/-- The image of a fraction is the ratio of its two integer-coefficient polynomial images. -/
theorem toFractionRing_mk' (p : MvPolynomial K ℕ) (q : regularElements (MvPolynomial K ℕ)) :
    toFractionRing K (IsLocalization.mk' (QsfZero K) p q) =
      polynomialMap K p / polynomialMap K q := by
  simp only [TotalQuotient.map_mk'_eq_div, toFractionRing_algebraMap, polynomialMap,
    RingHom.comp_apply]

end FractionField

end QsfZero

namespace Qsf

open CoefficientSemifield CoefficientSemifieldHom

variable {K : Type*}

/-- The universal generator, as a unit of the total quotient semiring. -/
def X (i : K) : Qsf K := Units.mk0 (QsfZero.X i) (QsfZero.X_ne_zero i)

@[simp]
theorem val_X (i : K) : (X i : QsfZero K) = QsfZero.X i := (rfl)

/-- Every element has a presentation with nonzero numerator and denominator. -/
theorem exists_mk' (a : Qsf K) :
    ∃ (p : MvPolynomial K ℕ) (q : regularElements (MvPolynomial K ℕ)),
      p ≠ 0 ∧ IsLocalization.mk' (QsfZero K) p q = (a : QsfZero K) := by
  obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.mk'_surjective (regularElements (MvPolynomial K ℕ))
    (a : QsfZero K)
  exact ⟨p, q, IsLocalization.ne_zero_of_mk'_ne_zero (h.symm ▸ a.ne_zero), h⟩

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Evaluation on the coefficient semifield is the restriction of semiring evaluation to units. -/
def eval (y : K → P) : CoefficientSemifieldHom (Qsf K) P :=
  unitsWithZero.comp (mapUnits (QsfZero.eval (fun i => WithZero.unitsWithZeroEquiv.symm (y i))))

/-- Evaluation agrees with semiring evaluation after adjoining zero to the target. -/
@[simp]
theorem coe_eval (y : K → P) (a : Qsf K) :
    (eval y a : WithZero P) =
      QsfZero.eval (fun i => WithZero.unitsWithZeroEquiv.symm (y i)) (a : QsfZero K) := by
  simp [eval]

@[simp]
theorem eval_X (y : K → P) (i : K) : eval y (X i) = y i := by
  apply WithZero.coe_injective
  simp

/-- Coefficient homomorphisms from `Qsf K` are determined by their values on the variables. -/
@[ext]
theorem hom_ext {f g : CoefficientSemifieldHom (Qsf K) P}
    (h : ∀ i, f (X i) = g (X i)) : f = g := by
  have hfg : f.withZeroMap.comp (withZeroUnitsRingEquiv (QsfZero K)).symm.toRingHom =
      g.withZeroMap.comp (withZeroUnitsRingEquiv (QsfZero K)).symm.toRingHom := by
    apply QsfZero.hom_ext
    intro i
    simpa [← val_X] using h i
  apply CoefficientSemifieldHom.ext
  intro a
  simpa using DFunLike.congr_fun hfg (a : QsfZero K)

/-- Universal property: families in a coefficient semifield classify homomorphisms from
`Qsf K`. -/
def evalEquiv : (K → P) ≃ CoefficientSemifieldHom (Qsf K) P where
  toFun := eval
  invFun f i := f (X i)
  left_inv y := funext (eval_X y)
  right_inv f := hom_ext (eval_X fun i => f (X i))

@[simp]
theorem evalEquiv_apply (y : K → P) : evalEquiv y = eval y := (rfl)

@[simp]
theorem evalEquiv_symm_apply (f : CoefficientSemifieldHom (Qsf K) P) (i : K) :
    evalEquiv.symm f i = f (X i) := (rfl)

/-- Substitution commutes with applying a homomorphism to the coefficients. -/
@[simp]
theorem comp_eval (f : CoefficientSemifieldHom P Q) (y : K → P) :
    f.comp (eval y) = eval (f ∘ y) := by
  apply hom_ext
  intro i
  simp

@[simp]
theorem eval_X_left : eval (X : K → Qsf K) = CoefficientSemifieldHom.id (Qsf K) := by
  apply hom_ext
  intro i
  simp

/-- Rename the variables along an arbitrary function. -/
def rename {L : Type*} (r : K → L) : CoefficientSemifieldHom (Qsf K) (Qsf L) :=
  eval (X ∘ r)

@[simp]
theorem rename_X {L : Type*} (r : K → L) (i : K) : rename r (X i) = X (r i) :=
  eval_X _ _

/-- Renaming along the identity is the identity homomorphism. -/
@[simp]
theorem rename_id : rename (id : K → K) = CoefficientSemifieldHom.id (Qsf K) := eval_X_left

/-- Renaming preserves composition of reindexing functions. -/
@[simp]
theorem rename_comp_rename {L M : Type*} (r : K → L) (s : L → M) :
    (rename s).comp (rename r) = rename (s ∘ r) := by
  apply hom_ext
  intro i
  simp

/-- Evaluation after renaming is evaluation at the pulled back assignment. -/
@[simp]
theorem eval_comp_rename {L : Type*} (r : K → L) (y : L → P) :
    (eval y).comp (rename r) = eval (y ∘ r) := by
  apply hom_ext
  intro i
  simp

end Qsf

end TauCeti
