/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero
public import TauCeti.Algebra.MonoidAlgebra.ZeroSumFree
public import TauCeti.RingTheory.Localization.TotalQuotient
import TauCeti.Algebra.MvPolynomial.ZeroSumFree
import TauCeti.Data.Nat.Cast.ZeroSumFree
import TauCeti.RingTheory.Localization.Defs

/-!
# The universal coefficient semifield

`TauCeti.QsfZero K` is the total quotient of the semiring `MvPolynomial K ℕ` of
natural-coefficient polynomials in variables `X i`, `i : K`. It is a semifield in which sums vanish
only when every summand does, and its units form the coefficient semifield `TauCeti.Qsf K` of
subtraction-free rational functions. These are the universal coefficients of Fomin and
Zelevinsky: for every family `y` in a coefficient semifield `P` there is exactly one homomorphism
`TauCeti.Qsf.eval y : Qsf K → P` sending `X i` to `y i` (`TauCeti.Qsf.evalEquiv`).

Evaluation is constructed on the semiring `QsfZero K`. A nonzero natural-coefficient polynomial,
evaluated at units of a semifield in which sums vanish only when every summand does, is nonzero
and hence a unit, so polynomial evaluation extends through the localization
(`TauCeti.QsfZero.eval`, with universal property `TauCeti.QsfZero.evalEquiv`). Evaluation into a
coefficient semifield `P` is the restriction to units of evaluation into `WithZero P`, and
restricting evaluation into a semifield `S` to units is evaluation into `Sˣ`
(`TauCeti.Qsf.mapUnits_eval`). Both evaluations commute with maps of the targets and with
renaming the variables.

Mapping coefficients to `ℤ` embeds `QsfZero K` in the field of rational functions
`FractionRing (MvPolynomial K ℤ)` (`TauCeti.QsfZero.toFractionRing_injective`). Its image consists
of the ratios of natural-coefficient polynomials with nonzero denominator, and `Qsf K` corresponds
to the ratios of nonzero ones.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §2, Definitions 2.1 and 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CoefficientSemifield

/-- The semifield of subtraction-free rational functions in variables indexed by `K`, together
with zero: the total quotient of the natural-coefficient polynomials. -/
abbrev QsfZero (K : Type*) := TotalQuotient (MvPolynomial K ℕ)

/-- The universal coefficient semifield in variables indexed by `K`: the nonzero subtraction-free
rational functions, as the units of `QsfZero K`. -/
abbrev Qsf (K : Type*) := (QsfZero K)ˣ

variable {K L M : Type*}

namespace QsfZero

/-- The variable indexed by `i`. -/
def X (i : K) : QsfZero K :=
  algebraMap (MvPolynomial K ℕ) (QsfZero K) (MvPolynomial.X i)

@[simp]
theorem algebraMap_X (i : K) :
    algebraMap (MvPolynomial K ℕ) (QsfZero K) (MvPolynomial.X i) = X i :=
  (rfl)

@[simp]
theorem X_ne_zero (i : K) : X i ≠ 0 := by
  rw [← algebraMap_X, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  exact MvPolynomial.X_ne_zero i

end QsfZero

namespace Qsf

/-- The variable indexed by `i`, as a unit. -/
def X (i : K) : Qsf K :=
  Units.mk0 (QsfZero.X i) (QsfZero.X_ne_zero i)

@[simp]
theorem val_X (i : K) : (X i : QsfZero K) = QsfZero.X i :=
  (rfl)

end Qsf

namespace QsfZero

/-! ### Evaluation in semifields -/

section Eval

variable {S T : Type*} [Semifield S] [Subsingleton (AddUnits S)] [Semifield T]
  [Subsingleton (AddUnits T)]

/-- A nonzero natural-coefficient polynomial takes unit values at units. -/
private theorem isUnit_aeval (y : K → Sˣ) (p : regulars (MvPolynomial K ℕ)) :
    IsUnit (MvPolynomial.aeval (fun i ↦ (y i : S)) (p : MvPolynomial K ℕ)) := by
  refine isUnit_iff_ne_zero.mpr fun h ↦ mem_regulars_iff_ne_zero.mp p.2 ?_
  rwa [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_zero_iff (fun a ↦ by simp)
    fun i ↦ (y i).isUnit.mem_nonZeroDivisors] at h

/-- Evaluation of subtraction-free rational functions at units of a semifield in which sums
vanish only when every summand does. -/
def eval (y : K → Sˣ) : QsfZero K →+* S :=
  IsLocalization.lift (g := (MvPolynomial.aeval fun i ↦ (y i : S)).toRingHom) (isUnit_aeval y)

@[simp]
theorem eval_algebraMap (y : K → Sˣ) (p : MvPolynomial K ℕ) :
    eval y (algebraMap (MvPolynomial K ℕ) (QsfZero K) p) =
      MvPolynomial.aeval (fun i ↦ (y i : S)) p :=
  IsLocalization.lift_eq _ p

@[simp]
theorem eval_X (y : K → Sˣ) (i : K) : eval y (X i) = y i := by
  simp [← algebraMap_X]

/-- Evaluation of a fraction is the quotient of the values of its numerator and denominator. -/
theorem eval_mk' (y : K → Sˣ) (p : MvPolynomial K ℕ) (q : regulars (MvPolynomial K ℕ)) :
    eval y (IsLocalization.mk' (QsfZero K) p q) =
      MvPolynomial.aeval (fun i ↦ (y i : S)) p /
        MvPolynomial.aeval (fun i ↦ (y i : S)) (q : MvPolynomial K ℕ) := by
  rw [TotalQuotient.mk'_eq_div, map_div₀, eval_algebraMap, eval_algebraMap]

/-- Semiring maps out of `QsfZero K` agree when they agree on the variables. -/
@[ext]
theorem hom_ext {A : Type*} [Semiring A] {f g : QsfZero K →+* A} (h : ∀ i, f (X i) = g (X i)) :
    f = g :=
  IsLocalization.ringHom_ext (regulars (MvPolynomial K ℕ)) <|
    MvPolynomial.ringHom_ext (fun n ↦ by simp) fun i ↦ by simpa using h i

/-- Evaluation at the variables is the identity. -/
@[simp]
theorem eval_X_left : eval (Qsf.X : K → Qsf K) = RingHom.id (QsfZero K) := by
  ext
  simp

/-- A semiring map applied to an evaluation is evaluation at the images of the values. -/
@[simp]
theorem map_eval (f : S →+* T) (y : K → Sˣ) (a : QsfZero K) :
    f (eval y a) = eval (fun i ↦ Units.map f (y i)) a := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _) fun i ↦ by simp) a

theorem comp_eval (f : S →+* T) (y : K → Sˣ) :
    f.comp (eval y) = eval fun i ↦ Units.map f (y i) :=
  RingHom.ext (map_eval f y)

/-- **Universal property of `QsfZero K`.** Semiring maps from `QsfZero K` to a semifield in
which sums vanish only when every summand does correspond to families of units, by evaluation. -/
def evalEquiv : (K → Sˣ) ≃ (QsfZero K →+* S) where
  toFun := eval
  invFun f i := Units.map f (Qsf.X i)
  left_inv y := funext fun i ↦ Units.ext <| by simp
  right_inv f := by ext; simp

@[simp]
theorem evalEquiv_apply (y : K → Sˣ) : evalEquiv y = eval y :=
  (rfl)

@[simp]
theorem evalEquiv_symm_apply (f : QsfZero K →+* S) (i : K) :
    evalEquiv.symm f i = Units.map f (Qsf.X i) :=
  (rfl)

end Eval

/-! ### Renaming the variables -/

section Rename

/-- Rename the variables along a function `r : K → L`. -/
def rename (r : K → L) : QsfZero K →+* QsfZero L :=
  eval fun i ↦ Qsf.X (r i)

@[simp]
theorem rename_X (r : K → L) (i : K) : rename r (X i) = X (r i) := by
  simp [rename]

@[simp]
theorem rename_algebraMap (r : K → L) (p : MvPolynomial K ℕ) :
    rename r (algebraMap (MvPolynomial K ℕ) (QsfZero K) p) =
      algebraMap (MvPolynomial L ℕ) (QsfZero L) (MvPolynomial.rename r p) := by
  have : (rename r).comp (algebraMap (MvPolynomial K ℕ) (QsfZero K)) =
      (algebraMap (MvPolynomial L ℕ) (QsfZero L)).comp (MvPolynomial.rename r).toRingHom :=
    MvPolynomial.ringHom_ext (fun n ↦ by simp) fun i ↦ by simp
  exact DFunLike.congr_fun this p

@[simp]
theorem rename_id : rename (id : K → K) = RingHom.id (QsfZero K) := by
  ext
  simp

@[simp]
theorem rename_rename (r : K → L) (s : L → M) (a : QsfZero K) :
    rename s (rename r a) = rename (s ∘ r) a := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := rename _) fun i ↦ by simp) a

theorem rename_comp_rename (r : K → L) (s : L → M) :
    (rename s).comp (rename r) = rename (s ∘ r) :=
  RingHom.ext (rename_rename r s)

variable {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]

@[simp]
theorem eval_rename (r : K → L) (y : L → Sˣ) (a : QsfZero K) :
    eval y (rename r a) = eval (y ∘ r) a := by
  rw [← RingHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _) fun i ↦ by simp) a

end Rename

/-! ### Comparison with rational functions -/

section FractionRing

variable (K) in
/-- The comparison of subtraction-free rational functions with the rational functions with
integer coefficients, induced by mapping natural coefficients to `ℤ`. -/
def toFractionRing : QsfZero K →+* FractionRing (MvPolynomial K ℤ) :=
  IsLocalization.lift (M := regulars (MvPolynomial K ℕ))
    (g := (algebraMap (MvPolynomial K ℤ) (FractionRing (MvPolynomial K ℤ))).comp
      (MvPolynomial.map (Nat.castRingHom ℤ))) fun p ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      ← map_zero (MvPolynomial.map (Nat.castRingHom ℤ)),
      (MvPolynomial.map_injective _ Nat.cast_injective).eq_iff]
    exact mem_regulars_iff_ne_zero.mp p.2

@[simp]
theorem toFractionRing_algebraMap (p : MvPolynomial K ℕ) :
    toFractionRing K (algebraMap (MvPolynomial K ℕ) (QsfZero K) p) =
      algebraMap (MvPolynomial K ℤ) (FractionRing (MvPolynomial K ℤ))
        (MvPolynomial.map (Nat.castRingHom ℤ) p) :=
  IsLocalization.lift_eq _ p

@[simp]
theorem toFractionRing_X (i : K) :
    toFractionRing K (X i) =
      algebraMap (MvPolynomial K ℤ) (FractionRing (MvPolynomial K ℤ)) (MvPolynomial.X i) := by
  simp [← algebraMap_X]

/-- Subtraction-free rational functions embed in the rational functions. -/
theorem toFractionRing_injective : Function.Injective (toFractionRing K) :=
  IsLocalization.lift_injective_of_injective _ <| by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective _ _).comp (MvPolynomial.map_injective _ Nat.cast_injective)

@[simp]
theorem toFractionRing_inj {a b : QsfZero K} : toFractionRing K a = toFractionRing K b ↔ a = b :=
  toFractionRing_injective.eq_iff

/-- The image of a fraction is the ratio of its numerator and denominator. -/
theorem toFractionRing_mk' (p : MvPolynomial K ℕ) (q : regulars (MvPolynomial K ℕ)) :
    toFractionRing K (IsLocalization.mk' (QsfZero K) p q) =
      algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) p) /
        algebraMap (MvPolynomial K ℤ) _
          (MvPolynomial.map (Nat.castRingHom ℤ) (q : MvPolynomial K ℕ)) := by
  rw [TotalQuotient.mk'_eq_div, map_div₀, toFractionRing_algebraMap, toFractionRing_algebraMap]

/-- The rational functions coming from subtraction-free ones are exactly the ratios of
natural-coefficient polynomials with nonzero denominator. -/
theorem mem_range_toFractionRing_iff {z : FractionRing (MvPolynomial K ℤ)} :
    z ∈ Set.range (toFractionRing K) ↔ ∃ p q : MvPolynomial K ℕ, q ≠ 0 ∧
      z = algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) p) /
        algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) q) := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars (MvPolynomial K ℕ)) a
    exact ⟨p, q, mem_regulars_iff_ne_zero.mp q.2, toFractionRing_mk' p q⟩
  · rintro ⟨p, q, hq, rfl⟩
    exact ⟨IsLocalization.mk' _ p ⟨q, mem_regulars_iff_ne_zero.mpr hq⟩, toFractionRing_mk' _ _⟩

end FractionRing

end QsfZero

namespace Qsf

/-! ### The universal coefficient semifield -/

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Evaluation of subtraction-free rational functions in a coefficient semifield, sending the
variable `X i` to `y i`. -/
def eval (y : K → P) : CoefficientSemifieldHom (Qsf K) P :=
  unitsWithZeroRingEquiv.toCoefficientSemifieldHom.comp
    (QsfZero.eval fun i ↦ unitsWithZeroRingEquiv.symm (y i)).mapUnits

/-- Evaluation in a coefficient semifield is evaluation in the semifield obtained by adjoining
zero. -/
theorem coe_eval_apply (y : K → P) (a : Qsf K) :
    (eval y a : WithZero P) = QsfZero.eval (fun i ↦ unitsWithZeroRingEquiv.symm (y i)) a := by
  simp [eval]

@[simp]
theorem eval_X (y : K → P) (i : K) : eval y (X i) = y i :=
  WithZero.coe_injective <| by simp [coe_eval_apply]

/-- Homomorphisms out of the universal coefficient semifield agree when they agree on the
variables. -/
@[ext]
theorem hom_ext {f g : CoefficientSemifieldHom (Qsf K) P} (h : ∀ i, f (X i) = g (X i)) : f = g := by
  refine CoefficientSemifieldHom.withZeroMap_injective ?_
  have : f.withZeroMap.comp (withZeroUnitsRingEquiv (QsfZero K)).symm.toRingHom =
      g.withZeroMap.comp (withZeroUnitsRingEquiv (QsfZero K)).symm.toRingHom :=
    QsfZero.hom_ext fun i ↦ by simpa [← val_X] using congrArg WithZero.coe (h i)
  simpa [RingHom.comp_assoc] using
    congrArg (·.comp (withZeroUnitsRingEquiv (QsfZero K)).toRingHom) this

/-- **Universal property of `Qsf K`.** Homomorphisms from `Qsf K` to a coefficient semifield
correspond to families of elements, by evaluation. -/
def evalEquiv : (K → P) ≃ CoefficientSemifieldHom (Qsf K) P where
  toFun := eval
  invFun f i := f (X i)
  left_inv y := funext (eval_X y)
  right_inv f := by ext; simp

@[simp]
theorem evalEquiv_apply (y : K → P) : evalEquiv y = eval y :=
  (rfl)

@[simp]
theorem evalEquiv_symm_apply (f : CoefficientSemifieldHom (Qsf K) P) (i : K) :
    evalEquiv.symm f i = f (X i) :=
  (rfl)

/-- Evaluation at the variables is the identity. -/
@[simp]
theorem eval_X_left : eval (X : K → Qsf K) = CoefficientSemifieldHom.id (Qsf K) := by
  ext
  simp

/-- A homomorphism applied to an evaluation is evaluation at the images of the values. -/
@[simp]
theorem map_eval (f : CoefficientSemifieldHom P Q) (y : K → P) (a : Qsf K) :
    f (eval y a) = eval (f ∘ y) a := by
  rw [← CoefficientSemifieldHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _) fun i ↦ by simp) a

theorem comp_eval (f : CoefficientSemifieldHom P Q) (y : K → P) :
    f.comp (eval y) = eval (f ∘ y) :=
  CoefficientSemifieldHom.ext fun a ↦ (f.comp_apply _ a).trans (map_eval f y a)

section Semifield

variable {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]

/-- Restricting evaluation in a semifield to the units is evaluation in its coefficient
semifield of units. -/
theorem mapUnits_eval (y : K → Sˣ) : (QsfZero.eval y).mapUnits = eval y := by
  ext
  simp

/-- Evaluation in the coefficient semifield of units of a semifield is evaluation in the
semifield. -/
@[simp]
theorem val_eval (y : K → Sˣ) (a : Qsf K) : (eval y a : S) = QsfZero.eval y a := by
  rw [← mapUnits_eval, RingHom.val_mapUnits]

end Semifield

/-- In `Qsf (Fin 2)`, the fraction `(u₀² + u₀u₁) / (u₀ + u₁)` evaluates to the value of `u₀`
in every coefficient semifield. -/
example (y : Fin 2 → P) : eval y ((X 0 ^ 2 + X 0 * X 1) / (X 0 + X 1)) = y 0 := by
  simp [pow_two, ← mul_add]

/-! ### Renaming the variables -/

/-- Rename the variables along a function `r : K → L`. -/
def rename (r : K → L) : CoefficientSemifieldHom (Qsf K) (Qsf L) :=
  (QsfZero.rename r).mapUnits

@[simp]
theorem val_rename (r : K → L) (a : Qsf K) :
    (rename r a : QsfZero L) = QsfZero.rename r a :=
  RingHom.val_mapUnits _ a

/-- Renaming is evaluation at the renamed variables. -/
theorem rename_eq_eval (r : K → L) : rename r = eval fun i ↦ X (r i) :=
  mapUnits_eval _

@[simp]
theorem rename_X (r : K → L) (i : K) : rename r (X i) = X (r i) :=
  Units.ext <| by simp

@[simp]
theorem rename_id : rename (id : K → K) = CoefficientSemifieldHom.id (Qsf K) := by
  ext
  simp

@[simp]
theorem rename_rename (r : K → L) (s : L → M) (a : Qsf K) :
    rename s (rename r a) = rename (s ∘ r) a :=
  Units.ext <| by simp

theorem rename_comp_rename (r : K → L) (s : L → M) :
    (rename s).comp (rename r) = rename (s ∘ r) :=
  CoefficientSemifieldHom.ext fun a ↦ ((rename s).comp_apply _ a).trans (rename_rename r s a)

@[simp]
theorem eval_rename (r : K → L) (y : L → P) (a : Qsf K) :
    eval y (rename r a) = eval (y ∘ r) a := by
  rw [← CoefficientSemifieldHom.comp_apply]
  exact DFunLike.congr_fun (hom_ext (g := eval _) fun i ↦ by simp) a

/-! ### Comparison with rational functions -/

/-- The rational functions coming from the universal coefficient semifield are exactly the
ratios of nonzero natural-coefficient polynomials. -/
theorem exists_toFractionRing_eq_iff {z : FractionRing (MvPolynomial K ℤ)} :
    (∃ a : Qsf K, QsfZero.toFractionRing K a = z) ↔ ∃ p q : MvPolynomial K ℕ, p ≠ 0 ∧ q ≠ 0 ∧
      z = algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) p) /
        algebraMap (MvPolynomial K ℤ) _ (MvPolynomial.map (Nat.castRingHom ℤ) q) := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.mk'_surjective (regulars (MvPolynomial K ℕ))
      (a : QsfZero K)
    refine ⟨p, q, IsLocalization.ne_zero_of_mk'_ne_zero (h ▸ a.ne_zero),
      mem_regulars_iff_ne_zero.mp q.2, ?_⟩
    rw [← h, QsfZero.toFractionRing_mk']
  · rintro ⟨p, q, hp, hq, rfl⟩
    have hq' : q ∈ regulars (MvPolynomial K ℕ) := mem_regulars_iff_ne_zero.mpr hq
    refine ⟨Units.mk0 (IsLocalization.mk' _ p ⟨q, hq'⟩) ?_, QsfZero.toFractionRing_mk' _ _⟩
    rw [ne_eq, IsLocalization.mk'_eq_zero_iff]
    rintro ⟨m, hm⟩
    exact hp ((mem_regulars.mp m.2).left (by simpa using hm))

end Qsf

end TauCeti
