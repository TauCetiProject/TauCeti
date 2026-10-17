/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Ore extensions by a skew derivation

This file constructs the Ore extension associated to an algebra endomorphism `σ` and a
`σ`-derivation `δ`. Its elements are finitely supported left-coefficient sequences
`∑ i, aᵢ Xⁱ`, and multiplication is characterized by

`X * C a = C (σ a) * X + C (δ a)`.

The direct finitely supported model makes the left monomials a basis without any injectivity
assumption on `σ`. Multiplication is constructed through the faithful action on the same free
module: `C a` acts coefficientwise on the left, while `X` sends `a Xⁿ` to
`σ(a) Xⁿ⁺¹ + δ(a) Xⁿ`.

## Main definitions

* `TauCeti.SigmaDerivation`: a linear map satisfying the skew Leibniz rule.
* `TauCeti.OreExtension`: the associated Ore extension with left coefficients.
* `TauCeti.OreExtension.C` and `TauCeti.OreExtension.X`: its constants and variable.

## References

* P. M. Cohn, *Free Rings and Their Relations*, second edition, Chapter 2.
* The finitely supported normal-form design follows Mathlib's `SkewPolynomial`; the extra
  degree-preserving term implements the skew derivation.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {k : Type u} {R : Type v} [CommSemiring k] [Semiring R] [Algebra k R]

/-- A `σ`-derivation is a linear map satisfying
`δ (a * b) = σ a * δ b + δ a * b` and sending one to zero. -/
@[ext]
structure SigmaDerivation (σ : R →ₐ[k] R) extends R →ₗ[k] R where
  /-- The skew Leibniz rule. -/
  leibniz' (a b : R) : toLinearMap (a * b) = σ a * toLinearMap b + toLinearMap a * b
  /-- A skew derivation sends one to zero. -/
  map_one' : toLinearMap 1 = 0

namespace SigmaDerivation

variable {σ : R →ₐ[k] R}

instance : Zero (SigmaDerivation σ) where
  zero :=
    { toLinearMap := 0
      leibniz' := by simp
      map_one' := by simp }

instance : FunLike (SigmaDerivation σ) R R where
  coe δ := δ.toLinearMap
  coe_injective := by
    intro δ ε h
    ext a
    exact congrFun h a

instance : AddMonoidHomClass (SigmaDerivation σ) R R where
  map_add δ := δ.toLinearMap.map_add
  map_zero δ := δ.toLinearMap.map_zero

@[simp]
theorem coe_toLinearMap (δ : SigmaDerivation σ) : ⇑δ.toLinearMap = δ := rfl

@[simp]
theorem coe_zero : ⇑(0 : SigmaDerivation σ) = (0 : R → R) := rfl

/-- The skew Leibniz rule. -/
theorem leibniz (δ : SigmaDerivation σ) (a b : R) :
    δ (a * b) = σ a * δ b + δ a * b :=
  δ.leibniz' a b

/-- A skew derivation sends one to zero. -/
@[simp]
theorem map_one (δ : SigmaDerivation σ) : δ 1 = 0 :=
  δ.map_one'

end SigmaDerivation

/-- The Ore extension `R[X; σ, δ]`, represented by its finitely supported left coefficients. -/
@[ext]
structure OreExtension (σ : R →ₐ[k] R) (δ : SigmaDerivation σ) where
  /-- The finitely supported sequence of left coefficients. -/
  toFinsupp : ℕ →₀ R

namespace OreExtension

variable {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : OreExtension σ δ → ℕ →₀ R) := by
  rintro ⟨p⟩ ⟨q⟩ h
  cases h
  rfl

instance : Zero (OreExtension σ δ) := ⟨⟨0⟩⟩

@[no_expose] instance : Add (OreExtension σ δ) :=
  ⟨fun p q => ⟨p.toFinsupp + q.toFinsupp⟩⟩

instance : SMul ℕ (OreExtension σ δ) :=
  ⟨fun n p => ⟨n • p.toFinsupp⟩⟩

instance : SMul k (OreExtension σ δ) :=
  ⟨fun c p => ⟨c • p.toFinsupp⟩⟩

instance : SMul R (OreExtension σ δ) :=
  ⟨fun a p => ⟨p.toFinsupp.mapRange (a * ·) (mul_zero a)⟩⟩

@[simp] theorem toFinsupp_zero : (0 : OreExtension σ δ).toFinsupp = 0 := rfl

@[simp] theorem ofFinsupp_zero : (⟨0⟩ : OreExtension σ δ) = 0 := rfl

@[simp] theorem toFinsupp_add (p q : OreExtension σ δ) :
    (p + q).toFinsupp = p.toFinsupp + q.toFinsupp := (rfl)

@[simp] theorem toFinsupp_nsmul (p : OreExtension σ δ) (n : ℕ) :
    (n • p).toFinsupp = n • p.toFinsupp := rfl

@[simp] theorem toFinsupp_smul (c : k) (p : OreExtension σ δ) :
    (c • p).toFinsupp = c • p.toFinsupp := rfl

@[simp] theorem toFinsupp_smul_left (a : R) (p : OreExtension σ δ) :
    (a • p).toFinsupp = p.toFinsupp.mapRange (a * ·) (mul_zero a) := rfl

instance instAddCommMonoid : AddCommMonoid (OreExtension σ δ) :=
  Function.Injective.addCommMonoid toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_add toFinsupp_nsmul

instance : Module k (OreExtension σ δ) :=
  Function.Injective.module k
    ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

instance : Module R (OreExtension σ δ) :=
  Function.Injective.module R
    ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul_left

/-- The coefficient of `Xⁿ` in an Ore polynomial. -/
def coeff (p : OreExtension σ δ) (n : ℕ) : R := p.toFinsupp n

private def coeffLinearEquiv : OreExtension σ δ ≃ₗ[k] (ℕ →₀ R) where
  toFun := toFinsupp
  invFun p := ⟨p⟩
  left_inv p := by rcases p; rfl
  right_inv _ := rfl
  map_add' := toFinsupp_add
  map_smul' := toFinsupp_smul

/-- The linear equivalence recording the left coefficients of an Ore polynomial. -/
def leftCoeffLinearEquiv : OreExtension σ δ ≃ₗ[R] (ℕ →₀ R) where
  toFun := toFinsupp
  invFun p := ⟨p⟩
  left_inv p := by rcases p; rfl
  right_inv _ := rfl
  map_add' := toFinsupp_add
  map_smul' := toFinsupp_smul_left

/-- The left monomial basis of an Ore extension. -/
noncomputable def monomialBasis : Module.Basis ℕ R (OreExtension σ δ) :=
  Module.Basis.ofRepr leftCoeffLinearEquiv

/-- The left-coefficient monomial `a Xⁿ`. -/
def monomial (n : ℕ) : R →ₗ[k] OreExtension σ δ where
  toFun a := ⟨Finsupp.single n a⟩
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

@[simp]
theorem toFinsupp_monomial (n : ℕ) (a : R) :
    (monomial (σ := σ) (δ := δ) n a).toFinsupp = Finsupp.single n a := (rfl)

/-- Induction on an Ore polynomial by adjoining one left monomial at a time. -/
@[elab_as_elim]
theorem induction_on {P : OreExtension σ δ → Prop} (p : OreExtension σ δ)
    (zero : P 0)
    (add : ∀ n a p, n ∉ p.toFinsupp.support → a ≠ 0 → P p → P (monomial n a + p)) : P p := by
  rcases p with ⟨p⟩
  induction p using Finsupp.induction with
  | zero => exact zero
  | @single_add n a p hn ha ih => exact add n a ⟨p⟩ hn ha ih

@[simp]
theorem coeff_monomial (m : ℕ) (a : R) (n : ℕ) :
    coeff (monomial (σ := σ) (δ := δ) m a) n = if m = n then a else 0 := by
  by_cases h : m = n
  · subst n
    simp [coeff]
  · simp [coeff, h, Ne.symm h]

theorem monomial_injective (n : ℕ) :
    Function.Injective (monomial (σ := σ) (δ := δ) n) := by
  intro a b h
  simpa using congr_arg (fun p ↦ coeff p n) h

@[simp]
theorem monomialBasis_apply (n : ℕ) :
    monomialBasis (σ := σ) (δ := δ) n = monomial n 1 := by
  -- Expose `Basis.ofRepr` application to compare the two coefficient-sequence wrappers.
  change leftCoeffLinearEquiv.symm (Finsupp.single n 1) = monomial n 1
  rfl

@[simp] theorem coeff_zero (n : ℕ) : coeff (0 : OreExtension σ δ) n = 0 := (rfl)

@[simp] theorem coeff_add (p q : OreExtension σ δ) (n : ℕ) :
    coeff (p + q) n = coeff p n + coeff q n := by simp [coeff]

private def coeffLeft (a : R) : OreExtension σ δ →ₗ[k] OreExtension σ δ where
  toFun p := ⟨p.toFinsupp.mapRange (a * ·) (mul_zero a)⟩
  map_add' p q := by ext n; simp [mul_add]
  map_smul' c p := by ext n; simp

@[simp]
private theorem coeffLeft_monomial (a b : R) (n : ℕ) :
    coeffLeft (σ := σ) (δ := δ) a (monomial n b) = monomial n (a * b) := by
  ext m
  simp [coeffLeft]

private def xOperator : OreExtension σ δ →ₗ[k] OreExtension σ δ where
  __ := (Finsupp.lsum k fun n =>
    (monomial (n + 1)).comp σ.toLinearMap + (monomial n).comp δ.toLinearMap).comp
      coeffLinearEquiv.toLinearMap

@[simp]
private theorem xOperator_monomial (a : R) (n : ℕ) :
    xOperator (σ := σ) (δ := δ) (monomial n a) =
      monomial (n + 1) (σ a) + monomial n (δ a) := by
  -- Expose the `Finsupp.lsum` input so its single-support lemma applies.
  change (Finsupp.lsum k (fun i =>
    (monomial (i + 1)).comp σ.toLinearMap + (monomial i).comp δ.toLinearMap))
      (Finsupp.single n a) = _
  rw [Finsupp.lsum_single]
  rfl

private def coeffLeftLinear : R →ₗ[k] Module.End k (OreExtension σ δ) where
  toFun := coeffLeft
  map_add' a b := by
    ext p n
    simp [coeffLeft, add_mul]
  map_smul' c a := by
    ext p n
    simp [coeffLeft, Algebra.smul_mul_assoc]

private def regularRepresentation : OreExtension σ δ →ₗ[k] Module.End k (OreExtension σ δ) where
  __ := (Finsupp.lsum k fun n =>
    (LinearMap.mul k (Module.End k (OreExtension σ δ))).flip (xOperator ^ n) ∘ₗ
      coeffLeftLinear).comp coeffLinearEquiv.toLinearMap

@[simp]
private theorem regularRepresentation_monomial (a : R) (n : ℕ) :
    regularRepresentation (σ := σ) (δ := δ) (monomial n a) =
      coeffLeft a * xOperator ^ n := by
  -- Expose the `Finsupp.lsum` input so its single-support lemma applies.
  change (Finsupp.lsum k (fun i =>
    (LinearMap.mul k (Module.End k (OreExtension σ δ))).flip (xOperator ^ i) ∘ₗ
      coeffLeftLinear)) (Finsupp.single n a) = _
  rw [Finsupp.lsum_single]
  rfl

private def mul (p q : OreExtension σ δ) : OreExtension σ δ := regularRepresentation p q

@[no_expose] instance : Mul (OreExtension σ δ) := ⟨mul⟩

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (OreExtension σ δ) where
  -- These goals expose private multiplication only to invoke linearity of its representation.
  left_distrib p q r := by
    change regularRepresentation p (q + r) = _
    exact map_add _ _ _
  right_distrib p q r := by
    change regularRepresentation (p + q) r = _
    rw [map_add]
    rfl
  zero_mul p := by
    change regularRepresentation 0 p = 0
    rw [map_zero]
    rfl
  mul_zero p := by
    change regularRepresentation p 0 = 0
    exact map_zero _

@[simp]
private theorem monomial_mul_apply (a : R) (n : ℕ) (p : OreExtension σ δ) :
    monomial n a * p = coeffLeft a ((xOperator ^ n) p) := by
  -- Expose private multiplication so the monomial representation lemma applies.
  rw [show monomial n a * p = regularRepresentation (monomial n a) p from rfl,
    regularRepresentation_monomial]
  rfl

/-- The constant Ore polynomial. -/
def C : R →ₗ[k] OreExtension σ δ := monomial 0

/-- The Ore variable. -/
def X : OreExtension σ δ := monomial 1 1

@[simp]
theorem monomial_zero_left (a : R) : monomial (σ := σ) (δ := δ) 0 a = C a := (rfl)

theorem X_eq_monomial : X (σ := σ) (δ := δ) = monomial 1 1 := (rfl)

private theorem xOperator_coeffLeft (a : R) :
    xOperator (σ := σ) (δ := δ) * coeffLeft a =
      coeffLeft (σ a) * xOperator + coeffLeft (δ a) := by
  apply LinearMap.ext
  intro p
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      simp only [map_add, Module.End.mul_apply, LinearMap.add_apply]
      have ih' : xOperator (coeffLeft a p) =
          coeffLeft (σ a) (xOperator p) + coeffLeft (δ a) p := by
        simpa only [Module.End.mul_apply, LinearMap.add_apply] using ih
      rw [ih']
      congr 1
      simp only [coeffLeft_monomial, xOperator_monomial, map_add]
      rw [SigmaDerivation.leibniz]
      simp only [map_mul]
      ext m
      simp [add_assoc]

private theorem xOperator_regularRepresentation (p : OreExtension σ δ) :
    xOperator * regularRepresentation p = regularRepresentation (xOperator p) := by
  rcases p with ⟨p⟩
  induction p using Finsupp.induction with
  | zero => rw [ofFinsupp_zero, map_zero, mul_zero, map_zero, map_zero]
  | @single_add n a p hn ha ih =>
      -- Identify the structure wrapper with the corresponding monomial sum.
      rw [show (⟨Finsupp.single n a + p⟩ : OreExtension σ δ) =
        monomial n a + ⟨p⟩ from rfl, map_add, map_add, mul_add, ih]
      simp only [regularRepresentation_monomial, xOperator_monomial, map_add]
      congr 1
      rw [← mul_assoc, xOperator_coeffLeft, add_mul, mul_assoc, ← pow_succ']

private theorem xOperator_pow_regularRepresentation (n : ℕ) (p : OreExtension σ δ) :
    xOperator ^ n * regularRepresentation p = regularRepresentation ((xOperator ^ n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, xOperator_regularRepresentation]
      rfl

private theorem coeffLeft_mul (a b : R) :
    coeffLeft (σ := σ) (δ := δ) (a * b) = coeffLeft a * coeffLeft b := by
  apply LinearMap.ext
  intro p
  ext n
  simp [coeffLeft, Module.End.mul_apply, mul_assoc]

private theorem regularRepresentation_coeffLeft (a : R) (p : OreExtension σ δ) :
    regularRepresentation (coeffLeft a p) = coeffLeft a * regularRepresentation p := by
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      rw [map_add, map_add, map_add, ih, coeffLeft_monomial,
        regularRepresentation_monomial, regularRepresentation_monomial]
      rw [coeffLeft_mul, mul_assoc, mul_add]

private theorem regularRepresentation_mul (p q : OreExtension σ δ) :
    regularRepresentation (p * q) = regularRepresentation p * regularRepresentation q := by
  rcases p with ⟨p⟩
  induction p using Finsupp.induction with
  | zero =>
      rw [ofFinsupp_zero, zero_mul, map_zero]
      exact (zero_mul _).symm
  | @single_add n a p hn ha ih =>
      -- Identify the structure wrapper with the corresponding monomial sum.
      rw [show (⟨Finsupp.single n a + p⟩ : OreExtension σ δ) =
        monomial n a + ⟨p⟩ from rfl, add_mul, map_add, map_add, add_mul, ih]
      simp only [monomial_mul_apply, regularRepresentation_monomial]
      rw [regularRepresentation_coeffLeft, ← xOperator_pow_regularRepresentation, mul_assoc]

private theorem xOperator_pow_C_one (n : ℕ) :
    (xOperator (σ := σ) (δ := δ) ^ n) (C 1) = monomial n 1 := by
  induction n with
  | zero => simp [C, monomial]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, xOperator_monomial]
      simp

private theorem regularRepresentation_apply_C_one (p : OreExtension σ δ) :
    regularRepresentation p (C 1) = p := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [map_add, LinearMap.add_apply, ih, regularRepresentation_monomial,
        Module.End.mul_apply, xOperator_pow_C_one, coeffLeft_monomial]
      simp

private theorem regularRepresentation_injective :
    Function.Injective (regularRepresentation (σ := σ) (δ := δ)) := by
  intro p q h
  rw [← regularRepresentation_apply_C_one p, ← regularRepresentation_apply_C_one q, h]

instance instOne : One (OreExtension σ δ) := ⟨C 1⟩

instance instNatCast : NatCast (OreExtension σ δ) := ⟨Nat.unaryCast⟩

@[simp] theorem toFinsupp_one : (1 : OreExtension σ δ).toFinsupp = Finsupp.single 0 1 := (rfl)

instance instNonUnitalSemiring : NonUnitalSemiring (OreExtension σ δ) where
  mul_assoc p q r := by
    apply regularRepresentation_injective
    simp only [regularRepresentation_mul, mul_assoc]

instance instNonAssocSemiring : NonAssocSemiring (OreExtension σ δ) where
  -- Expose private multiplication to use faithfulness at `C 1` and coefficientwise action.
  one_mul p := by
    change regularRepresentation (C 1) p = p
    rw [← monomial_zero_left, regularRepresentation_monomial]
    change coeffLeft 1 p = p
    ext n
    simp [coeffLeft]
  mul_one p := by
    change regularRepresentation p (C 1) = p
    exact regularRepresentation_apply_C_one p

instance : Semiring (OreExtension σ δ) where
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance : Algebra k (OreExtension σ δ) :=
  Algebra.ofModule
    (fun c p q => by
      -- Expose private multiplication to use linearity in its left input.
      change regularRepresentation (c • p) q = c • regularRepresentation p q
      rw [map_smul]
      rfl)
    (fun c p q => by
      -- Expose private multiplication to use linearity in its right input.
      change regularRepresentation p (c • q) = c • regularRepresentation p q
      exact map_smul (regularRepresentation p) c q)

@[simp]
theorem algebraMap_apply (c : k) :
    algebraMap k (OreExtension σ δ) c = C (algebraMap k R c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext n
  simp only [toFinsupp_smul, toFinsupp_one, Finsupp.smul_single, ← monomial_zero_left,
    toFinsupp_monomial]
  have hc : c • (1 : R) = algebraMap k R c := by simp [Algebra.smul_def]
  rw [hc]

@[simp]
theorem C_one : C (σ := σ) (δ := δ) 1 = 1 := rfl

@[simp]
theorem C_mul (a b : R) : C (σ := σ) (δ := δ) (a * b) = C a * C b := by
  -- Expose private multiplication so the constant regular-representation formula applies.
  change monomial 0 (a * b) = regularRepresentation (monomial 0 a) (monomial 0 b)
  rw [regularRepresentation_monomial]
  rw [pow_zero, mul_one, coeffLeft_monomial]

/-- Constants embed into the Ore extension as a ring homomorphism. -/
def CRingHom : R →+* OreExtension σ δ where
  toFun := C
  map_zero' := map_zero C
  map_one' := C_one
  map_add' := map_add C
  map_mul' := C_mul

@[simp]
theorem CRingHom_eq_C (a : R) : CRingHom (σ := σ) (δ := δ) a = C a := (rfl)

theorem CRingHom_injective : Function.Injective (CRingHom (σ := σ) (δ := δ)) :=
  monomial_injective 0

@[simp]
theorem coeff_C (a : R) (n : ℕ) : coeff (C (σ := σ) (δ := δ) a) n = if n = 0 then a else 0 := by
  rw [← monomial_zero_left, coeff_monomial]
  simp only [eq_comm]

@[simp]
theorem coeff_X (n : ℕ) : coeff (X (σ := σ) (δ := δ)) n = if n = 1 then 1 else 0 := by
  rw [X_eq_monomial, coeff_monomial]
  simp only [eq_comm]

/-- The defining Ore commutation relation. -/
theorem X_mul_C (a : R) :
    X (σ := σ) (δ := δ) * C a = C (σ a) * X + C (δ a) := by
  rw [X_eq_monomial, ← monomial_zero_left, monomial_mul_apply, pow_one, xOperator_monomial,
    map_add, coeffLeft_monomial, coeffLeft_monomial, ← monomial_zero_left,
    ← monomial_zero_left]
  rw [monomial_mul_apply, pow_zero, Module.End.one_apply, coeffLeft_monomial]
  simp

@[simp]
theorem X_pow (n : ℕ) : X (σ := σ) (δ := δ) ^ n = monomial n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', ih, X_eq_monomial, monomial_mul_apply, pow_one,
        xOperator_monomial]
      simp

@[simp]
theorem C_mul_monomial (a b : R) (n : ℕ) :
    C (σ := σ) (δ := δ) a * monomial n b = monomial n (a * b) := by
  rw [← monomial_zero_left, monomial_mul_apply, pow_zero, Module.End.one_apply,
    coeffLeft_monomial]

section UniversalProperty

variable {S : Type*} [Semiring S]

/-- Evaluate an Ore polynomial at a coefficient homomorphism `f` and an element `x`, without yet
assuming that `x` satisfies the Ore commutation relation. -/
def eval (f : R →+* S) (x : S) : OreExtension σ δ →+ S :=
  (Finsupp.liftAddHom fun n => (AddMonoidHom.mulRight (x ^ n)).comp f.toAddMonoidHom).comp
    leftCoeffLinearEquiv.toLinearMap.toAddMonoidHom

@[simp]
theorem eval_monomial (f : R →+* S) (x : S) (n : ℕ) (a : R) :
    eval (σ := σ) (δ := δ) f x (monomial n a) = f a * x ^ n := by
  simp [eval, leftCoeffLinearEquiv, monomial]

private theorem eval_coeffLeft (f : R →+* S) (x : S) (a : R) (p : OreExtension σ δ) :
    eval f x (coeffLeft a p) = f a * eval f x p := by
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      rw [map_add, map_add, map_add, ih, coeffLeft_monomial,
        eval_monomial, eval_monomial, map_mul, mul_add, mul_assoc]

private theorem eval_xOperator (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (p : OreExtension σ δ) :
    eval f x (xOperator p) = x * eval f x p := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [map_add, xOperator_monomial]
      simp only [(eval f x).map_add, eval_monomial, ih]
      rw [mul_add]
      congr 1
      rw [← mul_assoc, h, add_mul, pow_succ', mul_assoc]

private theorem eval_xOperator_pow (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (n : ℕ) (p : OreExtension σ δ) :
    eval f x ((xOperator ^ n) p) = x ^ n * eval f x p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, eval_xOperator f x h, ih, pow_succ', mul_assoc]

/-- Evaluation is multiplicative when the chosen image of `X` satisfies the Ore relation. -/
theorem eval_mul (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (p q : OreExtension σ δ) :
    eval f x (p * q) = eval f x p * eval f x q := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [add_mul, (eval f x).map_add, (eval f x).map_add, add_mul, ih, monomial_mul_apply,
        eval_coeffLeft, eval_xOperator_pow f x h, eval_monomial, mul_assoc]

/-- The universal map from an Ore extension. The chosen image `x` of the variable must satisfy
the defining Ore commutation relation with every coefficient. -/
def lift (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : OreExtension σ δ →+* S where
  __ := eval f x
  map_one' := by
    -- Expose the additive-map carrier of `eval` to use its monomial formula.
    change eval f x (monomial 0 1) = 1
    rw [eval_monomial]
    simp
  map_mul' := eval_mul f x h

@[simp]
theorem lift_C (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (a : R) :
    lift f x h (C a) = f a := by
  -- Expose the ring-hom carrier, which is definitionally the additive evaluation map.
  change eval f x (C a) = f a
  rw [← monomial_zero_left, eval_monomial]
  simp

@[simp]
theorem lift_X (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : lift f x h X = x := by
  -- Expose the ring-hom carrier, which is definitionally the additive evaluation map.
  change eval f x X = x
  rw [X_eq_monomial, eval_monomial]
  simp

/-- A ring homomorphism from an Ore extension is determined by its values on the coefficients
and the Ore variable. -/
theorem ringHom_ext {f g : OreExtension σ δ →+* S}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) : f = g := by
  apply DFunLike.ext _ _
  intro p
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      have hmonomial : monomial (σ := σ) (δ := δ) n a =
          C (σ := σ) (δ := δ) a * monomial n 1 := by simp
      rw [map_add, map_add, ih, hmonomial, map_mul, map_mul, ← X_pow, map_pow, map_pow,
        hC, hX]

end UniversalProperty

end OreExtension

end TauCeti
