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
* `TauCeti.OreExtension.monomialBasis`: the left monomial basis `Xⁿ` over `R`.
* `TauCeti.OreExtension.CRingHom` and `TauCeti.OreExtension.CAlgHom`: the inclusion of the
  coefficients as a ring and as a `k`-algebra homomorphism.
* `TauCeti.OreExtension.eval₂`: evaluation along a coefficient homomorphism at a chosen element.
* `TauCeti.OreExtension.lift` and `TauCeti.OreExtension.liftAlgHom`: the universal ring and
  `k`-algebra homomorphisms out of the Ore extension.

## Main statements

* `TauCeti.OreExtension.X_mul_C`: the Ore commutation relation.
* `TauCeti.OreExtension.coeff_X_mul_zero` and `coeff_X_mul_succ`: the coefficient recursion
  for left multiplication by the variable.
* `TauCeti.OreExtension.sum_monomial_eq`: the left-coefficient expansion.
* `TauCeti.OreExtension.lift_C`, `TauCeti.OreExtension.lift_X`, and
  `TauCeti.OreExtension.ringHom_ext`: the universal property for ring homomorphisms.
* `TauCeti.OreExtension.liftAlgHom_C`, `TauCeti.OreExtension.liftAlgHom_X`, and
  `TauCeti.OreExtension.algHom_ext`: the universal property for `k`-algebra homomorphisms.

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
    cases δ
    cases ε
    congr
    exact LinearMap.ext (congrFun h)

instance : LinearMapClass (SigmaDerivation σ) k R R where
  map_add δ := δ.toLinearMap.map_add
  map_smulₛₗ δ := δ.toLinearMap.map_smul

/-- Two skew derivations are equal when they agree at every point. -/
@[ext]
theorem ext {δ ε : SigmaDerivation σ} (h : ∀ a, δ a = ε a) : δ = ε :=
  DFunLike.ext _ _ h

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
structure OreExtension (σ : R →ₐ[k] R) (δ : SigmaDerivation σ) where ofFinsupp ::
  /-- The finitely supported sequence of left coefficients. -/
  toFinsupp : ℕ →₀ R

namespace OreExtension

variable {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : OreExtension σ δ → ℕ →₀ R) := by
  rintro ⟨p⟩ ⟨q⟩ h
  cases h
  rfl

/-- The coefficient of `Xⁿ` in an Ore polynomial. -/
def coeff (p : OreExtension σ δ) (n : ℕ) : R := p.toFinsupp n

theorem coeff_def (p : OreExtension σ δ) (n : ℕ) : coeff p n = p.toFinsupp n := (rfl)

/-- Ore polynomials are equal when all their left coefficients agree. -/
@[ext]
theorem ext {p q : OreExtension σ δ} (h : ∀ n, coeff p n = coeff q n) : p = q :=
  toFinsupp_injective (Finsupp.ext h)

instance : Zero (OreExtension σ δ) := ⟨⟨0⟩⟩

@[no_expose] instance : Add (OreExtension σ δ) :=
  ⟨fun p q => ⟨p.toFinsupp + q.toFinsupp⟩⟩

instance instNSMul : SMul ℕ (OreExtension σ δ) :=
  ⟨fun n p => ⟨n • p.toFinsupp⟩⟩

instance smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S (OreExtension σ δ) where
  smul s p := ⟨s • p.toFinsupp⟩
  smul_zero s := congrArg ofFinsupp (smul_zero s)

@[simp] theorem toFinsupp_zero : (0 : OreExtension σ δ).toFinsupp = 0 := rfl

@[simp] theorem ofFinsupp_zero : (⟨0⟩ : OreExtension σ δ) = 0 := rfl

@[simp] theorem toFinsupp_add (p q : OreExtension σ δ) :
    (p + q).toFinsupp = p.toFinsupp + q.toFinsupp := (rfl)

@[simp] theorem toFinsupp_nsmul (p : OreExtension σ δ) (n : ℕ) :
    (n • p).toFinsupp = n • p.toFinsupp := rfl

@[simp] theorem toFinsupp_smul {S : Type*} [SMulZeroClass S R] (s : S) (p : OreExtension σ δ) :
    (s • p).toFinsupp = s • p.toFinsupp := rfl

instance instAddCommMonoid : AddCommMonoid (OreExtension σ δ) :=
  Function.Injective.addCommMonoid toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_add toFinsupp_nsmul

instance module {S : Type*} [Semiring S] [Module S R] : Module S (OreExtension σ δ) :=
  Function.Injective.module S
    ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_injective toFinsupp_smul

instance smulCommClass {S₁ S₂ : Type*} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [SMulCommClass S₁ S₂ R] : SMulCommClass S₁ S₂ (OreExtension σ δ) :=
  ⟨fun s₁ s₂ p => toFinsupp_injective (smul_comm s₁ s₂ p.toFinsupp)⟩

instance isScalarTower {S₁ S₂ : Type*} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ (OreExtension σ δ) :=
  ⟨fun s₁ s₂ p => toFinsupp_injective (smul_assoc s₁ s₂ p.toFinsupp)⟩

/-- The linear equivalence recording the left coefficients of an Ore polynomial. -/
def leftCoeffLinearEquiv : OreExtension σ δ ≃ₗ[R] (ℕ →₀ R) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := toFinsupp_add
  map_smul' := toFinsupp_smul

@[simp]
theorem leftCoeffLinearEquiv_apply (p : OreExtension σ δ) :
    leftCoeffLinearEquiv p = p.toFinsupp := (rfl)

@[simp]
theorem leftCoeffLinearEquiv_symm_apply (f : ℕ →₀ R) :
    (leftCoeffLinearEquiv (σ := σ) (δ := δ)).symm f = ⟨f⟩ := (rfl)

instance [Nontrivial R] : Nontrivial (OreExtension σ δ) := leftCoeffLinearEquiv.nontrivial

/-- The left monomial basis of an Ore extension. -/
noncomputable def monomialBasis : Module.Basis ℕ R (OreExtension σ δ) :=
  Module.Basis.ofRepr leftCoeffLinearEquiv

@[simp]
theorem monomialBasis_repr (p : OreExtension σ δ) : monomialBasis.repr p = p.toFinsupp := (rfl)

/-- The left-coefficient monomial `a Xⁿ`. -/
def monomial (n : ℕ) : R →ₗ[k] OreExtension σ δ where
  toFun a := ⟨Finsupp.single n a⟩
  map_add' a b := by ext; simp [coeff_def]
  map_smul' c a := by ext; simp [coeff_def]

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
    simp [coeff_def]
  · simp [coeff_def, h, Ne.symm h]

theorem monomial_injective (n : ℕ) :
    Function.Injective (monomial (σ := σ) (δ := δ) n) := by
  intro a b h
  simpa using congr_arg (fun p ↦ coeff p n) h

@[simp]
theorem monomialBasis_apply (n : ℕ) :
    monomialBasis (σ := σ) (δ := δ) n = monomial n 1 := by
  rw [Module.Basis.apply_eq_iff, monomialBasis_repr, toFinsupp_monomial]

@[simp] theorem coeff_zero (n : ℕ) : coeff (0 : OreExtension σ δ) n = 0 := (rfl)

@[simp] theorem coeff_add (p q : OreExtension σ δ) (n : ℕ) :
    coeff (p + q) n = coeff p n + coeff q n := by simp [coeff_def]

@[simp]
theorem coeff_smul {S : Type*} [SMulZeroClass S R] (s : S) (p : OreExtension σ δ) (n : ℕ) :
    coeff (s • p) n = s • coeff p n := (rfl)

@[simp]
theorem smul_monomial {S : Type*} [SMulZeroClass S R] (s : S) (n : ℕ) (a : R) :
    s • monomial (σ := σ) (δ := δ) n a = monomial n (s • a) := by
  ext m
  by_cases h : n = m <;> simp [h]

/-- Coefficients commute with finite sums. -/
@[simp]
theorem finsetSum_coeff {ι : Type*} (s : Finset ι) (p : ι → OreExtension σ δ) (n : ℕ) :
    coeff (∑ i ∈ s, p i) n = ∑ i ∈ s, coeff (p i) n := by
  simp only [coeff_def, ← leftCoeffLinearEquiv_apply, map_sum, Finset.sum_apply']

/-- Every Ore polynomial is the sum of its left-coefficient monomials. -/
theorem sum_monomial_eq (p : OreExtension σ δ) :
    ∑ n ∈ p.toFinsupp.support, monomial n (coeff p n) = p := by
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, coeff_def, smul_monomial, smul_eq_mul]
    using (monomialBasis (σ := σ) (δ := δ)).linearCombination_repr p

private def xOperator : OreExtension σ δ →ₗ[k] OreExtension σ δ :=
  (Finsupp.lsum k fun n =>
    (monomial (n + 1)).comp σ.toLinearMap + (monomial n).comp δ.toLinearMap).comp
      (leftCoeffLinearEquiv.toLinearMap.restrictScalars k)

@[simp]
private theorem xOperator_monomial (a : R) (n : ℕ) :
    xOperator (σ := σ) (δ := δ) (monomial n a) =
      monomial (n + 1) (σ a) + monomial n (δ a) := by
  simp only [xOperator, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, leftCoeffLinearEquiv_apply, toFinsupp_monomial, Finsupp.lsum_single,
    LinearMap.add_apply, AlgHom.toLinearMap_apply, SigmaDerivation.coe_toLinearMap]

private def regularRepresentation : OreExtension σ δ →ₗ[k] Module.End k (OreExtension σ δ) :=
  (Finsupp.lsum k fun n =>
    (LinearMap.mul k (Module.End k (OreExtension σ δ))).flip (xOperator ^ n) ∘ₗ
      (Algebra.lsmul k k (OreExtension σ δ)).toLinearMap).comp
    (leftCoeffLinearEquiv.toLinearMap.restrictScalars k)

@[simp]
private theorem regularRepresentation_monomial (a : R) (n : ℕ) :
    regularRepresentation (σ := σ) (δ := δ) (monomial n a) =
      Algebra.lsmul k k (OreExtension σ δ) a * xOperator ^ n := by
  simp only [regularRepresentation, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, leftCoeffLinearEquiv_apply, toFinsupp_monomial, Finsupp.lsum_single,
    LinearMap.flip_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]

@[no_expose] instance : Mul (OreExtension σ δ) := ⟨fun p q => regularRepresentation p q⟩

private theorem mul_def (p q : OreExtension σ δ) : p * q = regularRepresentation p q := rfl

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (OreExtension σ δ) where
  left_distrib p q r := by simp only [mul_def, map_add]
  right_distrib p q r := by simp only [mul_def, map_add, LinearMap.add_apply]
  zero_mul p := by simp only [mul_def, map_zero, LinearMap.zero_apply]
  mul_zero p := by simp only [mul_def, map_zero]

@[simp]
private theorem monomial_mul_apply (a : R) (n : ℕ) (p : OreExtension σ δ) :
    monomial n a * p = a • (xOperator ^ n) p := by
  rw [mul_def, regularRepresentation_monomial, Module.End.mul_apply, Algebra.lsmul_apply]

/-- The constant Ore polynomial. -/
def C : R →ₗ[k] OreExtension σ δ := monomial 0

/-- The Ore variable. -/
def X : OreExtension σ δ := monomial 1 1

@[simp]
theorem monomial_zero_left (a : R) : monomial (σ := σ) (δ := δ) 0 a = C a := (rfl)

theorem X_eq_monomial : X (σ := σ) (δ := δ) = monomial 1 1 := (rfl)

private theorem xOperator_lsmul (a : R) :
    xOperator (σ := σ) (δ := δ) * Algebra.lsmul k k (OreExtension σ δ) a =
      Algebra.lsmul k k _ (σ a) * xOperator + Algebra.lsmul k k _ (δ a) := by
  apply LinearMap.ext
  intro p
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      simp only [map_add, Module.End.mul_apply, LinearMap.add_apply, Algebra.lsmul_apply] at ih ⊢
      rw [ih]
      congr 1
      simp only [smul_monomial, xOperator_monomial, smul_add, smul_eq_mul,
        SigmaDerivation.leibniz, map_mul]
      ext m
      simp [add_assoc]

private theorem xOperator_regularRepresentation (p : OreExtension σ δ) :
    xOperator * regularRepresentation p = regularRepresentation (xOperator p) := by
  induction p using induction_on with
  | zero => rw [map_zero, mul_zero, map_zero, map_zero]
  | add n a p hn ha ih =>
      rw [map_add, map_add, mul_add, ih]
      simp only [regularRepresentation_monomial, xOperator_monomial, map_add]
      congr 1
      rw [← mul_assoc, xOperator_lsmul, add_mul, mul_assoc, ← pow_succ']

private theorem xOperator_pow_regularRepresentation (n : ℕ) (p : OreExtension σ δ) :
    xOperator ^ n * regularRepresentation p = regularRepresentation ((xOperator ^ n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, xOperator_regularRepresentation, Module.End.mul_apply]

private theorem regularRepresentation_smul (a : R) (p : OreExtension σ δ) :
    regularRepresentation (a • p) = Algebra.lsmul k k _ a * regularRepresentation p := by
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      rw [smul_add, map_add, map_add, ih, smul_monomial, smul_eq_mul,
        regularRepresentation_monomial, regularRepresentation_monomial, map_mul, mul_assoc,
        mul_add]

private theorem regularRepresentation_mul (p q : OreExtension σ δ) :
    regularRepresentation (p * q) = regularRepresentation p * regularRepresentation q := by
  induction p using induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add n a p hn ha ih =>
      rw [add_mul, map_add, map_add, add_mul, ih, monomial_mul_apply,
        regularRepresentation_smul, ← xOperator_pow_regularRepresentation,
        regularRepresentation_monomial, mul_assoc]

private theorem xOperator_pow_C_one (n : ℕ) :
    (xOperator (σ := σ) (δ := δ) ^ n) (C 1) = monomial n 1 := by
  induction n with
  | zero => rw [pow_zero, Module.End.one_apply, monomial_zero_left]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, xOperator_monomial]
      simp

private theorem regularRepresentation_apply_C_one (p : OreExtension σ δ) :
    regularRepresentation p (C 1) = p := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [map_add, LinearMap.add_apply, ih, regularRepresentation_monomial,
        Module.End.mul_apply, xOperator_pow_C_one, Algebra.lsmul_apply, smul_monomial,
        smul_eq_mul, mul_one]

private theorem regularRepresentation_injective :
    Function.Injective (regularRepresentation (σ := σ) (δ := δ)) := by
  intro p q h
  rw [← regularRepresentation_apply_C_one p, ← regularRepresentation_apply_C_one q, h]

instance instOne : One (OreExtension σ δ) := ⟨C 1⟩

instance instNatCast : NatCast (OreExtension σ δ) := ⟨Nat.unaryCast⟩

private theorem one_def : (1 : OreExtension σ δ) = monomial 0 1 := rfl

@[simp] theorem toFinsupp_one : (1 : OreExtension σ δ).toFinsupp = Finsupp.single 0 1 := (rfl)

instance instNonUnitalSemiring : NonUnitalSemiring (OreExtension σ δ) where
  mul_assoc p q r := by
    apply regularRepresentation_injective
    simp only [regularRepresentation_mul, mul_assoc]

instance instNonAssocSemiring : NonAssocSemiring (OreExtension σ δ) where
  one_mul p := by
    rw [one_def, monomial_mul_apply, pow_zero, Module.End.one_apply, one_smul]
  mul_one p := by
    rw [mul_def]
    exact regularRepresentation_apply_C_one p

instance : Semiring (OreExtension σ δ) where
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance : Algebra k (OreExtension σ δ) :=
  Algebra.ofModule
    (fun c p q => by rw [mul_def, mul_def, map_smul, LinearMap.smul_apply])
    (fun c p q => by rw [mul_def, mul_def, map_smul])

@[simp]
theorem C_one : C (σ := σ) (δ := δ) 1 = 1 := rfl

@[simp]
theorem algebraMap_apply (c : k) :
    algebraMap k (OreExtension σ δ) c = C (algebraMap k R c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← C_one, ← map_smul]

@[simp]
theorem C_mul_monomial (a b : R) (n : ℕ) :
    C (σ := σ) (δ := δ) a * monomial n b = monomial n (a * b) := by
  rw [← monomial_zero_left, monomial_mul_apply, pow_zero, Module.End.one_apply, smul_monomial,
    smul_eq_mul]

@[simp]
theorem C_mul (a b : R) : C (σ := σ) (δ := δ) (a * b) = C a * C b := by
  rw [← monomial_zero_left b, C_mul_monomial, monomial_zero_left]

theorem smul_eq_C_mul (a : R) (p : OreExtension σ δ) : a • p = C a * p := by
  rw [← monomial_zero_left, monomial_mul_apply, pow_zero, Module.End.one_apply]

@[simp]
theorem coeff_C_mul (a : R) (p : OreExtension σ δ) (n : ℕ) :
    coeff (C a * p) n = a * coeff p n := by
  rw [← smul_eq_C_mul, coeff_smul, smul_eq_mul]

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

/-- Constants embed into the Ore extension as a `k`-algebra homomorphism. -/
def CAlgHom : R →ₐ[k] OreExtension σ δ where
  __ := CRingHom
  commutes' c := (algebraMap_apply c).symm

@[simp]
theorem CAlgHom_eq_C (a : R) : CAlgHom (σ := σ) (δ := δ) a = C a := (rfl)

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
  simp [X_eq_monomial, ← monomial_zero_left]

theorem X_pow_eq_monomial (n : ℕ) : X (σ := σ) (δ := δ) ^ n = monomial n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', ih, X_eq_monomial, monomial_mul_apply, pow_one, xOperator_monomial]
      simp

@[simp]
theorem C_mul_X_pow_eq_monomial (a : R) (n : ℕ) :
    C (σ := σ) (δ := δ) a * X ^ n = monomial n a := by
  rw [X_pow_eq_monomial, C_mul_monomial, mul_one]

/-- Induction on an Ore polynomial through the constants, the variable, sums and products. -/
@[elab_as_elim]
theorem induction_on_mul {P : OreExtension σ δ → Prop} (p : OreExtension σ δ)
    (C : ∀ a, P (C a)) (X : P X) (add : ∀ p q, P p → P q → P (p + q))
    (mul : ∀ p q, P p → P q → P (p * q)) : P p := by
  have hpow (n : ℕ) : P (OreExtension.X ^ n) := by
    induction n with
    | zero => simpa using C 1
    | succ n ih => simpa [pow_succ] using mul _ _ ih X
  induction p using induction_on with
  | zero => simpa using C 0
  | add n a p _ _ ih => simpa using add _ _ (mul _ _ (C a) (hpow n)) ih

/-- Multiplication by the variable has the skew-derivation coefficient recursion. -/
@[simp]
theorem X_mul_monomial (n : ℕ) (a : R) :
    X (σ := σ) (δ := δ) * monomial n a =
      monomial (n + 1) (σ a) + monomial n (δ a) := by
  simp [X_eq_monomial]

/-- The constant coefficient of left multiplication by the variable. -/
@[simp]
theorem coeff_X_mul_zero (p : OreExtension σ δ) : coeff (X * p) 0 = δ (coeff p 0) := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
    simp only [mul_add, coeff_add, X_mul_monomial, map_add, ih]
    by_cases h : n = 0 <;> simp [coeff_monomial, h]

/-- The positive-degree coefficients of left multiplication by the variable. -/
@[simp]
theorem coeff_X_mul_succ (p : OreExtension σ δ) (n : ℕ) :
    coeff (X * p) (n + 1) = σ (coeff p n) + δ (coeff p (n + 1)) := by
  induction p using induction_on with
  | zero => simp
  | add m a p hm ha ih =>
    simp only [mul_add, coeff_add, X_mul_monomial, map_add, ih, coeff_monomial]
    by_cases h : m = n
    · subst m
      simp [add_comm, add_left_comm]
    · by_cases h' : m = n + 1
      · subst m
        simp [add_comm, add_left_comm]
      · simp [h, h']

section UniversalProperty

variable {S : Type*} [Semiring S]

/-- Evaluate an Ore polynomial along a coefficient homomorphism `f` at an element `x`, without
yet assuming that `x` satisfies the Ore commutation relation. -/
def eval₂ (f : R →+* S) (x : S) : OreExtension σ δ →+ S :=
  (Finsupp.liftAddHom fun n => (AddMonoidHom.mulRight (x ^ n)).comp f.toAddMonoidHom).comp
    leftCoeffLinearEquiv.toLinearMap.toAddMonoidHom

@[simp]
theorem eval₂_monomial (f : R →+* S) (x : S) (n : ℕ) (a : R) :
    eval₂ (σ := σ) (δ := δ) f x (monomial n a) = f a * x ^ n := by
  simp [eval₂]

private theorem eval₂_smul (f : R →+* S) (x : S) (a : R) (p : OreExtension σ δ) :
    eval₂ f x (a • p) = f a * eval₂ f x p := by
  induction p using induction_on with
  | zero => simp
  | add n b p hn hb ih =>
      rw [smul_add, map_add, map_add, ih, smul_monomial, smul_eq_mul,
        eval₂_monomial, eval₂_monomial, map_mul, mul_add, mul_assoc]

private theorem eval₂_xOperator (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (p : OreExtension σ δ) :
    eval₂ f x (xOperator p) = x * eval₂ f x p := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [map_add, xOperator_monomial]
      simp only [map_add, eval₂_monomial, ih]
      rw [mul_add]
      congr 1
      rw [← mul_assoc, h, add_mul, pow_succ', mul_assoc]

private theorem eval₂_xOperator_pow (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (n : ℕ) (p : OreExtension σ δ) :
    eval₂ f x ((xOperator ^ n) p) = x ^ n * eval₂ f x p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, eval₂_xOperator f x h, ih, pow_succ', mul_assoc]

/-- Evaluation is multiplicative when the chosen image of `X` satisfies the Ore relation. -/
theorem eval₂_mul (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (p q : OreExtension σ δ) :
    eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := by
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [add_mul, map_add, map_add, add_mul, ih, monomial_mul_apply,
        eval₂_smul, eval₂_xOperator_pow f x h, eval₂_monomial, mul_assoc]

/-- The universal map from an Ore extension. The chosen image `x` of the variable must satisfy
the defining Ore commutation relation with every coefficient. -/
def lift (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : OreExtension σ δ →+* S where
  __ := eval₂ f x
  map_one' := by
    rw [AddMonoidHom.toFun_eq_coe, ← C_one, ← monomial_zero_left, eval₂_monomial]
    simp
  map_mul' := eval₂_mul f x h

theorem lift_apply (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (p : OreExtension σ δ) :
    lift f x h p = eval₂ f x p := (rfl)

@[simp]
theorem lift_C (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (a : R) :
    lift f x h (C a) = f a := by
  rw [lift_apply, ← monomial_zero_left, eval₂_monomial, pow_zero, mul_one]

@[simp]
theorem lift_X (f : R →+* S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : lift f x h X = x := by
  rw [lift_apply, X_eq_monomial, eval₂_monomial, map_one, one_mul, pow_one]

/-- A ring homomorphism from an Ore extension is determined by its values on the coefficients
and the Ore variable. -/
theorem ringHom_ext {f g : OreExtension σ δ →+* S}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) : f = g := by
  apply DFunLike.ext _ _
  intro p
  induction p using induction_on with
  | zero => simp
  | add n a p hn ha ih =>
      rw [map_add, map_add, ih, ← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
        hC, hX]

variable [Algebra k S]

/-- The universal `k`-algebra map from an Ore extension. The chosen image `x` of the variable
must satisfy the defining Ore commutation relation with every coefficient. -/
def liftAlgHom (f : R →ₐ[k] S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : OreExtension σ δ →ₐ[k] S where
  __ := lift (f : R →+* S) x h
  commutes' c :=
    (congrArg (lift (f : R →+* S) x h) (algebraMap_apply c)).trans
      ((lift_C (f : R →+* S) x h _).trans (f.commutes c))

@[simp]
theorem liftAlgHom_C (f : R →ₐ[k] S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) (a : R) :
    liftAlgHom f x h (C a) = f a :=
  lift_C (f : R →+* S) x h a

@[simp]
theorem liftAlgHom_X (f : R →ₐ[k] S) (x : S)
    (h : ∀ a, x * f a = f (σ a) * x + f (δ a)) : liftAlgHom f x h X = x :=
  lift_X (f : R →+* S) x h

/-- A `k`-algebra homomorphism from an Ore extension is determined by its values on the
coefficients and the Ore variable. -/
theorem algHom_ext {f g : OreExtension σ δ →ₐ[k] S}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) : f = g :=
  AlgHom.toRingHom_injective (ringHom_ext hC hX)

end UniversalProperty

section Ring

variable {S : Type*} [Ring S] [Algebra k S] {τ : S →ₐ[k] S} {ε : SigmaDerivation τ}

instance instAddCommGroup : AddCommGroup (OreExtension τ ε) :=
  Module.addCommMonoidToAddCommGroup S

instance instRing : Ring (OreExtension τ ε) where

/-- Negation acts coefficientwise on Ore polynomials. -/
@[simp]
theorem coeff_neg (p : OreExtension τ ε) (n : ℕ) : coeff (-p) n = -coeff p n := by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

/-- Subtraction acts coefficientwise on Ore polynomials. -/
@[simp]
theorem coeff_sub (p q : OreExtension τ ε) (n : ℕ) :
    coeff (p - q) n = coeff p n - coeff q n := by
  simp [sub_eq_add_neg]

end Ring

end OreExtension

end TauCeti
