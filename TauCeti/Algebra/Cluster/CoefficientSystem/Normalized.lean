/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Ring.WithZero
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.Order.Ring.NNRat
import Mathlib.Tactic.NormNum

/-!
# The normalized coefficient system of a coefficient semifield

Given a coefficient semifield `P`, a commutative semiring `R`, and a multiplicative group
homomorphism `φ : P →* Rˣ` (not required to be additive or injective), the *normalized coefficient
system* lives over the zero-adjoined monoid `WithZero P`, extends `φ` by zero to `WithZero P →*₀ R`,
and normalizes each exchange polynomial `H` by the inverse of the auxiliary sum of its coefficients
in `WithZero P`:

`ν(H) = (∑_{l=0}^{r} h_l)⁻¹`.

Because `h₀` is a unit in `WithZero P` and the auxiliary addition on `WithZero P` has no nontrivial
additive cancellations, the sum is nonzero, hence a unit in `WithZero P`. The normalizer is
homogeneous of degree `-1` for every unit of `WithZero P`, so `G_ν = ⊤` and the normalized
polynomials are precisely those whose coefficients sum to `1` in `WithZero P`.

In degree `1`, the normalized exchange polynomials are in bijection with `P` via
`y ↦ (y + 1)⁻¹ (1 + y T)`, under which reversal corresponds to `y ↦ y⁻¹`, normalized dilation by
`κ` corresponds to `y ↦ y * κ`, and the dilation factor at `b` is `y^{[b]₊} (y + 1)^{-b}`—the
exact factor governing `Y`-seed mutation.

## Main definitions

* `TauCeti.CoefficientSystem.normalized`: the normalized coefficient system associated to a group
  homomorphism `φ : P →* Rˣ` out of a coefficient semifield `P`.
* `TauCeti.CoefficientSystem.normalizedBinomial`: the normalized degree-one polynomial
  `(y + 1)⁻¹ (1 + y T)` associated to `y : P`.
* `TauCeti.CoefficientSystem.normalizedBinomialEquiv`: the bijection between `P` and normalized
  degree-one exchange polynomials over `WithZero P`.
* `TauCeti.CoefficientSystem.normalizedHom`: functoriality of `normalized` along
  `CoefficientSemifieldHom`.
* `TauCeti.CoefficientSystem.normalizedPUnitToTrivial`: the coefficient-system map from the
  normalized system of the one-element semifield `PUnit` to `CoefficientSystem.trivial R`.

## Main results

* `TauCeti.CoefficientSystem.normalized_normalizer_scale`: homogeneity of degree `-1` on all units
  of `WithZero P`.
* `TauCeti.CoefficientSystem.isNormalized_normalized_iff`: `H` is normalized if and only if its
  coefficients sum to `1` in `WithZero P`.
* `TauCeti.CoefficientSystem.reverse_normalizedBinomial`,
  `TauCeti.CoefficientSystem.normalize_dilate_normalizedBinomial`,
  `TauCeti.CoefficientSystem.dilationFactor_normalizedBinomial`: action of reversal, normalized
  dilation, and `dilationFactor` on normalized binomials.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  Definition 5.3.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2, equation (2.14).
-/

public section

namespace TauCeti.CoefficientSystem

variable {P Q P' : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]
  [CoefficientSemifield P'] {R : Type*} [CommSemiring R]

/-- The auxiliary sum of the coefficients of an exchange polynomial over `WithZero P` is nonzero,
because the constant term is a unit. -/
theorem sum_coeff_ne_zero (H : ExchangePolynomial (WithZero P)) :
    ∑ l ∈ Finset.range (H.degree + 1), H.coeff l ≠ 0 := by
  have : Subsingleton (AddUnits (WithZero P)) :=
    subsingleton_of_forall_eq 0 fun u ↦ AddUnits.ext <| by
      have hval := u.val_neg
      cases hu : u.val with
      | zero => rfl
      | coe a =>
        cases hv : u.neg with
        | zero =>
          rw [hu, hv, add_zero] at hval
          exact absurd hval WithZero.coe_ne_zero
        | coe b =>
          rw [hu, hv, ← WithZero.coe_add] at hval
          exact absurd hval WithZero.coe_ne_zero
  intro h
  have h0 : H.coeff 0 = 0 :=
    Finset.sum_eq_zero_iff.mp h 0 (Finset.mem_range.mpr (Nat.succ_pos _))
  exact H.isUnit_coeff_zero.ne_zero h0

/-- The normalized coefficient system over `WithZero P` associated to a multiplicative group
homomorphism `φ : P →* Rˣ`. The scalar map extends `φ` by zero, and the normalizer takes the
inverse of the auxiliary sum of coefficients in `WithZero P`. -/
noncomputable def normalized (φ : P →* Rˣ) : CoefficientSystem (WithZero P) R where
  toScalar := WithZero.lift' ((Units.coeHom R).comp φ)
  normalizer H :=
    (Units.mk0 (∑ l ∈ Finset.range (H.degree + 1), H.coeff l) (sum_coeff_ne_zero H))⁻¹
  normalizer_reverse H := by
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, ExchangePolynomial.reverse_degree]
    congr 1
    have hsum :
        ∑ l ∈ Finset.range (H.degree + 1), H.reverse.coeff l =
          ∑ l ∈ Finset.range (H.degree + 1), H.coeff (H.degree + 1 - 1 - l) := by
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hle : l ≤ H.degree := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      simp [hle]
    rw [hsum, Finset.sum_range_reflect]
  normalizer_scale H H' := by
    apply Units.ext
    let mulAdd : WithZero P →+ WithZero P :=
      { toFun := ((∑ l ∈ Finset.range (H'.degree + 1), H'.coeff l)⁻¹ * ·)
        map_zero' := mul_zero _
        map_add' := mul_add _ }
    have hmul :
        ∑ l ∈ Finset.range (H.degree + 1),
            (∑ l' ∈ Finset.range (H'.degree + 1), H'.coeff l')⁻¹ * H.coeff l =
          (∑ l' ∈ Finset.range (H'.degree + 1), H'.coeff l')⁻¹ *
            ∑ l ∈ Finset.range (H.degree + 1), H.coeff l :=
      (map_sum mulAdd (fun l ↦ H.coeff l) (Finset.range (H.degree + 1))).symm
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
      ExchangePolynomial.scale_degree, ExchangePolynomial.scale_coeff, hmul, mul_inv, inv_inv]
    rw [mul_right_comm, mul_inv_cancel₀ (sum_coeff_ne_zero H'), one_mul]

@[simp]
theorem normalized_toScalar_coe (φ : P →* Rˣ) (p : P) :
    (normalized φ).toScalar (p : WithZero P) = (φ p : R) :=
  (rfl)

@[simp]
theorem normalized_toScalar_zero (φ : P →* Rˣ) : (normalized φ).toScalar 0 = 0 :=
  (rfl)

/-- The underlying value of the normalizer in `WithZero P` is the inverse of the coefficient sum. -/
theorem val_normalized_normalizer (φ : P →* Rˣ) (H : ExchangePolynomial (WithZero P)) :
    ((normalized φ).normalizer H : WithZero P) =
      (∑ l ∈ Finset.range (H.degree + 1), H.coeff l)⁻¹ :=
  (rfl)

/-- The normalizer of `CoefficientSystem.normalized` is homogeneous of degree `-1` for every unit
of `WithZero P`. -/
theorem normalized_normalizer_scale (φ : P →* Rˣ) (e : (WithZero P)ˣ)
    (H : ExchangePolynomial (WithZero P)) :
    (normalized φ).normalizer (H.scale e) * e = (normalized φ).normalizer H := by
  apply Units.ext
  let mulAdd : WithZero P →+ WithZero P :=
    { toFun := ((e : WithZero P) * ·)
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  have hmul :
      ∑ l ∈ Finset.range (H.degree + 1), (e : WithZero P) * H.coeff l =
        (e : WithZero P) * ∑ l ∈ Finset.range (H.degree + 1), H.coeff l :=
    (map_sum mulAdd (fun l ↦ H.coeff l) (Finset.range (H.degree + 1))).symm
  simp only [Units.val_mul, val_normalized_normalizer, ExchangePolynomial.scale_degree,
    ExchangePolynomial.scale_coeff, hmul, mul_inv]
  rw [mul_right_comm, inv_mul_cancel₀ e.ne_zero, one_mul]

/-- Every unit of `WithZero P` belongs to the normalizer subgroup of `normalized φ`. -/
@[simp]
theorem normalized_normalizerSubgroup (φ : P →* Rˣ) :
    (normalized φ).normalizerSubgroup = ⊤ := by
  rw [eq_top_iff]
  intro e _
  let H₀ := (normalized φ).normalize (ExchangePolynomial.binary (𝕂 := WithZero P))
  have hnorm : (normalized φ).normalizer H₀ = 1 := (normalized φ).normalizer_normalize _
  have hscale : (normalized φ).normalizer (H₀.scale e⁻¹) = e := by
    have h := normalized_normalizer_scale φ e⁻¹ H₀
    rw [hnorm] at h
    exact eq_of_mul_inv_eq_one h
  exact hscale ▸ (normalized φ).normalizer_mem_normalizerSubgroup (H₀.scale e⁻¹)

/-- An exchange polynomial over `WithZero P` is normalized in `normalized φ` if and only if the
auxiliary sum of its coefficients is `1`. -/
theorem isNormalized_normalized_iff (φ : P →* Rˣ) (H : ExchangePolynomial (WithZero P)) :
    (normalized φ).IsNormalized H ↔ ∑ l ∈ Finset.range (H.degree + 1), H.coeff l = 1 := by
  rw [isNormalized_iff, Units.ext_iff, val_normalized_normalizer, Units.val_one, inv_eq_one]

/-! ### Normalized binomials and degree-one classification -/

/-- The normalized degree-one exchange polynomial `(y + 1)⁻¹ (1 + y T)` associated to `y : P`. -/
def normalizedBinomial (y : P) : ExchangePolynomial (WithZero P) :=
  ExchangePolynomial.binomial
    (WithZero.unitsWithZeroEquiv.symm (y + 1)⁻¹)
    (WithZero.unitsWithZeroEquiv.symm (y * (y + 1)⁻¹))

@[simp]
theorem normalizedBinomial_degree (y : P) : (normalizedBinomial y).degree = 1 :=
  ExchangePolynomial.binomial_degree _ _

@[simp]
theorem normalizedBinomial_coeff_zero (y : P) :
    (normalizedBinomial y).coeff 0 = (((y + 1)⁻¹ : P) : WithZero P) := by
  simp [normalizedBinomial]

@[simp]
theorem normalizedBinomial_coeff_one (y : P) :
    (normalizedBinomial y).coeff 1 = ((y * (y + 1)⁻¹ : P) : WithZero P) := by
  simp [normalizedBinomial]

/-- Every `normalizedBinomial y` is normalized in `CoefficientSystem.normalized φ`. -/
@[simp]
theorem isNormalized_normalizedBinomial (φ : P →* Rˣ) (y : P) :
    (normalized φ).IsNormalized (normalizedBinomial y) := by
  rw [isNormalized_normalized_iff]
  simp only [normalizedBinomial_degree, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    zero_add, normalizedBinomial_coeff_zero, normalizedBinomial_coeff_one, ← WithZero.coe_add,
    ← WithZero.coe_one, WithZero.coe_inj]
  calc
    (y + 1)⁻¹ + y * (y + 1)⁻¹ = (1 + y) * (y + 1)⁻¹ := by rw [add_mul, one_mul]
    _ = (y + 1) * (y + 1)⁻¹ := by rw [add_comm]
    _ = 1 := mul_inv_cancel (y + 1)

/-- Normalizing `1 + y T` produces `normalizedBinomial y`. -/
theorem normalize_binomial_one (φ : P →* Rˣ) (y : P) :
    (normalized φ).normalize
      (ExchangePolynomial.binomial 1 (WithZero.unitsWithZeroEquiv.symm y)) =
        normalizedBinomial y := by
  have hν : (normalized φ).normalizer
      (ExchangePolynomial.binomial 1 (WithZero.unitsWithZeroEquiv.symm y)) =
        WithZero.unitsWithZeroEquiv.symm (y + 1)⁻¹ := by
    apply Units.ext
    rw [val_normalized_normalizer]
    simp only [ExchangePolynomial.binomial_degree, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, zero_add, ExchangePolynomial.binomial_coeff_zero,
      ExchangePolynomial.binomial_coeff_one, Units.val_one, WithZero.unitsWithZeroEquiv_symm_apply,
      Units.val_mk0]
    rw [← WithZero.coe_one, ← WithZero.coe_add, ← WithZero.coe_inv, add_comm]
  rw [normalize_def, hν, ExchangePolynomial.scale_binomial, mul_one, normalizedBinomial]
  congr 1
  rw [← map_mul, mul_comm]

/-- Reversing `normalizedBinomial y` inverts `y`. -/
@[simp]
theorem reverse_normalizedBinomial (y : P) :
    (normalizedBinomial y).reverse = normalizedBinomial y⁻¹ := by
  have hinv : (y⁻¹ + 1)⁻¹ = y * (y + 1)⁻¹ := by
    have h1 : y⁻¹ + 1 = (y + 1) / y := by
      simpa using CoefficientSemifield.inv_add_inv y 1
    rw [h1, inv_div, div_eq_mul_inv]
  have hinv2 : y⁻¹ * (y⁻¹ + 1)⁻¹ = (y + 1)⁻¹ := by
    rw [hinv, inv_mul_cancel_left]
  rw [normalizedBinomial, ExchangePolynomial.reverse_binomial, normalizedBinomial, hinv2, hinv]

/-- Normalizing the dilation of `normalizedBinomial y` by `κ` multiplies `y` by `κ`. -/
theorem normalize_dilate_normalizedBinomial (φ : P →* Rˣ) (y κ : P) :
    (normalized φ).normalize
      ((normalizedBinomial y).dilate (WithZero.unitsWithZeroEquiv.symm κ)) =
        normalizedBinomial (y * κ) := by
  have hscale :
      (normalizedBinomial y).dilate (WithZero.unitsWithZeroEquiv.symm κ) =
        (ExchangePolynomial.binomial 1 (WithZero.unitsWithZeroEquiv.symm (y * κ))).scale
          (WithZero.unitsWithZeroEquiv.symm (y + 1)⁻¹) := by
    rw [normalizedBinomial, ExchangePolynomial.dilate_binomial, ExchangePolynomial.scale_binomial,
      mul_one]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    ac_rfl
  rw [hscale, normalize_scale_of_mem _ (by simp), normalize_binomial_one]

/-- The dilation factor of `normalizedBinomial y` at `b` is `y^{[b]₊} (y + 1)^{-b}`, the factor
of Y-seed mutation. -/
@[simp]
theorem dilationFactor_normalizedBinomial (y : P) (b : ℤ) :
    (normalizedBinomial y).dilationFactor b =
      WithZero.unitsWithZeroEquiv.symm (y ^ b⁺ * (y + 1) ^ (-b)) := by
  rw [normalizedBinomial, ExchangePolynomial.dilationFactor_binomial]
  apply WithZero.unitsWithZeroEquiv.injective
  simp only [map_mul, map_inv, map_zpow, MulEquiv.apply_symm_apply, mul_zpow, inv_zpow]
  have hexp : -b⁺ + b⁻ = -b := by
    have := posPart_sub_negPart b
    omega
  rw [← zpow_neg, ← zpow_neg, neg_neg, mul_assoc, ← zpow_add, hexp]

/-- Distinct elements of `P` produce distinct normalized binomials. -/
theorem normalizedBinomial_injective : Function.Injective (normalizedBinomial (P := P)) := by
  intro y₁ y₂ h
  have h0 : (y₁ + 1)⁻¹ = (y₂ + 1)⁻¹ := by
    have := congrArg (fun H ↦ H.coeff 0) h
    simpa only [normalizedBinomial_coeff_zero, WithZero.coe_inj] using this
  have h1 : y₁ * (y₁ + 1)⁻¹ = y₂ * (y₂ + 1)⁻¹ := by
    have := congrArg (fun H ↦ H.coeff 1) h
    simpa only [normalizedBinomial_coeff_one, WithZero.coe_inj] using this
  rw [h0] at h1
  exact mul_right_cancel h1

/-- Normalized degree-one exchange polynomials over `WithZero P` are in bijection with `P` via
`y ↦ (y + 1)⁻¹ (1 + y T)`. -/
noncomputable def normalizedBinomialEquiv (φ : P →* Rˣ) :
    P ≃ {H : ExchangePolynomial (WithZero P) // H.degree = 1 ∧ (normalized φ).IsNormalized H} where
  toFun y := ⟨normalizedBinomial y, normalizedBinomial_degree y,
    isNormalized_normalizedBinomial φ y⟩
  invFun H := WithZero.unitsWithZeroEquiv
    (H.1.isUnit_coeff_degree.unit * H.1.isUnit_coeff_zero.unit⁻¹)
  left_inv y := by
    let u₀ : (WithZero P)ˣ := WithZero.unitsWithZeroEquiv.symm (y + 1)⁻¹
    let u₁ : (WithZero P)ˣ := WithZero.unitsWithZeroEquiv.symm (y * (y + 1)⁻¹)
    have h0 : (normalizedBinomial y).isUnit_coeff_zero.unit = u₀ :=
      Units.ext (by simp [u₀, normalizedBinomial_coeff_zero])
    have h1 : (normalizedBinomial y).isUnit_coeff_degree.unit = u₁ :=
      Units.ext (by simp [u₁, normalizedBinomial_degree, normalizedBinomial_coeff_one])
    dsimp only
    rw [h0, h1, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  right_inv H := by
    rcases H with ⟨H, hdeg, hnorm⟩
    apply Subtype.ext
    let a₀ : P := WithZero.unitsWithZeroEquiv H.isUnit_coeff_zero.unit
    let a₁ : P := WithZero.unitsWithZeroEquiv H.isUnit_coeff_degree.unit
    have ha₀ : H.coeff 0 = (a₀ : WithZero P) := by simp [a₀]
    have ha₁ : H.coeff 1 = (a₁ : WithZero P) := by simp [a₁, hdeg]
    have hsum : a₀ + a₁ = 1 := by
      rw [isNormalized_normalized_iff] at hnorm
      have h' : ((a₀ + a₁ : P) : WithZero P) = ((1 : P) : WithZero P) := by
        simpa [hdeg, Finset.sum_range_succ, ha₀, ha₁, ← WithZero.coe_add] using hnorm
      exact WithZero.coe_inj.mp h'
    have hy1 : a₁ * a₀⁻¹ + 1 = a₀⁻¹ := by
      calc
        a₁ * a₀⁻¹ + 1 = a₁ * a₀⁻¹ + a₀ * a₀⁻¹ := by rw [mul_inv_cancel]
        _ = (a₁ + a₀) * a₀⁻¹ := by rw [add_mul]
        _ = (a₀ + a₁) * a₀⁻¹ := by rw [add_comm]
        _ = a₀⁻¹ := by rw [hsum, one_mul]
    have harg :
        WithZero.unitsWithZeroEquiv (H.isUnit_coeff_degree.unit * H.isUnit_coeff_zero.unit⁻¹) =
          a₁ * a₀⁻¹ := by
      rw [map_mul, map_inv]
    dsimp only
    rw [harg]
    ext l hl
    · exact (normalizedBinomial_degree _).trans hdeg.symm
    · simp only [normalizedBinomial_degree] at hl
      have hl' : l = 0 ∨ l = 1 := by omega
      rcases hl' with rfl | rfl
      · simp [hy1, ha₀]
      · simp [hy1, ha₁]

@[simp]
theorem normalizedBinomialEquiv_apply (φ : P →* Rˣ) (y : P) :
    (normalizedBinomialEquiv φ y).1 = normalizedBinomial y :=
  (rfl)

/-! ### Functoriality and comparison with the trivial semifield -/

/-- A homomorphism of coefficient semifields induces a homomorphism between their normalized
coefficient systems when the scalar maps commute with it. -/
noncomputable def normalizedHom (f : CoefficientSemifieldHom P Q)
    (φ₁ : P →* Rˣ) (φ₂ : Q →* Rˣ) (hφ : ∀ p, φ₂ (f p) = φ₁ p) :
    (normalized φ₁).Hom (normalized φ₂) where
  toMonoidWithZeroHom := WithZero.map' f.toMonoidHom
  toScalar_comp := by
    ext p
    exact congrArg Units.val (hφ p)
  map_normalizer H := by
    apply Units.ext
    have hmap : ∀ x : WithZero P,
        WithZero.map' f.toMonoidHom x = WithZero.mapAddHom f.toAddHom x := by
      intro x
      cases x <;> rfl
    have hsum :
        ∑ l ∈ Finset.range (H.degree + 1), WithZero.map' f.toMonoidHom (H.coeff l) =
          WithZero.map' f.toMonoidHom (∑ l ∈ Finset.range (H.degree + 1), H.coeff l) := by
      simp_rw [hmap]
      exact (map_sum (WithZero.mapAddHom f.toAddHom)
        (fun l ↦ H.coeff l) (Finset.range (H.degree + 1))).symm
    simp only [val_normalized_normalizer, ExchangePolynomial.map_degree,
      ExchangePolynomial.map_coeff, Units.coe_map, hsum]
    exact (map_inv₀ (WithZero.map' f.toMonoidHom) _).symm

@[simp]
theorem normalizedHom_apply_coe (f : CoefficientSemifieldHom P Q) (φ₁ : P →* Rˣ) (φ₂ : Q →* Rˣ)
    (hφ : ∀ p, φ₂ (f p) = φ₁ p) (p : P) :
    normalizedHom f φ₁ φ₂ hφ (p : WithZero P) = (f p : WithZero Q) :=
  (rfl)

@[simp]
theorem normalizedHom_id (φ : P →* Rˣ) :
    normalizedHom (CoefficientSemifieldHom.id P) φ φ (fun _ ↦ by simp) =
      Hom.id (normalized φ) := by
  ext x
  cases x with
  | zero => simp
  | coe p => simp

theorem normalizedHom_comp (g : CoefficientSemifieldHom Q P') (f : CoefficientSemifieldHom P Q)
    (φ₁ : P →* Rˣ) (φ₂ : Q →* Rˣ) (φ₃ : P' →* Rˣ)
    (h₁₂ : ∀ p, φ₂ (f p) = φ₁ p) (h₂₃ : ∀ q, φ₃ (g q) = φ₂ q) :
    normalizedHom (g.comp f) φ₁ φ₃ (fun p ↦ by simp [h₂₃, h₁₂]) =
      (normalizedHom g φ₂ φ₃ h₂₃).comp (normalizedHom f φ₁ φ₂ h₁₂) := by
  ext x
  cases x with
  | zero => simp
  | coe p => simp

/-- Pushing forward a normalized binomial along a homomorphism of coefficient semifields applies
the homomorphism to its parameter. -/
@[simp]
theorem map_normalizedBinomial (f : CoefficientSemifieldHom P Q) (y : P) :
    (normalizedBinomial y).map (WithZero.map' f.toMonoidHom) = normalizedBinomial (f y) := by
  ext l hl
  · exact (ExchangePolynomial.map_degree _ _).trans
      ((normalizedBinomial_degree y).trans (normalizedBinomial_degree (f y)).symm)
  · simp only [ExchangePolynomial.map_degree, normalizedBinomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl
    · rw [ExchangePolynomial.map_coeff, normalizedBinomial_coeff_zero,
        normalizedBinomial_coeff_zero, WithZero.map'_coe]
      simp [map_inv, map_add]
    · rw [ExchangePolynomial.map_coeff, normalizedBinomial_coeff_one,
        normalizedBinomial_coeff_one, WithZero.map'_coe]
      simp [map_mul, map_inv, map_add]

/-- The canonical coefficient-system homomorphism from the normalized system of the one-element
coefficient semifield `PUnit` to the scalar system `CoefficientSystem.trivial R`. -/
noncomputable def normalizedPUnitToTrivial (R : Type*) [CommSemiring R] :
    (normalized (1 : PUnit →* Rˣ)).Hom (trivial R) where
  toMonoidWithZeroHom := WithZero.lift' (1 : PUnit →* R)
  toScalar_comp := by
    ext p
    simp
  map_normalizer H := by
    have h1 : (normalized (1 : PUnit →* Rˣ)).normalizer H = 1 := by
      apply WithZero.unitsWithZeroEquiv.injective
      exact Subsingleton.elim _ _
    simp [h1]

/-- Under the map from the one-element semifield to the scalar system, the unique normalized
binomial maps to the binary polynomial `1 + T`. -/
@[simp]
theorem map_normalizedBinomial_punit (R : Type*) [CommSemiring R] :
    (normalizedBinomial PUnit.unit).map (normalizedPUnitToTrivial R).toMonoidWithZeroHom =
      ExchangePolynomial.binary := by
  ext l hl
  · exact (ExchangePolynomial.map_degree _ _).trans
      ((normalizedBinomial_degree _).trans ExchangePolynomial.binary_degree.symm)
  · simp only [ExchangePolynomial.map_degree, normalizedBinomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;>
      simp [normalizedBinomial_coeff_zero, normalizedBinomial_coeff_one, normalizedPUnitToTrivial]

/-! ### Non-examples of normalizers -/

/-- Over `ℚ≥0`, no coefficient system has normalizer `ν(H) = h₀⁻¹`, because reversal invariance
fails on `1 + 2T`. -/
example :
    ¬ ∃ c : CoefficientSystem ℚ≥0 ℚ≥0,
      ∀ H : ExchangePolynomial ℚ≥0, c.normalizer H = (H.isUnit_coeff_zero.unit)⁻¹ := by
  rintro ⟨c, hc⟩
  let H : ExchangePolynomial ℚ≥0 := ExchangePolynomial.binomial 1 (Units.mk0 2 (by norm_num))
  have hrev := c.normalizer_reverse H
  rw [hc, hc] at hrev
  have hval := congrArg Units.val hrev
  simp only [Units.val_inv_eq_inv_val] at hval
  have h1 : (H.reverse.isUnit_coeff_zero.unit : ℚ≥0) = 2 := by simp [H]
  have h2 : (H.isUnit_coeff_zero.unit : ℚ≥0) = 1 := by simp [H]
  rw [h1, h2] at hval
  norm_num at hval

/-- Over `ℚ≥0`, no coefficient system has constant normalizer `ν(H) = 2`, because scaling
homogeneity fails. -/
example :
    ¬ ∃ c : CoefficientSystem ℚ≥0 ℚ≥0,
      ∀ H : ExchangePolynomial ℚ≥0, c.normalizer H = Units.mk0 2 (by norm_num) := by
  rintro ⟨c, hc⟩
  have hnorm := c.normalizer_normalize ExchangePolynomial.binary
  rw [hc] at hnorm
  have hval := congrArg Units.val hnorm
  norm_num at hval

end TauCeti.CoefficientSystem
