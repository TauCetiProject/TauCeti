/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.LinearAlgebra.Matrix.FinsuppBilinForm

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Ring

/-!
# Based quantum tori and based charts

Given a commutative semiring `R`, a unit `u : Rˣ`, and an integer matrix `Λ : Matrix I I ℤ`, the
biadditive pairing `Λ.finsuppBilinForm` on `I →₀ ℤ` defines a normalized factor set
`(a, b) ↦ u ^ Λ.finsuppBilinForm a b` on `Multiplicative (I →₀ ℤ)`. The resulting twisted group
algebra `TauCeti.basedTorus R u Λ` is the based quantum torus `T(R, u, Λ)`. Its basis monomials
`X^a` multiply by `X^a * X^b = u ^ Λ(a, b) • X^{a + b}` and are units; when `Λ` is alternating,
the inverse of `X^a` is `X^{-a}` and variables quasi-commute by
`X_i * X_j = u ^ (2 * Λ i j) • (X_j * X_i)`. At `u = 1` (for any `Λ`) or at `Λ = 0` (for any `u`),
the factor set is trivial and `basedTorus` is isomorphic to the multivariable Laurent polynomial
ring `TauCeti.LaurentRing R I`.

In an arbitrary (not necessarily commutative) `R`-algebra `B`, a **based chart**
`TauCeti.BasedChart R u Λ B` is an `R`-linearly independent family of unit monomials
`M : (I →₀ ℤ) → Bˣ` satisfying `M(0) = 1` and `M(a) * M(b) = u ^ Λ(a, b) * M(a + b)`. A based
chart is uniquely determined by its coordinates `X_i = M(e_i)`, and for any linear order on `I`
and vanishing diagonal of `Λ`, each monomial is given by the normalized ordered product
`u ^ (-∑_{i < j} a_i Λ_{ij} a_j) * ∏_i X_i^{a_i}`. Conversely, when `Λ` is alternating, any
quasi-commuting family of units `U : I → Bˣ` defines normalized ordered-product monomials
independent of the chosen linear order, assembling into a universal `R`-algebra map from
`basedTorus R u Λ` and, when linearly independent, into a based chart.

Evaluating `M` along `TwistedMonoidAlgebra.lift` identifies `BasedChart R u Λ B` bijectively with
injective `R`-algebra maps `basedTorus R u Λ →ₐ[R] B`. At `u = 1` and `Λ = 0` in a commutative
target `B`, this further identifies based charts with injective Laurent charts
`LaurentRing R I →ₐ[R] B`.

## Main definitions

* `TauCeti.formFactorSet`: the normalized factor set `(a, b) ↦ u ^ Λ.finsuppBilinForm a b` on
  `Multiplicative (I →₀ ℤ)`.
* `TauCeti.basedTorus`: the based quantum torus `T(R, u, Λ)`.
* `TauCeti.BasedTorus.monomial`, `TauCeti.BasedTorus.unitMonomial`, `TauCeti.BasedTorus.X`,
  `TauCeti.BasedTorus.basis`: basis monomials, unit monomials, coordinate generators, and basis of
  `basedTorus R u Λ`.
* `TauCeti.BasedTorus.laurentRingEquivOfUnitOne` and
  `TauCeti.BasedTorus.laurentRingEquivOfFormZero`: untwisted `R`-algebra isomorphisms with
  `LaurentRing R I` when `u = 1` or `Λ = 0`.
* `TauCeti.BasedChart`: a faithful normalized monomial chart in an `R`-algebra `B`.
* `TauCeti.BasedChart.coordinate`, `TauCeti.BasedChart.eval`, `TauCeti.BasedChart.toAlgHom`:
  coordinates, coefficient-family chart map, and induced torus algebra map.
* `TauCeti.BasedChart.algHomEquiv` and `TauCeti.BasedChart.laurentChartEquiv`: bijections with
  injective torus maps and (for `u = 1`, `Λ = 0`, commutative `B`) injective Laurent charts.
* `TauCeti.orderedMonomial` and `TauCeti.BasedChart.ofCoordinates`: normalized ordered-product
  monomials of quasi-commuting units and the resulting based chart.
* `TauCeti.BasedChart.reindex`, `TauCeti.BasedChart.map`, `TauCeti.BasedChart.congrAlgEquiv`:
  transport along index equivalences and injective algebra homomorphisms.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195 (2005),
  §4, for based quantum tori and normalized torus monomials.
* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §3, for classical Laurent charts.
-/

public section

namespace TauCeti

section FactorSet

variable {R I : Type*} [CommSemiring R]

/-- The factor set on `Multiplicative (I →₀ ℤ)` attached to a unit `u : Rˣ` and an integer matrix
`Λ : Matrix I I ℤ`, sending `(ofAdd a, ofAdd b)` to `u ^ Λ.finsuppBilinForm a b`. -/
noncomputable def formFactorSet (u : Rˣ) (Λ : Matrix I I ℤ) :
    Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ :=
  fun g h ↦ u ^ Λ.finsuppBilinForm g.toAdd h.toAdd

@[simp]
theorem formFactorSet_ofAdd (u : Rˣ) (Λ : Matrix I I ℤ) (a b : I →₀ ℤ) :
    formFactorSet u Λ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) =
      u ^ Λ.finsuppBilinForm a b :=
  (rfl)

@[simp]
theorem formFactorSet_one_left_unit (Λ : Matrix I I ℤ) :
    formFactorSet (1 : Rˣ) Λ = 1 := by
  ext g h
  simp [formFactorSet]

@[simp]
theorem formFactorSet_zero_right_matrix (u : Rˣ) :
    formFactorSet u (0 : Matrix I I ℤ) = 1 := by
  ext g h
  simp [formFactorSet]

/-- Bilinearity of `Λ.finsuppBilinForm` makes `formFactorSet u Λ` a normalized factor set on
`Multiplicative (I →₀ ℤ)` without any symmetry or alternation hypothesis on `Λ`. -/
instance isFactorSet_formFactorSet (u : Rˣ) (Λ : Matrix I I ℤ) :
    IsFactorSet (formFactorSet u Λ) where
  cocycle g h j := by
    simp only [formFactorSet, toAdd_mul, ← zpow_add]
    congr 1
    simp only [map_add, LinearMap.add_apply]
    ring
  one_left g := by simp [formFactorSet]

end FactorSet

/-- **The based quantum torus** `T(R, u, Λ)`, realized as the twisted group algebra of
`Multiplicative (I →₀ ℤ)` for the bilinear factor set `formFactorSet u Λ`. -/
noncomputable abbrev basedTorus (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*}
    (Λ : Matrix I I ℤ) :=
  twistedMonoidAlgebra R (Multiplicative (I →₀ ℤ)) (formFactorSet u Λ)

namespace BasedTorus

section General

variable {R I : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ}

/-- The normalized basis monomial `X^a` of `basedTorus R u Λ` at exponent `a : I →₀ ℤ`. -/
noncomputable def monomial (a : I →₀ ℤ) : basedTorus R u Λ :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a)

theorem monomial_def (a : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) = TwistedMonoidAlgebra.of (Multiplicative.ofAdd a) :=
  (rfl)

@[simp]
theorem monomial_zero : (monomial 0 : basedTorus R u Λ) = 1 :=
  TwistedMonoidAlgebra.of_one

/-- **Multiplication law in the based quantum torus**:
`X^a * X^b = (u ^ Λ(a, b)) • X^{a + b}`. -/
@[simp]
theorem monomial_mul (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ Λ.finsuppBilinForm a b : Rˣ) : R) • monomial (a + b) := by
  simp [monomial_def, ← ofAdd_add]

/-- Each normalized monomial `X^a` is a unit of `basedTorus R u Λ`, with inverse
`(u ^ Λ(a, -a))⁻¹ • X^{-a}`. -/
noncomputable def unitMonomial (a : I →₀ ℤ) : (basedTorus R u Λ)ˣ where
  val := monomial a
  inv := (((u ^ Λ.finsuppBilinForm a (-a))⁻¹ : Rˣ) : R) • monomial (-a)
  val_inv := by simp [smul_smul, ← Units.val_mul]
  inv_val := by simp [smul_smul, ← Units.val_mul]

@[simp]
theorem val_unitMonomial (a : I →₀ ℤ) :
    ((unitMonomial a : (basedTorus R u Λ)ˣ) : basedTorus R u Λ) = monomial a :=
  (rfl)

/-- When `Λ(a, a) = 0`, the inverse of the unit monomial `X^a` is `X^{-a}` with no scalar twist. -/
theorem inv_unitMonomial_of_self_eq_zero {a : I →₀ ℤ} (ha : Λ.finsuppBilinForm a a = 0) :
    (unitMonomial a : (basedTorus R u Λ)ˣ)⁻¹ = unitMonomial (-a) :=
  inv_eq_of_mul_eq_one_right <| Units.ext <| by simp [ha]

/-- When `Λ` is alternating, `(X^a)⁻¹ = X^{-a}` for every exponent `a`. -/
theorem inv_unitMonomial_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (a : I →₀ ℤ) :
    (unitMonomial a : (basedTorus R u Λ)ˣ)⁻¹ = unitMonomial (-a) :=
  inv_unitMonomial_of_self_eq_zero (hΛ.self_eq_zero a)

/-- The `i`-th coordinate generator `X_i = X^{e_i}` of `basedTorus R u Λ`. -/
noncomputable def X (i : I) : basedTorus R u Λ :=
  monomial (Finsupp.single i 1)

theorem X_def (i : I) : (X i : basedTorus R u Λ) = monomial (Finsupp.single i 1) :=
  (rfl)

/-- The `i`-th coordinate generator `X_i` as a unit of `basedTorus R u Λ`. -/
noncomputable def unitX (i : I) : (basedTorus R u Λ)ˣ :=
  unitMonomial (Finsupp.single i 1)

@[simp]
theorem val_unitX (i : I) : ((unitX i : (basedTorus R u Λ)ˣ) : basedTorus R u Λ) = X i :=
  (rfl)

/-- Quasi-commutation of basis monomials for an arbitrary matrix `Λ`. -/
theorem monomial_mul_comm (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ (Λ.finsuppBilinForm a b - Λ.finsuppBilinForm b a) : Rˣ) : R) •
        (monomial b * monomial a) := by
  rw [monomial_mul, monomial_mul, add_comm b a, smul_smul, ← Units.val_mul, ← zpow_add,
    sub_add_cancel]

/-- For an alternating form `Λ`, basis monomials quasi-commute by `u ^ (2 * Λ(a, b))`. -/
theorem monomial_mul_comm_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ (2 * Λ.finsuppBilinForm a b) : Rˣ) : R) • (monomial b * monomial a) := by
  rw [monomial_mul_comm, ← hΛ.neg_eq a b]
  congr 3
  ring

/-- For an alternating form `Λ`, coordinate generators satisfy
`X_i * X_j = (u ^ (2 * Λ i j)) • (X_j * X_i)`. -/
theorem X_mul_X_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (i j : I) :
    (X i : basedTorus R u Λ) * X j =
      ((u ^ (2 * Λ i j) : Rˣ) : R) • (X j * X i) := by
  simpa [X_def, Matrix.finsuppBilinForm_single_single] using
    monomial_mul_comm_of_isAlt (R := R) (u := u) hΛ (Finsupp.single i 1) (Finsupp.single j 1)

variable (R u Λ)

/-- The `R`-basis of `basedTorus R u Λ` indexed by the exponent group `I →₀ ℤ`. -/
noncomputable def basis : Module.Basis (I →₀ ℤ) R (basedTorus R u Λ) :=
  (TwistedMonoidAlgebra.basis R (Multiplicative (I →₀ ℤ)) (formFactorSet u Λ)).reindex
    Multiplicative.ofAdd.symm

@[simp]
theorem basis_apply (a : I →₀ ℤ) : basis R u Λ a = monomial a := by
  simp [basis, monomial_def]

variable {R u Λ}

/-- An `R`-algebra map out of `basedTorus R u Λ` is determined by its values on the basis
monomials `monomial a`. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A]
    {f g : basedTorus R u Λ →ₐ[R] A} (h : ∀ a : I →₀ ℤ, f (monomial a) = g (monomial a)) :
    f = g :=
  TwistedMonoidAlgebra.algHom_ext fun x ↦ h x.toAdd

/-- When `formFactorSet u Λ = 1`, the based quantum torus is canonically isomorphic as an
`R`-algebra to `LaurentRing R I`. -/
noncomputable def laurentRingEquivOfFactorSetEqOne (h : formFactorSet u Λ = 1) :
    basedTorus R u Λ ≃ₐ[R] LaurentRing R I :=
  (TwistedMonoidAlgebra.equivOfCoboundary
      (1 : Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ)
      (formFactorSet u Λ) 1 (by simp [h])).trans <|
    (TwistedMonoidAlgebra.monoidAlgebraEquiv R (Multiplicative (I →₀ ℤ))).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (I →₀ ℤ)).symm

@[simp]
theorem laurentRingEquivOfFactorSetEqOne_monomial (h : formFactorSet u Λ = 1) (a : I →₀ ℤ) :
    laurentRingEquivOfFactorSetEqOne h (monomial a) = AddMonoidAlgebra.single a 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (I →₀ ℤ)).injective
  simp [laurentRingEquivOfFactorSetEqOne, monomial_def]

@[simp]
theorem laurentRingEquivOfFactorSetEqOne_symm_single (h : formFactorSet u Λ = 1)
    (a : I →₀ ℤ) (r : R) :
    (laurentRingEquivOfFactorSetEqOne h).symm (AddMonoidAlgebra.single a r) = r • monomial a := by
  apply (laurentRingEquivOfFactorSetEqOne h).injective
  simp [AddMonoidAlgebra.smul_single]

/-- At `u = 1`, the based torus is isomorphic to `LaurentRing R I` for every matrix `Λ`. -/
noncomputable def laurentRingEquivOfUnitOne (R : Type*) [CommSemiring R] {I : Type*}
    (Λ : Matrix I I ℤ) : basedTorus R 1 Λ ≃ₐ[R] LaurentRing R I :=
  laurentRingEquivOfFactorSetEqOne (formFactorSet_one_left_unit Λ)

@[simp]
theorem laurentRingEquivOfUnitOne_monomial (R : Type*) [CommSemiring R] {I : Type*}
    (Λ : Matrix I I ℤ) (a : I →₀ ℤ) :
    laurentRingEquivOfUnitOne R Λ (monomial a) = AddMonoidAlgebra.single a 1 :=
  laurentRingEquivOfFactorSetEqOne_monomial _ a

/-- At `Λ = 0`, the based torus is isomorphic to `LaurentRing R I` for every unit `u`. -/
noncomputable def laurentRingEquivOfFormZero (R : Type*) [CommSemiring R] (u : Rˣ) (I : Type*) :
    basedTorus R u (0 : Matrix I I ℤ) ≃ₐ[R] LaurentRing R I :=
  laurentRingEquivOfFactorSetEqOne (formFactorSet_zero_right_matrix u)

@[simp]
theorem laurentRingEquivOfFormZero_monomial (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*}
    (a : I →₀ ℤ) :
    laurentRingEquivOfFormZero R u I (monomial a) = AddMonoidAlgebra.single a 1 :=
  laurentRingEquivOfFactorSetEqOne_monomial _ a

end General

end BasedTorus

/-! ### Normalized monomial families and based charts -/

private theorem map_algebraMap_comm {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (w : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B).toMonoidHom w * x = x * Units.map (algebraMap R B).toMonoidHom w :=
  Units.ext <| Algebra.commutes _ _

/-- Two normalized `(u, Λ)`-monomial families into `Bˣ` agree everywhere as soon as they agree on
the coordinate generators `Finsupp.single i 1`. -/
theorem normalizedMonomial_eq_of_single_one_eq {R I B : Type*} [CommSemiring R] [Semiring B]
    [Algebra R B] {u : Rˣ} {Λ : Matrix I I ℤ} {M₁ M₂ : (I →₀ ℤ) → Bˣ}
    (h₁0 : M₁ 0 = 1) (h₂0 : M₂ 0 = 1)
    (h₁m : ∀ a b, M₁ a * M₁ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * M₁ (a + b))
    (h₂m : ∀ a b, M₂ a * M₂ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * M₂ (a + b))
    (h : ∀ i, M₁ (Finsupp.single i 1) = M₂ (Finsupp.single i 1)) : M₁ = M₂ := by
  have hadd {a b : I →₀ ℤ} (ha : M₁ a = M₂ a) (hb : M₁ b = M₂ b) : M₁ (a + b) = M₂ (a + b) :=
    mul_left_cancel <| (h₁m a b).symm.trans <| by rw [ha, hb, h₂m]
  have hsub {a b : I →₀ ℤ} (hab : M₁ (a + b) = M₂ (a + b)) (hb : M₁ b = M₂ b) : M₁ a = M₂ a :=
    mul_right_cancel <| (h₁m a b).trans <| by rw [hab, ← h₂m, hb]
  have hsingle (i : I) (n : ℤ) : M₁ (Finsupp.single i n) = M₂ (Finsupp.single i n) := by
    induction n using Int.induction_on with
    | zero => simp [h₁0, h₂0]
    | succ k hk =>
      rw [Finsupp.single_add]
      exact hadd hk (h i)
    | pred k hk =>
      refine hsub (b := Finsupp.single i 1) ?_ (h i)
      simpa [← Finsupp.single_add] using hk
  funext a
  induction a using Finsupp.induction_linear with
  | zero => simp [h₁0, h₂0]
  | add a b ha hb => exact hadd ha hb
  | single i n => exact hsingle i n

/-- **A based chart** for `(R, u, Λ)` in a (not necessarily commutative) `R`-algebra `B`: a
normalized `(u, Λ)`-multiplicative family of units `M : (I →₀ ℤ) → Bˣ` whose underlying elements
in `B` are `R`-linearly independent. -/
structure BasedChart (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*}
    (Λ : Matrix I I ℤ) (B : Type*) [Semiring B] [Algebra R B] where
  /-- The normalized monomial `M(a)` at exponent `a`, as a unit of `B`. -/
  monomial : (I →₀ ℤ) → Bˣ
  /-- The normalized monomial at `0` is `1`. -/
  monomial_zero : monomial 0 = 1
  /-- Multiplication of normalized monomials is twisted by `u ^ Λ(a, b)`. -/
  monomial_mul : ∀ a b, monomial a * monomial b =
    Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * monomial (a + b)
  /-- The normalized monomials are `R`-linearly independent in `B`. -/
  linearIndependent : LinearIndependent R fun a ↦ (monomial a : B)

namespace BasedChart

section Basic

variable {R I J B B' : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ}
  [Semiring B] [Algebra R B] [Semiring B'] [Algebra R B']

@[ext]
theorem ext {c₁ c₂ : BasedChart R u Λ B} (h : ∀ a, c₁.monomial a = c₂.monomial a) : c₁ = c₂ := by
  cases c₁; cases c₂; congr; funext a; exact h a

@[simp]
theorem val_monomial_zero (c : BasedChart R u Λ B) : (c.monomial 0 : B) = 1 := by
  simp [c.monomial_zero]

theorem val_monomial_mul (c : BasedChart R u Λ B) (a b : I →₀ ℤ) :
    (c.monomial a : B) * c.monomial b =
      ((u ^ Λ.finsuppBilinForm a b : Rˣ) : R) • (c.monomial (a + b) : B) := by
  rw [← Units.val_mul, c.monomial_mul, Units.val_mul, Units.coe_map]
  simp [Algebra.smul_def]

/-- Quasi-commutation of normalized monomials in a based chart. -/
theorem monomial_mul_comm (c : BasedChart R u Λ B) (a b : I →₀ ℤ) :
    c.monomial a * c.monomial b =
      Units.map (algebraMap R B).toMonoidHom
        (u ^ (Λ.finsuppBilinForm a b - Λ.finsuppBilinForm b a)) *
        (c.monomial b * c.monomial a) := by
  rw [c.monomial_mul, c.monomial_mul, add_comm b a, ← mul_assoc, ← map_mul, ← zpow_add,
    sub_add_cancel]

/-- For an alternating form `Λ`, normalized monomials quasi-commute by `u ^ (2 * Λ(a, b))`. -/
theorem monomial_mul_comm_of_isAlt (c : BasedChart R u Λ B) (hΛ : Λ.finsuppBilinForm.IsAlt)
    (a b : I →₀ ℤ) :
    c.monomial a * c.monomial b =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ.finsuppBilinForm a b)) *
        (c.monomial b * c.monomial a) := by
  rw [c.monomial_mul_comm, ← hΛ.neg_eq a b]
  congr 3
  ring

/-- When `Λ(a, a) = 0`, the inverse of `c.monomial a` is `c.monomial (-a)`. -/
theorem inv_monomial_of_self_eq_zero (c : BasedChart R u Λ B) {a : I →₀ ℤ}
    (ha : Λ.finsuppBilinForm a a = 0) : (c.monomial a)⁻¹ = c.monomial (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  simpa [ha, c.monomial_zero] using c.monomial_mul a (-a)

/-- The `i`-th coordinate `X_i = M(e_i)` of a based chart. -/
noncomputable def coordinate (c : BasedChart R u Λ B) (i : I) : Bˣ :=
  c.monomial (Finsupp.single i 1)

theorem coordinate_def (c : BasedChart R u Λ B) (i : I) :
    c.coordinate i = c.monomial (Finsupp.single i 1) :=
  (rfl)

/-- **Coordinates determine a based chart**: two based charts with the same coordinates are
equal. -/
theorem ext_coordinate {c₁ c₂ : BasedChart R u Λ B}
    (h : ∀ i, c₁.coordinate i = c₂.coordinate i) : c₁ = c₂ :=
  BasedChart.ext fun a ↦
    congr_fun (normalizedMonomial_eq_of_single_one_eq c₁.monomial_zero c₂.monomial_zero
      c₁.monomial_mul c₂.monomial_mul h) a

/-- When `Λ i i = 0`, the monomial along the `i`-th axis is the integer power of `coordinate i`. -/
theorem monomial_single_of_diag_zero (c : BasedChart R u Λ B) {i : I} (hi : Λ i i = 0) (n : ℤ) :
    c.monomial (Finsupp.single i n) = c.coordinate i ^ n := by
  have hmul (p q : ℤ) :
      c.monomial (Finsupp.single i p) * c.monomial (Finsupp.single i q) =
        c.monomial (Finsupp.single i (p + q)) := by
    rw [c.monomial_mul, Finsupp.single_add, Matrix.finsuppBilinForm_single_single, hi, mul_zero,
      zpow_zero, map_one, one_mul]
  induction n using Int.induction_on with
  | zero => simp [c.monomial_zero]
  | succ k hk => rw [← hmul, hk, ← coordinate_def, ← zpow_add_one]
  | pred k hk =>
    rw [zpow_sub_one]
    refine eq_mul_inv_of_mul_eq ?_
    rw [← hk, coordinate_def, hmul, sub_add_cancel]

/-- For an alternating form `Λ`, the coordinates satisfy
`X_i * X_j = u ^ (2 * Λ i j) * (X_j * X_i)`. -/
theorem coordinate_mul_comm_of_isAlt (c : BasedChart R u Λ B) (hΛ : Λ.finsuppBilinForm.IsAlt)
    (i j : I) :
    c.coordinate i * c.coordinate j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) *
        (c.coordinate j * c.coordinate i) := by
  simpa [coordinate_def, Matrix.finsuppBilinForm_single_single] using
    c.monomial_mul_comm_of_isAlt hΛ (Finsupp.single i 1) (Finsupp.single j 1)

/-- The chart map on finitely supported coefficient families: `f ↦ ∑_a f(a) • M(a)`. -/
noncomputable def eval (c : BasedChart R u Λ B) : ((I →₀ ℤ) →₀ R) →ₗ[R] B :=
  Finsupp.linearCombination R fun a ↦ (c.monomial a : B)

theorem eval_def (c : BasedChart R u Λ B) :
    c.eval = Finsupp.linearCombination R fun a ↦ (c.monomial a : B) :=
  (rfl)

@[simp]
theorem eval_single (c : BasedChart R u Λ B) (a : I →₀ ℤ) (r : R) :
    c.eval (Finsupp.single a r) = r • (c.monomial a : B) := by
  simp [eval_def]

/-- **Injectivity of the chart map** on finitely supported coefficient families. -/
theorem eval_injective (c : BasedChart R u Λ B) : Function.Injective c.eval :=
  c.linearIndependent

/-- The `R`-algebra map `basedTorus R u Λ →ₐ[R] B` induced by `TwistedMonoidAlgebra.lift` applied
to the normalized monomials of `c`. -/
noncomputable def toAlgHom (c : BasedChart R u Λ B) : basedTorus R u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift (fun g ↦ (c.monomial g.toAdd : B)) (by simp)
    (fun g h ↦ c.val_monomial_mul g.toAdd h.toAdd)

@[simp]
theorem toAlgHom_monomial (c : BasedChart R u Λ B) (a : I →₀ ℤ) :
    c.toAlgHom (BasedTorus.monomial a) = c.monomial a :=
  TwistedMonoidAlgebra.lift_of ..

@[simp]
theorem toAlgHom_X (c : BasedChart R u Λ B) (i : I) :
    c.toAlgHom (BasedTorus.X i) = c.coordinate i :=
  c.toAlgHom_monomial (Finsupp.single i 1)

@[simp]
theorem unitsMap_toAlgHom_unitMonomial (c : BasedChart R u Λ B) (a : I →₀ ℤ) :
    Units.map (c.toAlgHom : basedTorus R u Λ →* B) (BasedTorus.unitMonomial a) = c.monomial a :=
  Units.ext <| c.toAlgHom_monomial a

/-- **Factorization of the chart map**: `c.eval` is the inverse basis representation
`f ↦ ∑_a f(a) • X^a` of `basedTorus R u Λ` followed by the underlying linear map of `c.toAlgHom`. -/
theorem eval_eq_toAlgHom_comp_repr_symm (c : BasedChart R u Λ B) :
    c.eval = c.toAlgHom.toLinearMap.comp (BasedTorus.basis R u Λ).repr.symm.toLinearMap := by
  refine Finsupp.lhom_ext' fun a ↦ LinearMap.ext fun r ↦ ?_
  simp

/-- The induced `R`-algebra map `basedTorus R u Λ →ₐ[R] B` of a based chart is injective. -/
theorem toAlgHom_injective (c : BasedChart R u Λ B) : Function.Injective c.toAlgHom := by
  intro x y hxy
  apply (BasedTorus.basis R u Λ).repr.injective
  apply c.eval_injective
  rw [c.eval_eq_toAlgHom_comp_repr_symm]
  simpa using hxy

variable (R u Λ) in
/-- The tautological based chart of `basedTorus R u Λ` in itself. -/
noncomputable def tautological : BasedChart R u Λ (basedTorus R u Λ) where
  monomial := BasedTorus.unitMonomial
  monomial_zero := Units.ext BasedTorus.monomial_zero
  monomial_mul a b := Units.ext <| by
    rw [Units.val_mul, Units.val_mul, Units.coe_map]
    simp [Algebra.smul_def]
  linearIndependent := by
    convert (BasedTorus.basis R u Λ).linearIndependent using 1
    ext a
    simp

@[simp]
theorem tautological_monomial (a : I →₀ ℤ) :
    (tautological R u Λ).monomial a = BasedTorus.unitMonomial a :=
  (rfl)

@[simp]
theorem tautological_toAlgHom :
    (tautological R u Λ).toAlgHom = AlgHom.id R (basedTorus R u Λ) := by
  ext a
  simp

/-- Transport a based chart along an injective `R`-algebra homomorphism `B →ₐ[R] B'`. -/
def map (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B) :
    BasedChart R u Λ B' where
  monomial a := Units.map f.toMonoidHom (c.monomial a)
  monomial_zero := by simp [c.monomial_zero]
  monomial_mul a b := by
    rw [← map_mul, c.monomial_mul, map_mul]
    refine congrArg (· * _) (Units.ext ?_)
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact f.commutes _
  linearIndependent := by
    rw [LinearIndependent]
    intro l₁ l₂ hl
    apply c.linearIndependent
    apply hf
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] using hl

@[simp]
theorem map_monomial (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B)
    (a : I →₀ ℤ) : (c.map f hf).monomial a = Units.map f.toMonoidHom (c.monomial a) :=
  (rfl)

@[simp]
theorem map_coordinate (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B)
    (i : I) : (c.map f hf).coordinate i = Units.map f.toMonoidHom (c.coordinate i) :=
  (rfl)

@[simp]
theorem map_toAlgHom (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B) :
    (c.map f hf).toAlgHom = f.comp c.toAlgHom := by
  ext a
  simp

/-- Equivalence of based charts induced by an `R`-algebra isomorphism `B ≃ₐ[R] B'`. -/
def congrAlgEquiv (e : B ≃ₐ[R] B') : BasedChart R u Λ B ≃ BasedChart R u Λ B' where
  toFun := map e.toAlgHom (by rw [AlgEquiv.coe_toAlgHom]; exact e.injective)
  invFun := map e.symm.toAlgHom (by rw [AlgEquiv.coe_toAlgHom]; exact e.symm.injective)
  left_inv c := BasedChart.ext fun a ↦ Units.ext (by simp)
  right_inv c := BasedChart.ext fun a ↦ Units.ext (by simp)

@[simp]
theorem congrAlgEquiv_monomial (e : B ≃ₐ[R] B') (c : BasedChart R u Λ B) (a : I →₀ ℤ) :
    (congrAlgEquiv e c).monomial a = Units.map e.toAlgHom.toMonoidHom (c.monomial a) :=
  (rfl)

/-- Reindex a based chart along an equivalence `e : I ≃ J` of index types. -/
noncomputable def reindex (e : I ≃ J) :
    BasedChart R u Λ B ≃ BasedChart R u (Λ.submatrix e.symm e.symm) B where
  toFun c :=
    { monomial := fun a ↦ c.monomial (a.mapDomain e.symm)
      monomial_zero := by simp [c.monomial_zero]
      monomial_mul := fun a b ↦ by simp [c.monomial_mul, Finsupp.mapDomain_add]
      linearIndependent :=
        c.linearIndependent.comp _ (Finsupp.mapDomain_injective e.symm.injective) }
  invFun c :=
    { monomial := fun a ↦ c.monomial (a.mapDomain e)
      monomial_zero := by simp [c.monomial_zero]
      monomial_mul := fun a b ↦ by
        simp [c.monomial_mul, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      linearIndependent := c.linearIndependent.comp _ (Finsupp.mapDomain_injective e.injective) }
  left_inv c := BasedChart.ext fun a ↦ by simp [← Finsupp.mapDomain_comp]
  right_inv c := BasedChart.ext fun a ↦ by simp [← Finsupp.mapDomain_comp]

@[simp]
theorem reindex_monomial (e : I ≃ J) (c : BasedChart R u Λ B) (a : J →₀ ℤ) :
    (reindex e c).monomial a = c.monomial (a.mapDomain e.symm) :=
  (rfl)

@[simp]
theorem reindex_coordinate (e : I ≃ J) (c : BasedChart R u Λ B) (j : J) :
    (reindex e c).coordinate j = c.coordinate (e.symm j) := by
  rw [coordinate_def, reindex_monomial, Finsupp.mapDomain_single, ← coordinate_def]

/-- Construct a based chart from an injective `R`-algebra map `basedTorus R u Λ →ₐ[R] B`. -/
noncomputable def ofAlgHom (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    BasedChart R u Λ B :=
  (tautological R u Λ).map χ hχ

@[simp]
theorem ofAlgHom_monomial (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ)
    (a : I →₀ ℤ) :
    (ofAlgHom χ hχ).monomial a = Units.map χ.toMonoidHom (BasedTorus.unitMonomial a) :=
  (rfl)

theorem val_ofAlgHom_monomial (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ)
    (a : I →₀ ℤ) : ((ofAlgHom χ hχ).monomial a : B) = χ (BasedTorus.monomial a) :=
  (rfl)

@[simp]
theorem ofAlgHom_toAlgHom (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    (ofAlgHom χ hχ).toAlgHom = χ := by
  simp [ofAlgHom]

/-- **Bijection between injective torus maps and based charts**: sending an injective
`R`-algebra map `χ : basedTorus R u Λ →ₐ[R] B` to `a ↦ χ(X^a)` is a bijection onto
`BasedChart R u Λ B`. -/
noncomputable def algHomEquiv :
    { χ : basedTorus R u Λ →ₐ[R] B // Function.Injective χ } ≃ BasedChart R u Λ B where
  toFun χ := ofAlgHom χ.1 χ.2
  invFun c := ⟨c.toAlgHom, c.toAlgHom_injective⟩
  left_inv χ := Subtype.ext <| ofAlgHom_toAlgHom χ.1 χ.2
  right_inv c := BasedChart.ext fun a ↦ Units.ext (by simp)

@[simp]
theorem algHomEquiv_monomial (χ : { χ : basedTorus R u Λ →ₐ[R] B // Function.Injective χ })
    (a : I →₀ ℤ) :
    (algHomEquiv χ).monomial a = Units.map χ.1.toMonoidHom (BasedTorus.unitMonomial a) :=
  (rfl)

@[simp]
theorem algHomEquiv_symm_coe (c : BasedChart R u Λ B) :
    (algHomEquiv.symm c : basedTorus R u Λ →ₐ[R] B) = c.toAlgHom :=
  (rfl)

end Basic

section LaurentComparison

variable {R I A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **Bijection between injective Laurent charts and untwisted based charts**: at `u = 1` and
`Λ = 0` in a commutative `R`-algebra `A`, injective `R`-algebra maps `LaurentRing R I →ₐ[R] A`
correspond bijectively to `BasedChart R 1 0 A` via `M(a) = φ(X^a)`. -/
noncomputable def laurentChartEquiv :
    { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ } ≃
      BasedChart R 1 (0 : Matrix I I ℤ) A where
  toFun φ := ofAlgHom (φ.1.comp (BasedTorus.laurentRingEquivOfFormZero R 1 I).toAlgHom)
    (by
      rw [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom]
      exact φ.2.comp (BasedTorus.laurentRingEquivOfFormZero R 1 I).injective)
  invFun c := ⟨c.toAlgHom.comp (BasedTorus.laurentRingEquivOfFormZero R 1 I).symm.toAlgHom,
    by
      rw [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom]
      exact c.toAlgHom_injective.comp (BasedTorus.laurentRingEquivOfFormZero R 1 I).symm.injective⟩
  left_inv φ := Subtype.ext <| AlgHom.ext fun x ↦ by
    dsimp only
    rw [ofAlgHom_toAlgHom, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  right_inv c := BasedChart.ext fun a ↦ Units.ext <| by
    dsimp only
    rw [val_ofAlgHom_monomial, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, toAlgHom_monomial]

@[simp]
theorem val_laurentChartEquiv_monomial
    (φ : { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ }) (a : I →₀ ℤ) :
    ((laurentChartEquiv φ).monomial a : A) = φ.1 (AddMonoidAlgebra.single a 1) := by
  dsimp only [laurentChartEquiv, Equiv.coe_fn_mk]
  rw [val_ofAlgHom_monomial, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    BasedTorus.laurentRingEquivOfFormZero_monomial]

@[simp]
theorem val_laurentChartEquiv_coordinate
    (φ : { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ }) (i : I) :
    ((laurentChartEquiv φ).coordinate i : A) = φ.1 (LaurentRing.X i) := by
  simp [coordinate_def, LaurentRing.X_def]

end LaurentComparison

end BasedChart

/-! ### Ordered-product monomials -/

section OrderedProduct

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- The ordered product `∏_{i ∈ a.support} U_i^{a_i}` taken in increasing order of `I`. -/
noncomputable def orderedCoordProd [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) : Bˣ :=
  ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod

/-- Any finite superset `s ⊇ a.support` computes the same ordered coordinate product, since factors
outside `a.support` have exponent zero. -/
theorem orderedCoordProd_eq_sort_prod [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) {s : Finset I}
    (hs : a.support ⊆ s) :
    orderedCoordProd U a = ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod := by
  have hfilt : (s.sort (· ≤ ·)).filter (· ∈ a.support) = a.support.sort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise' ((s.pairwise_sort (· ≤ ·)).filter _)
      (a.support.pairwise_sort (· ≤ ·)) ?_
    refine (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _) (a.support.sort_nodup _)).mpr
      fun i ↦ ?_
    simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hi ↦ hs hi
  have hprod : ∀ (l : List I),
      (∀ i ∈ l, (i ∈ a.support : Bool) = false → U i ^ a i = 1) →
      (((l.filter (· ∈ a.support)).map fun i ↦ U i ^ a i).prod) =
        ((l.map fun i ↦ U i ^ a i).prod) := by
    intro l
    induction l with
    | nil => simp
    | cons i tl ih =>
      intro hf
      rw [List.filter_cons]
      split_ifs with hp
      · rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
          ih (fun j hj ↦ hf j (List.mem_cons_of_mem i hj))]
      · rw [List.map_cons, List.prod_cons, hf i List.mem_cons_self (Bool.eq_false_iff.mpr hp),
          one_mul, ih (fun j hj ↦ hf j (List.mem_cons_of_mem i hj))]
  rw [orderedCoordProd, ← hfilt]
  exact hprod (s.sort (· ≤ ·)) fun i _ hi ↦ by
    have hai : a i = 0 := by simpa using hi
    simp [hai]

theorem orderedCoordProd_eq_univ_sort [LinearOrder I] [Fintype I] (U : I → Bˣ) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((Finset.univ.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  orderedCoordProd_eq_sort_prod U a (Finset.subset_univ _)

/-- The normalized ordered-product monomial `u ^ (-∑_{i < j} a_i Λ_{ij} a_j) * ∏_i U_i^{a_i}`
associated to a family of units `U : I → Bˣ` and a linear order on `I`. -/
noncomputable def orderedMonomial [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B).toMonoidHom (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) *
    orderedCoordProd U a

@[simp]
theorem orderedMonomial_zero [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ) :
    orderedMonomial u Λ U 0 = 1 := by
  simp [orderedMonomial, orderedCoordProd]

@[simp]
theorem orderedMonomial_single_one [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (i : I) : orderedMonomial u Λ U (Finsupp.single i 1) = U i := by
  have hs : (Finsupp.single i (1 : ℤ)).support ⊆ ({i} : Finset I) := Finsupp.support_single_subset
  rw [orderedMonomial, orderedCoordProd_eq_sort_prod U _ hs, Matrix.finsuppBilinForm_single_single]
  simp

private theorem strictUpper_finsuppBilinForm_single_of_lt [LinearOrder I] (Λ : Matrix I I ℤ)
    {i : I} (x : ℤ) {a : I →₀ ℤ} (ha : ∀ j ∈ a.support, i < j) :
    Λ.strictUpper.finsuppBilinForm (Finsupp.single i x) a =
        Λ.finsuppBilinForm (Finsupp.single i x) a ∧
      Λ.strictUpper.finsuppBilinForm a (Finsupp.single i x) = 0 := by
  constructor
  · rw [Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp),
      Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp)]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp [ha j hj]
  · rw [Matrix.finsuppBilinForm_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finsupp.sum_single_index (by simp)]
    simp [(ha j hj).not_gt]

private theorem erase_support_mem_of_cons {i : I} {tl : List I} {b : I →₀ ℤ}
    (hb : ∀ j ∈ b.support, j ∈ i :: tl) :
    ∀ j ∈ (b.erase i).support, j ∈ tl := fun j hj ↦ by
  classical
  have hj0 : (b.erase i) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hji : j ≠ i := fun h ↦ hj0 (by simp [h])
  exact (List.mem_cons.mp
    (hb j (Finsupp.mem_support_iff.mpr (by simpa [hji] using hj0)))).resolve_left hji

private theorem map_zpow_erase_of_lt [LinearOrder I] (U : I → Bˣ) {i : I} {tl : List I}
    (hlt : ∀ j ∈ tl, i < j) (b : I →₀ ℤ) :
    (tl.map fun j ↦ U j ^ b j) = (tl.map fun j ↦ U j ^ (b.erase i) j) :=
  List.map_congr_left fun j hj ↦ by simp [(hlt j hj).ne']

/-- **Ordered-product formula for a based chart**: when `Λ` has zero diagonal, every normalized
monomial of `c` is determined from its coordinates by `orderedMonomial`. -/
theorem BasedChart.monomial_eq_orderedMonomial [LinearOrder I] (c : BasedChart R u Λ B)
    (hdiag : ∀ i, Λ i i = 0) (a : I →₀ ℤ) :
    c.monomial a = orderedMonomial u Λ c.coordinate a := by
  suffices ∀ (l : List I), l.Pairwise (· < ·) → ∀ b : I →₀ ℤ, (∀ j ∈ b.support, j ∈ l) →
      ((l.map fun i ↦ c.coordinate i ^ b i).prod : Bˣ) =
        Units.map (algebraMap R B).toMonoidHom (u ^ Λ.strictUpper.finsuppBilinForm b b) *
          c.monomial b by
    have key := this (a.support.sort (· ≤ ·)) (a.support.sortedLT_sort.pairwise) a
      fun j hj ↦ (Finset.mem_sort _).mpr hj
    rw [orderedMonomial, orderedCoordProd, key, ← mul_assoc, ← map_mul, ← zpow_add,
      neg_add_cancel, zpow_zero, map_one, one_mul]
  intro l hl
  induction l with
  | nil =>
    intro b hb
    have hb0 : b = 0 := Finsupp.support_eq_empty.mp
      (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hb j hj))
    simp [hb0, c.monomial_zero]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    intro b hb
    set b' := b.erase i
    have hb'_supp : ∀ j ∈ b'.support, j ∈ tl := erase_support_mem_of_cons hb
    have hb_decomp : Finsupp.single i (b i) + b' = b := Finsupp.single_add_erase i b
    obtain ⟨hup₁, hup₂⟩ := strictUpper_finsuppBilinForm_single_of_lt Λ (b i)
      fun j hj ↦ hl.1 j (hb'_supp j hj)
    have hup : Λ.strictUpper.finsuppBilinForm b b =
        Λ.finsuppBilinForm (Finsupp.single i (b i)) b' +
          Λ.strictUpper.finsuppBilinForm b' b' := by
      conv_lhs => rw [← hb_decomp]
      simp only [map_add, LinearMap.add_apply]
      rw [Matrix.finsuppBilinForm_single_single, hup₁, hup₂]
      simp only [Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    calc ((i :: tl).map fun j ↦ c.coordinate j ^ b j).prod
        = c.coordinate i ^ b i * (tl.map fun j ↦ c.coordinate j ^ b' j).prod := by
            rw [List.map_cons, List.prod_cons, map_zpow_erase_of_lt c.coordinate hl.1 b]
      _ = c.monomial (Finsupp.single i (b i)) *
            (Units.map (algebraMap R B).toMonoidHom (u ^ Λ.strictUpper.finsuppBilinForm b' b') *
              c.monomial b') := by
            rw [← c.monomial_single_of_diag_zero (hdiag i), ih hl.2 b' hb'_supp]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ Λ.strictUpper.finsuppBilinForm b' b') *
            (c.monomial (Finsupp.single i (b i)) * c.monomial b') := by
            rw [← mul_assoc, ← map_algebraMap_comm, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ Λ.strictUpper.finsuppBilinForm b b) *
            c.monomial b := by
            rw [c.monomial_mul, hb_decomp, ← mul_assoc, ← map_mul, ← zpow_add, add_comm, hup]

private theorem map_algebraMap_mul_comm (w : Rˣ) (x y : Bˣ) :
    x * (Units.map (algebraMap R B).toMonoidHom w * y) =
      Units.map (algebraMap R B).toMonoidHom w * (x * y) := by
  rw [← mul_assoc, ← map_algebraMap_comm, mul_assoc]

private theorem zpow_single_right_of_quasiComm {u : Rˣ} {Λ : Matrix I I ℤ} {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (i j : I) (k : ℤ) :
    U i * U j ^ k =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * k))) * (U j ^ k * U i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k hk =>
    calc U i * U j ^ ((k : ℤ) + 1)
        = (U i * U j ^ (k : ℤ)) * U j := by rw [zpow_add_one, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * (k : ℤ)))) *
            (U j ^ (k : ℤ) * (U i * U j)) := by rw [hk, mul_assoc, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * ((k : ℤ) + 1)))) *
            (U j ^ ((k : ℤ) + 1) * U i) := by
          rw [hU i j, map_algebraMap_mul_comm, ← mul_assoc, ← map_mul, ← zpow_add,
            ← mul_assoc (U j ^ (k : ℤ)), ← zpow_add_one]
          congr 3
          ring
  | pred k hk =>
    set z : ℤ := -(k : ℤ) - 1
    have hz : z + 1 = -(k : ℤ) := sub_add_cancel _ _
    refine mul_right_cancel (b := U j) ?_
    calc (U i * U j ^ z) * U j
        = U i * U j ^ (-(k : ℤ)) := by rw [mul_assoc, ← zpow_add_one, hz]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * (-(k : ℤ))))) *
            (U j ^ (-(k : ℤ)) * U i) := hk
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * z) + 2 * Λ i j)) *
            ((U j ^ z * U j) * U i) := by
          rw [← hz, zpow_add_one]
          congr 3
          ring
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * z))) *
            (U j ^ z * (Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) *
              (U j * U i))) := by
          rw [zpow_add, map_mul, mul_assoc, mul_assoc (U j ^ z),
            ← map_algebraMap_mul_comm (u ^ (2 * Λ i j)) (U j ^ z)]
      _ = (Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * z))) *
            (U j ^ z * U i)) * U j := by
          rw [← hU i j]
          simp only [mul_assoc]

private theorem zpow_mul_zpow_of_quasiComm {u : Rˣ} {Λ : Matrix I I ℤ} {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (i j : I) (m n : ℤ) :
    U i ^ m * U j ^ n =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (m * Λ i j * n))) * (U j ^ n * U i ^ m) := by
  have h1 := zpow_single_right_of_quasiComm hU i j n
  induction m using Int.induction_on with
  | zero => simp
  | succ m hm =>
    calc U i ^ ((m : ℤ) + 1) * U j ^ n
        = U i ^ (m : ℤ) * (U i * U j ^ n) := by rw [zpow_add_one, mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (((m : ℤ) + 1) * Λ i j * n))) *
            (U j ^ n * U i ^ ((m : ℤ) + 1)) := by
          rw [h1, map_algebraMap_mul_comm, ← mul_assoc (U i ^ (m : ℤ)), hm,
            mul_assoc (Units.map _ _) (U j ^ n * U i ^ (m : ℤ)), ← mul_assoc, ← map_mul,
            ← zpow_add, mul_assoc (U j ^ n), ← zpow_add_one]
          congr 3
          ring
  | pred m hm =>
    set z : ℤ := -(m : ℤ) - 1
    have hz : 1 + z = -(m : ℤ) := by dsimp [z]; ring
    refine mul_left_cancel (a := U i) ?_
    calc U i * (U i ^ z * U j ^ n)
        = U i ^ (-(m : ℤ)) * U j ^ n := by rw [← mul_assoc, ← zpow_one_add, hz]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (-(m : ℤ) * Λ i j * n))) *
            (U j ^ n * U i ^ (-(m : ℤ))) := hm
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * n) + 2 * (z * Λ i j * n))) *
            (U j ^ n * (U i * U i ^ z)) := by
          rw [← hz, zpow_one_add]
          congr 3
          ring
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (z * Λ i j * n))) *
            ((Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (Λ i j * n))) *
              (U j ^ n * U i)) * U i ^ z) := by
          rw [add_comm (2 * (Λ i j * n)), zpow_add, map_mul]
          simp only [mul_assoc]
      _ = U i * (Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (z * Λ i j * n))) *
            (U j ^ n * U i ^ z)) := by
          rw [← h1, mul_assoc (U i), ← map_algebraMap_mul_comm]

private theorem prod_zpow_mul_zpow_of_lt [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (tl : List I) {i : I} (htl : tl.Pairwise (· < ·)) (hi : ∀ j ∈ tl, i < j)
    (a : I →₀ ℤ) (ha : ∀ j ∈ a.support, j ∈ tl) (n : ℤ) :
    ((tl.map fun j ↦ U j ^ a j).prod) * U i ^ n =
      Units.map (algebraMap R B).toMonoidHom
        (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a)) *
        (U i ^ n * (tl.map fun j ↦ U j ^ a j).prod) := by
  induction tl generalizing a with
  | nil =>
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp
      (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (ha j hj))
    simp [ha0]
  | cons j rest ih =>
    rw [List.pairwise_cons] at htl
    set a' := a.erase j
    have ha'_supp : ∀ k ∈ a'.support, k ∈ rest := erase_support_mem_of_cons ha
    have ha_decomp : Finsupp.single j (a j) + a' = a := Finsupp.single_add_erase j a
    have hij : i < j := hi j List.mem_cons_self
    have hneg := Matrix.neg_apply_eq_of_isAlt_finsuppBilinForm hΛ i j
    have hup : Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a =
        n * Λ i j * a j + Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a' := by
      conv_lhs => rw [← ha_decomp]
      rw [map_add, Matrix.finsuppBilinForm_single_single, Matrix.strictUpper_apply]
      simp only [hij, ↓reduceIte]
      ring
    rw [List.map_cons, List.prod_cons, map_zpow_erase_of_lt U htl.1 a, mul_assoc,
      ih htl.2 (fun k hk ↦ hi k (List.mem_cons_of_mem j hk)) a' ha'_supp,
      map_algebraMap_mul_comm, ← mul_assoc (U j ^ a j),
      zpow_mul_zpow_of_quasiComm hU j i (a j) n,
      mul_assoc (Units.map _ _) (U i ^ n * U j ^ a j),
      ← mul_assoc, ← map_mul, ← zpow_add, hup]
    simp only [mul_assoc]
    congr 3
    rw [← hneg]
    ring

private theorem prod_zpow_mul_prod_zpow [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (l : List I) (hl : l.Pairwise (· < ·)) (p q : I →₀ ℤ)
    (hp : ∀ j ∈ p.support, j ∈ l) (hq : ∀ j ∈ q.support, j ∈ l) :
    ((l.map fun i ↦ U i ^ p i).prod) * ((l.map fun i ↦ U i ^ q i).prod) =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
        ((l.map fun i ↦ U i ^ (p + q) i).prod) := by
  induction l generalizing p q with
  | nil =>
    have hp0 : p = 0 := Finsupp.support_eq_empty.mp
      (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hp j hj))
    have hq0 : q = 0 := Finsupp.support_eq_empty.mp
      (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hq j hj))
    simp [hp0, hq0]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    set p' := p.erase i
    set q' := q.erase i
    have hp'_supp : ∀ j ∈ p'.support, j ∈ tl := erase_support_mem_of_cons hp
    have hq'_supp : ∀ j ∈ q'.support, j ∈ tl := erase_support_mem_of_cons hq
    have hp_decomp : Finsupp.single i (p i) + p' = p := Finsupp.single_add_erase i p
    have hq_decomp : Finsupp.single i (q i) + q' = q := Finsupp.single_add_erase i q
    have hup_q' : Λ.strictUpper.finsuppBilinForm q' (Finsupp.single i (p i)) = 0 :=
      (strictUpper_finsuppBilinForm_single_of_lt Λ (p i) (fun j hj ↦ hl.1 j (hq'_supp j hj))).2
    have hup : Λ.strictUpper.finsuppBilinForm q p =
        Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p' +
          Λ.strictUpper.finsuppBilinForm q' p' := by
      conv_lhs => rw [← hp_decomp, ← hq_decomp]
      simp only [map_add, LinearMap.add_apply]
      rw [Matrix.finsuppBilinForm_single_single, hup_q']
      simp only [Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    set P' := (tl.map fun j ↦ U j ^ p' j).prod with hP'
    set Q' := (tl.map fun j ↦ U j ^ q' j).prod with hQ'
    set PQ' := (tl.map fun j ↦ U j ^ (p' + q') j).prod with hPQ'
    have hpqmap : (tl.map fun j ↦ U j ^ (p + q) j) = (tl.map fun j ↦ U j ^ (p' + q') j) := by
      rw [map_zpow_erase_of_lt U hl.1 (p + q), Finsupp.erase_add]
    calc ((i :: tl).map fun j ↦ U j ^ p j).prod * ((i :: tl).map fun j ↦ U j ^ q j).prod
        = (U i ^ p i * (P' * U i ^ q i)) * Q' := by
            rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
              map_zpow_erase_of_lt U hl.1 p, map_zpow_erase_of_lt U hl.1 q, ← hP', ← hQ']
            simp only [mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p')) *
            (U i ^ (p + q) i * (P' * Q')) := by
            rw [hP', prod_zpow_mul_zpow_of_lt hΛ hU tl hl.2 hl.1 p' hp'_supp (q i), ← hP',
              map_algebraMap_mul_comm, ← mul_assoc (U i ^ p i), ← zpow_add, ← Finsupp.add_apply]
            simp only [mul_assoc]
      _ = Units.map (algebraMap R B).toMonoidHom
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p' +
              -2 * Λ.strictUpper.finsuppBilinForm q' p')) * (U i ^ (p + q) i * PQ') := by
            rw [hP', hQ', ih hl.2 p' q' hp'_supp hq'_supp, ← hPQ',
              map_algebraMap_mul_comm, ← mul_assoc, ← map_mul, ← zpow_add]
      _ = Units.map (algebraMap R B).toMonoidHom (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
            ((i :: tl).map fun j ↦ U j ^ (p + q) j).prod := by
            rw [List.map_cons, List.prod_cons, hpqmap, ← hPQ', hup]
            congr 3
            ring

/-- **Multiplication law for ordered-product monomials**: when `Λ` is alternating and the units
`U_i` satisfy `U_i * U_j = u ^ (2 * Λ i j) * (U_j * U_i)`, the family `orderedMonomial u Λ U`
satisfies the `(u, Λ)`-multiplication law `M(a) * M(b) = u ^ Λ(a, b) * M(a + b)`. -/
theorem orderedMonomial_mul [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (a b : I →₀ ℤ) :
    orderedMonomial u Λ U a * orderedMonomial u Λ U b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) *
        orderedMonomial u Λ U (a + b) := by
  let s := a.support ∪ b.support
  have ha : a.support ⊆ s := Finset.subset_union_left
  have hb : b.support ⊆ s := Finset.subset_union_right
  have hab : (a + b).support ⊆ s := Finsupp.support_add
  set P_a := ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod
  set P_b := ((s.sort (· ≤ ·)).map fun i ↦ U i ^ b i).prod
  set P_ab := ((s.sort (· ≤ ·)).map fun i ↦ U i ^ (a + b) i).prod
  have hprod : P_a * P_b =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-2 * Λ.strictUpper.finsuppBilinForm b a)) *
        P_ab :=
    prod_zpow_mul_prod_zpow hΛ hU (s.sort (· ≤ ·)) (s.sortedLT_sort.pairwise) a b
      (fun j hj ↦ (Finset.mem_sort _).mpr (ha hj))
      (fun j hj ↦ (Finset.mem_sort _).mpr (hb hj))
  calc orderedMonomial u Λ U a * orderedMonomial u Λ U b
      = (Units.map (algebraMap R B).toMonoidHom (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) * P_a) *
          (Units.map (algebraMap R B).toMonoidHom
            (u ^ (-Λ.strictUpper.finsuppBilinForm b b)) * P_b) := by
          rw [orderedMonomial, orderedMonomial, orderedCoordProd_eq_sort_prod U a ha,
            orderedCoordProd_eq_sort_prod U b hb]
    _ = Units.map (algebraMap R B).toMonoidHom (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) *
          (Units.map (algebraMap R B).toMonoidHom (u ^ (-Λ.strictUpper.finsuppBilinForm b b)) *
            (P_a * P_b)) := by
          rw [mul_assoc, ← mul_assoc P_a, ← map_algebraMap_comm _ P_a, mul_assoc _ P_a]
    _ = Units.map (algebraMap R B).toMonoidHom
          (u ^ (-Λ.strictUpper.finsuppBilinForm a a + -Λ.strictUpper.finsuppBilinForm b b +
            -2 * Λ.strictUpper.finsuppBilinForm b a)) * P_ab := by
          rw [hprod, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← zpow_add, ← zpow_add]
    _ = Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) *
          orderedMonomial u Λ U (a + b) := by
          rw [orderedMonomial, orderedCoordProd_eq_sort_prod U (a + b) hab, ← mul_assoc,
            ← map_mul, ← zpow_add, Matrix.finsuppBilinForm_eq_strictUpper_sub_flip hΛ a b]
          simp only [map_add, LinearMap.add_apply]
          congr 3
          ring

/-- **Order-independence of normalized ordered monomials**: for an alternating form `Λ` and
quasi-commuting units `U_i`, `orderedMonomial` does not depend on the linear order on `I`. -/
theorem orderedMonomial_eq_of_linearOrder (l₁ l₂ : LinearOrder I) {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (a : I →₀ ℤ) :
    @orderedMonomial R I B _ _ _ l₁ u Λ U a = @orderedMonomial R I B _ _ _ l₂ u Λ U a :=
  congr_fun (normalizedMonomial_eq_of_single_one_eq
    (@orderedMonomial_zero R I B _ _ _ l₁ u Λ U)
    (@orderedMonomial_zero R I B _ _ _ l₂ u Λ U)
    (@orderedMonomial_mul R I B _ _ _ l₁ u Λ hΛ U hU)
    (@orderedMonomial_mul R I B _ _ _ l₂ u Λ hΛ U hU)
    fun i ↦ by
      rw [@orderedMonomial_single_one R I B _ _ _ l₁,
        @orderedMonomial_single_one R I B _ _ _ l₂]) a

/-- **Universal property of the based quantum torus on quasi-commuting units**: for an alternating
form `Λ` and units `U : I → Bˣ` satisfying `U_i * U_j = u ^ (2 * Λ i j) * (U_j * U_i)`, there is
an `R`-algebra map `basedTorus R u Λ →ₐ[R] B` sending each coordinate `X_i` to `U_i` (unique by
`BasedTorus.algHom_ext` and normalized-monomial determination). -/
noncomputable def BasedTorus.liftCoordinates {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i)) :
    basedTorus R u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift
    (fun g ↦ (@orderedMonomial R I B _ _ _ (exists_wellFoundedLT I).choose u Λ U g.toAdd : B))
    (by simp [@orderedMonomial_zero R I B _ _ _ (exists_wellFoundedLT I).choose])
    fun g h ↦ by
      rw [← Units.val_mul,
        @orderedMonomial_mul R I B _ _ _ (exists_wellFoundedLT I).choose u Λ hΛ U hU,
        Units.val_mul, Units.coe_map]
      simp [Algebra.smul_def, toAdd_mul, formFactorSet]

@[simp]
theorem BasedTorus.liftCoordinates_X {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i)) (i : I) :
    BasedTorus.liftCoordinates hΛ U hU (BasedTorus.X i) = U i := by
  rw [BasedTorus.liftCoordinates, BasedTorus.X_def, BasedTorus.monomial_def,
    TwistedMonoidAlgebra.lift_of, toAdd_ofAdd,
    @orderedMonomial_single_one R I B _ _ _ (exists_wellFoundedLT I).choose]

private theorem unitsMap_unitMonomial_mul {u : Rˣ} {Λ : Matrix I I ℤ}
    (φ : basedTorus R u Λ →ₐ[R] B) (b c : I →₀ ℤ) :
    Units.map φ.toMonoidHom (BasedTorus.unitMonomial b) *
        Units.map φ.toMonoidHom (BasedTorus.unitMonomial c) =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm b c) *
        Units.map φ.toMonoidHom (BasedTorus.unitMonomial (b + c)) := by
  have hm : BasedTorus.unitMonomial (R := R) (u := u) (Λ := Λ) b * BasedTorus.unitMonomial c =
      Units.map (algebraMap R (basedTorus R u Λ)).toMonoidHom (u ^ Λ.finsuppBilinForm b c) *
        BasedTorus.unitMonomial (b + c) :=
    (BasedChart.tautological R u Λ).monomial_mul b c
  rw [← map_mul, hm, map_mul]
  refine congrArg (· * _) (Units.ext ?_)
  rw [Units.coe_map, Units.coe_map, Units.coe_map]
  exact φ.commutes _

/-- **Coordinate extensionality for maps from the based quantum torus**: two `R`-algebra
homomorphisms out of `basedTorus R u Λ` agree as soon as they agree on every coordinate `X_i`. -/
theorem BasedTorus.algHom_ext_X {u : Rˣ} {Λ : Matrix I I ℤ}
    {φ₁ φ₂ : basedTorus R u Λ →ₐ[R] B} (h : ∀ i, φ₁ (BasedTorus.X i) = φ₂ (BasedTorus.X i)) :
    φ₁ = φ₂ := by
  refine BasedTorus.algHom_ext fun a ↦ ?_
  exact congrArg Units.val <| congr_fun (normalizedMonomial_eq_of_single_one_eq
    (M₁ := fun b ↦ Units.map φ₁.toMonoidHom (BasedTorus.unitMonomial b))
    (M₂ := fun b ↦ Units.map φ₂.toMonoidHom (BasedTorus.unitMonomial b))
    (Units.ext <| by simp) (Units.ext <| by simp)
    (unitsMap_unitMonomial_mul φ₁) (unitsMap_unitMonomial_mul φ₂)
    fun i ↦ Units.ext <| by simpa [BasedTorus.X_def] using h i) a

theorem BasedTorus.liftCoordinates_monomial [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i)) (a : I →₀ ℤ) :
    BasedTorus.liftCoordinates hΛ U hU (BasedTorus.monomial a) = orderedMonomial u Λ U a := by
  exact congrArg Units.val <| congr_fun (normalizedMonomial_eq_of_single_one_eq
    (M₁ := fun b ↦ Units.map (BasedTorus.liftCoordinates hΛ U hU).toMonoidHom
      (BasedTorus.unitMonomial b))
    (M₂ := orderedMonomial u Λ U)
    (Units.ext <| by simp) (orderedMonomial_zero u Λ U)
    (unitsMap_unitMonomial_mul _) (orderedMonomial_mul hΛ hU)
    fun i ↦ Units.ext <| by
      simpa [BasedTorus.X_def] using BasedTorus.liftCoordinates_X hΛ U hU i) a

theorem BasedTorus.liftCoordinates_unique {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    {φ : basedTorus R u Λ →ₐ[R] B} (hφ : ∀ i, φ (BasedTorus.X i) = U i) :
    φ = BasedTorus.liftCoordinates hΛ U hU :=
  BasedTorus.algHom_ext_X fun i ↦ (hφ i).trans (BasedTorus.liftCoordinates_X hΛ U hU i).symm

/-- **Constructing a based chart from quasi-commuting coordinates** whose normalized ordered
products are `R`-linearly independent. -/
noncomputable def BasedChart.ofCoordinates [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) :
    BasedChart R u Λ B where
  monomial := orderedMonomial u Λ U
  monomial_zero := orderedMonomial_zero u Λ U
  monomial_mul := orderedMonomial_mul hΛ hU
  linearIndependent := hli

@[simp]
theorem BasedChart.ofCoordinates_coordinate [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (i : I) :
    (BasedChart.ofCoordinates hΛ U hU hli).coordinate i = U i :=
  orderedMonomial_single_one u Λ U i

/-! ### Rank-two ordered-monomial check -/

/-- For the standard rank-two skew form with `Λ(e₀, e₁) = 1`, the normalized monomial of a based
chart at exponent `-e₀ + 2 e₁` is `u² * X₀⁻¹ * X₁²`. -/
theorem BasedChart.monomial_rankTwo_neg_one_two {u : Rˣ}
    (c : BasedChart R u (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) B) :
    c.monomial (-Finsupp.single 0 1 + 2 • Finsupp.single 1 1) =
      Units.map (algebraMap R B).toMonoidHom (u ^ 2) *
        ((c.coordinate 0)⁻¹ * c.coordinate 1 ^ 2) := by
  have hd : ∀ i : Fin 2, (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) i i = 0 := by
    intro i; fin_cases i <;> rfl
  set a : Fin 2 →₀ ℤ := -Finsupp.single 0 1 + 2 • Finsupp.single 1 1
  have hsort : (Finset.univ : Finset (Fin 2)).sort (· ≤ ·) = [0, 1] := by
    have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by decide
    rw [← huniv]
    exact (List.toFinset_sort (r := (· ≤ ·)) (by decide)).mpr (by decide)
  rw [c.monomial_eq_orderedMonomial hd a, orderedMonomial, orderedCoordProd_eq_univ_sort, hsort]
  have ha0 : a 0 = -1 := by simp [a]
  have ha1 : a 1 = 2 := by simp [a]
  have hup : (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).strictUpper.finsuppBilinForm a a =
      -2 := by
    rw [Matrix.finsuppBilinForm_apply_eq_dotProduct]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, ha0, ha1]
  rw [hup]
  simp [ha0, ha1]

end OrderedProduct

end TauCeti
